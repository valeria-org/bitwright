//! Exact 128-bit bit-table carry-tree equality solver (Meet-in-the-Middle).
//!
//! Recognizes 128-bit equalities of the form `(LO ^ C_lo) | (HI ^ C_hi) == 0` (or `!= 0`,
//! or `(LO == C_lo) & (HI == C_hi)`) where:
//! - `LO` is a 64-bit modular sum of small (`<= 2`-bit) lookup tables `g_0, ..., g_{m-1}`,
//! - `HI` is a 64-bit modular sum of small lookup tables `h_j` plus unsigned carry terms
//!   `zext(A + B <u A)` / `zext(~A <u B)` that inductively merge the leaf clusters of `LO`
//!   into a single cluster equal to `LO`.
//!
//! When the carry tree covers `LO` with disjoint merges, the 128-bit identity
//!   `((HI as u128) << 64) | LO == (bias128 + sum_g W_g[bits_g]) mod 2^128`
//! holds identically for every input. When at most 32 free bit keys remain (or up to 34 when
//! bits `>= 32` are determined by the single carry out of `zext<64>(y:32) + K`), exact
//! Meet-in-the-Middle over `<= 2^16 + 2^16` states finds all solutions and rewrites the
//! guard to a constant (`0` solutions) or an explicit equality/disjunction (`<= 4` solutions).

use super::{Counter, Runner, Stop};
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, CmpOp, UnOp};

const MAX_LEAVES: usize = 32;
const MAX_FREE_BITS: usize = 32;
const MAX_HALF_BITS: usize = 16;
const MAX_SOLUTIONS: usize = 4;
const MAX_GROUP_BITS: usize = 4;
const MAX_SMALL_NODES: usize = 48;

/// A canonicalized single bit of a word node.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct BitKey {
    word: u32,
    bit: u16,
}

/// A 64-bit lookup table depending on at most 3 raw bit keys (`n_bits <= 3`).
#[derive(Copy, Clone, Debug)]
struct SmallTable {
    bits: [BitKey; 3],
    n_bits: u8,
    vals: [u64; 8],
}

/// A 128-bit additive group depending on `n_bits <= MAX_GROUP_BITS` bit keys.
#[derive(Clone, Debug)]
struct Group128 {
    bits: Vec<BitKey>,
    vals: Vec<u128>,
}

/// Entry point: try to solve a 1-bit `Eq`/`Ne`/`And`/`Or` node as a 128-bit bit-table
/// carry-tree equality. Returns `Ok(Some(rewritten))` on success, `Ok(None)` otherwise.
pub(in crate::engine::pass) fn reduce(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
) -> Result<Option<u32>, Stop> {
    let Some((a, b, ca, cb, want_eq)) = extract_128_eq(cx, root) else {
        return Ok(None);
    };
    let key = (a, b, ((cb as u128) << 64) | (ca as u128));
    if let Some(&cached) = r.mba.bit_tables.get(&key) {
        return Ok(match cached {
            Some(eq_node) if want_eq => Some(eq_node),
            Some(eq_node) => Some(r.build(cx, |cx| cx.c_un(UnOp::Not, eq_node))?),
            None => None,
        });
    }
    let solved = if let Some(res) = solve_pair(r, cx, a, b, ca, cb)? {
        Some(res)
    } else {
        solve_pair(r, cx, b, a, cb, ca)?
    };
    r.mba.bit_tables.insert(key, solved);
    let Some(eq_node) = solved else {
        return Ok(None);
    };
    if want_eq {
        Ok(Some(eq_node))
    } else {
        Ok(Some(r.build(cx, |cx| cx.c_un(UnOp::Not, eq_node))?))
    }
}

/// Recognize a 1-bit predicate testing `(a == ca) && (b == cb)` (when `want_eq == true`)
/// or its negation (when `want_eq == false`), for 64-bit `a, b`.
fn extract_128_eq(cx: &Context, root: u32) -> Option<(u32, u32, u64, u64, bool)> {
    let n = cx.node(root);
    if n.width != 1 {
        return None;
    }
    match n.op {
        OpCode::Eq | OpCode::Ne => {
            let want_eq = n.op == OpCode::Eq;
            let (lhs, k) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => (n.a, k.to_u64()?),
                (Some(k), None) => (n.b, k.to_u64()?),
                _ => return None,
            };
            if cx.wid(lhs) != 64 {
                return None;
            }
            let (or_node, inverted) = match (cx.node(lhs).op, k) {
                (OpCode::Or, 0) => (lhs, false),
                (OpCode::Not, u64::MAX) if cx.node(cx.node(lhs).a).op == OpCode::Or => {
                    (cx.node(lhs).a, false)
                }
                (OpCode::And, u64::MAX) => {
                    let an = cx.node(lhs);
                    let (na, nb) = (cx.node(an.a), cx.node(an.b));
                    if na.op == OpCode::Not && nb.op == OpCode::Not {
                        let (ea, ca) = zero_test_64(cx, na.a)?;
                        let (eb, cb) = zero_test_64(cx, nb.a)?;
                        return Some((ea, eb, ca, cb, want_eq));
                    }
                    return None;
                }
                _ => return None,
            };
            let _ = inverted;
            let on = cx.node(or_node);
            let (ea, ca) = zero_test_64(cx, on.a)?;
            let (eb, cb) = zero_test_64(cx, on.b)?;
            Some((ea, eb, ca, cb, want_eq))
        }
        OpCode::And => {
            let (ea, ca) = eq_const_64(cx, n.a, true)?;
            let (eb, cb) = eq_const_64(cx, n.b, true)?;
            Some((ea, eb, ca, cb, true))
        }
        OpCode::Or => {
            let (ea, ca) = eq_const_64(cx, n.a, false)?;
            let (eb, cb) = eq_const_64(cx, n.b, false)?;
            Some((ea, eb, ca, cb, false))
        }
        _ => None,
    }
}

fn eq_const_64(cx: &Context, i: u32, is_eq: bool) -> Option<(u32, u64)> {
    let n = cx.node(i);
    if (is_eq && n.op != OpCode::Eq) || (!is_eq && n.op != OpCode::Ne) {
        return None;
    }
    let (lhs, k) = match (cx.const_val(n.a), cx.const_val(n.b)) {
        (None, Some(k)) => (n.a, k.to_u64()?),
        (Some(k), None) => (n.b, k.to_u64()?),
        _ => return None,
    };
    if cx.wid(lhs) != 64 {
        return None;
    }
    peel_const_target_64(cx, lhs, k)
}

/// Rewrite `x == 0` (64-bit) into `expr == target`, requiring `expr` to be an `Add`.
fn zero_test_64(cx: &Context, x: u32) -> Option<(u32, u64)> {
    peel_const_target_64(cx, x, 0)
}

/// Rewrite `x == target` (64-bit) into `sum_expr == adjusted_target`, requiring `sum_expr` to be `Add`.
fn peel_const_target_64(cx: &Context, mut x: u32, mut target: u64) -> Option<(u32, u64)> {
    for _ in 0..6 {
        let n = cx.node(x);
        if n.width != 64 {
            return None;
        }
        match n.op {
            OpCode::Xor => {
                if let Some(k) = cx.const_val(n.b).and_then(|v| v.to_u64()) {
                    target ^= k;
                    x = n.a;
                } else if let Some(k) = cx.const_val(n.a).and_then(|v| v.to_u64()) {
                    target ^= k;
                    x = n.b;
                } else {
                    break;
                }
            }
            OpCode::Not => {
                target = !target;
                x = n.a;
            }
            OpCode::Sub => {
                if let Some(k) = cx.const_val(n.b).and_then(|v| v.to_u64()) {
                    target = target.wrapping_add(k);
                    x = n.a;
                } else if let Some(k) = cx.const_val(n.a).and_then(|v| v.to_u64()) {
                    target = k.wrapping_sub(target);
                    x = n.b;
                } else {
                    break;
                }
            }
            OpCode::Add => {
                // Keep Add as the sum root unless it is `sum + const` where `sum` is NOT an Add;
                // flattening will collect any constant bias automatically.
                return Some((x, target));
            }
            _ => break,
        }
    }
    (cx.node(x).op == OpCode::Add).then_some((x, target))
}

/// Flatten a 64-bit sum tree of `Add`s into `(addends, const_bias)`.
/// Only accepts pure `+` (no subtractions) for `LO`, where unsigned carries require `+`.
fn flatten_add_only(
    cx: &Context,
    root: u32,
    max_terms: usize,
    stop_leaves: Option<&[u32]>,
) -> Option<(Vec<u32>, u64)> {
    let mut stack = vec![root];
    let mut out = Vec::new();
    let mut bias = 0u64;
    let mut steps = 0usize;
    while let Some(i) = stack.pop() {
        steps += 1;
        if steps > max_terms * 4 {
            return None;
        }
        if stop_leaves.is_some_and(|leaves| leaves.contains(&i)) {
            if out.len() >= max_terms {
                return None;
            }
            out.push(i);
            continue;
        }
        if let Some(k) = cx.const_val(i).and_then(|v| v.to_u64()) {
            bias = bias.wrapping_add(k);
            continue;
        }
        let n = cx.node(i);
        let atomic_small_add = stop_leaves.is_none()
            && i != root
            && n.op == OpCode::Add
            && n.width == 64
            && cx.node(n.a).op != OpCode::Add
            && cx.node(n.b).op != OpCode::Add
            && eval_small_table(cx, i).is_some();
        if n.op == OpCode::Add && n.width == 64 && !atomic_small_add {
            stack.push(n.b);
            stack.push(n.a);
        } else {
            if out.len() >= max_terms {
                return None;
            }
            out.push(i);
        }
    }
    Some((out, bias))
}

/// Flatten a 64-bit linear sum for `HI` into `(terms_with_sign, const_bias)`.
/// Sign is `+1` for `Add`, `-1` for `Sub`/`Neg`.
fn flatten_hi_sum(cx: &Context, root: u32, max_terms: usize) -> Option<(Vec<(u32, bool)>, u64)> {
    let mut stack = vec![(root, false)];
    let mut out = Vec::new();
    let mut bias = 0u64;
    let mut steps = 0usize;
    while let Some((i, neg)) = stack.pop() {
        steps += 1;
        if steps > max_terms * 6 {
            return None;
        }
        if let Some(k) = cx.const_val(i).and_then(|v| v.to_u64()) {
            bias = if neg {
                bias.wrapping_sub(k)
            } else {
                bias.wrapping_add(k)
            };
            continue;
        }
        let n = cx.node(i);
        if n.width != 64 {
            return None;
        }
        match n.op {
            OpCode::Add => {
                stack.push((n.b, neg));
                stack.push((n.a, neg));
            }
            OpCode::Sub => {
                stack.push((n.b, !neg));
                stack.push((n.a, neg));
            }
            OpCode::Neg => {
                stack.push((n.a, !neg));
            }
            _ => {
                if out.len() >= max_terms {
                    return None;
                }
                out.push((i, neg));
            }
        }
    }
    Some((out, bias))
}

/// Peel a 1-bit condition into a canonical `(BitKey, polarity)` where the condition holds
/// iff `bit(word, bit_index) == polarity`, or `Ok(Err(constant_bool))` if constant.
/// Does NOT peel `Add(x, const)` here so that all bits of `x + const` stay attached to the
/// same word; low-bit unification happens afterward.
fn peel_bit(cx: &Context, cond: u32) -> Option<Result<(BitKey, bool), bool>> {
    let mut cur = cond;
    let mut pol = true;
    let (mut word, mut bit): (u32, u16) = loop {
        let n = cx.node(cur);
        if let Some(v) = cx.const_val(cur) {
            if n.width == 1 {
                return Some(Err((!v.is_zero()) == pol));
            }
            return None;
        }
        match n.op {
            OpCode::Not if n.width == 1 => {
                pol = !pol;
                cur = n.a;
            }
            OpCode::Eq | OpCode::Ne => {
                let (lhs, k) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (None, Some(k)) => (n.a, k.to_u64()?),
                    (Some(k), None) => (n.b, k.to_u64()?),
                    _ => return None,
                };
                let is_eq = n.op == OpCode::Eq;
                if cx.wid(lhs) == 1 {
                    if k == 0 {
                        if is_eq {
                            pol = !pol;
                        }
                        cur = lhs;
                        continue;
                    } else if k == 1 {
                        if !is_eq {
                            pol = !pol;
                        }
                        cur = lhs;
                        continue;
                    }
                    return None;
                }
                let ln = cx.node(lhs);
                if ln.op == OpCode::And {
                    let (src, mask) = match (cx.const_val(ln.a), cx.const_val(ln.b)) {
                        (None, Some(m)) => (ln.a, m.to_u64()?),
                        (Some(m), None) => (ln.b, m.to_u64()?),
                        _ => return None,
                    };
                    if mask.is_power_of_two() && (k == 0 || k == mask) {
                        let bit_on = (k == mask) == is_eq;
                        if !bit_on {
                            pol = !pol;
                        }
                        break (src, mask.trailing_zeros() as u16);
                    } else {
                        return None;
                    }
                } else if ln.op == OpCode::LShr
                    && let Some(sh) = cx.const_val(ln.b).and_then(|v| v.to_u64())
                    && sh + 1 == u64::from(ln.width)
                    && (k == 0 || k == 1)
                {
                    let bit_on = (k == 1) == is_eq;
                    if !bit_on {
                        pol = !pol;
                    }
                    break (ln.a, sh as u16);
                } else {
                    return None;
                }
            }
            OpCode::Slt | OpCode::Sle | OpCode::Ult | OpCode::Ule => {
                let (w, b, p) = crate::expr::field::bit_literal(cx, cur);
                if w == cur {
                    return None;
                }
                if !p {
                    pol = !pol;
                }
                break (w, b);
            }
            OpCode::Extract if n.width == 1 => {
                break (n.a, n.b as u16);
            }
            _ => return None,
        }
    };
    // Peel bit-preserving word operators down to the source word.
    for _ in 0..16 {
        let n = cx.node(word);
        let w = n.width;
        if bit >= w {
            return None;
        }
        if let Some(v) = cx.const_val(word).and_then(|v| v.to_u64()) {
            return Some(Err((((v >> bit) & 1) != 0) == pol));
        }
        match n.op {
            OpCode::Extract => {
                bit += n.b as u16;
                word = n.a;
            }
            OpCode::Zext => {
                let sw = cx.wid(n.a);
                if bit < sw {
                    word = n.a;
                } else {
                    return Some(Err(!pol));
                }
            }
            OpCode::Sext => {
                let sw = cx.wid(n.a);
                bit = bit.min(sw - 1);
                word = n.a;
            }
            OpCode::LShr => {
                let Some(s) = cx.const_val(n.b).and_then(|v| v.to_u64()) else {
                    break;
                };
                if u64::from(bit) + s < u64::from(w) {
                    bit += s as u16;
                    word = n.a;
                } else {
                    return Some(Err(!pol));
                }
            }
            OpCode::Shl => {
                let Some(s) = cx.const_val(n.b).and_then(|v| v.to_u64()) else {
                    break;
                };
                if u64::from(bit) >= s {
                    bit -= s as u16;
                    word = n.a;
                } else {
                    return Some(Err(!pol));
                }
            }
            OpCode::And => {
                let (src, m) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (None, Some(m)) => (n.a, m.to_u64()?),
                    (Some(m), None) => (n.b, m.to_u64()?),
                    _ => break,
                };
                if (m >> bit) & 1 == 1 {
                    word = src;
                } else {
                    return Some(Err(!pol));
                }
            }
            OpCode::Or => {
                let (src, m) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (None, Some(m)) => (n.a, m.to_u64()?),
                    (Some(m), None) => (n.b, m.to_u64()?),
                    _ => break,
                };
                if (m >> bit) & 1 == 0 {
                    word = src;
                } else {
                    return Some(Err(pol));
                }
            }
            OpCode::Xor => {
                let (src, m) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (None, Some(m)) => (n.a, m.to_u64()?),
                    (Some(m), None) => (n.b, m.to_u64()?),
                    _ => break,
                };
                if (m >> bit) & 1 == 1 {
                    pol = !pol;
                }
                word = src;
            }
            OpCode::Not => {
                pol = !pol;
                word = n.a;
            }
            OpCode::RotL | OpCode::RotR if w <= 64 => {
                let Some(s) = cx.const_val(n.b).and_then(|v| v.to_u64()) else {
                    break;
                };
                let wu = u64::from(w);
                let s = (s % wu) as u16;
                bit = if n.op == OpCode::RotL {
                    (bit + w - s) % w
                } else {
                    (bit + s) % w
                };
                word = n.a;
            }
            _ => break,
        }
    }
    Some(Ok((BitKey { word, bit }, pol)))
}

/// Evaluate a small node `root` (width `<= 64`) as an exact lookup table over at most 2 bit
/// keys. Returns `None` if `root` depends on more than 2 bit keys or unsupported operations.
fn eval_small_table(cx: &Context, root: u32) -> Option<SmallTable> {
    if cx.wid(root) > 64 {
        return None;
    }
    let mut bits = [BitKey { word: 0, bit: 0 }; 3];
    let mut n_bits = 0usize;
    let mut visited = 0usize;
    let mut seen: Vec<u32> = Vec::new();
    let mut stack = vec![root];
    // Pass 1: discover all bit keys (stopping at 1-bit predicates recognized by `peel_bit`).
    while let Some(i) = stack.pop() {
        if seen.contains(&i) {
            continue;
        }
        seen.push(i);
        visited += 1;
        if visited > MAX_SMALL_NODES {
            return None;
        }
        let n = cx.node(i);
        if n.width > 64 {
            return None;
        }
        if cx.const_val(i).is_some() {
            continue;
        }
        if n.width == 1 && let Some(res) = peel_bit(cx, i) {
            if let Ok((bk, _)) = res
                && !bits[..n_bits].contains(&bk)
            {
                if n_bits == 3 {
                    return None;
                }
                bits[n_bits] = bk;
                n_bits += 1;
            }
            continue;
        }
        match n.op {
            OpCode::Select => {
                stack.push(n.a);
                stack.push(n.b);
                stack.push(n.c);
            }
            OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::Shl
            | OpCode::LShr
            | OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Concat
            | OpCode::Eq
            | OpCode::Ne
            | OpCode::Ult
            | OpCode::Ule
            | OpCode::Slt
            | OpCode::Sle => {
                stack.push(n.a);
                stack.push(n.b);
            }
            OpCode::Not | OpCode::Neg | OpCode::Zext | OpCode::Sext | OpCode::Extract => {
                stack.push(n.a);
            }
            _ => return None,
        }
    }
    bits[..n_bits].sort();
    // Pass 2: evaluate `root` for every bit assignment `0..(1 << n_bits)`.
    let mut vals = [0u64; 8];
    let mut memo: Vec<(u32, u64)> = Vec::with_capacity(seen.len());
    for (assign, slot) in vals.iter_mut().enumerate().take(1usize << n_bits) {
        memo.clear();
        let v = eval_node(cx, root, &bits[..n_bits], assign, &mut memo, 0)?;
        *slot = v;
    }
    Some(SmallTable {
        bits,
        n_bits: n_bits as u8,
        vals,
    })
}

fn eval_node(
    cx: &Context,
    i: u32,
    bits: &[BitKey],
    assign: usize,
    memo: &mut Vec<(u32, u64)>,
    depth: u8,
) -> Option<u64> {
    if depth > 40 {
        return None;
    }
    if let Some(&(_, v)) = memo.iter().find(|&&(id, _)| id == i) {
        return Some(v);
    }
    let n = cx.node(i);
    let w = n.width;
    if w == 0 || w > 64 {
        return None;
    }
    let mask = u64::MAX >> (64 - w);
    let val = if let Some(k) = cx.const_val(i) {
        k.to_u64()? & mask
    } else if w == 1 && let Some(res) = peel_bit(cx, i) {
        match res {
            Err(c) => u64::from(c),
            Ok((bk, pol)) => {
                let pos = bits.iter().position(|&k| k == bk)?;
                let bit_val = ((assign >> pos) & 1) != 0;
                u64::from(bit_val == pol)
            }
        }
    } else {
        match n.op {
            OpCode::Select => {
                let c = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                if c != 0 {
                    eval_node(cx, n.b, bits, assign, memo, depth + 1)?
                } else {
                    eval_node(cx, n.c, bits, assign, memo, depth + 1)?
                }
            }
            OpCode::Add => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                a.wrapping_add(b) & mask
            }
            OpCode::Sub => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                a.wrapping_sub(b) & mask
            }
            OpCode::Mul => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                a.wrapping_mul(b) & mask
            }
            OpCode::Shl => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                if b >= u64::from(w) { 0 } else { (a << b) & mask }
            }
            OpCode::LShr => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                if b >= u64::from(w) { 0 } else { (a >> b) & mask }
            }
            OpCode::And => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                (a & b) & mask
            }
            OpCode::Or => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                (a | b) & mask
            }
            OpCode::Xor => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                (a ^ b) & mask
            }
            OpCode::Not => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                (!a) & mask
            }
            OpCode::Neg => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                a.wrapping_neg() & mask
            }
            OpCode::Zext => eval_node(cx, n.a, bits, assign, memo, depth + 1)? & mask,
            OpCode::Sext => {
                let sw = cx.wid(n.a);
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let sign = (a >> (sw - 1)) & 1;
                let ext = if sign != 0 {
                    a | (!0u64 << sw)
                } else {
                    a
                };
                ext & mask
            }
            OpCode::Extract => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                (a >> n.b) & mask
            }
            OpCode::Concat => {
                let hi = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let lo = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                let lw = cx.wid(n.b);
                ((hi << lw) | lo) & mask
            }
            OpCode::Eq => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                u64::from(a == b)
            }
            OpCode::Ne => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                u64::from(a != b)
            }
            OpCode::Ult => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                u64::from(a < b)
            }
            OpCode::Ule => {
                let a = eval_node(cx, n.a, bits, assign, memo, depth + 1)?;
                let b = eval_node(cx, n.b, bits, assign, memo, depth + 1)?;
                u64::from(a <= b)
            }
            OpCode::Slt | OpCode::Sle => {
                let aw = cx.wid(n.a);
                let shift = 64 - aw;
                let a = (eval_node(cx, n.a, bits, assign, memo, depth + 1)? << shift) as i64;
                let b = (eval_node(cx, n.b, bits, assign, memo, depth + 1)? << shift) as i64;
                u64::from(if n.op == OpCode::Slt { a < b } else { a <= b })
            }
            _ => return None,
        }
    };
    memo.push((i, val));
    Some(val)
}

/// If `term` is a positive carry `zext<64>(cmp)`, return the pair of operands `(a, b)` for
/// either `Carry::Sum(sum, part)` (`sum <u part`) or `Carry::Not(x, y)` (`~x <u y`).
enum CarryTerm {
    SumLt(u32, u32),
    NotLt(u32, u32),
}

fn parse_carry(cx: &Context, term: u32) -> Option<CarryTerm> {
    let n = cx.node(term);
    if n.op != OpCode::Zext || n.width != 64 || cx.wid(n.a) != 1 {
        return None;
    }
    let cmp = cx.node(n.a);
    if cmp.op != OpCode::Ult || cx.wid(cmp.a) != 64 {
        return None;
    }
    let lhs = cmp.a;
    let rhs = cmp.b;
    if cx.node(lhs).op == OpCode::Not {
        return Some(CarryTerm::NotLt(cx.node(lhs).a, rhs));
    }
    if cx.node(rhs).op == OpCode::Not {
        // `a <u ~b` is NOT a carry (`a + b < 2^64 - 1`).
        return None;
    }
    Some(CarryTerm::SumLt(lhs, rhs))
}

/// Convert a node `x` (which is a sum of leaf nodes from `leaf_ids`, plus optional bias)
/// into a bitmask of leaf indices in `0..leaf_ids.len()`. Returns `None` if any addend is
/// missing, duplicated, or has a mismatched bias.
fn expr_leaf_mask(
    cx: &Context,
    x: u32,
    leaf_ids: &[u32],
    absorbed_bias: Option<(usize, u64)>,
    const_leaf: Option<(usize, u64)>,
) -> Option<u64> {
    let (terms, bias) = flatten_add_only(cx, x, leaf_ids.len() + 2, Some(leaf_ids))?;
    let mut mask = 0u64;
    let mut expected_bias = 0u64;
    for t in terms {
        let idx = leaf_ids.iter().position(|&id| id == t)?;
        if (mask >> idx) & 1 != 0 {
            return None;
        }
        mask |= 1u64 << idx;
        if let Some((a_idx, a_bias)) = absorbed_bias
            && idx == a_idx
        {
            expected_bias = expected_bias.wrapping_add(a_bias);
        }
    }
    if bias == expected_bias {
        return Some(mask);
    }
    if let Some((c_idx, c_val)) = const_leaf
        && (mask >> c_idx) & 1 == 0
        && bias == expected_bias.wrapping_add(c_val)
    {
        return Some(mask | (1u64 << c_idx));
    }
    None
}

/// Try to solve `((hi_expr << 64) | lo_expr) == ((c_hi << 64) | c_lo)` as a 128-bit
/// bit-table carry-tree equality. Returns `Ok(Some(eq_node))` on an exact proof.
fn solve_pair(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    lo_expr: u32,
    hi_expr: u32,
    c_lo: u64,
    c_hi: u64,
) -> Result<Option<u32>, Stop> {
    // 1. Flatten LO into pure positive addends + constant bias.
    let Some((lo_raw, lo_bias)) = flatten_add_only(cx, lo_expr, MAX_LEAVES, None) else {
        return Ok(None);
    };
    if lo_raw.len() < 4 || lo_raw.len() > MAX_LEAVES {
        return Ok(None);
    }
    // Reject duplicate raw leaves in LO (distinct leaves required for simple bitmask tracking).
    for i in 0..lo_raw.len() {
        if lo_raw[i + 1..].contains(&lo_raw[i]) {
            return Ok(None);
        }
    }
    // 2. Flatten HI into signed terms + constant bias.
    let Some((hi_raw, hi_bias)) = flatten_hi_sum(cx, hi_expr, MAX_LEAVES * 4) else {
        return Ok(None);
    };
    // Quick check: HI must contain at least `lo_raw.len() - 2` positive `zext(ult)` terms
    // (`lo_raw.len() - 1` for a full carry tree, or `lo_raw.len() - 2` when the final top-level
    // carry against a single leaf table is folded into `HI` as `[c_lo <u leaf]`).
    let mut carry_candidates: Vec<(u32, CarryTerm)> = Vec::new();
    let mut hi_other: Vec<(u32, bool)> = Vec::new();
    for (t, neg) in hi_raw {
        if !neg && let Some(ct) = parse_carry(cx, t) {
            carry_candidates.push((t, ct));
        } else {
            hi_other.push((t, neg));
        }
    }
    if carry_candidates.len() * 2 + 2 < lo_raw.len() {
        return Ok(None);
    }
    // 3. Evaluate every LO leaf as a small (`<= 2`-bit) table.
    let mut lo_tables: Vec<SmallTable> = Vec::with_capacity(lo_raw.len() + 1);
    for &leaf in &lo_raw {
        let Some(tbl) = eval_small_table(cx, leaf) else {
            return Ok(None);
        };
        lo_tables.push(tbl);
    }
    // 4. Handle nonzero `lo_bias`: either absorbed into a single leaf `g_j` when a carry
    //    references `g_j + lo_bias`, or kept as a 0-bit constant leaf.
    let mut absorbed_bias: Option<(usize, u64)> = None;
    let mut const_leaf: Option<(usize, u64)> = None;
    if lo_bias != 0 {
        'find_absorb: for (_, ct) in &carry_candidates {
            let ops = match *ct {
                CarryTerm::SumLt(a, b) | CarryTerm::NotLt(a, b) => [a, b],
            };
            for op in ops {
                if let Some((ts, b)) = flatten_add_only(cx, op, 2, Some(&lo_raw))
                    && ts.len() == 1
                    && b == lo_bias
                    && let Some(idx) = lo_raw.iter().position(|&id| id == ts[0])
                {
                    absorbed_bias = Some((idx, lo_bias));
                    let len = 1usize << lo_tables[idx].n_bits;
                    for v in &mut lo_tables[idx].vals[..len] {
                        *v = v.wrapping_add(lo_bias);
                    }
                    break 'find_absorb;
                }
            }
        }
        if absorbed_bias.is_none() {
            if lo_raw.len() >= MAX_LEAVES {
                return Ok(None);
            }
            const_leaf = Some((lo_raw.len(), lo_bias));
            lo_tables.push(SmallTable {
                bits: [BitKey { word: 0, bit: 0 }; 3],
                n_bits: 0,
                vals: [lo_bias, 0, 0, 0, 0, 0, 0, 0],
            });
        }
    }
    let m = lo_tables.len();
    let full_mask = (1u64 << m) - 1;
    // 5. Inductively verify the carry tree merges all `m` singleton clusters into `full_mask`.
    let mut active: Vec<u64> = (0..m).map(|i| 1u64 << i).collect();
    let mut cluster_max: Vec<u64> = lo_tables
        .iter()
        .map(|t| {
            t.vals[..1usize << t.n_bits]
                .iter()
                .copied()
                .max()
                .unwrap_or(0)
        })
        .collect();
    let mut used = vec![false; carry_candidates.len()];
    let mut parsed_carries: Vec<Option<(u64, u64)>> = Vec::with_capacity(carry_candidates.len());
    let mut carry_op_masks: Vec<u64> = Vec::new();
    // Helper: recognize `x` as `~lo_raw[k]` when `~` was pushed into a small `select` table.
    let complement_leaf = |cx: &Context, x: u32| -> Option<usize> {
        let xt = eval_small_table(cx, x)?;
        let len = 1usize << xt.n_bits;
        lo_tables.iter().enumerate().position(|(_, lt)| {
            lt.n_bits == xt.n_bits
                && lt.bits[..xt.n_bits as usize] == xt.bits[..xt.n_bits as usize]
                && (0..len).all(|a| !lt.vals[a] == xt.vals[a])
        })
    };
    for (_, ct) in &carry_candidates {
        let pair = match *ct {
            CarryTerm::SumLt(sum, part) => {
                if let (Some(sm), Some(pm)) = (
                    expr_leaf_mask(cx, sum, &lo_raw, absorbed_bias, const_leaf),
                    expr_leaf_mask(cx, part, &lo_raw, absorbed_bias, const_leaf),
                ) && pm != 0
                    && (sm & pm) == pm
                    && sm != pm
                {
                    carry_op_masks.push(sm ^ pm);
                    carry_op_masks.push(pm);
                    Some((sm ^ pm, pm))
                } else if let (Some(k), Some(ym)) = (
                    complement_leaf(cx, sum),
                    expr_leaf_mask(cx, part, &lo_raw, absorbed_bias, const_leaf),
                ) && ym != 0
                    && ((ym >> k) & 1) == 0
                {
                    carry_op_masks.push(ym);
                    Some((1u64 << k, ym))
                } else {
                    None
                }
            }
            CarryTerm::NotLt(x, y) => {
                if let (Some(xm), Some(ym)) = (
                    expr_leaf_mask(cx, x, &lo_raw, absorbed_bias, const_leaf),
                    expr_leaf_mask(cx, y, &lo_raw, absorbed_bias, const_leaf),
                ) && xm != 0
                    && ym != 0
                    && (xm & ym) == 0
                {
                    carry_op_masks.push(xm);
                    carry_op_masks.push(ym);
                    Some((xm, ym))
                } else {
                    None
                }
            }
        };
        parsed_carries.push(pair);
    }
    loop {
        let mut merged_any = false;
        for (idx, pair) in parsed_carries.iter().enumerate() {
            if used[idx] {
                continue;
            }
            let Some((u, v)) = *pair else { continue };
            let Some(pu) = active.iter().position(|&c| c == u) else {
                continue;
            };
            let Some(pv) = active.iter().position(|&c| c == v) else {
                continue;
            };
            if pu == pv {
                continue;
            }
            used[idx] = true;
            let combined = u | v;
            let combined_max = cluster_max[pu].saturating_add(cluster_max[pv]);
            if pu > pv {
                active.swap_remove(pu);
                cluster_max.swap_remove(pu);
                active[pv] = combined;
                cluster_max[pv] = combined_max;
            } else {
                active.swap_remove(pv);
                cluster_max.swap_remove(pv);
                active[pu] = combined;
                cluster_max[pu] = combined_max;
            }
            merged_any = true;
        }
        // Any two active clusters inside the same carry operand mask whose maximum possible values
        // satisfy `max_u + max_v <= u64::MAX` can never produce a 64-bit unsigned carry (`0`).
        if !merged_any && active.len() > 1 {
            'zero_carry: for &m_op in &carry_op_masks {
                if m_op.count_ones() < 2 {
                    continue;
                }
                for pu in 0..active.len() {
                    let u = active[pu];
                    if (m_op & u) != u {
                        continue;
                    }
                    for pv in (pu + 1)..active.len() {
                        let v = active[pv];
                        if (m_op & v) != v {
                            continue;
                        }
                        let Some(sum_max) = cluster_max[pu].checked_add(cluster_max[pv]) else {
                            continue;
                        };
                        active.swap_remove(pv);
                        cluster_max.swap_remove(pv);
                        active[pu] = u | v;
                        cluster_max[pu] = sum_max;
                        merged_any = true;
                        break 'zero_carry;
                    }
                }
            }
        }
        if !merged_any {
            break;
        }
    }
    let mut implicit_top_carry: Option<SmallTable> = None;
    if active.len() == 2 && (active[0] | active[1]) == full_mask && (active[0] & active[1]) == 0 {
        // Under `LO == c_lo`, a missing top-level carry between `(full_mask ^ (1 << v))` and a
        // single leaf `g_v` equals `[(L_rest + g_v) mod 2^64 <u g_v] == [c_lo <u g_v]`, which is
        // an exact `<= 2`-bit table over `g_v`'s bits subtracted from the 128-bit sum's high word.
        let single = if active[0].count_ones() == 1 {
            Some(active[0].trailing_zeros() as usize)
        } else if active[1].count_ones() == 1 {
            Some(active[1].trailing_zeros() as usize)
        } else {
            None
        };
        let Some(v_idx) = single else {
            return Ok(None);
        };
        let gv = lo_tables[v_idx];
        let mut cvals = [0u64; 8];
        for a in 0..(1usize << gv.n_bits) {
            cvals[a] = u64::from(c_lo < gv.vals[a]);
        }
        implicit_top_carry = Some(SmallTable {
            bits: gv.bits,
            n_bits: gv.n_bits,
            vals: cvals,
        });
    } else if active.len() != 1 || active[0] != full_mask {
        return Ok(None);
    }
    // 6. Any unused carry candidate (e.g., local constant-offset carries on 2 bits) and all
    //    other HI terms must evaluate as small (`<= 2`-bit) tables.
    for (idx, &(term, _)) in carry_candidates.iter().enumerate() {
        if !used[idx] {
            hi_other.push((term, false));
        }
    }
    let mut hi_tables: Vec<(SmallTable, bool)> = Vec::with_capacity(hi_other.len() + 1);
    if let Some(ctbl) = implicit_top_carry {
        hi_tables.push((ctbl, true));
    }
    for (term, neg) in hi_other {
        let Some(tbl) = eval_small_table(cx, term) else {
            return Ok(None);
        };
        hi_tables.push((tbl, neg));
    }

    // 7. Unify bit keys across equivalent 32-bit/64-bit offsets and low-bit `Add(y, K)` words.
    let unify = build_bit_unification(cx, &lo_tables, &hi_tables);
    let mut lo_128: Vec<(SmallTable, bool)> = lo_tables
        .into_iter()
        .map(|t| (apply_unification(t, &unify), false))
        .collect();
    let hi_128: Vec<(SmallTable, bool)> = hi_tables
        .into_iter()
        .map(|(t, neg)| (apply_unification(t, &unify), neg))
        .collect();

    // 8. Build combined 128-bit additive groups by merging tables that share bit keys.
    let mut base128: u128 = (hi_bias as u128) << 64;
    let mut groups: Vec<Group128> = Vec::new();
    let mut add_table = |tbl: SmallTable, is_hi: bool, neg: bool| -> bool {
        let n = tbl.n_bits as usize;
        if n == 0 {
            let v = if is_hi {
                let h = if neg { tbl.vals[0].wrapping_neg() } else { tbl.vals[0] };
                (h as u128) << 64
            } else {
                tbl.vals[0] as u128
            };
            base128 = base128.wrapping_add(v);
            return true;
        }
        let tbl_bits = &tbl.bits[..n];
        let mut vals = Vec::with_capacity(1 << n);
        for &raw in &tbl.vals[..(1usize << n)] {
            let v = if is_hi {
                let h = if neg { raw.wrapping_neg() } else { raw };
                (h as u128) << 64
            } else {
                raw as u128
            };
            vals.push(v);
        }
        // Find all existing groups overlapping `tbl_bits`.
        let mut hits: Vec<usize> = Vec::new();
        for (gi, g) in groups.iter().enumerate() {
            if tbl_bits.iter().any(|b| g.bits.contains(b)) {
                hits.push(gi);
            }
        }
        if hits.is_empty() {
            groups.push(Group128 {
                bits: tbl_bits.to_vec(),
                vals,
            });
            return true;
        }
        // Merge `tbl` and all overlapping groups into one group (capped at MAX_GROUP_BITS).
        let mut merged_bits: Vec<BitKey> = tbl_bits.to_vec();
        for &gi in &hits {
            for &b in &groups[gi].bits {
                if !merged_bits.contains(&b) {
                    merged_bits.push(b);
                }
            }
        }
        if merged_bits.len() > MAX_GROUP_BITS {
            return false;
        }
        merged_bits.sort();
        let mut merged_vals = vec![0u128; 1 << merged_bits.len()];
        let map_tbl: Vec<usize> = tbl_bits
            .iter()
            .map(|b| merged_bits.iter().position(|x| x == b).unwrap_or(0))
            .collect();
        for (a, slot) in merged_vals.iter_mut().enumerate() {
            let mut ta = 0usize;
            for (k, &pos) in map_tbl.iter().enumerate() {
                ta |= ((a >> pos) & 1) << k;
            }
            *slot = slot.wrapping_add(vals[ta]);
        }
        for &gi in &hits {
            let g = &groups[gi];
            let map_g: Vec<usize> = g
                .bits
                .iter()
                .map(|b| merged_bits.iter().position(|x| x == b).unwrap_or(0))
                .collect();
            for (a, slot) in merged_vals.iter_mut().enumerate() {
                let mut ga = 0usize;
                for (k, &pos) in map_g.iter().enumerate() {
                    ga |= ((a >> pos) & 1) << k;
                }
                *slot = slot.wrapping_add(g.vals[ga]);
            }
        }
        // Remove merged groups from back to front and push the new combined group.
        for &gi in hits.iter().rev() {
            groups.swap_remove(gi);
        }
        groups.push(Group128 {
            bits: merged_bits,
            vals: merged_vals,
        });
        true
    };
    for (t, _) in lo_128.drain(..) {
        if !add_table(t, false, false) {
            return Ok(None);
        }
    }
    for (t, neg) in hi_128 {
        if !add_table(t, true, neg) {
            return Ok(None);
        }
    }

    let target128 = (((c_hi as u128) << 64) | (c_lo as u128)).wrapping_sub(base128);
    let total_bits: usize = groups.iter().map(|g| g.bits.len()).sum();

    // 9. Check whether all bit keys belong to a single word `W = zext<w>(y:nw) + K`
    //    with some bits >= nw (carry-coupled 2-case MITM).
    if total_bits > MAX_FREE_BITS {
        return solve_carry_split(r, cx, &groups, target128);
    }
    if let Some(res) = solve_carry_split(r, cx, &groups, target128)? {
        return Ok(Some(res));
    }

    let Some(sols) = run_mitm(r, &groups, target128)? else {
        return Ok(None);
    };
    emit_solutions(r, cx, &groups, &sols, None)
}

/// Detect `W64 = (zext<64>(y:32) | (y64 & 0xffffffff)) + K64` and unify:
/// 1. `W32 = (y:32 | trunc<32>(y64)) + (K64 as u32)` -> `(W64, b)` for `b < 32`.
/// 2. `(y, b)` for `b <= trailing_zeros(K64)` -> `(W64, b)` (flipping polarity at `b == tz`).
fn build_bit_unification(
    cx: &Context,
    lo_tables: &[SmallTable],
    hi_tables: &[(SmallTable, bool)],
) -> IdMap<BitKey, (BitKey, bool)> {
    let mut words: Vec<u32> = Vec::new();
    let mut note = |t: &SmallTable| {
        for b in &t.bits[..t.n_bits as usize] {
            if !words.contains(&b.word) {
                words.push(b.word);
            }
        }
    };
    for t in lo_tables {
        note(t);
    }
    for (t, _) in hi_tables {
        note(t);
    }
    let mut map: IdMap<BitKey, (BitKey, bool)> = IdMap::default();
    if words.len() < 2 {
        return map;
    }
    // Extract `(source_node_for_low32, k64)` for any 64-bit `Add(low32, K64)`.
    let low32_origin = |cx: &Context, x: u32| -> Option<u32> {
        let n = cx.node(x);
        match n.op {
            OpCode::Zext if cx.wid(n.a) == 32 => {
                let inner = cx.node(n.a);
                if inner.op == OpCode::Extract && inner.b == 0 {
                    Some(inner.a)
                } else {
                    Some(n.a)
                }
            }
            OpCode::And if n.width == 64 => {
                let (src, m) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (None, Some(m)) => (n.a, m.to_u64()?),
                    (Some(m), None) => (n.b, m.to_u64()?),
                    _ => return None,
                };
                (m == 0xffffffff).then_some(src)
            }
            _ => None,
        }
    };
    let word32_origin = |cx: &Context, x: u32| -> u32 {
        let n = cx.node(x);
        if n.op == OpCode::Extract && n.b == 0 && n.width == 32 {
            n.a
        } else {
            x
        }
    };
    let mut add_words: Vec<(u32, u32, u64)> = Vec::new();
    let add_const_form = |cx: &Context, id: u32| -> Option<(u32, u64)> {
        let n = cx.node(id);
        if n.width > 64 {
            return None;
        }
        let mask = u64::MAX >> (64 - n.width);
        match n.op {
            OpCode::Add => match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => Some((n.a, k.to_u64()? & mask)),
                (Some(k), None) => Some((n.b, k.to_u64()? & mask)),
                _ => None,
            },
            OpCode::Sub => {
                if let Some(c1) = cx.const_val(n.a).and_then(|v| v.to_u64()) {
                    let inner = cx.node(n.b);
                    if inner.op == OpCode::Sub
                        && let Some(c2) = cx.const_val(inner.a).and_then(|v| v.to_u64())
                    {
                        return Some((inner.b, c1.wrapping_sub(c2) & mask));
                    }
                }
                if let Some(c2) = cx.const_val(n.b).and_then(|v| v.to_u64()) {
                    return Some((n.a, c2.wrapping_neg() & mask));
                }
                None
            }
            _ => None,
        }
    };
    for &w in &words {
        let n = cx.node(w);
        if let Some((lhs, k)) = add_const_form(cx, w) {
            if n.width == 64
                && let Some(orig) = low32_origin(cx, lhs)
            {
                add_words.push((w, orig, k));
            } else if n.width <= 64 {
                add_words.push((w, lhs, k));
            }
        }
    }
    // Map equivalent 32-bit `Add(y32, k32)` words onto their 64-bit `Add(zext32(y), k64)` word,
    // map low bits `b <= tz(k)` of `orig` onto `(w_add, b)`, and unify `orig + k` with
    // `orig + ok` on bits `0..=tz(ok - k)`.
    for &(w_add, orig, k) in &add_words {
        let nw = cx.wid(w_add);
        let tz = if k == 0 { nw } else { (k.trailing_zeros() as u16).min(nw) };
        for &other in &words {
            if other == w_add {
                continue;
            }
            let on = cx.node(other);
            // Case 0: another `Add(orig, ok)` of the same width (`w_add < other` canonical).
            if nw == on.width
                && w_add < other
                && let Some(&(_, o_orig, ok)) = add_words.iter().find(|&&(ow, _, _)| ow == other)
                && o_orig == orig
            {
                let full = u64::MAX >> (64 - nw);
                let delta = ok.wrapping_sub(k) & full;
                let dtz = if delta == 0 {
                    nw
                } else {
                    (delta.trailing_zeros() as u16).min(nw)
                };
                for b in 0..=dtz.min(nw.saturating_sub(1)) {
                    if b < dtz {
                        map.entry(BitKey { word: other, bit: b })
                            .or_insert((BitKey { word: w_add, bit: b }, false));
                    } else if b == dtz && delta != 0 {
                        map.entry(BitKey { word: other, bit: b })
                            .or_insert((BitKey { word: w_add, bit: b }, true));
                    }
                }
            }
            // Case 1: 32-bit `Add(orig_32, k as u32)` matches 64-bit `w_add`.
            if nw == 64
                && on.width == 32
                && on.op == OpCode::Add
                && let Some((olhs, ok)) = match (cx.const_val(on.a), cx.const_val(on.b)) {
                    (None, Some(v)) => Some((on.a, v.to_u64().unwrap_or(0))),
                    (Some(v), None) => Some((on.b, v.to_u64().unwrap_or(0))),
                    _ => None,
                }
                && word32_origin(cx, olhs) == orig
                && (ok as u32) == (k as u32)
            {
                for b in 0..32u16 {
                    map.entry(BitKey { word: other, bit: b })
                        .or_insert((BitKey { word: w_add, bit: b }, false));
                }
            }
            // Case 2: `other` is `orig` (or `trunc<32>(orig)`): bits `0..=tz` agree with `w_add`
            // (with bit `tz` inverted).
            let same_base = other == orig || (nw == 64 && on.width == 32 && word32_origin(cx, other) == orig);
            if same_base {
                let lim = tz.min(on.width.saturating_sub(1));
                for b in 0..=lim {
                    if b < tz {
                        map.entry(BitKey { word: other, bit: b })
                            .or_insert((BitKey { word: w_add, bit: b }, false));
                    } else if b == tz && b < on.width && k != 0 {
                        map.entry(BitKey { word: other, bit: b })
                            .or_insert((BitKey { word: w_add, bit: b }, true));
                    }
                }
            }
        }
    }
    map
}

fn apply_unification(t: SmallTable, map: &IdMap<BitKey, (BitKey, bool)>) -> SmallTable {
    if map.is_empty() || t.n_bits == 0 {
        return t;
    }
    let n = t.n_bits as usize;
    let mut mapped = [BitKey { word: 0, bit: 0 }; 3];
    let mut flips = [false; 3];
    for k in 0..n {
        if let Some(&(dst, flip)) = map.get(&t.bits[k]) {
            mapped[k] = dst;
            flips[k] = flip;
        } else {
            mapped[k] = t.bits[k];
        }
    }
    let mut uniq = [BitKey { word: 0, bit: 0 }; 3];
    let mut u_len = 0usize;
    for &b in &mapped[..n] {
        if !uniq[..u_len].contains(&b) {
            uniq[u_len] = b;
            u_len += 1;
        }
    }
    uniq[..u_len].sort();
    let mut new_vals = [0u64; 8];
    for (u_assign, slot) in new_vals.iter_mut().enumerate().take(1usize << u_len) {
        let mut orig_assign = 0usize;
        for k in 0..n {
            let pos = uniq[..u_len].iter().position(|&x| x == mapped[k]).unwrap();
            let bit_on = (((u_assign >> pos) & 1) != 0) ^ flips[k];
            if bit_on {
                orig_assign |= 1 << k;
            }
        }
        *slot = t.vals[orig_assign];
    }
    SmallTable {
        bits: uniq,
        n_bits: u_len as u8,
        vals: new_vals,
    }
}

/// Handle `W = (zext<w>(y:nw) | (yw & ((1 << nw) - 1))) + K` (`1 <= nw < w <= 64`, `nw <= 32`)
/// when high bits `b >= nw` of `W` appear in `groups`: those bits are determined by the single
/// carry out of `y:nw + (K & ((1 << nw) - 1))`.
fn solve_carry_split(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    groups: &[Group128],
    target128: u128,
) -> Result<Option<u32>, Stop> {
    let Some(first_word) = groups.first().and_then(|g| g.bits.first()).map(|b| b.word) else {
        return Ok(None);
    };
    if !groups
        .iter()
        .all(|g| g.bits.iter().all(|b| b.word == first_word))
    {
        return Ok(None);
    }
    let wn = cx.node(first_word);
    let w = wn.width;
    if !(2..=64).contains(&w) || wn.op != OpCode::Add {
        return Ok(None);
    }
    let full_w = u64::MAX >> (64 - w);
    let Some((lhs, kw)) = (match (cx.const_val(wn.a), cx.const_val(wn.b)) {
        (None, Some(k)) => k.to_u64().map(|v| (wn.a, v & full_w)),
        (Some(k), None) => k.to_u64().map(|v| (wn.b, v & full_w)),
        _ => None,
    }) else {
        return Ok(None);
    };
    let ln = cx.node(lhs);
    let nw_opt: Option<u16> = if ln.op == OpCode::Zext && cx.wid(ln.a) < w && cx.wid(ln.a) <= 32 {
        Some(cx.wid(ln.a))
    } else if ln.op == OpCode::And
        && let Some(m) = cx
            .const_val(ln.b)
            .or_else(|| cx.const_val(ln.a))
            .and_then(|v| v.to_u64())
        && m != 0
        && (m & (m + 1)) == 0
    {
        let nw = m.count_ones() as u16;
        (nw < w && nw <= 32).then_some(nw)
    } else {
        None
    };
    let Some(nw) = nw_opt else {
        return Ok(None);
    };
    if !groups.iter().any(|g| g.bits.iter().any(|b| b.bit >= nw)) {
        return Ok(None);
    }
    let low_nw_mask = if nw == 32 {
        u64::from(u32::MAX)
    } else {
        (1u64 << nw) - 1
    };
    let lo_k = (kw & low_nw_mask) as u32;
    let hi_k = kw >> nw;
    let hi_mask = u64::MAX >> (64 - (w - nw));
    let mut all_valid: Vec<(u32, u64)> = Vec::new();
    let carry_cases: &[u64] = if lo_k == 0 { &[0] } else { &[0, 1] };
    for &carry in carry_cases {
        let hi_val = hi_k.wrapping_add(carry) & hi_mask;
        // Specialize every group by fixing all bits >= nw to `bit(hi_val, b - nw)`.
        let mut sub_groups: Vec<Group128> = Vec::new();
        let mut sub_base = 0u128;
        for g in groups {
            let mut free_idx = Vec::new();
            let mut fixed_mask = 0usize;
            for (k, b) in g.bits.iter().enumerate() {
                if b.bit >= nw {
                    if ((hi_val >> (b.bit - nw)) & 1) != 0 {
                        fixed_mask |= 1 << k;
                    }
                } else {
                    free_idx.push(k);
                }
            }
            if free_idx.is_empty() {
                sub_base = sub_base.wrapping_add(g.vals[fixed_mask]);
            } else {
                let sub_bits: Vec<BitKey> = free_idx.iter().map(|&k| g.bits[k]).collect();
                let mut sub_vals = Vec::with_capacity(1 << free_idx.len());
                for a in 0..(1usize << free_idx.len()) {
                    let mut orig_a = fixed_mask;
                    for (j, &k) in free_idx.iter().enumerate() {
                        if (a >> j) & 1 != 0 {
                            orig_a |= 1 << k;
                        }
                    }
                    sub_vals.push(g.vals[orig_a]);
                }
                sub_groups.push(Group128 {
                    bits: sub_bits,
                    vals: sub_vals,
                });
            }
        }
        let free_total: usize = sub_groups.iter().map(|g| g.bits.len()).sum();
        if free_total > MAX_FREE_BITS {
            return Ok(None);
        }
        // Only emit if all `nw` low bits are present (so carry condition `w_low < lo_k` is exact).
        let mut low_mask = 0u64;
        for g in &sub_groups {
            for b in &g.bits {
                low_mask |= 1u64 << b.bit;
            }
        }
        if low_mask != low_nw_mask {
            return Ok(None);
        }
        let Some(sols) = run_mitm(r, &sub_groups, target128.wrapping_sub(sub_base))? else {
            return Ok(None);
        };
        for sol in sols {
            let mut w_low = 0u32;
            for (g, &a) in sub_groups.iter().zip(&sol) {
                for (k, b) in g.bits.iter().enumerate() {
                    if (a >> k) & 1 != 0 {
                        w_low |= 1u32 << b.bit;
                    }
                }
            }
            let valid = if carry == 1 { w_low < lo_k } else { w_low >= lo_k };
            if valid {
                all_valid.push((w_low, ((hi_val << nw) | u64::from(w_low)) & full_w));
                if all_valid.len() > MAX_SOLUTIONS {
                    return Ok(None);
                }
            }
        }
    }
    if all_valid.is_empty() {
        return Ok(Some(r.build(cx, |cx| cx.mk_const_u64(1, 0))?));
    }
    let narrow_target: Option<u32> = if ln.op == OpCode::Zext && cx.wid(ln.a) == nw {
        Some(ln.a)
    } else if ln.op == OpCode::And {
        let src = if cx.const_val(ln.b).and_then(|v| v.to_u64()) == Some(low_nw_mask) {
            Some(ln.a)
        } else if cx.const_val(ln.a).and_then(|v| v.to_u64()) == Some(low_nw_mask) {
            Some(ln.b)
        } else {
            None
        };
        match src {
            Some(s) => Some(r.build(cx, |cx| cx.c_extract(s, 0, nw))?),
            None => None,
        }
    } else {
        None
    };
    let mut acc: Option<u32> = None;
    for &(w_low, full_val) in &all_valid {
        let eq = if let Some(yn) = narrow_target {
            let y_val = u64::from(w_low.wrapping_sub(lo_k)) & low_nw_mask;
            r.build(cx, |cx| {
                let k = cx.mk_const_u64(nw, y_val)?;
                cx.c_cmp(CmpOp::Eq, yn, k)
            })?
        } else {
            r.build(cx, |cx| {
                let k = cx.mk_const_u64(w, full_val)?;
                cx.c_cmp(CmpOp::Eq, first_word, k)
            })?
        };
        acc = Some(match acc {
            None => eq,
            Some(prev) => r.build(cx, |cx| cx.c_bin(BinOp::Or, prev, eq))?,
        });
    }
    Ok(acc)
}

/// Exact Meet-in-the-Middle over `groups`: returns `Ok(Some(solutions))` (each solution is a
/// `Vec<usize>` giving the chosen index per group) when `<= MAX_SOLUTIONS` solutions exist,
/// or `Ok(None)` if over budget, unpartitionable into `<= 16 + 16` bits, or `> MAX_SOLUTIONS`.
fn run_mitm(
    r: &mut Runner<'_, '_>,
    groups: &[Group128],
    mut target128: u128,
) -> Result<Option<Vec<Vec<usize>>>, Stop> {
    // Normalize each group so `vals[0] == 0` by folding `vals[0]` into `target128`.
    let mut norm: Vec<Vec<u128>> = Vec::with_capacity(groups.len());
    for g in groups {
        let v0 = g.vals[0];
        target128 = target128.wrapping_sub(v0);
        norm.push(g.vals.iter().map(|v| v.wrapping_sub(v0)).collect());
    }
    // Partition groups into Left and Right halves with `<= MAX_HALF_BITS` bits each.
    let mut order: Vec<usize> = (0..groups.len()).collect();
    order.sort_by_key(|&i| core::cmp::Reverse(groups[i].bits.len()));
    let mut left_idx: Vec<usize> = Vec::new();
    let mut right_idx: Vec<usize> = Vec::new();
    let (mut n_left, mut n_right) = (0usize, 0usize);
    for gi in order {
        let b = groups[gi].bits.len();
        if n_left <= n_right && n_left + b <= MAX_HALF_BITS {
            left_idx.push(gi);
            n_left += b;
        } else if n_right + b <= MAX_HALF_BITS {
            right_idx.push(gi);
            n_right += b;
        } else if n_left + b <= MAX_HALF_BITS {
            left_idx.push(gi);
            n_left += b;
        } else {
            return Ok(None);
        }
    }
    let work_cost = (((1u64 << n_left) + (1u64 << n_right)) / 4).max(64);
    if work_cost > r.meter.left_in(|b| b.pass_work) / 2 {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, work_cost)?;

    // Enumerate all `1 << n_left` sums of the Left half.
    let n_l = 1usize << n_left;
    let mut left_sums: Vec<u128> = Vec::with_capacity(n_l);
    left_sums.push(0);
    for &gi in &left_idx {
        let vals = &norm[gi];
        let prev_len = left_sums.len();
        for &delta in &vals[1..] {
            for j in 0..prev_len {
                let s = left_sums[j].wrapping_add(delta);
                left_sums.push(s);
            }
        }
    }
    // Build open-addressed hash table on `lo64(sum_L)` (load factor <= 0.5).
    let tab_bits = (n_left + 1).max(4);
    let tab_size = 1usize << tab_bits;
    let tab_mask = tab_size - 1;
    let shift = 64 - tab_bits;
    let mut table: Vec<u32> = vec![u32::MAX; tab_size];
    for (idx, &sum) in left_sums.iter().enumerate() {
        let mut slot = ((sum as u64).wrapping_mul(0x9e3779b97f4a7c15) >> shift) as usize;
        while table[slot] != u32::MAX {
            slot = (slot + 1) & tab_mask;
        }
        table[slot] = idx as u32;
    }

    // Enumerate all `1 << n_right` sums of the Right half and probe the Left table.
    let n_r = 1usize << n_right;
    let mut right_sums: Vec<u128> = Vec::with_capacity(n_r);
    right_sums.push(0);
    for &gi in &right_idx {
        let vals = &norm[gi];
        let prev_len = right_sums.len();
        for &delta in &vals[1..] {
            for j in 0..prev_len {
                let s = right_sums[j].wrapping_add(delta);
                right_sums.push(s);
            }
        }
    }

    let mut solutions: Vec<Vec<usize>> = Vec::new();
    for (r_state, &sum_r) in right_sums.iter().enumerate() {
        let need = target128.wrapping_sub(sum_r);
        let mut slot = ((need as u64).wrapping_mul(0x9e3779b97f4a7c15) >> shift) as usize;
        loop {
            let entry = table[slot];
            if entry == u32::MAX {
                break;
            }
            if left_sums[entry as usize] == need {
                if solutions.len() >= MAX_SOLUTIONS {
                    return Ok(None);
                }
                let mut sol = vec![0usize; groups.len()];
                let mut l_code = entry as usize;
                for &gi in &left_idx {
                    let b = groups[gi].bits.len();
                    sol[gi] = l_code & ((1 << b) - 1);
                    l_code >>= b;
                }
                let mut r_code = r_state;
                for &gi in &right_idx {
                    let b = groups[gi].bits.len();
                    sol[gi] = r_code & ((1 << b) - 1);
                    r_code >>= b;
                }
                solutions.push(sol);
            }
            slot = (slot + 1) & tab_mask;
        }
    }
    Ok(Some(solutions))
}

/// Emit the exact 1-bit predicate representing the union of `sols`.
fn emit_solutions(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    groups: &[Group128],
    sols: &[Vec<usize>],
    _extra: Option<()>,
) -> Result<Option<u32>, Stop> {
    if sols.is_empty() {
        return Ok(Some(r.build(cx, |cx| cx.mk_const_u64(1, 0))?));
    }
    let mut disj: Option<u32> = None;
    for sol in sols {
        // Group constrained bits by word node.
        let mut by_word: Vec<(u32, u64, u64)> = Vec::new(); // (word, mask, val)
        for (g, &a) in groups.iter().zip(sol) {
            for (k, bk) in g.bits.iter().enumerate() {
                let bit_val = ((a >> k) & 1) as u64;
                if let Some(entry) = by_word.iter_mut().find(|e| e.0 == bk.word) {
                    entry.1 |= 1u64 << bk.bit;
                    entry.2 |= bit_val << bk.bit;
                } else {
                    by_word.push((bk.word, 1u64 << bk.bit, bit_val << bk.bit));
                }
            }
        }
        let mut conj: Option<u32> = None;
        for (word, mask, val) in by_word {
            let w = cx.wid(word);
            if w == 0 || w > 64 {
                return Ok(None);
            }
            let all = u64::MAX >> (64 - w);
            let eq = r.build(cx, |cx| {
                let lhs = if mask == all {
                    word
                } else {
                    let m = cx.mk_const_u64(w, mask)?;
                    cx.c_bin(BinOp::And, word, m)?
                };
                let rhs = cx.mk_const_u64(w, val)?;
                cx.c_cmp(CmpOp::Eq, lhs, rhs)
            })?;
            conj = Some(match conj {
                None => eq,
                Some(prev) => r.build(cx, |cx| cx.c_bin(BinOp::And, prev, eq))?,
            });
        }
        let Some(c) = conj else { continue };
        disj = Some(match disj {
            None => c,
            Some(prev) => r.build(cx, |cx| cx.c_bin(BinOp::Or, prev, c))?,
        });
    }
    Ok(disj)
}

#[cfg(test)]
mod tests {
    use crate::engine::{Budget, Engine, Run, Strategy};
    use crate::mba::MbaConfig;
    use crate::{BitVec, Context, ParseOptions, View, Width};

    fn run_sweep(expr: &str) -> (Context, crate::Expr) {
        let mut cx = Context::new();
        let e = cx.parse(expr, &ParseOptions::width(Width::W64)).unwrap();
        let strategy = Strategy::deobfuscate()
            .with_mba(MbaConfig::default().with_opaque_sweep(true));
        let engine = Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap();
        let out = engine
            .run(&mut cx, &[e], Run::default().with_per_call(Budget::fuel(1 << 18)))
            .unwrap();
        (cx, out.roots[0].expr)
    }

    #[test]
    fn solves_128bit_bit_table_guard_unique_and_unsat() {
        // 4 two-bit tables on bits 0..7 of 8-bit `x` (total 8 bits -> 256 states).
        // Weights are 67-bit constants `(hi_i << 64) | lo_i`.
        let w: [u128; 8] = [
            0x3_123456789abcdef0u128,
            0x5_fedcba9876543211u128,
            0x2_0f1e2d3c4b5a6978u128,
            0x7_a1b2c3d4e5f60718u128,
            0x4_9081726354453627u128,
            0x6_1122334455667789u128,
            0x1_8877665544332211u128,
            0x3_deadbeefcafebabeu128,
        ];
        // Pick target = sum for x = 0xa5 (binary 1010_0101).
        let x_sol: u8 = 0xa5;
        let mut target = 0u128;
        for (b, &wb) in w.iter().enumerate() {
            if (x_sol >> b) & 1 != 0 {
                target = target.wrapping_add(wb);
            }
        }
        let mk_group = |k: usize| {
            let w00 = 0u128;
            let w01 = w[2 * k];
            let w10 = w[2 * k + 1];
            let w11 = w01.wrapping_add(w10);
            let lo = format!(
                "select(extract<{}, 1>(x:8), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}))",
                2 * k,
                2 * k + 1,
                w11 as u64,
                w01 as u64,
                2 * k + 1,
                w10 as u64,
                w00 as u64
            );
            let hi = format!(
                "select(extract<{}, 1>(x:8), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}))",
                2 * k,
                2 * k + 1,
                (w11 >> 64) as u64,
                (w01 >> 64) as u64,
                2 * k + 1,
                (w10 >> 64) as u64,
                (w00 >> 64) as u64
            );
            (lo, hi)
        };
        let (l0, h0) = mk_group(0);
        let (l1, h1) = mk_group(1);
        let (l2, h2) = mk_group(2);
        let (l3, h3) = mk_group(3);
        let src_unique = format!(
            "let %0 = {l0}; let %1 = {l1}; let %2 = {l2}; let %3 = {l3}; \
             let %4 = %0 + %1; let %5 = %2 + %3; let %6 = %4 + %5; \
             let %7 = ({h0}) + ({h1}) + ({h2}) + ({h3}) + zext<64>(%4 <u %0) + zext<64>(%5 <u %2) + zext<64>(%6 <u %4); \
             ((%6 ^ {:#x}) | (%7 ^ {:#x})) == 0",
            target as u64,
            (target >> 64) as u64
        );
        let (mut cx, out) = run_sweep(&src_unique);
        for v in 0..=255u64 {
            let got = cx
                .eval(&[out], &[("x".into(), BitVec::from_u64(Width::W8, v).unwrap())][..])
                .unwrap()[0];
            assert_eq!(!got.is_zero(), v == u64::from(x_sol), "mismatch at x={v}");
        }
        assert!(cx.dag_size(&[out], 10).is_ok());

        // Unsatisfiable target (`target ^ 1` has no solution).
        let unsat_target = target ^ 1;
        let src_unsat = format!(
            "let %0 = {l0}; let %1 = {l1}; let %2 = {l2}; let %3 = {l3}; \
             let %4 = %0 + %1; let %5 = %2 + %3; let %6 = %4 + %5; \
             let %7 = ({h0}) + ({h1}) + ({h2}) + ({h3}) + zext<64>(%4 <u %0) + zext<64>(%5 <u %2) + zext<64>(%6 <u %4); \
             ((%6 ^ {:#x}) | (%7 ^ {:#x})) == 0",
            unsat_target as u64,
            (unsat_target >> 64) as u64
        );
        let (cx2, out2) = run_sweep(&src_unsat);
        assert!(matches!(cx2.view(out2).unwrap(), View::Const(v) if v.is_zero()));

        // Soundness check: drop one carry from `%hi`; the carry tree is incomplete, so
        // `bit_table` must NOT rewrite it to an unsound constant or wrong equality.
        let src_missing_carry = format!(
            "let %0 = {l0}; let %1 = {l1}; let %2 = {l2}; let %3 = {l3}; \
             let %4 = %0 + %1; let %5 = %2 + %3; let %6 = %4 + %5; \
             let %7 = ({h0}) + ({h1}) + ({h2}) + ({h3}) + zext<64>(%4 <u %0) + zext<64>(%5 <u %2); \
             ((%6 ^ {:#x}) | (%7 ^ {:#x})) == 0",
            target as u64,
            (target >> 64) as u64
        );
        let (mut cx3, out3) = run_sweep(&src_missing_carry);
        let orig3 = cx3.parse(&src_missing_carry, &ParseOptions::width(Width::W64)).unwrap();
        for v in 0..=255u64 {
            let env = [("x".into(), BitVec::from_u64(Width::W8, v).unwrap())];
            let vals = cx3.eval(&[orig3, out3], &env[..]).unwrap();
            assert_eq!(vals[0], vals[1], "unsound rewrite at x={v}");
        }
    }

    #[test]
    fn solves_pushed_complement_carry_guard() {
        // Use pushed-complement carries `select(~w) <u other` (as emitted after `~` folding).
        let w: [u128; 8] = [
            0x2_0123456789abcdefu128,
            0x6_fedcba9876543210u128,
            0x1_13579bdf02468aceu128,
            0x4_eca86420fdb97531u128,
            0x5_0f0e0d0c0b0a0908u128,
            0x3_f0f1f2f3f4f5f6f7u128,
            0x7_1020304050607080u128,
            0x2_8070605040302010u128,
        ];
        let x_sol: u8 = 0x5c;
        let mut target = 0u128;
        for (b, &wb) in w.iter().enumerate() {
            if (x_sol >> b) & 1 != 0 {
                target = target.wrapping_add(wb);
            }
        }
        let mk_group = |k: usize| {
            let w00 = 0u128;
            let w01 = w[2 * k];
            let w10 = w[2 * k + 1];
            let w11 = w01.wrapping_add(w10);
            let lo = format!(
                "select(extract<{}, 1>(x:8), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}))",
                2 * k, 2 * k + 1, w11 as u64, w01 as u64, 2 * k + 1, w10 as u64, w00 as u64
            );
            let lo_not = format!(
                "select(extract<{}, 1>(x:8), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}))",
                2 * k, 2 * k + 1, !(w11 as u64), !(w01 as u64), 2 * k + 1, !(w10 as u64), !(w00 as u64)
            );
            let hi = format!(
                "select(extract<{}, 1>(x:8), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}), select(extract<{}, 1>(x:8), {:#x}:64, {:#x}))",
                2 * k, 2 * k + 1, (w11 >> 64) as u64, (w01 >> 64) as u64, 2 * k + 1, (w10 >> 64) as u64, (w00 >> 64) as u64
            );
            (lo, lo_not, hi)
        };
        let (l0, ln0, h0) = mk_group(0);
        let (l1, _, h1) = mk_group(1);
        let (l2, ln2, h2) = mk_group(2);
        let (l3, _, h3) = mk_group(3);
        let src = format!(
            "let %0 = {l0}; let %1 = {l1}; let %2 = {l2}; let %3 = {l3}; \
             let %4 = %0 + %1; let %5 = %2 + %3; let %6 = %4 + %5; \
             let %7 = ({h0}) + ({h1}) + ({h2}) + ({h3}) + zext<64>({ln0} <u %1) + zext<64>({ln2} <u %3) + zext<64>(~%4 <u %5); \
             ((%6 ^ {:#x}) | (%7 ^ {:#x})) == 0",
            target as u64,
            (target >> 64) as u64
        );
        let (mut cx, out) = run_sweep(&src);
        for v in 0..=255u64 {
            let got = cx
                .eval(&[out], &[("x".into(), BitVec::from_u64(Width::W8, v).unwrap())][..])
                .unwrap()[0];
            assert_eq!(!got.is_zero(), v == u64::from(x_sol), "mismatch at x={v}");
        }
        assert!(cx.dag_size(&[out], 10).is_ok());
    }

    #[test]
    fn solves_implicit_top_carry_34bit_guard() {
        let src = r#"
let %0 = trunc<32>(#2:64);
let %1 = %0 + 0xdd9eda58;
let %2 = extract<30, 1>(%1);
let %3 = %1 <s 0;
let %4 = select(%3, 0x526dd042f4d1446a:64, 0xcdde0d0021c241cc);
let %5 = select(%2, %4, %4 + 0x3221f2ffde3dbe34);
let %6 = extract<28, 1>(%1);
let %7 = #2 & 0xffffffff;
let %8 = %7 + 0x5d4c0259dd9eda58;
let %9 = extract<29, 1>(%8);
let %10 = select(%9, 0xf837a932c5f7d65c:64, 0x8fb385729f4a1118);
let %11 = select(%6, %10, %10 + 0x704c7a8d60b5eee8);
let %12 = %5 + %11;
let %13 = extract<26, 1>(%1);
let %14 = extract<27, 1>(%1);
let %15 = select(%14, 0x21687fbeaecd2d02:64, 0x3100cb0f2db87c1e);
let %16 = select(%13, %15, %15 + 0xceff34f0d24783e2);
let %17 = extract<24, 1>(%8);
let %18 = select(extract<25, 1>(%1), 0xc21cb0d86c1d26d4:64, 0xa7439f6f4d829bac);
let %19 = select(%17, %18, %18 + 0x58bc6090b27d6454);
let %20 = %12 + %16 + %19;
let %21 = extract<22, 1>(%8);
let %22 = extract<23, 1>(%8);
let %23 = select(%22, 0x7ac92728e3c3027e:64, 0xcf36604e9a9d32b0);
let %24 = select(%21, %23, %23 + 0x30c99fb16562cd50);
let %25 = extract<20, 1>(%8);
let %26 = extract<21, 1>(%8);
let %27 = select(%26, 0x391c6fc8318fa58:64, 0xec28555fc602146a);
let %28 = select(%25, %27, %27 + 0x13d7aaa039fdeb96);
let %29 = extract<18, 1>(%8);
let %30 = extract<19, 1>(%8);
let %31 = select(%30, 0x9f52c7d9b0b42bdc:64, 0x81692c94c97fbd86);
let %32 = select(%29, %31, %31 + 0x7e96d36b3680427a);
let %33 = %20 + %24 + %28 + %32;
let %34 = extract<14, 1>(%8);
let %35 = extract<15, 1>(%8);
let %36 = select(%35, 0x73f1878434accafc:64, 0xe2714f5893413d40);
let %37 = select(%34, %36, %36 + 0x1d8eb0a76cbec2c0);
let %38 = extract<12, 1>(%8);
let %39 = extract<13, 1>(%8);
let %40 = select(%39, 0x1c34b2a88b544698:64, 0x3313b865a01daabe);
let %41 = select(%38, %40, %40 + 0xccec479a5fe25542);
let %42 = extract<10, 1>(%8);
let %43 = extract<11, 1>(%8);
let %44 = select(%43, 0x11a37f57bbefe77a:64, 0xa9f2638e1c106274);
let %45 = select(%42, %44, %44 + 0x560d9c71e3ef9d8c);
let %46 = extract<6, 1>(%8);
let %47 = trunc<8>(%8) <s 0;
let %48 = select(%47, 0x5092c6ff4a01a8a4:64, 0x7f87b2f16b5c52c2);
let %49 = select(%46, %48, %48 + 0x80784d0e94a3ad3e);
let %50 = trunc<1>(%8);
let %51 = extract<1, 1>(#2);
let %52 = select(%51, 0x2c7d6e88303b0275:64, 0xa09d2204f6bdd145);
let %53 = select(%50, %52, %52 + 0x5f62ddfb09422ebb);
let %54 = extract<2, 1>(#2);
let %55 = extract<3, 1>(#2);
let %56 = select(%55, 0x9a59a2110e9a1d60:64, 0xc71ef9b3aaf82b40);
let %57 = select(%54, %56, %56 + 0x65a65deef165e2a0);
let %58 = extract<4, 1>(%8);
let %59 = extract<5, 1>(%8);
let %60 = select(%59, 0x17e01e1e6024331c:64, 0xb74de02b410ab86a);
let %61 = select(%58, %60, %60 + 0x48b21fd4bef54796);
let %62 = extract<8, 1>(%8);
let %63 = extract<9, 1>(%8);
let %64 = select(%63, 0x7df8efd6f23fb130:64, 0x358f1c5a274837ea);
let %65 = select(%62, %64, %64 + 0xca70e3a5d8b7c816);
let %66 = extract<16, 1>(%8);
let %67 = extract<17, 1>(%8);
let %68 = select(%67, 0x73de706c3bbca9c:64, 0x3001002089328d1e);
let %69 = select(%66, %68, %68 + 0xcffeffdf76cd72e2);
let %70 = %33 + %37 + %41 + %45 + %49 + %53 + %57 + %61 + %65 + %69;
let %71 = extract<32, 1>(%8);
let %72 = extract<33, 1>(%8);
let %73 = select(%72, 0xd75ddbfe6e679da0:64, 0x9d8d3f5639c65448);
let %74 = zext<64>(%71);
let %75 = zext<64>(~%71);
let %76 = %33 + %69;
let %77 = concat(zext<63>(%9), 0:1);
let %78 = %28 + %24;
let %79 = select(%30, 9:64, 2);
let %80 = %37 + %41;
let %81 = %80 + %45;
let %82 = %81 + %65;
let %83 = zext<64>(%43);
let %84 = select(%63, 9:64, 3);
(%70 + select(%71, %73, %73 + 0x6272c0a9c639abb8) == 0x9d40e5a6867a7e4c) & (%74 + select(%72, %74, 1) + select(%72, %75, %74) + select(%72, 1, %75) + zext<64>(%70 <u %76) + zext<64>(%76 <u %20) + zext<64>(%20 <u %12) + zext<64>(~%5 <u %11) + select(%2, select(%3, 10:64, 4), zext<64>(%3) * 5) + select(%6, %77 | 1, %77) + zext<64>(~%16 <u %19) + select(%13, concat(zext<61>(%14), -2:3), select(%14, 7:64, 0)) + select(%17, 7:64, 0) + zext<64>(%78 + %32 + %69 <u %78) + zext<64>(~%24 <u %28) + select(%22, select(%21, 13:64, 4), select(%21, 8:64, 0)) + select(%25, select(%26, 13:64, 7), zext<64>(%26) * 5) + zext<64>(~%32 <u %69) + select(%29, %79, %79 - 2) + zext<64>(%81 + %49 + %53 + %57 + %61 + %65 <u %82) + zext<64>(%82 <u %80) + zext<64>(~%37 <u %41) + select(%34, select(%35, 6:64, 0), zext<64>(%35) * 5) + select(%39, select(%38, 10:64, 2), select(%38, 7:64, 0)) + zext<64>(~%45 <u %65) + select(%42, (%83 << 1) + 6, %83) + zext<64>(%53 + %49 + %57 + %61 <u %61 + %49) + zext<64>(~%49 <u %61) + select(%47, select(%46, 10:64, 2), select(%46, 7:64, 0)) + zext<64>(~%57 <u %53) + select(%50, concat(zext<61>(%51), -1:3), select(%51, 7:64, 0)) + zext<64>(~%54) * -1 + select(%55, 1:64, 7) + select(%58, select(%59, 8:64, 1), select(%59, 6:64, 0)) + select(%62, %84, %84 - 3) + select(%67, select(%66, 15:64, 8), select(%66, 6:64, 0)) + concat(zext<63>(%71), 0:1) == 113)
"#;
        let (mut cx, out) = run_sweep(src.trim());
        assert!(
            cx.dag_size(&[out], 12).is_ok(),
            "expected compact solved guard, got: {}",
            cx.display(out)
        );
    }

    #[test]
    fn solves_narrow_carry_split_and_zero_overflow_cluster_merge() {
        // Group 0 and Group 1 have 64-bit low parts whose maxima sum to < u64::MAX, so `%a = %0 + %1`
        // needs no explicit carry term and merges via the zero-overflow carry-operand check.
        // Word `%w = (y:16 & 0xff) + 0x34a1:16` exercises `solve_carry_split` for `nw = 8 < w = 16`.
        let w: [u128; 10] = [
            0x2_0123456789abcdefu128,
            0x5_0fedcba987654321u128,
            0x1_0111222233334445u128,
            0x4_0555666677778889u128,
            0x3_9abcdef012345678u128,
            0x6_fedcba9876543211u128,
            0x2_a1b2c3d4e5f60718u128,
            0x7_9081726354453627u128,
            0x5_deadbeefcafebabeu128,
            0x3_8877665544332211u128,
        ];
        let sum_for_w = |w_val: u16| -> u128 {
            let mut acc = 0u128;
            for (b, &wb) in w.iter().enumerate() {
                if (w_val >> b) & 1 != 0 {
                    acc = acc.wrapping_add(wb);
                }
            }
            acc
        };
        let mk_group = |k: usize| {
            let w00 = 0u128;
            let w01 = w[2 * k];
            let w10 = w[2 * k + 1];
            let w11 = w01.wrapping_add(w10);
            let lo = format!(
                "select(extract<{}, 1>(%90), select(extract<{}, 1>(%90), {:#x}:64, {:#x}), select(extract<{}, 1>(%90), {:#x}:64, {:#x}))",
                2 * k, 2 * k + 1, w11 as u64, w01 as u64, 2 * k + 1, w10 as u64, w00 as u64
            );
            let hi = format!(
                "select(extract<{}, 1>(%90), select(extract<{}, 1>(%90), {:#x}:64, {:#x}), select(extract<{}, 1>(%90), {:#x}:64, {:#x}))",
                2 * k, 2 * k + 1, (w11 >> 64) as u64, (w01 >> 64) as u64, 2 * k + 1, (w10 >> 64) as u64, (w00 >> 64) as u64
            );
            (lo, hi)
        };
        let (l0, h0) = mk_group(0);
        let (l1, h1) = mk_group(1);
        let (l2, h2) = mk_group(2);
        let (l3, h3) = mk_group(3);
        let (l4, h4) = mk_group(4);

        let y_sol: u16 = 0x70;
        let w_sol = y_sol.wrapping_add(0x34a1); // 0x3511 (carry = 1 out of low 8 bits)
        let target = sum_for_w(w_sol);
        let src = format!(
            "let %90 = (y:16 & 0xff) + 0x34a1:16; \
             let %0 = {l0}; let %1 = {l1}; let %2 = {l2}; let %3 = {l3}; let %4 = {l4}; \
             let %91 = %0 + %1; let %92 = %2 + %3; let %93 = %91 + %92; let %94 = %93 + %4; \
             let %95 = ({h0}) + ({h1}) + ({h2}) + ({h3}) + ({h4}) \
                       + zext<64>(%92 <u %2) + zext<64>(%93 <u %91) + zext<64>(%94 <u %93); \
             ((%94 ^ {:#x}) | (%95 ^ {:#x})) == 0",
            target as u64,
            (target >> 64) as u64
        );
        let (mut cx, out) = run_sweep(&src);
        for v in [0u64, 0x6f, 0x70, 0x71, 0xff, 0x1370, 0xff70, 0xff71] {
            let got = cx
                .eval(&[out], &[("y".into(), BitVec::from_u64(Width::W16, v).unwrap())][..])
                .unwrap()[0];
            assert_eq!(!got.is_zero(), (v & 0xff) == u64::from(y_sol), "mismatch at y={v:#x}");
        }
        assert!(
            cx.dag_size(&[out], 10).is_ok(),
            "expected compact carry-split guard, got: {}",
            cx.display(out)
        );

        // Inconsistent carry combination (`hi = 0x34` requires `w_low >= 0xa1`, paired with `w_low = 0x11`)
        // must be rejected as unsatisfiable (`0:1`).
        let fake_target = sum_for_w(0x3411);
        let src_fake = format!(
            "let %90 = (y:16 & 0xff) + 0x34a1:16; \
             let %0 = {l0}; let %1 = {l1}; let %2 = {l2}; let %3 = {l3}; let %4 = {l4}; \
             let %91 = %0 + %1; let %92 = %2 + %3; let %93 = %91 + %92; let %94 = %93 + %4; \
             let %95 = ({h0}) + ({h1}) + ({h2}) + ({h3}) + ({h4}) \
                       + zext<64>(%92 <u %2) + zext<64>(%93 <u %91) + zext<64>(%94 <u %93); \
             ((%94 ^ {:#x}) | (%95 ^ {:#x})) == 0",
            fake_target as u64,
            (fake_target >> 64) as u64
        );
        let (cx2, out2) = run_sweep(&src_fake);
        assert!(matches!(cx2.view(out2).unwrap(), View::Const(v) if v.is_zero()));
    }
}
