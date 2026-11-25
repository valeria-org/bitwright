//! Proofs for a sampled one-bit root. A product bit sees only the low `bit + 1` bits of
//! each factor. One factor is often an integer constant on those bits, written as a sum
//! of Boolean functions of differently shifted, rotated and sliced words.

use super::{Counter, Runner, Stop};
use crate::expr::{Context, OpCode};
use crate::{BinOp, BitVec};

// A lane is a Boolean function of at most six distinct (node, bit) pairs. Treating a bit
// we cannot trace as independent can only prevent a proof. The same source bit, including
// through a rotate or a sign extension, must get the same truth-table column.
const VAR: [u64; 6] = [
    0xaaaa_aaaa_aaaa_aaaa,
    0xcccc_cccc_cccc_cccc,
    0xf0f0_f0f0_f0f0_f0f0,
    0xff00_ff00_ff00_ff00,
    0xffff_0000_ffff_0000,
    0xffff_ffff_0000_0000,
];

pub(super) struct Work {
    pub(super) left: u64,
    projections: crate::hash::IdMap<u32, Option<Projection>>,
}
impl Work {
    pub(super) fn new(left: u64) -> Self {
        Self { left, projections: Default::default() }
    }

    pub(super) fn take(&mut self, n: u64) -> Option<()> {
        self.left = self.left.checked_sub(n)?;
        Some(())
    }
}

fn scalar(cx: &Context, n: u32) -> Option<u64> {
    cx.const_val(n)?.to_u64()
}

// Flatten the additive layer in Z/2^64. It is used only at widths <= 64 and ultimately
// reduced modulo the requested power of two. No arithmetic is pushed through a bitwise op.
pub(super) fn terms(
    cx: &Context,
    i: u32,
    k: u64,
    bias: &mut u64,
    out: &mut Vec<(u32, u64)>,
    depth: u8,
    keep_not: bool,
    work: &mut Work,
) -> Option<()> {
    terms_at(cx, i, k, bias, out, depth, keep_not, None, 64, work)
}

fn terms_at(
    cx: &Context, i: u32, k: u64, bias: &mut u64, out: &mut Vec<(u32, u64)>,
    depth: u8, keep_not: bool, cut: Option<u32>, mod_bits: u16, work: &mut Work,
) -> Option<()> {
    work.take(1)?;
    let d = depth.checked_sub(1)?;
    let n = cx.node(i);
    let mod_mask = if mod_bits >= 64 {
        u64::MAX
    } else if mod_bits == 0 {
        0
    } else {
        (1u64 << mod_bits) - 1
    };
    match n.op {
        _ if Some(i) == cut => push_term(out, i, k)?,
        OpCode::Const => *bias = bias.wrapping_add(k.wrapping_mul(scalar(cx, i)?)),
        OpCode::Add | OpCode::Sub => {
            terms_at(cx, n.a, k, bias, out, d, keep_not, cut, mod_bits, work)?;
            terms_at(
                cx,
                n.b,
                if n.op == OpCode::Add {
                    k
                } else {
                    k.wrapping_neg()
                },
                bias,
                out,
                d,
                keep_not,
                cut,
                mod_bits,
                work,
            )?;
        }
        OpCode::Not | OpCode::Neg if !keep_not || n.op == OpCode::Neg => {
            if n.op == OpCode::Not {
                *bias = bias.wrapping_sub(k);
            }
            terms_at(cx, n.a, k.wrapping_neg(), bias, out, d, keep_not, cut, mod_bits, work)?;
        }
        OpCode::Mul if scalar(cx, n.b).is_some() => {
            let c = scalar(cx, n.b)?;
            let next_mod = mod_bits.saturating_sub(c.trailing_zeros() as u16);
            if next_mod > 0 {
                terms_at(
                    cx,
                    n.a,
                    k.wrapping_mul(c),
                    bias,
                    out,
                    d,
                    keep_not,
                    cut,
                    next_mod,
                    work,
                )?;
            }
        }
        OpCode::Mul if scalar(cx, n.a).is_some() => {
            let c = scalar(cx, n.a)?;
            let next_mod = mod_bits.saturating_sub(c.trailing_zeros() as u16);
            if next_mod > 0 {
                terms_at(
                    cx,
                    n.b,
                    k.wrapping_mul(c),
                    bias,
                    out,
                    d,
                    keep_not,
                    cut,
                    next_mod,
                    work,
                )?;
            }
        }
        OpCode::Shl if scalar(cx, n.b).is_some() => {
            let count = scalar(cx, n.b)?;
            let next_mod = mod_bits.saturating_sub(count.min(64) as u16);
            if count < 64 && next_mod > 0 {
                terms_at(cx, n.a, k << count, bias, out, d, keep_not, cut, next_mod, work)?;
            }
        }
        OpCode::Extract if mod_bits <= n.width && n.b == 0 && cx.node(n.a).width <= 64 => {
            terms_at(cx, n.a, k, bias, out, d, keep_not, cut, mod_bits, work)?;
        }
        OpCode::Zext if mod_bits <= cx.node(n.a).width && cx.node(n.a).width <= 64 => {
            terms_at(cx, n.a, k, bias, out, d, keep_not, cut, mod_bits, work)?;
        }
        OpCode::And
            if mod_bits < 64
                && scalar(cx, n.b).is_some_and(|m| (m & mod_mask) == mod_mask) =>
        {
            terms_at(cx, n.a, k, bias, out, d, keep_not, cut, mod_bits, work)?;
        }
        OpCode::And
            if mod_bits < 64
                && scalar(cx, n.a).is_some_and(|m| (m & mod_mask) == mod_mask) =>
        {
            terms_at(cx, n.b, k, bias, out, d, keep_not, cut, mod_bits, work)?;
        }
        _ => push_term(out, i, k)?,
    }
    Some(())
}

fn push_term(out: &mut Vec<(u32, u64)>, i: u32, k: u64) -> Option<()> {
    if out.len() == 192 { return None; }
    out.push((i, k));
    Some(())
}

/// Merge identical additive terms and drop any whose combined coefficient vanishes
/// modulo `2^bits` (`mask = (1 << bits) - 1`). Cancelling equal terms up front avoids
/// spending lane/table atom slots on unrestricted words that disappear algebraically.
pub(super) fn cancel_parts(parts: &mut Vec<(u32, u64)>, mask: u64, work: &mut Work) -> Option<()> {
    if parts.len() <= 1 {
        parts.retain(|&(_, k)| k & mask != 0);
        return Some(());
    }
    work.take((parts.len() * 6) as u64)?;
    parts.sort_unstable_by_key(|&(id, _)| id);
    parts.dedup_by(|next, prev| {
        if next.0 != prev.0 {
            return false;
        }
        prev.1 = prev.1.wrapping_add(next.1);
        true
    });
    parts.retain(|&(_, k)| k & mask != 0);
    Some(())
}

/// `bias + Σ c_t·bit(x,t)` for a sum of masked multiples of one word. A coefficient
/// `-2^b` is `+2^b` on the complemented source bit, minus `2^b` in the bias. Wherever
/// the resulting fields don't overlap there's no carry: those output bits are wires.
/// This recovers, for example, the bits of `K - ((x << s) - ((x & M) << (s+1)))`
/// without treating an arithmetic spelling of a bit permutation as a new source.
struct Projection {
    source: u32,
    bits: [u8; 64], // source index, or 64 for a fixed bit
    invert: u64,
    end: u16,
}

fn projection(cx: &Context, i: u32, work: &mut Work) -> Option<Projection> {
    let w = cx.node(i).width;
    if w > 64 {
        return None;
    }
    let mask = u64::MAX >> (64 - w);
    let mut bias = 0u64;
    let mut parts = Vec::new();
    terms(cx, i, 1, &mut bias, &mut parts, 24, false, work)?;
    if parts.len() > 8 {
        return None;
    }
    let mut source = None;
    let mut weights = [0u64; 64];
    for (part, k) in parts {
        let n = cx.node(part);
        let (x, mut m) = if n.op == OpCode::And {
            if let Some(m) = scalar(cx, n.b) {
                (n.a, m)
            } else if let Some(m) = scalar(cx, n.a) {
                (n.b, m)
            } else {
                (part, mask)
            }
        } else {
            (part, mask)
        };
        if source.replace(x).is_some_and(|s| s != x) {
            return None;
        }
        work.take(u64::from(m.count_ones()))?;
        while m != 0 {
            let j = m.trailing_zeros();
            weights[j as usize] = weights[j as usize].wrapping_add(k << j);
            m &= m - 1;
        }
    }
    let mut bits = [64; 64];
    let mut used = 0u64;
    let mut neg = 0u64;
    let mut end = w;
    for (j, coeff) in weights[..usize::from(w)].iter().enumerate() {
        let c = coeff & mask;
        if c == 0 {
            continue;
        }
        let b = c.trailing_zeros();
        let v = 1 << b;
        if used & v != 0 || (c != v && c != (0u64.wrapping_sub(v) & mask)) {
            end = end.min(b as u16);
            continue;
        }
        used |= v;
        bits[b as usize] = j as u8;
        if c != v {
            neg |= v;
            bias = bias.wrapping_sub(v);
        }
    }
    // The first overlap with the bias only toggles that bit. Above it a carry may arrive.
    end = end.min((used & bias).trailing_zeros() as u16 + 1);
    Some(Projection {
        source: source?,
        bits,
        invert: bias ^ neg,
        end,
    })
}

fn affine_key(cx: &Context, mut i: u32) -> (u32, u64) {
    let w = cx.node(i).width;
    if w == 0 || w > 64 {
        return (i, 0);
    }
    let mask = u64::MAX >> (64 - w);
    let mut off = 0u64;
    for _ in 0..8 {
        let n = cx.node(i);
        match n.op {
            OpCode::Add => {
                if let Some(c) = scalar(cx, n.b) {
                    off = off.wrapping_add(c);
                    i = n.a;
                } else if let Some(c) = scalar(cx, n.a) {
                    off = off.wrapping_add(c);
                    i = n.b;
                } else {
                    break;
                }
            }
            OpCode::Sub => {
                if let Some(c) = scalar(cx, n.b) {
                    off = off.wrapping_sub(c);
                    i = n.a;
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
    (i, off & mask)
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum LaneKey {
    Bit(u32, u64, u16),
    Eq((u32, u64), (u32, u64)),
}

impl Default for LaneKey {
    fn default() -> Self {
        Self::Bit(0, 0, 0)
    }
}

#[derive(Default)]
struct Lane {
    keys: [LaneKey; 6],
    len: usize,
    memo: crate::hash::IdMap<(u32, u16), u64>,
}
impl Lane {
    fn clear(&mut self) {
        self.len = 0;
        self.memo.clear();
    }

    fn sym(&mut self, cx: &Context, i: u32, j: u16) -> Option<u64> {
        let n = cx.node(i);
        let key = if j == 0 && n.op == OpCode::Eq {
            let ka = affine_key(cx, n.a);
            let kb = affine_key(cx, n.b);
            if ka <= kb {
                LaneKey::Eq(ka, kb)
            } else {
                LaneKey::Eq(kb, ka)
            }
        } else {
            let (base, off) = affine_key(cx, i);
            LaneKey::Bit(base, off, j)
        };
        let at = match self.keys[..self.len].iter().position(|k| *k == key) {
            Some(at) => at,
            None => {
                *self.keys.get_mut(self.len)? = key;
                self.len += 1;
                self.len - 1
            }
        };
        Some(VAR[at])
    }

    fn bit(&mut self, cx: &Context, i: u32, j: u16, depth: u8, work: &mut Work) -> Option<u64> {
        work.take(1)?;
        if let Some(&v) = self.memo.get(&(i, j)) {
            return Some(v);
        }
        let x = self.bit_uncached(cx, i, j, depth, work)?;
        self.memo.insert((i, j), x);
        Some(x)
    }

    fn bit_uncached(&mut self, cx: &Context, i: u32, j: u16, depth: u8, work: &mut Work) -> Option<u64> {
        let d = depth.checked_sub(1)?;
        let n = cx.node(i);
        let w = n.width;
        if matches!(n.op, OpCode::Add | OpCode::Sub | OpCode::Neg) && w <= 64 {
            if !work.projections.contains_key(&i) {
                let p = projection(cx, i, work);
                work.projections.insert(i, p);
            }
            if let Some(p) = &work.projections[&i]
                && j < p.end
            {
                let (src, index, flip) = (p.source, p.bits[j as usize], (p.invert >> j) & 1 != 0);
                let col = if index == 64 {
                    0
                } else {
                    self.bit(cx, src, u16::from(index), d, work)?
                };
                return Some(if flip { !col } else { col });
            }
        }
        let x = match n.op {
            OpCode::Const => {
                if cx.const_val(i)?.bit(j)? {
                    u64::MAX
                } else {
                    0
                }
            }
            // Adding or subtracting a constant `c` has zero carry into every bit `j <= tz(c)`:
            // bits below `tz(c)` pass through unchanged, and bit `tz(c)` flips.
            OpCode::Add if scalar(cx, n.b).is_some() || scalar(cx, n.a).is_some() => {
                let (other, c) = match scalar(cx, n.b) {
                    Some(c) => (n.a, c),
                    None => (n.b, scalar(cx, n.a)?),
                };
                if c == 0 {
                    self.bit(cx, other, j, d, work)?
                } else {
                    let tz = c.trailing_zeros() as u16;
                    if j < tz {
                        self.bit(cx, other, j, d, work)?
                    } else if j == tz {
                        !self.bit(cx, other, j, d, work)?
                    } else {
                        self.sym(cx, i, j)?
                    }
                }
            }
            OpCode::Sub if scalar(cx, n.b).is_some() => {
                let c = scalar(cx, n.b)?;
                if c == 0 {
                    self.bit(cx, n.a, j, d, work)?
                } else {
                    let tz = c.trailing_zeros() as u16;
                    if j < tz {
                        self.bit(cx, n.a, j, d, work)?
                    } else if j == tz {
                        !self.bit(cx, n.a, j, d, work)?
                    } else {
                        self.sym(cx, i, j)?
                    }
                }
            }
            OpCode::Not => !self.bit(cx, n.a, j, d, work)?,
            OpCode::And | OpCode::Or | OpCode::Xor => {
                // The constructors put constant masks on the right. A masked-out bit
                // has no source: don't spend a free column (or fuel) tracing it.
                if let Some(k) = scalar(cx, n.b) {
                    let set = j < 64 && k & (1u64 << j) != 0;
                    if n.op == OpCode::Xor {
                        let a = self.bit(cx, n.a, j, d, work)?;
                        return Some(if set { !a } else { a });
                    }
                    if (n.op == OpCode::Or) == set {
                        return Some(if set { u64::MAX } else { 0 });
                    }
                    return self.bit(cx, n.a, j, d, work);
                }
                let a = self.bit(cx, n.a, j, d, work)?;
                if (n.op == OpCode::Or && a == u64::MAX) || (n.op == OpCode::And && a == 0) {
                    return Some(a);
                }
                let b = self.bit(cx, n.b, j, d, work)?;
                match n.op {
                    OpCode::And => a & b,
                    OpCode::Or => a | b,
                    _ => a ^ b,
                }
            }
            OpCode::Select => {
                let const_arm = scalar(cx, n.b).is_some() || scalar(cx, n.c).is_some();
                if const_arm {
                    let a = self.bit(cx, n.b, j, d, work)?;
                    let b = self.bit(cx, n.c, j, d, work)?;
                    if a == b {
                        a
                    } else {
                        let (cond, flip) = if cx.node(n.a).op == OpCode::Not {
                            (cx.node(n.a).a, true)
                        } else {
                            (n.a, false)
                        };
                        let c = self.sym(cx, cond, 0)?;
                        let c = if flip { !c } else { c };
                        (c & a) | (!c & b)
                    }
                } else {
                    // For non-constant `select` arms, try a shallow bit-trace on a saved
                    // snapshot of `self.vars`; if the arms pull in too many variables or
                    // run out of shallow depth, fall back to treating `select` as one atom
                    // instead of aborting the whole lane proof.
                    let (saved_keys, saved_len) = (self.keys, self.len);
                    let sub_d = d.min(4);
                    let traced = (|| -> Option<u64> {
                        let a = self.bit(cx, n.b, j, sub_d, work)?;
                        let b = self.bit(cx, n.c, j, sub_d, work)?;
                        if a == b {
                            return Some(a);
                        }
                        let (cond, flip) = if cx.node(n.a).op == OpCode::Not {
                            (cx.node(n.a).a, true)
                        } else {
                            (n.a, false)
                        };
                        let c = self.sym(cx, cond, 0)?;
                        let c = if flip { !c } else { c };
                        Some((c & a) | (!c & b))
                    })();
                    match traced {
                        Some(v) => v,
                        None => {
                            self.keys = saved_keys;
                            self.len = saved_len;
                            self.sym(cx, i, j)?
                        }
                    }
                }
            }
            OpCode::Zext | OpCode::Sext => {
                let sw = cx.node(n.a).width;
                if j >= sw && n.op == OpCode::Zext {
                    0
                } else {
                    self.bit(cx, n.a, j.min(sw - 1), d, work)?
                }
            }
            OpCode::Extract => self.bit(cx, n.a, j + n.b as u16, d, work)?,
            OpCode::Concat => {
                let lo = cx.node(n.b).width;
                if j < lo {
                    self.bit(cx, n.b, j, d, work)?
                } else {
                    self.bit(cx, n.a, j - lo, d, work)?
                }
            }
            OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR
                if scalar(cx, n.b).is_some() =>
            {
                let k = scalar(cx, n.b)?;
                let (j, w) = (u64::from(j), u64::from(w));
                let src = match n.op {
                    OpCode::Shl if j >= k => j - k,
                    OpCode::LShr if k < w - j => j + k,
                    OpCode::AShr => j.saturating_add(k).min(w - 1),
                    OpCode::RotL => (j + w - k % w) % w,
                    OpCode::RotR => (j + k % w) % w,
                    _ => return Some(0),
                };
                self.bit(cx, n.a, src as u16, d, work)?
            }
            OpCode::Mul if scalar(cx, n.b).is_some() || scalar(cx, n.a).is_some() => {
                let (x, k) = match scalar(cx, n.b) {
                    Some(k) => (n.a, k),
                    None => (n.b, scalar(cx, n.a)?),
                };
                let tz = k.trailing_zeros() as u16;
                if j < tz {
                    0
                } else if j == tz && k != 0 {
                    self.bit(cx, x, 0, d, work)?
                } else {
                    return self.sym(cx, i, j);
                }
            }
            OpCode::Mul if j == 0 => {
                self.bit(cx, n.a, 0, d, work)? & self.bit(cx, n.b, 0, d, work)?
            }
            _ => return self.sym(cx, i, j),
        };
        Some(x)
    }
}

fn constant(
    cx: &Context, x: u32, bits: u16, parts: &mut Vec<(u32, u64)>, work: &mut Work,
) -> Option<u64> {
    if !matches!(cx.node(x).op, OpCode::Add | OpCode::Sub | OpCode::Neg) {
        return None;
    }
    let mask = u64::MAX >> (64 - bits);
    let mut sum = 0u64;
    parts.clear();
    terms(cx, x, 1, &mut sum, parts, 96, false, work)?;
    cancel_parts(parts, mask, work)?;
    Some(sum.wrapping_add(constant_lanes(cx, parts, bits, work)?) & mask)
}

pub(super) fn constant_parts(cx: &Context, parts: &[(u32, u64)], bits: u16, left: &mut u64) -> Option<u64> {
    if !(1..=64).contains(&bits) || parts.len() > 96 || parts.iter().any(|&(i, _)| cx.node(i).width < bits) {
        return None;
    }
    let mut work = Work { left: *left, projections: Default::default() };
    let result = constant_lanes(cx, parts, bits, &mut work);
    *left = work.left;
    result
}

/// Prove that a width-`<= 64` node `root` equals constant `expected` by flattening its
/// additive layer and checking each bit column independently.
pub(super) fn constant_word(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    root: u32,
    expected: &BitVec,
) -> Result<bool, Stop> {
    let w = cx.wid(root);
    let Some(want) = expected.to_u64() else {
        return Ok(false);
    };
    if w == 0 || w > 64 {
        return Ok(false);
    }
    const LIMIT: u64 = 4096;
    let budget = (r.meter.left_in(|b| b.pass_work) / 8).min(LIMIT);
    let mut work = Work::new(budget);
    let proved = (|| {
        let mask = u64::MAX >> (64 - w);
        let mut parts = Vec::new();
        let mut bias = 0u64;
        terms(cx, root, 1, &mut bias, &mut parts, 64, false, &mut work)?;
        cancel_parts(&mut parts, mask, &mut work)?;
        let value = constant_lanes(cx, &parts, w, &mut work)?;
        Some(bias.wrapping_add(value) & mask == want & mask)
    })();
    r.meter.charge(Counter::PassWork, budget - work.left)?;
    Ok(proved == Some(true))
}

/// Sound over-approximation of the bits that can be 1 in `i` (any 0 bit in the result is
/// guaranteed to be 0 for all inputs).
fn possible_ones(cx: &Context, i: u32, depth: u8) -> u64 {
    let w = cx.node(i).width;
    if w == 0 || w > 64 {
        return u64::MAX;
    }
    let full = u64::MAX >> (64 - w);
    if depth == 0 {
        return full;
    }
    let n = cx.node(i);
    let m = match n.op {
        OpCode::Const => scalar(cx, i).unwrap_or(full),
        OpCode::Zext => possible_ones(cx, n.a, depth - 1),
        OpCode::Extract if cx.node(n.a).width <= 64 => {
            let lo = n.b;
            let src = possible_ones(cx, n.a, depth - 1);
            if lo < 64 { (src >> lo) & full } else { 0 }
        }
        OpCode::And => possible_ones(cx, n.a, depth - 1) & possible_ones(cx, n.b, depth - 1),
        OpCode::Or | OpCode::Xor => {
            possible_ones(cx, n.a, depth - 1) | possible_ones(cx, n.b, depth - 1)
        }
        OpCode::Shl => match scalar(cx, n.b) {
            Some(s) if s < 64 => (possible_ones(cx, n.a, depth - 1) << s) & full,
            Some(_) => 0,
            None => full,
        },
        OpCode::LShr => match scalar(cx, n.b) {
            Some(s) if s < 64 => possible_ones(cx, n.a, depth - 1) >> s,
            Some(_) => 0,
            None => full,
        },
        OpCode::Add => {
            let a = possible_ones(cx, n.a, depth - 1);
            let b = possible_ones(cx, n.b, depth - 1);
            if a & b == 0 {
                a | b
            } else if let Some(c) = scalar(cx, n.a)
                && b.is_power_of_two()
            {
                c | c.wrapping_add(b)
            } else if let Some(c) = scalar(cx, n.b)
                && a.is_power_of_two()
            {
                c | c.wrapping_add(a)
            } else {
                let tz = a.trailing_zeros().min(b.trailing_zeros());
                if tz >= 64 { 0 } else { full << tz }
            }
        }
        OpCode::Sub => {
            let a = possible_ones(cx, n.a, depth - 1);
            let b = possible_ones(cx, n.b, depth - 1);
            if let Some(c) = scalar(cx, n.a)
                && b & !c == 0
            {
                c
            } else if let Some(c) = scalar(cx, n.a)
                && b.is_power_of_two()
            {
                c | c.wrapping_sub(b)
            } else if let Some(c) = scalar(cx, n.b)
                && a.is_power_of_two()
            {
                c.wrapping_neg() | a.wrapping_sub(c)
            } else {
                let tz = a.trailing_zeros().min(b.trailing_zeros());
                if tz >= 64 { 0 } else { full << tz }
            }
        }
        OpCode::Neg => {
            let tz = possible_ones(cx, n.a, depth - 1).trailing_zeros();
            if tz >= 64 { 0 } else { full << tz }
        }
        OpCode::Mul => {
            let tz = possible_ones(cx, n.a, depth - 1)
                .trailing_zeros()
                .saturating_add(possible_ones(cx, n.b, depth - 1).trailing_zeros());
            if tz >= 64 { 0 } else { full << tz }
        }
        OpCode::Select => possible_ones(cx, n.b, depth - 1) | possible_ones(cx, n.c, depth - 1),
        _ => full,
    };
    m & full
}

/// Upper bound on the active bit width of `i` (all bits at positions `>= ret` are guaranteed 0).
fn active_bits(cx: &Context, i: u32, depth: u8) -> u16 {
    let w = cx.node(i).width;
    if w > 64 {
        return w;
    }
    (64 - possible_ones(cx, i, depth).leading_zeros()) as u16
}

/// Distribute `Mul(Add/Sub(u, Const(c)), v)` when `Mul(u, v)` (or `Mul(v, u)`) also appears
/// in `parts`, rewriting the factored product into `(existing_mul, ±k)` plus `terms_at(v, k * c)`
/// so `cancel_parts` cancels the shared product term.
fn distribute_matching_prods(
    cx: &Context,
    parts: &mut Vec<(u32, u64)>,
    bias: &mut u64,
    mod_bits: u16,
    work: &mut Work,
) -> Option<()> {
    let mut existing: Vec<(u32, u32, u32)> = Vec::new();
    for &(id, _) in parts.iter() {
        let n = cx.node(id);
        if n.op == OpCode::Mul {
            let (lo, hi) = if n.a <= n.b { (n.a, n.b) } else { (n.b, n.a) };
            existing.push((lo, hi, id));
        }
    }
    if existing.is_empty() {
        return Some(());
    }
    let split_affine = |x: u32| -> Option<(u32, bool, u64)> {
        let n = cx.node(x);
        match n.op {
            OpCode::Add => {
                if let Some(c) = scalar(cx, n.b) {
                    Some((n.a, false, c))
                } else {
                    scalar(cx, n.a).map(|c| (n.b, false, c))
                }
            }
            OpCode::Sub => {
                if let Some(c) = scalar(cx, n.b) {
                    Some((n.a, false, c.wrapping_neg()))
                } else {
                    scalar(cx, n.a).map(|c| (n.b, true, c))
                }
            }
            _ => None,
        }
    };
    let mut extra: Vec<(u32, u64)> = Vec::new();
    for slot in parts.iter_mut() {
        let (id, k) = *slot;
        let n = cx.node(id);
        if n.op != OpCode::Mul {
            continue;
        }
        let mut matched = None;
        for (lhs, rhs) in [(n.a, n.b), (n.b, n.a)] {
            if let Some((u, neg_u, c)) = split_affine(lhs) {
                let key = if u <= rhs { (u, rhs) } else { (rhs, u) };
                if let Some(&(_, _, prod_id)) =
                    existing.iter().find(|&&(a, b, pid)| (a, b) == key && pid != id)
                {
                    matched = Some((prod_id, neg_u, rhs, c));
                    break;
                }
            }
        }
        if let Some((prod_id, neg_u, v, c)) = matched {
            *slot = (prod_id, if neg_u { k.wrapping_neg() } else { k });
            terms_at(cx, v, k.wrapping_mul(c), bias, &mut extra, 32, false, None, mod_bits, work)?;
        }
    }
    for (id, k) in extra {
        push_term(parts, id, k)?;
    }
    // Also collapse groups of products `k_i * (A_i * v)` sharing a common factor `v` when
    // `Σ k_i * A_i` reduces to a constant `c` via `constant_lanes`, replacing the group with `c * v`.
    let mask = if mod_bits >= 64 {
        u64::MAX
    } else if mod_bits == 0 {
        0
    } else {
        (1u64 << mod_bits) - 1
    };
    let mut prod_factors: Vec<(usize, u32, u32)> = Vec::new();
    for (idx, (id, k)) in parts.iter_mut().enumerate() {
        if *k & mask == 0 {
            continue;
        }
        let n = cx.node(*id);
        if n.op == OpCode::Mul {
            if let Some((v, fs)) = super::super::linear::scaled_factors(cx, *id)
                && let &[fa, fb] = fs.as_slice()
            {
                *k = k.wrapping_mul(v.limbs()[0]) & mask;
                if *k != 0 {
                    prod_factors.push((idx, fa, fb));
                }
            } else {
                prod_factors.push((idx, n.a, n.b));
            }
        }
    }
    if prod_factors.len() >= 2 {
        let mut seen_v: Vec<u32> = Vec::new();
        let mut extra_v: Vec<(u32, u64)> = Vec::new();
        for &(_, fa, fb) in &prod_factors {
            for v in [fa, fb] {
                if seen_v.contains(&v) {
                    continue;
                }
                seen_v.push(v);
                let members: Vec<(usize, u32)> = prod_factors
                    .iter()
                    .filter_map(|&(idx, a, b)| {
                        if parts[idx].1 & mask == 0 {
                            return None;
                        }
                        if a == v {
                            Some((idx, b))
                        } else if b == v {
                            Some((idx, a))
                        } else {
                            None
                        }
                    })
                    .collect();
                if members.len() < 2 {
                    continue;
                }
                let mut cbias = 0u64;
                let mut cparts: Vec<(u32, u64)> = Vec::new();
                let mut ok = true;
                for &(idx, other) in &members {
                    if terms_at(
                        cx,
                        other,
                        parts[idx].1,
                        &mut cbias,
                        &mut cparts,
                        32,
                        false,
                        None,
                        mod_bits,
                        work,
                    )
                    .is_none()
                    {
                        ok = false;
                        break;
                    }
                }
                if !ok || cancel_parts(&mut cparts, mask, work).is_none() {
                    continue;
                }
                let Some(val) = constant_lanes(cx, &cparts, mod_bits, work) else {
                    continue;
                };
                let c = cbias.wrapping_add(val) & mask;
                for &(idx, _) in &members {
                    parts[idx].1 = 0;
                }
                if c != 0 {
                    terms_at(cx, v, c, bias, &mut extra_v, 32, false, None, mod_bits, work)?;
                }
            }
        }
        for (id, k) in extra_v {
            push_term(parts, id, k)?;
        }
    }
    Some(())
}

/// If a plain linear term `(base, k)` in `parts` also appears inside a bitwise operand of
/// `parts` shifted by a unique constant offset (`shifted = base + off`), rewrite `k * base`
/// as `k * shifted - k * off`. This is exact in Z/2^W and lets `Lane` share one bit column
/// for `shifted` instead of treating `base` and `base + off` as unrelated variables.
fn rebase_shifted_terms(
    cx: &Context,
    parts: &mut [(u32, u64)],
    bias: &mut u64,
    width: u16,
    work: &mut Work,
) -> Option<()> {
    let mut shifted: Vec<(u32, u64, u32)> = Vec::new();
    let mut stack: Vec<(u32, u8)> = Vec::new();
    for &(id, _) in parts.iter() {
        if !matches!(cx.node(id).op, OpCode::Sym) {
            stack.push((id, 6));
        }
    }
    let mut visited = 0u32;
    while let Some((i, depth)) = stack.pop() {
        visited += 1;
        if visited > 64 {
            break;
        }
        work.take(1)?;
        let n = cx.node(i);
        if n.width == width && matches!(n.op, OpCode::Add | OpCode::Sub) {
            let (base, off) = affine_key(cx, i);
            if base != i && off != 0 && !shifted.iter().any(|&(b, o, _)| b == base && o == off) {
                shifted.push((base, off, i));
            }
            continue;
        }
        if depth > 0
            && matches!(
                n.op,
                OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not | OpCode::Select
            )
        {
            for c in n.children() {
                stack.push((c, depth - 1));
            }
        }
    }
    if shifted.is_empty() {
        return Some(());
    }
    for slot in parts.iter_mut() {
        let (t, k) = *slot;
        let mut found = None;
        let mut unique = true;
        for &(base, off, node_id) in &shifted {
            if base == t && found.replace((off, node_id)).is_some() {
                unique = false;
                break;
            }
        }
        if unique && let Some((off, node_id)) = found {
            *slot = (node_id, k);
            *bias = bias.wrapping_sub(k.wrapping_mul(off));
        }
    }
    Some(())
}

/// Collect pure-bitwise DAG atoms (up to 5) of `root` (with only uniform 0/-1 constants
/// allowed inside bitwise ops) and evaluate it at all `2^t` corners `{0, mask}^t`.
fn eval_pure_bitwise_corners(
    cx: &Context,
    root: u32,
    atoms: &mut Vec<u32>,
    mask: u64,
    depth: u8,
    work: &mut Work,
) -> Option<[u64; 32]> {
    work.take(1)?;
    if depth == 0 {
        return None;
    }
    let n = cx.node(root);
    if let Some(c) = scalar(cx, root) {
        let cm = c & mask;
        if cm == 0 {
            return Some([0u64; 32]);
        }
        if cm == mask {
            return Some([mask; 32]);
        }
        return None;
    }
    match n.op {
        OpCode::Not => {
            let mut v = eval_pure_bitwise_corners(cx, n.a, atoms, mask, depth - 1, work)?;
            for x in &mut v {
                *x = !*x & mask;
            }
            Some(v)
        }
        OpCode::And | OpCode::Or | OpCode::Xor => {
            let a = eval_pure_bitwise_corners(cx, n.a, atoms, mask, depth - 1, work)?;
            let b = eval_pure_bitwise_corners(cx, n.b, atoms, mask, depth - 1, work)?;
            let mut out = [0u64; 32];
            for i in 0..32 {
                out[i] = match n.op {
                    OpCode::And => a[i] & b[i],
                    OpCode::Or => a[i] | b[i],
                    _ => a[i] ^ b[i],
                };
            }
            Some(out)
        }
        _ => {
            let pos = if let Some(p) = atoms.iter().position(|&x| x == root) {
                p
            } else {
                if atoms.len() >= 5 {
                    return None;
                }
                let p = atoms.len();
                atoms.push(root);
                p
            };
            let mut out = [0u64; 32];
            for (p, slot) in out.iter_mut().enumerate() {
                if (p >> pos) & 1 != 0 {
                    *slot = mask;
                }
            }
            Some(out)
        }
    }
}

/// Collapse equal-magnitude pure-bitwise sub-groups in `parts` (e.g. `(a ^ (a ^ b) & c) + (a & c) - (b & c) == a`)
/// whose exact `2^t` (`t <= 5`) signature is purely affine, then re-expand the exposed atoms via
/// `terms_at` so hidden linear/product terms inside `a` can cancel against the rest of `parts`.
fn collapse_affine_bitwise_groups(
    cx: &Context,
    parts: &mut Vec<(u32, u64)>,
    bias: &mut u64,
    cur_bits: u16,
    work: &mut Work,
) -> Option<bool> {
    let mask = u64::MAX >> (64 - cur_bits);
    let is_bw = |id: u32| matches!(cx.node(id).op, OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not);
    let mag = |k: u64| {
        let km = k & mask;
        km.min(km.wrapping_neg() & mask)
    };
    let mut mags: Vec<u64> = Vec::new();
    for &(t, k) in parts.iter() {
        let m = mag(k);
        if m != 0 && is_bw(t) && !mags.contains(&m) {
            mags.push(m);
        }
    }
    let mut changed = false;
    for m in mags {
        let idxs: Vec<usize> = parts
            .iter()
            .enumerate()
            .filter_map(|(idx, &(t, k))| (is_bw(t) && mag(k) == m).then_some(idx))
            .collect();
        if idxs.len() < 2 {
            continue;
        }
        let mut atoms: Vec<u32> = Vec::new();
        let mut sig = [0u64; 32];
        let mut ok = true;
        for &idx in &idxs {
            let (t, k) = parts[idx];
            let Some(vals) = eval_pure_bitwise_corners(cx, t, &mut atoms, mask, 16, work) else {
                ok = false;
                break;
            };
            for i in 0..32 {
                sig[i] = sig[i].wrapping_add(k.wrapping_mul(vals[i])) & mask;
            }
        }
        if !ok || atoms.is_empty() {
            continue;
        }
        let t = atoms.len();
        let corners = 1usize << t;
        work.take(corners as u64)?;
        // Möbius transform: `-sig[p] = sum_{S <= p} d[S]`, so affine iff `d[S] == 0` for `|S| >= 2`.
        let mut d = [0u64; 32];
        for i in 0..corners {
            d[i] = sig[i].wrapping_neg() & mask;
        }
        let mut bit = 1;
        while bit < corners {
            for p in 0..corners {
                if p & bit != 0 {
                    d[p] = d[p].wrapping_sub(d[p ^ bit]) & mask;
                }
            }
            bit <<= 1;
        }
        if (0..corners).any(|s| s.count_ones() >= 2 && d[s] != 0) {
            continue;
        }
        for &idx in &idxs {
            parts[idx].1 = 0;
        }
        *bias = bias.wrapping_sub(d[0]) & mask;
        for (j, &a) in atoms.iter().enumerate() {
            let c = d[1 << j];
            if c != 0 {
                terms_at(cx, a, c, bias, parts, 64, false, None, cur_bits, work)?;
            }
        }
        changed = true;
    }
    if changed {
        cancel_parts(parts, mask, work)?;
    }
    Some(changed)
}
/// Compare two nodes jointly modulo `2^bits` by flattening their additive layers and checking
/// each bit column independently. When both sides are guaranteed zero above `k < bits`, equality
/// modulo `2^k` implies equality modulo `2^bits`, letting `terms_at` see through `zext`/`trunc`/
/// low masks modulo `2^k`.
pub(in crate::engine::pass) fn equal_lanes(
    r: &mut Runner<'_, '_>, cx: &Context, a: u32, b: u32, bits: u16,
) -> Result<bool, Stop> {
    if bits == 0 {
        return Ok(true);
    }
    let wa = cx.wid(a);
    if wa != cx.wid(b) || wa > 64 || bits > wa {
        return Ok(false);
    }
    let check_bits = bits.min(active_bits(cx, a, 8).max(active_bits(cx, b, 8)));
    if check_bits == 0 {
        return Ok(true);
    }
    let budget = (r.meter.left_in(|b| b.pass_work) / 8).min(1 << 13);
    let mut work = Work::new(budget);
    let equal = (|| {
        let mut cur_bits = check_bits;
        let mut mask = u64::MAX >> (64 - cur_bits);
        let mut parts = Vec::new();
        let mut bias = 0;
        terms_at(cx, a, 1, &mut bias, &mut parts, 64, false, None, cur_bits, &mut work)?;
        terms_at(cx, b, u64::MAX, &mut bias, &mut parts, 64, false, None, cur_bits, &mut work)?;
        distribute_matching_prods(cx, &mut parts, &mut bias, cur_bits, &mut work)?;
        cancel_parts(&mut parts, mask, &mut work)?;
        // Cancel opposite-signed product terms `k * A + (-k) * B` when `A ≡ B (mod 2^cur_bits)`
        // polynomially (e.g. quadratic/polynomial terms mixed into a masked linear MBA).
        if parts.len() >= 2 {
            let mut poly_checks = 0usize;
            let mut removed = vec![false; parts.len()];
            let mut any_removed = false;
            for i in 0..parts.len() {
                if removed[i] || cx.node(parts[i].0).op != OpCode::Mul {
                    continue;
                }
                let ki = parts[i].1 & mask;
                let neg_ki = ki.wrapping_neg() & mask;
                for j in (i + 1)..parts.len() {
                    if removed[j]
                        || (parts[j].1 & mask) != neg_ki
                        || cx.node(parts[j].0).op != OpCode::Mul
                    {
                        continue;
                    }
                    if poly_checks >= 12 {
                        break;
                    }
                    poly_checks += 1;
                    if super::super::poly::equal_mod(r, cx, parts[i].0, parts[j].0, cur_bits)
                        .unwrap_or(false)
                    {
                        removed[i] = true;
                        removed[j] = true;
                        any_removed = true;
                        break;
                    }
                }
            }
            if any_removed {
                let mut idx = 0;
                parts.retain(|_| {
                    let keep = !removed[idx];
                    idx += 1;
                    keep
                });
            }
        }
        // After outer shared terms cancel, two surviving terms with active width `lo < cur_bits`
        // can be decided modulo `2^lo` in two exact cases:
        //   1. `p1 - p2 == 0` (since `0 <= p1, p2 < 2^lo`), or
        //   2. `p1 + p2 == 2^lo - 1` (since `0 <= p1 + p2 <= 2^(lo+1) - 2`, the only residue
        //      congruent to `2^lo - 1` mod `2^lo` in range is `2^lo - 1` itself).
        if parts.len() == 2 && cur_bits > 1 {
            let ((p1, k1), (p2, k2)) = (parts[0], parts[1]);
            let lo = active_bits(cx, p1, 8).max(active_bits(cx, p2, 8));
            if lo > 0 && lo < cur_bits {
                let lo_mask = u64::MAX >> (64 - lo);
                let k1m = k1 & mask;
                let k2m = k2 & mask;
                let eq_case = (k1m == 1 && k2m == mask) || (k1m == mask && k2m == 1);
                let comp_case = (k1m == 1 && k2m == 1 && bias.wrapping_add(lo_mask) & mask == 0)
                    || (k1m == mask && k2m == mask && bias.wrapping_sub(lo_mask) & mask == 0);
                if (eq_case && bias & mask == 0) || comp_case {
                    cur_bits = lo;
                    mask = lo_mask;
                    let mut narrow_parts = Vec::new();
                    let mut narrow_bias = bias;
                    terms_at(cx, p1, k1, &mut narrow_bias, &mut narrow_parts, 64, false, None, cur_bits, &mut work)?;
                    terms_at(cx, p2, k2, &mut narrow_bias, &mut narrow_parts, 64, false, None, cur_bits, &mut work)?;
                    cancel_parts(&mut narrow_parts, mask, &mut work)?;
                    parts = narrow_parts;
                    bias = narrow_bias;
                }
            }
        }
        rebase_shifted_terms(cx, &mut parts, &mut bias, wa, &mut work)?;
        let value = match constant_lanes(cx, &parts, cur_bits, &mut work) {
            Some(v) => v,
            None => {
                if cur_bits <= 8
                    && let Some(eq) = equal_low_cone_zero(cx, &parts, bias, cur_bits, &mut work)
                {
                    return Some(eq);
                }
                if !collapse_affine_bitwise_groups(cx, &mut parts, &mut bias, cur_bits, &mut work)? {
                    return None;
                }
                rebase_shifted_terms(cx, &mut parts, &mut bias, wa, &mut work)?;
                match constant_lanes(cx, &parts, cur_bits, &mut work) {
                    Some(v) => v,
                    None if cur_bits <= 8 => {
                        return equal_low_cone_zero(cx, &parts, bias, cur_bits, &mut work);
                    }
                    None => return None,
                }
            }
        };
        Some(bias.wrapping_add(value) & mask == 0)
    })();
    r.meter.charge(Counter::PassWork, budget - work.left)?;
    Ok(equal == Some(true))
}

/// Compare two additive layers jointly modulo `2^bits`. The unrestricted words that occur
/// on both sides cancel before tracing bits; the remaining weighted Boolean terms need at
/// most four independent source bits per column, not four bits across the whole word.
pub(in crate::engine::pass) fn equal_sums(
    r: &mut Runner<'_, '_>, cx: &Context, a: u32, b: u32, bits: u16,
) -> Result<bool, Stop> {
    if bits == 0 {
        return Ok(true);
    }
    let wa = cx.wid(a);
    let has_sum = |i| matches!(cx.node(i).op, OpCode::Add | OpCode::Sub | OpCode::Neg);
    if wa != cx.wid(b) || wa > 64 || bits > wa || !(has_sum(a) || has_sum(b)) {
        return Ok(false);
    }
    equal_lanes(r, cx, a, b, bits)
}

/// Truncation is a ring homomorphism: the outer weights can be applied to the
/// wide additive terms, provided we check every column modulo the *narrow*
/// width. High slices, unlike low slices, can observe carries from below.
/// Plain width-`bits` terms may mix with low truncations in the same sum.
pub(in crate::engine::pass) fn truncated_constant(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    terms_in: &[(u32, BitVec)],
    bias: &BitVec,
) -> Result<Option<BitVec>, Stop> {
    let bits = bias.width().bits();
    if bits > 64 || !(1..=32).contains(&terms_in.len()) {
        return Ok(None);
    }
    let mut crosses_sum = false;
    for &(i, _) in terms_in {
        let n = cx.node(i);
        if n.op == OpCode::Extract && n.b == 0 && cx.node(n.a).width <= 64 {
            let src = cx.node(n.a);
            crosses_sum |= matches!(src.op, OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Not)
                || (src.op == OpCode::Mul && (cx.is_const(src.a) || cx.is_const(src.b)));
        } else if n.width != bits {
            return Ok(None);
        }
    }
    // Direct truncations of registers have no hidden sum to flatten.
    if !crosses_sum {
        return Ok(None);
    }
    const LIMIT: u64 = 8192;
    let mut work = Work::new(LIMIT);
    let value = (|| {
        let mask = u64::MAX >> (64 - bits);
        let mut sum = bias.to_u64()?;
        let mut parts = Vec::new();
        for &(i, k) in terms_in {
            let n = cx.node(i);
            let src = if n.op == OpCode::Extract && n.b == 0 && cx.node(n.a).width <= 64 {
                n.a
            } else {
                i
            };
            terms(cx, src, k.to_u64()?, &mut sum, &mut parts, 64, false, &mut work)?;
        }
        cancel_parts(&mut parts, mask, &mut work)?;
        let k = constant_lanes(cx, &parts, bits, &mut work)?;
        Some(BitVec::wrapping_from_u64(bias.width(), sum.wrapping_add(k)))
    })();
    r.meter.charge(Counter::PassWork, LIMIT - work.left)?;
    Ok(value)
}

/// Exact exhaustive decision procedure for `bias + Σ k_i * t_i ≡ 0 (mod 2^bits)` when `bits <= 8`
/// and the causal mod-`2^bits` cone has `<= 48` nodes and `<= 12` total input bits across its
/// leaf variables. Evaluates inductively at `b = 2, 4, ..., bits` so unequal cones exit in `<= 16` steps.
fn equal_low_cone_zero(
    cx: &Context,
    parts: &[(u32, u64)],
    bias: u64,
    bits: u16,
    work: &mut Work,
) -> Option<bool> {
    if !(1..=8).contains(&bits) || parts.is_empty() || parts.len() > 24 {
        return None;
    }
    let mut order: Vec<u32> = Vec::new();
    let mut idx_map: crate::hash::IdMap<u32, usize> = crate::hash::IdMap::default();
    let mut leaves: Vec<(u32, u16)> = Vec::new();
    let mut stack: Vec<(u32, bool)> = parts.iter().map(|&(id, _)| (id, false)).collect();
    while let Some((i, expanded)) = stack.pop() {
        if idx_map.contains_key(&i) {
            continue;
        }
        let n = cx.node(i);
        if n.width > 64 {
            return None;
        }
        let causal = cx.const_val(i).is_some()
            || matches!(
                n.op,
                OpCode::Add
                    | OpCode::Sub
                    | OpCode::Neg
                    | OpCode::Mul
                    | OpCode::Not
                    | OpCode::And
                    | OpCode::Or
                    | OpCode::Xor
            )
            || (n.op == OpCode::Shl && scalar(cx, n.b).is_some())
            || (matches!(n.op, OpCode::Zext | OpCode::Sext) && cx.wid(n.a) <= 64)
            || (n.op == OpCode::Extract && n.b == 0 && n.width >= bits && cx.wid(n.a) <= 64);
        if !causal {
            let vbits = n.width.min(bits);
            leaves.push((i, vbits));
            idx_map.insert(i, order.len());
            order.push(i);
            continue;
        }
        if !expanded {
            if order.len() + stack.len() > 96 {
                return None;
            }
            stack.push((i, true));
            if n.op == OpCode::Shl {
                stack.push((n.a, false));
            } else {
                for c in n.children() {
                    stack.push((c, false));
                }
            }
            continue;
        }
        if order.len() >= 48 {
            return None;
        }
        idx_map.insert(i, order.len());
        order.push(i);
    }
    let total_bits: u16 = leaves.iter().map(|&(_, b)| b).sum();
    if total_bits > 12 {
        return None;
    }
    let mut vals = [0u64; 48];
    let term_idxs: Vec<(usize, u64)> = parts
        .iter()
        .map(|&(id, k)| (idx_map[&id], k))
        .collect();
    let mut b = 2u16.min(bits);
    loop {
        let bmask = (1u64 << b) - 1;
        let mut var_shifts: Vec<(usize, u16, u64)> = Vec::with_capacity(leaves.len());
        let mut shift = 0u16;
        for &(lid, lbits) in &leaves {
            let vb = lbits.min(b);
            var_shifts.push((idx_map[&lid], shift, (1u64 << vb) - 1));
            shift += vb;
        }
        let states = 1u64 << shift;
        let charge = ((order.len() as u64) * states).div_ceil(32);
        work.take(charge)?;
        for st in 0..states {
            for &(slot, sh, vm) in &var_shifts {
                vals[slot] = (st >> sh) & vm;
            }
            for (pos, &id) in order.iter().enumerate() {
                if leaves.iter().any(|&(lid, _)| lid == id) {
                    continue;
                }
                if let Some(c) = scalar(cx, id) {
                    vals[pos] = c & bmask;
                    continue;
                }
                let n = cx.node(id);
                vals[pos] = match n.op {
                    OpCode::Add => vals[idx_map[&n.a]].wrapping_add(vals[idx_map[&n.b]]) & bmask,
                    OpCode::Sub => vals[idx_map[&n.a]].wrapping_sub(vals[idx_map[&n.b]]) & bmask,
                    OpCode::Neg => vals[idx_map[&n.a]].wrapping_neg() & bmask,
                    OpCode::Mul => vals[idx_map[&n.a]].wrapping_mul(vals[idx_map[&n.b]]) & bmask,
                    OpCode::Not => (!vals[idx_map[&n.a]]) & bmask,
                    OpCode::And => vals[idx_map[&n.a]] & vals[idx_map[&n.b]],
                    OpCode::Or => vals[idx_map[&n.a]] | vals[idx_map[&n.b]],
                    OpCode::Xor => vals[idx_map[&n.a]] ^ vals[idx_map[&n.b]],
                    OpCode::Shl => {
                        let s = scalar(cx, n.b).unwrap_or(64);
                        if s >= u64::from(b) {
                            0
                        } else {
                            (vals[idx_map[&n.a]] << s) & bmask
                        }
                    }
                    OpCode::Zext => {
                        let sw = cx.wid(n.a);
                        let v = vals[idx_map[&n.a]];
                        if sw < b {
                            v & ((1u64 << sw) - 1)
                        } else {
                            v & bmask
                        }
                    }
                    OpCode::Sext => {
                        let sw = cx.wid(n.a);
                        let v = vals[idx_map[&n.a]];
                        if sw < b {
                            let sm = (1u64 << sw) - 1;
                            let sign = (v >> (sw - 1)) & 1;
                            if sign != 0 {
                                ((v & sm) | !sm) & bmask
                            } else {
                                v & sm
                            }
                        } else {
                            v & bmask
                        }
                    }
                    OpCode::Extract => vals[idx_map[&n.a]] & bmask,
                    _ => return None,
                };
            }
            let mut acc = bias;
            for &(slot, k) in &term_idxs {
                acc = acc.wrapping_add(k.wrapping_mul(vals[slot]));
            }
            if acc & bmask != 0 {
                return Some(false);
            }
        }
        if b == bits {
            return Some(true);
        }
        b = (b + 2).min(bits);
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum AlignMode {
    Plain,
    ShiftWords,
    AllTz,
}

fn constant_lanes(cx: &Context, parts: &[(u32, u64)], bits: u16, work: &mut Work) -> Option<u64> {
    let mask = u64::MAX >> (64 - bits);
    if let Some(v) = constant_lanes_mode(cx, parts, bits, AlignMode::Plain, work) {
        return Some(v);
    }
    if parts
        .iter()
        .any(|&(_, k)| (k & mask) != 0 && k.trailing_zeros() > 0)
    {
        if let Some(v) = constant_lanes_mode(cx, parts, bits, AlignMode::ShiftWords, work) {
            return Some(v);
        }
        return constant_lanes_mode(cx, parts, bits, AlignMode::AllTz, work);
    }
    None
}

fn constant_lanes_mode(
    cx: &Context,
    parts: &[(u32, u64)],
    bits: u16,
    mode: AlignMode,
    work: &mut Work,
) -> Option<u64> {
    let mut sum = 0u64;
    let mask = u64::MAX >> (64 - bits);
    let mut lane = Lane::default();
    let mut col_terms: Vec<(u64, u64)> = Vec::with_capacity(parts.len());
    for j in 0..bits {
        lane.clear();
        col_terms.clear();
        for &(t, k) in parts {
            if k == 0 {
                continue;
            }
            let use_tz = match mode {
                AlignMode::Plain => false,
                AlignMode::AllTz => true,
                AlignMode::ShiftWords => !matches!(
                    cx.node(t).op,
                    OpCode::And
                        | OpCode::Or
                        | OpCode::Xor
                        | OpCode::Not
                        | OpCode::Zext
                        | OpCode::Sext
                        | OpCode::Extract
                        | OpCode::Select
                ),
            };
            let b = if use_tz {
                let tz = k.trailing_zeros() as u16;
                if j < tz {
                    continue;
                }
                j - tz
            } else {
                j
            };
            let coeff = (k << b) & mask;
            if coeff == 0 {
                continue;
            }
            let rows = lane.bit(cx, t, b, 64, work)?;
            if rows != 0 {
                col_terms.push((rows, coeff));
            }
        }
        let n_rows = 1usize << lane.len;
        let row_mask = if n_rows == 64 {
            u64::MAX
        } else {
            (1u64 << n_rows) - 1
        };
        let mut values = [0u64; 64];
        for &(raw_rows, coeff) in &col_terms {
            let mut rows = raw_rows & row_mask;
            work.take(u64::from(rows.count_ones()))?;
            while rows != 0 {
                let at = rows.trailing_zeros() as usize;
                values[at] = values[at].wrapping_add(coeff);
                rows &= rows - 1;
            }
        }
        // Equality for every assignment in this column is sufficient even when columns
        // share a source bit. We never assume inaccessible rows are the only ones needed.
        let v = values[0];
        if values[1..n_rows]
            .iter()
            .any(|&other| (other ^ v) & mask != 0)
        {
            return None;
        }
        sum = sum.wrapping_add(v);
    }
    Some(sum & mask)
}

// Each row simultaneously evaluates all the bit columns for one assignment
// of their two input bits. Unsupported operations are opaque word atoms.
#[derive(Default)]
pub(super) struct Rows {
    atoms: [((u32, u64), bool, u32); 2],
    len: usize,
    cut: Option<u32>,
    memo: crate::hash::IdMap<u32, [u64; 4]>,
}

impl Rows {
    fn atom(&mut self, cx: &Context, i: u32) -> Option<[u64; 4]> {
        let n = cx.node(i);
        let mask = u64::MAX >> (64 - n.width);
        // c-x = ~(x+!c), so both spellings can share a column.
        let (key, neg) = match n.op {
            OpCode::Sub if scalar(cx, n.a).is_some() => ((n.b, !scalar(cx, n.a)? & mask), true),
            OpCode::Sub if scalar(cx, n.b).is_some() => ((n.a, scalar(cx, n.b)?.wrapping_neg() & mask), false),
            OpCode::Add if scalar(cx, n.b).is_some() => ((n.a, scalar(cx, n.b)?), false),
            OpCode::Add if scalar(cx, n.a).is_some() => ((n.b, scalar(cx, n.a)?), false),
            _ => ((i, 0), false),
        };
        let at = match self.atoms[..self.len].iter().position(|a| a.0 == key) {
            Some(at) => at,
            None => {
                *self.atoms.get_mut(self.len)? = (key, neg, i);
                self.len += 1;
                self.len - 1
            }
        };
        let invert = neg != self.atoms[at].1;
        Some(std::array::from_fn(|r| if (r & (1 << at) != 0) ^ invert { u64::MAX } else { 0 }))
    }

    pub(super) fn read(&mut self, cx: &Context, i: u32, depth: u8, work: &mut Work) -> Option<[u64; 4]> {
        work.take(1)?;
        if let Some(&v) = self.memo.get(&i) {
            return Some(v);
        }
        let d = depth.checked_sub(1)?;
        let n = cx.node(i);
        let v = match n.op {
            _ if self.cut == Some(i) => self.atom(cx, i)?,
            OpCode::Const => [scalar(cx, i)?; 4],
            OpCode::Not => self.read(cx, n.a, d, work)?.map(|x| !x),
            OpCode::And | OpCode::Or | OpCode::Xor => {
                let a = self.read(cx, n.a, d, work)?;
                let b = self.read(cx, n.b, d, work)?;
                std::array::from_fn(|r| match n.op {
                    OpCode::And => a[r] & b[r],
                    OpCode::Or => a[r] | b[r],
                    _ => a[r] ^ b[r],
                })
            }
            OpCode::Select if scalar(cx, n.b).is_some() && scalar(cx, n.c).is_some() => {
                let yes = scalar(cx, n.b)?;
                let no = scalar(cx, n.c)?;
                self.atom(cx, n.a)?.map(|c| (yes & c) | (no & !c))
            }
            _ => self.atom(cx, i)?,
        };
        self.memo.insert(i, v);
        Some(v)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum ColumnSource {
    Word(u32),
    Pair(u32, BinOp, u32),
    Rotated(u32, u32),
}

impl ColumnSource {
    fn build(self, cx: &mut Context) -> Result<u32, crate::Error> {
        match self {
            Self::Word(x) => Ok(x),
            Self::Pair(a, op, b) => cx.c_bin(op, a, b),
            Self::Rotated(x, k) => {
                let k = cx.mk_const_u64(cx.wid(x), u64::from(k))?;
                cx.c_bin(BinOp::RotL, x, k)
            }
        }
    }
}

// bias + ((source & mask) ^ flip), with the source unused for constants.
pub(super) struct ColumnSum {
    source: ColumnSource,
    mask: u64,
    flip: u64,
    bias: u64,
}

pub(super) fn columns(cx: &Context, x: u32, parts: &mut Vec<(u32, u64)>, work: &mut Work) -> Option<ColumnSum> {
    columns_low(cx, x, cx.node(x).width, parts, work)
}

/// Decode a sum modulo `2^w`. When `w` is smaller than the node's width,
/// the returned word may replace it only where its upper bits are dead.
pub(super) fn columns_low(
    cx: &Context, x: u32, w: u16, parts: &mut Vec<(u32, u64)>, work: &mut Work,
) -> Option<ColumnSum> {
    columns_at(cx, x, w, None, parts, work)
}

/// The same prefix certificate with every use of `cut` treated as one word.
/// In particular, the unmasked occurrence in `s + k*(s & m)` must not be
/// expanded through `s` while its masked occurrence reads `s` as an atom.
pub(super) fn columns_cut(
    cx: &Context, x: u32, w: u16, cut: u32, parts: &mut Vec<(u32, u64)>, work: &mut Work,
) -> Option<ColumnSum> {
    columns_at(cx, x, w, Some(cut), parts, work)
}

fn columns_at(
    cx: &Context, x: u32, w: u16, cut: Option<u32>, parts: &mut Vec<(u32, u64)>, work: &mut Work,
) -> Option<ColumnSum> {
    let width = cx.node(x).width;
    if width > 64 || !(1..=width).contains(&w) {
        return None;
    }
    let ones = u64::MAX >> (64 - w);
    let mut bias = 0u64;
    parts.clear();
    terms_at(cx, x, 1, &mut bias, parts, 96, true, cut, 64, work)?;
    if parts.len() < 3 {
        return None;
    }
    let mut rows = Rows { cut, ..Default::default() };
    let mut deltas = [[0u64; 64]; 3];
    for &(i, k) in parts.iter() {
        // ((v << s) ^ m) has constant low bits and scaled, possibly
        // inverted bits of v above them. Accumulate at the input column,
        // not at its shifted position, so it can cancel unshifted terms.
        let n = cx.node(i);
        let shifted = if n.op == OpCode::Xor && cut != Some(i) {
            scalar(cx, n.b).map(|m| (n.a, m))
                .or_else(|| scalar(cx, n.a).map(|m| (n.b, m)))
                .filter(|&(s, _)| cut != Some(s))
                .map(|(s, m)| (cx.node(s), m))
        } else {
            None
        };
        let (f, k) = if let Some((shift, m)) = shifted
            && shift.op == OpCode::Shl
            && let Some(s) = scalar(cx, shift.b)
            && s < u64::from(w)
        {
            bias = bias.wrapping_add(k.wrapping_mul(m & ((1u64 << s) - 1)));
            (rows.read(cx, shift.a, 64, work)?.map(|v| v ^ (m >> s)), k << s)
        } else {
            (rows.read(cx, i, 64, work)?, k)
        };
        bias = bias.wrapping_add(k.wrapping_mul(f[0]));
        for (r, delta) in deltas.iter_mut().enumerate() {
            let mut changed = (f[r + 1] ^ f[0]) & ones;
            work.take(u64::from(changed.count_ones()))?;
            while changed != 0 {
                let j = changed.trailing_zeros();
                let k = if f[0] & (1 << j) == 0 { k } else { k.wrapping_neg() };
                delta[j as usize] = delta[j as usize].wrapping_add(k << j);
                changed &= changed - 1;
            }
        }
    }
    // The three nonzero rows are (1,0), (0,1), (1,1). In each
    // nonconstant column all active rows must add the *same* ±2^j,
    // and the active-row pattern must describe one gate across the word.
    // Checking four all-zero/all-one words alone would miss cross-bit carries.
    work.take(2 * u64::from(w))?;
    let mut gate = 0;
    let mut mask = 0;
    let mut flip = 0;
    for j in 0..usize::from(w) {
        let mut active = 0;
        let mut coeff = 0;
        for (r, delta) in deltas.iter().enumerate() {
            let d = delta[j] & ones;
            if d == 0 { continue; }
            if coeff != 0 && coeff != d { return None; }
            coeff = d;
            active |= 1 << r;
        }
        if active == 0 { continue; }
        if gate != 0 && gate != active { return None; }
        gate = active;
        let bit = 1u64 << j;
        mask |= bit;
        if coeff != bit {
            if coeff != bit.wrapping_neg() & ones { return None; }
            flip |= bit;
        }
    }
    let atoms = &rows.atoms[..rows.len];
    let a = atoms.first()?.2;
    let source = match gate {
        0 => ColumnSource::Word(a), // unused
        0b101 if cx.node(a).width == width => ColumnSource::Word(a),
        0b110 if cx.node(atoms.get(1)?.2).width == width => ColumnSource::Word(atoms[1].2),
        0b100 | 0b111 | 0b011 => {
            let b = atoms.get(1)?.2;
            if cx.node(a).width != width || cx.node(b).width != width { return None; }
            let op = match gate { 0b100 => BinOp::And, 0b111 => BinOp::Or, _ => BinOp::Xor };
            ColumnSource::Pair(a, op, b)
        }
        _ => return None,
    };
    Some(ColumnSum { source, mask, flip, bias: bias.wrapping_sub(flip) & ones })
}

impl ColumnSum {
    // No carry is visible if the bias and the possible ones of the Boolean
    // word intersect only at the top bit. Keep that sum Boolean so the next
    // column decoder sees the original source rather than a new add atom.
    fn offsets(&self, ones: u64) -> (u64, u64) {
        if self.bias & (self.mask | self.flip) & (ones >> 1) == 0 {
            (self.flip ^ self.bias, 0)
        } else {
            (self.flip, self.bias)
        }
    }

    pub(super) fn build(self, r: &mut Runner<'_, '_>, cx: &mut Context, w: u16) -> Result<u32, Stop> {
        r.build(cx, |cx| {
            if self.mask == 0 {
                return cx.mk_const_u64(w, self.bias.wrapping_add(self.flip));
            }
            let ones = u64::MAX >> (64 - w);
            let mut x = self.source.build(cx)?;
            if self.mask != ones {
                let mask = cx.mk_const_u64(w, self.mask)?;
                x = cx.c_bin(BinOp::And, x, mask)?;
            }
            let (flip, bias) = self.offsets(ones);
            if flip != 0 {
                let flip = cx.mk_const_u64(w, flip)?;
                x = cx.c_bin(BinOp::Xor, x, flip)?;
            }
            if bias != 0 {
                let bias = cx.mk_const_u64(w, bias)?;
                x = cx.c_bin(BinOp::Add, x, bias)?;
            }
            Ok(x)
        })
    }
}

// In a sum of products sharing f, prove the remaining column sum constant instead
// of taking independent copies of f or trying to enumerate the unrestricted words
// that disappear from the result. All identities here are modulo 2^bits.
pub(super) fn scaled_sum(cx: &Context, root: u32, bits: u16, left: &mut u64) -> Option<(u32, u64)> {
    let mut todo = [(root, 1u64); 16];
    let mut pending = 1;
    let mut products = [([0u32; 2], 0u64); 16];
    let mut len = 0;
    while pending != 0 {
        *left = left.checked_sub(1)?;
        pending -= 1;
        let (i, k) = todo[pending];
        let n = cx.node(i);
        match n.op {
            OpCode::Add | OpCode::Sub => {
                if pending + len + 2 > products.len() {
                    return None;
                }
                todo[pending] = (n.a, k);
                todo[pending + 1] = (n.b, if n.op == OpCode::Add { k } else { k.wrapping_neg() });
                pending += 2;
            }
            OpCode::Mul | OpCode::Neg => {
                // scaled_factors visits at most 32 nodes per product.
                *left = left.checked_sub(32)?;
                let (c, f) = super::super::linear::scaled_factors(cx, i)?;
                let &[a, b] = f.as_slice() else { return None };
                products[len] = ([a, b], k.wrapping_mul(c.to_u64()?));
                len += 1;
            }
            _ => return None,
        }
    }
    let products = &products[..len];
    let &(candidates, _) = products.first()?;
    let factor = candidates.into_iter().find(|f| products.iter().all(|(pair, _)| pair.contains(f)))?;
    let mut cofactors = [(0u32, 0u64); 16];
    for (out, &([a, b], k)) in cofactors.iter_mut().zip(products) {
        *out = (if a == factor { b } else { a }, k);
    }
    let k = constant_parts(cx, &cofactors[..len], bits, left)?;
    Some((factor, k))
}

// A projected sum of nonlinear products goes through the linear pass first:
// it exposes common factors across terms. Rewriting its inner column sums
// separately can hide that factorization from the product-bit certificate.
fn product_terms(cx: &Context, i: u32, left: &mut u8) -> bool {
    if *left == 0 { return true; }
    *left -= 1;
    let n = cx.node(i);
    match n.op {
        OpCode::Add | OpCode::Sub => product_terms(cx, n.a, left) || product_terms(cx, n.b, left),
        OpCode::Neg | OpCode::Not => product_terms(cx, n.a, left),
        OpCode::Mul if cx.is_const(n.b) => product_terms(cx, n.a, left),
        OpCode::Mul => true,
        _ => false,
    }
}

fn is_sum(cx: &Context, i: u32) -> bool {
    matches!(cx.node(i).op, OpCode::Add | OpCode::Sub)
}

/// Try the compared sum first: its inner arithmetic need not be understood
/// when the enclosing Boolean combination cancels for every word. For a
/// sampled bit, also decode maximal inner sums bottom up.
pub(super) fn reduce_columns(
    r: &mut Runner<'_, '_>, cx: &mut Context, root: u32, order: &[u32],
) -> Result<Option<u32>, Stop> {
    if !(12..=4096).contains(&order.len()) || cx.node(root).width != 1 || r.mba.swept.contains_key(&root) {
        return Ok(None);
    }
    let n = cx.node(root);
    let equality = matches!(n.op, OpCode::Eq | OpCode::Ne) && scalar(cx, n.b).is_some();
    // The large-equality sweep can defer this spelling before it reaches the
    // usual product pass. Try only the sparse factors, not the other operand.
    if equality && cx.node(n.a).op == OpCode::Not && zero_product(cx, root).is_some() {
        return reduce_product(r, cx, root, order);
    }
    if equality && let Some(v) = rotated_layers(r, cx, root, order)? {
        return Ok(Some(v));
    }
    let compared = equality && is_sum(cx, n.a);
    // `zext(low) | tag`, `zext(low) ^ tag`, `concat(tag, low)` and complemented masks all
    // compare a field: decode the sums feeding the field before a general MBA search spends
    // fuel on their unrelated inputs.
    let field = matches!(n.op, OpCode::Extract | OpCode::Not) || (equality && {
        let lhs = cx.node(n.a);
        let value = if lhs.op == OpCode::Not { cx.node(lhs.a) } else { lhs };
        matches!(value.op, OpCode::Extract | OpCode::And | OpCode::Concat)
            || (matches!(value.op, OpCode::Or | OpCode::Xor)
                && cx.const_val(value.b).is_some()
                && matches!(cx.node(value.a).op, OpCode::Zext | OpCode::And | OpCode::Extract))
    });
    if !compared && !field {
        return Ok(None);
    }
    if n.op == OpCode::Extract {
        let mut left = 32;
        let nonlinear = product_terms(cx, n.a, &mut left);
        r.meter.charge(Counter::PassWork, u64::from(32 - left))?;
        if nonlinear { return Ok(None); }
    }
    let budget = (r.meter.left_in(|b| b.pass_work) / 8).min(1 << 15);
    let mut work = Work { left: budget, projections: Default::default() };
    let mut parts = Vec::new();
    if compared && let Some(s) = columns(cx, n.a, &mut parts, &mut work) {
        let w = cx.node(n.a).width;
        let x = s.build(r, cx, w)?;
        let out = r.build(cx, |cx| cx.rebuild(root, [x, n.b, 0]))?;
        r.meter.charge(Counter::PassWork, budget - work.left)?;
        return Ok((out != root).then_some(out));
    }
    // Distinct slices of one computed word look like unrelated atoms to `columns`.
    // For a literal comparison only constancy matters. Trace each term's bits back
    // through those slices and check all assignments in each column independently.
    if compared && parts.len() >= 3 && cx.wid(n.a) <= 64
        && let Some(k) = constant(cx, n.a, cx.wid(n.a), &mut parts, &mut work)
    {
        r.meter.charge(Counter::PassWork, budget - work.left)?;
        let equal = Some(k) == scalar(cx, n.b);
        return r.build(cx, |cx| cx.mk_const_u64(1, u64::from(equal == (n.op == OpCode::Eq)))).map(Some);
    }
    if work.take(3 * order.len() as u64).is_none() {
        r.meter.charge(Counter::PassWork, budget - work.left)?;
        return Ok(None);
    }
    let result = rewrite_sums(r, cx, order, |r, cx, cur| {
        let w = cx.node(cur).width;
        if let Some(s) = columns(cx, cur, &mut parts, &mut work) {
            return s.build(r, cx, w).map(Some);
        }
        if w <= 64 && let Some((f, k)) = scaled_sum(cx, cur, w, &mut work.left) {
            return r.build(cx, |cx| {
                let k = cx.mk_const_u64(w, k)?;
                cx.c_bin(BinOp::Mul, f, k)
            }).map(Some);
        }
        Ok(None)
    })?;
    r.meter.charge(Counter::PassWork, budget - work.left)?;
    Ok(result.get(root))
}

pub(super) fn rewrite_sums(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    order: &[u32],
    mut decode: impl FnMut(&mut Runner<'_, '_>, &mut Context, u32) -> Result<Option<u32>, Stop>,
) -> Result<super::super::Lease, Stop> {
    rewrite_nodes(r, cx, order, |r, cx, cur, top| {
        if top { decode(r, cx, cur) } else { Ok(None) }
    })
}

fn rewrite_nodes(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    order: &[u32],
    mut decode: impl FnMut(&mut Runner<'_, '_>, &mut Context, u32, bool) -> Result<Option<u32>, Stop>,
) -> Result<super::super::Lease, Stop> {
    let mut tops = super::super::Lease::new(cx.len());
    for &i in order {
        if !is_sum(cx, i) {
            for c in cx.node(i).children() {
                if is_sum(cx, c) {
                    tops.insert(c, 0);
                }
            }
        }
    }
    let mut rewrites = super::super::Lease::new(cx.len());
    for &i in order {
        let mut kids = [0; 3];
        let mut changed = false;
        for (k, c) in cx.node(i).children().enumerate() {
            kids[k] = rewrites.get(c).unwrap_or(c);
            changed |= kids[k] != c;
        }
        let mut cur = if changed { r.build(cx, |cx| cx.rebuild(i, kids))? } else { i };
        if let Some(v) = decode(r, cx, cur, tops.contains(i) && is_sum(cx, cur))? {
            cur = v;
        }
        if cur != i {
            rewrites.insert(i, cur);
        }
    }
    Ok(rewrites)
}

/// Recognize `bias + ((rotl(x,r) & mask) ^ flip)` in an additive layer.
/// Accumulate coefficients by *source* bit, not term bit: a left shift
/// spelled as a scalar multiple and a right-shifted slice can read different
/// positions of one word. Every nonzero coefficient must be ±2^j for the
/// output bit j of one common rotation. The baseline is the all-clear word.
fn sum_slice(
    cx: &Context,
    i: u32,
    memo: &mut super::SliceMemo,
    parts: &mut Vec<(u32, u64)>,
    work: &mut Work,
) -> Option<ColumnSum> {
    let w = cx.node(i).width;
    if w > 64 {
        return None;
    }
    let ones = u64::MAX >> (64 - w);
    let mut bias = 0u64;
    parts.clear();
    terms(cx, i, 1, &mut bias, parts, 96, false, work)?;
    if parts.len() < 2 {
        return None;
    }
    let mut weights = [0u64; 64];
    let mut source = None;
    for &(t, k) in parts.iter() {
        let s = super::slice_of(cx, t, memo, 0);
        if s.mask != 0 && source.replace(s.base).is_some_and(|b| b != s.base) {
            return None;
        }
        bias = bias.wrapping_add(k.wrapping_mul(s.flip));
        let mut m = s.mask;
        work.take(u64::from(m.count_ones()))?;
        while m != 0 {
            let j = m.trailing_zeros();
            let bit = 1 << j;
            let delta = if s.flip & bit == 0 { k } else { k.wrapping_neg() };
            let b = if j >= s.rot { j - s.rot } else { j + u32::from(w) - s.rot };
            weights[b as usize] = weights[b as usize].wrapping_add(delta << j);
            m &= m - 1;
        }
    }
    work.take(u64::from(w))?;
    let mut mask = 0;
    let mut flip = 0;
    let mut rotation = None;
    for (j, &coeff) in weights[..usize::from(w)].iter().enumerate() {
        let c = coeff & ones;
        if c == 0 {
            continue;
        }
        let dest = c.trailing_zeros();
        let bit = 1u64 << dest;
        let j = j as u32;
        let rot = if dest >= j { dest - j } else { dest + u32::from(w) - j };
        if rotation.replace(rot).is_some_and(|r| r != rot) { return None; }
        if c == (bit.wrapping_neg() & ones) && (c != bit || bias & bit != 0) {
            flip |= bit;
        } else if c != bit {
            return None;
        }
        mask |= bit;
    }
    let base = source.unwrap_or(i); // unused for a constant
    let rot = rotation.unwrap_or(0);
    // If no addition is needed, keep constant lanes in the Boolean mask.
    if (bias ^ flip) & mask == 0 { flip = bias & ones; }
    let source = if rot == 0 { ColumnSource::Word(base) } else { ColumnSource::Rotated(base, rot) };
    Some(ColumnSum { source, mask, flip, bias: bias.wrapping_sub(flip) & ones })
}

// Both p == 0 and ~p == all-ones test the same word. The polarity belongs
// to the comparison, not to the complement on its operand.
fn zero_product(cx: &Context, root: u32) -> Option<(u32, bool)> {
    let n = cx.node(root);
    if !matches!(n.op, OpCode::Eq | OpCode::Ne) { return None; }
    let lhs = cx.node(n.a);
    let k = scalar(cx, n.b)?;
    if lhs.op == OpCode::Mul && k == 0 {
        Some((n.a, false))
    } else if lhs.op == OpCode::Not && lhs.width <= 64 && k == u64::MAX >> (64 - lhs.width)
        && cx.node(lhs.a).op == OpCode::Mul
    {
        Some((lhs.a, true))
    } else {
        None
    }
}

// Emit only factors equal to a zero-extended `source & mask`. A factor
// outside this bounded part of the multiplication tree can only add zeros.
fn field_factors(cx: &Context, i: u32, depth: u8, emit: &mut impl FnMut(u32, u64)) {
    let n = cx.node(i);
    if n.op == OpCode::Mul && depth != 0 {
        field_factors(cx, n.a, depth - 1, emit);
        field_factors(cx, n.b, depth - 1, emit);
        return;
    }
    let i = if n.op == OpCode::Zext { n.a } else { i };
    let n = cx.node(i);
    if n.op == OpCode::Extract && n.width <= 8 {
        emit(i, (1 << n.width) - 1);
    } else if n.op == OpCode::And && let Some(mask) = scalar(cx, n.b)
        && mask.count_ones() <= 8
    {
        emit(i, mask);
    }
}

// A lower bound on trailing zeros. A lane is zero only if it is zero at
// *every* row. A free bit, depth/fuel exhaustion, or too many distinct bits
// stops the count; no bit above the lowest possible one matters.
fn field_zeros(cx: &Context, x: u32, mut mask: u64, work: &mut Work) -> u16 {
    while mask != 0 {
        let j = mask.trailing_zeros() as u16;
        if Lane::default().bit(cx, x, j, 64, work) != Some(0) { return j; }
        mask &= mask - 1;
    }
    64
}

// A Boolean encoding between two additions can be the identity on their
// intermediate sum. Combine offsets only after proving every bit is a wire:
// the presence of even one mask/flip would invalidate cancellation of carries.
fn joined_offset(cx: &Context, i: u32, memo: &mut super::SliceMemo) -> Option<(u32, u64)> {
    let n = cx.node(i);
    if n.width > 64 || n.op != OpCode::Add { return None; }
    let k = scalar(cx, n.b)?;
    let s = super::slice_of(cx, n.a, memo, 0);
    if s.rot != 0 || s.mask != u64::MAX >> (64 - n.width) || s.flip != 0 { return None; }
    let a = cx.node(s.base);
    if a.op != OpCode::Add { return None; }
    Some((a.a, k.wrapping_add(scalar(cx, a.b)?) & s.mask))
}

/// A sequence of split rotations can hide inverse constant additions on
/// either end. Decode the arithmetic on its halves *before* treating the
/// intermediate rotated words as independent inputs to the following sum.
/// Commit only a smaller DAG. Sparse masks at the end often leave no bit of
/// the original word; don't enumerate the irrelevant shifts or input bits.
fn rotated_layers(
    r: &mut Runner<'_, '_>, cx: &mut Context, root: u32, order: &[u32],
) -> Result<Option<u32>, Stop> {
    let budget = (r.meter.left_in(|b| b.pass_work) / 8).min(1 << 15);
    let scan = order.len() as u64;
    if budget < 9 * scan { return Ok(None); }
    r.meter.charge(Counter::PassWork, scan)?;
    let mut shifts = super::super::Lease::new(cx.len());
    let mut paired = false;
    for &i in order {
        let n = cx.node(i);
        if matches!(n.op, OpCode::Shl | OpCode::LShr) && n.width <= 64 && scalar(cx, n.b).is_some() {
            let flag = if n.op == OpCode::Shl { 1 } else { 2 };
            let flags = shifts.get(n.a).unwrap_or(0) | flag;
            if flags == 3 { paired = true; break; }
            shifts.insert(n.a, flags);
        }
    }
    if !paired { return Ok(None); }
    // Memoized slice reads, rebuilding and the final size check are linear
    // in the DAG. Charge coefficient accumulation by the live columns.
    let mut work = Work::new(budget - 9 * scan);
    let mut memo = super::SliceMemo::new(cx);
    let mut parts = Vec::new();
    let out = rewrite_nodes(r, cx, order, |r, cx, i, sum| {
        let n = cx.node(i);
        if n.width > 64 || work.left == 0 { return Ok(None); }
        if sum {
            if let Some((x, k)) = joined_offset(cx, i, &mut memo) {
                return r.build(cx, |cx| {
                    let k = cx.mk_const_u64(n.width, k)?;
                    cx.c_bin(BinOp::Add, x, k)
                }).map(Some);
            }
            if let Some(s) = sum_slice(cx, i, &mut memo, &mut parts, &mut work) {
                return s.build(r, cx, n.width).map(Some);
            }
        } else if matches!(n.op, OpCode::And | OpCode::Or) && scalar(cx, n.b).is_some() {
            let s = super::slice_of(cx, i, &mut memo, 0);
            let ones = u64::MAX >> (64 - n.width);
            let constant = if s.mask == 0 {
                Some(s.flip)
            } else if s.rot != 0 && s.mask.count_ones() <= super::EXHAUSTIVE_BITS {
                // Only query the base, before the rotations, for these few
                // surviving bits. A scoped fact must not escape in a rewrite.
                let (kb, fin) = super::super::known_words(r, cx, s.base)?;
                kb.and_then(|[z, o]| {
                    let rot = |x: u64|
                        ((x << s.rot) | ((x & ones) >> (u32::from(n.width) - s.rot))) & ones;
                    (fin == super::Fin::FINAL && s.mask & !rot(z | o) == 0)
                        .then(|| (rot(o) & s.mask) ^ s.flip)
                })
            } else {
                None
            };
            if let Some(v) = constant {
                return r.build(cx, |cx| cx.mk_const_u64(n.width, v)).map(Some);
            }
        }
        Ok(None)
    })?;
    r.meter.charge(Counter::PassWork, budget - scan - work.left)?;
    let Some(out) = out.get(root) else { return Ok(None) };
    let smaller = matches!(
        cx.dag_size(&[cx.handle(out)], order.len() as u32 - 1).map_err(Stop::Error)?,
        crate::expr::Bounded::Exact(_)
    );
    Ok(smaller.then_some(out))
}

/// A product's few visible bits may read an entire chain of encoded words.
/// Collapse the maximal sums in that chain *before* asking about unrelated
/// subexpressions. The other phases handle the resulting small product.
pub(super) fn reduce_product(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    order: &[u32],
) -> Result<Option<u32>, Stop> {
    let Some((product, complemented)) = zero_product(cx, root) else { return Ok(None) };
    if !(32..=4096).contains(&order.len()) || r.mba.swept.contains_key(&root)
    {
        return Ok(None);
    }
    const DEPTH: u8 = 3;
    let mut fields = [(0u32, 0u64); 1 << DEPTH];
    let mut len = 0;
    field_factors(cx, product, DEPTH, &mut |x, mask| {
        fields[len] = (x, mask);
        len += 1;
    });
    let fields = &fields[..len];
    if fields.is_empty() { return Ok(None); }
    let budget = (r.meter.left_in(|b| b.pass_work) / 8).min(1 << 15);
    let mut work = Work::new(budget);
    // Marking tops, rebuilding, and memoized slice reads of original and
    // rebuilt nodes are linear in the order; charge the additive walks below
    // separately, including each input bit whose weight they accumulate.
    if work.take(8 * order.len() as u64).is_none() {
        return Ok(None);
    }
    // For the early spelling, touch only the sparse factors' common cone;
    // the dense factors may be unrelated even when they dominate the DAG.
    let mut cone = Vec::new();
    let order = if complemented {
        let mut wanted = super::super::Lease::new(cx.len());
        for &(x, _) in fields { wanted.insert(x, 0); }
        for &i in order.iter().rev() {
            if wanted.contains(i) {
                cone.push(i);
                for c in cx.node(i).children() { wanted.insert(c, 0); }
            }
        }
        cone.reverse();
        cone.as_slice()
    } else {
        order
    };
    let mut memo = super::SliceMemo::new(cx);
    let mut parts = Vec::new();
    let rewrites = rewrite_sums(r, cx, order, |r, cx, cur| {
        if let Some(sum) = sum_slice(cx, cur, &mut memo, &mut parts, &mut work) {
            return sum.build(r, cx, cx.node(cur).width).map(Some);
        }
        if let Some((x, k)) = joined_offset(cx, cur, &mut memo) {
            return r.build(cx, |cx| {
                let k = cx.mk_const_u64(cx.node(cur).width, k)?;
                cx.c_bin(BinOp::Add, x, k)
            }).map(Some);
        }
        Ok(None)
    })?;
    let width = cx.node(product).width;
    let mut zeros = 0;
    for &(x, mask) in fields {
        zeros += field_zeros(cx, rewrites.get(x).unwrap_or(x), mask, &mut work);
        if zeros >= width { break; }
    }
    r.meter.charge(Counter::PassWork, budget - work.left)?;
    if zeros >= width {
        let value = u64::from(cx.node(root).op == OpCode::Eq);
        return r.build(cx, |cx| cx.mk_const_u64(1, value)).map(Some);
    }
    Ok(rewrites.get(root))
}

pub(super) fn folded(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    k: &BitVec,
) -> Result<bool, Stop> {
    let n = cx.node(root);
    if n.op != OpCode::Extract {
        return Ok(false);
    }
    let p = cx.node(n.a);
    if p.op != OpCode::Mul
        || p.width > 64
        || cx.const_val(p.a).is_some()
        || cx.const_val(p.b).is_some()
    {
        return Ok(false);
    }
    let bits = n.b as u16 + 1;
    let budget = r.meter.left_in(|b| b.mba_steps).min(1 << 17);
    let mut work = Work {
        left: budget,
        projections: Default::default(),
    };
    let mut parts = Vec::new();
    for (x, y) in [(p.a, p.b), (p.b, p.a)] {
        if let Some(c) = constant(cx, x, bits, &mut parts, &mut work) {
            r.meter.charge(Counter::MbaSteps, budget - work.left)?;
            let w = cx.width_of(y);
            let c = r.build(cx, |cx| cx.mk_const(&BitVec::wrapping_from_u64(w, c)))?;
            let prod = r.build(cx, |cx| cx.c_bin(BinOp::Mul, y, c))?;
            let (known, _) = super::super::known(r, cx, prod)?;
            return Ok(known.is_some_and(|kb| {
                kb.known().bit(bits - 1) == Some(true) && kb.known_one().bit(bits - 1) == k.bit(0)
            }));
        }
    }
    r.meter.charge(Counter::MbaSteps, budget - work.left)?;
    Ok(false)
}

/// A single root-only question after cheaper certificates. Copy into the pure circuit
/// oracle: no simplifier recursion and no use of the samples as a proof. Each question
/// receives at most a fraction of the remaining fuel, including circuit construction.
#[cfg(feature = "prove")]
pub(super) fn circuit(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    root: u32,
    k: &BitVec,
) -> Result<bool, Stop> {
    use crate::engine::oracle::{EqualityCaps, EqualityVerdict};
    let cap = (r.meter.left_in(|b| b.mba_steps) / 32).min(1 << 17);
    if cap < 256 {
        return Ok(false);
    }
    let mut scx = Context::new();
    let left = match scx.import(cx, &[cx.handle(root)]) {
        Ok(roots) => roots[0],
        Err(crate::Error::Unsupported(_)) => return Ok(false),
        Err(e) => return Err(Stop::Error(e)),
    };
    let right = scx.constant(k).map_err(Stop::Error)?;
    let caps = EqualityCaps {
        samples: 0,
        max_nodes: cap as usize,
        max_propagations: cap,
    };
    let answer = crate::circuit_equality()(&mut scx, left, right, &caps).map_err(Stop::Error)?;
    r.meter
        .charge(Counter::MbaSteps, answer.nodes as u64 + answer.propagations)?;
    Ok(answer.verdict == EqualityVerdict::Proved)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{FnEnv, ParseOptions, SymbolKey, Width};

    #[test]
    fn compared_sum_of_four_projected_bits() {
        use crate::engine::{Budget, Engine, Run, Strategy};
        use crate::mba::MbaConfig;

        let strategy = Strategy::deobfuscate().with_mba(MbaConfig::default().with_opaque_sweep(true));
        let engine = Engine::builder().builtin().strategy(strategy).build().unwrap();
        for (coefficient, op, expected) in [(7, "==", Some(true)), (7, "!=", Some(false)), (8, "==", None)] {
            let text = format!("let h = x:64 * x + y:64; \
                let p = extract<0,8>(h) ^ extract<16,8>(h); \
                let q = extract<8,8>(h) ^ extract<24,8>(h); \
                zext<64>(p & q)*{coefficient} + zext<64>(~p & q)*7 + \
                zext<64>(p & ~q)*7 + zext<64>(~p & ~q)*7 {op} 1785");
            let mut cx = Context::new();
            let root = cx.parse(&text, &ParseOptions::width(Width::W64)).unwrap();
            let out = engine.run(&mut cx, &[root], Run::default().with_per_call(Budget::fuel(1 << 14))).unwrap();
            assert_eq!(cx.as_const(out.roots[0].expr).unwrap(), expected.map(BitVec::from_bool));
        }
    }

    #[test]
    fn tagged_low_word_of_scaled_partition() {
        use crate::engine::{Budget, Engine, Run, Strategy};
        use crate::mba::MbaConfig;

        let strategy = Strategy::deobfuscate().with_mba(MbaConfig::default().with_opaque_sweep(true));
        let engine = Engine::builder().builtin().strategy(strategy).build().unwrap();
        // The three masks partition the word, giving s = -k if they have
        // equal weights. The complementary multipliers leave only -s.
        for (weight, k, tag, lhs, rhs, expected) in [
            (5, 5, 0x9300, "tagged", 0x9305, Some(true)),
            (19, 19, 0xa084, "~tagged", 0x5f68, Some(true)),
            (6, 5, 0x9300, "tagged", 0x9305, None),
        ] {
            let text = format!(
                "let a = x:16 * x + 7; let b = z:16 ^ 0x69ac; \
                 let s = (a & b)*{weight} + (a & ~b)*{k} + ~a*{k}; \
                 let low = trunc<8>(s*y:16 + ~y*s); \
                 let tagged = zext<16>(low) | {tag}; {lhs} == {rhs}"
            );
            let mut cx = Context::new();
            let root = cx.parse(&text, &ParseOptions::width(Width::W16)).unwrap();
            let out = engine.run(&mut cx, &[root], Run::default().with_per_call(Budget::fuel(1 << 14))).unwrap();
            assert_eq!(cx.as_const(out.roots[0].expr).unwrap(), expected.map(BitVec::from_bool));
        }
    }

    #[test]
    fn sparse_zero_product_through_an_encoded_offset() {
        use crate::engine::{Budget, Engine, Run, Strategy};
        use crate::mba::MbaConfig;

        let strategy = Strategy::deobfuscate().with_mba(MbaConfig::default().with_opaque_sweep(true));
        let engine = Engine::builder().builtin().strategy(strategy).build().unwrap();
        for (mask, cmp, value) in [(132, "==", Some(true)), (132, "!=", Some(false)), (4, "==", None)] {
            let text = format!(
                "let a = (x | {mask}) + 27; \
                 let b = (a & 51)*3 - (a & 51)*2 + (a & 204); \
                 let c = ((b | 170) & (b | 85)) - 27; \
                 let d = (~(c >>u 2) & 33); \
                 let e = ((x*x + y) ^ rotl(y, 3)) | 1; \
                 ~(e * ((y | 1) * d)) {cmp} -1"
            );
            let mut cx = Context::new();
            let before = cx.parse(&text, &ParseOptions::width(Width::W8)).unwrap();
            let out = engine.run(&mut cx, &[before], Run::default().with_per_call(Budget::fuel(1 << 14))).unwrap();
            let after = out.roots[0].expr;
            assert_eq!(cx.as_const(after).unwrap(), value.map(BitVec::from_bool), "{text}");
            // With bit 7 unrestricted, the odd multipliers leave a real
            // nonzero word at x=0, whereas x=128 kills the same product.
            for x in [0, 128] {
                let env = FnEnv(|key: &SymbolKey, w| {
                    let v = if matches!(key, SymbolKey::Str(s) if s.as_ref() == "x") { x } else { 3 };
                    Some(BitVec::wrapping_from_u64(w, v))
                });
                let v = cx.eval(&[before, after], &env).unwrap();
                assert_eq!(v[0], v[1]);
                if value.is_none() { assert_eq!(v[0], BitVec::from_bool(x != 0)); }
            }
        }
    }

    #[test]
    fn sparse_valuation_never_drops_an_unproved_lane() {
        let mut cx = Context::new();
        let x = cx.parse("~(x | 5)", &ParseOptions::width(Width::W8)).unwrap();
        let x = cx.id(x).unwrap();
        let mut work = Work::new(128);
        assert_eq!(field_zeros(&cx, x, 0b0101, &mut work), 64);
        assert_eq!(field_zeros(&cx, x, 0b1101, &mut work), 3);
        assert_eq!(field_zeros(&cx, x, 0b0101, &mut Work::new(0)), 0);
    }

    #[test]
    fn affine_boolean_columns() {
        let mut cx = Context::new();
        let w = Width::new(4).unwrap();
        let mut parts = Vec::new();
        for (text, constant) in [
            ("(x & y)*2 + (x ^ y) - (x | y) - (x & y) + 3", Some(true)),
            ("(x & y) + (x & ~y) + (~x & 3) - (x & 3) + 5", Some(false)),
            ("((x+3) & 12) + ((12-x) & 12) + (x & 1)", Some(false)),
            ("((x << 1) ^ 7) - (x ^ 3)*2 + (y & 1)", Some(false)),
            ("select(x <s 0, 3, 0) + select(x <s 0, 4, 0) - select(x <s 0, 7, 0)", Some(true)),
            ("(x & y)*2 + (x ^ y) - (x | y)", Some(false)),
            ("x + y - (x & y)", Some(false)),
            ("x + y - (x & y)*2", Some(false)),
            ("((x & y) & 1) + ((x | y) & 2) + ((x ^ y) & 12)", None),
            ("(x & y) + (x & ~z) + (~x & 3)", None),
            // All-zero and all-one words give 0, but the two bits vary independently.
            ("(x & 1)*2 - (x & 2) + (x & 4)*4", None),
        ] {
            let e = cx.parse(text, &ParseOptions::width(w)).unwrap();
            let i = cx.id(e).unwrap();
            let mut work = Work { left: 4096, projections: Default::default() };
            let s = columns(&cx, i, &mut parts, &mut work);
            assert_eq!(s.as_ref().map(|s| s.mask == 0), constant, "{text}");
            if let Some(s) = s {
                let source = s.source.build(&mut cx).unwrap();
                for x in 0..16 {
                    for y in 0..16 {
                        let env = FnEnv(|key: &SymbolKey, w| {
                            let v = if matches!(key, SymbolKey::Str(name) if name.as_ref() == "x") { x } else { y };
                            Some(BitVec::wrapping_from_u64(w, v))
                        });
                        let v = cx.eval(&[e, cx.handle(source)], &env).unwrap();
                        let word = v[1].to_u64().unwrap();
                        assert_eq!(v[0].to_u64(), Some((s.bias + ((word ^ s.flip) & s.mask)) & 15));
                    }
                }
            }
            work.left = 1;
            assert!(columns(&cx, i, &mut parts, &mut work).is_none());
        }
    }

    #[test]
    fn column_wire_may_hold_only_in_a_prefix() {
        let mut cx = Context::new();
        let e = cx.parse("(x & 3)*3 - (x & 3)*2 + (y & 1)*16", &ParseOptions::width(Width::W8)).unwrap();
        let i = cx.id(e).unwrap();
        let mut parts = Vec::new();
        let mut work = Work::new(4096);
        let low = columns_low(&cx, i, 4, &mut parts, &mut work).unwrap();
        assert_eq!((low.mask, low.flip, low.bias), (3, 0, 0));
        for bits in [0, 5, 8, 9] {
            assert!(columns_low(&cx, i, bits, &mut parts, &mut work).is_none(), "{bits}");
        }
    }

    #[test]
    fn shared_cut_survives_arithmetic_and_boolean_readers() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W8);
        let e = cx.parse("let s = x + 7; s - (s & 45)*3 + (s & 45) + 45", &opt).unwrap();
        let s = cx.parse("x + 7", &opt).unwrap();
        let (i, s) = (cx.id(e).unwrap(), cx.id(s).unwrap());
        let mut parts = Vec::new();
        let mut work = Work::new(4096);
        assert!(columns_low(&cx, i, 8, &mut parts, &mut work).is_none());
        let wire = columns_cut(&cx, i, 8, s, &mut parts, &mut work).unwrap();
        assert_eq!((wire.source, wire.mask, wire.flip, wire.bias), (ColumnSource::Word(s), 255, 45, 0));
    }

    #[test]
    fn only_carry_free_offsets_join_the_flip() {
        for (mask, flip, bias, expected) in [
            (0b0101, 0b0001, 0b1010, (0b1011, 0)),
            (0b1101, 0b1001, 0b1000, (0b0001, 0)),
            (0b0101, 0b0001, 0b0100, (0b0001, 0b0100)),
            (0b0101, 0b0011, 0b0010, (0b0011, 0b0010)),
        ] {
            let word = ColumnSum { source: ColumnSource::Word(0), mask, flip, bias };
            let offsets = word.offsets(15);
            assert_eq!(offsets, expected);
            for x in 0..16 {
                assert_eq!((bias + ((x & mask) ^ flip)) & 15,
                           (offsets.1 + ((x & mask) ^ offsets.0)) & 15);
            }
        }
    }

    #[test]
    fn unary_sum_requires_wire_weights() {
        let mut cx = Context::new();
        let w = Width::new(4).unwrap();
        let mut parts = Vec::new();
        let mut work = Work { left: 4096, projections: Default::default() };
        for (text, bias) in [
            ("(x & 3)*3 - (x & 3)*2 + (~x & 12)", Some(0)),
            // The carry is not a wire: the offset must remain an addition.
            ("(x & 3)*3 - (x & 3)*2 + (~x & 12) + 1", Some(1)),
            ("(x & 3)*3 - (x & 3)*2 + (~y & 12)", None),
            ("(x & 3)*5 - (x & 3)*2 + (~x & 12)", None),
            // Both shift halves and their masks read one rotated word.
            ("let h = x << 1; let l = x >>u 3; (h | l) + (h & l)*5 + (~h & ~l)*2", Some(15)),
            ("(x << 1) + (x >>u 3)", Some(0)),
            ("(x << 1) + (x >>u 2)", None),
        ] {
            let e = cx.parse(text, &ParseOptions::width(w)).unwrap();
            let mut memo = super::super::SliceMemo::new(&cx);
            let slice = sum_slice(&cx, cx.id(e).unwrap(), &mut memo, &mut parts, &mut work);
            assert_eq!(slice.as_ref().map(|s| s.bias), bias, "{text}");
            if let Some(s) = slice {
                let source = s.source.build(&mut cx).unwrap();
                for x in 0..16 {
                    let env = FnEnv(|_: &SymbolKey, w| Some(BitVec::wrapping_from_u64(w, x)));
                    let v = cx.eval(&[e, cx.handle(source)], &env).unwrap();
                    let word = (v[1].to_u64().unwrap() & s.mask) ^ s.flip;
                    assert_eq!(v[0].to_u64(), Some((word + s.bias) & 15));
                }
            }
        }
    }

    #[test]
    fn projected_fields_stop_at_carries() {
        let mut cx = Context::new();
        let w = Width::new(4).unwrap();
        for (text, end) in [("x - (x & 5) * 2 + 5", 4), ("x - (x & 5) * 2 + 6", 1)] {
            let e = cx.parse(text, &ParseOptions::width(w)).unwrap();
            let mut work = Work {
                left: 4096,
                projections: Default::default(),
            };
            let p = projection(&cx, cx.id(e).unwrap(), &mut work).unwrap();
            assert_eq!(p.end, end);
            for x in 0..16 {
                let env = FnEnv(|_: &SymbolKey, w: Width| Some(BitVec::wrapping_from_u64(w, x)));
                let evaluated = cx.eval(&[e, cx.handle(p.source)], &env).unwrap();
                let (result, source) = (
                    evaluated[0].to_u64().unwrap(),
                    evaluated[1].to_u64().unwrap(),
                );
                for j in 0..usize::from(p.end) {
                    let bit = if p.bits[j] == 64 {
                        0
                    } else {
                        source >> p.bits[j]
                    };
                    assert_eq!((bit ^ (p.invert >> j)) & 1, (result >> j) & 1);
                }
            }
        }
    }

    #[test]
    fn equal_lanes_proves_masked_shifted_and_narrow_identities() {
        let mut cx = Context::new();
        let w = Width::W64;
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Shift-aligned cancellation (0007-style)
            "let a = x & 0x3c7300; let b = (y & 1) << 2; let c = zext<64>(z + 3872 == w) << 6; \
             (a | (b ^ 6) | c) - (a | c) + b == 6",
            // Unshifted linear MBA with mixed trailing zeros (2*(x & y) - x - y + (x ^ y) == 0)
            "2 * (x & y) + (x ^ y) == x + y",
            // Factored product cancellation + affine rebasing (0x14048ca15-style)
            "let a = x + 1720; let m = ~(y & 0x3001fffff267); let p = ~y & a; \
             ((-1721 - x + (y & 0xffffcffe00000d98)) * 0x3001fffff0b8 + (z + 0x3001ffffef08) * p) \
             == (m * -432 + (m & ~p) * 0x3001fffff268 + (a ^ y) * 0x3001fffff0b8 + p * z)",
            // Post-cancellation 32-bit complement sum (0x14048ba44-style)
            "w + zext<64>(trunc<32>(x * 0x8790180abab6084b) * 0x55d87e9d) - 1 \
             == w + 0xfffffffe - (x + 0xffffffff & 0xffffffff)",
            // 5-variable bitwise equality inside Lane (0x14048ba44__5add92da-style)
            "let s = ~(a & b) & (~c | a); let r = rotl(s, 24); \
             ~(d & r) & (~e | (s << 24) | (s >>u 40)) == ~e ^ (e ^ d) & r",
            // Non-constant Select traced bit-by-bit in Lane::bit
            "let c = k == 0; select(c, a ^ b, d ^ b) == (select(c, a, d) ^ b)",
            // Carry-free low bits of Add/Sub with constant (j <= tz(c))
            "(((x ^ y) & 2) + (((x + 2) ^ y) & 2)) == 2",
            "(((x ^ y) & 2) + (((x - 2) ^ y) & 2)) == 2",
            // Quadratic polynomial cancellation mixed with masked linear MBA
            "let p = a + (b | 1); let q = a + (b & ~1) + 1; \
             (p * ~p) * 5 + (x & 34) + (~(x & 34)) == (q * ~q) * 5 - 1",
        ] {
            let e = cx.parse(text, &ParseOptions::width(w)).unwrap();
            let outcome = crate::prove::valid_under_with(&mut cx, e, None, &cfg, &prover).unwrap();
            assert!(
                matches!(outcome, crate::prove::Outcome::Proved(_)),
                "expected Proved for {text}, got {outcome:?}"
            );
        }
    }

    #[test]
    fn equal_lanes_rejects_unsound_narrow_complement_and_shifts() {
        let mut cx = Context::new();
        let w = Width::W64;
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Sum of two 32-bit values equals 2^32 (not 2^32 - 1): wraps when x == 0
            "zext<64>(trunc<32>(-x)) + (x & 0xffffffff) == 0x100000000",
            // Off-by-one in shift-aligned sum
            "let a = x & 0x3c7300; let b = (y & 1) << 2; (a | (b ^ 6)) - a + b == 7",
            // Wrong affine offset in rebasing
            "let a = x + 1720; (-1720 - x) + (a ^ y) == ~(a & ~y) + (a & y) - 1",
            // High 64-bit extract of a 128-bit value is NOT zero (must not under-approximate wide extracts)
            "extract<64, 64>(#0:128) == 0:64",
            "extract<32, 64>(#0:128) == (extract<32, 64>(#0:128) & 0xffffffff)",
            // Bit above tz(c) DOES see carry from adding/subtracting c (j = 2 > tz(2) = 1)
            "(((x ^ y) & 4) + (((x + 2) ^ y) & 4)) == 4",
            "((x + 2) & 4) == (x & 4)",
        ] {
            let e = cx.parse(text, &ParseOptions::width(w)).unwrap();
            let outcome = crate::prove::valid_under_with(&mut cx, e, None, &cfg, &prover).unwrap();
            assert!(
                matches!(outcome, crate::prove::Outcome::Refuted(_)),
                "expected Refuted for {text}, got {outcome:?}"
            );
        }
    }
}
