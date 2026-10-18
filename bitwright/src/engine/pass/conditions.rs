//! Readings of 1-bit conditions in linear forms (for the linear and demanded-bits passes). A
//! sum often reads one condition `c` several ways: `zext(c)`, `sext(c)` (`−zext(c)`), a select
//! between constants (`select(c, K1, K0)` is `K0 + (K1 − K0)·zext(c)`), and the carry out of a
//! partial-width addition. With `L = trunc_j(x + k)`, the low `j` bits of a sum, `zext(L)`,
//! `concat(H, L)` and `(x + k) & (2^j − 1)` are the same field over `x` plus `k mod 2^j`,
//! minus `2^j` when the addition carries, which it does exactly when
//! `trunc_j(x) ≥u 2^j − (k mod 2^j)` (x86's `sub ax, 64` merged into the wide register, and
//! its borrow).
//!
//! Conditions meet up to polarity and spelling: a comparison of a field of `x` with a
//! constant, `x & M == 0` for a run of bits `M`, and an extraction compared with zero are each
//! `trunc_j(x) <u t` for some `j` and `t`, or its negation. When two terms of a form read one
//! condition, every term reading it is replaced by its reading over one `zext(c)` of one
//! polarity (`zext(¬c) = 1 − zext(c)`).
//!
//! The nodes a reading builds (that `zext`, the field over `x`, the condition of a carry) are
//! new: the leaves [`merge`] returns for the commit rule are nodes the form already read, so
//! the rule counts what was built (see `merge_signs` in the linear pass).

use super::forms::Parts;
use super::linear::{self, Form};
use super::{Fin, PassKind, Runner, Step, Stop, finish};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::ops::{BinOp, CmpOp, UnOp};

/// A condition up to polarity.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Key {
    /// `trunc_j(x) <u t`, with `0 < t < 2^j` and `j ≤ 64`.
    Below { x: u32, j: u16, t: u64 },
    /// `a op b` for `op` among `==`, `<u`, `<s` (`!=` is `¬==` and `b ≤ a` is `¬(a < b)`).
    Cmp(OpCode, u32, u32),
    /// Any other condition.
    Node(u32),
}

/// The value of `x & (2^m − 1)` for `m` below the width, as `(x, m)`.
fn low_field(cx: &Context, a: u32, b: u32) -> Option<(u32, u16)> {
    let (x, k) = match (cx.const_val(a), cx.const_val(b)) {
        (None, Some(k)) => (a, k),
        (Some(k), None) => (b, k),
        _ => return None,
    };
    let v = k.to_u64()?;
    let m = v.trailing_ones();
    let low = m == 64 || v >> m == 0;
    (m > 0 && low && m < u32::from(k.width().bits())).then_some((x, m as u16))
}

/// `(y, i)` with `trunc_i(y)` the number `trunc_j(x)` is, through truncations, zero extensions
/// and low masks.
fn field(cx: &Context, mut x: u32, mut j: u16) -> (u32, u16) {
    loop {
        let n = cx.node(x);
        let (y, m) = match n.op {
            OpCode::Extract if n.b == 0 => (n.a, n.width),
            OpCode::Zext => (n.a, cx.wid(n.a)),
            OpCode::And => match low_field(cx, n.a, n.b) {
                Some(f) => f,
                None => break,
            },
            _ => break,
        };
        x = y;
        j = j.min(m);
    }
    (x, j)
}

/// The key of `trunc_j(x) <u t`, unless that is always false or always true.
fn below(cx: &Context, x: u32, j: u16, t: u128) -> Option<Key> {
    let (x, j) = field(cx, x, j);
    if j > 64 || t == 0 || t >= 1u128 << j {
        return None;
    }
    Some(Key::Below { x, j, t: t as u64 })
}

/// A constant as a number, if it fits 128 bits.
fn num(cx: &Context, i: u32) -> Option<u128> {
    cx.const_val(i)?.to_u128()
}

/// The key of `y == 0` as a threshold: a run of bits `[s, e)` of `v` is zero when
/// `trunc_e(v) <u 2^s`.
fn zero_test(cx: &Context, a: u32, b: u32) -> Option<Key> {
    let zero = |i: u32| cx.const_val(i).is_some_and(|v| v.is_zero());
    let y = if zero(b) {
        a
    } else if zero(a) {
        b
    } else {
        return None;
    };
    let n = cx.node(y);
    match n.op {
        OpCode::And => {
            let (v, m) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(m)) => (n.a, m),
                (Some(m), None) => (n.b, m),
                _ => return below(cx, y, n.width, 1),
            };
            let bits = m.to_u64().filter(|&b| b != 0)?;
            let (s, e) = (bits.trailing_zeros(), 64 - bits.leading_zeros());
            let run = (u64::MAX >> (64 - (e - s))) << s;
            if bits != run {
                return below(cx, y, n.width, 1);
            }
            below(cx, v, e as u16, 1u128 << s)
        }
        OpCode::Extract if n.b < 64 => below(cx, n.a, n.b as u16 + n.width, 1u128 << n.b),
        _ => below(cx, y, n.width, 1),
    }
}

/// The key of a 1-bit condition and whether the condition is the key (or its negation).
fn key(cx: &Context, mut c: u32) -> (Key, bool) {
    let mut pos = true;
    while cx.node(c).op == OpCode::Not {
        c = cx.node(c).a;
        pos = !pos;
    }
    let n = cx.node(c);
    let w = |i: u32| cx.wid(i);
    let (key, p) = match n.op {
        OpCode::Eq | OpCode::Ne => (
            zero_test(cx, n.a, n.b).unwrap_or(Key::Cmp(OpCode::Eq, n.a, n.b)),
            n.op == OpCode::Eq,
        ),
        // `u <u t`, and `k <u u` as `¬(u <u k + 1)`.
        OpCode::Ult => match (num(cx, n.a), num(cx, n.b)) {
            (None, Some(t)) => (
                below(cx, n.a, w(n.a), t).unwrap_or(Key::Cmp(OpCode::Ult, n.a, n.b)),
                true,
            ),
            (Some(k), None) => match below(cx, n.b, w(n.b), k.saturating_add(1)) {
                Some(key) => (key, false),
                None => (Key::Cmp(OpCode::Ult, n.a, n.b), true),
            },
            _ => (Key::Cmp(OpCode::Ult, n.a, n.b), true),
        },
        // `u ≤u k` as `u <u k + 1`, and `k ≤u u` as `¬(u <u k)`.
        OpCode::Ule => match (num(cx, n.a), num(cx, n.b)) {
            (None, Some(k)) => match below(cx, n.a, w(n.a), k.saturating_add(1)) {
                Some(key) => (key, true),
                None => (Key::Cmp(OpCode::Ult, n.b, n.a), false),
            },
            (Some(k), None) => (
                below(cx, n.b, w(n.b), k).unwrap_or(Key::Cmp(OpCode::Ult, n.b, n.a)),
                false,
            ),
            _ => (Key::Cmp(OpCode::Ult, n.b, n.a), false),
        },
        OpCode::Slt => (Key::Cmp(OpCode::Slt, n.a, n.b), true),
        OpCode::Sle => (Key::Cmp(OpCode::Slt, n.b, n.a), false),
        _ => (Key::Node(c), true),
    };
    (key, p == pos)
}

/// The field a carry reading writes over `x` in place of the sum: `concat(H, trunc_j(x))`,
/// `zext(trunc_j(x))` or `x & (2^j − 1)`.
#[derive(Clone, Copy)]
enum Shape {
    Concat(u32),
    Zext,
    Mask,
}

/// A term's atom as `konst + coef·[key]` (`[¬key]` unless `pos`), plus the field `x` of a
/// carry reading.
#[derive(Clone, Copy)]
struct Reading {
    key: Key,
    pos: bool,
    konst: BitVec,
    coef: BitVec,
    /// The condition node the atom reads, if it has one (the key when `pos`).
    cond: Option<u32>,
    /// Whether the atom is `zext(cond)`.
    zext: bool,
    carry: Option<(Shape, u32, u16)>,
}

/// `x + k` with `k` a constant: `(x, k)`.
fn sum(cx: &Context, s: u32) -> Option<(u32, BitVec)> {
    let n = cx.node(s);
    match n.op {
        OpCode::Add => match (cx.const_val(n.a), cx.const_val(n.b)) {
            (None, Some(k)) => Some((n.a, k)),
            (Some(k), None) => Some((n.b, k)),
            _ => None,
        },
        OpCode::Sub => cx
            .const_val(n.b)
            .filter(|_| cx.const_val(n.a).is_none())
            .map(|k| (n.a, BitVec::un_unchecked(UnOp::Neg, &k))),
        _ => None,
    }
}

/// The carry reading of a field `j` bits wide of `x + k` (the sum `s`, `j` at most its width)
/// in an atom `w` bits wide.
fn carry(cx: &Context, s: u32, j: u16, w: crate::Width, shape: Shape) -> Option<Reading> {
    if j > 64 || j >= w.bits() {
        return None;
    }
    let (x, k) = sum(cx, s)?;
    let kj = k.limbs()[0] & (u64::MAX >> (64 - j));
    if kj == 0 {
        return None;
    }
    // Carries when `trunc_j(x) ≥u 2^j − kj`.
    let key = below(cx, x, j, (1u128 << j) - u128::from(kj))?;
    let two_j = BitVec::bin_unchecked(
        BinOp::Shl,
        &BitVec::one(w),
        &BitVec::wrapping_from_u64(w, u64::from(j)),
    );
    Some(Reading {
        key,
        pos: false,
        konst: BitVec::wrapping_from_u64(w, kj),
        coef: BitVec::un_unchecked(UnOp::Neg, &two_j),
        cond: None,
        zext: false,
        carry: Some((shape, x, j)),
    })
}

/// The low field `l` of a concatenation or extension: a sum, or the truncation of one.
fn carry_of_field(cx: &Context, l: u32, w: crate::Width, shape: Shape) -> Option<Reading> {
    let n = cx.node(l);
    let j = n.width;
    if n.op == OpCode::Extract && n.b == 0 {
        carry(cx, n.a, j, w, shape)
    } else {
        carry(cx, l, j, w, shape)
    }
}

/// The reading of the atom `a` (`w` bits wide), if it reads a condition.
fn reading(cx: &Context, a: u32, w: crate::Width) -> Option<Reading> {
    let n = cx.node(a);
    let cond = |c: u32, konst: BitVec, coef: BitVec, zext: bool| {
        let (key, pos) = key(cx, c);
        Reading {
            key,
            pos,
            konst,
            coef,
            cond: Some(c),
            zext,
            carry: None,
        }
    };
    match n.op {
        OpCode::Zext if cx.wid(n.a) == 1 => Some(cond(n.a, BitVec::zero(w), BitVec::one(w), true)),
        OpCode::Sext if cx.wid(n.a) == 1 => {
            Some(cond(n.a, BitVec::zero(w), BitVec::ones(w), false))
        }
        OpCode::Select => {
            let (t, f) = (cx.const_val(n.b)?, cx.const_val(n.c)?);
            let d = BitVec::bin_unchecked(BinOp::Sub, &t, &f);
            Some(cond(n.a, f, d, false))
        }
        OpCode::Concat => carry_of_field(cx, n.b, w, Shape::Concat(n.a)),
        OpCode::Zext => carry_of_field(cx, n.a, w, Shape::Zext),
        OpCode::And => {
            let (s, j) = low_field(cx, n.a, n.b)?;
            carry(cx, s, j, w, Shape::Mask)
        }
        _ => None,
    }
}

/// Whether the atom `a` has a shape [`reading`] reads, from its operators alone.
fn candidate(cx: &Context, a: u32) -> bool {
    let n = cx.node(a);
    let sum = |s: u32| {
        let m = cx.node(s);
        matches!(m.op, OpCode::Add | OpCode::Sub) && (cx.is_const(m.a) || cx.is_const(m.b))
    };
    let field = |l: u32| {
        let m = cx.node(l);
        sum(l) || (m.op == OpCode::Extract && m.b == 0 && sum(m.a))
    };
    match n.op {
        OpCode::Zext | OpCode::Sext if cx.wid(n.a) == 1 => true,
        OpCode::Select => cx.is_const(n.b) && cx.is_const(n.c),
        OpCode::Concat => field(n.b),
        OpCode::Zext => field(n.a),
        OpCode::And => (cx.is_const(n.a) && sum(n.b)) || (cx.is_const(n.b) && sum(n.a)),
        _ => false,
    }
}

/// Whether two atoms of the sum at `x` may read one condition, before its form is computed: a
/// walk of at most 64 nodes through its linear operators (and `|`, `^`, which may be disjoint
/// sums) that finds two atoms whose readings have one key.
pub(super) fn may_merge(cx: &Context, x: u32) -> bool {
    let w = cx.width_of(x);
    let mut stack = [0u32; 32];
    let mut keys: [Option<Key>; 8] = [None; 8];
    let (mut top, mut seen, mut found) = (1, 0, 0);
    stack[0] = x;
    while top > 0 {
        top -= 1;
        let i = stack[top];
        seen += 1;
        if seen > 64 {
            return false;
        }
        if candidate(cx, i) {
            if let Some(rd) = reading(cx, i, w) {
                if keys[..found].contains(&Some(rd.key)) {
                    return true;
                }
                if found < keys.len() {
                    keys[found] = Some(rd.key);
                    found += 1;
                }
            }
            continue;
        }
        let n = cx.node(i);
        let (a, b) = match n.op {
            OpCode::Add | OpCode::Sub | OpCode::Or | OpCode::Xor => (Some(n.a), Some(n.b)),
            OpCode::Neg | OpCode::Not => (Some(n.a), None),
            OpCode::Mul | OpCode::Shl if cx.is_const(n.b) => (Some(n.a), None),
            OpCode::Mul if cx.is_const(n.a) => (Some(n.b), None),
            _ => (None, None),
        };
        for c in [a, b].into_iter().flatten() {
            if top == stack.len() {
                return false;
            }
            stack[top] = c;
            top += 1;
        }
    }
    false
}

/// `form` with every condition that two of its terms read replaced by one `zext` of it, and
/// the nodes the new form reads that existed (the leaves for the commit rule); `None` when no
/// two terms read one condition.
pub(super) fn merge(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    form: &Form,
) -> Result<Option<(Form, Vec<u32>)>, Stop> {
    let (konst, terms, fin) = form.parts();
    let w = konst.width();
    if w.bits() < 2 || terms.iter().filter(|t| candidate(cx, t.0)).take(2).count() < 2 {
        return Ok(None);
    }
    let reads: Vec<Option<Reading>> = terms.iter().map(|&(a, _)| reading(cx, a, w)).collect();
    let mut groups: Vec<Key> = Vec::new();
    for (i, ri) in reads.iter().enumerate() {
        if let Some(ri) = ri
            && !groups.contains(&ri.key)
            && reads[i + 1..].iter().flatten().any(|rj| rj.key == ri.key)
        {
            groups.push(ri.key);
        }
    }
    if groups.is_empty() {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, terms.len() as u64)?;
    let (terms, fin) = (terms.to_vec(), fin);
    let mut konst = *konst;
    let mut out: Vec<(u32, BitVec)> = Vec::new();
    let mut leaves: Vec<u32> = Vec::new();
    let grouped = |ri: &Option<Reading>| ri.as_ref().is_some_and(|x| groups.contains(&x.key));
    for (i, &(a, q)) in terms.iter().enumerate() {
        if !grouped(&reads[i]) {
            out.push((a, q));
            leaves.push(a);
        }
    }
    let mul = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Mul, a, b);
    let add = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Add, a, b);
    let sub = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Sub, a, b);
    for g in &groups {
        let members: Vec<(u32, BitVec, Reading)> = terms
            .iter()
            .zip(&reads)
            .filter_map(|(&(a, q), ri)| ri.filter(|x| x.key == *g).map(|x| (a, q, x)))
            .collect();
        // The condition's `zext`: an atom of the form, else built over a condition node the
        // form reads, else over the threshold of a carry.
        let (z, zpos) = if let Some(&(a, _, rd)) = members.iter().find(|m| m.2.zext) {
            leaves.push(a);
            (a, rd.pos)
        } else if let Some((c, rd)) = members.iter().find_map(|m| m.2.cond.map(|c| (c, m.2))) {
            leaves.push(c);
            (r.build(cx, |cx| cx.c_zext(c, w.bits()))?, rd.pos)
        } else {
            let Key::Below { x, j, t } = *g else {
                return Ok(None);
            };
            leaves.push(x);
            let z = r.build(cx, |cx| {
                let f = cx.c_extract(x, 0, j)?;
                let t = cx.mk_const(&BitVec::wrapping_from_u64(cx.width_of(f), t))?;
                let c = cx.c_cmp(CmpOp::Ult, f, t)?;
                cx.c_zext(c, w.bits())
            })?;
            (z, true)
        };
        let mut zk = BitVec::zero(w);
        for (_, q, rd) in members {
            let v = mul(&q, &rd.coef);
            if rd.pos == zpos {
                zk = add(&zk, &v);
            } else {
                konst = add(&konst, &v);
                zk = sub(&zk, &v);
            }
            konst = add(&konst, &mul(&q, &rd.konst));
            if let Some((shape, x, j)) = rd.carry {
                leaves.push(x);
                let p = r.build(cx, |cx| match shape {
                    Shape::Concat(h) => {
                        let l = cx.c_extract(x, 0, j)?;
                        cx.c_concat(h, l)
                    }
                    Shape::Zext => {
                        let l = cx.c_extract(x, 0, j)?;
                        cx.c_zext(l, w.bits())
                    }
                    Shape::Mask => {
                        let m = cx.mk_const(&BitVec::wrapping_from_u128(w, (1u128 << j) - 1))?;
                        cx.c_bin(BinOp::And, x, m)
                    }
                })?;
                if let Shape::Concat(h) = shape {
                    leaves.push(h);
                }
                out.push((p, q));
            }
        }
        out.push((z, zk));
    }
    leaves.sort_unstable();
    leaves.dedup();
    let mut f = Form::of(konst, &out);
    f.fin = fin;
    Ok(Some((f, leaves)))
}

/// The linear pass's reading of `n` (whose form is `form`) with its conditions merged:
/// `Ok(step)` when it commits, else `Err(fin)` with what the rejection contributes to the
/// node's finality.
pub(super) fn step(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    form: &Form,
) -> Result<Result<Step, Fin>, Stop> {
    let before = cx.len() as u32;
    let Some((f, leaves)) = merge(r, cx, form)? else {
        return Ok(Err(Fin::FINAL));
    };
    let e = linear::emit(r, cx, &f)?;
    Ok(
        match finish(r, cx, PassKind::Linear, n, e, before, &leaves, f.fin)? {
            Step::To(x, fin) => Ok(Step::To(x, fin)),
            Step::Normal(fin) => Err(fin),
        },
    )
}
