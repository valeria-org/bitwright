//! The compares pass: boolean combinations (`& | ^ ~` on 1-bit values) of comparisons.
//!
//! *Same operand pair.* Two values `x`, `y` stand in exactly one of five relations: equal, or
//! one of {less, greater} unsigned × {less, greater} signed. Every predicate over `(x, y)` (in
//! either operand order) is a set of those relations, and `& | ^ ~` are set operations, so any
//! combination is a set; it is emitted when that set is one predicate, true or false. At
//! W = 1 only three relations can occur (`0 <u 1` but `0 >s -1`), which is accounted for.
//!
//! *One operand against constants.* A comparison of `x` with a constant is a set of values of
//! `x`: a union of unsigned intervals (signed comparisons split at the sign boundary).
//! Combinations are exact interval-set operations, emitted when the set is empty, everything, a
//! single comparison, or one wrapped interval `[lo, hi]` as the range check `x - lo <=u hi - lo`.
//!
//! Both are exact at every width; the result replaces the node only when smaller.

use super::{Fin, PassKind, Runner, Step, Stop, finish};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::ops::{BinOp, CmpOp};

/// The most intervals an interval set keeps before its node is treated as opaque.
const MAX_INTERVALS: usize = 8;

// ----- relation sets ------------------------------------------------------------------------------

/// Relations of the first operand to the second: bit 0 equal, bit 1 (<u, <s), bit 2 (<u, >s),
/// bit 3 (>u, <s), bit 4 (>u, >s).
const ALL: u8 = 0b11111;

fn pred_set(op: CmpOp) -> u8 {
    match op {
        CmpOp::Eq => 0b00001,
        CmpOp::Ne => 0b11110,
        CmpOp::Ult => 0b00110,
        CmpOp::Ule => 0b00111,
        CmpOp::Slt => 0b01010,
        CmpOp::Sle => 0b01011,
    }
}

/// The same set with the operands exchanged.
fn swap_set(s: u8) -> u8 {
    let bit = |k: u8| (s >> k) & 1;
    bit(0) | (bit(4) << 1) | (bit(3) << 2) | (bit(2) << 3) | (bit(1) << 4)
}

/// The relations that can occur at width `w`.
fn realizable(w: u16) -> u8 {
    if w == 1 { 0b01101 } else { ALL }
}

// ----- interval sets ------------------------------------------------------------------------------

/// Sorted, disjoint, non-adjacent unsigned intervals.
type Set = Vec<(BitVec, BitVec)>;

fn one(w: crate::Width) -> BitVec {
    BitVec::one(w)
}

fn inc(v: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Add, v, &one(v.width()))
}

fn dec(v: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Sub, v, &one(v.width()))
}

fn ult(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Ult, a, b)
}

fn ule(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Ule, a, b)
}

fn full(w: crate::Width) -> Set {
    vec![(BitVec::zero(w), BitVec::ones(w))]
}

fn complement(s: &Set, w: crate::Width) -> Set {
    let mut out = Vec::new();
    let mut next = Some(BitVec::zero(w));
    for (lo, hi) in s {
        if let Some(n) = next
            && ult(&n, lo)
        {
            out.push((n, dec(lo)));
        }
        next = if hi.is_ones() { None } else { Some(inc(hi)) };
    }
    if let Some(n) = next {
        out.push((n, BitVec::ones(w)));
    }
    out
}

fn intersect(a: &Set, b: &Set) -> Set {
    let mut out = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        let lo = if ult(&a[i].0, &b[j].0) {
            b[j].0
        } else {
            a[i].0
        };
        let hi = if ult(&a[i].1, &b[j].1) {
            a[i].1
        } else {
            b[j].1
        };
        if ule(&lo, &hi) {
            out.push((lo, hi));
        }
        if ult(&a[i].1, &b[j].1) {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

fn union(a: &Set, b: &Set, w: crate::Width) -> Set {
    complement(&intersect(&complement(a, w), &complement(b, w)), w)
}

fn sym_diff(a: &Set, b: &Set, w: crate::Width) -> Set {
    union(
        &intersect(a, &complement(b, w)),
        &intersect(&complement(a, w), b),
        w,
    )
}

/// The values `x` for which `x op c` holds.
fn interval_of(op: CmpOp, c: &BitVec, x_first: bool) -> Set {
    let w = c.width();
    let zero = BitVec::zero(w);
    let max = BitVec::ones(w);
    let smin = BitVec::smin(w);
    let smax = BitVec::smax(w);
    // A signed interval [a, b] (a <=s b) as unsigned intervals.
    let signed = |a: BitVec, b: BitVec| -> Set {
        if a.msb() == b.msb() {
            vec![(a, b)]
        } else {
            vec![(zero, b), (a, max)]
        }
    };
    match (op, x_first) {
        (CmpOp::Eq, _) => vec![(*c, *c)],
        (CmpOp::Ne, _) => complement(&vec![(*c, *c)], w),
        // x <u c / x <=u c
        (CmpOp::Ult, true) if c.is_zero() => Vec::new(),
        (CmpOp::Ult, true) => vec![(zero, dec(c))],
        (CmpOp::Ule, true) => vec![(zero, *c)],
        // c <u x / c <=u x
        (CmpOp::Ult, false) if c.is_ones() => Vec::new(),
        (CmpOp::Ult, false) => vec![(inc(c), max)],
        (CmpOp::Ule, false) => vec![(*c, max)],
        // x <s c / x <=s c
        (CmpOp::Slt, true) if *c == smin => Vec::new(),
        (CmpOp::Slt, true) => signed(smin, dec(c)),
        (CmpOp::Sle, true) => signed(smin, *c),
        // c <s x / c <=s x
        (CmpOp::Slt, false) if *c == smax => Vec::new(),
        (CmpOp::Slt, false) => signed(inc(c), smax),
        (CmpOp::Sle, false) => signed(*c, smax),
    }
}

// ----- per-node descriptions ------------------------------------------------------------------------

/// What a 1-bit node says, if it is in a fragment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Info {
    /// A constant truth value.
    Const(bool),
    /// A set of relations of `x` to `y` (`x < y` by index).
    Pair(u32, u32, u8),
    /// A set of values of `x`.
    Values(u32, Set),
    /// Neither (or over a cap).
    Opaque,
}

fn boolean_op(op: OpCode) -> bool {
    matches!(op, OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not)
}

fn leaf(cx: &Context, i: u32) -> Info {
    let n = cx.node(i);
    if let Some(v) = cx.const_val(i) {
        return if n.width == 1 {
            Info::Const(!v.is_zero())
        } else {
            Info::Opaque
        };
    }
    let Some(op) = n.op.as_cmp() else {
        return Info::Opaque;
    };
    match (cx.const_val(n.a), cx.const_val(n.b)) {
        (Some(_), Some(_)) => Info::Opaque,
        (None, Some(c)) => Info::Values(n.a, interval_of(op, &c, true)),
        (Some(c), None) => Info::Values(n.b, interval_of(op, &c, false)),
        (None, None) if n.a == n.b => Info::Opaque,
        (None, None) if n.a < n.b => Info::Pair(n.a, n.b, pred_set(op)),
        (None, None) => Info::Pair(n.b, n.a, swap_set(pred_set(op))),
    }
}

/// Combines operand descriptions under a boolean operator (`None` operand for `Not`).
fn combine(cx: &Context, op: OpCode, a: &Info, b: Option<&Info>) -> Info {
    // A constant becomes the neutral description of the other side's fragment.
    let lift = |c: bool, other: &Info| -> Info {
        match other {
            Info::Pair(x, y, _) => Info::Pair(*x, *y, if c { ALL } else { 0 }),
            Info::Values(x, _) => {
                let w = cx.width_of(*x);
                Info::Values(*x, if c { full(w) } else { Vec::new() })
            }
            _ => Info::Const(c),
        }
    };
    let (a, b) = match (a, b) {
        (Info::Const(c), Some(o)) => (lift(*c, o), Some(o.clone())),
        (o, Some(Info::Const(c))) => (o.clone(), Some(lift(*c, o))),
        (o, b) => (o.clone(), b.cloned()),
    };
    let bool_op = |x: bool, y: bool| match op {
        OpCode::And => x & y,
        OpCode::Or => x | y,
        _ => x ^ y,
    };
    match (op, &a, &b) {
        (OpCode::Not, Info::Const(c), None) => Info::Const(!c),
        (OpCode::Not, Info::Pair(x, y, s), None) => Info::Pair(*x, *y, !s & ALL),
        (OpCode::Not, Info::Values(x, s), None) => Info::Values(*x, complement(s, cx.width_of(*x))),
        (_, Info::Const(p), Some(Info::Const(q))) => Info::Const(bool_op(*p, *q)),
        (_, Info::Pair(x, y, s), Some(Info::Pair(x2, y2, t))) if x == x2 && y == y2 => {
            let r = match op {
                OpCode::And => s & t,
                OpCode::Or => s | t,
                _ => s ^ t,
            };
            Info::Pair(*x, *y, r)
        }
        (_, Info::Values(x, s), Some(Info::Values(x2, t))) if x == x2 => {
            let w = cx.width_of(*x);
            let r = match op {
                OpCode::And => intersect(s, t),
                OpCode::Or => union(s, t, w),
                _ => sym_diff(s, t, w),
            };
            if r.len() > MAX_INTERVALS {
                Info::Opaque
            } else {
                Info::Values(*x, r)
            }
        }
        _ => Info::Opaque,
    }
}

fn info_of(r: &mut Runner<'_, '_>, cx: &Context, root: u32) -> Result<Info, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.compares.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        if node.width != 1 || !boolean_op(node.op) {
            r.compares.insert(i, leaf(cx, i));
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if !r.compares.contains_key(&c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        r.meter.check()?;
        let a = r.compares[&node.a].clone();
        let info = if node.op == OpCode::Not {
            combine(cx, OpCode::Not, &a, None)
        } else {
            let b = r.compares[&node.b].clone();
            combine(cx, node.op, &a, Some(&b))
        };
        r.compares.insert(i, info);
    }
    Ok(r.compares[&root].clone())
}

// ----- emission -------------------------------------------------------------------------------------

fn bool_const(r: &mut Runner<'_, '_>, cx: &mut Context, v: bool) -> Result<u32, Stop> {
    r.build(cx, |cx| cx.mk_const(&BitVec::from_bool(v)))
}

/// A comparison `x op c` or `c op x`.
fn cmp_const(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    op: CmpOp,
    x: u32,
    c: &BitVec,
    x_first: bool,
) -> Result<u32, Stop> {
    let c = *c;
    r.build(cx, |cx| {
        let k = cx.mk_const(&c)?;
        if x_first {
            cx.c_cmp(op, x, k)
        } else {
            cx.c_cmp(op, k, x)
        }
    })
}

fn emit_pair(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    y: u32,
    s: u8,
) -> Result<Option<u32>, Stop> {
    let real = realizable(cx.wid(x));
    let s = s & real;
    if s == 0 {
        return bool_const(r, cx, false).map(Some);
    }
    if s == real {
        return bool_const(r, cx, true).map(Some);
    }
    for op in [
        CmpOp::Eq,
        CmpOp::Ne,
        CmpOp::Ult,
        CmpOp::Ule,
        CmpOp::Slt,
        CmpOp::Sle,
    ] {
        if pred_set(op) & real == s {
            return r.build(cx, |cx| cx.c_cmp(op, x, y)).map(Some);
        }
        if swap_set(pred_set(op)) & real == s {
            return r.build(cx, |cx| cx.c_cmp(op, y, x)).map(Some);
        }
    }
    Ok(None)
}

fn emit_values(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    s: &Set,
) -> Result<Option<u32>, Stop> {
    let w = cx.width_of(x);
    let (zero, max, smin, smax) = (
        BitVec::zero(w),
        BitVec::ones(w),
        BitVec::smin(w),
        BitVec::smax(w),
    );
    if s.is_empty() {
        return bool_const(r, cx, false).map(Some);
    }
    if *s == full(w) {
        return bool_const(r, cx, true).map(Some);
    }
    // One wrapped interval [lo, hi]: either one interval, or two touching both ends.
    let (lo, hi) = match s.as_slice() {
        [(lo, hi)] => (*lo, *hi),
        [(z, hi), (lo, m)] if z.is_zero() && m.is_ones() => (*lo, *hi),
        _ => return Ok(None),
    };
    let comp = complement(s, w);
    Ok(Some(if lo == hi {
        cmp_const(r, cx, CmpOp::Eq, x, &lo, true)?
    } else if let [(a, b)] = comp.as_slice()
        && a == b
    {
        cmp_const(r, cx, CmpOp::Ne, x, a, true)?
    } else if lo == zero {
        cmp_const(r, cx, CmpOp::Ule, x, &hi, true)?
    } else if hi == max {
        cmp_const(r, cx, CmpOp::Ule, x, &lo, false)?
    } else if lo == smin {
        cmp_const(r, cx, CmpOp::Sle, x, &hi, true)?
    } else if hi == smax {
        cmp_const(r, cx, CmpOp::Sle, x, &lo, false)?
    } else {
        // x - lo <=u hi - lo (wrapping).
        let span = BitVec::bin_unchecked(BinOp::Sub, &hi, &lo);
        r.build(cx, |cx| {
            let l = cx.mk_const(&lo)?;
            let d = cx.c_bin(BinOp::Sub, x, l)?;
            let k = cx.mk_const(&span)?;
            cx.c_cmp(CmpOp::Ule, d, k)
        })?
    }))
}

/// The compares pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    if node.width != 1 || !(boolean_op(node.op) || node.op.as_cmp().is_some()) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let info = info_of(r, cx, n)?;
    let before = cx.len() as u32;
    let (e, atoms) = match &info {
        Info::Pair(x, y, s) => (emit_pair(r, cx, *x, *y, *s)?, vec![*x, *y]),
        Info::Values(x, s) => (emit_values(r, cx, *x, s)?, vec![*x]),
        Info::Const(v) if boolean_op(node.op) => (Some(bool_const(r, cx, *v)?), Vec::new()),
        _ => (None, Vec::new()),
    };
    let Some(e) = e else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    finish(r, cx, PassKind::Compares, n, e, before, &atoms, Fin::FINAL)
}
