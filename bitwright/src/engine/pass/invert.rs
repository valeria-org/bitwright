//! The invert pass: equalities through invertible maps (see `crate::invert`).
//!
//! At `a == b` and `a != b`:
//!
//! - both sides one injective layer over different operands (`f(x) == f(y)`, `f` fixed by the
//!   operands the sides share): the operands are compared instead, layer after layer;
//! - against a constant (`f(x) == c`): `x` is compared with the preimage `f⁻¹(c)`, through
//!   every layer whose parameters are constants, and the comparison is a constant when `c` has
//!   no preimage;
//! - against a constant through an even multiplier (`x·c == k`, `x << t == k`): the low bits
//!   of `x` are compared with the preimage of `k` without its low zeros, and the comparison is
//!   a constant when `k` has none there;
//! - some bits of a value against a constant (`(y | m) == k`, and `(y & c) == k` with `y` a
//!   slice or a zero extension): the same bits of the value itself, `(x & c') == k'`, or the
//!   slice of them where they are one run;
//! - a value the facts leave one bit of against 0 or 1: that bit or its complement, the
//!   truncation pushed into the value, when that is a smaller tree;
//! - when none of those decides it, truncations and slices (`extract<lo, k>(f(x))`) pushed
//!   into their operands and tried again at their own width, where a map that is no bijection at
//!   the full width can be one of the bits read (`trunc<17>(2x² + x) == trunc<17>(2y² + y)` is
//!   `trunc<17>(x) == trunc<17>(y)`): committed only when the result is a smaller tree;
//! - `a₁ | … | aₙ == 0` (and `a₁ & … & aₙ == ones`): every `aᵢ` is solved against the constant
//!   on its own, and the answers are intersected, so one value compared with two different
//!   constants is false;
//! - the sides `select` trees: their leaves are peeled together through one common injective
//!   layer, a constant leaf by its preimage (`select(c, x + 1, y + 1) == z + 1` is
//!   `select(c, x, y) == z`).
//!
//! At `a <u b`, `a <=u b`, `a <s b` and `a <=s b` (see `crate::invert::monotone`):
//!
//! - a sign test of a value rotated or shifted left by a constant: the bit of the value that
//!   lands on top, or its complement (`rotl(x, 56) <s 0` is `extract<7, 1>(x)`);
//! - both sides one strictly monotone layer over different operands (`f(x) <u f(y)`), or
//!   `select` trees whose leaves all are: the operands (the trees over the inner values) are
//!   compared instead, in the order the layer is monotone from, swapped for a decreasing layer,
//!   layer after layer (`zext(x) <s zext(y)` is `x <u y`, `~x <u ~y` is `y <u x`, `x + k <u
//!   y + k` is `x <u y` where neither sum wraps, `select(c, ~x, ~y) <u ~z` is
//!   `z <u select(c, x, y)`);
//! - against a constant on either side (`f(x) <u c`): `x` is compared with the threshold where
//!   the comparison changes, found by bisection over `x`'s range, or the comparison is a
//!   constant (`zext<16>(x) <u 300` at 8 bits is true).
//!
//! A bijection does not preserve order, so the injective layers above are never used for
//! orderings; a strictly monotone layer is injective, but its monotonicity usually rests on
//! facts, so equalities keep to the layers above. A rewrite replaces a comparison by one of proper subterms of its operands and a
//! constant, or by a constant, so like a rule it strictly decreases the termination order, and
//! it is committed whether or not the operands are shared elsewhere; a split is committed only
//! when its result is a smaller tree.

use super::{Accept, By, Fin, PassKind, Reject, Runner, Step, Stop, discard, facts};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::facts::Facts;
use crate::hash::IdMap;
use crate::invert::monotone::{self, Inner, Order};
use crate::invert::{self, MAX_SPLIT, Oracle, Solved};
use crate::ops::{BinOp, CmpOp};

/// Facts and work for the analysis, from the call: facts under the run's assumptions and fact
/// budget (what they rely on, and whether a cap cut them, collected in `fin`), work charged to
/// `pass_work`.
struct Calls<'x, 'r, 'a> {
    r: &'x mut Runner<'r, 'a>,
    fin: Fin,
}

impl Oracle for Calls<'_, '_, '_> {
    type Err = Stop;

    fn facts(&mut self, cx: &mut Context, i: u32) -> Result<Option<Facts>, Stop> {
        let (f, fin) = facts(self.r, cx, i)?;
        self.fin = self.fin.and(fin);
        Ok(f)
    }

    fn charge(&mut self, units: u64) -> Result<(), Stop> {
        self.r.meter.charge(Counter::PassWork, units)?;
        Ok(())
    }
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry(PassKind::Invert.name()).or_default()
}

/// The invert pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let Some(op) = node.op.as_cmp() else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    let before = cx.len() as u32;
    let mut o = Calls { r, fin: Fin::FINAL };
    let e = if op.is_commutative() {
        // Constants are on the right of a stored equality.
        match cx.const_val(node.b) {
            Some(c) => {
                let join = cx.node(node.a).op;
                if (join == OpCode::Or && c.is_zero()) || (join == OpCode::And && c.is_ones()) {
                    split(cx, &mut o, op, n, node.a, &c, before)?
                } else {
                    match solve(cx, &mut o, op, node.a, &c)? {
                        Some(e) => Some(e),
                        None => match halved(cx, &mut o, op, node.a, &c)? {
                            Some(e) => Some(e),
                            None => match masked(cx, &mut o, op, node.a, &c)? {
                                Some(e) => Some(e),
                                None => match flag(cx, &mut o, op, n, node.a, &c)? {
                                    Some(e) => Some(e),
                                    None => match narrowed(cx, &mut o, node.a)? {
                                        Some(a) => solve(cx, &mut o, op, a, &c)?,
                                        None => None,
                                    }
                                    .filter(|&e| smaller(cx, e, n)),
                                },
                            },
                        },
                    }
                }
            }
            None => match cancel(cx, &mut o, op, n, node.a, node.b)? {
                Some(e) => Some(e),
                None => match (narrowed(cx, &mut o, node.a)?, narrowed(cx, &mut o, node.b)?) {
                    (Some(a), Some(b)) => cancel(cx, &mut o, op, n, a, b)?,
                    _ => None,
                }
                .filter(|&e| smaller(cx, e, n)),
            },
        }
    } else {
        match (cx.const_val(node.a), cx.const_val(node.b)) {
            (_, Some(c)) => match sign_bit(cx, &mut o, op, node.a, &c, false)? {
                Some(e) => Some(e),
                None => solve_order(cx, &mut o, op, node.a, &c, false)?,
            },
            (Some(c), None) => match sign_bit(cx, &mut o, op, node.b, &c, true)? {
                Some(e) => Some(e),
                None => solve_order(cx, &mut o, op, node.b, &c, true)?,
            },
            (None, None) => cancel_order(cx, &mut o, op, node.a, node.b)?,
        }
    };
    let e = match e {
        Some(e) => Some(e),
        None => fitted(cx, &mut o, op, n, node.a, node.b)?,
    };
    let fin = o.fin;
    let e = match e {
        Some(e) if e != n => e,
        _ => {
            // What a narrowing built for nothing.
            discard(r, cx, before);
            count(r).noop += 1;
            return Ok(Step::Normal(fin));
        }
    };
    match r.accept(cx, By::Pass(PassKind::Invert.name()), true, n, e, fin.rel)? {
        Accept::Yes => {
            count(r).changed += 1;
            Ok(Step::To(e, fin))
        }
        Accept::Vetoed => {
            count(r).rejected += 1;
            discard(r, cx, before);
            Ok(Step::Normal(fin))
        }
        Accept::Rejected(reason) => {
            count(r).rejected += 1;
            discard(r, cx, before);
            if matches!(reason, Reject::Width | Reject::Verify | Reject::Tripwire) {
                r.quarantined_passes.push(PassKind::Invert);
                r.stats.quarantined += 1;
            }
            Ok(Step::Normal(fin))
        }
    }
}

/// `x·c op k` for an even constant `c = 2^t·d` (or `x << t op k`): the product's low `t`
/// bits are zero, so the comparison is decided when `k`'s are not, and otherwise it is
/// `trunc<w−t>(x)·d op k >> t` at `w − t` bits, where the odd `d` has an inverse:
/// `trunc<w−t>(x) op (k >> t)·d⁻¹`. A dispatcher compares one state `x` with its cases through
/// several such multipliers (`x·c₁ == k₁`, `x·c₂ == k₂`, …), and these are then comparisons of
/// the same low bits of `x` with the same constants.
fn halved(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    lhs: u32,
    k: &BitVec,
) -> Result<Option<u32>, Stop> {
    let node = cx.node(lhs);
    let w = node.width;
    let zeros = |v: &BitVec| (0..w).take_while(|&i| v.bit(i) == Some(false)).count() as u16;
    let (x, t, odd) = match node.op {
        OpCode::Mul => {
            let (x, c) = match (cx.const_val(node.a), cx.const_val(node.b)) {
                (None, Some(c)) => (node.a, c),
                (Some(c), None) => (node.b, c),
                _ => return Ok(None),
            };
            (x, zeros(&c), Some(c))
        }
        OpCode::Shl => match cx.const_val(node.b).and_then(|c| c.to_u64()) {
            Some(t) if t < u64::from(w) => (node.a, t as u16, None),
            _ => return Ok(None),
        },
        _ => return Ok(None),
    };
    if t == 0 || t >= w {
        return Ok(None);
    }
    o.r.meter.charge(Counter::PassWork, 1)?;
    if zeros(k) < t {
        return Ok(Some(truth(o, cx, op == CmpOp::Ne)?));
    }
    let m = w - t;
    let width = crate::Width::new(m).map_err(|e| Stop::Error(e.into()))?;
    let slice = |v: &BitVec| v.extract(t, width).map_err(|e| Stop::Error(e.into()));
    let k = slice(k)?;
    let odd = match odd {
        Some(c) => Some(slice(&c)?),
        None => None,
    };
    let narrow = o.r.build(cx, |cx| {
        let low = cx.c_extract(x, 0, m)?;
        match odd {
            Some(d) if d != BitVec::one(width) => {
                let d = cx.mk_const(&d)?;
                cx.c_bin(BinOp::Mul, low, d)
            }
            _ => Ok(low),
        }
    })?;
    Ok(Some(match solve(cx, o, op, narrow, &k)? {
        Some(e) => e,
        None => compare(o, cx, op, narrow, &k)?,
    }))
}

/// `(y | m) op k` and `(y & c) op k` as a comparison of bits of the value `y` is a slice or
/// a zero extension of: `(y | m) == k` reads the bits of `y` outside `m` (and is false when
/// `k` lacks a bit of `m`), and bits of `extract<lo, n>(x)` are bits of `x`, so both are
/// `(x & c') op k'` over the value itself (`extract<lo', n'>(x) op k'` where the bits are one
/// run). One state read through slices of several widths (`extract<22, 29>(x) | m₁ == k₁`,
/// `extract<22, 27>(x) | m₂ == k₂`) is then compared once. `None` when the comparison is that
/// already.
fn masked(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    lhs: u32,
    k: &BitVec,
) -> Result<Option<u32>, Stop> {
    let node = cx.node(lhs);
    let constant = |a: u32, b: u32| match (cx.const_val(a), cx.const_val(b)) {
        (None, Some(c)) => Some((a, c)),
        (Some(c), None) => Some((b, c)),
        _ => None,
    };
    let and = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::And, a, b);
    let not = |a: &BitVec| BitVec::un_unchecked(crate::ops::UnOp::Not, a);
    // The value, the bits of it compared, and what they are compared with.
    let (mut y, mut c, mut k, mut changed) = match node.op {
        OpCode::Or => {
            let Some((y, m)) = constant(node.a, node.b) else {
                return Ok(None);
            };
            if and(k, &m) != m {
                return Ok(Some(truth(o, cx, op == CmpOp::Ne)?));
            }
            (y, not(&m), and(k, &not(&m)), true)
        }
        OpCode::And => {
            let Some((y, c)) = constant(node.a, node.b) else {
                return Ok(None);
            };
            if !and(k, &not(&c)).is_zero() {
                return Ok(Some(truth(o, cx, op == CmpOp::Ne)?));
            }
            (y, c, *k, false)
        }
        _ => return Ok(None),
    };
    o.r.meter.charge(Counter::PassWork, 1)?;
    loop {
        let n = cx.node(y);
        match n.op {
            OpCode::Extract => {
                let wide = cx.width_of(n.a);
                let at = BitVec::wrapping_from_u64(wide, u64::from(n.b));
                let up = |v: &BitVec| -> Result<BitVec, Stop> {
                    let z = v.zext(wide).map_err(|e| Stop::Error(e.into()))?;
                    Ok(BitVec::bin_unchecked(BinOp::Shl, &z, &at))
                };
                (c, k) = (up(&c)?, up(&k)?);
                y = n.a;
            }
            OpCode::Zext => {
                let narrow = cx.width_of(n.a);
                let low = |v: &BitVec| v.trunc(narrow).map_err(|e| Stop::Error(e.into()));
                // The extension's high bits are zero.
                let back = low(&k)?
                    .zext(k.width())
                    .map_err(|e| Stop::Error(e.into()))?;
                if back != k {
                    return Ok(Some(truth(o, cx, op == CmpOp::Ne)?));
                }
                (c, k) = (low(&c)?, low(&k)?);
                y = n.a;
            }
            _ => break,
        }
        changed = true;
    }
    if !changed {
        return Ok(None);
    }
    // One run of bits is a slice (the form a comparison of a field has); other bits are
    // read under their mask.
    let w = c.width().bits();
    let set = |i: u16| c.bit(i) == Some(true);
    let lo = (0..w).take_while(|&i| !set(i)).count() as u16;
    let len = (lo..w).take_while(|&i| set(i)).count() as u16;
    if len > 0 && (lo + len..w).all(|i| !set(i)) {
        let width = crate::Width::new(len).map_err(|e| Stop::Error(e.into()))?;
        let k = k.extract(lo, width).map_err(|e| Stop::Error(e.into()))?;
        let field = o.r.build(cx, |cx| cx.c_extract(y, lo, len))?;
        return Ok(Some(compare(o, cx, op, field, &k)?));
    }
    let bits = o.r.build(cx, |cx| {
        let c = cx.mk_const(&c)?;
        cx.c_bin(BinOp::And, y, c)
    })?;
    Ok(Some(compare(o, cx, op, bits, &k)?))
}

/// `x op k` for `k` 0 or 1 and an `x` whose other bits the facts know zero: the low bit of
/// `x` or its complement, the truncation pushed into `x`, when that is a smaller tree than
/// the comparison `n`. A flag kept in a byte and tested there (`((zext<8>(a) & zext<8>(b)) ^ 1)
/// & zext<8>(c) != 1`) is then the one-bit function it computes (`~(~(a & b) & c)`).
fn flag(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    n: u32,
    lhs: u32,
    k: &BitVec,
) -> Result<Option<u32>, Stop> {
    let w = k.width();
    let one = *k == BitVec::one(w);
    if w.bits() < 2 || !(one || k.is_zero()) {
        return Ok(None);
    }
    let Some(f) = o.facts(cx, lhs)? else {
        return Ok(None);
    };
    let high = BitVec::un_unchecked(crate::ops::UnOp::Not, &BitVec::one(w));
    if BitVec::bin_unchecked(BinOp::And, &f.known.known_zero(), &high) != high {
        return Ok(None);
    }
    let low = o.r.build(cx, |cx| cx.c_extract(lhs, 0, 1))?;
    let low = narrowed(cx, o, low)?.unwrap_or(low);
    // `x == 1` and `x != 0` are the bit; `x != 1` and `x == 0` its complement.
    let e = match (op == CmpOp::Eq) == one {
        true => low,
        false => o.r.build(cx, |cx| cx.c_un(crate::ops::UnOp::Not, low))?,
    };
    Ok(smaller(cx, e, n).then_some(e))
}

/// A truncation or slice `extract<lo, k>(x)` pushed into `x` (see `casts`), when that is
/// another node: a map that is no bijection at `x`'s width can be one of the bits the slice
/// reads (`trunc<17>(2x² + x)` is `2t² + t` over `t = trunc<17>(x)`, a bijection of `t`).
fn narrowed(cx: &mut Context, o: &mut Calls<'_, '_, '_>, s: u32) -> Result<Option<u32>, Stop> {
    let node = cx.node(s);
    if node.op != OpCode::Extract {
        return Ok(None);
    }
    let Some((e, fin)) = super::casts::narrowed(o.r, cx, node.a, node.b as u16, node.width)? else {
        return Ok(None);
    };
    o.fin = o.fin.and(fin);
    Ok((e != s).then_some(e))
}

/// The fewest low bits `i` fits in: its width less its high bits known zero.
fn fits(cx: &mut Context, o: &mut Calls<'_, '_, '_>, i: u32) -> Result<u16, Stop> {
    let w = cx.wid(i);
    Ok(match o.facts(cx, i)? {
        Some(f) => w - f.known().leading_known_zeros() as u16,
        None => w,
    })
}

/// `a op b` (the comparison `n`) at the low `k` bits both sides fit in, when that is fewer than
/// their width: each side's truncation pushed into it (see `casts`), so
/// `(x & 0x1fffff) <u (y & 0x1fffff)` is `trunc<21>(x) <u trunc<21>(y)` and
/// `trunc<16>(x & 0x3fff) == trunc<16>(y & 0x3fff)` is `trunc<14>(x) == trunc<14>(y)`. A value
/// below `2^k` is `zext(trunc<k>(v))`, which is injective and increasing, so equality and the
/// unsigned orders carry over; with `k` less than the width both sides are nonnegative, so a
/// signed order is the unsigned one. The narrow sides are new nodes that may stand beside the
/// wide ones they read, so this is committed by the passes' rule, only when the DAG gets no
/// larger (a tie only for a smaller tree: comparisons of one shared wide operand narrow one at
/// a time, as `y` in `(y & m) <u (x & m)` and `(y & m) <u (z & m)`): a narrowed `<u` beside
/// the `==` of the same wide operands would split the pair the compares pass joins
/// (`(a == b) | (a <u b)`), so it waits for that join.
fn fitted(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    n: u32,
    a: u32,
    b: u32,
) -> Result<Option<u32>, Stop> {
    let w = cx.wid(a);
    if w <= 1 {
        return Ok(None);
    }
    let k = fits(cx, o, a)?.max(fits(cx, o, b)?).max(1);
    if k >= w {
        return Ok(None);
    }
    let Some((x, fx, mut atoms)) = super::casts::narrowed_from(o.r, cx, a, 0, k)? else {
        return Ok(None);
    };
    let Some((y, fy, more)) = super::casts::narrowed_from(o.r, cx, b, 0, k)? else {
        return Ok(None);
    };
    o.fin = o.fin.and(fx).and(fy);
    atoms.extend(more);
    atoms.sort_unstable();
    atoms.dedup();
    let op = match op {
        CmpOp::Slt => CmpOp::Ult,
        CmpOp::Sle => CmpOp::Ule,
        op => op,
    };
    let e = o.r.build(cx, |cx| cx.c_cmp(op, x, y))?;
    if e == n {
        return Ok(None);
    }
    match super::ties_smaller(o.r, cx, n, e, &atoms)? {
        Ok(()) => Ok(Some(e)),
        Err(more) => {
            o.fin = o.fin.and(more);
            Ok(None)
        }
    }
}

/// Whether `e` is a smaller tree than `n`: a comparison of narrowed sides is a comparison of
/// subterms of new nodes, committed only when it is smaller (which also orders it).
fn smaller(cx: &Context, e: u32, n: u32) -> bool {
    let size = |i: u32| cx.tree_size(cx.handle(i)).unwrap_or(u32::MAX);
    size(e) < size(n)
}

fn truth(o: &mut Calls<'_, '_, '_>, cx: &mut Context, v: bool) -> Result<u32, Stop> {
    o.r.build(cx, |cx| cx.mk_const(&BitVec::from_bool(v)))
}

/// `x op v`.
fn compare(
    o: &mut Calls<'_, '_, '_>,
    cx: &mut Context,
    op: CmpOp,
    x: u32,
    v: &BitVec,
) -> Result<u32, Stop> {
    let v = *v;
    o.r.build(cx, |cx| {
        let k = cx.mk_const(&v)?;
        cx.c_cmp(op, x, k)
    })
}

/// The leaves of the `select` trees at `a` and `b` (the nodes under their arms that are not
/// selects, without repeats), and whether any select was seen; `None` past [`MAX_SPLIT`]
/// leaves.
fn leaves(
    cx: &Context,
    o: &mut Calls<'_, '_, '_>,
    a: u32,
    b: u32,
) -> Result<Option<(Vec<u32>, bool)>, Stop> {
    let mut out = Vec::new();
    let mut seen = false;
    let mut stack = vec![b, a];
    while let Some(i) = stack.pop() {
        o.charge(1)?;
        let node = cx.node(i);
        if node.op == OpCode::Select {
            seen = true;
            stack.push(node.c);
            stack.push(node.b);
        } else if out.contains(&i) {
        } else if out.len() >= MAX_SPLIT {
            return Ok(None);
        } else {
            out.push(i);
        }
    }
    Ok(Some((out, seen)))
}

/// `t` with each leaf replaced by its inner value (`map`), its selects rebuilt.
fn relabel(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    t: u32,
    map: &IdMap<u32, u32>,
) -> Result<u32, Stop> {
    if let Some(&x) = map.get(&t) {
        return Ok(x);
    }
    let node = cx.node(t);
    debug_assert_eq!(node.op, OpCode::Select);
    let (c, p, q) = (node.a, node.b, node.c);
    let p = relabel(cx, o, p, map)?;
    let q = relabel(cx, o, q, map)?;
    o.r.build(cx, |cx| cx.c_select(c, p, q))
}

/// The leaves of `a` and `b` as their inner values: the two trees over them.
fn relabelled(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    a: u32,
    b: u32,
    leaves: &[u32],
    inners: &[Inner],
) -> Result<(u32, u32), Stop> {
    let mut map = IdMap::default();
    for (&l, x) in leaves.iter().zip(inners) {
        let x = match x {
            Inner::Node(x) => *x,
            Inner::Const(v) => {
                let v = *v;
                o.r.build(cx, |cx| cx.mk_const(&v))?
            }
        };
        map.insert(l, x);
    }
    Ok((relabel(cx, o, a, &map)?, relabel(cx, o, b, &map)?))
}

/// `f(x) op f(y)` as `x op y`, through every common injective layer; then semantic outer-affine /
/// GF(2)-matrix reduction when it strictly shrinks the comparison tree; then, when the sides are
/// `select` trees, their leaves peeled together through every common injective layer.
fn cancel(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    cmp_node: u32,
    a: u32,
    b: u32,
) -> Result<Option<u32>, Stop> {
    let (mut x, mut y) = (a, b);
    let mut peeled = false;
    while let Some((p, q)) = invert::cancel_layer(cx, o, x, y)? {
        o.charge(1)?;
        (x, y) = (p, q);
        peeled = true;
    }
    if let Some(sem) = cancel_semantic(cx, o, op, cmp_node, x, y)? {
        return Ok(Some(sem));
    }
    if !peeled {
        while let Some((ls, true)) = leaves(cx, o, x, y)? {
            let Some(inners) = invert::cancel_leaves(cx, o, &ls)? else {
                break;
            };
            (x, y) = relabelled(cx, o, x, y, &ls, &inners)?;
            peeled = true;
        }
    }
    if !peeled {
        return Ok(None);
    }
    Ok(Some(o.r.build(cx, |cx| cx.c_cmp(op, x, y))?))
}

/// Peels mismatched constant-parameter modular-affine bijections (`alpha_1 * d_1 + beta_1` vs
/// `alpha_2 * d_2 + beta_2`) or full-rank GF(2) maps differing by a constant (`M·d_1 ⊕ c_1` vs
/// `M·d_2 ⊕ c_2`), committing only when the comparison becomes a constant or strictly smaller tree.
fn cancel_semantic(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    cmp_node: u32,
    x: u32,
    y: u32,
) -> Result<Option<u32>, Stop> {
    if x == y || cx.wid(x) != cx.wid(y) {
        return Ok(None);
    }
    let w = cx.width_of(x);
    if w.bits() >= 2 {
        let ma = invert::peel_mod_affine(cx, x);
        let mb = invert::peel_mod_affine(cx, y);
        if ma.is_some() || mb.is_some() {
            let id = |v: u32| invert::ModAffine {
                inner: v,
                scale: BitVec::one(w),
                offset: BitVec::zero(w),
                depth: 0,
            };
            let (m1, m2) = (ma.unwrap_or_else(|| id(x)), mb.unwrap_or_else(|| id(y)));
            if m1.depth + m2.depth >= 2 && m1.inner != m2.inner {
                o.charge(u64::from(m1.depth + m2.depth))?;
                let mut best: Option<(u32, u32)> = None;
                for (lhs, rhs) in [(&m1, &m2), (&m2, &m1)] {
                    let Some(inv) = invert::mul_inverse(&lhs.scale) else {
                        continue;
                    };
                    let gamma = BitVec::bin_unchecked(BinOp::Mul, &inv, &rhs.scale);
                    let diff = BitVec::bin_unchecked(BinOp::Sub, &rhs.offset, &lhs.offset);
                    let delta = BitVec::bin_unchecked(BinOp::Mul, &inv, &diff);
                    let cand = o.r.build(cx, |cx| {
                        let scaled = if gamma == BitVec::one(w) {
                            rhs.inner
                        } else if gamma.is_ones() {
                            cx.c_un(crate::ops::UnOp::Neg, rhs.inner)?
                        } else {
                            let g = cx.mk_const(&gamma)?;
                            cx.c_bin(BinOp::Mul, rhs.inner, g)?
                        };
                        let full_rhs = if delta.is_zero() {
                            scaled
                        } else {
                            let d = cx.mk_const(&delta)?;
                            cx.c_bin(BinOp::Add, scaled, d)?
                        };
                        cx.c_cmp(op, lhs.inner, full_rhs)
                    })?;
                    let sz = cx.tree_size(cx.handle(cand)).unwrap_or(u32::MAX);
                    if best.is_none_or(|(_, bsz)| sz < bsz) {
                        best = Some((cand, sz));
                    }
                }
                if let Some((cand, _)) = best
                    && smaller(cx, cand, cmp_node)
                {
                    return Ok(Some(cand));
                }
            }
        }
    }
    if let (Some(ga), Some(gb)) = (
        invert::peel_gf2_injective(cx, o, x)?,
        invert::peel_gf2_injective(cx, o, y)?,
    ) {
        for g1 in ga.iter().rev() {
            for g2 in gb.iter().rev() {
                if cx.wid(g1.inner) != cx.wid(g2.inner) || g1.rows != g2.rows {
                    continue;
                }
                let wd = cx.width_of(g1.inner);
                if g1.konst == g2.konst {
                    let cand = o.r.build(cx, |cx| cx.c_cmp(op, g1.inner, g2.inner))?;
                    if smaller(cx, cand, cmp_node) {
                        return Ok(Some(cand));
                    }
                    continue;
                }
                let rhs_bits: Vec<bool> = (0..g1.rows.len() as u16)
                    .map(|k| g1.konst.bit(k) != g2.konst.bit(k))
                    .collect();
                match invert::gf2::solve(&g1.rows, &rhs_bits, u32::from(wd.bits())) {
                    Some(None) => return Ok(Some(truth(o, cx, op == CmpOp::Ne)?)),
                    Some(Some(row)) => {
                        let delta = BitVec::wrapping_from_limbs(wd, &row);
                        let cand = o.r.build(cx, |cx| {
                            let k = cx.mk_const(&delta)?;
                            let rx = cx.c_bin(BinOp::Xor, g2.inner, k)?;
                            cx.c_cmp(op, g1.inner, rx)
                        })?;
                        if smaller(cx, cand, cmp_node) {
                            return Ok(Some(cand));
                        }
                    }
                    None => {}
                }
            }
        }
    }
    Ok(None)
}

// ----- value-level inverse composition (`g(f(x)) -> x / ~x / x + k / x ^ k`) ----------------------

#[derive(Clone, Copy)]
enum ComposedTarget {
    Id,
    Not,
    Add(BitVec),
    Xor(BitVec),
}

impl ComposedTarget {
    fn eval(&self, x: &BitVec) -> BitVec {
        match self {
            ComposedTarget::Id => *x,
            ComposedTarget::Not => BitVec::un_unchecked(crate::ops::UnOp::Not, x),
            ComposedTarget::Add(k) => BitVec::bin_unchecked(BinOp::Add, x, k),
            ComposedTarget::Xor(k) => BitVec::bin_unchecked(BinOp::Xor, x, k),
        }
    }

    fn is_ring_poly(&self) -> bool {
        matches!(
            self,
            ComposedTarget::Id | ComposedTarget::Not | ComposedTarget::Add(_)
        )
    }
}

fn sample_pattern(w: crate::Width, s0: u64, s1: u64) -> BitVec {
    let mut limbs = [0u64; 8];
    let mut z = s0;
    for l in &mut limbs {
        z = z.wrapping_add(s1);
        let mut x = z;
        x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        *l = x ^ (x >> 31);
    }
    BitVec::wrapping_from_limbs(w, &limbs)
}

/// Formal polynomial degree over `Z` of `nodes_asc.last()` in `hole` when every operation in
/// `nodes_asc` is a ring operation at `w` (`Add`, `Sub`, `Neg`, `Not`, `Mul`, constant `Shl`),
/// capped at `256`. By Newton's binomial interpolation over `Z[x]`, a degree-`D` integer
/// polynomial vanishes modulo `2^W` at every input iff it vanishes at `0, 1, ..., D`.
fn ring_poly_degree(cx: &Context, hole: u32, nodes_asc: &[u32], w: u16) -> Option<u64> {
    const MAX_DEG: u64 = 256;
    let mut deg: IdMap<u32, u64> = IdMap::default();
    deg.insert(hole, 1);
    for &i in nodes_asc {
        let node = cx.node(i);
        if node.width != w {
            return None;
        }
        let d_of = |c: u32, map: &IdMap<u32, u64>| -> Option<u64> {
            if let Some(&d) = map.get(&c) {
                Some(d)
            } else if cx.is_const(c) {
                Some(0)
            } else {
                None
            }
        };
        let d = match node.op {
            OpCode::Add | OpCode::Sub => d_of(node.a, &deg)?.max(d_of(node.b, &deg)?),
            OpCode::Neg | OpCode::Not => d_of(node.a, &deg)?,
            OpCode::Shl if cx.is_const(node.b) => d_of(node.a, &deg)?,
            OpCode::Mul => d_of(node.a, &deg)?.saturating_add(d_of(node.b, &deg)?),
            _ => return None,
        };
        if d > MAX_DEG {
            return None;
        }
        deg.insert(i, d);
    }
    nodes_asc.last().and_then(|t| deg.get(t)).copied()
}

#[cfg(feature = "prove")]
fn prove_composed_circuit(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    hole: u32,
    nodes_asc: &[u32],
    target: &ComposedTarget,
) -> Result<bool, Stop> {
    use crate::engine::oracle::{EqualityCaps, EqualityVerdict};
    let left = r.meter.left_in(|b| b.pass_work);
    let cap = (left / 16).min(16_384);
    if cap < 512 {
        return Ok(false);
    }
    r.meter.deadline_now()?;
    let w = cx.width_of(hole);
    let mut scratch = Context::new();
    let Ok(sym) = scratch.fresh_symbol(w) else {
        return Ok(false);
    };
    let Ok(sym_id) = scratch.id(sym) else {
        return Ok(false);
    };
    let mut map: IdMap<u32, u32> = IdMap::default();
    map.insert(hole, sym_id);
    for &i in nodes_asc {
        let node = cx.node(i);
        // Extension ops require the host registry; skip rather than mis-rebuilding.
        if node.op.as_ext().is_some() || node.op.is_fp() {
            return Ok(false);
        }
        let mut kids = [0u32; 3];
        for (k, c) in node.children().enumerate() {
            kids[k] = if let Some(&m) = map.get(&c) {
                m
            } else if let Some(cv) = cx.const_val(c) {
                let Ok(mc) = scratch.mk_const(&cv) else {
                    return Ok(false);
                };
                map.insert(c, mc);
                mc
            } else {
                return Ok(false);
            };
        }
        let Ok(rebuilt) = (match node.op {
            OpCode::Extract => scratch.c_extract(kids[0], node.b as u16, node.width),
            OpCode::Zext => scratch.c_zext(kids[0], node.width),
            OpCode::Sext => scratch.c_sext(kids[0], node.width),
            OpCode::Concat => {
                let (ha, hb) = (scratch.handle(kids[0]), scratch.handle(kids[1]));
                scratch.concat(ha, hb).and_then(|h| scratch.id(h))
            }
            OpCode::Select => scratch.c_select(kids[0], kids[1], kids[2]),
            _ => {
                if let Some(u) = node.op.as_un() {
                    scratch.c_un(u, kids[0])
                } else if let Some(b) = node.op.as_bin() {
                    scratch.c_bin(b, kids[0], kids[1])
                } else if let Some(c) = node.op.as_cmp() {
                    scratch.c_cmp(c, kids[0], kids[1])
                } else {
                    return Ok(false);
                }
            }
        }) else {
            return Ok(false);
        };
        map.insert(i, rebuilt);
    }
    let Some(&root_id) = nodes_asc.last().and_then(|t| map.get(t)) else {
        return Ok(false);
    };
    let Ok(rhs_id) = (match target {
        ComposedTarget::Id => Ok(sym_id),
        ComposedTarget::Not => scratch.c_un(crate::ops::UnOp::Not, sym_id),
        ComposedTarget::Add(k) => scratch
            .mk_const(k)
            .and_then(|kc| scratch.c_bin(BinOp::Add, sym_id, kc)),
        ComposedTarget::Xor(k) => scratch
            .mk_const(k)
            .and_then(|kc| scratch.c_bin(BinOp::Xor, sym_id, kc)),
    }) else {
        return Ok(false);
    };
    if root_id == rhs_id {
        return Ok(true);
    }
    let caps = EqualityCaps {
        samples: 0,
        max_nodes: (cap as usize).min(8_192),
        max_propagations: cap,
    };
    let (lhs_h, rhs_h) = (scratch.handle(root_id), scratch.handle(rhs_id));
    let proof =
        crate::circuit_equality()(&mut scratch, lhs_h, rhs_h, &caps).map_err(Stop::Error)?;
    let cost = (proof.nodes as u64).saturating_add(proof.propagations);
    r.meter.charge(Counter::PassWork, cost.min(left))?;
    Ok(proof.verdict == EqualityVerdict::Proved)
}

/// Collapses single-dominator composed bijections `F(d)` (`unmix(mix(d))`, nonlinear T-function
/// round + inverse `T⁻¹(T(d))`, Feistel round + unround, or high-degree permutation polynomial
/// `P⁻¹(P(d))`) to `d`, `~d`, `d + k`, or `d ^ k` when nominated by 4 sample points and proved.
pub(super) fn collapse_composed(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    pass: PassKind,
) -> Result<Option<Step>, Stop> {
    const MAX_CONE: usize = 64;
    const MAX_FRONTIER: usize = 16;
    let w = cx.width_of(n);
    if w.bits() < 2 || w.bits() > 512 {
        return Ok(None);
    }
    let node = cx.node(n);
    if !matches!(
        node.op,
        OpCode::Add
            | OpCode::Sub
            | OpCode::Neg
            | OpCode::Mul
            | OpCode::Xor
            | OpCode::Not
            | OpCode::And
            | OpCode::Or
            | OpCode::Shl
            | OpCode::LShr
            | OpCode::AShr
            | OpCode::RotL
            | OpCode::RotR
            | OpCode::Bswap
            | OpCode::BitRev
            | OpCode::Extract
            | OpCode::Concat
    ) {
        return Ok(None);
    }
    // Depth-1 expressions over symbols/constants have no composed inner layer.
    if !node
        .children()
        .any(|c| !cx.is_const(c) && cx.node(c).op.arity() > 0)
    {
        return Ok(None);
    }
    let cap = MAX_CONE.min(r.inner.strategy.max_region as usize);
    if cap < 3 {
        return Ok(None);
    }
    let mut frontier = [0u32; MAX_FRONTIER];
    let mut f_len = 1usize;
    frontier[0] = n;
    let mut cone = [0u32; MAX_CONE];
    let mut c_len = 0usize;
    let mut doms = [(0u32, 0usize); 4];
    let mut d_len = 0usize;

    while f_len > 0 {
        let mut max_idx = 0usize;
        for k in 1..f_len {
            if frontier[k] > frontier[max_idx] {
                max_idx = k;
            }
        }
        let cur = frontier[max_idx];
        f_len -= 1;
        frontier[max_idx] = frontier[f_len];
        if c_len >= cap {
            break;
        }
        cone[c_len] = cur;
        c_len += 1;

        let cn = cx.node(cur);
        let mut had_varying = false;
        let mut overflow = false;
        for child in cn.children() {
            if cx.is_const(child) {
                continue;
            }
            had_varying = true;
            if !frontier[..f_len].contains(&child) {
                if f_len >= MAX_FRONTIER {
                    overflow = true;
                    break;
                }
                frontier[f_len] = child;
                f_len += 1;
            }
        }
        if !had_varying || overflow {
            break;
        }
        if f_len == 1 {
            let d = frontier[0];
            if c_len >= 3
                && cx.wid(d) == w.bits()
                && !r.bitwise.composed_tried.contains_key(&(n, d))
            {
                if d_len < doms.len() {
                    doms[d_len] = (d, c_len);
                    d_len += 1;
                } else {
                    doms[d_len - 1] = (d, c_len);
                }
            }
        }
    }
    if d_len == 0 {
        return Ok(None);
    }

    // Try deepest dominator first so `g(f(x))` collapses directly to `x`.
    for &(d, sub_len) in doms[..d_len].iter().rev() {
        let nodes_asc: Vec<u32> = cone[..sub_len].iter().rev().copied().collect();
        r.meter.charge(Counter::PassWork, sub_len as u64 * 2)?;
        let p0 = BitVec::zero(w);
        let Some(y0) = invert::eval_region(cx, &nodes_asc, d, &p0) else {
            continue;
        };
        let p1 = BitVec::one(w);
        let Some(y1) = invert::eval_region(cx, &nodes_asc, d, &p1) else {
            continue;
        };
        let mut add_ok = BitVec::bin_unchecked(BinOp::Sub, &y1, &p1) == y0;
        let mut xor_ok = BitVec::bin_unchecked(BinOp::Xor, &y1, &p1) == y0;
        if !add_ok && !xor_ok {
            continue;
        }
        for (s0, s1) in [
            (0x9E37_79B9_7F4A_7C15, 0xD1B5_4A32_D192_ED03),
            (0xBF58_476D_1CE4_E5B9, 0x94D0_49BB_1331_11EB),
        ] {
            let pt = sample_pattern(w, s0, s1);
            let Some(yt) = invert::eval_region(cx, &nodes_asc, d, &pt) else {
                add_ok = false;
                xor_ok = false;
                break;
            };
            add_ok &= BitVec::bin_unchecked(BinOp::Sub, &yt, &pt) == y0;
            xor_ok &= BitVec::bin_unchecked(BinOp::Xor, &yt, &pt) == y0;
            if !add_ok && !xor_ok {
                break;
            }
        }
        if !add_ok && !xor_ok {
            continue;
        }

        r.bitwise.composed_tried.insert((n, d), ());
        let target = if y0.is_zero() {
            ComposedTarget::Id
        } else if xor_ok && y0.is_ones() {
            ComposedTarget::Not
        } else if add_ok {
            ComposedTarget::Add(y0)
        } else {
            ComposedTarget::Xor(y0)
        };

        let mut proved = false;
        // Tier 1: Exhaustive proof for widths `<= 10`.
        if w.bits() <= 10 {
            let total = 1u64 << w.bits();
            r.meter
                .charge(Counter::PassWork, total * (sub_len as u64 / 4 + 1))?;
            proved = (2..total).all(|v| {
                let bv = BitVec::wrapping_from_u64(w, v);
                invert::eval_region(cx, &nodes_asc, d, &bv) == Some(target.eval(&bv))
            });
        }
        // Tier 2: Exact Newton binomial interpolation for ring polynomials (`1..=512` bits).
        if !proved
            && target.is_ring_poly()
            && let Some(deg) = ring_poly_degree(cx, d, &nodes_asc, w.bits())
        {
            r.meter
                .charge(Counter::PassWork, deg * (sub_len as u64 / 2 + 1) + 1)?;
            proved = (2..=deg).all(|v| {
                let bv = BitVec::wrapping_from_u64(w, v);
                invert::eval_region(cx, &nodes_asc, d, &bv) == Some(target.eval(&bv))
            });
        }
        // Tier 3: Bounded single-variable circuit miter (`prove` feature, `1..=512` bits).
        #[cfg(feature = "prove")]
        if !proved {
            proved = prove_composed_circuit(r, cx, d, &nodes_asc, &target)?;
        }
        if !proved {
            continue;
        }

        let before = cx.len() as u32;
        let e = r.build(cx, |cx| match &target {
            ComposedTarget::Id => Ok(d),
            ComposedTarget::Not => cx.c_un(crate::ops::UnOp::Not, d),
            ComposedTarget::Add(k) => {
                let kc = cx.mk_const(k)?;
                cx.c_bin(BinOp::Add, d, kc)
            }
            ComposedTarget::Xor(k) => {
                let kc = cx.mk_const(k)?;
                cx.c_bin(BinOp::Xor, d, kc)
            }
        })?;
        return Ok(Some(super::finish(
            r,
            cx,
            pass,
            n,
            e,
            before,
            &[d],
            Fin::FINAL,
        )?));
    }
    Ok(None)
}

/// `f(x) op c` as `x op f⁻¹(c)`, or a constant.
fn solve(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    lhs: u32,
    c: &BitVec,
) -> Result<Option<u32>, Stop> {
    let mut peels = Vec::new();
    let explaining = o.r.explaining();
    let solved = invert::solve_eq_peels(cx, o, lhs, c, explaining.then_some(&mut peels))?;
    if explaining && solved.is_some() {
        let layers = peels
            .into_iter()
            .map(|(node, l, preimage)| crate::engine::Peel {
                node: cx.handle(node),
                inner: cx.handle(l.inner),
                map: l.map.spelling(),
                bijective: l.kind == invert::Kind::Bijective,
                preimage,
            })
            .collect();
        o.r.explain_with(|| crate::engine::Explanation::Invert { layers });
    }
    Ok(match solved {
        None => None,
        Some(Solved::Const(eq)) => Some(truth(o, cx, eq == (op == CmpOp::Eq))?),
        Some(Solved::Eq(x, v)) => Some(compare(o, cx, op, x, &v)?),
    })
}

/// `f(x) op f(y)` as `x op' y`, through every common strictly monotone layer, the sides
/// `select` trees whose leaves are peeled together.
fn cancel_order(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    a: u32,
    b: u32,
) -> Result<Option<u32>, Stop> {
    let Some((mut order, strict)) = Order::of(op) else {
        return Ok(None);
    };
    let (mut x, mut y) = (a, b);
    let mut peeled = false;
    while let Some((ls, _)) = leaves(cx, o, x, y)? {
        let Some((inners, m)) = monotone::cancel_many(cx, o, &ls, order)? else {
            break;
        };
        let (p, q) = relabelled(cx, o, x, y, &ls, &inners)?;
        (x, y) = if m.increasing { (p, q) } else { (q, p) };
        order = m.input;
        peeled = true;
    }
    if !peeled {
        return Ok(None);
    }
    Ok(Some(o.r.build(cx, |cx| cx.c_cmp(order.cmp(strict), x, y))?))
}

/// A sign test of a value rotated or shifted left by a constant (`rotl(x, k) <s 0`,
/// `0 <=s x << k`, spelled either way): the bit of `x` that lands on top, or its complement.
/// (The sign of the low byte is `rotl(x, 56) <s 0`, bit 7.)
fn sign_bit(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    lhs: u32,
    c: &BitVec,
    const_left: bool,
) -> Result<Option<u32>, Stop> {
    // `x <s 0` and `x <=s −1` hold for a set top bit; `0 <=s x` and `−1 <s x` for a clear one.
    let negative = match (op, const_left) {
        (CmpOp::Slt, false) if c.is_zero() => true,
        (CmpOp::Sle, false) if c.is_ones() => true,
        (CmpOp::Sle, true) if c.is_zero() => false,
        (CmpOp::Slt, true) if c.is_ones() => false,
        _ => return Ok(None),
    };
    let node = cx.node(lhs);
    let w = u64::from(node.width);
    let Some(k) = (matches!(node.op, OpCode::RotL | OpCode::RotR | OpCode::Shl))
        .then(|| cx.const_val(node.b).and_then(|k| k.to_u64()))
        .flatten()
    else {
        return Ok(None);
    };
    let bit = match node.op {
        OpCode::Shl if k >= w => return Ok(None),
        OpCode::RotR => (w - 1 + k % w) % w,
        _ => (w - 1 + w - k % w) % w,
    };
    o.r.meter.charge(Counter::PassWork, 1)?;
    let x = node.a;
    Ok(Some(o.r.build(cx, |cx| {
        let b = cx.c_extract(x, bit as u16, 1)?;
        match negative {
            true => Ok(b),
            false => cx.c_un(crate::ops::UnOp::Not, b),
        }
    })?))
}

/// `f(x) op c` (or `c op f(x)`, with `const_left`) as a comparison of `x` with a threshold, or
/// a constant.
fn solve_order(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    lhs: u32,
    c: &BitVec,
    const_left: bool,
) -> Result<Option<u32>, Stop> {
    Ok(match monotone::solve(cx, o, op, lhs, c, const_left)? {
        None => None,
        Some(monotone::Solved::Const(v)) => Some(truth(o, cx, v)?),
        Some(monotone::Solved::Cmp {
            op,
            x,
            t,
            const_left,
        }) => Some(o.r.build(cx, |cx| {
            let t = cx.mk_const(&t)?;
            if const_left {
                cx.c_cmp(op, t, x)
            } else {
                cx.c_cmp(op, x, t)
            }
        })?),
    })
}

/// `a₁ | … | aₙ op 0` (or `a₁ & … & aₙ op ones`): each `aᵢ op c` solved alone, then
/// intersected (for `==`; `!=` is its negation).
fn split(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    n: u32,
    lhs: u32,
    c: &BitVec,
    before: u32,
) -> Result<Option<u32>, Stop> {
    let join = cx.node(lhs).op;
    let mut leaves = Vec::new();
    let mut stack = vec![lhs];
    while let Some(i) = stack.pop() {
        o.charge(1)?;
        let node = cx.node(i);
        if node.op == join {
            stack.push(node.b);
            stack.push(node.a);
        } else if leaves.len() >= MAX_SPLIT {
            return Ok(None);
        } else {
            leaves.push(i);
        }
    }
    let eq = op == CmpOp::Eq;
    // What each leaf being `c` means: `x == v`, in leaf order, without repeats.
    let mut conj: Vec<(u32, BitVec)> = Vec::new();
    let mut solved = false;
    for leaf in leaves {
        let (x, v) = match invert::solve_eq(cx, o, leaf, c)? {
            // One leaf can never be `c`: the conjunction is false.
            Some(Solved::Const(false)) => return Ok(Some(truth(o, cx, !eq)?)),
            Some(Solved::Const(true)) => {
                solved = true;
                continue;
            }
            Some(Solved::Eq(x, v)) => {
                solved = true;
                (x, v)
            }
            None => (leaf, *c),
        };
        match conj.iter().find(|(y, _)| *y == x) {
            // One value equal to two different constants.
            Some((_, w)) if *w != v => return Ok(Some(truth(o, cx, !eq)?)),
            Some(_) => {}
            None => conj.push((x, v)),
        }
    }
    if !solved {
        return Ok(None);
    }
    let mut out: Option<u32> = None;
    for (x, v) in &conj {
        let t = compare(o, cx, op, *x, v)?;
        out = Some(match out {
            None => t,
            Some(acc) => {
                let join = if eq { BinOp::And } else { BinOp::Or };
                o.r.build(cx, |cx| cx.c_bin(join, acc, t))?
            }
        });
    }
    let e = match out {
        Some(e) => e,
        None => truth(o, cx, eq)?,
    };
    // Kept only when smaller as a tree (a saturated size decides nothing).
    let tree = |i: u32| cx.meta[i as usize].tree;
    if tree(n) == u32::MAX || tree(e) >= tree(n) {
        discard(o.r, cx, before);
        return Ok(None);
    }
    Ok(Some(e))
}
