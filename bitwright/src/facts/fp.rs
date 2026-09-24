//! Facts of floating-point operations.
//!
//! The facts of an encoding describe a set of floats: whether it may hold a NaN, and for each
//! sign an interval of values. Within one sign half, unsigned and signed order agree, so the
//! unsigned range bounds the negative magnitudes and the signed range the positive ones (the
//! pair describes `|x| ≤ 1` exactly, both signs included), and known bits snap the ends. An
//! operation is applied to the ends of its operands' value intervals, in the node's own rounding
//! mode: correct rounding is monotonic, so the results bound every result (at the corners of a
//! product or a quotient, and at both ends of a sum). Where the ends meet a special case (0 · ∞,
//! ∞ − ∞, a divisor that may be 0) the bound falls back to every value; a possible NaN is the
//! canonical one, one encoding. The result is encoded back as ranges, both zeros included when
//! the interval crosses 0.

use core::cmp::Ordering;

use super::Facts;
use super::known::KnownBits;
use super::range::{SRange, URange, slt, ult};
use super::transfer::span;
use crate::fp::node::Desc;
use crate::fp::{FpFormat, FpOp, RoundingMode};
use crate::ops::CmpOp;
use crate::{BitVec, Width};

/// A set of floats: a possible NaN and the non-NaN values between two encodings (by value).
#[derive(Clone, Copy, Debug)]
struct Floats {
    nan: bool,
    /// The least and the greatest value (`None`: only NaN, or nothing).
    range: Option<(BitVec, BitVec)>,
}

fn sign(w: Width) -> BitVec {
    BitVec::smin(w)
}

fn add(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(crate::BinOp::Add, a, b)
}

fn sub(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(crate::BinOp::Sub, a, b)
}

/// The floats an encoding's facts allow.
fn decode(f: FpFormat, x: &Facts) -> Floats {
    let w = f.width();
    let s = sign(w);
    let inf = f.inf(false);
    let one = BitVec::one(w);
    let pos = span(x, &BitVec::zero(w), &inf, false);
    let neg = span(x, &s, &add(&s, &inf), true);
    let nan = span(x, &add(&inf, &one), &sub(&s, &one), false).is_some()
        || span(x, &add(&add(&s, &inf), &one), &BitVec::ones(w), true).is_some();
    // Least: the most negative (greatest magnitude) when negatives exist; greatest likewise.
    let range = match (neg, pos) {
        (Some((_, nhi)), Some((_, phi))) => Some((nhi, phi)),
        (Some((nlo, nhi)), None) => Some((nhi, nlo)),
        (None, Some((plo, phi))) => Some((plo, phi)),
        (None, None) => None,
    };
    Floats { nan, range }
}

/// The facts of an encoding holding one of `x`'s floats (both zeros where the range crosses 0).
fn encode(f: FpFormat, x: Floats) -> Facts {
    let w = f.width();
    let s = sign(w);
    let mut parts: Vec<(BitVec, BitVec)> = Vec::new();
    if x.nan {
        let n = f.nan();
        parts.push((n, n));
    }
    if let Some((lo, hi)) = x.range {
        let negative = |v: &BitVec| v.msb();
        // A range strictly across 0 may hold either zero (a cancellation's sign depends on the
        // mode); at its ends, the ends themselves carry their zeros' signs.
        let zero_inside = f.compare(&lo, &f.zero(false)) == Ok(Some(Ordering::Less))
            && f.compare(&hi, &f.zero(false)) == Ok(Some(Ordering::Greater));
        // Negative values: from the least (largest magnitude) up to −0 or `hi`.
        if negative(&lo) {
            let top = if negative(&hi) { hi } else { s };
            parts.push((top, lo));
        }
        if !negative(&hi) {
            let bottom = if negative(&lo) { BitVec::zero(w) } else { lo };
            parts.push((bottom, hi));
        }
        if zero_inside {
            parts.push((s, s));
            let z = BitVec::zero(w);
            parts.push((z, z));
        }
    }
    let Some(&(first_lo, first_hi)) = parts.first() else {
        return Facts::top(w);
    };
    let (mut ulo, mut uhi, mut slo, mut shi) = (first_lo, first_hi, first_lo, first_hi);
    for &(lo, hi) in &parts[1..] {
        if ult(&lo, &ulo) {
            ulo = lo;
        }
        if ult(&uhi, &hi) {
            uhi = hi;
        }
        if slt(&lo, &slo) {
            slo = lo;
        }
        if slt(&shi, &hi) {
            shi = hi;
        }
    }
    let u = URange::new(ulo, uhi).unwrap_or(URange::full(w));
    let sr = SRange::new(slo, shi).unwrap_or(SRange::full(w));
    Facts::reduce(KnownBits::unknown(w), u, sr).unwrap_or_else(|| Facts::top(w))
}

/// The value order of two non-NaN encodings (`−0 = +0`).
fn cmp(f: FpFormat, a: &BitVec, b: &BitVec) -> Ordering {
    f.compare(a, b).ok().flatten().unwrap_or(Ordering::Equal)
}

/// The least and the greatest of non-NaN candidates, or `None` if any is a NaN.
fn bounds(f: FpFormat, vals: &[BitVec]) -> Option<(BitVec, BitVec)> {
    let mut lo = *vals.first()?;
    let mut hi = lo;
    for v in vals {
        if f.test(crate::fp::FpTest::Nan, v).ok()? {
            return None;
        }
        // Ties between zeros: keep −0 as the least and +0 as the greatest.
        if cmp(f, v, &lo) == Ordering::Less || (cmp(f, v, &lo) == Ordering::Equal && v.msb()) {
            lo = *v;
        }
        if cmp(f, v, &hi) == Ordering::Greater || (cmp(f, v, &hi) == Ordering::Equal && !v.msb()) {
            hi = *v;
        }
    }
    Some((lo, hi))
}

/// Every value from −∞ to +∞.
fn everything(f: FpFormat) -> Option<(BitVec, BitVec)> {
    Some((f.inf(true), f.inf(false)))
}

fn is(f: FpFormat, t: crate::fp::FpTest, v: &BitVec) -> bool {
    f.test(t, v).unwrap_or(true)
}

/// Whether the non-NaN range may hold a value passing `t`.
fn may(f: FpFormat, x: &Floats, t: crate::fp::FpTest) -> bool {
    use crate::fp::FpTest;
    let Some((lo, hi)) = x.range else {
        return false;
    };
    match t {
        FpTest::Zero => {
            cmp(f, &lo, &f.zero(false)) != Ordering::Greater
                && cmp(f, &hi, &f.zero(false)) != Ordering::Less
        }
        FpTest::Infinite => is(f, FpTest::Infinite, &lo) || is(f, FpTest::Infinite, &hi),
        _ => true,
    }
}

/// The facts of a floating-point operation's result.
pub(crate) fn transfer(d: &Desc, args: &[&Facts]) -> Facts {
    use crate::fp::FpTest;
    let f = d.format;
    let x: Vec<Floats> = match d.op {
        FpOp::FromSInt(_) | FpOp::FromUInt(_) => Vec::new(),
        _ => args.iter().map(|a| decode(f, a)).collect(),
    };
    let nan_in = x.iter().any(|v| v.nan);
    let op2 = |g: &dyn Fn(&BitVec, &BitVec) -> BitVec| -> Option<(BitVec, BitVec)> {
        let ((alo, ahi), (blo, bhi)) = (x[0].range?, x[1].range?);
        bounds(
            f,
            &[g(&alo, &blo), g(&alo, &bhi), g(&ahi, &blo), g(&ahi, &bhi)],
        )
    };
    let float = |nan: bool, range: Option<(BitVec, BitVec)>| encode(f, Floats { nan, range });
    match d.op {
        FpOp::Add(rm) => {
            let (a, b) = (&x[0], &x[1]);
            // ∞ − ∞: opposite infinities meet.
            let inf_clash = may(f, a, FpTest::Infinite) && may(f, b, FpTest::Infinite);
            let range = if a.range.is_none() || b.range.is_none() {
                None
            } else {
                op2(&|p, q| f.add(rm, p, q).unwrap_or(f.nan())).or_else(|| everything(f))
            };
            float(nan_in || inf_clash, range)
        }
        FpOp::Mul(rm) => {
            let (a, b) = (&x[0], &x[1]);
            let zero_inf = (may(f, a, FpTest::Zero) && may(f, b, FpTest::Infinite))
                || (may(f, a, FpTest::Infinite) && may(f, b, FpTest::Zero));
            let range = if a.range.is_none() || b.range.is_none() {
                None
            } else {
                op2(&|p, q| f.mul(rm, p, q).unwrap_or(f.nan())).or_else(|| everything(f))
            };
            float(nan_in || zero_inf, range)
        }
        FpOp::Div(rm) => {
            let (a, b) = (&x[0], &x[1]);
            let both_zero = may(f, a, FpTest::Zero) && may(f, b, FpTest::Zero);
            let both_inf = may(f, a, FpTest::Infinite) && may(f, b, FpTest::Infinite);
            let range = if a.range.is_none() || b.range.is_none() {
                None
            } else if may(f, b, FpTest::Zero) {
                everything(f)
            } else {
                op2(&|p, q| f.div(rm, p, q).unwrap_or(f.nan())).or_else(|| everything(f))
            };
            float(nan_in || both_zero || both_inf, range)
        }
        FpOp::Fma(rm) => {
            let (a, b, c) = (&x[0], &x[1], &x[2]);
            let zero_inf = (may(f, a, FpTest::Zero) && may(f, b, FpTest::Infinite))
                || (may(f, a, FpTest::Infinite) && may(f, b, FpTest::Zero));
            let inf_clash = (may(f, a, FpTest::Infinite) || may(f, b, FpTest::Infinite))
                && may(f, c, FpTest::Infinite);
            let range = match (a.range, b.range, c.range) {
                (Some((alo, ahi)), Some((blo, bhi)), Some((clo, chi))) => {
                    let mut v = Vec::with_capacity(8);
                    for p in [alo, ahi] {
                        for q in [blo, bhi] {
                            for r in [clo, chi] {
                                v.push(f.fma(rm, &p, &q, &r).unwrap_or(f.nan()));
                            }
                        }
                    }
                    bounds(f, &v).or_else(|| everything(f))
                }
                _ => None,
            };
            float(nan_in || zero_inf || inf_clash, range)
        }
        FpOp::Sqrt(rm) => {
            let a = &x[0];
            match a.range {
                Some((lo, hi)) => {
                    let negative = cmp(f, &lo, &f.zero(false)) == Ordering::Less;
                    let lo = if negative { f.zero(true) } else { lo };
                    let range = if cmp(f, &hi, &f.zero(false)) == Ordering::Less {
                        None
                    } else {
                        bounds(
                            f,
                            &[
                                f.sqrt(rm, &lo).unwrap_or(f.nan()),
                                f.sqrt(rm, &hi).unwrap_or(f.nan()),
                            ],
                        )
                    };
                    float(nan_in || negative, range)
                }
                None => float(true, None),
            }
        }
        FpOp::RoundToIntegral(rm) => {
            let range = x[0].range.and_then(|(lo, hi)| {
                bounds(
                    f,
                    &[
                        f.round_to_integral(rm, &lo).unwrap_or(f.nan()),
                        f.round_to_integral(rm, &hi).unwrap_or(f.nan()),
                    ],
                )
            });
            float(nan_in, range)
        }
        FpOp::Rem => {
            let (a, b) = (&x[0], &x[1]);
            // |a rem b| ≤ min(|a|, |b| / 2).
            let magnitude = |r: (BitVec, BitVec)| {
                let (lo, hi) = r;
                let (l, h) = (f.abs(&lo).unwrap_or(lo), f.abs(&hi).unwrap_or(hi));
                if cmp(f, &l, &h) == Ordering::Greater {
                    l
                } else {
                    h
                }
            };
            let nan = nan_in || may(f, a, FpTest::Infinite) || may(f, b, FpTest::Zero);
            let range = match (a.range, b.range) {
                (Some(ra), Some(rb)) => {
                    let ma = magnitude(ra);
                    let two = f
                        .round_rational(RoundingMode::Rne, false, &[2], &[1])
                        .unwrap_or(f.inf(false));
                    let mb = f
                        .div(RoundingMode::Rtp, &magnitude(rb), &two)
                        .unwrap_or(f.inf(false));
                    let m = if cmp(f, &ma, &mb) == Ordering::Less {
                        ma
                    } else {
                        mb
                    };
                    let m = if is(f, FpTest::Nan, &m) {
                        f.inf(false)
                    } else {
                        m
                    };
                    Some((f.neg(&m).unwrap_or(m), m))
                }
                _ => None,
            };
            float(nan, range)
        }
        FpOp::Min | FpOp::Max => {
            let (a, b) = (&x[0], &x[1]);
            let pick = |p: &BitVec, q: &BitVec| {
                if d.op == FpOp::Min {
                    f.min(p, q).unwrap_or(*p)
                } else {
                    f.max(p, q).unwrap_or(*p)
                }
            };
            let mut range = match (a.range, b.range) {
                (Some((alo, ahi)), Some((blo, bhi))) => {
                    bounds(f, &[pick(&alo, &blo), pick(&ahi, &bhi)])
                }
                _ => None,
            };
            // A NaN operand leaves the other operand's value.
            for (v, other) in [(a, b), (b, a)] {
                if v.nan {
                    range = hull(f, range, other.range);
                }
            }
            float(a.nan && b.nan, range)
        }
        FpOp::Eq | FpOp::Lt | FpOp::Le => {
            let cmp_op = match d.op {
                FpOp::Eq => CmpOp::Eq,
                FpOp::Lt => CmpOp::Slt,
                _ => CmpOp::Sle,
            };
            match decide(f, cmp_op, &x[0], &x[1]) {
                Some(v) => Facts::constant(&BitVec::from_bool(v)),
                None => Facts::top(Width::W1),
            }
        }
        FpOp::Convert { to, rm } => {
            let range = x[0].range.and_then(|(lo, hi)| {
                bounds(
                    to,
                    &[
                        f.convert(to, rm, &lo).unwrap_or(to.nan()),
                        f.convert(to, rm, &hi).unwrap_or(to.nan()),
                    ],
                )
            });
            encode(to, Floats { nan: nan_in, range })
        }
        FpOp::FromSInt(rm) | FpOp::FromUInt(rm) => {
            let a = args[0];
            let (lo, hi) = match d.op {
                FpOp::FromSInt(_) => (a.srange.lo(), a.srange.hi()),
                _ => (a.urange.lo(), a.urange.hi()),
            };
            let conv = |v: &BitVec| match d.op {
                FpOp::FromSInt(_) => f.from_sint(rm, v),
                _ => f.from_uint(rm, v),
            };
            float(false, bounds(f, &[conv(&lo), conv(&hi)]))
        }
        FpOp::ToSInt(rm, w) | FpOp::ToUInt(rm, w) => {
            let signed = matches!(d.op, FpOp::ToSInt(..));
            let conv = |v: &BitVec| {
                if signed {
                    f.to_sint(rm, v, w)
                } else {
                    f.to_uint(rm, v, w)
                }
                .unwrap_or(BitVec::zero(w))
            };
            let mut ends: Vec<BitVec> = Vec::new();
            if let Some((lo, hi)) = x[0].range {
                ends.push(conv(&lo));
                ends.push(conv(&hi));
            }
            if nan_in {
                ends.push(BitVec::zero(w));
            }
            let Some(&first) = ends.first() else {
                return Facts::top(w);
            };
            let (mut lo, mut hi) = (first, first);
            for e in &ends {
                let less = if signed { slt(e, &lo) } else { ult(e, &lo) };
                let more = if signed { slt(&hi, e) } else { ult(&hi, e) };
                if less {
                    lo = *e;
                }
                if more {
                    hi = *e;
                }
            }
            let known = KnownBits::unknown(w);
            if signed {
                let s = SRange::new(lo, hi).unwrap_or(SRange::full(w));
                Facts::reduce(known, URange::full(w), s).unwrap_or_else(|| Facts::top(w))
            } else {
                let u = URange::new(lo, hi).unwrap_or(URange::full(w));
                Facts::reduce(known, u, SRange::full(w)).unwrap_or_else(|| Facts::top(w))
            }
        }
    }
}

/// The smallest range holding both (either may be absent).
fn hull(
    f: FpFormat,
    a: Option<(BitVec, BitVec)>,
    b: Option<(BitVec, BitVec)>,
) -> Option<(BitVec, BitVec)> {
    match (a, b) {
        (Some((alo, ahi)), Some((blo, bhi))) => bounds(f, &[alo, ahi, blo, bhi]),
        (x, None) | (None, x) => x,
    }
}

/// Decides `a = b` (`Eq`), `a < b` (`Slt`) or `a ≤ b` (`Sle`) on floats, if the sets decide it:
/// true needs no NaN and the ranges ordered; false needs the ranges ordered the other way (a
/// NaN makes every comparison false).
fn decide(f: FpFormat, op: CmpOp, a: &Floats, b: &Floats) -> Option<bool> {
    let no_nan = !a.nan && !b.nan;
    let (Some((alo, ahi)), Some((blo, bhi))) = (a.range, b.range) else {
        // Only NaNs on one side: every comparison is false.
        return (a.range.is_none() && a.nan || b.range.is_none() && b.nan).then_some(false);
    };
    let c = |p: &BitVec, q: &BitVec| cmp(f, p, q);
    match op {
        CmpOp::Eq => {
            if c(&ahi, &blo) == Ordering::Less || c(&bhi, &alo) == Ordering::Less {
                Some(false)
            } else if no_nan
                && c(&alo, &ahi) == Ordering::Equal
                && c(&blo, &bhi) == Ordering::Equal
                && c(&alo, &blo) == Ordering::Equal
            {
                Some(true)
            } else {
                None
            }
        }
        CmpOp::Slt => {
            if no_nan && c(&ahi, &blo) == Ordering::Less {
                Some(true)
            } else if c(&alo, &bhi) != Ordering::Less {
                Some(false)
            } else {
                None
            }
        }
        _ => {
            if no_nan && c(&ahi, &blo) != Ordering::Greater {
                Some(true)
            } else if c(&alo, &bhi) == Ordering::Greater {
                Some(false)
            } else {
                None
            }
        }
    }
}
