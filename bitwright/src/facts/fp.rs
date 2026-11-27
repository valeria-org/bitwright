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

/// The members of facts packed as words (up to 64 bits: known zeros, known ones, unsigned
/// bounds, stride, signed bounds) between `lo` and `hi`, within one sign half: [`span`] on a
/// machine word.
fn span_word(x: &[u64; 7], mask: u64, lo: u64, hi: u64, negative_half: bool) -> Option<(u64, u64)> {
    let sign = (mask >> 1) + 1;
    let (kz, ko, ulo, uhi, slo, shi) = (x[0], x[1], x[2], x[3], x[5], x[6]);
    let (slo_neg, shi_neg) = (slo & sign != 0, shi & sign != 0);
    let (sl, sh) = if negative_half {
        if !slo_neg {
            return None;
        }
        (slo, if shi_neg { shi } else { mask })
    } else {
        if shi_neg {
            return None;
        }
        (if slo_neg { 0 } else { slo }, shi)
    };
    let lo = lo.max(ulo).max(sl);
    let hi = hi.min(uhi).min(sh);
    if hi < lo {
        return None;
    }
    let lo = super::narrow::next_member(lo, kz, ko, mask)?;
    let hi = super::narrow::prev_member(hi, kz, ko, mask)?;
    (lo <= hi).then_some((lo, hi))
}

/// [`decode`] for formats of at most 64 bits.
fn decode_word(f: FpFormat, x: &Facts) -> Floats {
    let w = f.width();
    let bits = u32::from(w.bits());
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let sign = (mask >> 1) + 1;
    let inf = (u64::MAX >> (64 - f.eb())) << (f.sb() - 1);
    let words = super::to_words(x);
    // Nothing known (a symbol): every float.
    if words[0] | words[1] == 0
        && words[2] == 0
        && words[3] == mask
        && words[5] == sign
        && words[6] == mask >> 1
    {
        return Floats {
            nan: true,
            range: everything(f),
        };
    }
    let pos = span_word(&words, mask, 0, inf, false);
    let neg = span_word(&words, mask, sign, sign | inf, true);
    let nan = span_word(&words, mask, inf + 1, sign - 1, false).is_some()
        || span_word(&words, mask, (sign | inf) + 1, mask, true).is_some();
    let v = |u: u64| BitVec::from_canonical_u64(w, u);
    let range = match (neg, pos) {
        (Some((_, nhi)), Some((_, phi))) => Some((v(nhi), v(phi))),
        (Some((nlo, nhi)), None) => Some((v(nhi), v(nlo))),
        (None, Some((plo, phi))) => Some((v(plo), v(phi))),
        (None, None) => None,
    };
    Floats { nan, range }
}

/// The floats an encoding's facts allow.
fn decode(f: FpFormat, x: &Facts) -> Floats {
    if f.width().bits() <= 64 {
        return decode_word(f, x);
    }
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

/// [`encode_with`] for formats of at most 64 bits.
fn encode_word_with(f: FpFormat, x: Floats, all_nans: bool) -> Facts {
    let w = f.width();
    let bits = u32::from(w.bits());
    let mask = if bits == 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let sign = (mask >> 1) + 1;
    let inf = (u64::MAX >> (64 - f.eb())) << (f.sb() - 1);
    let word = |v: &BitVec| v.limbs()[0];
    // Unsigned and signed hulls of the parts (a part is within one sign half).
    let (mut ulo, mut uhi, mut slo, mut shi) = (u64::MAX, 0u64, u64::MAX, 0u64);
    let mut add = |lo: u64, hi: u64| {
        ulo = ulo.min(lo);
        uhi = uhi.max(hi);
        // Signed order is unsigned order with the sign bit flipped.
        slo = slo.min(lo ^ sign);
        shi = shi.max(hi ^ sign);
    };
    if x.nan {
        if all_nans {
            add(inf + 1, sign - 1);
            add((sign | inf) + 1, mask);
        } else {
            let n = word(&f.nan());
            add(n, n);
        }
    }
    if let Some((lo, hi)) = x.range {
        let (l, h) = (word(&lo), word(&hi));
        let (l_neg, h_neg) = (l & sign != 0, h & sign != 0);
        let magnitude = |v: u64| v & !sign & mask;
        if l_neg {
            add(if h_neg { h } else { sign }, l);
        }
        if !h_neg {
            add(if l_neg { 0 } else { l }, h);
        }
        // Strictly across 0 (negative least, positive greatest, neither a zero): both zeros.
        if l_neg && !h_neg && magnitude(l) != 0 && magnitude(h) != 0 {
            add(sign, sign);
            add(0, 0);
        }
    }
    if ulo > uhi {
        return Facts::top(w);
    }
    let v = |u: u64| BitVec::from_canonical_u64(w, u);
    let u = URange::new(v(ulo), v(uhi)).unwrap_or(URange::full(w));
    let s = SRange::new(v(slo ^ sign), v(shi ^ sign)).unwrap_or(SRange::full(w));
    Facts::reduce(KnownBits::unknown(w), u, s).unwrap_or_else(|| Facts::top(w))
}

/// The facts of an encoding holding one of `x`'s floats (both zeros where the range crosses 0).
/// Forward results only ever produce the canonical NaN (`all_nans = false`); backward operand
/// constraints must admit every positive and negative NaN payload (`all_nans = true`).
fn encode_with(f: FpFormat, x: Floats, all_nans: bool) -> Facts {
    if f.width().bits() <= 64 {
        return encode_word_with(f, x, all_nans);
    }
    let w = f.width();
    let s = sign(w);
    let mut parts: Vec<(BitVec, BitVec)> = Vec::new();
    if x.nan {
        if all_nans {
            let inf = f.inf(false);
            let one = BitVec::one(w);
            parts.push((add(&inf, &one), sub(&s, &one)));
            parts.push((add(&add(&s, &inf), &one), BitVec::ones(w)));
        } else {
            let n = f.nan();
            parts.push((n, n));
        }
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

fn encode(f: FpFormat, x: Floats) -> Facts {
    encode_with(f, x, false)
}

fn encode_any_nan(f: FpFormat, x: Floats) -> Facts {
    encode_with(f, x, true)
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

/// Whether an encoding of `f` with facts `x` may be a NaN, an infinity, a zero: what a rule's
/// floating-point guard predicates ask (each "no" a proof).
pub(crate) fn may_be(f: FpFormat, x: &Facts) -> (bool, bool, bool) {
    use crate::fp::FpTest;
    let d = decode(f, x);
    (
        d.nan,
        may(f, &d, FpTest::Infinite),
        may(f, &d, FpTest::Zero),
    )
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

/// Total order on non-NaN encodings (`−0 < +0`).
fn total_cmp(f: FpFormat, a: &BitVec, b: &BitVec) -> Ordering {
    match cmp(f, a, b) {
        Ordering::Equal => match (a.msb(), b.msb()) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            _ => Ordering::Equal,
        },
        ord => ord,
    }
}

fn max_total(f: FpFormat, a: BitVec, b: BitVec) -> BitVec {
    if total_cmp(f, &a, &b) == Ordering::Less {
        b
    } else {
        a
    }
}

fn min_total(f: FpFormat, a: BitVec, b: BitVec) -> BitVec {
    if total_cmp(f, &a, &b) == Ordering::Greater {
        b
    } else {
        a
    }
}

/// Intersects two non-NaN intervals in [`total_cmp`] order.
fn clamp_total(
    f: FpFormat,
    (alo, ahi): (BitVec, BitVec),
    (blo, bhi): (BitVec, BitVec),
) -> Option<(BitVec, BitVec)> {
    let lo = max_total(f, alo, blo);
    let hi = min_total(f, ahi, bhi);
    (total_cmp(f, &lo, &hi) != Ordering::Greater).then_some((lo, hi))
}

/// Greatest non-NaN encoding (in [`total_cmp`]) with `x <_fp v`, if any (`None` at `−∞`).
fn strictly_below(f: FpFormat, v: &BitVec) -> Option<BitVec> {
    let w = f.width();
    let one = BitVec::one(w);
    if *v == f.inf(true) {
        None
    } else if is(f, crate::fp::FpTest::Zero, v) {
        Some(add(&f.zero(true), &one))
    } else if v.msb() {
        Some(add(v, &one))
    } else {
        Some(sub(v, &one))
    }
}

/// Least non-NaN encoding (in [`total_cmp`]) with `x >_fp v`, if any (`None` at `+∞`).
fn strictly_above(f: FpFormat, v: &BitVec) -> Option<BitVec> {
    let w = f.width();
    let one = BitVec::one(w);
    if *v == f.inf(false) {
        None
    } else if is(f, crate::fp::FpTest::Zero, v) {
        Some(one)
    } else if !v.msb() {
        Some(add(v, &one))
    } else {
        Some(sub(v, &one))
    }
}

/// Greatest non-NaN encoding (in [`total_cmp`]) with `x <=_fp v` (`−0` widens to `+0`).
fn at_most(f: FpFormat, v: &BitVec) -> BitVec {
    if *v == f.zero(true) {
        f.zero(false)
    } else {
        *v
    }
}

/// Least non-NaN encoding (in [`total_cmp`]) with `x >=_fp v` (`+0` widens to `−0`).
fn at_least(f: FpFormat, v: &BitVec) -> BitVec {
    if *v == f.zero(false) {
        f.zero(true)
    } else {
        *v
    }
}

/// Removes encodings equal in FP value to `v` (`±0` removes both zeros) from an endpoint of
/// `range`; `None` if nothing remains.
fn exclude_val(
    f: FpFormat,
    range: Option<(BitVec, BitVec)>,
    v: &BitVec,
) -> Option<(BitVec, BitVec)> {
    let (mut lo, mut hi) = range?;
    if cmp(f, &lo, &hi) == Ordering::Equal && cmp(f, &lo, v) == Ordering::Equal {
        return None;
    }
    let w = f.width();
    let one = BitVec::one(w);
    if cmp(f, &lo, v) == Ordering::Equal {
        lo = if is(f, crate::fp::FpTest::Zero, v) {
            one
        } else {
            strictly_above(f, v)?
        };
    }
    if cmp(f, &hi, v) == Ordering::Equal {
        hi = if is(f, crate::fp::FpTest::Zero, v) {
            add(&f.zero(true), &one)
        } else {
            strictly_below(f, v)?
        };
    }
    (total_cmp(f, &lo, &hi) != Ordering::Greater).then_some((lo, hi))
}

/// Meets `arg` with `encode_any_nan(f, target)`: `None` if contradictory, `Some(None)` if nothing
/// beyond `arg` is learned.
fn refine_arg(arg: &Facts, f: FpFormat, target: Floats) -> Option<Option<Facts>> {
    if !target.nan && target.range.is_none() {
        return None;
    }
    let refined = arg.meet(&encode_any_nan(f, target))?;
    Some((refined != *arg).then_some(refined))
}

/// Backward transfer for a floating-point operation given result facts `r` and operand `args`.
pub(super) fn backward(d: Desc, r: &Facts, args: &[&Facts]) -> super::backward::Operands {
    use crate::fp::FpTest;
    // If the forward image cannot intersect `r`, no concrete input tuple maps into `r`.
    transfer(&d, args).meet(r)?;
    let f = d.format;
    match d.op {
        FpOp::Eq | FpOp::Lt | FpOp::Le => {
            let Some(rv) = r.as_constant() else {
                return Some([None, None, None]);
            };
            let holds = !rv.is_zero();
            let (da, db) = (decode(f, args[0]), decode(f, args[1]));
            if holds {
                // Every IEEE comparison is false when either operand is a NaN.
                let (Some((alo, ahi)), Some((blo, bhi))) = (da.range, db.range) else {
                    return None;
                };
                let (ra, rb) = match d.op {
                    FpOp::Eq => {
                        if cmp(f, &alo, &bhi) == Ordering::Greater
                            || cmp(f, &blo, &ahi) == Ordering::Greater
                        {
                            return None;
                        }
                        let mut lo = if cmp(f, &alo, &blo) == Ordering::Greater {
                            alo
                        } else {
                            blo
                        };
                        let mut hi = if cmp(f, &ahi, &bhi) == Ordering::Less {
                            ahi
                        } else {
                            bhi
                        };
                        if is(f, FpTest::Zero, &lo) {
                            lo = f.zero(true);
                        }
                        if is(f, FpTest::Zero, &hi) {
                            hi = f.zero(false);
                        }
                        (
                            clamp_total(f, (alo, ahi), (lo, hi))?,
                            clamp_total(f, (blo, bhi), (lo, hi))?,
                        )
                    }
                    FpOp::Lt => {
                        if cmp(f, &alo, &bhi) != Ordering::Less {
                            return None;
                        }
                        let a_hi = strictly_below(f, &bhi)?;
                        let b_lo = strictly_above(f, &alo)?;
                        (
                            clamp_total(f, (alo, ahi), (f.inf(true), a_hi))?,
                            clamp_total(f, (blo, bhi), (b_lo, f.inf(false)))?,
                        )
                    }
                    _ => {
                        if cmp(f, &alo, &bhi) == Ordering::Greater {
                            return None;
                        }
                        let a_hi = at_most(f, &bhi);
                        let b_lo = at_least(f, &alo);
                        (
                            clamp_total(f, (alo, ahi), (f.inf(true), a_hi))?,
                            clamp_total(f, (blo, bhi), (b_lo, f.inf(false)))?,
                        )
                    }
                };
                let fa = refine_arg(
                    args[0],
                    f,
                    Floats {
                        nan: false,
                        range: Some(ra),
                    },
                )?;
                let fb = refine_arg(
                    args[1],
                    f,
                    Floats {
                        nan: false,
                        range: Some(rb),
                    },
                )?;
                Some([fa, fb, None])
            } else {
                let (mut ta, mut tb) = (da, db);
                if !db.nan {
                    let (blo, bhi) = db.range?;
                    ta.range = match d.op {
                        FpOp::Eq if cmp(f, &blo, &bhi) == Ordering::Equal => {
                            exclude_val(f, ta.range, &blo)
                        }
                        FpOp::Eq => ta.range,
                        FpOp::Lt => ta
                            .range
                            .and_then(|ra| clamp_total(f, ra, (at_least(f, &blo), f.inf(false)))),
                        _ => ta.range.and_then(|ra| {
                            strictly_above(f, &blo)
                                .and_then(|lo| clamp_total(f, ra, (lo, f.inf(false))))
                        }),
                    };
                }
                if !da.nan {
                    let (alo, ahi) = da.range?;
                    tb.range = match d.op {
                        FpOp::Eq if cmp(f, &alo, &ahi) == Ordering::Equal => {
                            exclude_val(f, tb.range, &alo)
                        }
                        FpOp::Eq => tb.range,
                        FpOp::Lt => tb
                            .range
                            .and_then(|rb| clamp_total(f, rb, (f.inf(true), at_most(f, &ahi)))),
                        _ => tb.range.and_then(|rb| {
                            strictly_below(f, &ahi)
                                .and_then(|hi| clamp_total(f, rb, (f.inf(true), hi)))
                        }),
                    };
                }
                let fa = refine_arg(args[0], f, ta)?;
                let fb = refine_arg(args[1], f, tb)?;
                Some([fa, fb, None])
            }
        }
        FpOp::Add(_) | FpOp::Mul(_) | FpOp::Div(_) | FpOp::Fma(_) | FpOp::Rem => {
            let dr = decode(f, r);
            let res_may_nan = r.contains(&f.nan());
            if !res_may_nan && dr.range.is_none() {
                return None;
            }
            if res_may_nan {
                return Some([None, None, None]);
            }
            let mut out = [None, None, None];
            for (k, &arg) in args.iter().enumerate() {
                let mut dk = decode(f, arg);
                dk.nan = false;
                if d.op == FpOp::Rem {
                    if k == 0 {
                        // `±∞ rem b` is always NaN.
                        let one = BitVec::one(f.width());
                        let max_pos = sub(&f.inf(false), &one);
                        let max_neg = sub(&f.inf(true), &one);
                        dk.range = dk
                            .range
                            .and_then(|rk| clamp_total(f, rk, (max_neg, max_pos)));
                    } else if k == 1 {
                        // `a rem ±0` is always NaN.
                        dk.range = exclude_val(f, dk.range, &f.zero(false));
                    }
                }
                out[k] = refine_arg(arg, f, dk)?;
            }
            Some(out)
        }
        FpOp::RoundToIntegral(_) => {
            let dr = decode(f, r);
            let res_may_nan = r.contains(&f.nan());
            if !res_may_nan && dr.range.is_none() {
                return None;
            }
            let da = decode(f, args[0]);
            if dr.range.is_none() {
                let fa = refine_arg(
                    args[0],
                    f,
                    Floats {
                        nan: da.nan,
                        range: None,
                    },
                )?;
                return Some([fa, None, None]);
            }
            if !res_may_nan {
                let fa = refine_arg(
                    args[0],
                    f,
                    Floats {
                        nan: false,
                        range: da.range,
                    },
                )?;
                return Some([fa, None, None]);
            }
            Some([None, None, None])
        }
        FpOp::Sqrt(_) => {
            let dr = decode(f, r);
            let res_may_nan = r.contains(&f.nan());
            if !res_may_nan && dr.range.is_none() {
                return None;
            }
            let da = decode(f, args[0]);
            let one = BitVec::one(f.width());
            if dr.range.is_none() {
                // Result must be NaN: operand is NaN or strictly negative (`< −0.0`).
                let neg_hi = add(&f.zero(true), &one);
                let range = da
                    .range
                    .and_then(|ra| clamp_total(f, ra, (f.inf(true), neg_hi)));
                let fa = refine_arg(args[0], f, Floats { nan: da.nan, range })?;
                return Some([fa, None, None]);
            }
            if !res_may_nan {
                let (rlo, rhi) = dr.range?;
                if cmp(f, &rhi, &f.zero(false)) == Ordering::Less {
                    return None;
                }
                let a_lo = if cmp(f, &rlo, &f.zero(false)) == Ordering::Greater {
                    one
                } else if !rlo.msb() {
                    f.zero(false)
                } else {
                    f.zero(true)
                };
                let a_hi = if rhi == f.zero(true) {
                    f.zero(true)
                } else if rhi == f.zero(false) {
                    f.zero(false)
                } else {
                    f.inf(false)
                };
                let range = clamp_total(f, da.range?, (a_lo, a_hi))?;
                let fa = refine_arg(
                    args[0],
                    f,
                    Floats {
                        nan: false,
                        range: Some(range),
                    },
                )?;
                return Some([fa, None, None]);
            }
            Some([None, None, None])
        }
        FpOp::Convert { to, .. } => {
            let dr = decode(to, r);
            let res_may_nan = r.contains(&to.nan());
            if !res_may_nan && dr.range.is_none() {
                return None;
            }
            let da = decode(f, args[0]);
            if dr.range.is_none() {
                let fa = refine_arg(
                    args[0],
                    f,
                    Floats {
                        nan: da.nan,
                        range: None,
                    },
                )?;
                return Some([fa, None, None]);
            }
            let (rlo, rhi) = dr.range?;
            let nan = da.nan && res_may_nan;
            let mut range = da.range;
            if f.eb() <= to.eb() && f.sb() <= to.sb() {
                // Lossless widening: every non-NaN value of `f` embeds into `to` without rounding,
                // so rounding `[rlo, rhi]` inward (`Rtp` on `rlo`, `Rtn` on `rhi`) is exact.
                let lo_f = to.convert(f, RoundingMode::Rtp, &rlo).ok()?;
                let hi_f = to.convert(f, RoundingMode::Rtn, &rhi).ok()?;
                range = range.and_then(|ra| clamp_total(f, ra, (lo_f, hi_f)));
            }
            if !nan && range.is_none() {
                return None;
            }
            if nan != da.nan || range != da.range {
                let fa = refine_arg(args[0], f, Floats { nan, range })?;
                return Some([fa, None, None]);
            }
            Some([None, None, None])
        }
        FpOp::Min | FpOp::Max => {
            let dr = decode(f, r);
            let res_may_nan = r.contains(&f.nan());
            if !res_may_nan && dr.range.is_none() {
                return None;
            }
            if res_may_nan {
                return Some([None, None, None]);
            }
            let (rlo, rhi) = dr.range?;
            let (da, db) = (decode(f, args[0]), decode(f, args[1]));
            if da.range.is_none() && db.range.is_none() {
                return None;
            }
            let tighten = |own: Floats, other: Floats| -> Floats {
                let nan = own.nan
                    && other
                        .range
                        .and_then(|ro| clamp_total(f, ro, (rlo, rhi)))
                        .is_some();
                let range = own.range.and_then(|ro| {
                    if d.op == FpOp::Min {
                        let hi = if other
                            .range
                            .is_none_or(|(olo, _)| total_cmp(f, &olo, &rhi) == Ordering::Greater)
                        {
                            rhi
                        } else {
                            f.inf(false)
                        };
                        clamp_total(f, ro, (rlo, hi))
                    } else {
                        let lo = if other
                            .range
                            .is_none_or(|(_, ohi)| total_cmp(f, &ohi, &rlo) == Ordering::Less)
                        {
                            rlo
                        } else {
                            f.inf(true)
                        };
                        clamp_total(f, ro, (lo, rhi))
                    }
                });
                Floats { nan, range }
            };
            let fa = refine_arg(args[0], f, tighten(da, db))?;
            let fb = refine_arg(args[1], f, tighten(db, da))?;
            Some([fa, fb, None])
        }
        FpOp::FromSInt(_) | FpOp::FromUInt(_) => {
            decode(f, r).range?;
            Some([None, None, None])
        }
        FpOp::ToSInt(_, w) | FpOp::ToUInt(_, w) => {
            if !r.contains(&BitVec::zero(w)) {
                // NaN always converts to 0; for `ToUInt`, every float `<= +0.0` also converts to 0.
                let mut da = decode(f, args[0]);
                da.nan = false;
                if matches!(d.op, FpOp::ToUInt(..)) {
                    da.range = da
                        .range
                        .and_then(|ra| clamp_total(f, ra, (BitVec::one(f.width()), f.inf(false))));
                }
                let fa = refine_arg(args[0], f, da)?;
                return Some([fa, None, None]);
            }
            Some([None, None, None])
        }
    }
}
