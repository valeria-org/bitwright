//! Unsigned strided intervals and signed intervals, neither wrapping around.

use crate::ops::{BinOp, CmpOp};
use crate::{BitVec, Width};

pub(crate) fn ult(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Ult, a, b)
}
pub(crate) fn ule(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Ule, a, b)
}
pub(crate) fn slt(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Slt, a, b)
}
pub(crate) fn sle(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Sle, a, b)
}

fn umin(a: BitVec, b: BitVec) -> BitVec {
    if ult(&a, &b) { a } else { b }
}
fn umax(a: BitVec, b: BitVec) -> BitVec {
    if ult(&a, &b) { b } else { a }
}
fn smin(a: BitVec, b: BitVec) -> BitVec {
    if slt(&a, &b) { a } else { b }
}
fn smax(a: BitVec, b: BitVec) -> BitVec {
    if slt(&a, &b) { b } else { a }
}

// ----- residue arithmetic ----------------------------------------------------------------------

/// `v mod m`, for `m >= 1`.
pub(crate) fn rem(v: &BitVec, m: u64) -> u64 {
    if m == 1 {
        return 0;
    }
    let m = u128::from(m);
    let mut r = 0u128;
    for &limb in v.limbs().iter().rev() {
        r = ((r << 64) | u128::from(limb)) % m;
    }
    r as u64
}

/// The greatest common divisor (`gcd(0, b) = b`).
pub(crate) fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// The inverse of `a` modulo `n` (`n >= 2`), if `a` is invertible.
fn inverse(a: u64, n: u64) -> Option<u64> {
    let (mut t, mut next_t) = (0i128, 1i128);
    let (mut r, mut next_r) = (i128::from(n), i128::from(a % n));
    while next_r != 0 {
        let q = r / next_r;
        (t, next_t) = (next_t, t - q * next_t);
        (r, next_r) = (next_r, r - q * next_r);
    }
    (r == 1).then(|| t.rem_euclid(i128::from(n)) as u64)
}

/// The residue class common to `x ≡ r1 (mod m1)` and `x ≡ r2 (mod m2)` (moduli at least 1), as
/// `(r, lcm)`: `None` if there is none, `Some(None)` if its modulus does not fit in 64 bits.
pub(crate) fn crt(r1: u64, m1: u64, r2: u64, m2: u64) -> Option<Option<(u64, u64)>> {
    let (r1, r2) = (r1 % m1, r2 % m2);
    let g = gcd(m1, m2);
    if r1 % g != r2 % g {
        return None;
    }
    let Ok(lcm) = u64::try_from(u128::from(m1 / g) * u128::from(m2)) else {
        return Some(None);
    };
    // x = r1 + m1·k, where (m1 / g)·k ≡ (r2 − r1) / g (mod m2 / g).
    let n = m2 / g;
    let k = if n == 1 {
        0
    } else {
        let d = ((i128::from(r2) - i128::from(r1)) / i128::from(g)).rem_euclid(i128::from(n));
        let inv = inverse(m1 / g, n)?;
        (d as u128 * u128::from(inv)) % u128::from(n)
    };
    let x = (u128::from(r1) + u128::from(m1) * k) % u128::from(lcm);
    Some(Some((x as u64, lcm)))
}

/// `v + d`, if it does not wrap.
fn add_small(v: &BitVec, d: u64) -> Option<BitVec> {
    let w = v.width();
    if w.bits() < 64 && d >> w.bits() != 0 {
        return None;
    }
    let r = BitVec::bin_unchecked(BinOp::Add, v, &BitVec::wrapping_from_u64(w, d));
    ule(v, &r).then_some(r)
}

/// `v − d`, if it does not wrap.
fn sub_small(v: &BitVec, d: u64) -> Option<BitVec> {
    let w = v.width();
    if w.bits() < 64 && d >> w.bits() != 0 {
        return None;
    }
    let r = BitVec::bin_unchecked(BinOp::Sub, v, &BitVec::wrapping_from_u64(w, d));
    ule(&r, v).then_some(r)
}

/// The smallest value `>= lo` congruent to `r` modulo `m`, if one fits the width.
fn snap_up(lo: &BitVec, r: u64, m: u64) -> Option<BitVec> {
    if m <= 1 {
        return Some(*lo);
    }
    let d = (u128::from(r % m) + u128::from(m) - u128::from(rem(lo, m))) % u128::from(m);
    add_small(lo, d as u64)
}

/// The largest value `<= hi` congruent to `r` modulo `m`, if there is one.
fn snap_down(hi: &BitVec, r: u64, m: u64) -> Option<BitVec> {
    if m <= 1 {
        return Some(*hi);
    }
    let d = (u128::from(rem(hi, m)) + u128::from(m) - u128::from(r % m)) % u128::from(m);
    sub_small(hi, d as u64)
}

/// A stride dividing the non-zero distance `d`: `d` itself when it fits, else the largest power
/// of two dividing it that does.
pub(crate) fn stride_of(d: &BitVec) -> u64 {
    match d.to_u64() {
        Some(v) if v > 0 => v,
        _ => 1 << super::known::trailing_zeros(d).min(63),
    }
}

// ----- unsigned strided intervals --------------------------------------------------------------

/// The unsigned strided interval `{lo, lo + stride, lo + 2·stride, …, hi}` (`lo <=u hi`, no
/// wrap-around). The stride is 0 exactly when `lo == hi`, and otherwise divides `hi − lo`, so
/// both bounds are members. A stride of 1 is the plain interval `[lo, hi]`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct URange {
    lo: BitVec,
    hi: BitVec,
    stride: u64,
}

impl URange {
    /// Every value.
    pub fn full(w: Width) -> Self {
        URange {
            lo: BitVec::zero(w),
            hi: BitVec::ones(w),
            stride: 1,
        }
    }

    /// One value.
    pub fn constant(v: &BitVec) -> Self {
        URange {
            lo: *v,
            hi: *v,
            stride: 0,
        }
    }

    /// `[lo, hi]` (stride 1), if the widths match and `lo <=u hi`.
    pub fn new(lo: BitVec, hi: BitVec) -> Option<Self> {
        (lo.width() == hi.width() && ule(&lo, &hi)).then(|| URange::from_parts(lo, hi, 1))
    }

    /// `{lo, lo + stride, …, hi}`, if the widths match, `lo <=u hi`, and `stride` is at least 1
    /// and divides `hi − lo` (when `lo == hi`, one value whatever the stride).
    pub fn strided(lo: BitVec, hi: BitVec, stride: u64) -> Option<Self> {
        if lo.width() != hi.width() || !ule(&lo, &hi) {
            return None;
        }
        if lo == hi {
            return Some(URange::constant(&lo));
        }
        let span = BitVec::bin_unchecked(BinOp::Sub, &hi, &lo);
        (stride >= 1 && rem(&span, stride) == 0).then_some(URange { lo, hi, stride })
    }

    /// From parts known to form a strided interval; the stride of one value becomes 0.
    pub(crate) fn from_parts(lo: BitVec, hi: BitVec, stride: u64) -> Self {
        debug_assert!(lo.width() == hi.width() && ule(&lo, &hi));
        let stride = if lo == hi { 0 } else { stride.max(1) };
        debug_assert!(
            stride == 0 || rem(&BitVec::bin_unchecked(BinOp::Sub, &hi, &lo), stride) == 0,
            "stride {stride} does not divide [{lo}, {hi}]"
        );
        URange { lo, hi, stride }
    }

    /// From parts that already form a normalized strided interval (as cached).
    pub(crate) fn from_raw(lo: BitVec, hi: BitVec, stride: u64) -> Self {
        debug_assert_eq!(URange::from_parts(lo, hi, stride).stride, stride);
        URange { lo, hi, stride }
    }

    /// The lower bound (a member).
    pub fn lo(&self) -> BitVec {
        self.lo
    }

    /// The upper bound (a member).
    pub fn hi(&self) -> BitVec {
        self.hi
    }

    /// The distance between consecutive members: 0 for one value, 1 for a plain interval.
    pub fn stride(&self) -> u64 {
        self.stride
    }

    /// The width.
    pub fn width(&self) -> Width {
        self.lo.width()
    }

    /// Whether `v` is a member.
    pub fn contains(&self, v: &BitVec) -> bool {
        v.width() == self.width()
            && ule(&self.lo, v)
            && ule(v, &self.hi)
            && (self.stride <= 1
                || rem(&BitVec::bin_unchecked(BinOp::Sub, v, &self.lo), self.stride) == 0)
    }

    /// Whether every member of `self` is a member of `o`.
    pub(crate) fn within(&self, o: &URange) -> bool {
        if !ule(&o.lo, &self.lo) || !ule(&self.hi, &o.hi) {
            return false;
        }
        if o.stride <= 1 {
            return true;
        }
        let offset = rem(
            &BitVec::bin_unchecked(BinOp::Sub, &self.lo, &o.lo),
            o.stride,
        );
        offset == 0 && (self.stride == 0 || self.stride.is_multiple_of(o.stride))
    }

    /// Whether the interval is every value.
    pub fn is_full(&self) -> bool {
        self.lo.is_zero() && self.hi.is_ones() && self.stride == 1
    }

    /// The single value, if the interval has one.
    pub fn as_constant(&self) -> Option<BitVec> {
        (self.lo == self.hi).then_some(self.lo)
    }

    /// The intersection; `None` if empty or the widths differ.
    pub fn meet(&self, o: &URange) -> Option<URange> {
        if self.width() != o.width() {
            return None;
        }
        // One value is in the meet when both contain it.
        if self.stride == 0 {
            return o.contains(&self.lo).then_some(*self);
        }
        if o.stride == 0 {
            return self.contains(&o.lo).then_some(*o);
        }
        let (lo, hi) = (umax(self.lo, o.lo), umin(self.hi, o.hi));
        if ult(&hi, &lo) {
            return None;
        }
        let (r1, r2) = (rem(&self.lo, self.stride), rem(&o.lo, o.stride));
        let (r, m) = match crt(r1, self.stride, r2, o.stride)? {
            Some(class) => class,
            // A common class too fine to represent: the finer given one contains the meet.
            None if self.stride >= o.stride => (r1, self.stride),
            None => (r2, o.stride),
        };
        URange::snapped(&lo, &hi, r, m)
    }

    /// The members congruent to `r` modulo `m` (`m >= 1`); `None` if there are none.
    pub(crate) fn meet_class(&self, r: u64, m: u64) -> Option<URange> {
        if m <= 1 {
            return Some(*self);
        }
        if self.stride == 0 {
            return (rem(&self.lo, m) == r % m).then_some(*self);
        }
        let own = rem(&self.lo, self.stride);
        let (r, m) = crt(own, self.stride, r, m)?.unwrap_or((own, self.stride));
        URange::snapped(&self.lo, &self.hi, r, m)
    }

    /// The values of `[lo, hi]` congruent to `r` modulo `m`, if any.
    fn snapped(lo: &BitVec, hi: &BitVec, r: u64, m: u64) -> Option<URange> {
        let lo = snap_up(lo, r, m)?;
        let hi = snap_down(hi, r, m)?;
        ule(&lo, &hi).then(|| URange::from_parts(lo, hi, m))
    }

    /// The smallest strided interval containing both; `None` if the widths differ.
    pub fn join(&self, o: &URange) -> Option<URange> {
        (self.width() == o.width()).then(|| self.hull(o))
    }

    /// `join` for operands known to have the same width.
    pub(crate) fn hull(&self, o: &URange) -> URange {
        debug_assert_eq!(self.width(), o.width());
        let (lo, hi) = (umin(self.lo, o.lo), umax(self.hi, o.hi));
        if lo == hi {
            return URange::constant(&lo);
        }
        // Every member of either is congruent to `lo` modulo the strides' common divisor that
        // also divides the distance between the two lower bounds.
        let apart = BitVec::bin_unchecked(BinOp::Sub, &umax(self.lo, o.lo), &lo);
        let g = gcd(self.stride, o.stride);
        let stride = match g {
            0 => stride_of(&apart),
            _ => gcd(g, rem(&apart, g)),
        };
        URange::from_parts(lo, hi, stride)
    }
}

/// The signed interval `[lo, hi]` (`lo <=s hi`, no wrap-around).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct SRange {
    lo: BitVec,
    hi: BitVec,
}

impl SRange {
    /// Every value.
    pub fn full(w: Width) -> Self {
        SRange {
            lo: BitVec::smin(w),
            hi: BitVec::smax(w),
        }
    }

    /// One value.
    pub fn constant(v: &BitVec) -> Self {
        SRange { lo: *v, hi: *v }
    }

    /// `[lo, hi]`, if the widths match and `lo <=s hi`.
    pub fn new(lo: BitVec, hi: BitVec) -> Option<Self> {
        (lo.width() == hi.width() && sle(&lo, &hi)).then_some(SRange { lo, hi })
    }

    /// `[lo, hi]` from bounds known to form a range (taken from one).
    pub(crate) fn from_bounds(lo: BitVec, hi: BitVec) -> Self {
        debug_assert!(lo.width() == hi.width() && sle(&lo, &hi));
        SRange { lo, hi }
    }

    /// The lower bound.
    pub fn lo(&self) -> BitVec {
        self.lo
    }

    /// The upper bound.
    pub fn hi(&self) -> BitVec {
        self.hi
    }

    /// The width.
    pub fn width(&self) -> Width {
        self.lo.width()
    }

    /// Whether `v` is in the interval.
    pub fn contains(&self, v: &BitVec) -> bool {
        v.width() == self.width() && sle(&self.lo, v) && sle(v, &self.hi)
    }

    /// Whether the interval is every value.
    pub fn is_full(&self) -> bool {
        self.lo == BitVec::smin(self.width()) && self.hi == BitVec::smax(self.width())
    }

    /// The single value, if the interval has one.
    pub fn as_constant(&self) -> Option<BitVec> {
        (self.lo == self.hi).then_some(self.lo)
    }

    /// The intersection; `None` if empty or the widths differ.
    pub fn meet(&self, o: &SRange) -> Option<SRange> {
        if self.width() != o.width() {
            return None;
        }
        SRange::new(smax(self.lo, o.lo), smin(self.hi, o.hi))
    }

    /// The smallest interval containing both; `None` if the widths differ.
    pub fn join(&self, o: &SRange) -> Option<SRange> {
        (self.width() == o.width()).then(|| self.hull(o))
    }

    /// `join` for operands known to have the same width.
    pub(crate) fn hull(&self, o: &SRange) -> SRange {
        debug_assert_eq!(self.width(), o.width());
        SRange {
            lo: smin(self.lo, o.lo),
            hi: smax(self.hi, o.hi),
        }
    }
}
