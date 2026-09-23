//! Non-wrapping unsigned and signed intervals.

use crate::ops::CmpOp;
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

/// The unsigned interval `[lo, hi]` (`lo <=u hi`, no wrap-around).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct URange {
    lo: BitVec,
    hi: BitVec,
}

impl URange {
    /// Every value.
    pub fn full(w: Width) -> Self {
        URange {
            lo: BitVec::zero(w),
            hi: BitVec::ones(w),
        }
    }

    /// One value.
    pub fn constant(v: &BitVec) -> Self {
        URange { lo: *v, hi: *v }
    }

    /// `[lo, hi]`, if the widths match and `lo <=u hi`.
    pub fn new(lo: BitVec, hi: BitVec) -> Option<Self> {
        (lo.width() == hi.width() && ule(&lo, &hi)).then_some(URange { lo, hi })
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
        v.width() == self.width() && ule(&self.lo, v) && ule(v, &self.hi)
    }

    /// Whether the interval is every value.
    pub fn is_full(&self) -> bool {
        self.lo.is_zero() && self.hi.is_ones()
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
        URange::new(umax(self.lo, o.lo), umin(self.hi, o.hi))
    }

    /// The smallest interval containing both; `None` if the widths differ.
    pub fn join(&self, o: &URange) -> Option<URange> {
        (self.width() == o.width()).then(|| self.hull(o))
    }

    /// `join` for operands known to have the same width.
    pub(crate) fn hull(&self, o: &URange) -> URange {
        debug_assert_eq!(self.width(), o.width());
        URange {
            lo: umin(self.lo, o.lo),
            hi: umax(self.hi, o.hi),
        }
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
