//! Known bits: which bits of a value are certainly 0 and which are certainly 1.

use core::fmt;

use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// Per-bit knowledge about a `W`-bit value: bits in `zero` are certainly 0, bits in `one` are
/// certainly 1, and the two masks are disjoint. The concretization is every value `v` with
/// `v & zero == 0` and `v & one == one`.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct KnownBits {
    zero: BitVec,
    one: BitVec,
}

pub(crate) fn bv_and(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::And, a, b)
}
pub(crate) fn bv_or(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Or, a, b)
}
pub(crate) fn bv_xor(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Xor, a, b)
}
pub(crate) fn bv_not(a: &BitVec) -> BitVec {
    BitVec::un_unchecked(UnOp::Not, a)
}
pub(crate) fn bv_add(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Add, a, b)
}
pub(crate) fn bv_shl(a: &BitVec, k: u32) -> BitVec {
    let c = BitVec::wrapping_from_u64(a.width(), u64::from(k));
    if u64::from(k) >= u64::from(a.width().bits()) {
        return BitVec::zero(a.width());
    }
    BitVec::bin_unchecked(BinOp::Shl, a, &c)
}
pub(crate) fn bv_lshr(a: &BitVec, k: u32) -> BitVec {
    if u64::from(k) >= u64::from(a.width().bits()) {
        return BitVec::zero(a.width());
    }
    let c = BitVec::wrapping_from_u64(a.width(), u64::from(k));
    BitVec::bin_unchecked(BinOp::LShr, a, &c)
}
/// The low `k` bits set (`k` may exceed the width).
pub(crate) fn low_mask(w: Width, k: u32) -> BitVec {
    if k >= u32::from(w.bits()) {
        BitVec::ones(w)
    } else {
        bv_not(&bv_shl(&BitVec::ones(w), k))
    }
}
/// The high `k` bits set.
pub(crate) fn high_mask(w: Width, k: u32) -> BitVec {
    if k >= u32::from(w.bits()) {
        BitVec::ones(w)
    } else {
        bv_not(&bv_lshr(&BitVec::ones(w), k))
    }
}
pub(crate) fn count_ones(a: &BitVec) -> u32 {
    a.limbs().iter().map(|l| l.count_ones()).sum()
}
/// Number of leading zero bits of `a` within its width.
pub(crate) fn leading_zeros(a: &BitVec) -> u32 {
    let c = BitVec::un_unchecked(UnOp::Clz, a);
    c.to_u64().unwrap_or(0) as u32
}
/// Number of trailing zero bits of `a` within its width.
pub(crate) fn trailing_zeros(a: &BitVec) -> u32 {
    let c = BitVec::un_unchecked(UnOp::Ctz, a);
    c.to_u64().unwrap_or(0) as u32
}

impl KnownBits {
    /// Nothing known.
    pub fn unknown(width: Width) -> Self {
        KnownBits {
            zero: BitVec::zero(width),
            one: BitVec::zero(width),
        }
    }

    /// Every bit known.
    pub fn constant(v: &BitVec) -> Self {
        KnownBits {
            zero: bv_not(v),
            one: *v,
        }
    }

    /// From masks of known-zero and known-one bits; `None` unless the widths are equal and
    /// the masks disjoint.
    pub fn new(zero: BitVec, one: BitVec) -> Option<Self> {
        (zero.width() == one.width() && bv_and(&zero, &one).is_zero())
            .then_some(KnownBits { zero, one })
    }

    pub(crate) fn from_masks(zero: BitVec, one: BitVec) -> Self {
        debug_assert!(bv_and(&zero, &one).is_zero());
        KnownBits { zero, one }
    }

    /// The width.
    pub fn width(&self) -> Width {
        self.zero.width()
    }

    /// Bits that are certainly 0.
    pub fn known_zero(&self) -> BitVec {
        self.zero
    }

    /// Bits that are certainly 1.
    pub fn known_one(&self) -> BitVec {
        self.one
    }

    /// Bits whose value is known.
    pub fn known(&self) -> BitVec {
        bv_or(&self.zero, &self.one)
    }

    /// Bits whose value is not known.
    pub fn unknown_mask(&self) -> BitVec {
        bv_not(&self.known())
    }

    /// Bits that may be 1 (the complement of `known_zero`).
    pub fn maybe_one(&self) -> BitVec {
        bv_not(&self.zero)
    }

    /// The value, if every bit is known.
    pub fn as_constant(&self) -> Option<BitVec> {
        self.known().is_ones().then_some(self.one)
    }

    /// Whether `v` is consistent with this knowledge.
    pub fn contains(&self, v: &BitVec) -> bool {
        v.width() == self.width()
            && bv_and(v, &self.zero).is_zero()
            && bv_and(v, &self.one) == self.one
    }

    /// The knowledge of both (the intersection of the described sets); `None` if they
    /// contradict each other or have different widths.
    pub fn meet(&self, o: &KnownBits) -> Option<KnownBits> {
        if self.width() != o.width() {
            return None;
        }
        let zero = bv_or(&self.zero, &o.zero);
        let one = bv_or(&self.one, &o.one);
        bv_and(&zero, &one)
            .is_zero()
            .then_some(KnownBits { zero, one })
    }

    /// Knowledge true of either (the smallest description of the union); `None` if the
    /// widths differ.
    pub fn join(&self, o: &KnownBits) -> Option<KnownBits> {
        (self.width() == o.width()).then(|| self.hull(o))
    }

    /// `join` for operands known to have the same width.
    pub(crate) fn hull(&self, o: &KnownBits) -> KnownBits {
        debug_assert_eq!(self.width(), o.width());
        KnownBits {
            zero: bv_and(&self.zero, &o.zero),
            one: bv_and(&self.one, &o.one),
        }
    }

    /// Whether bit `i` is known, and its value.
    pub fn bit(&self, i: u16) -> Option<bool> {
        if self.one.bit(i)? {
            Some(true)
        } else if self.zero.bit(i)? {
            Some(false)
        } else {
            None
        }
    }

    /// The smallest unsigned value consistent with the knowledge.
    pub fn umin(&self) -> BitVec {
        self.one
    }

    /// The largest unsigned value consistent with the knowledge.
    pub fn umax(&self) -> BitVec {
        bv_not(&self.zero)
    }

    /// The smallest signed value consistent with the knowledge.
    pub fn smin(&self) -> BitVec {
        let w = self.width();
        let sign = BitVec::smin(w);
        // Set the sign bit unless it is known zero; everything else at its minimum.
        if bv_and(&self.zero, &sign).is_zero() {
            bv_or(&self.one, &sign)
        } else {
            self.one
        }
    }

    /// The largest signed value consistent with the knowledge.
    pub fn smax(&self) -> BitVec {
        let w = self.width();
        let sign = BitVec::smin(w);
        let max = bv_not(&self.zero);
        // Clear the sign bit unless it is known one.
        if bv_and(&self.one, &sign).is_zero() {
            bv_and(&max, &bv_not(&sign))
        } else {
            max
        }
    }

    /// Number of low bits known to be zero.
    pub fn trailing_known_zeros(&self) -> u32 {
        trailing_zeros(&bv_not(&self.zero))
    }

    /// Number of high bits known to be zero.
    pub fn leading_known_zeros(&self) -> u32 {
        leading_zeros(&bv_not(&self.zero))
    }

    /// Number of low bits whose values are all known (a known prefix from bit 0).
    pub fn known_low_prefix(&self) -> u32 {
        trailing_zeros(&self.unknown_mask())
    }

    /// Enumerates every consistent value if there are at most `2^max_unknown_bits` (and at
    /// most 2^20 in any case).
    pub fn enumerate(&self, max_unknown_bits: u32) -> Option<Vec<BitVec>> {
        let unknown = self.unknown_mask();
        let n = count_ones(&unknown);
        if n > max_unknown_bits.min(20) {
            return None;
        }
        let positions: Vec<u16> = (0..self.width().bits())
            .filter(|&i| unknown.bit(i) == Some(true))
            .collect();
        let mut out = Vec::with_capacity(1 << n);
        for k in 0u64..(1u64 << n) {
            let mut limbs: Vec<u64> = self.one.limbs().to_vec();
            for (j, &p) in positions.iter().enumerate() {
                if (k >> j) & 1 == 1 {
                    limbs[p as usize / 64] |= 1 << (p % 64);
                }
            }
            out.push(BitVec::wrapping_from_limbs(self.width(), &limbs));
        }
        Some(out)
    }
}

impl fmt::Debug for KnownBits {
    /// MSB first: `0`, `1` or `?` per bit.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let w = self.width().bits();
        let mut s = String::with_capacity(w as usize + 8);
        for i in (0..w).rev() {
            s.push(match self.bit(i) {
                Some(true) => '1',
                Some(false) => '0',
                None => '?',
            });
        }
        write!(f, "KnownBits({s})")
    }
}
