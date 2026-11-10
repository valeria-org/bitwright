//! The value operations the solver performs by the million, in one word when the width is at
//! most 64. A [`BitVec`] has room for 512 bits, and its general operations pay for that on
//! every call: these give the same results (each falls back on the general operation above 64
//! bits, or for what it does not take), computed on the low limb.

use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// The low `bits` bits of a word (`bits` in `1..=64`).
#[inline]
fn mask(bits: u16) -> u64 {
    u64::MAX >> (64 - bits)
}

/// `a op b` ([`BitVec::bin_unchecked`]).
#[inline]
pub(crate) fn bin(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
    let w = a.width();
    if w.bits() <= 64 && b.width() == w {
        let (x, y) = (a.limbs()[0], b.limbs()[0]);
        let r = match op {
            BinOp::Add => x.wrapping_add(y) & mask(w.bits()),
            BinOp::Sub => x.wrapping_sub(y) & mask(w.bits()),
            BinOp::Mul => x.wrapping_mul(y) & mask(w.bits()),
            BinOp::And => x & y,
            BinOp::Or => x | y,
            BinOp::Xor => x ^ y,
            _ => return BitVec::bin_unchecked(op, a, b),
        };
        return BitVec::from_canonical_u64(w, r);
    }
    BitVec::bin_unchecked(op, a, b)
}

/// `op a` ([`BitVec::un_unchecked`]).
#[inline]
pub(crate) fn un(op: UnOp, a: &BitVec) -> BitVec {
    let w = a.width();
    if w.bits() <= 64 {
        let x = a.limbs()[0];
        let r = match op {
            UnOp::Neg => x.wrapping_neg() & mask(w.bits()),
            UnOp::Not => !x & mask(w.bits()),
            _ => return BitVec::un_unchecked(op, a),
        };
        return BitVec::from_canonical_u64(w, r);
    }
    BitVec::un_unchecked(op, a)
}

/// One ([`BitVec::one`]).
#[inline]
pub(crate) fn one(w: Width) -> BitVec {
    BitVec::from_canonical_u64(w, 1)
}

/// `v` truncated to `w` bits ([`BitVec::wrapping_from_u64`]).
#[inline]
pub(crate) fn small(w: Width, v: u64) -> BitVec {
    match w.bits() {
        bits if bits < 64 => BitVec::from_canonical_u64(w, v & mask(bits)),
        _ => BitVec::from_canonical_u64(w, v),
    }
}

/// `v` in two's complement at `w` bits ([`BitVec::wrapping_from_i128`]).
#[inline]
pub(crate) fn signed(w: Width, v: i128) -> BitVec {
    match w.bits() {
        bits if bits <= 64 => BitVec::from_canonical_u64(w, v as u64 & mask(bits)),
        _ => BitVec::wrapping_from_i128(w, v),
    }
}

/// `a & b`.
#[inline]
pub(crate) fn bv_and(a: &BitVec, b: &BitVec) -> BitVec {
    bin(BinOp::And, a, b)
}

/// `a | b`.
#[inline]
pub(crate) fn bv_or(a: &BitVec, b: &BitVec) -> BitVec {
    bin(BinOp::Or, a, b)
}

/// `a ^ b`.
#[inline]
pub(crate) fn bv_xor(a: &BitVec, b: &BitVec) -> BitVec {
    bin(BinOp::Xor, a, b)
}

/// `~a`.
#[inline]
pub(crate) fn bv_not(a: &BitVec) -> BitVec {
    un(UnOp::Not, a)
}

/// `a << k` (zero from the width on), as `crate::facts::known::bv_shl`.
#[inline]
pub(crate) fn bv_shl(a: &BitVec, k: u32) -> BitVec {
    let w = a.width();
    if w.bits() <= 64 {
        let r = match k < u32::from(w.bits()) {
            true => a.limbs()[0] << k & mask(w.bits()),
            false => 0,
        };
        return BitVec::from_canonical_u64(w, r);
    }
    crate::facts::known::bv_shl(a, k)
}

/// `a >> k`, logical (zero from the width on), as `crate::facts::known::bv_lshr`.
#[inline]
pub(crate) fn bv_lshr(a: &BitVec, k: u32) -> BitVec {
    let w = a.width();
    if w.bits() <= 64 {
        let r = match k < u32::from(w.bits()) {
            true => a.limbs()[0] >> k,
            false => 0,
        };
        return BitVec::from_canonical_u64(w, r);
    }
    crate::facts::known::bv_lshr(a, k)
}

/// The low `k` bits set (`k` may exceed the width), as `crate::facts::known::low_mask`.
#[inline]
pub(crate) fn low_mask(w: Width, k: u32) -> BitVec {
    if w.bits() <= 64 {
        let r = match k {
            0 => 0,
            k if k >= u32::from(w.bits()) => mask(w.bits()),
            k => mask(k as u16),
        };
        return BitVec::from_canonical_u64(w, r);
    }
    crate::facts::known::low_mask(w, k)
}

/// The number of trailing zero bits of `a` within its width (the width for zero), as
/// `crate::facts::known::trailing_zeros`.
#[inline]
pub(crate) fn trailing_zeros(a: &BitVec) -> u32 {
    for (i, &l) in a.limbs().iter().enumerate() {
        if l != 0 {
            return 64 * i as u32 + l.trailing_zeros();
        }
    }
    u32::from(a.width().bits())
}

pub(crate) use crate::facts::known::count_ones;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::facts::known;

    /// Values of interest at `w`: the corners and a spread of others.
    fn values(w: Width) -> Vec<BitVec> {
        let mut seed = 0x9e37_79b9_7f4a_7c15u64 ^ u64::from(w.bits());
        let mut next = || {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            seed
        };
        let mut out = vec![
            BitVec::zero(w),
            BitVec::one(w),
            BitVec::ones(w),
            BitVec::smin(w),
            BitVec::smax(w),
            BitVec::wrapping_from_u64(w, 2),
        ];
        for _ in 0..10 {
            let limbs: Vec<u64> = (0..8).map(|_| next()).collect();
            out.push(BitVec::wrapping_from_limbs(w, &limbs));
            out.push(BitVec::wrapping_from_u64(w, next() >> (next() % 64)));
        }
        out
    }

    #[test]
    fn the_word_operations_are_the_general_ones() {
        for bits in [1u16, 2, 3, 7, 8, 31, 32, 33, 63, 64, 65, 128, 200, 512] {
            let w = Width::new(bits).unwrap();
            let vs = values(w);
            assert_eq!(one(w), BitVec::one(w));
            for v in [0u64, 1, 2, 3, 255, u64::MAX, 1 << 63] {
                assert_eq!(small(w, v), BitVec::wrapping_from_u64(w, v), "{v} at {bits}");
            }
            for v in [0i128, 1, -1, 2, -2, 4, -4, i128::from(i64::MIN), i128::MAX, i128::MIN] {
                assert_eq!(signed(w, v), BitVec::wrapping_from_i128(w, v), "{v} at {bits}");
            }
            for k in [0u32, 1, 2, u32::from(bits) - 1, u32::from(bits), u32::from(bits) + 1, 600] {
                assert_eq!(low_mask(w, k), known::low_mask(w, k), "{k} at {bits}");
            }
            for a in &vs {
                assert_eq!(un(UnOp::Neg, a), BitVec::un_unchecked(UnOp::Neg, a));
                assert_eq!(un(UnOp::Not, a), BitVec::un_unchecked(UnOp::Not, a));
                assert_eq!(un(UnOp::Popcnt, a), BitVec::un_unchecked(UnOp::Popcnt, a));
                assert_eq!(bv_not(a), known::bv_not(a));
                assert_eq!(trailing_zeros(a), known::trailing_zeros(a), "{a:?}");
                for k in [0u32, 1, 5, u32::from(bits) - 1, u32::from(bits), 700] {
                    assert_eq!(bv_shl(a, k), known::bv_shl(a, k), "{a:?} << {k}");
                    assert_eq!(bv_lshr(a, k), known::bv_lshr(a, k), "{a:?} >> {k}");
                }
                for b in &vs {
                    for op in [
                        BinOp::Add,
                        BinOp::Sub,
                        BinOp::Mul,
                        BinOp::And,
                        BinOp::Or,
                        BinOp::Xor,
                        BinOp::AShr,
                    ] {
                        assert_eq!(bin(op, a, b), BitVec::bin_unchecked(op, a, b), "{op:?}");
                    }
                    assert_eq!(bv_and(a, b), known::bv_and(a, b));
                    assert_eq!(bv_or(a, b), known::bv_or(a, b));
                    assert_eq!(bv_xor(a, b), known::bv_xor(a, b));
                }
            }
        }
    }
}
