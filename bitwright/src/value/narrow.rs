//! Native fast path for widths `1..=128`: the value is one `u128` with canonical padding.

use crate::ops::{BinOp, CmpOp, UnOp};

#[inline]
pub(crate) const fn mask(w: u16) -> u128 {
    if w >= 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    }
}

#[inline]
fn msb(a: u128, w: u16) -> bool {
    (a >> (w - 1)) & 1 == 1
}

/// Two's-complement interpretation of a canonical `w`-bit value.
#[inline]
pub(crate) fn signed(a: u128, w: u16) -> i128 {
    let sh = 128 - u32::from(w);
    ((a << sh) as i128) >> sh
}

#[inline]
fn count(b: u128, w: u16) -> Option<u32> {
    (b < u128::from(w)).then_some(b as u32)
}

fn udiv(a: u128, b: u128, w: u16) -> u128 {
    a.checked_div(b).unwrap_or(mask(w))
}

fn urem(a: u128, b: u128) -> u128 {
    a.checked_rem(b).unwrap_or(a)
}

fn neg(a: u128, w: u16) -> u128 {
    a.wrapping_neg() & mask(w)
}

fn rotl_by(a: u128, r: u32, w: u16) -> u128 {
    if r == 0 {
        a
    } else {
        ((a << r) | (a >> (u32::from(w) - r))) & mask(w)
    }
}

pub(crate) fn un(op: UnOp, w: u16, a: u128) -> u128 {
    let m = mask(w);
    match op {
        UnOp::Not => !a & m,
        UnOp::Neg => neg(a, w),
        UnOp::Popcnt => u128::from(a.count_ones()),
        UnOp::Clz => u128::from(a.leading_zeros() - (128 - u32::from(w))),
        UnOp::Ctz => {
            if a == 0 {
                u128::from(w)
            } else {
                u128::from(a.trailing_zeros())
            }
        }
        // The caller guarantees w % 8 == 0.
        UnOp::Bswap => a.swap_bytes() >> (128 - u32::from(w)),
        UnOp::BitRev => a.reverse_bits() >> (128 - u32::from(w)),
    }
}

/// Every binary operator except the multiply-high pair above 64 bits, which needs a 256-bit
/// product (see [`bin_supported`]).
pub(crate) fn bin(op: BinOp, w: u16, a: u128, b: u128) -> u128 {
    debug_assert!(
        bin_supported(op, w),
        "{op:?} at {w} bits needs the limb kernel"
    );
    let m = mask(w);
    match op {
        BinOp::Add => a.wrapping_add(b) & m,
        BinOp::Sub => a.wrapping_sub(b) & m,
        BinOp::Mul => a.wrapping_mul(b) & m,
        BinOp::UMulHi => (a * b) >> w,
        BinOp::SMulHi => ((signed(a, w) * signed(b, w)) >> w) as u128 & m,
        BinOp::UDiv => udiv(a, b, w),
        BinOp::URem => urem(a, b),
        BinOp::SDiv => match (msb(a, w), msb(b, w)) {
            (false, false) => udiv(a, b, w),
            (true, false) => neg(udiv(neg(a, w), b, w), w),
            (false, true) => neg(udiv(a, neg(b, w), w), w),
            (true, true) => udiv(neg(a, w), neg(b, w), w),
        },
        BinOp::SRem => match (msb(a, w), msb(b, w)) {
            (false, false) => urem(a, b),
            (true, false) => neg(urem(neg(a, w), b), w),
            (false, true) => urem(a, neg(b, w)),
            (true, true) => neg(urem(neg(a, w), neg(b, w)), w),
        },
        BinOp::And => a & b,
        BinOp::Or => a | b,
        BinOp::Xor => a ^ b,
        BinOp::Shl => count(b, w).map_or(0, |c| (a << c) & m),
        BinOp::LShr => count(b, w).map_or(0, |c| a >> c),
        BinOp::AShr => {
            let c = count(b, w).unwrap_or(u32::from(w) - 1);
            (signed(a, w) >> c) as u128 & m
        }
        BinOp::RotL => rotl_by(a, (b % u128::from(w)) as u32, w),
        BinOp::RotR => {
            let r = (b % u128::from(w)) as u32;
            rotl_by(a, (u32::from(w) - r) % u32::from(w), w)
        }
        BinOp::Pdep => {
            let (mut out, mut mm, mut k) = (0u128, b, 0u32);
            while mm != 0 {
                let p = mm.trailing_zeros();
                if (a >> k) & 1 == 1 {
                    out |= 1 << p;
                }
                k += 1;
                mm &= mm - 1;
            }
            out
        }
        BinOp::Pext => {
            let (mut out, mut mm, mut k) = (0u128, b, 0u32);
            while mm != 0 {
                let p = mm.trailing_zeros();
                if (a >> p) & 1 == 1 {
                    out |= 1 << k;
                }
                k += 1;
                mm &= mm - 1;
            }
            out
        }
    }
}

/// Whether [`bin`] handles `op` at width `w`.
#[inline]
pub(crate) fn bin_supported(op: BinOp, w: u16) -> bool {
    w <= 64 || !matches!(op, BinOp::UMulHi | BinOp::SMulHi)
}

pub(crate) fn cmp(op: CmpOp, w: u16, a: u128, b: u128) -> bool {
    match op {
        CmpOp::Eq => a == b,
        CmpOp::Ne => a != b,
        CmpOp::Ult => a < b,
        CmpOp::Ule => a <= b,
        CmpOp::Slt => signed(a, w) < signed(b, w),
        CmpOp::Sle => signed(a, w) <= signed(b, w),
    }
}
