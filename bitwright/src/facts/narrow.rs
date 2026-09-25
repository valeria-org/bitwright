//! The reduced product for widths up to 128, on one or two machine words: the steps of
//! `Facts::reduce_wide` in the same order, with the same results (a test compares them),
//! without `BitVec` arithmetic. Signed bounds are kept as bit patterns and compared with their
//! sign bits flipped.

use core::ops::{BitAnd, BitOr, BitXor, Not, Shl};

use super::range::crt;
use super::{Facts, KnownBits, SRange, URange};
use crate::{BitVec, Width};

/// A machine word holding a value of at most its own width.
pub(super) trait Word:
    Copy
    + Ord
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
    + BitXor<Output = Self>
    + Not<Output = Self>
    + Shl<u32, Output = Self>
{
    const BITS: u32;
    const ZERO: Self;
    const ONE: Self;
    fn leading_zeros(self) -> u32;
    fn trailing_zeros(self) -> u32;
    /// `self mod m` (`m >= 1`).
    fn rem(self, m: u64) -> u64;
    fn checked_add_small(self, d: u64) -> Option<Self>;
    fn checked_sub_small(self, d: u64) -> Option<Self>;
    fn from_bits(v: &BitVec) -> Self;
    fn to_bits(self, w: Width) -> BitVec;
}

impl Word for u64 {
    const BITS: u32 = 64;
    const ZERO: Self = 0;
    const ONE: Self = 1;
    fn leading_zeros(self) -> u32 {
        u64::leading_zeros(self)
    }
    fn trailing_zeros(self) -> u32 {
        u64::trailing_zeros(self)
    }
    fn rem(self, m: u64) -> u64 {
        self % m
    }
    fn checked_add_small(self, d: u64) -> Option<Self> {
        self.checked_add(d)
    }
    fn checked_sub_small(self, d: u64) -> Option<Self> {
        self.checked_sub(d)
    }
    fn from_bits(v: &BitVec) -> Self {
        v.limbs()[0]
    }
    fn to_bits(self, w: Width) -> BitVec {
        BitVec::from_canonical_u64(w, self)
    }
}

impl Word for u128 {
    const BITS: u32 = 128;
    const ZERO: Self = 0;
    const ONE: Self = 1;
    fn leading_zeros(self) -> u32 {
        u128::leading_zeros(self)
    }
    fn trailing_zeros(self) -> u32 {
        u128::trailing_zeros(self)
    }
    fn rem(self, m: u64) -> u64 {
        (self % u128::from(m)) as u64
    }
    fn checked_add_small(self, d: u64) -> Option<Self> {
        self.checked_add(u128::from(d))
    }
    fn checked_sub_small(self, d: u64) -> Option<Self> {
        self.checked_sub(u128::from(d))
    }
    fn from_bits(v: &BitVec) -> Self {
        let l = v.limbs();
        u128::from(l[0]) | l.get(1).map_or(0, |&h| u128::from(h) << 64)
    }
    fn to_bits(self, w: Width) -> BitVec {
        BitVec::wrapping_from_u128(w, self)
    }
}

/// Bits strictly above bit `i`, within `mask`.
fn above<T: Word>(i: u32, mask: T) -> T {
    if i + 1 >= T::BITS {
        T::ZERO
    } else {
        (!T::ZERO << (i + 1)) & mask
    }
}

/// Bits strictly below bit `i` (`i < BITS`).
fn below<T: Word>(i: u32) -> T {
    if i == 0 { T::ZERO } else { !(!T::ZERO << i) }
}

/// The smallest value `>= lo` with no bit of `kz` and every bit of `ko`, if there is one.
pub(super) fn next_member<T: Word>(lo: T, kz: T, ko: T, mask: T) -> Option<T> {
    let bad = (lo & kz) | (!lo & ko);
    if bad == T::ZERO {
        return Some(lo);
    }
    let i = T::BITS - 1 - bad.leading_zeros();
    let raise = |p: u32| (lo & above(p, mask)) | (T::ONE << p) | (ko & below(p));
    if lo & (T::ONE << i) == T::ZERO {
        return Some(raise(i));
    }
    let room = !lo & !(kz | ko) & above(i, mask);
    (room != T::ZERO).then(|| raise(room.trailing_zeros()))
}

/// The largest value `<= hi` with no bit of `kz` and every bit of `ko`, if there is one.
pub(super) fn prev_member<T: Word>(hi: T, kz: T, ko: T, mask: T) -> Option<T> {
    let bad = (hi & kz) | (!hi & ko);
    if bad == T::ZERO {
        return Some(hi);
    }
    let i = T::BITS - 1 - bad.leading_zeros();
    let lower = |p: u32| (hi & above(p, mask)) | (!kz & below(p));
    if hi & (T::ONE << i) != T::ZERO {
        return Some(lower(i));
    }
    let room = hi & !(kz | ko) & above(i, mask);
    (room != T::ZERO).then(|| lower(room.trailing_zeros()))
}

/// The common high bits of `lo` and `hi`, as known zero and one bits.
fn prefix<T: Word>(lo: T, hi: T, mask: T) -> (T, T) {
    let diff = lo ^ hi;
    let common = if diff == T::ZERO {
        mask
    } else {
        above(T::BITS - 1 - diff.leading_zeros(), mask)
    };
    (!lo & common, lo & common)
}

/// The members of `[lo, hi]` congruent to `r` modulo `m`, as bounds.
fn snap<T: Word>(lo: T, hi: T, r: u64, m: u64) -> Option<(T, T)> {
    if m <= 1 {
        return (lo <= hi).then_some((lo, hi));
    }
    let (r, wm) = (u128::from(r % m), u128::from(m));
    let up = ((r + wm - u128::from(lo.rem(m))) % wm) as u64;
    let down = ((u128::from(hi.rem(m)) + wm - r) % wm) as u64;
    let lo = lo.checked_add_small(up)?;
    let hi = hi.checked_sub_small(down)?;
    (lo <= hi).then_some((lo, hi))
}

/// An unsigned strided interval: bounds and stride.
pub(super) type U<T> = (T, T, u64);

fn strided<T: Word>(lo: T, hi: T, stride: u64) -> U<T> {
    (lo, hi, if lo == hi { 0 } else { stride })
}

/// `u` met with the plain interval `[a, b]` (`a <= b`).
fn meet_interval<T: Word>(u: U<T>, a: T, b: T) -> Option<U<T>> {
    let (ulo, uhi, s) = u;
    if s == 0 {
        return (a <= ulo && ulo <= b).then_some(u);
    }
    let (lo, hi) = snap(ulo.max(a), uhi.min(b), ulo.rem(s), s)?;
    Some(strided(lo, hi, s))
}

/// The members of `u` congruent to `r` modulo `m`.
fn meet_class<T: Word>(u: U<T>, r: u64, m: u64) -> Option<U<T>> {
    let (ulo, uhi, s) = u;
    if m <= 1 {
        return Some(u);
    }
    if s == 0 {
        return (ulo.rem(m) == r % m).then_some(u);
    }
    let own = ulo.rem(s);
    let (r, m) = crt(own, s, r, m)?.unwrap_or((own, s));
    let (lo, hi) = snap(ulo, uhi, r, m)?;
    Some(strided(lo, hi, m))
}

/// `Facts::reduce` for widths up to `T::BITS`.
pub(super) fn reduce<T: Word>(k: &KnownBits, u: &URange, s: &SRange) -> Option<Facts> {
    let word = |v: BitVec| T::from_bits(&v);
    reduce_raw(
        k.width(),
        word(k.known_zero()),
        word(k.known_one()),
        (word(u.lo()), word(u.hi()), u.stride()),
        word(s.lo()),
        word(s.hi()),
    )
}

/// [`reduce`] of components given as words of width `w`: known zero and one bits, a strided
/// unsigned interval as `URange` normalizes it, and signed bounds with `slo <=s shi`.
pub(super) fn reduce_raw<T: Word>(
    w: Width,
    mut kz: T,
    mut ko: T,
    mut u: U<T>,
    mut slo: T,
    mut shi: T,
) -> Option<Facts> {
    let bits = u32::from(w.bits());
    let mask = if bits == T::BITS {
        !T::ZERO
    } else {
        below::<T>(bits)
    };
    let sign = T::ONE << (bits - 1);
    let smax = below::<T>(bits - 1);
    let slt = |a: T, b: T| (a ^ sign) < (b ^ sign);
    // `[slo, shi]` met with the signed interval `[a, b]`, if `a <=s b` and the meet is not empty.
    let meet_signed = |slo: T, shi: T, a: T, b: T| {
        if slt(b, a) {
            return None;
        }
        let lo = if slt(slo, a) { a } else { slo };
        let hi = if slt(b, shi) { b } else { shi };
        (!slt(hi, lo)).then_some((lo, hi))
    };
    for _ in 0..3 {
        let before = (kz, ko, u, slo, shi);
        // Known bits move each unsigned end to the nearest value they allow, and their known
        // low bits are a residue class of the stride. (With no bit known, nothing moves.)
        if kz | ko != T::ZERO {
            let a = next_member(u.0, kz, ko, mask)?;
            let b = prev_member(u.1, kz, ko, mask)?;
            if a > b {
                return None;
            }
            u = meet_interval(u, a, b)?;
            let unknown = !(kz | ko) & mask;
            let t = if unknown == T::ZERO {
                bits
            } else {
                unknown.trailing_zeros()
            }
            .min(63);
            if t > 0 {
                let low = ko & below(t);
                u = meet_class(u, low.rem(1 << t), 1 << t)?;
            }
            // Likewise for the signed ends.
            let (kzs, kos) = ((kz & !sign) | (ko & sign), (ko & !sign) | (kz & sign));
            let a = next_member(slo ^ sign, kzs, kos, mask)? ^ sign;
            let b = prev_member(shi ^ sign, kzs, kos, mask)? ^ sign;
            (slo, shi) = meet_signed(slo, shi, a, b)?;
        }
        // The unsigned values fix their bounds' common high bits, and a stride with the factor
        // 2^a their low a bits.
        let (z, o) = prefix(u.0, u.1, mask);
        (kz, ko) = (kz | z, ko | o);
        if u.2 >= 2 && u.2.trailing_zeros() > 0 {
            let m = below::<T>(u.2.trailing_zeros());
            (kz, ko) = (kz | (!u.0 & m), ko | (u.0 & m));
        }
        if kz & ko != T::ZERO {
            return None;
        }
        // A signed range on one side of zero orders like an unsigned one.
        if slo & sign == T::ZERO || shi & sign != T::ZERO {
            let (z, o) = prefix(slo, shi, mask);
            (kz, ko) = (kz | z, ko | o);
            if kz & ko != T::ZERO || slo > shi {
                return None;
            }
            u = meet_interval(u, slo, shi)?;
        }
        // An unsigned range on one side of the sign boundary is also a signed range.
        if u.1 <= smax || smax < u.0 {
            (slo, shi) = meet_signed(slo, shi, u.0, u.1)?;
        }
        if before == (kz, ko, u, slo, shi) {
            break;
        }
    }
    Some(Facts {
        known: KnownBits::from_masks(kz.to_bits(w), ko.to_bits(w)),
        urange: URange::from_raw(u.0.to_bits(w), u.1.to_bits(w), u.2),
        srange: SRange::from_bounds(slo.to_bits(w), shi.to_bits(w)),
    })
}
