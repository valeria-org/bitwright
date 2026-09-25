//! The unsigned integers the software floating-point algorithms compute in: `u64` and `u128`
//! for formats whose intermediate results fit (precision at most [`SMALL_PRECISION`] and
//! [`NARROW_PRECISION`]), and [`Big`], a fixed-capacity integer, for the others ([`Mid`] up to
//! [`MID_PRECISION`], [`Wide`] beyond). Both hold a format's encodings as well as its
//! significands and their products.

use core::cmp::Ordering;

/// The largest precision whose algorithms stay within 128 bits: `fma` aligns a `2p`-bit product
/// and an addend in `2p + 6` bits.
pub(crate) const NARROW_PRECISION: u32 = 61;

/// Unsigned integer arithmetic for the software algorithms. Results never exceed the type's
/// capacity for the formats it is used with (the callers size every intermediate).
pub(crate) trait Frame: Copy + Ord + core::fmt::Debug {
    fn from_u64(v: u64) -> Self;
    /// From little-endian limbs (at most the capacity).
    fn from_limbs(limbs: &[u64]) -> Self;
    /// The low `out.len()` limbs, little-endian.
    fn write_limbs(&self, out: &mut [u64]);
    /// The number of significant bits (0 for zero).
    fn bits(&self) -> u32;
    fn is_zero(&self) -> bool;
    fn bit(&self, i: u32) -> bool;
    /// `self · 2^n` (the result must fit).
    fn shl(self, n: u32) -> Self;
    /// `⌊self / 2^n⌋` (any `n`).
    fn shr(self, n: u32) -> Self;
    /// `self mod 2^n` (any `n`).
    fn low(self, n: u32) -> Self;
    fn add(self, o: Self) -> Self;
    /// `self − o`, with `o ≤ self`.
    fn sub(self, o: Self) -> Self;
    /// The full product (it must fit).
    fn mul(self, o: Self) -> Self;
    /// Quotient and remainder, `o ≠ 0`.
    fn divrem(self, o: Self) -> (Self, Self);
    /// `⌊√self⌋`.
    fn isqrt(self) -> Self;

    fn zero() -> Self {
        Self::from_u64(0)
    }
    fn one() -> Self {
        Self::from_u64(1)
    }
    /// `2^n`.
    fn pow2(n: u32) -> Self {
        Self::one().shl(n)
    }
    /// `⌊self / 2^n⌋`, with the bits shifted out ORed into bit 0 (a sticky bit).
    fn shr_jam(self, n: u32) -> Self {
        let hi = self.shr(n);
        if self.low(n).is_zero() {
            hi
        } else {
            hi.or_one()
        }
    }
    /// `self | 1`.
    fn or_one(self) -> Self {
        if self.bit(0) {
            self
        } else {
            self.add(Self::one())
        }
    }
    /// `(self · o) mod m`.
    fn mul_mod(self, o: Self, m: Self) -> Self {
        self.mul(o).divrem(m).1
    }
}

/// The largest precision whose algorithms stay within 64 bits (`2p + 6 ≤ 64`).
pub(crate) const SMALL_PRECISION: u32 = 29;

impl Frame for u64 {
    fn from_u64(v: u64) -> Self {
        v
    }
    fn from_limbs(limbs: &[u64]) -> Self {
        debug_assert!(limbs.iter().skip(1).all(|&l| l == 0));
        limbs.first().copied().unwrap_or(0)
    }
    fn write_limbs(&self, out: &mut [u64]) {
        for (i, l) in out.iter_mut().enumerate() {
            *l = if i == 0 { *self } else { 0 };
        }
    }
    fn bits(&self) -> u32 {
        64 - self.leading_zeros()
    }
    fn is_zero(&self) -> bool {
        *self == 0
    }
    fn bit(&self, i: u32) -> bool {
        i < 64 && (*self >> i) & 1 == 1
    }
    fn shl(self, n: u32) -> Self {
        debug_assert!(n < 64 && self.leading_zeros() >= n, "u64 frame overflow");
        self << n
    }
    fn shr(self, n: u32) -> Self {
        if n >= 64 { 0 } else { self >> n }
    }
    fn low(self, n: u32) -> Self {
        if n >= 64 {
            self
        } else {
            self & ((1u64 << n) - 1)
        }
    }
    fn add(self, o: Self) -> Self {
        debug_assert!(self.checked_add(o).is_some(), "u64 frame overflow");
        self.wrapping_add(o)
    }
    fn sub(self, o: Self) -> Self {
        debug_assert!(o <= self);
        self - o
    }
    fn mul(self, o: Self) -> Self {
        debug_assert!(self.checked_mul(o).is_some(), "u64 frame overflow");
        self.wrapping_mul(o)
    }
    fn divrem(self, o: Self) -> (Self, Self) {
        (self / o, self % o)
    }
    fn isqrt(self) -> Self {
        u64::isqrt(self)
    }
    fn mul_mod(self, o: Self, m: Self) -> Self {
        ((u128::from(self) * u128::from(o)) % u128::from(m)) as u64
    }
}

impl Frame for u128 {
    fn from_u64(v: u64) -> Self {
        u128::from(v)
    }
    fn from_limbs(limbs: &[u64]) -> Self {
        debug_assert!(limbs.iter().skip(2).all(|&l| l == 0));
        let lo = limbs.first().copied().unwrap_or(0);
        let hi = limbs.get(1).copied().unwrap_or(0);
        u128::from(lo) | (u128::from(hi) << 64)
    }
    fn write_limbs(&self, out: &mut [u64]) {
        for (i, l) in out.iter_mut().enumerate() {
            *l = match i {
                0 => *self as u64,
                1 => (*self >> 64) as u64,
                _ => 0,
            };
        }
    }
    fn bits(&self) -> u32 {
        128 - self.leading_zeros()
    }
    fn is_zero(&self) -> bool {
        *self == 0
    }
    fn bit(&self, i: u32) -> bool {
        i < 128 && (*self >> i) & 1 == 1
    }
    fn shl(self, n: u32) -> Self {
        debug_assert!(n < 128 && self.leading_zeros() >= n, "u128 frame overflow");
        self << n
    }
    fn shr(self, n: u32) -> Self {
        if n >= 128 { 0 } else { self >> n }
    }
    fn low(self, n: u32) -> Self {
        if n >= 128 {
            self
        } else {
            self & ((1u128 << n) - 1)
        }
    }
    fn add(self, o: Self) -> Self {
        debug_assert!(self.checked_add(o).is_some(), "u128 frame overflow");
        self.wrapping_add(o)
    }
    fn sub(self, o: Self) -> Self {
        debug_assert!(o <= self);
        self - o
    }
    fn mul(self, o: Self) -> Self {
        debug_assert!(self.checked_mul(o).is_some(), "u128 frame overflow");
        self.wrapping_mul(o)
    }
    fn divrem(self, o: Self) -> (Self, Self) {
        (self / o, self % o)
    }
    fn isqrt(self) -> Self {
        u128::isqrt(self)
    }
    fn mul_mod(self, o: Self, m: Self) -> Self {
        // The operands are below `m`, which may use most of the 128 bits: multiply by parts.
        match self.checked_mul(o) {
            Some(p) => p % m,
            None => {
                let (mut acc, mut a, mut b) = (0u128, self % m, o);
                while b != 0 {
                    if b & 1 == 1 {
                        acc = add_mod(acc, a, m);
                    }
                    a = add_mod(a, a, m);
                    b >>= 1;
                }
                acc
            }
        }
    }
}

/// `(a + b) mod m` for `a, b < m`, without overflowing.
fn add_mod(a: u128, b: u128, m: u128) -> u128 {
    if a >= m - b { a - (m - b) } else { a + b }
}

/// The largest precision [`Mid`] serves: `2p + 6 ≤ 320` (binary128, x87).
pub(crate) const MID_PRECISION: u32 = 157;

/// 320 bits: the intermediates of formats up to [`MID_PRECISION`].
pub(crate) type Mid = Big<5>;

/// 1,280 bits: every intermediate of a 512-bit format (`2p + 6 ≤ 1,026` bits), and the
/// 513-bit magnitudes of integer conversions.
pub(crate) type Wide = Big<20>;

/// A fixed-capacity unsigned integer of `N` limbs for the wide formats' algorithms.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Big<const N: usize> {
    limbs: [u64; N],
}

impl<const N: usize> core::fmt::Debug for Big<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "0x")?;
        let top = self.used().max(1);
        for (i, l) in self.limbs[..top].iter().rev().enumerate() {
            if i == 0 {
                write!(f, "{l:x}")?;
            } else {
                write!(f, "{l:016x}")?;
            }
        }
        Ok(())
    }
}

impl<const N: usize> Big<N> {
    const ZERO: Self = Big { limbs: [0; N] };

    /// The number of limbs up to the highest nonzero one.
    fn used(&self) -> usize {
        self.limbs
            .iter()
            .rposition(|&l| l != 0)
            .map_or(0, |i| i + 1)
    }

    /// `self + o·2^(64·shift)` in place (wrapping; used to undo an overdrawn step).
    fn add_shifted(&mut self, o: &Self, shift: usize) {
        let mut carry = 0u128;
        for i in 0..N - shift {
            let s = u128::from(self.limbs[i + shift]) + u128::from(o.limbs[i]) + carry;
            self.limbs[i + shift] = s as u64;
            carry = s >> 64;
        }
    }
}

impl<const N: usize> PartialOrd for Big<N> {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl<const N: usize> Ord for Big<N> {
    fn cmp(&self, o: &Self) -> Ordering {
        self.limbs.iter().rev().cmp(o.limbs.iter().rev())
    }
}

impl<const N: usize> Frame for Big<N> {
    fn from_u64(v: u64) -> Self {
        let mut b = Self::ZERO;
        b.limbs[0] = v;
        b
    }
    fn from_limbs(limbs: &[u64]) -> Self {
        let mut b = Self::ZERO;
        for (d, s) in b.limbs.iter_mut().zip(limbs) {
            *d = *s;
        }
        debug_assert!(limbs.iter().skip(N).all(|&l| l == 0));
        b
    }
    fn write_limbs(&self, out: &mut [u64]) {
        for (i, l) in out.iter_mut().enumerate() {
            *l = self.limbs.get(i).copied().unwrap_or(0);
        }
    }
    fn bits(&self) -> u32 {
        match self.used() {
            0 => 0,
            n => (n as u32 - 1) * 64 + (64 - self.limbs[n - 1].leading_zeros()),
        }
    }
    fn is_zero(&self) -> bool {
        self.limbs.iter().all(|&l| l == 0)
    }
    fn bit(&self, i: u32) -> bool {
        let (w, b) = ((i / 64) as usize, i % 64);
        w < N && (self.limbs[w] >> b) & 1 == 1
    }
    fn shl(self, n: u32) -> Self {
        debug_assert!(
            self.is_zero() || self.bits() + n <= (N * 64) as u32,
            "Big frame overflow"
        );
        let (w, b) = ((n / 64) as usize, n % 64);
        let mut r = Self::ZERO;
        for i in (w..N).rev() {
            let src = i - w;
            let mut v = self.limbs[src] << b;
            if b != 0 && src > 0 {
                v |= self.limbs[src - 1] >> (64 - b);
            }
            r.limbs[i] = v;
        }
        r
    }
    fn shr(self, n: u32) -> Self {
        let (w, b) = ((n / 64) as usize, n % 64);
        let mut r = Self::ZERO;
        if w >= N {
            return r;
        }
        for i in 0..N - w {
            let src = i + w;
            let mut v = self.limbs[src] >> b;
            if b != 0 && src + 1 < N {
                v |= self.limbs[src + 1] << (64 - b);
            }
            r.limbs[i] = v;
        }
        r
    }
    fn low(self, n: u32) -> Self {
        let (w, b) = ((n / 64) as usize, n % 64);
        let mut r = self;
        if w >= N {
            return r;
        }
        r.limbs[w] &= if b == 0 { 0 } else { (1u64 << b) - 1 };
        for l in r.limbs[w + 1..].iter_mut() {
            *l = 0;
        }
        r
    }
    fn add(self, o: Self) -> Self {
        let mut r = self;
        r.add_shifted(&o, 0);
        r
    }
    fn sub(self, o: Self) -> Self {
        debug_assert!(o <= self);
        let mut r = Self::ZERO;
        let mut borrow = 0u64;
        for i in 0..N {
            let (d1, b1) = self.limbs[i].overflowing_sub(o.limbs[i]);
            let (d2, b2) = d1.overflowing_sub(borrow);
            r.limbs[i] = d2;
            borrow = u64::from(b1 || b2);
        }
        r
    }
    fn mul(self, o: Self) -> Self {
        let (na, nb) = (self.used(), o.used());
        debug_assert!(na + nb <= N + 1, "Big frame overflow");
        let mut r = Self::ZERO;
        for i in 0..na {
            let mut carry = 0u128;
            for j in 0..nb {
                if i + j >= N {
                    debug_assert!(self.limbs[i] == 0 || o.limbs[j] == 0 || carry == 0);
                    break;
                }
                let t = u128::from(self.limbs[i]) * u128::from(o.limbs[j])
                    + u128::from(r.limbs[i + j])
                    + carry;
                r.limbs[i + j] = t as u64;
                carry = t >> 64;
            }
            if i + nb < N {
                r.limbs[i + nb] = carry as u64;
            } else {
                debug_assert!(carry == 0, "Big frame overflow");
            }
        }
        r
    }
    fn divrem(self, o: Self) -> (Self, Self) {
        assert!(!o.is_zero(), "division by zero");
        if self < o {
            return (Self::ZERO, self);
        }
        // Schoolbook long division in base 2^64 (Knuth's algorithm D): normalize the divisor
        // so its top limb has its top bit set, estimate each quotient limb from the top two
        // limbs, and correct the (at most two) overestimates.
        let n = o.used();
        if n == 1 {
            let d = u128::from(o.limbs[0]);
            let mut q = Self::ZERO;
            let mut rem = 0u128;
            for i in (0..self.used()).rev() {
                let cur = (rem << 64) | u128::from(self.limbs[i]);
                q.limbs[i] = (cur / d) as u64;
                rem = cur % d;
            }
            return (q, Self::from_u64(rem as u64));
        }
        let s = o.limbs[n - 1].leading_zeros();
        let v = o.shl(s);
        // The shifted dividend can need one limb more than the value itself.
        let mut buf = [0u64; 33];
        debug_assert!(N < buf.len());
        let u = &mut buf[..=N];
        {
            let top = self.limbs[N - 1];
            let sh = self.shl_wrapping(s);
            u[..N].copy_from_slice(&sh.limbs);
            u[N] = if s == 0 { 0 } else { top >> (64 - s) };
        }
        let m = self.used() + 1 - n;
        let mut q = Self::ZERO;
        let vtop = u128::from(v.limbs[n - 1]);
        let vnext = u128::from(v.limbs[n - 2]);
        for j in (0..m).rev() {
            let num = (u128::from(u[j + n]) << 64) | u128::from(u[j + n - 1]);
            let mut qhat = num / vtop;
            let mut rhat = num % vtop;
            while qhat > u128::from(u64::MAX)
                || qhat * vnext > ((rhat << 64) | u128::from(u[j + n - 2]))
            {
                qhat -= 1;
                rhat += vtop;
                if rhat > u128::from(u64::MAX) {
                    break;
                }
            }
            // u[j..=j+n] -= qhat · v
            let mut borrow: i128 = 0;
            let mut carry: u128 = 0;
            for i in 0..n {
                let p = qhat * u128::from(v.limbs[i]) + carry;
                carry = p >> 64;
                let t = i128::from(u[i + j]) - i128::from(p as u64) + borrow;
                u[i + j] = t as u64;
                borrow = t >> 64;
            }
            let t = i128::from(u[j + n]) - carry as i128 + borrow;
            u[j + n] = t as u64;
            if t < 0 {
                // Overdrawn by one divisor: add it back.
                qhat -= 1;
                let mut c = 0u128;
                for i in 0..n {
                    let s2 = u128::from(u[i + j]) + u128::from(v.limbs[i]) + c;
                    u[i + j] = s2 as u64;
                    c = s2 >> 64;
                }
                u[j + n] = u[j + n].wrapping_add(c as u64);
            }
            q.limbs[j] = qhat as u64;
        }
        let mut r = Self::ZERO;
        r.limbs[..n].copy_from_slice(&u[..n]);
        (q, r.shr(s))
    }
    fn isqrt(self) -> Self {
        let bits = self.bits();
        let top = |x: Self| {
            let mut l = [0u64; 2];
            x.write_limbs(&mut l);
            u128::from(l[0]) | (u128::from(l[1]) << 64)
        };
        if bits <= 128 {
            let r = top(self).isqrt();
            return Self::from_limbs(&[r as u64, (r >> 64) as u64]);
        }
        // Newton's iteration from above: x ← (x + n/x) / 2 decreases to ⌊√n⌋. It starts at
        // (⌊√(n / 4^k)⌋ + 1)·2^k > √n, from the top bits of n: good to about 64 bits, so a few
        // steps finish.
        let k = (bits - 127).div_ceil(2);
        let r = top(self.shr(2 * k)).isqrt() + 1;
        let mut x = Self::from_limbs(&[r as u64, (r >> 64) as u64]).shl(k);
        loop {
            let y = x.add(self.divrem(x).0).shr(1);
            if y >= x {
                return x;
            }
            x = y;
        }
    }
}

impl<const N: usize> Big<N> {
    /// `self · 2^n` keeping only the low `N` limbs (the caller saves the top bits).
    fn shl_wrapping(self, n: u32) -> Self {
        let (w, b) = ((n / 64) as usize, n % 64);
        let mut r = Self::ZERO;
        for i in (w..N).rev() {
            let src = i - w;
            let mut v = self.limbs[src] << b;
            if b != 0 && src > 0 {
                v |= self.limbs[src - 1] >> (64 - b);
            }
            r.limbs[i] = v;
        }
        r
    }
}

#[cfg(test)]
pub(crate) mod testing {
    //! Checks both frames against each other on random operands.
    use super::*;

    pub(crate) fn big(v: u128) -> Wide {
        Wide::from_limbs(&[v as u64, (v >> 64) as u64])
    }

    pub(crate) fn to_u128(b: Wide) -> u128 {
        let mut l = [0u64; 2];
        b.write_limbs(&mut l);
        assert!(b.bits() <= 128);
        u128::from(l[0]) | (u128::from(l[1]) << 64)
    }
}
