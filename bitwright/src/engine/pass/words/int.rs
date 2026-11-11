//! The integers the limb-arithmetic pass computes in: 256 bits, two's complement.
//!
//! A word of 128 bits, a coefficient and a shift on top of it do not fit 128 bits. The pass
//! bounds its coefficients itself (`form::BIG`) and uses the checked operations where a
//! result may leave that bound; the plain operators wrap, as the machine integers they
//! replace do in a release build.

use core::cmp::Ordering;
use core::ops::{Add, AddAssign, BitAnd, Mul, Neg, Rem, Shl, Shr, Sub, SubAssign};

/// A 256-bit signed integer: four limbs, low first.
#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub(crate) struct Int([u64; 4]);

// (Two words, not the limbs as bytes: forms are hashed at every lookup of one.)
impl core::hash::Hash for Int {
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0[0] ^ self.0[2].rotate_left(17));
        state.write_u64(self.0[1] ^ self.0[3].rotate_left(17));
    }
}

// (Some of the operations are there for the tests against the machine integers; the limbs
// are walked by index, low to high, as the carries go.)
#[allow(dead_code, clippy::needless_range_loop)]
impl Int {
    pub(crate) const ZERO: Int = Int([0; 4]);
    pub(crate) const ONE: Int = Int([1, 0, 0, 0]);
    pub(crate) const MAX: Int = Int([u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]);
    pub(crate) const MIN: Int = Int([0, 0, 0, 1 << 63]);

    /// Two to the `n` (below 255).
    pub(crate) const fn pow2(n: u32) -> Int {
        let mut limbs = [0u64; 4];
        limbs[(n / 64) as usize] = 1 << (n % 64);
        Int(limbs)
    }

    pub(crate) const fn is_negative(self) -> bool {
        self.0[3] >> 63 == 1
    }

    pub(crate) fn is_zero(self) -> bool {
        self == Int::ZERO
    }

    /// The low 64 bits.
    pub(crate) const fn low_u64(self) -> u64 {
        self.0[0]
    }

    /// The low 128 bits.
    pub(crate) const fn low_u128(self) -> u128 {
        (self.0[1] as u128) << 64 | self.0[0] as u128
    }

    /// The value, when it is one of 128 bits.
    #[inline]
    pub(crate) fn to_i128(self) -> Option<i128> {
        // The high limbs are the sign of the low ones.
        let fill = ((self.0[1] as i64) >> 63) as u64;
        (self.0[2] == fill && self.0[3] == fill).then(|| self.low_u128() as i128)
    }

    /// The value, when it is one of 64 bits.
    #[inline]
    fn to_i64(self) -> Option<i64> {
        let fill = ((self.0[0] as i64) >> 63) as u64;
        (self.0[1] == fill && self.0[2] == fill && self.0[3] == fill).then_some(self.0[0] as i64)
    }

    /// The product, when both values are of 64 bits (it is of 128 then, whatever they are).
    #[inline]
    fn mul_small(self, o: Int) -> Option<Int> {
        Some(Int::from(
            i128::from(self.to_i64()?) * i128::from(o.to_i64()?),
        ))
    }

    /// Both values, when each is one of 128 bits: where the machine's own arithmetic does
    /// (nearly all the pass computes with is this small).
    #[inline]
    fn small(self, o: Int) -> Option<(i128, i128)> {
        Some((self.to_i128()?, o.to_i128()?))
    }

    /// The value, when it is an unsigned one of 128 bits.
    pub(crate) fn to_u128(self) -> Option<u128> {
        (self.0[2] == 0 && self.0[3] == 0).then(|| self.low_u128())
    }

    fn add_carry(self, o: Int) -> (Int, bool) {
        let mut out = [0u64; 4];
        let mut carry = false;
        for k in 0..4 {
            let (s, c1) = self.0[k].overflowing_add(o.0[k]);
            let (s, c2) = s.overflowing_add(u64::from(carry));
            out[k] = s;
            carry = c1 || c2;
        }
        (Int(out), carry)
    }

    #[inline]
    pub(crate) fn wrapping_add(self, o: Int) -> Int {
        if let Some((a, b)) = self.small(o)
            && let Some(s) = a.checked_add(b)
        {
            return Int::from(s);
        }
        self.add_carry(o).0
    }

    pub(crate) fn wrapping_neg(self) -> Int {
        (!self).wrapping_add(Int::ONE)
    }

    #[inline]
    pub(crate) fn wrapping_sub(self, o: Int) -> Int {
        if let Some((a, b)) = self.small(o)
            && let Some(s) = a.checked_sub(b)
        {
            return Int::from(s);
        }
        self.wrapping_add(o.wrapping_neg())
    }

    #[inline]
    pub(crate) fn checked_add(self, o: Int) -> Option<Int> {
        if let Some((a, b)) = self.small(o)
            && let Some(s) = a.checked_add(b)
        {
            return Some(Int::from(s));
        }
        let s = self.wrapping_add(o);
        // Wrong exactly when the operands agree in sign and the sum does not.
        (self.is_negative() != o.is_negative() || s.is_negative() == self.is_negative())
            .then_some(s)
    }

    #[inline]
    pub(crate) fn checked_sub(self, o: Int) -> Option<Int> {
        if let Some((a, b)) = self.small(o)
            && let Some(s) = a.checked_sub(b)
        {
            return Some(Int::from(s));
        }
        let s = self.wrapping_sub(o);
        (self.is_negative() == o.is_negative() || s.is_negative() == self.is_negative())
            .then_some(s)
    }

    pub(crate) fn checked_neg(self) -> Option<Int> {
        (self != Int::MIN).then(|| self.wrapping_neg())
    }

    pub(crate) fn saturating_add(self, o: Int) -> Int {
        self.checked_add(o)
            .unwrap_or(if o.is_negative() { Int::MIN } else { Int::MAX })
    }

    pub(crate) fn saturating_sub(self, o: Int) -> Int {
        self.checked_sub(o)
            .unwrap_or(if o.is_negative() { Int::MAX } else { Int::MIN })
    }

    /// The magnitude, as limbs (of `MIN` too: it fits unsigned).
    fn magnitude(self) -> [u64; 4] {
        if self.is_negative() {
            self.wrapping_neg().0
        } else {
            self.0
        }
    }

    /// The product of two magnitudes: the low 256 bits, and whether any bit above is set.
    fn mul_limbs(a: [u64; 4], b: [u64; 4]) -> ([u64; 4], bool) {
        let mut out = [0u64; 8];
        for i in 0..4 {
            let mut carry = 0u128;
            for j in 0..4 {
                let t = u128::from(a[i]) * u128::from(b[j]) + u128::from(out[i + j]) + carry;
                out[i + j] = t as u64;
                carry = t >> 64;
            }
            out[i + 4] = carry as u64;
        }
        (
            [out[0], out[1], out[2], out[3]],
            out[4..].iter().any(|&l| l != 0),
        )
    }

    #[inline]
    pub(crate) fn wrapping_mul(self, o: Int) -> Int {
        if let Some(p) = self.mul_small(o) {
            return p;
        }
        if let Some((a, b)) = self.small(o)
            && let Some(p) = a.checked_mul(b)
        {
            return Int::from(p);
        }
        // (Two's complement: the low half of the product of the limbs as they are.)
        Int(Int::mul_limbs(self.0, o.0).0)
    }

    #[inline]
    pub(crate) fn checked_mul(self, o: Int) -> Option<Int> {
        if let Some(p) = self.mul_small(o) {
            return Some(p);
        }
        if let Some((a, b)) = self.small(o)
            && let Some(p) = a.checked_mul(b)
        {
            return Some(Int::from(p));
        }
        self.checked_mul_limbs(o)
    }

    #[inline(never)]
    fn checked_mul_limbs(self, o: Int) -> Option<Int> {
        let negative = self.is_negative() != o.is_negative();
        let (m, over) = Int::mul_limbs(self.magnitude(), o.magnitude());
        if over {
            return None;
        }
        let m = Int(m);
        if negative {
            // A magnitude up to 2^255 has a negative.
            (!m.is_negative() || m == Int::MIN).then(|| m.wrapping_neg())
        } else {
            (!m.is_negative()).then_some(m)
        }
    }

    pub(crate) fn abs(self) -> Int {
        if self.is_negative() {
            self.wrapping_neg()
        } else {
            self
        }
    }

    pub(crate) fn leading_zeros(self) -> u32 {
        for k in (0..4).rev() {
            if self.0[k] != 0 {
                return (3 - k as u32) * 64 + self.0[k].leading_zeros();
            }
        }
        256
    }

    pub(crate) fn trailing_zeros(self) -> u32 {
        for k in 0..4 {
            if self.0[k] != 0 {
                return k as u32 * 64 + self.0[k].trailing_zeros();
            }
        }
        256
    }

    /// Quotient and remainder of magnitudes, a bit at a time.
    fn div_limbs(a: [u64; 4], b: [u64; 4]) -> ([u64; 4], [u64; 4]) {
        let (mut q, mut r) = (Int::ZERO, Int::ZERO);
        let b = Int(b);
        for bit in (0..256u32).rev() {
            r = r.shl_bits(1);
            r.0[0] |= a[(bit / 64) as usize] >> (bit % 64) & 1;
            // (Unsigned: `r` is below `2b`, and both are below 2^255 or compared as limbs.)
            if r.cmp_unsigned(b) != Ordering::Less {
                r = r.wrapping_sub(b);
                q.0[(bit / 64) as usize] |= 1 << (bit % 64);
            }
        }
        (q.0, r.0)
    }

    fn cmp_unsigned(self, o: Int) -> Ordering {
        for k in (0..4).rev() {
            match self.0[k].cmp(&o.0[k]) {
                Ordering::Equal => {}
                other => return other,
            }
        }
        Ordering::Equal
    }

    /// The quotient towards zero and the remainder with the dividend's sign, as the machine
    /// integers have them. `None` for a divisor of zero.
    #[inline]
    pub(crate) fn div_rem(self, o: Int) -> Option<(Int, Int)> {
        if o.is_zero() {
            return None;
        }
        if let Some((a, b)) = self.small(o)
            && let (Some(q), Some(r)) = (a.checked_div(b), a.checked_rem(b))
        {
            return Some((Int::from(q), Int::from(r)));
        }
        Some(self.div_rem_limbs(o))
    }

    #[inline(never)]
    fn div_rem_limbs(self, o: Int) -> (Int, Int) {
        let (q, r) = Int::div_limbs(self.magnitude(), o.magnitude());
        let (q, r) = (Int(q), Int(r));
        let q = if self.is_negative() != o.is_negative() {
            q.wrapping_neg()
        } else {
            q
        };
        let r = if self.is_negative() {
            r.wrapping_neg()
        } else {
            r
        };
        (q, r)
    }

    /// The remainder that is not negative.
    pub(crate) fn rem_euclid(self, o: Int) -> Int {
        match self.div_rem(o) {
            Some((_, r)) if r.is_negative() => r.wrapping_add(o.abs()),
            Some((_, r)) => r,
            None => Int::ZERO,
        }
    }

    #[inline]
    fn shl_bits(self, n: u32) -> Int {
        if n < 64
            && let Some(v) = self.to_i64()
        {
            return Int::from(i128::from(v) << n);
        }
        self.shl_limbs(n)
    }

    fn shl_limbs(self, n: u32) -> Int {
        if n >= 256 {
            return Int::ZERO;
        }
        let (limbs, bits) = ((n / 64) as usize, n % 64);
        let mut out = [0u64; 4];
        for k in (limbs..4).rev() {
            out[k] = self.0[k - limbs] << bits;
            if bits > 0 && k > limbs {
                out[k] |= self.0[k - limbs - 1] >> (64 - bits);
            }
        }
        Int(out)
    }

    #[inline]
    fn shr_bits(self, n: u32) -> Int {
        if let Some(v) = self.to_i128() {
            return Int::from(v >> n.min(127));
        }
        self.shr_limbs(n)
    }

    fn shr_limbs(self, n: u32) -> Int {
        let fill = if self.is_negative() { u64::MAX } else { 0 };
        if n >= 256 {
            return Int([fill; 4]);
        }
        let (limbs, bits) = ((n / 64) as usize, n % 64);
        let mut out = [fill; 4];
        for k in 0..4 - limbs {
            let above = if k + limbs + 1 < 4 {
                self.0[k + limbs + 1]
            } else {
                fill
            };
            out[k] = self.0[k + limbs] >> bits;
            if bits > 0 {
                out[k] |= above << (64 - bits);
            }
        }
        Int(out)
    }
}

impl From<i128> for Int {
    fn from(v: i128) -> Int {
        let fill = if v < 0 { u64::MAX } else { 0 };
        Int([v as u64, (v >> 64) as u64, fill, fill])
    }
}

impl From<u128> for Int {
    fn from(v: u128) -> Int {
        Int([v as u64, (v >> 64) as u64, 0, 0])
    }
}

impl From<u64> for Int {
    fn from(v: u64) -> Int {
        Int([v, 0, 0, 0])
    }
}

impl From<u32> for Int {
    fn from(v: u32) -> Int {
        Int([u64::from(v), 0, 0, 0])
    }
}

impl From<i32> for Int {
    fn from(v: i32) -> Int {
        Int::from(i128::from(v))
    }
}

impl From<i64> for Int {
    fn from(v: i64) -> Int {
        Int::from(i128::from(v))
    }
}

impl Ord for Int {
    #[inline]
    fn cmp(&self, o: &Int) -> Ordering {
        if let Some((a, b)) = self.small(*o) {
            return a.cmp(&b);
        }
        match (self.is_negative(), o.is_negative()) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            _ => self.cmp_unsigned(*o),
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, o: &Int) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

impl Neg for Int {
    type Output = Int;
    fn neg(self) -> Int {
        self.wrapping_neg()
    }
}

impl Add for Int {
    type Output = Int;
    fn add(self, o: Int) -> Int {
        self.wrapping_add(o)
    }
}

impl Sub for Int {
    type Output = Int;
    fn sub(self, o: Int) -> Int {
        self.wrapping_sub(o)
    }
}

impl AddAssign for Int {
    fn add_assign(&mut self, o: Int) {
        *self = *self + o;
    }
}

impl SubAssign for Int {
    fn sub_assign(&mut self, o: Int) {
        *self = *self - o;
    }
}

impl Mul for Int {
    type Output = Int;
    fn mul(self, o: Int) -> Int {
        self.wrapping_mul(o)
    }
}

impl Rem for Int {
    type Output = Int;
    fn rem(self, o: Int) -> Int {
        self.div_rem(o).map_or(Int::ZERO, |(_, r)| r)
    }
}

impl BitAnd for Int {
    type Output = Int;
    fn bitand(self, o: Int) -> Int {
        Int([
            self.0[0] & o.0[0],
            self.0[1] & o.0[1],
            self.0[2] & o.0[2],
            self.0[3] & o.0[3],
        ])
    }
}

impl Shl<u32> for Int {
    type Output = Int;
    fn shl(self, n: u32) -> Int {
        self.shl_bits(n)
    }
}

impl Shr<u32> for Int {
    type Output = Int;
    fn shr(self, n: u32) -> Int {
        self.shr_bits(n)
    }
}

impl core::ops::Div for Int {
    type Output = Int;
    fn div(self, o: Int) -> Int {
        self.div_rem(o).map_or(Int::ZERO, |(q, _)| q)
    }
}

impl core::ops::Div<i32> for Int {
    type Output = Int;
    fn div(self, o: i32) -> Int {
        self / Int::from(o)
    }
}

impl Rem<i32> for Int {
    type Output = Int;
    fn rem(self, o: i32) -> Int {
        self % Int::from(o)
    }
}

impl core::ops::BitXor for Int {
    type Output = Int;
    fn bitxor(self, o: Int) -> Int {
        Int([
            self.0[0] ^ o.0[0],
            self.0[1] ^ o.0[1],
            self.0[2] ^ o.0[2],
            self.0[3] ^ o.0[3],
        ])
    }
}

impl core::ops::BitXorAssign for Int {
    fn bitxor_assign(&mut self, o: Int) {
        *self = *self ^ o;
    }
}

impl core::ops::Not for Int {
    type Output = Int;
    fn not(self) -> Int {
        Int([!self.0[0], !self.0[1], !self.0[2], !self.0[3]])
    }
}

impl core::ops::ShrAssign<u32> for Int {
    fn shr_assign(&mut self, n: u32) {
        *self = *self >> n;
    }
}

impl core::ops::ShlAssign<u32> for Int {
    fn shl_assign(&mut self, n: u32) {
        *self = *self << n;
    }
}

impl core::ops::BitOr for Int {
    type Output = Int;
    fn bitor(self, o: Int) -> Int {
        Int([
            self.0[0] | o.0[0],
            self.0[1] | o.0[1],
            self.0[2] | o.0[2],
            self.0[3] | o.0[3],
        ])
    }
}

impl From<usize> for Int {
    fn from(v: usize) -> Int {
        Int([v as u64, 0, 0, 0])
    }
}

// With the small literals the pass writes (`c == 0`, `k - 1`, `-1`).
impl PartialEq<i32> for Int {
    fn eq(&self, o: &i32) -> bool {
        *self == Int::from(*o)
    }
}

impl PartialOrd<i32> for Int {
    fn partial_cmp(&self, o: &i32) -> Option<Ordering> {
        Some(self.cmp(&Int::from(*o)))
    }
}

impl Add<i32> for Int {
    type Output = Int;
    fn add(self, o: i32) -> Int {
        self + Int::from(o)
    }
}

impl Sub<i32> for Int {
    type Output = Int;
    fn sub(self, o: i32) -> Int {
        self - Int::from(o)
    }
}

impl Mul<i32> for Int {
    type Output = Int;
    fn mul(self, o: i32) -> Int {
        self * Int::from(o)
    }
}

impl core::fmt::Debug for Int {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.to_i128() {
            Some(v) => write!(f, "{v}"),
            None => write!(
                f,
                "{:#x}:{:016x}:{:016x}:{:016x}",
                self.0[3], self.0[2], self.0[1], self.0[0]
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::Rng;

    /// Every operation agrees with the machine's 128-bit integers where both hold the result.
    #[test]
    fn agrees_with_the_machine_integers() {
        let mut rng = Rng(0x1ab5_0256);
        let pick = |rng: &mut Rng| -> i128 {
            let bits = rng.below(62) as u32;
            let v = (rng.below(u64::MAX) as i128) << rng.below(40) >> (63 - bits.min(62));
            match rng.below(6) {
                0 => 0,
                1 => 1,
                2 => -1,
                3 => -v,
                _ => v,
            }
        };
        for _ in 0..20_000 {
            let (a, b) = (pick(&mut rng), pick(&mut rng));
            let (x, y) = (Int::from(a), Int::from(b));
            assert_eq!((x + y).to_i128(), a.checked_add(b), "{a} + {b}");
            assert_eq!((x - y).to_i128(), a.checked_sub(b), "{a} - {b}");
            assert_eq!((x * y).to_i128(), a.checked_mul(b), "{a} * {b}");
            assert_eq!(x.checked_mul(y).and_then(Int::to_i128), a.checked_mul(b));
            // (The limb routines too, which small values no longer reach.)
            assert_eq!(x.checked_mul_limbs(y), x.checked_mul(y), "{a} * {b}");
            assert_eq!(Int(Int::mul_limbs(x.0, y.0).0), x * y, "{a} * {b}");
            if b != 0 {
                assert_eq!(Some(x.div_rem_limbs(y)), x.div_rem(y), "{a} / {b}");
            }
            assert_eq!(x.cmp(&y), a.cmp(&b), "{a} ? {b}");
            assert_eq!((-x).to_i128(), a.checked_neg());
            assert_eq!(x.abs().to_i128(), a.checked_abs());
            if b != 0 {
                let (q, r) = x.div_rem(y).unwrap();
                assert_eq!(
                    (q.to_i128(), r.to_i128()),
                    (Some(a / b), Some(a % b)),
                    "{a} / {b}"
                );
                assert_eq!(x.rem_euclid(y).to_i128(), Some(a.rem_euclid(b)));
                assert_eq!((x % y).to_i128(), Some(a % b));
            }
            let s = rng.below(60) as u32;
            assert_eq!((x >> s).to_i128(), Some(a >> s), "{a} >> {s}");
            assert_eq!(x.shr_limbs(s), x >> s, "{a} >> {s}");
            assert_eq!(x.shl_limbs(s), x << s, "{a} << {s}");
            assert_eq!(x.add_carry(y).0, x + y, "{a} + {b}");
            assert_eq!(x.add_carry(y.wrapping_neg()).0, x - y, "{a} - {b}");
            assert_eq!((x << s).to_i128(), a.checked_mul(1i128 << s), "{a} << {s}");
            if a >= 0 {
                assert_eq!(x.leading_zeros(), 128 + a.leading_zeros());
                assert_eq!(x.trailing_zeros().min(128), a.trailing_zeros());
            }
            assert_eq!((x & y).to_i128(), Some(a & b));
        }
    }

    /// Beyond 128 bits: carries across limbs, overflow at the ends, shifts of whole limbs.
    #[test]
    fn holds_256_bits() {
        let big = Int::ONE << 200;
        assert_eq!((big >> 200), Int::ONE);
        assert_eq!((big * big), Int::ZERO, "wraps");
        assert_eq!(big.checked_mul(big), None);
        assert_eq!(
            (Int::ONE << 127).checked_mul(Int::ONE << 127),
            Some(Int::ONE << 254)
        );
        assert_eq!(
            (Int::ONE << 128).checked_mul(Int::ONE << 127),
            None,
            "2^255 is not positive"
        );
        assert_eq!(
            (-(Int::ONE << 128)).checked_mul(Int::ONE << 127),
            Some(Int::MIN)
        );
        assert_eq!(Int::MAX.checked_add(Int::ONE), None);
        assert_eq!(Int::MIN.checked_sub(Int::ONE), None);
        assert_eq!(Int::MAX + Int::ONE, Int::MIN);
        assert_eq!(Int::MAX.saturating_add(big), Int::MAX);
        assert_eq!(Int::MIN.saturating_sub(big), Int::MIN);
        assert!(Int::MIN < -big && -big < Int::ZERO && Int::ZERO < big && big < Int::MAX);
        let low = (Int::ONE << 130) - Int::ONE;
        assert_eq!(low.leading_zeros(), 126);
        assert_eq!((low + Int::ONE).trailing_zeros(), 130);
        assert_eq!(low.to_i128(), None);
        assert_eq!((low >> 2).to_u128(), Some(u128::MAX));
        // (2^200 + 5) / 2^100 and its remainder, of either sign.
        let (q, r) = (big + Int::from(5u32)).div_rem(Int::ONE << 100).unwrap();
        assert_eq!((q, r), (Int::ONE << 100, Int::from(5u32)));
        let (q, r) = (-(big + Int::from(5u32))).div_rem(Int::ONE << 100).unwrap();
        assert_eq!((q, r), (-(Int::ONE << 100), Int::from(-5i32)));
        assert_eq!(
            (-(big + Int::from(5u32))).rem_euclid(Int::ONE << 100),
            (Int::ONE << 100) - Int::from(5u32)
        );
        assert_eq!((-Int::ONE >> 255), -Int::ONE);
        assert_eq!((Int::MIN >> 255), -Int::ONE);
        assert_eq!(Int::ONE.div_rem(Int::ZERO), None);
    }
}
