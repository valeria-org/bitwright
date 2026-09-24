//! Arbitrary-precision natural numbers for the floating-point oracle.
//!
//! A [`Nat`] is a vector of little-endian `u64` limbs with no trailing zero limb (zero is the
//! empty vector), so equal numbers have equal representations and the derived `Eq` is numeric
//! equality. Everything here is exact schoolbook arithmetic: carry-propagating addition and
//! subtraction, `u128`-accumulated multiplication, short division by one limb, binary long
//! division by longer divisors, and Newton's integer square root (checked on exit).

use std::cmp::Ordering;

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub(super) struct Nat(Vec<u64>);

impl Nat {
    pub(super) fn zero() -> Nat {
        Nat(Vec::new())
    }

    pub(super) fn one() -> Nat {
        Nat(vec![1])
    }

    /// Builds a number from little-endian limbs (trailing zero limbs are dropped).
    pub(super) fn from_limbs(mut limbs: Vec<u64>) -> Nat {
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
        Nat(limbs)
    }

    pub(super) fn from_u64(v: u64) -> Nat {
        Nat::from_limbs(vec![v])
    }

    /// `2^k`.
    pub(super) fn pow2(k: u64) -> Nat {
        let k = usize::try_from(k).expect("shift fits in usize");
        let mut limbs = vec![0u64; k / 64 + 1];
        limbs[k / 64] = 1u64 << (k % 64);
        Nat(limbs)
    }

    /// `2^k - 1` (`k` ones).
    pub(super) fn ones(k: u64) -> Nat {
        Nat::pow2(k).sub(&Nat::one())
    }

    /// The little-endian limbs (empty for zero).
    pub(super) fn limbs(&self) -> &[u64] {
        &self.0
    }

    pub(super) fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    pub(super) fn is_odd(&self) -> bool {
        self.0.first().is_some_and(|l| l & 1 == 1)
    }

    /// The value as a `u64`, if it fits.
    pub(super) fn to_u64(&self) -> Option<u64> {
        match self.0.len() {
            0 => Some(0),
            1 => Some(self.0[0]),
            _ => None,
        }
    }

    /// The number of significant bits (0 for zero): `2^(len-1) <= self < 2^len`.
    pub(super) fn bit_len(&self) -> u64 {
        match self.0.last() {
            None => 0,
            Some(&top) => (self.0.len() as u64 - 1) * 64 + u64::from(64 - top.leading_zeros()),
        }
    }

    /// Bit `i` (0 = least significant); bits past the top read as zero.
    pub(super) fn bit(&self, i: u64) -> bool {
        let limb = usize::try_from(i / 64).unwrap_or(usize::MAX);
        self.0.get(limb).is_some_and(|l| (l >> (i % 64)) & 1 == 1)
    }

    /// Whether the number is a power of two (zero is not).
    pub(super) fn is_pow2(&self) -> bool {
        match self.0.split_last() {
            None => false,
            Some((top, rest)) => top.is_power_of_two() && rest.iter().all(|&l| l == 0),
        }
    }

    /// `self * 2^k`.
    pub(super) fn shl(&self, k: u64) -> Nat {
        if self.is_zero() {
            return Nat::zero();
        }
        let k = usize::try_from(k).expect("shift fits in usize");
        let (limbs, bits) = (k / 64, (k % 64) as u32);
        let mut out = vec![0u64; limbs + self.0.len() + 1];
        for (i, &l) in self.0.iter().enumerate() {
            out[i + limbs] |= l << bits;
            if bits > 0 {
                out[i + limbs + 1] |= l >> (64 - bits);
            }
        }
        Nat::from_limbs(out)
    }

    /// `floor(self / 2^k)`.
    pub(super) fn shr(&self, k: u64) -> Nat {
        let limbs = usize::try_from(k / 64).unwrap_or(usize::MAX);
        let bits = (k % 64) as u32;
        if limbs >= self.0.len() {
            return Nat::zero();
        }
        let src = &self.0[limbs..];
        let out = (0..src.len())
            .map(|i| {
                let lo = src[i] >> bits;
                let hi = match src.get(i + 1) {
                    Some(&next) if bits > 0 => next << (64 - bits),
                    _ => 0,
                };
                lo | hi
            })
            .collect();
        Nat::from_limbs(out)
    }

    /// `self mod 2^k`.
    pub(super) fn low_bits(&self, k: u64) -> Nat {
        let limbs = usize::try_from(k / 64).unwrap_or(usize::MAX);
        let bits = (k % 64) as u32;
        if limbs >= self.0.len() {
            return self.clone();
        }
        // limbs < len, so limb `limbs` exists; keep it only for a partial limb.
        let mut out = self.0[..limbs + usize::from(bits > 0)].to_vec();
        if bits > 0 {
            out[limbs] &= (1u64 << bits) - 1;
        }
        Nat::from_limbs(out)
    }

    pub(super) fn add(&self, other: &Nat) -> Nat {
        let (long, short) = if self.0.len() >= other.0.len() {
            (&self.0, &other.0)
        } else {
            (&other.0, &self.0)
        };
        let mut out = Vec::with_capacity(long.len() + 1);
        let mut carry = 0u64;
        for (i, &x) in long.iter().enumerate() {
            let y = short.get(i).copied().unwrap_or(0);
            let t = u128::from(x) + u128::from(y) + u128::from(carry);
            out.push(t as u64);
            carry = (t >> 64) as u64;
        }
        out.push(carry);
        Nat::from_limbs(out)
    }

    /// `self - other`; panics if `other > self`.
    pub(super) fn sub(&self, other: &Nat) -> Nat {
        let mut out = self.0.clone();
        sub_in_place(&mut out, &other.0);
        Nat::from_limbs(out)
    }

    pub(super) fn mul(&self, other: &Nat) -> Nat {
        if self.is_zero() || other.is_zero() {
            return Nat::zero();
        }
        let (a, b) = (&self.0, &other.0);
        let mut out = vec![0u64; a.len() + b.len()];
        for (i, &x) in a.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &y) in b.iter().enumerate() {
                // At most (2^64 - 1) + (2^64 - 1)^2 + (2^64 - 1) = 2^128 - 1.
                let t = u128::from(out[i + j]) + u128::from(x) * u128::from(y) + carry;
                out[i + j] = t as u64;
                carry = t >> 64;
            }
            // Rows before i wrote at most position i - 1 + b.len(), so this slot is still 0.
            out[i + b.len()] = carry as u64;
        }
        Nat::from_limbs(out)
    }

    /// `(floor(self / d), self mod d)`; panics if `d` is zero.
    pub(super) fn divrem(&self, d: &Nat) -> (Nat, Nat) {
        assert!(
            !d.is_zero(),
            "bitwright-ref: fp: division by zero in Nat::divrem"
        );
        if *self < *d {
            return (Nat::zero(), self.clone());
        }
        if d.is_pow2() {
            let k = d.bit_len() - 1;
            return (self.shr(k), self.low_bits(k));
        }
        if d.0.len() == 1 {
            // Short division: the running remainder stays below d < 2^64.
            let dv = u128::from(d.0[0]);
            let mut q = vec![0u64; self.0.len()];
            let mut r = 0u128;
            for i in (0..self.0.len()).rev() {
                let cur = (r << 64) | u128::from(self.0[i]);
                q[i] = (cur / dv) as u64;
                r = cur % dv;
            }
            return (Nat::from_limbs(q), Nat::from_limbs(vec![r as u64]));
        }
        // Binary long division. The top bit_len(d) - 1 bits of self are below d, so they start
        // the partial remainder; each remaining bit is shifted in and d subtracted when it fits,
        // which keeps the partial remainder below d.
        let (ln, ld) = (self.bit_len(), d.bit_len());
        let steps = ln - ld + 1;
        let mut r = self.shr(steps).0;
        let mut q = vec![0u64; usize::try_from(steps / 64 + 1).expect("quotient size")];
        for i in (0..steps).rev() {
            shl1_in_place(&mut r, self.bit(i));
            if cmp_limbs(&r, &d.0) != Ordering::Less {
                sub_in_place(&mut r, &d.0);
                q[(i / 64) as usize] |= 1u64 << (i % 64);
            }
        }
        (Nat::from_limbs(q), Nat::from_limbs(r))
    }

    /// `floor(sqrt(self))`, by Newton's iteration on integers from a start at or above the
    /// root; the result is checked (`x^2 <= self < (x + 1)^2`) before it is returned.
    pub(super) fn isqrt(&self) -> Nat {
        if self.is_zero() {
            return Nat::zero();
        }
        // x0 = 2^ceil(len/2): x0^2 >= 2^len > self.
        let mut x = Nat::pow2(self.bit_len().div_ceil(2));
        loop {
            let y = x.add(&self.divrem(&x).0).shr(1);
            if y >= x {
                break;
            }
            x = y;
        }
        let next = x.add(&Nat::one());
        assert!(
            x.mul(&x) <= *self && next.mul(&next) > *self,
            "bitwright-ref: fp: integer square root check failed"
        );
        x
    }
}

/// Compares normalized limb vectors.
fn cmp_limbs(a: &[u64], b: &[u64]) -> Ordering {
    a.len()
        .cmp(&b.len())
        .then_with(|| a.iter().rev().cmp(b.iter().rev()))
}

/// `a = 2a + bit`, keeping `a` normalized.
fn shl1_in_place(a: &mut Vec<u64>, bit: bool) {
    let mut carry = u64::from(bit);
    for l in a.iter_mut() {
        let out = *l >> 63;
        *l = (*l << 1) | carry;
        carry = out;
    }
    if carry != 0 {
        a.push(carry);
    }
}

/// `a -= b` for normalized `a >= b`, leaving `a` normalized; panics on underflow.
fn sub_in_place(a: &mut Vec<u64>, b: &[u64]) {
    assert!(
        cmp_limbs(a, b) != Ordering::Less,
        "bitwright-ref: fp: negative result in Nat subtraction"
    );
    let mut borrow = false;
    for (i, x) in a.iter_mut().enumerate() {
        let y = b.get(i).copied().unwrap_or(0);
        let (d1, b1) = x.overflowing_sub(y);
        let (d2, b2) = d1.overflowing_sub(u64::from(borrow));
        *x = d2;
        borrow = b1 || b2;
        if !borrow && i >= b.len() {
            break;
        }
    }
    debug_assert!(!borrow);
    while a.last() == Some(&0) {
        a.pop();
    }
}

impl Ord for Nat {
    fn cmp(&self, other: &Nat) -> Ordering {
        cmp_limbs(&self.0, &other.0)
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, other: &Nat) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Compares `a * 2^x` with `b * 2^y` exactly (`a`, `b` nonzero).
pub(super) fn cmp_scaled(a: &Nat, x: i64, b: &Nat, y: i64) -> Ordering {
    debug_assert!(!a.is_zero() && !b.is_zero());
    // a * 2^x lies in [2^(len_a - 1 + x), 2^(len_a + x)); different tops decide at once.
    let ta = a.bit_len() as i64 + x;
    let tb = b.bit_len() as i64 + y;
    if ta != tb {
        return ta.cmp(&tb);
    }
    let s = x.min(y);
    a.shl((x - s) as u64).cmp(&b.shl((y - s) as u64))
}
