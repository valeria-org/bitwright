//! Limb kernels: exact for every width in `1..=512`.
//!
//! Values are little-endian `u64` limbs with every bit at or above the width clear (canonical
//! padding). Every function takes and returns canonical limbs. These kernels are the general
//! path; `narrow` is the fast path for widths up to 128 and is tested against these and against
//! the independent reference evaluator.

use crate::ops::{BinOp, CmpOp, UnOp};

pub(crate) const MAX_LIMBS: usize = 8;
pub(crate) type Limbs = [u64; MAX_LIMBS];

#[inline]
pub(crate) const fn nlimbs(w: u16) -> usize {
    (w as usize).div_ceil(64)
}

/// Clears every bit at or above `w`.
#[inline]
pub(crate) fn mask_top(l: &mut Limbs, w: u16) {
    let n = nlimbs(w);
    for x in l.iter_mut().skip(n) {
        *x = 0;
    }
    let r = w as usize % 64;
    if r != 0 {
        l[n - 1] &= (1u64 << r) - 1;
    }
}

/// All ones at width `w`.
pub(crate) fn ones(w: u16) -> Limbs {
    let mut l = [u64::MAX; MAX_LIMBS];
    mask_top(&mut l, w);
    l
}

#[inline]
pub(crate) fn is_zero(a: &Limbs) -> bool {
    a.iter().all(|&x| x == 0)
}

#[inline]
pub(crate) fn bit(a: &Limbs, i: usize) -> bool {
    (a[i / 64] >> (i % 64)) & 1 == 1
}

#[inline]
fn set_bit(a: &mut Limbs, i: usize) {
    a[i / 64] |= 1u64 << (i % 64);
}

#[inline]
pub(crate) fn msb(a: &Limbs, w: u16) -> bool {
    bit(a, w as usize - 1)
}

fn small(v: u64) -> Limbs {
    let mut l = [0; MAX_LIMBS];
    l[0] = v;
    l
}

/// Shifts the first `src.len()` limbs right by `s` bits; bits shifted in are zero.
fn shr_bits(src: &[u64], s: usize) -> Limbs {
    let (ls, bs) = (s / 64, s % 64);
    let mut out = [0u64; MAX_LIMBS];
    for (i, o) in out.iter_mut().enumerate() {
        let lo = src.get(i + ls).copied().unwrap_or(0);
        let hi = src.get(i + ls + 1).copied().unwrap_or(0);
        *o = if bs == 0 {
            lo
        } else {
            (lo >> bs) | (hi << (64 - bs))
        };
    }
    out
}

/// Shifts left by `s` bits within 512 bits; the caller masks to the result width.
fn shl_bits(src: &Limbs, s: usize) -> Limbs {
    let (ls, bs) = (s / 64, s % 64);
    let mut out = [0u64; MAX_LIMBS];
    for (i, o) in out.iter_mut().enumerate() {
        let lo = if i >= ls { src[i - ls] } else { 0 };
        let lower = if i > ls { src[i - ls - 1] } else { 0 };
        *o = if bs == 0 {
            lo
        } else {
            (lo << bs) | (lower >> (64 - bs))
        };
    }
    out
}

/// The unsigned value of a shift count if it is below 2^32, else `None` (certainly >= any width).
fn small_count(b: &Limbs) -> Option<u32> {
    if b[1..].iter().any(|&x| x != 0) {
        return None;
    }
    u32::try_from(b[0]).ok()
}

/// `b mod m` for a small modulus.
fn mod_small(b: &Limbs, w: u16, m: u16) -> usize {
    let mut rem: u128 = 0;
    for i in (0..nlimbs(w)).rev() {
        rem = ((rem << 64) | u128::from(b[i])) % u128::from(m);
    }
    rem as usize
}

pub(crate) fn not(w: u16, a: &Limbs) -> Limbs {
    let mut r = [0; MAX_LIMBS];
    for i in 0..nlimbs(w) {
        r[i] = !a[i];
    }
    mask_top(&mut r, w);
    r
}

pub(crate) fn add(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    let mut r = [0; MAX_LIMBS];
    let mut carry = false;
    for i in 0..nlimbs(w) {
        let (s1, c1) = a[i].overflowing_add(b[i]);
        let (s2, c2) = s1.overflowing_add(u64::from(carry));
        r[i] = s2;
        carry = c1 | c2;
    }
    mask_top(&mut r, w);
    r
}

pub(crate) fn sub(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    let mut r = [0; MAX_LIMBS];
    let mut borrow = false;
    for i in 0..nlimbs(w) {
        let (d1, b1) = a[i].overflowing_sub(b[i]);
        let (d2, b2) = d1.overflowing_sub(u64::from(borrow));
        r[i] = d2;
        borrow = b1 | b2;
    }
    mask_top(&mut r, w);
    r
}

pub(crate) fn neg(w: u16, a: &Limbs) -> Limbs {
    sub(w, &[0; MAX_LIMBS], a)
}

/// The full `2n`-limb product of two `n`-limb operands.
fn mul_full(n: usize, a: &Limbs, b: &Limbs) -> [u64; 2 * MAX_LIMBS] {
    let mut p = [0u64; 2 * MAX_LIMBS];
    for i in 0..n {
        let mut carry: u128 = 0;
        for j in 0..n {
            // (2^64-1) + (2^64-1)^2 + (2^64-1) = 2^128 - 1: no overflow.
            let t = u128::from(p[i + j]) + u128::from(a[i]) * u128::from(b[j]) + carry;
            p[i + j] = t as u64;
            carry = t >> 64;
        }
        p[i + n] = carry as u64;
    }
    p
}

pub(crate) fn mul(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    let n = nlimbs(w);
    let p = mul_full(n, a, b);
    let mut r = [0; MAX_LIMBS];
    r[..n].copy_from_slice(&p[..n]);
    mask_top(&mut r, w);
    r
}

pub(crate) fn umulhi(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    let n = nlimbs(w);
    let p = mul_full(n, a, b);
    let mut r = shr_bits(&p[..2 * n], w as usize);
    mask_top(&mut r, w);
    r
}

/// `smulhi(a, b) = umulhi(a, b) - (a <s 0 ? b : 0) - (b <s 0 ? a : 0)  (mod 2^W)`.
pub(crate) fn smulhi(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    let mut r = umulhi(w, a, b);
    if msb(a, w) {
        r = sub(w, &r, b);
    }
    if msb(b, w) {
        r = sub(w, &r, a);
    }
    r
}

/// Unsigned quotient and remainder with the SMT-LIB conventions for a zero divisor.
///
/// Shift-subtract long division, one quotient bit per step over whole limbs (about 3 µs at 512
/// bits). Wide division is rare in practice; Knuth's algorithm D is the planned replacement if
/// profiling ever shows it matters.
pub(crate) fn udivrem(w: u16, a: &Limbs, b: &Limbs) -> (Limbs, Limbs) {
    if is_zero(b) {
        return (ones(w), *a);
    }
    // Binary long division with one extra limb for the remainder's shifted-out bit.
    let mut q = [0u64; MAX_LIMBS];
    let mut r = [0u64; MAX_LIMBS + 1];
    for i in (0..w as usize).rev() {
        let mut carry = u64::from(bit(a, i));
        for x in r.iter_mut() {
            let next = *x >> 63;
            *x = (*x << 1) | carry;
            carry = next;
        }
        let ge = {
            let mut ge = true;
            for k in (0..=MAX_LIMBS).rev() {
                let bk = if k < MAX_LIMBS { b[k] } else { 0 };
                if r[k] != bk {
                    ge = r[k] > bk;
                    break;
                }
            }
            ge
        };
        if ge {
            let mut borrow = false;
            for (k, x) in r.iter_mut().enumerate() {
                let bk = if k < MAX_LIMBS { b[k] } else { 0 };
                let (d1, b1) = x.overflowing_sub(bk);
                let (d2, b2) = d1.overflowing_sub(u64::from(borrow));
                *x = d2;
                borrow = b1 | b2;
            }
            set_bit(&mut q, i);
        }
    }
    let mut rem = [0u64; MAX_LIMBS];
    rem.copy_from_slice(&r[..MAX_LIMBS]);
    (q, rem)
}

/// `bvsdiv`, defined over unsigned division and negation.
pub(crate) fn sdiv(w: u16, a: &Limbs, b: &Limbs, udiv: impl Fn(&Limbs, &Limbs) -> Limbs) -> Limbs {
    match (msb(a, w), msb(b, w)) {
        (false, false) => udiv(a, b),
        (true, false) => neg(w, &udiv(&neg(w, a), b)),
        (false, true) => neg(w, &udiv(a, &neg(w, b))),
        (true, true) => udiv(&neg(w, a), &neg(w, b)),
    }
}

/// `bvsrem`, defined over unsigned remainder and negation.
pub(crate) fn srem(w: u16, a: &Limbs, b: &Limbs, urem: impl Fn(&Limbs, &Limbs) -> Limbs) -> Limbs {
    match (msb(a, w), msb(b, w)) {
        (false, false) => urem(a, b),
        (true, false) => neg(w, &urem(&neg(w, a), b)),
        (false, true) => urem(a, &neg(w, b)),
        (true, true) => neg(w, &urem(&neg(w, a), &neg(w, b))),
    }
}

fn shift_amount(w: u16, b: &Limbs) -> Option<usize> {
    small_count(b)
        .map(|c| c as usize)
        .filter(|&c| c < w as usize)
}

pub(crate) fn shl(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    match shift_amount(w, b) {
        None => [0; MAX_LIMBS],
        Some(s) => {
            let mut r = shl_bits(a, s);
            mask_top(&mut r, w);
            r
        }
    }
}

pub(crate) fn lshr(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    match shift_amount(w, b) {
        None => [0; MAX_LIMBS],
        Some(s) => shr_bits(a, s),
    }
}

pub(crate) fn ashr(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    let negative = msb(a, w);
    match shift_amount(w, b) {
        None if negative => ones(w),
        None => [0; MAX_LIMBS],
        Some(s) => {
            let mut r = shr_bits(a, s);
            if negative {
                // Fill bits [w - s, w).
                let mut fill = shl_bits(&ones(w), w as usize - s);
                mask_top(&mut fill, w);
                for (x, f) in r.iter_mut().zip(fill) {
                    *x |= f;
                }
            }
            r
        }
    }
}

fn rotl_by(w: u16, a: &Limbs, r: usize) -> Limbs {
    if r == 0 {
        return *a;
    }
    let mut hi = shl_bits(a, r);
    mask_top(&mut hi, w);
    let lo = shr_bits(a, w as usize - r);
    let mut out = [0; MAX_LIMBS];
    for i in 0..MAX_LIMBS {
        out[i] = hi[i] | lo[i];
    }
    out
}

pub(crate) fn rotl(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    rotl_by(w, a, mod_small(b, w, w))
}

pub(crate) fn rotr(w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    let r = mod_small(b, w, w);
    rotl_by(w, a, (w as usize - r) % w as usize)
}

pub(crate) fn pdep(w: u16, x: &Limbs, m: &Limbs) -> Limbs {
    // Walk the set bits of the mask a word at a time; bit k of x goes to the k-th set bit.
    let mut out = [0; MAX_LIMBS];
    let mut k = 0usize;
    for (li, &word) in m.iter().enumerate().take(nlimbs(w)) {
        let mut mm = word;
        while mm != 0 {
            let p = mm.trailing_zeros() as usize;
            if bit(x, k) {
                out[li] |= 1 << p;
            }
            k += 1;
            mm &= mm - 1;
        }
    }
    out
}

pub(crate) fn pext(w: u16, x: &Limbs, m: &Limbs) -> Limbs {
    // Walk the set bits of the mask a word at a time; the k-th set bit's value goes to bit k.
    let mut out = [0; MAX_LIMBS];
    let mut k = 0usize;
    for (li, &word) in m.iter().enumerate().take(nlimbs(w)) {
        let mut mm = word;
        while mm != 0 {
            let p = mm.trailing_zeros() as usize;
            if (x[li] >> p) & 1 == 1 {
                set_bit(&mut out, k);
            }
            k += 1;
            mm &= mm - 1;
        }
    }
    out
}

pub(crate) fn popcnt(a: &Limbs) -> Limbs {
    small(a.iter().map(|x| u64::from(x.count_ones())).sum())
}

pub(crate) fn clz(w: u16, a: &Limbs) -> Limbs {
    let n = nlimbs(w);
    let pad = n * 64 - w as usize;
    for i in (0..n).rev() {
        if a[i] != 0 {
            let lz = (n - 1 - i) * 64 + a[i].leading_zeros() as usize;
            return small((lz - pad) as u64);
        }
    }
    small(u64::from(w))
}

pub(crate) fn ctz(w: u16, a: &Limbs) -> Limbs {
    for (i, &x) in a.iter().enumerate().take(nlimbs(w)) {
        if x != 0 {
            return small((i * 64 + x.trailing_zeros() as usize) as u64);
        }
    }
    small(u64::from(w))
}

/// Byte reversal. The caller guarantees `w % 8 == 0`.
pub(crate) fn bswap(w: u16, a: &Limbs) -> Limbs {
    let nbytes = w as usize / 8;
    let mut bytes = [0u8; MAX_LIMBS * 8];
    for (i, x) in a.iter().enumerate() {
        bytes[i * 8..i * 8 + 8].copy_from_slice(&x.to_le_bytes());
    }
    bytes[..nbytes].reverse();
    let mut out = [0u64; MAX_LIMBS];
    for (i, o) in out.iter_mut().enumerate() {
        let mut chunk = [0u8; 8];
        chunk.copy_from_slice(&bytes[i * 8..i * 8 + 8]);
        *o = u64::from_le_bytes(chunk);
    }
    mask_top(&mut out, w);
    out
}

pub(crate) fn bitrev(w: u16, a: &Limbs) -> Limbs {
    let n = nlimbs(w);
    let mut rev = [0u64; MAX_LIMBS];
    for i in 0..n {
        rev[i] = a[n - 1 - i].reverse_bits();
    }
    let mut r = shr_bits(&rev[..n], n * 64 - w as usize);
    mask_top(&mut r, w);
    r
}

pub(crate) fn ult(w: u16, a: &Limbs, b: &Limbs) -> bool {
    for i in (0..nlimbs(w)).rev() {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
    }
    false
}

pub(crate) fn slt(w: u16, a: &Limbs, b: &Limbs) -> bool {
    match (msb(a, w), msb(b, w)) {
        (true, false) => true,
        (false, true) => false,
        _ => ult(w, a, b),
    }
}

pub(crate) fn un(op: UnOp, w: u16, a: &Limbs) -> Limbs {
    match op {
        UnOp::Not => not(w, a),
        UnOp::Neg => neg(w, a),
        UnOp::Popcnt => popcnt(a),
        UnOp::Clz => clz(w, a),
        UnOp::Ctz => ctz(w, a),
        UnOp::Bswap => bswap(w, a),
        UnOp::BitRev => bitrev(w, a),
    }
}

pub(crate) fn bin(op: BinOp, w: u16, a: &Limbs, b: &Limbs) -> Limbs {
    match op {
        BinOp::Add => add(w, a, b),
        BinOp::Sub => sub(w, a, b),
        BinOp::Mul => mul(w, a, b),
        BinOp::UMulHi => umulhi(w, a, b),
        BinOp::SMulHi => smulhi(w, a, b),
        BinOp::UDiv => udivrem(w, a, b).0,
        BinOp::URem => udivrem(w, a, b).1,
        BinOp::SDiv => sdiv(w, a, b, |x, y| udivrem(w, x, y).0),
        BinOp::SRem => srem(w, a, b, |x, y| udivrem(w, x, y).1),
        BinOp::And => core::array::from_fn(|i| a[i] & b[i]),
        BinOp::Or => core::array::from_fn(|i| a[i] | b[i]),
        BinOp::Xor => core::array::from_fn(|i| a[i] ^ b[i]),
        BinOp::Shl => shl(w, a, b),
        BinOp::LShr => lshr(w, a, b),
        BinOp::AShr => ashr(w, a, b),
        BinOp::RotL => rotl(w, a, b),
        BinOp::RotR => rotr(w, a, b),
        BinOp::Pdep => pdep(w, a, b),
        BinOp::Pext => pext(w, a, b),
    }
}

pub(crate) fn cmp(op: CmpOp, w: u16, a: &Limbs, b: &Limbs) -> bool {
    match op {
        CmpOp::Eq => a == b,
        CmpOp::Ne => a != b,
        CmpOp::Ult => ult(w, a, b),
        CmpOp::Ule => !ult(w, b, a),
        CmpOp::Slt => slt(w, a, b),
        CmpOp::Sle => !slt(w, b, a),
    }
}

/// Sign extension from `from` bits to `to` bits (`to > from`).
pub(crate) fn sext(a: &Limbs, from: u16, to: u16) -> Limbs {
    let mut r = *a;
    if msb(a, from) {
        let hi = ones(to);
        let lo = ones(from);
        for i in 0..MAX_LIMBS {
            r[i] |= hi[i] & !lo[i];
        }
    }
    r
}

/// Bits `[lo, lo + n)`.
pub(crate) fn extract(a: &Limbs, lo: u16, n: u16) -> Limbs {
    let mut r = shr_bits(a, lo as usize);
    mask_top(&mut r, n);
    r
}

/// `hi * 2^lo_w + lo` (the caller checks the total width).
pub(crate) fn concat(hi: &Limbs, lo: &Limbs, lo_w: u16) -> Limbs {
    let h = shl_bits(hi, lo_w as usize);
    core::array::from_fn(|i| h[i] | lo[i])
}
