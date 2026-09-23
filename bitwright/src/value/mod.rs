//! Exact fixed-width bit-vector values.
//!
//! [`BitVec`] is an exact `W`-bit value for `W` in `1..=512`. It is `Copy`, and its padding
//! (the bits at and above `W`) is always zero, so derived equality and hashing are exact.
//! Every operation dispatches once on the width: `W <= 128` runs on a native `u128`, wider
//! values on `u64` limbs. Both paths are tested against an independent bit-serial reference.

mod narrow;
pub(crate) mod wide;

#[cfg(test)]
mod tests;

use core::fmt;
use core::num::NonZeroU16;

use crate::error::{ParseError, ValueError, WidthError};
use crate::ops::{BinOp, CmpOp, CmpOpExt, UnOp};
use wide::{Limbs, MAX_LIMBS, mask_top};

/// A bit width in `1..=512`. Invalid widths cannot be constructed.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Width(NonZeroU16);

const fn width_const(bits: u16) -> Width {
    match Width::new(bits) {
        Ok(w) => w,
        Err(_) => panic!("invalid width constant"),
    }
}

impl Width {
    /// The largest supported width.
    pub const MAX_BITS: u16 = 512;
    /// 1 bit (the width of comparisons and select conditions).
    pub const W1: Width = width_const(1);
    /// 8 bits.
    pub const W8: Width = width_const(8);
    /// 16 bits.
    pub const W16: Width = width_const(16);
    /// 32 bits.
    pub const W32: Width = width_const(32);
    /// 64 bits.
    pub const W64: Width = width_const(64);
    /// 128 bits.
    pub const W128: Width = width_const(128);
    /// 256 bits.
    pub const W256: Width = width_const(256);
    /// 512 bits.
    pub const W512: Width = width_const(512);

    /// A width of `bits` bits, if `bits` is in `1..=512`.
    pub const fn new(bits: u16) -> Result<Width, WidthError> {
        match NonZeroU16::new(bits) {
            Some(nz) if bits <= Self::MAX_BITS => Ok(Width(nz)),
            _ => Err(WidthError::Invalid { bits: bits as u32 }),
        }
    }

    /// The number of bits.
    #[inline]
    pub const fn bits(self) -> u16 {
        self.0.get()
    }

    /// Whether values of this width use the native (`<= 128` bits) fast path.
    #[inline]
    pub const fn is_narrow(self) -> bool {
        self.0.get() <= 128
    }
}

impl fmt::Debug for Width {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "W{}", self.bits())
    }
}

impl fmt::Display for Width {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.bits())
    }
}

impl TryFrom<u16> for Width {
    type Error = WidthError;
    fn try_from(bits: u16) -> Result<Self, WidthError> {
        Width::new(bits)
    }
}

/// An exact `W`-bit value, `W` in `1..=512`.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct BitVec {
    width: Width,
    limbs: Limbs,
}

impl BitVec {
    // ----- construction -------------------------------------------------------------------

    /// Builds from limbs that are already canonical for `width`.
    #[inline]
    pub(crate) const fn from_canonical(width: Width, limbs: Limbs) -> Self {
        BitVec { width, limbs }
    }

    #[inline]
    fn from_u128_masked(width: Width, v: u128) -> Self {
        let mut limbs = [0; MAX_LIMBS];
        limbs[0] = v as u64;
        limbs[1] = (v >> 64) as u64;
        mask_top(&mut limbs, width.bits());
        BitVec { width, limbs }
    }

    /// Zero.
    pub fn zero(width: Width) -> Self {
        BitVec {
            width,
            limbs: [0; MAX_LIMBS],
        }
    }

    /// One.
    pub fn one(width: Width) -> Self {
        Self::from_u128_masked(width, 1)
    }

    /// All ones (`-1` as a signed value).
    pub fn ones(width: Width) -> Self {
        BitVec {
            width,
            limbs: wide::ones(width.bits()),
        }
    }

    /// The most negative signed value (only the top bit set).
    pub fn smin(width: Width) -> Self {
        let mut limbs = [0; MAX_LIMBS];
        let top = width.bits() as usize - 1;
        limbs[top / 64] = 1 << (top % 64);
        BitVec { width, limbs }
    }

    /// The most positive signed value (every bit but the top set).
    pub fn smax(width: Width) -> Self {
        let mut v = Self::ones(width);
        let top = width.bits() as usize - 1;
        v.limbs[top / 64] &= !(1 << (top % 64));
        v
    }

    /// `v`, which must fit in `width` bits as an unsigned value.
    pub fn from_u64(width: Width, v: u64) -> Result<Self, ValueError> {
        Self::from_u128(width, u128::from(v))
    }

    /// `v`, which must fit in `width` bits as an unsigned value.
    pub fn from_u128(width: Width, v: u128) -> Result<Self, ValueError> {
        let r = Self::from_u128_masked(width, v);
        if r.to_u128() == Some(v) {
            Ok(r)
        } else {
            Err(ValueError::DoesNotFit {
                width: width.bits(),
            })
        }
    }

    /// `v`, which must be representable as a `width`-bit signed value.
    pub fn from_i128(width: Width, v: i128) -> Result<Self, ValueError> {
        let r = Self::wrapping_from_i128(width, v);
        if r.to_i128() == Some(v) {
            Ok(r)
        } else {
            Err(ValueError::DoesNotFit {
                width: width.bits(),
            })
        }
    }

    /// `v` truncated to `width` bits.
    pub fn wrapping_from_u64(width: Width, v: u64) -> Self {
        Self::from_u128_masked(width, u128::from(v))
    }

    /// `v` truncated to `width` bits.
    pub fn wrapping_from_u128(width: Width, v: u128) -> Self {
        Self::from_u128_masked(width, v)
    }

    /// `v` in two's complement, sign-extended or truncated to `width` bits.
    pub fn wrapping_from_i128(width: Width, v: i128) -> Self {
        let fill = if v < 0 { u64::MAX } else { 0 };
        let mut limbs = [fill; MAX_LIMBS];
        limbs[0] = v as u64;
        limbs[1] = (v >> 64) as u64;
        mask_top(&mut limbs, width.bits());
        BitVec { width, limbs }
    }

    /// Little-endian limbs, which must not have bits set at or above `width`.
    pub fn from_limbs(width: Width, limbs: &[u64]) -> Result<Self, ValueError> {
        let r = Self::wrapping_from_limbs(width, limbs);
        let fits = limbs.iter().enumerate().all(|(i, &x)| {
            let kept = if i < MAX_LIMBS { r.limbs[i] } else { 0 };
            x == kept
        });
        if fits {
            Ok(r)
        } else {
            Err(ValueError::DoesNotFit {
                width: width.bits(),
            })
        }
    }

    /// Little-endian limbs truncated to `width` bits.
    pub fn wrapping_from_limbs(width: Width, limbs: &[u64]) -> Self {
        let mut l = [0; MAX_LIMBS];
        for (d, s) in l.iter_mut().zip(limbs) {
            *d = *s;
        }
        mask_top(&mut l, width.bits());
        BitVec { width, limbs: l }
    }

    // ----- inspection ---------------------------------------------------------------------

    /// The width.
    #[inline]
    pub fn width(&self) -> Width {
        self.width
    }

    /// The `ceil(W / 64)` active little-endian limbs.
    #[inline]
    pub fn limbs(&self) -> &[u64] {
        &self.limbs[..wide::nlimbs(self.width.bits())]
    }

    #[inline]
    #[cfg_attr(not(test), expect(dead_code, reason = "used by the arena from M1"))]
    pub(crate) fn raw(&self) -> &Limbs {
        &self.limbs
    }

    /// The unsigned value, if it fits in a `u64`.
    pub fn to_u64(&self) -> Option<u64> {
        self.to_u128().and_then(|v| u64::try_from(v).ok())
    }

    /// The unsigned value, if it fits in a `u128`.
    pub fn to_u128(&self) -> Option<u128> {
        if self.limbs[2..].iter().any(|&x| x != 0) {
            return None;
        }
        Some(u128::from(self.limbs[0]) | (u128::from(self.limbs[1]) << 64))
    }

    /// The signed (two's-complement) value, if it fits in an `i128`.
    pub fn to_i128(&self) -> Option<i128> {
        let w = self.width.bits();
        if w <= 128 {
            return Some(narrow::signed(self.low_u128(), w));
        }
        // Wider: fits iff bits [127, w) are all equal.
        let sign = self.bit_unchecked(127);
        let fits = (128..w as usize).all(|i| self.bit_unchecked(i) == sign);
        fits.then(|| self.low_u128() as i128)
    }

    #[inline]
    fn low_u128(&self) -> u128 {
        u128::from(self.limbs[0]) | (u128::from(self.limbs[1]) << 64)
    }

    #[inline]
    fn bit_unchecked(&self, i: usize) -> bool {
        wide::bit(&self.limbs, i)
    }

    /// Bit `i`, or `None` if `i >= W`.
    pub fn bit(&self, i: u16) -> Option<bool> {
        (i < self.width.bits()).then(|| self.bit_unchecked(i as usize))
    }

    /// The sign (most significant) bit.
    pub fn msb(&self) -> bool {
        wide::msb(&self.limbs, self.width.bits())
    }

    /// Whether the value is zero.
    pub fn is_zero(&self) -> bool {
        wide::is_zero(&self.limbs)
    }

    /// Whether every bit is set.
    pub fn is_ones(&self) -> bool {
        self.limbs == wide::ones(self.width.bits())
    }

    // ----- operators ----------------------------------------------------------------------

    /// Applies a unary operator. The only error is `Bswap` at a width that is not a multiple
    /// of 8.
    pub fn apply_un(op: UnOp, a: &BitVec) -> Result<BitVec, WidthError> {
        let w = a.width.bits();
        if op == UnOp::Bswap && !w.is_multiple_of(8) {
            return Err(WidthError::NotByteMultiple { bits: w });
        }
        Ok(Self::un_unchecked(op, a))
    }

    pub(crate) fn un_unchecked(op: UnOp, a: &BitVec) -> BitVec {
        let w = a.width.bits();
        debug_assert!(
            op != UnOp::Bswap || w.is_multiple_of(8),
            "bswap at {w} bits"
        );
        if w <= 128 {
            Self::from_u128_masked(a.width, narrow::un(op, w, a.low_u128()))
        } else {
            BitVec::from_canonical(a.width, wide::un(op, w, &a.limbs))
        }
    }

    /// Applies a binary operator. Both operands must have the same width.
    pub fn apply_bin(op: BinOp, a: &BitVec, b: &BitVec) -> Result<BitVec, WidthError> {
        same_width(a, b)?;
        Ok(Self::bin_unchecked(op, a, b))
    }

    pub(crate) fn bin_unchecked(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
        let w = a.width.bits();
        if w <= 128 && narrow::bin_supported(op, w) {
            Self::from_u128_masked(a.width, narrow::bin(op, w, a.low_u128(), b.low_u128()))
        } else {
            BitVec::from_canonical(a.width, wide::bin(op, w, &a.limbs, &b.limbs))
        }
    }

    /// Evaluates a comparison. Both operands must have the same width.
    pub fn apply_cmp(op: impl Into<CmpOpExt>, a: &BitVec, b: &BitVec) -> Result<bool, WidthError> {
        same_width(a, b)?;
        let (op, swap) = op.into().canonical();
        let (a, b) = if swap { (b, a) } else { (a, b) };
        Ok(Self::cmp_unchecked(op, a, b))
    }

    pub(crate) fn cmp_unchecked(op: CmpOp, a: &BitVec, b: &BitVec) -> bool {
        let w = a.width.bits();
        if w <= 128 {
            narrow::cmp(op, w, a.low_u128(), b.low_u128())
        } else {
            wide::cmp(op, w, &a.limbs, &b.limbs)
        }
    }

    /// Zero extension to `to`, which must be at least as wide (equal width is the identity).
    pub fn zext(&self, to: Width) -> Result<BitVec, WidthError> {
        self.check_widen(to)?;
        Ok(BitVec {
            width: to,
            limbs: self.limbs,
        })
    }

    /// Sign extension to `to`, which must be at least as wide (equal width is the identity).
    pub fn sext(&self, to: Width) -> Result<BitVec, WidthError> {
        self.check_widen(to)?;
        Ok(BitVec {
            width: to,
            limbs: wide::sext(&self.limbs, self.width.bits(), to.bits()),
        })
    }

    fn check_widen(&self, to: Width) -> Result<(), WidthError> {
        if to < self.width {
            return Err(WidthError::NotWider {
                from: self.width.bits(),
                to: to.bits(),
            });
        }
        Ok(())
    }

    /// The low `to` bits (`to` must not exceed the width).
    pub fn trunc(&self, to: Width) -> Result<BitVec, WidthError> {
        self.extract(0, to)
    }

    /// Bits `[lo, lo + len)`.
    pub fn extract(&self, lo: u16, len: Width) -> Result<BitVec, WidthError> {
        let w = self.width.bits();
        if u32::from(lo) + u32::from(len.bits()) > u32::from(w) {
            return Err(WidthError::ExtractRange {
                width: w,
                lo,
                len: len.bits(),
            });
        }
        Ok(BitVec {
            width: len,
            limbs: wide::extract(&self.limbs, lo, len.bits()),
        })
    }

    /// `hi` in the high bits and `lo` in the low bits.
    pub fn concat(hi: &BitVec, lo: &BitVec) -> Result<BitVec, WidthError> {
        let total = u32::from(hi.width.bits()) + u32::from(lo.width.bits());
        let width = u16::try_from(total)
            .ok()
            .and_then(|t| Width::new(t).ok())
            .ok_or(WidthError::ConcatTooWide {
                hi: hi.width.bits(),
                lo: lo.width.bits(),
            })?;
        Ok(BitVec {
            width,
            limbs: wide::concat(&hi.limbs, &lo.limbs, lo.width.bits()),
        })
    }

    /// `if c { t } else { f }` for a 1-bit condition.
    pub fn select(c: &BitVec, t: &BitVec, f: &BitVec) -> Result<BitVec, WidthError> {
        if c.width != Width::W1 {
            return Err(WidthError::ConditionWidth {
                bits: c.width.bits(),
            });
        }
        same_width(t, f)?;
        Ok(if c.is_zero() { *f } else { *t })
    }

    /// A 1-bit value from a boolean.
    pub fn from_bool(b: bool) -> BitVec {
        Self::from_u128_masked(Width::W1, u128::from(b))
    }

    // ----- text ---------------------------------------------------------------------------

    /// Parses `<digits>:<width>`, where digits are decimal (optionally negative), `0x` hex or
    /// `0b` binary, or the Verilog form `<width>'h<hex>` / `'d` / `'b`.
    ///
    /// ```
    /// use bitwright::{BitVec, Width};
    /// assert_eq!(BitVec::parse("0xff:8").unwrap(), BitVec::ones(Width::W8));
    /// assert_eq!(BitVec::parse("-1:32").unwrap(), BitVec::ones(Width::W32));
    /// assert_eq!(BitVec::parse("8'h80").unwrap(), BitVec::smin(Width::W8));
    /// ```
    pub fn parse(s: &str) -> Result<BitVec, ParseError> {
        let s = s.trim();
        if let Some(q) = s.find('\'') {
            let width = parse_width(&s[..q])?;
            let rest = &s[q + 1..];
            let (radix, digits) = match rest.as_bytes().first() {
                Some(b'h' | b'H') => (16, &rest[1..]),
                Some(b'd' | b'D') => (10, &rest[1..]),
                Some(b'b' | b'B') => (2, &rest[1..]),
                _ => return Err(ParseError::BadDigit { at: q + 1 }),
            };
            return parse_magnitude(digits, radix, q + 2, width, false);
        }
        let colon = s.rfind(':').ok_or(ParseError::MissingWidth)?;
        let width = parse_width(&s[colon + 1..])?;
        let body = &s[..colon];
        let (neg, body, off) = match body.strip_prefix('-') {
            Some(rest) => (true, rest, 1),
            None => (false, body, 0),
        };
        let (radix, digits, off) = if let Some(d) = body.strip_prefix("0x") {
            (16, d, off + 2)
        } else if let Some(d) = body.strip_prefix("0b") {
            (2, d, off + 2)
        } else {
            (10, body, off)
        };
        parse_magnitude(digits, radix, off, width, neg)
    }
}

fn same_width(a: &BitVec, b: &BitVec) -> Result<(), WidthError> {
    if a.width != b.width {
        return Err(WidthError::Mismatch {
            left: a.width.bits(),
            right: b.width.bits(),
        });
    }
    Ok(())
}

fn parse_width(s: &str) -> Result<Width, ParseError> {
    let bad = || ParseError::BadWidth(WidthError::Invalid { bits: 0 });
    if s.is_empty() || !s.bytes().all(|b| b.is_ascii_digit()) {
        return Err(bad());
    }
    let bits: u32 = s
        .parse()
        .map_err(|_| ParseError::BadWidth(WidthError::Invalid { bits: u32::MAX }))?;
    let bits =
        u16::try_from(bits).map_err(|_| ParseError::BadWidth(WidthError::Invalid { bits }))?;
    Width::new(bits).map_err(ParseError::BadWidth)
}

fn parse_magnitude(
    digits: &str,
    radix: u32,
    offset: usize,
    width: Width,
    negative: bool,
) -> Result<BitVec, ParseError> {
    // Accumulate into one extra limb so overflow past 512 bits is detected.
    let mut acc = [0u64; MAX_LIMBS + 1];
    let mut any = false;
    for (i, ch) in digits.char_indices() {
        if ch == '_' {
            continue;
        }
        let d = ch
            .to_digit(radix)
            .ok_or(ParseError::BadDigit { at: offset + i })?;
        any = true;
        let mut carry = u128::from(d);
        for x in acc.iter_mut() {
            let t = u128::from(*x) * u128::from(radix) + carry;
            *x = t as u64;
            carry = t >> 64;
        }
        if carry != 0 || acc[MAX_LIMBS] != 0 {
            return Err(ParseError::DoesNotFit {
                width: width.bits(),
            });
        }
    }
    if !any {
        return Err(ParseError::BadDigit { at: offset });
    }
    let mut limbs = [0u64; MAX_LIMBS];
    limbs.copy_from_slice(&acc[..MAX_LIMBS]);
    let magnitude = BitVec::from_limbs(width, &limbs).map_err(|_| ParseError::DoesNotFit {
        width: width.bits(),
    })?;
    if !negative {
        return Ok(magnitude);
    }
    // -m must be representable: m <= 2^(W-1).
    let smin = BitVec::smin(width);
    if !magnitude.is_zero() && BitVec::cmp_unchecked(CmpOp::Ult, &smin, &magnitude) {
        return Err(ParseError::DoesNotFit {
            width: width.bits(),
        });
    }
    Ok(BitVec::un_unchecked(UnOp::Neg, &magnitude))
}

impl fmt::Display for BitVec {
    /// `0x<hex>:<width>`, the form accepted by [`BitVec::parse`].
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = wide::nlimbs(self.width.bits());
        let top = (0..n).rev().find(|&i| self.limbs[i] != 0);
        match top {
            None => write!(f, "0x0:{}", self.width.bits()),
            Some(t) => {
                write!(f, "0x{:x}", self.limbs[t])?;
                for i in (0..t).rev() {
                    write!(f, "{:016x}", self.limbs[i])?;
                }
                write!(f, ":{}", self.width.bits())
            }
        }
    }
}

impl fmt::Debug for BitVec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)?;
        if let Some(s) = self.to_i128().filter(|&s| s < 0) {
            write!(f, " ({s})")?;
        }
        Ok(())
    }
}

impl PartialOrd for BitVec {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BitVec {
    /// By width, then by unsigned value. (A total order for sorting and canonical keys; use
    /// [`BitVec::apply_cmp`] for signed or unsigned comparison of same-width values.)
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.width
            .cmp(&other.width)
            .then_with(|| self.limbs.iter().rev().cmp(other.limbs.iter().rev()))
    }
}

impl core::str::FromStr for BitVec {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, ParseError> {
        BitVec::parse(s)
    }
}

impl fmt::LowerHex for BitVec {
    /// The value in lower-case hexadecimal, without prefix or width.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = wide::nlimbs(self.width.bits());
        let top = (0..n).rev().find(|&i| self.limbs[i] != 0).unwrap_or(0);
        let mut s = format!("{:x}", self.limbs[top]);
        for i in (0..top).rev() {
            s.push_str(&format!("{:016x}", self.limbs[i]));
        }
        f.pad_integral(true, "0x", &s)
    }
}
