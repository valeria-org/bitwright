//! Literals read against their types, and values written as LLVM IR constants.

use super::ir::Ty;
use crate::fp::{FpFormat, RoundingMode};
use crate::{BitVec, Width};

/// The magnitude of an unsigned number (decimal, or hexadecimal after `0x`) as limbs.
fn magnitude(s: &str) -> Option<Vec<u64>> {
    let (digits, radix) = match s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        Some(h) => (h, 16u64),
        None => (s, 10),
    };
    if digits.is_empty() {
        return None;
    }
    let mut limbs: Vec<u64> = vec![0];
    for ch in digits.chars() {
        let d = u64::from(ch.to_digit(radix as u32)?);
        // limbs = limbs * radix + d
        let mut carry = u128::from(d);
        for l in limbs.iter_mut() {
            let v = u128::from(*l) * u128::from(radix) + carry;
            *l = v as u64;
            carry = v >> 64;
        }
        if carry > 0 {
            limbs.push(carry as u64);
        }
    }
    Some(limbs)
}

fn bit_len(limbs: &[u64]) -> u32 {
    for (i, &l) in limbs.iter().enumerate().rev() {
        if l != 0 {
            return 64 * i as u32 + (64 - l.leading_zeros());
        }
    }
    0
}

/// An integer literal at width `w`, if it fits as an unsigned or a signed number.
pub(crate) fn int_literal(s: &str, w: u16) -> Option<BitVec> {
    let width = Width::new(w).ok()?;
    let (neg, body) = match s.strip_prefix('-') {
        Some(b) => (true, b),
        None => (false, s),
    };
    let m = magnitude(body)?;
    let bits = bit_len(&m);
    if neg {
        // −m fits when m ≤ 2^(w−1).
        let limit_ok = bits < u32::from(w)
            || (bits == u32::from(w)
                && m.iter().enumerate().all(|(i, &l)| {
                    let top = u32::from(w) - 1;
                    let want = if i as u32 == top / 64 {
                        1u64 << (top % 64)
                    } else {
                        0
                    };
                    l == want
                }));
        if !limit_ok {
            return None;
        }
        let v = BitVec::wrapping_from_limbs(width, &m);
        Some(BitVec::apply_un(crate::UnOp::Neg, &v).ok()?)
    } else {
        if bits > u32::from(w) {
            return None;
        }
        Some(BitVec::wrapping_from_limbs(width, &m))
    }
}

/// A floating-point literal of format `f`: a decimal number exactly representable in `f`
/// (read through binary64), `0x` and 16 hexadecimal digits (a binary64 encoding, LLVM's form
/// for `float` and `double`, exactly representable in `f`), or `0xH` (half), `0xR` (bfloat)
/// and `0xL` (fp128) encodings.
pub(crate) fn float_literal(s: &str, f: FpFormat) -> Option<BitVec> {
    let (neg, body) = match s.strip_prefix('-') {
        Some(b) => (true, b),
        None => (false, s),
    };
    let bits = if let Some(h) = body.strip_prefix("0x") {
        let (kind, hex) = match h.chars().next()? {
            c @ ('H' | 'R' | 'L' | 'K' | 'M') => (Some(c), &h[1..]),
            _ => (None, h),
        };
        let m = magnitude(&format!("0x{hex}"))?;
        match kind {
            None => {
                if hex.len() > 16 {
                    return None;
                }
                let d = BitVec::wrapping_from_limbs(Width::W64, &m);
                from_f64_bits(&d, f)?
            }
            Some('H') if f == FpFormat::F16 => {
                BitVec::wrapping_from_limbs(Width::new(16).ok()?, &m)
            }
            Some('R') if f == FpFormat::BF16 => {
                BitVec::wrapping_from_limbs(Width::new(16).ok()?, &m)
            }
            // fp128: LLVM writes the low 64 bits first.
            Some('L') if f == FpFormat::F128 => {
                if hex.len() != 32 {
                    return None;
                }
                let lo = u64::from_str_radix(&hex[..16], 16).ok()?;
                let hi = u64::from_str_radix(&hex[16..], 16).ok()?;
                BitVec::wrapping_from_limbs(Width::new(128).ok()?, &[lo, hi])
            }
            _ => return None,
        }
    } else {
        let v: f64 = body.parse().ok()?;
        if !v.is_finite() {
            return None;
        }
        from_f64_bits(&BitVec::from_f64(v), f)?
    };
    Some(if neg {
        BitVec::apply_bin(crate::BinOp::Xor, &bits, &sign_bit(f)).ok()?
    } else {
        bits
    })
}

fn sign_bit(f: FpFormat) -> BitVec {
    BitVec::smin(f.width())
}

/// A binary64 value converted to `f`, if exactly (NaNs keep their payload's high bits).
fn from_f64_bits(d: &BitVec, f: FpFormat) -> Option<BitVec> {
    if f == FpFormat::F64 {
        return Some(*d);
    }
    let v = f64::from_bits(d.to_u64()?);
    if v.is_nan() {
        // Sign, a quiet bit and payload's high bits, as LLVM converts NaN constants.
        let raw = d.to_u64()?;
        let sign = raw >> 63;
        let mant = raw & ((1u64 << 52) - 1);
        let mw = f.sb() - 1;
        let m = if mw <= 52 {
            mant >> (52 - mw)
        } else {
            mant << (mw - 52)
        };
        if m == 0 {
            return None;
        }
        let e = (1u64 << f.eb()) - 1;
        let w = f.width();
        let bits = u128::from(sign) << (w.bits() - 1) | u128::from(e) << mw | u128::from(m);
        return BitVec::from_u128(w, bits).ok();
    }
    let out = FpFormat::F64.convert(f, RoundingMode::Rne, d).ok()?;
    let back = f.convert(FpFormat::F64, RoundingMode::Rne, &out).ok()?;
    (back == *d).then_some(out)
}

/// A value as an LLVM IR constant of its type: `i8 -1`, `i1 true`, `float 1.5`,
/// `double 0x7FF8000000000000`.
pub(crate) fn ir_constant(ty: Ty, v: &BitVec) -> String {
    match ty {
        Ty::Int(1) => format!("i1 {}", if v.is_zero() { "false" } else { "true" }),
        Ty::Int(w) => format!("i{w} {}", signed_decimal(v)),
        Ty::Float(f) => format!("{ty} {}", float_text(f, v)),
    }
}

/// The signed decimal value of `v`.
pub(crate) fn signed_decimal(v: &BitVec) -> String {
    if let Some(x) = v.to_i128()
        && v.width().bits() <= 128
    {
        let w = v.width().bits();
        let x = if w < 128 {
            // Sign-extend from `w` bits.
            let shift = 128 - u32::from(w);
            (x << shift) >> shift
        } else {
            x
        };
        return x.to_string();
    }
    // Wider values: hexadecimal of the bits.
    let mut s = String::from("0x");
    for l in v.limbs().iter().rev() {
        s.push_str(&format!("{l:016x}"));
    }
    s
}

/// A floating-point value as LLVM writes it: a short exact decimal when there is one, else
/// hexadecimal (the binary64 encoding for `float` and `double`).
pub(crate) fn float_text(f: FpFormat, v: &BitVec) -> String {
    let nan = f.test(crate::fp::FpTest::Nan, v).unwrap_or(false);
    let inf = f.test(crate::fp::FpTest::Infinite, v).unwrap_or(false);
    let hex = || -> String {
        match (f.eb(), f.sb()) {
            (5, 11) => format!("0xH{:04X}", v.to_u64().unwrap_or(0)),
            (8, 8) => format!("0xR{:04X}", v.to_u64().unwrap_or(0)),
            (15, 113) => {
                let l = v.limbs();
                format!("0xL{:016X}{:016X}", l[0], l.get(1).copied().unwrap_or(0))
            }
            _ => {
                // The binary64 encoding (NaN payloads widened as LLVM does).
                let d = if f == FpFormat::F64 {
                    v.to_u64().unwrap_or(0)
                } else if nan {
                    let raw = v.to_u64().unwrap_or(0);
                    let mw = f.sb() - 1;
                    let sign = raw >> (f.width().bits() - 1) & 1;
                    let mant = raw & ((1u64 << mw) - 1);
                    sign << 63 | 0x7ffu64 << 52 | mant << (52 - mw)
                } else {
                    f.convert(FpFormat::F64, RoundingMode::Rne, v)
                        .ok()
                        .and_then(|b| b.to_u64())
                        .unwrap_or(0)
                };
                format!("0x{d:016X}")
            }
        }
    };
    if nan || inf {
        let what = if nan {
            "NaN"
        } else if v.msb() {
            "-inf"
        } else {
            "+inf"
        };
        return format!("{} ({what})", hex());
    }
    // Exact decimal of m·2^e when short.
    let Ok(d) = f.convert(FpFormat::F64, RoundingMode::Rne, v) else {
        return hex();
    };
    let x = f64::from_bits(d.to_u64().unwrap_or(0));
    let back = FpFormat::F64.convert(f, RoundingMode::Rne, &d).ok();
    if back.as_ref() != Some(v) {
        return hex();
    }
    match exact_decimal(x) {
        Some(s) => s,
        None => hex(),
    }
}

/// The exact decimal expansion of `x` when it has at most 17 significant digits.
fn exact_decimal(x: f64) -> Option<String> {
    if x == 0.0 {
        return Some(if x.is_sign_negative() { "-0.0" } else { "0.0" }.into());
    }
    let bits = x.to_bits();
    let neg = bits >> 63 == 1;
    let exp = ((bits >> 52) & 0x7ff) as i32;
    let frac = bits & ((1u64 << 52) - 1);
    let (mut m, mut e) = if exp == 0 {
        (frac, -1074)
    } else {
        (frac | 1 << 52, exp - 1075)
    };
    while m & 1 == 0 && m != 0 {
        m >>= 1;
        e += 1;
    }
    let digits: String;
    let point: i32; // digits after the decimal point
    if e >= 0 {
        if e > 60 {
            return None;
        }
        let v = u128::from(m).checked_shl(e as u32)?;
        digits = v.to_string();
        point = 0;
    } else {
        let k = (-e) as u32;
        if k > 24 {
            return None;
        }
        let v = u128::from(m).checked_mul(5u128.checked_pow(k)?)?;
        digits = v.to_string();
        point = k as i32;
    }
    let significant = digits.trim_start_matches('0').trim_end_matches('0').len();
    if significant > 17 {
        return None;
    }
    let s = if point == 0 {
        format!("{digits}.0")
    } else {
        let p = point as usize;
        let padded = if digits.len() <= p {
            format!("{}{digits}", "0".repeat(p - digits.len() + 1))
        } else {
            digits
        };
        let (int, fr) = padded.split_at(padded.len() - p);
        let fr = fr.trim_end_matches('0');
        format!("{int}.{}", if fr.is_empty() { "0" } else { fr })
    };
    Some(if neg { format!("-{s}") } else { s })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn literals() {
        let w8 = |s| int_literal(s, 8).map(|v| v.to_u64().unwrap());
        assert_eq!(w8("255"), Some(255));
        assert_eq!(w8("-128"), Some(128));
        assert_eq!(w8("-1"), Some(255));
        assert_eq!(w8("0x7f"), Some(127));
        assert_eq!(w8("256"), None);
        assert_eq!(w8("-129"), None);
        assert_eq!(int_literal("-1", 1).map(|v| v.to_u64().unwrap()), Some(1));
        assert_eq!(int_literal("2", 1), None);
        let f = |s, fmt| float_literal(s, fmt).map(|v| v.to_u64().unwrap());
        assert_eq!(f("1.0", FpFormat::F32), Some(0x3f80_0000));
        assert_eq!(f("-0.0", FpFormat::F32), Some(0x8000_0000));
        assert_eq!(f("0x3FF0000000000000", FpFormat::F32), Some(0x3f80_0000));
        assert_eq!(f("0.1", FpFormat::F32), None, "not exact in binary32");
        assert_eq!(f("0xH3C00", FpFormat::F16), Some(0x3c00));
        assert_eq!(f("1.5", FpFormat::F64), Some(1.5f64.to_bits()));
    }

    #[test]
    fn constants() {
        let f32v = |x: f32| BitVec::from_f32(x);
        assert_eq!(float_text(FpFormat::F32, &f32v(1.5)), "1.5");
        assert_eq!(float_text(FpFormat::F32, &f32v(-0.0)), "-0.0");
        assert_eq!(float_text(FpFormat::F32, &f32v(3.0)), "3.0");
        assert_eq!(float_text(FpFormat::F32, &f32v(0.1)), "0x3FB99999A0000000");
        assert_eq!(
            float_text(FpFormat::F32, &f32v(f32::INFINITY)),
            "0x7FF0000000000000 (+inf)"
        );
        assert_eq!(
            ir_constant(Ty::Int(8), &BitVec::from_u64(Width::W8, 0x80).unwrap()),
            "i8 -128"
        );
        assert_eq!(ir_constant(Ty::Int(1), &BitVec::from_bool(true)), "i1 true");
    }
}
