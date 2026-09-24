//! binary32 and binary64 under round-to-nearest-even against the host's IEEE 754 arithmetic.
//!
//! Results must be bit-identical, except that when the host produces a NaN the oracle must
//! produce the canonical NaN (hosts propagate payloads; the contract does not). `rem` is checked
//! against a remainder derived from the host's exact `fmod` (`%`), and float-to-integer
//! conversions against Rust's saturating `as` casts (truncation, NaN to 0).

use super::*;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

/// Random inputs per suite and format.
const PAIRS: usize = 150_000;

trait Host:
    Copy
    + std::fmt::Debug
    + PartialEq
    + PartialOrd
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + Neg<Output = Self>
{
    const F: Format;
    fn from_raw(b: u64) -> Self;
    fn raw(self) -> u64;
    fn two() -> Self;
    fn nan_(self) -> bool;
    fn inf_(self) -> bool;
    fn normal_(self) -> bool;
    fn subnormal_(self) -> bool;
    fn sign_negative_(self) -> bool;
    fn sqrt_(self) -> Self;
    fn mul_add_(self, b: Self, c: Self) -> Self;
    fn round_ties_even_(self) -> Self;
    fn floor_(self) -> Self;
    fn ceil_(self) -> Self;
    fn trunc_(self) -> Self;
    fn round_(self) -> Self;
    fn abs_(self) -> Self;
    fn copysign_(self, sign: Self) -> Self;
    fn min_(self, o: Self) -> Self;
    fn max_(self, o: Self) -> Self;
}

macro_rules! host_impl {
    ($t:ty, $f:expr, $u:ty) => {
        impl Host for $t {
            const F: Format = $f;
            fn from_raw(b: u64) -> Self {
                <$t>::from_bits(b as $u)
            }
            fn raw(self) -> u64 {
                self.to_bits().into()
            }
            fn two() -> Self {
                2.0
            }
            fn nan_(self) -> bool {
                self.is_nan()
            }
            fn inf_(self) -> bool {
                self.is_infinite()
            }
            fn normal_(self) -> bool {
                self.is_normal()
            }
            fn subnormal_(self) -> bool {
                self.is_subnormal()
            }
            fn sign_negative_(self) -> bool {
                self.is_sign_negative()
            }
            fn sqrt_(self) -> Self {
                self.sqrt()
            }
            fn mul_add_(self, b: Self, c: Self) -> Self {
                self.mul_add(b, c)
            }
            fn round_ties_even_(self) -> Self {
                self.round_ties_even()
            }
            fn floor_(self) -> Self {
                self.floor()
            }
            fn ceil_(self) -> Self {
                self.ceil()
            }
            fn trunc_(self) -> Self {
                self.trunc()
            }
            fn round_(self) -> Self {
                self.round()
            }
            fn abs_(self) -> Self {
                self.abs()
            }
            fn copysign_(self, sign: Self) -> Self {
                self.copysign(sign)
            }
            fn min_(self, o: Self) -> Self {
                self.min(o)
            }
            fn max_(self, o: Self) -> Self {
                self.max(o)
            }
        }
    };
}

host_impl!(f32, B32, u32);
host_impl!(f64, B64, u64);

fn hb<T: Host>(x: T) -> Bits {
    bw(T::F.width(), x.raw().into())
}

/// Bit-identical to the host, or the canonical NaN where the host gives a NaN.
fn agrees<T: Host>(got: &Bits, want: T) -> bool {
    if want.nan_() {
        *got == canonical_nan(T::F)
    } else {
        val(got) == u128::from(want.raw())
    }
}

/// IEEE `remainder(a, b)` for finite `a` and finite nonzero `b`, from the host's exact `fmod`.
///
/// `r2 = fmod(a, 2|b|)` is exact and has `a`'s sign; `a / |b| = 2 · trunc(a / 2|b|) + r2 / |b|`
/// with an even first term, so the nearest integer (ties to even) only depends on
/// `x = |r2| / |b|` in `[0, 2)`: 0 up to `1/2` inclusive, 1 up to `3/2` exclusive, else 2. Every
/// subtraction below is exact by Sterbenz's lemma. When `2|b|` overflows, `fmod(a, ∞) = a` is
/// still right because then `|a| < 2|b|`.
fn host_remainder<T: Host>(a: T, b: T) -> T {
    let ab = b.abs_();
    let r2 = a % (T::two() * ab);
    let x = r2.abs_();
    let mag = if x >= ab {
        let d = x - ab;
        if T::two() * d < ab { d } else { d - ab }
    } else if T::two() * x <= ab {
        x
    } else {
        x - ab
    };
    if r2.sign_negative_() { -mag } else { mag }
}

fn width_mask(f: Format) -> u64 {
    if f.width() == 64 {
        u64::MAX
    } else {
        (1u64 << f.width()) - 1
    }
}

fn arithmetic_against_host<T: Host>(seed: u64) {
    let f = T::F;
    let rm = Rm::Rne;
    let mut rng = Rng(seed);
    for _ in 0..PAIRS {
        let ra = rng.value(f);
        let rb = if rng.coin() {
            rng.related(f, ra)
        } else {
            rng.value(f)
        };
        let (x, y) = (T::from_raw(ra), T::from_raw(rb));
        let (a, b) = (hb(x), hb(y));
        let check = |op: &str, got: Bits, want: T| {
            assert!(
                agrees(&got, want),
                "{op}({x:?} [{ra:#x}], {y:?} [{rb:#x}]): got {:#x}, host {want:?} [{:#x}]",
                val(&got),
                want.raw()
            );
        };
        check("add", add(f, rm, &a, &b), x + y);
        check("sub", sub(f, rm, &a, &b), x - y);
        check("mul", mul(f, rm, &a, &b), x * y);
        check("div", div(f, rm, &a, &b), x / y);
        check("sqrt", sqrt(f, rm, &a), x.sqrt_());

        // fma: an unrelated addend, one related to b, or about -(x * y) for cancellation.
        let rc = match rng.below(4) {
            0 | 1 => rng.value(f),
            2 => rng.related(f, rb),
            _ => {
                let p = (-(x * y)).raw();
                p.wrapping_add(rng.below(5)).wrapping_sub(2) & width_mask(f)
            }
        };
        let z = T::from_raw(rc);
        let got = fma(f, rm, &a, &b, &hb(z));
        let want = x.mul_add_(y, z);
        assert!(
            agrees(&got, want),
            "fma({x:?}, {y:?}, {z:?}) [{ra:#x}, {rb:#x}, {rc:#x}]: got {:#x}, host {want:?} [{:#x}]",
            val(&got),
            want.raw()
        );

        assert_eq!(eq(f, &a, &b), x == y, "eq({x:?}, {y:?})");
        assert_eq!(lt(f, &a, &b), x < y, "lt({x:?}, {y:?})");
        assert_eq!(le(f, &a, &b), x <= y, "le({x:?}, {y:?})");

        let finite = |v: T| !v.nan_() && !v.inf_();
        if finite(x) && finite(y) && y != T::from_raw(0) {
            check("rem", rem(f, &a, &b), host_remainder(x, y));
        }
        // The host's min/max leave the order of -0 and +0 unspecified.
        if !(x == T::from_raw(0) && y == T::from_raw(0)) {
            check("min", min(f, &a, &b), x.min_(y));
            check("max", max(f, &a, &b), x.max_(y));
        }

        // Sign-bit operations keep NaN payloads: compare every bit.
        assert_eq!(val(&neg(f, &a)), u128::from((-x).raw()), "neg({x:?})");
        assert_eq!(val(&abs(f, &a)), u128::from(x.abs_().raw()), "abs({x:?})");
        assert_eq!(
            val(&copysign(f, &a, &b)),
            u128::from(x.copysign_(y).raw()),
            "copysign({x:?}, {y:?})"
        );

        assert_eq!(is_nan(f, &a), x.nan_(), "is_nan({x:?})");
        assert_eq!(is_infinite(f, &a), x.inf_(), "is_infinite({x:?})");
        assert_eq!(is_zero(f, &a), x == T::from_raw(0), "is_zero({x:?})");
        assert_eq!(is_normal(f, &a), x.normal_(), "is_normal({x:?})");
        assert_eq!(is_subnormal(f, &a), x.subnormal_(), "is_subnormal({x:?})");
        assert_eq!(
            is_negative(f, &a),
            x.sign_negative_() && !x.nan_(),
            "is_negative({x:?})"
        );
        assert_eq!(
            is_positive(f, &a),
            !x.sign_negative_() && !x.nan_(),
            "is_positive({x:?})"
        );
    }
}

#[test]
fn binary32_arithmetic_matches_host() {
    arithmetic_against_host::<f32>(0x0123_4567_89ab_cdef);
}

#[test]
fn binary64_arithmetic_matches_host() {
    arithmetic_against_host::<f64>(0xfedc_ba98_7654_3210);
}

/// A value near the integers: a random encoding, a multiple of 1/2 or 1/4 (ties), an integer
/// plus or minus a few ulps, or a value whose binade makes its last bits the fraction.
fn near_integer<T: Host>(rng: &mut Rng) -> T {
    let f = T::F;
    let sb = u64::from(f.sb);
    let bias = (1u64 << (f.eb - 1)) - 1;
    match rng.below(5) {
        0 => T::from_raw(rng.value(f)),
        1 | 2 => {
            // k / 4 for small k, exactly (built from bits: k · 2^-2 with k < 2^12).
            let k = rng.below(1 << 12);
            let v = if k == 0 {
                0
            } else {
                let e = 63 - u64::from(k.leading_zeros()); // floor(log2 k)
                let t = (k << (sb - 1 - e)) & ((1 << (sb - 1)) - 1);
                ((bias + e - 2) << (sb - 1)) | t
            };
            let s = u64::from(rng.coin()) << (f.width() - 1);
            let v = (s | v).wrapping_add(rng.below(3)).wrapping_sub(1) & width_mask(f);
            T::from_raw(v)
        }
        _ => {
            // A binade near p, where the ones digit and the fraction share the significand.
            let e = bias + sb - 4 + rng.below(6);
            let t = rng.next() & ((1 << (sb - 1)) - 1);
            let s = u64::from(rng.coin()) << (f.width() - 1);
            T::from_raw(s | (e << (sb - 1)) | t)
        }
    }
}

fn round_to_integral_against_host<T: Host>(seed: u64) {
    let f = T::F;
    let mut rng = Rng(seed);
    for _ in 0..PAIRS {
        let x: T = near_integer(&mut rng);
        let a = hb(x);
        for (rm, want) in [
            (Rm::Rne, x.round_ties_even_()),
            (Rm::Rna, x.round_()),
            (Rm::Rtp, x.ceil_()),
            (Rm::Rtn, x.floor_()),
            (Rm::Rtz, x.trunc_()),
        ] {
            let got = round_to_integral(f, rm, &a);
            assert!(
                agrees(&got, want),
                "round_to_integral({rm:?}, {x:?} [{:#x}]): got {:#x}, host {want:?}",
                x.raw(),
                val(&got)
            );
        }
    }
}

#[test]
fn binary32_round_to_integral_matches_host() {
    round_to_integral_against_host::<f32>(0x5eed_0001);
}

#[test]
fn binary64_round_to_integral_matches_host() {
    round_to_integral_against_host::<f64>(0x5eed_0002);
}

#[test]
fn binary32_binary64_conversions_match_host() {
    let mut rng = Rng(0x5eed_0003);
    for _ in 0..PAIRS {
        // binary64 -> binary32: a binary32 value widened, then its 29 extra bits disturbed
        // (ties, near-ties, sticky bits), or any binary64 value.
        let x = if rng.coin() {
            f64::from_bits(rng.value(B64))
        } else {
            let base = f64::from(f32::from_bits(rng.value(B32) as u32)).to_bits();
            let low = match rng.below(4) {
                0 => 1 << 28,
                1 => (1 << 28) + rng.below(3) - 1,
                _ => rng.next() & ((1 << 29) - 1),
            };
            f64::from_bits(base ^ low)
        };
        let got = to_fp(B64, B32, Rm::Rne, &f64b(x));
        assert!(
            agrees(&got, x as f32),
            "to_fp(b64 -> b32, {x:e} [{:#x}]): got {:#x}",
            x.to_bits(),
            val(&got)
        );
        // binary32 -> binary64 is exact in every mode.
        let y = f32::from_bits(rng.value(B32) as u32);
        for rm in Rm::ALL {
            let got = to_fp(B32, B64, rm, &f32b(y));
            assert!(agrees(&got, f64::from(y)), "to_fp(b32 -> b64, {y:e})");
        }
    }
}

/// Random integers biased toward small values, extremes, powers of two and their neighbours,
/// and odd multiples shifted so that their last bits are exact halves after rounding.
fn gen_u128(rng: &mut Rng) -> u128 {
    let r = (u128::from(rng.next()) << 64) | u128::from(rng.next());
    match rng.below(8) {
        0 => u128::from(rng.below(1000)),
        1 => u128::MAX - u128::from(rng.below(4)),
        2 => (1u128 << rng.below(128))
            .wrapping_add(u128::from(rng.below(5)))
            .wrapping_sub(2),
        3 => r >> rng.below(128),
        4 => (u128::from(rng.next() >> 9) | 1) << rng.below(60), // 55-bit odd numbers
        5 => (u128::from(rng.next() >> 38) | 1) << rng.below(90), // 26-bit odd numbers
        _ => r,
    }
}

/// `(x as T)` for the integer type of width `w` and signedness `signed` holding `x`'s low bits.
fn host_int_to_float(x: u128, w: u16, signed: bool) -> (f32, f64) {
    macro_rules! conv {
        ($t:ty) => {{
            let v = x as $t;
            (v as f32, v as f64)
        }};
    }
    match (w, signed) {
        (8, false) => conv!(u8),
        (8, true) => conv!(i8),
        (16, false) => conv!(u16),
        (16, true) => conv!(i16),
        (32, false) => conv!(u32),
        (32, true) => conv!(i32),
        (64, false) => conv!(u64),
        (64, true) => conv!(i64),
        (128, false) => conv!(u128),
        (128, true) => conv!(i128),
        _ => unreachable!(),
    }
}

#[test]
fn integer_to_float_matches_host() {
    let mut rng = Rng(0x5eed_0004);
    for _ in 0..PAIRS {
        let x = gen_u128(&mut rng);
        for w in [8u16, 16, 32, 64, 128] {
            let xw = if w == 128 { x } else { x & ((1u128 << w) - 1) };
            for signed in [false, true] {
                let (h32, h64) = host_int_to_float(xw, w, signed);
                let conv = if signed { from_sint } else { from_uint };
                let (g32, g64) = (
                    conv(B32, Rm::Rne, &bw(w, xw)),
                    conv(B64, Rm::Rne, &bw(w, xw)),
                );
                assert!(agrees(&g32, h32), "w={w} signed={signed} {xw:#x} -> b32");
                assert!(agrees(&g64, h64), "w={w} signed={signed} {xw:#x} -> b64");
            }
        }
    }
}

/// `(x as int)` (truncation, saturation, NaN to 0) for the integer type of width `w`, as the
/// integer's `w`-bit pattern.
fn host_float_to_int(x: f64, w: u16, signed: bool) -> u128 {
    let m = if w == 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    };
    let v = match (w, signed) {
        (8, false) => (x as u8).into(),
        (8, true) => (x as i8) as u128,
        (16, false) => (x as u16).into(),
        (16, true) => (x as i16) as u128,
        (32, false) => (x as u32).into(),
        (32, true) => (x as i32) as u128,
        (64, false) => (x as u64).into(),
        (64, true) => (x as i64) as u128,
        (128, false) => x as u128,
        (128, true) => (x as i128) as u128,
        _ => unreachable!(),
    };
    v & m
}

#[test]
fn float_to_integer_matches_host() {
    let mut rng = Rng(0x5eed_0005);
    for _ in 0..PAIRS {
        // Magnitudes spread over the integer ranges: exponents -4 to 132, plus the usual specials.
        let x64 = if rng.below(4) == 0 {
            f64::from_bits(rng.value(B64))
        } else {
            let e = 1023 - 4 + rng.below(137);
            let t = rng.next() & ((1 << 52) - 1);
            f64::from_bits((u64::from(rng.coin()) << 63) | (e << 52) | t)
        };
        let x32 = x64 as f32;
        for w in [8u16, 16, 32, 64, 128] {
            for signed in [false, true] {
                let conv = if signed { to_sint } else { to_uint };
                let got = conv(B64, Rm::Rtz, &f64b(x64), w);
                assert_eq!(
                    val(&got),
                    host_float_to_int(x64, w, signed),
                    "{x64:e} [{:#x}] -> w={w} signed={signed}",
                    x64.to_bits()
                );
                let got = conv(B32, Rm::Rtz, &f32b(x32), w);
                assert_eq!(
                    val(&got),
                    host_float_to_int(f64::from(x32), w, signed),
                    "{x32:e} (b32) -> w={w} signed={signed}"
                );
            }
        }
    }
}

/// The host value of a binary16 or bfloat16 encoding, from its fields (exact in binary64).
fn narrow_value(f: Format, bits: u128) -> f64 {
    let (eb, sb) = (i32::from(f.eb), i32::from(f.sb));
    let bias = (1 << (eb - 1)) - 1;
    let s = if bits >> (eb + sb - 1) == 1 {
        -1.0
    } else {
        1.0
    };
    let e = ((bits >> (sb - 1)) & ((1 << eb) - 1)) as i32;
    let t = (bits & ((1 << (sb - 1)) - 1)) as f64;
    let hidden = f64::from(1u32 << (sb - 1));
    if e == (1 << eb) - 1 {
        if t == 0.0 {
            s * f64::INFINITY
        } else {
            f64::NAN
        }
    } else if e == 0 {
        s * t * 2f64.powi(2 - bias - sb)
    } else {
        s * (hidden + t) * 2f64.powi(e - bias - sb + 1)
    }
}

#[test]
fn narrow_formats_widen_exactly() {
    // Every binary16 and bfloat16 value converts to binary64 exactly (in every mode) and back.
    for f in [B16, BF16] {
        for bits in 0..(1u128 << 16) {
            let a = bw(16, bits);
            let v = narrow_value(f, bits);
            for rm in Rm::ALL {
                let wide = to_fp(f, B64, rm, &a);
                assert!(agrees(&wide, v), "{f:?} {bits:#x} -> binary64 ({rm:?})");
                let back = to_fp(B64, f, rm, &wide);
                if v.is_nan() {
                    assert_eq!(back, canonical_nan(f));
                } else {
                    assert_eq!(back, a, "{f:?} {bits:#x} round trip ({rm:?})");
                }
            }
        }
    }
}

/// binary16 and bfloat16 add, sub, mul, div and sqrt under RNE, through the host's binary64:
/// the host's correctly rounded binary64 result, narrowed by `to_fp` (checked against the host
/// by the binary64 -> binary32 test), must equal the oracle's direct result. Rounding to nearest
/// twice is innocuous for these operations when the intermediate precision is at least `2p + 2`
/// (53 >= 2 * 11 + 2) and the intermediate exponent range contains the narrow one.
#[test]
fn narrow_arithmetic_matches_host_binary64() {
    let mut rng = Rng(0x5eed_0006);
    let rm = Rm::Rne;
    for f in [B16, BF16] {
        let narrow = |x: f64| to_fp(B64, f, rm, &f64b(x));
        for _ in 0..PAIRS / 2 {
            let (ra, rb) = (
                u128::from(rng.next() & 0xffff),
                u128::from(rng.next() & 0xffff),
            );
            let (a, b) = (bw(16, ra), bw(16, rb));
            let (x, y) = (narrow_value(f, ra), narrow_value(f, rb));
            let cases = [
                ("add", add(f, rm, &a, &b), x + y),
                ("sub", sub(f, rm, &a, &b), x - y),
                ("mul", mul(f, rm, &a, &b), x * y),
                ("div", div(f, rm, &a, &b), x / y),
                ("sqrt", sqrt(f, rm, &a), x.sqrt()),
            ];
            for (op, got, host) in cases {
                assert_eq!(got, narrow(host), "{f:?} {op}({ra:#x}, {rb:#x})");
            }
        }
    }
}

/// Wide formats against the host: binary32 operands computed in x87's (15, 64), binary128 or
/// binary64, and binary64 operands computed in binary128 or (15, 497), then narrowed by `to_fp`
/// under RNE, must give the host's result. Each wide precision is at least `2p + 2` for its
/// narrow format, which makes the double rounding of add, sub, mul, div and sqrt innocuous;
/// `rem` and roundToIntegral are exact in both formats.
fn wide_against_host<T: Host>(wide: Format, seed: u64, n: usize) {
    let f = T::F;
    let rne = Rm::Rne;
    let mut rng = Rng(seed);
    let widen = |x: T| {
        let w = to_fp(f, wide, rne, &hb(x));
        assert!(
            agrees(&to_fp(wide, f, Rm::Rtz, &w), x),
            "widening {x:?} is exact"
        );
        w
    };
    for _ in 0..n {
        let ra = rng.value(f);
        let rb = if rng.coin() {
            rng.related(f, ra)
        } else {
            rng.value(f)
        };
        let (x, y) = (T::from_raw(ra), T::from_raw(rb));
        let (a, b) = (widen(x), widen(y));
        let narrow = |r: Bits| to_fp(wide, f, rne, &r);
        let check = |op: &str, got: Bits, want: T| {
            assert!(
                agrees(&got, want),
                "{wide:?} {op}({x:?}, {y:?}): got {:#x}, host {want:?}",
                val(&got)
            );
        };
        check("add", narrow(add(wide, rne, &a, &b)), x + y);
        check("sub", narrow(sub(wide, rne, &a, &b)), x - y);
        check("mul", narrow(mul(wide, rne, &a, &b)), x * y);
        check("div", narrow(div(wide, rne, &a, &b)), x / y);
        check("sqrt", narrow(sqrt(wide, rne, &a)), x.sqrt_());
        if !x.nan_() && !x.inf_() && !y.nan_() && !y.inf_() && y != T::from_raw(0) {
            check("rem", narrow(rem(wide, &a, &b)), host_remainder(x, y));
        }
        for (rm, want) in [
            (Rm::Rne, x.round_ties_even_()),
            (Rm::Rna, x.round_()),
            (Rm::Rtp, x.ceil_()),
            (Rm::Rtn, x.floor_()),
            (Rm::Rtz, x.trunc_()),
        ] {
            check("rti", narrow(round_to_integral(wide, rm, &a)), want);
        }
        assert_eq!(lt(wide, &a, &b), x < y);
        assert_eq!(eq(wide, &a, &b), x == y);
    }
}

#[test]
fn x87_and_binary128_match_host_on_binary32() {
    wide_against_host::<f32>(X87V, 0x5eed_000b, 20_000);
    wide_against_host::<f32>(B128, 0x5eed_000c, 10_000);
    wide_against_host::<f32>(B64, 0x5eed_000d, 20_000);
}

#[test]
fn binary128_and_512_bit_match_host_on_binary64() {
    wide_against_host::<f64>(B128, 0x5eed_000e, 10_000);
    wide_against_host::<f64>(Format { eb: 15, sb: 497 }, 0x5eed_000f, 2_000);
}
