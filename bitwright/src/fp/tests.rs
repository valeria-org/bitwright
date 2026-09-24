//! Tests of the floating-point arithmetic: the two integer frames against each other, binary32
//! and binary64 against the host's hardware under round-to-nearest-even, the narrow and the wide
//! frame on the same formats under every mode, and hand-checked special cases. The independent
//! reference in `bitwright-ref` checks every mode against the specification itself.

use super::frame::testing::{big, to_u128};
use super::frame::{self, Frame, Mid, Wide};
use super::soft;
use super::*;
use crate::testutil::Rng;

// ---------------------------------------------------------------------------------------------
// Frames

#[test]
fn the_wide_frame_agrees_with_u128() {
    let mut rng = Rng(1);
    for _ in 0..20_000 {
        let bits_a = 1 + rng.below(127) as u32;
        let bits_b = 1 + rng.below(127) as u32;
        let a = (u128::from(rng.next()) << 64 | u128::from(rng.next())) >> (128 - bits_a);
        let b = (u128::from(rng.next()) << 64 | u128::from(rng.next())) >> (128 - bits_b);
        let (ba, bb) = (big(a), big(b));
        assert_eq!(ba.bits(), a.bits(), "{a:#x}");
        assert_eq!(ba.cmp(&bb), a.cmp(&b));
        if let Some(s) = a.checked_add(b) {
            assert_eq!(to_u128(ba.add(bb)), s);
        }
        let (hi, lo) = if a >= b { (a, b) } else { (b, a) };
        assert_eq!(to_u128(big(hi).sub(big(lo))), hi - lo);
        if let Some(p) = a.checked_mul(b) {
            assert_eq!(to_u128(ba.mul(bb)), p, "{a:#x} * {b:#x}");
        }
        if let (Some(q), Some(r)) = (a.checked_div(b), a.checked_rem(b)) {
            let (bq, br) = ba.divrem(bb);
            assert_eq!((to_u128(bq), to_u128(br)), (q, r), "{a:#x} / {b:#x}");
            assert_eq!(to_u128(ba.mul_mod(big(r), bb)), a.mul_mod(r, b));
        }
        let n = rng.below(140) as u32;
        assert_eq!(to_u128(ba.shr(n)), a.shr(n));
        assert_eq!(to_u128(ba.low(n)), a.low(n));
        assert_eq!(to_u128(ba.shr_jam(n)), a.shr_jam(n));
        if n < 128 && a.leading_zeros() >= n {
            assert_eq!(to_u128(ba.shl(n)), a << n);
        }
        assert_eq!(to_u128(ba.isqrt()), a.isqrt());
    }
}

#[test]
fn wide_division_and_roots_are_exact() {
    let mut rng = Rng(2);
    let random = |rng: &mut Rng, bits: u32| {
        let limbs: Vec<u64> = (0..bits.div_ceil(64)).map(|_| rng.next()).collect();
        Wide::from_limbs(&limbs).low(bits)
    };
    for _ in 0..3_000 {
        let (bits_a, bits_b) = (1 + rng.below(1_000) as u32, 1 + rng.below(600) as u32);
        let a = random(&mut rng, bits_a);
        let b = random(&mut rng, bits_b);
        if b.is_zero() {
            continue;
        }
        let (q, r) = a.divrem(b);
        assert!(r < b);
        assert_eq!(q.mul(b).add(r), a);
        let s = a.isqrt();
        assert!(s.mul(s) <= a);
        let s1 = s.add(Wide::one());
        assert!(s1.mul(s1) > a);
    }
}

// ---------------------------------------------------------------------------------------------
// Samples

/// A random encoding of `f`, biased toward the values arithmetic treats specially: zeros,
/// subnormals, the boundaries of the exponent range, infinities, NaNs, significands with few
/// bits set (ties) or all set.
pub(crate) fn sample(rng: &mut Rng, f: FpFormat) -> BitVec {
    let (eb, sb) = (f.eb(), f.sb());
    let w = f.width();
    if rng.chance(1, 5) {
        let limbs: Vec<u64> = (0..8).map(|_| rng.next()).collect();
        return BitVec::wrapping_from_limbs(w, &limbs);
    }
    let e_max = Wide::pow2(eb).sub(Wide::one());
    let bias = Wide::pow2(eb - 1).sub(Wide::one());
    let e = match rng.below(9) {
        0 => Wide::zero(),
        1 => Wide::one(),
        2 => e_max,
        3 => e_max.sub(Wide::one()),
        4 => bias,
        5 => bias.add(Wide::from_u64(rng.below(4))),
        6 => bias.sub(Wide::from_u64(rng.below(4).min(bias.bits().into()))),
        _ => Wide::from_u64(rng.next()).low(eb),
    };
    let t_bits = sb - 1;
    let limbs: Vec<u64> = (0..8).map(|_| rng.next()).collect();
    let rand_t = Wide::from_limbs(&limbs).low(t_bits);
    let t = match rng.below(8) {
        0 => Wide::zero(),
        1 => Wide::one(),
        2 => Wide::pow2(t_bits).sub(Wide::one()),
        3 => Wide::pow2(t_bits - 1),
        4 => rand_t.shr(t_bits / 2).shl(t_bits / 2),
        5 => Wide::pow2(t_bits - 1).add(Wide::one()).low(t_bits),
        _ => rand_t,
    };
    let sign = if rng.chance(1, 2) {
        Wide::pow2(eb + sb - 1)
    } else {
        Wide::zero()
    };
    let x = sign.add(e.shl(sb - 1)).add(t);
    let mut l = [0u64; 8];
    x.write_limbs(&mut l);
    BitVec::wrapping_from_limbs(w, &l)
}

// ---------------------------------------------------------------------------------------------
// Against the hardware (binary32 and binary64, round to nearest even)

fn assert_f32(ours: BitVec, hw: f32, what: &str) {
    if hw.is_nan() {
        assert_eq!(
            ours,
            FpFormat::F32.nan(),
            "{what}: expected the canonical NaN"
        );
    } else {
        assert_eq!(
            ours.to_f32().unwrap().to_bits(),
            hw.to_bits(),
            "{what}: ours {:?} hardware {hw:?}",
            ours.to_f32().unwrap()
        );
    }
}

fn assert_f64(ours: BitVec, hw: f64, what: &str) {
    if hw.is_nan() {
        assert_eq!(
            ours,
            FpFormat::F64.nan(),
            "{what}: expected the canonical NaN"
        );
    } else {
        assert_eq!(
            ours.to_f64().unwrap().to_bits(),
            hw.to_bits(),
            "{what}: ours {:?} hardware {hw:?}",
            ours.to_f64().unwrap()
        );
    }
}

#[test]
fn binary32_matches_the_hardware() {
    let f = FpFormat::F32;
    let rne = RoundingMode::Rne;
    let mut rng = Rng(3);
    for _ in 0..60_000 {
        let (a, b, c) = (
            sample(&mut rng, f),
            sample(&mut rng, f),
            sample(&mut rng, f),
        );
        let (x, y, z) = (
            a.to_f32().unwrap(),
            b.to_f32().unwrap(),
            c.to_f32().unwrap(),
        );
        let what = format!("{x:e} ({:#x}), {y:e} ({:#x})", x.to_bits(), y.to_bits());
        assert_f32(f.add(rne, &a, &b).unwrap(), x + y, &format!("add {what}"));
        assert_f32(f.sub(rne, &a, &b).unwrap(), x - y, &format!("sub {what}"));
        assert_f32(f.mul(rne, &a, &b).unwrap(), x * y, &format!("mul {what}"));
        assert_f32(f.div(rne, &a, &b).unwrap(), x / y, &format!("div {what}"));
        assert_f32(f.sqrt(rne, &a).unwrap(), x.sqrt(), &format!("sqrt {what}"));
        assert_f32(
            f.fma(rne, &a, &b, &c).unwrap(),
            x.mul_add(y, z),
            &format!("fma {what}, {z:e}"),
        );
        assert_f32(
            f.round_to_integral(RoundingMode::Rne, &a).unwrap(),
            x.round_ties_even(),
            &format!("rne {what}"),
        );
        assert_f32(
            f.round_to_integral(RoundingMode::Rna, &a).unwrap(),
            x.round(),
            "rna",
        );
        assert_f32(
            f.round_to_integral(RoundingMode::Rtp, &a).unwrap(),
            x.ceil(),
            "rtp",
        );
        assert_f32(
            f.round_to_integral(RoundingMode::Rtn, &a).unwrap(),
            x.floor(),
            "rtn",
        );
        assert_f32(
            f.round_to_integral(RoundingMode::Rtz, &a).unwrap(),
            x.trunc(),
            "rtz",
        );
        // Conversions: to binary64 exactly, back with rounding, integers both ways.
        assert_f64(
            f.convert(FpFormat::F64, rne, &a).unwrap(),
            f64::from(x),
            "to f64",
        );
        let i = rng.next() as i32 >> rng.below(32);
        let iv = BitVec::wrapping_from_u64(Width::W32, u64::from(i as u32));
        assert_f32(f.from_sint(rne, &iv), i as f32, &format!("from i32 {i}"));
        let u = rng.next() >> rng.below(64);
        let uv = BitVec::wrapping_from_u64(Width::W64, u);
        assert_f32(f.from_uint(rne, &uv), u as f32, &format!("from u64 {u}"));
        let rtz = RoundingMode::Rtz;
        assert_eq!(
            f.to_sint(rtz, &a, Width::W32).unwrap().to_u64(),
            Some(u64::from(x as i32 as u32)),
            "to i32 {what}"
        );
        assert_eq!(
            f.to_uint(rtz, &a, Width::W16).unwrap().to_u64(),
            Some(u64::from(x as u16)),
            "to u16 {what}"
        );
        assert_eq!(f.cmp(FpCmpOp::Lt, &a, &b).unwrap(), x < y, "lt {what}");
        assert_eq!(f.cmp(FpCmpOp::Eq, &a, &b).unwrap(), x == y, "eq {what}");
        assert_eq!(f.cmp(FpCmpOp::Ge, &a, &b).unwrap(), x >= y, "ge {what}");
    }
}

#[test]
fn binary64_matches_the_hardware() {
    let f = FpFormat::F64;
    let rne = RoundingMode::Rne;
    let mut rng = Rng(4);
    for _ in 0..60_000 {
        let (a, b, c) = (
            sample(&mut rng, f),
            sample(&mut rng, f),
            sample(&mut rng, f),
        );
        let (x, y, z) = (
            a.to_f64().unwrap(),
            b.to_f64().unwrap(),
            c.to_f64().unwrap(),
        );
        let what = format!("{x:e} ({:#x}), {y:e} ({:#x})", x.to_bits(), y.to_bits());
        assert_f64(f.add(rne, &a, &b).unwrap(), x + y, &format!("add {what}"));
        assert_f64(f.sub(rne, &a, &b).unwrap(), x - y, &format!("sub {what}"));
        assert_f64(f.mul(rne, &a, &b).unwrap(), x * y, &format!("mul {what}"));
        assert_f64(f.div(rne, &a, &b).unwrap(), x / y, &format!("div {what}"));
        assert_f64(f.sqrt(rne, &a).unwrap(), x.sqrt(), &format!("sqrt {what}"));
        assert_f64(
            f.fma(rne, &a, &b, &c).unwrap(),
            x.mul_add(y, z),
            &format!("fma {what}, {z:e} ({:#x})", z.to_bits()),
        );
        assert_f64(
            f.round_to_integral(rne, &a).unwrap(),
            x.round_ties_even(),
            "rne",
        );
        assert_f64(
            f.round_to_integral(RoundingMode::Rna, &a).unwrap(),
            x.round(),
            "rna",
        );
        assert_f64(
            f.round_to_integral(RoundingMode::Rtp, &a).unwrap(),
            x.ceil(),
            "rtp",
        );
        assert_f64(
            f.round_to_integral(RoundingMode::Rtn, &a).unwrap(),
            x.floor(),
            "rtn",
        );
        assert_f64(
            f.round_to_integral(RoundingMode::Rtz, &a).unwrap(),
            x.trunc(),
            "rtz",
        );
        assert_f32(
            f.convert(FpFormat::F32, rne, &a).unwrap(),
            x as f32,
            &format!("to f32 {what}"),
        );
        let i = rng.next() as i64 >> rng.below(64);
        let iv = BitVec::wrapping_from_u64(Width::W64, i as u64);
        assert_f64(f.from_sint(rne, &iv), i as f64, &format!("from i64 {i}"));
        let rtz = RoundingMode::Rtz;
        assert_eq!(
            f.to_sint(rtz, &a, Width::W64).unwrap().to_u64(),
            Some(x as i64 as u64),
            "to i64 {what}"
        );
        assert_eq!(
            f.to_uint(rtz, &a, Width::W32).unwrap().to_u64(),
            Some(u64::from(x as u32)),
            "to u32 {what}"
        );
        assert_eq!(f.cmp(FpCmpOp::Le, &a, &b).unwrap(), x <= y, "le {what}");
    }
}

// ---------------------------------------------------------------------------------------------
// The narrow and the wide frame agree, under every mode

/// Every operation under every mode, computed in the frame `S`.
fn all_ops<S: Frame>(f: FpFormat, a: &BitVec, b: &BitVec, c: &BitVec) -> Vec<BitVec> {
    let fm = f.fmt();
    let (x, y, z): (S, S, S) = (load(a), load(b), load(c));
    let mut out = Vec::new();
    for rm in RoundingMode::ALL {
        for r in [
            soft::add(&fm, rm, x, y),
            soft::mul(&fm, rm, x, y),
            soft::div(&fm, rm, x, y),
            soft::fma(&fm, rm, x, y, z),
            soft::sqrt(&fm, rm, x),
            soft::round_to_integral(&fm, rm, x),
        ] {
            out.push(store(f.width(), r));
        }
    }
    out.push(store(f.width(), soft::rem(&fm, x, y)));
    out
}

#[test]
fn every_frame_agrees() {
    let mut rng = Rng(5);
    let formats = [
        FpFormat::new(2, 2).unwrap(),
        FpFormat::new(2, 3).unwrap(),
        FpFormat::new(3, 4).unwrap(),
        FpFormat::new(4, 4).unwrap(),
        FpFormat::F16,
        FpFormat::BF16,
        FpFormat::F32,
        FpFormat::new(31, 29).unwrap(),
        FpFormat::F64,
        FpFormat::new(31, 61).unwrap(),
        FpFormat::X87,
        FpFormat::F128,
        FpFormat::new(20, 157).unwrap(),
    ];
    for &format in &formats {
        let p = format.sb();
        for _ in 0..2_000 {
            let (a, b, c) = (
                sample(&mut rng, format),
                sample(&mut rng, format),
                sample(&mut rng, format),
            );
            let wide = all_ops::<Wide>(format, &a, &b, &c);
            let what = format!("{format:?} {a} {b} {c}");
            if p <= frame::MID_PRECISION {
                assert_eq!(all_ops::<Mid>(format, &a, &b, &c), wide, "mid {what}");
            }
            if p <= frame::NARROW_PRECISION {
                assert_eq!(all_ops::<u128>(format, &a, &b, &c), wide, "u128 {what}");
            }
            if p <= frame::SMALL_PRECISION {
                assert_eq!(all_ops::<u64>(format, &a, &b, &c), wide, "u64 {what}");
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Hand-checked cases

fn tiny(eb: u32, sb: u32) -> FpFormat {
    FpFormat::new(eb, sb).unwrap()
}

fn bits(f: FpFormat, v: u64) -> BitVec {
    BitVec::wrapping_from_u64(f.width(), v)
}

#[test]
fn round_to_integral_overflows_in_a_format_too_small_for_its_integers() {
    // (2, 3): 3.5 is the largest finite value; toward +∞ and to nearest it rounds to 4, which
    // overflows, as z3 has it.
    let f = tiny(2, 3);
    let big = bits(f, 0b0_10_11);
    assert_eq!(
        f.round_to_integral(RoundingMode::Rtp, &big).unwrap(),
        f.inf(false)
    );
    assert_eq!(
        f.round_to_integral(RoundingMode::Rne, &big).unwrap(),
        f.inf(false)
    );
    assert_eq!(
        f.round_to_integral(RoundingMode::Rtz, &big).unwrap(),
        bits(f, 0b0_10_10)
    );
}

#[test]
fn signed_zeros_follow_the_zero_rule() {
    let f = FpFormat::F64;
    let one = BitVec::from_f64(1.0);
    let rtn = RoundingMode::Rtn;
    assert_eq!(f.sub(rtn, &one, &one).unwrap(), f.zero(true));
    assert_eq!(f.sub(RoundingMode::Rne, &one, &one).unwrap(), f.zero(false));
    let (pz, nz) = (f.zero(false), f.zero(true));
    assert_eq!(f.add(RoundingMode::Rne, &nz, &nz).unwrap(), nz);
    assert_eq!(f.add(RoundingMode::Rne, &pz, &nz).unwrap(), pz);
    assert_eq!(f.add(rtn, &pz, &nz).unwrap(), nz);
    // fma: an exactly zero product plus a zero of its sign keeps the sign.
    let m1 = BitVec::from_f64(-1.0);
    assert_eq!(f.fma(RoundingMode::Rne, &pz, &m1, &nz).unwrap(), nz);
    assert_eq!(f.fma(RoundingMode::Rne, &pz, &one, &nz).unwrap(), pz);
    assert_eq!(f.fma(rtn, &pz, &one, &nz).unwrap(), nz);
    // sqrt(−0) = −0; roundToIntegral keeps the sign of a zero result.
    assert_eq!(f.sqrt(RoundingMode::Rne, &nz).unwrap(), nz);
    let small_neg = BitVec::from_f64(-0.3);
    assert_eq!(
        f.round_to_integral(RoundingMode::Rne, &small_neg).unwrap(),
        nz
    );
}

#[test]
fn overflow_depends_on_the_mode() {
    let f = FpFormat::F32;
    let max = BitVec::from_f32(f32::MAX);
    let neg_max = BitVec::from_f32(-f32::MAX);
    let cases = [
        (RoundingMode::Rne, f32::INFINITY, f32::NEG_INFINITY),
        (RoundingMode::Rna, f32::INFINITY, f32::NEG_INFINITY),
        (RoundingMode::Rtz, f32::MAX, -f32::MAX),
        (RoundingMode::Rtp, f32::INFINITY, -f32::MAX),
        (RoundingMode::Rtn, f32::MAX, f32::NEG_INFINITY),
    ];
    for (rm, pos, neg) in cases {
        assert_eq!(f.add(rm, &max, &max).unwrap().to_f32(), Some(pos), "{rm:?}");
        assert_eq!(
            f.add(rm, &neg_max, &neg_max).unwrap().to_f32(),
            Some(neg),
            "{rm:?}"
        );
    }
}

#[test]
fn min_and_max_order_zeros_and_skip_nans() {
    let f = FpFormat::F32;
    let (pz, nz) = (f.zero(false), f.zero(true));
    let nan = f.nan();
    let signaling = BitVec::from_f32(f32::from_bits(0x7f80_0001));
    let one = BitVec::from_f32(1.0);
    assert_eq!(f.min(&pz, &nz).unwrap(), nz);
    assert_eq!(f.min(&nz, &pz).unwrap(), nz);
    assert_eq!(f.max(&nz, &pz).unwrap(), pz);
    assert_eq!(f.min(&nan, &one).unwrap(), one);
    assert_eq!(f.max(&one, &signaling).unwrap(), one);
    assert_eq!(f.min(&signaling, &nan).unwrap(), nan);
}

#[test]
fn integer_conversions_saturate() {
    let f = FpFormat::F64;
    let w8 = Width::W8;
    let rne = RoundingMode::Rne;
    let v = |x: f64| BitVec::from_f64(x);
    let si = |x: f64, rm| f.to_sint(rm, &v(x), w8).unwrap().to_u64().unwrap() as u8 as i8;
    let ui = |x: f64, rm| f.to_uint(rm, &v(x), w8).unwrap().to_u64().unwrap();
    assert_eq!(si(1e10, rne), 127);
    assert_eq!(si(-1e10, rne), -128);
    assert_eq!(si(-128.4, rne), -128);
    assert_eq!(si(-128.6, rne), -128);
    assert_eq!(si(127.5, rne), 127);
    assert_eq!(si(2.5, rne), 2);
    assert_eq!(si(2.5, RoundingMode::Rna), 3);
    assert_eq!(si(-2.5, RoundingMode::Rtp), -2);
    assert_eq!(si(f64::NAN, rne), 0);
    assert_eq!(si(f64::NEG_INFINITY, rne), -128);
    assert_eq!(ui(-0.4, rne), 0);
    assert_eq!(ui(-3.0, rne), 0);
    assert_eq!(ui(255.4, rne), 255);
    assert_eq!(ui(1e300, rne), 255);
    assert_eq!(ui(f64::INFINITY, rne), 255);
    // The most negative integer converts exactly.
    let min = BitVec::smin(Width::W64);
    assert_eq!(f.from_sint(rne, &min).to_f64(), Some(-(2f64.powi(63))));
    let one_bit = BitVec::ones(Width::W1);
    assert_eq!(f.from_sint(rne, &one_bit).to_f64(), Some(-1.0));
    assert_eq!(f.from_uint(rne, &one_bit).to_f64(), Some(1.0));
}

#[test]
fn remainder_rounds_its_quotient_to_even() {
    let f = FpFormat::F64;
    let r = |a: f64, b: f64| f.rem(&BitVec::from_f64(a), &BitVec::from_f64(b)).unwrap();
    assert_eq!(r(5.0, 2.0).to_f64(), Some(1.0)); // 5/2 = 2.5 → 2
    assert_eq!(r(7.0, 2.0).to_f64(), Some(-1.0)); // 7/2 = 3.5 → 4
    assert_eq!(r(-7.0, 2.0).to_f64(), Some(1.0));
    assert_eq!(
        r(6.0, 3.0).to_f64().map(f64::to_bits),
        Some(0.0f64.to_bits())
    );
    assert_eq!(
        r(-6.0, 3.0).to_f64().map(f64::to_bits),
        Some((-0.0f64).to_bits())
    );
    assert_eq!(r(1.0, f64::INFINITY).to_f64(), Some(1.0));
    assert_eq!(r(f64::INFINITY, 1.0), f.nan());
    assert_eq!(r(1.0, 0.0), f.nan());
    // A huge quotient: 2^1000 = 3q + 1, and q is the nearest integer to 2^1000 / 3.
    assert_eq!(r(2f64.powi(1000), 3.0).to_f64(), Some(1.0));
    // 0.75 rem 0.5: quotient 1.5 → 2, remainder −0.25.
    assert_eq!(r(0.75, 0.5).to_f64(), Some(-0.25));
    assert_eq!(r(0.25, 0.5).to_f64(), Some(0.25)); // quotient 0.5 → 0
}

#[test]
fn x87_encodings_load_and_store() {
    let w80 = Width::new(80).unwrap();
    let x80 = |s: u128, e: u128, i: u128, f: u128| {
        BitVec::wrapping_from_u128(w80, s << 79 | e << 64 | i << 63 | f)
    };
    let x79 = |s: u128, e: u128, f: u128| {
        BitVec::wrapping_from_u128(FpFormat::X87.width(), s << 78 | e << 63 | f)
    };
    let nan = FpFormat::X87.nan();
    // Zero, denormal, pseudo-denormal, normal, unnormal, infinity, NaN, pseudo-inf, pseudo-NaN.
    assert_eq!(x87_load(&x80(1, 0, 0, 0)).unwrap(), x79(1, 0, 0));
    assert_eq!(x87_load(&x80(0, 0, 0, 5)).unwrap(), x79(0, 0, 5));
    assert_eq!(x87_load(&x80(0, 0, 1, 5)).unwrap(), x79(0, 1, 5));
    assert_eq!(x87_load(&x80(0, 16383, 1, 7)).unwrap(), x79(0, 16383, 7));
    assert_eq!(x87_load(&x80(0, 16383, 0, 7)).unwrap(), nan);
    assert_eq!(x87_load(&x80(1, 0x7fff, 1, 0)).unwrap(), x79(1, 0x7fff, 0));
    assert_eq!(x87_load(&x80(0, 0x7fff, 1, 9)).unwrap(), x79(0, 0x7fff, 9));
    assert_eq!(x87_load(&x80(0, 0x7fff, 0, 0)).unwrap(), nan);
    assert_eq!(x87_load(&x80(0, 0x7fff, 0, 9)).unwrap(), nan);
    let mut rng = Rng(6);
    for _ in 0..10_000 {
        let a = sample(&mut rng, FpFormat::X87);
        assert_eq!(x87_load(&x87_store(&a).unwrap()).unwrap(), a);
    }
}

#[test]
fn classification_and_sign_operations() {
    let f = FpFormat::F32;
    let v = |x: f32| BitVec::from_f32(x);
    let t = |t: FpTest, x: f32| f.test(t, &v(x)).unwrap();
    assert!(t(FpTest::Nan, f32::NAN));
    assert!(!t(FpTest::Negative, -f32::NAN));
    assert!(t(FpTest::Negative, -0.0));
    assert!(t(FpTest::Zero, -0.0));
    assert!(t(FpTest::Subnormal, 1e-40));
    assert!(t(FpTest::Normal, f32::MIN_POSITIVE));
    assert!(t(FpTest::Infinite, f32::NEG_INFINITY));
    assert!(t(FpTest::Positive, 0.0));
    // Sign operations change a NaN's sign bit and nothing else.
    let q = v(f32::from_bits(0x7fc0_1234));
    assert_eq!(f.neg(&q).unwrap().to_u64(), Some(0xffc0_1234));
    assert_eq!(f.abs(&f.neg(&q).unwrap()).unwrap(), q);
    assert_eq!(f.copysign(&v(2.0), &v(-0.0)).unwrap(), v(-2.0));
    // Arithmetic canonicalizes: a NaN payload does not survive an addition.
    assert_eq!(f.add(RoundingMode::Rne, &q, &v(1.0)).unwrap(), f.nan());
    assert_eq!(f.nan().to_u64(), Some(0x7fc0_0000));
    assert_eq!(FpFormat::F64.nan().to_u64(), Some(0x7ff8_0000_0000_0000));
}

#[test]
fn formats_are_validated() {
    assert!(FpFormat::new(1, 5).is_err());
    assert!(FpFormat::new(32, 5).is_err());
    assert!(FpFormat::new(5, 1).is_err());
    assert!(FpFormat::new(31, 481).is_ok());
    assert!(FpFormat::new(31, 482).is_err());
    // No overflow on the way to the answer.
    assert!(FpFormat::new(8, u32::MAX).is_err());
    assert!(FpFormat::new(u32::MAX, 24).is_err());
    assert_eq!(FpFormat::F32.name(), Some("f32"));
    assert_eq!(FpFormat::from_name("bf16"), Some(FpFormat::BF16));
    assert_eq!(format!("{:?}", FpFormat::X87), "fp<15, 64>");
    let x = BitVec::from_f32(1.0);
    assert!(FpFormat::F64.add(RoundingMode::Rne, &x, &x).is_err());
}
