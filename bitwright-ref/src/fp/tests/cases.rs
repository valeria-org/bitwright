//! Hand-computed cases from the contract, for every operation and rounding mode.
//!
//! Expected values are bit patterns worked out by hand (binary32 unless stated). Per-mode
//! expectations are listed in the order of `Rm::ALL`: `Rne, Rna, Rtp, Rtn, Rtz`.

use super::*;

/// A binary32 pattern.
fn s(x: u32) -> Bits {
    bw(32, x.into())
}

/// Checks `op(rm)` for every mode against `want` (in the order of `Rm::ALL`).
fn modes(what: &str, want: [u128; 5], op: impl Fn(Rm) -> Bits) {
    for (rm, w) in Rm::ALL.into_iter().zip(want) {
        let got = val(&op(rm));
        assert_eq!(got, w, "{what} {rm:?}: got {got:#x}, want {w:#x}");
    }
}

fn all_modes(what: &str, want: u128, op: impl Fn(Rm) -> Bits) {
    modes(what, [want; 5], op);
}

const ONE: u32 = 0x3f80_0000;
const NEG_ONE: u32 = 0xbf80_0000;
const TWO: u32 = 0x4000_0000;
const THREE: u32 = 0x4040_0000;
const HALF: u32 = 0x3f00_0000;
const PZ: u32 = 0;
const NZ: u32 = 0x8000_0000;
const PINF: u32 = 0x7f80_0000;
const NINF: u32 = 0xff80_0000;
const OMEGA: u32 = 0x7f7f_ffff;
const NEG_OMEGA: u32 = 0xff7f_ffff;
const MIN_SUB: u32 = 1;
const MAX_SUB: u32 = 0x007f_ffff;
const MIN_NORMAL: u32 = 0x0080_0000;
const QNAN: u128 = 0x7fc0_0000;

#[test]
fn canonical_nans() {
    assert_eq!(val(&canonical_nan(B16)), 0x7e00);
    assert_eq!(val(&canonical_nan(BF16)), 0x7fc0);
    assert_eq!(val(&canonical_nan(B32)), QNAN);
    assert_eq!(val(&canonical_nan(B64)), 0x7ff8_0000_0000_0000);
    assert_eq!(val(&canonical_nan(B128)), (0xffffu128 << 111) & !(1 << 127));
    assert_eq!(val(&canonical_nan(X87V)), (0x7fffu128 << 63) | (1 << 62));
    // (2, 2): s = 0, E = 11, T = 1.
    assert_eq!(val(&canonical_nan(Format { eb: 2, sb: 2 })), 0b0111);
    // Width 512: E = 2^15 - 1 at bits 510..496, T = 2^495.
    let mut want = vec![0u64; 8];
    want[7] = 0x7fff_8000_0000_0000;
    assert_eq!(
        canonical_nan(Format { eb: 15, sb: 497 }),
        Bits::from_limbs(512, &want)
    );
}

#[test]
fn signed_zero_rules() {
    let f = B32;
    let zr = [0, 0, 0, NZ.into(), 0]; // the zero rule: -0 only under Rtn
    modes("1 + -1", zr, |rm| add(f, rm, &s(ONE), &s(NEG_ONE)));
    modes("1 - 1", zr, |rm| sub(f, rm, &s(ONE), &s(ONE)));
    modes("x - x subnormal", zr, |rm| {
        sub(f, rm, &s(MIN_SUB), &s(MIN_SUB))
    });
    modes("+0 + -0", zr, |rm| add(f, rm, &s(PZ), &s(NZ)));
    modes("-0 + +0", zr, |rm| add(f, rm, &s(NZ), &s(PZ)));
    modes("+0 - +0", zr, |rm| sub(f, rm, &s(PZ), &s(PZ)));
    all_modes("-0 + -0", NZ.into(), |rm| add(f, rm, &s(NZ), &s(NZ)));
    all_modes("-0 - +0", NZ.into(), |rm| sub(f, rm, &s(NZ), &s(PZ)));
    all_modes("+0 + +0", 0, |rm| add(f, rm, &s(PZ), &s(PZ)));
    all_modes("+0 - -0", 0, |rm| sub(f, rm, &s(PZ), &s(NZ)));
    // A zero plus a nonzero value is that value, whatever the mode.
    all_modes("-0 + 1", ONE.into(), |rm| add(f, rm, &s(NZ), &s(ONE)));
    all_modes("-min_sub + +0", 0x8000_0001, |rm| {
        add(f, rm, &s(0x8000_0001), &s(PZ))
    });
    // Products and quotients of zeros take the xor of the signs.
    all_modes("-0 * 3", NZ.into(), |rm| mul(f, rm, &s(NZ), &s(THREE)));
    all_modes("-0 * -3", 0, |rm| mul(f, rm, &s(NZ), &s(THREE | NZ)));
    all_modes("+0 * -1", NZ.into(), |rm| mul(f, rm, &s(PZ), &s(NEG_ONE)));
    all_modes("-0 / 3", NZ.into(), |rm| div(f, rm, &s(NZ), &s(THREE)));
    all_modes("3 / -inf", NZ.into(), |rm| div(f, rm, &s(THREE), &s(NINF)));
    all_modes("-3 / -inf", 0, |rm| div(f, rm, &s(THREE | NZ), &s(NINF)));
    all_modes("sqrt(-0)", NZ.into(), |rm| sqrt(f, rm, &s(NZ)));
    all_modes("sqrt(+0)", 0, |rm| sqrt(f, rm, &s(PZ)));
}

#[test]
fn fma_zero_rule_and_specials() {
    let f = B32;
    let zr = [0, 0, 0, NZ.into(), 0];
    // Product +0 (signs agree) and c = -0: different zero signs, so the zero rule.
    modes("fma(+0, 1, -0)", zr, |rm| {
        fma(f, rm, &s(PZ), &s(ONE), &s(NZ))
    });
    // Product -0 and c = -0: that zero.
    all_modes("fma(-0, 1, -0)", NZ.into(), |rm| {
        fma(f, rm, &s(NZ), &s(ONE), &s(NZ))
    });
    // Product +0 (-0 * -1) and c = +0.
    all_modes("fma(-0, -1, +0)", 0, |rm| {
        fma(f, rm, &s(NZ), &s(NEG_ONE), &s(PZ))
    });
    // A nonzero exact product cancelled exactly by c: the zero rule.
    modes("fma(1, 1, -1)", zr, |rm| {
        fma(f, rm, &s(ONE), &s(ONE), &s(NEG_ONE))
    });
    modes("fma(-3, 1, 3)", zr, |rm| {
        fma(f, rm, &s(THREE | NZ), &s(ONE), &s(THREE))
    });
    // A tiny nonzero product plus a zero is a nonzero r: rounded, not the zero rule.
    let tiny = 0x0d80_0000; // 2^-100 (biased exponent 27)
    modes(
        "fma(2^-100, 2^-100, -0)",
        [0, 0, MIN_SUB.into(), 0, 0],
        |rm| fma(f, rm, &s(tiny), &s(tiny), &s(NZ)),
    );
    modes(
        "fma(2^-100, -2^-100, +0)",
        [NZ.into(), NZ.into(), NZ.into(), 0x8000_0001, NZ.into()],
        |rm| fma(f, rm, &s(tiny), &s(tiny | NZ), &s(PZ)),
    );
    // Infinities.
    let nan = QNAN;
    all_modes("fma(inf, 0, 1)", nan, |rm| {
        fma(f, rm, &s(PINF), &s(PZ), &s(ONE))
    });
    all_modes("fma(0, -inf, -inf)", nan, |rm| {
        fma(f, rm, &s(PZ), &s(NINF), &s(NINF))
    });
    all_modes("fma(inf, 1, -inf)", nan, |rm| {
        fma(f, rm, &s(PINF), &s(ONE), &s(NINF))
    });
    all_modes("fma(inf, -1, -inf)", NINF.into(), |rm| {
        fma(f, rm, &s(PINF), &s(NEG_ONE), &s(NINF))
    });
    all_modes("fma(-inf, -inf, 1)", PINF.into(), |rm| {
        fma(f, rm, &s(NINF), &s(NINF), &s(ONE))
    });
    all_modes("fma(Ω, Ω, -inf)", NINF.into(), |rm| {
        fma(f, rm, &s(OMEGA), &s(OMEGA), &s(NINF))
    });
    all_modes("fma(1, 1, NaN)", nan, |rm| {
        fma(f, rm, &s(ONE), &s(ONE), &s(0xff80_0001))
    });
    // One rounding: (1 + 2^-23)^2 - 1 = 2^-22 + 2^-46 exactly, which is 2^-22 plus half of its
    // ulp 2^-45: a tie (a separate multiply would have lost the 2^-46).
    let one_ulp = 0x3f80_0001;
    modes(
        "fma((1+u), (1+u), -1)",
        [
            0x3480_0000,
            0x3480_0001,
            0x3480_0001,
            0x3480_0000,
            0x3480_0000,
        ],
        |rm| fma(f, rm, &s(one_ulp), &s(one_ulp), &s(NEG_ONE)),
    );
}

#[test]
fn rounding_ties_and_directions() {
    let f = B32;
    let two_m24 = 0x3380_0000; // 2^-24, half an ulp of 1
    // 1 + 2^-24: a tie with M even.
    modes(
        "1 + 2^-24",
        [
            0x3f80_0000,
            0x3f80_0001,
            0x3f80_0001,
            0x3f80_0000,
            0x3f80_0000,
        ],
        |rm| add(f, rm, &s(ONE), &s(two_m24)),
    );
    modes(
        "-1 - 2^-24",
        [
            0xbf80_0000,
            0xbf80_0001,
            0xbf80_0000,
            0xbf80_0001,
            0xbf80_0000,
        ],
        |rm| sub(f, rm, &s(NEG_ONE), &s(two_m24)),
    );
    // (1 + 2^-23) + 2^-24: a tie with M odd.
    modes(
        "(1 + 2^-23) + 2^-24",
        [
            0x3f80_0002,
            0x3f80_0002,
            0x3f80_0002,
            0x3f80_0001,
            0x3f80_0001,
        ],
        |rm| add(f, rm, &s(0x3f80_0001), &s(two_m24)),
    );
    // 1 + 3 · 2^-25: above the tie.
    modes(
        "1 + 1.5 * 2^-24",
        [
            0x3f80_0001,
            0x3f80_0001,
            0x3f80_0001,
            0x3f80_0000,
            0x3f80_0000,
        ],
        |rm| add(f, rm, &s(ONE), &s(0x33c0_0000)),
    );
    // (1 + 2^-23)^2 = 1 + 2^-22 + 2^-46: below the tie.
    modes(
        "(1 + 2^-23)^2",
        [
            0x3f80_0002,
            0x3f80_0002,
            0x3f80_0003,
            0x3f80_0002,
            0x3f80_0002,
        ],
        |rm| mul(f, rm, &s(0x3f80_0001), &s(0x3f80_0001)),
    );
    // 1/3 = 1.0101...b · 2^-2: the dropped part is 2/3 of an ulp.
    modes(
        "1 / 3",
        [
            0x3eaa_aaab,
            0x3eaa_aaab,
            0x3eaa_aaab,
            0x3eaa_aaaa,
            0x3eaa_aaaa,
        ],
        |rm| div(f, rm, &s(ONE), &s(THREE)),
    );
    modes(
        "-1 / 3",
        [
            0xbeaa_aaab,
            0xbeaa_aaab,
            0xbeaa_aaaa,
            0xbeaa_aaab,
            0xbeaa_aaaa,
        ],
        |rm| div(f, rm, &s(NEG_ONE), &s(THREE)),
    );
    modes(
        "2 / 3",
        [
            0x3f2a_aaab,
            0x3f2a_aaab,
            0x3f2a_aaab,
            0x3f2a_aaaa,
            0x3f2a_aaaa,
        ],
        |rm| div(f, rm, &s(TWO), &s(THREE)),
    );
    // sqrt(2) = 1.41421356...: 0x3fb504f3 = 1.41421353... lies 0.2 ulp below.
    modes(
        "sqrt(2)",
        [
            0x3fb5_04f3,
            0x3fb5_04f3,
            0x3fb5_04f4,
            0x3fb5_04f3,
            0x3fb5_04f3,
        ],
        |rm| sqrt(f, rm, &s(TWO)),
    );
    all_modes("sqrt(9)", THREE.into(), |rm| sqrt(f, rm, &s(0x4110_0000)));
    all_modes("sqrt(1/4)", HALF.into(), |rm| sqrt(f, rm, &s(0x3e80_0000)));
    // sqrt(2^-149) = 2^-74.5 = sqrt(2) · 2^-75: the same significand as sqrt(2).
    modes(
        "sqrt(min_sub)",
        [
            0x1a35_04f3,
            0x1a35_04f3,
            0x1a35_04f4,
            0x1a35_04f3,
            0x1a35_04f3,
        ],
        |rm| sqrt(f, rm, &s(MIN_SUB)),
    );
    for bad in [0x8000_0001u32, NINF, NEG_ONE, 0x7f80_0001, 0xffc0_0000] {
        all_modes("sqrt(negative or NaN)", QNAN, |rm| sqrt(f, rm, &s(bad)));
    }
    all_modes("sqrt(+inf)", PINF.into(), |rm| sqrt(f, rm, &s(PINF)));
}

#[test]
fn overflow_per_mode() {
    let f = B32;
    let (pinf, ninf, om, nom) = (
        u128::from(PINF),
        u128::from(NINF),
        u128::from(OMEGA),
        u128::from(NEG_OMEGA),
    );
    modes("Ω + Ω", [pinf, pinf, pinf, om, om], |rm| {
        add(f, rm, &s(OMEGA), &s(OMEGA))
    });
    modes("-Ω - Ω", [ninf, ninf, nom, ninf, nom], |rm| {
        sub(f, rm, &s(NEG_OMEGA), &s(OMEGA))
    });
    // Ω + 2^103 is exactly halfway between Ω (odd M) and 2^128: to nearest overflows.
    modes("Ω + half ulp", [pinf, pinf, pinf, om, om], |rm| {
        add(f, rm, &s(OMEGA), &s(0x7300_0000))
    });
    // Ω + 2^102 is below the midpoint: only Rtp leaves Ω.
    modes("Ω + quarter ulp", [om, om, pinf, om, om], |rm| {
        add(f, rm, &s(OMEGA), &s(0x7280_0000))
    });
    modes("2^127 * 2", [pinf, pinf, pinf, om, om], |rm| {
        mul(f, rm, &s(0x7f00_0000), &s(TWO))
    });
    modes("-2^127 * 2", [ninf, ninf, nom, ninf, nom], |rm| {
        mul(f, rm, &s(0xff00_0000), &s(TWO))
    });
    modes("Ω / 0.5", [pinf, pinf, pinf, om, om], |rm| {
        div(f, rm, &s(OMEGA), &s(HALF))
    });
    // Nonzero finite / 0 is an infinity in every mode (not an overflow).
    all_modes("1 / -0", ninf, |rm| div(f, rm, &s(ONE), &s(NZ)));
    all_modes("-inf / 0", ninf, |rm| div(f, rm, &s(NINF), &s(PZ)));
    all_modes("0 / 0", QNAN, |rm| div(f, rm, &s(PZ), &s(NZ)));
    all_modes("inf / -inf", QNAN, |rm| div(f, rm, &s(PINF), &s(NINF)));
    all_modes("inf - inf", QNAN, |rm| sub(f, rm, &s(PINF), &s(PINF)));
    all_modes("-inf + -inf", ninf, |rm| add(f, rm, &s(NINF), &s(NINF)));
    all_modes("inf + -Ω", pinf, |rm| add(f, rm, &s(PINF), &s(NEG_OMEGA)));
    all_modes("0 * inf", QNAN, |rm| mul(f, rm, &s(NZ), &s(PINF)));
    all_modes("-inf * -0.5", pinf, |rm| {
        mul(f, rm, &s(NINF), &s(HALF | NZ))
    });

    // binary16: 65520 is halfway between Ω = 65504 and 2^16.
    let h = B16;
    let (hinf, hom) = (0x7c00u128, 0x7bffu128);
    modes("b16 from 65520", [hinf, hinf, hinf, hom, hom], |rm| {
        from_uint(h, rm, &bw(32, 65520))
    });
    modes("b16 from 65519", [hom, hom, hinf, hom, hom], |rm| {
        from_uint(h, rm, &bw(32, 65519))
    });
    modes(
        "b16 from -65520",
        [
            hinf | 0x8000,
            hinf | 0x8000,
            hom | 0x8000,
            hinf | 0x8000,
            hom | 0x8000,
        ],
        |rm| from_sint(h, rm, &Bits::from_i128(32, -65520)),
    );
}

#[test]
fn gradual_underflow() {
    let f = B32;
    all_modes("min_normal - min_sub", MAX_SUB.into(), |rm| {
        sub(f, rm, &s(MIN_NORMAL), &s(MIN_SUB))
    });
    all_modes("max_sub + min_sub", MIN_NORMAL.into(), |rm| {
        add(f, rm, &s(MAX_SUB), &s(MIN_SUB))
    });
    all_modes("min_normal / 2", 0x0040_0000, |rm| {
        div(f, rm, &s(MIN_NORMAL), &s(TWO))
    });
    // Half of the smallest subnormal: a tie between 0 (even) and min_sub.
    modes("min_sub / 2", [0, 1, 1, 0, 0], |rm| {
        div(f, rm, &s(MIN_SUB), &s(TWO))
    });
    modes(
        "-min_sub / 2",
        [NZ.into(), 0x8000_0001, NZ.into(), 0x8000_0001, NZ.into()],
        |rm| div(f, rm, &s(0x8000_0001), &s(TWO)),
    );
    // A quarter of it: below the tie.
    modes("min_sub / 4", [0, 0, 1, 0, 0], |rm| {
        mul(f, rm, &s(MIN_SUB), &s(0x3e80_0000))
    });
    // 1.5 and 2.5 smallest subnormals: ties resolved to even (2 both times under Rne).
    modes("3 min_sub / 2", [2, 2, 2, 1, 1], |rm| {
        mul(f, rm, &s(3), &s(HALF))
    });
    modes("5 min_sub / 2", [2, 3, 3, 2, 2], |rm| {
        mul(f, rm, &s(5), &s(HALF))
    });
    // min_normal · (1 - 2^-24) = (2^23 - 1/2) · 2^-149: a tie between max_sub and min_normal.
    modes(
        "min_normal * (1 - 2^-24)",
        [
            MIN_NORMAL.into(),
            MIN_NORMAL.into(),
            MIN_NORMAL.into(),
            MAX_SUB.into(),
            MAX_SUB.into(),
        ],
        |rm| mul(f, rm, &s(MIN_NORMAL), &s(0x3f7f_ffff)),
    );
    // The smallest subnormal times 1 - 2^-24 sits just under it.
    modes("min_sub * (1 - 2^-24)", [1, 1, 1, 0, 0], |rm| {
        mul(f, rm, &s(MIN_SUB), &s(0x3f7f_ffff))
    });
    // Subnormal arithmetic is exact when the result is a multiple of 2^-149.
    all_modes("3 min_sub - 5 min_sub", 0x8000_0002, |rm| {
        sub(f, rm, &s(3), &s(5))
    });
}

#[test]
fn remainder_cases() {
    let f = B32;
    let r = |a: u32, b: u32| val(&rem(f, &s(a), &s(b)));
    let (five, four_half, seven_half, one_half, six): (u32, u32, u32, u32, u32) = (
        0x40a0_0000,
        0x4090_0000,
        0x40f0_0000,
        0x3fc0_0000,
        0x40c0_0000,
    );
    assert_eq!(r(five, THREE), NEG_ONE.into()); // 5/3 -> n = 2
    assert_eq!(r(five | NZ, THREE), ONE.into()); // -5/3 -> n = -2
    assert_eq!(r(five, THREE | NZ), NEG_ONE.into()); // 5/-3 -> n = -2
    assert_eq!(r(four_half, THREE), 0xbfc0_0000); // 1.5 ties to n = 2: -1.5
    assert_eq!(r(seven_half, THREE), one_half.into()); // 2.5 ties to n = 2: 1.5
    assert_eq!(r(one_half, THREE), one_half.into()); // 0.5 ties to n = 0
    assert_eq!(r(six, THREE), 0); // exact: a zero with a's sign
    assert_eq!(r(six | NZ, THREE), NZ.into());
    assert_eq!(r(NZ, THREE), NZ.into());
    assert_eq!(r(PZ, THREE | NZ), 0);
    // a finite, b infinite: a itself; otherwise NaN for an infinite a or a zero b.
    assert_eq!(r(THREE, NINF), THREE.into());
    assert_eq!(r(0x8000_0001, PINF), 0x8000_0001);
    assert_eq!(r(NZ, PINF), NZ.into());
    for (a, b) in [
        (PINF, THREE),
        (NINF, PINF),
        (THREE, PZ),
        (THREE, NZ),
        (PZ, PZ),
        (0x7f80_0001, PINF),
        (THREE, 0xffc0_0000),
    ] {
        assert_eq!(r(a, b), QNAN, "rem({a:#x}, {b:#x})");
    }
    // Huge quotients. Ω = (2^24 - 1) · 2^104 is a multiple of the smallest subnormal.
    assert_eq!(r(OMEGA, MIN_SUB), 0);
    // Ω / (11 · 2^-149) = (2^24 - 1) · 2^253 / 11, and (2^24 - 1) · 2^253 = 10 (mod 11):
    // the quotient rounds up and the remainder is -1 unit.
    assert_eq!(r(OMEGA, 11), 0x8000_0001);
    // Ω / 2^105 = 2^23 - 1/2: a tie, to the even n = 2^23, leaving -2^104.
    assert_eq!(r(OMEGA, 0x7400_0000), 0xf380_0000);
    // (2^24 - 1) · 2^-149 over 2 · 2^-149: again 2^23 - 1/2, leaving -2^-149.
    assert_eq!(r(0x00ff_ffff, 2), 0x8000_0001);
    // 1.5 · 2^101 / 2^101 and 1.25 · 2^102 / 2^101: ties to n = 2.
    assert_eq!(r(0x7240_0000, 0x7200_0000), 0xf180_0000);
    assert_eq!(r(0x72a0_0000, 0x7200_0000), 0x7180_0000);

    // binary64: Ω / (3 · 2^-1074) = (2^53 - 1) · 2^2045 / 3, which is 2 (mod 3).
    let d = |x: u64| bw(64, x.into());
    assert_eq!(
        val(&rem(B64, &d(0x7fef_ffff_ffff_ffff), &d(3))),
        0x8000_0000_0000_0001
    );
    // binary128: Ω = (2^113 - 1) · 2^16271 over 3 · 2^-16494; (2^113 - 1) · 2^32765 = 2 (mod 3).
    let omega128 = (0x7ffeu128 << 112) | ((1u128 << 112) - 1);
    assert_eq!(
        val(&rem(B128, &bw(128, omega128), &bw(128, 3))),
        (1u128 << 127) | 1
    );
    assert_eq!(val(&rem(B128, &bw(128, omega128), &bw(128, 1))), 0);
}

#[test]
fn round_to_integral_cases() {
    let f = B32;
    let rti = |x: u32| move |rm| round_to_integral(f, rm, &s(x));
    let (p25, n25, p15, n15) = (0x4020_0000, 0xc020_0000, 0x3fc0_0000, 0xbfc0_0000);
    let (n2, n3) = (0xc000_0000u128, 0xc040_0000u128);
    let (two, three) = (u128::from(TWO), u128::from(THREE));
    modes("rti(2.5)", [two, three, three, two, two], rti(p25));
    modes("rti(-2.5)", [n2, n3, n2, n3, n2], rti(n25));
    modes(
        "rti(1.5)",
        [two, two, two, ONE.into(), ONE.into()],
        rti(p15),
    );
    modes(
        "rti(-1.5)",
        [n2, n2, NEG_ONE.into(), n2, NEG_ONE.into()],
        rti(n15),
    );
    // |x| < 1: a zero with x's sign unless the mode moves away from zero.
    modes("rti(0.5)", [0, ONE.into(), ONE.into(), 0, 0], rti(HALF));
    modes(
        "rti(-0.5)",
        [
            NZ.into(),
            NEG_ONE.into(),
            NZ.into(),
            NEG_ONE.into(),
            NZ.into(),
        ],
        rti(HALF | NZ),
    );
    modes(
        "rti(-min_sub)",
        [NZ.into(), NZ.into(), NZ.into(), NEG_ONE.into(), NZ.into()],
        rti(0x8000_0001),
    );
    // 2^22 + 1/2 (T = 1) and 2^22 + 3/2 (T = 3): ties at the edge of the fraction bits.
    modes(
        "rti(2^22 + 0.5)",
        [
            0x4a80_0000,
            0x4a80_0002,
            0x4a80_0002,
            0x4a80_0000,
            0x4a80_0000,
        ],
        rti(0x4a80_0001),
    );
    modes(
        "rti(2^22 + 1.5)",
        [
            0x4a80_0004,
            0x4a80_0004,
            0x4a80_0004,
            0x4a80_0002,
            0x4a80_0002,
        ],
        rti(0x4a80_0003),
    );
    for x in [0x4e80_0000u32, OMEGA, PINF, NINF, PZ, NZ, 0x4b00_0001] {
        all_modes("rti(integral)", x.into(), rti(x));
    }
    all_modes("rti(NaN)", QNAN, rti(0xff80_0001));

    // (2, 3): values 0, 1/4, 1/2, 3/4, 1, 5/4, 3/2, 7/4, 2, 5/2, 3, 7/2; Ω = 3.5 < 2^(p-1) = 4.
    // roundToIntegral(3.5) is 4 under Rne, Rna and Rtp, which overflows to +∞ (z3 agrees).
    let t = Format { eb: 2, sb: 3 };
    let rt = |x: u128| move |rm| round_to_integral(t, rm, &bw(5, x));
    let (inf, ninf) = (0b0_11_00, 0b1_11_00);
    let (three, nthree, two, one) = (0b0_10_10, 0b1_10_10, 0b0_10_00, 0b0_01_00);
    modes(
        "(2,3) rti(3.5)",
        [inf, inf, inf, three, three],
        rt(0b0_10_11),
    );
    modes(
        "(2,3) rti(-3.5)",
        [ninf, ninf, nthree, ninf, nthree],
        rt(0b1_10_11),
    );
    modes(
        "(2,3) rti(2.5)",
        [two, three, three, two, two],
        rt(0b0_10_01),
    );
    modes("(2,3) rti(0.75)", [one, one, one, 0, 0], rt(0b0_00_11));
    modes("(2,3) rti(0.5)", [0, one, one, 0, 0], rt(0b0_00_10));
    modes(
        "(2,3) rti(-0.25)",
        [0b1_00_00, 0b1_00_00, 0b1_00_00, 0b1_01_00, 0b1_00_00],
        rt(0b1_00_01),
    );
    // 3.5 + 0.25 = 3.75: seven and a half quanta of 1/2, rounding (Rne: to 8, odd M) past Ω.
    modes(
        "(2,3) 3.5 + 0.25",
        [inf, inf, inf, 0b0_10_11, 0b0_10_11],
        |rm| add(t, rm, &bw(5, 0b0_10_11), &bw(5, 0b0_00_01)),
    );
    // to_sint does not go through the format: 3.5 converts to 4 under Rne.
    modes("(2,3) to_sint(3.5)", [4, 4, 4, 3, 3], |rm| {
        to_sint(t, rm, &bw(5, 0b0_10_11), 8)
    });
}

#[test]
fn min_max_cases() {
    let f = B32;
    let mn = |a: u32, b: u32| val(&min(f, &s(a), &s(b)));
    let mx = |a: u32, b: u32| val(&max(f, &s(a), &s(b)));
    assert_eq!(mn(PZ, NZ), NZ.into());
    assert_eq!(mn(NZ, PZ), NZ.into());
    assert_eq!(mx(PZ, NZ), 0);
    assert_eq!(mx(NZ, PZ), 0);
    assert_eq!(mn(NZ, NZ), NZ.into());
    // One NaN: the other operand's pattern, whatever the NaN.
    for nan in [0x7fc0_0000u32, 0xffc0_0001, 0x7f80_0001, 0xff80_0002] {
        assert_eq!(mn(nan, ONE), ONE.into());
        assert_eq!(mn(ONE, nan), ONE.into());
        assert_eq!(mx(nan, NZ), NZ.into());
        assert_eq!(mx(NINF, nan), NINF.into());
        assert_eq!(mn(nan, 0x8000_0001), 0x8000_0001);
    }
    // Both NaN: the canonical NaN.
    assert_eq!(mn(0xffc0_0001, 0x7f80_0002), QNAN);
    assert_eq!(mx(0xff80_0001, 0xffff_ffff), QNAN);
    assert_eq!(mn(THREE | NZ, TWO), (THREE | NZ).into());
    assert_eq!(mx(THREE | NZ, TWO), TWO.into());
    assert_eq!(mn(NINF, PINF), NINF.into());
    assert_eq!(mx(NINF, PINF), PINF.into());
    assert_eq!(mn(MIN_SUB, 0x8000_0001), 0x8000_0001);
    assert_eq!(mx(OMEGA, PINF), PINF.into());
}

#[test]
fn comparison_and_class_cases() {
    let f = B32;
    let nan = 0x7fc0_0000;
    assert!(eq(f, &s(PZ), &s(NZ)));
    assert!(!lt(f, &s(NZ), &s(PZ)));
    assert!(le(f, &s(NZ), &s(PZ)) && le(f, &s(PZ), &s(NZ)));
    assert!(!eq(f, &s(nan), &s(nan)));
    assert!(!lt(f, &s(nan), &s(ONE)) && !lt(f, &s(ONE), &s(nan)));
    assert!(!le(f, &s(nan), &s(nan)) && !le(f, &s(ONE), &s(0xff80_0001)));
    assert!(lt(f, &s(NINF), &s(NEG_OMEGA)) && lt(f, &s(OMEGA), &s(PINF)));
    assert!(le(f, &s(PINF), &s(PINF)) && !lt(f, &s(PINF), &s(PINF)));
    assert!(lt(f, &s(0x8000_0001), &s(PZ)) && lt(f, &s(NZ), &s(MIN_SUB)));
    assert!(lt(f, &s(0xc000_0000), &s(NEG_ONE)));

    assert!(is_negative(f, &s(NZ)) && !is_positive(f, &s(NZ)));
    assert!(is_positive(f, &s(PZ)) && !is_negative(f, &s(PZ)));
    assert!(!is_negative(f, &s(0xffc0_0000)) && !is_positive(f, &s(0x7fc0_0000)));
    assert!(is_negative(f, &s(NINF)) && is_infinite(f, &s(NINF)));
    assert!(is_zero(f, &s(NZ)) && !is_normal(f, &s(NZ)) && !is_subnormal(f, &s(NZ)));
    assert!(is_normal(f, &s(MIN_NORMAL)) && is_normal(f, &s(OMEGA)));
    assert!(is_subnormal(f, &s(MAX_SUB)) && is_subnormal(f, &s(0x8000_0001)));
    assert!(is_nan(f, &s(0x7f80_0001)) && !is_infinite(f, &s(0x7f80_0001)));
    assert!(!is_normal(f, &s(PINF)) && !is_normal(f, &s(nan)));

    // Sign operations change only the sign bit, even of NaNs.
    assert_eq!(val(&neg(f, &s(0x7fc0_0001))), 0xffc0_0001);
    assert_eq!(val(&neg(f, &s(NZ))), 0);
    assert_eq!(val(&abs(f, &s(0xffc0_0001))), 0x7fc0_0001);
    assert_eq!(val(&abs(f, &s(NINF))), PINF.into());
    assert_eq!(val(&copysign(f, &s(0x7f80_0001), &s(NEG_ONE))), 0xff80_0001);
    assert_eq!(val(&copysign(f, &s(NEG_ONE), &s(0x7fc0_0000))), ONE.into());
    assert_eq!(val(&copysign(f, &s(ONE), &s(0xffc0_0000))), NEG_ONE.into());
}

#[test]
fn conversion_cases() {
    let f = B32;
    let three_e9 = 0x4f32_d05e; // 3e9 = 5859375 · 2^9, exact
    let to_i = |rm, x: u32, n| val(&to_sint(f, rm, &s(x), n));
    let to_u = |rm, x: u32, n| val(&to_uint(f, rm, &s(x), n));
    for rm in Rm::ALL {
        assert_eq!(to_i(rm, three_e9, 32), 0x7fff_ffff);
        assert_eq!(to_i(rm, three_e9 | NZ, 32), 0x8000_0000);
        assert_eq!(to_u(rm, three_e9, 32), 3_000_000_000);
        assert_eq!(to_u(rm, three_e9 | NZ, 32), 0);
        assert_eq!(to_u(rm, three_e9, 31), 0x7fff_ffff);
        for nan in [0x7fc0_0000u32, 0xff80_0001] {
            assert_eq!(to_i(rm, nan, 32), 0);
            assert_eq!(to_u(rm, nan, 64), 0);
        }
        assert_eq!(to_i(rm, PINF, 8), 0x7f);
        assert_eq!(to_i(rm, NINF, 8), 0x80);
        assert_eq!(to_u(rm, PINF, 8), 0xff);
        assert_eq!(to_u(rm, NINF, 8), 0);
        assert_eq!(to_i(rm, NZ, 8), 0);
        assert_eq!(to_u(rm, OMEGA, 128), ((1 << 24) - 1) << 104); // Ω < 2^128
        assert_eq!(to_u(rm, OMEGA, 127), (1 << 127) - 1);
        assert_eq!(to_i(rm, NEG_OMEGA, 128), 1 << 127);
        // Width 1: signed range [-1, 0], unsigned [0, 1].
        assert_eq!(to_i(rm, PINF, 1), 0);
        assert_eq!(to_i(rm, NINF, 1), 1);
        assert_eq!(to_u(rm, PINF, 1), 1);
    }
    let per = |x: u32, signed: bool| {
        Rm::ALL.map(|rm| {
            if signed {
                to_i(rm, x, 8)
            } else {
                to_u(rm, x, 8)
            }
        })
    };
    assert_eq!(per(0x4020_0000, true), [2, 3, 3, 2, 2]); // 2.5
    assert_eq!(per(0xc020_0000, true), [0xfe, 0xfd, 0xfe, 0xfd, 0xfe]); // -2.5
    // Negative values saturate to 0 unsigned, including those whose integer is 0.
    assert_eq!(per(0xbfc0_0000, false), [0; 5]); // -1.5
    assert_eq!(per(HALF | NZ, true), [0, 0xff, 0, 0xff, 0]); // -0.5
    assert_eq!(per(HALF | NZ, false), [0; 5]);
    assert_eq!(per(0x437f_8000, false), [0xff, 0xff, 0xff, 0xff, 0xff]); // 255.5 -> 256 saturates
    assert_eq!(per(0x437f_8000, true), [0x7f; 5]);
    // 0.75 and -0.75 into one bit.
    assert_eq!(
        Rm::ALL.map(|rm| to_i(rm, 0x3f40_0000, 1)),
        [0, 0, 0, 0, 0] // 1 saturates to 0; 0 is 0
    );
    assert_eq!(Rm::ALL.map(|rm| to_i(rm, 0xbf40_0000, 1)), [1, 1, 0, 1, 0]);
    assert_eq!(Rm::ALL.map(|rm| to_u(rm, 0x3f40_0000, 1)), [1, 1, 1, 0, 0]);
    assert_eq!(Rm::ALL.map(|rm| to_u(rm, 0x3fc0_0000, 1)), [1; 5]); // 2 or 1 -> 1

    // Wide integers. binary128 Ω saturates at 512 bits; 2^200 converts exactly.
    let omega128 = (0x7ffeu128 << 112) | ((1u128 << 112) - 1);
    let top = |bit: usize, ones_below: bool| {
        let mut v = vec![if ones_below { u64::MAX } else { 0 }; 8];
        v[bit / 64] = if ones_below {
            !0 >> (63 - bit % 64)
        } else {
            1 << (bit % 64)
        };
        for l in v.iter_mut().skip(bit / 64 + 1) {
            *l = 0;
        }
        Bits::from_limbs(512, &v)
    };
    for rm in Rm::ALL {
        assert_eq!(
            to_sint(B128, rm, &bw(128, omega128), 512),
            top(510, true) // 2^511 - 1
        );
        assert_eq!(
            to_sint(B128, rm, &bw(128, omega128 | 1 << 127), 512),
            top(511, false) // -2^511
        );
        assert_eq!(to_uint(B128, rm, &bw(128, omega128), 512), top(511, true));
        let p200 = f64b(2f64.powi(200));
        assert_eq!(to_uint(B64, rm, &p200, 512), top(200, false));
        // 2^200 saturates to 2^200 - 1 at 201 bits signed, and fits unsigned.
        let below = Bits::from_limbs(201, &[u64::MAX, u64::MAX, u64::MAX, 0xff]);
        assert_eq!(to_sint(B64, rm, &p200, 201), below);
        let exact = Bits::from_limbs(201, &[0, 0, 0, 0x100]);
        assert_eq!(to_uint(B64, rm, &p200, 201), exact);
    }

    // Integers to binary64: 2^512 - 1 rounds to 2^512 or to (2^53 - 1) · 2^459.
    let all_ones = Bits::from_limbs(512, &[u64::MAX; 8]);
    let (p512, below) = (0x5ff0_0000_0000_0000u128, 0x5fef_ffff_ffff_ffffu128);
    modes(
        "b64 from 2^512 - 1",
        [p512, p512, p512, below, below],
        |rm| from_uint(B64, rm, &all_ones),
    );
    all_modes("b64 from -1 (512 bits)", 0xbff0_0000_0000_0000, |rm| {
        from_sint(B64, rm, &all_ones)
    });
    all_modes("b64 from -2^511", 0xdfe0_0000_0000_0000, |rm| {
        from_sint(B64, rm, &top(511, false))
    });
    all_modes("b32 from 1-bit 1 unsigned", ONE.into(), |rm| {
        from_uint(f, rm, &bw(1, 1))
    });
    all_modes("b32 from 1-bit 1 signed", NEG_ONE.into(), |rm| {
        from_sint(f, rm, &bw(1, 1))
    });
    all_modes("b32 from 0", 0, |rm| from_sint(f, rm, &bw(64, 0)));
    // 2^24 + 1 is a tie in binary32; 2^24 + 3 rounds up to nearest.
    modes(
        "b32 from 2^24 + 1",
        [
            0x4b80_0000,
            0x4b80_0001,
            0x4b80_0001,
            0x4b80_0000,
            0x4b80_0000,
        ],
        |rm| from_uint(f, rm, &bw(32, (1 << 24) + 1)),
    );
    modes(
        "b32 from -(2^24 + 3)",
        [
            0xcb80_0002,
            0xcb80_0002,
            0xcb80_0001,
            0xcb80_0002,
            0xcb80_0001,
        ],
        |rm| from_sint(f, rm, &Bits::from_i128(32, -((1 << 24) + 3))),
    );

    // Between formats: specials, and a binary64 value rounded to binary32 in each mode.
    all_modes("b64 NaN -> b32", QNAN, |rm| {
        to_fp(B64, f, rm, &f64b(f64::from_bits(0xfff0_0000_0000_0001)))
    });
    all_modes("b64 -0 -> b32", NZ.into(), |rm| {
        to_fp(B64, f, rm, &f64b(-0.0))
    });
    all_modes("b64 -inf -> b16", 0xfc00, |rm| {
        to_fp(B64, B16, rm, &f64b(f64::NEG_INFINITY))
    });
    let third = f64b(1.0 / 3.0);
    modes(
        "b64 1/3 -> b32",
        [
            0x3eaa_aaab,
            0x3eaa_aaab,
            0x3eaa_aaab,
            0x3eaa_aaaa,
            0x3eaa_aaaa,
        ],
        |rm| to_fp(B64, f, rm, &third),
    );
    let (om, pinf) = (u128::from(OMEGA), u128::from(PINF));
    modes("b64 1e300 -> b32", [pinf, pinf, pinf, om, om], |rm| {
        to_fp(B64, f, rm, &f64b(1e300))
    });
    modes("b64 1e-300 -> b32", [0, 0, 1, 0, 0], |rm| {
        to_fp(B64, f, rm, &f64b(1e-300))
    });
}

#[test]
fn wide_format_cases() {
    // binary128: 1 + 2^-113 is a tie; 1 + 2^-112 is the next value.
    let one = 0x3fffu128 << 112;
    let tie = 16270u128 << 112; // 2^-113
    let f = B128;
    modes("b128 1 + 2^-113", [one, one + 1, one + 1, one, one], |rm| {
        add(f, rm, &bw(128, one), &bw(128, tie))
    });
    let omega = (0x7ffeu128 << 112) | ((1u128 << 112) - 1);
    let inf = 0x7fffu128 << 112;
    modes("b128 Ω + Ω", [inf, inf, inf, omega, omega], |rm| {
        add(f, rm, &bw(128, omega), &bw(128, omega))
    });
    // The smallest subnormal halved: a tie with 0.
    modes("b128 min_sub / 2", [0, 1, 1, 0, 0], |rm| {
        div(f, rm, &bw(128, 1), &bw(128, 0x4000u128 << 112))
    });
    // Ω - min_sub rounds back to Ω (or to its predecessor when directed down).
    modes(
        "b128 Ω - min_sub",
        [omega, omega, omega, omega - 1, omega - 1],
        |rm| sub(f, rm, &bw(128, omega), &bw(128, 1)),
    );

    // x87 values (15, 64): 1 + 2^-64 is a tie; (1 + 2^-63)^2 = 1 + 2^-62 + 2^-126.
    let x = X87V;
    let one87 = 0x3fffu128 << 63;
    let tie87 = (0x3fffu128 - 64) << 63;
    modes(
        "x87 1 + 2^-64",
        [one87, one87 + 1, one87 + 1, one87, one87],
        |rm| add(x, rm, &bw(79, one87), &bw(79, tie87)),
    );
    modes(
        "x87 (1 + 2^-63)^2",
        [one87 + 2, one87 + 2, one87 + 3, one87 + 2, one87 + 2],
        |rm| mul(x, rm, &bw(79, one87 + 1), &bw(79, one87 + 1)),
    );

    // Width 512 (eb = 15, sb = 497): 1 + 2^-497 is a tie; 3 · (1/3) is not 1 when rounded down.
    let wide = Format { eb: 15, sb: 497 };
    let enc512 = |e: u64, t_low: u64| {
        let mut v = vec![0u64; 8];
        v[0] = t_low;
        // Biased exponent at bits 510..496.
        v[7] = e << (496 - 448);
        Bits::from_limbs(512, &v)
    };
    let one512 = enc512(0x3fff, 0);
    let tie512 = enc512(0x3fff - 497, 0);
    for (rm, want) in Rm::ALL.into_iter().zip([0u64, 1, 1, 0, 0]) {
        assert_eq!(
            add(wide, rm, &one512, &tie512),
            enc512(0x3fff, want),
            "wide 1 + 2^-497 {rm:?}"
        );
    }
    assert_eq!(
        sqrt(wide, Rm::Rne, &enc512(0x3fff + 2, 0)),
        enc512(0x3fff + 1, 0),
        "wide sqrt(4)"
    );
}

#[test]
fn x87_load_rows() {
    // 80-bit fields: sign 79, exponent 78..64, integer bit 63, fraction 62..0.
    let ext = |s: u128, e: u128, i: u128, f: u128| bw(80, (s << 79) | (e << 64) | (i << 63) | f);
    // (15, 64) fields: sign 78, exponent 77..63, trailing significand 62..0.
    let v = |s: u128, e: u128, t: u128| bw(79, (s << 78) | (e << 63) | t);
    let nan = canonical_nan(X87V);
    // E = 0, i = 0: zero or denormal.
    assert_eq!(x87_load(&ext(0, 0, 0, 0)), v(0, 0, 0));
    assert_eq!(x87_load(&ext(1, 0, 0, 0)), v(1, 0, 0));
    assert_eq!(x87_load(&ext(1, 0, 0, 5)), v(1, 0, 5));
    // E = 0, i = 1: pseudo-denormal, 1.f · 2^-16382, loads with E = 1.
    assert_eq!(x87_load(&ext(0, 0, 1, 5)), v(0, 1, 5));
    assert_eq!(x87_load(&ext(1, 0, 1, 0)), v(1, 1, 0));
    // Normal.
    assert_eq!(x87_load(&ext(0, 0x3fff, 1, 0)), v(0, 0x3fff, 0));
    assert_eq!(x87_load(&ext(1, 1, 1, 7)), v(1, 1, 7));
    assert_eq!(
        x87_load(&ext(0, 32766, 1, (1 << 63) - 1)),
        v(0, 32766, (1 << 63) - 1)
    );
    // Unnormal: the canonical NaN.
    assert_eq!(x87_load(&ext(0, 0x3fff, 0, 0x123)), nan);
    assert_eq!(x87_load(&ext(1, 1, 0, 0)), nan);
    assert_eq!(x87_load(&ext(0, 32766, 0, 1)), nan);
    // E = 32767, i = 1: infinity, or a NaN with its payload and sign kept.
    assert_eq!(x87_load(&ext(0, 32767, 1, 0)), v(0, 32767, 0));
    assert_eq!(x87_load(&ext(1, 32767, 1, 0)), v(1, 32767, 0));
    assert_eq!(x87_load(&ext(1, 32767, 1, 1 << 62)), v(1, 32767, 1 << 62));
    assert_eq!(x87_load(&ext(0, 32767, 1, 1)), v(0, 32767, 1));
    // E = 32767, i = 0: pseudo-infinity and pseudo-NaN become the canonical NaN.
    assert_eq!(x87_load(&ext(0, 32767, 0, 0)), nan);
    assert_eq!(x87_load(&ext(1, 32767, 0, 5)), nan);

    // Store: i = (E != 0), everything else kept.
    assert_eq!(x87_store(&v(0, 0, 0)), ext(0, 0, 0, 0));
    assert_eq!(x87_store(&v(1, 0, 5)), ext(1, 0, 0, 5));
    assert_eq!(x87_store(&v(0, 1, 5)), ext(0, 1, 1, 5));
    assert_eq!(x87_store(&v(0, 0x3fff, 0)), ext(0, 0x3fff, 1, 0));
    assert_eq!(x87_store(&v(1, 32767, 0)), ext(1, 32767, 1, 0));
    assert_eq!(x87_store(&v(1, 32767, 3)), ext(1, 32767, 1, 3));
    assert_eq!(x87_store(&nan), ext(0, 32767, 1, 1 << 62));

    // Round trip on every class, including payloads, and random patterns.
    let mut rng = Rng(0x5eed_0008);
    for _ in 0..20_000 {
        let s = u128::from(rng.coin());
        let e = match rng.below(4) {
            0 => 0,
            1 => 32767,
            _ => u128::from(rng.below(32768)),
        };
        let t = (u128::from(rng.next()) >> rng.below(64)) & ((1 << 63) - 1);
        let a = v(s, e, t);
        assert_eq!(x87_load(&x87_store(&a)), a);
    }
}

#[test]
fn format_and_width_checks() {
    assert_eq!(B64.width(), 64);
    assert_eq!(X87V.width(), 79);
    assert_eq!(Rm::ALL.len(), 5);
    let panics = |f: fn()| std::panic::catch_unwind(f).is_err();
    assert!(panics(|| {
        canonical_nan(Format { eb: 16, sb: 2 });
    }));
    assert!(panics(|| {
        canonical_nan(Format { eb: 1, sb: 2 });
    }));
    assert!(panics(|| {
        canonical_nan(Format { eb: 2, sb: 1 });
    }));
    assert!(panics(|| {
        canonical_nan(Format { eb: 15, sb: 498 });
    }));
    assert!(panics(|| {
        add(B32, Rm::Rne, &bw(32, 0), &bw(64, 0));
    }));
    assert!(panics(|| {
        to_sint(B32, Rm::Rne, &bw(32, 0), 0);
    }));
    assert!(panics(|| {
        to_uint(B32, Rm::Rne, &bw(32, 0), 513);
    }));
    assert!(panics(|| {
        from_sint(B32, Rm::Rne, &Bits::zero(513));
    }));
    assert!(panics(|| {
        x87_load(&bw(79, 0));
    }));
    assert!(panics(|| {
        x87_store(&bw(80, 0));
    }));
    assert!(panics(|| {
        neg(B32, &bw(31, 0));
    }));
}
