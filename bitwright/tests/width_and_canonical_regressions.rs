//! Regression tests for width mismatches in MBA cofactors / opaque_predicate / causal narrowing,
//! and canonicalization / simplification / separable-MBA improvements.
#![cfg(all(feature = "mba", feature = "prove"))]

use std::sync::Arc;

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::{
    self, MbaBudget, MbaConfig, MbaLimits, MbaSolver, NfOptions, NormalFormSolver, Verdict,
};
use bitwright::prove::{self, Config as ProveConfig, Outcome};
use bitwright::{BitVec, Bounded, Context, Expr, KnownBits, ParseOptions, View, Width};

fn build_engine(opaque_sweep: bool, words_proved: bool) -> Engine {
    let solver: Arc<dyn MbaSolver> = Arc::new(NormalFormSolver::new(NfOptions::default()));
    let mba_cfg = MbaConfig::default().with_opaque_sweep(opaque_sweep);
    let mut strategy = Strategy::deobfuscate().with_mba(mba_cfg);
    if words_proved {
        strategy = strategy.with_words_proved(true);
    }
    Engine::builder()
        .builtin()
        .strategy(strategy)
        .mba_solver(solver)
        .build()
        .expect("build engine")
}

fn simplify_fuel(engine: &Engine, cx: &mut Context, e: Expr, fuel: u64) -> Expr {
    engine
        .run(cx, &[e], Run::default().with_per_call(Budget::fuel(fuel)))
        .expect("engine run must succeed without WidthError")
        .roots[0]
        .expr
}

fn assert_bitblasted_equal(cx: &mut Context, a: Expr, b: Expr) {
    let cfg = ProveConfig::default()
        .with_simplify(false)
        .with_certificate(false);
    let out = prove::equal(cx, a, b, &cfg).expect("bit-blasted equivalence check failed");
    assert!(
        matches!(out, Outcome::Proved(_)),
        "expected Proved for `{}` == `{}`, got {out:?}",
        cx.display(a),
        cx.display(b)
    );
}

#[test]
fn minimal_txt_cofactors_56_vs_64_width_mismatch() {
    let src = "\
        let %0 = #3:64; \
        let %1 = #1:64 | 0xfe7f3feff7ebffe7; \
        let %2 = %1 * 0xffffcffe2083df59 * %0; \
        let %3 = %1 * 0xffffffff4a38442e * %0; \
        let %4 = %1 * 0xb5cdbad4 * %0; \
        let %5 = %1 * 0xffffcffe2089de5c * %0; \
        let %6 = %4 * 0x8282c0a894022280 \
               + (zext<64>(extract<8, 56>(%5 * 0x7d7d3f576bfddd80)) << 8) \
               + (zext<64>(extract<8, 56>(%5 * 0x37bfd3fa00040100)) << 8) \
               + (zext<64>(extract<8, 56>(%2 * 0xc8402c05fffbff00 + %3 * 0xc8402c05fffbff00 + %4 * 0xc8402c05fffbff00)) << 8) \
               + %1 * 0x5805ef7a1d70e894 * %0; \
        ~%6 ^ %6";
    let mut cx = Context::new();
    let e = cx
        .parse(src, &ParseOptions::width(Width::W64))
        .expect("parse minimal.txt");
    let engine = build_engine(true, false);
    let out = simplify_fuel(&engine, &mut cx, e, 1 << 18);
    assert_eq!(cx.view(out).unwrap(), View::Const(BitVec::ones(Width::W64)));
}

#[test]
fn cofactors_shifted_narrow_extract_preserves_width_and_semantics() {
    // 1) Non-cancelling 64-bit version from `minimal.txt` (must not WidthError).
    let src64 = "\
        let %0 = #3:64; \
        let %1 = #1:64 | 0xfe7f3feff7ebffe7; \
        let %2 = %1 * 0xffffcffe2083df59 * %0; \
        let %3 = %1 * 0xffffffff4a38442e * %0; \
        let %4 = %1 * 0xb5cdbad4 * %0; \
        let %5 = %1 * 0xffffcffe2089de5c * %0; \
        %4 * 0x8282c0a894022280 \
        + (zext<64>(extract<8, 56>(%5 * 0x7d7d3f576bfddd80)) << 8) \
        + (zext<64>(extract<8, 56>(%5 * 0x37bfd3fa00040100)) << 8) \
        + (zext<64>(extract<8, 56>(%2 * 0xc8402c05fffbff00 + %3 * 0xc8402c05fffbff00 + %4 * 0xc8402c05fffbff00)) << 8) \
        + %1 * 0x5805ef7a1d70e894 * %0";
    let mut cx64 = Context::new();
    let e64 = cx64
        .parse(src64, &ParseOptions::width(Width::W64))
        .expect("parse 64-bit sum");
    let engine = build_engine(true, false);
    let out64 = simplify_fuel(&engine, &mut cx64, e64, 1 << 18);
    assert_eq!(cx64.width(out64).unwrap(), Width::W64);

    // 2) 16-bit analogue with 12-bit shifted extracts: exhaustively bit-blast verified!
    let src16 = "\
        let %0 = #3:16; \
        let %1 = #1:16 | 0xfef7; \
        let %2 = %1 * 0xdf59 * %0; \
        let %3 = %1 * 0x442e * %0; \
        let %4 = %1 * 0xbad4 * %0; \
        let %5 = %1 * 0xde5c * %0; \
        %4 * 0x2280 \
        + (zext<16>(extract<4, 12>(%5 * 0xdd80)) << 4) \
        + (zext<16>(extract<4, 12>(%5 * 0x0100)) << 4) \
        + (zext<16>(extract<4, 12>(%2 * 0xff00 + %3 * 0xff00 + %4 * 0xff00)) << 4) \
        + %1 * 0xe894 * %0";
    let mut cx16 = Context::new();
    let e16 = cx16
        .parse(src16, &ParseOptions::width(Width::W16))
        .expect("parse 16-bit sum");
    let out16 = simplify_fuel(&engine, &mut cx16, e16, 1 << 18);
    assert_bitblasted_equal(&mut cx16, e16, out16);
}

#[test]
fn narrow_causal_two_bit_zext_under_three_bit_mask_no_width_error() {
    // Previously `narrow_causal` on `zext<64>(w2)` with `bits = 3` called `c_zext(w2, 3 - 2)`
    // (`c_zext(w2, 1)`), failing with `WidthError::NotWider { from: 2, to: 1 }`.
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let src = "\
        let %0 = extract<0, 2>(y); \
        let %1 = ((x ^ z) + 2 * (x & z) + zext<64>(%0) + (u << 3)) & 7; \
        let %2 = (x + z + zext<64>(%0)) & 7; \
        select(%1 == %2, x, y)";
    let e = cx.parse(src, &o).unwrap();
    let x = cx.parse("x", &o).unwrap();
    let engine = build_engine(true, true);
    let out = simplify_fuel(&engine, &mut cx, e, 1 << 18);
    assert_eq!(out, x);
    assert_bitblasted_equal(&mut cx, e, out);
}

#[test]
fn one_atom_multi_constant_bitwise_reduction() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let (c, m) = (0x100002u64, 0x1ff89be3fbu64);
    let e = cx
        .parse(&format!("(x | {c:#x}) & ((x & {c:#x}) ^ {m:#x})"), &o)
        .unwrap();
    // When `c & !m == 0`, `(x | c) & ((x & c) ^ m) == (x & m) ^ c` (shrinks 7 nodes -> 5 nodes).
    let expected_raw = cx
        .parse(&format!("(x & {m:#x}) ^ {c:#x}"), &o)
        .unwrap();
    let engine = build_engine(false, false);
    let out = simplify_fuel(&engine, &mut cx, e, 1 << 15);
    let expected = simplify_fuel(&engine, &mut cx, expected_raw, 1 << 15);
    assert_eq!(cx.dag_size(&[out], u32::MAX).unwrap(), Bounded::Exact(5));
    assert_bitblasted_equal(&mut cx, e, out);
    assert_bitblasted_equal(&mut cx, out, expected);
}

#[test]
fn complementary_zero_extended_arms_merge_to_select() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let engine = build_engine(false, false);
    for op in ["|", "^", "+"] {
        let src = format!("(x * zext<64>(u == 5)) {op} (y * zext<64>(u != 5))");
        let e = cx.parse(&src, &o).unwrap();
        let out = simplify_fuel(&engine, &mut cx, e, 1 << 15);
        let shown = cx.display(out).to_string();
        assert!(
            shown.starts_with("select("),
            "expected select(...) for `{src}`, got `{shown}`"
        );
        assert_bitblasted_equal(&mut cx, e, out);
    }
}

#[test]
fn additive_select_zero_corners_and_disjoint_or() {
    let mut cx = Context::new();
    let o16 = ParseOptions::width(Width::W16);
    let engine = build_engine(false, false);
    // Pattern 2 with `c01 == 0`: `8 + (-3) == 5 + 0 (mod 2^16)`.
    let e1 = cx
        .parse(
            "select(a == 0, select(b == 0, 8, 5), select(b == 0, 0, 0xfffd))",
            &o16,
        )
        .unwrap();
    let r1 = simplify_fuel(&engine, &mut cx, e1, 1 << 15);
    assert_bitblasted_equal(&mut cx, e1, r1);

    // Pattern 1 with scaled 1-bit arm and disjoint `| 8` inside a sum:
    let e2 = cx
        .parse(
            "select(a == 0, (zext<16>(b == 0) * 3) | 8, zext<16>(b == 0) * 3) + c",
            &o16,
        )
        .unwrap();
    let r2 = simplify_fuel(&engine, &mut cx, e2, 1 << 15);
    let shown2 = cx.display(r2).to_string();
    assert!(
        !shown2.contains("| 8"),
        "expected additive select split, got `{shown2}`"
    );
    assert_bitblasted_equal(&mut cx, e2, r2);
}

#[test]
fn popcnt_zext_trunc_and_shifted_mask_canonicalization() {
    let mut cx = Context::new();
    let o32 = ParseOptions::width(Width::W32);
    let engine = build_engine(false, false);

    // 1a) `popcnt(zext<32>(extract<0, 8>(x))) == zext<32>(popcnt(extract<0, 8>(x)))`
    let eq1 = cx
        .parse(
            "popcnt(zext<32>(extract<0, 8>(x))) == zext<32>(popcnt(extract<0, 8>(x)))",
            &o32,
        )
        .unwrap();
    let r1 = simplify_fuel(&engine, &mut cx, eq1, 1 << 15);
    assert_eq!(cx.view(r1).unwrap(), View::Const(BitVec::ones(Width::W1)));

    // 1b) Non-zero slice `popcnt(zext<32>(extract<4, 8>(x))) == zext<32>(popcnt(extract<4, 8>(x)))`
    let eq1b = cx
        .parse(
            "popcnt(zext<32>(extract<4, 8>(x))) == zext<32>(popcnt(extract<4, 8>(x)))",
            &o32,
        )
        .unwrap();
    let r1b = simplify_fuel(&engine, &mut cx, eq1b, 1 << 15);
    assert_eq!(cx.view(r1b).unwrap(), View::Const(BitVec::ones(Width::W1)));

    // 2) `zext<32>(popcnt(trunc<16>(y))) == popcnt(y)` when high 16 bits of `y` are known zero.
    let y = cx.parse("y", &o32).unwrap();
    let high_zero = BitVec::from_u64(Width::W32, 0xffff_0000).unwrap();
    cx.declare_known(
        y,
        KnownBits::new(high_zero, BitVec::zero(Width::W32)).unwrap(),
    )
    .unwrap();
    let eq2 = cx
        .parse("zext<32>(popcnt(trunc<16>(y))) == popcnt(y)", &o32)
        .unwrap();
    let r2 = simplify_fuel(&engine, &mut cx, eq2, 1 << 15);
    assert_eq!(cx.view(r2).unwrap(), View::Const(BitVec::ones(Width::W1)));

    // 3) `popcnt((x >>u 8) & 0xff) == zext<32>(popcnt(extract<8, 8>(x)))`
    let eq3 = cx
        .parse(
            "popcnt((x >>u 8) & 0xff) == zext<32>(popcnt(extract<8, 8>(x)))",
            &o32,
        )
        .unwrap();
    let r3 = simplify_fuel(&engine, &mut cx, eq3, 1 << 15);
    assert_eq!(cx.view(r3).unwrap(), View::Const(BitVec::ones(Width::W1)));
}

#[test]
fn carry_free_xor_plus_const_canonicalization() {
    let mut cx = Context::new();
    let o32 = ParseOptions::width(Width::W32);
    let engine = build_engine(false, false);
    let e = cx
        .parse("((x & 7) ^ 0xab9d8e9f) + 0x93f96fe8", &o32)
        .unwrap();
    let expected = cx.parse("(x & 7) ^ 0x3f96fe87", &o32).unwrap();
    let out = simplify_fuel(&engine, &mut cx, e, 1 << 15);
    assert_eq!(out, expected);
    assert_bitblasted_equal(&mut cx, e, out);
}

#[test]
fn separable_sum_fast_path_skips_whole_sum_nonlinear_mba_and_simplifies_clusters() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let engine = build_engine(true, false);
    let src = "\
        x * (x ^ 3) + y * (y | 5) + z * (z & 7) + w * (w ^ 9) \
        + ((u ^ v) + 2 * (u & v))";
    let e = cx.parse(src, &o).unwrap();
    let out = simplify_fuel(&engine, &mut cx, e, 1 << 16);
    let shown = cx.display(out).to_string();
    assert!(
        !shown.contains("u ^ v") && !shown.contains("u & v"),
        "expected linear cluster `(u ^ v) + 2 * (u & v)` to simplify, got `{shown}`"
    );
    assert_bitblasted_equal(&mut cx, e, out);

    let plus_one = cx.parse(&format!("({src}) + 1"), &o).unwrap();
    let verdict = mba::equal(&mut cx, out, plus_one, &MbaLimits::default(), &MbaBudget::default())
        .expect("mba::equal");
    assert_ne!(verdict, Verdict::Proved);
}

#[test]
fn demanded_constant_narrowing_and_shared_bitwise_reassociation() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let engine = build_engine(true, false);

    // Shared `u = x ^ c_wide` alongside `u ^ -2` under 32-bit demanded mask unifies with `x ^ c_32`.
    let src = "\
        let u = (x & 7) ^ 0x19319e04478be8ac; \
        let lhs = ((a + (~b & 0xfffa7b3b) + 0x8040) * (u ^ -2) + c * u) & 0xffffffff; \
        let rhs = ((a - (b & 0xfffa7b3b) + 0xfffafb7b) * ((x & 7) ^ 0xb8741752) + c * ((x & 7) ^ 0x478be8ac)) & 0xffffffff; \
        lhs == rhs";
    let eq = cx.parse(src, &o).unwrap();
    let out = simplify_fuel(&engine, &mut cx, eq, 1 << 18);
    assert_eq!(cx.view(out).unwrap(), View::Const(BitVec::ones(Width::W1)));

    // Bit-blast verify on 16-bit analogue.
    let mut cx16 = Context::new();
    let o16 = ParseOptions::width(Width::W16);
    let e16 = cx16
        .parse(
            "let u = (x & 7) ^ 0x9e04; ((a + (~b & 0x7b3b) + 0x0040) * (u ^ -2) + c * u) & 0x00ff",
            &o16,
        )
        .unwrap();
    let out16 = simplify_fuel(&engine, &mut cx16, e16, 1 << 16);
    assert_bitblasted_equal(&mut cx16, e16, out16);
}

#[test]
fn nearly_complementary_xor_pair_and_boolean_mul_idempotence() {
    let mut cx = Context::new();
    let o32 = ParseOptions::width(Width::W32);
    let engine = build_engine(false, false);

    // `0xb8741752 ^ 0x478be8ac == 0xfffffffe` (`-2`); when `x` is known except bit 0,
    // `-(x ^ c1) - (x ^ c2) == 2 - 2 * (u & 1)`, and `(2 - 2 * b) * b == 0`.
    let src = "\
        let b = u & 1; \
        let x = b | 0x2618a2aa; \
        let p = x ^ 0xb8741752; \
        let q = x ^ 0x478be8ac; \
        (-p - q) * b";
    let e = cx.parse(src, &o32).unwrap();
    let out = simplify_fuel(&engine, &mut cx, e, 1 << 16);
    assert_eq!(cx.view(out).unwrap(), View::Const(BitVec::zero(Width::W32)));
    assert_bitblasted_equal(&mut cx, e, out);
}

#[test]
fn known_zero_complement_mask_and_not_trunc_zext() {
    let mut cx = Context::new();
    let o32 = ParseOptions::width(Width::W32);
    let engine = build_engine(false, false);

    let e1 = cx.parse("~(x & 7) & 0xeb348d1f", &o32).unwrap();
    let exp1 = cx.parse("(x & 7) ^ 0xeb348d1f", &o32).unwrap();
    let out1 = simplify_fuel(&engine, &mut cx, e1, 1 << 15);
    assert_eq!(out1, exp1);
    assert_bitblasted_equal(&mut cx, e1, out1);

    let e2 = cx.parse("zext<32>(extract<0, 3>(~(x & 7)))", &o32).unwrap();
    let exp2 = cx.parse("(x & 7) ^ 7", &o32).unwrap();
    let out2 = simplify_fuel(&engine, &mut cx, e2, 1 << 15);
    assert_eq!(out2, exp2);
    assert_bitblasted_equal(&mut cx, e2, out2);
}

#[test]
fn majority_select_and_rotated_bit_mask_unification() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let engine = build_engine(false, false);

    let src = "\
        let b1 = extract<23, 1>(x); \
        let b2 = extract<21, 1>(x); \
        let c = y == 0; \
        let r1 = rotl(x, 41); \
        let r2 = rotl(x, 43); \
        let lhs = zext<64>((b1 & b2) | ((b1 | b2) & c)) + zext<64>(b1) * 5 + zext<64>(b2); \
        let rhs = (((r1 ^ zext<64>(c)) & (r2 ^ r1) ^ r1) & 1) + (r1 & 1) * 5 + (r2 & 1); \
        lhs == rhs";
    let eq = cx.parse(src, &o).unwrap();
    let out = simplify_fuel(&engine, &mut cx, eq, 1 << 16);
    assert_eq!(cx.view(out).unwrap(), View::Const(BitVec::ones(Width::W1)));

    // Bit-blast verify on 16-bit analogue.
    let mut cx16 = Context::new();
    let o16 = ParseOptions::width(Width::W16);
    let e16 = cx16
        .parse(
            "let b1 = extract<5, 1>(x); let b2 = extract<3, 1>(x); let c = y == 0; \
             zext<16>((b1 & b2) | ((b1 | b2) & c))",
            &o16,
        )
        .unwrap();
    let out16 = simplify_fuel(&engine, &mut cx16, e16, 1 << 15);
    assert_bitblasted_equal(&mut cx16, e16, out16);
}

#[test]
fn multi_term_carry_cancel_and_concat_zext_condition() {
    let mut cx = Context::new();
    let o16 = ParseOptions::width(Width::W16);
    let engine = build_engine(false, false);

    let eq1 = cx
        .parse("((a + b + c + d) <u (b + d)) == (~(b + d) <u (a + c))", &o16)
        .unwrap();
    let out1 = simplify_fuel(&engine, &mut cx, eq1, 1 << 15);
    assert_eq!(cx.view(out1).unwrap(), View::Const(BitVec::ones(Width::W1)));

    let e2 = cx.parse("concat(zext<13>(a == 0), 6:3)", &o16).unwrap();
    let exp2 = cx.parse("select(a == 0, 14:16, 6:16)", &o16).unwrap();
    let out2 = simplify_fuel(&engine, &mut cx, e2, 1 << 15);
    assert_eq!(out2, exp2);
    assert_bitblasted_equal(&mut cx, e2, out2);
}

#[test]
fn mba_correlated_xor_and_nested_mask_peer_atoms() {
    let mut cx = Context::new();
    let o16 = ParseOptions::width(Width::W16);
    let engine = build_engine(true, false);
    // Under `Reading::Linear` (where non-uniform constant bitwise ops are atoms), 9 raw atoms
    // (`x ^ 3`, `x ^ 5`, `y & 7`, `y & 5`, `y & 2`, plus `a`, `b`, `c`, `d`) exceed `max_vars = 8`,
    // and `PeerSolved` deduplicates `(x ^ 3, x ^ 5)` and `(y & 7, y & 5, y & 2)` down to 6 atoms.
    let eq_src = "\
        let p = (x * z) ^ 3; \
        let q = (x * z) ^ 5; \
        let r = u * v; \
        (p + q - 2 * (p & q) + (r & 7) - (r & 5) - (r & 2) + a + b + c + d) \
        == (6 + a + b + c + d)";
    let eq = cx.parse(eq_src, &o16).unwrap();
    let out = simplify_fuel(&engine, &mut cx, eq, 1 << 18);
    assert_eq!(
        cx.view(out).unwrap(),
        View::Const(BitVec::ones(Width::W1)),
        "expected 1:1, got `{}`",
        cx.display(out)
    );

    let mut cx_small = Context::new();
    let core_e = cx_small
        .parse(
            "let p = (x * y) ^ 3; let q = (x * y) ^ 5; let r = u * v; \
             p + q - 2 * (p & q) + (r & 7) - (r & 5) - (r & 2)",
            &o16,
        )
        .unwrap();
    let core_out = simplify_fuel(&engine, &mut cx_small, core_e, 1 << 16);
    assert_eq!(
        cx_small.view(core_out).unwrap(),
        View::Const(BitVec::from_u64(Width::W16, 6).unwrap())
    );
    assert_bitblasted_equal(&mut cx_small, core_e, core_out);
}

#[test]
fn width_128_casts_and_compares_consts_never_panic() {
    let mut cx = Context::new();
    let w128 = Width::new(128).unwrap();
    let o128 = ParseOptions::width(w128);
    let engine = build_engine(false, false);

    // Non-contiguous mask in `zext<128>(extract<8, 16>(x) & 0x55aa)` and inverted variant:
    // exercises >64-bit `BitVec::wrapping_from_u64` instead of `mk_const_u64`.
    let e1 = cx
        .parse("zext<128>(extract<8, 16>(x) & 0x55aa:16)", &o128)
        .unwrap();
    let r1 = simplify_fuel(&engine, &mut cx, e1, 1 << 15);
    let exp1 = cx.parse("(x >>u 8) & 0x55aa", &o128).unwrap();
    assert_eq!(r1, exp1);
    assert_bitblasted_equal(&mut cx, e1, r1);

    let e2 = cx
        .parse("zext<128>(~extract<8, 16>(x) & 0x55aa:16)", &o128)
        .unwrap();
    let r2 = simplify_fuel(&engine, &mut cx, e2, 1 << 15);
    assert_bitblasted_equal(&mut cx, e2, r2);

    // `one_value` substituting `x & 255` at width 128 when `extract<0, 8>(x) == 5` (`5 + 10 == 5 * 3`).
    let e3 = cx
        .parse(
            "select(extract<0, 8>(x) == 5:8, 15, (x & 255) * 3)",
            &o128,
        )
        .unwrap();
    let r3 = simplify_fuel(&engine, &mut cx, e3, 1 << 15);
    let exp3 = cx.parse("(x & 255) * 3", &o128).unwrap();
    assert_eq!(r3, exp3);
    assert_bitblasted_equal(&mut cx, e3, r3);
}

#[test]
fn mba_chained_peer_solved_and_opposite_sign_product_atoms() {
    let mut cx = Context::new();
    let o8 = ParseOptions::width(Width::W8);
    let engine = build_engine(true, false);

    // Chained nested masks `[r & 2, r & 7, r]` where `r & 2` first targets `r & 7` and `r & 7`
    // then targets `r`, plus chained xor+mask `[(t ^ 5) & 7, t ^ 3, t ^ 5]`.
    let src1 = "\
        let r = u * v; \
        let t = x * y; \
        ((r & 2) + (r & 5) - (r & 7) + (r ^ r)) \
        + (((t ^ 5) & 7) - ((t ^ 5) & 5) - ((t ^ 5) & 2)) \
        + ((t ^ 3) + (t ^ 5) - 2 * ((t ^ 3) & (t ^ 5))) \
        + a + b + c";
    let e1 = cx.parse(src1, &o8).unwrap();
    let r1 = simplify_fuel(&engine, &mut cx, e1, 1 << 18);
    let exp1 = cx.parse("6 + a + b + c", &o8).unwrap();
    let r1_exp = simplify_fuel(&engine, &mut cx, exp1, 1 << 15);
    assert_eq!(r1, r1_exp);

    // Opposite-sign nonlinear product atoms `((x - 2) * m) + ((2 - x) * m)` with 7 extra variables.
    let src2 = "\
        let m = (u ^ 3) | 1; \
        let p = (x + 0xfe) * m; \
        let q = (2 - x) * m; \
        p + q + a + b + c + d + e + f + g";
    let e2 = cx.parse(src2, &o8).unwrap();
    let r2 = simplify_fuel(&engine, &mut cx, e2, 1 << 18);
    let exp2 = cx.parse("a + b + c + d + e + f + g", &o8).unwrap();
    let r2_exp = simplify_fuel(&engine, &mut cx, exp2, 1 << 15);
    assert_eq!(r2, r2_exp);

    let mut cx_small = Context::new();
    let e_core = cx_small
        .parse(
            "let m = (u ^ 3) | 1; ((x + 0xfe) * m) + ((2 - x) * m)",
            &o8,
        )
        .unwrap();
    let r_core = simplify_fuel(&engine, &mut cx_small, e_core, 1 << 16);
    assert_eq!(
        cx_small.view(r_core).unwrap(),
        View::Const(BitVec::zero(Width::W8))
    );
    assert_bitblasted_equal(&mut cx_small, e_core, r_core);
}

#[test]
fn memo_provisionality_when_shared_node_becomes_single_use() {
    let mut cx = Context::new();
    let o32 = ParseOptions::width(Width::W32);
    let engine = build_engine(false, false);

    // Run 1: `m = x & 0xff0f` has two live users (`m >>u 4` and `m * 3`), so `(x & 0xff0f) >>u 4`
    // declines on sharing (`Fin::PROVISIONAL`, NOT `Fin::FINAL`).
    let shared_root = cx
        .parse("let m = x & 0xff0f; (m >>u 4) + m * 3", &o32)
        .unwrap();
    let out1 = simplify_fuel(&engine, &mut cx, shared_root, 1 << 15);
    assert_bitblasted_equal(&mut cx, shared_root, out1);

    // Run 2 in the SAME `Context`: `m >>u 4` is now the sole user of `m = x & 0xff0f` and must
    // simplify to `(x >>u 4) & 0x0ff0` rather than returning a stale memoized `m >>u 4`.
    let solo = cx.parse("(x & 0xff0f) >>u 4", &o32).unwrap();
    let out2 = simplify_fuel(&engine, &mut cx, solo, 1 << 15);
    let expected = cx.parse("(x >>u 4) & 0x0ff0", &o32).unwrap();
    assert_eq!(out2, expected);
    assert_bitblasted_equal(&mut cx, solo, out2);
}

#[test]
fn zero_cycles_cut_invariant_across_casts_shuffle_linear_mba() {
    let engine = build_engine(true, true);
    for src in [
        // `zext(extract<23, 1>(x))` alongside `rotl(x, 41) & 1` and `(x >>u 23) & 1`.
        "zext<64>(extract<23, 1>(x)) + (rotl(x, 41) & 1) * 3 + ((x >>u 23) & 1) * 5",
        // Multiple disjoint `Or` subtrees flattened into an additive spine.
        "let p = (a & 4) | 1; let q = (b & 8) | 2; c + p + q + (d & 16)",
        // `zext(extract<8, 16>(x) & 7)` single-bit-run mask vs `Shuffle`.
        "zext<64>(extract<8, 16>(x) & 7:16) + ((x >>u 8) & 7)",
        // Majority `& 1` narrowing alongside live slices.
        "let r1 = rotl(x, 41); let r2 = rotl(x, 43); let c = y == 0; \
         (((r1 ^ zext<64>(c)) & (r2 ^ r1) ^ r1) & 1) + zext<64>(extract<23, 1>(x))",
    ] {
        let mut cx = Context::new();
        let e = cx.parse(src, &ParseOptions::width(Width::W64)).unwrap();
        let run_out = engine
            .run(
                &mut cx,
                &[e],
                Run::default().with_per_call(Budget::fuel(1 << 17)),
            )
            .expect("engine run");
        assert_eq!(
            run_out.stats.cycles_cut, 0,
            "expected 0 cycles_cut on `{src}`, got {}",
            run_out.stats.cycles_cut
        );
    }
}

#[test]
fn p1_and_p2_identities_demorgan_cofactor_borrow_free_sub_demanded_and_compares() {
    let engine = build_engine(true, true);
    let o16 = ParseOptions::width(Width::W16);

    // 1) `other & zext<16>(bit)` 1-bit narrowing (Cluster V2a).
    {
        let mut cx = Context::new();
        let src = "\
            let b = c == 0; \
            let lhs = ((x >>u 2) ^ (y >>u 3)) & zext<16>(b); \
            let rhs = zext<16>((extract<2, 1>(x) ^ extract<3, 1>(y)) & b); \
            lhs == rhs";
        let eq = cx.parse(src, &o16).unwrap();
        let out = simplify_fuel(&engine, &mut cx, eq, 1 << 16);
        assert_eq!(cx.view(out).unwrap(), View::Const(BitVec::ones(Width::W1)));
    }

    // 2) De Morgan `(~u) & (~v)` in `by_multiplicand` + 1-bit `(b ^ C)` factor + cofactor known bits (V2c).
    {
        let mut cx = Context::new();
        let src = "\
            let m = (0x1063 - a * 4) | (b * 8); \
            let g1 = (x ^ 0x000a) | (y ^ 0x000a); \
            let g2 = (x ^ 0xfff5) & (y ^ 0xfff5); \
            let b0 = u & 1; \
            (g1 * (m & 3) + g2 * 3 + 3) + ((0x8040 - b0) * v + (b0 ^ 0x8041) * v - 0x8041 * v)";
        let e = cx.parse(src, &o16).unwrap();
        let out = simplify_fuel(&engine, &mut cx, e, 1 << 18);
        assert_bitblasted_equal(&mut cx, e, out);

        // Exact identity where both halves cancel to 0:
        let zero_src = "\
            let m = (0x1063 - a * 4) | (b * 8); \
            let g1 = (x ^ 0x000a) | (y ^ 0x000a); \
            let g2 = (x ^ 0xfff5) & (y ^ 0xfff5); \
            let b0 = u & 1; \
            (g1 * (m & 3) + g2 * 3 + 3) + ((b0 ^ 0x8041) * v - (0x8041 - b0) * v)";
        let ez = cx.parse(zero_src, &o16).unwrap();
        let out_z = simplify_fuel(&engine, &mut cx, ez, 1 << 18);
        assert_eq!(cx.view(out_z).unwrap(), View::Const(BitVec::zero(Width::W16)));
        assert_bitblasted_equal(&mut cx, ez, out_z);
    }

    // 3) Borrow-free `c2 - (x ^ c1) -> x ^ k` and `-1 - (x ^ c1) -> x ^ ~c1` (Cluster V2d).
    {
        let mut cx = Context::new();
        let e1 = cx.parse("0xffba - ((x & 0xffba) ^ 0x0012)", &o16).unwrap();
        let r1 = simplify_fuel(&engine, &mut cx, e1, 1 << 15);
        let exp1 = cx.parse("(x & 0xffba) ^ 0xffa8", &o16).unwrap();
        assert_eq!(r1, exp1);
        assert_bitblasted_equal(&mut cx, e1, r1);

        let e2 = cx.parse("0xffff - (x ^ 0x1234)", &o16).unwrap();
        let r2 = simplify_fuel(&engine, &mut cx, e2, 1 << 15);
        let exp2 = cx.parse("x ^ 0xedcb", &o16).unwrap();
        assert_eq!(r2, exp2);
        assert_bitblasted_equal(&mut cx, e2, r2);
    }

    // 4) Demanded `Select` + `RotL` + multi-use `Add`/`Sub` constant narrowing + `narrow_to_live_wide` high-bit const.
    {
        let mut cx = Context::new();
        let src = "\
            let s = x + 0xfe05; \
            let mux = select(c == 0, rotl(s, 8), rotl(x + 5, 8)); \
            (rotr(mux, 8) + s) & 0x00ff";
        let e = cx.parse(src, &o16).unwrap();
        let out = simplify_fuel(&engine, &mut cx, e, 1 << 16);
        assert_bitblasted_equal(&mut cx, e, out);

        let mut cx2 = Context::new();
        let src2 = "\
            let w16 = x | 0xfe6f; \
            let n8 = extract<0, 8>(x) | 0x6f:8; \
            zext<16>(n8) + (w16 & 0x00ff)";
        let e2 = cx2.parse(src2, &o16).unwrap();
        let out2 = simplify_fuel(&engine, &mut cx2, e2, 1 << 16);
        assert_bitblasted_equal(&mut cx2, e2, out2);
    }

    // 5) Bare-base `x + (x ^ -2)`, 1-bit `Mul`, boolean `b * (b ^ c)`, 4-way carry cancel,
    //    linear `Eq` term cancellation, and `select` arm guard specialization.
    {
        let mut cx = Context::new();
        let e_xor = cx.parse("x + (x ^ 0xfffe)", &o16).unwrap();
        let r_xor = simplify_fuel(&engine, &mut cx, e_xor, 1 << 15);
        assert_bitblasted_equal(&mut cx, e_xor, r_xor);

        let e_mul1 = cx.parse("(a == 0) * (b == 0)", &o16).unwrap();
        let r_mul1 = simplify_fuel(&engine, &mut cx, e_mul1, 1 << 15);
        assert_bitblasted_equal(&mut cx, e_mul1, r_mul1);

        let e_bmul = cx.parse("(x & 1) * ((x & 1) ^ 0x1235)", &o16).unwrap();
        let r_bmul = simplify_fuel(&engine, &mut cx, e_bmul, 1 << 15);
        let exp_bmul = cx.parse("(x & 1) * 0x1234", &o16).unwrap();
        assert_eq!(r_bmul, exp_bmul);
        assert_bitblasted_equal(&mut cx, e_bmul, r_bmul);

        let eq_ult = cx
            .parse("((b + d) <u (a + b + c + d)) == ((b + d) <u -(a + c))", &o16)
            .unwrap();
        let r_ult = simplify_fuel(&engine, &mut cx, eq_ult, 1 << 15);
        assert_eq!(cx.view(r_ult).unwrap(), View::Const(BitVec::ones(Width::W1)));

        let eq_ule = cx
            .parse("((a + b + c + d) <=u (b + d)) == (-(a + c) <=u (b + d))", &o16)
            .unwrap();
        let r_ule = simplify_fuel(&engine, &mut cx, eq_ule, 1 << 15);
        assert_eq!(cx.view(r_ule).unwrap(), View::Const(BitVec::ones(Width::W1)));

        let e_lin_eq = cx.parse("(x * 3 + 5) == (x + 9)", &o16).unwrap();
        let r_lin_eq = simplify_fuel(&engine, &mut cx, e_lin_eq, 1 << 15);
        assert_bitblasted_equal(&mut cx, e_lin_eq, r_lin_eq);

        let e_sel = cx
            .parse("select(x == 5, y, y + (zext<16>(x != 5) - 1) * z)", &o16)
            .unwrap();
        let r_sel = simplify_fuel(&engine, &mut cx, e_sel, 1 << 15);
        let exp_sel = cx.parse("y", &o16).unwrap();
        assert_eq!(r_sel, exp_sel);
        assert_bitblasted_equal(&mut cx, e_sel, r_sel);

        // Same-guard bitwise select merge + zero-annihilating shared select factor on `Eq`.
        let e_rot_sel = cx
            .parse(
                "let c = u == 0; let s = select(c, 0:16, 3); \
                 ((select(c, x >>u 4, 0x0123) | select(c, x << 12, 0x4000)) * s) \
                 == (select(c, rotl(x, 12), 0x4123) * s)",
                &o16,
            )
            .unwrap();
        let r_rot_sel = simplify_fuel(&engine, &mut cx, e_rot_sel, 1 << 16);
        assert_eq!(
            cx.view(r_rot_sel).unwrap(),
            View::Const(BitVec::ones(Width::W1))
        );
        assert_bitblasted_equal(&mut cx, e_rot_sel, r_rot_sel);

        // Masked-XOR complementary factor pairing `((v & 5) ^ c1)` vs `((v & 4) ^ c2)` when bit 0 of `v` is known.
        let e_mxor = cx
            .parse(
                "let v = (a << 2) | 3; \
                 let f1 = (v & 5) ^ 0x1750; \
                 let f2 = (v & 4) ^ 0xe8af; \
                 f1 * y + f2 * y",
                &o16,
            )
            .unwrap();
        let r_mxor = simplify_fuel(&engine, &mut cx, e_mxor, 1 << 16);
        assert_eq!(
            cx.view(r_mxor).unwrap(),
            View::Const(BitVec::zero(Width::W16))
        );
        assert_bitblasted_equal(&mut cx, e_mxor, r_mxor);
    }
}

#[test]
fn signature_guided_dag_dedup_merges_nested_equivalent_subtrees() {
    let engine = build_engine(true, true);
    let o16 = ParseOptions::width(Width::W16);

    // 1) Size-tied interior subtrees `p = (a | b) & 7` vs `q = b | (a & 7)` (`b = ~rotl(u, 15) & 4`)
    //    nested inside an identical degree-3 nonlinear polynomial `F(p) == F(q)`.
    {
        let mut cx = Context::new();
        let src = "\
            let b = ~rotl(u, 15) & 4; \
            let p = (a | b) & 7; \
            let q = b | (a & 7); \
            (((c + (p ^ 204)) & (c + (p ^ 130) ^ 59) & 255 | 0x8200) * (p ^ 0x3d4f) * (p ^ 0xe8ac)) \
            == (((c + (q ^ 204)) & (c + (q ^ 130) ^ 59) & 255 | 0x8200) * (q ^ 0xe8ac) * (q ^ 0x3d4f))";
        let eq = cx.parse(src, &o16).unwrap();
        let out = simplify_fuel(&engine, &mut cx, eq, 1 << 17);
        assert_eq!(cx.view(out).unwrap(), View::Const(BitVec::ones(Width::W1)));
        assert_bitblasted_equal(&mut cx, eq, out);
    }

    // 2) Non-prefix demanded mask over `select` subtrees differing only on un-demanded high bits.
    {
        let mut cx = Context::new();
        let src = "\
            let lo = x & 0x00ff; \
            let d = (0x6323 - lo) + 0x1111; \
            let s1 = select(c == 0, d & ((0x0023 - lo) | 0xc004), 0x4806); \
            let s2 = select(c == 0, d & ((0x6323 - lo) | 0xc004), 0x4806); \
            (k1 * (~s1 >>u 14) ^ k2 * ((s1 >>u 2) & 0x0031)) \
            == (k1 * (~s2 >>u 14) ^ k2 * ((s2 >>u 2) & 0x0031))";
        let eq = cx.parse(src, &o16).unwrap();
        let out = simplify_fuel(&engine, &mut cx, eq, 1 << 17);
        assert_eq!(cx.view(out).unwrap(), View::Const(BitVec::ones(Width::W1)));
        assert_bitblasted_equal(&mut cx, eq, out);
    }
}

#[test]
fn small_support_known_bits_and_modular_bridge_constant_round_trips() {
    let engine = build_engine(true, true);
    let o16 = ParseOptions::width(Width::W16);

    // 1) Disguised `mult + add/sub` round-trip recovering passed-in constant `0x4242` via
    //    2-adic zero-divisor + `u * (u + 1)` parity noise annihilation (`0x4242 * 0x6000 + 0x8242 == 0x4242`).
    {
        let mut cx = Context::new();
        let src = "(0x4242 + (y << 3) + (u * (u + 1)) * 4) * 0x6000 + 0x8242";
        let e = cx.parse(src, &o16).unwrap();
        let out = simplify_fuel(&engine, &mut cx, e, 1 << 15);
        assert_eq!(
            cx.view(out).unwrap(),
            View::Const(BitVec::from_u64(Width::W16, 0x4242).unwrap())
        );
        assert_bitblasted_equal(&mut cx, e, out);
    }

    // 2) Affine inverse round-trip through MSB sign-bit XOR `^ 0x8000` (`0x3335 * 0xf33d == 1 mod 2^16`):
    //    `(((0x1337 + x * 0x3335) ^ 0x8000) * 0xf33d) - x - ((0x1337 + 0x8000) * 0xf33d) + 0x1337 == 0x1337`.
    {
        let mut cx = Context::new();
        // Verify modular inverse: `5 * 0xcd == 0x401`; at 16 bits, `5 * 0xcccd == 0x40001 == 1 (mod 2^16)`!
        // With `K = 0x1337`: `((0x1337 + x * 5) ^ 0x8000) * 0xcccd - x + 0x1ff4 == 0x1337`? Compute constant directly:
        let src = "(((0x1337 + x * 5) ^ 0x8000) * 0xcccd) - x - ((0x9337 * 0xcccd) - 0x1337)";
        let e = cx.parse(src, &o16).unwrap();
        let out = simplify_fuel(&engine, &mut cx, e, 1 << 15);
        assert_eq!(
            cx.view(out).unwrap(),
            View::Const(BitVec::from_u64(Width::W16, 0x1337).unwrap())
        );
        assert_bitblasted_equal(&mut cx, e, out);
    }

    // 3) Small-support (<= 3 unknown bits) nonlinear mult+add round-trip recovering constant `0x5a5a`,
    //    plus 1-unknown-bit canonicalization unifying `v + C1`, `w | C2`, `-(y ^ C3)`, and `(z | C4) & C5`.
    {
        let mut cx = Context::new();
        // For `t = x & 3` (`t in 0..4`), `t * (t - 1) * (t - 2) * (t - 3)` is divisible by `4! = 24` (multiple of 8),
        // so multiplying by `0x2000` (`8192`, `8 * 8192 = 65536 = 0 mod 2^16`) annihilates it on all 4 states!
        let src_const = "\
            let t = x & 3; \
            0x5a5a + (t * (t + 0xffff) * (t + 0xfffe) * (t + 0xfffd)) * 0x2000";
        let ec = cx.parse(src_const, &o16).unwrap();
        let rc = simplify_fuel(&engine, &mut cx, ec, 1 << 16);
        assert_eq!(
            cx.view(rc).unwrap(),
            View::Const(BitVec::from_u64(Width::W16, 0x5a5a).unwrap())
        );
        assert_bitblasted_equal(&mut cx, ec, rc);

        let src_1bit = "\
            let v = (x & 4) | 3; \
            let w = x & 4; \
            let lhs = (v + 0x174e) + (-(((x & 4) | 1) ^ 0xe8ae)); \
            let rhs = (w | 0x1751) * 2; \
            lhs == rhs";
        let e1b = cx.parse(src_1bit, &o16).unwrap();
        let r1b = simplify_fuel(&engine, &mut cx, e1b, 1 << 16);
        assert_eq!(cx.view(r1b).unwrap(), View::Const(BitVec::ones(Width::W1)));
        assert_bitblasted_equal(&mut cx, e1b, r1b);
    }
}

#[test]
fn xor_complement_zext_peers_nonzero_select_facts_and_bit_table_multi_carry() {
    let engine = build_engine(true, true);
    let prover = bitwright::prove::Simplifiers::new();

    // 1) `Facts::nonzero_select_bound`: 128-bit `udiv(zext<128>(a + 1), select(z == 0, 1, z))`
    //    where `z = zext<128>(b:64)` fits in 64 bits (`%1 == zext<128>(trunc<64>(%1))` -> true).
    {
        let mut cx = Context::new();
        let w128 = Width::new(128).unwrap();
        let src = "\
            let z = zext<128>(b:64); \
            let q = udiv(zext<128>(a:64 + 1), select(z == 0, 1, z)); \
            q == zext<128>(trunc<64>(q))";
        let eq = cx.parse(src, &ParseOptions::width(w128)).unwrap();
        let out = simplify_fuel(&engine, &mut cx, eq, 1 << 15);
        assert_eq!(cx.view(out).unwrap(), View::Const(BitVec::ones(Width::W1)));

        // Also `select(b == 0, 3:128, zext<128>(b))` (cross-width zero check against `Zext(b)`):
        let src2 = "\
            let q = udiv(zext<128>(a:64), select(b:64 == 0, 3:128, zext<128>(b))); \
            q == zext<128>(trunc<64>(q))";
        let eq2 = cx.parse(src2, &ParseOptions::width(w128)).unwrap();
        let out2 = simplify_fuel(&engine, &mut cx, eq2, 1 << 15);
        assert_eq!(cx.view(out2).unwrap(), View::Const(BitVec::ones(Width::W1)));
    }

    // 2) `Facts::opposite_bit0`: generalized opposite-parity products (`(x ^ 2) * (x ^ 5)`) get
    //    `trailing_known_zeros >= 1` directly in `Facts`, folding `* 0x8000` to `0` at 16 bits.
    {
        let mut cx = Context::new();
        let o16 = ParseOptions::width(Width::W16);
        let e = cx.parse("((x ^ 2) * (x ^ 5)) * 0x8000", &o16).unwrap();
        let out = simplify_fuel(&engine, &mut cx, e, 1 << 15);
        assert_eq!(cx.view(out).unwrap(), View::Const(BitVec::zero(Width::W16)));
        assert_bitblasted_equal(&mut cx, e, out);
    }

    // 3) Complementary XORs (`x ^ c` vs `x ^ ~c`), narrow `zext(u ^ c)` vs `zext(u ^ ~c)` vs `zext(u)`
    //    peer unification + `by_multiplicand` + `poly::XorConst`: proves the 64-bit identity from
    //    `0004-2183ms` (`-(%3 * (%2 ^ K)) - %3 * (%2 ^ ~K)` AND `zext<64>(%0 ^ K32)` vs `zext<64>(%0 ^ ~K32)`).
    {
        let mut cx = Context::new();
        let o64 = ParseOptions::width(Width::W64);
        let src = "\
            let %0 = trunc<32>(x:64); \
            let %1 = zext<64>(%0); \
            let %2 = (%1 | 0x410340d08025a990) & 0x7cf89367efbd | 0x4103000000000000; \
            let %3 = %2 & 0xffffffffffff | 0x4103000000000000; \
            let %4 = -(%3 * (%2 ^ 0xd2d1c1970a4543b5)) - %3 * (%2 ^ 0x2d2e3e68f5babc4a) | 0xff6ffffb3f7efe6d; \
            let %5 = %4 * 0xeaf80aa55c637369; \
            let %6 = %5 * 0x2d2f8e790a59cec9; \
            let %7 = %4 * 0xd5f0154ab8c6e6d2; \
            let %8 = %7 * 0x180110a414281; \
            let %9 = %5 * 0x3000f5a23002; \
            let %10 = %5 * 0xffffcfff0a5dcffd; \
            let %11 = %4 * 0xd5da5854a0a0adad; \
            let %12 = %4 * 0xa14583511aa2a9e2; \
            let %13 = -%7; \
            let %14 = (zext<64>(%0 ^ 0x821f580f) << 11) + 0xefef1800000003e1; \
            let %15 = -(%14 * ((%1 << 26 ^ 0x8e087d603df0f7f7) >>u 15 ^ 0xefee000000000000) + (%14 * ((zext<64>(%0 ^ 0x7de0a7f0) << 11) + 0x1010e0000000041e) & -256 | 94) & -256 | 31) & -256 | 225; \
            let %16 = trunc<32>(%6 + %8 + %9 + %10 + %11 + %12 - %7); \
            let %17 = %15 << (zext<64>(trunc<8>(%16 * 61)) & 63) | %15 >>u (zext<64>(trunc<8>(%16 * -125)) & 63); \
            ~(%6 * 0x6a95e63ebafa8175 + %8 * 0x6a95e63ebafa8175 + %9 * 0x6a95e63ebafa8175 + %10 * 0x6a95e63ebafa8175 + %11 * 0x6a95e63ebafa8175 + %12 * 0x6a95e63ebafa8175 + %13 * 0x6a95e63ebafa8175 & %17) & (~(%8 * 0xc9c68196e2e00f98 + %6 * 0xc9c68196e2e00f98 + %9 * 0xc9c68196e2e00f98 + %10 * 0xc9c68196e2e00f98 + %11 * 0xc9c68196e2e00f98 + %12 * 0xc9c68196e2e00f98 + %13 * 0xc9c68196e2e00f98) | %17) == rotl(((x & 0x7de0a7f0) - (x & 0x821f580f) << 11) + 0xefef1c10fac07be0, 15) ^ 0x8e087d603df077f7";
        let eq = cx.parse(src, &o64).unwrap();
        let cfg = bitwright::prove::Config::default()
            .with_simplify_fuel(1 << 18)
            .with_max_conflicts(2_000)
            .with_max_propagations(20_000);
        let res = bitwright::prove::valid_under_with(&mut cx, eq, None, &cfg, &prover).unwrap();
        assert!(
            matches!(res, bitwright::prove::Outcome::Proved(_)),
            "expected Proved on zext-xor complement identity, got {res:?}"
        );
    }

    // 4) Multi-bit constant mask collapse + disjoint mask pair in `linear::masked` with non-zero
    //    residual constant, plus single-side `select` equality + `guard_samples` `Sub` inversion.
    {
        let mut cx = Context::new();
        let o8 = ParseOptions::width(Width::W8);
        let e_mask = cx
            .parse("(x & 18) * 12 + (y - x) * 6 + 0x90", &o8)
            .unwrap();
        let r_mask = simplify_fuel(&engine, &mut cx, e_mask, 1 << 15);
        assert_bitblasted_equal(&mut cx, e_mask, r_mask);

        let e_disj = cx.parse("(x & 0x50) * 3 - (x & 0x0a) * 3 + 7", &o8).unwrap();
        let r_disj = simplify_fuel(&engine, &mut cx, e_disj, 1 << 15);
        assert_bitblasted_equal(&mut cx, e_disj, r_disj);

        let mut cx64 = Context::new();
        let o64 = ParseOptions::width(Width::W64);
        let src_ref = "\
            let u = a ^ 0xe7262998390b56c8; \
            select((b - 5) >>u 3 == 1, (~(~a & 0xe7262998390b56c8) & ~(a & 0x18d9d667c6f4a937)) * u * 0x61c8864680b583ab + u * u * 0x61c8864680b583ab, c) == c";
        let eq_ref = cx64.parse(src_ref, &o64).unwrap();
        let cfg = bitwright::prove::Config::default()
            .with_max_conflicts(200)
            .with_max_propagations(2000);
        let res_ref =
            bitwright::prove::valid_under_with(&mut cx64, eq_ref, None, &cfg, &prover).unwrap();
        assert!(
            matches!(res_ref, bitwright::prove::Outcome::Refuted(_)),
            "expected fast Refuted via guard_samples + single-side select eq, got {res_ref:?}"
        );
    }

    // 5) `bit_table` multi-cluster carry compensation (`MultiCarryComp`) on folded 6-bit sub-cluster
    //    carries (`0371-124ms` structure over 16-bit input).
    {
        let mut cx = Context::new();
        let o64 = ParseOptions::width(Width::W64);
        let src_bt = "\
            let %0 = trunc<32>(~(zext<64>(zext<32>(x16:16) - 4) * -1) + 1); \
            let %1 = %0 + 0x2f9f8590; \
            let %2 = extract<18, 8>(%1) & 1 != 0; \
            let %3 = extract<19, 8>(%1) & 1; \
            let %4 = %3 != 0; \
            let %5 = %3 == 0; \
            let %6 = select(%2, select(%4, 0x37d9c5f60c0b80cd:64, 0xe3eed707db2d95e2), select(%5, 0:64, 0x53eaeeee30ddeaeb)); \
            let %7 = extract<10, 8>(%1) & 1 != 0; \
            let %8 = extract<11, 8>(%1) & 1; \
            let %9 = %8 != 0; \
            let %10 = select(%7, select(%9, 0xf7a992e3ade7ebe6:64, 0x23f98183526cab00), select(%8 == 0, 0:64, 0xd3b011605b7b40e6)); \
            let %11 = trunc<8>(%1); \
            let %12 = %11 >>u 6 & 1; \
            let %13 = %11 & -128; \
            let %14 = %13 != 0; \
            let %15 = select(%12 != 0, select(%14, 0xc1d215293480d126:64, 0x38014d7accb533c5), select(%13 == 0, 0:64, 0x89d0c7ae67cb9d61)); \
            let %16 = %11 & 1 != 0; \
            let %17 = %11 >>u 1 & 1; \
            let %18 = %17 != 0; \
            let %19 = %17 == 0; \
            let %20 = select(%16, select(%18, 0x656969889870bfcb:64, 0x58934d6791b5f96e), select(%19, 0:64, 0xcd61c2106bac65d)); \
            let %21 = %11 >>u 2 & 1 != 0; \
            let %22 = %11 >>u 3 & 1; \
            let %23 = %22 != 0; \
            let %24 = %22 == 0; \
            let %25 = select(%21, select(%23, 0xd0d8639095ceabe1:64, 0x5a96ba7c39a02804), select(%24, 0:64, 0x7641a9145c2e83dd)); \
            let %26 = %11 >>u 4 & 1; \
            let %27 = %11 >>u 5 & 1; \
            let %28 = %27 != 0; \
            let %29 = select(%26 != 0, select(%28, 0x8c746ecb98d4f493:64, 0xfb30ecbeb5a3e728), select(%27 == 0, 0:64, 0x9143820ce3310d6b)); \
            let %30 = extract<8, 8>(%1) & 1 != 0; \
            let %31 = extract<9, 8>(%1) & 1; \
            let %32 = %31 != 0; \
            let %33 = select(%30, select(%32, 0x249c6c4ee4c31a5:64, 0x71364f203014c64), select(%31 == 0, 0:64, 0xfb3661d2eb4ae541)); \
            let %34 = extract<14, 8>(%1) & 1; \
            let %35 = extract<15, 8>(%1) & 1; \
            let %36 = %35 != 0; \
            let %37 = select(%34 != 0, select(%36, 0xd81b5d1bfb3743eb:64, 0x3b1964d6ab81f814), select(%35 == 0, 0:64, 0x9d01f8454fb54bd7)); \
            let %38 = extract<12, 8>(%1) & 1 != 0; \
            let %39 = extract<13, 8>(%1) & 1; \
            let %40 = %39 != 0; \
            let %41 = select(%38, select(%40, 0x72bd05afdd29f57:64, 0xa34e974776e37c92), select(%39 == 0, 0:64, 0x63dd391386ef22c5)); \
            let %42 = extract<16, 8>(%1) & 1; \
            let %43 = extract<17, 8>(%1) & 1; \
            let %44 = %43 != 0; \
            let %45 = select(%42 != 0, select(%44, 0x4c910d0e0c30e3da:64, 0x22a495383978d81e), select(%43 == 0, 0:64, 0x29ec77d5d2b80bbc)); \
            let %46 = extract<20, 8>(%1) & 1; \
            let %47 = extract<21, 8>(%1) & 1; \
            let %48 = %47 != 0; \
            let %49 = select(%46 != 0, select(%48, 0xa367a59637babe9b:64, 0xcbfdcd6be0dd22a5), select(%47 == 0, 0:64, 0xd769d82a56dd9bf6)); \
            let %50 = %6 + %10 + %15 + %20 + %25 + %29 + %33 + %37 + %41 + %45 + %49 + 0x913d8ee744f703bc; \
            let %51 = zext<64>(%32); \
            let %52 = zext<64>(zext<32>(%44) << 2); \
            let %53 = zext<64>(zext<32>(%14) * 2); \
            let %54 = %15 + %29; \
            let %55 = zext<64>(%9); \
            let %56 = (%55 << 1) + %55; \
            let %57 = %33 + %10; \
            let %58 = zext<64>(%40); \
            let %59 = zext<64>(%36); \
            let %60 = %37 + %41; \
            let %61 = %57 + %37 + %41; \
            let %62 = %50 ^ 0x874a0fe692594c3a | select(%2, (zext<64>(%4) << 3) + 1, select(%5, 0:64, 7)) + select(%46 == 0, 0, zext<64>(%48) + 5) + select(%30, %51 * 2, %51) + select(%42 == 0, %52, %52 + 5) + select(%26 == 0, 0, zext<64>(%28) | 4) + select(%21, select(%23, 11:64, 5), select(%24, 0:64, 6)) + select(%16, select(%19, 7:64, 14), select(%18, 7:64, 0)) + zext<64>(%25 + %20 <u %25) + select(%12 == 0, %53, %53 + 4) + zext<64>(%54 <u %15) + zext<64>(%15 + %20 + %25 + %29 <u %54) + select(%7, %56 + 6, %56) + zext<64>(%57 <u %10) + select(%38, (%58 << 1) + %58 + 1, zext<64>(zext<32>(%40) * 2)) + select(%34 == 0, %59, %59 + 7) + zext<64>(%60 <u %37) + zext<64>(%61 <u %60) + zext<64>(%15 + %10 + %20 + %25 + %29 + %33 + %37 + %41 <u %61) + zext<64>(%50 <u %45 + %6 + %49 + 0x913d8ee744f703bc) + 24 ^ 70 == 0; \
            let %63 = zext<64>(trunc<32>(zext<64>(~%0) | 0xffffffff00000000)) | 0xffffffff00000000; \
            let %64 = select(%62, (%63 + 0x5b639bfff5fe3eb1 & (select(%62, 9:64, 251) + 0x1400ef08c | %63 + 0x2210ba5e064080f)) >>u 10, 0x30aae08169b88); \
            ((~%64 ^ %64) & 0x610010680043894 ^ %64) & 0xf867d0f83760852a == 0x300a800008108";
        let eq_bt = cx.parse(src_bt, &o64).unwrap();
        let out_bt = simplify_fuel(&engine, &mut cx, eq_bt, 1 << 17);
        assert!(
            matches!(cx.view(out_bt).unwrap(), View::Const(_) | View::Cmp(..)),
            "expected bit_table multi-carry to collapse 328-node guard to a direct comparison or constant, got {:?}",
            cx.view(out_bt).unwrap()
        );
        assert_bitblasted_equal(&mut cx, eq_bt, out_bt);
        let cfg_bt = bitwright::prove::Config::default()
            .with_simplify_fuel(1 << 17)
            .with_max_conflicts(200)
            .with_max_propagations(2000);
        let res_bt =
            bitwright::prove::valid_under_with(&mut cx, eq_bt, None, &cfg_bt, &prover).unwrap();
        assert!(
            matches!(
                res_bt,
                bitwright::prove::Outcome::Proved(_) | bitwright::prove::Outcome::Refuted(_)
            ),
            "expected decided outcome on 0371-124ms bit_table query, got {res_bt:?}"
        );
    }

    // 6) Sparse `kb_mul` non-overlapping partial-product known bits + Hacker's Delight signed
    //    overflow sign-test elimination (`ssub.overflow`, `sadd.overflow`, `~a + b` borrow).
    {
        for bits in [8u16, 16, 32, 64] {
            let mut cx = Context::new();
            let w = Width::new(bits).unwrap();
            let opt = ParseOptions::width(w);
            // Sparse `kb_mul`: `(x & 5) * (y & 16)` only touches bits `{4, 6}` when `bits >= 8`.
            let prod = cx.parse("(x & 5) * (y & 16)", &opt).unwrap();
            let kb = cx.facts(prod).unwrap().known();
            assert_eq!(kb.bit(0), Some(false));
            assert_eq!(kb.bit(5), Some(false));
            assert_eq!(kb.bit(7), Some(false));

            // Bounded signed overflow sign-bit tests fold to false (`0:1`), while overflowing
            // operands are NOT falsely folded to `0:1`.
            let half = bits / 2;
            let src_no_ovf = format!(
                "let a = (sext<{bits}>(extract<0, 1>(x)) - (x & 3)) * (y & 3); \
                 let b = zext<{bits}>(trunc<{half}>(z)); \
                 ((a ^ b) & ((~a + b) ^ b)) <s 0"
            );
            let e_no_ovf = cx.parse(&src_no_ovf, &opt).unwrap();
            let r_no_ovf = simplify_fuel(&engine, &mut cx, e_no_ovf, 1 << 15);
            assert_eq!(
                cx.as_const(r_no_ovf).unwrap(),
                Some(bitwright::BitVec::zero(Width::W1)),
                "width {bits}: bounded (~a + b) overflow test should fold to 0"
            );
            if bits <= 16 {
                assert_bitblasted_equal(&mut cx, e_no_ovf, r_no_ovf);
            }

            let e_may_ovf = cx.parse("((x ^ y) & ((~x + y) ^ y)) <s 0", &opt).unwrap();
            let r_may_ovf = simplify_fuel(&engine, &mut cx, e_may_ovf, 1 << 15);
            assert!(
                cx.as_const(r_may_ovf).unwrap().is_none(),
                "width {bits}: unrestricted signed overflow test must not fold to constant"
            );
        }
    }
}

#[test]
fn opaque_predicate_48_leaf_low_cone_boundary_no_panic() {
    // Regression test for `equal_low_cone_zero` 48-input boundary when `!causal` leaf nodes
    // reach index 48 during low-cone collection.
    let src = "\
        let %0 = ~#337011:64; \
        let %1 = %0 & (#336973:64 | 0xffffcffe2160fe4d); \
        let %2 = ~#336973; \
        let %3 = %2 ^ #337011 ^ 0xffffcffe2160fe4d; \
        let %4 = %0 & #336973; \
        let %5 = ~%4 & 0x3001de9f01b2; \
        let %6 = ~(#336973 & 0x3001de9f01b2) & #337011; \
        let %7 = %2 & ~(%0 & 0xffffcffe2160fe4d); \
        let %8 = #337011 | 0xffffcffe2160fe4d; \
        let %9 = %8 & #336973; \
        let %10 = ~(%2 & %8) & ~(%4 & 0x3001de9f01b2); \
        let %11 = %3 * 0x40f7ccfc84b18b4b + #337089:64 + %1 * 0x40f7ccfc84b18b4b + %5 * 0x40f7ccfc84b18b4b + %6 * 0x81ef99f909631696 + %7 * 0x7e106606f69ce96a + %9 * 0x7e106606f69ce96a + %10 * 0x40f7ccfc84b18b4b; \
        let %12 = trunc<32>(%6 * 0xff7fff7dd7ef6fff); \
        let %13 = trunc<32>(%9 * 0xff7fff7dd7ef6fff + %7 * 0xff7fff7dd7ef6fff); \
        let %14 = trunc<32>(%1 * 0xff7fff7dd7ef6fff + %3 * 0xff7fff7dd7ef6fff + %5 * 0xff7fff7dd7ef6fff + %10 * 0xff7fff7dd7ef6fff); \
        let %15 = zext<64>(trunc<32>(zext<64>(%12 * 0xceb1181e + %13 * 0x314ee7e2 + %14 * 0x67588c0f) << 2)); \
        let %16 = %11 << (zext<64>(trunc<8>((%15 << 2) + %15)) & 63) | %11 >>u (zext<64>(trunc<8>(%12 * 0x2de41628 + %13 * 0xd21be9d8 + %14 * 0x16f20b14)) & 63); \
        let %17 = %1 * 0x421332d0572007b7 + %3 * 0x421332d0572007b7 + %5 * 0x421332d0572007b7 + %6 * 0x842665a0ae400f6e + %7 * 0x7bd99a5f51bff092 + %9 * 0x7bd99a5f51bff092 + %10 * 0x421332d0572007b7 + (%16 << zext<64>(%13 * 0x73813f8c + %12 * 0x8c7ec074 + %14 * 0x463f603a & 62) | %16 >>u zext<64>(%13 * 0x14c6bff4 + %12 * 0xeb39400c + %14 * 0xf59ca006 & 62)); \
        let %18 = (%17 << (zext<64>(trunc<8>(%13 * 0xee7c539a + %12 * 0x1183ac66 + %14 * 0x8c1d633)) & 63) | %17 >>u (zext<64>(trunc<8>(%12 * 0x42364c1a + %13 * 0xbdc9b3e6 + %14 * 0x211b260d)) & 63)) + zext<64>(%12 * 0x51dee002 + %13 * 0xae211ffe + %14 * 0x28ef7001) <u #337011; \
        let %19 = %1 * 61 + %3 * 61 + %5 * 61 + %6 * 122 + %7 * -122 + %9 * -122 + %10 * 61; \
        let %20 = zext<64>(%12 * 0xd6728018 + %13 * 0x298d7fe8 + %14 * 0xeb39400c); \
        let %21 = select(%18, %19, %20); \
        let %22 = ~(%1 * 0xf8bb06422beb8150 + %3 * 0xf8bb06422beb8150 + %5 * 0xf8bb06422beb8150 + %6 * 0xf1760c8457d702a0 + %7 * 0xe89f37ba828fd60 + %9 * 0xe89f37ba828fd60 + %10 * 0xf8bb06422beb8150 + %21 + 0xf8bb06436bfddd80); \
        let %23 = ~select(%18, %19 & 0x744f9bc9402227f, %20 & 0x744f9bc9402227f) & ~(~%21 & 0xf8bb06436bfddd80); \
        let %24 = select(%18, %19 ^ 0xf8bb06436bfddd80, %20 ^ 0xf8bb06436bfddd80); \
        let %25 = select(%18, ~(%22 & %1 * 0x85c83c0482a04423 + %3 * 0x85c83c0482a04423 + %5 * 0x85c83c0482a04423 + %6 * 0xb90780905408846 + %7 * 0xf46f87f6fabf77ba + %9 * 0xf46f87f6fabf77ba + %10 * 0x85c83c0482a04423) & %23 * 0x37013168419011 + %24 * 0x37013168419011, ~(%22 & %3 * 0x4068d0404630c3 + %1 * 0x4068d0404630c3 + %5 * 0x4068d0404630c3 + %6 * 0x80d1a0808c6186 + %7 * 0xff7f2e5f7f739e7a + %9 * 0xff7f2e5f7f739e7a + %10 * 0x4068d0404630c3) & %24 * 0x910503210b80c401 + %23 * 0x910503210b80c401); \
        let %26 = %25 << zext<64>(%13 * 0xbafcbf94 + %12 * 0x4503406c + %14 * 0xa281a036 & 62); \
        let %27 = ~%26; \
        let %28 = %25 >>u zext<64>(%13 * 0xcd4b3fec + %12 * 0x32b4c014 + %14 * 0x995a600a & 62); \
        let %29 = ~%28; \
        let %30 = %1 * 0x7982f07c89f7ad6 + %3 * 0x7982f07c89f7ad6 + %5 * 0x7982f07c89f7ad6 + %6 * 0xf305e0f913ef5ac + %7 * 0xf0cfa1f06ec10a54 + %9 * 0xf0cfa1f06ec10a54 + %10 * 0x7982f07c89f7ad6 & (%27 & %29); \
        let %31 = %3 * 0xf867d0f83760852b + %1 * 0xf867d0f83760852b + %5 * 0xf867d0f83760852b + %6 * 0xf0cfa1f06ec10a56 + %7 * 0xf305e0f913ef5aa + %9 * 0xf305e0f913ef5aa + %10 * 0xf867d0f83760852b & (%26 | %28); \
        let %32 = ~(~%30 & (~%31 & %1 * 0xc65041ee97643995 + %3 * 0xc65041ee97643995 + %5 * 0xc65041ee97643995 + %6 * 0x8ca083dd2ec8732a + %7 * 0x735f7c22d1378cd6 + %9 * 0x735f7c22d1378cd6 + %10 * 0xc65041ee97643995)) & ~(%1 * 0x39afbe11689bc66c + %3 * 0x39afbe11689bc66c + %5 * 0x39afbe11689bc66c + %6 * 0x735f7c22d1378cd8 + %7 * 0x8ca083dd2ec87328 + %9 * 0x8ca083dd2ec87328 + %10 * 0x39afbe11689bc66c & (%31 | %30)); \
        let %33 = %28 ^ #337060:64; \
        let %34 = ~#337060; \
        let %35 = %26 ^ %28; \
        let %36 = ~(%27 & %28) & ~(%29 & %26); \
        let %37 = ~(%32 * (%33 ^ %26) + %32 * (~(%34 & %35) & ~(%36 & #337060))) + ((%34 & %36 | %35 & #337060) * 0x44a5e8672092f88c + ((%27 ^ %26) & %33 ^ %26) * 0x44a5e8672092f88c) + 1; \
        let %38 = ~(%37 * (%37 ^ #337011) + %37 * (~(~%37 & #337011) & ~(%0 & %37))) + zext<64>(trunc<32>(%1 * 0x9ef1bd12b0ef03f1 + %3 * 0x9ef1bd12b0ef03f1 + %5 * 0x9ef1bd12b0ef03f1 + %6 * 0x3de37a2561de07e2 + %7 * 0xc21c85da9e21f81e + %9 * 0xc21c85da9e21f81e + %10 * 0x9ef1bd12b0ef03f1) * 0xc4ba72ef); \
        let %39 = %38 + 0x44a5e8672092f88c; \
        let %40 = %39 & 0x39afbe11689bc66b; \
        let %41 = ~%39 & 0xc65041ee97643994; \
        let %42 = (~(~%40 & ~%41) | 0xf867d0f83760852a) & (~(%40 + %41) | 0x7982f07c89f7ad5); \
        let %43 = ~(~(%42 << 10) & ~(%42 >>u 54)) | 0x7fe3ceffffdf3bfd; \
        let %44 = zext<64>((trunc<32>(rotl(%39, 10) ^ 0xde445a8012f2f8f8) | 0xffdf3bfd) * 0xe7fe30) + 0xffffcffe00000d88; \
        let %45 = %43 * 0xf862f5bf5bb30774 + select(%44 == 0xffffcffe00000f58, %38, select(%44 == 0xffffcffe00740f58, #396171:64, select(%44 == 0xffffcffe374812f8, #396169:64, select(%44 == 0xffffcffe37bc12f8, #396167:64, select(%44 == 0xffffcffe383012f8, #396165:64, select(%44 == 0xffffcffe38a412f8, #396163:64, select(%44 == 0xffffcffe39180f58, #396161:64, select(%44 == 0xffffcffe398c0f58, #396159:64, select(%44 == 0xffffcffe3a000f58, #396157:64, select(%44 == 0xffffcffe3a740f58, #396155:64, select(%44 == 0xffffcffe5d4f52f8, #396153:64, select(%44 == 0xffffcffe5dc352f8, #396151:64, select(%44 == 0xffffcffe5e3752f8, #396149:64, select(%44 == 0xffffcffe5eab52f8, #396147:64, select(%44 == 0xffffcffe5f1f4f58, #396145:64, select(%44 == 0xffffcffe5f934f58, #396143:64, select(%44 == 0xffffcffe60074f58, #396141:64, select(%44 == 0xffffcffe607b4f58, #396139:64, select(%44 == 0xffffcffe974f52f8, #396137:64, select(%44 == 0xffffcffe97c352f8, #396135:64, select(%44 == 0xffffcffe983752f8, #396133:64, select(%44 == 0xffffcffe98ab52f8, #396131:64, select(%44 == 0xffffcffe991f4f58, #396129:64, select(%44 == 0xffffcffe99934f58, #396127:64, select(%44 == 0xffffcffe9a074f58, #396125:64, select(%44 == 0xffffcffe9a7b4f58, #396123:64, select(%44 == 0xffffcffefd4812f8, #396121:64, select(%44 == 0xffffcffefdbc12f8, #396119:64, select(%44 == 0xffffcffefe3012f8, #396117:64, select(%44 == 0xffffcffefea412f8, #396115:64, select(%44 == 0xffffcffeff180f58, #396113:64, #396112:64))))))))))))))))))))))))))))))); \
        let %46 = ~%45 & %43 * 0x4bca0f5e8565c66c; \
        let %47 = %45 & %43 * 0xc521cfa1ba99b995; \
        let %48 = ~(~%46 & (~%47 & %43 * 0x203d4b92b4cb052b)) & ~(%43 * 0xf0ae936d8b347ad6 & (%46 | %47)); \
        let %49 = trunc<32>(%43 * 0x7e069afa45762d39); \
        let %50 = ~(%48 >>u zext<64>(%49 * 0x64d5a81a & 62)) & ~(%48 << zext<64>(%49 * 0x2f1e15a6 & 62)); \
        let %51 = zext<64>(%49 * 0x1e4fcef7); \
        let %52 = %50 >>u 50 & 1 == 0; \
        let %53 = ~zext<64>(%52); \
        let %54 = %50 >>u 44 & 1 == 0; \
        let %55 = ~zext<64>(%54); \
        let %56 = trunc<32>(%50); \
        let %57 = %51 * 2 + (zext<64>(trunc<8>(zext<64>(%56 >>u 3 & 1 != 0) - 2)) | -256) + (zext<64>(trunc<8>(zext<64>(%50 >>u 33 & 1 != 0) - 2)) | -256) + zext<64>(zext<32>(%50 >>u 52 & 1 == 0) + zext<32>(%56 >>u 21 & 1 == 0) & zext<32>(%56 >>u 25 & 1 == 0)) + zext<64>(~extract<16, 8>(%50) & 7); \
        let %58 = %55 & %57; \
        let %59 = zext<32>(%54); \
        let %60 = ~%57; \
        let %61 = trunc<32>(%60); \
        let %62 = %59 & %61; \
        let %63 = %56 >>u 29 & 1 == 0; \
        let %64 = ~zext<64>(%63); \
        let %65 = zext<64>(trunc<8>(%64)) | -256; \
        let %66 = (%58 | zext<64>(%62)) & %65; \
        let %67 = ~%62; \
        let %68 = zext<32>(%63); \
        let %69 = %67 & (~trunc<32>(%58) & %68); \
        let %70 = zext<32>(%52); \
        let %71 = %70 & %61; \
        let %72 = ~%71 & %59; \
        let %73 = trunc<32>(%53); \
        let %74 = %68 & %73; \
        let %75 = ~zext<64>(%74); \
        let %76 = trunc<32>(%55); \
        let %77 = trunc<32>(%57); \
        let %78 = %70 & %76; \
        let %79 = (%59 ^ %77) & %68; \
        let %80 = %57 & (%53 & %64); \
        let %81 = %74 & %61; \
        let %82 = %75 & %57; \
        (%43 * 0xebdf003fff80010 | zext<64>(%50 >>u 38 & 1 == 0)) * -1 + %51 + (~(%53 & (%66 | zext<64>(%69))) & ~zext<64>(~trunc<32>(%66) & ~%69 & %70)) * 0x97b425ed097b427 + (~zext<64>(~%72 & %68) & ~zext<64>(%72 & trunc<32>(%65))) * 0x2f684bda12f684bf + ~(~zext<64>(%59 & trunc<32>(%75)) & %57) * 0x5555555555555559 + (~zext<64>((%68 | %59) & %73) & %60) * 0x2f684bda12f684bb + zext<64>(%68 & %70 & (%59 ^ %76) & %77 ^ %59) * 0x5555555555555557 + zext<64>(~(%68 & %77) & %78) * 0x8e38e38e38e38e38 + ~zext<64>(%74 & %59 & %61) * 0x684bda12f684bda3 + zext<64>((%67 ^ %68) & %70) * 0xe38e38e38e38e391 + ~zext<64>(%59 & %73 & (%68 | %77)) * 0xf684bda12f684bdc + ~zext<64>(~(~%78 & %77) & %68) * 0x12f684bda12f684c + (~zext<64>(%79 & %73) & ~zext<64>(~%79 & %70)) * 0x684bda12f684bda3 + (%55 & %80 | zext<64>(~trunc<32>(%80) & %59)) * 0x97b425ed097b425d + (~(~zext<64>(%81) & (%55 & ~%82)) & ~zext<64>((%81 | trunc<32>(%82)) & %59)) * 0x7b425ed097b425ee + zext<64>(((%68 ^ %77) & (%70 ^ %73) ^ %70) & %59) + ~zext<64>(((%59 | %77) & %73 | %71 & %76) & %68) * 0xe38e38e38e38e38a + ~(%57 & (%65 & (zext<64>(trunc<8>(%53 & %55)) | -256))) * 0x84bda12f684bda0f == 0";
    let mut cx = Context::new();
    let e = cx.parse(src, &ParseOptions::width(Width::W64)).unwrap();
    let solver: Arc<dyn MbaSolver> = Arc::new(NormalFormSolver::new(
        NfOptions::default().with_memo(1 << 14).with_basis_sums(true),
    ));
    let strat = Strategy::deobfuscate().with_mba(
        MbaConfig::default()
            .with_opaque_sweep(true)
            .with_noise_forms(true)
            .with_known_atoms(true),
    );
    let engine = Engine::builder()
        .builtin()
        .strategy(strat)
        .mba_solver(solver)
        .build()
        .unwrap();
    let out = simplify_fuel(&engine, &mut cx, e, 524_288);
    assert_eq!(cx.width(out).unwrap(), Width::W1);
}

#[test]
fn demanded_stop_at_shared_multistage_dag_linear_traversal() {
    // Regression test for exponential re-traversal / 4 GiB Vec growth in `demanded::stop_at`
    // when a newly-built (`>= st.before`) multi-stage shared byte-chain DAG is walked without
    // a visited set.
    let src = "\
        let %0 = ~#73699:64; \
        let %1 = ~#65004:64; \
        let %2 = trunc<32>(zext<64>(trunc<16>(zext<64>(trunc<16>(#68930:64 & 65523 | 0x14041000c)) | 0x140410000)) | 0x140410000) & 0xbfffffff; \
        let %3 = ~%2; \
        let %4 = trunc<32>((zext<64>(%3) << 1) + zext<64>(%2)); \
        let %5 = extract<16, 8>(%4); \
        let %6 = zext<32>(%5); \
        let %7 = trunc<32>(#68386:64); \
        let %8 = ~zext<64>(%5); \
        let %9 = ~#68386; \
        let %11 = trunc<32>(%9); \
        let %12 = ~(%9 & 0x1b43b026dad416b0); \
        let %13 = %8 & #68386; \
        let %14 = %6 & 0xdad416b0; \
        let %15 = ~zext<64>(%14); \
        let %16 = ~(%8 & 0xe4bc4fd9252be94f) & %15; \
        let %17 = zext<64>(%4 >>u 16 & %11 & 0x252be94f) * 0x100000001b3 + ~(%12 & %8) * 0xfffffdfffffffc9a + ~(~(~%13 & 0xe4bc4fd9252be94f) & ~(%13 & 0x1b43b026dad416b0)) * 0xfffffdfffffffc9a + ~zext<64>(%6 & trunc<32>(%12)) * 0xfffffefffffffe4d + (~(%16 & #68386) & ~(~%16 & %9)) * 0x20000000366 + (~zext<64>(%14 & %11) & ~(%15 & #68386)) * 0x100000001b3 + zext<64>(~(%7 & 0xdad416b0) & (~(%11 & 0x252be94f) & %6)) * 0x100000001b3; \
        let %19 = ~%17; \
        let %20 = ~#68388:64; \
        let %22 = extract<8, 8>(%4); \
        let %23 = ~zext<64>(%22); \
        let %28 = %20 & %23; \
        let %29 = (~(%19 & %28) & ~(~%28 & %17)) * 0xfffffefffffffe4d; \
        let %32 = zext<64>(~%4) | -256; \
        let %36 = %29 & #11:64; \
        let %37 = ~%36; \
        let %39 = ~(~zext<64>(trunc<8>(%4 & trunc<32>(%37))) & ~(%36 & %32)) * 0xfffffefffffffe4d; \
        let %40 = trunc<32>(%39); \
        let %41 = extract<8, 8>(%39); \
        let %42 = extract<16, 8>(%39); \
        let %43 = %40 >>u 24; \
        let %44 = %39 >>u 56; \
        let %45 = (~(~%44 & 0x340d631b7bdddcda) & ~zext<64>(trunc<32>(%44) & 0x84222325)) * 0x100000001b3; \
        let %46 = trunc<32>(%39 >>u 48); \
        let %47 = (~(~%45 & (zext<64>(~%46) | -256)) & ~zext<64>(trunc<8>(trunc<32>(%45) & %46))) * 0x100000001b3; \
        let %48 = trunc<32>(%39 >>u 40); \
        let %49 = (~(~%47 & (zext<64>(~%48) | -256)) & ~zext<64>(trunc<8>(trunc<32>(%47) & %48))) * 0x100000001b3; \
        let %50 = extract<32, 32>(%39); \
        let %51 = (~zext<64>(trunc<8>(trunc<32>(%49) & %50)) & ~(~%49 & (zext<64>(~%50) | -256))) * 0x100000001b3; \
        let %52 = (~zext<64>(%43 & trunc<32>(%51)) & ~(~zext<64>(%43) & ~%51)) * 0x100000001b3; \
        let %53 = (~zext<64>(zext<32>(%42) & trunc<32>(%52)) & ~(~%52 & ~zext<64>(%42))) * 0x100000001b3; \
        let %54 = (~zext<64>(zext<32>(%41) & trunc<32>(%53)) & ~(~zext<64>(%41) & ~%53)) * 0x100000001b3; \
        let %56 = ~%54; \
        let %57 = (zext<64>(~%40) | -256) & #68592:64; \
        let %58 = ~zext<64>(trunc<8>(trunc<32>(~#68592) & %40)) & ~%57; \
        let %59 = ~(~(%56 & %58) & ~(~%58 & %54)) * 0xfffffefffffffe4d; \
        let %60 = extract<8, 8>(%59); \
        let %61 = %59 >>u 56; \
        let %62 = (~zext<64>(trunc<32>(%61) & 0x84222325) & ~(~%61 & 0x340d631b7bdddcda)) * 0x100000001b3; \
        let %63 = trunc<32>(%59 >>u 48); \
        let %64 = (~zext<64>(trunc<8>(trunc<32>(%62) & %63)) & ~(~%62 & (zext<64>(~%63) | -256))) * 0x100000001b3; \
        let %65 = trunc<32>(%59 >>u 40); \
        let %66 = (~(~%64 & (zext<64>(~%65) | -256)) & ~zext<64>(trunc<8>(%65 & trunc<32>(%64)))) * 0x100000001b3; \
        let %67 = extract<32, 32>(%59); \
        let %68 = (~(~%66 & (zext<64>(~%67) | -256)) & ~zext<64>(trunc<8>(%67 & trunc<32>(%66)))) * 0x100000001b3; \
        let %69 = trunc<32>(%59); \
        let %70 = %69 >>u 24; \
        let %71 = (~(~%68 & ~zext<64>(%70)) & ~zext<64>(%70 & trunc<32>(%68))) * 0x100000001b3; \
        let %72 = extract<16, 8>(%59); \
        let %73 = (~(~%71 & ~zext<64>(%72)) & ~zext<64>(zext<32>(%72) & trunc<32>(%71))) * 0x100000001b3; \
        let %74 = (~(~zext<64>(%60) & ~%73) & ~zext<64>(zext<32>(%60) & trunc<32>(%73))) * 0x100000001b3; \
        let %75 = ~%74; \
        let %76 = zext<64>(~%69) | -256; \
        let %77 = ~(~#68211:64 & ~(~(%75 & %76) & ~zext<64>(trunc<8>(%69 & trunc<32>(%74))))) * 0x100000001b3; \
        let %78 = trunc<32>(%77); \
        let %79 = zext<64>(~%78) | -256; \
        let %81 = extract<8, 8>(%77); \
        let %82 = %78 >>u 24; \
        let %83 = trunc<32>(%77 >>u 40); \
        let %84 = %77 >>u 56; \
        let %85 = (~(~%84 & 0x340d631b7bdddcda) & ~zext<64>(trunc<32>(%84) & 0x84222325)) * 0x100000001b3; \
        let %86 = trunc<32>(%77 >>u 48); \
        let %87 = (~zext<64>(trunc<8>(trunc<32>(%85) & %86)) & ~(~%85 & (zext<64>(~%86) | -256))) * 0x100000001b3; \
        let %88 = (~zext<64>(trunc<8>(%83 & trunc<32>(%87))) & ~(~%87 & (zext<64>(~%83) | -256))) * 0x100000001b3; \
        let %89 = extract<32, 32>(%77); \
        let %90 = (~zext<64>(trunc<8>(trunc<32>(%88) & %89)) & ~(~%88 & (zext<64>(~%89) | -256))) * 0x100000001b3; \
        let %91 = (~zext<64>(%82 & trunc<32>(%90)) & ~(~zext<64>(%82) & ~%90)) * 0x100000001b3; \
        let %92 = extract<16, 8>(%77); \
        let %93 = (~(~%91 & ~zext<64>(%92)) & ~zext<64>(zext<32>(%92) & trunc<32>(%91))) * 0x100000001b3; \
        let %94 = (~zext<64>(zext<32>(%81) & trunc<32>(%93)) & ~(~%93 & ~zext<64>(%81))) * 0x100000001b3; \
        let %95 = ~%94; \
        let %97 = ~(~(%95 & #65004) & (~(%1 & %94) & %79)) * 0x100000001b3; \
        let %98 = extract<8, 8>(%97); \
        let %99 = trunc<32>(%97); \
        let %100 = %99 >>u 24; \
        let %101 = %97 >>u 56; \
        let %102 = (~zext<64>(trunc<32>(%101) & 0x84222325) & ~(~%101 & 0x340d631b7bdddcda)) * 0x100000001b3; \
        let %103 = trunc<32>(%97 >>u 48); \
        let %104 = (~(~%102 & (zext<64>(~%103) | -256)) & ~zext<64>(trunc<8>(%103 & trunc<32>(%102)))) * 0x100000001b3; \
        let %105 = trunc<32>(%97 >>u 40); \
        let %106 = (~(~%104 & (zext<64>(~%105) | -256)) & ~zext<64>(trunc<8>(trunc<32>(%104) & %105))) * 0x100000001b3; \
        let %107 = extract<32, 32>(%97); \
        let %108 = (~(~%106 & (zext<64>(~%107) | -256)) & ~zext<64>(trunc<8>(%107 & trunc<32>(%106)))) * 0x100000001b3; \
        let %109 = (~(~zext<64>(%100) & ~%108) & ~zext<64>(%100 & trunc<32>(%108))) * 0x100000001b3; \
        let %110 = extract<16, 8>(%97); \
        let %111 = (~(~%109 & ~zext<64>(%110)) & ~zext<64>(zext<32>(%110) & trunc<32>(%109))) * 0x100000001b3; \
        let %112 = (~zext<64>(zext<32>(%98) & trunc<32>(%111)) & ~(~zext<64>(%98) & ~%111)) * 0x100000001b3; \
        let %113 = ~%112; \
        let %114 = zext<64>(~%99) | -256; \
        let %116 = zext<64>(#68636:8) << 8 | zext<64>(#68633:8) | zext<64>(#68639:8) << 16 | zext<64>(#68642:8) << 24 | zext<64>(#68645:8) << 32 | zext<64>(#68648:8) << 40 | zext<64>(#68651:8) << 48 | zext<64>(#68654:8) << 56; \
        let %118 = %116 & %114; \
        let %119 = ~(%113 & ~%118); \
        let %123 = (%119 & ~(%112 & %118)) * 0x100000001b3; \
        let %124 = ~%123; \
        let %125 = zext<64>(#68524:8) << 8 | zext<64>(#68521:8) | zext<64>(#68527:8) << 16 | zext<64>(#68530:8) << 24 | zext<64>(#68533:8) << 32 | zext<64>(#68536:8) << 40 | zext<64>(#68539:8) << 48 | zext<64>(#68542:8) << 56; \
        let %126 = ~%125; \
        let %127 = ~(%124 & %125) & ~(%126 & %123); \
        let %128 = %0 & %127; \
        let %129 = #73699 & 0x140000000; \
        let %130 = %123 & %129; \
        let %131 = zext<64>(extract<24, 16>(%125 & 0x140000000)) << 24; \
        let %132 = %0 & %131; \
        let %133 = ~%132; \
        let %134 = %0 & ~%127; \
        let %135 = %0 & %124; \
        let %136 = ~(%123 & #73699) & ~%135; \
        let %137 = ~(%136 & %125) & ~(~%136 & %126); \
        let %138 = %125 & #73699; \
        let %139 = ~%138; \
        let %140 = ~(%0 & %126) & %139; \
        let %141 = %124 & %131; \
        let %142 = %135 & %125; \
        let %143 = %123 & 0xfffffffebfffffff; \
        ~(~(%128 & 0x140000000) & ~(~%128 & 0xfffffffebfffffff)) + (~(~(~%129 & %124) & (%126 & ~%130)) + (%123 & (%133 & ~((zext<64>(extract<24, 16>(~%131)) << 24 | 0xffffff | 0xffffff0000000000) & #73699)))) + ~(%124 & (~(%125 & 0xfffffffebfffffff) & ~(zext<64>(extract<24, 16>(%126 & 0x140000000)) << 24) & #73699)) * 0xaaaaaaaaaaaaaaa7 + ~(~(%134 & 0xfffffffebfffffff) & ~(~%134 & 0x140000000)) * 0x5555555555555556 + (~(~%137 & 0x140000000) & ~(%137 & 0xfffffffebfffffff)) * 0xaaaaaaaaaaaaaaac + (~(%124 & ~(~(~%140 & 0x140000000) & ~(%140 & 0xfffffffebfffffff))) << 1) + (%124 & (~(%138 & 0x140000000) & ~(%139 & 0xfffffffebfffffff))) + (~(%133 & %123) & ~(%124 & zext<64>(extract<24, 16>(%132)) << 24)) * 0x5555555555555555 + ~(~(~%141 & %0) & ~(%141 & #73699)) * 0xaaaaaaaaaaaaaaab + ~(~(%142 & 0xfffffffebfffffff) & ~(~%142 & 0x140000000)) * 0x5555555555555557 + ~(~(~%143 & %0) & (~(%143 & #73699) & %125)) * 0x5555555555555556 + (%125 & zext<64>(extract<24, 16>(%130)) << 24) * 0xaaaaaaaaaaaaaaa9 + ~(~(%126 & #73699) & %143) * 0x5555555555555555 + 1";
    let mut cx = Context::new();
    let e = cx.parse(src, &ParseOptions::width(Width::W64)).unwrap();
    let sz_before = match cx.dag_size(&[e], 1 << 20).unwrap() {
        Bounded::Exact(n) | Bounded::AtLeast(n) => n,
        _ => panic!("unexpected Bounded"),
    };
    let engine = build_engine(true, false);
    let out = simplify_fuel(&engine, &mut cx, e, 1 << 21);
    let sz_after = match cx.dag_size(&[out], 1 << 20).unwrap() {
        Bounded::Exact(n) | Bounded::AtLeast(n) => n,
        _ => panic!("unexpected Bounded"),
    };
    assert!(
        sz_after < sz_before,
        "expected shared byte-chain expression to shrink cleanly ({sz_before} -> {sz_after})"
    );
}

#[test]
fn popcnt_boundary_comparisons_and_carry_out_canonicalization() {
    let engine = build_engine(true, false);

    // 1) Width-polymorphic popcnt(x) zero / all-ones boundary canonicalization.
    for bits in [8u16, 16, 32, 64, 128] {
        let mut cx = Context::new();
        let w = Width::new(bits).unwrap();
        let opt = ParseOptions::width(w);
        let cases = [
            (format!("popcnt(x) == 0"), "x == 0"),
            (format!("popcnt(x) != 0"), "x != 0"),
            (format!("popcnt(x) <=u 0"), "x == 0"),
            (format!("0 <u popcnt(x)"), "x != 0"),
            (format!("popcnt(x) == {bits}"), "x == -1"),
            (format!("popcnt(x) != {bits}"), "x != -1"),
            (format!("{bits} <=u popcnt(x)"), "x == -1"),
            (format!("popcnt(x) <u {bits}"), "x != -1"),
            (format!("zext<256>(popcnt(x)) == 0"), "x == 0"),
            (format!("zext<256>(popcnt(x)) == {bits}"), "x == -1"),
        ];
        for (lhs_s, rhs_s) in &cases {
            let lhs = cx.parse(lhs_s, &opt).unwrap();
            let rhs = cx.parse(rhs_s, &opt).unwrap();
            let lhs_out = simplify_fuel(&engine, &mut cx, lhs, 1 << 14);
            let rhs_out = simplify_fuel(&engine, &mut cx, rhs, 1 << 14);
            assert_eq!(
                lhs_out,
                rhs_out,
                "width {bits}: expected `{lhs_s}` and `{rhs_s}` to canonicalize identically (`{}` vs `{}`)",
                cx.display(lhs_out),
                cx.display(rhs_out)
            );
            if bits <= 32 {
                assert_bitblasted_equal(&mut cx, lhs, lhs_out);
            }
        }
    }

    // 2) `extract<W, 1>(zext<W2>(x:W) + K)` carry-out comparison canonicalization & shifted-atom
    //    multiply high-bit noise reduction modulo `2^(W - ctz(a))`.
    for bits in [8u16, 16, 32, 64] {
        let mut cx = Context::new();
        let w = Width::new(bits).unwrap();
        let opt = ParseOptions::width(w);
        let w1 = bits + 1;
        let ones = (1u128 << bits) - 1;
        let carry_nz = cx
            .parse(
                &format!("extract<{bits}, 1>(zext<{w1}>(x) + 0x{ones:x})"),
                &opt,
            )
            .unwrap();
        let expect_nz = cx.parse("x != 0", &opt).unwrap();
        let out_nz = simplify_fuel(&engine, &mut cx, carry_nz, 1 << 14);
        assert_eq!(out_nz, simplify_fuel(&engine, &mut cx, expect_nz, 1 << 14));
        if bits <= 32 {
            assert_bitblasted_equal(&mut cx, carry_nz, out_nz);
        }

        // Annihilated 2-adic scaled term stripping (`(x & 48) * (1 << (bits - 4)) == 0`).
        let shift_annih = 1u128 << (bits - 4);
        let mul_zero = cx
            .parse(&format!("(x & 48) * 0x{shift_annih:x}"), &opt)
            .unwrap();
        let out_zero = simplify_fuel(&engine, &mut cx, mul_zero, 1 << 14);
        assert_eq!(cx.as_const(out_zero).unwrap(), Some(BitVec::zero(w)));
        if bits <= 32 {
            assert_bitblasted_equal(&mut cx, mul_zero, out_zero);
        }

        // Diamond nested `select` collapse across all 4 symmetric arm shapes.
        for s in [
            "select(a:1, select(b:1, x, y), x)",
            "select(a:1, select(b:1, y, x), x)",
            "select(a:1, x, select(b:1, y, x))",
            "select(a:1, x, select(b:1, x, y))",
        ] {
            let e = cx.parse(s, &opt).unwrap();
            let out = simplify_fuel(&engine, &mut cx, e, 1 << 14);
            if bits <= 32 {
                assert_bitblasted_equal(&mut cx, e, out);
            }
        }
    }

    // 3) Flags-driven `popcnt` + carry-out constant-folding regression (`0x70:32`).
    let src_const = "\
        let %0 = extract<64, 1>(zext<65>(#28126:64) + 0xffffffffffffffff); \
        let %1 = #35753:64 * -1 + #28126 == -16; \
        let %2 = trunc<8>(#9994:32) & 8; \
        let %3 = trunc<8>(#16640:64 & 0x3c7300 | (zext<64>(popcnt(%2) == 0) << 2 | 2 | zext<64>(%2 == 0) << 6)); \
        let %4 = %3 == 70; \
        let %5 = zext<64>(#9994); \
        let %6 = %5 ^ 4384; \
        let %7 = %3 >>u 6; \
        let %8 = %3 == 2; \
        let %9 = (~select(%7 == 0, 272:64, 192) & 0xffffcffe00000d18 == 0xffffcffe00000c08) & %8; \
        let %10 = %7 != 0; \
        let %11 = select(%4, %6, select(%9, select(%10, 0x5db2585140c78218:64, 0xb64318a03ca5b395), #2:64 ^ 4384)); \
        let %12 = %5 & 0x3001fffff127; \
        let %13 = select(%4, %12, select(%9, select(%10, 0x100140c79120:64, 0x10003ca5a025), #2 & 0x3001fffff127)); \
        let %14 = ~select(%0, select(%1, select(%0, %13, select(%8, %12, #13:64 & 0x3001fffff127)), 0x2001bd891001), select(%0, 0x300016c69120, %13)); \
        let %15 = select(%4, %5, select(%9, select(%10, 0x5db2585140c79338:64, 0xb64318a03ca5a2b5), #2)); \
        let %16 = ~select(%0, select(%1, select(%0, %15, select(%8, %5, #13)), 0xbe72ae97bd891211), select(%0, 0xff87711c16c697b0, %15)); \
        let %17 = ~(%16 & 0xffffcffe00000ed8) & %14; \
        let %18 = %5 & 0x3001ffffecdf; \
        let %19 = select(%4, %18, select(%9, select(%10, 0x100140c78018:64, 0x10003ca5a095), #2 & 0x3001ffffecdf)); \
        let %20 = (%5 ^ 0xffffcffe00001320) & 0x3001fffff127; \
        let %21 = select(%4, %20, select(%9, select(%10, 0x100140c78000:64, 0x10003ca5b105), (#2 ^ 0xffffcffe00001320) & 0x3001fffff127)); \
        trunc<32>(select(%0, select(%1, select(%0, %11, select(%8, %6, #13 ^ 4384)), 0xbe72ae97bd890331), select(%0, 0xff87711c16c68690, %11)) * 0x891d0a3f15ef3bdb + (%14 & 0xffffcffe00001320) * 0x76e2f5c0ea10c425 + (%17 & 0xffffcffe00001320) * 0x891d0a3f15ef3bdb + ~(%17 & 0x3001ffffecdf) * 0x891d0a3f15ef3bdb + (~(%16 & 0xffffcffe00001320) & (~select(%0, select(%1, select(%0, %19, select(%8, %18, #13 & 0x3001ffffecdf)), 0x2001bd890011), select(%0, 0x300016c68490, %19)) & 0xffffcffe00000ed8) | select(%0, select(%1, select(%0, %21, select(%8, %20, (#13 ^ 0xffffcffe00001320) & 0x3001fffff127)), 0x2001bd890121), select(%0, 0x300016c68000, %21))) * 0x76e2f5c0ea10c425 + (%16 & -4385) * 0x891d0a3f15ef3bdb) * 0x7c05bb0";
    let mut cx = Context::new();
    let e_const = cx.parse(src_const, &ParseOptions::width(Width::W64)).unwrap();
    let out_const = simplify_fuel(&engine, &mut cx, e_const, 524_288);
    assert_eq!(
        cx.as_const(out_const).unwrap(),
        Some(BitVec::from_u64(Width::W32, 0x70).unwrap())
    );
}

#[test]
fn prove_too_large_compact_retry_shares_sums() {
    // Build a predicate with two differently associated 16-term 64-bit sums that exceeds a tight
    // `max_nodes` cap when blasted naively (`shared_sums = false`), and verify the compact-circuit
    // retry (`sums::shared` + `carry_save_multiplication` + `join_factoring`) fits the cap and
    // proves equivalence.
    let mut cx = Context::new();
    let opt = ParseOptions::width(Width::W64);
    let lhs = cx
        .parse(
            "(((((((((((((((x0 + x1) + x2) + x3) + x4) + x5) + x6) + x7) + x8) + x9) + x10) + x11) + x12) + x13) + x14) + x15)",
            &opt,
        )
        .unwrap();
    let rhs = cx
        .parse(
            "(x15 + (x14 + (x13 + (x12 + (x11 + (x10 + (x9 + (x8 + (x7 + (x6 + (x5 + (x4 + (x3 + (x2 + (x1 + x0)))))))))))))))",
            &opt,
        )
        .unwrap();
    let eq = cx.cmp(bitwright::CmpOp::Eq, lhs, rhs).unwrap();
    let cfg = ProveConfig::default()
        .with_simplify(false)
        .with_certificate(false)
        .with_shared_sums(false)
        .with_max_nodes(6_000);
    let out = prove::valid(&mut cx, eq, &cfg).unwrap();
    assert!(
        matches!(out, Outcome::Proved(_)),
        "expected compact retry to share sum prefixes under tight max_nodes and prove equality, got {out:?}"
    );
}
