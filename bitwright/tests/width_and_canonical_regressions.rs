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
