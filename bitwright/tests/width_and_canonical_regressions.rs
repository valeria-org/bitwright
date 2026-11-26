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
