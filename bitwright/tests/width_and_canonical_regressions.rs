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
