//! A small demanded support can hide a shifted field in a mixed arithmetic expression.
#![cfg(feature = "mba")]

use bitwright::engine::{Engine, Sharing, Strategy};
use bitwright::mba::MbaConfig;
use bitwright::{BitVec, Bounded, Context, FnEnv, ParseOptions, SymbolKey, Width};

const MASKED: &str = "\
let %0 = trunc<32>($625:64);
let %1 = %0 + 0xb1a05b8b;
let %2 = -12 - %0 & 0x1d494bfa;
let %3 = (%1 | 0xe2b6b405) * -15 + %0 + %2 * 6 + (%1 & 0x1d494bfa) * -13 + 0xb119e974;
zext<64>(((%1 ^ 0x1d494bfa) * 3 + %0 * 10 + (%1 ^ 0xe2b6b405) * 15 + (%3 & 0x1d494bfa) * -15 + %2 * -12 + (%3 & 0xe2b6b405) * 3 - 16 ^ %0) & 16)";

const BIT: &str = "\
let %0 = trunc<5>($625:64);
let %1 = %0 + 11;
let %2 = %1 ^ -6;
let %3 = (%1 | -6) * 13 + %2 * 3 - (%1 | 5) * 15 - %0 * 15;
zext<32>(extract<4, 1>($625) + extract<4, 1>((%3 & -6) * 15 - %2 * 13 - (%1 ^ 5) * 15 - (%3 & 5) * 3 + 9))";

const BYTE: &str = "\
let %0 = zext<64>($1311:8);
(%0 ^ 48) * 26 + (%0 ^ -49) * -34 + zext<64>(zext<32>($1311) ^ 48) * -52 - 34";

fn check(src: &str, support: u32, size: Option<u32>, expected: impl Fn(u64) -> u64) {
    let engine = Engine::builder()
        .builtin()
        .strategy(
            Strategy::deobfuscate()
                .with_mba(MbaConfig::default().with_opaque_sweep(true))
                .with_sharing(Sharing::Ignored)
                .with_max_region(1024),
        )
        .build()
        .unwrap();
    let mut cx = Context::new();
    let input = cx.parse(src, &ParseOptions::default()).unwrap();
    let out = engine.simplify(&mut cx, input).unwrap().expr;
    if let Some(limit) = size {
        assert!(
            matches!(cx.dag_size(&[out], limit).unwrap(), Bounded::Exact(_)),
            "{} exceeds {limit} nodes",
            cx.display(out)
        );
    }
    let count = 1 << support;
    for low in 0..count {
        for x in [low, low | !(count - 1)] {
            let env = FnEnv(|_: &SymbolKey, w: Width| Some(BitVec::wrapping_from_u64(w, x)));
            for v in cx.eval(&[input, out], &env).unwrap() {
                assert_eq!(v.to_u64(), Some(expected(low)), "x={x:#x}, {src}");
            }
        }
    }
}

#[test]
fn extract_a_field_hidden_by_arithmetic() {
    // r0680 and r0696 only read the low five bits. Their truth tables are bit 3,
    // at two different destination positions.
    check(MASKED, 5, Some(5), |x| (x & 8) << 1);
    check(BIT, 5, Some(3), |x| (x >> 3) & 1);
    // r0764: put t = zext(x) ^ 48. The sum is 26*t - 34*(~t) - 52*t - 34 = 8*t.
    check(BYTE, 8, Some(6), |x| (x ^ 48) << 3);
}

#[test]
fn singleton_columns_do_not_prove_a_field() {
    // Zero and every basis input still suggest the same shifted byte. Exactly one
    // mixed input breaks the affine identity and must survive simplification.
    let src = format!("{BYTE} ^ zext<64>($1311 == 253)");
    check(&src, 8, None, |x| ((x ^ 48) << 3) ^ u64::from(x == 253));
}

#[test]
fn weighted_truncations_cancel_only_at_the_observed_width() {
    let src = "\
let %0 = x:64 >>u 3;
let %1 = %0 * -8;
let %2 = %1 | %0;
let %3 = trunc<32>((%1 | %0 ^ 0x3001ffe53ab1) * 0xafe94f8e811fb0f5);
let %4 = trunc<32>(-(%2 & 0xffffcffe001ac54e) + (~(%0 * 8 - 1 ^ %0) & 0x3001ffe53ab1) + 0xffffcffe001ac54d);
let %5 = trunc<32>((%1 & 0x3001ffe53ab1 ^ %0) + (~%0 & %1 ^ 0xffffcffe001ac54e));
let %6 = trunc<32>(~(%0 - (%2 & 0x3001ffe53ab1)));
%3 * 0x156d1858 + %4 * 0x666665a0 + %5 * 0x66666698 + %6 * 0xcccccd30";
    let eng = Engine::standard();
    let mut cx = Context::new();
    let input = cx.parse(src, &ParseOptions::default()).unwrap();
    let out = eng.simplify(&mut cx, input).unwrap().expr;
    assert_eq!(
        cx.as_const(out).unwrap().and_then(|k| k.to_u64()),
        Some(248)
    );

    // Raising just the last slice by one bit invalidates the low-word identity.
    let shifted = src.replace("%6 = trunc<32>", "%6 = extract<1, 32>");
    let input = cx.parse(&shifted, &ParseOptions::default()).unwrap();
    let out = eng.simplify(&mut cx, input).unwrap().expr;
    let env = FnEnv(|_: &SymbolKey, w: Width| Some(BitVec::wrapping_from_u64(w, 16)));
    assert_eq!(
        cx.eval(&[out], &env).unwrap()[0].to_u64(),
        Some(0x052f_d5a8)
    );
}

#[test]
fn truncated_constant_handles_mixed_narrow_terms_and_cancelling_atoms() {
    let eng = Engine::standard();
    let mut cx = Context::new();
    // Mixes a wide truncated sum with a plain narrow term and a shared unrestricted word
    // `w = a*a + b` that cancels algebraically before column evaluation.
    let src = "let w = a:64 * a + b:64; \
               let s = (x:64 & y:64)*3 + (x & ~y)*3 + w; \
               trunc<32>(s) - trunc<32>(w) - trunc<32>(x)*3 + z:32 - z";
    let input = cx.parse(src, &ParseOptions::default()).unwrap();
    let out = eng.simplify(&mut cx, input).unwrap().expr;
    assert_eq!(cx.as_const(out).unwrap().and_then(|k| k.to_u64()), Some(0));
}
