//! Regression cases for exact predicate proofs in the MBA sweep.
#![cfg(feature = "mba")]

use bitwright::engine::{Budget, Engine, Run, Sharing, Strategy};
use bitwright::mba::MbaConfig;
#[cfg(feature = "prove")]
use bitwright::{BitVec, FnEnv, SymbolKey, Width};
use bitwright::{Context, ParseOptions, View};

fn engine() -> Engine {
    Engine::builder()
        .builtin()
        .strategy(
            Strategy::deobfuscate()
                .with_mba(MbaConfig::default().with_opaque_sweep(true))
                .with_sharing(Sharing::Ignored)
                .with_max_region(1024),
        )
        .build()
        .unwrap()
}

#[test]
fn constant_bits_of_a_product_with_a_masked_mba_factor() {
    // Same word read at six bit offsets. At bit 27 the demanded form also spells
    // a field arithmetically, as a sum of shifted, masked copies of one input.
    const PRODUCT: &str = include_str!("questions/projected_product_bits.bw");
    let engine = engine();
    let (definitions, operand) = PRODUCT.rsplit_once("extract<12, 1>(").unwrap();
    for bit in [12, 17, 27, 35, 49, 59] {
        let text = format!("{definitions}extract<{bit}, 1>({operand}");
        let mut cx = Context::new();
        let root = cx.parse(&text, &ParseOptions::default()).unwrap();
        let run = Run::default().with_per_call(Budget::fuel(50_000_000));
        let result = engine.run(&mut cx, &[root], run).unwrap().roots[0].expr;
        assert!(
            matches!(cx.view(result).unwrap(), View::Const(v) if v.to_u64() == Some(1)),
            "bit {bit}: {}",
            cx.display(result)
        );
    }
}

#[test]
fn masked_product_sees_through_nested_unary_sums() {
    // Each sum spells a different XOR on the biased word. After their flips
    // cancel, rotating back exposes the two bits cleared by the input mask.
    let mut cx = Context::new();
    let root = cx
        .parse(
            "let %0 = rotl(x:8 & 243, 3) + 17;
             let %1 = (%0 & 15)*3 - (%0 & 15)*2 + (~%0 & 240);
             let %2 = (%1 & 85)*3 - (%1 & 85)*2 + (~%1 & 170);
             let %3 = rotr((%2 ^ 90) - 17, 3);
             zext<8>(extract<2, 2>(%3)) * (x:8 & 3) == 0",
            &ParseOptions::default(),
        )
        .unwrap();
    let run = Run::default().with_per_call(Budget::fuel(16_384));
    let result = engine().run(&mut cx, &[root], run).unwrap().roots[0].expr;
    assert!(matches!(cx.view(result).unwrap(), View::Const(v) if v.to_u64() == Some(1)));
}

#[test]
fn projected_input_can_exclude_a_word_without_excluding_its_neighbor() {
    use bitwright::{BitVec, FnEnv, SymbolKey, Width};
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let mask = cx.constant_u64(Width::W8, 0x55).unwrap();
    let mut mixed = cx.and(x, mask).unwrap();
    // A bijection of the masked inputs. One label below is reachable, one is not.
    let encode = |mut v: u8| {
        for i in 1..=55u8 {
            v = v.wrapping_add(i) ^ i.wrapping_mul(13);
        }
        v
    };
    for i in 1..=55u8 {
        let a = cx.constant_u64(Width::W8, i.into()).unwrap();
        let b = cx
            .constant_u64(Width::W8, i.wrapping_mul(13).into())
            .unwrap();
        mixed = cx.add(mixed, a).unwrap();
        mixed = cx.xor(mixed, b).unwrap();
    }
    let eng = engine();
    for seed in [0x54, 0x56] {
        let label = cx.constant_u64(Width::W8, encode(seed).into()).unwrap();
        let cmp = cx.ne(mixed, label).unwrap();
        let out = eng
            .run(
                &mut cx,
                &[cmp],
                Run::default().with_per_call(Budget::fuel(4096)),
            )
            .unwrap()
            .roots[0]
            .expr;
        if seed == 0x56 {
            assert!(matches!(cx.view(out).unwrap(), View::Const(v) if !v.is_zero()));
        }
        for v in 0..=255 {
            let env = FnEnv(|_: &SymbolKey, w| Some(BitVec::wrapping_from_u64(w, v)));
            assert_eq!(
                cx.eval(&[out], &env).unwrap()[0].is_zero(),
                v as u8 & 0x55 == seed
            );
        }
    }
}

#[test]
fn projected_select_tags_do_not_escape_their_guard() {
    use bitwright::{BitVec, Width};
    let mut cx = Context::new();
    let p = ParseOptions::default();
    let x = cx.symbol("x", Width::W8).unwrap();
    let tag = cx.parse("(extract<2,4>(x:8 + 23) | 5) == 7", &p).unwrap();
    let a = cx.parse("((trunc<6>(x:8) + 23) & 40) == 8", &p).unwrap();
    let b = cx.parse("((trunc<6>(x:8) + 23) & 32) == 0", &p).unwrap();
    let mut noise = x;
    for i in 1..80 {
        let k = cx.constant_u64(Width::W8, i).unwrap();
        noise = cx.xor(noise, k).unwrap();
        noise = cx.add(noise, x).unwrap();
    }
    let payload = cx.bit(x, 0).unwrap();
    let noise = cx.bit(noise, 3).unwrap();
    let arm = cx.select(a, payload, noise).unwrap();
    let choice = cx.select(b, arm, noise).unwrap();
    let body = cx.and(tag, choice).unwrap();
    let root = cx.not(body).unwrap();
    let out = engine()
        .run(
            &mut cx,
            &[root],
            Run::default().with_per_call(Budget::fuel(4096)),
        )
        .unwrap()
        .roots[0]
        .expr;
    for x in 0u64..256 {
        let got = cx
            .eval(
                &[out],
                &[("x".into(), BitVec::from_u64(Width::W8, x).unwrap())][..],
            )
            .unwrap();
        assert_eq!(!got[0].is_zero(), (x + 23) & 40 != 8 || x & 1 == 0);
    }
}

#[cfg(feature = "prove")]
#[test]
fn prove_the_impossible_conjunction_but_keep_a_rare_equality() {
    let mut cx = Context::new();
    let root = cx.parse("let %0 = x:64 + 32768; let %1 = %0 & 0xe81e29f90359fa11 - x; (%1 & 0x7f9fffff1c7 == 0) & (~%1 & 0x7f9fffff1c7 == 0x7f9fffff1c7) & (~(x + 0x17e1d606fca605ee & 0x7f9fffff1c7) & %0 == x)", &ParseOptions::default()).unwrap();
    let e = engine();
    let out = e.simplify(&mut cx, root).unwrap().expr;
    assert!(matches!(cx.view(out).unwrap(), View::Const(v) if v.is_zero()));

    let rare = cx
        .parse(
            "(rotl(x:64, 50) & 124 ^ 28) + 0x180680398 == 0x1806803a4",
            &ParseOptions::default(),
        )
        .unwrap();
    let out = e.simplify(&mut cx, rare).unwrap().expr;
    for (input, want) in [(0, 0), (0x40000, 1)] {
        let env = FnEnv(|_: &SymbolKey, w: Width| Some(BitVec::wrapping_from_u64(w, input)));
        assert_eq!(cx.eval(&[out], &env).unwrap()[0].to_u64(), Some(want));
    }
}

#[cfg(feature = "prove")]
#[test]
fn specializing_a_guard_does_not_drop_unlisted_labels() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let mut mixed = x;
    for i in 1..81 {
        let k = cx.constant_u64(Width::W8, i).unwrap();
        mixed = cx.add(mixed, k).unwrap();
        mixed = cx.xor(mixed, k).unwrap();
    }
    let mut guards = Vec::new();
    let mut excludes = Vec::new();
    for label in [3, 17, 5] {
        let word = cx.constant_u64(Width::W8, label).unwrap();
        guards.push(cx.eq(x, word).unwrap());
        let value = cx
            .eval(
                &[mixed],
                &FnEnv(|_: &SymbolKey, w| Some(BitVec::wrapping_from_u64(w, label))),
            )
            .unwrap()[0];
        let value = cx.constant_u64(Width::W8, value.to_u64().unwrap()).unwrap();
        excludes.push(cx.ne(mixed, value).unwrap());
    }
    let two = cx.or(guards[0], guards[1]).unwrap();
    let three = cx.or(two, guards[2]).unwrap();
    let excluded = cx.and(excludes[0], excludes[1]).unwrap();
    let eng = engine();
    for (allowed, has_third) in [(two, false), (three, true)] {
        let body = cx.and(allowed, excluded).unwrap();
        let root = cx.not(body).unwrap();
        let run = Run::default().with_per_call(Budget::fuel(16_384));
        let out = eng.run(&mut cx, &[root], run).unwrap().roots[0].expr;
        if !has_third {
            assert!(matches!(cx.view(out).unwrap(), View::Const(v) if !v.is_zero()));
        }
        for i in 0..=255 {
            let env = FnEnv(|_: &SymbolKey, w| Some(BitVec::wrapping_from_u64(w, i)));
            assert_eq!(
                cx.eval(&[out], &env).unwrap()[0].is_zero(),
                has_third && i == 5
            );
        }
    }
}

#[cfg(feature = "prove")]
#[test]
fn guarded_pairs_need_a_contradiction_in_every_case() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let y = cx.symbol("y", Width::W8).unwrap();
    let mut value = cx.xor(x, y).unwrap();
    let mut outputs = [3u8 ^ 5, 3 ^ 29, 17 ^ 5, 17 ^ 29];
    // A permutation: each pair needs a different exclusion. Neither label
    // alone determines the word, so splitting one input need not shrink it.
    for k in 1..=80u8 {
        let c = cx.constant_u64(Width::W8, u64::from(k)).unwrap();
        value = cx.add(value, c).unwrap();
        value = cx.xor(value, c).unwrap();
        for v in &mut outputs {
            *v = v.wrapping_add(k) ^ k;
        }
    }
    let po = ParseOptions::default();
    let guards = cx
        .parse("((x:8 == 3) | (x == 17)) & ((y:8 == 5) | (y == 29))", &po)
        .unwrap();
    let exception = cx.parse("z:8 == 223", &po).unwrap();
    let eng = engine();
    for open in [false, true] {
        let mut body = guards;
        for (j, &v) in outputs.iter().enumerate() {
            let c = cx.constant_u64(Width::W8, u64::from(v)).unwrap();
            let mut clause = cx.ne(value, c).unwrap();
            if open && j == 3 {
                clause = cx.or(clause, exception).unwrap();
            }
            body = cx.and(body, clause).unwrap();
        }
        let root = cx.not(body).unwrap();
        let run = Run::default().with_per_call(Budget::fuel(16_384));
        let out = eng.run(&mut cx, &[root], run).unwrap().roots[0].expr;
        if !open {
            assert!(matches!(cx.view(out).unwrap(), View::Const(v) if !v.is_zero()));
        }
        for (x, y, z) in [
            (3, 5, 223),
            (3, 29, 223),
            (17, 5, 223),
            (17, 29, 223),
            (17, 29, 224),
            (0, 29, 223),
        ] {
            let env = FnEnv(|s: &SymbolKey, w| match s {
                SymbolKey::Str(s) => Some(BitVec::wrapping_from_u64(
                    w,
                    match s.as_ref() {
                        "x" => x,
                        "y" => y,
                        "z" => z,
                        _ => unreachable!(),
                    },
                )),
                _ => None,
            });
            assert_eq!(
                cx.eval(&[out], &env).unwrap()[0].is_zero(),
                open && (x, y, z) == (17, 29, 223)
            );
        }
    }
}
