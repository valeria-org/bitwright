use super::*;
use crate::prove::{Config, Limits, Outcome, Question};
use crate::{BinOp, KnownBits, SymbolKey};

const KEYS: [u64; 2] = [0x9e37_79b9_7f4a_7c15, 0xc26a_114a_f502_712b];

fn k(cx: &mut Context, value: u64) -> Expr {
    cx.constant_u64(Width::W64, value).unwrap()
}

fn expression(cx: &mut Context, x: Expr, key: u64, compact: bool, bad_shift: bool) -> Expr {
    let key = k(cx, key);
    let masked = cx.xor(x, key).unwrap();
    let h = cx.mul(masked, key).unwrap();
    let sixty = k(cx, 60);
    let top = cx.bin(BinOp::LShr, h, sixty).unwrap();
    let thirty_two = k(cx, 32);
    let shifted = if compact {
        let count = cx.add(thirty_two, top).unwrap();
        cx.bin(BinOp::LShr, h, count).unwrap()
    } else {
        let hi = cx
            .bin(
                if bad_shift { BinOp::AShr } else { BinOp::LShr },
                h,
                thirty_two,
            )
            .unwrap();
        let mask = k(cx, 63);
        let count = cx.and(top, mask).unwrap();
        cx.bin(BinOp::LShr, hi, count).unwrap()
    };
    let s = cx.xor(h, shifted).unwrap();
    cx.mul(key, s).unwrap()
}

fn pair(cx: &mut Context, a: Expr, b: Expr, compact: bool, bad_shift: bool) -> Expr {
    let first = expression(cx, a, KEYS[0], compact, bad_shift);
    let second = expression(cx, b, KEYS[1], compact, false);
    cx.xor(first, second).unwrap()
}

fn fact() -> CheckedPair {
    let salt = mixer(KEYS[0], 7) ^ mixer(KEYS[1], 7);
    let fact = CheckedPair::verify(KEYS, salt, u64::MAX, 8, VerifyLimits::default()).unwrap();
    assert_eq!(fact.candidates(), &[7]);
    fact
}

#[test]
fn verification_requires_full_coverage_and_discards_overfull_candidate_sets() {
    assert!(matches!(
        CheckedPair::verify(KEYS, 0, 0, 33, VerifyLimits::default()),
        Err(VerifyError::DomainTooWide(33))
    ));
    assert_eq!(
        CheckedPair::verify(
            KEYS,
            0,
            0,
            8,
            VerifyLimits {
                inputs: 255,
                candidates: 256
            }
        )
        .unwrap_err(),
        VerifyError::Budget {
            required: 256,
            allowed: 255
        }
    );
    assert_eq!(
        CheckedPair::verify(
            KEYS,
            0,
            0,
            8,
            VerifyLimits {
                inputs: 256,
                candidates: 255
            }
        )
        .unwrap_err(),
        VerifyError::TooManyCandidates(255)
    );
    let all = CheckedPair::verify(
        KEYS,
        0,
        0,
        8,
        VerifyLimits {
            inputs: 256,
            candidates: 256,
        },
    )
    .unwrap();
    assert_eq!(all.candidates(), &(0..256).collect::<Vec<_>>());
    let zero = CheckedPair::verify(
        [0, 0],
        0,
        u64::MAX,
        0,
        VerifyLimits {
            inputs: 1,
            candidates: 1,
        },
    )
    .unwrap();
    assert_eq!(zero.candidates(), &[0]);
}

#[test]
fn enumeration_agrees_with_the_generic_evaluator_including_even_keys() {
    for keys in [KEYS, [2, 4], [0, u64::MAX]] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let a = expression(&mut cx, x, keys[0], false, false);
        let b = expression(&mut cx, x, keys[1], true, false);
        let p = cx.xor(a, b).unwrap();
        let salt = mixer(keys[0], 7) ^ mixer(keys[1], 7);
        let checked = CheckedPair::verify(keys, salt, 0xffff, 8, VerifyLimits::default()).unwrap();
        let mut expected = Vec::new();
        for value in 0..256 {
            let model = [(
                SymbolKey::from("x"),
                BitVec::from_u64(Width::W64, value).unwrap(),
            )];
            if (cx.eval(&[p], &model[..]).unwrap()[0].to_u64().unwrap() ^ salt) & 0xffff == 0 {
                expected.push(value);
            }
        }
        assert_eq!(checked.candidates(), expected);
    }
}

#[test]
fn both_shift_spellings_reduce_exact_pair_comparisons_without_changing_models() {
    let checked = fact();
    for compact in [false, true] {
        for unequal in [false, true] {
            let mut cx = Context::new();
            let x = cx.symbol("x", Width::W8).unwrap();
            let wide = cx.zext(x, Width::W64).unwrap();
            let subject = pair(&mut cx, wide, wide, compact, false);
            let target = k(&mut cx, checked.salt);
            let original = if unequal {
                cx.ne(subject, target).unwrap()
            } else {
                cx.eq(subject, target).unwrap()
            };
            let reduced = checked.simplify(&mut cx, original).unwrap();
            assert_ne!(reduced, original);
            for value in 0..256 {
                let model = [(
                    SymbolKey::from("x"),
                    BitVec::from_u64(Width::W8, value).unwrap(),
                )];
                let values = cx.eval(&[original, reduced], &model[..]).unwrap();
                assert_eq!(values[0], values[1]);
            }
        }
    }
}

#[test]
fn unrestricted_sources_separate_inputs_and_arithmetic_shifts_are_rejected() {
    let checked = fact();
    for mode in 0..4 {
        let mut cx = Context::new();
        let x = cx
            .symbol("x", if mode == 0 { Width::W64 } else { Width::W8 })
            .unwrap();
        let wide = if mode == 0 {
            x
        } else {
            cx.zext(x, Width::W64).unwrap()
        };
        let other = if mode == 1 {
            let y = cx.symbol("y", Width::W8).unwrap();
            cx.zext(y, Width::W64).unwrap()
        } else {
            wide
        };
        let subject = pair(&mut cx, wide, other, false, mode == 2);
        let target = k(&mut cx, checked.salt ^ u64::from(mode == 3));
        let p = cx.eq(subject, target).unwrap();
        assert_eq!(checked.simplify(&mut cx, p).unwrap(), p);
    }
}

#[test]
fn original_residual_symbols_remain_guarded_by_the_checked_candidate() {
    let checked = fact();
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let wide = cx.zext(x, Width::W64).unwrap();
    let extra = cx.symbol("extra", Width::W64).unwrap();
    let p = pair(&mut cx, wide, wide, false, false);
    let salt = k(&mut cx, checked.salt);
    let term = cx.xor(p, salt).unwrap();
    let joined = cx.or(term, extra).unwrap();
    let zero = k(&mut cx, 0);
    let original = cx.ne(joined, zero).unwrap();
    let rewritten = checked.simplify(&mut cx, original).unwrap();
    assert_ne!(original, rewritten);
    for value in 0..256 {
        for other in [0, 1, u64::MAX] {
            let model = [
                (
                    SymbolKey::from("x"),
                    BitVec::from_u64(Width::W8, value).unwrap(),
                ),
                (
                    SymbolKey::from("extra"),
                    BitVec::from_u64(Width::W64, other).unwrap(),
                ),
            ];
            let results = cx.eval(&[original, rewritten], &model[..]).unwrap();
            assert_eq!(results[0], results[1]);
        }
    }
    let cfg = Config::default().with_samples(0).with_simplify(false);
    let mut q = Question::valid_with_pairs(&mut cx, original, std::slice::from_ref(&checked), &cfg)
        .unwrap();
    let Outcome::Refuted(model) = q.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("the residual has a real counterexample");
    };
    assert!(cx.eval(&[original], &model[..]).unwrap()[0].is_zero());
    assert!(
        model
            .iter()
            .any(|(key, value)| *key == SymbolKey::from("x") && value.to_u64() == Some(7))
    );
    assert!(
        model
            .iter()
            .any(|(key, value)| *key == SymbolKey::from("extra") && value.is_zero())
    );
}

#[test]
fn known_bit_bounds_are_ranges_and_omitted_original_symbols_are_restored() {
    let checked = CheckedPair::verify(KEYS, 0x1234, u64::MAX, 8, VerifyLimits::default()).unwrap();
    assert!(checked.candidates().is_empty());
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    cx.declare_known(
        x,
        KnownBits::new(
            BitVec::from_u64(Width::W64, !255).unwrap(),
            BitVec::from_u64(Width::W64, 128).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    let subject = pair(&mut cx, x, x, false, false);
    let target = k(&mut cx, checked.salt);
    let p = cx.eq(subject, target).unwrap();
    let cfg = Config::default().with_samples(0).with_max_nodes(1);
    let mut q =
        Question::valid_with_pairs(&mut cx, p, std::slice::from_ref(&checked), &cfg).unwrap();
    let Outcome::Refuted(model) = q.solve(&mut cx, Limits::conflicts(1)).unwrap() else {
        panic!("the fact's complete empty preimage set must refute equality");
    };
    assert_eq!(
        model,
        [(
            SymbolKey::from("x"),
            BitVec::from_u64(Width::W64, 128).unwrap()
        )]
    );
    assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());

    // Eight unknown bits at a nonzero upper address are not a small-valued source.
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    cx.declare_known(
        x,
        KnownBits::new(
            BitVec::from_u64(Width::W64, !(255 | (1 << 40))).unwrap(),
            BitVec::from_u64(Width::W64, 1 << 40).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();
    let subject = pair(&mut cx, x, x, false, false);
    let target = k(&mut cx, checked.salt);
    let p = cx.eq(subject, target).unwrap();
    assert_eq!(checked.simplify(&mut cx, p).unwrap(), p);
}

#[test]
fn certificate_requests_keep_the_original_question_and_deep_dags_fall_back() {
    let checked = CheckedPair::verify(KEYS, 0x1234, u64::MAX, 8, VerifyLimits::default()).unwrap();
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let wide = cx.zext(x, Width::W64).unwrap();
    let subject = pair(&mut cx, wide, wide, false, false);
    let target = k(&mut cx, checked.salt);
    let p = cx.ne(subject, target).unwrap();
    let cfg = Config::default()
        .with_samples(0)
        .with_certificate(true)
        .with_max_nodes(0);
    let q = Question::valid_with_pairs(&mut cx, p, std::slice::from_ref(&checked), &cfg).unwrap();
    assert!(matches!(q.outcome(), Some(Outcome::Unknown(_))));
    let mut chain = x;
    for _ in 0..10_000 {
        chain = cx.add(chain, x).unwrap();
    }
    let wide = cx.zext(chain, Width::W64).unwrap();
    let subject = pair(&mut cx, wide, wide, false, false);
    let deep = cx.ne(subject, target).unwrap();
    assert_eq!(checked.simplify(&mut cx, deep).unwrap(), deep);
}

#[test]
fn smaller_domains_do_not_truncate_out_of_range_candidates() {
    let checked = fact();
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W1).unwrap();
    let wide = cx.zext(x, Width::W64).unwrap();
    let subject = pair(&mut cx, wide, wide, false, false);
    let target = k(&mut cx, checked.salt);
    let original = cx.eq(subject, target).unwrap();
    let reduced = checked.simplify(&mut cx, original).unwrap();
    assert!(cx.as_const(reduced).unwrap().is_some_and(|v| v.is_zero()));
    for value in 0..2 {
        let model = [(
            SymbolKey::from("x"),
            BitVec::from_u64(Width::W1, value).unwrap(),
        )];
        let values = cx.eval(&[original, reduced], &model[..]).unwrap();
        assert_eq!(values[0], values[1]);
    }
}

#[test]
fn mask_strengthening_rechecks_candidates_and_weaker_masks_are_not_rewritten() {
    let salt = mixer(KEYS[0], 7) ^ mixer(KEYS[1], 7);
    let checked = CheckedPair::verify(KEYS, salt, 255, 4, VerifyLimits::default()).unwrap();
    assert_eq!(checked.candidates(), &[7]);
    for mask in [127, 255, 511, u64::MAX] {
        for actual_salt in [salt, salt ^ (1 << 40)] {
            let mut cx = Context::new();
            let x = cx.symbol("x", Width::new(4).unwrap()).unwrap();
            let wide = cx.zext(x, Width::W64).unwrap();
            let subject = pair(&mut cx, wide, wide, false, false);
            let s = k(&mut cx, actual_salt);
            let salted = cx.xor(subject, s).unwrap();
            let m = k(&mut cx, mask);
            let masked = cx.and(salted, m).unwrap();
            let zero = k(&mut cx, 0);
            let original = cx.eq(masked, zero).unwrap();
            let rewritten = checked.simplify(&mut cx, original).unwrap();
            if mask == 127 {
                assert_eq!(original, rewritten);
            } else {
                assert_ne!(original, rewritten);
            }
            for value in 0..16 {
                let model = [(
                    SymbolKey::from("x"),
                    BitVec::from_u64(Width::new(4).unwrap(), value).unwrap(),
                )];
                let roots = cx.eval(&[original, rewritten], &model[..]).unwrap();
                assert_eq!(roots[0], roots[1]);
            }
        }
    }
}

#[test]
fn original_assumptions_remain_required_for_counterexamples() {
    let checked = fact();
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let wide = cx.zext(x, Width::W64).unwrap();
    let subject = pair(&mut cx, wide, wide, false, false);
    let target = k(&mut cx, checked.salt);
    let original = cx.ne(subject, target).unwrap();
    let seven = cx.constant_u64(Width::W8, 7).unwrap();
    let excluded = cx.ne(x, seven).unwrap();
    let mut assumptions = crate::Assumptions::new();
    assumptions.assume_true(&mut cx, excluded).unwrap();
    let cfg = Config::default().with_samples(0).with_simplify(false);
    let mut q = Question::valid_under_with_pairs(
        &mut cx,
        original,
        Some(&assumptions),
        std::slice::from_ref(&checked),
        &cfg,
    )
    .unwrap();
    assert!(matches!(
        q.solve(&mut cx, Limits::conflicts(100)).unwrap(),
        Outcome::Proved(None)
    ));
}
