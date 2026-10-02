use super::*;

fn keys() -> Vec<u64> {
    let mut keys = vec![
        0xc26a_114a_f502_712b,
        0xcbb4_ec85_4c6b_3e87,
        0xce8b_b36c_f4ae_36f5,
        0xd9d7_620d_5093_d5a1,
    ];
    let mut state = 0x1234_5678_9abc_def0u64;
    for _ in 0..28 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        keys.push(state | 1);
    }
    keys
}

#[test]
fn parallel_signed_digit_cost_matches_serial_carries() {
    fn serial(value: u64) -> usize {
        if value == 0 {
            return 0;
        }
        let mut carry = false;
        let mut signed = Vec::new();
        let mut ordinary = Vec::new();
        for bit in 0..64 {
            let set = value >> bit & 1 != 0;
            if set {
                ordinary.push(bit);
            }
            match usize::from(set) + usize::from(carry) {
                0 => carry = false,
                2 => carry = true,
                _ => {
                    let negative = bit < 63 && value >> (bit + 1) & 1 != 0;
                    signed.push((bit, negative));
                    carry = negative;
                }
            }
        }
        let last = signed.last().unwrap();
        if signed.len() + usize::from(last.1) >= ordinary.len() {
            ordinary.iter().map(|bit| 64 - bit).sum::<usize>() - (64 - ordinary[0])
        } else {
            signed.iter().map(|(bit, _)| 64 - bit).sum::<usize>()
                - if last.1 { 0 } else { 64 - last.0 }
        }
    }
    let mut state = 0x0073_9221_9314_u64;
    for value in (0..=u16::MAX)
        .map(u64::from)
        .chain([1 << 63, u64::MAX, u64::MAX - 1])
    {
        assert_eq!(constant_work(value, 64), serial(value));
    }
    for _ in 0..32_768 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        assert_eq!(constant_work(state, 64), serial(state));
    }
}

#[test]
fn factor_plans_are_exact_modular_identities_and_bounded() {
    let mut selected = 0;
    let mut corrections = [false; 3];
    for key in keys()
        .into_iter()
        .chain([0, 1, 2, 111, u64::MAX, u64::MAX - 1])
    {
        let constant = small(64, key);
        if let Some((first, second, correction)) = constant_factors(&constant) {
            assert!((3..256).contains(&first));
            assert_eq!(first & 1, 1);
            assert!((-1..=1).contains(&correction));
            corrections[(correction + 1) as usize] = true;
            assert_eq!(
                first
                    .wrapping_mul(second)
                    .wrapping_add_signed(i64::from(correction)),
                key
            );
            let correction_work = match correction {
                1 if second != 0 => 64 - second.trailing_zeros() as usize,
                0 => 0,
                _ => 64,
            };
            let work = constant_work(first, 64) + constant_work(second, 64) + correction_work;
            assert!(work * 10 <= constant_work(key, 64) * 9);
            selected += 1;
        }
        for width in [1, 8, 31, 32, 63, 65, 129, 512] {
            assert!(constant_factors(&small(width, key)).is_none());
        }
    }
    assert!(selected >= 4);
    assert!(corrections.into_iter().all(|covered| covered));
    let mut mixed = small(64, keys()[0]);
    mixed[7] = 4;
    assert!(constant_factors(&mixed).is_none());
}

#[test]
fn factor_data_guards_reject_narrow_and_repeated_literals() {
    let mut graph = Aig::new();
    let inputs: Bits = (0..64).map(|_| graph.input()).collect();
    assert!(factorable_data(&inputs));
    let mut low = inputs[..32].to_vec();
    low.resize(64, TRUE);
    assert!(factorable_data(&low));
    low[63] = FALSE;
    assert!(!factorable_data(&low));
    let mut repeated: Bits = (0..64).map(|i| inputs[i % 31] ^ (i as u32 & 1)).collect();
    assert!(!factorable_data(&repeated));
    repeated[63] = inputs[31];
    assert!(factorable_data(&repeated));
    repeated[0] = TRUE;
    assert!(!factorable_data(&repeated));
    for width in [0, 1, 32, 63, 65, 129] {
        assert!(!factorable_data(&small(width, 1)));
    }
}

#[test]
fn affine_product_identities_prove_without_search_and_missing_corrections_refute() {
    use crate::prove::{Config, Limits, Outcome, Question};
    use crate::{BitVec, Context, SymbolKey, Width};

    // These independent coefficients exercise three different small factors. The
    // scalar identity checks the recipe before the native compiler sees it.
    for key in keys().into_iter().skip(1).take(3) {
        let (factor, other, correction) = constant_factors(&small(64, key)).unwrap();
        assert_ne!(correction, 0);
        assert_eq!(
            factor
                .wrapping_mul(other)
                .wrapping_add_signed(i64::from(correction)),
            key
        );
        assert!(constant_work(factor, 64) <= 128);
        for narrow in [false, true] {
            for compressed in [false, true] {
                let mut cx = Context::new();
                let width = if narrow { Width::W32 } else { Width::W64 };
                let source = cx.symbol("source", width).unwrap();
                let word = if narrow {
                    let low = cx.zext(source, Width::W64).unwrap();
                    let high = cx.constant_u64(Width::W64, 0xffff_ffff_0000_0000).unwrap();
                    cx.or(low, high).unwrap()
                } else {
                    source
                };
                let k = cx.constant_u64(Width::W64, key).unwrap();
                let original = cx.mul(word, k).unwrap();
                let a = cx.constant_u64(Width::W64, factor).unwrap();
                let b = cx.constant_u64(Width::W64, other).unwrap();
                let first = cx.mul(word, a).unwrap();
                let product = cx.mul(first, b).unwrap();
                let reconstructed = if correction == 1 {
                    cx.add(product, word).unwrap()
                } else {
                    cx.sub(product, word).unwrap()
                };
                let claim = cx.eq(original, reconstructed).unwrap();
                for value in [0, 1, 17, 1 << 31, 1 << 63, u64::MAX] {
                    let model = [(
                        SymbolKey::from("source"),
                        BitVec::wrapping_from_u64(width, value),
                    )];
                    assert!(!cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
                }
                let cfg = Config::default()
                    .with_samples(0)
                    .with_simplify(false)
                    .with_certificate(true)
                    .with_carry_save_multiplication(compressed)
                    .with_xor3_encoding(compressed);
                let mut q = Question::valid(&mut cx, claim, &cfg).unwrap();
                let Outcome::Proved(Some(cert)) = q
                    .solve(
                        &mut cx,
                        Limits {
                            conflicts: 0,
                            propagations: 0,
                        },
                    )
                    .unwrap()
                else {
                    panic!("the original and affine coefficient products must share their circuit");
                };
                assert_eq!(q.stats().vars, 1);
                cert.check().unwrap();

                let near_miss = cx.eq(original, product).unwrap();
                // A point witness is enough to reject the near miss. Use original-word
                // sampling rather than requiring SAT to rediscover this arithmetic model.
                let counter_cfg = cfg.with_word_sampling(true).with_samples(64);
                let mut q = Question::valid(&mut cx, near_miss, &counter_cfg).unwrap();
                let Outcome::Refuted(model) = q
                    .solve(
                        &mut cx,
                        Limits {
                            conflicts: 256,
                            propagations: 75_000,
                        },
                    )
                    .unwrap()
                else {
                    panic!("dropping a nonzero correction must retain a real counterexample");
                };
                assert!(cx.eval(&[near_miss], &model[..]).unwrap()[0].is_zero());
                assert_eq!(model.len(), 1);
                assert_eq!(model[0].0, SymbolKey::from("source"));
                assert_eq!(model[0].1.width(), width);
            }
        }
    }
}

#[test]
fn factored_products_preserve_fixed_and_correlated_input_values() {
    let mut full_before = 0;
    let mut full_after = 0;
    for key in keys() {
        for mode in 0..8 {
            for compressed in [false, true] {
                let mut sizes = Vec::new();
                for factored in [false, true] {
                    let mut graph = Aig::new();
                    let inputs: Bits = (0..64).map(|_| graph.input()).collect();
                    let data: Bits = (0..64)
                        .map(|i| match mode {
                            0 => inputs[i],
                            1 => {
                                if i < 8 {
                                    inputs[i]
                                } else {
                                    FALSE
                                }
                            }
                            2 => {
                                if i < 8 {
                                    inputs[i]
                                } else {
                                    TRUE
                                }
                            }
                            3 => inputs[i % 7] ^ (i as u32 & 1),
                            4 => u32::from(i % 2 == 0),
                            5 => {
                                if i < 32 {
                                    inputs[i]
                                } else {
                                    FALSE
                                }
                            }
                            6 => {
                                if i < 32 {
                                    FALSE
                                } else {
                                    inputs[i]
                                }
                            }
                            _ => {
                                if i < 32 {
                                    inputs[i]
                                } else {
                                    TRUE
                                }
                            }
                        })
                        .collect();
                    let constant = small(64, key);
                    let output = match (factored, compressed) {
                        (false, false) => mul_constant_unfactored(&mut graph, &data, &constant),
                        (false, true) => mul_carry_save_unfactored(&mut graph, &data, &constant),
                        (true, false) => mul(&mut graph, &data, &constant),
                        (true, true) => mul_carry_save(&mut graph, &data, &constant),
                    };
                    sizes.push(graph.len());
                    let values = graph.eval_words(|i| {
                        let mut s = 0x9876_5432_10ab_cdefu64.wrapping_add(u64::from(i) * 7919);
                        s ^= s << 13;
                        s ^= s >> 7;
                        s ^= s << 17;
                        s
                    });
                    for lane in 0..64 {
                        let mut input = 0u64;
                        let mut got = 0u64;
                        for i in 0..64 {
                            input |= (Aig::word(&values, data[i]) >> lane & 1) << i;
                            got |= (Aig::word(&values, output[i]) >> lane & 1) << i;
                        }
                        assert_eq!(got, input.wrapping_mul(key));
                    }
                }
                if mode == 0 {
                    full_before += sizes[0];
                    full_after += sizes[1];
                } else if mode != 7 {
                    assert_eq!(
                        sizes[0], sizes[1],
                        "ineligible data must retain its circuit"
                    );
                }
            }
        }
    }
    assert!(full_after < full_before);
}

#[test]
fn factored_native_products_preserve_models_continuation_and_certificates() {
    use crate::prove::{Config, Limits, Outcome, Question};
    use crate::{Context, Width};

    for compressed in [false, true] {
        for key in keys().into_iter().take(4) {
            let mut cx = Context::new();
            let x = cx.symbol("x", Width::W64).unwrap();
            let constant = cx.constant_u64(Width::W64, key).unwrap();
            let product = cx.mul(x, constant).unwrap();
            let chosen = 0x8123_4567_89ab_cdefu64;
            let target = cx
                .constant_u64(Width::W64, chosen.wrapping_mul(key))
                .unwrap();
            let claim = cx.ne(product, target).unwrap();
            let cfg = Config::default()
                .with_simplify(false)
                .with_samples(0)
                .with_certificate(true)
                .with_carry_save_multiplication(compressed)
                .with_xor3_encoding(compressed);
            let mut whole = Question::valid(&mut cx, claim, &cfg).unwrap();
            let Outcome::Refuted(expected) = whole.solve(&mut cx, Limits::conflicts(1000)).unwrap()
            else {
                panic!("a single odd product must have its unique original-input model");
            };
            assert_eq!(expected[0].1.to_u64(), Some(chosen));
            assert!(cx.eval(&[claim], &expected[..]).unwrap()[0].is_zero());

            // A fully specified odd image propagates immediately. The opposite
            // question leaves the input free and exercises interrupted search.
            let broad = cx.eq(product, target).unwrap();
            let mut whole = Question::valid(&mut cx, broad, &cfg).unwrap();
            let Outcome::Refuted(expected) = whole.solve(&mut cx, Limits::conflicts(1000)).unwrap()
            else {
                panic!("an odd product has inputs outside one selected image");
            };
            assert!(cx.eval(&[broad], &expected[..]).unwrap()[0].is_zero());
            let mut stepped = Question::valid(&mut cx, broad, &cfg).unwrap();
            let mut interruptions = 0;
            loop {
                let before = stepped.stats();
                match stepped
                    .solve(
                        &mut cx,
                        Limits {
                            conflicts: u64::MAX,
                            propagations: 31,
                        },
                    )
                    .unwrap()
                {
                    Outcome::Unknown(_) => {
                        interruptions += 1;
                        assert!(stepped.stats().propagations - before.propagations <= 31);
                    }
                    Outcome::Refuted(model) => {
                        assert_eq!(model, expected);
                        break;
                    }
                    other => panic!("unexpected product result: {other:?}"),
                }
            }
            assert!(interruptions > 1);
            assert_eq!(stepped.stats(), whole.stats());

            let value = cx.constant_u64(Width::W64, chosen).unwrap();
            let at_value = cx.eq(x, value).unwrap();
            let not_at_value = cx.not(at_value).unwrap();
            let matches = cx.eq(product, target).unwrap();
            let implication = cx.or(not_at_value, matches).unwrap();
            let mut question = Question::valid(&mut cx, implication, &cfg).unwrap();
            let Outcome::Proved(Some(cert)) =
                question.solve(&mut cx, Limits::conflicts(0)).unwrap()
            else {
                panic!("a fully fixed factored product must prove without search");
            };
            cert.check().unwrap();
        }
    }
}
