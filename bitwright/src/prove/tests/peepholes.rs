use super::*;

#[test]
fn boolean_word_products_use_conditional_copies_for_both_encodings() {
    use bitwright_ref as reference;
    for width in [1u16, 8, 32, 64, 65, 129, 512] {
        for compressed in [false, true] {
            for swap in [false, true] {
                for polarity in [0, 1] {
                    let mut graph = Aig::new();
                    let flag = graph.input() ^ polarity;
                    let data = (0..width).map(|_| graph.input()).collect::<Vec<_>>();
                    let mut factor = vec![aig::FALSE; usize::from(width)];
                    factor[0] = flag;
                    let (a, b) = if swap {
                        (&data, &factor)
                    } else {
                        (&factor, &data)
                    };
                    let before = graph.len();
                    let product = if compressed {
                        blast::mul_carry_save(&mut graph, a, b)
                    } else {
                        blast::mul(&mut graph, a, b)
                    };
                    assert_eq!(graph.len() - before, usize::from(width));
                    let mut rng = Rng(0x719e_352a_c42f_689d);
                    let words = (0..=width).map(|_| rng.next()).collect::<Vec<_>>();
                    let values = graph.eval_words(|i| words[i as usize]);
                    for lane in 0..64 {
                        let input = reference::Bits::from_bools(
                            data.iter()
                                .map(|&bit| Aig::word(&values, bit) >> lane & 1 == 1)
                                .collect(),
                        );
                        let scalar_flag = reference::Bits::from_u128(
                            width,
                            u128::from(Aig::word(&values, flag) >> lane & 1),
                        );
                        let want = reference::bin(reference::BinOp::Mul, &input, &scalar_flag);
                        for (bit, &literal) in product.iter().enumerate() {
                            assert_eq!(
                                Aig::word(&values, literal) >> lane & 1 == 1,
                                want.bit(bit as u16)
                            );
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn nonzero_high_multiplier_bits_do_not_use_boolean_copy_rule() {
    for compressed in [false, true] {
        for swap in [false, true] {
            let mut graph = Aig::new();
            let flag = graph.input();
            let data = (0..8).map(|_| graph.input()).collect::<Vec<_>>();
            let mut factor = vec![aig::FALSE; 8];
            factor[0] = flag;
            factor[1] = aig::TRUE;
            assert!(blast::binary_factor(&factor, &data).is_none());
            let (a, b) = if swap {
                (&data, &factor)
            } else {
                (&factor, &data)
            };
            let product = if compressed {
                blast::mul_carry_save(&mut graph, a, b)
            } else {
                blast::mul(&mut graph, a, b)
            };
            for assignment in 0..512u32 {
                let values = graph.eval_all(|i| assignment >> i & 1 == 1);
                let value = product.iter().enumerate().fold(0u32, |v, (i, &bit)| {
                    v | (u32::from(Aig::value(&values, bit)) << i)
                });
                assert_eq!(value, ((assignment >> 1) * (2 + (assignment & 1))) & 255);
            }
        }
    }
}

#[test]
fn shared_xor_or_factoring_preserves_all_polarities_and_checked_certificates() {
    for count in 2..=4usize {
        for signs in 0..32u32 {
            let mut graph = Aig::new();
            let common = graph.input();
            let inputs: Vec<_> = (0..count).map(|_| graph.input()).collect();
            let terms: Vec<_> = inputs
                .iter()
                .enumerate()
                .map(|(i, &input)| {
                    graph.xor(common ^ (signs >> i & 1), input ^ (signs >> (i + 1) & 1))
                })
                .collect();
            let old = if count == 4 {
                let left = graph.or(terms[0], terms[1]);
                let right = graph.or(terms[2], terms[3]);
                graph.or(left, right)
            } else {
                graph.or_all(&terms)
            };
            let reduced = graph.factor_positive_or(old, 2);
            assert_eq!(graph.factor_positive_or(old ^ 1, 2), old ^ 1);
            for assignment in 0..1u32 << (count + 1) {
                let values = graph.eval_all(|i| assignment >> i & 1 == 1);
                assert_eq!(Aig::value(&values, old), Aig::value(&values, reduced));
            }
            if count >= 3 {
                let mut before = Solver::new();
                let old_cnf = aig::Cnf::encode(&graph, &[old], &mut before, true);
                let mut after = Solver::new();
                let new_cnf = aig::Cnf::encode(&graph, &[reduced], &mut after, true);
                assert!(after.num_vars() < before.num_vars());
                assert!(new_cnf.emitted() < old_cnf.emitted());
            }
            // Retain original/shared outputs in the certificate's cone too.
            let differs = graph.xor(old, reduced);
            let mut solver = Solver::new();
            solver.log_proof();
            let mut roots = terms;
            roots.extend([differs, old]);
            let mut cnf = aig::Cnf::encode(&graph, &roots, &mut solver, true);
            cnf.assert(differs, &mut solver);
            assert_eq!(solver.solve(1_000), Answer::Unsat);
            drup::check(&cnf.clauses, &solver.take_proof().unwrap()).unwrap();
        }
    }
}

#[test]
fn unrelated_xor_and_mux_terms_do_not_factor() {
    let mut graph = Aig::new();
    let inputs: Vec<_> = (0..6).map(|_| graph.input()).collect();
    let a = graph.xor(inputs[0], inputs[1]);
    let b = graph.xor(inputs[2], inputs[3]);
    let original = graph.or(a, b);
    assert_eq!(graph.factor_positive_or(original, 2), original);
    let a = graph.mux(inputs[0], inputs[1], inputs[2]);
    let b = graph.mux(inputs[3], inputs[4], inputs[5]);
    let original = graph.or(a, b);
    assert_eq!(graph.factor_positive_or(original, 2), original);
}

#[test]
fn native_factoring_keeps_zero_target_aliases_and_replays_mixed_target_models() {
    for bits in [1u16, 8, 65] {
        for target in [0u64, 1, 0x55, 0xa5] {
            let mut cx = Context::new();
            let w = Width::new(bits).unwrap();
            let common = cx.symbol("common", w).unwrap();
            let mut terms = Vec::new();
            for key in ["b", "c", "d"] {
                let leaf = cx.symbol(key, w).unwrap();
                terms.push(cx.xor(common, leaf).unwrap());
            }
            let pair = cx.or(terms[0], terms[1]).unwrap();
            let combined = cx.or(pair, terms[2]).unwrap();
            let value = cx.constant(&BitVec::wrapping_from_u64(w, target)).unwrap();
            let claim = cx.ne(combined, value).unwrap();
            let cfg = Config::default()
                .with_samples(0)
                .with_simplify(false)
                .with_certificate(true)
                .with_relational_lemmas(true);
            let baseline = Question::valid(&mut cx, claim, &cfg).unwrap();
            let mut question =
                Question::valid(&mut cx, claim, &cfg.with_join_factoring(true)).unwrap();
            if target == 0 {
                assert_eq!(question.stats(), baseline.stats());
            }
            let search = question.search.as_ref().unwrap();
            drup::check_prefix(&search.cnf.clauses, search.solver.proof_steps().unwrap()).unwrap();
            let Outcome::Refuted(model) =
                question.solve(&mut cx, Limits::conflicts(1_000)).unwrap()
            else {
                panic!("a factored OR must retain its original-symbol witness");
            };
            assert_eq!(model.len(), 4);
            assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
        }
    }
}

#[test]
fn native_positive_target_factoring_has_checked_complete_certificates() {
    for bits in [1, 8, 65] {
        let mut cx = Context::new();
        let w = Width::new(bits).unwrap();
        let x = cx.symbol("x", w).unwrap();
        let leaves: Vec<_> = ["b", "c", "d"]
            .iter()
            .map(|&key| cx.symbol(key, w).unwrap())
            .collect();
        let terms: Vec<_> = leaves
            .iter()
            .map(|&leaf| cx.xor(x, leaf).unwrap())
            .collect();
        let combined = cx.or(terms[0], terms[1]).unwrap();
        let combined = cx.or(combined, terms[2]).unwrap();
        let all = cx.and(leaves[0], leaves[1]).unwrap();
        let all = cx.and(all, leaves[2]).unwrap();
        let not_all = cx.not(all).unwrap();
        let any = cx.or(leaves[0], leaves[1]).unwrap();
        let any = cx.or(any, leaves[2]).unwrap();
        let t = cx.and(x, not_all).unwrap();
        let not_x = cx.not(x).unwrap();
        let e = cx.and(not_x, any).unwrap();
        let expected = cx.or(t, e).unwrap();
        let ones = cx.ones(w).unwrap();
        let actual_one = cx.eq(combined, ones).unwrap();
        let expected_one = cx.eq(expected, ones).unwrap();
        let claim = cx.eq(actual_one, expected_one).unwrap();
        let cfg = Config::default()
            .with_samples(0)
            .with_simplify(false)
            .with_certificate(true)
            .with_join_factoring(true);
        let mut question = Question::valid(&mut cx, claim, &cfg).unwrap();
        let Outcome::Proved(Some(cert)) =
            question.solve(&mut cx, Limits::conflicts(10_000)).unwrap()
        else {
            panic!("positive OR factoring must be proved");
        };
        cert.check().unwrap();
    }
}
