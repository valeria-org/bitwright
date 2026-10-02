use super::*;

fn raw() -> Config {
    Config::default()
        .with_samples(0)
        .with_simplify(false)
        .with_certificate(true)
        .with_relational_lemmas(true)
}

#[test]
fn xor_cancellation_preserves_polarities_shared_outputs_and_nonlinear_leaves() {
    for signs in 0..32 {
        let mut graph = Aig::new();
        let inputs: Vec<_> = (0..4).map(|_| graph.input()).collect();
        let (a, b, c, d) = (inputs[0], inputs[1], inputs[2], inputs[3]);
        let nonlinear = graph.maj(a, b, c);
        let left = graph.xor(nonlinear ^ (signs & 1), d ^ (signs >> 1 & 1));
        let right = graph.xor(nonlinear ^ (signs >> 2 & 1), c ^ (signs >> 3 & 1));
        let old = graph.xor(left, right) ^ (signs >> 4 & 1);
        let reduced = graph.xor_simplified(left, right) ^ (signs >> 4 & 1);
        for assignment in 0..16 {
            let values = graph.eval_all(|i| assignment >> i & 1 == 1);
            assert_eq!(Aig::value(&values, old), Aig::value(&values, reduced));
            assert_eq!(
                Aig::value(&values, left),
                Aig::value(&values, nonlinear ^ (signs & 1))
                    ^ Aig::value(&values, d ^ (signs >> 1 & 1))
            );
        }
    }
}

#[test]
fn shared_input_cancellation_preserves_arithmetic_branches_and_bounded_fallback() {
    let mut rng = Rng(0xca11ce1);
    for depth in [1, 5, 6] {
        for signs in 0..32u32 {
            let mut graph = Aig::new();
            let payload: Vec<_> = (0..12).map(|_| graph.input()).collect();
            let shared = graph.input();
            let mut a = shared ^ (signs & 1);
            let mut b = shared ^ (signs >> 1 & 1);
            for i in 0..depth {
                let left = graph.maj(payload[i], payload[i + 1], payload[i + 3]);
                let right = graph.maj(payload[i + 1], payload[i + 2], payload[i + 4]);
                a = graph.xor(a, left ^ (signs >> 2 & 1));
                b = graph.xor(b, right ^ (signs >> 3 & 1));
            }
            let old = graph.xor(a, b);
            let reduced = graph.xor_cancel_input(a, b);
            for _ in 0..16 {
                let words: Vec<_> = (0..13).map(|_| rng.next()).collect();
                let evaluated = graph.eval_words(|i| words[i as usize]);
                assert_eq!(Aig::word(&evaluated, old), Aig::word(&evaluated, reduced));
            }
            let mut solver = Solver::new();
            let cnf = aig::Cnf::encode(&graph, &[reduced], &mut solver, true);
            if depth <= 5 {
                assert!(cnf.mapped_lit(shared).is_none());
            } else {
                assert_eq!(old, reduced);
            }
            // A separately observed arithmetic branch must still retain the shared input.
            let mut solver = Solver::new();
            let cnf = aig::Cnf::encode(&graph, &[reduced, a], &mut solver, true);
            assert!(cnf.mapped_lit(shared).is_some());
        }
    }
}

#[test]
fn paired_odd_products_eliminate_their_direct_high_input_dependency() {
    for width in [8u16, 32, 64, 129] {
        let mut cx = Context::new();
        let w = Width::new(width).unwrap();
        let x = cx.symbol("x", w).unwrap();
        let mut high = vec![0u64; usize::from(width).div_ceil(64)];
        high[usize::from(width - 1) / 64] = 1u64 << ((width - 1) % 64);
        let high = cx.constant(&BitVec::wrapping_from_limbs(w, &high)).unwrap();
        let changed = cx.xor(x, high).unwrap();
        let a = cx.constant_u64(w, 0x7f).unwrap();
        let b = cx.constant_u64(w, 0x3f).unwrap();
        let pair = |cx: &mut Context, input| {
            let a = cx.mul(a, input).unwrap();
            let b = cx.mul(b, input).unwrap();
            let pair = cx.xor(a, b).unwrap();
            cx.extract(pair, width - 1, Width::W1).unwrap()
        };
        let before = pair(&mut cx, x);
        let after = pair(&mut cx, changed);
        let claim = cx.eq(before, after).unwrap();
        let cfg = Config::default()
            .with_samples(0)
            .with_simplify(false)
            .with_certificate(true)
            .with_input_cancellation(true);
        let mut original =
            Question::valid(&mut cx, claim, &cfg.with_input_cancellation(false)).unwrap();
        let Outcome::Proved(Some(cert)) = original.solve(&mut cx, Limits::conflicts(0)).unwrap()
        else {
            panic!("modular-boundary sharing must also prove the default encoding");
        };
        cert.check().unwrap();
        assert_eq!(original.stats().conflicts, 0);
        let mut question = Question::valid(&mut cx, claim, &cfg).unwrap();
        let Outcome::Proved(Some(cert)) = question.solve(&mut cx, Limits::conflicts(0)).unwrap()
        else {
            panic!("the paired products retained their direct high input bit at width {width}");
        };
        cert.check().unwrap();
        assert_eq!(question.stats().conflicts, 0);
    }
}

#[test]
fn input_cancellation_preserves_declared_bits_models_and_exact_resumption() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let fixed = BitVec::from_u64(Width::W64, 1 << 63).unwrap();
    cx.declare_known(
        x,
        crate::KnownBits::new(BitVec::zero(Width::W64), fixed).unwrap(),
    )
    .unwrap();
    let a = cx.constant_u64(Width::W64, 0x7f).unwrap();
    let b = cx.constant_u64(Width::W64, 0x3f).unwrap();
    let a = cx.mul(a, x).unwrap();
    let b = cx.mul(b, x).unwrap();
    let pair = cx.xor(a, b).unwrap();
    let high = cx.extract(pair, 63, Width::W1).unwrap();
    let low = cx.extract(x, 0, Width::W1).unwrap();
    let claim = cx.eq(high, low).unwrap();
    let cfg = raw().with_input_cancellation(true);
    let mut whole = Question::valid(&mut cx, claim, &cfg).unwrap();
    let Outcome::Refuted(expected) = whole.solve(&mut cx, Limits::conflicts(1_000)).unwrap() else {
        panic!("the high/low-bit equivalence should retain a counterexample");
    };
    assert_eq!(expected[0].1.bit(63), Some(true));
    assert!(cx.eval(&[claim], &expected[..]).unwrap()[0].is_zero());
    let mut stepped = Question::valid(&mut cx, claim, &cfg).unwrap();
    loop {
        let before = stepped.stats();
        let answer = stepped
            .solve(
                &mut cx,
                Limits {
                    conflicts: 1_000,
                    propagations: 1,
                },
            )
            .unwrap();
        assert!(stepped.stats().propagations - before.propagations <= 1);
        match answer {
            Outcome::Refuted(model) => {
                assert_eq!(model, expected);
                break;
            }
            Outcome::Unknown(_) => {}
            other => panic!("unexpected outcome: {other:?}"),
        }
    }
    assert_eq!(stepped.stats(), whole.stats());
}

#[test]
fn bounded_xor_rewriting_preserves_large_and_deep_parity_cones() {
    let mut rng = Rng(0x5a17);
    for size in [2, 16, 17, 64, 4096] {
        let mut graph = Aig::new();
        let inputs: Vec<_> = (0..size).map(|_| graph.input()).collect();
        let mut left = aig::FALSE;
        let mut right = aig::TRUE;
        for (i, &input) in inputs.iter().enumerate() {
            left = graph.xor(left, input ^ (i as u32 & 1));
            right = graph.xor(right, input ^ (i as u32 >> 1 & 1));
        }
        let old = graph.xor(left, right);
        let reduced = graph.xor_simplified(left, right);
        for _ in 0..16 {
            let assignments: Vec<_> = (0..size).map(|_| rng.next()).collect();
            let values = graph.eval_words(|i| assignments[i as usize]);
            assert_eq!(Aig::word(&values, old), Aig::word(&values, reduced));
        }
    }
}

#[test]
fn large_signed_equality_components_retain_checked_models_and_proof_prefixes() {
    let mut cx = Context::new();
    let symbols: Vec<_> = (0..129)
        .map(|i| cx.symbol(format!("v{i}"), Width::W1).unwrap())
        .collect();
    let mut chain = cx.one(Width::W1).unwrap();
    for (i, adjacent) in symbols.windows(2).enumerate() {
        let b = if i % 2 == 0 {
            cx.not(adjacent[1]).unwrap()
        } else {
            adjacent[1]
        };
        let equal = cx.eq(adjacent[0], b).unwrap();
        chain = cx.and(chain, equal).unwrap();
    }
    let claim = cx.not(chain).unwrap();
    let mut question = Question::valid(&mut cx, claim, &raw()).unwrap();
    assert!(question.stats().learned > 0);
    let search = question.search.as_ref().unwrap();
    drup::check_prefix(&search.cnf.clauses, search.solver.proof_steps().unwrap()).unwrap();
    let Outcome::Refuted(model) = question.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("a long acyclic signed equality chain is satisfiable");
    };
    assert_eq!(model.len(), symbols.len());
    assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
}

#[test]
fn root_conditioned_aliases_have_checked_proof_prefixes_without_extra_premises() {
    for width in [1, 8, 65, 129, 512] {
        let mut cx = Context::new();
        let w = Width::new(width).unwrap();
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let z = cx.symbol("z", w).unwrap();
        let a = cx.xor(x, y).unwrap();
        let b = cx.xor(x, z).unwrap();
        let target = cx
            .constant(&BitVec::wrapping_from_limbs(
                w,
                &[if width == 1 { 0 } else { 0x55 }],
            ))
            .unwrap();
        let combined = cx.or(a, b).unwrap();
        let claim = cx.ne(combined, target).unwrap();
        let mut question = Question::valid(&mut cx, claim, &raw()).unwrap();
        let search = question.search.as_ref().unwrap();
        assert!(search.solver.num_learnts() > 0);
        let proof = search.solver.proof_steps().unwrap();
        assert!(!proof.is_empty());
        drup::check_prefix(&search.cnf.clauses, proof).unwrap();
        // Strengthening is logged as derivation, not included in the question's premises.
        assert_eq!(question.stats().clauses, search.cnf.clauses.len());
        let Outcome::Refuted(model) = question.solve(&mut cx, Limits::conflicts(100)).unwrap()
        else {
            panic!("a satisfiable mask must retain its original-symbol witness");
        };
        assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
    }
}

#[test]
fn contradictory_masked_parity_cycles_prove_without_sat_conflicts() {
    for width in [1, 8, 65, 512] {
        let mut cx = Context::new();
        let w = Width::new(width).unwrap();
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let z = cx.symbol("z", w).unwrap();
        let xy = cx.xor(x, y).unwrap();
        let yz = cx.xor(y, z).unwrap();
        let xz = cx.xor(x, z).unwrap();
        let one = cx.one(w).unwrap();
        let wrong = cx.xor(xz, one).unwrap();
        let a = cx.or(xy, yz).unwrap();
        let a = cx.or(a, wrong).unwrap();
        let zero = cx.zero(w).unwrap();
        let claim = cx.ne(a, zero).unwrap();
        for lemmas in [false, true] {
            let cfg = raw().with_relational_lemmas(lemmas);
            let mut question = Question::valid(&mut cx, claim, &cfg).unwrap();
            let search = question.search.as_ref().unwrap();
            drup::check_prefix(&search.cnf.clauses, search.solver.proof_steps().unwrap()).unwrap();
            let Outcome::Proved(Some(cert)) =
                question.solve(&mut cx, Limits::conflicts(0)).unwrap()
            else {
                panic!("a contradictory parity cycle should close during preparation");
            };
            cert.check().unwrap();
            assert_eq!(question.stats().conflicts, 0);
        }
    }
}

#[test]
fn one_bits_of_or_targets_require_coverage_instead_of_forcing_each_term() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let y = cx.symbol("y", Width::W8).unwrap();
    let z = cx.symbol("z", Width::W8).unwrap();
    let xy = cx.xor(x, y).unwrap();
    let xz = cx.xor(x, z).unwrap();
    let combined = cx.or(xy, xz).unwrap();
    let ones = cx.ones(Width::W8).unwrap();
    let claim = cx.ne(combined, ones).unwrap();
    let mut question = Question::valid(&mut cx, claim, &raw()).unwrap();
    assert_eq!(question.stats().learned, 0);
    let search = question.search.as_ref().unwrap();
    drup::check_prefix(&search.cnf.clauses, search.solver.proof_steps().unwrap()).unwrap();
    let Outcome::Refuted(model) = question.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("coverage can be satisfied")
    };
    assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
}

#[test]
fn proof_prefix_checker_rejects_unjustified_relations_on_satisfiable_inputs() {
    let a = Lit::pos(0);
    let b = Lit::pos(1);
    assert!(drup::check_prefix(&[vec![a, b]], &[Step::Add(vec![a])]).is_err());
    assert!(drup::check(&[vec![a, b]], &[]).is_err());
    drup::check_prefix(&[vec![a, b]], &[]).unwrap();
}

#[test]
fn selectors_do_not_assume_a_count_value_and_resume_exactly() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W16).unwrap();
    let count = cx.symbol("count", Width::new(4).unwrap()).unwrap();
    let count = cx.zext(count, Width::W16).unwrap();
    let shifted = cx.bin(BinOp::LShr, x, count).unwrap();
    let high_count = cx.constant_u64(Width::W16, 15).unwrap();
    let is_high = cx.eq(count, high_count).unwrap();
    let one = cx.one(Width::W16).unwrap();
    let output_one = cx.eq(shifted, one).unwrap();
    let witness = cx.and(is_high, output_one).unwrap();
    let claim = cx.not(witness).unwrap();
    let cfg = raw().with_selector_branching(true);
    let mut whole = Question::valid(&mut cx, claim, &cfg).unwrap();
    let want = whole.solve(&mut cx, Limits::conflicts(100)).unwrap();
    let Outcome::Refuted(model) = &want else {
        panic!("the largest selector value is reachable")
    };
    assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
    assert_eq!(
        model
            .iter()
            .find(|(k, _)| *k == SymbolKey::from("count"))
            .unwrap()
            .1
            .to_u64(),
        Some(15)
    );
    let mut stepped = Question::valid(&mut cx, claim, &cfg).unwrap();
    loop {
        let before = stepped.stats();
        let answer = stepped
            .solve(
                &mut cx,
                Limits {
                    conflicts: 100,
                    propagations: 1,
                },
            )
            .unwrap();
        assert!(stepped.stats().propagations - before.propagations <= 1);
        if let Outcome::Refuted(model) = answer {
            let Outcome::Refuted(want) = &want else {
                unreachable!()
            };
            assert_eq!(&model, want);
            break;
        }
        assert!(matches!(answer, Outcome::Unknown(_)));
    }
    assert_eq!(stepped.stats(), whole.stats());
}

#[test]
fn signed_relations_agree_with_brute_force_and_all_derivations_check() {
    let mut rng = Rng(0x13579);
    for _ in 0..96 {
        let mut cx = Context::new();
        let symbols: Vec<_> = (0..5)
            .map(|i| cx.symbol(format!("v{i}"), Width::W1).unwrap())
            .collect();
        let mut conjunction = cx.one(Width::W1).unwrap();
        for _ in 0..2 + rng.below(12) {
            let a = symbols[rng.below(5) as usize];
            let mut b = symbols[rng.below(5) as usize];
            if rng.below(2) == 1 {
                b = cx.not(b).unwrap();
            }
            let equal = cx.eq(a, b).unwrap();
            conjunction = cx.and(conjunction, equal).unwrap();
        }
        let expected_sat = (0..32).any(|assignment| {
            let env: Vec<_> = (0..5)
                .map(|i| {
                    (
                        SymbolKey::from(format!("v{i}")),
                        BitVec::from_bool(assignment >> i & 1 == 1),
                    )
                })
                .collect();
            !cx.eval(&[conjunction], &env[..]).unwrap()[0].is_zero()
        });
        let claim = cx.not(conjunction).unwrap();
        for lemmas in [false, true] {
            let mut question =
                Question::valid(&mut cx, claim, &raw().with_relational_lemmas(lemmas)).unwrap();
            let search = question.search.as_ref().unwrap();
            drup::check_prefix(&search.cnf.clauses, search.solver.proof_steps().unwrap()).unwrap();
            match question.solve(&mut cx, Limits::conflicts(100)).unwrap() {
                Outcome::Refuted(model) => {
                    assert!(expected_sat);
                    assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
                }
                Outcome::Proved(Some(cert)) => {
                    assert!(!expected_sat);
                    cert.check().unwrap();
                }
                other => panic!("small equality system was not decided: {other:?}"),
            }
        }
    }
}
