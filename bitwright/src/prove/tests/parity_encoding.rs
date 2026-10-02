use super::*;

#[test]
fn shared_logical_cones_preserve_every_observed_root_and_polarity() {
    for signs in 0..16u32 {
        let mut graph = Aig::new();
        let inputs: Vec<_> = (0..4).map(|_| graph.input()).collect();
        let signed: Vec<_> = inputs
            .iter()
            .enumerate()
            .map(|(i, &l)| l ^ (signs >> i & 1))
            .collect();
        let xy = graph.xor(signed[0], signed[1]);
        let sum = graph.xor(xy, signed[2]);
        let carry = graph.maj(signed[0], signed[1], signed[2]);
        let mux = graph.mux(signed[3], signed[0], sum);
        let product = graph.and(signed[0], signed[1]);
        let then_product = graph.and(signed[3], signed[0]);
        let else_product = graph.and(signed[3] ^ 1, sum);
        let all = [sum, carry, mux, xy, product, then_product, else_product];

        for observed in 0..16u32 {
            let indices: Vec<_> = (0..3)
                .chain((3..7).filter(|&i| observed >> (i - 3) & 1 != 0))
                .collect();
            let roots: Vec<_> = indices
                .iter()
                .map(|&i| all[i] ^ (signs >> (i % 4) & 1))
                .collect();
            for xor3 in [false, true] {
                for assignment in 0..16u32 {
                    let values: Vec<_> =
                        (0..4).map(|i| (assignment ^ signs) >> i & 1 != 0).collect();
                    let parity = values[0] ^ values[1] ^ values[2];
                    let expected = [
                        parity,
                        values[..3].iter().filter(|&&v| v).count() >= 2,
                        if values[3] { values[0] } else { parity },
                        values[0] ^ values[1],
                        values[0] && values[1],
                        values[3] && values[0],
                        !values[3] && parity,
                    ];
                    let expected: Vec<_> = indices
                        .iter()
                        .map(|&i| expected[i] ^ (signs >> (i % 4) & 1 != 0))
                        .collect();
                    for corrupt in [false, true] {
                        let mut solver = Solver::new();
                        solver.log_proof();
                        let mut cnf =
                            aig::Cnf::encode_with_xor3(&graph, &roots, &mut solver, true, xor3);
                        for &root in &roots {
                            assert!(cnf.mapped_lit(root).is_some());
                        }
                        for (i, &input) in inputs.iter().enumerate() {
                            cnf.assert(input ^ u32::from(assignment >> i & 1 == 0), &mut solver);
                        }
                        let wrong = (assignment + signs + observed) as usize % roots.len();
                        for (i, (&root, &value)) in roots.iter().zip(&expected).enumerate() {
                            let wanted = value ^ (corrupt && i == wrong);
                            cnf.assert(root ^ u32::from(!wanted), &mut solver);
                        }
                        match solver.solve(100) {
                            Answer::Sat(model) => {
                                assert!(!corrupt);
                                for (&root, &value) in roots.iter().zip(&expected) {
                                    assert_eq!(cnf.value(root, &model), value);
                                }
                                assert!(cnf.clauses.iter().all(|clause| {
                                    clause.iter().any(|l| model[l.var() as usize] != l.is_neg())
                                }));
                            }
                            Answer::Unsat => {
                                assert!(corrupt);
                                drup::check(&cnf.clauses, &solver.take_proof().unwrap()).unwrap();
                            }
                            Answer::Unknown => panic!("a complete observed input must settle"),
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn three_input_parity_is_exact_for_all_input_intermediate_and_output_polarities() {
    for signs in 0..32u32 {
        let mut graph = Aig::new();
        let inputs: Vec<_> = (0..3).map(|_| graph.input()).collect();
        let ab =
            graph.xor(inputs[0] ^ (signs & 1), inputs[1] ^ (signs >> 1 & 1)) ^ (signs >> 3 & 1);
        let output = graph.xor(ab, inputs[2] ^ (signs >> 2 & 1)) ^ (signs >> 4 & 1);
        for assignment in 0..8u32 {
            let expected = (assignment.count_ones() & 1) ^ (signs.count_ones() & 1);
            for wanted in 0..2 {
                let mut solver = Solver::new();
                solver.log_proof();
                let mut cnf =
                    aig::Cnf::encode_with_xor3(&graph, &[output], &mut solver, true, true);
                assert_eq!(solver.num_vars(), 4);
                assert_eq!(cnf.emitted(), 8);
                assert!(cnf.mapped_lit(ab).is_none());
                cnf.assert(output ^ u32::from(wanted == 0), &mut solver);
                for (bit, &input) in inputs.iter().enumerate() {
                    cnf.assert(input ^ u32::from(assignment >> bit & 1 == 0), &mut solver);
                }
                match solver.solve(100) {
                    Answer::Sat(model) => {
                        assert_eq!(wanted, expected);
                        assert_eq!(cnf.value(output, &model), wanted == 1);
                    }
                    Answer::Unsat => {
                        assert_ne!(wanted, expected);
                        drup::check(&cnf.clauses, &solver.take_proof().unwrap()).unwrap();
                    }
                    Answer::Unknown => panic!("a fully assigned parity must be decided"),
                }
            }
        }
    }
}

#[test]
fn observed_intermediates_and_inner_products_remain_encoded() {
    for observe_product in [false, true] {
        let mut graph = Aig::new();
        let inputs: Vec<_> = (0..3).map(|_| graph.input()).collect();
        let ab = graph.xor(inputs[0], inputs[1]);
        let output = graph.xor(ab, inputs[2]);
        let product = graph.and(inputs[0], inputs[1] ^ 1);
        let observed = if observe_product { product } else { ab };
        for assignment in 0..8u32 {
            let mut solver = Solver::new();
            solver.log_proof();
            let mut cnf =
                aig::Cnf::encode_with_xor3(&graph, &[output, observed], &mut solver, true, true);
            assert!(cnf.mapped_lit(observed).is_some());
            if !observe_product {
                assert!(cnf.mapped_lit(ab).is_some());
            }
            let want_output = assignment.count_ones() & 1 == 1;
            let want_observed = if observe_product {
                assignment & 1 != 0 && assignment & 2 == 0
            } else {
                (assignment ^ (assignment >> 1)) & 1 != 0
            };
            for (i, &input) in inputs.iter().enumerate() {
                cnf.assert(input ^ u32::from(assignment >> i & 1 == 0), &mut solver);
            }
            cnf.assert(observed ^ u32::from(want_observed), &mut solver);
            cnf.assert(output ^ u32::from(!want_output), &mut solver);
            assert_eq!(solver.solve(100), Answer::Unsat);
            drup::check(&cnf.clauses, &solver.take_proof().unwrap()).unwrap();
        }
    }
}

#[test]
fn fixed_parity_operands_remain_available_for_root_aliases() {
    let mut graph = Aig::new();
    let inputs: Vec<_> = (0..4).map(|_| graph.input()).collect();
    let ab = graph.xor(inputs[0], inputs[1]);
    let output = graph.xor(ab, inputs[2]);
    let root = graph.and(output, inputs[3]);
    let mut solver = Solver::new();
    let cnf = aig::Cnf::encode_with_xor3(&graph, &[root], &mut solver, true, true);
    assert!(cnf.mapped_lit(ab).is_some());
    let aliases = graph.asserted_aliases(&[root]);
    assert!(!aliases.is_empty());
    for (a, b) in aliases {
        assert!(cnf.mapped_lit(a).is_some() && cnf.mapped_lit(b).is_some());
    }
}

#[test]
fn repeated_signed_parity_operands_preserve_cancellation_and_models() {
    for signs in 0..16u32 {
        let mut graph = Aig::new();
        let a = graph.input();
        let b = graph.input();
        let ab = graph.xor(a ^ (signs & 1), b ^ (signs >> 1 & 1));
        let output = graph.xor(ab, a ^ (signs >> 2 & 1)) ^ (signs >> 3 & 1);
        for assignment in 0..4u32 {
            let expected = (assignment >> 1 & 1) ^ (signs.count_ones() & 1);
            let mut solver = Solver::new();
            solver.log_proof();
            let mut cnf = aig::Cnf::encode_with_xor3(&graph, &[output], &mut solver, true, true);
            cnf.assert(a ^ u32::from(assignment & 1 == 0), &mut solver);
            cnf.assert(b ^ u32::from(assignment & 2 == 0), &mut solver);
            cnf.assert(output ^ u32::from(expected == 1), &mut solver);
            assert_eq!(solver.solve(100), Answer::Unsat);
            drup::check(&cnf.clauses, &solver.take_proof().unwrap()).unwrap();
        }
    }
}

#[test]
fn native_three_input_encoding_preserves_declared_models_and_exact_resumption() {
    for bits in [8u16, 65, 129] {
        let mut cx = Context::new();
        let w = Width::new(bits).unwrap();
        let a = cx.symbol("a", w).unwrap();
        let b = cx.symbol("b", w).unwrap();
        let c = cx.symbol("c", w).unwrap();
        let target = cx.symbol("target", w).unwrap();
        let mut high = vec![0u64; usize::from(bits).div_ceil(64)];
        high[usize::from(bits - 1) / 64] = 1u64 << ((bits - 1) % 64);
        cx.declare_known(
            a,
            crate::KnownBits::new(BitVec::zero(w), BitVec::wrapping_from_limbs(w, &high)).unwrap(),
        )
        .unwrap();
        let pair = cx.add(a, b).unwrap();
        let sum = cx.add(pair, c).unwrap();
        let claim = cx.ne(sum, target).unwrap();
        let cfg = Config::default()
            .with_samples(0)
            .with_simplify(false)
            .with_certificate(true);
        let baseline = Question::valid(&mut cx, claim, &cfg).unwrap();
        let cfg = cfg.with_xor3_encoding(true);
        let mut whole = Question::valid(&mut cx, claim, &cfg).unwrap();
        assert!(whole.stats().vars < baseline.stats().vars);
        let Outcome::Refuted(expected) = whole.solve(&mut cx, Limits::conflicts(1_000)).unwrap()
        else {
            panic!("the sum must retain an original-symbol counterexample");
        };
        assert_eq!(
            expected
                .iter()
                .find(|(key, _)| *key == SymbolKey::from("a"))
                .unwrap()
                .1
                .bit(bits - 1),
            Some(true)
        );
        assert!(cx.eval(&[claim], &expected[..]).unwrap()[0].is_zero());
        let mut stepped = Question::valid(&mut cx, claim, &cfg).unwrap();
        loop {
            let before = stepped.stats();
            match stepped
                .solve(
                    &mut cx,
                    Limits {
                        conflicts: 1_000,
                        propagations: 1,
                    },
                )
                .unwrap()
            {
                Outcome::Refuted(model) => {
                    assert_eq!(model, expected);
                    break;
                }
                Outcome::Unknown(_) => {}
                other => panic!("unexpected outcome: {other:?}"),
            }
            assert!(stepped.stats().propagations - before.propagations <= 1);
        }
        assert_eq!(stepped.stats(), whole.stats());
    }
}
