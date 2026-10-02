use super::*;

fn raw() -> Config {
    Config::default()
        .with_certificate(true)
        .with_samples(0)
        .with_simplify(false)
}

#[test]
fn exhaustive_boolean_cuts_prove_nonstructural_tautologies_with_one_node() {
    let mut cx = Context::new();
    let predicates = (0..8)
        .map(|i| cx.symbol(format!("p{i}"), Width::W1).unwrap())
        .collect::<Vec<_>>();
    let mut word = predicates[7];
    for &p in predicates[..7].iter().rev() {
        word = cx.concat(word, p).unwrap();
    }
    let three = cx.constant_u64(Width::W8, 3).unwrap();
    let inverse = cx.constant_u64(Width::W8, 171).unwrap();
    let product = cx.mul(word, three).unwrap();
    let restored = cx.mul(product, inverse).unwrap();
    let claim = cx.eq(word, restored).unwrap();
    // This arithmetic circuit is not a structurally constant AIG. Every Boolean
    // input assignment must be examined before replacing it by true.
    let mut probe = crate::prove::cuts::Probe::new(&mut cx, 256, 4096, 16_384);
    assert_ne!(probe.word(claim.index()).unwrap(), [aig::TRUE]);
    drop(probe);
    let mut question = Question::valid(&mut cx, claim, &raw().with_max_nodes(1)).unwrap();
    let Outcome::Proved(Some(cert)) = question
        .solve(
            &mut cx,
            Limits {
                conflicts: 0,
                propagations: 0,
            },
        )
        .unwrap()
    else {
        panic!("complete Boolean-cut enumeration must establish this tautology");
    };
    assert_eq!(question.stats().nodes, 1);
    cert.check().unwrap();
}

#[test]
fn boolean_cut_enumeration_never_proves_a_prefix_or_exceeds_its_input_cap() {
    let mut cx = Context::new();
    let predicates = (0..9)
        .map(|i| cx.symbol(format!("p{i}"), Width::W1).unwrap())
        .collect::<Vec<_>>();
    let mut all = cx.one(Width::W1).unwrap();
    for &p in &predicates[..8] {
        all = cx.and(all, p).unwrap();
    }
    let claim = cx.not(all).unwrap();
    let mut question = Question::valid(&mut cx, claim, &raw()).unwrap();
    let Outcome::Refuted(model) = question.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("the last Boolean assignment refutes the almost-tautology");
    };
    assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());

    let mut word = predicates[8];
    for &p in predicates[..8].iter().rev() {
        word = cx.concat(word, p).unwrap();
    }
    let width = Width::new(9).unwrap();
    let three = cx.constant_u64(width, 3).unwrap();
    let inverse = cx.constant_u64(width, 171).unwrap();
    let product = cx.mul(word, three).unwrap();
    let restored = cx.mul(product, inverse).unwrap();
    let claim = cx.eq(word, restored).unwrap();
    let mut question = Question::valid(&mut cx, claim, &raw().with_max_nodes(1)).unwrap();
    assert!(matches!(
        question.solve(&mut cx, Limits::conflicts(0)).unwrap(),
        Outcome::Unknown(Unknown::TooLarge { .. })
    ));
}

#[test]
fn shared_predicate_cuts_preserve_correlations_across_word_operations() {
    for bits in [8, 64, 129, 512] {
        let mut cx = Context::new();
        let w = Width::new(bits).unwrap();
        let x = cx.symbol("x", w).unwrap();
        let three = cx.constant_u64(w, 3).unwrap();
        let product = cx.mul(x, three).unwrap();
        let one = cx.one(w).unwrap();
        let p = cx.eq(product, one).unwrap();
        let a = cx.constant_u64(w, 0x15).unwrap();
        let b = cx.constant_u64(w, 0x72).unwrap();
        let target = cx.select(p, a, b).unwrap();
        let signed = cx.sext(p, w).unwrap();
        let zero = cx.zero(w).unwrap();
        let is_a = cx.eq(target, a).unwrap();
        let is_zero = cx.eq(signed, zero).unwrap();
        let both = cx.and(is_a, is_zero).unwrap();
        let exclusion = cx.not(both).unwrap();
        let mut question = Question::valid(&mut cx, exclusion, &raw().with_max_nodes(1)).unwrap();
        assert_eq!(question.stats().nodes, 1);
        let Outcome::Proved(Some(cert)) = question.solve(&mut cx, Limits::conflicts(0)).unwrap()
        else {
            panic!("the same predicate cannot select a and sign-extend to zero");
        };
        cert.check().unwrap();
    }
}

#[test]
fn distinct_predicates_and_false_abstract_assignments_require_real_models() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let y = cx.symbol("y", Width::W8).unwrap();
    let three = cx.constant_u64(Width::W8, 3).unwrap();
    let zero = cx.zero(Width::W8).unwrap();
    let mx = cx.mul(x, three).unwrap();
    let my = cx.mul(y, three).unwrap();
    let p = cx.eq(mx, zero).unwrap();
    let q = cx.eq(my, zero).unwrap();
    let np = cx.not(p).unwrap();
    let implication = cx.or(np, q).unwrap();
    let target = cx.select(p, zero, three).unwrap();
    let near_miss = cx.eq(target, zero).unwrap();
    for root in [implication, near_miss] {
        assert!(!super::super::cuts::constant_true(&mut cx, root.index()));
        let Outcome::Refuted(model) = valid(&mut cx, root, &raw()).unwrap() else {
            panic!("abstract false results must fall back to original symbols");
        };
        assert!(
            model
                .iter()
                .all(|(key, _)| *key == SymbolKey::from("x") || *key == SymbolKey::from("y"))
        );
        assert!(cx.eval(&[root], &model[..]).unwrap()[0].is_zero());
    }
}

#[test]
fn boolean_cut_budget_bounds_descent_through_deep_word_dags() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let mut word = x;
    for _ in 0..10_000 {
        word = cx.add(word, x).unwrap();
    }
    let zero = cx.zero(Width::W64).unwrap();
    let p = cx.eq(word, zero).unwrap();
    // Budget exhaustion is conservative, with no recursive walk through the full DAG.
    assert!(!super::super::cuts::constant_true(&mut cx, p.index()));
    let question = Question::valid(&mut cx, p, &raw().with_max_nodes(1)).unwrap();
    assert!(matches!(
        question.outcome(),
        Some(Outcome::Unknown(Unknown::TooLarge { .. }))
    ));
}

#[test]
fn masked_source_bits_prove_bounds_but_false_cuts_return_original_models() {
    for bits in [3, 8, 32, 64, 65, 129, 512] {
        let mut cx = Context::new();
        let width = Width::new(bits).unwrap();
        let x = cx.symbol("source", width).unwrap();
        let p = cx.symbol("enabled", Width::W1).unwrap();
        let mask = cx.zext(p, width).unwrap();
        let masked = cx.and(x, mask).unwrap();
        let coefficient = cx.constant_u64(width, 5).unwrap();
        let product = cx.mul(masked, coefficient).unwrap();
        let bound = cx.cmp(crate::CmpOp::Ule, product, coefficient).unwrap();
        let mut question = Question::valid(&mut cx, bound, &raw().with_max_nodes(1)).unwrap();
        let Outcome::Proved(Some(cert)) = question
            .solve(
                &mut cx,
                Limits {
                    conflicts: 0,
                    propagations: 0,
                },
            )
            .unwrap()
        else {
            panic!("a masked Boolean bit can only select zero or the coefficient");
        };
        assert_eq!(question.stats().nodes, 1);
        cert.check().unwrap();

        let zero = cx.zero(width).unwrap();
        let false_claim = cx.eq(product, zero).unwrap();
        assert!(!super::super::cuts::constant_true(
            &mut cx,
            false_claim.index()
        ));
        let Outcome::Refuted(model) = valid(&mut cx, false_claim, &raw()).unwrap() else {
            panic!("false abstract values require an original-symbol model");
        };
        assert!(model.iter().all(|(key, _)| {
            *key == SymbolKey::from("source") || *key == SymbolKey::from("enabled")
        }));
        assert!(cx.eval(&[false_claim], &model[..]).unwrap()[0].is_zero());
        assert_eq!(cx.eval(&[p], &model[..]).unwrap()[0].to_u64(), Some(1));
        assert_eq!(cx.eval(&[x], &model[..]).unwrap()[0].bit(0), Some(true));
    }
}
