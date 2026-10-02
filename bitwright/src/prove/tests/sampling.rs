use super::*;
use crate::KnownBits;

fn small(samples: u32) -> Config {
    Config::default()
        .with_simplify(false)
        .with_certificate(true)
        .with_samples(samples)
        .with_sample_mode(SampleMode::Small)
}

#[test]
fn word_streams_recover_independent_and_diagonal_symbol_witnesses() {
    for diagonal in [false, true] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let y = cx.symbol("y", Width::W64).unwrap();
        let one = cx.one(Width::W64).unwrap();
        let zero = cx.zero(Width::W64).unwrap();
        let a = cx.eq(x, if diagonal { one } else { zero }).unwrap();
        let b = cx.eq(y, one).unwrap();
        let both = cx.and(a, b).unwrap();
        let claim = cx.not(both).unwrap();
        let cfg = small(192)
            .with_sample_mode(SampleMode::Words)
            .with_max_nodes(0);
        let question = Question::valid(&mut cx, claim, &cfg).unwrap();
        let Some(Outcome::Refuted(model)) = question.outcome() else {
            panic!("the independent or diagonal word stream missed a small witness");
        };
        assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
        assert!(question.stats().samples <= 192);
        assert_eq!(question.stats().nodes, 0);
        assert!(cx.declared_known(x).unwrap().is_none());
        assert!(cx.declared_known(y).unwrap().is_none());
    }
}

#[test]
fn reconstructed_byte_order_precedes_an_equal_width_backing_symbol() {
    let mut cx = Context::new();
    let original = cx.symbol("backing", Width::W32).unwrap();
    let mut bytes = Vec::new();
    for offset in [0, 8, 16, 24] {
        bytes.push(cx.extract(original, offset, Width::W8).unwrap());
    }
    let mut word = bytes[0];
    for byte in bytes.into_iter().skip(1) {
        word = cx.concat(word, byte).unwrap();
    }
    let one = cx.one(Width::W32).unwrap();
    let claim = cx.ne(word, one).unwrap();
    let cfg = small(64)
        .with_sample_mode(SampleMode::Words)
        .with_max_nodes(0);
    let q = Question::valid(&mut cx, claim, &cfg).unwrap();
    let Some(Outcome::Refuted(model)) = q.outcome() else {
        panic!("a reconstructed word must retain its byte order when sharing a backing symbol");
    };
    assert_eq!(model.len(), 1);
    assert_eq!(model[0].1.to_u64(), Some(0x0100_0000));
    assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
    assert_eq!(q.stats().samples, 64);
    assert_eq!(q.stats().nodes, 0);
}

#[test]
fn word_streams_share_one_allowance_and_do_not_prove_exhausted_queries() {
    for samples in [0u32, 1, 64, 65, 192] {
        let mut cx = Context::new();
        let mut tests = Vec::new();
        for index in 0..16 {
            let symbol = cx.symbol(format!("word{index}"), Width::W64).unwrap();
            let value = cx.constant_u64(Width::W64, 1 << 40).unwrap();
            tests.push(cx.eq(symbol, value).unwrap());
        }
        let mut condition = tests[0];
        for test in tests.into_iter().skip(1) {
            condition = cx.and(condition, test).unwrap();
        }
        let claim = cx.not(condition).unwrap();
        let cfg = small(samples)
            .with_sample_mode(SampleMode::Words)
            .with_max_nodes(0);
        let q = Question::valid(&mut cx, claim, &cfg).unwrap();
        assert!(matches!(q.outcome(), Some(Outcome::Unknown(_))));
        assert_eq!(q.stats().samples, u64::from(samples.div_ceil(64)) * 64);
        assert_eq!(q.stats().nodes, 0);
    }
}

#[test]
fn diagonal_word_samples_respect_assumptions_before_native_certification() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let y = cx.symbol("y", Width::W64).unwrap();
    let one = cx.one(Width::W64).unwrap();
    let zero = cx.zero(Width::W64).unwrap();
    let a = cx.eq(x, one).unwrap();
    let b = cx.eq(y, one).unwrap();
    let both = cx.and(a, b).unwrap();
    let claim = cx.not(both).unwrap();
    let excluded = cx.eq(x, zero).unwrap();
    let mut assumptions = Assumptions::new();
    assumptions.assume_true(&mut cx, excluded).unwrap();
    let cfg = small(192).with_sample_mode(SampleMode::Words);
    let mut q = Question::valid_under(&mut cx, claim, Some(&assumptions), &cfg).unwrap();
    assert_eq!(q.stats().samples, 192);
    assert!(q.outcome().is_none());
    let Outcome::Proved(Some(cert)) = q.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("an excluded diagonal witness must leave the native proof intact");
    };
    cert.check().unwrap();
}

#[test]
fn small_integer_samples_find_wide_witnesses_without_sat_or_domain_narrowing() {
    for value in [0, 1, 63, 64, 65_535] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let constant = cx.constant_u64(Width::W64, value).unwrap();
        let p = cx.ne(x, constant).unwrap();
        let question = Question::valid(&mut cx, p, &small(65_536)).unwrap();
        let Some(Outcome::Refuted(model)) = question.outcome() else {
            panic!("no small witness")
        };
        assert_eq!(model[0].1.to_u64(), Some(value));
        assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());
        assert_eq!(question.stats().samples, (value / 64 + 1) * 64);
        assert_eq!(question.stats().vars, 0);
        assert_eq!(question.stats().conflicts, 0);
        assert!(cx.declared_known(x).unwrap().is_none());
    }
}

#[test]
fn samples_retain_declared_fixed_bits_and_combine_multiple_symbols() {
    let mut cx = Context::new();
    let w = Width::new(65).unwrap();
    let x = cx.symbol("x", w).unwrap();
    cx.declare_known(x, KnownBits::new(BitVec::one(w), BitVec::smin(w)).unwrap())
        .unwrap();
    let expected = BitVec::from_u128(w, (1 << 64) | 38).unwrap();
    let value = cx.constant(&expected).unwrap();
    let p = cx.ne(x, value).unwrap();
    let question = Question::valid(&mut cx, p, &small(64)).unwrap();
    let Some(Outcome::Refuted(model)) = question.outcome() else {
        panic!("fixed bits were lost")
    };
    assert_eq!(model[0].1, expected);
    assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());

    let mut cx = Context::new();
    let w = Width::new(2).unwrap();
    let x = cx.symbol("x", w).unwrap();
    let y = cx.symbol("y", w).unwrap();
    let two = cx.constant_u64(w, 2).unwrap();
    let one = cx.one(w).unwrap();
    let a = cx.eq(x, two).unwrap();
    let b = cx.eq(y, one).unwrap();
    let ab = cx.and(a, b).unwrap();
    let p = cx.not(ab).unwrap();
    let question = Question::valid(&mut cx, p, &small(64)).unwrap();
    let Some(Outcome::Refuted(model)) = question.outcome() else {
        panic!("no combined assignment")
    };
    assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());
}

#[test]
fn exhausting_small_samples_leaves_large_domain_queries_open_and_resumable() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let outside = cx.constant_u64(Width::W64, 1 << 32).unwrap();
    let p = cx.ne(x, outside).unwrap();
    let mut question = Question::valid(&mut cx, p, &small(64)).unwrap();
    assert!(question.outcome().is_none());
    assert_eq!(question.stats().samples, 64);
    assert!(matches!(
        question.solve(&mut cx, Limits::conflicts(0)).unwrap(),
        Outcome::Unknown(_)
    ));
    let Outcome::Refuted(model) = question.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("sample exhaustion must not prove a wide-domain exclusion");
    };
    assert_eq!(model[0].1.to_u64(), Some(1 << 32));
    assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());
}

#[test]
fn small_assignment_words_match_scalar_enumeration_at_batch_and_word_boundaries() {
    for batch in [0, 1, 255, 1024, (1 << 26) - 1, u32::MAX] {
        for bit in 0..512 {
            let word = super::super::small_sample(batch, bit);
            for lane in 0..64 {
                let assignment = u64::from(batch) * 64 + lane;
                let expected = bit < 64 && (assignment >> bit) & 1 != 0;
                assert_eq!(
                    (word >> lane) & 1 != 0,
                    expected,
                    "batch {batch}, input {bit}, lane {lane}"
                );
            }
        }
    }
}

#[test]
fn small_samples_respect_assumptions_and_keep_certificates_on_the_sat_path() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let nine = cx.constant_u64(Width::W8, 9).unwrap();
    let eight = cx.constant_u64(Width::W8, 8).unwrap();
    let p = cx.ne(x, nine).unwrap();
    let lower = cx.ult(x, eight).unwrap();
    let mut assumptions = Assumptions::new();
    assumptions.assume_true(&mut cx, lower).unwrap();
    let mut question = Question::valid_under(&mut cx, p, Some(&assumptions), &small(256)).unwrap();
    assert!(question.outcome().is_none());
    let Outcome::Proved(Some(cert)) = question.solve(&mut cx, Limits::conflicts(100)).unwrap()
    else {
        panic!("excluded sample must not refute the constrained query");
    };
    cert.check().unwrap();
}

#[test]
fn direct_word_samples_match_circuit_inputs_with_fixed_bits_and_multiple_symbols() {
    for mode in [SampleMode::Small, SampleMode::Random] {
        let mut cx = Context::new();
        let wx = Width::new(3).unwrap();
        let x = cx.symbol("x", wx).unwrap();
        let y = cx.symbol("y", Width::W8).unwrap();
        cx.declare_known(
            x,
            KnownBits::new(
                BitVec::from_u64(wx, 2).unwrap(),
                BitVec::from_u64(wx, 4).unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        cx.declare_known(
            y,
            KnownBits::new(
                BitVec::zero(Width::W8),
                BitVec::from_u64(Width::W8, 0x80).unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        let a = cx.constant_u64(wx, 5).unwrap();
        let b = cx.constant_u64(Width::W8, 0x93).unwrap();
        let a = cx.eq(x, a).unwrap();
        let b = cx.eq(y, b).unwrap();
        let both = cx.and(a, b).unwrap();
        let claim = cx.not(both).unwrap();
        let cfg = small(65_536).with_sample_mode(mode);
        let circuit = Question::valid(&mut cx, claim, &cfg).unwrap();
        let word = Question::valid(&mut cx, claim, &cfg.with_word_sampling(true)).unwrap();
        let (Some(Outcome::Refuted(expected)), Some(Outcome::Refuted(actual))) =
            (circuit.outcome(), word.outcome())
        else {
            panic!("both samplers must find the same constrained input");
        };
        assert_eq!(expected, actual);
        assert_eq!(circuit.stats().samples, word.stats().samples);
        assert_eq!(word.stats().nodes, 0);
        assert!(cx.eval(&[claim], &actual[..]).unwrap()[0].is_zero());
    }
}

#[test]
fn word_sample_exhaustion_retains_sat_certificates_and_full_domain_counterexamples() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let outside = cx.constant_u64(Width::W64, 1 << 32).unwrap();
    let p = cx.ne(x, outside).unwrap();
    let cfg = small(64).with_word_sampling(true);
    let mut question = Question::valid(&mut cx, p, &cfg).unwrap();
    assert!(question.outcome().is_none());
    assert_eq!(question.stats().samples, 64);
    assert!(matches!(
        question.solve(&mut cx, Limits::conflicts(0)).unwrap(),
        Outcome::Unknown(_)
    ));
    let Outcome::Refuted(model) = question.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("unsampled input must remain reachable");
    };
    assert_eq!(model[0].1.to_u64(), Some(1 << 32));

    let nine = cx.constant_u64(Width::W64, 9).unwrap();
    let eight = cx.constant_u64(Width::W64, 8).unwrap();
    let p = cx.ne(x, nine).unwrap();
    let lower = cx.ult(x, eight).unwrap();
    let mut assumptions = Assumptions::new();
    assumptions.assume_true(&mut cx, lower).unwrap();
    let mut q =
        Question::valid_under(&mut cx, p, Some(&assumptions), &cfg.with_samples(256)).unwrap();
    assert!(q.outcome().is_none());
    let Outcome::Proved(Some(cert)) = q.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("out-of-domain samples must not refute a constrained query");
    };
    cert.check().unwrap();
}

#[test]
fn early_word_models_restore_omitted_declared_symbols_and_wide_inputs_fall_back() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let w = Width::new(65).unwrap();
    let y = cx.symbol("y", w).unwrap();
    let one = BitVec::apply_bin(BinOp::Or, &BitVec::one(w), &BitVec::smin(w)).unwrap();
    cx.declare_known(y, KnownBits::new(BitVec::zero(w), one).unwrap())
        .unwrap();
    let bit = cx.extract(y, 0, Width::W1).unwrap();
    let yes = cx.one(Width::W1).unwrap();
    let is_odd = cx.eq(bit, yes).unwrap();
    let five = cx.constant_u64(Width::W8, 5).unwrap();
    let at_five = cx.eq(x, five).unwrap();
    let both = cx.and(is_odd, at_five).unwrap();
    let root = cx.not(both).unwrap();
    assert_eq!(cx.symbols_in(&[root]).unwrap().len(), 2);
    let cfg = small(64)
        .with_certificate(false)
        .with_simplify(true)
        .with_word_sampling(true)
        .with_max_nodes(0);
    let question = Question::valid(&mut cx, root, &cfg).unwrap();
    let Some(Outcome::Refuted(model)) = question.outcome() else {
        panic!("simplified word model should precede bit-blasting");
    };
    assert_eq!(
        model
            .iter()
            .find(|(key, _)| *key == SymbolKey::from("y"))
            .unwrap()
            .1,
        one
    );
    assert!(cx.eval(&[root], &model[..]).unwrap()[0].is_zero());
    assert_eq!(question.stats().nodes, 0);

    let zero = cx.zero(w).unwrap();
    let wide = cx.ne(y, zero).unwrap();
    let question = Question::valid(
        &mut cx,
        wide,
        &small(64).with_word_sampling(true).with_max_nodes(0),
    )
    .unwrap();
    assert!(matches!(
        question.outcome(),
        Some(Outcome::Unknown(Unknown::TooLarge { .. }))
    ));
    assert_eq!(question.stats().samples, 0);
}

#[test]
fn word_coordinates_preserve_repeated_symbols_and_wide_fallback() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let doubled = cx.concat(x, x).unwrap();
    let target = cx.constant_u64(Width::W16, 0x0102).unwrap();
    let claim = cx.ne(doubled, target).unwrap();
    let cfg = small(256)
        .with_word_sampling(false)
        .with_sample_mode(SampleMode::Words);
    let mut q = Question::valid(&mut cx, claim, &cfg).unwrap();
    assert!(q.outcome().is_none());
    assert_eq!(q.stats().samples, 256);
    let Outcome::Proved(Some(cert)) = q.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("one byte cannot take independent values in its two positions");
    };
    cert.check().unwrap();
    let wide = cx.symbol("wide", Width::new(65).unwrap()).unwrap();
    let value = cx.constant_u64(Width::new(65).unwrap(), 13).unwrap();
    let claim = cx.ne(wide, value).unwrap();
    let q = Question::valid(&mut cx, claim, &cfg).unwrap();
    let Some(Outcome::Refuted(model)) = q.outcome() else {
        panic!("unsupported words must retain circuit sampling");
    };
    assert_eq!(model[0].1.to_u64(), Some(13));
    assert!(q.stats().nodes > 0);
}
