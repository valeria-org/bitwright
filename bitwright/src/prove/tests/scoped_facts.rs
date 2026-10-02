use super::*;
use crate::{CmpOp, Facts, KnownBits, SRange, URange};

fn raw() -> Config {
    Config::default()
        .with_simplify(false)
        .with_samples(0)
        .with_certificate(true)
}

#[test]
fn masks_ranges_and_strides_are_exact_native_premises_with_original_models() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let facts = Facts::new(
        KnownBits::unknown(Width::W8),
        URange::strided(
            BitVec::from_u64(Width::W8, 13).unwrap(),
            BitVec::from_u64(Width::W8, 223).unwrap(),
            7,
        )
        .unwrap(),
        SRange::full(Width::W8),
    )
    .unwrap();
    let mut assumptions = Assumptions::new();
    assumptions.assume(&mut cx, x, facts).unwrap();
    let lo = cx.constant_u64(Width::W8, 13).unwrap();
    let delta = cx.sub(x, lo).unwrap();
    let seven = cx.constant_u64(Width::W8, 7).unwrap();
    let residue = cx.bin(BinOp::URem, delta, seven).unwrap();
    let zero = cx.zero(Width::W8).unwrap();
    let aligned = cx.eq(residue, zero).unwrap();
    let Outcome::Proved(Some(cert)) =
        valid_under(&mut cx, aligned, Some(&assumptions), &raw()).unwrap()
    else {
        panic!("the stride premise must remain exact");
    };
    cert.check().unwrap();

    let at_lo = cx.eq(x, lo).unwrap();
    let Outcome::Refuted(model) = valid_under(&mut cx, at_lo, Some(&assumptions), &raw()).unwrap()
    else {
        panic!("a strided interval is not a constant");
    };
    let value = cx.eval(&[x], &model[..]).unwrap()[0];
    assert!(facts.contains(&value));
    assert_ne!(value.to_u64(), Some(13));
    assert!(cx.eval(&[at_lo], &model[..]).unwrap()[0].is_zero());

    let bounded = cx.cmp(CmpOp::Ule, lo, x).unwrap();
    let Outcome::Refuted(model) = valid(&mut cx, bounded, &raw()).unwrap() else {
        panic!("withdrawing the scope must restore inputs below its lower bound");
    };
    assert!(cx.eval(&[bounded], &model[..]).unwrap()[0].is_zero());
    assert!(cx.declared_known(x).unwrap().is_none());
}

#[test]
fn wide_masks_and_signed_crossings_certify_without_becoming_global_declarations() {
    for bits in [8, 64, 65, 129, 512] {
        let width = Width::new(bits).unwrap();
        let mut cx = Context::new();
        let x = cx.symbol("x", width).unwrap();
        let mask = BitVec::wrapping_from_u64(width, 0x05);
        let ones = BitVec::wrapping_from_u64(width, 0x01);
        let known = KnownBits::new(BitVec::wrapping_from_u64(width, 0x04), ones).unwrap();
        let mut assumptions = Assumptions::new();
        assumptions
            .assume(&mut cx, x, Facts::from_known(known))
            .unwrap();
        let mask = cx.constant(&mask).unwrap();
        let ones = cx.constant(&ones).unwrap();
        let masked = cx.and(x, mask).unwrap();
        let claim = cx.eq(masked, ones).unwrap();
        let Outcome::Proved(Some(cert)) =
            valid_under(&mut cx, claim, Some(&assumptions), &raw()).unwrap()
        else {
            panic!("a partial mask is a valid scoped constraint at width {bits}");
        };
        cert.check().unwrap();
        let Outcome::Refuted(model) = valid(&mut cx, claim, &raw()).unwrap() else {
            panic!("an assumed mask is not a global declaration");
        };
        assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());

        let facts = Facts::new(
            KnownBits::unknown(width),
            URange::full(width),
            SRange::new(
                BitVec::wrapping_from_i128(width, -20),
                BitVec::wrapping_from_i128(width, 20),
            )
            .unwrap(),
        )
        .unwrap();
        let mut signed = Assumptions::new();
        signed.assume(&mut cx, x, facts).unwrap();
        let lo = cx
            .constant(&BitVec::wrapping_from_i128(width, -20))
            .unwrap();
        let hi = cx.constant(&BitVec::wrapping_from_i128(width, 20)).unwrap();
        let lower = cx.cmp(CmpOp::Sle, lo, x).unwrap();
        let upper = cx.cmp(CmpOp::Sle, x, hi).unwrap();
        let claim = cx.and(lower, upper).unwrap();
        let Outcome::Proved(Some(cert)) =
            valid_under(&mut cx, claim, Some(&signed), &raw()).unwrap()
        else {
            panic!("the signed interval must retain both sides of zero");
        };
        cert.check().unwrap();
        assert!(cx.declared_known(x).unwrap().is_none());
    }
}

#[test]
fn partial_constraints_on_expressions_and_contradictory_scopes_remain_exact() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let one = cx.one(Width::W8).unwrap();
    let shifted = cx.add(x, one).unwrap();
    let known = KnownBits::new(
        BitVec::from_u64(Width::W8, 1).unwrap(),
        BitVec::zero(Width::W8),
    )
    .unwrap();
    let mut assumptions = Assumptions::new();
    assumptions
        .assume(&mut cx, shifted, Facts::from_known(known))
        .unwrap();
    let low = cx.and(x, one).unwrap();
    let odd = cx.eq(low, one).unwrap();
    let Outcome::Proved(Some(cert)) =
        valid_under(&mut cx, odd, Some(&assumptions), &raw()).unwrap()
    else {
        panic!("an expression constraint must refer to that expression's value");
    };
    cert.check().unwrap();
    let mut contradiction = Assumptions::new();
    contradiction
        .assume(&mut cx, x, Facts::from_known(known))
        .unwrap();
    let opposite = KnownBits::new(
        BitVec::zero(Width::W8),
        BitVec::from_u64(Width::W8, 1).unwrap(),
    )
    .unwrap();
    contradiction
        .assume(&mut cx, x, Facts::from_known(opposite))
        .unwrap();
    let falsehood = cx.zero(Width::W1).unwrap();
    let Outcome::Proved(Some(cert)) =
        valid_under(&mut cx, falsehood, Some(&contradiction), &raw()).unwrap()
    else {
        panic!("contradictory original premises must be vacuous");
    };
    cert.check().unwrap();
}

#[test]
fn raw_scoped_word_masks_reduce_only_the_current_sampling_domain() {
    for spelling in [0, 1, 2] {
        let mut cx = Context::new();
        let source = cx.symbol("x", Width::W64).unwrap();
        let low = cx.extract(source, 0, Width::W32).unwrap();
        let high = cx.extract(source, 32, Width::W32).unwrap();
        let subject = if spelling == 0 {
            source
        } else {
            let joined = cx.concat(high, low).unwrap();
            if spelling == 1 {
                joined
            } else {
                cx.not(joined).unwrap()
            }
        };
        let known = KnownBits::new(
            BitVec::from_u64(Width::W64, u64::MAX ^ 3).unwrap(),
            BitVec::zero(Width::W64),
        )
        .unwrap();
        let facts = Facts::from_known(known);
        let mut assumptions = Assumptions::new();
        assumptions.assume(&mut cx, subject, facts).unwrap();
        let three = cx.constant_u64(Width::W64, 3).unwrap();
        let goal = cx.cmp(CmpOp::Ule, subject, three).unwrap();
        let cfg = Config::default()
            .with_simplify(false)
            .with_word_sampling(true)
            .with_sample_mode(SampleMode::Small)
            .with_samples(64)
            .with_max_nodes(0);
        let question = Question::valid_under(&mut cx, goal, Some(&assumptions), &cfg).unwrap();
        assert!(matches!(question.outcome(), Some(Outcome::Proved(None))));
        assert_eq!(question.stats().nodes, 0);
        assert!(question.stats().samples <= 64);
        let zero = cx.zero(Width::W64).unwrap();
        let false_goal = cx.eq(subject, zero).unwrap();
        let question =
            Question::valid_under(&mut cx, false_goal, Some(&assumptions), &cfg).unwrap();
        let Some(Outcome::Refuted(model)) = question.outcome() else {
            panic!("the bounded scope has nonzero values");
        };
        let value = cx.eval(&[subject], &model[..]).unwrap()[0];
        assert!(facts.contains(&value));
        assert!(!value.is_zero());
        let unrestricted = Question::valid(&mut cx, goal, &cfg).unwrap();
        assert!(!matches!(unrestricted.outcome(), Some(Outcome::Proved(_))));
        assert!(cx.declared_known(source).unwrap().is_none());
    }
}

#[test]
fn sampling_original_constraint_masks_preserves_overlapping_byte_sources() {
    let mut cx = Context::new();
    let bytes = (0..3)
        .map(|i| cx.symbol(format!("byte{i}"), Width::W8).unwrap())
        .collect::<Vec<_>>();
    let left = cx.concat(bytes[1], bytes[0]).unwrap();
    let right = cx.concat(bytes[2], bytes[1]).unwrap();
    let width = Width::W16;
    let unknown_low_two = Facts::from_known(
        KnownBits::new(
            BitVec::from_u64(width, 0xfffc).unwrap(),
            BitVec::zero(width),
        )
        .unwrap(),
    );
    let low_two_zero = Facts::from_known(
        KnownBits::new(
            BitVec::from_u64(width, 0xfcff).unwrap(),
            BitVec::zero(width),
        )
        .unwrap(),
    );
    let mut assumptions = Assumptions::new();
    assumptions.assume(&mut cx, left, unknown_low_two).unwrap();
    assumptions.assume(&mut cx, right, low_two_zero).unwrap();
    let key = cx.constant_u64(width, 0x303).unwrap();
    let combined = cx.or(left, right).unwrap();
    let goal = cx.cmp(CmpOp::Ule, combined, key).unwrap();
    let cfg = Config::default()
        .with_simplify(false)
        .with_word_sampling(true)
        .with_sample_mode(SampleMode::Small)
        .with_samples(64)
        .with_max_nodes(0);
    let q = Question::valid_under(&mut cx, goal, Some(&assumptions), &cfg).unwrap();
    assert!(matches!(q.outcome(), Some(Outcome::Proved(None))));
    assert_eq!(q.stats().nodes, 0);
    let zero = cx.zero(width).unwrap();
    let false_goal = cx.eq(combined, zero).unwrap();
    let q = Question::valid_under(&mut cx, false_goal, Some(&assumptions), &cfg).unwrap();
    let Some(Outcome::Refuted(model)) = q.outcome() else {
        panic!("overlapping words have a real nonzero model");
    };
    let values = cx.eval(&[left, right, false_goal], &model[..]).unwrap();
    assert!(unknown_low_two.contains(&values[0]));
    assert!(low_two_zero.contains(&values[1]));
    assert_eq!(
        (values[0].to_u64().unwrap() >> 8) & 255,
        values[1].to_u64().unwrap() & 255
    );
    assert!(values[2].is_zero());
}

#[test]
fn scoped_sampling_keeps_late_refutations_and_certificates_on_the_original_path() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let facts = Facts::from_known(
        KnownBits::new(
            BitVec::from_u64(Width::W64, u64::MAX ^ 255).unwrap(),
            BitVec::zero(Width::W64),
        )
        .unwrap(),
    );
    let mut assumptions = Assumptions::new();
    assumptions.assume(&mut cx, x, facts).unwrap();
    let max = cx.constant_u64(Width::W64, 255).unwrap();
    let almost = cx.cmp(CmpOp::Ult, x, max).unwrap();
    let cfg = Config::default()
        .with_simplify(false)
        .with_word_sampling(true)
        .with_sample_mode(SampleMode::Small)
        .with_samples(64)
        .with_max_nodes(0);
    let partial = Question::valid_under(&mut cx, almost, Some(&assumptions), &cfg).unwrap();
    assert!(matches!(partial.outcome(), Some(Outcome::Unknown(_))));
    let full =
        Question::valid_under(&mut cx, almost, Some(&assumptions), &cfg.with_samples(256)).unwrap();
    let Some(Outcome::Refuted(model)) = full.outcome() else {
        panic!("the last scoped input is a real refutation");
    };
    assert_eq!(cx.eval(&[x], &model[..]).unwrap()[0].to_u64(), Some(255));
    let bounded = cx.cmp(CmpOp::Ule, x, max).unwrap();
    let checked = Question::valid_under(
        &mut cx,
        bounded,
        Some(&assumptions),
        &cfg.with_samples(256).with_certificate(true),
    )
    .unwrap();
    assert!(matches!(checked.outcome(), Some(Outcome::Unknown(_))));
}

#[test]
fn scoped_sampling_reads_original_masks_after_global_declarations_are_withdrawn() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    cx.declare_known(x, KnownBits::constant(&BitVec::zero(Width::W64)))
        .unwrap();
    let facts = Facts::from_known(
        KnownBits::new(
            BitVec::from_u64(Width::W64, u64::MAX ^ 3).unwrap(),
            BitVec::zero(Width::W64),
        )
        .unwrap(),
    );
    let mut assumptions = Assumptions::new();
    assumptions.assume(&mut cx, x, facts).unwrap();
    cx.declare_known(x, KnownBits::unknown(Width::W64)).unwrap();
    let zero = cx.zero(Width::W64).unwrap();
    let goal = cx.eq(x, zero).unwrap();
    let cfg = Config::default()
        .with_simplify(false)
        .with_word_sampling(true)
        .with_sample_mode(SampleMode::Small)
        .with_samples(64)
        .with_max_nodes(0);
    let q = Question::valid_under(&mut cx, goal, Some(&assumptions), &cfg).unwrap();
    let Some(Outcome::Refuted(model)) = q.outcome() else {
        panic!("derived old declarations must not freeze the source");
    };
    let value = cx.eval(&[x], &model[..]).unwrap()[0];
    assert!(facts.contains(&value));
    assert!(!value.is_zero());
}

#[test]
fn simplification_does_not_reuse_propagated_bits_from_withdrawn_declarations() {
    for boolean_seed in [false, true] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W8).unwrap();
        cx.declare_known(
            x,
            KnownBits::new(
                BitVec::from_u64(Width::W8, 0x10).unwrap(),
                BitVec::zero(Width::W8),
            )
            .unwrap(),
        )
        .unwrap();
        let odd = Facts::from_known(
            KnownBits::new(
                BitVec::zero(Width::W8),
                BitVec::from_u64(Width::W8, 1).unwrap(),
            )
            .unwrap(),
        );
        let mut assumptions = Assumptions::new();
        if boolean_seed {
            let one = cx.one(Width::W8).unwrap();
            let low = cx.and(x, one).unwrap();
            let odd_predicate = cx.eq(low, one).unwrap();
            assumptions.assume_true(&mut cx, odd_predicate).unwrap();
        } else {
            assumptions.assume(&mut cx, x, odd).unwrap();
        }
        cx.declare_known(x, KnownBits::unknown(Width::W8)).unwrap();
        let high = cx.constant_u64(Width::W8, 0x10).unwrap();
        let masked = cx.and(x, high).unwrap();
        let zero = cx.zero(Width::W8).unwrap();
        let claim = cx.eq(masked, zero).unwrap();
        let cfg = Config::default()
            .with_word_sampling(true)
            .with_sample_mode(SampleMode::Small)
            .with_samples(256)
            .with_max_nodes(0);
        let q = Question::valid_under(&mut cx, claim, Some(&assumptions), &cfg).unwrap();
        let Some(Outcome::Refuted(model)) = q.outcome() else {
            panic!(
                "old globally zero bits must not become scoped theorems: {:?}",
                q.outcome()
            );
        };
        let value = cx.eval(&[x], &model[..]).unwrap()[0];
        assert!(odd.contains(&value));
        assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
        let current = cx.facts_under(x, &assumptions).unwrap().unwrap().0;
        assert!(current.contains(&BitVec::from_u64(Width::W8, 17).unwrap()));
    }
}
