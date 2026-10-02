use super::*;
use crate::prove::{Limits, Outcome, Question};
use crate::testutil::{Gen, Rng, ref_bin};
use bitwright_ref as reference;

fn ordered_config(mode: SampleMode, samples: u32) -> Config {
    Config::default()
        .with_simplify(false)
        .with_word_sampling(true)
        .with_sample_mode(mode)
        .with_samples(samples)
        .with_max_nodes(0)
}

fn division_recomposition(cx: &mut Context, x: crate::Expr, y: crate::Expr) -> crate::Expr {
    let quotient = cx.bin(BinOp::UDiv, x, y).unwrap();
    let product = cx.mul(quotient, y).unwrap();
    let remainder = cx.bin(BinOp::URem, x, y).unwrap();
    let sum = cx.add(product, remainder).unwrap();
    cx.eq(sum, x).unwrap()
}

#[test]
fn complete_ordered_word_domains_prove_without_a_circuit() {
    for mode in [SampleMode::Small, SampleMode::Words] {
        let mut cx = Context::new();
        let width = Width::new(4).unwrap();
        let x = cx.symbol("x", width).unwrap();
        let y = cx.symbol("y", width).unwrap();
        let p = division_recomposition(&mut cx, x, y);
        // Includes division by zero: the quotient times zero vanishes and the remainder
        // is the dividend. Every pair in the Cartesian product must be checked.
        let cfg = ordered_config(mode, 1024);
        let trial = try_sample(&mut cx, p.index(), &[], None, &cfg).unwrap();
        assert!(trial.complete);
        assert!(trial.model.is_none());
        assert!(trial.samples >= 256);
        let q = Question::valid(&mut cx, p, &cfg).unwrap();
        assert!(matches!(q.outcome(), Some(Outcome::Proved(None))));
        assert_eq!(q.stats().nodes, 0);
        assert_eq!(q.stats().samples, trial.samples);
        let control = cfg
            .with_word_sampling(false)
            .with_sample_mode(SampleMode::Small);
        let q = Question::valid(&mut cx, p, &control).unwrap();
        assert!(matches!(q.outcome(), Some(Outcome::Unknown(_))));
    }
}

#[test]
fn exhausting_individual_and_diagonal_streams_does_not_prove_the_joint_domain() {
    let mut cx = Context::new();
    let width = Width::new(4).unwrap();
    let x = cx.symbol("x", width).unwrap();
    let y = cx.symbol("y", width).unwrap();
    let fifteen = cx.constant_u64(width, 15).unwrap();
    let fourteen = cx.constant_u64(width, 14).unwrap();
    let px = cx.ne(x, fifteen).unwrap();
    let py = cx.ne(y, fourteen).unwrap();
    let p = cx.or(px, py).unwrap();
    let cfg = ordered_config(SampleMode::Words, 256);
    let trial = try_sample(&mut cx, p.index(), &[], None, &cfg).unwrap();
    assert!(!trial.complete);
    assert!(trial.model.is_none());
    let q = Question::valid(&mut cx, p, &cfg).unwrap();
    assert!(matches!(q.outcome(), Some(Outcome::Unknown(_))));
    let mut q = Question::valid(&mut cx, p, &cfg.with_samples(1024)).unwrap();
    let Outcome::Refuted(model) = q.solve(&mut cx, Limits::conflicts(0)).unwrap() else {
        panic!("the joint stream must reach (15, 14)");
    };
    assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());
    assert_eq!(q.stats().nodes, 0);
}

#[test]
fn partial_random_and_large_domains_do_not_become_word_proofs() {
    for (width, mode, samples) in [
        (8, SampleMode::Small, 192),
        (8, SampleMode::Words, 192),
        (8, SampleMode::Random, 256),
        (32, SampleMode::Small, 256),
        (32, SampleMode::Words, 256),
        (64, SampleMode::Words, 256),
        (8, SampleMode::Small, 0),
    ] {
        let mut cx = Context::new();
        let width = Width::new(width).unwrap();
        let x = cx.symbol("x", width).unwrap();
        let three = cx.constant_u64(width, 3).unwrap();
        let p = division_recomposition(&mut cx, x, three);
        let cfg = ordered_config(mode, samples);
        let trial = try_sample(&mut cx, p.index(), &[], None, &cfg).unwrap();
        assert!(!trial.complete, "width={width:?}, mode={mode:?}");
        assert_eq!(trial.samples, u64::from(samples));
        let q = Question::valid(&mut cx, p, &cfg).unwrap();
        assert!(matches!(q.outcome(), Some(Outcome::Unknown(_))));
    }
}

#[test]
fn declared_sparse_high_bits_are_enumerated_and_constraints_are_checked() {
    for mode in [SampleMode::Small, SampleMode::Words] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let unknown = 1 | (1 << 7) | (1 << 63);
        let ones = 0x1234_0000;
        cx.declare_known(
            x,
            crate::KnownBits::new(
                BitVec::from_u64(Width::W64, !(unknown | ones)).unwrap(),
                BitVec::from_u64(Width::W64, ones).unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
        let three = cx.constant_u64(Width::W64, 3).unwrap();
        let p = division_recomposition(&mut cx, x, three);
        let cfg = ordered_config(mode, 256);
        let q = Question::valid(&mut cx, p, &cfg).unwrap();
        assert!(matches!(q.outcome(), Some(Outcome::Proved(None))));
        assert_eq!(q.stats().samples, 64);
        // The predicate fails exactly at the highest legal assignment. A constraint
        // excluding that point must be evaluated, and cannot silently discard others.
        let largest = cx.constant_u64(Width::W64, unknown | ones).unwrap();
        let p = cx.ne(x, largest).unwrap();
        let mut assumptions = crate::Assumptions::new();
        assumptions.assume_true(&mut cx, p).unwrap();
        let q = Question::valid_under(&mut cx, p, Some(&assumptions), &cfg).unwrap();
        assert!(matches!(q.outcome(), Some(Outcome::Proved(None))));
        let q = Question::valid(&mut cx, p, &cfg).unwrap();
        let Some(Outcome::Refuted(model)) = q.outcome() else {
            panic!("all three unknown bits must be varied, including bit 63");
        };
        assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());
    }
}

#[test]
fn complete_word_enumeration_does_not_replace_a_requested_certificate() {
    let mut cx = Context::new();
    let width = Width::new(2).unwrap();
    let x = cx.symbol("x", width).unwrap();
    let three = cx.constant_u64(width, 3).unwrap();
    let p = division_recomposition(&mut cx, x, three);
    let cfg = ordered_config(SampleMode::Small, 64).with_certificate(true);
    let q = Question::valid(&mut cx, p, &cfg).unwrap();
    assert!(matches!(q.outcome(), Some(Outcome::Unknown(_))));
    let mut q = Question::valid(&mut cx, p, &cfg.with_max_nodes(100_000)).unwrap();
    let Outcome::Proved(Some(cert)) = q.solve(&mut cx, Limits::conflicts(10_000)).unwrap() else {
        panic!("certificate path must use the original circuit");
    };
    cert.check().unwrap();
}

#[test]
fn complete_decisions_match_independent_generated_truth_tables() {
    let mut decisions = [0usize; 2];
    for seed in 0..128 {
        let mut cx = Context::new();
        let mut generator = Gen {
            rng: Rng(0x434f_5645_5241_4745 + seed),
            max_w: 3,
            vars: Vec::new(),
        };
        let (p, reference) = generator.expr(&mut cx, 1, 4);
        let input_bits: u16 = generator.vars.iter().map(|(_, width)| width).sum();
        if input_bits > 12 {
            continue;
        }
        let mut valid = true;
        for assignment in 0..1u64 << input_bits {
            let mut offset = 0;
            let env: Vec<_> = generator
                .vars
                .iter()
                .map(|(_, width)| {
                    let value = (assignment >> offset) & mask(*width);
                    offset += width;
                    reference::Bits::from_u128(*width, u128::from(value))
                })
                .collect();
            valid &= reference.eval(&env).unwrap().bit(0);
        }
        decisions[usize::from(valid)] += 1;
        for mode in [SampleMode::Small, SampleMode::Words] {
            let cfg = ordered_config(mode, (1 << input_bits) * 10);
            let q = Question::valid(&mut cx, p, &cfg).unwrap();
            match q.outcome().unwrap() {
                Outcome::Proved(None) => assert!(valid, "{}", cx.display(p)),
                Outcome::Refuted(model) => {
                    assert!(!valid, "{}", cx.display(p));
                    let env: Vec<_> = generator
                        .vars
                        .iter()
                        .map(|(name, width)| {
                            let value = model
                                .iter()
                                .find(|(key, _)| key == &SymbolKey::from(name.as_str()))
                                .map_or(0, |(_, value)| value.to_u64().unwrap());
                            reference::Bits::from_u128(*width, u128::from(value))
                        })
                        .collect();
                    assert!(!reference.eval(&env).unwrap().bit(0));
                }
                other => panic!("complete small domain left undecided: {other:?}"),
            }
            assert_eq!(q.stats().nodes, 0);
        }
    }
    assert!(decisions[0] >= 10 && decisions[1] >= 10, "{decisions:?}");
}

#[test]
fn scalar_integer_ops_match_independent_small_exhaustive_and_wide_boundaries() {
    for w in [1u16, 2, 3, 4, 5, 8, 16, 31, 32, 63, 64] {
        let values: Vec<u64> = if w <= 5 {
            (0..1u64 << w).collect()
        } else {
            vec![
                0,
                1,
                mask(w),
                1 << (w - 1),
                mask(w) >> 1,
                0xaaaa_aaaa_aaaa_aaaa & mask(w),
                0x5555_5555_5555_5555 & mask(w),
            ]
        };
        for &a in &values {
            for &b in &values {
                for op in BinOp::ALL {
                    let want = reference::bin(
                        ref_bin(op),
                        &reference::Bits::from_u128(w, u128::from(a)),
                        &reference::Bits::from_u128(w, u128::from(b)),
                    );
                    let got = binary(op, a, b, w) & mask(w);
                    for bit in 0..w {
                        assert_eq!(
                            got >> bit & 1 != 0,
                            want.bit(bit),
                            "w={w}, op={op:?}, a={a:#x}, b={b:#x}, bit={bit}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn compiled_shared_integer_programs_match_generic_evaluation() {
    let mut generator = Gen {
        rng: Rng(0x574f5244),
        max_w: 64,
        vars: Vec::new(),
    };
    for round in 0..256 {
        let mut cx = Context::new();
        let width = [1, 3, 8, 16, 31, 32, 63, 64][round % 8];
        let (root, _) = generator.expr(&mut cx, width, 4);
        let mut program = Program::compile(&mut cx, root.index(), &[], None).unwrap();
        if round % 2 == 0 {
            program.prioritize_words();
        }
        let inputs: Vec<_> = (0..program.inputs).map(|_| generator.rng.next()).collect();
        let mut values = vec![0; program.ops.len()];
        for lane in 0..64 {
            program.evaluate(&inputs, lane, &mut values);
            let env: Vec<_> = program
                .symbols
                .iter()
                .map(|s| {
                    (
                        s.key.clone(),
                        BitVec::from_u64(s.width, Program::symbol_value(s, &inputs, lane)).unwrap(),
                    )
                })
                .collect();
            assert_eq!(
                values[program.goal],
                cx.eval(&[root], &env[..]).unwrap()[0].to_u64().unwrap(),
                "{}",
                cx.display(root)
            );
        }
    }
}

#[test]
fn compiler_bounds_deep_dags_and_skips_wide_and_float_operations() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let mut chain = x;
    for _ in 0..10_000 {
        chain = cx.add(chain, x).unwrap();
    }
    assert!(Program::compile(&mut cx, chain.index(), &[], None).is_none());
    let wide = cx.symbol("wide", Width::new(65).unwrap()).unwrap();
    let low = cx.extract(wide, 0, Width::W64).unwrap();
    assert!(Program::compile(&mut cx, low.index(), &[], None).is_none());
    let format = crate::fp::FpFormat::F32;
    let a = cx.symbol("a", Width::W32).unwrap();
    let b = cx.symbol("b", Width::W32).unwrap();
    let eq = cx.fp_cmp(format, crate::fp::FpCmpOp::Eq, a, b).unwrap();
    assert!(Program::compile(&mut cx, eq.index(), &[], None).is_none());
}

#[test]
fn word_coordinate_order_preserves_overlapping_inputs_and_fixed_bits() {
    let mut cx = Context::new();
    let width = Width::new(2).unwrap();
    let a = cx.symbol("a", width).unwrap();
    let b = cx.symbol("b", width).unwrap();
    let c = cx.symbol("c", width).unwrap();
    cx.declare_known(
        b,
        crate::KnownBits::new(BitVec::zero(width), BitVec::from_u64(width, 2).unwrap()).unwrap(),
    )
    .unwrap();
    let low = cx.concat(b, a).unwrap();
    let high = cx.concat(c, b).unwrap();
    let root = cx.concat(high, low).unwrap();
    let natural = Program::compile(&mut cx, root.index(), &[], None).unwrap();
    let mut words = Program::compile(&mut cx, root.index(), &[], None).unwrap();
    words.prioritize_words();
    assert_eq!(natural.inputs, 5);
    assert_eq!(words.inputs, natural.inputs);
    let mut sets = Vec::new();
    for program in [&natural, &words] {
        let inputs: Vec<_> = (0..program.inputs).map(|k| small_sample(0, k)).collect();
        let mut set = std::collections::BTreeSet::new();
        let mut values = vec![0; program.ops.len()];
        for lane in 0..64 {
            let model: Vec<_> = program
                .symbols
                .iter()
                .map(|s| {
                    (
                        s.key.clone(),
                        BitVec::from_u64(s.width, Program::symbol_value(s, &inputs, lane)).unwrap(),
                    )
                })
                .collect();
            program.evaluate(&inputs, lane, &mut values);
            assert_eq!(
                values[program.goal],
                cx.eval(&[root], &model[..]).unwrap()[0].to_u64().unwrap()
            );
            assert_eq!(
                model
                    .iter()
                    .find(|(key, _)| *key == SymbolKey::from("b"))
                    .unwrap()
                    .1
                    .bit(1),
                Some(true)
            );
            set.insert(
                model
                    .iter()
                    .map(|(_, value)| value.to_u64().unwrap())
                    .collect::<Vec<_>>(),
            );
        }
        assert_eq!(set.len(), 32);
        sets.push(set);
    }
    assert_eq!(sets[0], sets[1]);
}

#[test]
fn independent_streams_are_bounded_and_keep_shared_inputs_single_valued() {
    let mut cx = Context::new();
    let a = cx.symbol("a", Width::W8).unwrap();
    let b = cx.symbol("b", Width::W8).unwrap();
    let c = cx.symbol("c", Width::W8).unwrap();
    let first = cx.concat(b, a).unwrap();
    let second = cx.concat(c, b).unwrap();
    let sum = cx.add(first, second).unwrap();
    let mut p = Program::compile(&mut cx, sum.index(), &[], None).unwrap();
    p.prioritize_words();
    assert_eq!(p.word_groups.len(), 2);
    let streams = p.streams();
    assert!(streams.len() <= 10);
    let mut values = vec![0; p.ops.len()];
    for mapping in streams {
        let inputs: Vec<_> = mapping
            .iter()
            .map(|bit| bit.map_or(0, |k| small_sample(0, k)))
            .collect();
        for lane in 0..64 {
            p.evaluate(&inputs, lane, &mut values);
            let model: Vec<_> = p
                .symbols
                .iter()
                .map(|s| {
                    (
                        s.key.clone(),
                        BitVec::from_u64(s.width, Program::symbol_value(s, &inputs, lane)).unwrap(),
                    )
                })
                .collect();
            assert_eq!(
                values[p.goal],
                cx.eval(&[sum], &model[..]).unwrap()[0].to_u64().unwrap()
            );
        }
    }
}
