use super::*;
use crate::prove::{Config, Outcome, Question};
use crate::{BinOp, KnownBits, SymbolKey, Width};

fn domain(cx: &mut Context, outputs: &[Expr], premises: &[Expr]) -> TupleDomain {
    let Analysis::Superset(domain) = analyze(cx, outputs, premises, Limits::default()).unwrap()
    else {
        panic!("expected a bounded joint domain");
    };
    domain
}

fn certify(cx: &mut Context, domain: &TupleDomain) {
    let claim = domain.coverage(cx).unwrap();
    let cfg = Config::default()
        .with_samples(0)
        .with_simplify(false)
        .with_certificate(true);
    let mut question = Question::valid(cx, claim, &cfg).unwrap();
    let Outcome::Proved(Some(cert)) = question
        .solve(cx, crate::prove::Limits::conflicts(1000))
        .unwrap()
    else {
        panic!("joint coverage must hold over the original expressions");
    };
    cert.check().unwrap();
}

#[test]
fn same_target_keeps_distinct_keys_and_shared_predicate_casts() {
    let mut cx = Context::new();
    let p = cx.symbol("p", Width::W1).unwrap();
    let q = cx.symbol("q", Width::W1).unwrap();
    let target = cx.constant_u64(Width::W64, 123).unwrap();
    let low = cx.zext(p, Width::W32).unwrap();
    let wide = cx.zext(p, Width::W64).unwrap();
    let widened = cx.zext(low, Width::W64).unwrap();
    let np = cx.not(p).unwrap();
    let tail = cx.zext(np, Width::W64).unwrap();
    let independent = cx.zext(q, Width::W64).unwrap();
    let outputs = [target, wide, widened, tail, independent];
    let result = domain(&mut cx, &outputs, &[]);
    assert_eq!(result.outputs(), outputs);
    assert_eq!(result.stats().inputs, 2);
    assert_eq!(result.stats().assignments, 4);
    assert_eq!(result.tuples().len(), 4);
    for tuple in result.tuples() {
        assert_eq!(tuple[0].to_u64(), Some(123));
        assert_eq!(tuple[1], tuple[2]);
        assert_eq!(tuple[1].to_u64().unwrap() ^ tuple[3].to_u64().unwrap(), 1);
    }
    certify(&mut cx, &result);
}

#[test]
fn scoped_premises_filter_shared_roots_without_becoming_global_facts() {
    let mut cx = Context::new();
    let p = cx.symbol("p", Width::W1).unwrap();
    let q = cx.symbol("q", Width::W1).unwrap();
    let wide = cx.zext(p, Width::W64).unwrap();
    let same = cx.eq(p, q).unwrap();
    let scoped = domain(&mut cx, &[wide, q], &[same, p]);
    assert_eq!(scoped.premises(), [same, p]);
    assert_eq!(scoped.tuples().len(), 1);
    assert!(scoped.tuples()[0].iter().all(|v| v.to_u64() == Some(1)));
    certify(&mut cx, &scoped);
    let unrestricted = domain(&mut cx, &[wide, q], &[]);
    assert_eq!(unrestricted.tuples().len(), 4);
    assert!(cx.declared_known(p).unwrap().is_none());

    let np = cx.not(p).unwrap();
    let infeasible = domain(&mut cx, &[wide], &[p, np]);
    assert!(infeasible.tuples().is_empty());
    certify(&mut cx, &infeasible);
    let zero_cap = Limits {
        tuples: 0,
        ..Limits::default()
    };
    assert!(matches!(
        analyze(&mut cx, &[wide], &[p, np], zero_cap).unwrap(),
        Analysis::Superset(d) if d.tuples().is_empty()
    ));
}

#[test]
fn impossible_opaque_branch_is_retained_without_claiming_reachability() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let one = cx.one(Width::W64).unwrap();
    let next = cx.add(x, one).unwrap();
    let impossible = cx.eq(x, next).unwrap();
    let output = cx.zext(impossible, Width::W64).unwrap();
    let result = domain(&mut cx, &[output], &[]);
    assert_eq!(result.stats().inputs, 1);
    assert_eq!(result.tuples().len(), 2);
    assert!(result.tuples().iter().any(|t| t[0].to_u64() == Some(1)));
    for value in [0, 1, 1 << 63, u64::MAX] {
        let model = [(
            SymbolKey::from("x"),
            BitVec::from_u64(Width::W64, value).unwrap(),
        )];
        assert!(cx.eval(&[output], &model[..]).unwrap()[0].is_zero());
    }
    certify(&mut cx, &result);
}

#[test]
fn abandoned_boolean_inputs_do_not_inflate_live_support() {
    let mut cx = Context::new();
    let p = cx.symbol("p", Width::W1).unwrap();
    let x = cx.symbol("x", Width::W64).unwrap();
    let one = cx.one(Width::W64).unwrap();
    // The probe visits p before discovering that the wide x arm is unavailable.
    let partial = cx.select(p, one, x).unwrap();
    let guard = cx.cmp(crate::CmpOp::Ult, partial, one).unwrap();
    let limits = Limits {
        inputs: 1,
        ..Limits::default()
    };
    let Analysis::Superset(result) = analyze(&mut cx, &[guard], &[], limits).unwrap() else {
        panic!("only the opaque comparison is live");
    };
    assert_eq!(result.stats().inputs, 1);
    assert!(result.stats().nodes > 2);
    assert_eq!(result.tuples().len(), 2);
    certify(&mut cx, &result);
}

#[test]
fn multi_batch_enumeration_matches_every_original_boolean_assignment() {
    let mut cx = Context::new();
    let outputs = (0..8)
        .map(|i| cx.symbol(format!("p{i}"), Width::W1).unwrap())
        .collect::<Vec<_>>();
    let result = domain(&mut cx, &outputs, &[]);
    assert_eq!(result.stats().assignments, 256);
    assert_eq!(result.tuples().len(), 256);
    for (assignment, tuple) in result.tuples().iter().enumerate() {
        for (i, bit) in tuple.iter().enumerate() {
            assert_eq!(bit.to_u64(), Some((assignment >> i & 1) as u64));
        }
        let model = tuple
            .iter()
            .enumerate()
            .map(|(i, &v)| (SymbolKey::from(format!("p{i}")), v))
            .collect::<Vec<_>>();
        assert_eq!(cx.eval(&outputs, &model[..]).unwrap(), *tuple);
    }
    // A duplicated field must preserve its value through every batch.
    let mut repeated = outputs.clone();
    repeated.push(outputs[7]);
    let result = domain(&mut cx, &repeated, &[]);
    assert_eq!(result.tuples().len(), 256);
    assert!(result.tuples().iter().all(|t| t[7] == t[8]));
}

#[test]
fn wide_wrapping_outputs_and_signed_extensions_replay_at_limb_boundaries() {
    for bits in [8, 32, 64, 65, 129, 512] {
        let mut cx = Context::new();
        let width = Width::new(bits).unwrap();
        let p = cx.symbol("p", Width::W1).unwrap();
        let value = cx.zext(p, width).unwrap();
        let minus_one = cx.constant(&BitVec::ones(width)).unwrap();
        let wrapped = cx.add(value, minus_one).unwrap();
        let signed = cx.sext(p, width).unwrap();
        let outputs = [wrapped, signed, value];
        let result = domain(&mut cx, &outputs, &[]);
        assert_eq!(result.tuples().len(), 2);
        for p in [false, true] {
            let model = [(SymbolKey::from("p"), BitVec::from_bool(p))];
            assert!(
                result
                    .tuples()
                    .contains(&cx.eval(&outputs, &model[..]).unwrap())
            );
        }
        certify(&mut cx, &result);
    }
}

#[test]
fn declared_constant_words_are_supported_and_not_widened() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let value = BitVec::from_u64(Width::W64, u64::MAX).unwrap();
    cx.declare_known(x, KnownBits::constant(&value)).unwrap();
    let result = domain(&mut cx, &[x], &[]);
    assert_eq!(result.stats().inputs, 0);
    assert_eq!(result.tuples(), [vec![value]]);
    certify(&mut cx, &result);
}

#[test]
fn all_limits_leave_explicit_unknown_instead_of_a_truncated_domain() {
    let mut cx = Context::new();
    let p = cx.symbol("p", Width::W1).unwrap();
    let x = cx.symbol("x", Width::W64).unwrap();
    let constant = cx.one(Width::W64).unwrap();
    let cases = [
        (
            p,
            Limits {
                nodes: 1,
                ..Limits::default()
            },
            Stop::Nodes(2),
        ),
        (
            p,
            Limits {
                inputs: 0,
                ..Limits::default()
            },
            Stop::Inputs(1),
        ),
        (
            p,
            Limits {
                tuples: 1,
                ..Limits::default()
            },
            Stop::Tuples,
        ),
        (
            p,
            Limits {
                enumeration_work: 19,
                ..Limits::default()
            },
            Stop::EnumerationWork,
        ),
        (
            constant,
            Limits {
                output_bits: 63,
                ..Limits::default()
            },
            Stop::OutputBits,
        ),
        (
            constant,
            Limits {
                visits: 0,
                ..Limits::default()
            },
            Stop::UnavailableOutput(0),
        ),
        (
            constant,
            Limits {
                construction_work: 0,
                ..Limits::default()
            },
            Stop::UnavailableOutput(0),
        ),
        (x, Limits::default(), Stop::UnavailableOutput(0)),
    ];
    for (root, limits, expected) in cases {
        assert!(matches!(
            analyze(&mut cx, &[root], &[], limits).unwrap(),
            Analysis::Unknown(why) if why == expected
        ));
    }
    assert!(matches!(
        analyze(
            &mut cx,
            &[p],
            &[],
            Limits {
                enumeration_work: 20,
                ..Limits::default()
            }
        )
        .unwrap(),
        Analysis::Superset(_)
    ));
    assert!(matches!(
        analyze(&mut cx, &[p, x], &[], Limits::default()).unwrap(),
        Analysis::Unknown(Stop::UnavailableOutput(1))
    ));
    assert!(matches!(
        analyze(&mut cx, &[p; 65], &[], Limits::default()).unwrap(),
        Analysis::Unknown(Stop::TooManyRoots)
    ));
    assert!(matches!(
        analyze(&mut cx, &[p], &[p; 65], Limits::default()).unwrap(),
        Analysis::Unknown(Stop::TooManyRoots)
    ));
    assert!(matches!(
        analyze(
            &mut cx,
            &[],
            &[],
            Limits {
                nodes: 0,
                ..Limits::default()
            }
        )
        .unwrap(),
        Analysis::Unknown(Stop::Nodes(1))
    ));
}

#[test]
fn root_handles_and_premise_widths_are_checked() {
    let mut cx = Context::new();
    let p = cx.symbol("p", Width::W1).unwrap();
    let word = cx.one(Width::W8).unwrap();
    assert!(matches!(
        analyze(&mut cx, &[p], &[word], Limits::default()),
        Err(Error::Width(WidthError::ConditionWidth { bits: 8 }))
    ));
    let result = domain(&mut cx, &[p], &[]);
    let mut other = Context::new();
    assert!(matches!(
        result.coverage(&mut other),
        Err(Error::ForeignExpr)
    ));
    assert!(matches!(
        analyze(&mut other, &[p], &[], Limits::default()),
        Err(Error::ForeignExpr)
    ));
    cx.clear();
    assert!(matches!(result.coverage(&mut cx), Err(Error::StaleExpr)));
}

#[test]
fn empty_outputs_preserve_the_empty_tuple_and_infeasible_premises() {
    let mut cx = Context::new();
    let result = domain(&mut cx, &[], &[]);
    assert_eq!(result.tuples(), [Vec::<BitVec>::new()]);
    certify(&mut cx, &result);
    let false_premise = cx.zero(Width::W1).unwrap();
    let result = domain(&mut cx, &[], &[false_premise]);
    assert!(result.tuples().is_empty());
    certify(&mut cx, &result);
}

#[test]
fn requested_large_visit_allowance_does_not_unbound_recursion() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let mut deep = x;
    for i in 0..600 {
        let k = cx.constant_u64(Width::W64, 3 + i).unwrap();
        deep = cx.bin(BinOp::Mul, deep, k).unwrap();
        deep = cx.xor(deep, k).unwrap();
    }
    let zero = cx.zero(Width::W64).unwrap();
    let guard = cx.eq(deep, zero).unwrap();
    let output = cx.zext(guard, Width::W64).unwrap();
    let Analysis::Superset(result) = analyze(
        &mut cx,
        &[output],
        &[],
        Limits {
            visits: usize::MAX,
            construction_work: usize::MAX,
            ..Limits::default()
        },
    )
    .unwrap() else {
        panic!("the bounded Boolean cut should avoid descending through the deep word");
    };
    assert_eq!(result.stats().inputs, 1);
    assert_eq!(result.tuples().len(), 2);
    assert!(result.stats().nodes <= 2);
}

#[test]
fn arithmetic_and_shift_domains_match_the_independent_reference_exhaustively() {
    use bitwright_ref as reference;
    for op in [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
    ] {
        let mut cx = Context::new();
        let predicates = (0..4)
            .map(|i| cx.symbol(format!("p{i}"), Width::W1).unwrap())
            .collect::<Vec<_>>();
        let mut packed = predicates[3];
        for &p in predicates[..3].iter().rev() {
            packed = cx.concat(packed, p).unwrap();
        }
        let count = cx.zext(packed, Width::W8).unwrap();
        let base = cx.constant_u64(Width::W8, 0x83).unwrap();
        let output = cx.bin(op, base, count).unwrap();
        let result = domain(&mut cx, &[count, output], &[]);
        assert_eq!(result.stats().inputs, 4);
        assert_eq!(result.tuples().len(), 16);
        for count in 0..16u128 {
            let lhs = reference::Bits::from_u128(8, 0x83);
            let rhs = reference::Bits::from_u128(8, count);
            let want = reference::bin(crate::testutil::ref_bin(op), &lhs, &rhs);
            let tuple = [
                BitVec::from_u128(Width::W8, count).unwrap(),
                BitVec::from_limbs(Width::W8, &want.to_limbs()).unwrap(),
            ];
            assert!(
                result.tuples().iter().any(|actual| actual == &tuple),
                "{op:?}, {count}"
            );
        }
        certify(&mut cx, &result);
    }
}

#[test]
fn masked_source_domains_match_the_reference_exhaustively() {
    use bitwright_ref as reference;
    for bits in 2..=8 {
        let width = Width::new(bits).unwrap();
        let all = (1u64 << bits) - 1;
        for mask in [0, 1, 2, 3, 1 << (bits - 1), all ^ 1] {
            // An all-ones AND canonicalizes to the unrestricted wide source itself.
            if mask == all {
                continue;
            }
            let mut cx = Context::new();
            let x = cx.symbol("source", width).unwrap();
            let k = cx.constant_u64(width, mask).unwrap();
            let output = cx.and(x, k).unwrap();
            let result = domain(&mut cx, &[output], &[]);
            let expected = (0..=all)
                .map(|value| {
                    let value = reference::Bits::from_u128(bits, u128::from(value));
                    let mask = reference::Bits::from_u128(bits, u128::from(mask));
                    let value = reference::bin(reference::BinOp::And, &value, &mask);
                    BitVec::from_limbs(width, &value.to_limbs()).unwrap()
                })
                .collect::<std::collections::HashSet<_>>();
            assert_eq!(result.tuples().len(), expected.len());
            assert!(
                result
                    .tuples()
                    .iter()
                    .all(|tuple| expected.contains(&tuple[0]))
            );
        }
    }
}

#[test]
fn sparse_wide_masks_keep_only_selected_source_bits() {
    use bitwright_ref as reference;
    for bits in [9, 32, 64, 65, 127, 128, 129, 256, 511, 512] {
        let mut cx = Context::new();
        let width = Width::new(bits).unwrap();
        let x = cx.symbol("source", width).unwrap();
        let positions = [0, 1, bits / 2, bits - 1];
        let mut limbs = [0u64; 8];
        for bit in positions {
            limbs[usize::from(bit / 64)] |= 1u64 << (bit % 64);
        }
        let mask = BitVec::from_limbs(width, &limbs).unwrap();
        let k = cx.constant(&mask).unwrap();
        let output = cx.and(x, k).unwrap();
        let result = domain(&mut cx, &[output], &[]);
        assert_eq!(result.stats().inputs, 4);
        assert_eq!(result.tuples().len(), 16);
        for assignment in 0..16 {
            // Set every discarded source bit, including bits in the high limbs.
            let mut input = [u64::MAX; 8];
            for (i, bit) in positions.into_iter().enumerate() {
                if assignment & (1 << i) == 0 {
                    input[usize::from(bit / 64)] &= !(1u64 << (bit % 64));
                }
            }
            let input = BitVec::wrapping_from_limbs(width, &input);
            let want = reference::bin(
                reference::BinOp::And,
                &reference::Bits::from_limbs(bits, input.limbs()),
                &reference::Bits::from_limbs(bits, mask.limbs()),
            );
            let want = BitVec::from_limbs(width, &want.to_limbs()).unwrap();
            assert!(result.tuples().iter().any(|tuple| tuple == &[want]));
            let model = [(SymbolKey::from("source"), input)];
            assert_eq!(cx.eval(&[output], &model[..]).unwrap(), [want]);
        }
    }
}

#[test]
fn masked_projections_preserve_wiring_aliases_and_complements() {
    let mut cx = Context::new();
    let x = cx.symbol("byte", Width::W8).unwrap();
    let zero_extended = cx.zext(x, Width::W512).unwrap();
    let sign_extended = cx.sext(x, Width::W512).unwrap();
    let complement = cx.not(sign_extended).unwrap();
    let low_mask = cx.one(Width::W512).unwrap();
    let high_mask = cx.constant(&BitVec::smin(Width::W512)).unwrap();
    let low = cx.and(zero_extended, low_mask).unwrap();
    let opposite = cx.and(complement, low_mask).unwrap();
    let high = cx.and(sign_extended, high_mask).unwrap();
    let sign = cx.extract(x, 7, Width::W1).unwrap();
    let sign = cx.zext(sign, Width::W512).unwrap();
    let outputs = [low, opposite, high, sign];
    let result = domain(&mut cx, &outputs, &[]);
    assert_eq!(result.stats().inputs, 2);
    assert_eq!(result.tuples().len(), 4);
    for tuple in result.tuples() {
        assert_eq!(tuple[0].to_u64().unwrap() ^ tuple[1].to_u64().unwrap(), 1);
        assert_eq!(tuple[2].bit(511), Some(!tuple[3].is_zero()));
    }
    for value in 0..256 {
        let model = [(
            SymbolKey::from("byte"),
            BitVec::from_u64(Width::W8, value).unwrap(),
        )];
        let values = cx.eval(&outputs, &model[..]).unwrap();
        assert!(result.tuples().contains(&values));
    }
    certify(&mut cx, &result);
}

#[test]
fn opaque_source_bits_are_supersets_without_original_witnesses() {
    let mut cx = Context::new();
    let x = cx.symbol("source", Width::W64).unwrap();
    let square = cx.mul(x, x).unwrap();
    let one = cx.one(Width::W64).unwrap();
    let low = cx.and(x, one).unwrap();
    let square_low = cx.and(square, one).unwrap();
    let result = domain(&mut cx, &[low, square_low], &[]);
    // Separate opaque bit projections may include impossible pairs. No reachability
    // theorem follows from membership in this completely enumerated overapproximation.
    assert_eq!(result.tuples().len(), 4);
    assert!(result.tuples().iter().any(|tuple| tuple[0] != tuple[1]));
    for value in [0, 1, 17, 1 << 63, u64::MAX] {
        let model = [(
            SymbolKey::from("source"),
            BitVec::from_u64(Width::W64, value).unwrap(),
        )];
        let tuple = cx.eval(&[low, square_low], &model[..]).unwrap();
        assert_eq!(tuple[0], tuple[1]);
        assert!(result.tuples().contains(&tuple));
    }
    certify(&mut cx, &result);
}

#[test]
fn projected_bits_respect_changed_partial_declarations() {
    let mut cx = Context::new();
    let x = cx.symbol("source", Width::W512).unwrap();
    let high = BitVec::smin(Width::W512);
    let low = BitVec::one(Width::W512);
    let mask = BitVec::bin_unchecked(BinOp::Or, &high, &low);
    let k = cx.constant(&mask).unwrap();
    let output = cx.and(x, k).unwrap();
    cx.declare_known(x, KnownBits::new(high, low).unwrap())
        .unwrap();
    let fixed = domain(&mut cx, &[output], &[]);
    assert_eq!(fixed.stats().inputs, 0);
    assert_eq!(fixed.tuples(), [vec![low]]);
    certify(&mut cx, &fixed);
    cx.declare_known(x, KnownBits::unknown(Width::W512))
        .unwrap();
    let unrestricted = domain(&mut cx, &[output], &[]);
    assert_eq!(unrestricted.stats().inputs, 2);
    assert_eq!(unrestricted.tuples().len(), 4);
}

#[test]
fn masked_projection_caps_never_return_a_partial_domain() {
    let mut cx = Context::new();
    let x = cx.symbol("source", Width::W64).unwrap();
    let too_many = cx.constant_u64(Width::W64, 0x1ff).unwrap();
    let too_many = cx.and(x, too_many).unwrap();
    assert!(matches!(
        analyze(&mut cx, &[too_many], &[], Limits::default()).unwrap(),
        Analysis::Unknown(Stop::UnavailableOutput(0))
    ));
    let mask = cx.one(Width::W64).unwrap();
    let output = cx.and(x, mask).unwrap();
    for limits in [
        Limits {
            construction_work: 0,
            ..Limits::default()
        },
        Limits {
            visits: 0,
            ..Limits::default()
        },
        Limits {
            nodes: 1,
            ..Limits::default()
        },
        Limits {
            inputs: 0,
            ..Limits::default()
        },
        Limits {
            tuples: 1,
            ..Limits::default()
        },
    ] {
        assert!(matches!(
            analyze(&mut cx, &[output], &[], limits).unwrap(),
            Analysis::Unknown(_)
        ));
    }
}
