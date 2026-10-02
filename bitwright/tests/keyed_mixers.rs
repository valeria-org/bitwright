#![cfg(feature = "prove")]

#[path = "common/keyed_mixers.rs"]
mod fixture;

use bitwright::Assumptions;
use bitwright::engine::{Engine, Strategy};
use bitwright::prove::{self, Config, Limits, Outcome, Question, SampleMode, Unknown};
use bitwright::{BitVec, Context, KnownBits, Query, SymbolKey, Truth, Width};
use fixture::*;

const BOUNDED_PAIR_KEYS: [u64; 2] = [0xc42a_d415_00f4_0813, 0xe3c9_f615_a3eb_92e9];
const BOUNDED_PAIR_SALT: u64 = 0x3ac4_d7d4_3879_6455;

fn target_tail_tuple(
    cx: &mut Context,
    outputs: [bitwright::Expr; 3],
    values: [u64; 3],
) -> bitwright::Expr {
    let mut tuple = cx.one(Width::W1).unwrap();
    for (output, value) in outputs.into_iter().zip(values) {
        let value = constant(cx, value);
        let equal = cx.eq(output, value).unwrap();
        tuple = cx.and(tuple, equal).unwrap();
    }
    tuple
}

#[test]
fn shared_boolean_casts_preserve_correlated_target_and_tail_outputs() {
    use bitwright::View;

    let mut cx = Context::new();
    let target = cx
        .parse(
            include_str!("common/correlated_tail_dispatch.txt"),
            &bitwright::ParseOptions::width(Width::W64),
        )
        .unwrap();
    let predicates = cx
        .post_order(&[target])
        .unwrap()
        .into_iter()
        .filter_map(|e| match cx.view(e).unwrap() {
            View::Zext(p) if cx.width(p).unwrap() == Width::W1 => Some(p),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(predicates.len(), 1);
    let p = predicates[0];
    let wide = cx.zext(p, Width::W64).unwrap();
    let narrow = cx.zext(p, Width::W32).unwrap();
    let widened = cx.zext(narrow, Width::W64).unwrap();
    let same_predicate = cx.eq(wide, widened).unwrap();

    // These are conditional output definitions in the captured input model.
    // They assert no pointer, predecessor, or entry-state restriction, and
    // do not establish that either underlying mixer branch is reachable.
    let yes = [0x14036946d, 0, 0x28634e30b96147a7];
    let no = [0x1403d611e, 0x8ed3cfdc1f9b5303, 0xa000ab116202306f];
    let tail0_yes = constant(&mut cx, yes[1]);
    let tail0_no = constant(&mut cx, no[1]);
    let tail0 = cx.select(p, tail0_yes, tail0_no).unwrap();
    let tail1_yes = constant(&mut cx, yes[2]);
    let tail1_no = constant(&mut cx, no[2]);
    let tail1 = cx.select(p, tail1_yes, tail1_no).unwrap();
    let outputs = [target, tail0, tail1];
    let prove::domain::Analysis::Superset(recovered) =
        prove::domain::analyze(&mut cx, &outputs, &[], prove::domain::Limits::default()).unwrap()
    else {
        panic!("the shared guard should expose a bounded joint output domain");
    };
    assert_eq!(recovered.tuples().len(), 2);
    for values in [no, yes] {
        let tuple = values.map(|v| BitVec::from_u64(Width::W64, v).unwrap());
        assert!(recovered.tuples().iter().any(|t| t == &tuple));
    }
    let recovered_coverage = recovered.coverage(&mut cx).unwrap();
    let true_tuple = target_tail_tuple(&mut cx, outputs, yes);
    let false_tuple = target_tail_tuple(&mut cx, outputs, no);
    let covered = cx.or(true_tuple, false_tuple).unwrap();
    let crossed = target_tail_tuple(&mut cx, outputs, [yes[0], no[1], no[2]]);
    let excluded = cx.not(crossed).unwrap();

    for claim in [same_predicate, covered, excluded, recovered_coverage] {
        for certificate in [false, true] {
            let cfg = Config::default()
                .with_simplify(false)
                .with_samples(0)
                .with_certificate(certificate)
                .with_max_nodes(1);
            let mut question = Question::valid(&mut cx, claim, &cfg).unwrap();
            let Outcome::Proved(proof) = question
                .solve(
                    &mut cx,
                    Limits {
                        conflicts: 0,
                        propagations: 0,
                    },
                )
                .unwrap()
            else {
                panic!("a shared predicate must retain its joint output relations");
            };
            assert!(question.stats().nodes <= 1);
            if certificate {
                proof.unwrap().check().unwrap();
            }
        }
    }

    // Check both abstract predicate values without asserting the existence
    // of a guest satisfying the expensive true fingerprint branch.
    for (value, expected) in [(false, no), (true, yes)] {
        let value = cx.constant(&BitVec::from_bool(value)).unwrap();
        let specialized = cx.substitute(&outputs, &[(p, value)]).unwrap();
        for (e, expected) in specialized.into_iter().zip(expected) {
            assert_eq!(cx.eval(&[e], &[][..]).unwrap()[0].to_u64(), Some(expected));
        }
    }

    // Original byte models retain every high input bit; the input remains
    // an unrestricted 64-bit word despite the Boolean casts above it.
    for x in [0, 1, CANDIDATE, u32::MAX as u64, 1 << 32, 1 << 63, u64::MAX] {
        let environment = (0..8)
            .map(|i| {
                (
                    SymbolKey::from(format!("byte{i}")),
                    BitVec::from_u64(Width::W8, (x >> (8 * i)) & 255).unwrap(),
                )
            })
            .collect::<Vec<_>>();
        assert!(
            cx.eval(&[same_predicate, covered, excluded], &environment[..])
                .unwrap()
                .iter()
                .all(|value| !value.is_zero())
        );
    }
}

#[test]
fn independent_predicates_do_not_inherit_target_tail_correlation() {
    let mut cx = Context::new();
    let p = cx.symbol("p", Width::W1).unwrap();
    let q = cx.symbol("q", Width::W1).unwrap();
    let wide = cx.zext(p, Width::W64).unwrap();
    let narrow = cx.zext(q, Width::W32).unwrap();
    let widened = cx.zext(narrow, Width::W64).unwrap();
    let cast_equal = cx.eq(wide, widened).unwrap();
    let yes = [0x14036946d, 0, 0x28634e30b96147a7];
    let no = [0x1403d611e, 0x8ed3cfdc1f9b5303, 0xa000ab116202306f];
    let target_yes = constant(&mut cx, yes[0]);
    let target_no = constant(&mut cx, no[0]);
    let target = cx.select(p, target_yes, target_no).unwrap();
    let tail0_yes = constant(&mut cx, yes[1]);
    let tail0_no = constant(&mut cx, no[1]);
    let tail0 = cx.select(q, tail0_yes, tail0_no).unwrap();
    let tail1_yes = constant(&mut cx, yes[2]);
    let tail1_no = constant(&mut cx, no[2]);
    let tail1 = cx.select(p, tail1_yes, tail1_no).unwrap();
    let outputs = [target, tail0, tail1];
    let prove::domain::Analysis::Superset(recovered) =
        prove::domain::analyze(&mut cx, &outputs, &[], prove::domain::Limits::default()).unwrap()
    else {
        panic!("the independent predicates should expose all four tuple combinations");
    };
    assert_eq!(recovered.tuples().len(), 4);
    let true_tuple = target_tail_tuple(&mut cx, outputs, yes);
    let false_tuple = target_tail_tuple(&mut cx, outputs, no);
    let covered = cx.or(true_tuple, false_tuple).unwrap();
    for claim in [cast_equal, covered] {
        let cfg = Config::default().with_samples(0);
        let mut question = Question::valid(&mut cx, claim, &cfg).unwrap();
        let Outcome::Refuted(model) = question.solve(&mut cx, Limits::conflicts(100)).unwrap()
        else {
            panic!("independent predicates need an original refuting model");
        };
        let values = cx.eval(&[p, q, claim], &model[..]).unwrap();
        assert_ne!(values[0], values[1]);
        assert!(values[2].is_zero());
    }
}

#[test]
fn independent_word_dispatch_domain_has_a_bounded_original_coverage_certificate() {
    let mut cx = Context::new();
    let target = cx
        .parse(
            include_str!("common/independent_words_dispatch.txt"),
            &bitwright::ParseOptions::width(Width::W64),
        )
        .unwrap();
    let prove::domain::Analysis::Superset(domain) =
        prove::domain::analyze(&mut cx, &[target], &[], prove::domain::Limits::default()).unwrap()
    else {
        panic!("joint Boolean structure must expose a bounded target domain");
    };
    assert_eq!(domain.tuples().len(), 2);
    let coverage = domain.coverage(&mut cx).unwrap();
    let cfg = Config::default()
        .with_simplify(false)
        .with_samples(0)
        .with_certificate(true)
        .with_max_nodes(1);
    let mut question = Question::valid(&mut cx, coverage, &cfg).unwrap();
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
        panic!("original target coverage should require no search");
    };
    assert_eq!(question.stats().nodes, 1);
    cert.check().unwrap();
    // Replay both independently known expression witnesses; abstract cut values
    // alone would not establish these original-symbol models.
    let mut replayed = Vec::new();
    for y in [0, 1] {
        let model = (0..8)
            .chain(16..24)
            .map(|i| {
                (
                    SymbolKey::from(format!("byte{i}")),
                    BitVec::from_u64(Width::W8, if i == 16 { y } else { 0 }).unwrap(),
                )
            })
            .collect::<Vec<_>>();
        let value = cx.eval(&[target], &model[..]).unwrap();
        assert!(domain.tuples().contains(&value));
        replayed.push(value[0]);
    }
    assert_ne!(replayed[0], replayed[1]);
}

#[test]
fn odd_product_high_bit_covariance_proves_without_search() {
    use bitwright::BinOp;
    for bits in [1u16, 8, 32, 64, 65, 129] {
        let width = Width::new(bits).unwrap();
        for compressed in [false, true] {
            for key in [GOLDEN, KEYS[0], KEYS[1]] {
                let mut cx = Context::new();
                let x = cx.symbol("x", width).unwrap();
                let one = cx.one(width).unwrap();
                let count = cx.constant_u64(width, u64::from(bits - 1)).unwrap();
                let high = cx.bin(BinOp::Shl, one, count).unwrap();
                let key = cx.constant(&BitVec::wrapping_from_u64(width, key)).unwrap();
                let flipped = cx.xor(x, high).unwrap();
                let left = cx.mul(flipped, key).unwrap();
                let product = cx.mul(x, key).unwrap();
                let right = cx.xor(product, high).unwrap();
                let claim = cx.eq(left, right).unwrap();
                let cfg = Config::default()
                    .with_simplify(false)
                    .with_samples(0)
                    .with_certificate(true)
                    .with_carry_save_multiplication(compressed)
                    .with_xor3_encoding(compressed);
                let mut q = Question::valid(&mut cx, claim, &cfg).unwrap();
                let Outcome::Proved(Some(cert)) = q.solve(&mut cx, Limits::conflicts(0)).unwrap()
                else {
                    panic!("an odd product must preserve a flip of the highest input bit");
                };
                assert_eq!(q.stats().conflicts, 0);
                cert.check().unwrap();

                // Even multiplication discards this input bit instead. Replaying
                // its counterexample guards the parity requirement of the identity.
                let even = cx.constant(&BitVec::wrapping_from_u64(width, 2)).unwrap();
                let left = cx.mul(flipped, even).unwrap();
                let product = cx.mul(x, even).unwrap();
                let right = cx.xor(product, high).unwrap();
                let wrong = cx.eq(left, right).unwrap();
                let mut q = Question::valid(&mut cx, wrong, &cfg).unwrap();
                let Outcome::Refuted(model) = q.solve(&mut cx, Limits::conflicts(1)).unwrap()
                else {
                    panic!("the highest-bit covariance does not hold for an even product");
                };
                assert!(cx.eval(&[wrong], &model[..]).unwrap()[0].is_zero());
            }
        }
    }
}

#[test]
fn high_projection_msb_symmetry_must_not_restrict_exact_guards() {
    use bitwright::Expr;
    let inverses = KEYS.map(|key| {
        let mut inverse = 1u64;
        for _ in 0..6 {
            inverse = inverse.wrapping_mul(2u64.wrapping_sub(key.wrapping_mul(inverse)));
        }
        assert_eq!(key.wrapping_mul(inverse), 1);
        inverse
    });
    fn projection(cx: &mut Context, x: Expr, image: Expr, inverses: &[u64; 4]) -> Expr {
        let mut all = cx.one(Width::W1).unwrap();
        for i in 0..4 {
            let key = constant(cx, KEYS[i]);
            let input = cx.xor(x, key).unwrap();
            let inner = cx.mul(input, key).unwrap();
            let salt = constant(cx, if i == 0 { 0 } else { SALTS[i - 1] });
            let output = cx.xor(image, salt).unwrap();
            let inverse = constant(cx, inverses[i]);
            let decoded = cx.mul(output, inverse).unwrap();
            let high = Width::new(36).unwrap();
            let inner = cx.extract(inner, 28, high).unwrap();
            let decoded = cx.extract(decoded, 28, high).unwrap();
            let equal = cx.eq(inner, decoded).unwrap();
            all = cx.and(all, equal).unwrap();
        }
        all
    }

    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let image = cx.symbol("image", Width::W64).unwrap();
    let msb = constant(&mut cx, 1 << 63);
    let flipped_x = cx.xor(x, msb).unwrap();
    let flipped_image = cx.xor(image, msb).unwrap();
    let necessary = projection(&mut cx, x, image, &inverses);
    let flipped = projection(&mut cx, flipped_x, flipped_image, &inverses);
    let claim = cx.eq(necessary, flipped).unwrap();
    for compressed in [false, true] {
        let cfg = Config::default()
            .with_simplify(false)
            .with_samples(0)
            .with_certificate(true)
            .with_carry_save_multiplication(compressed)
            .with_xor3_encoding(compressed);
        let mut q = Question::valid(&mut cx, claim, &cfg).unwrap();
        let Outcome::Proved(Some(cert)) = q.solve(&mut cx, Limits::conflicts(0)).unwrap() else {
            panic!("flipping both highest bits preserves the necessary high-bit system");
        };
        cert.check().unwrap();
    }

    for input in [
        0,
        1,
        CANDIDATE,
        u64::from(u32::MAX),
        1 << 32,
        1 << 63,
        PREIMAGE,
        u64::MAX,
    ] {
        for image in [0, 1, 1 << 63, u64::MAX, scalar(KEYS[0], input)] {
            for i in 0..4 {
                let salt = if i == 0 { 0 } else { SALTS[i - 1] };
                let inner = KEYS[i].wrapping_mul(input ^ KEYS[i]);
                let decoded = inverses[i].wrapping_mul(image ^ salt);
                let other_inner = KEYS[i].wrapping_mul((input ^ (1 << 63)) ^ KEYS[i]);
                let other_decoded = inverses[i].wrapping_mul((image ^ (1 << 63)) ^ salt);
                assert_eq!(
                    decoded.wrapping_sub(inner),
                    other_decoded.wrapping_sub(other_inner)
                );
                assert_eq!(
                    decoded >> 28 == inner >> 28,
                    other_decoded >> 28 == other_inner >> 28
                );
            }
        }
    }

    // The selector changes when the highest input bit flips. The exact guard is
    // therefore not invariant, even though both necessary systems stay satisfied.
    let (exact_exclusion, _) = fixture::claim(&mut cx, "cross-key-guards", Spelling::Nested);
    let value = scalar(KEYS[0], CANDIDATE);
    for flip in [0, 1u64 << 63] {
        let model = [
            (
                SymbolKey::from("x"),
                BitVec::from_u64(Width::W64, CANDIDATE ^ flip).unwrap(),
            ),
            (
                SymbolKey::from("image"),
                BitVec::from_u64(Width::W64, value ^ flip).unwrap(),
            ),
        ];
        let values = cx
            .eval(&[necessary, flipped, exact_exclusion], &model[..])
            .unwrap();
        assert!(!values[0].is_zero() && !values[1].is_zero());
        assert_eq!(!values[2].is_zero(), flip != 0);
    }
}

#[test]
fn decoded_mixer_guards_are_equivalent_over_complete_small_domains() {
    use bitwright::{BinOp, Expr};

    fn scramble(cx: &mut Context, h: Expr, spelling: Spelling) -> Expr {
        let four = cx.constant_u64(Width::W8, 4).unwrap();
        let six = cx.constant_u64(Width::W8, 6).unwrap();
        let selector = cx.bin(BinOp::LShr, h, six).unwrap();
        let shifted = match spelling {
            Spelling::Nested => {
                let high = cx.bin(BinOp::LShr, h, four).unwrap();
                cx.bin(BinOp::LShr, high, selector).unwrap()
            }
            Spelling::Compact => {
                let count = cx.add(four, selector).unwrap();
                cx.bin(BinOp::LShr, h, count).unwrap()
            }
        };
        cx.xor(h, shifted).unwrap()
    }

    fn oracle(key: u8, x: u8) -> u8 {
        let h = key.wrapping_mul(x ^ key);
        key.wrapping_mul(h ^ ((h >> 4) >> (h >> 6)))
    }

    let keys = [0x2bu8, 0x87, 0xf5, 0xa1];
    let inverses = keys.map(|key| {
        let mut inverse = 1u8;
        for _ in 0..3 {
            inverse = inverse.wrapping_mul(2u8.wrapping_sub(key.wrapping_mul(inverse)));
        }
        assert_eq!(key.wrapping_mul(inverse), 1);
        inverse
    });
    let salts = std::array::from_fn::<_, 3, _>(|i| oracle(keys[0], 13) ^ oracle(keys[i + 1], 13));

    for input_bits in [4, 8] {
        // The image is a fresh existential coordinate, not a free extra degree of
        // freedom: the complete decoded system also forces image = F0(input).
        for input in 0..(1u16 << input_bits) {
            let input = input as u8;
            let original =
                (1..4).all(|i| oracle(keys[0], input) ^ oracle(keys[i], input) == salts[i - 1]);
            for image in 0..=u8::MAX {
                let decoded = (0..4).all(|i| {
                    let h = keys[i].wrapping_mul(input ^ keys[i]);
                    let salt = if i == 0 { 0 } else { salts[i - 1] };
                    inverses[i].wrapping_mul(image ^ salt) == h ^ ((h >> 4) >> (h >> 6))
                });
                assert_eq!(decoded, original && image == oracle(keys[0], input));
            }
        }

        for spelling in [Spelling::Nested, Spelling::Compact] {
            let mut cx = Context::new();
            let input = cx.symbol("input", Width::new(input_bits).unwrap()).unwrap();
            let x = cx.zext(input, Width::W8).unwrap();
            let image = cx.symbol("image", Width::W8).unwrap();
            let mut outputs = Vec::new();
            let mut decoded_rows = cx.one(Width::W1).unwrap();
            for i in 0..4 {
                let key = cx.constant_u64(Width::W8, u64::from(keys[i])).unwrap();
                let masked = cx.xor(x, key).unwrap();
                let inner = cx.mul(key, masked).unwrap();
                let scrambled = scramble(&mut cx, inner, spelling);
                outputs.push(cx.mul(key, scrambled).unwrap());
                let salt = if i == 0 { 0 } else { salts[i - 1] };
                let salt = cx.constant_u64(Width::W8, u64::from(salt)).unwrap();
                let output = cx.xor(image, salt).unwrap();
                let inverse = cx.constant_u64(Width::W8, u64::from(inverses[i])).unwrap();
                let decoded = cx.mul(output, inverse).unwrap();
                let row = cx.eq(decoded, scrambled).unwrap();
                decoded_rows = cx.and(decoded_rows, row).unwrap();
            }
            let mut original = cx.one(Width::W1).unwrap();
            for i in 1..4 {
                let pair = cx.xor(outputs[0], outputs[i]).unwrap();
                let salt = cx.constant_u64(Width::W8, u64::from(salts[i - 1])).unwrap();
                let row = cx.eq(pair, salt).unwrap();
                original = cx.and(original, row).unwrap();
            }
            let link = cx.eq(image, outputs[0]).unwrap();
            let linked_original = cx.and(original, link).unwrap();
            let equivalent = cx.eq(decoded_rows, linked_original).unwrap();

            let words = Config::default()
                .with_simplify(false)
                .with_sample_mode(SampleMode::Words)
                .with_samples(1 << 18)
                .with_max_nodes(1);
            let mut q = Question::valid(&mut cx, equivalent, &words).unwrap();
            assert!(matches!(
                q.solve(&mut cx, Limits::conflicts(0)).unwrap(),
                Outcome::Proved(None)
            ));
            assert_eq!(q.stats().nodes, 0);

            // Omitting the image link changes the predicate over its extended
            // domain. A valid original input with a different image exposes it.
            let missing_link = cx.eq(decoded_rows, original).unwrap();
            let mut q = Question::valid(&mut cx, missing_link, &words).unwrap();
            let Outcome::Refuted(model) = q.solve(&mut cx, Limits::conflicts(0)).unwrap() else {
                panic!("an unconstrained image must not be treated as the original guard");
            };
            let values = cx
                .eval(&[missing_link, original, link], &model[..])
                .unwrap();
            assert!(values[0].is_zero());
            assert!(!values[1].is_zero());
            assert!(values[2].is_zero());
            assert_eq!(model.len(), 2);
            assert_eq!(q.stats().nodes, 0);

            if input_bits == 4 {
                for compressed in [false, true] {
                    let cfg = Config::default()
                        .with_simplify(false)
                        .with_samples(0)
                        .with_certificate(true)
                        .with_carry_save_multiplication(compressed)
                        .with_xor3_encoding(compressed);
                    let mut q = Question::valid(&mut cx, equivalent, &cfg).unwrap();
                    let Outcome::Proved(Some(cert)) = q
                        .solve(
                            &mut cx,
                            Limits {
                                conflicts: 10_000,
                                propagations: 5_000_000,
                            },
                        )
                        .unwrap()
                    else {
                        panic!("the exact decoded guard must agree with the original guard");
                    };
                    cert.check().unwrap();
                }
            }
        }
    }
}

#[test]
fn mixer_corrections_are_signed_small_and_relaxed_models_need_original_replay() {
    use bitwright::CmpOp;
    let bound = (1u64 << 28) - 1;
    // Every selector partitions the high half before shifting it. Check the ends of
    // each partition, including both signs of the maximal XOR correction.
    for selector in 0..16u128 {
        for high in [selector << 28, ((selector + 1) << 28) - 1] {
            for low in [0, bound, u64::from(u32::MAX)] {
                let h = ((high << 32) | u128::from(low)) as u64;
                let shifted = h >> (32 + (h >> 60));
                assert!(shifted <= bound);
                let exact_difference = i128::from(h ^ shifted) - i128::from(h);
                assert!((-(i128::from(bound))..=i128::from(bound)).contains(&exact_difference));
                assert_eq!(
                    exact_difference,
                    i128::from((h ^ shifted).wrapping_sub(h) as i64)
                );
            }
        }
    }
    for key in KEYS.into_iter().chain([GOLDEN]) {
        let mut inverse = 1u64;
        for _ in 0..6 {
            inverse = inverse.wrapping_mul(2u64.wrapping_sub(key.wrapping_mul(inverse)));
        }
        assert_eq!(inverse.wrapping_mul(key), 1);
        for value in [
            0,
            1,
            CANDIDATE,
            u64::from(u32::MAX),
            1 << 32,
            1 << 63,
            PREIMAGE,
            u64::MAX,
        ] {
            let h = key.wrapping_mul(value ^ key);
            let delta = inverse.wrapping_mul(scalar(key, value)).wrapping_sub(h) as i64;
            assert!((-(bound as i64)..=bound as i64).contains(&delta));
        }
    }

    // Zero error satisfies the necessary bound, but omitting the selected XOR changes
    // the actual image. A model of that relaxation cannot be admitted as a counterexample
    // to the original exclusion without evaluating the original expression.
    let h = GOLDEN.wrapping_mul(GOLDEN);
    let relaxed_image = GOLDEN.wrapping_mul(h);
    assert_ne!(relaxed_image, scalar(GOLDEN, 0));
    let mut inverse = 1u64;
    for _ in 0..6 {
        inverse = inverse.wrapping_mul(2u64.wrapping_sub(GOLDEN.wrapping_mul(inverse)));
    }
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let y = cx.symbol("image", Width::W64).unwrap();
        let output = mixer(&mut cx, x, GOLDEN, spelling);
        let key = constant(&mut cx, GOLDEN);
        let masked = cx.xor(x, key).unwrap();
        let inner = cx.mul(masked, key).unwrap();
        let inv = constant(&mut cx, inverse);
        let decoded = cx.mul(y, inv).unwrap();
        let delta = cx.sub(decoded, inner).unwrap();
        let lo = constant(&mut cx, 0u64.wrapping_sub(bound));
        let hi = constant(&mut cx, bound);
        let lower = cx.cmp(CmpOp::Sle, lo, delta).unwrap();
        let upper = cx.cmp(CmpOp::Sle, delta, hi).unwrap();
        let necessary = cx.and(lower, upper).unwrap();
        let low = cx.extract(delta, 0, Width::new(29).unwrap()).unwrap();
        let extended = cx.sext(low, Width::W64).unwrap();
        let weak_necessary = cx.eq(delta, extended).unwrap();
        let decoded_high = cx.extract(decoded, 28, Width::new(36).unwrap()).unwrap();
        let inner_high = cx.extract(inner, 28, Width::new(36).unwrap()).unwrap();
        let high_projection = cx.eq(decoded_high, inner_high).unwrap();
        let original = cx.ne(output, y).unwrap();
        cx.declare_known(x, KnownBits::constant(&BitVec::zero(Width::W64)))
            .unwrap();
        cx.declare_known(
            y,
            KnownBits::constant(&BitVec::from_u64(Width::W64, relaxed_image).unwrap()),
        )
        .unwrap();
        let cfg = Config::default()
            .with_simplify(false)
            .with_samples(0)
            .with_certificate(true);
        for predicate in [necessary, weak_necessary, high_projection] {
            let exclusion = cx.not(predicate).unwrap();
            let mut q = Question::valid(&mut cx, exclusion, &cfg).unwrap();
            let Outcome::Refuted(model) = q.solve(&mut cx, Limits::conflicts(1)).unwrap() else {
                panic!("the zero-error point must satisfy the relaxation");
            };
            let values = cx.eval(&[exclusion, original], &model[..]).unwrap();
            assert!(values[0].is_zero());
            assert!(!values[1].is_zero());
            assert_eq!(model.len(), 2);
        }
        let mut q = Question::valid(&mut cx, original, &cfg).unwrap();
        let Outcome::Proved(Some(cert)) = q.solve(&mut cx, Limits::conflicts(1)).unwrap() else {
            panic!("the original image excludes the same supplied output");
        };
        cert.check().unwrap();
    }
}

#[test]
fn captured_shared_mixer_pairs_replay_the_numeric_edges_and_reject_a_wrong_pivot() {
    use bitwright::{CmpOp, ParseOptions, View};
    let common_key = 0xe97b_5301_3b39_55b1;
    let other_keys = [
        0xdbc7_d903_c040_32f9,
        0xc07b_1c82_3afc_12ad,
        0xc766_dfa6_fc62_2543,
    ];
    let salts = [
        0xfccd_7455_0edc_ae39,
        0xdbeb_5595_b167_b8cb,
        0xb5fa_5a78_1d17_faab,
    ];
    let mut cx = Context::new();
    let target = cx
        .parse(
            include_str!("common/shared_mixer_dispatch.txt"),
            &ParseOptions::width(Width::W64),
        )
        .unwrap();
    let mut subjects = std::collections::HashMap::new();
    for e in cx.post_order(&[target]).unwrap() {
        if let View::Cmp(CmpOp::Eq, a, b) = cx.view(e).unwrap() {
            for (subject, constant) in [(a, b), (b, a)] {
                if let View::Const(value) = cx.view(constant).unwrap()
                    && let Some(salt) = value.to_u64()
                    && salts.contains(&salt)
                {
                    assert!(subjects.insert(salt, subject).is_none());
                }
            }
        }
    }
    assert_eq!(subjects.len(), 3);
    let word = cx.symbol("word", Width::W64).unwrap();
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let common = mixer(&mut cx, word, common_key, spelling);
        let mut reconstructed = Vec::new();
        for key in other_keys {
            let other = mixer(&mut cx, word, key, spelling);
            reconstructed.push(cx.xor(common, other).unwrap());
        }
        // Replacing the common mixer with the first listed one keeps the first edge but
        // changes the remaining edges. Boolean guards can be false in both versions;
        // compare their full numeric operands so such a transcription error is visible.
        let wrong_common = mixer(&mut cx, word, other_keys[0], spelling);
        let second = mixer(&mut cx, word, other_keys[1], spelling);
        let wrong_edge = cx.xor(wrong_common, second).unwrap();
        let mut detected_wrong_pivot = false;
        for value in [
            0,
            1,
            CANDIDATE,
            u64::from(u32::MAX),
            1 << 32,
            1 << 63,
            PREIMAGE,
            u64::MAX,
        ] {
            let mut env = (8..16)
                .map(|byte| {
                    (
                        SymbolKey::from(format!("byte{byte}")),
                        BitVec::from_u64(Width::W8, (value >> (8 * (byte - 8))) & 255).unwrap(),
                    )
                })
                .collect::<Vec<_>>();
            env.push((
                SymbolKey::from("word"),
                BitVec::from_u64(Width::W64, value).unwrap(),
            ));
            for i in 0..3 {
                let got = cx
                    .eval(&[subjects[&salts[i]], reconstructed[i]], &env[..])
                    .unwrap();
                let expected = scalar(common_key, value) ^ scalar(other_keys[i], value);
                assert_eq!(got[0].to_u64(), Some(expected));
                assert_eq!(got[1], got[0]);
            }
            let got = cx
                .eval(&[subjects[&salts[1]], wrong_edge], &env[..])
                .unwrap();
            detected_wrong_pivot |= got[0] != got[1];
        }
        assert!(detected_wrong_pivot);
    }
}

#[test]
fn complete_word_enumeration_recovers_small_fingerprint_domains_online() {
    for bits in [8, 12, 16] {
        for spelling in [Spelling::Nested, Spelling::Compact] {
            for case in ["fingerprint-32", "masked-pair-32-unique"] {
                let mut cx = Context::new();
                let (claim, expected) = fixture::claim(&mut cx, case, spelling);
                assert_eq!(expected, Expected::Proved);
                let x = cx.find_symbol(&SymbolKey::from("x")).unwrap();
                let high_zero = !((1u64 << bits) - 1) & u64::from(u32::MAX);
                cx.declare_known(
                    x,
                    KnownBits::new(
                        BitVec::from_u64(Width::W32, high_zero).unwrap(),
                        BitVec::zero(Width::W32),
                    )
                    .unwrap(),
                )
                .unwrap();
                let cfg = Config::default()
                    .with_simplify(false)
                    .with_sample_mode(SampleMode::Words)
                    .with_samples(1 << bits)
                    .with_max_nodes(0);
                let q = Question::valid(&mut cx, claim, &cfg).unwrap();
                assert!(
                    matches!(q.outcome(), Some(Outcome::Proved(None))),
                    "case={case}, bits={bits}, spelling={spelling:?}"
                );
                assert_eq!(q.stats().nodes, 0);
                assert_eq!(q.stats().samples, 1 << bits);
            }
        }
    }
}

#[test]
fn common_product_projections_do_not_remove_fingerprint_input_dependencies() {
    let difference = |x: u64, a: u64, b: u64| {
        let hi = a.wrapping_mul(x ^ a);
        let hj = b.wrapping_mul(x ^ b);
        hi.wrapping_mul(b).wrapping_sub(hj.wrapping_mul(a))
    };
    for a in KEYS.into_iter().chain([0, 2, u64::MAX]) {
        for b in KEYS.into_iter().chain([0, 4, u64::MAX]) {
            let d = a ^ b;
            for x in [0, 1, CANDIDATE, u32::MAX as u64, 1 << 63, u64::MAX] {
                let projected = d
                    .wrapping_sub(2u64.wrapping_mul((x ^ b) & d))
                    .wrapping_mul(a)
                    .wrapping_mul(b);
                assert_eq!(difference(x, a, b), projected);
            }
        }
    }
    // Every key has the same low bit, so that bit disappears from each scaled
    // product difference. It still affects the entire fingerprint through the shifts.
    for a in KEYS {
        for b in KEYS {
            assert_eq!(difference(0, a, b), difference(1, a, b));
        }
    }
    assert_ne!(scalar_fingerprint(0), scalar_fingerprint(1));

    // Passing the necessary mask alone does not establish a shared original input.
    // For keys 3 and 5, inner products 9 and 5 decode to raw words 3 and 1.
    let (a, b, raw_a, raw_b) = (3u64, 5u64, 3u64, 1u64);
    let d = a ^ b;
    let residual = d.wrapping_sub(raw_a.wrapping_sub(raw_b));
    assert_eq!(residual & !(d << 1), 0);
    assert_ne!(raw_a ^ a, raw_b ^ b);
}

#[test]
fn a_satisfied_output_prefix_is_not_a_full_fingerprint_counterexample() {
    let value = 0x15c4a4;
    assert_eq!(scalar_fingerprint(value), 0xff9f_ef7f_b9df_ff80);
    assert_eq!(scalar_fingerprint(value) & 255, TARGET & 255);
    assert_ne!(scalar_fingerprint(value), TARGET);
    for input_width in [Width::W32, Width::W64] {
        for spelling in [Spelling::Nested, Spelling::Compact] {
            let mut cx = Context::new();
            let input = cx.symbol("x", input_width).unwrap();
            let known = BitVec::from_u64(input_width, value).unwrap();
            cx.declare_known(input, KnownBits::constant(&known))
                .unwrap();
            let wide = if input_width == Width::W32 {
                cx.zext(input, Width::W64).unwrap()
            } else {
                input
            };
            let fp = fingerprint(&mut cx, wide, spelling);
            let byte = cx.extract(fp, 0, Width::W8).unwrap();
            let low_target = cx.constant_u64(Width::W8, TARGET & 255).unwrap();
            let projected_claim = cx.ne(byte, low_target).unwrap();
            let target = constant(&mut cx, TARGET);
            let full_claim = cx.ne(fp, target).unwrap();
            let cfg = Config::default()
                .with_samples(0)
                .with_simplify(false)
                .with_certificate(true);
            let mut q = Question::valid(&mut cx, projected_claim, &cfg).unwrap();
            let Outcome::Refuted(model) = q.solve(&mut cx, Limits::conflicts(1)).unwrap() else {
                panic!("the known input satisfies only the observed output prefix");
            };
            assert_eq!(model[0].1, known);
            let roots = cx.eval(&[projected_claim, full_claim], &model[..]).unwrap();
            assert!(roots[0].is_zero() && !roots[1].is_zero());
            let mut q = Question::valid(&mut cx, full_claim, &cfg).unwrap();
            let Outcome::Proved(Some(cert)) = q.solve(&mut cx, Limits::conflicts(1)).unwrap()
            else {
                panic!("the same assignment still excludes the full target");
            };
            cert.check().unwrap();
        }
    }
}

#[test]
fn bounded_loaded_word_pair_preserves_its_domain_and_exhaustion_is_explicit() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let input = cx.symbol("loaded_word", Width::W32).unwrap();
        let wide = cx.zext(input, Width::W64).unwrap();
        let a = mixer(&mut cx, wide, BOUNDED_PAIR_KEYS[0], spelling);
        let b = mixer(&mut cx, wide, BOUNDED_PAIR_KEYS[1], spelling);
        let pair = cx.xor(a, b).unwrap();
        let salt = constant(&mut cx, BOUNDED_PAIR_SALT);
        let claim = cx.ne(pair, salt).unwrap();
        for value in [0, 1, 63, 255, 65_535, 1 << 31, u32::MAX as u64] {
            let model = [(
                SymbolKey::from("loaded_word"),
                BitVec::from_u64(Width::W32, value).unwrap(),
            )];
            let evaluated = cx.eval(&[pair], &model[..]).unwrap()[0].to_u64().unwrap();
            assert_eq!(
                evaluated,
                scalar(BOUNDED_PAIR_KEYS[0], value) ^ scalar(BOUNDED_PAIR_KEYS[1], value)
            );
        }
        let cfg = Config::default()
            .with_simplify(false)
            .with_samples(256)
            .with_sample_mode(SampleMode::Words)
            .with_max_nodes(0);
        let q = Question::valid(&mut cx, claim, &cfg).unwrap();
        assert!(matches!(q.outcome(), Some(Outcome::Unknown(_))));
        assert_eq!(q.stats().samples, 256);
        assert_eq!(cx.width(input).unwrap(), Width::W32);
        assert!(cx.declared_known(input).unwrap().is_none());
    }
}

#[test]
#[ignore = "heavy: complete 2^32-input independent keyed-pair exclusion oracle; run with --release -- --ignored"]
fn bounded_loaded_word_pair_has_no_preimage_in_its_complete_domain() {
    for value in 0..1u64 << 32 {
        assert_ne!(
            scalar(BOUNDED_PAIR_KEYS[0], value) ^ scalar(BOUNDED_PAIR_KEYS[1], value),
            BOUNDED_PAIR_SALT,
            "the necessary pair condition has a 32-bit witness at {value:#x}"
        );
    }
}

#[test]
fn exact_odd_key_cancellation_and_inversion_precede_sat_for_both_spellings() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        for strategy in [Strategy::standard(), Strategy::compile()] {
            let engine = Engine::builder()
                .builtin()
                .strategy(strategy)
                .build()
                .unwrap();
            for key in [
                GOLDEN,
                0xff51_afd7_ed55_8ccd,
                KEYS[0],
                KEYS[1],
                KEYS[2],
                KEYS[3],
            ] {
                let mut cx = Context::new();
                let x = cx.symbol("x", Width::W64).unwrap();
                let y = cx.symbol("y", Width::W64).unwrap();
                let a = mixer(&mut cx, x, key, spelling);
                let b = mixer(&mut cx, y, key, spelling);
                assert_eq!(
                    cx.prove(Query::Bijective { e: a, of: x }).unwrap(),
                    Truth::True
                );
                let equality = cx.eq(a, b).unwrap();
                let want = cx.eq(x, y).unwrap();
                assert_eq!(engine.simplify(&mut cx, equality).unwrap().expr, want);
            }
            let mut cx = Context::new();
            let (p, _) = claim(&mut cx, "same-key-inverse", spelling);
            let x = cx.find_symbol(&SymbolKey::from("x")).unwrap();
            let expected = constant(&mut cx, PREIMAGE);
            let expected = cx.eq(x, expected).unwrap();
            assert_eq!(engine.simplify(&mut cx, p).unwrap().expr, expected);
            assert_eq!(scalar(GOLDEN, PREIMAGE), 0x1234);
        }
    }
}

#[test]
fn scalar_mixer_and_fingerprint_replay_match_the_original_dags() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let output = fingerprint(&mut cx, x, spelling);
        let roots: Vec<_> = KEYS
            .into_iter()
            .map(|k| mixer(&mut cx, x, k, spelling))
            .chain([output])
            .collect();
        let mut state = 0x1234_5678_9abc_def0u64;
        for value in [
            0,
            CANDIDATE - 1,
            CANDIDATE,
            CANDIDATE + 1,
            u32::MAX as u64,
            1 << 32,
            (1 << 32) + CANDIDATE,
            1 << 63,
            u64::MAX,
        ]
        .into_iter()
        .chain((0..128).map(|_| {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            state
        })) {
            let env = [(
                SymbolKey::from("x"),
                BitVec::from_u64(Width::W64, value).unwrap(),
            )];
            let got = cx.eval(&roots, &env[..]).unwrap();
            for (i, key) in KEYS.into_iter().enumerate() {
                assert_eq!(got[i].to_u64(), Some(scalar(key, value)));
            }
            assert_eq!(got[4].to_u64(), Some(scalar_fingerprint(value)));
        }
    }
    assert_eq!(scalar_terms(CANDIDATE), [0, 0, 0]);
    assert_ne!(scalar_fingerprint(CANDIDATE), TARGET);
}

#[test]
fn masked_pair_peephole_near_misses_preserve_the_full_mask_and_product_semantics() {
    let pair = scalar_terms(0x8d)[0];
    assert_eq!(pair & 0x7f, 0);
    assert_ne!(pair & !TARGET, 0);
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let (claim, _) = fixture::claim(&mut cx, "masked-pair-32", spelling);
        let env = [(
            SymbolKey::from("x"),
            BitVec::from_u64(Width::W32, 0x8d).unwrap(),
        )];
        // The low-seven-bit condition admits this value; the actual full mask rejects it.
        assert!(!cx.eval(&[claim], &env[..]).unwrap()[0].is_zero());
        let key = KEYS[0];
        let h = key.wrapping_mul(key);
        let r = h >> (32 + (h >> 60));
        let distributed = key.wrapping_mul(h) ^ key.wrapping_mul(r);
        assert_ne!(distributed, scalar(key, 0));
        let x = cx.symbol("wide", Width::W64).unwrap();
        let actual = mixer(&mut cx, x, key, spelling);
        let env = [(SymbolKey::from("wide"), BitVec::zero(Width::W64))];
        assert_ne!(
            cx.eval(&[actual], &env[..]).unwrap()[0].to_u64(),
            Some(distributed)
        );
    }
}

#[test]
fn even_keys_have_concrete_collisions_and_are_never_cancelled_as_bijections() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let y = cx.symbol("y", Width::W64).unwrap();
        let key = GOLDEN - 1;
        let a = mixer(&mut cx, x, key, spelling);
        let b = mixer(&mut cx, y, key, spelling);
        assert_ne!(
            cx.prove(Query::Bijective { e: a, of: x }).unwrap(),
            Truth::True
        );
        let equal = cx.eq(a, b).unwrap();
        let plain = cx.eq(x, y).unwrap();
        let simplified = Engine::standard().simplify(&mut cx, equal).unwrap().expr;
        assert_ne!(simplified, plain);
        let env = [
            (SymbolKey::from("x"), BitVec::zero(Width::W64)),
            (
                SymbolKey::from("y"),
                BitVec::from_u64(Width::W64, 1 << 63).unwrap(),
            ),
        ];
        assert_eq!(scalar(key, 0), scalar(key, 1 << 63));
        assert_eq!(
            cx.eval(&[equal, simplified, plain], &env[..]).unwrap(),
            [
                BitVec::from_bool(true),
                BitVec::from_bool(true),
                BitVec::from_bool(false)
            ]
        );
    }
}

#[test]
fn simplified_inverse_counterexamples_replay_in_original_symbols() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let (original, _) = claim(&mut cx, "same-key-inverse", spelling);
        let cfg = Config::default().with_samples(0).with_max_conflicts(100);
        let Outcome::Refuted(model) = prove::valid(&mut cx, original, &cfg).unwrap() else {
            panic!("not refuted");
        };
        let x = model
            .iter()
            .find(|(key, _)| *key == SymbolKey::from("x"))
            .unwrap()
            .1
            .to_u64()
            .unwrap();
        assert_ne!(scalar(GOLDEN, x), 0x1234);
        assert!(cx.eval(&[original], &model[..]).unwrap()[0].is_zero());
    }
}

#[test]
fn correlated_pair_exclusion_and_target_superset_do_not_require_mixer_reachability() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        for name in ["correlated-pair", "target-cut"] {
            let mut cx = Context::new();
            let (p, expected) = claim(&mut cx, name, spelling);
            assert_eq!(expected, Expected::Proved);
            let mut question =
                Question::valid(&mut cx, p, &Config::default().with_samples(0)).unwrap();
            assert!(
                matches!(
                    question.solve(&mut cx, Limits::conflicts(100)).unwrap(),
                    Outcome::Proved(_)
                ),
                "{name}"
            );
            assert_eq!(
                question.stats().conflicts,
                0,
                "no search through a hash predicate is needed"
            );
        }
    }
}

#[test]
fn raw_dispatch_certificates_fit_a_constant_circuit_budget() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        for name in ["correlated-pair", "target-cut"] {
            let mut cx = Context::new();
            let (p, _) = claim(&mut cx, name, spelling);
            let cfg = Config::default()
                .with_simplify(false)
                .with_certificate(true)
                .with_samples(0)
                .with_max_nodes(1);
            let mut question = Question::valid(&mut cx, p, &cfg).unwrap();
            assert_eq!(question.stats().nodes, 1);
            assert_eq!(question.stats().vars, 1);
            let Outcome::Proved(Some(cert)) =
                question.solve(&mut cx, Limits::conflicts(0)).unwrap()
            else {
                panic!("outer Boolean structure must suffice for {name}");
            };
            cert.check().unwrap();
            assert!(matches!(
                prove::valid(&mut cx, p, &cfg.with_max_nodes(0)).unwrap(),
                Outcome::Unknown(Unknown::TooLarge { .. })
            ));
        }
    }
}

#[test]
fn systematic_small_samples_refute_full_width_cross_key_guards_in_original_symbols() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let (p, _) = claim(&mut cx, "cross-key-guards", spelling);
        let cfg = Config::default()
            .with_simplify(false)
            .with_certificate(true)
            .with_samples(65_536)
            .with_sample_mode(SampleMode::Small);
        let question = Question::valid(&mut cx, p, &cfg).unwrap();
        let Some(Outcome::Refuted(model)) = question.outcome() else {
            panic!("small witness not found")
        };
        let x = model
            .iter()
            .find(|(key, _)| *key == SymbolKey::from("x"))
            .unwrap()
            .1;
        assert_eq!(x.width(), Width::W64);
        assert_eq!(x.to_u64(), Some(CANDIDATE));
        assert_eq!(scalar_terms(x.to_u64().unwrap()), [0; 3]);
        assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());
        assert_eq!(question.stats().samples, (CANDIDATE / 64 + 1) * 64);
        assert_eq!(question.stats().vars, 0);
        assert_eq!(question.stats().conflicts, 0);
        assert!(
            cx.declared_known(cx.find_symbol(&SymbolKey::from("x")).unwrap())
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn word_level_samples_recover_cross_key_witnesses_without_building_a_circuit() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        for high_one in [false, true] {
            for secret in [0, 1, 63, 64, 255, 256, 1023, CANDIDATE, 65_535] {
                let expected = secret | if high_one { 1 << 63 } else { 0 };
                let mut cx = Context::new();
                let x = cx.symbol("x", Width::W64).unwrap();
                if high_one {
                    cx.declare_known(
                        x,
                        KnownBits::new(
                            BitVec::zero(Width::W64),
                            BitVec::from_u64(Width::W64, 1 << 63).unwrap(),
                        )
                        .unwrap(),
                    )
                    .unwrap();
                }
                let a = mixer(&mut cx, x, KEYS[0], spelling);
                let mut guard = cx.one(Width::W1).unwrap();
                for &key in &KEYS[1..] {
                    let b = mixer(&mut cx, x, key, spelling);
                    let pair = cx.xor(a, b).unwrap();
                    let salt = constant(&mut cx, scalar(KEYS[0], expected) ^ scalar(key, expected));
                    let equal = cx.eq(pair, salt).unwrap();
                    guard = cx.and(guard, equal).unwrap();
                }
                let exclusion = cx.not(guard).unwrap();
                let cfg = Config::default()
                    .with_simplify(false)
                    .with_certificate(true)
                    .with_samples(65_536)
                    .with_sample_mode(SampleMode::Small)
                    .with_word_sampling(true)
                    .with_max_nodes(0);
                let q = Question::valid(&mut cx, exclusion, &cfg).unwrap();
                let Some(Outcome::Refuted(model)) = q.outcome() else {
                    panic!("word witness missing for {expected:#x}");
                };
                assert_eq!(q.stats().nodes, 0);
                assert_eq!(q.stats().vars, 0);
                assert_eq!(q.stats().conflicts, 0);
                let value = model
                    .iter()
                    .find(|(key, _)| *key == SymbolKey::from("x"))
                    .unwrap()
                    .1;
                assert_eq!(value.width(), Width::W64);
                if high_one {
                    assert_eq!(value.bit(63), Some(true));
                }
                assert!(cx.eval(&[exclusion], &model[..]).unwrap()[0].is_zero());
                let value = value.to_u64().unwrap();
                for &key in &KEYS[1..] {
                    assert_eq!(
                        scalar(KEYS[0], value) ^ scalar(key, value),
                        scalar(KEYS[0], expected) ^ scalar(key, expected)
                    );
                }
            }
        }
    }
}

#[test]
fn reconstructed_word_sampling_recovers_byte_models_that_small_input_order_misses() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let (claim, _) = fixture::claim(&mut cx, "cross-key-guards-bytes", spelling);
        let cfg = Config::default()
            .with_simplify(false)
            .with_samples(65_536)
            .with_sample_mode(SampleMode::Small)
            .with_word_sampling(true)
            .with_max_nodes(0);
        let missed = Question::valid(&mut cx, claim, &cfg).unwrap();
        assert!(matches!(
            missed.outcome(),
            Some(Outcome::Unknown(Unknown::TooLarge { .. }))
        ));
        assert_eq!(missed.stats().samples, 65_536);
        let found = Question::valid(
            &mut cx,
            claim,
            &cfg.with_sample_mode(SampleMode::Words)
                .with_word_sampling(false),
        )
        .unwrap();
        let Some(Outcome::Refuted(model)) = found.outcome() else {
            panic!("numeric word witness was missed");
        };
        assert_eq!(model.len(), 8);
        assert_eq!(found.stats().nodes, 0);
        assert_eq!(found.stats().samples, 17_792);
        let mut value = 0;
        for i in 0..8 {
            let byte = model
                .iter()
                .find(|(key, _)| *key == SymbolKey::from(format!("byte{i}")))
                .unwrap()
                .1;
            assert_eq!(byte.width(), Width::W8);
            value |= byte.to_u64().unwrap() << (8 * i);
        }
        assert_eq!(value, CANDIDATE);
        assert_eq!(scalar_terms(value), [0; 3]);
        assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
    }
}

#[test]
fn independent_word_streams_recover_a_captured_dispatch_without_touching_other_words() {
    let mut cx = Context::new();
    let expression = include_str!("common/independent_words_dispatch.txt");
    let target = cx
        .parse(expression, &bitwright::ParseOptions::width(Width::W64))
        .unwrap();
    let expected = cx.constant_u64(Width::W64, 0x1403e8d04).unwrap();
    let claim = cx.ne(target, expected).unwrap();
    let cfg = Config::default()
        .with_simplify(false)
        .with_certificate(true)
        .with_samples(192)
        .with_sample_mode(SampleMode::Words)
        .with_max_nodes(0);
    let q = Question::valid(&mut cx, claim, &cfg).unwrap();
    let Some(Outcome::Refuted(model)) = q.outcome() else {
        panic!("an independent second-word witness must be sampled");
    };
    assert!(q.stats().samples <= 192);
    assert_eq!(q.stats().nodes, 0);
    assert_eq!(model.len(), 16);
    assert!(model.iter().all(|(_, v)| v.width() == Width::W8));
    for (key, value) in model {
        let expected = u64::from(*key == SymbolKey::from("byte16"));
        assert_eq!(value.to_u64(), Some(expected));
    }
    let values = cx.eval(&[claim, target], &model[..]).unwrap();
    assert!(values[0].is_zero());
    assert_eq!(values[1].to_u64(), Some(0x1403e8d04));
}

#[test]
fn low_two_bit_cross_key_cancellation_has_a_checked_native_certificate() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let a = mixer(&mut cx, x, KEYS[0], spelling);
        let b = mixer(&mut cx, x, KEYS[1], spelling);
        let pair = cx.xor(a, b).unwrap();
        let low = cx.extract(pair, 0, Width::new(2).unwrap()).unwrap();
        let correction = |cx: &mut Context, key: u64| {
            let k = constant(cx, key);
            let masked = cx.xor(x, k).unwrap();
            let h = cx.mul(k, masked).unwrap();
            let top = constant(cx, 60);
            let top = cx.bin(bitwright::BinOp::LShr, h, top).unwrap();
            let shift = constant(cx, 32);
            let hi = cx.bin(bitwright::BinOp::LShr, h, shift).unwrap();
            let r = cx.bin(bitwright::BinOp::LShr, hi, top).unwrap();
            cx.mul(k, r).unwrap()
        };
        let ra = correction(&mut cx, KEYS[0]);
        let rb = correction(&mut cx, KEYS[1]);
        let difference = constant(&mut cx, KEYS[0] ^ KEYS[1]);
        let expected = cx.xor(ra, rb).unwrap();
        let expected = cx.xor(expected, difference).unwrap();
        let expected = cx.extract(expected, 0, Width::new(2).unwrap()).unwrap();
        let claim = cx.eq(low, expected).unwrap();
        let cfg = Config::default()
            .with_simplify(false)
            .with_samples(0)
            .with_certificate(true);
        let mut question = Question::valid(&mut cx, claim, &cfg).unwrap();
        let Outcome::Proved(Some(cert)) = question.solve(&mut cx, Limits::conflicts(100)).unwrap()
        else {
            panic!("odd-key low-bit cancellation was not proved");
        };
        cert.check().unwrap();
    }
}

#[test]
fn masked_pair_candidate_is_replayed_without_asserting_uniqueness() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let (exclusion, _) = claim(&mut cx, "masked-pair-32", spelling);
        let (unique, _) = claim(&mut cx, "masked-pair-32-unique", spelling);
        let cfg = Config::default()
            .with_simplify(false)
            .with_samples(65_536)
            .with_sample_mode(SampleMode::Small);
        let question = Question::valid(&mut cx, exclusion, &cfg).unwrap();
        let Some(Outcome::Refuted(model)) = question.outcome() else {
            panic!("masked-pair candidate was not found");
        };
        assert_eq!(model[0].1.width(), Width::W32);
        assert_eq!(model[0].1.to_u64(), Some(CANDIDATE));
        assert_eq!(scalar_terms(CANDIDATE)[0] & !TARGET, 0);
        let values = cx.eval(&[exclusion, unique], &model[..]).unwrap();
        assert!(values[0].is_zero());
        assert!(!values[1].is_zero());
        // Finding this candidate establishes existence, not the uniqueness lemma.
        let open_cfg = cfg.with_samples(0).with_certificate(true);
        let mut uniqueness = Question::valid(&mut cx, unique, &open_cfg).unwrap();
        assert!(matches!(
            uniqueness.solve(&mut cx, Limits::conflicts(0)).unwrap(),
            Outcome::Unknown(Unknown::Budget { .. })
        ));
    }
}

#[test]
fn a_correlated_pair_can_be_excluded_while_the_key_alone_is_reachable() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let mixed = mixer(&mut cx, x, GOLDEN, spelling);
        let hash = constant(&mut cx, 0x1234);
        let p = cx.eq(mixed, hash).unwrap();
        let (target, key) = dispatch(&mut cx, p);
        let anchor = constant(&mut cx, ANCHOR);
        let selected_key = constant(&mut cx, KEYS[0]);
        let at_anchor = cx.eq(target, anchor).unwrap();
        let at_key = cx.eq(key, selected_key).unwrap();
        let pair = cx.and(at_anchor, at_key).unwrap();
        let pair_exclusion = cx.not(pair).unwrap();
        let key_exclusion = cx.not(at_key).unwrap();
        let cfg = Config::default().with_samples(0).with_max_conflicts(100);
        assert!(matches!(
            prove::valid(&mut cx, pair_exclusion, &cfg).unwrap(),
            Outcome::Proved(_)
        ));
        let Outcome::Refuted(model) = prove::valid(&mut cx, key_exclusion, &cfg).unwrap() else {
            panic!("the selected key has the concrete mixer preimage as a witness");
        };
        assert_eq!(
            cx.eval(&[pair_exclusion, key_exclusion], &model[..])
                .unwrap(),
            [BitVec::from_bool(true), BitVec::from_bool(false)]
        );
        assert_eq!(
            model
                .iter()
                .find(|(k, _)| *k == SymbolKey::from("x"))
                .unwrap()
                .1
                .to_u64(),
            Some(PREIMAGE)
        );
    }
}

#[test]
fn fingerprint_domain_forms_and_candidate_satisfy_exact_input_boundaries() {
    for spelling in [Spelling::Nested, Spelling::Compact] {
        let mut cx = Context::new();
        let narrow = cx.symbol("narrow", Width::W32).unwrap();
        let widened = cx.zext(narrow, Width::W64).unwrap();
        let declared = cx.symbol("declared", Width::W64).unwrap();
        let zeros = BitVec::from_u64(Width::W64, 0xffff_ffff_0000_0000).unwrap();
        cx.declare_known(
            declared,
            KnownBits::new(zeros, BitVec::zero(Width::W64)).unwrap(),
        )
        .unwrap();
        let full = cx.symbol("full", Width::W64).unwrap();
        let mask = constant(&mut cx, u32::MAX as u64);
        let masked = cx.and(full, mask).unwrap();
        let roots = [
            fingerprint(&mut cx, widened, spelling),
            fingerprint(&mut cx, declared, spelling),
            fingerprint(&mut cx, masked, spelling),
        ];
        for value in [0, CANDIDATE, u32::MAX as u64] {
            let env = [
                (
                    SymbolKey::from("narrow"),
                    BitVec::from_u64(Width::W32, value).unwrap(),
                ),
                (
                    SymbolKey::from("declared"),
                    BitVec::from_u64(Width::W64, value).unwrap(),
                ),
                (
                    SymbolKey::from("full"),
                    BitVec::from_u64(Width::W64, value | 0xa5a5_1234_0000_0000).unwrap(),
                ),
            ];
            let expected = BitVec::from_u64(Width::W64, scalar_fingerprint(value)).unwrap();
            assert_eq!(cx.eval(&roots, &env[..]).unwrap(), [expected; 3]);
        }
        assert!(cx.declared_known(full).unwrap().is_none());
        assert_eq!(cx.width(narrow).unwrap(), Width::W32);
        assert_eq!(cx.width(full).unwrap(), Width::W64);
    }
}

#[test]
#[ignore = "heavy: complete 2^32-input four-key fingerprint masked-pair enumeration; run with --release -- --ignored"]
fn fingerprint_nonzero_target_is_excluded_by_complete_32_bit_enumeration() {
    let mut candidates = Vec::new();
    for x in 0..1u64 << 32 {
        let first = scalar(KEYS[0], x) ^ scalar(KEYS[1], x) ^ SALTS[0];
        if first & !TARGET == 0 {
            candidates.push(x);
        }
    }
    assert_eq!(candidates, [CANDIDATE]);
    // Any full OR equality must satisfy the necessary masked-pair condition. Check the
    // entire original predicate at every candidate, rather than treating the mask as enough.
    for x in candidates {
        assert_ne!(scalar_fingerprint(x), TARGET);
    }
}

#[test]
#[ignore = "heavy: prepare two completely verified 2^32-input facts; run with --release -- --ignored"]
fn checked_finite_facts_settle_bounded_queries_and_keep_full_width_sources_open() {
    use bitwright::prove::finite::{CheckedPair, VerifyLimits};
    let limits = VerifyLimits {
        inputs: 1 << 32,
        candidates: 256,
    };
    let pair = CheckedPair::verify([KEYS[0], KEYS[1]], SALTS[0], !TARGET, 32, limits).unwrap();
    assert_eq!(pair.candidates(), &[CANDIDATE]);
    let cfg = Config::default()
        .with_simplify(false)
        .with_samples(0)
        .with_max_nodes(0);
    for spelling in [Spelling::Nested, Spelling::Compact] {
        for name in ["fingerprint-32", "masked-pair-32-unique", "fingerprint-64"] {
            let mut cx = Context::new();
            let (original, _) = claim(&mut cx, name, spelling);
            let before = cx
                .width(cx.find_symbol(&SymbolKey::from("x")).unwrap())
                .unwrap();
            let q =
                Question::valid_with_pairs(&mut cx, original, std::slice::from_ref(&pair), &cfg)
                    .unwrap();
            if name == "fingerprint-64" {
                assert!(matches!(q.outcome(), Some(Outcome::Unknown(_))));
            } else {
                assert!(matches!(q.outcome(), Some(Outcome::Proved(None))));
                assert_eq!(q.stats().nodes, 0);
            }
            let x = cx.find_symbol(&SymbolKey::from("x")).unwrap();
            assert_eq!(cx.width(x).unwrap(), before);
            assert!(cx.declared_known(x).unwrap().is_none());
        }
        for form in ["masked", "declared"] {
            let mut cx = Context::new();
            let input = cx.symbol("input", Width::W64).unwrap();
            let source = if form == "masked" {
                let mask = constant(&mut cx, u32::MAX as u64);
                cx.and(input, mask).unwrap()
            } else {
                cx.declare_known(
                    input,
                    KnownBits::new(
                        BitVec::from_u64(Width::W64, !u64::from(u32::MAX)).unwrap(),
                        BitVec::zero(Width::W64),
                    )
                    .unwrap(),
                )
                .unwrap();
                input
            };
            let fp = fingerprint(&mut cx, source, spelling);
            let target = constant(&mut cx, TARGET);
            let original = cx.ne(fp, target).unwrap();
            let q =
                Question::valid_with_pairs(&mut cx, original, std::slice::from_ref(&pair), &cfg)
                    .unwrap();
            assert!(matches!(q.outcome(), Some(Outcome::Proved(None))));
        }
    }
    // The ordinary API does not install or implicitly use any prepared fact.
    let mut cx = Context::new();
    let (original, _) = claim(&mut cx, "fingerprint-32", Spelling::Nested);
    let ordinary = Question::valid(&mut cx, original, &cfg).unwrap();
    assert!(matches!(ordinary.outcome(), Some(Outcome::Unknown(_))));

    let loaded =
        CheckedPair::verify(BOUNDED_PAIR_KEYS, BOUNDED_PAIR_SALT, u64::MAX, 32, limits).unwrap();
    assert!(loaded.candidates().is_empty());
    let mut cx = Context::new();
    let source = include_str!("common/bounded_load_dispatch.txt");
    let target = cx
        .parse(source, &bitwright::ParseOptions::width(Width::W64))
        .unwrap();
    let excluded = cx.constant_u64(Width::W64, 0x1403e8d04).unwrap();
    let original = cx.ne(target, excluded).unwrap();
    let original_symbols = cx.symbols_in(&[original]).unwrap();
    assert_eq!(original_symbols.len(), 52);
    let q =
        Question::valid_with_pairs(&mut cx, original, std::slice::from_ref(&loaded), &cfg).unwrap();
    assert!(matches!(q.outcome(), Some(Outcome::Proved(None))));
    assert_eq!(q.stats().nodes, 0);
    assert_eq!(cx.symbols_in(&[original]).unwrap(), original_symbols);
}

#[test]
#[ignore = "heavy: sixteen checked selector cases per hard query; run with --release -- --ignored --nocapture"]
fn selector_partitions_keep_full_domains_and_report_conditional_verdicts() {
    println!("query,selector,verdict,conflicts,propagations,vars");
    for name in ["fingerprint-32", "fingerprint-64", "masked-pair-32-unique"] {
        let mut cx = Context::new();
        let (original, expected) = claim(&mut cx, name, Spelling::Nested);
        let x = cx.find_symbol(&SymbolKey::from("x")).unwrap();
        let width = cx.width(x).unwrap();
        let widened = cx.zext(x, Width::W64).unwrap();
        let key = constant(&mut cx, KEYS[0]);
        let input = cx.xor(widened, key).unwrap();
        let h = cx.mul(key, input).unwrap();
        let sixty = constant(&mut cx, 60);
        let selector = cx.bin(bitwright::BinOp::LShr, h, sixty).unwrap();
        let maximum = constant(&mut cx, 15);
        let covered = cx.ule(selector, maximum).unwrap();
        let cfg = Config::default()
            .with_samples(0)
            .with_simplify(false)
            .with_certificate(true);
        // This range certificate establishes that the sixteen cases cover the original
        // domain. No declaration on x changes when selecting a case.
        let Outcome::Proved(Some(coverage)) = prove::valid(&mut cx, covered, &cfg).unwrap() else {
            panic!("the complete selector partition must have a checked range bound");
        };
        coverage.check().unwrap();
        let mut proved = 0;
        let mut refuted = 0;
        for value in 0..16 {
            let selected = constant(&mut cx, value);
            let condition = cx.eq(selector, selected).unwrap();
            let mut assumptions = Assumptions::new();
            assumptions.assume_true(&mut cx, condition).unwrap();
            let mut question =
                Question::valid_under(&mut cx, original, Some(&assumptions), &cfg).unwrap();
            let outcome = question
                .solve(
                    &mut cx,
                    Limits {
                        conflicts: 10_000,
                        propagations: 5_000_000,
                    },
                )
                .unwrap();
            let status = match outcome {
                Outcome::Proved(Some(certificate)) => {
                    certificate.check().unwrap();
                    proved += 1;
                    "case-proved"
                }
                Outcome::Refuted(model) => {
                    assert_ne!(expected, Expected::Proved);
                    let values = cx.eval(&[original, condition], &model[..]).unwrap();
                    assert!(values[0].is_zero() && !values[1].is_zero());
                    assert_eq!(model[0].1.width(), width);
                    refuted += 1;
                    "original-refuted-replayed"
                }
                Outcome::Unknown(why) => {
                    assert!(why.is_budget());
                    "unknown-budget"
                }
                other => panic!("conditional verdict lacked evidence: {other:?}"),
            };
            assert_eq!(cx.width(x).unwrap(), width);
            assert!(cx.declared_known(x).unwrap().is_none());
            let stats = question.stats();
            println!(
                "{name},{value},{status},{},{},{}",
                stats.conflicts, stats.propagations, stats.vars
            );
        }
        // This is a collection of conditional proofs, not one DRUP certificate of the
        // unsplit predicate. Unknown cases always keep the partition unresolved.
        println!(
            "partition-summary,{name},proved={proved},refuted={refuted},unknown={}",
            16 - proved - refuted
        );
    }
}

#[test]
#[ignore = "heavy: large cross-key circuits with bounded native SAT and resumed searches"]
fn cross_key_budget_exhaustion_is_explicit_and_escalation_reuses_the_question() {
    for name in ["fingerprint-32", "fingerprint-64", "cross-key-guards"] {
        let mut cx = Context::new();
        let (p, _) = claim(&mut cx, name, Spelling::Nested);
        let cfg = Config::default()
            .with_simplify(false)
            .with_samples(0)
            .with_max_nodes(4_000_000);
        let mut q = Question::valid(&mut cx, p, &cfg).unwrap();
        let nodes = q.stats().nodes;
        let mut result = Outcome::Unknown(Unknown::Budget {
            conflicts: 0,
            propagations: 0,
        });
        for _ in 0..3 {
            result = q.solve(&mut cx, Limits::conflicts(1)).unwrap();
            assert_eq!(q.stats().nodes, nodes);
            if !matches!(result, Outcome::Unknown(_)) {
                break;
            }
        }
        let spent = q.stats();
        match &result {
            Outcome::Unknown(why) => assert!(why.is_budget()),
            Outcome::Refuted(model) => {
                assert_ne!(
                    name, "fingerprint-32",
                    "the complete 32-bit domain excludes this target"
                );
                assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());
            }
            Outcome::Proved(_) => assert_ne!(
                name, "cross-key-guards",
                "the candidate refutes the guard exclusion"
            ),
            _ => panic!("unexpected outcome"),
        }
        drop(q);
        let mut once = Question::valid(&mut cx, p, &cfg).unwrap();
        let whole = once
            .solve(&mut cx, Limits::conflicts(spent.conflicts.max(1)))
            .unwrap();
        assert_eq!(
            std::mem::discriminant(&result),
            std::mem::discriminant(&whole)
        );
        assert_eq!(once.stats(), spent);
    }
}

#[test]
#[ignore = "heavy: four 2^32-input exhaustive decisions with circuit-simulation certificates; run with --release -- --ignored"]
fn narrow_original_queries_are_decided_by_certified_exhaustion() {
    let cfg = Config::default()
        .with_certificate(true)
        .with_samples(0)
        .with_simplify(false)
        .with_exhaustive_inputs(32);
    for spelling in [Spelling::Nested, Spelling::Compact] {
        for name in ["masked-pair-32-unique", "fingerprint-32", "masked-pair-32"] {
            let mut cx = Context::new();
            let (claim, expected) = claim(&mut cx, name, spelling);
            let q = Question::valid(&mut cx, claim, &cfg).unwrap();
            assert_eq!(q.stats().nodes > 0, expected == Expected::Proved, "{name}");
            match (q.outcome(), expected) {
                (Some(Outcome::Proved(Some(cert))), Expected::Proved) => {
                    let exhaustion = cert.exhaustion.as_ref().unwrap();
                    assert_eq!(exhaustion.inputs(), 32, "{name}");
                    cert.check().unwrap();
                }
                (Some(Outcome::Refuted(model)), Expected::Refuted) => {
                    // The unique masked-pair solution, replayed on the original predicate.
                    assert_eq!(model[0].1.to_u64(), Some(CANDIDATE));
                    assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
                }
                (other, _) => panic!("{name} {spelling:?}: {other:?}"),
            }
        }
        // A full-width source is beyond any enumeration and keeps the ordinary search.
        let mut cx = Context::new();
        let (claim, _) = claim(&mut cx, "fingerprint-64", spelling);
        let q = Question::valid(&mut cx, claim, &cfg.with_exhaustive_inputs(63)).unwrap();
        assert!(q.outcome().is_none());
        assert_eq!(q.stats().samples, 0);
    }
}
