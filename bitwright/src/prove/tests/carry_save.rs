use super::*;
use bitwright_ref as reference;

fn check_product(width: u16, constant: Option<&reference::Bits>, swap: bool, seed: u64) {
    let mut rng = Rng(seed);
    let mut graph = Aig::new();
    let a: Vec<_> = (0..width).map(|_| graph.input()).collect();
    let b: Vec<_> = match constant {
        Some(c) => (0..width).map(|i| u32::from(c.bit(i))).collect(),
        None => (0..width).map(|_| graph.input()).collect(),
    };
    let product = if swap {
        blast::mul_carry_save(&mut graph, &b, &a)
    } else {
        blast::mul_carry_save(&mut graph, &a, &b)
    };
    let words: Vec<_> = (0..if constant.is_some() { width } else { width * 2 })
        .map(|_| rng.next())
        .collect();
    let evaluated = graph.eval_words(|i| words[i as usize]);
    for lane in 0..64 {
        let read = |bits: &[aig::L]| {
            let mut limbs = vec![0; usize::from(width).div_ceil(64)];
            for (i, &bit) in bits.iter().enumerate() {
                limbs[i / 64] |= ((Aig::word(&evaluated, bit) >> lane) & 1) << (i % 64);
            }
            reference::Bits::from_limbs(width, &limbs)
        };
        let want = reference::bin(reference::BinOp::Mul, &read(&a), &read(&b));
        for (bit, &literal) in product.iter().enumerate() {
            assert_eq!(
                Aig::word(&evaluated, literal) >> lane & 1 != 0,
                want.bit(bit as u16),
                "width={width}, swap={swap}, lane={lane}, bit={bit}"
            );
        }
    }
}

#[test]
fn carry_save_products_are_exhaustive_through_six_bits() {
    for width in 1..=6 {
        for constant in 0..1u64 << width {
            for swap in [false, true] {
                let mut graph = Aig::new();
                let a: Vec<_> = (0..width).map(|_| graph.input()).collect();
                let b = blast::small(width, constant);
                let product = if swap {
                    blast::mul_carry_save(&mut graph, &b, &a)
                } else {
                    blast::mul_carry_save(&mut graph, &a, &b)
                };
                let evaluated = graph.eval_words(|bit| {
                    (0..1u64 << width).fold(0, |word, x| word | ((x >> bit & 1) << x))
                });
                for x in 0..1u64 << width {
                    let want = (x * constant) & ((1 << width) - 1);
                    for (bit, &literal) in product.iter().enumerate() {
                        assert_eq!(Aig::word(&evaluated, literal) >> x & 1, want >> bit & 1);
                    }
                }
            }
        }
        let mut graph = Aig::new();
        let a: Vec<_> = (0..width).map(|_| graph.input()).collect();
        let b: Vec<_> = (0..width).map(|_| graph.input()).collect();
        let product = blast::mul_carry_save(&mut graph, &a, &b);
        for assignment in 0..1u64 << (2 * width) {
            let evaluated = graph.eval_all(|i| assignment >> i & 1 != 0);
            let mask = (1 << width) - 1;
            let want = ((assignment & mask) * (assignment >> width)) & mask;
            for (bit, &literal) in product.iter().enumerate() {
                assert_eq!(Aig::value(&evaluated, literal), want >> bit & 1 != 0);
            }
        }
    }
}

#[test]
fn carry_save_products_match_independent_wide_reference() {
    for width in [7, 16, 31, 32, 63, 64, 65, 129, 257] {
        check_product(width, None, false, u64::from(width));
    }
    for width in [7, 31, 64, 65, 129, 257, 512, 1024] {
        for limbs in [
            [0; 16],
            [1; 16],
            [u64::MAX; 16],
            [0xaaaa_aaaa_aaaa_aaaa; 16],
            [0xffff_0000_ffff_0001; 16],
            [0xc26a_114a_f502_712b; 16],
        ] {
            let constant = reference::Bits::from_limbs(width, &limbs);
            for swap in [false, true] {
                check_product(width, Some(&constant), swap, u64::from(width) ^ limbs[0]);
            }
        }
    }
}

#[test]
fn carry_save_products_preserve_fixed_bits_and_correlated_literals() {
    for width in [3u16, 8, 31, 65, 129] {
        let mut graph = Aig::new();
        let inputs: Vec<_> = (0..7).map(|_| graph.input()).collect();
        let a: Vec<_> = (0..usize::from(width))
            .map(|i| match i % 5 {
                0 => aig::FALSE,
                1 => aig::TRUE,
                _ => inputs[i % 7] ^ (i as u32 & 1),
            })
            .collect();
        let b: Vec<_> = (0..usize::from(width))
            .map(|i| match i % 4 {
                0 => aig::TRUE,
                _ => inputs[(i + 2) % 7] ^ (i as u32 >> 1 & 1),
            })
            .collect();
        let output = blast::mul_carry_save(&mut graph, &a, &b);
        for batch in 0..2 {
            let evaluated = graph.eval_words(|bit| small_sample(batch, bit));
            for lane in 0..64 {
                let read = |bits: &[aig::L]| {
                    let mut limbs = vec![0; usize::from(width).div_ceil(64)];
                    for (i, &l) in bits.iter().enumerate() {
                        limbs[i / 64] |= ((Aig::word(&evaluated, l) >> lane) & 1) << (i % 64);
                    }
                    reference::Bits::from_limbs(width, &limbs)
                };
                let want = reference::bin(reference::BinOp::Mul, &read(&a), &read(&b));
                for (bit, &l) in output.iter().enumerate() {
                    assert_eq!(
                        Aig::word(&evaluated, l) >> lane & 1 != 0,
                        want.bit(bit as u16)
                    );
                }
            }
        }
    }
}

#[test]
fn carry_save_native_certificates_and_original_symbol_models() {
    for bits in [4, 8, 65, 129] {
        let width = Width::new(bits).unwrap();
        let mut cx = Context::new();
        let x = cx.symbol("x", width).unwrap();
        let mut limbs = vec![0; usize::from(bits).div_ceil(64)];
        limbs[usize::from(bits - 1) / 64] = 1 << ((bits - 1) % 64);
        let high = BitVec::wrapping_from_limbs(width, &limbs);
        cx.declare_known(x, crate::KnownBits::new(BitVec::zero(width), high).unwrap())
            .unwrap();
        let key_value = BitVec::wrapping_from_limbs(width, &[0xff01]);
        let key = cx.constant(&key_value).unwrap();
        let product = cx.mul(x, key).unwrap();
        let chosen = BitVec::apply_bin(
            BinOp::Or,
            &high,
            &BitVec::wrapping_from_limbs(width, &[0x193]),
        )
        .unwrap();
        let target_value = BitVec::apply_bin(BinOp::Mul, &chosen, &key_value).unwrap();
        let target = cx.constant(&target_value).unwrap();
        let claim = cx.ne(product, target).unwrap();
        for xor3 in [false, true] {
            let cfg = Config::default()
                .with_simplify(false)
                .with_samples(0)
                .with_certificate(true)
                .with_carry_save_multiplication(true)
                .with_xor3_encoding(xor3);
            let mut whole = Question::valid(&mut cx, claim, &cfg).unwrap();
            let Outcome::Refuted(expected) =
                whole.solve(&mut cx, Limits::conflicts(1_000)).unwrap()
            else {
                panic!("odd product must have a model");
            };
            assert!(cx.eval(&[claim], &expected[..]).unwrap()[0].is_zero());
            assert_eq!(expected[0].1.bit(bits - 1), Some(true));
            let mut stepped = Question::valid(&mut cx, claim, &cfg).unwrap();
            loop {
                let before = stepped.stats();
                match stepped
                    .solve(
                        &mut cx,
                        Limits {
                            conflicts: u64::MAX,
                            propagations: 1,
                        },
                    )
                    .unwrap()
                {
                    Outcome::Unknown(_) => {
                        assert!(stepped.stats().propagations - before.propagations <= 1)
                    }
                    Outcome::Refuted(actual) => {
                        assert_eq!(actual, expected);
                        break;
                    }
                    other => panic!("unexpected product result: {other:?}"),
                }
            }
            assert_eq!(stepped.stats(), whole.stats());
            // Fully constrained products test certificates without asking SAT to prove a
            // second multiplier circuit equivalent to the first.
            let value = cx.constant(&expected[0].1).unwrap();
            let at_value = cx.eq(x, value).unwrap();
            let product_matches = cx.eq(product, target).unwrap();
            let not_at_value = cx.not(at_value).unwrap();
            let implication = cx.or(not_at_value, product_matches).unwrap();
            let Outcome::Proved(Some(cert)) = valid(&mut cx, implication, &cfg).unwrap() else {
                panic!("fixed product should be provable");
            };
            cert.check().unwrap();
        }
    }
}
