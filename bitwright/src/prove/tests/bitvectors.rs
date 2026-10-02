//! Bit-blasting against the independent bit-serial reference, with no simplifier, sampling
//! heuristic or SAT model used as the oracle. Circuits are evaluated on up to 64 lanes at once.

use super::*;
use crate::testutil::{ref_bin, ref_cmp, ref_un};
use bitwright_ref as reference;

struct Circuit {
    aig: Aig,
    output: Vec<aig::L>,
    symbols: Vec<(SymbolKey, Vec<aig::L>)>,
    description: String,
}

impl Circuit {
    fn new(cx: &mut Context, root: Expr) -> Self {
        let id = cx.id(root).unwrap();
        let mut blaster = Blaster::new(cx, usize::MAX);
        let output = blaster.blast(id).unwrap();
        let symbols = blaster.symbols.clone();
        let aig = core::mem::take(&mut blaster.g);
        drop(blaster);
        let symbols = symbols
            .into_iter()
            .map(|(id, bits)| {
                let symbol = cx.symbol_id(cx.handle(id)).unwrap().unwrap();
                (cx.symbol_key(symbol).unwrap().clone(), bits)
            })
            .collect();
        Self {
            aig,
            output,
            symbols,
            description: cx.display(root).to_string(),
        }
    }

    fn check(&self, inputs: &[(SymbolKey, Vec<BitVec>)], expected: &[reference::Bits]) {
        assert!(!expected.is_empty() && expected.len() <= 64);
        let mut words = Vec::new();
        for (key, bits) in &self.symbols {
            let values = &inputs.iter().find(|(k, _)| k == key).unwrap().1;
            assert_eq!(values.len(), expected.len());
            for (bit, &literal) in bits.iter().enumerate() {
                // Fixed declared bits are constants, not circuit inputs.
                if literal <= aig::TRUE {
                    continue;
                }
                let word = values.iter().enumerate().fold(0u64, |word, (lane, value)| {
                    word | (u64::from(value.bit(bit as u16) == Some(true)) << lane)
                });
                words.push(word);
            }
        }
        let evaluated = self.aig.eval_words(|input| words[input as usize]);
        for (lane, want) in expected.iter().enumerate() {
            assert_eq!(self.output.len(), usize::from(want.width()));
            for (bit, &literal) in self.output.iter().enumerate() {
                let got = Aig::word(&evaluated, literal) >> lane & 1 != 0;
                assert_eq!(
                    got,
                    want.bit(bit as u16),
                    "{}, lane {lane}, bit {bit}",
                    self.description
                );
            }
        }
    }
}

fn reference_value(value: BitVec) -> reference::Bits {
    reference::Bits::from_limbs(value.width().bits(), value.limbs())
}

#[test]
fn correlated_shift_counts_match_reference_with_signs_duplicates_and_overshifts() {
    let mut rng = Rng(0xc011a7ed);
    for width in [1u16, 3, 4, 7, 16, 31, 64, 65, 129, 512, 1024] {
        for count_support in [1usize, 4, 5] {
            for left in [false, true] {
                for signed in [false, true] {
                    let mut graph = Aig::new();
                    let inputs: Vec<_> = (0..8).map(|_| graph.input()).collect();
                    let data: Vec<_> = (0..usize::from(width))
                        .map(|i| match i % 7 {
                            0 => aig::FALSE,
                            1 => aig::TRUE,
                            _ => inputs[i % inputs.len()] ^ (i as u32 & 1),
                        })
                        .collect();
                    for large_count in [false, true] {
                        let count: Vec<_> = (0..usize::from(width))
                            .map(|i| {
                                if i < count_support || i == count_support + 1 {
                                    inputs[i % count_support] ^ (i as u32 >> 1 & 1)
                                } else if large_count && i + 1 == usize::from(width) {
                                    aig::TRUE
                                } else {
                                    aig::FALSE
                                }
                            })
                            .collect();
                        let fill = if signed && !left {
                            data[data.len() - 1]
                        } else {
                            aig::FALSE
                        };
                        let output = blast::shift(&mut graph, &data, &count, left, fill);
                        for _ in 0..2 {
                            let words: Vec<_> = (0..8).map(|_| rng.next()).collect();
                            let evaluated = graph.eval_words(|i| words[i as usize]);
                            for lane in 0..64 {
                                let operand = |bits: &[aig::L]| {
                                    let mut limbs = vec![0u64; usize::from(width).div_ceil(64)];
                                    for (i, &l) in bits.iter().enumerate() {
                                        limbs[i / 64] |=
                                            ((Aig::word(&evaluated, l) >> lane) & 1) << (i % 64);
                                    }
                                    reference::Bits::from_limbs(width, &limbs)
                                };
                                let op = if left {
                                    reference::BinOp::Shl
                                } else if signed {
                                    reference::BinOp::AShr
                                } else {
                                    reference::BinOp::LShr
                                };
                                let want = reference::bin(op, &operand(&data), &operand(&count));
                                for (bit, &l) in output.iter().enumerate() {
                                    assert_eq!(
                                        Aig::word(&evaluated, l) >> lane & 1 != 0,
                                        want.bit(bit as u16),
                                        "width={width}, support={count_support}, left={left}, signed={signed}, large={large_count}, bit={bit}"
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn self_selected_shift_folds_its_high_bits_for_both_spellings() {
    for compact in [false, true] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W64).unwrap();
        let thirty_two = cx.constant_u64(Width::W64, 32).unwrap();
        let sixty = cx.constant_u64(Width::W64, 60).unwrap();
        let count = cx.bin(BinOp::LShr, x, sixty).unwrap();
        let shifted = if compact {
            let count = cx.add(count, thirty_two).unwrap();
            cx.bin(BinOp::LShr, x, count).unwrap()
        } else {
            let hi = cx.bin(BinOp::LShr, x, thirty_two).unwrap();
            cx.bin(BinOp::LShr, hi, count).unwrap()
        };
        let circuit = Circuit::new(&mut cx, shifted);
        assert!(circuit.output[28..].iter().all(|&l| l == aig::FALSE));
        let bound = cx.constant_u64(Width::W64, 1 << 28).unwrap();
        let claim = cx.ult(shifted, bound).unwrap();
        let cfg = Config::default()
            .with_simplify(false)
            .with_samples(0)
            .with_certificate(true);
        let mut question = Question::valid(&mut cx, claim, &cfg).unwrap();
        let Outcome::Proved(Some(cert)) = question.solve(&mut cx, Limits::conflicts(0)).unwrap()
        else {
            panic!("correlated shift bound was not folded");
        };
        cert.check().unwrap();
        assert_eq!(question.stats().conflicts, 0);
    }
}

fn check_constant_product(width: u16, constant: &reference::Bits, values: &[reference::Bits]) {
    for constant_on_left in [false, true] {
        let mut graph = Aig::new();
        let input: Vec<_> = (0..width).map(|_| graph.input()).collect();
        let fixed: Vec<_> = (0..width)
            .map(|i| {
                if constant.bit(i) {
                    aig::TRUE
                } else {
                    aig::FALSE
                }
            })
            .collect();
        let output = if constant_on_left {
            blast::mul(&mut graph, &fixed, &input)
        } else {
            blast::mul(&mut graph, &input, &fixed)
        };
        for batch in values.chunks(64) {
            let evaluated = graph.eval_words(|bit| {
                batch.iter().enumerate().fold(0, |word, (lane, value)| {
                    word | (u64::from(value.bit(bit as u16)) << lane)
                })
            });
            for (lane, value) in batch.iter().enumerate() {
                let want = reference::bin(reference::BinOp::Mul, value, constant);
                for (bit, &literal) in output.iter().enumerate() {
                    assert_eq!(
                        Aig::word(&evaluated, literal) >> lane & 1 != 0,
                        want.bit(bit as u16),
                        "{width}-bit constant {constant:?}, input {value:?}, bit {bit}"
                    );
                }
            }
        }
    }
}

#[test]
fn constant_multiplication_matches_reference_exhaustively_through_six_bits() {
    for width in 1..=6 {
        let values: Vec<_> = (0..1u128 << width)
            .map(|v| reference::Bits::from_u128(width, v))
            .collect();
        for constant in &values {
            check_constant_product(width, constant, &values);
        }
    }
}

#[test]
fn constant_products_cover_dense_digits_terminal_carry_and_internal_wide_words() {
    for width in [7, 8, 31, 32, 63, 64, 65, 127, 129, 255, 257, 512, 1024] {
        let constants = [
            [0; 16],
            [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
            [u64::MAX; 16],
            [0xaaaa_aaaa_aaaa_aaaa; 16],
            [0x5555_5555_5555_5555; 16],
            [0x9e37_79b9_7f4a_7c15; 16],
            [0xffff_0000_ffff_0001; 16],
        ];
        let values: Vec<_> = constants
            .iter()
            .map(|limbs| reference::Bits::from_limbs(width, limbs))
            .collect();
        for constant in &values {
            check_constant_product(width, constant, &values);
        }
    }
}

#[test]
fn constant_products_preserve_fixed_upper_biases_and_narrow_input_domains() {
    for bits in [32, 64, 65, 129, 257, 512] {
        let w = Width::new(bits).unwrap();
        let narrow = Width::new(bits / 2).unwrap();
        let low_mask = BitVec::zext(&BitVec::ones(narrow), w).unwrap();
        let high_mask = BitVec::apply_un(UnOp::Not, &low_mask).unwrap();
        let key = BitVec::wrapping_from_limbs(w, &[0x9e37_79b9_7f4a_7c15; 8]);
        let bias = BitVec::apply_bin(BinOp::And, &key, &high_mask).unwrap();
        let zeros = BitVec::apply_bin(BinOp::Xor, &bias, &high_mask).unwrap();
        let mut cx = Context::new();
        let x = cx.symbol("x", w).unwrap();
        cx.declare_known(x, crate::KnownBits::new(zeros, bias).unwrap())
            .unwrap();
        let k = cx.constant(&key).unwrap();
        let product = cx.mul(x, k).unwrap();
        let circuit = Circuit::new(&mut cx, product);
        let values: Vec<_> = boundary_values(narrow)
            .iter()
            .map(|value| {
                let low = BitVec::zext(value, w).unwrap();
                BitVec::apply_bin(BinOp::Or, &low, &bias).unwrap()
            })
            .collect();
        let expected: Vec<_> = values
            .iter()
            .map(|value| {
                reference::bin(
                    reference::BinOp::Mul,
                    &reference_value(*value),
                    &reference_value(key),
                )
            })
            .collect();
        circuit.check(&[(SymbolKey::from("x"), values)], &expected);

        let y = cx.symbol("y", narrow).unwrap();
        let wide = cx.zext(y, w).unwrap();
        let biased = cx.xor(wide, k).unwrap();
        let product = cx.mul(biased, k).unwrap();
        let circuit = Circuit::new(&mut cx, product);
        let values = boundary_values(narrow);
        let expected: Vec<_> = values
            .iter()
            .map(|value| {
                let wide = reference::zext(&reference_value(*value), bits);
                let biased = reference::bin(reference::BinOp::Xor, &wide, &reference_value(key));
                reference::bin(reference::BinOp::Mul, &biased, &reference_value(key))
            })
            .collect();
        circuit.check(&[(SymbolKey::from("y"), values)], &expected);
    }
}

fn boundary_values(w: Width) -> Vec<BitVec> {
    vec![
        BitVec::zero(w),
        BitVec::one(w),
        BitVec::ones(w),
        BitVec::smin(w),
        BitVec::smax(w),
        BitVec::wrapping_from_limbs(w, &[0xaaaa_aaaa_aaaa_aaaa; 8]),
        BitVec::wrapping_from_limbs(w, &[0x5555_5555_5555_5555; 8]),
    ]
}

fn check_pairs(w: Width, pairs: &[(BitVec, BitVec)]) {
    let mut cx = Context::new();
    let x = cx.symbol("x", w).unwrap();
    let y = cx.symbol("y", w).unwrap();
    for op in BinOp::ALL {
        let expression = cx.bin(op, x, y).unwrap();
        let circuit = Circuit::new(&mut cx, expression);
        for batch in pairs.chunks(64) {
            let expected: Vec<_> = batch
                .iter()
                .map(|&(a, b)| {
                    reference::bin(ref_bin(op), &reference_value(a), &reference_value(b))
                })
                .collect();
            circuit.check(
                &[
                    (
                        SymbolKey::from("x"),
                        batch.iter().map(|&(a, _)| a).collect(),
                    ),
                    (
                        SymbolKey::from("y"),
                        batch.iter().map(|&(_, b)| b).collect(),
                    ),
                ],
                &expected,
            );
        }
    }
    for op in CmpOpExt::ALL {
        let expression = cx.cmp(op, x, y).unwrap();
        let circuit = Circuit::new(&mut cx, expression);
        for batch in pairs.chunks(64) {
            let expected: Vec<_> = batch
                .iter()
                .map(|&(a, b)| {
                    reference::Bits::from_u128(
                        1,
                        u128::from(reference::cmp(
                            ref_cmp(op),
                            &reference_value(a),
                            &reference_value(b),
                        )),
                    )
                })
                .collect();
            circuit.check(
                &[
                    (
                        SymbolKey::from("x"),
                        batch.iter().map(|&(a, _)| a).collect(),
                    ),
                    (
                        SymbolKey::from("y"),
                        batch.iter().map(|&(_, b)| b).collect(),
                    ),
                ],
                &expected,
            );
        }
    }
    for op in UnOp::ALL {
        if op == UnOp::Bswap && !w.bits().is_multiple_of(8) {
            continue;
        }
        let expression = cx.un(op, x).unwrap();
        let circuit = Circuit::new(&mut cx, expression);
        for batch in pairs.chunks(64) {
            let values: Vec<_> = batch.iter().map(|&(a, _)| a).collect();
            let expected: Vec<_> = values
                .iter()
                .map(|&a| reference::un(ref_un(op), &reference_value(a)).unwrap())
                .collect();
            circuit.check(&[(SymbolKey::from("x"), values)], &expected);
        }
    }
}

#[test]
fn every_integer_operator_and_comparison_exhaustively_at_small_widths() {
    for bits in 1..=4 {
        let w = Width::new(bits).unwrap();
        let mut pairs = Vec::new();
        for a in 0..1u64 << bits {
            for b in 0..1u64 << bits {
                pairs.push((
                    BitVec::from_u64(w, a).unwrap(),
                    BitVec::from_u64(w, b).unwrap(),
                ));
            }
        }
        check_pairs(w, &pairs);
    }
}

fn boundary_suite(widths: &[u16]) {
    let mut rng = Rng(0xb175_5a7e);
    for &bits in widths {
        let w = Width::new(bits).unwrap();
        let boundaries = boundary_values(w);
        let mut pairs: Vec<_> = boundaries
            .iter()
            .flat_map(|&a| boundaries.iter().map(move |&b| (a, b)))
            .collect();
        // Counts at and across the operand width and limb boundaries, including a high limb
        // that a mistaken truncation of a shift/rotation amount would lose.
        for count in [bits - 1, bits, bits + 1, 63, 64, 65, 127, 128, 129] {
            for value in [BitVec::ones(w), BitVec::smin(w)] {
                pairs.push((value, BitVec::wrapping_from_u64(w, u64::from(count))));
            }
        }
        for bit in [63, 64, 127, 128, 255, 256, 511] {
            if bit < bits {
                let mut limbs = [0; 8];
                limbs[usize::from(bit / 64)] = 1 << (bit % 64);
                pairs.push((BitVec::ones(w), BitVec::wrapping_from_limbs(w, &limbs)));
            }
        }
        for _ in 0..8 {
            let a = std::array::from_fn::<_, 8, _>(|_| rng.next());
            let b = std::array::from_fn::<_, 8, _>(|_| rng.next());
            pairs.push((
                BitVec::wrapping_from_limbs(w, &a),
                BitVec::wrapping_from_limbs(w, &b),
            ));
        }
        check_pairs(w, &pairs);
    }
}

#[test]
fn every_integer_operator_at_sign_carry_and_limb_boundaries() {
    boundary_suite(&[7, 8, 15, 16, 31, 32, 63, 64, 65, 127, 128, 129]);
}

#[test]
#[ignore = "heavy: 255–512-bit circuits against the bit-serial reference; run with --release -- --ignored"]
fn every_integer_operator_at_large_width_boundaries() {
    boundary_suite(&[255, 256, 257, 511, 512]);
}

#[test]
fn mixed_width_casts_slices_concats_and_conditional_dags() {
    for (a_bits, b_bits, wide_bits) in [
        (1, 2, 3),
        (7, 9, 33),
        (31, 33, 65),
        (63, 65, 129),
        (127, 129, 257),
        (255, 257, 512),
    ] {
        let mut cx = Context::new();
        let a = cx.symbol("a", Width::new(a_bits).unwrap()).unwrap();
        let b = cx.symbol("b", Width::new(b_bits).unwrap()).unwrap();
        let wide = Width::new(wide_bits).unwrap();
        let signed = cx.sext(a, wide).unwrap();
        let unsigned = cx.zext(b, wide).unwrap();
        let cond = cx.slt(signed, unsigned).unwrap();
        let sum = cx.add(signed, unsigned).unwrap();
        let xor = cx.xor(signed, unsigned).unwrap();
        let select = cx.select(cond, sum, xor).unwrap();
        let length = (wide_bits - a_bits).min(wide_bits / 2);
        let lo = wide_bits - length;
        let slice = cx.extract(select, lo, Width::new(length).unwrap()).unwrap();
        let root = cx.concat(slice, a).unwrap();
        let circuit = Circuit::new(&mut cx, root);
        let av = boundary_values(Width::new(a_bits).unwrap());
        let bv = boundary_values(Width::new(b_bits).unwrap());
        let mut values_a = Vec::new();
        let mut values_b = Vec::new();
        let mut expected = Vec::new();
        for a in &av {
            for b in &bv {
                let ra = reference_value(*a);
                let sa = reference::sext(&ra, wide_bits);
                let ub = reference::zext(&reference_value(*b), wide_bits);
                let choose = reference::cmp(reference::CmpOp::Slt, &sa, &ub);
                let selected = reference::bin(
                    if choose {
                        reference::BinOp::Add
                    } else {
                        reference::BinOp::Xor
                    },
                    &sa,
                    &ub,
                );
                expected.push(reference::concat(
                    &reference::extract(&selected, lo, length),
                    &ra,
                ));
                values_a.push(*a);
                values_b.push(*b);
            }
        }
        circuit.check(
            &[
                (SymbolKey::from("a"), values_a),
                (SymbolKey::from("b"), values_b),
            ],
            &expected,
        );
    }
}
