use bitwright::engine::Engine;
use bitwright::rules::{RuleProgram, builtin_sources};
use bitwright::{BinOp, BitVec, Context, FnEnv, ParseOptions, SymbolKey, Width};
use bitwright_ref as r;

#[test]
fn guarded_examples_are_reached_by_the_default_engine() {
    let program = RuleProgram::compile(builtin_sources()[0].1).unwrap();
    let engine = Engine::standard();
    let mut count = 0;
    for rule in program
        .rules()
        .iter()
        .filter(|r| r.name.starts_with("core.guarded_recovery"))
    {
        for (input, reference) in &rule.examples {
            let mut cx = Context::new();
            let options = ParseOptions::width(Width::W8);
            let input = cx.parse(input, &options).unwrap();
            let reference = cx.parse(reference, &options).unwrap();
            let output = engine.simplify(&mut cx, input).unwrap().expr;
            let expected = engine.simplify(&mut cx, reference).unwrap().expr;
            assert_eq!(
                output,
                expected,
                "{}: {} != {}",
                rule.name,
                cx.display(output),
                cx.display(expected)
            );
            count += 1;
        }
    }
    assert_eq!(count, 30);
}

#[test]
fn signed_negation_does_not_cancel_without_the_overflow_guards() {
    let mut cx = Context::new();
    let options = ParseOptions::width(Width::W8);
    let input = cx.parse("-x <s -y", &options).unwrap();
    let unsound = cx.parse("y <s x", &options).unwrap();
    let output = Engine::standard().simplify(&mut cx, input).unwrap().expr;
    let env = [
        (SymbolKey::from("x"), BitVec::smin(Width::W8)),
        (SymbolKey::from("y"), BitVec::zero(Width::W8)),
    ];
    let values = cx.eval(&[input, output, unsound], env.as_slice()).unwrap();
    assert_eq!(values[0], values[1]);
    assert_ne!(values[0], values[2]);
}

fn check_extract(width: u16, count: u64, lo: u16, len: u16, samples: &[Vec<u64>]) {
    let mut cx = Context::new();
    let w = Width::new(width).unwrap();
    let x = cx.symbol("x", w).unwrap();
    let k = cx.constant(&BitVec::wrapping_from_u64(w, count)).unwrap();
    let shifted = cx.bin(BinOp::LShr, x, k).unwrap();
    let output = cx.extract(shifted, lo, Width::new(len).unwrap()).unwrap();
    let shift_term = r::Term::Bin(
        r::BinOp::LShr,
        Box::new(r::Term::Var(0, width)),
        Box::new(r::Term::Const(r::Bits::from_u128(width, count.into()))),
    );
    let reference = r::Term::Extract(Box::new(shift_term.clone()), lo, len);
    let one = cx.constant(&BitVec::one(w)).unwrap();
    let bit_test = cx.bin(BinOp::And, shifted, one).unwrap();
    let bit_reference = r::Term::Bin(
        r::BinOp::And,
        Box::new(shift_term),
        Box::new(r::Term::Const(r::Bits::from_u128(width, 1))),
    );
    for sample in samples {
        let value = BitVec::wrapping_from_limbs(w, sample);
        let actual = cx
            .eval(&[output], &FnEnv(|_: &SymbolKey, _: Width| Some(value)))
            .unwrap()[0];
        let expected = reference
            .eval(&[r::Bits::from_limbs(width, sample)])
            .unwrap();
        assert_eq!(
            actual.limbs(),
            expected.to_limbs(),
            "W={width} count={count} lo={lo} len={len}"
        );
        let bit = cx
            .eval(&[bit_test], &FnEnv(|_: &SymbolKey, _: Width| Some(value)))
            .unwrap()[0];
        assert_eq!(
            bit.limbs(),
            bit_reference
                .eval(&[r::Bits::from_limbs(width, sample)])
                .unwrap()
                .to_limbs()
        );
    }
}

#[test]
fn extract_after_logical_shift_matches_the_independent_evaluator() {
    for width in 1..=6_u16 {
        let values: Vec<_> = (0..1_u64 << width).map(|v| vec![v]).collect();
        for count in 0..=(2 * u64::from(width)).min((1_u64 << width) - 1) {
            for lo in 0..width {
                for len in 1..=width - lo {
                    check_extract(width, count, lo, len, &values);
                }
            }
        }
    }
    for width in [33, 40, 63, 64, 65, 96, 127, 128, 512] {
        let samples = vec![vec![0; 8], vec![u64::MAX; 8], vec![0x87654321abcdef01; 8]];
        for count in [
            0,
            1,
            u64::from(width - 1),
            u64::from(width),
            u64::from(width + 1),
        ] {
            for (lo, len) in [(0, 1), (0, width - 1), (1, width - 1), (width - 1, 1)] {
                check_extract(width, count, lo, len, &samples);
            }
        }
    }
}

#[test]
fn huge_shift_counts_stay_zero_when_extracted() {
    let mut cx = Context::new();
    let width = Width::new(128).unwrap();
    let x = cx.symbol("x", width).unwrap();
    let count = cx
        .constant(&BitVec::from_u128(width, 1_u128 << 100).unwrap())
        .unwrap();
    let shifted = cx.bin(BinOp::LShr, x, count).unwrap();
    let output = cx.extract(shifted, 3, Width::new(7).unwrap()).unwrap();
    assert_eq!(
        cx.as_const(output).unwrap(),
        Some(BitVec::zero(Width::new(7).unwrap()))
    );
}

#[test]
fn adjacent_constant_concat_tails_match_the_independent_evaluator() {
    for (h, m, l) in [(4, 2, 2), (64, 33, 31), (128, 65, 63), (256, 128, 128)] {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::new(h).unwrap()).unwrap();
        let a = BitVec::wrapping_from_limbs(Width::new(m).unwrap(), &[0xa54df012edab9876; 8]);
        let b = BitVec::wrapping_from_limbs(Width::new(l).unwrap(), &[0x873612abf309be64; 8]);
        let ac = cx.constant(&a).unwrap();
        let bc = cx.constant(&b).unwrap();
        let first = cx.concat(x, ac).unwrap();
        let output = cx.concat(first, bc).unwrap();
        assert_eq!(cx.tree_size(output).unwrap(), 3);
        let reference = r::Term::Concat(
            Box::new(r::Term::Concat(
                Box::new(r::Term::Var(0, h)),
                Box::new(r::Term::Const(r::Bits::from_limbs(m, a.limbs()))),
            )),
            Box::new(r::Term::Const(r::Bits::from_limbs(l, b.limbs()))),
        );
        for limbs in [[0; 8], [u64::MAX; 8], [0x8765adca11223344; 8]] {
            let value = BitVec::wrapping_from_limbs(Width::new(h).unwrap(), &limbs);
            let got = cx
                .eval(&[output], &FnEnv(|_: &SymbolKey, _: Width| Some(value)))
                .unwrap()[0];
            assert_eq!(
                got.limbs(),
                reference
                    .eval(&[r::Bits::from_limbs(h, &limbs)])
                    .unwrap()
                    .to_limbs()
            );
        }
    }
}
