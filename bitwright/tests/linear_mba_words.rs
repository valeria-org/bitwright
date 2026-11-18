mod common;

use bitwright::engine::{Engine, Phase, Strategy};
use bitwright::{BinOp, BitVec, CmpOp, Context, SymbolKey, UnOp, Width};
use common::{Rng, w};

fn engine(phase: Phase) -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::new("words", vec![phase]))
        .build()
        .unwrap()
}

#[test]
fn masked_extended_complements_on_actual_words() {
    let simplify = engine(Phase::LinearMba);
    let compare = engine(Phase::Compares);
    let mut rng = Rng(0x8d79_3072_7b23_0c84);
    // Both signature implementations, including a correction beyond the first limb.
    for (narrow, wide) in [(w(8), w(16)), (w(8), w(65)), (w(65), w(129))] {
        for signed in [false, true] {
            let mut cx = Context::new();
            let x = cx.symbol("x", narrow).unwrap();
            let y = cx.symbol("y", wide).unwrap();
            let not_x = cx.un(UnOp::Not, x).unwrap();
            let mask = cx.constant_u64(narrow, 15).unwrap();
            // This entire OR is an atom: inspecting its complement's syntax to determine
            // the high bits gives the opposite answer to evaluating over the actual atom.
            let a = cx.bin(BinOp::Or, not_x, mask).unwrap();
            let not_a = cx.un(UnOp::Not, a).unwrap();
            let mut extend = |e| {
                if signed {
                    cx.sext(e, wide).unwrap()
                } else {
                    cx.zext(e, wide).unwrap()
                }
            };
            let ea = extend(a);
            let ec = extend(not_a);
            let ac = cx.bin(BinOp::And, ec, y).unwrap();
            let aa = cx.bin(BinOp::And, ea, y).unwrap();
            let pair = cx.bin(BinOp::Add, ac, aa).unwrap();
            let low = BitVec::ones(narrow).zext(wide).unwrap();
            let k = cx.constant(&low).unwrap();
            let ky = cx.bin(BinOp::Mul, k, y).unwrap();
            let expr = cx.bin(BinOp::Add, pair, ky).unwrap();
            let out = simplify.simplify(&mut cx, expr).unwrap().expr;
            // Compares asks about the signature of the difference without rewriting either side.
            let neg_ky = cx.un(UnOp::Neg, ky).unwrap();
            let eq = cx.cmp(CmpOp::Eq, pair, neg_ky).unwrap();
            let eq_out = compare.simplify(&mut cx, eq).unwrap().expr;
            for sample in 0..34 {
                let (x, y) = match sample {
                    0 => (BitVec::zero(narrow), BitVec::one(wide)), // original witness: 256 at W16
                    1 => (BitVec::ones(narrow), BitVec::zero(wide)),
                    _ => (rng.bitvec(narrow), rng.bitvec(wide)),
                };
                let env = [(SymbolKey::from("x"), x), (SymbolKey::from("y"), y)];
                // Disjoint complementary masks cover all of y for sext, only its low bits for zext.
                let covered = if signed {
                    y
                } else {
                    BitVec::apply_bin(BinOp::And, &y, &low).unwrap()
                };
                let scaled = BitVec::apply_bin(BinOp::Mul, &low, &y).unwrap();
                let want = BitVec::apply_bin(BinOp::Add, &covered, &scaled).unwrap();
                let truth = BitVec::wrapping_from_u64(Width::W1, u64::from(want.is_zero()));
                assert_eq!(
                    cx.eval(&[expr, out, eq, eq_out], &env[..]).unwrap(),
                    [want, want, truth, truth],
                    "{narrow} -> {wide}, signed={signed}, x={x}, y={y}"
                );
            }
        }
    }
}

#[test]
fn random_sums_on_word_inputs_with_two_to_five_atoms() {
    let eng = engine(Phase::LinearMba);
    let mut rng = Rng(0x000d_241b_6573_a8c9);
    let names = ["x", "y", "z", "p", "q"];
    for n in 2..=5 {
        let mut changed = false;
        for bits in [3, 7, 15, 31, 64] {
            let width = w(bits);
            for case in 0..12 {
                let mut cx = Context::new();
                let mut atoms: Vec<_> = names[..n]
                    .iter()
                    .map(|&name| cx.symbol(name, width).unwrap())
                    .collect();
                let dependent = case % 2 != 0 && n >= 3;
                if dependent {
                    let three = cx.constant_u64(width, 3).unwrap();
                    let product = cx.bin(BinOp::Mul, atoms[0], three).unwrap();
                    atoms[n - 1] = cx.bin(BinOp::Add, product, atoms[1]).unwrap();
                }
                let mut expr = cx.zero(width).unwrap();
                let mut terms = Vec::new();
                for i in 0..=n {
                    let a = i % n;
                    let b = (a + 1 + rng.below((n - 1) as u64) as usize) % n;
                    let k = rng.next() | 1;
                    let op = rng.below(3);
                    let and = cx.bin(BinOp::And, atoms[a], atoms[b]).unwrap();
                    let sum = cx.bin(BinOp::Add, atoms[a], atoms[b]).unwrap();
                    let term = match op {
                        0 => {
                            let two = cx.constant_u64(width, 2).unwrap();
                            let double = cx.bin(BinOp::Mul, two, and).unwrap();
                            cx.bin(BinOp::Sub, sum, double).unwrap()
                        }
                        1 => cx.bin(BinOp::Sub, sum, and).unwrap(),
                        _ => cx.bin(BinOp::Sub, atoms[a], and).unwrap(),
                    };
                    let coeff = cx.constant(&BitVec::wrapping_from_u64(width, k)).unwrap();
                    let product = cx.bin(BinOp::Mul, coeff, term).unwrap();
                    expr = cx.bin(BinOp::Add, expr, product).unwrap();
                    terms.push((a, b, k, op));
                }
                let out = eng.simplify(&mut cx, expr).unwrap().expr;
                changed |= expr != out;
                for _ in 0..32 {
                    let mut vs: [u64; 5] = std::array::from_fn(|_| rng.next());
                    let env: Vec<_> = names[..n]
                        .iter()
                        .zip(vs)
                        .map(|(&s, v)| (SymbolKey::from(s), BitVec::wrapping_from_u64(width, v)))
                        .collect();
                    if dependent {
                        vs[n - 1] = vs[0].wrapping_mul(3).wrapping_add(vs[1]);
                    }
                    // These operators commute with reduction to `bits`; compute independently
                    // on native words, then compare both the original and the rewrite.
                    let mut expected = 0u64;
                    for &(a, b, k, op) in &terms {
                        let term = match op {
                            0 => vs[a] ^ vs[b],
                            1 => vs[a] | vs[b],
                            _ => vs[a] & !vs[b],
                        };
                        expected = expected.wrapping_add(k.wrapping_mul(term));
                    }
                    let want = BitVec::wrapping_from_u64(width, expected);
                    assert_eq!(
                        cx.eval(&[expr, out], &env[..]).unwrap(),
                        [want, want],
                        "n={n} bits={bits} case={case}"
                    );
                }
            }
        }
        assert!(changed, "no nonidentity rewrite with {n} atoms");
    }
}
