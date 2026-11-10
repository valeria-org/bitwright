//! Pass tests: soundness (exhaustive at small widths, sampled wide), canonical results on
//! masking fixtures, idempotence, caps, and the commit rule.

use crate::engine::tests::{equivalent, generator};
use crate::engine::{Budget, End, Engine, Hooks, Phase, Run, Strategy, Verify};
use crate::testutil::{Gen, Rng};
use crate::{
    Assumptions, BinOp, BitVec, CmpOpExt, Context, Expr, FnEnv, ParseOptions, UnOp, Width,
    fp::FpFormat,
};

/// An engine running `phases` with the default verification: the tests' own equivalence
/// checks are the oracle (strict verification would reject a wrong rewrite before any test
/// could see it).
fn engine(phases: Vec<Phase>) -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::new("t", phases))
        .build()
        .unwrap()
}

/// A random expression in the linear fragment over a few atoms (symbols, and non-linear
/// compounds of them), with constants.
fn linear_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 4) {
        return match g.rng.below(5) {
            0 => {
                let v = g.constant(w);
                cx.constant(&v).unwrap()
            }
            1 => {
                let a = cx.symbol("a", width).unwrap();
                let b = cx.symbol("b", width).unwrap();
                cx.bin(BinOp::Mul, a, b).unwrap()
            }
            2 => {
                let a = cx.symbol("a", width).unwrap();
                let c = cx.symbol("c", width).unwrap();
                cx.bin(BinOp::And, a, c).unwrap()
            }
            k => cx.symbol(["a", "b", "c"][k as usize - 2], width).unwrap(),
        };
    }
    let d = depth - 1;
    match g.rng.below(8) {
        0 | 1 => {
            let (x, y) = (linear_expr(g, cx, w, d), linear_expr(g, cx, w, d));
            cx.bin(BinOp::Add, x, y).unwrap()
        }
        2 => {
            let (x, y) = (linear_expr(g, cx, w, d), linear_expr(g, cx, w, d));
            cx.bin(BinOp::Sub, x, y).unwrap()
        }
        3 => {
            let x = linear_expr(g, cx, w, d);
            cx.un(
                if g.rng.chance(1, 2) {
                    UnOp::Neg
                } else {
                    UnOp::Not
                },
                x,
            )
            .unwrap()
        }
        4 => {
            let x = linear_expr(g, cx, w, d);
            let k = g.constant(w);
            let k = cx.constant(&k).unwrap();
            cx.bin(BinOp::Mul, x, k).unwrap()
        }
        5 => {
            let x = linear_expr(g, cx, w, d);
            let k = cx
                .constant_u64(width, g.rng.below(u64::from(w) + 1))
                .unwrap();
            cx.bin(BinOp::Shl, x, k).unwrap()
        }
        _ => {
            // Disjoint or/xor: masks with no common bit.
            let (x, y) = (linear_expr(g, cx, w, d), linear_expr(g, cx, w, d));
            let m = g.constant(w);
            let mk = cx.constant(&m).unwrap();
            let nm = cx.un(UnOp::Not, mk).unwrap();
            let (x, y) = (
                cx.bin(BinOp::And, x, mk).unwrap(),
                cx.bin(BinOp::And, y, nm).unwrap(),
            );
            cx.bin(
                if g.rng.chance(1, 2) {
                    BinOp::Or
                } else {
                    BinOp::Xor
                },
                x,
                y,
            )
            .unwrap()
        }
    }
}

#[test]
fn linear_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Linear]);
    let mut g = generator(0x11ea_4001);
    let mut rng = Rng(9);
    let mut changed = 0;
    for i in 0..1500 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [16, 64, 128, 257, 512][g.rng.below(5) as usize]
        } else {
            1 + g.rng.below(6) as u16
        };
        let e = match i % 4 {
            0 => g.expr(&mut cx, w.min(6), 4).0,
            // `(P | Q) - Q` and `(P ^ Q) - Q` with overlapping operands: cancels only if the
            // or/xor is (wrongly) read as a sum.
            1 => {
                let p = linear_expr(&mut g, &mut cx, w, 3);
                let q = linear_expr(&mut g, &mut cx, w, 3);
                let op = if g.rng.chance(1, 2) {
                    BinOp::Or
                } else {
                    BinOp::Xor
                };
                let o = cx.bin(op, p, q).unwrap();
                cx.bin(BinOp::Sub, o, q).unwrap()
            }
            _ => linear_expr(&mut g, &mut cx, w, 5),
        };
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(r.end, End::Completed);
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        // Idempotent (recomputed, not answered from the memo).
        cx.memo.clear();
        let out2 = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !out2.roots[0].changed,
            "not idempotent: {} -> {}",
            cx.display(r.expr),
            cx.display(out2.roots[0].expr)
        );
    }
    assert!(changed > 200, "{changed}");
}

fn simplify(eng: &Engine, src: &str, w: u16) -> String {
    let mut cx = Context::new();
    let e = cx
        .parse(src, &ParseOptions::width(Width::new(w).unwrap()))
        .unwrap();
    let out = eng.simplify(&mut cx, e).unwrap();
    cx.display(out.expr).to_string()
}

#[test]
fn linear_cancels_additive_masking() {
    let eng = engine(vec![Phase::Linear]);
    for (src, want) in [
        ("(x + r) - r", "x"),
        ("(x - r) + (r + 5) - 5", "x"),
        ("~x + x", "-1:8"),
        ("x + x + x - 3 * x", "0:8"),
        ("(x << 2) - 4 * x", "0:8"),
        ("-(~x) - x", "1:8"),
        (
            "((x & 0xf0) | ((y * 2) & 0x0f)) - (y * 2 & 0x0f)",
            "x & -16",
        ),
        ("(x * y + 3) - (x * y + 1)", "2:8"),
        ("((x & 0xf0) ^ (y & 0x0f)) - (y & 0x0f)", "x & -16"),
        // Overlapping or/xor are not sums.
        ("(x | y) - y", "(x | y) - y"),
        ("(x ^ y) - y", "(x ^ y) - y"),
    ] {
        assert_eq!(simplify(&eng, src, 8), want, "{src}");
    }
    // Wide widths.
    assert_eq!(simplify(&eng, "(x + r) - r", 512), "x");
    assert_eq!(simplify(&eng, "~x + x + 1", 129), "0:129");
    // Equal-size rewrites are not made: a disjoint or stays an or.
    let mut cx = Context::new();
    let e = cx
        .parse("(x & 0xf0) | (y & 0x0f)", &ParseOptions::width(Width::W8))
        .unwrap();
    assert!(!eng.simplify(&mut cx, e).unwrap().changed);
}

#[test]
fn linear_atomizes_huge_forms() {
    let eng = engine(vec![Phase::Linear]);
    let mut cx = Context::new();
    let w = Width::W16;
    let mut e = cx.constant_u64(w, 0).unwrap();
    let mut syms = Vec::new();
    for i in 0..(super::linear::MAX_TERMS + 10) {
        let s = cx.symbol(format!("s{i}").as_str(), w).unwrap();
        syms.push(s);
        e = cx.bin(BinOp::Add, e, s).unwrap();
    }
    // (Σ s) - s0: the sum is over the cap, so it is an atom and nothing cancels, but the
    // result is still correct.
    let e2 = cx.bin(BinOp::Sub, e, syms[0]).unwrap();
    let out = eng.run(&mut cx, &[e2], Run::default()).unwrap();
    assert!(out.stats.passes["linear"].atomized > 0);
    let mut rng = Rng(1);
    assert!(equivalent(&mut cx, e2, out.roots[0].expr, &mut rng));
}

#[test]
fn linear_charges_pass_work() {
    let eng = engine(vec![Phase::Linear]);
    let mut cx = Context::new();
    let e = cx
        .parse("(x + r) - r + (y + q) - q", &ParseOptions::width(Width::W8))
        .unwrap();
    let out = eng
        .run(
            &mut cx,
            &[e],
            Run {
                per_call: Budget {
                    pass_work: 3,
                    ..Budget::UNLIMITED
                },
                ..Run::default()
            },
        )
        .unwrap();
    assert!(matches!(out.roots[0].end, End::BudgetTerminated(_)));
    assert!(out.stats.passes["linear"].calls > 0);
}

#[test]
fn fact_fold_folds_known_nodes_and_obeys_the_hook() {
    let eng = engine(vec![Phase::FactFold]);
    assert_eq!(simplify(&eng, "(x | 0x0f) & 0x0f", 8), "15:8");
    assert_eq!(simplify(&eng, "popcnt(x & 1) <=u 1", 8), "1:1");
    struct NoFold;
    impl Hooks for NoFold {
        fn fold_known(&self, _: &Context, _: Expr) -> bool {
            false
        }
    }
    let mut cx = Context::new();
    let e = cx
        .parse("(x | 0x0f) & 0x0f", &ParseOptions::width(Width::W8))
        .unwrap();
    let out = eng
        .run(
            &mut cx,
            &[e],
            Run {
                hooks: Some(&NoFold),
                ..Run::default()
            },
        )
        .unwrap();
    assert!(!out.roots[0].changed);
}

#[test]
fn passes_and_rules_compose() {
    let eng = engine(vec![
        Phase::FactFold,
        Phase::Local {
            groups: vec![
                "core.bitwise".into(),
                "core.arith".into(),
                "core.compare".into(),
                "core.casts".into(),
                "core.shift".into(),
            ],
        },
        Phase::Linear,
    ]);
    let mut g = generator(0xc0_4905);
    let mut rng = Rng(3);
    for _ in 0..500 {
        let mut cx = Context::new();
        let w = 1 + g.rng.below(6) as u16;
        let e = linear_expr(&mut g, &mut cx, w, 5);
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert!(equivalent(&mut cx, e, out.roots[0].expr, &mut rng));
        assert_eq!(out.stats.rejected, 0);
    }
}

// ----- bitwise ------------------------------------------------------------------------------------

#[test]
fn bitwise_table_is_exact_and_sized() {
    use super::bitwise::{T, min_forms};
    let forms = &min_forms().forms;
    assert_eq!(forms.len(), 256);
    let mut max = 0;
    for (tt, (tmpl, size)) in forms.iter().enumerate() {
        let mut vals: Vec<u8> = Vec::new();
        let mut ops = 0;
        for t in tmpl {
            let v = match *t {
                T::Var(k) => [0xAAu8, 0xCC, 0xF0][k as usize],
                T::Zero => 0,
                T::Ones => 0xFF,
                T::Not(a) => {
                    ops += 1;
                    !vals[a as usize]
                }
                T::Bin(op, a, b) => {
                    ops += 1;
                    let (a, b) = (vals[a as usize], vals[b as usize]);
                    match op {
                        BinOp::And => a & b,
                        BinOp::Or => a | b,
                        BinOp::Xor => a ^ b,
                        _ => panic!("not a bitwise op"),
                    }
                }
            };
            vals.push(v);
        }
        assert_eq!(*vals.last().unwrap() as usize, tt, "template for {tt:#04x}");
        assert_eq!(ops, *size as usize, "{tt:#04x}");
        max = max.max(*size);
    }
    // Every 3-input function needs at most a handful of operators; a regression in the search
    // would show here.
    assert!(max <= 7, "{max}");
    // The single-operator functions are single operators.
    assert_eq!(forms[0xAA & 0xCC].1, 1);
    assert_eq!(forms[0xAA ^ 0xCC ^ 0xF0].1, 2);
}

/// A random bitwise expression over up to six atoms (so some regions are over the caps).
fn bitwise_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32, atoms: u64) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 5) {
        return match g.rng.below(atoms + 2) {
            0 => cx.constant(&crate::BitVec::zero(width)).unwrap(),
            1 => cx.constant(&crate::BitVec::ones(width)).unwrap(),
            k => {
                let name = ["a", "b", "c", "d", "e", "f"][(k - 2) as usize];
                let s = cx.symbol(name, width).unwrap();
                if name == "d" {
                    // A non-bitwise atom.
                    let a = cx.symbol("a", width).unwrap();
                    cx.bin(BinOp::Add, s, a).unwrap()
                } else {
                    s
                }
            }
        };
    }
    let d = depth - 1;
    match g.rng.below(4) {
        0 => {
            let x = bitwise_expr(g, cx, w, d, atoms);
            cx.un(UnOp::Not, x).unwrap()
        }
        k => {
            let x = bitwise_expr(g, cx, w, d, atoms);
            let y = bitwise_expr(g, cx, w, d, atoms);
            cx.bin([BinOp::And, BinOp::Or, BinOp::Xor][(k - 1) as usize], x, y)
                .unwrap()
        }
    }
}

#[test]
fn bitwise_is_sound_minimal_and_idempotent() {
    let eng = engine(vec![Phase::Bitwise]);
    let mut g = generator(0xb175e);
    let mut rng = Rng(21);
    let mut changed = 0;
    for i in 0..1500 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [8, 64, 129, 512][g.rng.below(4) as usize]
        } else {
            1 + g.rng.below(6) as u16
        };
        let atoms = 2 + g.rng.below(5);
        let e = bitwise_expr(&mut g, &mut cx, w, 5, atoms);
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {}",
            cx.display(r.expr)
        );
    }
    assert!(changed > 300, "{changed}");
}

#[test]
fn bitwise_fixtures() {
    let eng = engine(vec![Phase::Bitwise]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let e = cx.parse(src, &o).unwrap();
        let w = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, w, "{src}: got {}", cx.display(out.expr));
    };
    same("(x & y) | (x & ~y)", "x");
    same("(x | y) & ~(x & y)", "x ^ y");
    same("~(~x & ~y)", "x | y");
    same("(x & ~y) | (~x & y)", "x ^ y");
    same("((x ^ y) & z) | (~(x ^ y) & z)", "z");
    same("(x & y & z) | (x & y & ~z)", "x & y");
    // A rewrite that drops an atom (`c` below) leaves no stale atom behind: the region above
    // has three atoms again and still reaches its minimum form.
    same("(d & ~b & ~a & ((b & c) | b)) | ~(d | a)", "~(a | d)");
    // Atoms may be arbitrary subterms.
    same("((p + q) & r) | ((p + q) & ~r)", "p + q");
}

#[test]
fn bitwise_reads_masking_over_six_atoms() {
    for eng in [engine(vec![Phase::Bitwise]), Engine::standard()] {
        let same = |src: &str, want: &str| {
            let mut cx = Context::new();
            let o = ParseOptions::width(Width::W32);
            let e = cx.parse(src, &o).unwrap();
            let w = cx.parse(want, &o).unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            assert_eq!(out.expr, w, "{src}: got {}", cx.display(out.expr));
        };
        // Boolean shares of `a & b` (masks `m`, `n`), and of `a & b & c` (six atoms).
        let share = "((a ^ m) & (b ^ n)) ^ ((a ^ m) & n) ^ (m & (b ^ n)) ^ (m & n)";
        same(share, "a & b");
        same(&format!("{share} ^ (a & b)"), "0");
        same(
            "((a ^ m) & (b ^ n) & (c ^ o)) ^ ((a ^ m) & (b ^ n) & o) ^ ((a ^ m) & n & (c ^ o)) \
             ^ ((a ^ m) & n & o) ^ (m & (b ^ n) & (c ^ o)) ^ (m & (b ^ n) & o) \
             ^ (m & n & (c ^ o)) ^ (m & n & o)",
            "a & b & c",
        );
        // Atoms may be subterms or constants.
        same(
            "(((p + q) ^ m) & (b ^ n)) ^ (((p + q) ^ m) & n) ^ (m & (b ^ n)) ^ (m & n)",
            "(p + q) & b",
        );
        same(
            "((a ^ 0x5a) & (b ^ n)) ^ ((a ^ 0x5a) & n) ^ (0x5a & (b ^ n)) ^ (0x5a & n)",
            "a & b",
        );
        // Read flat, this depends on four atoms; the three-atom reading still writes it over
        // the region of four as one atom.
        same(
            "((a ^ b ^ c ^ d) & x) | ((a ^ b ^ c ^ d) & ~x)",
            "a ^ b ^ c ^ d",
        );
    }
}

#[test]
fn bitwise_reads_constants_by_classes_before_reading_wide() {
    let eng = engine(vec![Phase::Bitwise]);
    let o = ParseOptions::width(Width::W8);
    // Four atoms with the constants: by classes, the constants fold (`~(0x36 ^ 0xc5)` is 12);
    // read wide, they would be atoms of the form.
    let mut cx = Context::new();
    let e = cx.parse("~(b ^ 0x36 ^ 0xc5) ^ (b ^ d)", &o).unwrap();
    let want = cx.parse("d ^ 12", &o).unwrap();
    assert_eq!(eng.simplify(&mut cx, e).unwrap().expr, want);
    // Over more than six atoms the wide reading is the node itself: nothing to write.
    let mut cx = Context::new();
    let e = cx.parse("(a ^ b ^ c ^ d) | (e ^ f ^ g ^ h)", &o).unwrap();
    let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
    assert!(!out.roots[0].changed);
    assert_eq!(out.stats.passes["bitwise"].noop, 0);
}

#[test]
fn passes_are_independent_of_construction_order() {
    for phase in [
        Phase::Linear,
        Phase::Bitwise,
        Phase::Xor,
        Phase::Compares,
        Phase::LinearMba,
        Phase::FactFold,
    ] {
        let eng = engine(vec![phase.clone()]);
        let mut g = generator(0x0de7);
        for _ in 0..300 {
            // The same expression in two contexts whose symbols were created in opposite
            // orders (so node indices differ).
            let mut c1 = Context::new();
            let mut c2 = Context::new();
            let w = Width::new(1 + g.rng.below(8) as u16).unwrap();
            for name in ["a", "b", "c", "d"] {
                c1.symbol(name, w).unwrap();
            }
            for name in ["d", "c", "b", "a"] {
                c2.symbol(name, w).unwrap();
            }
            for name in ["x", "y", "z"] {
                c1.symbol(name, w).unwrap();
            }
            for name in ["z", "y", "x"] {
                c2.symbol(name, w).unwrap();
            }
            let e1 = match g.rng.below(5) {
                4 => linear_mba_expr(&mut g, &mut c1, w.bits()),
                0 => bitwise_expr(&mut g, &mut c1, w.bits(), 5, 3),
                1 => xor_expr(&mut g, &mut c1, w.bits(), 5),
                2 => {
                    let mode = g.rng.below(3);
                    compare_expr(&mut g, &mut c1, w.bits(), 4, mode)
                }
                _ => linear_expr(&mut g, &mut c1, w.bits(), 4),
            };
            let text = c1.display(e1).to_string();
            let o = ParseOptions::width(w);
            let e2 = c2.parse(&text, &o).unwrap();
            let r1 = eng.simplify(&mut c1, e1).unwrap().expr;
            let r2 = eng.simplify(&mut c2, e2).unwrap().expr;
            assert_eq!(
                c1.display(r1).to_string(),
                c2.display(r2).to_string(),
                "{phase:?} on {text}"
            );
        }
    }
}

// ----- xor ----------------------------------------------------------------------------------------

/// A random expression in the xor fragment over up to six atoms.
fn xor_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 5) {
        return match g.rng.below(8) {
            0 => {
                let v = g.constant(w);
                cx.constant(&v).unwrap()
            }
            1 => {
                let a = cx.symbol("a", width).unwrap();
                let b = cx.symbol("b", width).unwrap();
                cx.bin(BinOp::Add, a, b).unwrap()
            }
            k => cx
                .symbol(["a", "b", "c", "d", "e", "f"][(k - 2) as usize], width)
                .unwrap(),
        };
    }
    let d = depth - 1;
    match g.rng.below(6) {
        0 | 1 => {
            let (x, y) = (xor_expr(g, cx, w, d), xor_expr(g, cx, w, d));
            cx.bin(BinOp::Xor, x, y).unwrap()
        }
        2 => {
            let x = xor_expr(g, cx, w, d);
            cx.un(UnOp::Not, x).unwrap()
        }
        3 => {
            let x = xor_expr(g, cx, w, d);
            let m = g.constant(w);
            let m = cx.constant(&m).unwrap();
            cx.bin(
                if g.rng.chance(1, 2) {
                    BinOp::And
                } else {
                    BinOp::Or
                },
                x,
                m,
            )
            .unwrap()
        }
        4 => {
            // Disjoint or.
            let (x, y) = (xor_expr(g, cx, w, d), xor_expr(g, cx, w, d));
            let m = g.constant(w);
            let mk = cx.constant(&m).unwrap();
            let nm = cx.un(UnOp::Not, mk).unwrap();
            let (x, y) = (
                cx.bin(BinOp::And, x, mk).unwrap(),
                cx.bin(BinOp::And, y, nm).unwrap(),
            );
            cx.bin(BinOp::Or, x, y).unwrap()
        }
        _ => {
            // Overlapping or: never a sum.
            let (x, y) = (xor_expr(g, cx, w, d), xor_expr(g, cx, w, d));
            let o = cx.bin(BinOp::Or, x, y).unwrap();
            cx.bin(BinOp::Xor, o, y).unwrap()
        }
    }
}

#[test]
fn xor_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Xor]);
    let mut g = generator(0x0a0f);
    let mut rng = Rng(33);
    let mut changed = 0;
    for i in 0..1500 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [8, 64, 128, 511][g.rng.below(4) as usize]
        } else {
            1 + g.rng.below(6) as u16
        };
        let e = if i % 4 == 0 {
            g.expr(&mut cx, w.min(6), 4).0
        } else {
            xor_expr(&mut g, &mut cx, w, 5)
        };
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {}",
            cx.display(r.expr)
        );
    }
    assert!(changed > 300, "{changed}");
}

/// Linear maps over GF(2) of one atom (xors of shifted, rotated, masked copies): the xor
/// pass's diagonal form is equivalent, exhaustively at small widths, and idempotent.
#[test]
fn gf2_forms_are_sound_and_idempotent() {
    let eng = engine(vec![Phase::Xor]);
    let mut g = generator(0x6f2f);
    let mut rng = Rng(51);
    let mut changed = 0;
    for i in 0..2000 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            64
        } else {
            2 + g.rng.below(7) as u16
        };
        let width = Width::new(w).unwrap();
        let x = cx.symbol("x", width).unwrap();
        let mut e = x;
        for _ in 0..1 + g.rng.below(5) {
            let k = BitVec::wrapping_from_u64(width, g.rng.below(u64::from(w)));
            let k = cx.constant(&k).unwrap();
            let t = match g.rng.below(5) {
                0 => cx.bin(BinOp::RotL, e, k).unwrap(),
                1 => cx.bin(BinOp::Shl, e, k).unwrap(),
                2 => cx.bin(BinOp::LShr, e, k).unwrap(),
                3 => {
                    let m = g.constant(w);
                    let m = cx.constant(&m).unwrap();
                    cx.bin(BinOp::And, e, m).unwrap()
                }
                _ => cx.un(UnOp::Not, e).unwrap(),
            };
            e = if g.rng.chance(1, 2) {
                cx.bin(BinOp::Xor, e, t).unwrap()
            } else {
                cx.bin(BinOp::Xor, t, x).unwrap()
            };
        }
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {}",
            cx.display(r.expr)
        );
    }
    assert!(changed > 100, "{changed}");
}

#[test]
fn xor_cancels_boolean_masking() {
    let eng = engine(vec![Phase::Xor]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let e = cx.parse(src, &o).unwrap();
        let w = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, w, "{src}: got {}", cx.display(out.expr));
    };
    same("(x ^ r) ^ r", "x");
    same("((x ^ k) & 0xf0) ^ (k & 0xf0)", "x & 0xf0");
    same("~(x ^ y) ^ y", "~x");
    same("(x | 0x0f) ^ 0x0f", "x & 0xf0");
    same("a ^ b ^ c ^ d ^ e ^ (b ^ d)", "a ^ c ^ e");
    same("((a ^ m) ^ (b ^ m)) ^ ((c + d) ^ (a ^ b))", "c + d");
    // Overlapping or is not an xor.
    same("(x | y) ^ y", "(x | y) ^ y");
    // `x | c` is read as `(x & ~c) ^ c` and comes back as itself, after a cancellation too;
    // a constant that misses every mask widens them (here x's mask to all-ones).
    same("x | 3", "x | 3");
    same("((x | 3) ^ v) ^ v", "x | 3");
    same("(((x | 3) ^ (y & 0xf0)) ^ v) ^ v", "(x ^ (y & 0xf3)) | 3");
    same("(x & 0xf0) ^ 1", "(x & 0xf0) ^ 1");
}

// ----- compares -----------------------------------------------------------------------------------

/// A random boolean combination of comparisons: of one operand pair, of one operand against
/// constants, or mixed.
fn compare_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32, mode: u64) -> Expr {
    use crate::CmpOpExt;
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 4) {
        let op = CmpOpExt::ALL[g.rng.below(10) as usize];
        let x = cx.symbol("x", width).unwrap();
        let other = match mode {
            0 => cx.symbol("y", width).unwrap(),
            1 => {
                let v = g.constant(w);
                cx.constant(&v).unwrap()
            }
            _ => match g.rng.below(3) {
                0 => cx.symbol("y", width).unwrap(),
                1 => cx.symbol("z", width).unwrap(),
                _ => {
                    let v = g.constant(w);
                    cx.constant(&v).unwrap()
                }
            },
        };
        let (a, b) = if g.rng.chance(1, 2) {
            (x, other)
        } else {
            (other, x)
        };
        if g.rng.chance(1, 12) {
            return cx
                .constant(&crate::BitVec::from_bool(g.rng.chance(1, 2)))
                .unwrap();
        }
        return cx.cmp(op, a, b).unwrap();
    }
    let d = depth - 1;
    match g.rng.below(4) {
        0 => {
            let x = compare_expr(g, cx, w, d, mode);
            cx.un(UnOp::Not, x).unwrap()
        }
        k => {
            let x = compare_expr(g, cx, w, d, mode);
            let y = compare_expr(g, cx, w, d, mode);
            cx.bin([BinOp::And, BinOp::Or, BinOp::Xor][(k - 1) as usize], x, y)
                .unwrap()
        }
    }
}

#[test]
fn compares_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Compares]);
    let mut g = generator(0xc0_3e);
    let mut rng = Rng(44);
    let mut changed = 0;
    for i in 0..3000 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [8, 32, 64, 128, 512][g.rng.below(5) as usize]
        } else {
            1 + g.rng.below(6) as u16
        };
        let mode = g.rng.below(3);
        let e = compare_expr(&mut g, &mut cx, w, 4, mode);
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {}",
            cx.display(r.expr)
        );
    }
    assert!(changed > 800, "{changed}");
}

#[test]
fn compares_fixtures() {
    let eng = engine(vec![Phase::Compares]);
    let same = |src: &str, want: &str, w: u16| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    same("(x <u y) | (x == y)", "x <=u y", 8);
    same("(x <u y) & (y <u x)", "false", 8);
    same("~(x <=s y)", "y <s x", 8);
    same("(x <=u y) & (x >=u y)", "x == y", 8);
    same("(x <u 10) & (x >u 3)", "x - 4 <=u 5", 8);
    same("(x == 5) | (x == 6)", "x - 5 <=u 1", 8);
    same("(x <u 3) | (x >u 250)", "x - 251 <=u 7", 8);
    same("(x <s 0) ^ (x <u 128)", "true", 8);
    same("(x <u 200) & (x != 7) & (x <u 8)", "x <=u 6", 8);
    same("(x <s 5) & (x >=s -3)", "x + 3 <=u 7", 8);
    // At W = 1 only three relations occur: `<u` and `<s` never hold together.
    same("(x <u y) & (x <s y)", "false", 1);
    same("(x <u y) ^ (x <s y)", "x != y", 1);
    // Different pairs are left alone.
    same("(x <u y) & (x <u z)", "(x <u y) & (x <u z)", 8);
    // Comparisons of functions of x combine on x.
    same("(x - 4 <=u 5) | (x == 10)", "x - 4 <=u 6", 8);
    same("(x + 3 <u 5) & (x == 1)", "x == 1", 8);
    same("((x & 0x7f) == 0) & (x <u 0x80)", "x == 0", 8);
    same("(~x <u 10) | (x <u 10)", "x - 246 <=u 19", 8);
    same("((x ^ 0x80) <u 0x10) | (x - 0x90 <u 0x10)", "x <=s 0x9f", 8);
    same("(-x == 3) & (x == 5)", "false", 8);
    same("((x | 0x80) == 0x85) ^ (x == 5)", "x == 0x85", 8);
    same("(x + 1 == 0) | (x + 1 == 1)", "x - 255 <=u 1", 8);
}

/// A term for the order reading: a symbol, a constant, an operation bounded by or monotone in
/// its operands, or a select between terms on a comparison (a minimum or maximum).
fn order_term(g: &mut Gen, cx: &mut Context, w: u16, depth: u32, signed: bool) -> Expr {
    let width = Width::new(w).unwrap();
    let sym = |cx: &mut Context, g: &mut Gen| {
        cx.symbol(["x", "y", "z"][g.rng.below(3) as usize], width)
            .unwrap()
    };
    if depth == 0 || g.rng.chance(1, 3) {
        return match g.rng.below(8) {
            0 => {
                let v = g.constant(w);
                cx.constant(&v).unwrap()
            }
            1 => {
                let (a, b) = (sym(cx, g), sym(cx, g));
                cx.bin(BinOp::And, a, b).unwrap()
            }
            2 => {
                let (a, b) = (sym(cx, g), sym(cx, g));
                cx.bin(BinOp::Or, a, b).unwrap()
            }
            3 => {
                let a = sym(cx, g);
                let k = BitVec::wrapping_from_u64(width, g.rng.below(3));
                let k = cx.constant(&k).unwrap();
                let op = if signed { BinOp::AShr } else { BinOp::LShr };
                cx.bin(op, a, k).unwrap()
            }
            4 => {
                let a = sym(cx, g);
                let k = BitVec::wrapping_from_u64(width, 1 + g.rng.below(3));
                let k = cx.constant(&k).unwrap();
                cx.bin(BinOp::UDiv, a, k).unwrap()
            }
            _ => sym(cx, g),
        };
    }
    let c = order_formula(g, cx, w, depth - 1, signed);
    let (a, b) = (
        order_term(g, cx, w, depth - 1, signed),
        order_term(g, cx, w, depth - 1, signed),
    );
    cx.select(c, a, b).unwrap()
}

/// A boolean combination of comparisons between order terms.
fn order_formula(g: &mut Gen, cx: &mut Context, w: u16, depth: u32, signed: bool) -> Expr {
    use crate::CmpOpExt;
    if depth == 0 || g.rng.chance(1, 3) {
        let ops: &[CmpOpExt] = if signed {
            &[
                CmpOpExt::Slt,
                CmpOpExt::Sle,
                CmpOpExt::Sgt,
                CmpOpExt::Sge,
                CmpOpExt::Eq,
                CmpOpExt::Ne,
            ]
        } else {
            &[
                CmpOpExt::Ult,
                CmpOpExt::Ule,
                CmpOpExt::Ugt,
                CmpOpExt::Uge,
                CmpOpExt::Eq,
                CmpOpExt::Ne,
            ]
        };
        let op = ops[g.rng.below(ops.len() as u64) as usize];
        let a = order_term(g, cx, w, depth.min(1), signed);
        let b = order_term(g, cx, w, depth.min(1), signed);
        return cx.cmp(op, a, b).unwrap();
    }
    let d = depth - 1;
    match g.rng.below(4) {
        0 => {
            let x = order_formula(g, cx, w, d, signed);
            cx.un(UnOp::Not, x).unwrap()
        }
        k => {
            let x = order_formula(g, cx, w, d, signed);
            let y = order_formula(g, cx, w, d, signed);
            cx.bin([BinOp::And, BinOp::Or, BinOp::Xor][(k - 1) as usize], x, y)
                .unwrap()
        }
    }
}

/// The order reading (in the compares pass) is sound: every result is equivalent,
/// exhaustively at small widths, and a second run changes nothing.
#[test]
fn order_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Compares]);
    let mut g = generator(0x0de5);
    let mut rng = Rng(46);
    let mut changed = 0;
    for i in 0..3000 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [8, 32, 64][g.rng.below(3) as usize]
        } else {
            1 + g.rng.below(4) as u16
        };
        let signed = g.rng.chance(1, 3);
        let e = if g.rng.chance(1, 3) {
            order_term(&mut g, &mut cx, w, 3, signed)
        } else {
            order_formula(&mut g, &mut cx, w, 3, signed)
        };
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {} became {}",
            cx.display(r.expr),
            cx.display(again.roots[0].expr)
        );
    }
    assert!(changed > 300, "{changed}");
}

#[test]
fn compares_handles_deep_boolean_chains() {
    let eng = engine(vec![Phase::Compares]);
    let mut cx = Context::new();
    let mut root = cx.symbol("p", Width::W1).unwrap();
    for k in 0..10_000 {
        let leaf = cx.symbol(format!("q{k}"), Width::W1).unwrap();
        let op = if k % 2 == 0 { BinOp::And } else { BinOp::Or };
        root = cx.bin(op, root, leaf).unwrap();
    }
    assert_eq!(cx.height(root).unwrap(), 10_000);
    // This formula has too many Boolean leaves for the order model. Declining it must be
    // bounded even when its entire left spine is visited before the first leaf is completed.
    assert_eq!(eng.simplify(&mut cx, root).unwrap().expr, root);
}

#[test]
fn order_fixtures() {
    let eng = engine(vec![Phase::Compares]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    // Laws of the order: transitivity, asymmetry, trichotomy, totality.
    same("(x <u y) & (y <u z) & (z <=u x)", "false");
    same("(x <=s y) & (y <=s z) & (z <s x)", "false");
    same("(x <u y) | (x == y) | (y <u x)", "true");
    same("~(x <u y) & ~(y <u x)", "x == y");
    same("(x <=u y) & (y <=u z) & (x <=u z)", "(x <=u y) & (y <=u z)");
    // Minimum and maximum, however they are written.
    same("select(x <u y, x, y) == select(y <u x, y, x)", "true");
    same("select(x <u y, x, y) <=u select(x <u y, y, x)", "true");
    same(
        "select(x <u select(x <u y, y, x), x, select(x <u y, y, x))",
        "x",
    );
    same(
        "select(x <u select(y <u z, y, z), x, select(y <u z, y, z)) \
         == select(select(x <u y, x, y) <u z, select(x <u y, x, y), z)",
        "true",
    );
    same("select(x <s y, x, y) == select(y <s x, y, x)", "true");
    // Bounded and monotone operations.
    same("(x & y) <=u x", "true");
    same("x <=u (x | y)", "true");
    same("~(x <=u y) | ((x >>u 2) <=u (y >>u 2))", "true");
    same("~(x <=u y) | (udiv(x, 3) <=u udiv(y, 3))", "true");
    same("~(x <=s y) | ((x >>s 2) <=s (y >>s 2))", "true");
    // Constants and ranges order atoms too.
    same("select(x <u 0xff, x, 0xff)", "x");
    same("((x & 0x0f) <u 0x20) & (y <=u x)", "y <=u x");
    // Other pairs stay.
    same("(x <u y) & (x <u z)", "(x <u y) & (x <u z)");
}

/// Comparisons of `x`, of functions of it that the pass sees through, and of extensions of a
/// narrower `v`, combined.
fn peeled_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> Expr {
    use crate::CmpOpExt;
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 4) {
        let x = cx.symbol("x", width).unwrap();
        let k = g.constant(w);
        let k = cx.constant(&k).unwrap();
        let low = BitVec::wrapping_from_u64(width, (1 << g.rng.below(u64::from(w.min(63)))) - 1);
        let low = cx.constant(&low).unwrap();
        let smin = cx.constant(&BitVec::smin(width)).unwrap();
        let v = || Width::new(w - 1).unwrap();
        let t = match g.rng.below(11) {
            0 => x,
            1 => cx.bin(BinOp::Add, x, k).unwrap(),
            2 => cx.bin(BinOp::Sub, k, x).unwrap(),
            3 => cx.un(UnOp::Neg, x).unwrap(),
            4 => cx.un(UnOp::Not, x).unwrap(),
            5 => cx.bin(BinOp::Xor, x, smin).unwrap(),
            6 => cx.bin(BinOp::And, x, low).unwrap(),
            7 => cx.bin(BinOp::Or, x, smin).unwrap(),
            8 if w > 1 => {
                let v = cx.symbol("v", v()).unwrap();
                cx.zext(v, width).unwrap()
            }
            9 if w > 1 => {
                let v = cx.symbol("v", v()).unwrap();
                cx.sext(v, width).unwrap()
            }
            _ => {
                let s = cx.bin(BinOp::Sub, x, k).unwrap();
                cx.bin(BinOp::And, s, low).unwrap()
            }
        };
        let op = CmpOpExt::ALL[g.rng.below(10) as usize];
        let c = g.constant(w);
        let c = cx.constant(&c).unwrap();
        return if g.rng.chance(1, 2) {
            cx.cmp(op, t, c).unwrap()
        } else {
            cx.cmp(op, c, t).unwrap()
        };
    }
    let d = depth - 1;
    match g.rng.below(4) {
        0 => {
            let x = peeled_expr(g, cx, w, d);
            cx.un(UnOp::Not, x).unwrap()
        }
        k => {
            let x = peeled_expr(g, cx, w, d);
            let y = peeled_expr(g, cx, w, d);
            cx.bin([BinOp::And, BinOp::Or, BinOp::Xor][(k - 1) as usize], x, y)
                .unwrap()
        }
    }
}

#[test]
fn compares_through_functions_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Compares]);
    let mut g = generator(0xc0_3f);
    let mut rng = Rng(45);
    let mut changed = 0;
    for i in 0..3000 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [8, 32, 64, 128][g.rng.below(4) as usize]
        } else {
            2 + g.rng.below(6) as u16
        };
        let e = peeled_expr(&mut g, &mut cx, w, 3);
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {} to {}",
            cx.display(r.expr),
            cx.display(again.roots[0].expr)
        );
    }
    assert!(changed > 600, "{changed}");
}

/// A random boolean combination of float comparisons (of `x`, `y` and constants), float tests
/// and integer comparisons of `x`, in format `f`.
fn float_compare_expr(g: &mut Gen, cx: &mut Context, f: FpFormat, depth: u32) -> Expr {
    use crate::fp::{FpCmpOp, FpTest};
    let w = f.width();
    if depth == 0 || g.rng.chance(1, 4) {
        let operand = |g: &mut Gen, cx: &mut Context| match g.rng.below(5) {
            0 | 1 => cx.symbol("x", w).unwrap(),
            2 => cx.symbol("y", w).unwrap(),
            _ => {
                let v = match g.rng.below(6) {
                    0 => f.zero(g.rng.chance(1, 2)),
                    1 => f.inf(g.rng.chance(1, 2)),
                    2 => f.nan(),
                    _ => g.constant(w.bits()),
                };
                cx.constant(&v).unwrap()
            }
        };
        return match g.rng.below(6) {
            0..=2 => {
                let op = [
                    FpCmpOp::Eq,
                    FpCmpOp::Lt,
                    FpCmpOp::Le,
                    FpCmpOp::Gt,
                    FpCmpOp::Ge,
                ][g.rng.below(5) as usize];
                let a = operand(g, cx);
                let b = operand(g, cx);
                cx.fp_cmp(f, op, a, b).unwrap()
            }
            3 | 4 => {
                let t = [
                    FpTest::Nan,
                    FpTest::Infinite,
                    FpTest::Zero,
                    FpTest::Subnormal,
                    FpTest::Normal,
                    FpTest::Negative,
                    FpTest::Positive,
                ][g.rng.below(7) as usize];
                let a = if g.rng.chance(3, 4) { "x" } else { "y" };
                let a = cx.symbol(a, w).unwrap();
                cx.fp_test(f, t, a).unwrap()
            }
            _ => {
                let op = CmpOpExt::ALL[g.rng.below(10) as usize];
                let x = cx.symbol("x", w).unwrap();
                let c = g.constant(w.bits());
                let c = cx.constant(&c).unwrap();
                cx.cmp(op, x, c).unwrap()
            }
        };
    }
    let d = depth - 1;
    match g.rng.below(4) {
        0 => {
            let x = float_compare_expr(g, cx, f, d);
            cx.un(UnOp::Not, x).unwrap()
        }
        k => {
            let x = float_compare_expr(g, cx, f, d);
            let y = float_compare_expr(g, cx, f, d);
            cx.bin([BinOp::And, BinOp::Or, BinOp::Xor][(k - 1) as usize], x, y)
                .unwrap()
        }
    }
}

#[test]
fn compares_of_floats_is_sound_and_idempotent() {
    compares_of_floats_is_sound_and_idempotent_cases(1500);
}

/// [`compares_of_floats_is_sound_and_idempotent`] over 4000 random cases.
#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn compares_of_floats_is_sound_and_idempotent_heavy() {
    compares_of_floats_is_sound_and_idempotent_cases(4000);
}

fn compares_of_floats_is_sound_and_idempotent_cases(cases: usize) {
    let eng = engine(vec![Phase::Compares]);
    let mut g = generator(0xf1_0a7);
    let mut rng = Rng(46);
    let formats = [
        (2, 2),
        (2, 3),
        (3, 2),
        (2, 4),
        (3, 3),
        (4, 2),
        (3, 4),
        (5, 2),
    ];
    let mut changed = 0;
    for i in 0..cases {
        let mut cx = Context::new();
        let f = if i % 10 == 0 {
            [FpFormat::F16, FpFormat::BF16, FpFormat::F32][g.rng.below(3) as usize]
        } else {
            let (eb, sb) = formats[g.rng.below(formats.len() as u64) as usize];
            FpFormat::new(eb, sb).unwrap()
        };
        let e = float_compare_expr(&mut g, &mut cx, f, 3);
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{f:?}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {} to {}",
            cx.display(r.expr),
            cx.display(again.roots[0].expr)
        );
    }
    assert!(changed > 800 * cases as u64 / 4000, "{changed}");
}

#[test]
fn compares_of_floats_fixtures() {
    let eng = engine(vec![Phase::Compares]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    // The classes and the signs cover every encoding; a zero is not normal.
    same(
        "fp.isnan.f32(x) | fp.isinf.f32(x) | fp.iszero.f32(x) | fp.isnormal.f32(x) \
         | fp.issubnormal.f32(x)",
        "true",
    );
    same(
        "fp.isnan.f32(x) | fp.isneg.f32(x) | fp.ispos.f32(x)",
        "true",
    );
    same("fp.iszero.f32(x) & fp.isnormal.f32(x)", "false");
    same(
        "fp.iszero.f32(x) | fp.issubnormal.f32(x)",
        "x & 0x7fffffff <=u 0x7fffff",
    );
    same("fp.isnan.f32(x) | fp.isneg.f32(x)", "0x7f800001 <=u x");
    // Two floats.
    same("fp.lt.f32(x, y) & fp.lt.f32(y, x)", "false");
    same("fp.lt.f32(x, y) | fp.eq.f32(x, y)", "fp.le.f32(x, y)");
    same("fp.le.f32(x, y) & fp.ge.f32(x, y)", "fp.eq.f32(x, y)");
    same("~fp.lt.f32(x, y) & ~fp.eq.f32(x, y)", "~fp.le.f32(x, y)");
    // x86's flags after `ucomiss x, y`: ZF, PF, CF are equal, unordered, less, each or
    // unordered; `ja`, `jae`, `jb`, `jbe` test them.
    let unordered = "(fp.isnan.f32(x) | fp.isnan.f32(y))";
    let cf = format!("(fp.lt.f32(x, y) | {unordered})");
    let zf = format!("(fp.eq.f32(x, y) | {unordered})");
    same(&format!("~{cf} & ~{zf}"), "fp.lt.f32(y, x)");
    same(&format!("~{cf}"), "fp.le.f32(y, x)");
    same(&cf, "~fp.le.f32(y, x)");
    same(&format!("{cf} | {zf}"), "~fp.lt.f32(y, x)");
    // A float against constants: 1.0 is 0x3f800000.
    same(
        "fp.lt.f32(x, 0x3f800000) | fp.eq.f32(x, 0x3f800000)",
        "fp.le.f32(x, 0x3f800000)",
    );
    same(
        "fp.isnan.f32(x) | fp.le.f32(x, 0x3f800000)",
        "~fp.lt.f32(0x3f800000, x)",
    );
    same(
        "fp.lt.f32(x, 0x3f800000) & ~fp.isnan.f32(x)",
        "fp.lt.f32(x, 0x3f800000)",
    );
    same(
        "fp.le.f32(x, 0x3f7fffff) & ~fp.isnan.f32(x)",
        "fp.lt.f32(x, 0x3f800000)",
    );
    same("fp.lt.f32(x, 0) | fp.iszero.f32(x)", "fp.le.f32(x, 0)");
    same("fp.lt.f32(0, x) | fp.iszero.f32(x)", "fp.le.f32(0, x)");
    same(
        "fp.lt.f32(x, 0x3f800000) & fp.lt.f32(0x40000000, x)",
        "false",
    );
    same("fp.isinf.f32(x) & fp.lt.f32(x, 0)", "x == 0xff800000");
}

// ----- casts --------------------------------------------------------------------------------------

#[test]
fn casts_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Casts]);
    let mut g = generator(0xca57);
    g.max_w = 8;
    let mut rng = Rng(55);
    let mut changed = 0;
    for _ in 0..2000 {
        let mut cx = Context::new();
        let wide = 2 + g.rng.below(7) as u16;
        let (x, _) = g.expr(&mut cx, wide, 4);
        // Extract some bits of it (the pass acts on extracts).
        let n = 1 + g.rng.below(u64::from(wide)) as u16;
        let lo = g.rng.below(u64::from(wide - n) + 1) as u16;
        let e = cx.extract(x, lo, Width::new(n).unwrap()).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {} -> {} (from {})",
            cx.display(r.expr),
            cx.display(again.roots[0].expr),
            cx.display(e)
        );
    }
    assert!(changed > 100, "{changed}");
}

#[test]
fn casts_fixtures() {
    let eng = engine(vec![Phase::Casts]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    same("trunc<8>(zext<16>(x) + zext<16>(y))", "x + y");
    same("extract<8, 8>(zext<16>(x) << 8)", "x");
    same("trunc<8>(sext<32>(x) * sext<32>(y))", "x * y");
    same("extract<4, 4>(concat(a, b))", "extract<4, 4>(b)");
    same("trunc<4>(x >>u 4)", "extract<4, 4>(x)");
    same("trunc<8>(~(zext<16>(x) ^ zext<16>(y)))", "~(x ^ y)");
    same("extract<8, 8>(zext<16>(x))", "0:8");
    // Opaque operands: narrowing would only add nodes.
    same("trunc<8>(a:16 + b:16)", "trunc<8>(a:16 + b:16)");
    // Equal size: no change (`~trunc<4>(x)` is no smaller).
    same("trunc<4>(~x)", "trunc<4>(~x)");
}

// ----- demanded -----------------------------------------------------------------------------------

#[test]
fn demanded_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Demanded]);
    let mut g = generator(0xde_3a);
    g.max_w = 8;
    let mut rng = Rng(66);
    let mut changed = 0;
    for i in 0..2500 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [16, 64, 130][g.rng.below(3) as usize]
        } else {
            1 + g.rng.below(7) as u16
        };
        let width = Width::new(w).unwrap();
        let (x, _) = if i % 3 == 0 {
            (xor_expr(&mut g, &mut cx, w, 4), ())
        } else if i % 3 == 1 {
            (linear_expr(&mut g, &mut cx, w, 4), ())
        } else {
            let (e, _) = g.expr(&mut cx, w.min(8), 4);
            (e, ())
        };
        let width = cx.width(x).unwrap_or(width);
        // Observe it through some bits.
        let e = match g.rng.below(4) {
            0 => {
                let m = g.constant(width.bits());
                let m = cx.constant(&m).unwrap();
                cx.bin(BinOp::And, x, m).unwrap()
            }
            1 => {
                let m = g.constant(width.bits());
                let m = cx.constant(&m).unwrap();
                cx.bin(BinOp::Or, x, m).unwrap()
            }
            2 => {
                let k = cx
                    .constant_u64(width, g.rng.below(u64::from(width.bits())))
                    .unwrap();
                let op = if g.rng.chance(1, 2) {
                    BinOp::Shl
                } else {
                    BinOp::LShr
                };
                cx.bin(op, x, k).unwrap()
            }
            _ => {
                let n = 1 + g.rng.below(u64::from(width.bits())) as u16;
                let lo = g.rng.below(u64::from(width.bits() - n) + 1) as u16;
                cx.extract(x, lo, Width::new(n).unwrap()).unwrap()
            }
        };
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {} -> {} (from {})",
            cx.display(r.expr),
            cx.display(again.roots[0].expr),
            cx.display(e)
        );
    }
    assert!(changed > 200, "{changed}");
}

/// A polynomial over one or two symbols, with bitwise operations and constants: the
/// fragment residues read.
fn poly_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 4) {
        return match g.rng.below(4) {
            0 => {
                let v = g.constant(w);
                cx.constant(&v).unwrap()
            }
            1 => cx.symbol("y", width).unwrap(),
            _ => cx.symbol("x", width).unwrap(),
        };
    }
    let d = depth - 1;
    let ops = [
        BinOp::Mul,
        BinOp::Mul,
        BinOp::Add,
        BinOp::Sub,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
    ];
    let op = ops[g.rng.below(ops.len() as u64) as usize];
    let (a, b) = (poly_expr(g, cx, w, d), poly_expr(g, cx, w, d));
    cx.bin(op, a, b).unwrap()
}

/// Residues: the low bits of polynomials (masked, compared with constants, shifted up) are
/// decided soundly, exhaustively at small widths.
#[test]
fn residues_are_sound_and_idempotent() {
    let eng = engine(vec![Phase::Demanded, Phase::Compares]);
    let mut g = generator(0x7e51);
    let mut rng = Rng(47);
    let mut changed = 0;
    for i in 0..2000 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            64
        } else {
            1 + g.rng.below(7) as u16
        };
        let width = Width::new(w).unwrap();
        let p = poly_expr(&mut g, &mut cx, w, 3);
        let e = match g.rng.below(3) {
            0 => {
                let m = BitVec::wrapping_from_u64(width, g.rng.below(16));
                let m = cx.constant(&m).unwrap();
                cx.bin(BinOp::And, p, m).unwrap()
            }
            1 => {
                let c = BitVec::wrapping_from_u64(width, g.rng.below(16));
                let c = cx.constant(&c).unwrap();
                cx.cmp(CmpOpExt::Eq, p, c).unwrap()
            }
            _ => {
                let s = cx.constant_u64(width, g.rng.below(u64::from(w))).unwrap();
                cx.bin(BinOp::Shl, p, s).unwrap()
            }
        };
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {}",
            cx.display(r.expr)
        );
    }
    assert!(changed > 200, "{changed}");
}

/// Polynomial equality: comparisons of random polynomials (with each other, and with a
/// rearrangement) are decided soundly, exhaustively at small widths.
#[test]
fn polynomial_equality_is_sound() {
    let eng = engine(vec![Phase::Compares]);
    let mut g = generator(0x9017);
    let mut rng = Rng(50);
    let mut decided = 0;
    for i in 0..1500 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            64
        } else {
            1 + g.rng.below(6) as u16
        };
        let a = poly_expr(&mut g, &mut cx, w, 3);
        let b = if g.rng.chance(1, 2) {
            poly_expr(&mut g, &mut cx, w, 3)
        } else {
            // a·(1 + k) − a·k, which expands to a.
            let k = g.constant(w);
            let k = cx.constant(&k).unwrap();
            let one = cx.constant_u64(Width::new(w).unwrap(), 1).unwrap();
            let k1 = cx.bin(BinOp::Add, one, k).unwrap();
            let p = cx.bin(BinOp::Mul, a, k1).unwrap();
            let q = cx.bin(BinOp::Mul, a, k).unwrap();
            cx.bin(BinOp::Sub, p, q).unwrap()
        };
        let op = if g.rng.chance(1, 2) {
            CmpOpExt::Eq
        } else {
            CmpOpExt::Ne
        };
        let e = cx.cmp(op, a, b).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        decided += u64::from(cx.const_val(cx.id(r.expr).unwrap()).is_some());
    }
    assert!(decided > 300, "{decided}");
}

#[test]
fn residue_fixtures() {
    let eng = Engine::standard();
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    same("(x * x) & 1", "x & 1");
    same("(x * x * x) & 1", "x & 1");
    same("(x * x + x) & 1", "0");
    same("(x * (x + 1) * (x + 2)) & 1", "0");
    same("((x | 1) * (x | 1)) & 7", "1");
    same("(((x | 1) - 1) * ((x | 1) + 1)) & 7", "0");
    same("((x * x) & 3) == 3", "false");
    same("((x * x) & 7) == 5", "false");
    same("x * x == 2", "false");
    same("(x * x) & 2", "0");
    same("(x * x + x) * 0x80", "0");
    same("(x * (x + 1) * ((x + 2) * (x + 3))) * 0x20", "0");
    // A product of two values has no such law.
    same("(x * y) & 1", "(x * y) & 1");
}

/// A term of width `w` for the predicate tests: squares and products of sums, multiples, masks,
/// shifts, remainders and quotients by small constants (unsigned and signed), and narrow values
/// extended.
fn predicate_term(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 4) {
        return match g.rng.below(7) {
            0 => {
                let v = BitVec::wrapping_from_u64(width, g.rng.below(16));
                cx.constant(&v).unwrap()
            }
            1 => cx.symbol("y", width).unwrap(),
            2 if w > 2 => {
                let a = cx.symbol("a", Width::new(2).unwrap()).unwrap();
                cx.zext(a, width).unwrap()
            }
            3 if w > 2 => {
                let b = cx.symbol("b", Width::new(2).unwrap()).unwrap();
                cx.sext(b, width).unwrap()
            }
            _ => cx.symbol("x", width).unwrap(),
        };
    }
    let d = depth - 1;
    let small = |g: &mut Gen, cx: &mut Context, n: u64| {
        let v = BitVec::wrapping_from_u64(width, g.rng.below(n));
        cx.constant(&v).unwrap()
    };
    match g.rng.below(11) {
        0 | 1 => {
            let t = predicate_term(g, cx, w, d);
            cx.bin(BinOp::Mul, t, t).unwrap()
        }
        2 => {
            let (a, b) = (predicate_term(g, cx, w, d), predicate_term(g, cx, w, d));
            cx.bin(BinOp::Mul, a, b).unwrap()
        }
        3 => {
            let (a, b) = (predicate_term(g, cx, w, d), predicate_term(g, cx, w, d));
            cx.bin(BinOp::Add, a, b).unwrap()
        }
        4 => {
            let (a, b) = (predicate_term(g, cx, w, d), predicate_term(g, cx, w, d));
            cx.bin(BinOp::Sub, a, b).unwrap()
        }
        5 => {
            let (t, k) = (predicate_term(g, cx, w, d), small(g, cx, 16));
            cx.bin(BinOp::Mul, t, k).unwrap()
        }
        6 => {
            let t = predicate_term(g, cx, w, d);
            let m = cx
                .constant_u64(width, (1u64 << g.rng.below(u64::from(w) + 1)) - 1)
                .unwrap();
            cx.bin(BinOp::And, t, m).unwrap()
        }
        7 => {
            let (t, k) = (predicate_term(g, cx, w, d), small(g, cx, 4));
            cx.bin(BinOp::Or, t, k).unwrap()
        }
        8 => {
            let t = predicate_term(g, cx, w, d);
            let k = BitVec::wrapping_from_u64(width, 2 + g.rng.below(6));
            let k = cx.constant(&k).unwrap();
            let op = [
                BinOp::URem,
                BinOp::URem,
                BinOp::SRem,
                BinOp::SRem,
                BinOp::UDiv,
                BinOp::SDiv,
            ][g.rng.below(6) as usize];
            cx.bin(op, t, k).unwrap()
        }
        9 => {
            let t = predicate_term(g, cx, w, d);
            let s = cx.constant_u64(width, g.rng.below(u64::from(w))).unwrap();
            cx.bin(BinOp::Shl, t, s).unwrap()
        }
        _ => {
            let (c, a, b) = (
                predicate(g, cx, w, 0),
                predicate_term(g, cx, w, d),
                predicate_term(g, cx, w, d),
            );
            cx.select(c, a, b).unwrap()
        }
    }
}

/// A 1-bit predicate over [`predicate_term`]s: comparisons of two terms or of a term with a
/// constant, under `& | ^ ~`.
fn predicate(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> Expr {
    if depth == 0 || g.rng.chance(1, 3) {
        let a = predicate_term(g, cx, w, 3);
        let b = if g.rng.chance(1, 3) {
            let v = BitVec::wrapping_from_u64(Width::new(w).unwrap(), g.rng.below(16));
            cx.constant(&v).unwrap()
        } else {
            predicate_term(g, cx, w, 3)
        };
        let op = [
            CmpOpExt::Eq,
            CmpOpExt::Ne,
            CmpOpExt::Eq,
            CmpOpExt::Ne,
            CmpOpExt::Ult,
            CmpOpExt::Slt,
        ][g.rng.below(6) as usize];
        return cx.cmp(op, a, b).unwrap();
    }
    let p = predicate(g, cx, w, depth - 1);
    if g.rng.chance(1, 4) {
        return cx.un(UnOp::Not, p).unwrap();
    }
    let q = predicate(g, cx, w, depth - 1);
    let op = [BinOp::And, BinOp::Or, BinOp::Xor][g.rng.below(3) as usize];
    cx.bin(op, p, q).unwrap()
}

/// Predicates decided by residues: random predicates over squares, products, masks and
/// remainders are folded only when constant (exhaustively checked), and many are.
#[test]
fn residue_predicates_are_sound() {
    residue_predicates_are_sound_cases(1000);
}

/// [`residue_predicates_are_sound`] over 3000 random cases.
#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn residue_predicates_are_sound_heavy() {
    residue_predicates_are_sound_cases(3000);
}

fn residue_predicates_are_sound_cases(cases: usize) {
    let eng = engine(vec![Phase::Compares]);
    let mut g = generator(0x0b5c_7e11);
    let mut rng = Rng(53);
    let mut decided = 0;
    for _ in 0..cases {
        let mut cx = Context::new();
        let w = 1 + g.rng.below(6) as u16;
        let p = predicate(&mut g, &mut cx, w, 2);
        let out = eng.run(&mut cx, &[p], Run::default()).unwrap();
        let r = out.roots[0];
        assert!(
            equivalent(&mut cx, p, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(p),
            cx.display(r.expr)
        );
        decided += u64::from(r.changed && cx.const_val(cx.id(r.expr).unwrap()).is_some());
    }
    assert!(decided > 300 * cases as u64 / 3000, "{decided}");
}

/// The decision itself, on its own: a predicate it calls constant is constant (exhaustively
/// checked), and it finds many of the constant ones the generator makes (those without a
/// product of a value with itself, or with comparisons only full values decide, it leaves).
#[test]
fn residue_decision_is_sound() {
    let mut g = generator(0x5e4c_0de1);
    let mut rng = Rng(54);
    let (mut constant, mut decided) = (0, 0);
    for _ in 0..4000 {
        let mut cx = Context::new();
        let w = 1 + g.rng.below(6) as u16;
        let p = predicate(&mut g, &mut cx, w, 2);
        let id = cx.id(p).unwrap();
        let (got, _) = super::predicate::constant(&cx, super::predicate::Pred::Node(id));
        let t = cx.bool(true).unwrap();
        let f = cx.bool(false).unwrap();
        let truth = if equivalent(&mut cx, p, t, &mut rng) {
            Some(true)
        } else if equivalent(&mut cx, p, f, &mut rng) {
            Some(false)
        } else {
            None
        };
        if let Some(v) = got {
            assert_eq!(truth, Some(v), "W={w}: {} is not {v}", cx.display(p));
            decided += 1;
        }
        constant += u32::from(truth.is_some() && cx.const_val(id).is_none());
    }
    assert!(decided * 2 > constant, "{decided} of {constant}");
}

/// The opaque predicates of number theory, as obfuscators write them, fold at every width; the
/// ones that are not constant on machine integers (a product that wraps) stay.
#[test]
fn opaque_predicate_fixtures() {
    let eng = Engine::standard();
    for w in [8, 32, 64, 128] {
        for (src, want) in [
            ("x * x != 7 * y * y - 1", "1:1"),
            ("7 * y * y - 1 == x * x", "0:1"),
            ("x * x + 1 != 7 * y * y", "1:1"),
            ("(x * x ^ (7 * y * y - 1)) == 0", "0:1"),
            ("x * x + x == 2 * y + 1", "0:1"),
            ("x * (x + 1) == 2 * y + 1", "0:1"),
            ("x * x == 8 * y + 5", "0:1"),
            ("x * x + y * y == 4 * z + 3", "0:1"),
            ("x * x - y * y != 4 * z + 2", "1:1"),
            ("x * x + y * y + z * z != 7", "1:1"),
            ("x * x * x != 4 * y + 2", "1:1"),
            ("(x * x | 1) != 7 * y * y - 1", "1:1"),
            ("((x & 1) == 0) | ((x * x & 7) == 1)", "1:1"),
            ("(urem(x * (x - 1), 2) == 0) | (y <s 10)", "1:1"),
            ("(x * x == 7 * y * y - 1) | (x == 3)", "x == 3"),
            ("(x * x != 7 * y * y - 1) & (x == 3)", "x == 3"),
            // Disguised: the sum `x·x + t` and the difference `x·x − (7·y·y − 1)` as MBA.
            ("(x * x ^ t) + 2 * (x * x & t) == 7 * y * y - 1 + t", "0:1"),
            (
                "((x * x | (7 * y * y - 1)) - (x * x & (7 * y * y - 1))) != 0",
                "1:1",
            ),
            ("select(x * x != 7 * y * y - 1, z + 1, z * 3)", "z + 1"),
            // Not constant: 2 is a difference of these modulo every power of two.
            ("x * x != 7 * y * y + 2", "y * 7 * y + 2 != x * x"),
        ] {
            assert_eq!(simplify(&eng, src, w), want, "{src} at {w} bits");
        }
    }
    // Signed remainders keep the low bits of their dividend; over values that do not wrap
    // (zero- or sign-extended, unsigned or signed), residues modulo other numbers decide: no
    // square is 3 modulo 7 or 2 modulo 3, `x² + 1` is never a multiple of 3, `x³ − x` always
    // one of 6, a square is not negative. `None`: not a constant (a product that wraps).
    for (src, want) in [
        ("srem(x * (x + 1), 2) == 0", Some("1:1")),
        ("srem(x * x, 4) != 2", Some("1:1")),
        ("srem((2 * x + 1) * (2 * x + 1), 8) != 3", Some("1:1")),
        ("urem(zext<32>(a:8) * zext<32>(a:8), 7) != 3", Some("1:1")),
        (
            "urem(zext<64>(c:16) * zext<64>(c:16) + 1, 3) != 0",
            Some("1:1"),
        ),
        ("urem(zext<64>(d:32) * zext<64>(d:32), 7) != 3", Some("1:1")),
        ("urem(zext<64>(d:32) * zext<64>(d:32), 3) == 2", Some("0:1")),
        (
            "urem(zext<64>(d:32) * (zext<64>(d:32) + 1), 6) != 1",
            Some("1:1"),
        ),
        // A divisibility test: `d² + 1` is never a multiple of 3.
        (
            "udiv(zext<64>(d:32) * zext<64>(d:32) + 1, 3) * 3 == zext<64>(d:32) * zext<64>(d:32) + 1",
            Some("0:1"),
        ),
        (
            "zext<64>(d:32) * zext<64>(d:32) + 1 != 3 * zext<64>(e:32)",
            Some("1:1"),
        ),
        (
            "urem(zext<32>(a:8) * (zext<32>(a:8) + 1) * (zext<32>(a:8) + 2), 3) == 0",
            Some("1:1"),
        ),
        (
            "srem(sext<64>(c:16) * sext<64>(c:16) + 1, 3) != 0",
            Some("1:1"),
        ),
        (
            "srem(sext<64>(c:16) * sext<64>(c:16) * sext<64>(c:16) - sext<64>(c:16), 6) == 0",
            Some("1:1"),
        ),
        ("sext<32>(a:8) * sext<32>(a:8) >=s 0", Some("1:1")),
        ("sext<64>(d:32) * sext<64>(d:32) >=s 0", Some("1:1")),
        ("x * x >=s 0", None),
        // Wraps: x = 7 at 8 bits, 336 mod 256 = 80.
        ("urem(x * x * x - x, 3) == 0", None),
        ("urem(x * x, 7) != 3", None),
    ] {
        let mut cx = Context::new();
        let e = cx.parse(src, &ParseOptions::width(Width::W8)).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        let got = cx.display(out.expr).to_string();
        match want {
            Some(want) => assert_eq!(got, want, "{src}"),
            None => assert!(
                cx.const_val(cx.id(out.expr).unwrap()).is_none(),
                "{src}: {got}"
            ),
        }
    }
}

/// A predicate over one value that only its low bits decide is recovered as the test of those
/// bits: parity and alignment tests in disguise.
#[test]
fn residue_tests_are_recovered() {
    let eng = Engine::standard();
    for w in [8, 32, 64] {
        for (src, want) in [
            ("((x * x) & 7) == 1", "trunc<1>(x)"),
            ("((x * x) & 7) != 1", "~trunc<1>(x)"),
            ("((x * x) & 3) == 0", "~trunc<1>(x)"),
            ("((x * x) & 15) == 0", "trunc<2>(x) == 0"),
            ("((x * x * x) & 7) == 1", "trunc<3>(x) == 1"),
            // 1 or 2 modulo 4.
            ("((x * (x + 1)) & 3) == 2", "trunc<2>(x) - 1 <=u 1"),
        ] {
            assert_eq!(simplify(&eng, src, w), want, "{src} at {w} bits");
        }
    }
}

/// `Context::prove` answers what residues decide, about expressions it does not build: the
/// equality, the order, the test against zero and the bit.
#[test]
fn prove_decides_by_residues() {
    use crate::{Query, Truth};
    for w in [8, 64] {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let sq = cx.parse("x * x", &o).unwrap();
        let rhs = cx.parse("7 * y * y - 1", &o).unwrap();
        let d = cx.bin(BinOp::Sub, sq, rhs).unwrap();
        // `x·(x + 1)` is even: bit 0 is 0.
        let e = cx.parse("x * (x + 1) + y * y * 4", &o).unwrap();
        let open = cx.parse("x * x != 7 * y * y + 2", &o).unwrap();
        let before = cx.len();
        assert_eq!(cx.prove(Query::Eq(sq, rhs)).unwrap(), Truth::False);
        assert_eq!(
            cx.prove(Query::Cmp(CmpOpExt::Ne, rhs, sq)).unwrap(),
            Truth::True
        );
        assert_eq!(cx.prove(Query::IsZero(d)).unwrap(), Truth::False);
        assert_eq!(cx.prove(Query::IsNonZero(d)).unwrap(), Truth::True);
        let bit = |value| Query::Bit { e, bit: 0, value };
        assert_eq!(cx.prove(bit(false)).unwrap(), Truth::True);
        assert_eq!(cx.prove(bit(true)).unwrap(), Truth::False);
        assert_eq!(cx.prove(Query::IsNonZero(open)).unwrap(), Truth::Unknown);
        // Nothing was built for the questions.
        assert_eq!(cx.len(), before);
    }
}

/// Sign extension spelled with shifts or with xor and a subtraction, and bit tests through a
/// mask: equivalent at every shift and mask at small widths, and recognized.
#[test]
fn sign_extension_and_bit_test_idioms() {
    let eng = Engine::standard();
    let mut rng = Rng(48);
    for w in 2..=8u16 {
        let width = Width::new(w).unwrap();
        let o = ParseOptions::width(width);
        for c in 1..w {
            let mut cx = Context::new();
            let e = cx.parse(&format!("(x << {c}) >>s {c}"), &o).unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            assert!(equivalent(&mut cx, e, out.expr, &mut rng));
            assert_eq!(
                cx.display(out.expr).to_string(),
                format!("sext<{w}>(trunc<{}>(x))", w - c)
            );
            let (m, h) = ((1u64 << c) - 1, 1u64 << (c - 1));
            let e = cx.parse(&format!("((x & {m}) ^ {h}) - {h}"), &o).unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            assert!(
                equivalent(&mut cx, e, out.expr, &mut rng),
                "{}",
                cx.display(e)
            );
            if c > 1 {
                assert_eq!(
                    cx.display(out.expr).to_string(),
                    format!("sext<{w}>(trunc<{c}>(x))")
                );
            }
        }
        for k in 0..w {
            let mut cx = Context::new();
            for (src, set) in [
                (format!("(x & {}) != 0", 1u64 << k), true),
                (format!("(x & {}) == 0", 1u64 << k), false),
            ] {
                let e = cx.parse(&src, &o).unwrap();
                let out = eng.simplify(&mut cx, e).unwrap();
                assert!(equivalent(&mut cx, e, out.expr, &mut rng), "{src}");
                let s = cx.display(out.expr).to_string();
                if k + 1 < w {
                    let bit = if k == 0 {
                        "trunc<1>(x)".to_string()
                    } else {
                        format!("extract<{k}, 1>(x)")
                    };
                    assert_eq!(s, if set { bit } else { format!("~{bit}") }, "{src}");
                }
            }
        }
    }
}

/// Case splits on condition masks: random linear and bitwise expressions reading `sext(c)`,
/// `-zext(c)` or a sign mask are equivalent after the split, exhaustively at small widths.
#[test]
fn case_splits_are_sound() {
    let eng = engine(vec![Phase::Linear]);
    let mut g = generator(0xca5e);
    let mut rng = Rng(49);
    let mut changed = 0;
    for i in 0..1500 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            32
        } else {
            2 + g.rng.below(4) as u16
        };
        let width = Width::new(w).unwrap();
        let c = cx.symbol("p", Width::W1).unwrap();
        let x = cx.symbol("x", width).unwrap();
        let m = match g.rng.below(3) {
            0 => cx.sext(c, width).unwrap(),
            1 => {
                let z = cx.zext(c, width).unwrap();
                cx.un(UnOp::Neg, z).unwrap()
            }
            _ => {
                let k = cx.constant_u64(width, u64::from(w) - 1).unwrap();
                cx.bin(BinOp::AShr, x, k).unwrap()
            }
        };
        let other = linear_expr(&mut g, &mut cx, w, 2);
        let ops = [BinOp::Add, BinOp::Sub, BinOp::Xor, BinOp::Or, BinOp::And];
        let op1 = ops[g.rng.below(5) as usize];
        let op2 = ops[g.rng.below(5) as usize];
        let inner = cx.bin(op1, other, m).unwrap();
        let e = cx.bin(op2, inner, m).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
    }
    assert!(changed > 100, "{changed}");
    // The conditional negation.
    let mut cx = Context::new();
    let e = cx
        .parse(
            "(x ^ sext<8>(c:1)) - sext<8>(c:1)",
            &ParseOptions::width(Width::W8),
        )
        .unwrap();
    let out = Engine::standard().simplify(&mut cx, e).unwrap();
    assert_eq!(cx.display(out.expr).to_string(), "select(c, -x, x)");
}

#[test]
fn demanded_fixtures() {
    let eng = engine(vec![Phase::Demanded]);
    let same = |src: &str, want: &str, w: u16| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    same("(x | 0xff00) & 0x00ff", "x & 0xff", 16);
    same("((x & 0xf0) + y) & 0x0f", "y & 0x0f", 8);
    same("trunc<8>((x << 8) | y)", "trunc<8>(y)", 16);
    same("(x & 0xffff0000) >>u 16", "x >>u 16", 32);
    same("((x ^ 0xff) | 0xf0) & 0x0f", "~x & 15", 8);
    same(
        "(zext<16>(a:8) + (b << 8)) & 0xff",
        "zext<16>(a:8) & 0xff",
        16,
    );
    same(
        "concat(a:8 ^ b:8, l:8) & 0x00ff",
        "zext<16>(l:8) & 0xff",
        16,
    );
}

// ----- regressions from the M5 review --------------------------------------------------------------

struct VetoAll;

impl Hooks for VetoAll {
    fn admit(&self, _: &Context, _: Expr, _: Expr, _: crate::engine::By<'_>) -> bool {
        false
    }
}

#[test]
fn passes_obey_the_host_veto_and_report_events() {
    let o = ParseOptions::width(Width::W8);
    let mut cx = Context::new();
    let e = cx.parse("((x + r) - r) & ((y ^ k) ^ k)", &o).unwrap();
    let out = Engine::standard()
        .run(
            &mut cx,
            &[e],
            Run {
                hooks: Some(&VetoAll),
                ..Run::default()
            },
        )
        .unwrap();
    assert!(!out.roots[0].changed, "{}", cx.display(out.roots[0].expr));
    assert!(out.stats.hook_vetoes > 0);
    // Applied events name the pass, and agree with the counters.
    struct Passes(u64);
    impl crate::engine::Observer for Passes {
        fn event(&mut self, e: crate::engine::Event<'_>) {
            if let crate::engine::Event::Applied {
                by: crate::engine::By::Pass(_),
                ..
            } = e
            {
                self.0 += 1;
            }
        }
    }
    let mut obs = Passes(0);
    let mut cx = Context::new();
    let e = cx.parse("((x + r) - r) & ((y ^ k) ^ k)", &o).unwrap();
    let out = Engine::standard()
        .run(
            &mut cx,
            &[e],
            Run {
                observer: Some(&mut obs),
                ..Run::default()
            },
        )
        .unwrap();
    let changed: u64 = out.stats.passes.values().map(|c| c.changed).sum();
    assert!(changed > 0);
    assert_eq!(obs.0, changed);
    assert!(out.stats.pass_work > 0);
}

#[test]
fn demanded_obeys_fold_known() {
    struct NoFold;
    impl Hooks for NoFold {
        fn fold_known(&self, _: &Context, _: Expr) -> bool {
            false
        }
    }
    let eng = engine(vec![Phase::Demanded]);
    let mut cx = Context::new();
    let e = cx
        .parse("(x * 16) & 0x0f", &ParseOptions::width(Width::W8))
        .unwrap();
    let out = eng
        .run(
            &mut cx,
            &[e],
            Run {
                hooks: Some(&NoFold),
                ..Run::default()
            },
        )
        .unwrap();
    assert!(!out.roots[0].changed, "{}", cx.display(out.roots[0].expr));
    // Without the hook it folds.
    assert_eq!(simplify(&eng, "(x * 16) & 0x0f", 8), "0:8");
}

#[test]
fn demanded_keeps_each_leaf_once_across_a_phase_run() {
    // A ripple chain read through `<< 1`: every level shares its operands' leaves, and the
    // leaves a step keeps for the next ones held each level's operands' copies, so they
    // doubled at every level (2^48 at 48 bits, past any memory). Kept once each, the run
    // takes a moment.
    let mut src = String::from("let a0 = x; let b0 = y; ");
    for k in 0..48 {
        src += &format!(
            "let a{n} = a{k} ^ b{k}; let b{n} = (a{k} & b{k}) << 1; ",
            n = k + 1
        );
    }
    src += "a48 << 1";
    let eng = engine(vec![Phase::Demanded]);
    let mut cx = Context::new();
    let e = cx
        .parse(&src, &ParseOptions::width(Width::new(48).unwrap()))
        .unwrap();
    let before = dag(&mut cx, &[e]);
    let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
    let r = out.roots[0].expr;
    assert!(dag(&mut cx, &[r]) < before);
    assert!(equivalent(&mut cx, e, r, &mut Rng(48)));
}

#[test]
fn demanded_reduces_constants_to_their_residues() {
    let eng = engine(vec![Phase::Demanded]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    // `43 · 0xbe83 = 0x200001`: an inverse modulo 2^17 that is none at 64 bits.
    same("(x * 0x200001) & 0x1ffff", "x & 0x1ffff");
    same("((x * 0x200001) + y) & 0x1ffff", "(x + y) & 0x1ffff");
    same("trunc<17>(x * 0x200001)", "trunc<17>(x)");
    same("(x * 0x100000001) & 0xffffffff", "x & 0xffffffff");
    // The residue extended with its sign when that is the smaller: `0x3ffff` is −1 there.
    same("(x * 0x3ffff) & 0x1ffff", "-x & 0x1ffff");
    // Read at every bit, or already a residue: unchanged.
    same("x * 0x200001", "x * 0x200001");
    same("(x + 0x1ffff) & 0x1ffff", "(x + 0x1ffff) & 0x1ffff");
}

fn dag(cx: &mut Context, roots: &[Expr]) -> u32 {
    match cx.dag_size(roots, u32::MAX).unwrap() {
        crate::Bounded::Exact(n) | crate::Bounded::AtLeast(n) => n,
    }
}

#[test]
fn shared_regions_never_grow_the_dag() {
    for phases in [
        vec![Phase::Linear],
        vec![Phase::Xor],
        Strategy::standard().phases,
    ] {
        let eng = engine(phases);
        let w = Width::W32;
        for op in [BinOp::Add, BinOp::Xor] {
            // (S - a0) * S with S a 60-term chain: S survives, so re-emitting S - a0 grows.
            let mut cx = Context::new();
            let mut s = cx.symbol("a0", w).unwrap();
            let mut atoms = vec![s];
            for i in 1..60 {
                let a = cx.symbol(format!("a{i}").as_str(), w).unwrap();
                atoms.push(a);
                s = cx.bin(op, s, a).unwrap();
            }
            let inv = if op == BinOp::Add {
                BinOp::Sub
            } else {
                BinOp::Xor
            };
            let d = cx.bin(inv, s, atoms[0]).unwrap();
            let root = cx.bin(BinOp::Mul, d, s).unwrap();
            let before = dag(&mut cx, &[root]);
            let out = eng.run(&mut cx, &[root], Run::default()).unwrap();
            let after = dag(&mut cx, &[out.roots[0].expr]);
            assert!(after <= before, "{op:?}: {before} -> {after}");
            // Many roots sharing S.
            let roots: Vec<Expr> = atoms.iter().map(|&a| cx.bin(inv, s, a).unwrap()).collect();
            let before = dag(&mut cx, &roots);
            let out = eng.run(&mut cx, &roots, Run::default()).unwrap();
            let results: Vec<Expr> = out.roots.iter().map(|r| r.expr).collect();
            let after = dag(&mut cx, &results);
            assert!(after <= before, "{op:?}, 60 roots: {before} -> {after}");
        }
    }
}

#[test]
fn long_chains_build_no_garbage() {
    let eng = engine(vec![Phase::Linear, Phase::Xor]);
    let mut cx = Context::new();
    let w = Width::W32;
    // A chain in an order unrelated to the canonical one, so every re-emission would differ.
    let mut rng = Rng(77);
    let mut names: Vec<u32> = (0..20_000).collect();
    for i in (1..names.len()).rev() {
        let j = rng.below(i as u64 + 1) as usize;
        names.swap(i, j);
    }
    let mut e = cx.symbol(format!("s{}", names[0]).as_str(), w).unwrap();
    for &k in &names[1..] {
        let a = cx.symbol(format!("s{k}").as_str(), w).unwrap();
        e = cx.bin(BinOp::Add, e, a).unwrap();
    }
    let nodes = cx.len() as u64;
    let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
    assert_eq!(out.roots[0].end, End::Completed);
    assert!(
        out.stats.new_nodes < nodes / 10,
        "{} new nodes for {nodes}",
        out.stats.new_nodes
    );
}

// ----- linear MBA ---------------------------------------------------------------------------------

/// A random linear MBA: a random integer combination of random bitwise functions of up to four
/// atoms (symbols, or a non-linear compound), plus a constant.
fn linear_mba_expr(g: &mut Gen, cx: &mut Context, w: u16) -> Expr {
    let width = Width::new(w).unwrap();
    let natoms = 1 + g.rng.below(4);
    let atoms: Vec<Expr> = (0..natoms)
        .map(|k| {
            if k == 3 {
                let a = cx.symbol("a", width).unwrap();
                let b = cx.symbol("b", width).unwrap();
                cx.bin(BinOp::Mul, a, b).unwrap()
            } else {
                cx.symbol(["a", "b", "c"][k as usize], width).unwrap()
            }
        })
        .collect();
    let terms = 1 + g.rng.below(4);
    let v = g.constant(w);
    let mut e = cx.constant(&v).unwrap();
    for _ in 0..terms {
        // A random bitwise function over the atoms.
        let mut f = atoms[g.rng.below(natoms) as usize];
        for _ in 0..g.rng.below(4) {
            let other = atoms[g.rng.below(natoms) as usize];
            f = match g.rng.below(4) {
                0 => cx.un(UnOp::Not, f).unwrap(),
                1 => cx.bin(BinOp::And, f, other).unwrap(),
                2 => cx.bin(BinOp::Or, f, other).unwrap(),
                _ => cx.bin(BinOp::Xor, f, other).unwrap(),
            };
        }
        // Sometimes under a non-uniform mask (then no longer a bitwise function of the atoms
        // alone: an atom of the fragment, and the pass must not read the mask as uniform).
        if g.rng.chance(1, 4) {
            let m = g.constant(w);
            let m = cx.constant(&m).unwrap();
            f = cx.bin(BinOp::And, f, m).unwrap();
        }
        let k = g.constant(w);
        let k = cx.constant(&k).unwrap();
        let t = cx.bin(BinOp::Mul, f, k).unwrap();
        e = cx
            .bin(
                if g.rng.chance(1, 3) {
                    BinOp::Sub
                } else {
                    BinOp::Add
                },
                e,
                t,
            )
            .unwrap();
    }
    e
}

#[test]
fn linear_mba_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::LinearMba]);
    let mut g = generator(0x3ba);
    let mut rng = Rng(88);
    let mut changed = 0;
    for i in 0..2000 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [16, 64, 128, 257, 512][g.rng.below(5) as usize]
        } else {
            1 + g.rng.below(6) as u16
        };
        let e = if i % 4 == 0 {
            g.expr(&mut cx, w.min(6), 4).0
        } else {
            linear_mba_expr(&mut g, &mut cx, w)
        };
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {} -> {} (from {})",
            cx.display(r.expr),
            cx.display(again.roots[0].expr),
            cx.display(e)
        );
    }
    assert!(changed > 200, "{changed}");
}

#[test]
fn linear_mba_identities() {
    let eng = engine(vec![Phase::LinearMba]);
    let same = |src: &str, want: &str, w: u16| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    for w in [8, 32, 64, 128] {
        same("(x ^ y) + 2 * (x & y)", "x + y", w);
        same("(x | y) - (x & ~y) - (~x & y)", "x & y", w);
        same("(x + y) - 2 * (x & y)", "x ^ y", w);
        same("2 * (x | y) - (x ^ y)", "x + y", w);
        same("(x ^ y) - 2 * (~x & y)", "x - y", w);
        same("(x & y) + (x | y)", "x + y", w);
        same("x + y - (x | y)", "x & y", w);
        same("~x + (x & y) + (x & ~y) + 1", "0", w);
        // Non-uniform masks are not bitwise functions of the atoms.
        same("(x & 0xf0) + (y & 0x0f)", "(x & 0xf0) + (y & 0x0f)", w);
        // Atoms may be compound: (p * q) plays the role of x.
        same("((p * q) ^ r) + 2 * ((p * q) & r)", "p * q + r", w);
    }
}

/// Fragments through extensions of narrow values (see the module notes of `linear_mba`): the
/// function under a cast is read over the atoms lifted by that cast.
#[test]
fn linear_mba_reads_through_extensions() {
    let eng = engine(vec![Phase::LinearMba]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    // Casts of the atoms themselves (as the input spells them)...
    same(
        "(zext<64>(a:32) ^ zext<64>(b:32)) + 2 * (zext<64>(a:32) & zext<64>(b:32))",
        "zext<64>(a) + zext<64>(b)",
    );
    same(
        "(sext<64>(a:32) ^ sext<64>(b:32)) + 2 * (sext<64>(a:32) & sext<64>(b:32))",
        "sext<64>(a) + sext<64>(b)",
    );
    // ...and casts of bitwise functions of them (as the rules spell them).
    same(
        "zext<64>(a:32 ^ b:32) + 2 * zext<64>(a:32 & b:32)",
        "zext<64>(a) + zext<64>(b)",
    );
    same(
        "sext<64>(a:32 ^ b:32) + 2 * sext<64>(a:32 & b:32)",
        "sext<64>(a) + sext<64>(b)",
    );
    same(
        "sext<64>(a:32 ^ b:32) - 2 * sext<64>(~a:32 & b:32)",
        "sext<64>(a) - sext<64>(b)",
    );
    // (What the pass leaves of a sum is linear: the linear pass finishes it.)
    {
        let eng = engine(vec![Phase::LinearMba, Phase::Linear]);
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let src = "zext<64>(a:32 | b:32) + zext<64>(a:32 & b:32) - zext<64>(a:32) - zext<64>(b:32)";
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse("0", &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    }
    // A zero extension of a function that is all ones at 0 is the function plus 2^W.
    same("zext<64>(~a:32) + zext<64>(a:32)", "0xffffffff");
    // (`~a & b` is 0 at 0: no `2^W` here.)
    same(
        "zext<64>(a:32 ^ b:32) - 2 * zext<64>(~a:32 & b:32)",
        "zext<64>(a) - zext<64>(b)",
    );
    same(
        "zext<64>(~a:32 | b:32) + zext<64>(a:32 & ~b:32)",
        "0xffffffff",
    );
    // A value read under casts of two kinds: the second cast is an atom (no identity holds
    // over independent lifted atoms), and nothing is rewritten.
    same(
        "zext<64>(a:32 & b:32) + sext<64>(a:32 & b:32)",
        "zext<64>(a & b) + sext<64>(a & b)",
    );
}

/// A tree of `& | ^ ~` over extensions of one kind and width, with constants, is the extension
/// of the tree over the operands (see `bitwise::hoist_cast`).
#[test]
fn bitwise_hoists_a_common_extension() {
    let eng = engine(vec![Phase::Bitwise]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    same("zext<64>(a:32) & ~zext<64>(b:32)", "zext<64>(a & ~b)");
    same("~zext<64>(a:32) & 0xffffffff", "zext<64>(~a)");
    same(
        "~(zext<64>(a:32) | zext<64>(b:32)) & 0xffffffff",
        "zext<64>(~(a | b))",
    );
    same("sext<64>(a:32) & ~sext<64>(b:32)", "sext<64>(a & ~b)");
    // The or below hoists; with one extension left and a constant, hoisting the xor would
    // trade the constant for a narrower one, no smaller (a sign extension of its low bits or
    // not).
    same(
        "(sext<64>(a:32) | sext<64>(b:32)) ^ 0xffffffff80000001",
        "sext<64>(a | b) ^ 0xffffffff80000001",
    );
    same(
        "(sext<64>(a:32) | sext<64>(b:32)) ^ 0xffffffff00000001",
        "sext<64>(a | b) ^ 0xffffffff00000001",
    );
    same(
        "(sext<64>(a:32) | sext<64>(b:32)) & 0xffffffff80000001 & sext<64>(c:32)",
        "sext<64>((a | b) & 0x80000001 & c)",
    );
    // All ones above the width: the complement of a zero extension of the complement, where
    // that is smaller (a constant absorbed); `~zext(a) | zext(b)` and `~zext(a & ~b)` are the
    // same size, and so are the forms once the trees below are hoisted.
    same("~zext<64>(a:32) | 0xffffffff00000000", "~zext<64>(a)");
    same(
        "~(zext<64>(a:32) | zext<64>(b:32)) | (zext<64>(c:32) & zext<64>(d:32))",
        "~zext<64>(a | b) | zext<64>(c & d)",
    );
    same(
        "~zext<64>(a:32) | zext<64>(b:32)",
        "~zext<64>(a) | zext<64>(b)",
    );
    // A constant that is no sign extension of its low bits stops the hoist (the xor below
    // still hoists), and so do extensions of two widths.
    same(
        "(sext<64>(a:32) ^ sext<64>(b:32)) | 0xffffffff00000000",
        "sext<64>(a ^ b) | 0xffffffff00000000",
    );
    same(
        "zext<64>(a:32) & zext<64>(c:16)",
        "zext<64>(a) & zext<64>(c)",
    );
}

/// `zext(~t)` is `lowmask − zext(t)` and `sext(~t)` is `−1 − sext(t)` to the linear pass,
/// where the extension of `t` exists.
#[test]
fn linear_reads_extended_complements() {
    let eng = engine(vec![Phase::Linear]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    same("sext<64>(a:32) + sext<64>(~a:32)", "-1");
    same("zext<64>(a:32) + zext<64>(~a:32)", "0xffffffff");
    same("zext<64>(a:32) * 3 + zext<64>(~a:32) * 3", "0x2fffffffd");
    same(
        "sext<64>(a:32) * 2 + sext<64>(~a:32) * 2 + sext<64>(b:32)",
        "sext<64>(b) - 2",
    );
    // A lone complement stays: building its extension would make the sum look cheaper.
    same(
        "zext<64>(~a:32) + zext<64>(b:32)",
        "zext<64>(~a) + zext<64>(b)",
    );
}

/// A lone comparison with a constant is re-expressed on the deepest term it is a function
/// of where that is smaller (see `compares::step`): extensions, offsets and complements come
/// off.
#[test]
fn compares_reexpress_on_the_deeper_term() {
    let eng = engine(vec![Phase::Compares]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    same("sext<64>(a:32) <s 0", "a <=s -1");
    same("sext<64>(a:32) <s 5", "a <=s 4");
    same("zext<64>(a:32) <u 5", "a <=u 4");
    same("5 <u zext<64>(a:32)", "6 <=u a");
    same("sext<64>(a:32) + 3 <s 10", "a <=s 6");
    same("sext<64>(trunc<8>(x)) <s 0", "trunc<8>(x) <=s -1");
    // A range check on the narrow term beats one comparison on the wide one...
    same("zext<64>(a:32) - 3 <u 10", "a - 3 <=u 9");
    // ...but not one on the same term.
    same("(x + 3) <u 10", "x + 3 <u 10");
    // Nothing deeper: as it is.
    same("x <s 0", "x <s 0");
}

/// Extracts push through more (see the `casts` module notes): a doubled value, a sum or
/// product with an operand whose low bits are zero, straddled left shifts, arithmetic shifts.
#[test]
fn casts_push_through_doubling_zero_lows_and_arithmetic_shifts() {
    let eng = engine(vec![Phase::Casts]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    same("extract<1, 31>(x + x)", "trunc<31>(x)");
    same("extract<1, 63>(x + x)", "trunc<63>(x)");
    same("extract<8, 8>((x << 8) + (y & 0xff))", "trunc<8>(x)");
    same(
        "extract<8, 8>((x << 8) - (y & 0xff))",
        "extract<8, 8>((x << 8) - (y & 0xff))",
    );
    same("extract<8, 8>((y & 0xff) - (x << 8))", "-trunc<8>(x)");
    same(
        "extract<4, 8>((x & 0xfffffff0) * y)",
        "trunc<8>(y) * extract<4, 8>(x)",
    );
    same("trunc<32>(x >>s 8)", "extract<8, 32>(x)");
    same("extract<8, 8>(x >>s 60)", "sext<8>(extract<63, 1>(x))");
    same("extract<8, 8>(x >>s 52)", "sext<8>(extract<60, 4>(x))");
}

#[test]
fn casts_split_sums_where_the_carry_is_decided() {
    let eng = engine(vec![Phase::Casts]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    // Three 20-bit lanes, guard bits 20, 41 and 62 clear in both: nothing carries into a lane.
    same(
        "extract<21, 20>((x & 0x3ffffdffffefffff) + (y & 0x3ffffdffffefffff))",
        "extract<21, 20>(x) + extract<21, 20>(y)",
    );
    // `a − b` is `a + ~b + 1`: a guard bit set in `a` and clear in `b` borrows nothing, one
    // clear in `a` and set in `b` always borrows.
    same(
        "extract<21, 20>((x | 0x100000) - (y & ~0x100000))",
        "extract<21, 20>(x) - extract<21, 20>(y)",
    );
    same(
        "extract<21, 20>((x & ~0x100000) - (y | 0x100000))",
        "extract<21, 20>(x) - extract<21, 20>(y) - 1",
    );
    // Undecided: unchanged.
    same("extract<21, 20>(x + y)", "extract<21, 20>(x + y)");
    // A shift straddling the slice: the operand's low bits, shifted at the narrow width.
    same("trunc<8>(zext<16>(a:8) << 3)", "a:8 << 3");
}

// ----- shuffle ------------------------------------------------------------------------------------

/// A random value assembled from slices: masks, shifts, rotations, extensions, extracts,
/// concats, byte swaps, and | ^ + of pieces.
fn shuffle_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 5) {
        return match g.rng.below(4) {
            0 => {
                let v = g.constant(w);
                cx.constant(&v).unwrap()
            }
            k => {
                let name = format!("{}{w}", ["x", "y", "z"][(k - 1) as usize]);
                cx.symbol(name.as_str(), width).unwrap()
            }
        };
    }
    let d = depth - 1;
    loop {
        match g.rng.below(9) {
            0 => {
                let x = shuffle_expr(g, cx, w, d);
                let m = g.constant(w);
                let m = cx.constant(&m).unwrap();
                return cx.bin(BinOp::And, x, m).unwrap();
            }
            1 => {
                let (x, y) = (shuffle_expr(g, cx, w, d), shuffle_expr(g, cx, w, d));
                let op = [BinOp::Or, BinOp::Xor, BinOp::Add][g.rng.below(3) as usize];
                return cx.bin(op, x, y).unwrap();
            }
            2 => {
                let x = shuffle_expr(g, cx, w, d);
                let kv = crate::BitVec::wrapping_from_u64(width, g.rng.below(u64::from(w) + 2));
                let k = cx.constant(&kv).unwrap();
                let op = [
                    BinOp::Shl,
                    BinOp::LShr,
                    BinOp::AShr,
                    BinOp::RotL,
                    BinOp::RotR,
                ][g.rng.below(5) as usize];
                return cx.bin(op, x, k).unwrap();
            }
            3 if w > 1 => {
                let from = 1 + g.rng.below(u64::from(w - 1)) as u16;
                let x = shuffle_expr(g, cx, from, d);
                return if g.rng.chance(1, 2) {
                    cx.zext(x, width).unwrap()
                } else {
                    cx.sext(x, width).unwrap()
                };
            }
            4 if w < 16 => {
                let from = w + 1 + g.rng.below(u64::from(16 - w)) as u16;
                let lo = g.rng.below(u64::from(from - w) + 1) as u16;
                let x = shuffle_expr(g, cx, from, d);
                return cx.extract(x, lo, width).unwrap();
            }
            5 if w > 1 => {
                let hw = 1 + g.rng.below(u64::from(w - 1)) as u16;
                let h = shuffle_expr(g, cx, hw, d);
                let l = shuffle_expr(g, cx, w - hw, d);
                return cx.concat(h, l).unwrap();
            }
            6 if w.is_multiple_of(8) => {
                let x = shuffle_expr(g, cx, w, d);
                return cx.un(UnOp::Bswap, x).unwrap();
            }
            7 | 8 => {
                // A split-and-recombine of one value: (x >> k) << k | x & lowmask(k).
                let x = shuffle_expr(g, cx, w, d);
                let k = g.rng.below(u64::from(w));
                let kc = cx.constant_u64(width, k).unwrap();
                let hi = cx.bin(BinOp::LShr, x, kc).unwrap();
                let hi = cx.bin(BinOp::Shl, hi, kc).unwrap();
                let m = crate::facts::known::low_mask(width, k as u32);
                let m = cx.constant(&m).unwrap();
                let lo = cx.bin(BinOp::And, x, m).unwrap();
                let op = [BinOp::Or, BinOp::Xor, BinOp::Add][g.rng.below(3) as usize];
                return cx.bin(op, hi, lo).unwrap();
            }
            _ => {}
        }
    }
}

#[test]
fn shuffle_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Shuffle]);
    let mut g = generator(0x5f1e);
    let mut rng = Rng(99);
    let mut changed = 0;
    for i in 0..2000 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [16, 32, 64, 128][g.rng.below(4) as usize]
        } else {
            1 + g.rng.below(8) as u16
        };
        let e = shuffle_expr(&mut g, &mut cx, w, 4);
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {} -> {} (from {})",
            cx.display(r.expr),
            cx.display(again.roots[0].expr),
            cx.display(e)
        );
    }
    assert!(changed > 200, "{changed}");
}

#[test]
fn shuffle_fixtures() {
    let eng = engine(vec![Phase::Shuffle]);
    let same = |src: &str, want: &str, w: u16| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    // Limb recomposition.
    same(
        "(zext<64>(extract<32, 32>(x:64)) << 32) | zext<64>(trunc<32>(x:64))",
        "x:64",
        64,
    );
    same("((x >>u 8) << 8) | (x & 0xff)", "x", 32);
    // Rotation spelled with shifts and a disjoint or.
    same("(x << 8) | (x >>u 24)", "rotl(x, 8)", 32);
    // Byte swap spelled with masks and shifts.
    same(
        "(x << 24) | ((x & 0xff00) << 8) | ((x >>u 8) & 0xff00) | (x >>u 24)",
        "bswap(x)",
        32,
    );
    // Overlapping pieces are not traced.
    same("(x << 1) | x", "(x << 1) | x", 8);
    // One source in place with constant bits: a mask and an or, not a concat.
    same("((x >>u 2) << 2) | 3", "x | 3", 8);
    same("((x >>u 4) << 4) | 5", "(x & 0xf0) | 5", 8);
    same("(x & 0xf0) | 0x0f", "x | 0x0f", 8);
    same("(x & -4) ^ 3", "x | 3", 8);
}

#[test]
fn deobfuscate_strategy_undoes_layered_masking() {
    let eng = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .verify(Verify::strict())
        .build()
        .unwrap();
    let mut rng = Rng(123);
    for (src, want) in [
        // Linear MBA of x + y, then additive masking, then an xor mask.
        ("(((x ^ y) + 2 * (x & y)) + r - r) ^ k ^ k", "x + y"),
        // A byte-shuffled value recomposed and masked.
        (
            "((((x << 24) | ((x & 0xff00) << 8) | ((x >>u 8) & 0xff00) | (x >>u 24)) + m) - m)",
            "bswap(x)",
        ),
        // Nested: an MBA over a recomposed limb.
        (
            "(((x >>u 8) << 8) | (x & 0xff)) - y + 2 * (y & ~(((x >>u 8) << 8) | (x & 0xff))) - ((((x >>u 8) << 8) | (x & 0xff)) ^ y)",
            "0",
        ),
    ] {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(out.stats.rejected, 0);
        assert!(equivalent(&mut cx, e, out.roots[0].expr, &mut rng));
        assert_eq!(
            out.roots[0].expr,
            want,
            "{src}: got {}",
            cx.display(out.roots[0].expr)
        );
    }
}

// ----- the MBA service ----------------------------------------------------------------------------

#[cfg(feature = "mba")]
mod mba_service {
    use super::*;
    use crate::mba::{
        Claim, EquivalenceProver, MOp, MbaAnswer, MbaBudget, MbaConfig, MbaExpr, MbaSolver,
        MbaTrust, MemoryCache, Verdict,
    };
    use std::sync::Arc;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn mba_engine(solver: Arc<dyn MbaSolver>, trust: MbaTrust) -> Engine {
        let cfg = MbaConfig {
            trust,
            ..MbaConfig::default()
        };
        Engine::builder()
            .builtin()
            .strategy(Strategy::new("mba", vec![Phase::Mba(cfg)]))
            .mba_solver(solver)
            .build()
            .unwrap()
    }

    /// Answers the questions it was scripted with (by content), and no others.
    struct Scripted(Vec<(MbaExpr, MbaExpr)>);

    impl MbaSolver for Scripted {
        fn id(&self) -> &str {
            "scripted"
        }
        fn solve(&self, p: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
            match self.0.iter().find(|(q, _)| q == p) {
                Some((_, a)) => MbaAnswer::Simplified {
                    expr: a.clone(),
                    claim: Claim::Proved,
                },
                None => MbaAnswer::NoSimpler,
            }
        }
    }

    #[test]
    fn a_rewrite_cycle_is_cut() {
        // `c = (x & 1)·(x & -2)` alone is smaller as `(x & 1)·(x ^ 1)`, and the context remembers
        // that; next to `(x & -2)²`, which keeps `x & -2` alive, it is the other way round. So the
        // answer for the sum brings back `c`, whose remembered answer rebuilds the sum, which is
        // still being worked out.
        let o = ParseOptions::width(Width::W8);
        let mut cx = Context::new();
        let n = cx
            .parse("((x & 1) * (x ^ 1)) + ((x & -2) * (x & -2))", &o)
            .unwrap();
        let r = cx
            .parse("((x & 1) * (x & -2)) + ((x & -2) * (x & -2))", &o)
            .unwrap();
        let c = cx.parse("(x & 1) * (x & -2)", &o).unwrap();
        let c1 = cx.parse("(x & 1) * (x ^ 1)", &o).unwrap();
        let lim = crate::mba::MbaLimits::default().with_min_nodes(0);
        let q = |cx: &Context, e: Expr| crate::mba::lower(cx, e, &lim).unwrap().0;
        let script = vec![(q(&cx, n), q(&cx, r)), (q(&cx, c), q(&cx, c1))];
        let trusted = MbaTrust::default().with_backend_certificates(true);
        let eng = mba_engine(Arc::new(Scripted(script)), trusted);
        let alone = eng.run(&mut cx, &[c], Run::default()).unwrap();
        assert_eq!(alone.roots[0].expr, c1);
        let out = eng.run(&mut cx, &[n], Run::default()).unwrap();
        assert_eq!(out.roots[0].end, End::Completed);
        assert!(out.stats.cycles_cut >= 1, "{:?}", out.stats);
        // Settled in the first round (the second only confirms it): the rewrite is made once.
        assert_eq!((out.stats.rounds, out.stats.mba.simplified), (2, 1));
        assert_eq!(out.roots[0].expr, r, "{}", cx.display(out.roots[0].expr));
        let mut rng = Rng(3);
        assert!(equivalent(&mut cx, n, out.roots[0].expr, &mut rng));
    }

    #[test]
    fn signature_solver_through_the_engine_is_sound() {
        let eng = mba_engine(Arc::new(crate::mba::SignatureSolver), MbaTrust::default());
        let mut g = generator(0x3bab);
        let mut rng = Rng(5);
        let mut changed = 0;
        for i in 0..800 {
            let mut cx = Context::new();
            let w = if i % 10 == 0 {
                64
            } else {
                1 + g.rng.below(6) as u16
            };
            let e = if i % 3 == 0 {
                g.expr(&mut cx, w.min(6), 4).0
            } else {
                linear_mba_expr(&mut g, &mut cx, w)
            };
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            assert!(equivalent(&mut cx, e, out.roots[0].expr, &mut rng));
            changed += u64::from(out.roots[0].changed);
        }
        assert!(changed > 50, "{changed}");
    }

    #[test]
    fn normal_form_solver_through_the_engine_is_sound() {
        let solver = Arc::new(crate::mba::NormalFormSolver::default());
        let no_trust = MbaTrust {
            backend_certificates: false,
            sampled: false,
        };
        let eng = mba_engine(solver.clone(), no_trust);
        let mut g = generator(0x9f5b);
        let mut rng = Rng(7);
        let mut changed = 0;
        for i in 0..800 {
            let mut cx = Context::new();
            let w = if i % 10 == 0 {
                64
            } else {
                1 + g.rng.below(6) as u16
            };
            let e = if i % 3 == 0 {
                g.expr(&mut cx, w.min(6), 4).0
            } else {
                linear_mba_expr(&mut g, &mut cx, w)
            };
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            assert!(equivalent(&mut cx, e, out.roots[0].expr, &mut rng));
            changed += u64::from(out.roots[0].changed);
            // Every answer it accepted was proved by the gate's own certificates; a candidate
            // the stronger solver exposes may still exceed a certificate's local budget.
            assert_eq!(
                out.stats.mba.simplified, out.stats.mba.certificates.proved,
                "iteration {i}: {:#?}",
                out.stats.mba
            );
        }
        assert!(changed > 50, "{changed}");
        let s = solver.stats();
        assert_eq!(s.declined_internal, 0);
        assert!(s.simplified > 50, "{s:?}");
    }

    /// Answers `x ⊕ ... ` wrongly but claims a certificate.
    struct Liar;
    impl MbaSolver for Liar {
        fn id(&self) -> &str {
            "test.liar"
        }
        fn solve(&self, p: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
            let mut m = MbaExpr::new(p.vars().to_vec());
            m.push(MOp::Var(0), &[]).unwrap();
            MbaAnswer::Simplified {
                expr: m,
                claim: Claim::Certified,
            }
        }
    }

    /// Right except at one input no sample reaches: `x + y + [x·K₁ = K₂]`, true only at
    /// `x = K₂·K₁⁻¹`, a value that is not a constant of either side (nor a neighbour of one).
    struct Subtle;
    impl MbaSolver for Subtle {
        fn id(&self) -> &str {
            "test.subtle"
        }
        fn solve(&self, p: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
            if p.vars().len() != 2 {
                return MbaAnswer::Unsupported("two variables only".into());
            }
            let w = p.width().unwrap();
            let c = |m: &mut MbaExpr, v: u64| {
                m.push(MOp::Const(crate::BitVec::wrapping_from_u64(w, v)), &[])
                    .unwrap()
            };
            let mut m = MbaExpr::new(p.vars().to_vec());
            let x = m.push(MOp::Var(0), &[]).unwrap();
            let y = m.push(MOp::Var(1), &[]).unwrap();
            let s = m.push(MOp::Add, &[x, y]).unwrap();
            let k1 = c(&mut m, 0x9e37_79b9_7f4a_7c15);
            let k2 = c(
                &mut m,
                0x9e37_79b9_7f4a_7c15u64.wrapping_mul(0x1234_5678_9abc_def1),
            );
            let xk = m.push(MOp::Mul, &[x, k1]).unwrap();
            let d = m.push(MOp::Xor, &[xk, k2]).unwrap();
            let nd = m.push(MOp::Neg, &[d]).unwrap();
            let o = m.push(MOp::Or, &[d, nd]).unwrap();
            let nz = m.push(MOp::LShr(w.bits() - 1), &[o]).unwrap();
            let one = c(&mut m, 1);
            let hit = m.push(MOp::Sub, &[one, nz]).unwrap();
            m.push(MOp::Add, &[s, hit]).unwrap();
            MbaAnswer::Simplified {
                expr: m,
                claim: Claim::Certified,
            }
        }
    }

    /// The right answer `x + y`, with no evidence.
    struct Unproven;
    impl MbaSolver for Unproven {
        fn id(&self) -> &str {
            "test.unproven"
        }
        fn solve(&self, p: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
            if p.vars().len() != 2 {
                return MbaAnswer::Unsupported("two variables only".into());
            }
            let mut m = MbaExpr::new(p.vars().to_vec());
            let x = m.push(MOp::Var(0), &[]).unwrap();
            let y = m.push(MOp::Var(1), &[]).unwrap();
            m.push(MOp::Add, &[x, y]).unwrap();
            MbaAnswer::Simplified {
                expr: m,
                claim: Claim::Unverified,
            }
        }
    }

    /// `x + y`, spelled with a degree-2 MBA identity (`x·y = (x&y)(x|y) + (x&~y)(~x&y)`): the
    /// linear signature and exhaustive evaluation (128 variable bits) cannot prove it, the
    /// degree-2 certificate can.
    const NONLINEAR: &str =
        "(x ^ y) + 2 * (x & y) + x * y - (x & y) * (x | y) - (x & ~y) * (~x & y)";

    /// `x + y`, through a relation between `(x + y) >> 1` and `x + y` that no native
    /// certificate sees (a right shift of arithmetic is an atom, independent of its operand).
    /// a right shift of a bitwise function is not an atom (`(x >> 1) * 2 + (x & 1)`
    /// is proved `x`), so the relation goes through a sum.
    const NOT_NATIVE: &str = "((x + y) >>u 1) * 2 + ((x + y) & 1)";

    fn run(eng: &Engine, src: &str) -> (Context, crate::engine::Outcome, Expr) {
        let mut cx = Context::new();
        let e = cx.parse(src, &ParseOptions::width(Width::W64)).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        (cx, out, e)
    }

    #[test]
    fn the_gate_refutes_liars_and_honours_trust() {
        // Trusting the backend: a certified lie is refuted by the always-on sampled check.
        let trusted = MbaTrust::default().with_backend_certificates(true);
        let (_, out, _) = run(
            &mba_engine(Arc::new(Liar), trusted),
            "(x ^ y) + 2 * (x & y)",
        );
        assert!(!out.roots[0].changed);
        assert!(out.stats.mba.refuted > 0);
        // An answer wrong at one unsampled point is accepted only on the backend's word, so
        // without trust in certificates (the default) it is rejected.
        let no_trust = MbaTrust::default();
        assert!(!no_trust.backend_certificates && !no_trust.sampled);
        let (mut cx, out, _) = run(&mba_engine(Arc::new(Subtle), no_trust), NONLINEAR);
        let wrong = cx.parse("x + y", &ParseOptions::width(Width::W64)).unwrap();
        assert_ne!(out.roots[0].expr, wrong);
        assert!(out.stats.mba.proof_unknown > 0);
        // A right answer bitwright can prove itself is taken without any trust: here as the
        // same polynomial over symbols, tried ahead of the degree-2 certificate's 18,337 points.
        let (mut cx, out, _) = run(&mba_engine(Arc::new(Unproven), no_trust), NONLINEAR);
        let want = cx.parse("x + y", &ParseOptions::width(Width::W64)).unwrap();
        assert_eq!(out.roots[0].expr, want);
        assert!(out.stats.mba.certificates.symbolic > 0);
        // A right but unproven answer no native certificate reaches: rejected by default,
        // accepted when sampling is trusted, and accepted by default when a prover proves it.
        let (mut cx, out, _) = run(
            &mba_engine(Arc::new(Unproven), MbaTrust::default()),
            NOT_NATIVE,
        );
        let want = cx.parse("x + y", &ParseOptions::width(Width::W64)).unwrap();
        assert_ne!(out.roots[0].expr, want);
        assert!(out.stats.mba.proof_unknown > 0);
        let sampled = MbaTrust {
            sampled: true,
            ..MbaTrust::default()
        };
        let (mut cx, out, _) = run(&mba_engine(Arc::new(Unproven), sampled), NOT_NATIVE);
        let want = cx.parse("x + y", &ParseOptions::width(Width::W64)).unwrap();
        assert_eq!(out.roots[0].expr, want);
        struct Yes;
        impl EquivalenceProver for Yes {
            fn id(&self) -> &str {
                "test.yes"
            }
            fn prove_equal(&self, _: &MbaExpr, _: &MbaExpr, _: &MbaBudget) -> Verdict {
                Verdict::Proved
            }
        }
        let eng = Engine::builder()
            .builtin()
            .strategy(Strategy::new("mba", vec![Phase::Mba(MbaConfig::default())]))
            .mba_solver(Arc::new(Unproven))
            .mba_prover(Arc::new(Yes))
            .build()
            .unwrap();
        let (mut cx, out, _) = run(&eng, NOT_NATIVE);
        let want = cx.parse("x + y", &ParseOptions::width(Width::W64)).unwrap();
        assert_eq!(out.roots[0].expr, want);
    }

    /// Counts calls and answers "no simpler".
    struct Counting(AtomicU64);
    impl MbaSolver for Counting {
        fn id(&self) -> &str {
            "test.counting"
        }
        fn solve(&self, _: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
            self.0.fetch_add(1, Ordering::Relaxed);
            MbaAnswer::NoSimpler
        }
    }

    #[test]
    fn answers_are_cached_and_calls_budgeted() {
        let solver = Arc::new(Counting(AtomicU64::new(0)));
        let cache = Arc::new(MemoryCache::new(1024));
        let eng = Engine::builder()
            .builtin()
            .strategy(Strategy::new("mba", vec![Phase::Mba(MbaConfig::default())]))
            .mba_solver(solver.clone())
            .mba_cache(cache.clone())
            .build()
            .unwrap();
        let (_, out, _) = run(&eng, NONLINEAR);
        let first = solver.0.load(Ordering::Relaxed);
        assert!(first > 0 && out.stats.mba.no_simpler > 0);
        // A fresh context: answered from the cache.
        let (_, out, _) = run(&eng, NONLINEAR);
        assert_eq!(solver.0.load(Ordering::Relaxed), first);
        assert!(out.stats.mba.cache_hits > 0);
        // The call budget.
        let eng = mba_engine(Arc::new(Counting(AtomicU64::new(0))), MbaTrust::default());
        let mut cx = Context::new();
        let e = cx
            .parse(NONLINEAR, &ParseOptions::width(Width::W64))
            .unwrap();
        let out = eng
            .run(
                &mut cx,
                &[e],
                Run {
                    per_call: Budget {
                        mba_calls: 0,
                        ..Budget::UNLIMITED
                    },
                    ..Run::default()
                },
            )
            .unwrap();
        assert_eq!(
            out.roots[0].end,
            End::BudgetTerminated(crate::engine::Exhausted::MbaCalls)
        );
    }

    /// Always runs out.
    struct Tired;
    impl MbaSolver for Tired {
        fn id(&self) -> &str {
            "test.tired"
        }
        fn solve(&self, _: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
            MbaAnswer::Exhausted
        }
    }

    #[test]
    fn exhausted_answers_are_not_final() {
        let eng = mba_engine(Arc::new(Tired), MbaTrust::default());
        let mut cx = Context::new();
        let e = cx
            .parse(NONLINEAR, &ParseOptions::width(Width::W64))
            .unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert!(matches!(out.roots[0].end, End::BudgetTerminated(_)));
        let again = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert!(
            again.stats.mba.calls > 0,
            "an exhausted answer was memoized"
        );
    }

    /// Answers "no simpler" for a fixed number of steps (at most its limit), counting calls.
    struct Steady(u64, AtomicU64);
    impl MbaSolver for Steady {
        fn id(&self) -> &str {
            "test.steady"
        }
        fn solve(&self, p: &MbaExpr, budget: &MbaBudget) -> MbaAnswer {
            self.solve_counted(p, budget).0
        }
        fn solve_counted(&self, _: &MbaExpr, budget: &MbaBudget) -> (MbaAnswer, u64) {
            self.1.fetch_add(1, Ordering::Relaxed);
            (MbaAnswer::NoSimpler, self.0.min(budget.steps))
        }
    }

    /// Several MBA questions, one per summand.
    const MANY: &str = "((x ^ y) + 2 * (x & y)) * ((x | z) - (x & z)) \
                        + ((y ^ z) + 2 * (y & z)) * ((y | x) + (y & x)) \
                        + ((z ^ x) + 2 * (z & x)) * ((z | y) - (z & y))";

    #[test]
    fn the_solvers_steps_are_an_account_of_the_run() {
        assert_eq!(Budget::fuel(1000).mba_steps, 8000);
        assert_eq!(Budget::default().mba_steps, 1 << 25);
        let ask = |solver: Arc<dyn MbaSolver>, steps: u64| {
            let eng = mba_engine(solver, MbaTrust::default());
            let mut cx = Context::new();
            let e = cx.parse(MANY, &ParseOptions::width(Width::W64)).unwrap();
            let run = Run::default().with_per_call(Budget::UNLIMITED.with_mba_steps(steps));
            eng.run(&mut cx, &[e], run).unwrap()
        };
        // Unlimited: every question asked, each charged what it spent.
        let s = Arc::new(Steady(1000, AtomicU64::new(0)));
        let out = ask(s.clone(), u64::MAX);
        let calls = s.1.load(Ordering::Relaxed);
        assert!(calls >= 3, "{calls}");
        assert_eq!(out.stats.mba.calls, calls);
        assert_eq!(out.stats.mba.steps, 1000 * calls);
        assert_eq!(out.roots[0].end, End::Completed);
        // An account for one question: the next ones are not asked, and the run says why.
        let s = Arc::new(Steady(1000, AtomicU64::new(0)));
        let out = ask(s.clone(), 1000);
        assert_eq!(
            (s.1.load(Ordering::Relaxed), out.stats.mba.steps),
            (1, 1000)
        );
        assert_eq!(
            out.roots[0].end,
            End::BudgetTerminated(crate::engine::Exhausted::MbaSteps)
        );
        // Nothing in it: nothing asked.
        let s = Arc::new(Steady(1000, AtomicU64::new(0)));
        let out = ask(s.clone(), 0);
        assert_eq!(s.1.load(Ordering::Relaxed), 0);
        assert_eq!(
            out.roots[0].end,
            End::BudgetTerminated(crate::engine::Exhausted::MbaSteps)
        );
        // A last question gets what is left, never more.
        let s = Arc::new(Steady(1000, AtomicU64::new(0)));
        let out = ask(s.clone(), 1000 * calls - 1);
        assert_eq!(out.stats.mba.steps, 1000 * calls - 1);
        // A solver that does not count is charged its whole limit.
        let limit = MbaConfig::default().budget.steps;
        let c = Arc::new(Counting(AtomicU64::new(0)));
        let out = ask(c.clone(), 2 * limit);
        assert_eq!(c.0.load(Ordering::Relaxed), 2);
        assert_eq!(out.stats.mba.steps, 2 * limit);
        // The normal-form solver counts its steps, and a remembered answer is charged what
        // finding it cost: the same run in a fresh context, answered from the solver's memory,
        // spends the same and gives the same.
        let nf: Arc<dyn MbaSolver> = Arc::new(crate::mba::NormalFormSolver::default());
        let eng = mba_engine(nf, MbaTrust::default());
        let once = |eng: &Engine| {
            let mut cx = Context::new();
            let e = cx.parse(MANY, &ParseOptions::width(Width::W64)).unwrap();
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            (cx.display(out.roots[0].expr).to_string(), out.stats.mba)
        };
        let (first, a) = once(&eng);
        let (again, b) = once(&eng);
        assert_eq!(first, again);
        assert!(a.calls > 0 && a.steps > 0 && a.steps < a.calls * limit);
        assert_eq!((a.calls, a.steps), (b.calls, b.steps));
    }

    #[test]
    fn the_signature_solver_counts_its_corners() {
        let s = crate::mba::SignatureSolver;
        let w = Width::W64;
        let mut p = MbaExpr::new(vec![w, w]);
        let x = p.push(MOp::Var(0), &[]).unwrap();
        let y = p.push(MOp::Var(1), &[]).unwrap();
        let and = p.push(MOp::And, &[x, y]).unwrap();
        let xor = p.push(MOp::Xor, &[x, y]).unwrap();
        let two = p
            .push(MOp::Const(BitVec::wrapping_from_u64(w, 2)), &[])
            .unwrap();
        let dbl = p.push(MOp::Mul, &[and, two]).unwrap();
        p.push(MOp::Add, &[xor, dbl]).unwrap();
        // Six nodes at four corners: 24 evaluations, one step.
        let (a, steps) = s.solve_counted(&p, &MbaBudget::default());
        assert!(matches!(a, MbaAnswer::Simplified { .. }));
        assert_eq!(steps, 1);
        assert_eq!(s.solve(&p, &MbaBudget::default()), a);
        // No step to spend: not computed.
        let (a, steps) = s.solve_counted(&p, &MbaBudget::default().with_steps(0));
        assert_eq!((a, steps), (MbaAnswer::Exhausted, 0));
        // Through the deadline wrapper, the same count.
        let t = crate::mba::ThreadedSolver::new(s, std::time::Duration::from_secs(30), 2);
        assert_eq!(t.solve_counted(&p, &MbaBudget::default()).1, 1);
    }

    // ----- M6 review regressions ------------------------------------------------------------

    #[test]
    fn cached_answers_are_keyed_by_trust() {
        // A lax engine takes `Subtle`'s wrong answer on sampling; a strict engine sharing the
        // cache must not take it from there.
        let cache = Arc::new(MemoryCache::new(1024));
        let with = |trust| {
            Engine::builder()
                .builtin()
                .strategy(Strategy::new(
                    "mba",
                    vec![Phase::Mba(MbaConfig {
                        trust,
                        ..MbaConfig::default()
                    })],
                ))
                .mba_solver(Arc::new(Subtle))
                .mba_cache(cache.clone())
                .build()
                .unwrap()
        };
        let lax = MbaTrust {
            backend_certificates: false,
            sampled: true,
        };
        let strict = MbaTrust {
            backend_certificates: false,
            sampled: false,
        };
        let (_, out, _) = run(&with(lax), NONLINEAR);
        assert!(out.roots[0].changed && out.stats.mba.simplified > 0);
        let (_, out, _) = run(&with(strict), NONLINEAR);
        assert!(!out.roots[0].changed, "a laxly accepted answer was reused");
        assert_eq!(out.stats.mba.simplified, 0);
    }

    struct Panicky;
    impl MbaSolver for Panicky {
        fn id(&self) -> &str {
            "test.panicky"
        }
        fn solve(&self, _: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
            panic!("a solver bug")
        }
    }

    #[test]
    fn a_panicking_solver_does_not_disable_the_deadline_wrapper() {
        let s = crate::mba::ThreadedSolver::new(Panicky, std::time::Duration::from_secs(5), 2);
        let m = MbaExpr::new(vec![]);
        for _ in 0..4 {
            assert!(matches!(
                s.solve(&m, &MbaBudget::default()),
                MbaAnswer::Unsupported(_)
            ));
        }
        assert_eq!(s.abandoned(), 0);
    }

    #[test]
    fn exact_evidence_is_charged_and_budgeted() {
        // At W = 6 the two variables have 12 bits: `Unproven`'s right answer, outside the
        // polynomial fragment, is proved by evaluating all 2^12 points, and that work is
        // charged.
        let eng = mba_engine(Arc::new(Unproven), MbaTrust::default());
        let o = ParseOptions::width(Width::new(6).unwrap());
        let mut cx = Context::new();
        let e = cx.parse(NOT_NATIVE, &o).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(
            out.roots[0].expr,
            cx.parse("x + y", &o).unwrap(),
            "{}\n{:#?}",
            cx.display(out.roots[0].expr),
            out.stats
        );
        assert!(out.stats.pass_work >= 1 << 12, "{}", out.stats.pass_work);
        assert_eq!(out.stats.mba.certificates.exhaustive, 1);
        assert_eq!(out.stats.mba.certificates.points, 1 << 12);
        // A pass-work budget stops it: the certificate is not started, and the node is not
        // final (more budget may prove it).
        let mut cx = Context::new();
        let e = cx.parse(NOT_NATIVE, &o).unwrap();
        let out = eng
            .run(
                &mut cx,
                &[e],
                Run {
                    per_call: Budget {
                        pass_work: 1 << 12,
                        ..Budget::UNLIMITED
                    },
                    ..Run::default()
                },
            )
            .unwrap();
        assert_eq!(
            out.roots[0].end,
            End::BudgetTerminated(crate::engine::Exhausted::PassWork)
        );
    }

    /// The normal-form solver, counting the questions put to it.
    struct Asked(crate::mba::NormalFormSolver, AtomicU64);
    impl MbaSolver for Asked {
        fn id(&self) -> &str {
            "test.counting"
        }
        fn solve(&self, p: &MbaExpr, budget: &MbaBudget) -> MbaAnswer {
            self.solve_counted(p, budget).0
        }
        fn solve_counted(&self, p: &MbaExpr, budget: &MbaBudget) -> (MbaAnswer, u64) {
            self.1.fetch_add(1, Ordering::Relaxed);
            self.0.solve_counted(p, budget)
        }
        fn polynomial_fragments(&self) -> bool {
            true
        }
    }

    /// The results of `roots` (one call) and the questions put to the solver, with the rule
    /// that declines questions no answer to which could be committed, or (`all`) without.
    fn limb_asked(roots: &[&str], all: bool) -> (Vec<String>, u64) {
        let solver = Arc::new(Asked(
            crate::mba::NormalFormSolver::default(),
            AtomicU64::new(0),
        ));
        let eng = mba_engine(
            solver.clone(),
            MbaTrust::default().with_backend_certificates(false),
        );
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let es: Vec<Expr> = roots.iter().map(|s| cx.parse(s, &o).unwrap()).collect();
        super::super::mba::ASK_ALL.set(all);
        let out = eng.run(&mut cx, &es, Run::default());
        super::super::mba::ASK_ALL.set(false);
        let out = out.unwrap();
        assert!(out.roots.iter().all(|r| r.end == End::Completed));
        let texts = out
            .roots
            .iter()
            .map(|r| cx.display(r.expr).to_string())
            .collect();
        (texts, solver.1.load(Ordering::Relaxed))
    }

    #[test]
    fn limb_questions_that_pay_are_asked() {
        // The comparison's other side reads what the sum reads, so replacing the sum frees
        // itself, or itself and one node: the answer is an atom, a constant, or one operator
        // over the atoms, and is found with the rule as without it.
        for (src, gone) in [
            // `x`: the difference goes.
            (
                "(((x | y) + (x & y)) - y) <u (((x | y) + (x & y)) * z)",
                " - y",
            ),
            // 0.
            (
                "(((x ^ y) + 2 * (x & y)) - (x + y)) <u (((x ^ y) + 2 * (x & y)) * (x + y) * z)",
                " - ",
            ),
            // `x + y`: the doubled conjunction goes.
            ("((x ^ y) + 2 * (x & y)) <u ((x ^ y) * (x & y) * z)", "2"),
        ] {
            let (with, _) = limb_asked(&[src], false);
            let (without, _) = limb_asked(&[src], true);
            assert_eq!(with, without, "{src}");
            assert!(!with[0].contains(gone), "{src}: {}", with[0]);
        }
    }

    #[test]
    fn limb_questions_that_cannot_pay_are_not_asked() {
        // The products are read by both sides, so replacing a side frees it alone, and it is
        // no atom, constant or node below it: no answer could be committed, none is asked
        // for, and the result is what it is with every question asked. The same where the
        // answer is one operator (`x ^ y`) for the one node freed: no smaller.
        for src in [
            "((x & y) * 5 + (x | y) * 3) <u ((x & y) * 5 ^ (x | y) * 3)",
            "((x | y) - (x & y)) <u ((x | y) * (x & y) * z)",
        ] {
            let (with, asked) = limb_asked(&[src], false);
            let (without, all) = limb_asked(&[src], true);
            assert_eq!(with, without, "{src}");
            assert!(asked < all, "{src}: {asked} of {all}");
        }
        // Sums of limb code that share their terms with the carries beside them, generated:
        // the same results, fewer questions.
        let ops = ["&", "|", "^"];
        let mut seed = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = |n: u64| {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 33) % n
        };
        let (mut asked, mut all) = (0, 0);
        for _ in 0..40 {
            let v = ["x", "y", "z"];
            let term = |next: &mut dyn FnMut(u64) -> u64| {
                format!(
                    "({} {} {})",
                    v[next(3) as usize],
                    ops[next(3) as usize],
                    v[next(3) as usize]
                )
            };
            let (a, b, c) = (term(&mut next), term(&mut next), term(&mut next));
            let k = 1 + next(4);
            let sum = format!("{a} + {b}");
            let low = format!("({sum} - {k} * {c})");
            // A word, a limb of it, a carry out of the limb, and a mask of the word beside.
            let e = format!(
                "({low} & 0x3fff) + zext<32>(trunc<14>({sum}) <u trunc<14>({a})) \
                 + (({sum}) & {c}) * 2 + ({low} >>u 14)"
            );
            let (with, n) = limb_asked(&[&e], false);
            let (without, m) = limb_asked(&[&e], true);
            assert_eq!(with, without, "{e}");
            assert!(n <= m, "{e}: {n} of {m}");
            asked += n;
            all += m;
        }
        assert!(asked < all, "{asked} of {all}");
    }

    /// [`limb_asked`] with `cannot_pay` deciding at most `most` freed nodes, with (`free`) or
    /// without the forms compared where the atoms are free.
    fn limb_ruled(roots: &[&str], most: u32, free: bool) -> (Vec<String>, u64) {
        super::super::mba::PAY_RULE.set((most, free));
        let out = std::panic::catch_unwind(|| limb_asked(roots, false));
        super::super::mba::PAY_RULE.set((u32::MAX, true));
        out.unwrap()
    }

    #[test]
    fn limb_questions_of_three_freed_nodes() {
        // An answer of two nodes for three freed (`(x + y) ^ z`, `(x + y) * z`: the sum of
        // `x ^ y` and twice `x & y` goes with its product) is found with the rule as without.
        for (src, gone) in [
            (
                "(((x ^ y) + 2 * (x & y)) ^ z) <u ((x ^ y) * (x & y) * (z * 2))",
                "2",
            ),
            (
                "(((x ^ y) + 2 * (x & y)) * z) <u ((x ^ y) * (x & y) + (z * 2))",
                "2",
            ),
        ] {
            let (all, _) = limb_asked(&[src], true);
            let (with, _) = limb_ruled(&[src], 3, true);
            assert_eq!(with, all, "{src}");
            assert!(!with[0].contains(gone), "{src}: {}", with[0]);
        }
        // Three freed nodes and no form of two over what stays (a sum of four terms the other
        // side reads too; a sum and a constant, where the constant is one of the three): not
        // asked, with the results of every question asked and of the rule for two.
        for src in [
            "((x | y) + (x & y) + 7) <u ((x | y) * (x & y) * z)",
            "(((x & y) * 5 + (x | y) * 3) + (x ^ y) * 7 + z) \
             <u ((x & y) * 5 ^ (x | y) * 3 ^ (x ^ y) * 7)",
            "((x & y) + (x | z) + (y ^ z) + x) <u ((x & y) * (x | z) * (y ^ z))",
            "(((x & y) * 5 ^ (x | y) * 3) + z + 1) <u ((x & y) * 5 + (x | y) * 3)",
        ] {
            let (all, _) = limb_asked(&[src], true);
            let (two, asked_two) = limb_ruled(&[src], 2, false);
            let (three, asked_three) = limb_ruled(&[src], 3, false);
            assert_eq!(two, all, "{src}");
            assert_eq!(three, all, "{src}");
            assert!(
                asked_three < asked_two,
                "{src}: {asked_three} of {asked_two}"
            );
        }
    }

    #[test]
    fn limb_forms_that_agree_by_the_atoms_relations_are_no_answers() {
        // `x <u y` implies `x <=u y` and excludes `x == y`, and the lesser of two is one of
        // them: the conjunctions are a node below them, or zero, at every point, which no
        // identity over the comparisons as atoms says. Compared where the atoms are free, no
        // form agrees and the question is not asked; the results are those of asking.
        for src in [
            "(zext<32>(x <u y) & zext<32>(x <=u y)) \
             <u (zext<32>(x <u y) * zext<32>(x <=u y) * z)",
            "(zext<32>(x <u y) & zext<32>(x == y)) <u (zext<32>(x <u y) * zext<32>(x == y) + z)",
            "((select(x <u y, x, y) ^ x) & (select(x <u y, x, y) ^ y)) \
             <u ((select(x <u y, x, y) ^ x) * (select(x <u y, x, y) ^ y) * z)",
        ] {
            let (all, _) = limb_asked(&[src], true);
            let (bound, asked_bound) = limb_ruled(&[src], 3, false);
            let (free, asked_free) = limb_ruled(&[src], 3, true);
            assert_eq!(bound, all, "{src}");
            assert_eq!(free, all, "{src}");
            assert!(
                asked_free < asked_bound,
                "{src}: {asked_free} of {asked_bound}"
            );
        }
        // A comparison and its negation stay related (`~` of one is built as the other):
        // their sum is 1, found with the rule as without.
        let src = "(zext<32>(x <u y) + zext<32>(y <=u x)) <u (zext<32>(x <u y) * z)";
        let (all, _) = limb_asked(&[src], true);
        let (free, _) = limb_ruled(&[src], 3, true);
        assert_eq!(free, all, "{src}");
    }

    #[test]
    fn limb_forms_of_two_nodes_are_all_tried() {
        // Generated: a form of two nodes over three values the other side keeps alive, spelled
        // so that three nodes go with it. Whatever the solver makes of it, the rule changes
        // no result (it asks wherever a form of two nodes agrees).
        let unary = ["~", "-"];
        let binary = ["+", "-", "*", "&", "|", "^"];
        let mut seed = 0x2545_f491_4f6c_dd1du64;
        let mut next = |n: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % n
        };
        let mut declined = 0;
        for _ in 0..60 {
            let (p, q) = (binary[next(6) as usize], binary[next(6) as usize]);
            let k = 3 + 2 * next(40);
            let inner = match next(4) {
                0 => format!("((x ^ y) + 2 * (x & y)) {p} z"),
                1 => format!("((x | y) - (x & y)) {p} (z + {k})"),
                2 => format!("{}((x | y) + (x & y))", unary[next(2) as usize]),
                _ => format!("((x & y) + (x | y)) {p} {k}"),
            };
            let src = format!("(({inner}) {q} w) <u ((x ^ y) * (x & y) * (x | y) * (z + {k}) + w)");
            let (all, asked_all) = limb_asked(&[&src], true);
            let (with, asked) = limb_ruled(&[&src], 3, true);
            assert_eq!(with, all, "{src}");
            declined += asked_all - asked;
        }
        assert!(declined > 0);
    }

    #[test]
    fn limb_sums_by_parts_do_not_depend_on_earlier_candidates() {
        // A sum whose groups of terms are simplified one by one is committed by what it reads
        // of the sum it replaces: a candidate built before (and left in the arena) changes
        // nothing.
        for (src, left) in [
            (
                "((a ^ b) + 2 * (a & b)) + ((c | d) - (c & d)) + (a ^ b) * (c | d)",
                "(a + b) + (c ^ d) + (a ^ b) * (c | d)",
            ),
            (
                "((a | b) + (a & b)) + 3 * ((c ^ d) + 2 * (c & d)) + (a & b) * (c & d)",
                "(a + b) + 3 * (c + d) + (a & b) * (c & d)",
            ),
        ] {
            let eng = mba_engine(
                Arc::new(crate::mba::NormalFormSolver::default()),
                MbaTrust::default().with_backend_certificates(false),
            );
            let o = ParseOptions::width(Width::W32);
            let mut fresh = Context::new();
            let e = fresh.parse(src, &o).unwrap();
            let want = eng.simplify(&mut fresh, e).unwrap();
            let mut used = Context::new();
            used.parse(left, &o).unwrap();
            let e = used.parse(src, &o).unwrap();
            let got = eng.simplify(&mut used, e).unwrap();
            assert_eq!(
                fresh.display(want.expr).to_string(),
                used.display(got.expr).to_string(),
                "{src}"
            );
        }
    }
}

// ----- regressions from the M6 review --------------------------------------------------------------

#[test]
fn linear_mba_never_reads_linear_terms_as_bitwise_operands() {
    linear_mba_never_reads_linear_terms_as_bitwise_operands_cases(1000);
}

/// [`linear_mba_never_reads_linear_terms_as_bitwise_operands`] over 3000 random cases.
#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn linear_mba_never_reads_linear_terms_as_bitwise_operands_heavy() {
    linear_mba_never_reads_linear_terms_as_bitwise_operands_cases(3000);
}

fn linear_mba_never_reads_linear_terms_as_bitwise_operands_cases(cases: usize) {
    for phases in [vec![Phase::LinearMba], Strategy::deobfuscate().phases] {
        let eng = engine(phases);
        let mut rng = Rng(0x6b);
        for w in [8u16, 32] {
            for src in [
                "(x + y) & (x | y)",
                "(x + y) | (x & y)",
                "(2 * x) & (x | y)",
                "((x << 1) & y) + (x & y)",
                "(x - y) & ~(x & y)",
                "~(x + y) & y",
            ] {
                let mut cx = Context::new();
                let e = cx
                    .parse(src, &ParseOptions::width(Width::new(w).unwrap()))
                    .unwrap();
                let out = eng.simplify(&mut cx, e).unwrap();
                assert!(
                    equivalent(&mut cx, e, out.expr, &mut rng),
                    "W={w}: {src} became {}",
                    cx.display(out.expr)
                );
            }
        }
        // Random DAGs over + - & | ^ of two symbols, linear terms under bitwise operators.
        let mut g = generator(0x6c);
        for _ in 0..cases {
            let mut cx = Context::new();
            let w = Width::new(1 + g.rng.below(8) as u16).unwrap();
            let mut pool = vec![cx.symbol("x", w).unwrap(), cx.symbol("y", w).unwrap()];
            for _ in 0..6 {
                let a = pool[g.rng.below(pool.len() as u64) as usize];
                let b = pool[g.rng.below(pool.len() as u64) as usize];
                let op = [BinOp::Add, BinOp::Sub, BinOp::And, BinOp::Or, BinOp::Xor]
                    [g.rng.below(5) as usize];
                pool.push(cx.bin(op, a, b).unwrap());
            }
            let e = *pool.last().unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            assert!(
                equivalent(&mut cx, e, out.expr, &mut rng),
                "{} became {}",
                cx.display(e),
                cx.display(out.expr)
            );
        }
    }
}

#[test]
fn linear_mba_is_independent_of_construction_order() {
    let eng = engine(vec![Phase::LinearMba]);
    let mut g = generator(0x1234);
    for _ in 0..5000 {
        let mut c1 = Context::new();
        let mut c2 = Context::new();
        let w = Width::new(1 + g.rng.below(8) as u16).unwrap();
        for name in ["a", "b", "c", "d", "x", "y", "z"] {
            c1.symbol(name, w).unwrap();
        }
        for name in ["z", "y", "x", "d", "c", "b", "a"] {
            c2.symbol(name, w).unwrap();
        }
        let e1 = linear_mba_expr(&mut g, &mut c1, w.bits());
        let text = c1.display(e1).to_string();
        let e2 = c2.parse(&text, &ParseOptions::width(w)).unwrap();
        let r1 = eng.simplify(&mut c1, e1).unwrap().expr;
        let r2 = eng.simplify(&mut c2, e2).unwrap().expr;
        assert_eq!(
            c1.display(r1).to_string(),
            c2.display(r2).to_string(),
            "{text}"
        );
    }
}

#[test]
fn linear_mba_emits_conjunctions_for_any_number_of_atoms() {
    let eng = engine(vec![Phase::LinearMba]);
    for (src, w, want) in [
        // The conjunction form is smaller than the indicator form here.
        (
            "3 * (x & ~y) + 2 * (~x & y) + 5 * (x & y) - (x | y)",
            64,
            "x + x + (x & y) + y",
        ),
        // Four atoms: the indicator form needs three or fewer, and a conjunction remains.
        ("(a | b) - (a ^ b) + (c & ~d) + (c & d)", 32, "(a & b) + c"),
    ] {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let e = cx.parse(src, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(cx.display(out.expr).to_string(), want, "{src}");
    }
    // Random linear MBAs over four to six symbols, exhaustively at two bits a symbol.
    let mut g = generator(0xc0_4d);
    let mut rng = Rng(0xc0_4e);
    let mut changed = 0;
    for _ in 0..1500 {
        let mut cx = Context::new();
        let w = Width::new(2).unwrap();
        let n = 4 + g.rng.below(3) as usize;
        let vars: Vec<Expr> = (0..n)
            .map(|k| cx.symbol(format!("v{k}").as_str(), w).unwrap())
            .collect();
        let mut sum = cx.constant_u64(w, g.rng.below(4)).unwrap();
        for _ in 0..(2 + g.rng.below(4)) {
            let mut f = vars[g.rng.below(n as u64) as usize];
            for _ in 0..(1 + g.rng.below(3)) {
                let o = vars[g.rng.below(n as u64) as usize];
                let o = if g.rng.chance(1, 3) {
                    cx.un(UnOp::Not, o).unwrap()
                } else {
                    o
                };
                let op = [BinOp::And, BinOp::Or, BinOp::Xor][g.rng.below(3) as usize];
                f = cx.bin(op, f, o).unwrap();
            }
            let k = cx.constant_u64(w, g.rng.below(4)).unwrap();
            let term = cx.bin(BinOp::Mul, f, k).unwrap();
            sum = cx.bin(BinOp::Add, sum, term).unwrap();
        }
        let out = eng.simplify(&mut cx, sum).unwrap();
        assert!(
            equivalent(&mut cx, sum, out.expr, &mut rng),
            "{} became {}",
            cx.display(sum),
            cx.display(out.expr)
        );
        changed += u32::from(out.changed);
    }
    assert!(changed > 300, "{changed}");
}

// ----- the invert pass --------------------------------------------------------------------------

/// A random chain of layers over `x`: invertible ones (with constant or symbol parameters, and
/// triangular `v ⊙ g(v)`) and non-invertible ones (masks, shifts, feeding `x` back in).
fn layered(g: &mut Gen, cx: &mut Context, x: Expr, w: u16, depth: u32) -> Expr {
    let wd = Width::new(w).unwrap();
    let mut e = x;
    for _ in 0..depth {
        let k = if g.rng.chance(1, 4) {
            cx.symbol("p", wd).unwrap()
        } else {
            let v = g.constant(w);
            cx.constant(&v).unwrap()
        };
        let sh = cx.constant_u64(wd, 1 + g.rng.below(u64::from(w))).unwrap();
        e = match g.rng.below(12) {
            0 => cx.bin(BinOp::Add, e, k).unwrap(),
            1 => cx.bin(BinOp::Xor, e, k).unwrap(),
            2 => cx.bin(BinOp::Mul, e, k).unwrap(),
            3 => cx.bin(BinOp::Sub, k, e).unwrap(),
            4 => cx.bin(BinOp::RotL, e, k).unwrap(),
            5 => cx
                .un(
                    [UnOp::Not, UnOp::Neg, UnOp::BitRev][g.rng.below(3) as usize],
                    e,
                )
                .unwrap(),
            6 => {
                let t = cx.bin(BinOp::LShr, e, sh).unwrap();
                cx.bin(BinOp::Xor, e, t).unwrap()
            }
            7 => {
                let t = cx.bin(BinOp::Shl, e, sh).unwrap();
                let t = cx.bin(BinOp::And, t, k).unwrap();
                cx.bin(BinOp::Sub, e, t).unwrap()
            }
            8 => {
                // The mixer's involution, scaled to the width.
                let a = cx.constant_u64(wd, u64::from(w / 2)).unwrap();
                let b = cx.constant_u64(wd, u64::from(w - w / 4 - 1)).unwrap();
                let (s1, s2) = (
                    cx.bin(BinOp::LShr, e, a).unwrap(),
                    cx.bin(BinOp::LShr, e, b).unwrap(),
                );
                let t = cx.bin(BinOp::LShr, s1, s2).unwrap();
                cx.bin(BinOp::Xor, e, t).unwrap()
            }
            9 => cx.bin(BinOp::And, e, k).unwrap(),
            10 => cx.bin(BinOp::LShr, e, sh).unwrap(),
            _ => cx.bin(BinOp::Xor, e, x).unwrap(),
        };
    }
    e
}

#[test]
fn invert_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Invert]);
    let std = Engine::standard();
    // Strict verification samples every rewrite and checks both sides' facts meet.
    let strict = Engine::builder()
        .builtin()
        .strategy(Strategy::standard())
        .verify(Verify::strict())
        .build()
        .unwrap();
    let mut g = generator(0x1a7e_0001);
    let mut rng = Rng(11);
    let mut changed = 0;
    for i in 0..1500 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [16, 64, 128, 257][g.rng.below(4) as usize]
        } else {
            1 + g.rng.below(4) as u16
        };
        let wd = Width::new(w).unwrap();
        let (x, y) = (cx.symbol("x", wd).unwrap(), cx.symbol("y", wd).unwrap());
        let depth = 1 + g.rng.below(4) as u32;
        let f = layered(&mut g, &mut cx, x, w, depth);
        // Sometimes widened by an injective map that is not onto: then a constant may have no
        // preimage at all.
        let widen = match g.rng.below(8) {
            _ if w >= 256 => None,
            0 => Some((0, w + 1 + g.rng.below(3) as u16)),
            1 => Some((1, w + 1 + g.rng.below(3) as u16)),
            2 => Some((2, w + 1 + g.rng.below(3) as u16)),
            _ => None,
        };
        let lo = widen.map(|(_, w2)| g.constant(w2 - w));
        let wide = |cx: &mut Context, e: Expr| -> Expr {
            let Some((how, w2)) = widen else {
                return e;
            };
            let wd2 = Width::new(w2).unwrap();
            match how {
                0 => cx.zext(e, wd2).unwrap(),
                1 => cx.sext(e, wd2).unwrap(),
                _ => {
                    let k = cx.constant(&lo.unwrap()).unwrap();
                    cx.concat(e, k).unwrap()
                }
            }
        };
        let fw = wide(&mut cx, f);
        let wc = cx.width(fw).unwrap();
        let op = [
            CmpOpExt::Eq,
            CmpOpExt::Ne,
            CmpOpExt::Ult,
            CmpOpExt::Ule,
            CmpOpExt::Slt,
            CmpOpExt::Sle,
        ][g.rng.below(6) as usize];
        let e = match i % 5 {
            // Against a constant: often an actual value of the chain, so it is solvable.
            0 | 1 => {
                let c = if g.rng.chance(1, 2) {
                    let xv = g.constant(w);
                    let env = FnEnv(|k: &crate::SymbolKey, _| {
                        Some(if *k == crate::SymbolKey::from("x") {
                            xv
                        } else {
                            BitVec::zero(wd)
                        })
                    });
                    cx.eval(&[fw], &env).unwrap()[0]
                } else {
                    g.constant(wc.bits())
                };
                let c = cx.constant(&c).unwrap();
                cx.cmp(op, fw, c).unwrap()
            }
            // The same chain over another value, or a different one.
            2 => {
                let fy = cx.substitute(&[fw], &[(x, y)]).unwrap()[0];
                cx.cmp(op, fw, fy).unwrap()
            }
            3 => {
                let depth = 1 + g.rng.below(3) as u32;
                let h = layered(&mut g, &mut cx, y, w, depth);
                let h = wide(&mut cx, h);
                cx.cmp(op, fw, h).unwrap()
            }
            // Or-trees against zero, over one value or two.
            _ => {
                let other = if g.rng.chance(1, 2) { x } else { y };
                let depth = 1 + g.rng.below(3) as u32;
                let h = layered(&mut g, &mut cx, other, w, depth);
                let h = wide(&mut cx, h);
                let o = cx.bin(BinOp::Or, fw, h).unwrap();
                let z = cx.constant(&BitVec::zero(wc)).unwrap();
                cx.cmp(op, o, z).unwrap()
            }
        };
        for engine in [&eng, &std, &strict] {
            let out = engine.run(&mut cx, &[e], Run::default()).unwrap();
            let r = out.roots[0];
            assert_eq!(r.end, End::Completed);
            assert_eq!(out.stats.rejected, 0, "{}", cx.display(e));
            assert!(
                equivalent(&mut cx, e, r.expr, &mut rng),
                "{} vs {}",
                cx.display(e),
                cx.display(r.expr)
            );
            changed += u64::from(r.changed);
            cx.memo.clear();
            let again = engine.run(&mut cx, &[r.expr], Run::default()).unwrap();
            assert!(
                !again.roots[0].changed,
                "not idempotent: {} -> {}",
                cx.display(r.expr),
                cx.display(again.roots[0].expr)
            );
        }
    }
    assert!(changed > 800, "{changed}");
}

/// Checks `src` simplifies to `want` (both parsed at `w` bits) under `eng`.
fn check_to(eng: &Engine, src: &str, want: &str, w: u16) {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::new(w).unwrap());
    let e = cx.parse(src, &o).unwrap();
    let out = eng.simplify(&mut cx, e).unwrap();
    let want = cx
        .parse(want, &ParseOptions::width(cx.width(e).unwrap()))
        .unwrap();
    assert_eq!(out.expr, want, "{src} gave {}", cx.display(out.expr));
}

#[test]
fn invert_fixtures() {
    let eng = Engine::standard();
    // Cancelling one layer on both sides, repeatedly.
    check_to(&eng, "x + 7 == y + 7", "x == y", 8);
    check_to(&eng, "(x ^ z) * 3 != (y ^ z) * 3", "x != y", 8);
    check_to(&eng, "rotl(x, z) == rotl(y, z)", "x == y", 8);
    check_to(&eng, "z - x == z - y", "x == y", 8);
    check_to(&eng, "zext<16>(x) == zext<16>(y)", "x == y", 8);
    // ... never through a map that is not injective.
    check_to(&eng, "x * 6 == y * 6", "x * 6 == y * 6", 8);
    check_to(&eng, "(x & z) == (y & z)", "(x & z) == (y & z)", 8);
    check_to(
        &eng,
        "(x ^ z) * w == (y ^ z) * w",
        "(x ^ z) * w == (y ^ z) * w",
        8,
    );
    // Moving a constant across: 5 * 3⁻¹ = 5 * 171 = 0x57 (mod 2^8).
    check_to(&eng, "x * 3 == 5", "x == 0x57", 8);
    check_to(&eng, "rotl(x, 3) != 5", "x != 0xa0", 8);
    check_to(&eng, "~(x - 9) == 0", "x == 8", 8);
    // A triangular map: the high nibble first, then the low one.
    check_to(&eng, "(x ^ (x >>u 4)) == 0x5a", "x == 0x5f", 8);
    check_to(&eng, "(x ^ (x >>u 4)) == (y ^ (y >>u 4))", "x == y", 8);
    // No preimage at all.
    check_to(&eng, "zext<16>(x) == 0x1ff", "false", 8);
    check_to(&eng, "concat(x, 1:4) == 0x12:12", "false", 8);
    check_to(&eng, "concat(x, 2:4) != 0x12:12", "x != 1", 8);
    // Zero or-trees are solved leaf by leaf.
    check_to(&eng, "((x ^ 1) | (x ^ 2)) == 0", "false", 8);
    check_to(
        &eng,
        "((x + 1) | (y * 3)) == 0",
        "(x == 0xff) & (y == 0)",
        8,
    );
    check_to(
        &eng,
        "((x + 1) | (y * 3)) != 0",
        "(x != 0xff) | (y != 0)",
        8,
    );
    // Orderings never go through a bijection that is not monotone.
    check_to(&eng, "x + 7 <u y + 7", "x + 7 <u y + 7", 8);
    check_to(&eng, "x * 3 <u 5", "x * 3 <u 5", 8);
    // The pass alone (fact folding would decide some of these first): no preimage.
    let only = engine(vec![Phase::Invert]);
    check_to(&only, "zext<16>(x + 1) != 0x1ff", "true", 8);
    check_to(&only, "sext<16>(x ^ 3) == 0x80", "false", 8);
    check_to(&only, "sext<16>(x ^ 3) == 0xff80", "x == 0x83", 8);
    check_to(&only, "(concat(x, 1:4) | y:12) == 0", "false", 8);
    check_to(&only, "(concat(x, 1:4) | y:12) != 0", "true", 8);
    check_to(
        &only,
        "(zext<16>(x) | concat(y, 0:8)) == 0",
        "(x == 0) & (y == 0)",
        8,
    );
    // `zext<16>(x)` is never `0xffff`; `sext<16>(x)` is, at one value.
    check_to(
        &only,
        "(zext<16>(x) & concat(y, 0xff:8)) == 0xffff",
        "false",
        8,
    );
    check_to(
        &only,
        "(sext<16>(x) & concat(y, 0xff:8)) == 0xffff",
        "(x == 0xff) & (y == 0xff)",
        8,
    );
}

/// Checks `src` simplifies to `want` at `w` bits under `eng`, assuming each of `under` true.
fn check_under(eng: &Engine, under: &[&str], src: &str, want: &str, w: u16) {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::new(w).unwrap());
    let e = cx.parse(src, &o).unwrap();
    let mut a = Assumptions::new();
    for u in under {
        let u = cx.parse(u, &o).unwrap();
        a.assume_true(&mut cx, u).unwrap();
    }
    let out = eng
        .run(&mut cx, &[e], Run::default().with_assumptions(&a))
        .unwrap()
        .roots[0];
    let want = cx
        .parse(want, &ParseOptions::width(cx.width(e).unwrap()))
        .unwrap();
    assert_eq!(
        out.expr,
        want,
        "{src} under {under:?} gave {}",
        cx.display(out.expr)
    );
}

#[test]
fn monotone_fixtures() {
    let eng = Engine::standard();
    let only = engine(vec![Phase::Invert]);
    // Layers monotone at every input, on both sides: the order they are monotone from.
    check_to(&eng, "zext<16>(x) <u zext<16>(y)", "x <u y", 8);
    check_to(&eng, "zext<16>(x) <s zext<16>(y)", "x <u y", 8);
    check_to(&eng, "sext<16>(x) <s sext<16>(y)", "x <s y", 8);
    check_to(&eng, "sext<16>(x) <u sext<16>(y)", "x <u y", 8);
    check_to(&eng, "concat(x, 3:4) <=u concat(y, 3:4)", "x <=u y", 8);
    check_to(&eng, "concat(x, 3:4) <s concat(y, 3:4)", "x <s y", 8);
    check_to(&eng, "concat(3:4, x) <s concat(3:4, y)", "x <u y", 8);
    check_to(&eng, "concat(9:4, x) <u concat(9:4, y)", "x <u y", 8);
    // Decreasing: the sides swap. Between orders: `x ^ smin`.
    check_to(&only, "~x <u ~y", "y <u x", 8);
    check_to(&only, "~x <=s ~y", "y <=s x", 8);
    check_to(&only, "(x ^ 0x80) <u (y ^ 0x80)", "x <s y", 8);
    check_to(&only, "(x ^ 0x80) <s (y ^ 0x80)", "x <u y", 8);
    check_to(&only, "(x + 0x80) <u (y + 0x80)", "x <s y", 8);
    // Chains, mixing orders along the way.
    check_to(&only, "zext<16>(~x) <s zext<16>(~y)", "y <u x", 8);
    check_to(&only, "~zext<16>(x) <u ~zext<16>(y)", "y <u x", 8);
    check_to(
        &only,
        "sext<16>(x ^ 0x80) <s sext<16>(y ^ 0x80)",
        "x <u y",
        8,
    );
    // Not without facts: a sum, a product or a shift may wrap.
    check_to(&only, "x + 7 <u y + 7", "x + 7 <u y + 7", 8);
    check_to(&only, "x * 3 <s y * 3", "x * 3 <s y * 3", 8);
    check_to(&only, "(x << 1) <u (y << 1)", "(x << 1) <u (y << 1)", 8);
    check_to(&only, "-x <u -y", "-x <u -y", 8);
    // ... and with them, when both ranges keep to one piece.
    check_under(
        &eng,
        &["x <u 100", "y <u 100"],
        "x + 7 <u y + 7",
        "x <u y",
        8,
    );
    check_under(
        &eng,
        &["x <u 100", "y <u 100", "k <u 10"],
        "x + k <u y + k",
        "x <u y",
        8,
    );
    check_under(
        &eng,
        &["x <u 100", "y <u 100"],
        "x - 7 <u y - 7",
        "x - 7 <u y - 7",
        8,
    );
    check_under(&eng, &["7 <=u x", "7 <=u y"], "x - 7 <u y - 7", "x <u y", 8);
    check_under(
        &eng,
        &["x <=u 50", "y <=u 50"],
        "50 - x <u 50 - y",
        "y <u x",
        8,
    );
    check_under(&eng, &["0 <u x", "0 <u y"], "-x <u -y", "y <u x", 8);
    check_under(
        &eng,
        &["x <s 50", "-50 <s x", "y <s 50", "-50 <s y"],
        "x + 7 <s y + 7",
        "x <s y",
        8,
    );
    check_under(
        &eng,
        &["x <s 40", "-40 <s x", "y <s 40", "-40 <s y"],
        "x * 3 <s y * 3",
        "x <s y",
        8,
    );
    check_under(
        &eng,
        &["x <s 40", "-40 <s x", "y <s 40", "-40 <s y"],
        "x * -3 <s y * -3",
        "y <s x",
        8,
    );
    check_under(&eng, &["x <u 80", "y <u 80"], "x * 3 <u y * 3", "x <u y", 8);
    check_under(
        &eng,
        &["x <u 60", "y <u 60"],
        "(x << 2) <u (y << 2)",
        "x <u y",
        8,
    );
    check_under(
        &eng,
        &["x <u 30", "y <u 30"],
        "(x << 2) <s (y << 2)",
        "x <s y",
        8,
    );
    check_under(
        &eng,
        &["x <u 60", "y <u 60"],
        "(x << 2) <s (y << 2)",
        "(x << 2) <s (y << 2)",
        8,
    );
    // Both on the wrapping piece is fine. One on each is not, unsigned; but read from the
    // signed order, `v + 10` is increasing on all of `[-6, 9]`.
    check_under(
        &eng,
        &["200 <=u x", "200 <=u y"],
        "x + 100 <u y + 100",
        "x <u y",
        8,
    );
    check_under(
        &only,
        &["x <u 10", "250 <=u y"],
        "x + 10 <u y + 10",
        "x <s y",
        8,
    );
    check_under(
        &only,
        &["200 <=u x", "x <u 210", "250 <=u y"],
        "x + 10 <u y + 10",
        "x + 10 <u y + 10",
        8,
    );
    // Against a constant: a threshold, or decided.
    check_to(&only, "zext<16>(x) <u 300", "true", 8);
    check_to(&only, "zext<16>(x) <u 100", "x <u 100", 8);
    check_to(&only, "zext<16>(x) <s 0xffff", "false", 8);
    check_to(&only, "sext<16>(x) <s 5", "x <s 5", 8);
    check_to(&only, "sext<16>(x) <=s 0x7f", "true", 8);
    check_to(&only, "sext<16>(x) <s 0xff80", "false", 8);
    check_to(&only, "~x <u 5", "0xfb <=u x", 8);
    check_to(&only, "5 <u ~x", "x <u 0xfa", 8);
    check_to(&only, "(x ^ 0x80) <u 0x90", "x <s 0x10", 8);
    check_to(&only, "0x90 <=u (x ^ 0x80)", "0x10 <=s x", 8);
    check_to(&only, "concat(x, 3:4) <u 0x5a3", "x <u 0x5a", 8);
    check_to(&only, "concat(x, 3:4) <u 0x5a4", "x <u 0x5b", 8);
    check_to(&only, "concat(x, 3:4) <u 0x5a2", "x <u 0x5a", 8);
    check_to(&only, "(x << 1) <u 10", "(x << 1) <u 10", 8);
    check_under(&eng, &["x <u 100"], "x + 7 <u 50", "x <u 43", 8);
    check_under(&eng, &["x <u 100"], "x + 7 <u 200", "true", 8);
    check_under(&eng, &["x <u 60"], "(x << 2) <u 100", "x <u 25", 8);
    check_under(
        &eng,
        &["x <s 40", "-40 <s x"],
        "x * 3 <s -30",
        "x <s -10",
        8,
    );
}

#[test]
fn monotone_trees() {
    let eng = Engine::standard();
    let only = engine(vec![Phase::Invert]);
    // A select passes its order to its arms: the leaves of both sides are peeled together.
    check_to(
        &only,
        "select(c, zext<16>(x), zext<16>(y)) <u zext<16>(z)",
        "select(c, x, y) <u z",
        8,
    );
    check_to(
        &eng,
        "select(zext<16>(x) <u zext<16>(y), zext<16>(x), zext<16>(y)) <u zext<16>(z)",
        "select(x <u y, x, y) <u z",
        8,
    );
    check_to(&only, "select(c, ~x, ~y) <u ~z", "z <u select(c, x, y)", 8);
    check_to(
        &only,
        "select(c, select(d, ~x, ~y), ~w) <=s ~z",
        "z <=s select(c, select(d, x, y), w)",
        8,
    );
    check_to(
        &only,
        "select(c, x ^ 0x80, y ^ 0x80) <s (z ^ 0x80)",
        "select(c, x, y) <u z",
        8,
    );
    // A constant leaf stands for its exact preimage, or stops the peeling.
    check_to(
        &only,
        "select(c, zext<16>(x), 5) <u zext<16>(z)",
        "select(c, x, 5) <u z",
        8,
    );
    check_to(
        &only,
        "select(c, zext<16>(x), 300) <u zext<16>(z)",
        "select(c, zext<16>(x), 300) <u zext<16>(z)",
        8,
    );
    check_to(
        &only,
        "select(c, ~x, 5) <u ~z",
        "z <u select(c, x, 0xfa)",
        8,
    );
    // ... but not through a layer monotone only on the facts' range.
    check_under(
        &only,
        &["x <u 10", "z <u 10"],
        "select(c, x + 1, 5) <u z + 1",
        "select(c, x + 1, 5) <u z + 1",
        8,
    );
    check_under(
        &only,
        &["x <u 10", "y <u 10", "z <u 10"],
        "select(c, x + 1, y + 1) <u z + 1",
        "select(c, x, y) <u z",
        8,
    );
    // Different layers, or one leaf that is not a layer: nothing.
    check_to(
        &only,
        "select(c, zext<16>(x), sext<16>(y)) <u zext<16>(z)",
        "select(c, zext<16>(x), sext<16>(y)) <u zext<16>(z)",
        8,
    );
    check_to(
        &only,
        "select(c, zext<16>(x), w) <u zext<16>(z)",
        "select(c, zext<16>(x), w) <u zext<16>(z)",
        8,
    );
    // Equalities through selects: an injective layer, constants by preimage.
    check_to(
        &only,
        "select(c, x + 1, y + 1) == z + 1",
        "select(c, x, y) == z",
        8,
    );
    check_to(
        &only,
        "select(c, x * 3, 7) != y * 3",
        "select(c, x, 0xad) != y",
        8,
    );
    check_to(
        &only,
        "select(c, zext<16>(x), 300) == zext<16>(z)",
        "select(c, zext<16>(x), 300) == zext<16>(z)",
        8,
    );
    check_to(
        &only,
        "select(c, x ^ (x >>u 4), y ^ (y >>u 4)) == z ^ (z >>u 4)",
        "select(c, x, y) == z",
        8,
    );
}

/// Random chains of layers monotone where the facts allow (sums, differences, products and
/// shifts by a constant or a shared symbol, complements, negations, `^ smin`, casts and
/// concatenations), compared through every ordering on both sides or against a constant, under
/// random range assumptions on the symbols: the result agrees with the input on every
/// assignment the assumptions admit.
#[test]
fn monotone_is_sound_under_ranges() {
    let eng = Engine::standard();
    let only = engine(vec![Phase::Invert]);
    let mut g = generator(0x3030_0001);
    let (mut changed, mut by_pass) = (0, 0);
    for _ in 0..800 {
        let mut cx = Context::new();
        let w = 3 + g.rng.below(3) as u16;
        let wd = Width::new(w).unwrap();
        let (x, y, k) = (
            cx.symbol("x", wd).unwrap(),
            cx.symbol("y", wd).unwrap(),
            cx.symbol("k", wd).unwrap(),
        );
        let (mut e, mut ew) = (x, w);
        for _ in 0..1 + g.rng.below(3) {
            let ewd = Width::new(ew).unwrap();
            let p = if ew == w && g.rng.chance(1, 3) {
                k
            } else {
                let v = g.constant(ew);
                cx.constant(&v).unwrap()
            };
            e = match g.rng.below(10) {
                0 => cx.bin(BinOp::Add, e, p).unwrap(),
                1 => cx.bin(BinOp::Sub, e, p).unwrap(),
                2 => cx.bin(BinOp::Sub, p, e).unwrap(),
                3 => cx.bin(BinOp::Mul, e, p).unwrap(),
                4 => {
                    let s = cx.constant_u64(ewd, g.rng.below(3)).unwrap();
                    cx.bin(BinOp::Shl, e, s).unwrap()
                }
                5 => cx.un(UnOp::Not, e).unwrap(),
                6 => cx.un(UnOp::Neg, e).unwrap(),
                7 => {
                    let m = cx.constant(&BitVec::smin(ewd)).unwrap();
                    cx.bin(BinOp::Xor, e, m).unwrap()
                }
                _ if ew >= 7 => e,
                _ => {
                    let to = Width::new(ew + 1 + g.rng.below(2) as u16).unwrap();
                    let r = match g.rng.below(4) {
                        0 => cx.zext(e, to).unwrap(),
                        1 => cx.sext(e, to).unwrap(),
                        2 => {
                            let c = cx.constant(&g.constant(to.bits() - ew)).unwrap();
                            cx.concat(e, c).unwrap()
                        }
                        _ => {
                            let c = cx.constant(&g.constant(to.bits() - ew)).unwrap();
                            cx.concat(c, e).unwrap()
                        }
                    };
                    ew = to.bits();
                    r
                }
            };
        }
        let op =
            [CmpOpExt::Ult, CmpOpExt::Ule, CmpOpExt::Slt, CmpOpExt::Sle][g.rng.below(4) as usize];
        let root = match g.rng.below(6) {
            0 => {
                let fy = cx.substitute(&[e], &[(x, y)]).unwrap()[0];
                cx.cmp(op, e, fy).unwrap()
            }
            // Select trees over the chain at `x`, `y`, `k` and constants, compared by an
            // ordering or an equality.
            4 | 5 => {
                let fy = cx.substitute(&[e], &[(x, y)]).unwrap()[0];
                let fk = cx.substitute(&[e], &[(x, k)]).unwrap()[0];
                let ewd = Width::new(ew).unwrap();
                let leaf = |cx: &mut Context, g: &mut Gen| match g.rng.below(4) {
                    0 => e,
                    1 => fy,
                    2 => fk,
                    _ => {
                        let v = g.constant(ewd.bits());
                        cx.constant(&v).unwrap()
                    }
                };
                let cond = |cx: &mut Context, g: &mut Gen| {
                    let a = [x, y, k][g.rng.below(3) as usize];
                    let b = [x, y, k][g.rng.below(3) as usize];
                    cx.cmp(CmpOpExt::Ult, a, b).unwrap()
                };
                let c1 = cond(&mut cx, &mut g);
                let (l1, l2) = (leaf(&mut cx, &mut g), leaf(&mut cx, &mut g));
                let a = cx.select(c1, l1, l2).unwrap();
                let b = if g.rng.chance(1, 2) {
                    leaf(&mut cx, &mut g)
                } else {
                    let c2 = cond(&mut cx, &mut g);
                    let (l3, l4) = (leaf(&mut cx, &mut g), leaf(&mut cx, &mut g));
                    cx.select(c2, l3, l4).unwrap()
                };
                let op = if g.rng.chance(1, 3) {
                    [CmpOpExt::Eq, CmpOpExt::Ne][g.rng.below(2) as usize]
                } else {
                    op
                };
                cx.cmp(op, a, b).unwrap()
            }
            1 => {
                let c = cx.constant(&g.constant(ew)).unwrap();
                cx.cmp(op, c, e).unwrap()
            }
            _ => {
                let c = cx.constant(&g.constant(ew)).unwrap();
                cx.cmp(op, e, c).unwrap()
            }
        };
        // Range assumptions: each symbol bounded on either side, in either order, or not.
        let mut preds = Vec::new();
        for s in [x, y, k] {
            for _ in 0..g.rng.below(3) {
                let c = cx.constant(&g.constant(w)).unwrap();
                let op = [CmpOpExt::Ult, CmpOpExt::Ule, CmpOpExt::Slt, CmpOpExt::Sle]
                    [g.rng.below(4) as usize];
                preds.push(if g.rng.chance(1, 2) {
                    cx.cmp(op, s, c).unwrap()
                } else {
                    cx.cmp(op, c, s).unwrap()
                });
            }
        }
        let mut a = Assumptions::new();
        for &p in &preds {
            a.assume_true(&mut cx, p).unwrap();
        }
        if a.is_infeasible() {
            continue;
        }
        for engine in [&eng, &only] {
            let out = engine
                .run(&mut cx, &[root], Run::default().with_assumptions(&a))
                .unwrap();
            let r = out.roots[0];
            assert_eq!(out.stats.rejected, 0, "{}", cx.display(root));
            if !r.changed {
                continue;
            }
            changed += 1;
            by_pass += u64::from(core::ptr::eq(engine, &only));
            for case in 0..1u64 << (3 * w) {
                let vals = [
                    ("x", case & ((1 << w) - 1)),
                    ("y", (case >> w) & ((1 << w) - 1)),
                    ("k", case >> (2 * w)),
                ];
                let env = FnEnv(|key: &crate::SymbolKey, _| {
                    vals.iter()
                        .find(|(n, _)| *key == crate::SymbolKey::from(*n))
                        .map(|(_, v)| BitVec::wrapping_from_u64(wd, *v))
                });
                let pv = cx.eval(&preds, &env).unwrap();
                if pv.iter().any(BitVec::is_zero) {
                    continue;
                }
                let v = cx.eval(&[root, r.expr], &env).unwrap();
                assert_eq!(
                    v[0],
                    v[1],
                    "{} -> {} under {:?} at {vals:?}",
                    cx.display(root),
                    cx.display(r.expr),
                    preds
                        .iter()
                        .map(|&p| cx.display(p).to_string())
                        .collect::<Vec<_>>()
                );
            }
        }
    }
    assert!(changed > 300 && by_pass > 100, "{changed} {by_pass}");
}

#[test]
fn invert_cancels_and_solves_permutation_polynomials() {
    let eng = Engine::standard();
    // `2x² + x`, `x·(2x + 1)` and `4x³ + 2x² + 3x` are bijections (bit `k` is `x_k` flipped
    // by lower bits); `x² + x` is not (it is always even).
    check_to(&eng, "2 * x * x + x == 2 * y * y + y", "x == y", 17);
    check_to(&eng, "x * (2 * x + 1) == y * (2 * y + 1)", "x == y", 17);
    check_to(
        &eng,
        "4 * x * x * x + 2 * x * x + 3 * x == 4 * y * y * y + 2 * y * y + 3 * y",
        "x == y",
        64,
    );
    check_to(&eng, "2 * x * x + x == 2 * y * y + y", "x == y", 64);
    check_to(&eng, "x * x + x == y * y + y", "x * x + x == y * y + y", 17);
    // Solved: 2·72115² + 72115 = 5, and 2·0x26c89aff803319b3² + … = 5, modulo the width.
    check_to(&eng, "2 * x * x + x == 5", "x == 72115", 17);
    check_to(&eng, "2 * x * x + x == 5", "x == 0x26c89aff803319b3", 64);
    // A truncation of a map that is a bijection only at the truncated width: compared there.
    check_to(
        &eng,
        "trunc<17>(2 * x * x + x) == trunc<17>(2 * y * y + y)",
        "trunc<17>(x) == trunc<17>(y)",
        64,
    );
    check_to(
        &eng,
        "trunc<17>(x * 0x1234567 + 9) == 77",
        "trunc<17>(x) == 110364",
        64,
    );
    check_to(
        &eng,
        "trunc<17>(x * x + x) == trunc<17>(y * y + y)",
        "trunc<17>(x * x + x) == trunc<17>(y * y + y)",
        64,
    );
}

#[test]
fn invert_commits_like_a_rule_through_sharing() {
    // The hash stays live as another root; its comparison is solved anyway.
    let eng = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let h = cx
        .parse(
            "let m = (x ^ 0x1234) * 0x87c37b91114253d5; m ^ (m >>u 29)",
            &o,
        )
        .unwrap();
    let c = cx.constant_u64(Width::W64, 0xfeed).unwrap();
    let e = cx.cmp(CmpOpExt::Eq, h, c).unwrap();
    let out = eng.run(&mut cx, &[h, e], Run::default()).unwrap();
    assert!(!out.roots[0].changed);
    let r = out.roots[1].expr;
    let crate::View::Cmp(crate::CmpOp::Eq, a, k) = cx.view(r).unwrap() else {
        panic!("{}", cx.display(r));
    };
    assert_eq!(cx.display(a).to_string(), "x");
    // And the constant is the preimage.
    let v = cx.as_const(k).unwrap().unwrap();
    let env = FnEnv(|_: &crate::SymbolKey, _| Some(v));
    assert_eq!(cx.eval(&[h], &env).unwrap()[0].to_u64(), Some(0xfeed));
}

#[test]
fn invert_relies_on_the_constraints_it_uses() {
    let eng = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let e = cx.parse("x * k == y * k", &o).unwrap();
    // `k` is not known to be odd: nothing to cancel.
    assert!(!eng.simplify(&mut cx, e).unwrap().changed);
    let odd = cx.parse("(k & 1) == 1", &o).unwrap();
    let other = cx.parse("x <u 100", &o).unwrap();
    let mut a = Assumptions::new();
    let u = a.assume_true(&mut cx, other).unwrap();
    let id = a.assume_true(&mut cx, odd).unwrap();
    let out = eng
        .run(&mut cx, &[e], Run::default().with_assumptions(&a))
        .unwrap()
        .roots[0];
    assert_eq!(cx.display(out.expr).to_string(), "x == y");
    assert!(
        out.relies_on.may_use(id) && !out.relies_on.may_use(u),
        "{:?}",
        out.relies_on
    );
    // So does the proof query.
    let (x, p) = (cx.parse("x", &o).unwrap(), cx.parse("x * k", &o).unwrap());
    let q = crate::Query::Bijective { e: p, of: x };
    assert_eq!(cx.prove(q).unwrap(), crate::Truth::Unknown);
    let proof = cx.prove_under(q, &a).unwrap();
    assert_eq!(proof.truth, crate::Truth::True);
    assert!(proof.relies_on.may_use(id) && !proof.relies_on.may_use(u));
}

#[test]
fn invert_obeys_budgets_and_the_host_veto() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let src = "let m = (x ^ 0x1234) * 0x87c37b91114253d5; \
               let s = m ^ ((m >>u 32) >>u (m >>u 60)); s * 0x87c37b91114253d5 == 0x42";
    let e = cx.parse(src, &o).unwrap();
    let eng = engine(vec![Phase::Invert]);
    // Every budget from nothing up: a sound result, never a panic.
    let mut rng = Rng(5);
    let mut done = false;
    for work in (0..3000).step_by(61) {
        cx.memo.clear();
        let run = Run::default().with_per_call(Budget::default().with_pass_work(work));
        let r = eng.run(&mut cx, &[e], run).unwrap().roots[0];
        assert!(equivalent(&mut cx, e, r.expr, &mut rng));
        done |= r.end == End::Completed && r.changed;
    }
    assert!(done);
    // The host can refuse the rewrite.
    struct No;
    impl Hooks for No {
        fn admit(&self, _: &Context, _: Expr, _: Expr, by: crate::engine::By<'_>) -> bool {
            !matches!(by, crate::engine::By::Pass("invert"))
        }
    }
    cx.memo.clear();
    let r = eng
        .run(&mut cx, &[e], Run::default().with_hooks(&No))
        .unwrap();
    assert!(!r.roots[0].changed);
    assert!(r.stats.hook_vetoes > 0);
}

/// The linear pass takes a constant into a term (`k·a + k = −k·~a`) when that is smaller,
/// doubles as `a + a`, starts a sum of subtractions from its constant or a product by a
/// negative coefficient, reads `concat(trunc(x), c)` as `x·2^|c| + c`, and a constant always
/// replaces what it folds.
#[test]
fn linear_emissions() {
    let eng = engine(vec![Phase::Linear]);
    for (src, want) in [
        ("-x - 1", "~x"),
        ("(y << 2) + 4", "~y * -4"),
        ("-2 * y - 2", "let %0 = ~y;\n%0 + %0"),
        ("2 * x + y", "x + x + y"),
        ("5 - 3 * x", "5 - x * 3"),
        ("-(y * 3) - z * 5", "y * -3 - z * 5"),
        (
            "concat(trunc<62>(y), 3:2) - 6 * y - 5",
            "let %0 = ~y;\n%0 + %0",
        ),
    ] {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx.parse(src, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(cx.display(out.expr).to_string(), want, "{src}");
    }
    // A constant replaces the node it is, even beside a shared term: `~x + x` is −1.
    let eng = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let e = cx.parse("(~x ^ (x + ~x)) + y", &o).unwrap();
    let out = eng.simplify(&mut cx, e).unwrap();
    assert_eq!(cx.display(out.expr).to_string(), "x + y");
}

/// `a + a` is `a << 1` for the facts: its low bit is known.
#[test]
fn doubling_knows_its_low_bit() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let e = cx.parse("x + x", &o).unwrap();
    let f = cx.facts(e).unwrap();
    assert_eq!(f.known().known_zero().bit(0), Some(true));
}

/// The MBA service with the native solver, on bitwright's own evidence (the `bw-nf` setup).
#[cfg(feature = "mba")]
mod native_mba {
    use super::*;
    use crate::Bounded;
    use crate::mba::{MbaConfig, MbaTrust, NormalFormSolver};
    use std::sync::Arc;

    fn nf_engine() -> Engine {
        let trust = MbaTrust::default().with_backend_certificates(false);
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default().with_trust(trust)))
            .mba_solver(Arc::new(NormalFormSolver::default()))
            .build()
            .unwrap()
    }

    fn size(cx: &mut Context, e: Expr) -> u32 {
        match cx.dag_size(&[e], u32::MAX).unwrap() {
            Bounded::Exact(n) => n,
            _ => u32::MAX,
        }
    }

    /// A sum of sixty null products (`2^57·c·x(x − 1)⋯(x − 7)·y^j` is 0 at 64 bits: 8! has
    /// the other seven factors of two) and `3·x`: the question is asked at the top of the sum
    /// first, and never at every link, so it is answered within the call budget.
    #[test]
    fn chains_are_asked_at_their_tops() {
        let mut src = String::from("x * 3");
        for i in 0..60u64 {
            let c = (2 * i + 1) << 57;
            src.push_str(&format!(" + {c} * x"));
            for d in 1..8 {
                src.push_str(&format!(" * (x - {d})"));
            }
            for _ in 0..i % 3 {
                src.push_str(" * y");
            }
        }
        let mut cx = Context::new();
        let e = cx.parse(&src, &ParseOptions::width(Width::W64)).unwrap();
        let out = nf_engine().run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(r.end, End::Completed);
        // `x * 3` or `x + x + x`: three nodes either way.
        assert_eq!(size(&mut cx, r.expr), 3, "{}", cx.display(r.expr));
        assert!(out.stats.mba.calls < 400, "{}", out.stats.mba.calls);
    }

    /// A link of a chain is asked when its user is not: a shift by a variable is no MBA
    /// operator, and a sum over more variables than the limits allow is refused.
    #[test]
    fn links_are_asked_under_users_that_are_not() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx
            .parse("((x & y) * (x | y) + (x & ~y) * (~x & y)) << z", &o)
            .unwrap();
        let out = nf_engine().simplify(&mut cx, e).unwrap();
        assert_eq!(cx.display(out.expr).to_string(), "x * y << z");
        let lim = crate::mba::MbaLimits::default().with_max_vars(2);
        let trust = MbaTrust::default().with_backend_certificates(false);
        let cfg = MbaConfig::default().with_trust(trust).with_limits(lim);
        let eng = Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate().with_mba(cfg))
            .mba_solver(Arc::new(NormalFormSolver::default()))
            .build()
            .unwrap();
        let mut cx = Context::new();
        let e = cx
            .parse("(x & y) * (x | y) + (x & ~y) * (~x & y) + z", &o)
            .unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(cx.display(out.expr).to_string(), "x * y + z");
    }

    /// Accurate use counts: a replaced node (and what only it used) no longer counts as a user,
    /// so a smaller answer is committed (10 nodes for 13).
    #[test]
    fn replaced_nodes_do_not_count_as_users() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx
            .parse("(~x & y) * -15 - ((~y & x) << 3) - 7", &o)
            .unwrap();
        let out = nf_engine().simplify(&mut cx, e).unwrap();
        assert!(size(&mut cx, out.expr) <= 10, "{}", cx.display(out.expr));
    }
}

// ----- bit subsets, masked bitwise functions, and both readings of a condition -----------------

/// A term of width `w` (at most 6) over `x`, `y` of 6 bits: their extractions, constants,
/// bitwise operations, and extractions, extensions and concatenations of other terms.
fn subset_term(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 4) {
        if g.rng.chance(1, 4) {
            let v = g.constant(w);
            return cx.constant(&v).unwrap();
        }
        let s = cx
            .symbol(["x", "y"][g.rng.below(2) as usize], Width::new(6).unwrap())
            .unwrap();
        let lo = g.rng.below(u64::from(6 - w) + 1) as u16;
        return cx.extract(s, lo, width).unwrap();
    }
    let d = depth - 1;
    match g.rng.below(9) {
        0 => {
            let a = subset_term(g, cx, w, d);
            cx.un(UnOp::Not, a).unwrap()
        }
        1..=4 => {
            let a = subset_term(g, cx, w, d);
            let b = subset_term(g, cx, w, d);
            let op = [BinOp::And, BinOp::And, BinOp::Or, BinOp::Xor][g.rng.below(4) as usize];
            cx.bin(op, a, b).unwrap()
        }
        5 if w > 1 => {
            let from = 1 + g.rng.below(u64::from(w) - 1) as u16;
            let a = subset_term(g, cx, from, d);
            cx.zext(a, width).unwrap()
        }
        6 if w < 6 => {
            let from = w + 1 + g.rng.below(u64::from(6 - w)) as u16;
            let lo = g.rng.below(u64::from(from - w) + 1) as u16;
            let a = subset_term(g, cx, from, d);
            cx.extract(a, lo, width).unwrap()
        }
        7 if w > 1 => {
            let h = 1 + g.rng.below(u64::from(w) - 1) as u16;
            let a = subset_term(g, cx, h, d);
            let b = subset_term(g, cx, w - h, d);
            cx.concat(a, b).unwrap()
        }
        _ => subset_term(g, cx, w, d),
    }
}

/// Every value of `e` over `x`, `y` of 6 bits.
fn values_6x6(cx: &mut Context, e: Expr) -> Vec<BitVec> {
    let w6 = Width::new(6).unwrap();
    (0..1u64 << 12)
        .map(|i| {
            let (xv, yv) = (
                BitVec::wrapping_from_u64(w6, i & 63),
                BitVec::wrapping_from_u64(w6, i >> 6),
            );
            let env = FnEnv(|k: &crate::SymbolKey, _| match k.to_string().as_str() {
                "x" => Some(xv),
                "y" => Some(yv),
                _ => None,
            });
            cx.eval(&[e], &env).unwrap()[0]
        })
        .collect()
}

/// What the order reading takes as bit subsets is: whenever `submask(b, a)` holds, no value of
/// `b` has a bit `a`'s lacks (exhaustively), and `zero_bits` likewise; and both hold often.
#[test]
fn bit_subsets_are_sound() {
    bit_subsets_are_sound_cases(1000);
}

/// [`bit_subsets_are_sound`] over 3000 random cases.
#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn bit_subsets_are_sound_heavy() {
    bit_subsets_are_sound_cases(3000);
}

fn bit_subsets_are_sound_cases(cases: usize) {
    let mut g = generator(0x0005_b5e7);
    let (mut subsets, mut zeros) = (0, 0);
    for _ in 0..cases {
        let mut cx = Context::new();
        let w = 1 + g.rng.below(6) as u16;
        let width = Width::new(w).unwrap();
        let a = subset_term(&mut g, &mut cx, w, 3);
        // Often a term built from the other, so that the relation is there to find.
        let b = match g.rng.below(4) {
            0 => {
                let t = subset_term(&mut g, &mut cx, w, 2);
                cx.bin(BinOp::And, a, t).unwrap()
            }
            1 => {
                let wide = subset_term(&mut g, &mut cx, w, 2);
                let t = cx.bin(BinOp::And, a, wide).unwrap();
                let t = cx.zext(t, Width::new(6).unwrap()).unwrap();
                let u = subset_term(&mut g, &mut cx, 6, 1);
                let t = cx.bin(BinOp::And, t, u).unwrap();
                cx.extract(t, 0, width).unwrap()
            }
            _ => subset_term(&mut g, &mut cx, w, 3),
        };
        let (ai, bi) = (cx.id(a).unwrap(), cx.id(b).unwrap());
        let mut left = super::order::SUBMASK_STEPS;
        if super::order::submask(&cx, bi, 0, ai, 0, w, &mut left) {
            let (va, vb) = (values_6x6(&mut cx, a), values_6x6(&mut cx, b));
            for (x, y) in vb.iter().zip(&va) {
                let extra =
                    BitVec::bin_unchecked(BinOp::And, x, &BitVec::un_unchecked(UnOp::Not, y));
                assert!(
                    extra.is_zero(),
                    "W={w}: {} not within {}",
                    cx.display(b),
                    cx.display(a)
                );
            }
            subsets += 1;
        }
        let mut left = super::order::SUBMASK_STEPS;
        let lo = g.rng.below(u64::from(w)) as u16;
        let len = 1 + g.rng.below(u64::from(w - lo)) as u16;
        if super::order::zero_bits(&cx, bi, lo, len, &mut left) {
            for v in values_6x6(&mut cx, b) {
                let part = v.extract(lo, Width::new(len).unwrap()).unwrap();
                assert!(
                    part.is_zero(),
                    "W={w}: bits {lo}+{len} of {}",
                    cx.display(b)
                );
            }
            zeros += 1;
        }
    }
    assert!(
        subsets > 600 * cases / 3000 && zeros > 300 * cases / 3000,
        "{subsets} subsets, {zeros} zero windows"
    );
}

/// Comparisons and selects of bit-subset terms through the order reading: sound
/// (exhaustively), idempotent, and many decided.
#[test]
fn order_through_bit_subsets_is_sound_and_idempotent() {
    use crate::CmpOpExt;
    let eng = engine(vec![Phase::Compares]);
    let mut g = generator(0x0de6);
    let mut rng = Rng(47);
    let mut changed = 0;
    for _ in 0..2000 {
        let mut cx = Context::new();
        let w = 1 + g.rng.below(6) as u16;
        let a = subset_term(&mut g, &mut cx, w, 3);
        let b = if g.rng.chance(1, 2) {
            let t = subset_term(&mut g, &mut cx, w, 2);
            let t = cx.bin(BinOp::And, a, t).unwrap();
            let s = cx.symbol("x", Width::new(6).unwrap()).unwrap();
            let u = cx.zext(t, Width::new(6).unwrap()).unwrap();
            let u = cx.bin(BinOp::And, u, s).unwrap();
            cx.trunc(u, Width::new(w).unwrap()).unwrap()
        } else {
            subset_term(&mut g, &mut cx, w, 3)
        };
        let ops = [
            CmpOpExt::Ult,
            CmpOpExt::Ule,
            CmpOpExt::Slt,
            CmpOpExt::Sle,
            CmpOpExt::Eq,
        ];
        let op = ops[g.rng.below(ops.len() as u64) as usize];
        let (p, q) = if g.rng.chance(1, 2) { (a, b) } else { (b, a) };
        let c = cx.cmp(op, p, q).unwrap();
        let e = if g.rng.chance(1, 3) {
            cx.select(c, p, q).unwrap()
        } else {
            c
        };
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {}",
            cx.display(r.expr)
        );
    }
    assert!(changed > 400, "{changed}");
}

/// A random bitwise expression over `a`, `b`, `c` and constants from a small pool.
fn masked_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32, pool: &[BitVec]) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 5) {
        return match g.rng.below(5) {
            0 | 1 => {
                let v = pool[g.rng.below(pool.len() as u64) as usize];
                cx.constant(&v).unwrap()
            }
            k => cx.symbol(["a", "b", "c"][(k - 2) as usize], width).unwrap(),
        };
    }
    let d = depth - 1;
    match g.rng.below(4) {
        0 => {
            let x = masked_expr(g, cx, w, d, pool);
            cx.un(UnOp::Not, x).unwrap()
        }
        k => {
            let x = masked_expr(g, cx, w, d, pool);
            let y = masked_expr(g, cx, w, d, pool);
            cx.bin([BinOp::And, BinOp::Or, BinOp::Xor][(k - 1) as usize], x, y)
                .unwrap()
        }
    }
}

/// Bitwise functions with constants, by classes of bit positions: sound (exhaustively at small
/// widths), idempotent, and often smaller.
#[test]
fn masked_bitwise_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Bitwise]);
    let mut g = generator(0xb17_3a5c);
    let mut rng = Rng(22);
    let mut changed = 0;
    for i in 0..2000 {
        let mut cx = Context::new();
        let w = if i % 10 == 0 {
            [8, 64, 129][g.rng.below(3) as usize]
        } else {
            1 + g.rng.below(4) as u16
        };
        let pool: Vec<BitVec> = (0..1 + g.rng.below(4)).map(|_| g.constant(w)).collect();
        let e = masked_expr(&mut g, &mut cx, w, 5, &pool);
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0);
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !again.roots[0].changed,
            "not idempotent: {}",
            cx.display(r.expr)
        );
    }
    assert!(changed > 500, "{changed}");
}

/// `p == q` of bitwise functions with constants is decided by their tables: soundly, and for
/// every pair that is the same function written twice.
#[test]
fn masked_equalities_are_decided_soundly() {
    use crate::CmpOpExt;
    let eng = engine(vec![Phase::Compares]);
    let rewrite = engine(vec![Phase::Bitwise]);
    let mut g = generator(0xe9_3a5c);
    let mut rng = Rng(23);
    let mut decided = 0;
    for _ in 0..2000 {
        let mut cx = Context::new();
        let w = 2 + g.rng.below(3) as u16;
        let pool: Vec<BitVec> = (0..1 + g.rng.below(3)).map(|_| g.constant(w)).collect();
        let p = masked_expr(&mut g, &mut cx, w, 4, &pool);
        // The same function in another form, or another function.
        let q = if g.rng.chance(1, 2) {
            let r = rewrite.run(&mut cx, &[p], Run::default()).unwrap().roots[0].expr;
            let x = cx.symbol("b", Width::new(w).unwrap()).unwrap();
            let y = cx.bin(BinOp::Xor, r, x).unwrap();
            cx.bin(BinOp::Xor, y, x).unwrap()
        } else {
            masked_expr(&mut g, &mut cx, w, 4, &pool)
        };
        let op = if g.rng.chance(1, 2) {
            CmpOpExt::Eq
        } else {
            CmpOpExt::Ne
        };
        let e = cx.cmp(op, p, q).unwrap();
        let r = eng.run(&mut cx, &[e], Run::default()).unwrap().roots[0];
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "W={w}: {} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        decided += u32::from(cx.const_val(cx.id(r.expr).unwrap()).is_some());
    }
    assert!(decided > 900, "{decided}");
}

#[test]
fn masked_bitwise_fixtures() {
    let eng = Engine::standard();
    for w in [8, 32, 64] {
        let (zero, f) = (format!("0:{w}"), "0:1".to_string());
        for (src, want) in [
            // Four atoms, one of them a mask: a function of three per class.
            ("~a & (~b & (y & 5))", "~(a | b) & y & 5"),
            ("(~a & (~b & (y & 5))) ^ (~(a | b) & y & 5)", &zero),
            // The same function written two ways is one value.
            ("~y & 37 != (y & 37) ^ 37", &f),
            ("~a & (~b & 37) & y != ~a & (~b & (y & 37))", &f),
            ("(x & y ^ x) & 37 != ~y & (x & 37)", &f),
            // Complementary on the mask's bits: never equal.
            ("(y & 5) == (~y & 5) | 2", &f),
        ] {
            assert_eq!(simplify(&eng, src, w), want, "{src} at {w} bits");
        }
        // Different functions stay.
        assert!(!simplify(&eng, "x & 5 == x & 6", w).contains(':'));
    }
    // Each two-class form, by the bitwise pass alone.
    let eng = engine(vec![Phase::Bitwise]);
    for (src, want) in [
        ("(y & a & 5) | (y & 5 & ~a)", "y & 5"),
        ("(~(y & a) & 5) | (y & a & 250)", "a & y ^ 5"),
        ("(y & a) | 5", "a & y | 5"),
        ("(~(y & a) & 5) | (a & 250)", "(~a | y) & 5 ^ a"),
    ] {
        assert_eq!(simplify(&eng, src, 8), want, "{src}");
    }
}

/// The borrow of an XOR or an OR with a constant done in limbs (`x ^ c` written `x + c − 2·(x
/// & c)`, its low limb compared with the sum's): the two low limbs differ by the conjunction,
/// which stays below the limb's top bit, so the high digit of the sum less the borrow is the
/// high digit of `x`.
#[cfg(feature = "prove")]
#[test]
fn limb_borrows_of_constant_masks() {
    let eng = deobfuscator();
    for (src, want) in [
        (
            "extract<18, 14>(x:32 + 0x19766) \
             + sext<14>(x + 0x19766 & 0x3ffff <u (x ^ 0x19766) & 0x3ffff)",
            "extract<18, 14>(x)",
        ),
        (
            "extract<18, 14>(x:32 + 0x19766) \
             + sext<14>(x + 0x19766 & 0x3ffff <u (x | 0x19766) & 0x3ffff)",
            "extract<18, 14>(x)",
        ),
    ] {
        assert_eq!(simplify(&eng, src, 32), want, "{src}");
    }
}

/// Limb arithmetic: a sum or difference computed digit by digit, the carry between the digits
/// written as a comparison of the low ones, is the sum or difference.
#[cfg(feature = "prove")]
#[test]
fn limb_carry_fixtures() {
    let eng = deobfuscator();
    for (src, want) in [
        // The high digits and the carry into them are the high digit of the sum.
        (
            "zext<64>(extract<3, 5>(x) + extract<3, 5>(y) \
             + zext<5>(trunc<3>(x + y) <u trunc<3>(x)))",
            "zext<64>(extract<3, 5>(x + y))",
        ),
        // The halves joined with a shift, not a `concat`.
        (
            "((x >>u 21) + (y >>u 21) + zext<64>((x + y & 0x1fffff) <u (x & 0x1fffff)) << 21) \
             | (x + y & 0x1fffff)",
            "x + y",
        ),
        (
            "((x >>u 21) - (y >>u 21) - zext<64>((x & 0x1fffff) <u (y & 0x1fffff)) << 21) \
             | (x - y & 0x1fffff)",
            "x - y",
        ),
    ] {
        assert_eq!(simplify(&eng, src, 64), want, "{src}");
    }
}

/// Limb arithmetic: a carry whose digits meet no term of its own sum (the sum has as many
/// terms with the carry read, or more) is read at the root once the rounds have changed
/// nothing, where the root so written needs no more nodes: the digits are slices of words
/// that are there, or what reads the sum reads them.
#[cfg(feature = "prove")]
#[test]
fn limb_late_carry_fixtures() {
    let eng = deobfuscator();
    let carry = "zext<12>(trunc<20>(x:32 + y:32) <u trunc<20>(x))";
    for (src, w, want) in [
        // The borrow of `x - y` beside one of its three high digits: the two others.
        (
            "zext<12>(trunc<20>(x:32) <u trunc<20>(y:32)) + extract<20, 12>(y)".to_string(),
            12,
            "extract<20, 12>(x) - extract<20, 12>(x - y)",
        ),
        // The carry of `x + y` beside the high digit of `x`: the high digit of the word,
        // which the `^` reads as well, less that of `y`.
        (
            format!("(extract<20, 12>(x:32) + {carry}) ^ extract<20, 12>(x + y)"),
            12,
            "let %0 = extract<20, 12>(x + y);\n%0 - extract<20, 12>(y) ^ %0",
        ),
        // What reads the sum reads the digit left over.
        (
            format!("(extract<20, 12>(x:32) + {carry}) * extract<20, 12>(y)"),
            12,
            "let %0 = extract<20, 12>(y);\n(extract<20, 12>(x + y) - %0) * %0",
        ),
        // The word's low limb beside its high one.
        (
            format!("zext<32>(extract<20, 12>(x:32) + {carry}) * (x + y & 0xfffff)"),
            32,
            "let %0 = x + y;\n\
             (%0 & 0xfffff) * zext<32>(extract<20, 12>(%0) - extract<20, 12>(y))",
        ),
        // Two borrows, each way.
        (
            "zext<12>(trunc<20>(x:32) <u trunc<20>(y:32)) \
             + zext<12>(trunc<20>(y) <u trunc<20>(x)) + extract<20, 12>(x * y)"
                .to_string(),
            12,
            "extract<20, 12>(x * y) - extract<20, 12>(y - x) - extract<20, 12>(x - y)",
        ),
    ] {
        assert_eq!(simplify(&eng, &src, w), want, "{src}");
    }
}

/// A carry whose digits meet nothing, of words that are no nodes: read, it is three high
/// digits for one comparison, and the root with them needs more nodes than it frees. The
/// late stage leaves it (and ends: it rewrites nothing).
#[cfg(feature = "prove")]
#[test]
fn limb_late_carries_do_not_grow() {
    let eng = deobfuscator();
    for (src, w) in [
        (
            "zext<32>(trunc<13>(x:32 * y:32) <u trunc<13>(z:32)) + v:32",
            32,
        ),
        (
            "zext<12>(trunc<20>(x:32 * y:32) <u trunc<20>(z:32 * v:32)) + u:12",
            12,
        ),
        (
            "zext<12>(trunc<20>(x:32 * y:32) <u trunc<20>(z:32)) + extract<20, 12>(z ^ v:32)",
            12,
        ),
    ] {
        let mut cx = Context::new();
        let e = cx
            .parse(src, &ParseOptions::width(Width::new(w).unwrap()))
            .unwrap();
        let before = dag(&mut cx, &[e]);
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(out.roots[0].end, End::Completed, "{src}");
        let after = dag(&mut cx, &[out.roots[0].expr]);
        assert!(
            after <= before,
            "{src}: {before} -> {after}: {}",
            cx.display(out.roots[0].expr)
        );
        assert_eq!(
            out.roots[0].expr, e,
            "{src}: the carry stays as it is written"
        );
    }
}

/// Limb arithmetic: sums of carries and terms their digits may or may not meet, under a
/// root that reads the sum with something else, stay equal to themselves: exhaustively.
/// (Such a sum is read in the late stage of the rounds, whatever terms it is left.)
#[cfg(feature = "prove")]
#[test]
fn limb_late_carries_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0031);
    let mut rng = Rng(97);
    let mut changed = 0;
    for i in 0..900 {
        let (w, syms): (u64, &[&str]) = if i % 3 == 0 {
            (4, &["a", "b", "c"])
        } else {
            (6, &["a", "b"])
        };
        let sym = |g: &mut Rng| format!("{}:{w}", syms[g.below(syms.len() as u64) as usize]);
        let value = |g: &mut Rng| {
            let (x, y) = (sym(g), sym(g));
            match g.below(5) {
                0 => format!("({x} + {y})"),
                1 => format!("({x} - {y})"),
                2 => format!("({x} * {})", g.below(1 << w)),
                3 => format!("({x} ^ {y})"),
                _ => x,
            }
        };
        let k = 1 + g.below(w - 1);
        let mask = (1u64 << k) - 1;
        // One carry or two, of sides that are related or not, and a term that is a high
        // digit of one of the words, of another value, or none.
        let mut s = String::new();
        let mut words = Vec::new();
        for _ in 0..1 + g.below(2) {
            let p = value(&mut g);
            let q = if g.chance(1, 2) {
                value(&mut g)
            } else {
                format!("({p} + {})", value(&mut g))
            };
            let sign = if g.chance(1, 3) { '-' } else { '+' };
            s += &format!(" {sign} zext<{w}>(({p} & {mask}) <u ({q} & {mask}))");
            words.extend([p, q]);
        }
        let own = match g.below(4) {
            0 => format!("({} >>u {k})", words[g.below(words.len() as u64) as usize]),
            1 => format!("({} >>u {k})", value(&mut g)),
            2 => value(&mut g),
            _ => "0".to_string(),
        };
        let s = format!("({own}{s})");
        let j = 1 + g.below(w - k);
        let low = format!("zext<{w}>(trunc<{j}>({s}))");
        let v = value(&mut g);
        let src = match g.below(5) {
            0 => low,
            1 => format!("{low} * {v}"),
            2 => format!("{low} ^ ({} >>u {k})", words[0]),
            3 => format!("({low} << {k}) | ({} & {mask})", words[0]),
            _ => format!("select(t:1, {low}, {v})"),
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 300, "{changed}");
}

/// Low digits a handler computes apart from the word.
#[cfg(feature = "prove")]
#[test]
fn limb_anchor_fixtures() {
    let eng = deobfuscator();
    for (src, want) in [
        // The low digit at its own width, the multiplier reduced to it (0x2d4b1 is 177 modulo
        // 2^9): the word is the one the high digit is of.
        (
            "let %0 = (x:32 ^ y:32) * 0x2d4b1; \
             let %1 = (trunc<9>(x) ^ trunc<9>(y)) * 177; \
             zext<9>(%1 + 301 <u %1) + extract<9, 9>(%0)",
            "extract<9, 9>((x ^ y) * 0x2d4b1 + 301)",
        ),
        // The high digit of `-(b - a)`: the borrow of a negation is `low != 0`.
        (
            "let %0 = b:32 - a:32; let %1 = a - b & 4095; let %2 = a - b + c:32 & 4095; \
             trunc<20>(%2 | (c >>u 12) - (%0 >>u 12) - zext<32>(%1 != 0) + zext<32>(%2 <u %1) << 12)",
            "trunc<20>(a - b + c)",
        ),
        // A carry out of a middle digit: a constant added limb by limb, the digit of the
        // constant (868 of 0xd9345) added to the word's own.
        (
            "zext<12>(extract<10, 10>(x:32 + 837) - 156 <u extract<10, 10>(x)) \
             + extract<20, 12>(x)",
            "extract<20, 12>(x + 0xd9345)",
        ),
        // Not where the digit of the difference may be all ones (the carry into the digit
        // then makes the two equal): the comparison stays, the constant beside its slice
        // taken into the slice's sum.
        (
            "zext<12>(extract<10, 10>(x:32 + 837) - 1 <u extract<10, 10>(x)) \
             + extract<20, 12>(x)",
            "zext<12>(extract<10, 10>(x + 0xfff45) <u extract<10, 10>(x)) + extract<20, 12>(x)",
        ),
        // The middle limb of `x - y`, a 64-bit word in limbs of 26 bits, its low limb
        // computed in a 32-bit register: the digits are the 64-bit word's.
        (
            "let %4 = -trunc<32>(y:64); let %5 = %4 & 0x3ffffff; let %11 = %4 + trunc<32>(x:64); \
             zext<32>(trunc<26>(-zext<32>(%5 != 0) + (-extract<26, 32>(y) + extract<26, 32>(x)) \
             + zext<32>(%11 & 0x3ffffff <u %5)))",
            "zext<32>(extract<26, 26>(x - y))",
        ),
        // The high limb of `(a ^ b) ^ c` written `x + c - 2·(x & c)`, the AND's digit read
        // one bit lower and of a slice of `a ^ b` where the borrow's own digit is of the
        // slices of `a` and `b`: one value, and it cancels.
        (
            "let %0 = a:32 ^ b:32; \
             zext<32>(trunc<13>(zext<32>(extract<18, 13>(%0 + c:32)) \
             - (c >>u 17 & zext<32>(extract<17, 13>(%0))) \
             + sext<32>(%0 + c & 0x3ffff <u (%0 ^ c) & 0x3ffff)))",
            "zext<32>(extract<18, 13>(a ^ b ^ c))",
        ),
    ] {
        assert_eq!(simplify(&eng, src, 32), want, "{src}");
    }
}

/// `x <u y` as a VM's flags spell it.
#[cfg(feature = "prove")]
fn below(x: &str, y: &str) -> String {
    format!("~((-{x} + {y} == 0) | ({y} <u {x}))")
}

/// The high limb of the 32-bit symbols of `ops` XORed one handler at a time, each in limbs of
/// 25 and 7 bits: an XOR is written `x + o - 2·(x & o)`, the low limb at the full width and
/// masked, the high limb from the digits, the carry of the sum and the borrow of the
/// difference (comparisons of the low limbs), and the next handler reads `x >> 24` back from
/// the two limbs.
#[cfg(feature = "prove")]
fn xor_limbs(ops: &[&str]) -> String {
    let m = "0x1ffffff";
    let (a, b) = (ops[0], ops[1]);
    // The word so far, its low limb and its high limb (the low 7 bits of a 32-bit value).
    let mut lets = vec![
        format!("{a}:32 & {b}:32"),
        format!("{a} + {b}"),
        "-(%0 << 1) + %1".to_string(),
        format!("%1 & {m}"),
        format!("%2 & {m}"),
    ];
    lets.push(format!(
        "({a} >>u 25) + ({b} >>u 25) - (%0 >>u 24) + sext<32>({}) + zext<32>({})",
        below("%3", "%4"),
        below("%3", &format!("({a} & {m})"))
    ));
    let (mut word, mut low, mut high) = (2, 4, 5);
    for o in &ops[2..] {
        let at = lets.len();
        lets.push(format!("%{word} + {o}:32"));
        lets.push(format!("%{at} + (%{word} & {o}) * -2"));
        lets.push(format!("%{at} & {m}"));
        lets.push(format!("%{} & {m}", at + 1));
        lets.push(format!(
            "-({o} >>u 24 & trunc<32>((zext<64>(%{high}) << 1) + zext<64>(%{low} >>u 24))) \
             + (%{high} + ({o} >>u 25) + zext<32>({})) + sext<32>({})",
            below(&format!("%{}", at + 2), &format!("%{low}")),
            below(&format!("%{}", at + 2), &format!("%{}", at + 3))
        ));
        (word, low, high) = (at + 1, at + 3, at + 4);
    }
    let mut src = String::new();
    for (k, e) in lets.iter().enumerate() {
        src.push_str(&format!("let %{k} = {e}; "));
    }
    format!("{src}trunc<7>(%{high})")
}

/// Limb arithmetic as a VM's handlers write it: a limb is the slice of the word its handler
/// computes at the full width for the lowest limb.
#[cfg(feature = "prove")]
#[test]
fn limb_slice_fixtures() {
    let eng = deobfuscator();
    // The top limb of `(w + k) ^ c` in limbs of 12, 12 and 8 bits: `x = w + k` with its
    // carries, `x + c` with its own, `- 2·(x & c)` with its borrows.
    let three = format!(
        "let %0 = w:32 + 0x2c51a7e3; \
         let %1 = trunc<16>(%0 & 4095); \
         let %2 = (w >>u 12) + zext<32>(%1 <u trunc<16>(w & 4095)); \
         let %3 = %2 + 0x2c51a; \
         let %4 = trunc<16>(%3 & 4095); \
         let %5 = zext<8>(%4 <u trunc<16>((w >>u 12) & 4095)); \
         let %6 = w + 0x7e15514f; \
         let %7 = trunc<16>(%6 & 4095); \
         let %8 = %2 + zext<32>({c0}) + 0x7e154; \
         let %9 = trunc<16>(%8 & 4095); \
         let %10 = trunc<16>(%6 + (%0 & 0x51c3a96c) * -2 & 4095); \
         let %11 = trunc<16>(%8 - (trunc<32>((zext<64>(%3) << 1) \
         + zext<64>((%0 & 4095) >>u 11)) & 0xa3875) + sext<32>({b0}) & 4095); \
         %5 + trunc<8>(zext<64>(w >>u 24) + 125) + zext<8>({c1}) \
         - (((trunc<8>(w >>u 24) << 1) + (%5 << 1) + 88 | extract<11, 8>(%3 & 4095)) & 163) \
         + sext<8>({b1})",
        c0 = below("%7", "%1"),
        b0 = below("%7", "%10"),
        c1 = below("%9", "%4"),
        b1 = below("%9", "%11"),
    );
    for (src, w, want) in [
        // One handler after another: each high limb is a slice of that handler's word, and
        // the words are XORs once nothing reads their sums.
        (xor_limbs(&["a", "b", "c"]), 32, "extract<25, 7>(b ^ c ^ a)"),
        // Three limbs: the carry into the third is no comparison of two low digits, and the
        // limb is found as the slice of the word and proved. (The word, which the handler
        // spells `x + c - 2·(x & c)` with the constants folded, is the XOR with the constant.)
        (three, 32, "extract<24, 8>(w + 0x2c51a7e3 ^ 0x51c3a96c)"),
        // A digit that is no truncation of the sum's operand: a value below `2^k`, and a mask
        // under the sum.
        (
            "extract<8, 8>(a) + extract<8, 8>(b) + zext<8>((a + b & 255) <u (a & 255))".into(),
            16,
            "extract<8, 8>(a + b)",
        ),
        (
            "extract<8, 8>(a) + zext<8>((a + (b & 15) & 255) <u (b & 15))".into(),
            16,
            "extract<8, 8>((b & 15) + a)",
        ),
        // Two neighbouring slices of one bitwise value, the upper one pushed into it.
        (
            "concat(extract<8, 8>(a) | extract<8, 8>(b), trunc<8>(a | b))".into(),
            32,
            "trunc<16>(a | b)",
        ),
        // A slice doubled beside the bit below it is the slice one lower.
        (
            "extract<25, 7>(x) + extract<25, 7>(x) | zext<7>(extract<24, 1>(x))".into(),
            32,
            "extract<24, 7>(x)",
        ),
        // An XOR written as a sum whose parts something else reads.
        (
            "(x + y - 2 * (x & y)) * ((x + y) ^ (x & y))".into(),
            32,
            "(x ^ y) * (x + y ^ x & y)",
        ),
        // A limb held at the word's width: what of it is not known to be 0 is a slice of the
        // word (the carry's digit here is of `x`, not of the sum's operand `x & 0xffff`).
        (
            "let %0 = (x & 0xffff) + (y & 0xffff); \
             zext<32>(trunc<8>(%0) <u trunc<8>(x)) + ((x & 0xffff) >>u 8) + ((y & 0xffff) >>u 8)"
                .into(),
            32,
            "zext<32>(extract<8, 9>((y & 65535) + (x & 65535)))",
        ),
        // The high limb shifted into its word beside the low one: an XOR in limbs of 18 and
        // 14 bits, its low limb already an XOR, is the XOR.
        (
            "let %0 = (a ^ b) & 0x3ffff; \
             let %1 = a + b & 0x3ffff; \
             %0 | (zext<32>(%1 <u (a & 0x3ffff)) + (a >>u 18) + (b >>u 18) \
             - zext<32>(%1 <u %0) - ((a & b) >>u 17) << 18)"
                .into(),
            32,
            "a ^ b",
        ),
        // The sum of two digits carries: its high digit is not 0, and this is no slice of
        // `x` (it was taken for one). It is the high digit of `x` less that carry (read in
        // the late stage of the rounds: the sum gets no fewer terms).
        (
            "extract<14, 16>(x - zext<32>(a:14) - zext<32>(b:14)) \
             + zext<16>(trunc<14>(x) <u (a:14 + b:14))"
                .into(),
            32,
            "extract<14, 16>(x) - extract<14, 16>(zext<32>(a) + zext<32>(b))",
        ),
    ] {
        assert_eq!(simplify(&eng, &src, w), want, "{src}");
    }
    // A longer chain, with the MBA phase beside these passes: an XOR of more than three
    // values written as a sum is that phase's to recognize.
    #[cfg(feature = "mba")]
    {
        use crate::mba::{MbaConfig, MbaTrust, NormalFormSolver};
        let trust = MbaTrust::default().with_backend_certificates(false);
        let eng = Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default().with_trust(trust)))
            .mba_solver(std::sync::Arc::new(NormalFormSolver::default()))
            .build()
            .unwrap();
        assert_eq!(
            simplify(&eng, &xor_limbs(&["a", "b", "c", "d", "e"]), 32),
            "extract<25, 7>(b ^ c ^ a ^ d ^ e)"
        );
    }
}

/// Limbs whose word is no node: a handler that adds a constant adds it limb by limb, so the
/// node the low limb is masked from has only the constant's low digit; and a limb's raw sum
/// read wider than the limb holds the carry out of its register.
#[cfg(feature = "prove")]
#[test]
fn limb_made_word_fixtures() {
    let eng = deobfuscator();
    // `x * 12123 + 46789` in limbs of 9 and 7 bits (46789 is 91 above 197): the high limb is
    // its own digit of the product, the carry of the low limb's 197 and 91.
    let high = "(p >>u 9) + zext<16>((p + 197 & 0x1ff) <u 197) + 91";
    for (src, want) in [
        (
            format!("let p = x * 0x2f5b; trunc<7>({high})"),
            "extract<9, 7>(x * 12123 - 18747)",
        ),
        // Read one bit wider, the sum has the carry out of the 16 bits: a slice of the word
        // zero-extended.
        (
            format!("let p = x * 0x2f5b; trunc<8>({high})"),
            "extract<9, 8>(zext<32>(x * 12123) + 46789)",
        ),
        // The same of the sum of two words.
        (
            "trunc<8>((a >>u 9) + (b >>u 9) + zext<16>((a + b & 0x1ff) <u (a & 0x1ff)))".into(),
            "extract<9, 8>(zext<32>(a) + zext<32>(b))",
        ),
    ] {
        assert_eq!(simplify(&eng, &src, 16), want, "{src}");
    }
}

/// Limbs of a word plus a constant, the constant added limb by limb (sometimes with the wrong
/// low digit in the carry), read on any number of bits up to the register's: whatever word
/// they are read as a slice of, the result is equal at every assignment.
#[cfg(feature = "prove")]
#[test]
fn limb_made_words_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0020);
    let mut rng = Rng(90);
    let mut changed = 0;
    let w = 7u64;
    for _ in 0..400 {
        let word = match g.below(3) {
            0 => format!("(a:{w} * {})", g.below(1 << w) | 1),
            1 => format!("(a:{w} + b:{w})"),
            _ => format!("a:{w}"),
        };
        let k = 1 + g.below(w - 2);
        let mask = (1u64 << k) - 1;
        let c = g.below(1 << w);
        let (c0, c1) = (c & mask, c >> k);
        let seen = if g.chance(1, 4) {
            g.below(mask + 1)
        } else {
            c0
        };
        let j = 1 + g.below(w);
        let carry = format!("zext<{w}>((({word} + {c0}) & {mask}) <u {seen})");
        let src = format!("trunc<{j}>(({word} >>u {k}) + {carry} + {c1})");
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 200, "{changed}");
}

/// The top limb of `(w + k) ^ c` in limbs of 12, 12 and 8 bits over the word `w` (an
/// expression of 32 bits), as [`limb_slice_fixtures`] spells it.
#[cfg(feature = "prove")]
fn three_limbs(w: &str) -> String {
    format!(
        "let %20 = {w}; \
         let %0 = %20 + 0x2c51a7e3; \
         let %1 = trunc<16>(%0 & 4095); \
         let %2 = (%20 >>u 12) + zext<32>(%1 <u trunc<16>(%20 & 4095)); \
         let %3 = %2 + 0x2c51a; \
         let %4 = trunc<16>(%3 & 4095); \
         let %5 = zext<8>(%4 <u trunc<16>((%20 >>u 12) & 4095)); \
         let %6 = %20 + 0x7e15514f; \
         let %7 = trunc<16>(%6 & 4095); \
         let %8 = %2 + zext<32>({c0}) + 0x7e154; \
         let %9 = trunc<16>(%8 & 4095); \
         let %10 = trunc<16>(%6 + (%0 & 0x51c3a96c) * -2 & 4095); \
         let %11 = trunc<16>(%8 - (trunc<32>((zext<64>(%3) << 1) \
         + zext<64>((%0 & 4095) >>u 11)) & 0xa3875) + sext<32>({b0}) & 4095); \
         %5 + trunc<8>(zext<64>(%20 >>u 24) + 125) + zext<8>({c1}) \
         - (((trunc<8>(%20 >>u 24) << 1) + (%5 << 1) + 88 | extract<11, 8>(%3 & 4095)) & 163) \
         + sext<8>({b1})",
        c0 = below("%7", "%1"),
        b0 = below("%7", "%10"),
        c1 = below("%9", "%4"),
        b1 = below("%9", "%11"),
    )
}

/// A limb is read back whatever computes its handler's operand: over a product of two
/// variables as over a symbol (in a slice proof's copy the product is a fresh symbol).
#[cfg(feature = "prove")]
#[test]
fn limb_slice_proofs_take_products_for_symbols() {
    let eng = deobfuscator();
    let run = |src: &str| {
        let mut cx = Context::new();
        let e = cx.parse(src, &ParseOptions::width(Width::W8)).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(out.roots[0].end, End::Completed);
        cx.display(out.roots[0].expr).to_string()
    };
    assert_eq!(
        run(&three_limbs("w:32")),
        "extract<24, 8>(w + 0x2c51a7e3 ^ 0x51c3a96c)"
    );
    assert_eq!(
        run(&three_limbs("(a:32 * b:32)")),
        "extract<24, 8>(a * b + 0x2c51a7e3 ^ 0x51c3a96c)"
    );
}

/// A limb of two products by constants written digit by digit, joined to its word's low
/// limb: the proof's two sides are one sum over the slices of the operands once their sums
/// are written one way (the search alone does not decide it within the caps), and the limbs
/// are the word.
#[cfg(feature = "prove")]
#[test]
fn limb_products_in_digits_are_read_back() {
    let eng = deobfuscator();
    let (k1, k2, m) = ("0x511bff07", "0x2c51a7e3", "0x3ffff");
    let src = format!(
        "let %0 = a:32 * {k1}; let %1 = b:32 * {k2}; let %2 = %0 + %1; let %3 = %2 + c:32; \
         let %4 = extract<18, 14>((a & {m}) * {k1}) + trunc<14>((a >>u 18) * {k1}); \
         let %5 = extract<18, 14>((b & {m}) * {k2}) + trunc<14>((b >>u 18) * {k2}); \
         let %6 = %4 + %5 + zext<14>((%2 & {m}) <u (%0 & {m})) + extract<18, 14>(c) \
         + zext<14>((%3 & {m}) <u (c & {m})); \
         concat(%6, trunc<18>(%3))"
    );
    let mut cx = Context::new();
    let e = cx.parse(&src, &ParseOptions::width(Width::W32)).unwrap();
    let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
    assert_eq!(out.roots[0].end, End::Completed);
    assert!(equivalent(&mut cx, e, out.roots[0].expr, &mut Rng(81)));
    assert_eq!(
        cx.display(out.roots[0].expr).to_string(),
        "b * 0x2c51a7e3 + a * 0x511bff07 + c"
    );
}

/// Limb arithmetic: a word several limbs read stays one node for them all.
#[cfg(feature = "prove")]
#[test]
fn limb_word_fixtures() {
    let eng = deobfuscator();
    for (src, want) in [
        // Read under 7 bits and under 14: written once, under 14 (a copy for each reader, its
        // constants reduced to that reader's bits, is `x * 7 - 59` beside `x * -249 + 4933`).
        (
            "let %0 = x * 0x511bff07 + (y << 14) + (z << 20) + 0x764d9345; \
             trunc<8>((%0 & 127) * a + ((%0 & 16383) >>u 7) * b)",
            "let %0 = x * -249 + 4933;\n\
             trunc<8>(zext<32>(extract<7, 7>(%0)) * b + (%0 & 127) * a)",
        ),
        // The truncation of a sum reaches a value whose truncation something else reads: it
        // is used, where narrowing the value again would build its `select` a second time
        // (and the sum would stay 64 bits wide, no XOR).
        (
            "let %0 = select(c:1, p:64 >>u 32, q:64 >>u 32); \
             let %1 = trunc<32>(%0); \
             let %2 = a & %1; \
             trunc<32>(zext<64>(a) + %0) - (%2 + %2)",
            "extract<32, 32>(select(c, p, q)) ^ a",
        ),
        // A register read limb by limb, each limb through its own chain of `select`s, is the
        // limbs of the one chain over the registers.
        (
            "let %0 = select(c:1, a, select(d:1, b, e)); \
             (%0 >>u s) + zext<32>(select(c, trunc<16>(a & 16383), \
             select(d, trunc<16>(b & 16383), trunc<16>(e & 16383)))) \
             * select(c, a >>u 14, select(d, b >>u 14, e >>u 14))",
            "let %0 = select(c, a, select(d, b, e));\n\
             (%0 & 16383) * (%0 >>u 14) + (%0 >>u s)",
        ),
        // Without the chain over the registers: it is built, one for the two.
        (
            "zext<32>(select(c:1, trunc<16>(a & 16383), trunc<16>(b & 16383))) \
             * select(c, a >>u 14, b >>u 14)",
            "let %0 = select(c, a, b);\n\
             (%0 & 16383) * (%0 >>u 14)",
        ),
        // An arm that masks the low bits beside one that zero-extends as many: one value.
        (
            "select(c:1, x & 255, zext<32>(v:8)) + zext<32>(select(c, trunc<8>(x), v)) * z",
            "let %0 = zext<32>(select(c, trunc<8>(x), v));\n\
             %0 * z + %0",
        ),
        // A word XORed with itself shifted by a count taken from it, each part selected
        // apart: the arms are the same operations over one pair of words and the same slice
        // of both, so they are done once over the selected word.
        (
            "let %1 = trunc<32>(p:64); \
             let %2 = extract<32, 32>(q:64); \
             let %3 = select(c:1, %1, %2); \
             let %4 = %1 >>u concat(2:29, extract<29, 3>(p)); \
             let %5 = %2 >>u concat(2:29, extract<61, 3>(q)); \
             select(c, %4, %5) + %3 - (select(c, %4 & %1, %5 & %2) << 1)",
            "let %0 = select(c, trunc<32>(p), extract<32, 32>(q));\n\
             %0 >>u concat(2:29, extract<29, 3>(%0)) ^ %0",
        ),
        // A `select` that exists is used though the other arm's operation is shared (it costs
        // nothing: the shift is done once more, on it, and once less, on an arm).
        (
            "let %5 = b >>u 14; \
             let %6 = select(c:1, a >>u 14, %5); \
             -select(c, a, b) * %6 + %5",
            "let %0 = select(c, a, b);\n\
             -%0 * (%0 >>u 14) + (b >>u 14)",
        ),
        // A limb of a register whose half is selected whole elsewhere is that limb of the
        // half.
        (
            "zext<32>(select(c:1, extract<28, 4>(p:64), extract<60, 4>(q:64))) \
             * select(c, trunc<32>(p), extract<32, 32>(q))",
            "let %0 = select(c, trunc<32>(p), extract<32, 32>(q));\n\
             zext<32>(extract<28, 4>(%0)) * %0",
        ),
        // A slice across the seam of the words the arms of a `select` join: the limbs on
        // either side, and the low limbs nothing reads are gone.
        (
            "zext<32>(extract<22, 10>(select(c:1, concat(a:6, concat(b:11, x:15)), \
             select(d:1, concat(e:6, concat(f:11, y:15)), g))))",
            "zext<32>(select(c, concat(a, extract<7, 4>(b)), \
             select(d, concat(e, extract<7, 4>(f)), extract<22, 10>(g))))",
        ),
    ] {
        assert_eq!(simplify(&eng, src, 32), want, "{src}");
    }
}

/// Limb arithmetic: one word, however its readers spell it. A carry whose sides are another
/// spelling of the word the sum holds the high digit of (its constant reduced to the limb's
/// bits, or the product computed in digits) is read over that word; a carry under `~`; the
/// top limb of `v ^ (v >>u s)` written as that of `v`; a constant added to a slice; and two
/// sums below a root that are one word on the bits read of them.
#[cfg(feature = "prove")]
#[test]
fn limb_one_word_fixtures() {
    let eng = deobfuscator();
    for (src, w, want) in [
        // The low limb with the constant reduced to it, beside the word's high digit.
        (
            "zext<8>(trunc<8>(x:16 * 0x35 + 93) <u trunc<8>(x * 0x35)) \
             + extract<8, 8>(x * 0x6b35)",
            8,
            "extract<8, 8>(x * 27445 + 93)",
        ),
        // The low limb as a product in 6-bit digits of a 12-bit limb.
        (
            "let %0 = (x:16 & 0xfff) * 53 + (x & 63) * 2816; \
             zext<8>(trunc<8>(%0 + 93) <u trunc<8>(%0)) + extract<8, 8>(x * 0x6b35)",
            8,
            "extract<8, 8>(x * 27445 + 93)",
        ),
        // One side written over the word already, the other over its reduced spelling: the
        // difference is taken over the word.
        (
            "let %0 = (x:16 & 63) * 53; \
             zext<4>(trunc<6>(x * 0x6b35 + y:16 * 64 + 29) <u trunc<6>(%0)) \
             + extract<6, 4>(x * 0x6b35) - extract<6, 4>(y * 64 + 29)",
            4,
            "extract<6, 4>(x * 27445 + 29) - trunc<4>(y)",
        ),
        // The carry out of a middle limb under `~` (`a − ~c` is `a + c + 1`), and the
        // constant taken into the word.
        (
            "let %0 = x:16 * 0x6b35; \
             extract<12, 4>(%0) - ~zext<4>(extract<8, 4>(%0 + 0x35d) <u extract<8, 4>(%0))",
            4,
            "extract<12, 4>(x * 27445 + 4957)",
        ),
        // The top limb of a word XORed with itself shifted is the top limb of the word.
        (
            "((v:16 ^ (v >>u 9)) & 1023) * 0x6b35 + (v >>u 10) * 0xd400",
            16,
            "(v >>u 9 ^ v) * 27445",
        ),
        // A constant added to a slice of a sum is the sum's.
        (
            "extract<8, 8>(x:16 * 0x6b35 + 93) + 7",
            8,
            "extract<8, 8>(x * 27445 + 1885)",
        ),
        // Two readers, each with the constant reduced to its bits: one word.
        (
            "zext<8>(extract<4, 4>(x:16 * 0x35 + 5)) + extract<8, 8>(x * 0x6b35 + 5)",
            8,
            "let %0 = x * 27445 + 5;\n\
             zext<8>(extract<4, 4>(%0)) + extract<8, 8>(%0)",
        ),
        // The product in digits, read below its limb's top, beside the product of the word.
        (
            "let %0 = (x:16 & 0xfff) * 53 + (x & 63) * 2816; \
             zext<8>(extract<3, 5>(%0)) + extract<8, 8>(x * 0x6b35) * y:8",
            8,
            "let %0 = x * 27445;\n\
             extract<8, 8>(%0) * y + zext<8>(extract<3, 5>(%0))",
        ),
    ] {
        assert_eq!(simplify(&eng, src, w), want, "{src}");
    }
}

/// Limb arithmetic: two sums written over other words at the root in one step, where what
/// one is written as reads the other. `lo·K` is read on its low digit and is `lo·k0` there;
/// `x·k0 + lo·(k1 << s) + c` is read on two digits and is `lo·K + hi·(k0 << d) + c` there,
/// which reads `lo·K` on both: the second has to keep the first as it was, not as the first
/// is written for its own readers. Equal at every value of `x`.
#[cfg(feature = "prove")]
#[test]
fn limb_one_word_keeps_what_it_reads() {
    let eng = deobfuscator();
    let mut g = Rng(0x0b17_5eed);
    let mut rng = Rng(53);
    for i in 0..240 {
        let (w, d) = match i % 3 {
            0 => (8u64, 3u64),
            1 => (8, 2),
            _ => (12, 3 + g.below(2)),
        };
        let k0 = g.below(1 << d) | 1;
        let k1 = 1 + g.below(3);
        let c = g.below(1 << d);
        let s = d + 1;
        let lo = format!("(x:{w} & {})", (1u64 << d) - 1);
        let hi = format!("zext<{w}>(extract<{d}, {d}>(x))");
        let sum = format!("(x * {k0} + {lo} * {} + {c})", k1 << s);
        let wide = 2 * w;
        let src = format!(
            "zext<{w}>(extract<{d}, {d}>({sum})) ^ (zext<{w}>(trunc<{d}>({lo} * {})) << {d}) \
             ^ extract<{}, {w}>(zext<{wide}>({hi} * {}) + zext<{wide}>({lo} * {}) \
             + zext<{wide}>({lo} * {k0}))",
            k0 + (k1 << s),
            2 * d,
            k0 << d,
            k1 << s
        );
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
    }
}

/// Limb arithmetic: a product `x·k` in several spellings (its constant with other bits
/// above some bit, or two limbs each under a constant of its own), a carry between two of
/// them beside the high digit of a third, slices of them added and constants added to the
/// slices, and the limbs of `a ^ (a >>u s)` with the top one written over `a`: each stays
/// equal to itself at every assignment. The spellings agree on their low bits only, and
/// the top limbs only for a shift that clears them, so a reading that took one for another
/// on more bits would be caught.
#[cfg(feature = "prove")]
#[test]
fn limb_one_word_readings_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0031);
    let mut rng = Rng(97);
    let mut changed = 0;
    let w: u64 = 7;
    let mask = (1u64 << w) - 1;
    for i in 0..900 {
        let s = 1 + g.below(w - 1);
        let x = match g.below(3) {
            0 => "a:7".to_string(),
            1 => format!("(a:7 ^ (a >>u {s}))"),
            _ => "(a:7 + b:7)".to_string(),
        };
        let k = g.below(1 << w) | 1;
        // `x·k` right on its low `m` bits: other bits above them in the constant, and the
        // product as it is or in two limbs.
        let spell = |g: &mut Rng, m: u64| {
            let other = (k ^ (g.below(1 << w) << m)) & mask;
            let h = m.div_ceil(2);
            if m < 2 || g.chance(1, 2) {
                format!("({x} * {other})")
            } else {
                let (lo, hi) = (other & ((1 << h) - 1), other >> h << h);
                format!(
                    "(({x} & {}) * {lo} + ({x} & {}) * {hi})",
                    (1u64 << m) - 1,
                    (1u64 << h) - 1
                )
            }
        };
        let (src, j) = match i % 3 {
            // A carry between two spellings beside the high digit of the word.
            0 => {
                let at = 1 + g.below(w - 2);
                let j = 1 + g.below(w - at);
                let word = spell(&mut g, w);
                let m = at + g.below(w - at + 1);
                let q = spell(&mut g, m);
                let d = if g.chance(1, 2) {
                    format!("{}:7", g.below(1 << w))
                } else {
                    "b:7".to_string()
                };
                let p = match g.below(3) {
                    0 => format!("({q} + {d})"),
                    1 => format!("({word} + {d})"),
                    _ => format!("({} + {d})", spell(&mut g, at)),
                };
                let (x, y) = if at > 1 && g.chance(1, 3) {
                    let o = 1 + g.below(at - 1);
                    let side = |v: &str| format!("extract<{o}, {}>({v})", at - o);
                    (side(&p), side(&q))
                } else {
                    (format!("trunc<{at}>({p})"), format!("trunc<{at}>({q})"))
                };
                let (x, y) = if g.chance(1, 4) { (y, x) } else { (x, y) };
                let high = |v: &str| format!("extract<{at}, {j}>({v})");
                let carry = match g.below(4) {
                    0 => format!("- ~zext<{j}>({x} <u {y})"),
                    1 => format!("+ sext<{j}>({x} <u {y})"),
                    _ => format!("+ zext<{j}>({x} <u {y})"),
                };
                let sign = if g.chance(1, 4) { '-' } else { '+' };
                let mut src = format!("{} {carry}", high(&word));
                if g.chance(1, 3) {
                    src.push_str(&format!(" {sign} {}", high(&d)));
                }
                if g.chance(1, 3) {
                    src.push_str(&format!(" + {}", g.below(1 << j)));
                }
                (src, j)
            }
            // Slices of two spellings, a constant added to each word and to each slice.
            1 => {
                let slice = |g: &mut Rng| {
                    let lo = 1 + g.below(w - 2);
                    let n = 1 + g.below(w - lo);
                    let v = spell(g, lo + n);
                    let c = g.below(1 << w);
                    let e = format!("zext<7>(extract<{lo}, {n}>({v} + {c}))");
                    if g.chance(1, 2) {
                        format!("({e} + {})", g.below(1 << n))
                    } else {
                        e
                    }
                };
                let (t, u) = (slice(&mut g), slice(&mut g));
                let src = match g.below(3) {
                    0 => format!("{t} + {u}"),
                    1 => format!("{t} * b:7 + {u}"),
                    _ => format!("{t} + ({} >>u {})", spell(&mut g, w), g.below(w)),
                };
                (src, w)
            }
            // The limbs of `a ^ (a >>u s)`, the top one written over `a`: the word only
            // where the shift clears the top limb.
            _ => {
                let m = 1 + g.below(w - 1);
                let top = (k << m) & mask;
                let src = format!(
                    "((a:7 ^ (a >>u {s})) & {}) * {k} + (a >>u {m}) * {top} + b:7",
                    (1u64 << m) - 1
                );
                (src, w)
            }
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(j as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 300, "{changed}");
}

/// Limb arithmetic: the step `T ^ (T << s)` in limbs, and one word in several spellings. The
/// low limb of `T << s` is written `(T & 1) << s` and the carry of `T + (T << s)` compares
/// with it: read over `T << s`, whose digit the sum holds in two pieces of `T`. The same
/// with a piece cut from the word at another width, its constant reduced to the limb's
/// bits; the high limb of a product written over the slices of the operands of an `^`; and
/// the borrow of an XOR whose operand is a truncated product.
#[cfg(feature = "prove")]
#[test]
fn limb_shifted_word_fixtures() {
    let eng = deobfuscator();
    for (src, w, want) in [
        // The high limb of `T + (T << 5) − 2·(T & (T << 5))` at 6 + 10 bits.
        (
            "let %0 = x:16 * 0x6b35; \
             zext<10>(extract<1, 5>(%0)) + extract<6, 10>(%0) * 33 \
             + zext<10>(trunc<6>(%0 + (%0 << 5)) <u trunc<6>((%0 & 1) << 5)) \
             - trunc<10>(%0 & (%0 >>u 5))",
            10,
            "let %0 = x * 27445;\n\
             extract<6, 10>(%0 + (%0 << 5)) - trunc<10>(%0 & %0 >>u 5)",
        ),
        // The piece below the limb's top cut from a 32-bit product over the sign extension.
        (
            "let %0 = x:16 * 0x6b35 + 9; \
             zext<10>(extract<1, 5>(sext<32>(x) * 53 + 9)) + extract<6, 10>(%0) * 33 \
             + zext<10>(trunc<6>(%0 + (%0 << 5)) <u trunc<6>((%0 & 1) << 5)) \
             - trunc<10>(%0 & (%0 >>u 5))",
            10,
            "let %0 = x * 27445 + 9;\n\
             extract<6, 10>(%0 + (%0 << 5)) - trunc<10>(%0 & %0 >>u 5)",
        ),
        // The high limb of `a ^ b` written over the slices of `a` and `b`.
        (
            "zext<16>(extract<6, 10>(a:16) ^ extract<6, 10>(b:16)) * 0xcd40 \
             + ((a ^ b) & 63) * 0x6b35",
            16,
            "(a ^ b) * 27445",
        ),
        // The carry and the borrow of an XOR in limbs, one operand a truncated product.
        (
            "let %0 = trunc<16>(y:32 * 0x12345); \
             extract<6, 10>(%0) + extract<6, 10>(b:16) - extract<5, 10>(%0 & b) \
             + zext<10>(trunc<6>(%0 + b) <u trunc<6>(%0)) \
             - zext<10>(trunc<6>(%0 + b) <u trunc<6>(%0 ^ b))",
            10,
            "extract<6, 10>(trunc<16>(y * 0x12345) ^ b)",
        ),
    ] {
        assert_eq!(simplify(&eng, src, w), want, "{src}");
    }
}

/// Limb arithmetic: the readings of a word shifted left and of one word at several widths
/// stay equal to their inputs at every assignment. A carry whose side is `(T & m) << s`,
/// with masks that have the digit's bits and masks that lack one (the side is then no
/// digit of `T << s`); pieces of `T` cut from a wider product whose constants agree with
/// the word's on some low bits only; a bitwise function of two slices cut at the same and at
/// different bits beside the function of the words; and the carries of an XOR and an OR in
/// limbs over a truncated product.
#[cfg(feature = "prove")]
#[test]
fn limb_shifted_word_readings_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x5eed_0b17);
    let mut rng = Rng(131);
    let mut changed = 0;
    let w: u64 = 7;
    let mask = (1u64 << w) - 1;
    for i in 0..800 {
        let k = g.below(1 << w) | 1;
        let c = g.below(1 << w);
        let t = match g.below(3) {
            0 => "a:7".to_string(),
            1 => format!("(a:7 * {k} + {c})"),
            _ => "(a:7 + b:7)".to_string(),
        };
        let at = 2 + g.below(w - 3);
        let j = w - at;
        let (src, bits) = match i % 4 {
            // The carry of `T + (T << s)` against the masked low digit of `T << s`.
            0 => {
                let s = 1 + g.below(at - 1);
                let digit = (1u64 << (at - s)) - 1;
                let m = match g.below(4) {
                    0 => digit,
                    1 => digit | (g.below(1 << w) << (at - s)) & mask,
                    2 => digit & !(1 << g.below(at - s)),
                    _ => g.below(1 << w),
                };
                let d = match g.below(3) {
                    0 => String::new(),
                    1 => format!(" + {}", g.below(1 << w)),
                    _ => " + b:7".to_string(),
                };
                let carry = format!(
                    "zext<{j}>(trunc<{at}>({t} + ({t} << {s}){d}) <u trunc<{at}>(({t} & {m}) << {s}))"
                );
                let n = s.min(j);
                let mut src = format!(
                    "zext<{j}>(extract<{}, {n}>({t})) + extract<{at}, {j}>({t}) * {} + {carry}",
                    at - s,
                    (1 + (1u64 << s)) & ((1 << j) - 1)
                );
                if g.chance(1, 2) {
                    src.push_str(&format!(" - trunc<{j}>({t} & ({t} >>u {s}))"));
                }
                (src, j)
            }
            // Pieces of one word at two widths: a wider product right on `m` low bits.
            1 => {
                let m = 1 + g.below(w);
                let high = |g: &mut Rng, v: u64| (v ^ (g.below(1 << 5) << m)) & 0xfff;
                let (kw, cw) = (high(&mut g, k), high(&mut g, c));
                let ext = if g.chance(1, 2) { "sext" } else { "zext" };
                let wide = format!("({ext}<12>(a:7) * {kw} + {cw})");
                let word = format!("(a:7 * {k} + {c})");
                let lo = g.below(at);
                let carry = format!(
                    "zext<{j}>(trunc<{at}>({word} + b:7) <u trunc<{at}>({}))",
                    if g.chance(1, 2) { &wide } else { &word }
                );
                let src = format!(
                    "extract<{at}, {j}>({word}) + {carry} \
                     + zext<{j}>(extract<{lo}, {}>({wide})) * {} - zext<{j}>(extract<{lo}, {}>({word}))",
                    (at - lo).min(j),
                    1 + g.below(3),
                    (at - lo).min(j)
                );
                (src, j)
            }
            // A bitwise function of two slices beside the function of the words.
            2 => {
                let op = ["^", "|", "&"][g.below(3) as usize];
                let lo = at + g.below(2) - g.below(2);
                let n = j - 1;
                let src = format!(
                    "zext<7>(extract<{at}, {n}>(a:7) {op} extract<{lo}, {n}>(b:7)) * {} \
                     + ((a {op} b) & {}) * {k} + {c}",
                    (k << at) & mask,
                    (1u64 << at) - 1
                );
                (src, w)
            }
            // The carry and the borrow of an XOR or an OR in limbs over a truncated product.
            _ => {
                let p = format!("trunc<7>(zext<10>(a:7) * {})", k | (g.below(8) << w));
                let (f, and, by) = if g.chance(1, 2) {
                    ("^", format!("extract<{}, {j}>({p} & b:7)", at - 1), 1)
                } else {
                    ("|", format!("extract<{at}, {j}>({p} & b:7)"), 0)
                };
                let q = if g.chance(1, 4) {
                    "b:7".to_string()
                } else {
                    p.clone()
                };
                let src = format!(
                    "extract<{at}, {j}>({p}) + extract<{at}, {j}>(b:7) - {and} \
                     + zext<{j}>(trunc<{at}>({p} + b) <u trunc<{at}>({q})) \
                     - zext<{j}>(trunc<{at}>({p} + b) <u trunc<{at}>({p} {f} b)) + {}",
                    g.below(2) * by
                );
                (src, j)
            }
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(bits as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = eng.simplify(&mut cx, e).unwrap();
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 400, "{changed}");
}

/// Limb arithmetic: sums of high digits and of carries written as comparisons of low digits,
/// each digit spelled every way the borrows pass reads one (a truncation, a mask, either under
/// a narrower truncation or a zero extension, a narrowed sum, a value that is small), stay
/// equal to themselves: exhaustively, at widths where a digit's reading can go wrong (a
/// narrowed sum that carries, a digit read at more bits than it has).
#[cfg(feature = "prove")]
#[test]
fn limb_carries_are_sound() {
    let eng = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let mut g = Rng(0x11b5_0001);
    let mut rng = Rng(77);
    let mut changed = 0;
    for i in 0..900 {
        // Two symbols of 7 bits, or three of 4: every assignment is checked.
        let (w, syms): (u64, &[&str]) = if i % 3 == 0 {
            (4, &["a", "b", "c"])
        } else {
            (7, &["a", "b"])
        };
        let sym = |g: &mut Rng| format!("{}:{w}", syms[g.below(syms.len() as u64) as usize]);
        // In a third of the cases every value has high bits known zero: their sums do not
        // wrap, and a carry is read at any width.
        let bounded = g.chance(1, 3);
        let value = |g: &mut Rng| {
            let (x, y) = (sym(g), sym(g));
            let c = g.below(1 << w);
            let v = match g.below(9) {
                0 => x,
                1 => format!("({x} + {y})"),
                2 => format!("({x} - {y})"),
                3 => format!("({x} + {c})"),
                4 => format!("({x} ^ {y})"),
                5 => format!("({x} & {y})"),
                6 => format!("({x} * {c})"),
                7 => format!("({x} >>u {})", g.below(w)),
                _ => format!("({x} + ({y} << {}))", g.below(w)),
            };
            match g.below(2) {
                _ if !bounded => v,
                0 => format!("({v} >>u {})", 1 + g.below(w - 1)),
                _ => format!("({v} & {})", g.below(1 << (w - 1))),
            }
        };
        let k = 1 + g.below(w - 1);
        let mask = (1u64 << k) - 1;
        // `Q`, and with a narrowed side its low `k` bits as a sum of `k`-bit values (the
        // truncation pushed into `Q`, slices of other values beside it).
        let narrow = g.chance(1, 4);
        let (q, narrowed) = if narrow {
            let leaf = |g: &mut Rng| {
                let v = value(g);
                if g.chance(1, 2) {
                    (format!("trunc<{k}>({v})"), v)
                } else {
                    let n = format!("extract<{}, {k}>({v})", g.below(w - k + 1));
                    (n.clone(), format!("zext<{w}>({n})"))
                }
            };
            let ((n1, v1), (n2, v2)) = (leaf(&mut g), leaf(&mut g));
            let op = ["+", "-", "^"][g.below(3) as usize];
            (format!("({v1} {op} {v2})"), format!("({n1} {op} {n2})"))
        } else {
            (value(&mut g), String::new())
        };
        // `P = Q + D`, or unrelated values.
        let d = value(&mut g);
        let p = if g.chance(2, 3) {
            format!("({q} + {d})")
        } else {
            value(&mut g)
        };
        // The comparison's width, and a side: the low `k` bits of `v` there.
        let m = match g.below(3) {
            _ if narrow => k,
            0 => k,
            1 => w,
            _ => k + g.below(w - k + 1),
        };
        let digit = |g: &mut Rng, v: &str| {
            let small = 1 + g.below(k);
            match g.below(5) {
                // A value below `2^k`, which is its own low digit.
                0 => format!("zext<{m}>(trunc<{small}>({v}))"),
                1 if m == w => format!("({v} & {mask})"),
                2 if m > k => format!("(trunc<{m}>({v}) & {mask})"),
                3 if m < w => format!("trunc<{m}>({v} & {mask})"),
                _ => format!("zext<{m}>(trunc<{k}>({v}))"),
            }
        };
        // The sum's width, and a high digit there.
        let j = match g.below(3) {
            0 => w - k,
            1 => w,
            _ => 1 + g.below(w),
        };
        let high = |v: &str| {
            if j == w {
                format!("({v} >>u {k})")
            } else if k + j <= w {
                format!("extract<{k}, {j}>({v})")
            } else {
                format!("trunc<{j}>({v} >>u {k})")
            }
        };
        let mut src = String::new();
        let mut term = |g: &mut Rng, t: String| {
            let sign = if g.chance(1, 4) { '-' } else { '+' };
            src.push_str(&format!(" {sign} {t}"));
        };
        let ext = if g.chance(1, 4) { "sext" } else { "zext" };
        let x = digit(&mut g, &p);
        let y = if narrow { narrowed } else { digit(&mut g, &q) };
        let (x, y) = if g.chance(1, 4) { (y, x) } else { (x, y) };
        term(&mut g, format!("{ext}<{j}>({x} <u {y})"));
        for v in [p.clone(), q.clone(), d.clone(), format!("({p} - {q})")] {
            if g.chance(1, 2) {
                term(&mut g, high(&v));
            }
        }
        if g.chance(1, 3) {
            let (x, y) = (digit(&mut g, &q), digit(&mut g, &d));
            term(&mut g, format!("zext<{j}>({x} <u {y})"));
        }
        if g.chance(1, 3) {
            let v = value(&mut g);
            term(&mut g, format!("trunc<{j}>({v})"));
        }
        let src = format!("0:{j}{src}");
        let src = match g.below(3) {
            0 => src,
            1 => format!("trunc<{}>({src})", 1 + g.below(j)),
            _ => format!("({src}) & {}", g.below(1 << j)),
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 600, "{changed}");
}

/// Carries of digits computed in a register narrower than the word: the low digits from
/// truncations of 7-bit values to 4 or 5 bits, the sum's high digits slices of the values
/// themselves that reach past the register's width, the sum read on more bits than the
/// register has above the digit. Checked at every assignment.
#[cfg(feature = "prove")]
#[test]
fn limb_lifted_digits_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0005);
    let mut rng = Rng(81);
    let mut changed = 0;
    for _ in 0..700 {
        let w = 7u64;
        let reg = 4 + g.below(2);
        let k = 1 + g.below(reg - 1);
        let mask = (1u64 << k) - 1;
        let sym = |g: &mut Rng| ["a:7", "b:7"][g.below(2) as usize].to_string();
        let value = |g: &mut Rng| {
            let (x, y) = (sym(g), sym(g));
            let c = g.below(1 << w);
            match g.below(6) {
                0 | 1 => x,
                2 => format!("({x} + {y})"),
                3 => format!("({x} - {y})"),
                4 => format!("({x} ^ {c})"),
                _ => format!("({x} + {c})"),
            }
        };
        // A register's value and the word it is the low bits of.
        let low = |g: &mut Rng, v: &str| match g.below(3) {
            0 => (format!("trunc<{reg}>({v})"), v.to_string()),
            1 => (format!("-trunc<{reg}>({v})"), format!("-({v})")),
            _ => {
                let u = value(g);
                (
                    format!("(trunc<{reg}>({v}) + trunc<{reg}>({u}))"),
                    format!("({v} + {u})"),
                )
            }
        };
        let v = value(&mut g);
        let (qr, q) = low(&mut g, &v);
        let v = value(&mut g);
        let (dr, d) = low(&mut g, &v);
        let (pr, p) = if g.chance(3, 4) {
            (format!("({qr} + {dr})"), format!("({q} + {d})"))
        } else {
            let v = value(&mut g);
            low(&mut g, &v)
        };
        // The sum's width (the digits reach past the register), and what is read of it.
        let m = (reg - k + 1 + g.below(w - reg)).min(w - k);
        let j = 1 + g.below(m);
        let high = |v: &str| format!("extract<{k}, {m}>({v})");
        let mut src = String::new();
        let mut term = |g: &mut Rng, t: String| {
            let sign = if g.chance(1, 4) { '-' } else { '+' };
            src.push_str(&format!(" {sign} {t}"));
        };
        let carry = if g.chance(1, 5) {
            format!("zext<{m}>(({qr} & {mask}) != 0)")
        } else {
            format!("zext<{m}>(({pr} & {mask}) <u ({qr} & {mask}))")
        };
        term(&mut g, carry);
        for v in [p.clone(), q.clone(), d.clone()] {
            if g.chance(3, 4) {
                term(&mut g, high(&v));
            }
        }
        let src = format!("trunc<{j}>(0:{m}{src})");
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 350, "{changed}");
}

/// The reading of a carry by the sum of its sides with its carry out, at every assignment:
/// with `P = Q + D` of `W` bits and `S = zext(Q) + zext(D)` at `W' > W` bits, `lo_k(P) <u
/// lo_k(Q)` is `hi_k(S) − hi_k(Q) − hi_k(D)` on any `j` bits, every digit zero-extended. A
/// borrow against that word, `lo_k(P) <u lo_k(Q ^ D)` (or `Q | D`), is `hi_k(S) − hi_k(Q ^
/// D) − hi_k(2·zext(Q & D))` (or of `zext(Q & D)`) modulo `2^j` where `W' ≥ k + j`.
#[cfg(feature = "prove")]
#[test]
fn limb_wide_carry_identity() {
    let mut rng = Rng(91);
    for w in 2..=6u64 {
        for k in 1..w {
            for j in 1..=9u64 {
                let mask = (1u64 << k) - 1;
                // Digits of the values themselves, zero-extended to `j` bits.
                let high = |v: &str| {
                    let digit = format!("extract<{k}, {}>({v})", w - k);
                    match j.cmp(&(w - k)) {
                        core::cmp::Ordering::Less => format!("trunc<{j}>({digit})"),
                        core::cmp::Ordering::Equal => digit,
                        core::cmp::Ordering::Greater => format!("zext<{j}>({digit})"),
                    }
                };
                for wide in [w + 1, k + j, 2 * w] {
                    if wide <= w {
                        continue;
                    }
                    // A digit of a `wide`-bit value at `j` bits.
                    let digit = |v: &str| {
                        if k + j <= wide {
                            format!("extract<{k}, {j}>({v})")
                        } else {
                            format!("zext<{j}>(extract<{k}, {}>({v}))", wide - k)
                        }
                    };
                    let (q, d) = (format!("q:{w}"), format!("d:{w}"));
                    let s = format!("(zext<{wide}>({q}) + zext<{wide}>({d}))");
                    let mut pairs = vec![(
                        format!("zext<{j}>(({q} + {d} & {mask}) <u ({q} & {mask}))"),
                        format!("{} - {} - {}", digit(&s), high(&q), high(&d)),
                    )];
                    if wide >= k + j {
                        for (op, twice) in [("^", " * 2"), ("|", "")] {
                            let and = format!("(zext<{wide}>({q} & {d}){twice})");
                            pairs.push((
                                format!(
                                    "zext<{j}>(({q} + {d} & {mask}) <u (({q} {op} {d}) & {mask}))"
                                ),
                                format!(
                                    "{} - {} - {}",
                                    digit(&s),
                                    high(&format!("({q} {op} {d})")),
                                    digit(&and)
                                ),
                            ));
                        }
                    }
                    for (carry, reading) in pairs {
                        let mut cx = Context::new();
                        let opts = ParseOptions::width(Width::new(j as u16).unwrap());
                        let a = cx
                            .parse(&carry, &opts)
                            .unwrap_or_else(|e| panic!("{carry}: {e}"));
                        let b = cx
                            .parse(&reading, &opts)
                            .unwrap_or_else(|e| panic!("{reading}: {e}"));
                        assert!(equivalent(&mut cx, a, b, &mut rng), "{carry} vs {reading}");
                    }
                }
            }
        }
    }
}

/// A sum that reads more bits of a carry than its sides have above the digit: the carry is
/// read off the sum of the sides with its carry out.
#[cfg(feature = "prove")]
#[test]
fn limb_wide_carry_fixtures() {
    let eng = deobfuscator();
    // Two 16-bit registers added in limbs of 10 bits, the high sum kept at 16 bits: 7 bits
    // of the sum of the registers with its carry out.
    let high = "((x:16 >>u 10) + (y:16 >>u 10) + zext<16>((x + y & 1023) <u (x & 1023)))";
    // The high limb of `x ^ y` written `x + y − 2·(x & y)`: its carry and its borrow.
    let xor = "((x:16 >>u 10) + (y:16 >>u 10) - ((x & y) >>u 9) \
               + zext<16>((x + y & 1023) <u (x & 1023)) \
               - zext<16>((x + y & 1023) <u (x + y - (x & y) * 2 & 1023)))";
    for (src, w, want) in [
        (
            high.to_string(),
            16,
            "extract<10, 16>(zext<32>(x) + zext<32>(y))",
        ),
        // A mask later, of more bits than a register has above the limb.
        (
            format!("trunc<7>({high})"),
            16,
            "extract<10, 7>(zext<32>(x) + zext<32>(y))",
        ),
        // The limbs joined: the sum itself.
        (
            format!("(zext<32>({high}) << 10) | zext<32>(x + y & 1023)"),
            32,
            "zext<32>(x) + zext<32>(y)",
        ),
        // The carry and the borrow of one word: the word goes, the limb stays.
        (xor.to_string(), 16, "zext<16>(extract<10, 6>(x ^ y))"),
        // A constant added in limbs of 14 and 18 bits, the high sum read on 19.
        (
            "trunc<19>((x:32 * 77 >>u 14) + zext<32>((x * 77 + 567 & 16383) <u 567))".to_string(),
            32,
            "extract<14, 19>(zext<64>(x * 77) + 567)",
        ),
    ] {
        assert_eq!(simplify(&eng, &src, w), want, "{src}");
    }
}

/// Sums that read a carry on more bits than its sides have above the digit, checked at every
/// assignment: the high digits of two registers and the carry between them at up to twice
/// the registers' width, with the borrow of an XOR or OR written as a sum and its and-term,
/// a second carry out of the same or another word, read whole, truncated or masked.
#[cfg(feature = "prove")]
#[test]
fn limb_wide_carries_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0021);
    let mut rng = Rng(92);
    let mut changed = 0;
    for i in 0..700 {
        let (w, syms): (u64, &[&str]) = if i % 3 == 0 {
            (4, &["a", "b", "c"])
        } else {
            (7, &["a", "b"])
        };
        let sym = |g: &mut Rng| format!("{}:{w}", syms[g.below(syms.len() as u64) as usize]);
        let value = |g: &mut Rng| {
            let (x, y) = (sym(g), sym(g));
            let c = g.below(1 << w);
            match g.below(7) {
                0..=2 => x,
                3 => format!("({x} ^ {y})"),
                4 => format!("({x} + {c})"),
                5 => format!("({x} * {c})"),
                _ => format!("{c}:{w}"),
            }
        };
        let k = 1 + g.below(w - 1);
        let mask = (1u64 << k) - 1;
        // The sum's width: more than the registers have above the digit.
        let m = w - k + 1 + g.below(w + k);
        let high = |v: &str| {
            if m <= w - k {
                format!("extract<{k}, {m}>({v})")
            } else {
                format!("zext<{m}>(extract<{k}, {}>({v}))", w - k)
            }
        };
        let (q, d) = (value(&mut g), value(&mut g));
        let p = format!("({q} + {d})");
        let mut src = String::new();
        // (`often`: in how many cases of four the term is there.)
        let mut term = |g: &mut Rng, t: String, often: u64| {
            if g.chance(often, 4) {
                let sign = if g.chance(1, 6) { '-' } else { '+' };
                src.push_str(&format!(" {sign} {t}"));
            }
        };
        term(&mut g, high(&q), 3);
        term(&mut g, high(&d), 3);
        term(
            &mut g,
            format!("zext<{m}>(({p} & {mask}) <u ({q} & {mask}))"),
            4,
        );
        // The borrow of `q ^ d` or `q | d` out of the same word, and its and-term.
        if g.chance(1, 2) {
            let (r, and) = match g.below(4) {
                0 => (format!("({p} - ({q} & {d}) * 2)"), 1),
                1 => (format!("({q} ^ {d})"), 1),
                2 => (format!("({p} - ({q} & {d}))"), 0),
                _ => (format!("({q} | {d})"), 0),
            };
            let ext = if g.chance(3, 4) { "sext" } else { "zext" };
            term(
                &mut g,
                format!("{ext}<{m}>(({p} & {mask}) <u ({r} & {mask}))"),
                4,
            );
            let digit = format!("extract<{}, {}>({q} & {d})", k - and, w - k + and);
            let digit = if m == w - k + and {
                digit
            } else {
                format!("zext<{m}>({digit})")
            };
            term(&mut g, format!("(0:{m} - {digit})"), 3);
            // The next handler's carry, out of the word made of this one's result.
            if g.chance(1, 2) {
                let e = value(&mut g);
                term(&mut g, high(&e), 3);
                term(
                    &mut g,
                    format!("zext<{m}>(({r} + {e} & {mask}) <u ({e} & {mask}))"),
                    4,
                );
            }
        } else if g.chance(1, 3) {
            // Another comparison of the same word, against anything.
            let v = value(&mut g);
            term(
                &mut g,
                format!("zext<{m}>(({p} & {mask}) <u ({v} & {mask}))"),
                4,
            );
        }
        let src = format!("0:{m}{src}");
        let src = match g.below(4) {
            0 | 1 => src,
            2 => format!("trunc<{}>({src})", 1 + g.below(m)),
            _ => format!("({src}) & {}", g.below(1 << m.min(16))),
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 350, "{changed}");
}

/// Carries of middle digits: comparisons of one slice from above bit 0 of two values, a
/// constant added to either, in sums with the high digits above them, checked at every
/// assignment. The reading holds only where the difference's digit is not all ones, so half
/// the differences are constants and the rest any value.
#[cfg(feature = "prove")]
#[test]
fn limb_middle_digits_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0004);
    let mut rng = Rng(80);
    let mut changed = 0;
    for i in 0..900 {
        let (w, syms): (u64, &[&str]) = if i % 3 == 0 {
            (5, &["a", "b"])
        } else {
            (7, &["a", "b"])
        };
        let sym = |g: &mut Rng| format!("{}:{w}", syms[g.below(syms.len() as u64) as usize]);
        let value = |g: &mut Rng| {
            let (x, y) = (sym(g), sym(g));
            let c = g.below(1 << w);
            match g.below(7) {
                0 | 1 => x,
                2 => format!("({x} + {y})"),
                3 => format!("({x} ^ {y})"),
                4 => format!("({x} * {c})"),
                5 => format!("({x} & {c})"),
                _ => format!("({x} + {c})"),
            }
        };
        // The digit `[o, o + n)`, with bits above it (or, one time in eight, none).
        let o = 1 + g.below(w - 2);
        let n = if g.chance(1, 8) {
            w - o
        } else {
            1 + g.below(w - o - 1)
        };
        let at = o + n;
        let q = value(&mut g);
        let d = if g.chance(1, 2) {
            format!("{}:{w}", g.below(1 << w))
        } else {
            value(&mut g)
        };
        let p = if g.chance(3, 4) {
            format!("({q} + {d})")
        } else {
            value(&mut g)
        };
        let side = |g: &mut Rng, v: &str| {
            let s = format!("extract<{o}, {n}>({v})");
            if g.chance(1, 3) {
                format!("({s} + {})", g.below(1 << n))
            } else {
                s
            }
        };
        let j = if at < w && g.chance(2, 3) {
            w - at
        } else {
            1 + g.below(w)
        };
        let high = |v: &str| {
            if at >= w {
                format!("trunc<{j}>({v})")
            } else if at + j <= w {
                format!("extract<{at}, {j}>({v})")
            } else {
                format!("zext<{j}>(extract<{at}, {}>({v}))", w - at)
            }
        };
        let mut src = String::new();
        let mut term = |g: &mut Rng, t: String| {
            let sign = if g.chance(1, 4) { '-' } else { '+' };
            src.push_str(&format!(" {sign} {t}"));
        };
        let ext = if g.chance(1, 4) { "sext" } else { "zext" };
        let (x, y) = (side(&mut g, &p), side(&mut g, &q));
        let (x, y) = if g.chance(1, 4) { (y, x) } else { (x, y) };
        term(&mut g, format!("{ext}<{j}>({x} <u {y})"));
        for v in [p.clone(), q.clone(), d.clone()] {
            if g.chance(2, 3) {
                term(&mut g, high(&v));
            }
        }
        let src = format!("0:{j}{src}");
        let src = match g.below(3) {
            0 => src,
            1 => format!("trunc<{}>({src})", 1 + g.below(j)),
            _ => format!("({src}) & {}", g.below(1 << j)),
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 450, "{changed}");
}

/// Limb arithmetic: a narrow value added into the middle of a wide one. The identity first,
/// at every offset and width in a 7-bit word and every assignment: the carry out of the
/// digit `[o, o + n)` of `a` plus an `n`-bit `t`, written against `t` or against the digit,
/// is the high digit of `a + (zext(t) << o)` less that of `a`, and the borrow of the digit
/// less `t` the high digit of `a` less that of `a − (zext(t) << o)`. Then generated sums:
/// such a comparison (a constant or other terms beside the slice, the sides swapped, a
/// subtraction, a term on one side only, a constant added to the word; the sides in a
/// register wider than the digit) with the high digits above the digit, simplified and
/// checked at every assignment.
#[cfg(feature = "prove")]
#[test]
fn limb_shifted_digits_are_sound() {
    let mut rng = Rng(91);
    let w = 7u64;
    for o in 1..w - 1 {
        for n in 1..w - o {
            let (at, j) = (o + n, w - o - n);
            let s = format!("extract<{o}, {n}>(a:{w})");
            let q = format!("(zext<{w}>(t:{n}) << {o})");
            let high = |v: &str| format!("extract<{at}, {j}>({v})");
            let carry = format!("{} - {}", high(&format!("(a:{w} + {q})")), high("a"));
            let borrow = format!("{} - {}", high("a"), high(&format!("(a:{w} - {q})")));
            for (test, digits) in [
                (format!("{s} + t:{n} <u t:{n}"), &carry),
                (format!("{s} + t:{n} <u {s}"), &carry),
                (format!("{s} <u t:{n}"), &borrow),
            ] {
                let mut cx = Context::new();
                let opts = ParseOptions::width(Width::new(w as u16).unwrap());
                let a = cx.parse(&format!("zext<{j}>({test})"), &opts).unwrap();
                let b = cx.parse(digits, &opts).unwrap();
                assert!(equivalent(&mut cx, a, b, &mut rng), "{test} vs {digits}");
            }
        }
    }
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0021);
    let mut changed = 0;
    for i in 0..900 {
        let w: u64 = if i % 3 == 0 { 6 } else { 7 };
        // The digit `[o, o + n)`, with bits above it (or, one time in eight, none).
        let o = 1 + g.below(w - 2);
        let n = if g.chance(1, 8) {
            w - o
        } else {
            1 + g.below(w - o - 1)
        };
        let at = o + n;
        let word = match g.below(4) {
            0 | 1 => format!("a:{w}"),
            2 => format!("(a:{w} + {})", g.below(1 << w)),
            _ => format!("(a:{w} * 3)"),
        };
        // An `n`-bit value that is no slice: of a 3-bit symbol, a constant, a product, a
        // flag or another symbol beside it.
        let fit = |v: &str, bits: u64| match bits.cmp(&n) {
            core::cmp::Ordering::Less => format!("zext<{n}>({v})"),
            core::cmp::Ordering::Equal => v.to_string(),
            core::cmp::Ordering::Greater => format!("trunc<{n}>({v})"),
        };
        let narrow = |g: &mut Rng| {
            let b = fit("b:3", 3);
            match g.below(7) {
                0..=2 => b,
                3 => format!("({b} + {})", g.below(1 << n)),
                4 => format!("({b} * {})", g.below(1 << n) | 1),
                5 => fit(&format!("(c:4 <u {})", g.below(16)), 1),
                _ => format!("({b} ^ {})", fit("c:4", 4)),
            }
        };
        let s = format!("extract<{o}, {n}>({word})");
        let (t, u) = (narrow(&mut g), narrow(&mut g));
        let k = g.below(1 << n);
        let (x, y) = match g.below(12) {
            0 | 1 => (format!("{s} + {t}"), t.clone()),
            2 => (format!("{s} + {t} + {k}"), t.clone()),
            3 | 4 => (format!("{t} + {s}"), s.clone()),
            5 => (format!("{s} + {t} + {k}"), format!("{s} + {u}")),
            6 => (s.clone(), t.clone()),
            7 => (format!("{s} + {k}"), t.clone()),
            8 => (s.clone(), format!("{s} - {t}")),
            9 => (format!("{s} + {t}"), u.clone()),
            10 => (format!("{s} - {t}"), s.clone()),
            _ => (
                format!("extract<{o}, {n}>(({word} + {})) + {k}", g.below(1 << w)),
                s.clone(),
            ),
        };
        let (x, y) = if g.chance(1, 5) { (y, x) } else { (x, y) };
        // One time in four in a register wider than the digit: the sides zero-extended, the
        // word's slice also taken longer from under a mask (or, without one, with the bits
        // above the digit: another comparison).
        let (x, y) = if g.chance(1, 4) {
            let m = n + 1 + g.below(2);
            let mut held = |v: &str| {
                if *v == s && o + m <= w && g.chance(1, 2) {
                    if g.chance(3, 4) {
                        format!("extract<{o}, {m}>({word} & {})", (1u64 << at) - 1)
                    } else {
                        format!("extract<{o}, {m}>({word})")
                    }
                } else {
                    format!("zext<{m}>({v})")
                }
            };
            (held(&x), held(&y))
        } else {
            (x, y)
        };
        let j = if at < w && g.chance(2, 3) {
            w - at
        } else {
            1 + g.below(w)
        };
        let high = |v: &str| {
            if at >= w {
                format!("trunc<{j}>({v})")
            } else if at + j <= w {
                format!("extract<{at}, {j}>({v})")
            } else {
                format!("zext<{j}>(extract<{at}, {}>({v}))", w - at)
            }
        };
        let mut src = String::new();
        let mut term = |g: &mut Rng, t: String| {
            let sign = if g.chance(1, 4) { '-' } else { '+' };
            src.push_str(&format!(" {sign} {t}"));
        };
        let ext = if g.chance(1, 4) { "sext" } else { "zext" };
        let test = format!("{ext}<{j}>({x} <u {y})");
        let shifted = format!("(zext<{w}>({t}) << {o})");
        if g.chance(1, 2) {
            // As the limb code writes it: the carry beside the word's high digit, or the
            // high digit less the borrow.
            let sign = if g.chance(1, 4) { '-' } else { '+' };
            src.push_str(&format!(" + {} {sign} {test}", high(&word)));
        } else {
            term(&mut g, test);
            for v in [
                word.clone(),
                format!("({word} + {shifted})"),
                format!("({word} - {shifted})"),
            ] {
                if g.chance(1, 2) {
                    term(&mut g, high(&v));
                }
            }
        }
        let src = format!("0:{j}{src}");
        let src = match g.below(3) {
            0 => src,
            1 => format!("trunc<{}>({src})", 1 + g.below(j)),
            _ => format!("({src}) & {}", g.below(1 << j)),
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 450, "{changed}");
}

/// Limb arithmetic: a narrow value added into the middle of a wide one, the carry out of the
/// limb written against the value or against the word's digit, is a slice of the word plus
/// the value shifted; the limb and its carry out are one slice.
#[cfg(feature = "prove")]
#[test]
fn limb_shifted_fixtures() {
    let eng = deobfuscator();
    for (src, w, want) in [
        // The carry out of the limb `[24, 36)` against the value added.
        (
            "let q = zext<12>(b:9); \
             zext<12>(q + extract<24, 12>(a:64) <u q) + extract<36, 12>(a)",
            12,
            "extract<36, 12>((zext<64>(b) << 24) + a)",
        ),
        // Against the word's digit.
        (
            "let s = extract<20, 17>(a:64); \
             zext<9>(zext<17>(b:10) + s <u s) + extract<37, 9>(a)",
            9,
            "extract<37, 9>((zext<64>(b) << 20) + a)",
        ),
        // The value a digit of another word: that word masked.
        (
            "let s = extract<16, 16>(a:64); \
             zext<16>(extract<16, 16>(c:64) + s <u s) + extract<32, 16>(a)",
            16,
            "extract<32, 16>((c & 0xffff0000) + a)",
        ),
        // The borrow of the digit less the value.
        (
            "extract<22, 10>(x:32) - zext<10>(extract<10, 12>(x) <u d:12)",
            10,
            "extract<22, 10>(x - (zext<32>(d) << 10))",
        ),
        // The limb and its carry out, joined by a concatenation and by a shift.
        (
            "let q = zext<12>(b:9); let m = q + extract<24, 12>(a:64); \
             concat(zext<12>(m <u q) + extract<36, 12>(a), m)",
            24,
            "zext<24>(b) + extract<24, 24>(a)",
        ),
        (
            "let m = d:12 + extract<10, 12>(x:32); \
             zext<32>(m) | (zext<32>(zext<10>(m <u d) + extract<22, 10>(x)) << 12)",
            32,
            "zext<32>(zext<22>(d) + extract<10, 22>(x))",
        ),
        // The digits in a 16-bit register: the value's zero-extended, the word's a longer
        // slice from under a mask.
        (
            "zext<10>(zext<16>(extract<11, 11>(x:32) + e:11) <u extract<11, 16>(x & 0x3fffff)) \
             + extract<22, 10>(x)",
            10,
            "extract<22, 10>((zext<32>(e) << 11) + x)",
        ),
        // A constant added limb by limb (11, 11 and 10 bits; 837 and 434 are its digits),
        // the middle limb's carry out compared in such a register.
        (
            "let m = x:32 * 0x2c51a7e3; \
             zext<10>(zext<16>(extract<11, 11>(m + 837) + 434) <u extract<11, 16>(m & 0x3fffff)) \
             + extract<22, 10>(m)",
            10,
            "extract<22, 10>(x * 0x2c51a7e3 + 0xd9345)",
        ),
    ] {
        assert_eq!(simplify(&eng, src, w), want, "{src}");
    }
}

/// Limb arithmetic: the carry out of a middle limb written with the carry into it (the other
/// operand's digit is all ones and a carry comes in, or the limb's sum wrapped) is the carry
/// at the limb's upper boundary, and the top limb the high digit of the word.
#[cfg(feature = "prove")]
#[test]
fn limb_detector_fixtures() {
    let eng = deobfuscator();
    for (src, want) in [
        // A constant added limb by limb (13, 13 and 6 bits): 421 and 2860 are its digits.
        (
            "let m = x * 0x2c51a7e3; let h = m >>u 13; let c = (m + 421 & 8191) <u 421; \
             let d = h + zext<32>(c) + 2860 & 8191; \
             trunc<6>(zext<8>(extract<26, 6>(m)) \
             + zext<8>((h + 1 & 8191 == 0) & c | (d <u 2860)))",
            "extract<26, 6>(x * 0x2c51a7e3 + 0x16581a5)",
        ),
        // A negation in limbs of 15, 15 and 2 bits: its borrows are `!= 0`.
        (
            "let h = x >>u 15; let b = -x & 32767 != 0; \
             let d = -(h + zext<32>(b)) & 32767; \
             trunc<2>(sext<8>((~h & 32767 == 0) & b | (d != 0)) - trunc<8>(x >>u 30))",
            "extract<30, 2>(-x)",
        ),
        // The top limb of `x + y` in limbs of 11, 11 and 10 bits, beside a third digit (no
        // slice of one word).
        (
            "let s = x + y; let c = (s & 2047) <u (x & 2047); \
             let m = (x >>u 11) + (y >>u 11) + zext<32>(c) & 2047; \
             trunc<10>((x >>u 22) + (y >>u 22) + (z >>u 22) \
             + zext<32>(((y >>u 11) + 1 & 2047 == 0) & c | (m <u (x >>u 11 & 2047))))",
            "extract<22, 10>(x + y) + extract<22, 10>(z)",
        ),
    ] {
        assert_eq!(simplify(&eng, src, 32), want, "{src}");
    }
}

/// Carry detectors with a carry in, generated: the words `q` and `d` and their sum, the limb
/// `[o, o + n)`, the carry into it and the test of a digit in several spellings, some of
/// them of another value (no detector then); every result is checked at every assignment.
#[cfg(feature = "prove")]
#[test]
fn limb_detectors_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0007);
    let mut rng = Rng(83);
    let (mut changed, mut read) = (0, 0);
    for i in 0..1200 {
        let w: u64 = if i % 3 == 0 { 6 } else { 7 };
        let sym = |g: &mut Rng| format!("{}:{w}", ["a", "b"][g.below(2) as usize]);
        let value = |g: &mut Rng| {
            let (x, y) = (sym(g), sym(g));
            let c = g.below(1 << w);
            match g.below(6) {
                0 | 1 => x,
                2 => format!("({x} + {y})"),
                3 => format!("({x} ^ {y})"),
                4 => format!("({x} * {c})"),
                _ => format!("({x} + {c})"),
            }
        };
        // The limbs `[0, o)` and `[o, o + n)`, with bits above them.
        let o = 1 + g.below(w - 2);
        let n = 1 + g.below(w - o - 1);
        let at = o + n;
        let (mo, mn) = ((1u64 << o) - 1, (1u64 << n) - 1);
        let q = value(&mut g);
        let d = if g.chance(1, 2) {
            format!("{}:{w}", g.below(1 << at))
        } else {
            value(&mut g)
        };
        let p = format!("({q} + {d})");
        // (One time in ten another value: the detector of no word.)
        let wrong = |g: &mut Rng, v: &str| {
            if g.chance(1, 10) {
                value(g)
            } else {
                v.to_string()
            }
        };
        let low = |g: &mut Rng, v: &str| {
            if g.chance(1, 2) {
                format!("({v} & {mo})")
            } else {
                format!("zext<{w}>(trunc<{o}>({v}))")
            }
        };
        let hi = |v: &str| format!("({v} >>u {o})");
        // The carry into the limb.
        let other = if g.chance(1, 2) { q.clone() } else { d.clone() };
        let (cp, cq) = (wrong(&mut g, &p), wrong(&mut g, &other));
        let cin = format!("({} <u {})", low(&mut g, &cp), low(&mut g, &cq));
        // The digit of `p` against that of one operand, the other's tested.
        let (y, z) = if g.chance(1, 2) { (&q, &d) } else { (&d, &q) };
        let tested = wrong(&mut g, z);
        let dz = format!("extract<{o}, {n}>({tested})");
        let test = match g.below(4) {
            0 => format!("({dz} == {mn})"),
            1 => format!("(((zext<{w}>({dz}) + 1) & {mn}) == 0)"),
            2 => format!("((~{} & {mn}) == 0)", hi(&tested)),
            _ => format!("((({} + 1) & {mn}) == 0)", hi(&tested)),
        };
        let x = match g.below(3) {
            0 => format!("({} & {mn})", hi(&p)),
            1 => format!("zext<{w}>(extract<{o}, {n}>({p}))"),
            _ => format!("(({} + {} + zext<{w}>({cin})) & {mn})", hi(&q), hi(&d)),
        };
        let cmp = format!("({x} <u ({} & {mn}))", hi(y));
        let det = if g.chance(1, 2) {
            format!("(({test} & {cin}) | {cmp})")
        } else {
            format!("({cmp} | ({cin} & {test}))")
        };
        let j = if g.chance(2, 3) {
            w - at
        } else {
            1 + g.below(w)
        };
        let high = |v: &str| {
            if at + j <= w {
                format!("extract<{at}, {j}>({v})")
            } else {
                format!("zext<{j}>(extract<{at}, {}>({v}))", w - at)
            }
        };
        let mut src = String::new();
        let mut term = |g: &mut Rng, t: String| {
            let sign = if g.chance(1, 4) { '-' } else { '+' };
            src.push_str(&format!(" {sign} {t}"));
        };
        let ext = if g.chance(1, 4) { "sext" } else { "zext" };
        term(&mut g, format!("{ext}<{j}>({det})"));
        for v in [&p, &q, &d] {
            if g.chance(2, 3) {
                term(&mut g, high(v));
            }
        }
        let src = format!("0:{j}{src}");
        let src = match g.below(3) {
            0 => src,
            1 => format!("trunc<{}>({src})", 1 + g.below(j)),
            _ => format!("({src}) & {}", g.below(1 << j)),
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
        read += u64::from(!cx.display(out.expr).to_string().contains("<u"));
    }
    // (614 are read without the detectors.)
    assert!(changed > 600 && read > 630, "{changed} {read}");
}

/// Limb arithmetic: a limb that is no slice of one word (a third value's digit added in it)
/// read for its carry-out detector as the digit of the word with that digit in its place; a
/// top limb in a register wider than the word, beside the digit of a wider value with the
/// word's low bits; a carry written `c <=u d` (of adding `2^n − c` to a digit) and one
/// written `x & M != M` (the borrow of subtracting `M`).
#[cfg(feature = "prove")]
#[test]
fn limb_detector_word_fixtures() {
    let eng = deobfuscator();
    for (src, want) in [
        // `x + y + (e << 11)` in limbs of 11, 11 and 10 bits, `e` a digit of a third value.
        (
            "let s = x + y; let c = (s & 2047) <u (x & 2047); let e = z & 2047; \
             let m = (x >>u 11) + (y >>u 11) + e + zext<32>(c) & 2047; \
             trunc<10>((x >>u 22) + (y + (e << 11) >>u 22) \
             + zext<32>(((y >>u 11) + e + 1 & 2047 == 0) & c | (m <u (x >>u 11 & 2047))))",
            "extract<22, 10>(((z & 2047) << 11) + x + y)",
        ),
        // A constant added in limbs of 13, 13 and 6 bits, the top limb in an 8-bit register
        // from the 64-bit product.
        (
            "let m = x * 0x2c51a7e3; let h = m >>u 13; let c = (m + 421 & 8191) <u 421; \
             let d = h + zext<32>(c) + 2860 & 8191; \
             zext<8>((h + 1 & 8191 == 0) & c | (d <u 2860)) \
             + extract<26, 8>(zext<64>(x) * 0x2c51a7e3)",
            "extract<26, 8>(zext<64>(x) * 0x2c51a7e3 + 0x16581a5)",
        ),
        // The borrow of subtracting 8191 from a low digit.
        (
            "let m = x * 0x2c51a7e3 + y; \
             trunc<19>((m >>u 13) + (z >>u 13) - zext<32>((m & 8191) != 8191))",
            "extract<13, 19>(z) + extract<13, 19>(x * 0x2c51a7e3 + y - 8191)",
        ),
    ] {
        assert_eq!(simplify(&eng, src, 32), want, "{src}");
    }
}

/// Carry detectors over limbs that are no slice of one word (a third value's digit beside
/// the operands'), the digit's test in three spellings, the top limb in a register wider than
/// the words (the digit of a wider value with the same low bits beside the carry), and
/// carries spelled `c <=u d` and `x != M`: generated, every result checked at every
/// assignment.
#[cfg(feature = "prove")]
#[test]
fn limb_detector_words_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0019);
    let mut rng = Rng(89);
    let (mut changed, mut read) = (0, 0);
    for i in 0..1500 {
        let w: u64 = if i % 3 == 0 { 6 } else { 7 };
        // A register wider than the words.
        let ww = w + 1 + g.below(3);
        let name = |g: &mut Rng| ["a", "b"][g.below(2) as usize];
        // A value at the words' width, and the same at the register's (its low bits).
        let value = |g: &mut Rng| {
            let (x, y, c, kind) = (name(g), name(g), g.below(1 << w), g.below(6));
            let at = |b: u64| {
                let s = |v: &str| {
                    if b == w {
                        format!("{v}:{w}")
                    } else {
                        format!("zext<{b}>({v}:{w})")
                    }
                };
                match kind {
                    0 | 1 => s(x),
                    2 => format!("({} + {})", s(x), s(y)),
                    3 => format!("({} ^ {})", s(x), s(y)),
                    4 => format!("({} * {c})", s(x)),
                    _ => format!("({} + {c})", s(x)),
                }
            };
            (at(w), at(ww))
        };
        let o = 1 + g.below(w - 2);
        let n = 1 + g.below(w - o - 1);
        let at = o + n;
        let (mo, mn) = ((1u64 << o) - 1, (1u64 << n) - 1);
        let j = if g.chance(2, 3) {
            ww - at
        } else {
            1 + g.below(ww - at)
        };
        // The high digit from bit `k` of a value, of the word or of the register.
        let high = |g: &mut Rng, v: &(String, String), k: u64| {
            if g.chance(1, 2) {
                format!("extract<{k}, {j}>({})", v.1)
            } else if k + j <= w {
                format!("extract<{k}, {j}>({})", v.0)
            } else {
                format!("zext<{j}>(extract<{k}, {}>({}))", w - k, v.0)
            }
        };
        let mut src = String::new();
        let mut term = |g: &mut Rng, t: String| {
            let sign = if g.chance(1, 4) { '-' } else { '+' };
            src.push_str(&format!(" {sign} {t}"));
        };
        let ext = if g.chance(1, 4) { "sext" } else { "zext" };
        let q = value(&mut g);
        if i % 4 == 3 {
            // A carry in another spelling, beside the digits it is of.
            let wide = |v: &(String, String), k: u64| {
                (format!("({} + {k})", v.0), format!("({} + {k})", v.1))
            };
            let (carry, k, other) = match g.below(3) {
                // `c <=u lo(q)`: the carry of adding `2^at − c`.
                0 => {
                    let c = 1 + g.below((1 << at) - 1);
                    let carry = format!("({c}:{at} <=u trunc<{at}>({}))", q.0);
                    (carry, at, wide(&q, (1 << at) - c))
                }
                // The same of a middle digit: nothing carries into it.
                1 => {
                    let c = 1 + g.below(mn);
                    let carry = format!("({c}:{n} <=u extract<{o}, {n}>({}))", q.0);
                    (carry, at, wide(&q, ((1 << n) - c) << o))
                }
                // `lo(q) != M`: the borrow of subtracting `M`.
                _ => {
                    let low = if g.chance(1, 2) {
                        format!("({} & {mo})", q.0)
                    } else {
                        format!("zext<{w}>(trunc<{o}>({}))", q.0)
                    };
                    let m = (1u64 << w) - mo;
                    (format!("({low} != {mo})"), o, wide(&q, m))
                }
            };
            term(&mut g, format!("{ext}<{j}>({carry})"));
            for v in [&q, &other] {
                if g.chance(2, 3) {
                    let t = high(&mut g, v, k);
                    term(&mut g, t);
                }
            }
        } else {
            let d = if g.chance(1, 2) {
                let c = g.below(1 << at);
                (format!("{c}:{w}"), format!("{c}:{ww}"))
            } else {
                value(&mut g)
            };
            let p = (
                format!("({} + {})", q.0, d.0),
                format!("({} + {})", q.1, d.1),
            );
            // A third value's digit beside the limb's own, one time in two.
            let third = g.chance(1, 2);
            let e = if third {
                format!("({}:{w} & {mn})", name(&mut g))
            } else {
                format!("0:{w}")
            };
            // (One time in ten another value: the detector of no word.)
            let wrong = |g: &mut Rng, v: &str| {
                if g.chance(1, 10) {
                    value(g).0
                } else {
                    v.to_string()
                }
            };
            let low = |v: &str| format!("({v} & {mo})");
            let hi = |v: &str| format!("({v} >>u {o})");
            let other = if g.chance(1, 2) { &q.0 } else { &d.0 };
            let (cp, cq) = (wrong(&mut g, &p.0), wrong(&mut g, other));
            let cin = format!("({} <u {})", low(&cp), low(&cq));
            let (y, z) = if g.chance(1, 2) {
                (&q.0, &d.0)
            } else {
                (&d.0, &q.0)
            };
            let tested = wrong(&mut g, z);
            // The digit of the other operand plus the third's is all ones.
            let test = match g.below(3) {
                0 => format!("((({} + {e} + 1) & {mn}) == 0)", hi(&tested)),
                1 => format!("(extract<{o}, {n}>({tested}) == ~trunc<{n}>({e}))"),
                _ => format!("((({} + {e}) & {mn}) == {mn})", hi(&tested)),
            };
            let x = if g.chance(1, 2) {
                format!("(({} + {e}) & {mn})", hi(&p.0))
            } else {
                format!(
                    "(({} + {} + {e} + zext<{w}>({cin})) & {mn})",
                    hi(&q.0),
                    hi(&d.0)
                )
            };
            let cmp = format!("({x} <u ({} & {mn}))", hi(y));
            let det = if g.chance(1, 2) {
                format!("(({test} & {cin}) | {cmp})")
            } else {
                format!("({cmp} | ({cin} & {test}))")
            };
            term(&mut g, format!("{ext}<{j}>({det})"));
            // The word the limbs are of: with the third digit in its place.
            let whole = if third {
                (
                    format!("({} + ({e} << {o}))", p.0),
                    format!("({} + (zext<{ww}>({e}) << {o}))", p.1),
                )
            } else {
                p
            };
            for v in [&whole, &q, &d] {
                if g.chance(2, 3) {
                    let t = high(&mut g, v, at);
                    term(&mut g, t);
                }
            }
        }
        let src = format!("0:{j}{src}");
        let src = match g.below(3) {
            0 => src,
            1 => format!("trunc<{}>({src})", 1 + g.below(j)),
            _ => format!("({src}) & {}", g.below(1 << j)),
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
        let text = cx.display(out.expr).to_string();
        read += u64::from(!(text.contains("<u") || text.contains("<=u") || text.contains("!=")));
    }
    // (481 are read without the limbs' words, the wider words and the spellings.)
    assert!(changed > 1100 && read > 500, "{changed} {read}");
}

/// Limb arithmetic: a carry whose difference the sum holds the high digit of in another
/// spelling (the partial product a schoolbook product adds, shifted into place, beside the
/// product of the word that a carry's side has become), and a carry between sides lifted
/// above their digit beside the word's high digit (the difference is read modulo the digit).
#[cfg(feature = "prove")]
#[test]
fn limb_difference_word_fixtures() {
    let eng = deobfuscator();
    for (src, w, want) in [
        // `x * 9653` in digits of 5 bits (21, 13 and 9), its limb from bit 10: the sum of
        // the low limbs is written as a product of the word right on 10 bits only, and the
        // sum holds the partial products from bit 5 on.
        (
            "let %0 = x:16 & 31; let %1 = (x >>u 5) & 31; let %2 = %0 * 21 + (%0 * 13 << 5); \
             trunc<5>(%0 * 9 + %1 * 13 + (x >>u 10) * 21 + (%0 * 13 >>u 5) + (%1 * 21 >>u 5) \
             + zext<16>(x * 38325 & 1023 <u %2 & 1023) + zext<16>(%2 & 1023 <u %0 * 21))",
            5,
            "extract<10, 5>(x * 9653)",
        ),
        // The low limb at its own width, the constant added to it written as a difference
        // (715 is -1333 modulo 2^11), beside the high digit of the word.
        (
            "zext<5>(77:11 - trunc<11>(x:16) * 715 <u trunc<11>(x) * 1333) \
             + extract<11, 5>(x * 27957)",
            5,
            "extract<11, 5>(x * 27957 + 77)",
        ),
    ] {
        assert_eq!(simplify(&eng, src, w), want, "{src}");
    }
}

/// Limb arithmetic: carries beside a high digit of a word that has the low bits of the
/// carry's difference, shifted into place, of one of its sides, or of neither (a reading
/// that took the word for the difference on more bits than the carry reads, or where it is
/// no spelling of it, would be caught); chains of two carries; and carries between sides at
/// the digit's own width beside the high digit of the word. Each stays equal to itself at
/// every assignment.
#[cfg(feature = "prove")]
#[test]
fn limb_difference_words_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0041);
    let mut rng = Rng(101);
    let mut changed = 0;
    let w: u64 = 7;
    let mask = (1u64 << w) - 1;
    for i in 0..900 {
        let at = 2 + g.below(w - 3);
        let j = 1 + g.below(w - at);
        let x = match g.below(3) {
            0 => "a:7".to_string(),
            1 => format!("(a:7 ^ (a >>u {}))", 1 + g.below(w - 1)),
            _ => "(a:7 + b:7)".to_string(),
        };
        // Anything above bit `at`, or (one time in six) a bit below it: no spelling then.
        let noise = |g: &mut Rng| {
            if g.chance(1, 6) {
                1u64 << g.below(at)
            } else {
                (g.below(1 << w) << at) & mask
            }
        };
        let carry = |g: &mut Rng, p: &str, q: &str| {
            let (p, q) = (format!("trunc<{at}>({p})"), format!("trunc<{at}>({q})"));
            match g.below(4) {
                0 => format!("- sext<{j}>({p} <u {q})"),
                1 => format!("- ~zext<{j}>({p} <u {q})"),
                _ => format!("+ zext<{j}>({p} <u {q})"),
            }
        };
        let src = if i % 3 < 2 {
            // `P = Q + (A << s) + noise` in one spelling or another, the sum holding the
            // digit of `A` from bit `at − s`.
            let o = 1 + g.below(at);
            let s = at - o;
            let ka = g.below(1 << w) | 1;
            let a = match g.below(3) {
                0 => format!("({x} * {ka})"),
                1 => format!("(({x} & {}) * {ka})", (1u64 << o) - 1),
                _ => "b:7".to_string(),
            };
            let kq = g.below(1 << w);
            let q = match g.below(3) {
                0 => format!("({x} * {kq})"),
                1 => format!("{kq}:7"),
                _ => format!("(({x} & {}) * {kq})", (1u64 << at) - 1),
            };
            let up = (ka << s) & mask;
            let p = match g.below(3) {
                0 => format!("({q} + ({a} << {s}) + {x} * {})", noise(&mut g)),
                1 => format!("({x} * {} + {q})", (up + noise(&mut g)) & mask),
                _ => format!("({q} + ({a} << {s}))"),
            };
            let digit = if g.chance(1, 2) {
                format!("extract<{o}, {j}>({a})")
            } else {
                format!("trunc<{j}>({a} >>u {o})")
            };
            let mut src = format!("{digit} {}", carry(&mut g, &p, &q));
            // The sum before, with its own carry and its own digit.
            if g.chance(1, 2) {
                let kb = g.below(1 << w);
                let r = format!("({q} - b:7 * {kb} + {x} * {})", noise(&mut g));
                src.push_str(&format!(" {}", carry(&mut g, &q, &r)));
                if g.chance(1, 2) {
                    src.push_str(&format!(" + extract<{at}, {j}>(b * {kb})"));
                }
            }
            if g.chance(1, 3) {
                src.push_str(&format!(" + extract<{at}, {j}>({q})"));
            }
            src
        } else {
            // Sides at the digit's width, their difference a constant there (or not), beside
            // the high digit of the word (or of another).
            let kq = g.below(1 << at) | 1;
            let kn = if g.chance(1, 5) {
                g.below(1 << at)
            } else {
                (1u64 << at) - kq
            };
            let k = if g.chance(1, 5) {
                g.below(1 << w)
            } else {
                kq | (g.below(1 << w) << at) & mask
            };
            let c = g.below(1 << at);
            let t = format!("trunc<{at}>({x})");
            format!(
                "zext<{j}>({c}:{at} - {t} * {kn} <u {t} * {kq}) + extract<{at}, {j}>({x} * {k})"
            )
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(j as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = eng.simplify(&mut cx, e).unwrap();
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 300, "{changed}");
}

/// Limb arithmetic: the limbs of one word, each under the coefficient of the one below shifted
/// by that limb's width, are the word (a product by a constant computed limb by limb is the
/// product of the word), in every spelling of a limb, modulo the bits read.
#[cfg(feature = "prove")]
#[test]
fn limb_join_fixtures() {
    let eng = deobfuscator();
    for (src, w, want) in [
        // Two limbs of 18 and 14 bits; the high one as a shift, as a slice, and as a slice of
        // the sign extension (whose high bits the coefficient's trailing zeros discard).
        (
            "(w & 0x3ffff) * 0x2f6b8d35 + (w >>u 18) * 0x34d40000",
            32,
            "w * 0x2f6b8d35",
        ),
        (
            "(w & 0x3ffff) * 0x2f6b8d35 + zext<32>(extract<18, 14>(w)) * 0x34d40000",
            32,
            "w * 0x2f6b8d35",
        ),
        (
            "(w & 0x3ffff) * 0x2f6b8d35 + extract<18, 32>(sext<64>(w)) * 0x34d40000",
            32,
            "w * 0x2f6b8d35",
        ),
        // Four digits, one of them a digit of a limb.
        (
            "(w & 127) * 11 + (w >>u 7 & 127) * 1408 + ((w >>u 14 & 0x3fff) & 127) * 180224 \
             + zext<32>(extract<21, 11>(w)) * 0x1600000",
            32,
            "w * 11",
        ),
        // The word less its low limb is its high limb, in place.
        ("w - (w & 0x1fff)", 32, "w & -8192"),
        // A product of the word (its high part of the constant) beside the limbs' products.
        (
            "w * 0x2f6b8000 + (w & 0x1fff) * 3381 + (w >>u 13) * 0x1a6a000",
            32,
            "w * 0x2f6b8d35",
        ),
        // The word joined by a `concat`, a limb put together again from its pieces.
        (
            "concat(h:6, concat(m:13, l:13)) * 0x2f6b8000 + concat(zext<19>(h), m) * 0x1a6a000 \
             + zext<32>(l) * 3381",
            32,
            "concat(h, concat(m, l)) * 0x2f6b8d35",
        ),
        // Modulo the bits read: the limbs of a 64-bit register's sum of which 32 are read.
        (
            "extract<18, 14>(zext<64>(x:32 & 0x3ffff) * 0x38d35 + sext<64>(x) * 0x2f680000 \
             + zext<64>(extract<18, 32>(sext<64>(x)) & 0x3ffff) * 0xe34d40000 + zext<64>(y:32))",
            14,
            "extract<18, 14>(sext<64>(x) * 0x2f6b8d35 + zext<64>(y))",
        ),
    ] {
        assert_eq!(simplify(&eng, src, w), want, "{src}");
    }
}

/// Limb arithmetic: a limb's sum in a register wider than the limb, read by several users
/// each through a truncation of its own that is wider than the limb, is read on the bits that
/// reach the result, where its carry completes the high digit; every reader shares the limb.
#[cfg(feature = "prove")]
#[test]
fn limb_reader_fixtures() {
    let eng = deobfuscator();
    let limb = "((x >>u 18) + (y >>u 18) + zext<32>((x + y & 0x3ffff) <u (x & 0x3ffff)))";
    for (src, w, want) in [
        (
            format!(
                "trunc<14>(zext<32>(trunc<19>({limb})) * 3 + (zext<32>(trunc<31>({limb})) & v))"
            ),
            32,
            "let %0 = extract<18, 14>(x + y);\n%0 * 3 + (trunc<14>(v) & %0)",
        ),
        // The readers of a handler's and-term: twice the high limb and a bit of the low one
        // against the next digit, held up as a high limb is.
        (
            format!(
                "(concat(trunc<31>({limb}), extract<17, 1>(x + y)) + 5 \
                 & concat(trunc<18>({limb} + 77), extract<4, 14>(x + y))) << 18"
            ),
            32,
            "let %0 = x + y;\n\
             (zext<32>(extract<17, 14>(%0)) + 5 & zext<32>(extract<4, 14>(%0))) << 18",
        ),
    ] {
        assert_eq!(simplify(&eng, &src, w), want, "{src}");
    }
}

/// Limb arithmetic: sums of the limbs of a word, each limb spelled every way the limbs pass
/// reads one (a mask, a shift, a slice, a digit of a limb, a slice of the sign extension, the
/// pieces of a `concat`), under coefficients that double from limb to limb or do not, read
/// whole or under a truncation, a mask or a slice, stay equal to themselves: exhaustively.
#[cfg(feature = "prove")]
#[test]
fn limb_joins_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0002);
    let mut rng = Rng(78);
    let mut changed = 0;
    for i in 0..1500 {
        // Two symbols of 7 bits, or three of 4: every assignment is checked.
        let (w, syms): (u64, &[&str]) = if i % 3 == 0 {
            (4, &["a", "b", "c"])
        } else {
            (7, &["a", "b"])
        };
        let full = (1u64 << w) - 1;
        let sym = |g: &mut Rng| format!("{}:{w}", syms[g.below(syms.len() as u64) as usize]);
        // The word: a symbol, a sum, or two slices put together by a `concat`.
        let x = match g.below(5) {
            0 => {
                let (p, q) = (sym(&mut g), sym(&mut g));
                format!("({p} + {q})")
            }
            1 => {
                let k = 1 + g.below(w - 1);
                let (p, q) = (sym(&mut g), sym(&mut g));
                let lo = g.below(k + 1);
                format!("concat(extract<{lo}, {}>({p}), trunc<{k}>({q}))", w - k)
            }
            _ => sym(&mut g),
        };
        // Its limbs, between cuts.
        let mut cuts = vec![0, w];
        for _ in 0..1 + g.below(3) {
            cuts.push(1 + g.below(w - 1));
        }
        cuts.sort_unstable();
        cuts.dedup();
        let k0 = g.below(1 << w) | u64::from(g.chance(2, 3));
        let mut src = format!("0:{w}");
        for c in cuts.windows(2) {
            let (lo, len) = (c[0], c[1] - c[0]);
            // (A limb left out now and then.)
            if g.chance(1, 8) {
                continue;
            }
            let mask = (1u64 << len) - 1;
            let limb = match g.below(6) {
                0 if lo == 0 => format!("({x} & {mask})"),
                1 => format!("zext<{w}>(extract<{lo}, {len}>({x}))"),
                // Right as a limb only under a coefficient whose trailing zeros discard the
                // sign's copies.
                2 => format!("extract<{lo}, {w}>(sext<{}>({x}))", 2 * w),
                3 => format!("(({x} & {}) >>u {lo})", (1u64 << (lo + len)) - 1),
                4 => format!("zext<{w}>(trunc<{len}>({x} >>u {lo}))"),
                _ => format!("(({x} >>u {lo}) & {mask})"),
            };
            // The coefficient of the lowest limb shifted to this one, mostly.
            let k = if g.chance(4, 5) {
                (k0 << lo) & full
            } else {
                g.below(1 << w)
            };
            src.push_str(&format!(" + {limb} * {k}"));
        }
        // The word itself, another value, a constant.
        if g.chance(1, 3) {
            src.push_str(&format!(" + {x} * {}", g.below(1 << w)));
        }
        if g.chance(1, 3) {
            src.push_str(&format!(" - {}", sym(&mut g)));
        }
        if g.chance(1, 3) {
            src.push_str(&format!(" + {}", g.below(1 << w)));
        }
        let src = match g.below(5) {
            0 | 1 => src,
            2 => format!("trunc<{}>({src})", 1 + g.below(w)),
            3 => format!("({src}) & {}", g.below(1 << w)),
            _ => {
                let lo = g.below(w);
                format!("extract<{lo}, {}>({src})", 1 + g.below(w - lo))
            }
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 1200, "{changed}");
}

/// Limb arithmetic: a sum of high digits and a carry, read by two users each through a mask,
/// a truncation or a shift of its own, under a result that reads a few bits of them, stays
/// equal to itself: exhaustively. (The sum is simplified on the bits its users read between
/// them, where its carry is read as high digits.)
#[cfg(feature = "prove")]
#[test]
fn limb_readers_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0003);
    let mut rng = Rng(79);
    let mut changed = 0;
    for i in 0..900 {
        let (w, syms): (u64, &[&str]) = if i % 3 == 0 {
            (4, &["a", "b", "c"])
        } else {
            (7, &["a", "b"])
        };
        let sym = |g: &mut Rng| format!("{}:{w}", syms[g.below(syms.len() as u64) as usize]);
        let value = |g: &mut Rng| {
            let (x, y) = (sym(g), sym(g));
            match g.below(4) {
                0 => format!("({x} + {y})"),
                1 => format!("({x} * {})", g.below(1 << w)),
                2 => format!("({x} ^ {y})"),
                _ => x,
            }
        };
        let k = 1 + g.below(w - 1);
        let mask = (1u64 << k) - 1;
        let (p, q) = (value(&mut g), value(&mut g));
        // The high limb of `p + q` as a register holds it, or a sum that only looks like it.
        let (cp, cq) = if g.chance(3, 4) {
            (format!("({p} + {q})"), p.clone())
        } else {
            (value(&mut g), value(&mut g))
        };
        let sign = if g.chance(1, 4) { '-' } else { '+' };
        let s = format!(
            "(({p} >>u {k}) + ({q} >>u {k}) {sign} zext<{w}>(({cp} & {mask}) <u ({cq} & {mask})))"
        );
        let reader = |g: &mut Rng| match g.below(5) {
            0 => format!("zext<{w}>(trunc<{}>({s}))", 1 + g.below(w)),
            1 => format!("({s} & {})", g.below(1 << w)),
            2 => format!("({s} << {})", g.below(w)),
            3 => format!("({s} + {})", g.below(1 << w)),
            _ => format!(
                "concat(trunc<{}>({s}), extract<{}, 1>({p}))",
                w - 1,
                g.below(w)
            ),
        };
        let (r1, r2) = (reader(&mut g), reader(&mut g));
        let v = sym(&mut g);
        let body = match g.below(4) {
            0 => format!("{r1} + {r2}"),
            1 => format!("({r1} & {r2})"),
            2 => format!("{r1} * 3 + ({r2} & {v})"),
            _ => format!("{r1} - ({r2} ^ {v})"),
        };
        let src = match g.below(5) {
            0 => body,
            1 | 2 => format!("trunc<{}>({body})", 1 + g.below(w - k)),
            3 => format!("({body}) & {}", g.below(1 << w)),
            _ => format!("({body}) << {}", 1 + g.below(w - 1)),
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 600, "{changed}");
}

/// Limb arithmetic: an XOR or an OR with a constant written as a sum (`a + c − 2·(a & c)`,
/// `a + c − (a & c)`, the constant folded into the sum around it) is read as what it spells,
/// and meets the XOR itself in a carry's difference.
#[cfg(feature = "prove")]
#[test]
fn limb_mask_fixtures() {
    let eng = deobfuscator();
    for (src, w, want) in [
        (
            "x:32 * 77 + 0x5234 - 2 * (x * 77 + 0x4000 & 0x1234)",
            32,
            "x * 77 + 16384 ^ 4660",
        ),
        (
            "x:32 * 77 + 0x5234 - (x * 77 + 0x4000 & 0x1234)",
            32,
            "x * 77 + 16384 | 4660",
        ),
        ("x:32 + 0x2d5 - 2 * (x & 0x2d5)", 32, "x ^ 725"),
        (
            "(x:32 + y:32 ^ 0x1234) + 2 * (x + y & 0x1234)",
            32,
            "x + y + 4660",
        ),
        // Two carries of one handler: the first against the XOR, the second against a
        // constant, whose difference is the first's word less `2^26`.
        (
            "let s = x:32 + y:32 - 2 * (x & 0x2d5c1) + z:32; \
             zext<6>((s + 0x2d5c1 & 0x3ffffff) <u ((x ^ 0x2d5c1) & 0x3ffffff)) \
             + extract<26, 6>(y + z) + zext<6>((s + 9 & 0x3ffffff) <u 0x3fd2a48) - 1",
            6,
            "let %0 = x & 0x2d5c1;\n\
             extract<26, 6>(x + y - (%0 + %0) + z + 9) - extract<26, 6>(x)",
        ),
    ] {
        assert_eq!(simplify(&eng, src, w), want, "{src}");
    }
}

/// Limb arithmetic: the high digits of a product by a constant done digit by digit. A
/// partial product shifted into place (`a·(c << 11)`) meets the product's own high digit
/// (`a·c >> 11`), and the high limb of the schoolbook sum (the cross products modulo the
/// limb, the partial products' high digits and the two carries of the low limb) is the high
/// limb of the product of the word.
#[cfg(feature = "prove")]
#[test]
fn limb_digit_fixtures() {
    let eng = deobfuscator();
    let (k0, k1, k2) = (0x2b7u64, 0x1c35u64, 0x19u64);
    let high = format!(
        "let d0 = x:32 & 8191; let d1 = zext<32>(extract<13, 13>(x)); \
         let p = (x & 0x3ffffff) * {k0}; let w = p + d0 * {}; let l = p & 0x3ffffff; \
         trunc<6>(d1 * {} + d0 * {} + (x >>u 26) * {k0} + zext<32>(w & 0x3ffffff <u l) \
         + (d1 * {k0} >>u 13) + (d0 * {k1} >>u 13) + zext<32>(l <u d0 * {k0}))",
        k1 << 13,
        k1 + (77 << 6),
        k2 + (5 << 6),
    );
    for (src, w, want) in [
        (
            "let a = x:32 & 2047; let b = zext<32>(extract<11, 11>(x)); let p = a * 1021; \
             let q = p + (a * 333 << 11) & 0x3fffff; \
             trunc<10>((b * 333 + a * 97) + zext<32>(q <u p) + (b * 1021 >>u 11) + y:32 \
             + (a * 333 >>u 11) + zext<32>(z:32 & 0x3fffff <u q))"
                .to_string(),
            10,
            // (The borrow against `z` is read last, in the late stage of the rounds: the
            // high digit of the product it leaves meets the one that is there.)
            "trunc<10>(x) * 97 + extract<11, 10>(zext<32>(extract<11, 11>(x)) * 1021) \
             + extract<11, 10>(x) * 333 + extract<22, 10>(z) + trunc<10>(y) \
             - extract<22, 10>(z - (x & 2047) * 0xa6bfd)",
        ),
        (high, 6, "extract<26, 6>(x * 0x6786a2b7)"),
    ] {
        assert_eq!(simplify(&eng, &src, w), want, "{src}");
    }
}

/// Limb arithmetic: sums over `a & c`, `a ^ c` and `a | c` for a constant `c`, beside the
/// terms of `a` and a constant, under the coefficients that make them one another or not,
/// stay equal to themselves: exhaustively.
#[cfg(feature = "prove")]
#[test]
fn limb_masks_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0004);
    let mut rng = Rng(80);
    let mut changed = 0;
    for i in 0..1200 {
        let (w, syms): (u64, &[&str]) = if i % 3 == 0 {
            (4, &["a", "b", "c"])
        } else {
            (7, &["a", "b"])
        };
        let full = (1u64 << w) - 1;
        let sym = |g: &mut Rng| format!("{}:{w}", syms[g.below(syms.len() as u64) as usize]);
        // The value under the mask and its terms as a sum would spell them.
        let (p, q) = (sym(&mut g), sym(&mut g));
        let (k1, k2) = (g.below(1 << w), g.below(1 << w));
        let (a, spelled): (String, Vec<(String, u64)>) = match g.below(5) {
            0 => (format!("({p} + {q})"), vec![(p, 1), (q, 1)]),
            1 => (
                format!("({p} + {k1})"),
                vec![(p, 1), (format!("1:{w}"), k1)],
            ),
            2 => (format!("({p} * {k1})"), vec![(p, k1)]),
            3 => (
                format!("({p} - {q} + {k2})"),
                vec![(p, 1), (q, full), (format!("1:{w}"), k2)],
            ),
            _ => (p.clone(), vec![(p, 1)]),
        };
        let c = g.below(1 << w);
        // `k·(a ^ c)` or `k·(a | c)` as a sum over `a & c`, mostly; a term changed or left
        // out now and then.
        let k = 1 + g.below(full);
        let xor = g.chance(1, 2);
        let near = |g: &mut Rng, v: u64| if g.chance(5, 6) { v } else { g.below(1 << w) };
        let on_and = if xor { k.wrapping_mul(2) } else { k }.wrapping_neg() & full;
        let mut src = format!("({a} & {c}) * {}", near(&mut g, on_and));
        for (t, kt) in &spelled {
            if g.chance(7, 8) {
                let kt = near(&mut g, k.wrapping_mul(*kt) & full);
                src.push_str(&format!(" + {t} * {kt}"));
            }
        }
        if g.chance(5, 6) {
            src.push_str(&format!(" + {}", near(&mut g, k.wrapping_mul(c) & full)));
        }
        // The XOR, the OR and the value themselves beside it.
        for op in ["^", "|"] {
            if g.chance(1, 3) {
                let kt = near(&mut g, k.wrapping_neg() & full);
                src.push_str(&format!(" + ({a} {op} {c}) * {kt}"));
            }
        }
        if g.chance(1, 4) {
            src.push_str(&format!(" - {}", sym(&mut g)));
        }
        let src = match g.below(4) {
            0 | 1 => src,
            2 => format!("trunc<{}>({src})", 1 + g.below(w)),
            _ => {
                let lo = g.below(w);
                format!("extract<{lo}, {}>({src})", 1 + g.below(w - lo))
            }
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 900, "{changed}");
}

/// Limb arithmetic: the high limb of a product by a constant done in digits (cross products,
/// the partial products' high digits, the carries of the low limb), and high digits of sums
/// whose constants differ by a multiple of the digit or whose coefficients are shifted into
/// place, with a term changed or left out now and then, stay equal to themselves:
/// exhaustively.
#[cfg(feature = "prove")]
#[test]
fn limb_digits_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0005);
    let mut rng = Rng(81);
    let mut changed = 0;
    for i in 0..1200 {
        // A word of 8 bits in digits of 2 or 3, or two of 6 in digits of 2.
        let (w, syms): (u64, &[&str]) = if i % 3 == 0 {
            (6, &["a", "b"])
        } else {
            (8, &["a"])
        };
        let full = (1u64 << w) - 1;
        let sym = |g: &mut Rng| format!("{}:{w}", syms[g.below(syms.len() as u64) as usize]);
        let k = if w == 8 { 2 + g.below(2) } else { 2 };
        let (mask, mask2) = ((1u64 << k) - 1, (1u64 << (2 * k)) - 1);
        let near = |g: &mut Rng, v: u64| if g.chance(7, 8) { v } else { g.below(1 << w) };
        let x = sym(&mut g);
        let j = 1 + g.below(w - 2 * k);
        let src = if g.chance(2, 3) {
            // The schoolbook high limb of `x·(k0 + k1·2^k + k2·4^k)`.
            let (k0, k1, k2) = (g.below(mask + 1) | 1, g.below(mask + 1), g.below(mask + 1));
            let d0 = format!("({x} & {mask})");
            let d1 = match g.below(3) {
                0 => format!("zext<{w}>(extract<{k}, {k}>({x}))"),
                1 => format!("(({x} >>u {k}) & {mask})"),
                _ => format!("(({x} & {mask2}) >>u {k})"),
            };
            let d2 = if g.chance(1, 2) {
                format!("({x} >>u {})", 2 * k)
            } else {
                format!("extract<{}, {w}>(sext<{}>({x}))", 2 * k, 2 * w)
            };
            let p = format!("(({x} & {mask2}) * {})", near(&mut g, k0));
            let cross = if g.chance(1, 2) {
                format!("{d0} * {}", near(&mut g, (k1 << k) & full))
            } else {
                format!("({d0} * {k1} << {k})")
            };
            let (word, low) = (format!("({p} + {cross})"), format!("({p} & {mask2})"));
            // Any multiple of the limb's size on a cross product's constant.
            let above = |g: &mut Rng, v: u64| (v + (g.below(4) << j)) & full;
            let mut terms = vec![
                format!("{d1} * {}", above(&mut g, k1)),
                format!("{d0} * {}", above(&mut g, k2)),
                format!("{d2} * {}", near(&mut g, k0)),
                format!("zext<{w}>(({word} & {mask2}) <u {low})"),
                format!("(({d1} * {k0}) >>u {k})"),
                format!("(({d0} * {}) >>u {k})", near(&mut g, k1)),
                format!("zext<{w}>({low} <u ({d0} * {k0}))"),
            ];
            if g.chance(1, 6) {
                terms.remove(g.below(terms.len() as u64) as usize);
            }
            if g.chance(1, 4) {
                terms.push(sym(&mut g));
            }
            format!("trunc<{j}>({})", terms.join(" + "))
        } else {
            // A carry against a constant, beside high digits of the same sum under
            // constants that differ above the digit, and of a product shifted into place.
            let at = 2 * k;
            let y = sym(&mut g);
            let (c1, c2, t) = (g.below(1 << w), g.below(1 << at), 1 + g.below(at));
            let v = match g.below(3) {
                0 => format!("({x} + {y})"),
                1 => format!("({x} * {})", g.below(1 << w) | 1),
                _ => format!("({x} * {} << {t})", g.below(1 << (w - t))),
            };
            let high = |e: &str| format!("extract<{at}, {j}>({e})");
            let d = c1.wrapping_sub(c2) & full;
            let mut src = format!(
                "zext<{j}>(({v} + {c1} & {mask2}) <u {c2}) + {}",
                high(&format!("({v} + {})", near(&mut g, d)))
            );
            if g.chance(1, 2) {
                let up = (d + (g.below(4) << at)) & full;
                src.push_str(&format!(" - {}", high(&format!("({v} + {up})"))));
            }
            if g.chance(1, 2) {
                let c = g.below(1 << (w - t));
                let e = format!("({y} * {} + {})", c << t, g.below(1 << t));
                src.push_str(&format!(" + {}", high(&e)));
                if at - t + j <= w {
                    src.push_str(&format!(
                        " - extract<{}, {j}>({y} * {})",
                        at - t,
                        near(&mut g, c)
                    ));
                }
            }
            src
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 900, "{changed}");
}

/// Limb arithmetic: a limb's sum read by users that have no observer in common below the root
/// (a product and a sum, the arms of a `select`), each through a truncation of its own. No
/// user's rewrite pays while the others hold the sum; at the root the sum is read on the bits
/// that reach the result, by every user at once (see `demanded::whole`).
#[cfg(feature = "prove")]
#[test]
fn limb_root_fixtures() {
    let eng = deobfuscator();
    // The high limb of `x + y` with a third digit: no slice of one word.
    let limb = "((x >>u 18) + (y >>u 18) + (z >>u 18) \
                + zext<32>((x + y & 0x3ffff) <u (x & 0x3ffff)))";
    // The carry of a product's digits beside a product nothing else reads narrowed: the
    // reading keeps the sum's own terms as they are.
    let (d, e) = ("(x & 0x1fff)", "((y >>u 13) & 0x1fff)");
    let (p, q) = (format!("({d} * (y & 0x1fff))"), format!("({d} * {e})"));
    let high = format!(
        "(({q} >>u 13) + zext<32>((({p} + ({q} << 13)) & 0x3ffffff) <u {p}) \
         + (x >>u 7) * (y >>u 9))"
    );
    for (src, w, want) in [
        // Read under 14 bits and under 7, by a product each.
        (
            format!("trunc<14>({limb}) * v + zext<14>(trunc<7>({limb})) * u"),
            14,
            "let %0 = extract<18, 14>(z) + extract<18, 14>(x + y);\n%0 * v + (%0 & 127) * u",
        ),
        // By the arms of a `select`.
        (
            format!("select(c:1, trunc<14>({limb}), zext<14>(trunc<7>({limb})))"),
            14,
            "let %0 = extract<18, 14>(z) + extract<18, 14>(x + y);\nselect(c, %0, %0 & 127)",
        ),
        // At the register's width, under 6 bits and under 3.
        (
            format!("zext<32>(trunc<6>({high})) * v + (zext<32>(trunc<3>({high})) ^ u)"),
            32,
            "let %0 = x & 8191;\n\
             let %1 = (x >>u 7) * (y >>u 9) \
             + zext<32>(extract<26, 6>(%0 * (y & 8191) + (%0 * (y >>u 13 & 8191) << 13)));\n\
             (%1 & 63) * v + (%1 & 7 ^ u)",
        ),
    ] {
        assert_eq!(simplify(&eng, &src, w), want, "{src}");
    }
}

/// Limb arithmetic: a sum of high digits, a carry and sometimes a term of its own, read by
/// two users through a truncation, a mask or a shift each, under a root that is no observer
/// (a sum, a product, a `select`, a comparison of them), stays equal to itself: exhaustively.
/// (The sum is read at the root on the bits that reach the result.)
#[cfg(feature = "prove")]
#[test]
fn limb_roots_are_sound() {
    let eng = deobfuscator();
    let mut g = Rng(0x11b5_0005);
    let mut rng = Rng(81);
    let mut changed = 0;
    for i in 0..1200 {
        let (w, syms): (u64, &[&str]) = if i % 3 == 0 {
            (4, &["a", "b", "c"])
        } else {
            (6, &["a", "b"])
        };
        let sym = |g: &mut Rng| format!("{}:{w}", syms[g.below(syms.len() as u64) as usize]);
        let value = |g: &mut Rng| {
            let (x, y) = (sym(g), sym(g));
            match g.below(4) {
                0 => format!("({x} + {y})"),
                1 => format!("({x} * {})", g.below(1 << w)),
                2 => format!("({x} ^ {y})"),
                _ => x,
            }
        };
        let k = 1 + g.below(w - 1);
        let mask = (1u64 << k) - 1;
        let (p, q) = (value(&mut g), value(&mut g));
        let (cp, cq) = if g.chance(3, 4) {
            (format!("({p} + {q})"), p.clone())
        } else {
            (value(&mut g), value(&mut g))
        };
        let sign = if g.chance(1, 4) { '-' } else { '+' };
        // A term the carry's digits meet nothing of.
        let own = match g.below(4) {
            0 => format!(" + {} * {}", value(&mut g), value(&mut g)),
            1 => format!(" - ({} >>u {})", value(&mut g), g.below(w)),
            _ => String::new(),
        };
        let s = format!(
            "(({p} >>u {k}) + ({q} >>u {k}) {sign} \
             zext<{w}>(({cp} & {mask}) <u ({cq} & {mask})){own})"
        );
        let reader = |g: &mut Rng| match g.below(6) {
            0 => format!("zext<{w}>(trunc<{}>({s}))", 1 + g.below(w)),
            1 => format!("({s} & {})", g.below(1 << w)),
            2 => format!("({s} << {})", g.below(w)),
            3 => format!("({s} + {})", g.below(1 << w)),
            4 => format!("zext<{w}>(extract<{}, 1>({s}))", g.below(w)),
            _ => format!(
                "concat(trunc<{}>({s}), extract<{}, 1>({p}))",
                w - 1,
                g.below(w)
            ),
        };
        let (r1, r2) = (reader(&mut g), reader(&mut g));
        let v = sym(&mut g);
        let src = match g.below(7) {
            0 => format!("{r1} * {v} + {r2}"),
            1 => format!("select(t:1, {r1}, {r2})"),
            2 => format!("select({r1} <u {v}, {r2}, {v})"),
            3 => format!("{r1} - ({r2} ^ {v})"),
            4 => format!("({r1} << 1) + ({r2} >>u 1)"),
            5 => format!("zext<{w}>({r1} == {r2}) + {r1}"),
            _ => format!("select(t:1, {r1}, {v}) * {r2}"),
        };
        let mut cx = Context::new();
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w as u16).unwrap()))
            .unwrap_or_else(|err| panic!("{src}: {err}"));
        let out = checked(&eng, &mut cx, e);
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 800, "{changed}");
}

/// Limb arithmetic: comparisons of digits held in wider registers, and their borrow tests.
#[test]
fn limb_compare_fixtures() {
    let eng = Engine::standard();
    for (src, want) in [
        // Both sides fit in 21 bits: compared there, the masks gone.
        (
            "(x & 0x1fffff) <u (y & 0x1fffff)",
            "trunc<21>(x) <u trunc<21>(y)",
        ),
        (
            "(x & 0x1fffff) == (y & 0x1fffff)",
            "trunc<21>(y) == trunc<21>(x)",
        ),
        // A signed order of values whose sign bits are known zero is the unsigned one.
        (
            "(x & 0x1fffff) <s (y & 0x1fffff)",
            "trunc<21>(x) <u trunc<21>(y)",
        ),
        // A digit shared by two comparisons holds neither back.
        (
            "zext<32>((trunc<32>(y) & 0x3fff) <u (trunc<32>(z) & 0x3fff)) \
             + zext<32>((trunc<32>(y) & 0x3fff) <u (trunc<32>(x) & 0x3fff))",
            "let %0 = trunc<14>(y);\nzext<32>(%0 <u trunc<14>(z)) + zext<32>(%0 <u trunc<14>(x))",
        ),
        // The borrow test `~((b - a == 0) | (b <u a))` is `a <u b`, also where the difference
        // is spelled with a negation, and where that negation is used again.
        (
            "sext<32>(~((-(trunc<32>(x) & 0x3fff) + (trunc<32>(y) & 0x3fff) == 0) \
             | ((trunc<32>(y) & 0x3fff) <u (trunc<32>(x) & 0x3fff))))",
            "sext<32>(trunc<14>(x) <u trunc<14>(y))",
        ),
        (
            "zext<64>(~((-(x & 0x3fff) + (y & 0x3fff) == 0) | ((y & 0x3fff) <u (x & 0x3fff)))) \
             + -(x & 0x3fff)",
            "let %0 = x & 16383;\nzext<64>(%0 <u y & 16383) - %0",
        ),
        ("-x + y == 0", "x == y"),
        ("-x + y != 0", "x != y"),
        ("trunc<14>(x - y) == 0", "trunc<14>(x) == trunc<14>(y)"),
        ("trunc<14>(x - y) != 0", "trunc<14>(x) != trunc<14>(y)"),
    ] {
        assert_eq!(simplify(&eng, src, 64), want, "{src}");
    }
}

#[test]
fn order_bit_subset_fixtures() {
    let eng = Engine::standard();
    for (src, want) in [
        // Through truncations and extractions of a meet.
        ("trunc<16>(a) & 5 <u trunc<16>(~b & (a & 5))", "0:1"),
        (
            "extract<16, 16>(y) & 16389 <u extract<16, 16>(~x & (y & 0x140050000))",
            "0:1",
        ),
        (
            "zext<16>(extract<32, 1>(y)) <u extract<32, 16>(~x & (y & 0x140050000))",
            "0:1",
        ),
        ("trunc<16>(x & y) <=u trunc<16>(x)", "1:1"),
        // A lane minimum of a value and its meet with another is the meet.
        (
            "select(trunc<16>(x) <u trunc<16>(x & y), trunc<16>(x), trunc<16>(x & y))",
            "trunc<16>(x & y)",
        ),
        // Undecided where a bit of the mask escapes the window, or equality is possible (here
        // compared at the two bits both sides fit in).
        (
            "zext<16>(extract<32, 1>(y)) <u extract<32, 16>(~x & (y & 0x340050000))",
            "zext<2>(extract<32, 1>(y)) <u ~extract<32, 2>(x) & extract<32, 2>(y)",
        ),
        (
            "trunc<16>(x) <u trunc<16>(x | y)",
            "trunc<16>(x) <u trunc<16>(x | y)",
        ),
    ] {
        assert_eq!(simplify(&eng, src, 64), want, "{src}");
    }
}

/// `sext(c)` and `zext(c)` of a 1-bit `c` in one sum are one atom: sound (exhaustively), and
/// `zext(c) + sext(c)` cancels. (Not checked for idempotence: the linear pass alone was not
/// idempotent on these sums before either; the engine's rounds settle them.)
#[test]
fn linear_merges_both_readings_of_a_condition() {
    let eng = engine(vec![Phase::Linear]);
    let mut g = generator(0x5e_c71);
    let mut rng = Rng(24);
    let mut changed = 0;
    for _ in 0..1500 {
        let mut cx = Context::new();
        let w = 2 + g.rng.below(4) as u16;
        let width = Width::new(w).unwrap();
        let conds: Vec<Expr> = (0..2)
            .map(|k| cx.symbol(["p", "q"][k], Width::W1).unwrap())
            .collect();
        let mut e = cx.symbol("x", width).unwrap();
        for _ in 0..1 + g.rng.below(4) {
            let c = conds[g.rng.below(2) as usize];
            let t = if g.rng.chance(1, 2) {
                cx.zext(c, width).unwrap()
            } else {
                cx.sext(c, width).unwrap()
            };
            let k = cx.constant(&g.constant(w)).unwrap();
            let t = if g.rng.chance(1, 2) {
                cx.bin(BinOp::Mul, t, k).unwrap()
            } else {
                t
            };
            let op = [BinOp::Add, BinOp::Sub][g.rng.below(2) as usize];
            e = cx.bin(op, e, t).unwrap();
        }
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
    }
    assert!(changed > 300, "{changed}");
    let std = Engine::standard();
    let mut cx = Context::new();
    let c = cx.symbol("c", Width::W1).unwrap();
    let (z, s) = (
        cx.zext(c, Width::W64).unwrap(),
        cx.sext(c, Width::W64).unwrap(),
    );
    let e = cx.bin(BinOp::Add, z, s).unwrap();
    let r = std.simplify(&mut cx, e).unwrap().expr;
    assert_eq!(cx.display(r).to_string(), "0:64");
    assert_eq!(
        simplify(
            &std,
            "~x + zext<64>(trunc<16>(x) != -1) + sext<64>(trunc<16>(x) != -1)",
            64
        ),
        "~x"
    );
    // A lone `sext` stays: rewriting it to `−zext` would not be smaller.
    let p = cx.sext(c, Width::W64).unwrap();
    let five = cx
        .constant(&BitVec::wrapping_from_u64(Width::W64, 5))
        .unwrap();
    let e = cx.bin(BinOp::Add, p, five).unwrap();
    assert_eq!(std.simplify(&mut cx, e).unwrap().expr, e);
}

/// A parallel-prefix adder (or, with `sub`, subtractor) of `x` and `y` with its first `levels`
/// levels (shifts 1, 2, 4, …; a network of `w` bits needs `log2(w)`, see [`full_levels`]);
/// `shift` overrides some levels' shifts and `extra` is xor-ed into the result.
#[cfg(feature = "prove")]
fn prefix_network(sub: bool, levels: usize, shift: &[(usize, u32)], extra: &str) -> String {
    let mut s = String::from("let s = x ^ y; ");
    s += if sub {
        "let p0 = ~s; let g0 = ~x & y; "
    } else {
        "let p0 = s; let g0 = x & y; "
    };
    for k in 0..levels {
        let sh = shift
            .iter()
            .find(|&&(l, _)| l == k)
            .map_or(1u32 << k, |&(_, v)| v);
        s += &format!(
            "let g{n} = g{k} | (p{k} & (g{k} << {sh})); let p{n} = p{k} & (p{k} << {sh}); ",
            n = k + 1
        );
    }
    s += &format!("s ^ (g{levels} << 1){extra}");
    s
}

#[cfg(feature = "prove")]
fn full_levels(w: u16) -> usize {
    (u16::BITS - (w - 1).leading_zeros()) as usize
}

#[cfg(feature = "prove")]
fn deobfuscator() -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .verify(Verify::strict())
        .build()
        .unwrap()
}

/// `e` simplified by `eng`, which verifies strictly: no candidate may have been rejected. A
/// pass that builds a candidate unequal to its node is caught by the verifier, the result
/// stays equal, and a test that compared results alone would take the pass for sound.
#[cfg(feature = "prove")]
fn checked(eng: &Engine, cx: &mut Context, e: Expr) -> crate::engine::RootOutcome {
    let out = eng.run(cx, &[e], Run::default()).unwrap();
    assert_eq!(out.stats.rejected, 0, "{}", cx.display(e));
    out.roots[0]
}

#[cfg(feature = "prove")]
#[test]
fn carries_recovers_prefix_adders_and_subtractors() {
    let eng = deobfuscator();
    for w in [8u16, 13, 16, 32, 33, 64] {
        for (sub, want) in [(false, "x + y"), (true, "x - y")] {
            let mut cx = Context::new();
            let src = prefix_network(sub, full_levels(w), &[], "");
            let e = cx
                .parse(&src, &ParseOptions::width(Width::new(w).unwrap()))
                .unwrap();
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            assert_eq!(
                cx.display(out.roots[0].expr).to_string(),
                want,
                "{w} bits: {src}"
            );
            assert_eq!(out.roots[0].end, End::Completed);
            let c = out.stats.passes["carries"];
            assert_eq!((c.proved, c.changed), (1, 1), "{w} bits: {c:?}");
        }
    }
}

/// A ripple chain adding `a` and `b` (texts) at `w` bits: `w` half additions, each sum
/// `a ^ b` and carry `(a & b) << 1`.
#[cfg(feature = "prove")]
fn ripple_sum(a: &str, b: &str, w: u16) -> String {
    let mut s = format!("let a0 = {a}; let b0 = {b}; ");
    for k in 0..w {
        s += &format!(
            "let a{n} = a{k} ^ b{k}; let b{n} = (a{k} & b{k}) << 1; ",
            n = k + 1
        );
    }
    s + &format!("a{w}")
}

#[cfg(feature = "prove")]
#[test]
fn carries_recovers_ripple_chains_constants_and_three_atoms() {
    let eng = deobfuscator();
    let same = |src: &str, want: &str, w: u16| -> crate::engine::PassCounts {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(
            out.roots[0].expr,
            want,
            "{w} bits: {}",
            cx.display(out.roots[0].expr)
        );
        out.stats.passes["carries"]
    };
    same(&ripple_sum("x", "y", 32), "x + y", 32);
    // With a constant, long carries happen only near `−K`: points there keep the partial sums
    // from the prover.
    let c = same(&ripple_sum("x", "0x55555555", 32), "x + 0x55555555", 32);
    assert!(c.refuted <= 1, "{c:?}");
    // Three atoms: a carry-save step, then a prefix adder of its sum and carries.
    let mut s = String::from(
        "let u = x ^ y ^ z; let v = ((x & y) | (x & z) | (y & z)) << 1; \
         let s = u ^ v; let p0 = s; let g0 = u & v; ",
    );
    for k in 0..4 {
        s += &format!(
            "let g{n} = g{k} | (p{k} & (g{k} << {sh})); let p{n} = p{k} & (p{k} << {sh}); ",
            n = k + 1,
            sh = 1 << k
        );
    }
    s += "s ^ (g4 << 1)";
    same(&s, "x + y + z", 16);
}

#[cfg(feature = "prove")]
#[test]
#[ignore = "heavy: a proof to the pass's caps; run with --release -- --ignored"]
fn carries_asks_a_region_past_its_caps_once() {
    // A 48-bit ripple chain is past the proof's caps; the region holding it, its double, is
    // larger still, and is not asked.
    let o = ParseOptions::width(Width::new(48).unwrap());
    let src = format!("{} << 1", ripple_sum("x", "y", 48));
    let mut rng = Rng(48);
    let mut cx = Context::new();
    let e = cx.parse(&src, &o).unwrap();
    let out = engine(vec![Phase::Carries])
        .run(&mut cx, &[e], Run::default())
        .unwrap();
    assert_eq!(out.roots[0].expr, e);
    let c = out.stats.passes["carries"];
    assert_eq!((c.proved, c.unknown), (0, 1), "{c:?}");
    // With the other passes, the demanded-bits pass rewrites the chain the shift reads only
    // the low 47 bits of (146 nodes to 143): a chain of its own, past the caps too, asked once.
    let mut cx = Context::new();
    let e = cx.parse(&src, &o).unwrap();
    let out = deobfuscator().run(&mut cx, &[e], Run::default()).unwrap();
    assert!(equivalent(&mut cx, e, out.roots[0].expr, &mut rng));
    assert_eq!(out.stats.passes["demanded"].changed, 1);
    let c = out.stats.passes["carries"];
    assert_eq!((c.proved, c.unknown), (0, 2), "{c:?}");
}

#[cfg(feature = "prove")]
#[test]
fn carries_leaves_a_prefix_tree_missing_its_last_level() {
    let eng = deobfuscator();
    let mut rng = Rng(7);
    for w in [8u16, 16, 32, 64] {
        for sub in [false, true] {
            let mut cx = Context::new();
            let o = ParseOptions::width(Width::new(w).unwrap());
            let e = cx
                .parse(&prefix_network(sub, full_levels(w) - 1, &[], ""), &o)
                .unwrap();
            let sum = cx.parse(if sub { "x - y" } else { "x + y" }, &o).unwrap();
            // Truncated, it is not the sum.
            assert!(matches!(
                crate::prove::equal(&mut cx, e, sum, &crate::prove::Config::default()).unwrap(),
                crate::prove::Outcome::Refuted(_)
            ));
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            let r = out.roots[0].expr;
            assert_ne!(r, sum, "{w} bits");
            assert!(equivalent(&mut cx, e, r, &mut rng), "{w} bits");
            let c = out.stats.passes["carries"];
            assert_eq!((c.proved, c.changed), (0, 0), "{w} bits: {c:?}");
        }
    }
}

#[cfg(feature = "prove")]
#[test]
fn carries_refutes_a_network_wrong_only_at_rare_inputs() {
    // The adder xor a term that is nonzero only where `x` has 16 alternating bits under a set
    // bit of `y`: none of the pass's points has that, so only the proof tells.
    let rare: String = (0..16)
        .map(|k| match (k, k % 2) {
            (0, _) => "x".to_string(),
            (_, 0) => format!(" & (x << {k})"),
            _ => format!(" & ~(x << {k})"),
        })
        .collect();
    let eng = deobfuscator();
    let mut rng = Rng(11);
    for w in [32u16, 64] {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let src = prefix_network(false, full_levels(w), &[], &format!(" ^ ({rare} & y)"));
        let e = cx.parse(&src, &o).unwrap();
        let sum = cx.parse("x + y", &o).unwrap();
        assert!(matches!(
            crate::prove::equal(&mut cx, e, sum, &crate::prove::Config::default()).unwrap(),
            crate::prove::Outcome::Refuted(_)
        ));
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0].expr;
        assert_ne!(r, sum, "{w} bits");
        assert!(equivalent(&mut cx, e, r, &mut rng), "{w} bits");
        let c = out.stats.passes["carries"];
        // The adder inside may become `x + y`; the whole is refuted.
        assert!(c.refuted >= 1, "{w} bits: {c:?}");
    }
}

#[cfg(feature = "prove")]
#[test]
fn carries_proves_within_what_is_left() {
    let eng = deobfuscator();
    let o = ParseOptions::width(Width::W32);
    let src = prefix_network(false, 5, &[], "");
    let nodes = super::carries::MAX_AIG_NODES as u64;
    // Room for a few hundred propagations: the proof (about 100,000) stops short, and the root
    // is not final.
    let mut cx = Context::new();
    let e = cx.parse(&src, &o).unwrap();
    let short = Budget::default().with_pass_work(nodes + 4_000);
    let out = eng
        .run(&mut cx, &[e], Run::default().with_per_call(short))
        .unwrap();
    assert_ne!(cx.display(out.roots[0].expr).to_string(), "x + y");
    assert_eq!(
        out.roots[0].end,
        End::BudgetTerminated(crate::engine::Exhausted::PassWork)
    );
    assert_eq!(out.stats.passes["carries"].proved, 0);
    // Less than a capped proof's whole cost is enough for this one.
    let mut cx = Context::new();
    let e = cx.parse(&src, &o).unwrap();
    let enough = Budget::default().with_pass_work(nodes + (1 << 20));
    let out = eng
        .run(&mut cx, &[e], Run::default().with_per_call(enough))
        .unwrap();
    assert_eq!(cx.display(out.roots[0].expr).to_string(), "x + y");
}

#[cfg(feature = "prove")]
#[test]
fn carries_is_sound_on_mutated_networks() {
    // 6-bit networks (shifts 1, 2, 4), some miswired: every result is checked at every input.
    let eng = engine(vec![Phase::Carries]);
    let mut rng = Rng(0xca44);
    let o = ParseOptions::width(Width::new(6).unwrap());
    let (mut changed, mut refuted) = (0, 0);
    for _ in 0..200 {
        let sub = rng.chance(1, 2);
        let levels = 1 + rng.below(3) as usize;
        let mut shift = Vec::new();
        if rng.chance(1, 2) {
            shift.push((rng.below(levels as u64) as usize, 1 + rng.below(5) as u32));
        }
        let extra = match rng.below(4) {
            0 => " ^ (x & (x << 1) & y)",
            1 => " ^ (y << 5)",
            _ => "",
        };
        let src = prefix_network(sub, levels, &shift, extra);
        let mut cx = Context::new();
        let e = cx.parse(&src, &o).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert!(
            equivalent(&mut cx, e, out.roots[0].expr, &mut rng),
            "{src} became {}",
            cx.display(out.roots[0].expr)
        );
        let c = out.stats.passes["carries"];
        changed += c.changed;
        refuted += c.refuted;
    }
    assert!(changed > 0 && refuted > 0, "{changed} {refuted}");
}

#[cfg(feature = "prove")]
#[test]
fn carries_reads_shifts_of_one_atom_exactly() {
    // `a << k` is `2^k·a`, and 0 once the shifts reach the width: no proof needed, so none is
    // taken, and every result is equal to its input. (Inner shifts by more than 1 are their
    // own form, so the chain is read whole; `a << 1` alone becomes `a + a`.)
    let eng = engine(vec![Phase::Carries]);
    let mut rng = Rng(0x5e1f);
    for w in [8u16, 64] {
        let o = ParseOptions::width(Width::new(w).unwrap());
        for (src, want) in [
            ("(x << 2) << 3".to_string(), "x << 5".to_string()),
            ("((x << 3) << 2) << 1".into(), "x << 6".into()),
            (format!("(x << {}) << 3", w - 2), format!("0:{w}")),
            ("x << 1".into(), "x + x".into()),
        ] {
            let mut cx = Context::new();
            let e = cx.parse(&src, &o).unwrap();
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            let r = out.roots[0].expr;
            assert_eq!(cx.display(r).to_string(), want, "{w} bits: {src}");
            assert!(equivalent(&mut cx, e, r, &mut rng), "{w} bits: {src}");
            assert_eq!(out.stats.passes["carries"].proofs, 0, "{w} bits: {src}");
        }
    }
}

/// A `w`-bit sum (or difference) split at bit `k`: the low halves added at `k + 1` bits, the
/// high ones apart, plus the carry read at bit `carry` of the low sum (`k` is right; `None`
/// drops it).
#[cfg(feature = "prove")]
fn split_sum(w: u16, k: u16, sub: bool, carry: Option<u16>) -> String {
    let (h, op) = (w - k, if sub { "-" } else { "+" });
    let c = carry.map_or(String::new(), |c| {
        format!(" {op} zext<{h}>(extract<{c}, 1>(s))")
    });
    format!(
        "let s = zext<{k1}>(trunc<{k}>(x)) {op} zext<{k1}>(trunc<{k}>(y)); \
         concat(extract<{k}, {h}>(x) {op} extract<{k}, {h}>(y){c}, trunc<{k}>(s))",
        k1 = k + 1
    )
}

#[cfg(feature = "prove")]
#[test]
fn carries_recombines_sums_split_at_any_boundary() {
    let eng = engine(vec![Phase::Carries]);
    let same = |src: &str, want: &str| {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx.parse(src, &o).unwrap();
        let want = cx.parse(want, &o).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap();
        assert_eq!(out.expr, want, "{src}: got {}", cx.display(out.expr));
    };
    same(&split_sum(64, 17, false, Some(17)), "x + y");
    same(&split_sum(64, 32, false, Some(32)), "x + y");
    same(&split_sum(64, 17, true, Some(17)), "x - y");
    // The carry as the low sum's unsigned overflow.
    same(
        "let s = trunc<23>(x) + trunc<23>(y); \
         concat(extract<23, 41>(x) + extract<23, 41>(y) + zext<41>(s <u trunc<23>(x)), s)",
        "x + y",
    );
    // Without the carry, or with it read a bit too low, it is not the sum: unchanged.
    for wrong in [
        split_sum(64, 17, false, None),
        split_sum(64, 17, false, Some(16)),
    ] {
        same(&wrong, &wrong);
    }
}

#[cfg(feature = "prove")]
#[test]
fn carries_is_sound_on_split_sums() {
    // Every split point of every width from 4 to 10 bits, with the carry right, missing, or
    // read a bit too low: every result is checked, and the right ones are the sum.
    let eng = engine(vec![Phase::Carries]);
    let mut rng = Rng(0x5711);
    let mut recombined = 0;
    for w in 4u16..=10 {
        let o = ParseOptions::width(Width::new(w).unwrap());
        for k in 1..w {
            for sub in [false, true] {
                for carry in [Some(k), None, Some(k - 1)] {
                    let src = split_sum(w, k, sub, carry);
                    let mut cx = Context::new();
                    let e = cx.parse(&src, &o).unwrap();
                    let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
                    let r = out.roots[0].expr;
                    assert!(
                        equivalent(&mut cx, e, r, &mut rng),
                        "{src} became {}",
                        cx.display(r)
                    );
                    if carry == Some(k) {
                        let want = cx.parse(if sub { "x - y" } else { "x + y" }, &o).unwrap();
                        assert_eq!(r, want, "{src}: got {}", cx.display(r));
                        recombined += 1;
                    }
                }
            }
        }
    }
    assert_eq!(recombined, 2 * (3 + 4 + 5 + 6 + 7 + 8 + 9));
}

// ----- opaque constants (`mba::sweep`) -------------------------------------------

#[cfg(feature = "mba")]
mod opaque_constants {
    use super::*;
    use crate::mba::MbaConfig;

    fn simplified(src: &str, fuel: u64) -> (Context, crate::engine::Outcome) {
        let eng = Engine::builder()
            .builtin()
            .strategy(
                Strategy::deobfuscate().with_mba(MbaConfig::default().with_opaque_sweep(true)),
            )
            .build()
            .unwrap();
        let mut cx = Context::new();
        let e = cx.parse(src, &ParseOptions::width(Width::W64)).unwrap();
        let out = eng
            .run(
                &mut cx,
                &[e],
                Run::default().with_per_call(Budget::fuel(fuel)),
            )
            .unwrap();
        (cx, out)
    }

    /// A constant hidden over three values that cancel (the FNV-1a prime), then read as a hash
    /// multiplier, through a high byte and through a cast.
    const PRIME: &str = "let p4 = ~b & ~(~c & a); let p6 = ~b & ~a; let p8 = ~p6 & c; \
         let p9 = ~(~b & c) & ~a; let p10 = ~(~(~a & b) & c); let p11 = p6 & c; \
         let p12 = ~(~b & ~(~c & ~a)); let p13 = ~(a & b) & ~p6; \
         let p14 = ~(p13 & c) & ~(~c & ~p13); let p15 = ~b & a; \
         let p16 = ~(p15 & c) & ~(~c & ~p15); \
         let p = p4 * 0x666665ffffffff52 + p8 * 0x999998fffffffefb + p9 * 0x99999a00000000ae \
         + p10 * 0xcccccbfffffffea4 + p11 * 0x666665ffffffff52 + p12 * 0x333332ffffffffa9 \
         + p14 * 0x666665ffffffff52 + p16 * 0xcccccd0000000057;";

    #[test]
    fn a_chain_of_hidden_constants_folds_operands_first() {
        let src = format!(
            "{PRIME} let h = (0xcbf29ce484222325 ^ (p >>u 40)) * p; \
             let g = zext<64>(extract<8, 8>(h)) * p; \
             g + (x ^ zext<64>(trunc<32>(h) & 39))"
        );
        let (mut cx, out) = simplified(&src, 1 << 14);
        let h: u64 =
            (0xcbf2_9ce4_8422_2325u64 ^ (0x100_0000_01b3u64 >> 40)).wrapping_mul(0x100_0000_01b3);
        let g = ((h >> 8) & 0xff).wrapping_mul(0x100_0000_01b3);
        let want = cx
            .parse(
                &format!("{g:#x} + (x ^ {:#x})", h & 39),
                &ParseOptions::width(Width::W64),
            )
            .unwrap();
        assert_eq!(out.roots[0].expr, want, "{}", cx.display(out.roots[0].expr));
        assert!(out.stats.mba.opaque_proved > 0);
    }

    #[test]
    fn a_guard_that_reads_constant_at_the_samples_is_not_folded() {
        // `x == k` is false at every sample point: the sum reads as 5, and is not.
        let (mut cx, out) = simplified("zext<64>(x == 0x1234567) + 5 + (y & (z | y)) - y", 1 << 14);
        let r = out.roots[0].expr;
        assert!(cx.as_const(r).unwrap().is_none(), "{}", cx.display(r));
        let want = cx
            .parse(
                "zext<64>(x == 0x1234567) + 5",
                &ParseOptions::width(Width::W64),
            )
            .unwrap();
        assert_eq!(r, want, "{}", cx.display(r));
    }
}
