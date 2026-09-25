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

/// A random bitwise expression over up to four atoms (so some regions are over the cap).
fn bitwise_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32, atoms: u64) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 5) {
        return match g.rng.below(atoms + 2) {
            0 => cx.constant(&crate::BitVec::zero(width)).unwrap(),
            1 => cx.constant(&crate::BitVec::ones(width)).unwrap(),
            k => {
                let name = ["a", "b", "c", "d"][(k - 2) as usize];
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
        let atoms = 2 + g.rng.below(3);
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
    for i in 0..4000 {
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
    assert!(changed > 800, "{changed}");
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
            "not idempotent: {} -> {}",
            cx.display(r.expr),
            cx.display(again.roots[0].expr)
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
            "not idempotent: {} -> {}",
            cx.display(r.expr),
            cx.display(again.roots[0].expr)
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
            "not idempotent: {} -> {}",
            cx.display(r.expr),
            cx.display(again.roots[0].expr)
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
            "not idempotent: {} -> {}",
            cx.display(r.expr),
            cx.display(again.roots[0].expr)
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
            // Everything it answered was proved by the gate's own certificates.
            assert_eq!(out.stats.mba.proof_unknown, 0);
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

    /// `x + y`, through a relation between `x >> 1` and `x` that no native certificate sees (a
    /// right shift is an atom, independent of `x`).
    const NOT_NATIVE: &str = "(x >>u 1) * 2 + (x & 1) + y";

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
        // A right answer bitwright can prove itself is taken without any trust: here by the
        // degree-2 certificate.
        let (mut cx, out, _) = run(&mba_engine(Arc::new(Unproven), no_trust), NONLINEAR);
        let want = cx.parse("x + y", &ParseOptions::width(Width::W64)).unwrap();
        assert_eq!(out.roots[0].expr, want);
        assert!(out.stats.mba.certificates.sparse > 0);
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
        // At W = 8 the two variables have 16 bits: `Unproven`'s right answer, outside the
        // polynomial fragment, is proved by evaluating all 2^16 points, and that work is
        // charged.
        let eng = mba_engine(Arc::new(Unproven), MbaTrust::default());
        let o = ParseOptions::width(Width::W8);
        let mut cx = Context::new();
        let e = cx.parse(NOT_NATIVE, &o).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(out.roots[0].expr, cx.parse("x + y", &o).unwrap());
        assert!(out.stats.pass_work >= 1 << 16, "{}", out.stats.pass_work);
        assert_eq!(out.stats.mba.certificates.exhaustive, 1);
        assert_eq!(out.stats.mba.certificates.points, 1 << 16);
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
}

// ----- regressions from the M6 review --------------------------------------------------------------

#[test]
fn linear_mba_never_reads_linear_terms_as_bitwise_operands() {
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
        for _ in 0..3000 {
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
        let op = [CmpOpExt::Eq, CmpOpExt::Ne, CmpOpExt::Ult][g.rng.below(3) as usize];
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
    // Orderings are left alone.
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
