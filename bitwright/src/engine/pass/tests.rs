//! Pass tests: soundness (exhaustive at small widths, sampled wide), canonical results on
//! masking fixtures, idempotence, caps, and the commit rule.

use crate::engine::tests::{equivalent, generator};
use crate::engine::{Budget, End, Engine, Hooks, Phase, Run, Strategy, Verify};
use crate::testutil::{Gen, Rng};
use crate::{BinOp, Context, Expr, ParseOptions, UnOp, Width};

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

    /// Right except at one point no sample reaches: `x + y + [x == K]`.
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
            let mut m = MbaExpr::new(p.vars().to_vec());
            let x = m.push(MOp::Var(0), &[]).unwrap();
            let y = m.push(MOp::Var(1), &[]).unwrap();
            let s = m.push(MOp::Add, &[x, y]).unwrap();
            let k = m
                .push(
                    MOp::Const(crate::BitVec::wrapping_from_u64(w, 0x1234_5678_9abc_def1)),
                    &[],
                )
                .unwrap();
            let d = m.push(MOp::Xor, &[x, k]).unwrap();
            let nd = m.push(MOp::Neg, &[d]).unwrap();
            let o = m.push(MOp::Or, &[d, nd]).unwrap();
            let nz = m.push(MOp::LShr(w.bits() - 1), &[o]).unwrap();
            let one = m.push(MOp::Const(crate::BitVec::one(w)), &[]).unwrap();
            let is_k = m.push(MOp::Sub, &[one, nz]).unwrap();
            m.push(MOp::Add, &[s, is_k]).unwrap();
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

    /// `x + y`, spelled with a degree-2 MBA identity (`x·y = (x&y)(x|y) + (x&~y)(~x&y)`), so
    /// neither the linear signature nor exhaustive evaluation (128 variable bits) can prove it.
    const NONLINEAR: &str =
        "(x ^ y) + 2 * (x & y) + x * y - (x & y) * (x | y) - (x & ~y) * (~x & y)";

    fn run(eng: &Engine, src: &str) -> (Context, crate::engine::Outcome, Expr) {
        let mut cx = Context::new();
        let e = cx.parse(src, &ParseOptions::width(Width::W64)).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        (cx, out, e)
    }

    #[test]
    fn the_gate_refutes_liars_and_honours_trust() {
        // A certified lie is refuted by the always-on sampled check.
        let (_, out, _) = run(
            &mba_engine(Arc::new(Liar), MbaTrust::default()),
            "(x ^ y) + 2 * (x & y)",
        );
        assert!(!out.roots[0].changed);
        assert!(out.stats.mba.refuted > 0);
        // An answer wrong at one unsampled point is accepted only on the backend's word, so
        // without trust in certificates it is rejected.
        let no_trust = MbaTrust {
            backend_certificates: false,
            sampled: false,
        };
        let (mut cx, out, _) = run(&mba_engine(Arc::new(Subtle), no_trust), NONLINEAR);
        let wrong = cx.parse("x + y", &ParseOptions::width(Width::W64)).unwrap();
        assert_ne!(out.roots[0].expr, wrong);
        assert!(out.stats.mba.proof_unknown > 0);
        // A right but unproven answer: rejected by default, accepted when sampling is trusted,
        // and accepted by default when a prover proves it.
        // (Where it is exactly provable, as at the linear subterm `(x ^ y) + 2 * (x & y)`, the
        // answer is taken; the whole, which needs the degree-2 identity, is not.)
        let (mut cx, out, _) = run(
            &mba_engine(Arc::new(Unproven), MbaTrust::default()),
            NONLINEAR,
        );
        let want = cx.parse("x + y", &ParseOptions::width(Width::W64)).unwrap();
        assert_ne!(out.roots[0].expr, want);
        assert!(out.stats.mba.proof_unknown > 0);
        let sampled = MbaTrust {
            sampled: true,
            ..MbaTrust::default()
        };
        let (mut cx, out, _) = run(&mba_engine(Arc::new(Unproven), sampled), NONLINEAR);
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
        let (mut cx, out, _) = run(&eng, NONLINEAR);
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
        // At W = 8 the two variables have 16 bits: `Unproven`'s right answer is proved by
        // evaluating all 2^16 points, and that work is charged.
        let eng = mba_engine(Arc::new(Unproven), MbaTrust::default());
        let o = ParseOptions::width(Width::W8);
        let mut cx = Context::new();
        let e = cx.parse(NONLINEAR, &o).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(out.roots[0].expr, cx.parse("x + y", &o).unwrap());
        assert!(out.stats.pass_work >= 1 << 16, "{}", out.stats.pass_work);
        // A pass-work budget stops it.
        let mut cx = Context::new();
        let e = cx.parse(NONLINEAR, &o).unwrap();
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

#[cfg(feature = "cobra")]
mod cobra_backend {
    use super::*;
    use crate::mba::{
        Claim, CobraSolver, MOp, MbaAnswer, MbaBudget, MbaConfig, MbaExpr, MbaSolver,
        ThreadedSolver,
    };
    use std::sync::Arc;
    use std::time::Duration;

    fn cobra_engine() -> Engine {
        Engine::builder()
            .builtin()
            .strategy(Strategy::new("mba", vec![Phase::Mba(MbaConfig::default())]))
            .mba_solver(Arc::new(CobraSolver::default()))
            .build()
            .unwrap()
    }

    #[test]
    fn cobra_solves_and_is_gated() {
        // Directly.
        let w = Width::W64;
        let mut m = MbaExpr::new(vec![w, w]);
        let x = m.push(MOp::Var(0), &[]).unwrap();
        let y = m.push(MOp::Var(1), &[]).unwrap();
        let a = m.push(MOp::And, &[x, y]).unwrap();
        let two = m
            .push(MOp::Const(crate::BitVec::from_u64(w, 2).unwrap()), &[])
            .unwrap();
        let t = m.push(MOp::Mul, &[a, two]).unwrap();
        let xo = m.push(MOp::Xor, &[x, y]).unwrap();
        m.push(MOp::Add, &[xo, t]).unwrap();
        match CobraSolver::default().solve(&m, &MbaBudget::default()) {
            MbaAnswer::Simplified { expr, claim } => {
                assert!(claim >= Claim::Proved, "{claim:?}");
                let v = [
                    crate::BitVec::from_u64(w, 7).unwrap(),
                    crate::BitVec::from_u64(w, 9).unwrap(),
                ];
                assert_eq!(expr.eval(&v).unwrap().to_u64(), Some(16));
            }
            other => panic!("{other:?}"),
        }
        // Through the engine, on a degree-2 identity bitwright cannot prove itself. (With its
        // default of requiring Lean certificates, cobra 0.4 simplifies the linear part and
        // answers "no simpler" for the rest; only soundness is asserted.)
        let eng = cobra_engine();
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let e = cx
            .parse(
                "(x ^ y) + 2 * (x & y) + x * y - (x & y) * (x | y) - (x & ~y) * (~x & y)",
                &o,
            )
            .unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let mut rng = Rng(1);
        assert!(equivalent(&mut cx, e, out.roots[0].expr, &mut rng));
        assert!(out.stats.mba.calls > 0);
    }

    #[test]
    fn cobra_through_the_engine_is_sound() {
        let eng = Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
            .mba_solver(Arc::new(CobraSolver::default()))
            .verify(Verify::strict())
            .build()
            .unwrap();
        let mut g = generator(0xc0b2a);
        let mut rng = Rng(2);
        for i in 0..150 {
            let mut cx = Context::new();
            let w = [8, 16, 32, 64][i % 4];
            let e = linear_mba_expr(&mut g, &mut cx, w);
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            assert!(equivalent(&mut cx, e, out.roots[0].expr, &mut rng));
        }
    }

    struct Slow;
    impl MbaSolver for Slow {
        fn id(&self) -> &str {
            "test.slow"
        }
        fn solve(&self, _: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
            std::thread::sleep(Duration::from_millis(200));
            MbaAnswer::NoSimpler
        }
    }

    #[test]
    fn deadlines_abandon_and_bound_late_answers() {
        let s = ThreadedSolver::new(Slow, Duration::from_millis(10), 2);
        let m = MbaExpr::new(vec![]);
        assert_eq!(s.solve(&m, &MbaBudget::default()), MbaAnswer::Exhausted);
        assert_eq!(s.solve(&m, &MbaBudget::default()), MbaAnswer::Exhausted);
        assert_eq!(s.abandoned(), 2);
        // At the cap: refused at once.
        let t0 = std::time::Instant::now();
        assert_eq!(s.solve(&m, &MbaBudget::default()), MbaAnswer::Exhausted);
        assert!(t0.elapsed() < Duration::from_millis(100));
        // The abandoned ones finish and are uncounted.
        std::thread::sleep(Duration::from_millis(400));
        assert_eq!(s.abandoned(), 0);
        // A generous deadline passes answers through.
        let s = ThreadedSolver::new(Slow, Duration::from_secs(5), 2);
        assert_eq!(s.solve(&m, &MbaBudget::default()), MbaAnswer::NoSimpler);
        assert_eq!(s.abandoned(), 0);
    }

    #[test]
    fn cobra_ids_record_what_changes_answers() {
        use crate::mba::CobraOptions;
        let id = |o: CobraOptions, v| CobraSolver::new(o, v).id().to_string();
        assert_ne!(
            id(CobraOptions::default(), 4),
            id(CobraOptions::default(), 8)
        );
        let lax = CobraOptions {
            require_lean_certificate: false,
            ..CobraOptions::default()
        };
        assert_ne!(id(lax, 8), id(CobraOptions::default(), 8));
        assert_eq!(CobraSolver::default().id(), id(CobraOptions::default(), 8));
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
            "(x & y) + (x << 1) + y",
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
