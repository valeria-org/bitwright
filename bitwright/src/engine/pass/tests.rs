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

/// `n` symbols `s0`, `s1`, … of width `w`.
fn symbols(cx: &mut Context, n: usize, w: Width) -> Vec<Expr> {
    (0..n)
        .map(|i| cx.symbol(format!("s{i}").as_str(), w).unwrap())
        .collect()
}

/// `terms` joined by `op`, left to right.
fn chain(cx: &mut Context, op: BinOp, terms: &[Expr]) -> Expr {
    terms[1..]
        .iter()
        .fold(terms[0], |e, &t| cx.bin(op, e, t).unwrap())
}

/// The symbols under `e`, and its distinct nodes.
fn size(cx: &mut Context, e: Expr) -> (usize, u32) {
    let nodes = match cx.dag_size(&[e], u32::MAX).unwrap() {
        crate::Bounded::Exact(n) | crate::Bounded::AtLeast(n) => n,
    };
    (cx.symbols_in(&[e]).unwrap().len(), nodes)
}

/// A sum over a pass's cap on terms is an atom of the forms over it, and terms still cancel
/// through it: in the linear pass's sums and in the xor pass's xors, at a width whose forms
/// are kept as words and at one over 64 bits.
#[test]
fn terms_cancel_through_sums_over_the_cap() {
    for (phase, name, add, sub, bits) in [
        (Phase::Linear, "linear", BinOp::Add, BinOp::Sub, 16),
        (Phase::Xor, "xor", BinOp::Xor, BinOp::Xor, 16),
        (Phase::Linear, "linear", BinOp::Add, BinOp::Sub, 200),
        (Phase::Xor, "xor", BinOp::Xor, BinOp::Xor, 200),
    ] {
        let eng = engine(vec![phase]);
        let w = Width::new(bits).unwrap();
        let mut rng = Rng(1);
        // One of 74 terms: the other 73 are left, as one sum.
        let mut cx = Context::new();
        let s = symbols(&mut cx, 74, w);
        let all = chain(&mut cx, add, &s);
        let e = cx.bin(sub, all, s[0]).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0].expr;
        assert!(out.stats.passes[name].atomized > 0);
        assert_eq!(size(&mut cx, r), (73, 73 + 72), "{name}");
        assert!(equivalent(&mut cx, e, r, &mut rng));
        cx.memo.clear();
        let again = eng.run(&mut cx, &[r], Run::default()).unwrap();
        assert!(!again.roots[0].changed, "{name}: not idempotent");
        // The same 70 terms in the other order: nothing is left.
        let mut cx = Context::new();
        let s = symbols(&mut cx, 70, w);
        let a = chain(&mut cx, add, &s);
        let back: Vec<Expr> = s.iter().rev().copied().collect();
        let b = chain(&mut cx, add, &back);
        let e = cx.bin(sub, a, b).unwrap();
        let zero = cx.constant_u64(w, 0).unwrap();
        assert_eq!(eng.simplify(&mut cx, e).unwrap().expr, zero, "{name}");
        // 100 of 200 terms, through three sums over the cap, one inside the other.
        let mut cx = Context::new();
        let s = symbols(&mut cx, 200, w);
        let a = chain(&mut cx, add, &s);
        let even: Vec<Expr> = s.iter().step_by(2).copied().collect();
        let b = chain(&mut cx, add, &even);
        let e = cx.bin(sub, a, b).unwrap();
        let r = eng.simplify(&mut cx, e).unwrap().expr;
        assert_eq!(size(&mut cx, r), (100, 100 + 99), "{name}");
        assert!(equivalent(&mut cx, e, r, &mut rng));
        // A sum with another use is not taken apart: its terms would be built a second time.
        let mut cx = Context::new();
        let s = symbols(&mut cx, 70, w);
        let a = chain(&mut cx, add, &s);
        let d = cx.bin(sub, a, s[0]).unwrap();
        let e = cx.bin(BinOp::Mul, d, a).unwrap();
        assert!(!eng.simplify(&mut cx, e).unwrap().changed, "{name}");
        // Over `MAX_WHOLE_TERMS` terms a sum keeps no whole form: it is an atom and no more.
        let mut cx = Context::new();
        let s = symbols(&mut cx, super::forms::MAX_WHOLE_TERMS + 76, w);
        let a = chain(&mut cx, add, &s);
        let e = cx.bin(sub, a, s[0]).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert!(!out.roots[0].changed, "{name}");
        assert_eq!(out.roots[0].end, End::Completed);
    }
}

/// Random sums and xors of hundreds of terms over a pool of symbols, built in pieces that
/// repeat terms (sums over the cap as operands of sums, scaled, masked, negated and
/// complemented): the results are equivalent, and a second run changes nothing.
#[test]
fn long_sums_are_sound_and_idempotent() {
    for (phase, linear) in [(Phase::Linear, true), (Phase::Xor, false)] {
        let eng = engine(vec![phase]);
        let mut g = generator(0x10_9500);
        let mut rng = Rng(5);
        let add = if linear { BinOp::Add } else { BinOp::Xor };
        let mut changed = 0;
        for i in 0..32 {
            let mut cx = Context::new();
            let bits = [8, 16, 64, 100][i % 4];
            let pool = symbols(
                &mut cx,
                40 + g.rng.below(200) as usize,
                Width::new(bits).unwrap(),
            );
            let mut e: Option<Expr> = None;
            for _ in 0..2 + g.rng.below(5) {
                let terms: Vec<Expr> = (0..1 + g.rng.below(150))
                    .map(|_| pool[g.rng.below(pool.len() as u64) as usize])
                    .collect();
                let mut piece = chain(&mut cx, add, &terms);
                match g.rng.below(4) {
                    0 => {
                        let k = g.constant(bits);
                        let k = cx.constant(&k).unwrap();
                        let op = if linear { BinOp::Mul } else { BinOp::And };
                        piece = cx.bin(op, piece, k).unwrap();
                    }
                    1 => {
                        let op = if linear { UnOp::Neg } else { UnOp::Not };
                        piece = cx.un(op, piece).unwrap();
                    }
                    _ => {}
                }
                e = Some(match e {
                    None => piece,
                    Some(e) if linear && g.rng.chance(1, 2) => {
                        cx.bin(BinOp::Sub, e, piece).unwrap()
                    }
                    Some(e) => cx.bin(add, e, piece).unwrap(),
                });
            }
            let e = e.unwrap();
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            let r = out.roots[0];
            assert_eq!(r.end, End::Completed);
            assert_eq!(out.stats.rejected, 0);
            assert!(equivalent(&mut cx, e, r.expr, &mut rng), "case {i}");
            changed += u64::from(r.changed);
            cx.memo.clear();
            let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
            assert!(!again.roots[0].changed, "case {i}: not idempotent");
        }
        assert!(changed > 8, "{changed}");
    }
}

/// Whole forms are read only where terms meet: a long sum of distinct terms costs what it did,
/// 36 units a node (taking each sum over the cap apart at every node above it would be 16 more).
#[test]
fn a_long_sum_of_distinct_terms_costs_what_it_did() {
    for (phase, add) in [(Phase::Linear, BinOp::Add), (Phase::Xor, BinOp::Xor)] {
        let eng = engine(vec![phase]);
        let mut cx = Context::new();
        let s = symbols(&mut cx, 4000, Width::W32);
        let e = chain(&mut cx, add, &s);
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert!(!out.roots[0].changed);
        assert!(out.stats.pass_work < 40 * 4000, "{}", out.stats.pass_work);
    }
}

/// A chain of `·`, `&` or `|` is one node however it was ordered and parenthesized, also over
/// more operands than the bitwise tables read: two writings of one chain cancel.
#[test]
fn chains_are_written_one_way() {
    for strategy in [Strategy::standard(), Strategy::deobfuscate()] {
        let eng = Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap();
        for (op, minus) in [("&", "^"), ("|", "^"), ("*", "-")] {
            for n in [3, 7, 9, 40] {
                let v: Vec<String> = (0..n).map(|i| format!("v{i}")).collect();
                let join = |v: &[String]| v.join(&format!(" {op} "));
                let back: Vec<String> = v.iter().rev().cloned().collect();
                // `v0 op (v1 op (…))`.
                let nested = back[1..]
                    .iter()
                    .fold(back[0].clone(), |e, x| format!("{x} {op} ({e})"));
                for other in [join(&back), nested] {
                    let src = format!("({}) {minus} ({other})", join(&v));
                    assert_eq!(simplify(&eng, &src, 32), "0:32", "{op} of {n}");
                }
            }
        }
        // An operand of `&` or `|` counts once, and beside its complement it decides the chain.
        for (src, want) in [
            (
                "(a & b & c & d & e & f & g & a) ^ (g & f & e & d & c & b & a)",
                "0:32",
            ),
            ("a & b & c & d & e & f & g & ~d", "0:32"),
            ("a | b | c | d | e | f | g | ~d", "-1:32"),
        ] {
            assert_eq!(simplify(&eng, src, 32), want, "{src}");
        }
        // Over `MAX_CHAIN` operands a chain is as written above the ones put in order: the
        // result is still the chain's value, and stable.
        let mut rng = Rng(7);
        for op in [BinOp::And, BinOp::Or, BinOp::Mul] {
            let mut cx = Context::new();
            let s = symbols(&mut cx, super::MAX_CHAIN + 44, Width::W32);
            let back: Vec<Expr> = s.iter().rev().copied().collect();
            let e = chain(&mut cx, op, &back);
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            let r = out.roots[0].expr;
            assert_eq!(out.roots[0].end, End::Completed);
            assert!(equivalent(&mut cx, e, r, &mut rng));
            cx.memo.clear();
            let again = eng.run(&mut cx, &[r], Run::default()).unwrap();
            assert!(!again.roots[0].changed, "{op:?}: not stable");
        }
    }
}

/// A node rebuilt over a rewrite below it will be used by every user of the node it replaced,
/// though the walk has rebuilt only some of them yet: a rewrite at one user that would leave
/// it to the others frees nothing. Here `y` is `p`; the pass that finds it then meets the chain
/// `x op (p op z)` over the rebuilt `p op z`, and putting that chain in order would build
/// `p op x` beside the `p op z` that `popcnt` keeps.
#[test]
fn a_rebuilt_node_counts_the_users_still_to_be_rebuilt() {
    for strategy in [Strategy::standard(), Strategy::deobfuscate()] {
        let eng = Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap();
        for op in ["&", "|"] {
            let mut cx = Context::new();
            let o = ParseOptions::width(Width::W32);
            let written =
                format!("let y = (p & q) | (p & ~q); let i = y {op} z; (x {op} i) ^ popcnt(i)");
            let reduced = format!("let i = p {op} z; (x {op} i) ^ popcnt(i)");
            let a = cx.parse(&written, &o).unwrap();
            let b = cx.parse(&reduced, &o).unwrap();
            let (_, nodes) = size(&mut cx, b);
            let got = eng.simplify(&mut cx, a).unwrap().expr;
            assert_eq!(size(&mut cx, got).1, nodes, "{op}: {}", cx.display(got));
        }
    }
}

/// Factoring reads a sum's terms and a term's factors from the top, and no more of them than
/// it may factor: a sum of 100 000 terms, and a product of as many factors under a sum, are
/// simplified on a stack of the size a thread gets by default. Read by recursion to the bottom
/// of the chain, each overflowed it.
#[test]
fn factoring_reads_long_sums_and_products_from_the_top() {
    let run = || {
        let eng = engine(vec![Phase::Linear]);
        for op in [BinOp::Add, BinOp::Mul] {
            let mut cx = Context::new();
            let s = symbols(&mut cx, 100_000, Width::W64);
            let mut e = chain(&mut cx, op, &s);
            if op == BinOp::Mul {
                let x = cx.symbol("x", Width::W64).unwrap();
                e = cx.bin(BinOp::Add, e, x).unwrap();
            }
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            assert_eq!(out.roots[0].end, End::Completed, "{op:?}");
        }
    };
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap();
}

/// Terms that read one condition are merged over the same spelling of it however the nodes
/// were built. A form's terms are in the order of their nodes, `Context::import` builds
/// operands right to left and the parser left to right; `zext(c) - zext(~c)` is
/// `2·zext(c) - 1` or `1 - 2·zext(~c)`, and over a `1` the sum already reads only the second
/// is smaller than it. Merged over the first term, the sum was left as written or not by the
/// order its nodes were built in, so a result changed again once imported.
#[test]
fn conditions_merge_whatever_the_order_of_construction() {
    for strategy in [Strategy::standard(), Strategy::deobfuscate()] {
        let eng = Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap();
        for src in [
            "let a = udiv(1, x); zext<8>(x <=s a) - zext<8>(a <s x)",
            "let a = udiv(1, x); zext<8>(a <s x) - zext<8>(x <=s a)",
            "let a = udiv(1, x); zext<8>(x <u a) - zext<8>(a <=u x)",
            "let a = udiv(1, x); zext<8>(x != a) - zext<8>(x == a)",
        ] {
            let mut parsed = Context::new();
            let e = parsed.parse(src, &ParseOptions::width(Width::W8)).unwrap();
            let mut imported = Context::new();
            let i = imported.import(&parsed, &[e]).unwrap()[0];
            let (e, i) = (
                eng.simplify(&mut parsed, e).unwrap().expr,
                eng.simplify(&mut imported, i).unwrap().expr,
            );
            assert_eq!(
                parsed.display(e).to_string(),
                imported.display(i).to_string(),
                "{src}"
            );
        }
    }
}

/// A pass tries several candidates at a node, and one declined only because a part of the node
/// has another user is declined for now: the node's result is not final, whichever candidate
/// it was. The linear pass tries a case split on a condition mask first; of these two inputs
/// it declined the split of `sext(b) + 2^31 ^ 2^31` and of `concat(a, 7) - (sext(c) << 2)`
/// while the sum had another user, then remembered the node as final by its last candidate
/// alone, and the other user went. So the result changed again in a context without that
/// memory.
#[test]
fn a_candidate_declined_for_sharing_is_decided_again() {
    // (A symbol's width at its first use: `b:1`.)
    let cases = [
        (
            32,
            "let %0 = sext<32>(b:1); let %1 = %0 + 0x80000000; \
             concat(trunc<17>(~(sext<32>(a:4) ^ sext<32>(extract<25, 1>(select((%1 ^ 0x80000000) \
             & (%1 ^ %0) <s 0, select(%0 <s 0, 0x80000000:32, 0x7fffffff), %1))))), \
             extract<7, 15>(zext<32>(b) * -1))",
        ),
        (
            7,
            "let %0 = sext<7>(a:3); let %1 = sext<7>(udiv(%0, 7) * %0 != %0 << 4) << 2; \
             let %2 = concat(a, 7:4); let %3 = %2 - %1; \
             let %4 = smulhi((concat(-1:4, a) << 4) - select((%1 ^ %2) & (%3 ^ %2) <s 0, \
             select(%2 <s 0, -64:7, 63), %3), concat(a, -1:4)); \
             zext<7>((%0 - %4 ^ %0) & (%4 ^ %0) <s 0)",
        ),
    ];
    for strategy in [
        Strategy::standard(),
        Strategy::decompile(),
        Strategy::deobfuscate(),
    ] {
        let eng = Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap();
        for (width, src) in cases {
            let mut cx = Context::new();
            let e = cx
                .parse(src, &ParseOptions::width(Width::new(width).unwrap()))
                .unwrap();
            let r = eng.simplify(&mut cx, e).unwrap().expr;
            let mut fresh = Context::new();
            let again = fresh.import(&cx, &[r]).unwrap()[0];
            let out = eng.run(&mut fresh, &[again], Run::default()).unwrap();
            assert!(
                !out.roots[0].changed,
                "{} became {}",
                cx.display(r),
                fresh.display(out.roots[0].expr)
            );
        }
    }
}

/// Under `(e << k) | s` nested thousands of times only the last levels reach the result: the
/// ones a shift has moved out of the word are dropped. The walk is operands first, and each of
/// those levels was simplified under the mask of the level above before the walk reached the
/// top, a window of levels rebuilt at every one (3000 levels: 6 s and 126 655 nodes built).
/// The node at the top is asked first, and the levels out of its reach are not walked.
#[test]
fn a_deep_chain_of_shifts_is_asked_at_its_top() {
    for strategy in [Strategy::standard(), Strategy::deobfuscate()] {
        let eng = Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap();
        let mut cx = Context::new();
        let n = 3000;
        let s = symbols(&mut cx, n, Width::W64);
        let mut e = s[0];
        for (i, &t) in s.iter().enumerate().skip(1) {
            let k = cx.constant_u64(Width::W64, 1 + i as u64 % 3).unwrap();
            let shifted = cx.bin(BinOp::Shl, e, k).unwrap();
            e = cx.bin(BinOp::Or, shifted, t).unwrap();
        }
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(r.end, End::Completed);
        for k in 0..8u64 {
            let env = FnEnv(|key: &crate::SymbolKey, w| {
                let h = format!("{key:?}")
                    .bytes()
                    .fold(k, |h, c| (h ^ u64::from(c)).wrapping_mul(0x100_0000_01b3));
                Some(BitVec::wrapping_from_u64(w, h))
            });
            let v = cx.eval(&[e, r.expr], &env).unwrap();
            assert_eq!(v[0], v[1]);
        }
        // 64 bits at one to three a level: 33 levels at most are read.
        let (read, nodes) = size(&mut cx, r.expr);
        assert!(read <= 34 && nodes < 110, "{read} symbols, {nodes} nodes");
        let built = out.stats.new_nodes;
        assert!(built < 10_000, "{built} nodes built");
    }
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
    // A truncation's values are the value's, a copy for each value of the bits dropped.
    same("(3 <u trunc<7>(x)) & (x <u 100)", "x - 4 <=u 95", 8);
    same("(trunc<7>(x) == 5) & (x <s 0)", "x == -123", 8);
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
        // A truncation of `x`, compared at its own width.
        if w > 1 && g.rng.chance(1, 6) {
            let j = 1 + g.rng.below(u64::from(w) - 1) as u16;
            let t = cx.trunc(x, Width::new(j).unwrap()).unwrap();
            let op = CmpOpExt::ALL[g.rng.below(10) as usize];
            let c = g.constant(j);
            let c = cx.constant(&c).unwrap();
            return if g.rng.chance(1, 2) {
                cx.cmp(op, t, c).unwrap()
            } else {
                cx.cmp(op, c, t).unwrap()
            };
        }
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

/// The residues compute with values of at most 128 bits, so an extension or a concatenation
/// wider than that is a leaf to them, whatever it reads: cut to 128 bits, `sext<257>(x)` of a
/// negative `x` was a large positive value, and `sext<257>(t·t) <=s sext<257>(x)` true.
#[test]
fn residues_read_no_value_over_128_bits() {
    use crate::{Query, Truth};
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::new(3).unwrap());
    for (a, b) in [
        ("let t = sext<33>(x); sext<257>(t * t)", "sext<257>(x)"),
        ("let t = sext<33>(x); zext<129>(t * t)", "sext<129>(x)"),
        ("let t = sext<33>(x); sext<512>(t * t)", "zext<512>(x)"),
        (
            "let t = sext<100>(x); concat(t * t, t)",
            "concat(sext<100>(x), zext<100>(x))",
        ),
    ] {
        let (a, b) = (cx.parse(a, &o).unwrap(), cx.parse(b, &o).unwrap());
        // Every value of `x`: what a proof says must hold at all of them.
        let values: Vec<Vec<BitVec>> = (0..8u64)
            .map(|v| {
                let x = BitVec::wrapping_from_u64(Width::new(3).unwrap(), v);
                cx.eval(&[a, b], &FnEnv(|_: &crate::SymbolKey, _| Some(x)))
                    .unwrap()
            })
            .collect();
        for op in CmpOpExt::ALL {
            let truth = cx.prove(Query::Cmp(op, a, b)).unwrap();
            if truth == Truth::Unknown {
                continue;
            }
            for v in &values {
                assert_eq!(
                    BitVec::apply_cmp(op, &v[0], &v[1]).unwrap(),
                    truth == Truth::True,
                    "`{}` {op:?} `{}` proved {truth:?}",
                    cx.display(a),
                    cx.display(b)
                );
            }
        }
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
        assert_eq!(Budget::fuel(1000).mba_steps, 4000);
        assert_eq!(Budget::default().mba_steps, 1 << 24);
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
/// doubles as `a << 1`, starts a sum of subtractions from its constant or a product by a
/// negative coefficient, reads `concat(trunc(x), c)` as `x·2^|c| + c`, and a constant always
/// replaces what it folds.
#[test]
fn linear_emissions() {
    let eng = engine(vec![Phase::Linear]);
    for (src, want) in [
        ("-x - 1", "~x"),
        ("(y << 2) + 4", "~y * -4"),
        ("-2 * y - 2", "y * -2 - 2"),
        ("2 * x + y", "x * 2 + y"),
        ("5 - 3 * x", "5 - x * 3"),
        ("-(y * 3) - z * 5", "y * -3 - z * 5"),
        ("concat(trunc<62>(y), 3:2) - 6 * y - 5", "~y << 1"),
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
        // limb is found as the slice of the word and proved. (The word is left as the handler
        // spells its XOR with a constant, `x + c - 2·(x & c)` with the constants folded.)
        (
            three,
            32,
            "extract<24, 8>(w + 0x7e15514f + (w + 0x2c51a7e3 & 0x51c3a96c) * -2)",
        ),
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
        // `x` (it was taken for one). It is the slice less that carry (the words pass).
        (
            "extract<14, 16>(x - zext<32>(a:14) - zext<32>(b:14)) \
             + zext<16>(trunc<14>(x) <u (a:14 + b:14))"
                .into(),
            32,
            "extract<14, 16>(x) - zext<16>(extract<14, 1>(zext<15>(b) + zext<15>(a)))",
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
        let out = eng.simplify(&mut cx, e).unwrap();
        assert!(
            equivalent(&mut cx, e, out.expr, &mut rng),
            "{src} vs {}",
            cx.display(out.expr)
        );
        changed += u64::from(out.changed);
    }
    assert!(changed > 600, "{changed}");
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
    // own form, so the chain is read whole; `a << 1` alone is left as it is.)
    let eng = engine(vec![Phase::Carries]);
    let mut rng = Rng(0x5e1f);
    for w in [8u16, 64] {
        let o = ParseOptions::width(Width::new(w).unwrap());
        for (src, want) in [
            ("(x << 2) << 3".to_string(), "x << 5".to_string()),
            ("((x << 3) << 2) << 1".into(), "x << 6".into()),
            (format!("(x << {}) << 3", w - 2), format!("0:{w}")),
            ("x << 1".into(), "x << 1".into()),
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

/// The SWAR population count of `v` at `w` bits (Hacker's Delight), with the pair mask `m1`.
#[cfg(feature = "prove")]
fn swar(w: u16, v: &str, m1: u64) -> String {
    let ones = u64::MAX >> (64 - w);
    format!(
        "let a = {v} - (({v} >>u 1) & {m1:#x}); let b = (a & {:#x}) + ((a >>u 2) & {:#x}); \
         let c = (b + (b >>u 4)) & {:#x}; (c * {:#x}) >>u {}",
        ones / 5,
        ones / 5,
        ones / 17,
        ones / 255,
        w - 8
    )
}

#[cfg(feature = "prove")]
#[test]
fn carries_recognizes_bit_counts() {
    let eng = engine(vec![Phase::Carries]);
    let mut rng = Rng(0xb17c);
    for w in [16u16, 32, 64] {
        let o = ParseOptions::width(Width::new(w).unwrap());
        let ones = u64::MAX >> (64 - w);
        // Ones above the highest set bit: the smear, counted, is the leading zeros.
        let mut smear = String::from("let s0 = x; ");
        let mut k = 0;
        while 1u32 << k < u32::from(w) {
            smear += &format!(
                "let s{n} = s{k} | (s{k} >>u {sh}); ",
                n = k + 1,
                sh = 1u32 << k
            );
            k += 1;
        }
        let clz = format!("{smear}let v = ~s{k}; {}", swar(w, "v", ones / 3));
        let ctz = format!("let v = (x & -x) - 1; {}", swar(w, "v", ones / 3));
        for (src, want) in [
            (swar(w, "x", ones / 3), "popcnt(x)"),
            (clz, "clz(x)"),
            (ctz, "ctz(x)"),
            // A wrong pair mask: no count, and left as it was.
            (swar(w, "x", ones / 3 - 4), ""),
        ] {
            let mut cx = Context::new();
            let e = cx.parse(&src, &o).unwrap();
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            let r = out.roots[0].expr;
            assert!(equivalent(&mut cx, e, r, &mut rng), "{w} bits: {src}");
            if want.is_empty() {
                assert_eq!(r, e, "{w} bits: {src} became {}", cx.display(r));
            } else {
                let want = cx.parse(want, &o).unwrap();
                assert_eq!(r, want, "{w} bits: {src} became {}", cx.display(r));
            }
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
