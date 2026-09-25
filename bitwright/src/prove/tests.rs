//! The prover: the SAT solver against brute force (with every proof checked), the blaster
//! against bitwright's evaluator on every operator, and proofs and refutations end to end.

use super::aig::Aig;
use super::sat::{Answer, Lit, Solver, Step};
use super::*;
use crate::testutil::{Gen, Rng};
use crate::{BinOp, CmpOpExt, ParseOptions, UnOp};

/// Random 3-SAT near the threshold, against brute force; models satisfy every clause, and
/// every unsatisfiability proof checks.
#[test]
fn the_solver_agrees_with_brute_force_and_its_proofs_check() {
    let mut rng = Rng(0x5a7);
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..400 {
        let n = 3 + rng.below(10) as u32;
        let m = (n as f64 * 4.3) as usize;
        let clauses: Vec<Vec<Lit>> = (0..m)
            .map(|_| {
                (0..3)
                    .map(|_| Lit::new(rng.below(u64::from(n)) as u32, rng.chance(1, 2)))
                    .collect()
            })
            .collect();
        let brute = (0..1u32 << n).any(|a| {
            clauses
                .iter()
                .all(|c| c.iter().any(|l| ((a >> l.var()) & 1 == 1) != l.is_neg()))
        });
        let mut s = Solver::new();
        s.log_proof();
        for _ in 0..n {
            s.new_var();
        }
        for c in &clauses {
            s.add_clause(c);
        }
        match s.solve(1_000_000) {
            Answer::Sat(model) => {
                assert!(brute);
                for c in &clauses {
                    assert!(c.iter().any(|l| model[l.var() as usize] != l.is_neg()));
                }
                sat += 1;
            }
            Answer::Unsat => {
                assert!(!brute);
                let proof = s.take_proof().unwrap();
                drup::check(&clauses, &proof).unwrap();
                unsat += 1;
            }
            Answer::Unknown => panic!("no answer"),
        }
    }
    assert!(sat > 50 && unsat > 50, "{sat} {unsat}");
}

/// Pigeonhole (n + 1 pigeons, n holes): unsatisfiable, with a checked proof; and a doctored
/// proof is refused.
#[test]
fn pigeonhole_proofs_check_and_forgeries_do_not() {
    for n in 2..=5u32 {
        let var = |p: u32, h: u32| p * n + h;
        let mut clauses: Vec<Vec<Lit>> = Vec::new();
        for p in 0..=n {
            clauses.push((0..n).map(|h| Lit::pos(var(p, h))).collect());
        }
        for h in 0..n {
            for p in 0..=n {
                for q in p + 1..=n {
                    clauses.push(vec![Lit::neg(var(p, h)), Lit::neg(var(q, h))]);
                }
            }
        }
        let mut s = Solver::new();
        s.log_proof();
        for c in &clauses {
            s.add_clause(c);
        }
        assert_eq!(s.solve(10_000_000), Answer::Unsat);
        let proof = s.take_proof().unwrap();
        drup::check(&clauses, &proof).unwrap();
        // Without the clauses of one hole, the proof falls apart.
        let weaker: Vec<Vec<Lit>> = clauses
            .iter()
            .filter(|c| c.len() != 2 || c[0].var() % n != 0)
            .cloned()
            .collect();
        assert!(drup::check(&weaker, &proof).is_err());
        // An empty proof proves nothing.
        assert!(drup::check(&clauses, &[]).is_err());
        assert!(drup::check(&clauses, &[Step::Add(Vec::new())]).is_err() || n < 2);
    }
}

/// A random expression over every bit-vector operator.
fn any_expr(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> Expr {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 4) {
        return match g.rng.below(3) {
            0 => {
                let v = g.constant(w);
                cx.constant(&v).unwrap()
            }
            1 => cx.symbol("y", width).unwrap(),
            _ => cx.symbol("x", width).unwrap(),
        };
    }
    let d = depth - 1;
    match g.rng.below(6) {
        0 => {
            let a = any_expr(g, cx, w, d);
            let mut op = UnOp::ALL[g.rng.below(UnOp::ALL.len() as u64) as usize];
            if op == UnOp::Bswap && !w.is_multiple_of(8) {
                op = UnOp::Not;
            }
            cx.un(op, a).unwrap()
        }
        1 => {
            let (a, b) = (any_expr(g, cx, w, d), any_expr(g, cx, w, d));
            let op = CmpOpExt::ALL[g.rng.below(10) as usize];
            let c = cx.cmp(op, a, b).unwrap();
            let t = any_expr(g, cx, w, d);
            let e = any_expr(g, cx, w, d);
            cx.select(c, t, e).unwrap()
        }
        2 if w > 1 => {
            let a = any_expr(g, cx, w, d);
            let lo = g.rng.below(u64::from(w)) as u16;
            let len = 1 + g.rng.below(u64::from(w - lo)) as u16;
            let x = cx.extract(a, lo, Width::new(len).unwrap()).unwrap();
            if g.rng.chance(1, 2) {
                cx.zext(x, width).unwrap()
            } else {
                cx.sext(x, width).unwrap()
            }
        }
        _ => {
            let (a, b) = (any_expr(g, cx, w, d), any_expr(g, cx, w, d));
            let op = BinOp::ALL[g.rng.below(BinOp::ALL.len() as u64) as usize];
            cx.bin(op, a, b).unwrap()
        }
    }
}

/// The circuit of every operator computes what bitwright's evaluator does, at random inputs
/// and widths (odd ones and wide ones included).
#[test]
fn blasting_agrees_with_evaluation() {
    let mut g = crate::engine::tests::generator(0xb1a5);
    let mut rng = Rng(9);
    for i in 0..600 {
        let w = [1u16, 2, 3, 5, 7, 8, 13, 16, 24, 32, 64, 65][i % 12];
        let mut cx = Context::new();
        let e = any_expr(&mut g, &mut cx, w, 3);
        let ei = cx.id(e).unwrap();
        let mut b = Blaster::new(&mut cx, usize::MAX);
        let bits = b.blast(ei).unwrap();
        let symbols = b.symbols.clone();
        let aig = core::mem::take(&mut b.g);
        drop(b);
        for _ in 0..8 {
            // Random values of the symbols; the circuit's inputs follow creation order.
            let vals: Vec<BitVec> = symbols
                .iter()
                .map(|(s, _)| {
                    let limbs: Vec<u64> = (0..2).map(|_| rng.next()).collect();
                    BitVec::wrapping_from_limbs(cx.width_of(*s), &limbs)
                })
                .collect();
            let mut input_bits: Vec<bool> = Vec::new();
            for (k, (_, bs)) in symbols.iter().enumerate() {
                for j in 0..bs.len() {
                    input_bits.push(vals[k].bit(j as u16) == Some(true));
                }
            }
            let av = aig.eval_all(|k| input_bits[k as usize]);
            let got: Vec<bool> = bits.iter().map(|&l| Aig::value(&av, l)).collect();
            let keys: Vec<SymbolKey> = symbols
                .iter()
                .map(|(s, _)| {
                    let h = cx.handle(*s);
                    let id = cx.symbol_id(h).unwrap().unwrap();
                    cx.symbol_key(id).unwrap().clone()
                })
                .collect();
            let env = crate::FnEnv(|key: &SymbolKey, _| {
                keys.iter()
                    .zip(&vals)
                    .find_map(|(k, v)| (k == key).then_some(*v))
            });
            let want = cx.eval(&[e], &env).unwrap()[0];
            let want: Vec<bool> = (0..w).map(|k| want.bit(k) == Some(true)).collect();
            assert_eq!(got, want, "W={w}: {}", cx.display(e));
        }
    }
}

/// Identities are proved (with certificates that check), non-identities refuted with a
/// counterexample that evaluates false, and assumptions are used. And without a certificate,
/// the engine settles what bit-level SAT finds hard: a 64-bit MBA product identity.
#[test]
fn proofs_and_refutations() {
    let cfg = Config::default().with_certificate(true);
    for (w, a, b) in [
        (32u16, "(x ^ y) + 2 * (x & y)", "x + y"),
        (8, "(x & y) * (x | y) + (x & ~y) * (~x & y)", "x * y"),
        (8, "udiv(x, y) * y + urem(x, y)", "x"),
        (8, "sdiv(x, y) * y + srem(x, y)", "x"),
        (13, "rotl(rotl(x, y), 13 - urem(y, 13))", "x"),
        (64, "(x << 3) >>u 3", "x & 0x1fffffffffffffff"),
        (32, "popcnt(x) + popcnt(~x)", "32"),
    ] {
        // A context per case: a symbol has one width in a context.
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let (ea, eb) = (cx.parse(a, &o).unwrap(), cx.parse(b, &o).unwrap());
        match equal(&mut cx, ea, eb, &cfg).unwrap() {
            Outcome::Proved(Some(c)) => c.check().unwrap(),
            other => panic!("{a} == {b} at {w}: {other:?}"),
        }
    }
    for (w, a, b) in [
        (32u16, "x + y", "x | y"),
        (8, "x * x", "x"),
        (16, "x >>s 3", "x >>u 3"),
    ] {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let (ea, eb) = (cx.parse(a, &o).unwrap(), cx.parse(b, &o).unwrap());
        let Outcome::Refuted(ce) = equal(&mut cx, ea, eb, &cfg).unwrap() else {
            panic!("{a} == {b} not refuted");
        };
        let env =
            crate::FnEnv(|k: &SymbolKey, _| ce.iter().find(|(kk, _)| kk == k).map(|(_, v)| *v));
        let (va, vb) = (cx.eval(&[ea], &env).unwrap(), cx.eval(&[eb], &env).unwrap());
        assert_ne!(va, vb);
    }
    // Under assumptions: x & 0xf0 is 0 where x <u 16.
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let p = cx.parse("(x & 0xf0) == 0", &o).unwrap();
    assert!(matches!(
        valid(&mut cx, p, &cfg).unwrap(),
        Outcome::Refuted(_)
    ));
    let mut a = Assumptions::new();
    let c = cx.parse("x <u 16", &o).unwrap();
    a.assume_true(&mut cx, c).unwrap();
    assert!(matches!(
        valid_under(&mut cx, p, Some(&a), &cfg).unwrap(),
        Outcome::Proved(_)
    ));
    let o64 = ParseOptions::width(Width::W64);
    let mut c64 = Context::new();
    let cx64 = &mut c64;
    let (ea, eb) = (
        cx64.parse("(x & y) * (x | y) + (x & ~y) * (~x & y)", &o64)
            .unwrap(),
        cx64.parse("x * y", &o64).unwrap(),
    );
    let fast = Config::default();
    #[cfg(feature = "mba")]
    assert!(matches!(
        equal(cx64, ea, eb, &fast).unwrap(),
        Outcome::Proved(None)
    ));
    let _ = (ea, eb, &fast);
    // Satisfying a predicate.
    let q = cx.parse("x * 3 == 7", &o).unwrap();
    let m = satisfy(&mut cx, q, &cfg).unwrap().unwrap().unwrap();
    let env = crate::FnEnv(|k: &SymbolKey, _| m.iter().find(|(kk, _)| kk == k).map(|(_, v)| *v));
    assert_eq!(cx.eval(&[q], &env).unwrap()[0], BitVec::from_bool(true));
}
