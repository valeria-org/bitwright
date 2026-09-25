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

/// Evaluates `e`'s circuit on 64 assignments of `syms` at once (bit `j` of each symbol's word
/// `k` is its bit `k` in assignment `j`) and compares every lane with bitwright's evaluator.
fn check_lanes(cx: &mut Context, e: Expr, syms: &[(Expr, Vec<BitVec>)]) {
    let ei = cx.id(e).unwrap();
    let mut b = Blaster::new(cx, usize::MAX);
    let bits = b.blast(ei).unwrap();
    let symbols = b.symbols.clone();
    let aig = core::mem::take(&mut b.g);
    drop(b);
    let lanes = syms[0].1.len();
    assert!(lanes <= 64);
    // The circuit's inputs, in creation order: each blasted symbol's bits.
    let mut words: Vec<u64> = Vec::new();
    for (s, sb) in &symbols {
        let (_, vals) = syms
            .iter()
            .find(|(x, _)| cx.id(*x).unwrap() == *s)
            .expect("a known symbol");
        for k in 0..sb.len() {
            let mut w = 0u64;
            for (j, v) in vals.iter().enumerate() {
                if v.bit(k as u16) == Some(true) {
                    w |= 1 << j;
                }
            }
            words.push(w);
        }
    }
    let vals = aig.eval_words(|k| words[k as usize]);
    let out: Vec<u64> = bits.iter().map(|&l| Aig::word(&vals, l)).collect();
    let keys: Vec<SymbolKey> = syms
        .iter()
        .map(|(x, _)| {
            let id = cx.symbol_id(*x).unwrap().unwrap();
            cx.symbol_key(id).unwrap().clone()
        })
        .collect();
    for j in 0..lanes {
        let env = crate::FnEnv(|key: &SymbolKey, _| {
            keys.iter().position(|k| k == key).map(|i| syms[i].1[j])
        });
        let want = cx.eval(&[e], &env).unwrap()[0];
        let got: Vec<bool> = out.iter().map(|w| (w >> j) & 1 == 1).collect();
        let wantb: Vec<bool> = (0..want.width().bits())
            .map(|k| want.bit(k) == Some(true))
            .collect();
        if got != wantb {
            let args: Vec<String> = syms.iter().map(|(_, v)| format!("{}", v[j])).collect();
            panic!(
                "{} at {args:?}: circuit {got:?}, evaluator {want}",
                cx.display(e)
            );
        }
    }
}

/// Every floating-point operation's circuit against the evaluator: every operand combination
/// in tiny formats, in every mode.
#[test]
fn float_circuits_agree_exhaustively_in_tiny_formats() {
    use crate::fp::{FpFormat, FpOp, RoundingMode};
    for (eb, sb) in [(2u32, 3u32), (3, 3), (2, 4), (3, 4)] {
        let f = FpFormat::new(eb, sb).unwrap();
        let w = f.width();
        let n = 1u64 << w.bits();
        let mut ops: Vec<(FpOp, usize)> = vec![
            (FpOp::Rem, 2),
            (FpOp::Min, 2),
            (FpOp::Max, 2),
            (FpOp::Eq, 2),
            (FpOp::Lt, 2),
            (FpOp::Le, 2),
        ];
        for rm in RoundingMode::ALL {
            ops.extend([
                (FpOp::Add(rm), 2),
                (FpOp::Mul(rm), 2),
                (FpOp::Div(rm), 2),
                (FpOp::Sqrt(rm), 1),
                (FpOp::RoundToIntegral(rm), 1),
                (FpOp::Fma(rm), 3),
                (
                    FpOp::Convert {
                        to: FpFormat::new(3, 5).unwrap(),
                        rm,
                    },
                    1,
                ),
                (
                    FpOp::Convert {
                        to: FpFormat::new(2, 3).unwrap(),
                        rm,
                    },
                    1,
                ),
                (FpOp::ToSInt(rm, Width::new(4).unwrap()), 1),
                (FpOp::ToUInt(rm, Width::new(3).unwrap()), 1),
            ]);
        }
        for (op, arity) in ops {
            if arity == 3 && w.bits() > 6 {
                continue;
            }
            let mut cx = Context::new();
            let names = ["a", "b", "c"];
            let xs: Vec<Expr> = names[..arity]
                .iter()
                .map(|s| cx.symbol(*s, w).unwrap())
                .collect();
            let e = cx.fp(op, f, &xs).unwrap();
            let total = n.pow(arity as u32);
            let mut start = 0;
            while start < total {
                let lanes = (total - start).min(64);
                let syms: Vec<(Expr, Vec<BitVec>)> = (0..arity)
                    .map(|k| {
                        let vals = (start..start + lanes)
                            .map(|c| BitVec::wrapping_from_u64(w, (c / n.pow(k as u32)) % n))
                            .collect();
                        (xs[k], vals)
                    })
                    .collect();
                check_lanes(&mut cx, e, &syms);
                start += lanes;
            }
        }
        // From integers of a few widths.
        for iw in [3u16, 5, 8] {
            for rm in RoundingMode::ALL {
                for signed in [true, false] {
                    let mut cx = Context::new();
                    let x = cx.symbol("i", Width::new(iw).unwrap()).unwrap();
                    let op = if signed {
                        FpOp::FromSInt(rm)
                    } else {
                        FpOp::FromUInt(rm)
                    };
                    let e = cx.fp(op, f, &[x]).unwrap();
                    let total = 1u64 << iw;
                    let mut start = 0;
                    while start < total {
                        let lanes = (total - start).min(64);
                        let vals = (start..start + lanes)
                            .map(|c| BitVec::wrapping_from_u64(Width::new(iw).unwrap(), c))
                            .collect();
                        check_lanes(&mut cx, e, &[(x, vals)]);
                        start += lanes;
                    }
                }
            }
        }
    }
}

/// Standard formats at random and special operands.
#[test]
fn float_circuits_agree_in_standard_formats() {
    use crate::fp::{FpFormat, FpOp, RoundingMode};
    let mut rng = Rng(0xf10a7);
    for f in [FpFormat::F16, FpFormat::BF16, FpFormat::F32, FpFormat::F64] {
        let w = f.width();
        let special = |rng: &mut Rng| -> BitVec {
            let r = rng.next();
            let v = match r % 8 {
                0 => f.zero(r & 8 != 0),
                1 => f.inf(r & 8 != 0),
                2 => f.nan(),
                3 => f.from_uint(
                    RoundingMode::Rne,
                    &BitVec::wrapping_from_u64(Width::W16, r >> 5),
                ),
                4 => BitVec::wrapping_from_u64(w, r >> 3 & 0xff),
                _ => BitVec::wrapping_from_limbs(w, &[rng.next(), rng.next()]),
            };
            if r & 16 != 0 { f.neg(&v).unwrap() } else { v }
        };
        let mut ops = vec![FpOp::Min, FpOp::Max, FpOp::Lt, FpOp::Eq];
        for rm in [RoundingMode::Rne, RoundingMode::Rtz, RoundingMode::Rtp] {
            ops.extend([
                FpOp::Add(rm),
                FpOp::Mul(rm),
                FpOp::Div(rm),
                FpOp::Sqrt(rm),
                FpOp::RoundToIntegral(rm),
                FpOp::Fma(rm),
                FpOp::ToSInt(rm, Width::W32),
                FpOp::Convert {
                    to: FpFormat::F32,
                    rm,
                },
            ]);
        }
        if f.width().bits() <= 32 {
            ops.push(FpOp::Rem);
        }
        for op in ops {
            let arity = match op {
                FpOp::Fma(_) => 3,
                FpOp::Sqrt(_)
                | FpOp::RoundToIntegral(_)
                | FpOp::ToSInt(..)
                | FpOp::Convert { .. } => 1,
                _ => 2,
            };
            let mut cx = Context::new();
            let xs: Vec<Expr> = ["a", "b", "c"][..arity]
                .iter()
                .map(|s| cx.symbol(*s, w).unwrap())
                .collect();
            let e = cx.fp(op, f, &xs).unwrap();
            let syms: Vec<(Expr, Vec<BitVec>)> = xs
                .iter()
                .map(|&x| (x, (0..64).map(|_| special(&mut rng)).collect()))
                .collect();
            check_lanes(&mut cx, e, &syms);
        }
    }
}

/// Every built-in rule is proved at a small width, none refuted; an unsound rule is refuted
/// with parameters that make its sides differ; and a rule of bitwise operations is settled for
/// every width at width 1.
#[test]
fn rule_obligations() {
    use crate::rules::RuleProgram;
    let p = RuleProgram::compile(crate::rules::corpus::CORE).unwrap();
    let cfg = Config::default().with_max_conflicts(20_000);
    let (mut proved, mut total) = (0, 0);
    for r in p.rules() {
        let nw = r.width_vars.len();
        let Some(ws) = crate::rules::width_assignments(r)
            .into_iter()
            .filter(|ws| r.admits(ws))
            .min_by_key(|ws| ws[..nw].iter().map(|&w| w.abs_diff(5)).sum::<u16>())
        else {
            continue;
        };
        total += 1;
        match rule(r, &ws, &cfg).unwrap() {
            RuleOutcome::Proved(_) => proved += 1,
            RuleOutcome::Refuted(ps) => panic!("{} at {ws:?} refuted: {ps:?}", r.name),
            RuleOutcome::Unknown(_) => {}
        }
    }
    assert!(
        total > 250 && proved * 50 >= total * 49,
        "{proved} of {total}"
    );

    let src = "bitwright 1;\ngroup t {\n\
        rule bad<W>(x: W, y: W) { x + y => x | y }\n\
        rule absorb<W>(x: W, y: W) { x & (x | y) => x }\n\
        rule bitwise_bad<W>(x: W, y: W) { x & ~y => x ^ y }\n\
        rule mba<W>(x: W, y: W) { (x ^ y) + 2 * (x & y) => x + y }\n\
        rule wide_pow2<W>(x: W, c: const W) { x * c => x << k if is_pow2(c) let k: W = ctz(c) }\n\
        }\n";
    let p = RuleProgram::compile(src).unwrap();
    let [bad, absorb, bitwise_bad, mba, wide_pow2] = p.rules() else {
        panic!()
    };
    let RuleOutcome::Refuted(ps) = rule(bad, &[16], &cfg).unwrap() else {
        panic!("x + y => x | y not refuted")
    };
    let lets = crate::rules::eval::eval_lets(bad, &[16], &ps);
    let side = |n| crate::rules::eval::eval(bad, n, &[16], &ps, &lets).and_then(|v| v.bv());
    assert_ne!(side(bad.lhs), side(bad.rhs));
    // Certificates of rule proofs check.
    let certified = Config::default().with_certificate(true);
    match rule(mba, &[12], &certified).unwrap() {
        RuleOutcome::Proved(Some(c)) => c.check().unwrap(),
        other => panic!("{other:?}"),
    }
    // A constant parameter under a guard: every power of two, at 32 bits.
    assert!(matches!(
        rule(wide_pow2, &[32], &cfg).unwrap(),
        RuleOutcome::Proved(_)
    ));

    let report = rule_all_widths(absorb, 64, &cfg).unwrap();
    assert!(report.every_width && report.refuted.is_none());
    assert_eq!(report.proved, vec![vec![1]]);
    let report = rule_all_widths(bitwise_bad, 64, &cfg).unwrap();
    assert_eq!(report.refuted.as_ref().map(|r| r.0.clone()), Some(vec![1]));
    // Widths 2 to 6 (the literal 2 needs two bits).
    let report = rule_all_widths(mba, 6, &cfg).unwrap();
    assert!(!report.every_width && report.refuted.is_none() && report.open.is_empty());
    assert_eq!(report.proved, (2..=6).map(|w| vec![w]).collect::<Vec<_>>());
    let report = rule_all_widths(bad, 6, &cfg).unwrap();
    assert!(report.refuted.is_some());
}
