//! The prover: the SAT solver against brute force (with every proof checked), the blaster
//! against bitwright's evaluator on every operator, and proofs and refutations end to end.

use super::aig::Aig;
use super::sat::{Answer, Limits, Lit, Solver, Step};
use super::*;
use crate::testutil::{Gen, Rng};
use crate::{BinOp, CmpOpExt, ParseOptions, UnOp};

mod bitvectors;
mod carry_save;
mod cuts;
mod parity_encoding;
mod peepholes;
mod problems;
mod relations;
mod sampling;
mod sat_families;
mod scoped_facts;

#[test]
fn preparation_stats_include_propagation_and_zero_work_preserves_them() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let zero = cx.zero(Width::W8).unwrap();
    let p = cx.eq(x, zero).unwrap();
    let cfg = Config::default()
        .with_samples(0)
        .with_simplify(false)
        .with_certificate(true);
    let mut question = Question::valid(&mut cx, p, &cfg).unwrap();
    let before = question.stats();
    assert!(before.propagations > 0);
    assert!(question.outcome().is_none());
    let Outcome::Unknown(Unknown::Budget {
        conflicts,
        propagations,
    }) = question
        .solve(
            &mut cx,
            Limits {
                conflicts: 0,
                propagations: 0,
            },
        )
        .unwrap()
    else {
        panic!("an open question must stay paused");
    };
    assert_eq!(
        (conflicts, propagations),
        (before.conflicts, before.propagations)
    );
    assert_eq!(question.stats(), before);
    let Outcome::Refuted(model) = question.solve(&mut cx, Limits::conflicts(100)).unwrap() else {
        panic!("the query must resume normally after a zero-work call");
    };
    assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());
}

#[test]
fn majority_encoding_is_exact_for_all_input_and_output_polarities() {
    for signs in 0..8 {
        for invert in 0..2 {
            let mut graph = Aig::new();
            let inputs: Vec<_> = (0..3).map(|_| graph.input()).collect();
            let root = graph.maj(
                inputs[0] ^ (signs & 1),
                inputs[1] ^ (signs >> 1 & 1),
                inputs[2] ^ (signs >> 2 & 1),
            ) ^ invert;
            for assignment in 0..8 {
                let values = graph.eval_all(|i| assignment >> i & 1 == 1);
                let want = Aig::value(&values, root);
                let mut solver = Solver::new();
                solver.log_proof();
                let mut cnf = aig::Cnf::encode(&graph, &[root], &mut solver, true);
                assert_eq!(solver.num_vars(), 4);
                assert_eq!(cnf.emitted(), 6);
                cnf.assert(root, &mut solver);
                for (i, &input) in inputs.iter().enumerate() {
                    cnf.assert(input ^ u32::from(assignment >> i & 1 == 0), &mut solver);
                }
                match solver.solve(100) {
                    Answer::Sat(model) => {
                        assert!(want);
                        assert!(cnf.value(root, &model));
                    }
                    Answer::Unsat => {
                        assert!(!want);
                        drup::check(&cnf.clauses, &solver.take_proof().unwrap()).unwrap();
                    }
                    Answer::Unknown => panic!("tiny majority circuit exceeded budget"),
                }
            }
        }
    }
}

#[test]
fn majority_recognition_preserves_observed_inner_gates_and_rejects_near_misses() {
    for share in [false, true] {
        for near_miss in [false, true] {
            let mut graph = Aig::new();
            let inputs: Vec<_> = (0..4).map(|_| graph.input()).collect();
            let (a, b, c, d) = (inputs[0], inputs[1], inputs[2], inputs[3]);
            let ab = graph.and(a, b);
            let ac = graph.and(a, c);
            let bc = graph.and(b, if near_miss { d } else { c });
            let sum = graph.or(ab, ac);
            let root = graph.or(sum, bc);
            let mut roots = inputs.clone();
            roots.push(root);
            if share {
                roots.push(ab);
            }
            for assignment in 0..16 {
                let values = graph.eval_all(|i| assignment >> i & 1 == 1);
                let want = Aig::value(&values, root);
                let mut solver = Solver::new();
                solver.log_proof();
                let mut cnf = aig::Cnf::encode(&graph, &roots, &mut solver, true);
                cnf.assert(root, &mut solver);
                for (i, &input) in inputs.iter().enumerate() {
                    cnf.assert(input ^ u32::from(assignment >> i & 1 == 0), &mut solver);
                }
                match solver.solve(100) {
                    Answer::Sat(model) => {
                        assert!(want);
                        if share {
                            assert_eq!(cnf.value(ab, &model), Aig::value(&values, ab));
                        }
                    }
                    Answer::Unsat => {
                        assert!(!want);
                        drup::check(&cnf.clauses, &solver.take_proof().unwrap()).unwrap();
                    }
                    Answer::Unknown => panic!("tiny circuit exceeded budget"),
                }
            }
        }
    }
}

#[test]
fn declarations_hold_in_sampled_sat_and_certified_proofs() {
    for bits in [1, 8, 65, 128, 512] {
        let w = Width::new(bits).unwrap();
        let mut cx = Context::new();
        let x = cx.symbol("x", w).unwrap();
        let zero = cx.zero(w).unwrap();
        let one = cx.one(w).unwrap();
        for value in [BitVec::zero(w), BitVec::one(w)] {
            let known = crate::KnownBits::constant(&value);
            cx.declare_known(x, known).unwrap();
            let constant = cx.constant(&value).unwrap();
            for certificate in [false, true] {
                for simplify in [false, true] {
                    for samples in [0, 256] {
                        let cfg = Config::default()
                            .with_certificate(certificate)
                            .with_simplify(simplify)
                            .with_samples(samples);
                        match equal(&mut cx, x, constant, &cfg).unwrap() {
                            Outcome::Proved(Some(cert)) => cert.check().unwrap(),
                            Outcome::Proved(None) => assert!(!certificate),
                            other => panic!("declaration at {bits} bits: {other:?}"),
                        }
                        let different = if value.is_zero() { one } else { zero };
                        let Outcome::Refuted(model) = equal(&mut cx, x, different, &cfg).unwrap()
                        else {
                            panic!("different declared value must be refuted");
                        };
                        assert_eq!(
                            model
                                .iter()
                                .find(|(k, _)| *k == SymbolKey::from("x"))
                                .unwrap()
                                .1,
                            value
                        );
                    }
                }
            }
        }
        if bits == 1 {
            continue;
        }
        // Keep unknown bits free while fixing a one and a zero across the entire width.
        let mut limbs = [0u64; 8];
        limbs[(bits as usize - 1) / 64] = 1 << ((bits - 1) % 64);
        let known_zero = BitVec::wrapping_from_limbs(w, &limbs);
        let known_one = BitVec::one(w);
        let known = crate::KnownBits::new(known_zero, known_one).unwrap();
        cx.declare_known(x, known).unwrap();
        let mask = BitVec::apply_bin(BinOp::Or, &known_zero, &known_one).unwrap();
        let mask = cx.constant(&mask).unwrap();
        let fixed = cx.and(x, mask).unwrap();
        for samples in [0, 256] {
            let cfg = Config::default()
                .with_certificate(true)
                .with_samples(samples);
            let Outcome::Proved(Some(cert)) = equal(&mut cx, fixed, one, &cfg).unwrap() else {
                panic!("fixed bits must be proved");
            };
            cert.check().unwrap();
            let Outcome::Refuted(model) = equal(&mut cx, x, one, &cfg).unwrap() else {
                panic!("unknown bits must remain free");
            };
            let value = model
                .iter()
                .find(|(k, _)| *k == SymbolKey::from("x"))
                .unwrap()
                .1;
            assert!(known.contains(&value));
            assert_ne!(value, known_one);
        }
    }
}

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

/// Random 3-SAT near the threshold (`n` variables), and pigeonhole (`n + 1` pigeons).
fn three_sat(rng: &mut Rng, n: u32) -> Vec<Vec<Lit>> {
    (0..(f64::from(n) * 4.26) as usize)
        .map(|_| {
            (0..3)
                .map(|_| Lit::new(rng.below(u64::from(n)) as u32, rng.chance(1, 2)))
                .collect()
        })
        .collect()
}

fn pigeonhole(n: u32) -> Vec<Vec<Lit>> {
    let var = |p: u32, h: u32| p * n + h;
    let mut clauses: Vec<Vec<Lit>> = (0..=n)
        .map(|p| (0..n).map(|h| Lit::pos(var(p, h))).collect())
        .collect();
    for h in 0..n {
        for p in 0..=n {
            for q in p + 1..=n {
                clauses.push(vec![Lit::neg(var(p, h)), Lit::neg(var(q, h))]);
            }
        }
    }
    clauses
}

/// A search stopped on its limits goes on where it stopped: in steps of a few conflicts (or
/// propagations) it meets the same conflicts, makes the same decisions and propagations, logs
/// the same proof and gives the same answer as in one call, through restarts, reductions and
/// collections of the learned clauses.
#[test]
fn a_resumed_search_is_the_search_it_continues() {
    let mut rng = Rng(0x11);
    let mut cases: Vec<Vec<Vec<Lit>>> = (0..8).map(|_| three_sat(&mut rng, 150)).collect();
    cases.push(pigeonhole(7));
    let (mut long, mut sat, mut unsat) = (0, 0, 0);
    for clauses in &cases {
        let fresh = || {
            let mut s = Solver::new();
            s.log_proof();
            for c in clauses {
                s.add_clause(c);
            }
            s
        };
        let mut whole = fresh();
        let want = whole.solve(u64::MAX);
        let want_proof = whole.take_proof().unwrap();
        for step in [
            Limits::conflicts(7),
            Limits {
                conflicts: u64::MAX,
                propagations: 500,
            },
        ] {
            let mut s = fresh();
            let got = loop {
                let (c0, p0) = (s.conflicts, s.propagations);
                let a = s.solve_within(step);
                assert!(s.conflicts - c0 <= step.conflicts);
                assert!(s.propagations - p0 <= step.propagations);
                if a != Answer::Unknown {
                    break a;
                }
            };
            assert_eq!(got, want);
            assert_eq!(
                (s.conflicts, s.decisions, s.propagations),
                (whole.conflicts, whole.decisions, whole.propagations)
            );
            assert_eq!(s.take_proof().unwrap(), want_proof);
        }
        // The learned clauses are reduced (and collected) every 2,000 conflicts or more.
        long += u32::from(whole.conflicts > 2000);
        match want {
            Answer::Sat(m) => {
                sat += 1;
                for c in clauses {
                    assert!(c.iter().any(|l| m[l.var() as usize] != l.is_neg()));
                }
            }
            Answer::Unsat => {
                unsat += 1;
                drup::check(clauses, &want_proof).unwrap();
            }
            Answer::Unknown => unreachable!(),
        }
    }
    // Long enough to reduce and collect the learned clauses, with both answers.
    assert!(long >= 2 && sat >= 2 && unsat >= 2, "{long} {sat} {unsat}");
}

/// Encoded with its gates recognized, a circuit's clauses are satisfiable with a root true
/// exactly when some input makes it true (every input tried), and a model's inputs do: on random
/// circuits of exclusive ors, multiplexers and trees of and-gates, sharing nodes between roots.
/// An exclusive or is one variable.
#[test]
fn encoded_circuits_agree_with_evaluation() {
    use super::aig::{Cnf, L};
    let mut rng = Rng(0xc1f);
    for _ in 0..400 {
        let mut g = Aig::new();
        let ni = 2 + rng.below(5) as u32;
        let mut lits: Vec<L> = (0..ni).map(|_| g.input()).collect();
        for _ in 0..3 + rng.below(30) {
            let mut pick = || lits[rng.below(lits.len() as u64) as usize] ^ rng.below(2) as u32;
            let (a, b, c) = (pick(), pick(), pick());
            let x = match rng.below(6) {
                0 | 1 => g.and(a, b),
                2 => g.xor(a, b),
                3 => g.mux(a, b, c),
                4 => g.or(a, b),
                _ => g.maj(a, b, c),
            };
            lits.push(x);
        }
        let roots = [
            lits[lits.len() - 1],
            lits[ni as usize + rng.below(lits.len() as u64 - u64::from(ni)) as usize] ^ 1,
        ];
        for &r in &roots {
            let holds_somewhere = (0..1u32 << ni).any(|a| {
                let vals = g.eval_all(|k| (a >> k) & 1 == 1);
                Aig::value(&vals, r)
            });
            let mut s = Solver::new();
            let mut cnf = Cnf::encode(&g, &roots, &mut s, true);
            assert!(cnf.emitted() == cnf.clauses.len());
            cnf.assert(r, &mut s);
            match s.solve(u64::MAX) {
                Answer::Sat(m) => {
                    assert!(holds_somewhere);
                    let vals = g.eval_all(|k| cnf.value(lits[k as usize], &m));
                    assert!(Aig::value(&vals, r));
                }
                Answer::Unsat => assert!(!holds_somewhere),
                Answer::Unknown => unreachable!(),
            }
        }
    }
    let mut g = Aig::new();
    let (a, b) = (g.input(), g.input());
    let x = g.xor(a, b);
    let mut s = Solver::new();
    let cnf = Cnf::encode(&g, &[x], &mut s, false);
    assert_eq!((g.len(), s.num_vars(), cnf.emitted()), (6, 3, 4));
}

/// A question decided in steps answers what one call does, with the same counterexample and work;
/// an undecided one says why (a budget it may pass, a circuit too large for any), and the
/// answer, once found, is kept.
#[test]
fn questions_resume_and_say_why_they_are_undecided() {
    let o = ParseOptions::width(Width::W32);
    let cfg = Config::default().with_samples(0).with_simplify(false);
    // x * y is never this odd constant: false, and the search needs a while to invert it.
    let claim = "x * (y | 1) != 0x9e3779b1";
    let mut cx = Context::new();
    let p = cx.parse(claim, &o).unwrap();
    let mut q = Question::valid(&mut cx, p, &cfg).unwrap();
    let mut steps = 0;
    let chunk = 10;
    let stepped = loop {
        steps += 1;
        match q.solve(&mut cx, Limits::conflicts(chunk)).unwrap() {
            Outcome::Unknown(why) => {
                let Unknown::Budget { conflicts, .. } = why else {
                    panic!("{why}")
                };
                assert_eq!(conflicts, q.stats().conflicts);
                assert!(why.is_budget() && why.to_string().contains("conflicts"));
            }
            o => break o,
        }
    };
    assert!(steps > 3, "{steps}");
    let Outcome::Refuted(m) = &stepped else {
        panic!("{stepped:?}")
    };
    let st = q.stats();
    assert!(st.nodes > 0 && st.vars > 0 && st.clauses > 0 && st.propagations > 0);
    // Once decided, the answer again, without more work.
    assert!(
        matches!(q.solve(&mut cx, Limits::conflicts(0)).unwrap(), Outcome::Refuted(n) if n == *m)
    );
    assert_eq!(q.stats(), st);
    // One call with the whole budget: the same counterexample, and the same work.
    let mut cx2 = Context::new();
    let p2 = cx2.parse(claim, &o).unwrap();
    let mut q2 = Question::valid(&mut cx2, p2, &cfg).unwrap();
    let once = q2
        .solve(&mut cx2, Limits::conflicts(steps * chunk))
        .unwrap();
    assert!(matches!(&once, Outcome::Refuted(n) if n == m));
    assert_eq!(q2.stats(), st);
    // A propagation limit stops the search as well.
    let mut cx3 = Context::new();
    let p3 = cx3.parse(claim, &o).unwrap();
    let few = cfg.with_max_propagations(2_000);
    let Outcome::Unknown(Unknown::Budget { propagations, .. }) = valid(&mut cx3, p3, &few).unwrap()
    else {
        panic!("decided within 2,000 propagations")
    };
    assert!((2_000..3_000).contains(&propagations), "{propagations}");

    // Too large under the node cap: the same under any budget, and before any search.
    let small = cfg.with_max_nodes(500);
    for conflicts in [1, 1_000_000] {
        let q = Question::valid(&mut cx, p, &small.with_max_conflicts(conflicts)).unwrap();
        let Some(Outcome::Unknown(Unknown::TooLarge { nodes })) = q.outcome() else {
            panic!("{:?}", q.outcome())
        };
        assert!(*nodes > 500 && q.stats().vars == 0);
    }

    // A refutation that many values give is found by sampling, with no clauses.
    let e = cx.parse("(x & 0xff) != 0x5a", &o).unwrap();
    let q = Question::valid(&mut cx, e, &Config::default().with_simplify(false)).unwrap();
    assert!(matches!(q.outcome(), Some(Outcome::Refuted(_))));
    assert!(q.stats().samples > 0 && q.stats().vars == 0);
    let Outcome::Refuted(_) = valid(&mut cx, e, &cfg).unwrap() else {
        panic!("not refuted")
    };
}
