//! SAT sweeping: the solver's search under assumptions, and questions swept, against the same
//! questions searched alone.

use super::*;

/// `x + y` written as a ripple chain of `w` steps (each step's sum and carry as words).
fn ripple(w: u16) -> String {
    let mut s = String::from("let a0 = x; let b0 = y; ");
    for k in 0..w {
        s += &format!(
            "let a{n} = a{k} ^ b{k}; let b{n} = (a{k} & b{k}) << 1; ",
            n = k + 1
        );
    }
    s + &format!("a{w}")
}

/// `x + y` (or `x - y` with `sub`) by a Kogge–Stone prefix tree, with `levels` levels (all of
/// them: the sum; fewer: a sum wrong where a carry runs farther).
fn prefix(w: u16, sub: bool, levels: Option<usize>) -> String {
    let all = (u16::BITS - (w - 1).leading_zeros()) as usize;
    let levels = levels.unwrap_or(all);
    let mut s = String::from(if sub {
        "let s = x ^ y; let p0 = ~s; let g0 = ~x & y; "
    } else {
        "let s = x ^ y; let p0 = s; let g0 = x & y; "
    });
    for k in 0..levels {
        s += &format!(
            "let g{n} = g{k} | (p{k} & (g{k} << {sh})); let p{n} = p{k} & (p{k} << {sh}); ",
            n = k + 1,
            sh = 1u32 << k
        );
    }
    s + &format!("s ^ (g{levels} << 1)")
}

/// Under assumptions, a contradiction leaves the clauses satisfiable, the negation of the
/// assumptions follows by unit propagation, and every clause logged on the way checks.
#[test]
fn search_under_assumptions() {
    let (a, b, c) = (Lit::pos(0), Lit::pos(1), Lit::pos(2));
    let clauses = vec![vec![a, b], vec![!a, c]];
    let mut s = Solver::new();
    s.log_proof();
    for cl in &clauses {
        s.add_clause(cl);
    }
    // ¬b forces a, which forces c: ¬b ∧ ¬c is contradictory.
    assert_eq!(
        s.solve_assuming(&[!b, !c], Limits::conflicts(100)),
        Answer::Unsat
    );
    assert!(!s.is_unsat());
    let rejected = s.rejected_lemmas;
    assert!(s.add_rup_clause(&[b, c]) && s.rejected_lemmas == rejected);
    // Satisfiable assumptions give a model that has them.
    match s.solve_assuming(&[!c], Limits::conflicts(100)) {
        Answer::Sat(m) => assert!(!m[2] && !m[0] && m[1]),
        other => panic!("{other:?}"),
    }
    // Still satisfiable with nothing assumed.
    assert!(matches!(s.solve(100), Answer::Sat(_)));
    // With ¬b and ¬c added, refuted, and the proof, the lemmas included, checks.
    s.add_clause(&[!b]);
    s.add_clause(&[!c]);
    assert_eq!(s.solve(100), Answer::Unsat);
    let mut all = clauses;
    all.push(vec![!b]);
    all.push(vec![!c]);
    drup::check(&all, &s.take_proof().unwrap()).unwrap();
}

/// Random 3-SAT under random assumptions, against brute force.
#[test]
fn assumptions_agree_with_brute_force() {
    let mut rng = Rng(0x5a55);
    for _ in 0..300 {
        let n = 3 + rng.below(6) as u32;
        let clauses = three_sat(&mut rng, n);
        let assumed: Vec<Lit> = (0..1 + rng.below(3))
            .map(|_| Lit::new(rng.below(u64::from(n)) as u32, rng.chance(1, 2)))
            .collect();
        let holds = |m: u32, l: Lit| ((m >> l.var()) & 1 == 1) != l.is_neg();
        let sat = (0..1u32 << n).any(|m| {
            assumed.iter().all(|&l| holds(m, l))
                && clauses.iter().all(|c| c.iter().any(|&l| holds(m, l)))
        });
        let mut s = Solver::new();
        for c in &clauses {
            s.add_clause(c);
        }
        match s.solve_assuming(&assumed, Limits::conflicts(10_000)) {
            Answer::Sat(m) => {
                assert!(sat);
                for &l in &assumed {
                    assert_eq!(m[l.var() as usize], !l.is_neg());
                }
                for c in &clauses {
                    assert!(c.iter().any(|&l| m[l.var() as usize] != l.is_neg()));
                }
            }
            Answer::Unsat => {
                assert!(!sat);
                // The negated assumptions follow, unless the clauses alone are contradictory.
                if !s.is_unsat() {
                    let negated: Vec<Lit> = assumed.iter().map(|&l| !l).collect();
                    let rejected = s.rejected_lemmas;
                    assert!(s.add_rup_clause(&negated));
                    assert_eq!(s.rejected_lemmas, rejected);
                }
            }
            Answer::Unknown => panic!("10,000 conflicts on {n} variables"),
        }
    }
}

/// `a == b` at `w` bits, swept or not, with a certificate: the outcome and the question's stats.
fn ask(w: u16, a: &str, b: &str, sweeping: bool) -> (Outcome, Stats) {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::new(w).unwrap());
    let (a, b) = (cx.parse(a, &o).unwrap(), cx.parse(b, &o).unwrap());
    let cfg = Config::default()
        .with_simplify(false)
        .with_samples(0)
        .with_certificate(true)
        .with_sweeping(sweeping);
    let mut q = Question::equal(&mut cx, a, b, &cfg).unwrap();
    let out = q.solve(&mut cx, cfg.limits()).unwrap();
    (out, q.stats())
}

/// Adders and subtractors as prefix trees and ripple chains: proved with certificates that
/// check, with internal nodes merged, and the wide ones in less work than the search alone.
#[test]
fn adders_are_proved_with_merges_and_certificates() {
    for (w, src, sum) in [
        (32u16, prefix(32, false, None), "x + y"),
        (64, prefix(64, false, None), "x + y"),
        (64, prefix(64, true, None), "x - y"),
        (16, ripple(16), "x + y"),
    ] {
        let (plain, plain_stats) = ask(w, &src, sum, false);
        let (swept, stats) = ask(w, &src, sum, true);
        for out in [&plain, &swept] {
            match out {
                Outcome::Proved(Some(c)) => c.check().unwrap(),
                other => panic!("{w} bits: {other:?}"),
            }
        }
        assert!(stats.sweeping.ran && stats.sweeping.merged > 0, "{stats:?}");
        assert!(stats.propagations >= stats.sweeping.propagations);
        if w >= 32 {
            assert!(
                stats.propagations < plain_stats.propagations,
                "{w} bits: {} swept, {} not",
                stats.propagations,
                plain_stats.propagations
            );
        }
    }
}

/// A prefix tree missing levels is wrong only where a carry runs far: refuted, swept or not
/// (a refutation's counterexample is checked by evaluation before it is returned).
#[test]
fn wrong_adders_are_refuted() {
    for w in [16u16, 32] {
        let src = prefix(w, false, Some(3));
        for sweeping in [false, true] {
            let (out, _) = ask(w, &src, "x + y", sweeping);
            assert!(matches!(out, Outcome::Refuted(_)), "{w} bits: {out:?}");
        }
    }
}

/// Random questions over small symbols: swept and searched alone, they get the same answer,
/// and every proof's certificate checks.
#[test]
fn sweeping_agrees_with_search() {
    let mut g = crate::engine::tests::generator(0x5e1e);
    let (mut proved, mut refuted) = (0, 0);
    for i in 0..300 {
        let w = 2 + (i % 5) as u16;
        g.max_w = w;
        let mut cx = Context::new();
        let (a, _) = g.expr(&mut cx, w, 4);
        // Half the questions `a` against the standard engine's rewriting of it, half `a`
        // against another expression.
        let b = if i % 2 == 0 {
            crate::engine::Engine::standard()
                .simplify(&mut cx, a)
                .unwrap()
                .expr
        } else {
            g.expr(&mut cx, w, 3).0
        };
        if cx.width(a).unwrap() != cx.width(b).unwrap() {
            continue;
        }
        let mut outcomes = Vec::new();
        for sweeping in [false, true] {
            let cfg = Config::default()
                .with_simplify(false)
                .with_samples(0)
                .with_certificate(true)
                .with_sweeping(sweeping);
            let mut q = Question::equal(&mut cx, a, b, &cfg).unwrap();
            let out = q.solve(&mut cx, cfg.limits()).unwrap();
            if let Outcome::Proved(Some(c)) = &out {
                c.check().unwrap();
            }
            outcomes.push(matches!(out, Outcome::Proved(_)));
        }
        assert_eq!(
            outcomes[0],
            outcomes[1],
            "{} == {}",
            cx.display(a),
            cx.display(b)
        );
        if outcomes[0] {
            proved += 1;
        } else {
            refuted += 1;
        }
    }
    assert!(
        proved > 50 && refuted > 50,
        "{proved} proved, {refuted} refuted"
    );
}

/// The sweep takes at most half of the first search's limits, and its work counts in the
/// question's totals; a question resumed in steps ends with the answer, swept once.
#[test]
fn sweeping_stays_within_its_share() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let (a, b) = (
        cx.parse(&prefix(64, false, None), &o).unwrap(),
        cx.parse("x + y", &o).unwrap(),
    );
    let cfg = Config::default()
        .with_simplify(false)
        .with_samples(0)
        .with_sweeping(true);
    let mut q = Question::equal(&mut cx, a, b, &cfg).unwrap();
    let step = Limits {
        conflicts: u64::MAX,
        propagations: 20_000,
    };
    let mut out = q.solve(&mut cx, step).unwrap();
    let first = q.stats();
    assert!(first.sweeping.ran);
    // A propagation call finishes the watch list it is on before it stops.
    assert!(first.sweeping.propagations <= step.propagations / 2 + 1_000);
    assert!(first.propagations >= first.sweeping.propagations);
    while let Outcome::Unknown(why) = &out {
        assert!(why.is_budget());
        out = q.solve(&mut cx, step).unwrap();
    }
    assert!(matches!(out, Outcome::Proved(_)));
    assert_eq!(q.stats().sweeping, first.sweeping);
}
