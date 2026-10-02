//! Structured CNF families, clause normalization, and incremental search against independent
//! truth tables or a family's mathematical SAT/UNSAT criterion.

use super::*;

fn model_satisfies(clauses: &[Vec<Lit>], model: &[bool]) -> bool {
    clauses
        .iter()
        .all(|c| c.iter().any(|l| model[l.var() as usize] != l.is_neg()))
}

fn brute(vars: u32, clauses: &[Vec<Lit>]) -> bool {
    assert!(vars <= 12);
    (0..1u32 << vars).any(|assignment| {
        clauses.iter().all(|c| {
            c.iter()
                .any(|l| ((assignment >> l.var()) & 1 != 0) != l.is_neg())
        })
    })
}

fn check(vars: u32, clauses: &[Vec<Lit>], expected_sat: bool) {
    let mut solver = Solver::new();
    solver.log_proof();
    for _ in 0..vars {
        solver.new_var();
    }
    for clause in clauses {
        solver.add_clause(clause);
    }
    match solver.solve(1_000_000) {
        Answer::Sat(model) => {
            assert!(expected_sat, "unexpected model: {clauses:?}");
            assert_eq!(model.len(), vars as usize);
            assert!(model_satisfies(clauses, &model));
        }
        Answer::Unsat => {
            assert!(!expected_sat, "unexpected UNSAT: {clauses:?}");
            drup::check(clauses, &solver.take_proof().unwrap()).unwrap();
        }
        Answer::Unknown => panic!("small structured formula exceeded its budget"),
    }
}

#[test]
fn empty_units_duplicates_tautologies_and_unused_variables() {
    let p = Lit::pos(0);
    let q = Lit::pos(4);
    let cases = [
        vec![],
        vec![vec![]],
        vec![vec![p]],
        vec![vec![p], vec![!p]],
        vec![vec![p, p, p]],
        vec![vec![p, !p]],
        vec![vec![q, q, !q, p], vec![!p]],
        vec![vec![p, q], vec![p, q], vec![!p], vec![!q]],
        vec![vec![p, q], vec![!p, q], vec![p, !q], vec![!p, !q]],
    ];
    for mut clauses in cases {
        let expected = brute(6, &clauses);
        check(6, &clauses, expected);
        clauses.reverse();
        for c in &mut clauses {
            c.reverse();
        }
        check(6, &clauses, expected);
    }
}

#[test]
fn long_watched_clauses_and_implication_chains() {
    for n in [3, 17, 65, 257] {
        // All but the final literal become false, forcing watch movement through a long
        // clause and then its last remaining literal.
        let mut clauses = vec![(0..n).map(Lit::pos).collect::<Vec<_>>()];
        clauses.extend((0..n - 1).map(|v| vec![Lit::neg(v)]));
        check(n, &clauses, true);
        clauses.push(vec![Lit::neg(n - 1)]);
        check(n, &clauses, false);

        let mut chain: Vec<Vec<Lit>> = (0..n - 1)
            .map(|v| vec![Lit::neg(v), Lit::pos(v + 1)])
            .collect();
        chain.push(vec![Lit::pos(0)]);
        check(n, &chain, true);
        chain.push(vec![Lit::neg(n - 1)]);
        chain.reverse();
        check(n, &chain, false);
    }
}

#[test]
fn parity_cycles_detect_both_consistent_and_inconsistent_systems() {
    for n in [3, 4, 7, 16, 31, 64] {
        for inconsistent in [false, true] {
            let mut clauses = Vec::new();
            for v in 0..n {
                let a = Lit::pos(v);
                let b = Lit::pos((v + 1) % n);
                // Every edge is equality except an optional contradictory last edge.
                clauses.extend(if inconsistent && v == n - 1 {
                    [vec![a, b], vec![!a, !b]]
                } else {
                    [vec![a, !b], vec![!a, b]]
                });
            }
            check(n, &clauses, !inconsistent);
        }
    }
}

#[test]
fn clause_order_variable_renaming_and_polarity_preserve_satisfiability() {
    let mut rng = Rng(0x5a71_5f1e);
    for _ in 0..24 {
        let n = 9u32;
        let clauses: Vec<Vec<Lit>> = (0..38)
            .map(|_| {
                (0..2 + rng.below(3))
                    .map(|_| Lit::new(rng.below(u64::from(n)) as u32, rng.chance(1, 2)))
                    .collect()
            })
            .collect();
        let expected = brute(n, &clauses);
        for shift in [0, 1, 4, 8] {
            let flip = rng.next();
            let mut transformed: Vec<Vec<Lit>> = clauses
                .iter()
                .rev()
                .map(|c| {
                    c.iter()
                        .rev()
                        .map(|&l| {
                            Lit::new(
                                (l.var() + shift) % n,
                                l.is_neg() == (flip >> l.var() & 1 != 0),
                            )
                        })
                        .collect()
                })
                .collect();
            // Repeated clauses and literals have no semantic effect but exercise normalization.
            transformed.extend(transformed[..3].to_vec());
            for c in &mut transformed {
                c.push(c[0]);
            }
            assert_eq!(brute(n, &transformed), expected);
            check(n, &transformed, expected);
        }
    }
}

fn exactly(n: u32, count: u32) -> Vec<Vec<Lit>> {
    let mut clauses = Vec::new();
    // At most k: every set of k+1 variables contains a false literal.
    // At least k: every set of n-k+1 variables contains a true literal.
    for mask in 1..1u32 << n {
        for (size, positive) in [(count + 1, false), (n - count + 1, true)] {
            if mask.count_ones() == size {
                clauses.push(
                    (0..n)
                        .filter(|v| mask >> v & 1 != 0)
                        .map(|v| Lit::new(v, positive))
                        .collect(),
                );
            }
        }
    }
    clauses
}

#[test]
fn cardinality_constraints_with_partial_assignments() {
    for n in 1..=8 {
        for count in 0..=n {
            let clauses = exactly(n, count);
            check(n, &clauses, true);
            for fixed in [0, n / 2, n] {
                for ones in 0..=fixed {
                    let mut constrained = clauses.clone();
                    constrained.extend((0..fixed).map(|v| vec![Lit::new(v, v < ones)]));
                    let expected = ones <= count && count <= ones + n - fixed;
                    assert_eq!(brute(n, &constrained), expected);
                    check(n, &constrained, expected);
                }
            }
        }
    }
}

#[test]
fn graph_coloring_cycles_and_cliques() {
    for n in 3..=6 {
        for colors in 2..=3 {
            for clique in [false, true] {
                let var = |v, c| Lit::pos(v * colors + c);
                let mut clauses: Vec<Vec<Lit>> = (0..n)
                    .map(|v| (0..colors).map(|c| var(v, c)).collect())
                    .collect();
                for v in 0..n {
                    for a in 0..colors {
                        for b in a + 1..colors {
                            clauses.push(vec![!var(v, a), !var(v, b)]);
                        }
                    }
                    for u in v + 1..n {
                        if clique || u == v + 1 || (v == 0 && u == n - 1) {
                            for c in 0..colors {
                                clauses.push(vec![!var(v, c), !var(u, c)]);
                            }
                        }
                    }
                }
                let expected = if clique {
                    n <= colors
                } else {
                    colors >= 3 || n % 2 == 0
                };
                check(n * colors, &clauses, expected);
            }
        }
    }
}

#[test]
fn adding_clauses_after_models_or_interrupted_search_matches_brute_force() {
    let mut rng = Rng(0x1ac4_ea5e);
    let (mut models, mut unsat, mut interrupted) = (0, 0, 0);
    for seed in 0..40 {
        let n = 7 + seed % 3;
        let mut solver = Solver::new();
        solver.log_proof();
        for _ in 0..n {
            solver.new_var();
        }
        let mut clauses = Vec::new();
        for round in 0..48 {
            let clause: Vec<Lit> = (0..2 + rng.below(4))
                .map(|_| Lit::new(rng.below(u64::from(n)) as u32, rng.chance(1, 2)))
                .collect();
            solver.add_clause(&clause);
            clauses.push(clause);
            if round % 3 == 0 {
                // The next clause may arrive while a nonzero decision level is pending.
                if solver.solve_within(Limits {
                    conflicts: 1,
                    propagations: 1,
                }) == Answer::Unknown
                {
                    interrupted += 1;
                }
                let extra: Vec<Lit> = (0..3)
                    .map(|_| Lit::new(rng.below(u64::from(n)) as u32, rng.chance(1, 2)))
                    .collect();
                solver.add_clause(&extra);
                clauses.push(extra);
            }
            let expected = brute(n, &clauses);
            match solver.solve(100_000) {
                Answer::Sat(model) => {
                    models += 1;
                    assert!(expected, "seed {seed}, prefix {round}");
                    assert!(model_satisfies(&clauses, &model));
                    // Block this model, as an SMT client enumerating solutions would do.
                    if round % 5 == 0 {
                        let block: Vec<Lit> = model
                            .iter()
                            .enumerate()
                            .map(|(v, &value)| Lit::new(v as u32, !value))
                            .collect();
                        solver.add_clause(&block);
                        clauses.push(block);
                    }
                }
                Answer::Unsat => {
                    unsat += 1;
                    assert!(!expected, "seed {seed}, prefix {round}");
                    drup::check(&clauses, &solver.take_proof().unwrap()).unwrap();
                    break;
                }
                Answer::Unknown => panic!("small incremental formula exceeded its budget"),
            }
        }
    }
    assert!(models > 10 && unsat > 10 && interrupted > 10);
}

#[test]
fn proof_checker_rejects_invalid_steps_and_recomputes_deleted_reasons() {
    let a = Lit::pos(0);
    let b = Lit::pos(1);
    let satisfiable = [vec![a, b]];
    assert!(drup::check(&satisfiable, &[Step::Add(vec![a]), Step::Add(vec![])]).is_err());
    assert!(drup::check(&satisfiable, &[Step::Add(vec![])]).is_err());
    let contradictory = [vec![a], vec![!a, b], vec![!b]];
    drup::check(&contradictory, &[Step::Add(vec![])]).unwrap();
    // Deleting a unit reason makes the active database satisfiable again.
    assert!(drup::check(&contradictory, &[Step::Delete(vec![a]), Step::Add(vec![])]).is_err());
}

#[test]
fn zero_budgets_preserve_fresh_and_paused_searches_and_their_proofs() {
    let a = Lit::pos(0);
    let b = Lit::pos(1);
    let clauses = [vec![a, b], vec![a, !b], vec![!a, b], vec![!a, !b]];
    let fresh = || {
        let mut solver = Solver::new();
        solver.log_proof();
        for clause in &clauses {
            solver.add_clause(clause);
        }
        solver
    };
    let mut whole = fresh();
    assert_eq!(whole.solve(u64::MAX), Answer::Unsat);
    let expected_proof = whole.take_proof().unwrap();
    for zero in [
        Limits::conflicts(0),
        Limits {
            conflicts: u64::MAX,
            propagations: 0,
        },
        Limits {
            conflicts: 0,
            propagations: 0,
        },
    ] {
        let mut solver = fresh();
        for paused in [false, true] {
            if paused {
                assert_eq!(solver.solve(1), Answer::Unknown);
                assert_eq!(solver.conflicts, 1);
            }
            let snapshot = (
                solver.conflicts,
                solver.decisions,
                solver.propagations,
                solver.num_learnts(),
            );
            for _ in 0..3 {
                assert_eq!(solver.solve_within(zero), Answer::Unknown);
                assert_eq!(
                    (
                        solver.conflicts,
                        solver.decisions,
                        solver.propagations,
                        solver.num_learnts()
                    ),
                    snapshot
                );
            }
        }
        assert_eq!(solver.solve(u64::MAX), Answer::Unsat);
        assert_eq!(
            (solver.conflicts, solver.decisions, solver.propagations),
            (whole.conflicts, whole.decisions, whole.propagations)
        );
        let proof = solver.take_proof().unwrap();
        assert_eq!(proof, expected_proof);
        drup::check(&clauses, &proof).unwrap();
        assert_eq!(solver.solve_within(zero), Answer::Unsat);
    }
}

#[test]
fn propagation_budgets_pause_inside_long_implication_chains_without_changing_search() {
    for length in [3, 64, 4096] {
        let a = Lit::pos(0);
        let b = Lit::pos(1);
        let mut clauses = vec![vec![a, b], vec![a, !b], vec![!a, Lit::pos(2)]];
        clauses.extend((2..length + 2).map(|v| vec![Lit::neg(v), Lit::pos(v + 1)]));
        let fresh = || {
            let mut solver = Solver::new();
            solver.log_proof();
            for clause in &clauses {
                solver.add_clause(clause);
            }
            solver
        };
        let mut whole = fresh();
        let want = whole.solve(u64::MAX);
        let Answer::Sat(model) = &want else {
            panic!("chain must be satisfiable")
        };
        assert!(model_satisfies(&clauses, model));
        let proof = whole.take_proof().unwrap();
        for budget in [1, 2, 7] {
            let mut solver = fresh();
            // The first conflict learns a, with its implication chain still queued.
            assert_eq!(solver.solve(1), Answer::Unknown);
            let got = loop {
                let p0 = solver.propagations;
                let answer = solver.solve_within(Limits {
                    conflicts: u64::MAX,
                    propagations: budget,
                });
                assert!(
                    solver.propagations - p0 <= budget,
                    "{length}-literal chain exceeded its {budget}-propagation allowance"
                );
                if answer != Answer::Unknown {
                    break answer;
                }
                assert!(solver.propagations > p0);
            };
            assert_eq!(got, want);
            assert_eq!(
                (solver.conflicts, solver.decisions, solver.propagations),
                (whole.conflicts, whole.decisions, whole.propagations)
            );
            assert_eq!(solver.take_proof().unwrap(), proof);
        }
    }
}
