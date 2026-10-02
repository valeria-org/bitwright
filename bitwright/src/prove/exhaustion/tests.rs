use super::*;
use crate::prove::aig::{Aig, FALSE, TRUE};
use crate::testutil::Rng;

/// Whether the goal holds wherever every constraint does, by evaluating each assignment.
fn brute_force(g: &Aig, inputs: u32, goal: L, constraints: &[L]) -> bool {
    (0..1u64 << inputs).all(|a| {
        let vals = g.eval_all(|k| (a >> k) & 1 == 1);
        !constraints.iter().all(|&c| Aig::value(&vals, c)) || Aig::value(&vals, goal)
    })
}

fn literal(rng: &mut Rng, nodes: &[L]) -> L {
    nodes[(rng.next() % nodes.len() as u64) as usize] ^ (rng.next() & 1) as L
}

#[test]
fn checks_agree_with_brute_force_on_random_circuits() {
    let mut rng = Rng(0x0045_5848_4155_5354);
    let mut verdicts = [0usize; 2];
    let mut segmented = 0;
    for round in 0..600 {
        let inputs = [0u32, 1, 3, 6, 9, 10, 11, 14][round % 8];
        let mut g = Aig::new();
        let mut nodes: Vec<L> = (0..inputs).map(|_| g.input()).collect();
        if nodes.is_empty() {
            nodes.push(FALSE);
        }
        for _ in 0..(rng.next() % 40) {
            let (a, b) = (literal(&mut rng, &nodes), literal(&mut rng, &nodes));
            nodes.push(g.and(a, b));
        }
        // Disjunctions of a few literals are valid often enough to exercise both verdicts,
        // and are negated conjunctions, the goal shape the check segments.
        let mut goal = literal(&mut rng, &nodes);
        for _ in 0..(rng.next() % 5) {
            let l = literal(&mut rng, &nodes);
            goal = g.or(goal, l);
        }
        if round % 5 == 0 {
            // A hidden tautology: (a and b) or not a or not b.
            let (a, b) = (literal(&mut rng, &nodes), literal(&mut rng, &nodes));
            let ab = g.and(a, b);
            let t = g.or(ab, a ^ 1);
            goal = g.or(t, b ^ 1);
        }
        let constraints: Vec<L> = (0..rng.next() % 3)
            .map(|_| {
                let (a, b) = (literal(&mut rng, &nodes), literal(&mut rng, &nodes));
                g.or(a, b)
            })
            .collect();
        let want = brute_force(&g, inputs, goal, &constraints);
        let e = Exhaustion::of(&g, goal, &constraints);
        assert!(e.inputs() <= inputs);
        if e.conjuncts().is_some() {
            segmented += 1;
        }
        let got = e.check();
        assert_eq!(got.is_ok(), want, "round {round}: {got:?}");
        verdicts[usize::from(want)] += 1;
    }
    assert!(verdicts[0] >= 100 && verdicts[1] >= 100, "{verdicts:?}");
    assert!(segmented >= 200, "{segmented}");
}

#[test]
fn constant_goals_and_single_failures_across_blocks() {
    let mut g = Aig::new();
    assert!(Exhaustion::of(&g, TRUE, &[]).check().is_ok());
    assert!(Exhaustion::of(&g, FALSE, &[]).check().is_err());
    // A goal false at exactly one of 2^13 assignments, in the last block: the whole domain is
    // visited, and the failure is found whichever conjunct order the schedule picks.
    let x: Vec<L> = (0..13).map(|_| g.input()).collect();
    let all = g.and_all(&x);
    let e = Exhaustion::of(&g, all ^ 1, &[]);
    assert_eq!(e.inputs(), 13);
    let err = e.check().unwrap_err();
    assert!(err.contains("0x1fff"), "{err}");
    // Excluding that assignment by a constraint makes it hold.
    assert!(Exhaustion::of(&g, all ^ 1, &[all ^ 1]).check().is_ok());
    // Unused inputs are not enumerated.
    let _ = g.input();
    assert_eq!(Exhaustion::of(&g, all ^ 1, &[]).inputs(), 13);
}
