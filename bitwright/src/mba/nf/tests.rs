use super::*;
use crate::{Context, ParseOptions};

const SUM: &str = "4*x+18*y+16*z-6*w-26*(x&y)-26*(x&z)-31*(y&z)+9*(w&x)-6*(w&z)+52*(x&y&z)";

fn sum() -> MbaExpr {
    let mut cx = Context::new();
    let e = cx.parse(SUM, &ParseOptions::width(Width::W64)).unwrap();
    crate::mba::lower(&cx, e, &Default::default()).unwrap().0
}

#[test]
fn unfinished_first_render_spends_its_allowance() {
    let p = sum();
    let solver = NormalFormSolver::default();
    // Normalization fits in 248 steps. Rendering tries to spend more than
    // what remains: do not lose its debit or count more than the allowance.
    for cap in [256, 2048] {
        let budget = MbaBudget::default().with_steps(cap);
        let cold = solver.solve_counted(&p, &budget);
        assert_eq!(cold, (MbaAnswer::Exhausted, cap));
        // A memo hit must replay the same debit.
        assert_eq!(solver.solve_counted(&p, &budget), cold);
    }
    let ample = MbaBudget::default().with_steps(1 << 20);
    let (answer, spent) = solver.solve_counted(&p, &ample);
    assert!(matches!(answer, MbaAnswer::Simplified { .. }));
    assert!(spent > 2048 && spent < ample.steps);
}

#[test]
fn unfinished_later_render_spends_its_allowance_but_keeps_the_first_answer() {
    // x*y + x*z renders as x*(y+z); the new factor y+z calls for a second round.
    let mut p = MbaExpr::new(vec![Width::W64; 3]);
    let x = p.push(MOp::Var(0), &[]).unwrap();
    let y = p.push(MOp::Var(1), &[]).unwrap();
    let z = p.push(MOp::Var(2), &[]).unwrap();
    let xy = p.push(MOp::Mul, &[x, y]).unwrap();
    let xz = p.push(MOp::Mul, &[x, z]).unwrap();
    p.push(MOp::Add, &[xy, xz]).unwrap();
    let opts = NfOptions::default()
        .with_synthesis(false)
        .with_basis_sums(false);
    let mut tally = NfStats::default();
    let n = normalize(
        &p,
        &opts,
        &MbaBudget::default(),
        &mut tally,
        &Used::default(),
    )
    .unwrap();
    let mut first = Render::new(p.vars().to_vec(), n.w, &n.classes, &n.atom_exprs, u64::MAX)
        .with_bar(n.input_cost)
        .with_basis(false);
    let candidates = candidates(&mut first, &n.nf, &n.factors);
    let best = first.best(&candidates).unwrap();
    let factors = first.factors_of(best);
    assert!(factors.iter().any(|f| !n.factors.contains(f)));
    let expected = first.b.finish(best).unwrap();
    // Just one step past the first rendering; the second must stop.
    let cap = first.work + 1;
    let used = Used::default();
    let mut work = Steps::counted(cap, &used);
    let rendered = best_rendering(&p, &n, (n.input_cost, false), &mut work, &mut tally).unwrap();
    assert_eq!(rendered.exact.unwrap().1, expected);
    assert_eq!((work.left, used.get()), (0, cap));
}

#[test]
fn solver_identity_distinguishes_basis_answers() {
    let p = sum();
    let basis = NormalFormSolver::default();
    let conjunction = NormalFormSolver::new(NfOptions::default().with_basis_sums(false));
    let budget = MbaBudget::default();
    assert_ne!(basis.solve(&p, &budget), conjunction.solve(&p, &budget));
    assert_ne!(basis.id(), conjunction.id());
}
