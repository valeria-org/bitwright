#![cfg(feature = "mba")]

use std::sync::Arc;

use bitwright::engine::{Budget, Each, End, Engine, Exhausted, Phase, Run, Strategy};
use bitwright::mba::{MbaBudget, MbaConfig, MbaLimits, MemoryCache, SignatureSolver};
use bitwright::{BinOp, Context, ParseOptions, Width};

fn phase(cfg: MbaConfig) -> Strategy {
    Strategy::new("mba", vec![Phase::Mba(cfg)]).with_kept_steps(1)
}

#[test]
fn incomplete_alternate_reading_is_retried_with_more_fuel() {
    // The whole reading exceeds max_vars; a retry reads x+y as one atom.
    let cfg = MbaConfig::default().with_limits(MbaLimits::default().with_max_vars(1));
    let eng = Engine::builder().strategy(phase(cfg)).build().unwrap();
    for (budget, reason) in [
        (Budget::UNLIMITED.with_mba_calls(0), Exhausted::MbaCalls),
        (Budget::UNLIMITED.with_mba_steps(0), Exhausted::MbaSteps),
    ] {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let root = cx.parse("((x+y) & 15)+((x+y) | 15)-(x+y)", &o).unwrap();
        let answer = cx.parse("15", &o).unwrap();
        let r = eng
            .run(&mut cx, &[root], Run::default().with_per_call(budget))
            .unwrap();
        assert_eq!(r.roots[0].end, End::BudgetTerminated(reason));
        assert_eq!(r.roots[0].expr, root);
        let r = eng
            .run(
                &mut cx,
                &[root],
                Run::default().with_per_call(Budget::UNLIMITED),
            )
            .unwrap();
        assert_eq!(r.roots[0].expr, answer);
        assert_eq!(r.roots[0].end, End::Completed);
        assert!(r.stats.mba.calls > 0);
    }
}

#[test]
fn exhausted_solver_budget_is_steps_not_calls() {
    let mut cx = Context::new();
    let root = cx
        .parse("(x ^ y) + (x & y)", &ParseOptions::width(Width::W32))
        .unwrap();
    let cfg = MbaConfig::default()
        .with_budget(MbaBudget::default().with_steps(1))
        .with_limits(MbaLimits::default().with_min_nodes(5));
    let eng = Engine::builder().strategy(phase(cfg)).build().unwrap();
    let r = eng
        .run(
            &mut cx,
            &[root],
            Run::default().with_per_call(Budget::UNLIMITED),
        )
        .unwrap();
    assert_eq!(r.roots[0].end, End::BudgetTerminated(Exhausted::MbaSteps));
    assert_eq!(r.stats.mba.steps, 1);
}

#[test]
fn independent_roots_do_not_lend_each_other_cached_solver_work() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let inner = cx.parse("(x ^ y) + (x & y)", &o).unwrap();
    let diff = cx.parse("((x ^ y) + (x & y)) - (x | y)", &o).unwrap();
    let zero = cx.parse("0", &o).unwrap();
    let q = cx.bin(BinOp::UDiv, diff, inner).unwrap();
    let folded = cx.bin(BinOp::UDiv, zero, inner).unwrap();
    let eng = Engine::builder()
        .strategy(phase(MbaConfig::default()))
        .mba_solver(Arc::new(SignatureSolver))
        .mba_cache(Arc::new(MemoryCache::new(64)))
        .build()
        .unwrap();
    // Warm both durable entries. On the cold single-root budget the denominator
    // spends the only call; the numerator must not get a free cancellation.
    assert_eq!(
        eng.run(&mut cx, &[q], Run::default()).unwrap().roots[0].expr,
        folded
    );
    for threads in [1, 2] {
        let each = Each::default()
            .with_threads(threads)
            .with_per_root(Budget::UNLIMITED.with_mba_calls(1));
        for (roots, k) in [([inner, q], 1), ([q, inner], 0)] {
            let r = eng.run_each(&mut cx, &roots, each).unwrap();
            assert_eq!(r.roots[k].end, End::BudgetTerminated(Exhausted::MbaCalls));
            assert_eq!(r.roots[k].expr, q);
            assert_eq!(r.stats.mba.calls, 2);
        }
    }
}
