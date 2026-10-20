//! A deadline means stop now (`engine::Deadline`).
//!
//! A budget stop keeps what the stopped phase did and goes on to the next
//! root, each with its own work worth keeping. A deadline is the host
//! saying it no longer wants the answer, so the run does nothing more: the
//! stopped root is not salvaged (which walks its whole DAG again) and the
//! roots after it are not started, each saying it stopped at the deadline.

use std::cell::Cell;

use bitwright::engine::{Clock, Deadline, End, Engine, Exhausted, Run, Strategy};
use bitwright::{Context, ParseOptions, Width};

/// A clock that runs until it has been read `at` times, then stands past
/// every deadline. One run reads it from one thread.
struct FireAfter {
    reads: Cell<u64>,
    at: u64,
}

impl Clock for FireAfter {
    fn now_ticks(&self) -> u64 {
        let n = self.reads.get() + 1;
        self.reads.set(n);
        if n > self.at { u64::MAX } else { 0 }
    }
}

/// `n` roots over one shared mix: each is that mix xored with its index,
/// so every root holds the same big subterm. Once a run has simplified
/// the mix for one root, salvaging another root rebuilds it over the
/// simplified mix — which is what a stopped run must not do.
fn roots(cx: &mut Context, n: usize) -> Vec<bitwright::Expr> {
    let opts = ParseOptions::width(Width::W64);
    let mix = "(((x ^ y) + ((x & y) * 2)) - (x | y)) + ((x & y) | (x ^ y))";
    (0..n)
        .map(|k| cx.parse(&format!("({mix}) ^ {k}"), &opts).unwrap())
        .collect()
}

#[test]
fn a_fired_deadline_leaves_the_roots_after_it_as_they_were() {
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let mut cx = Context::new();
    let es = roots(&mut cx, 64);
    // Long enough to rewrite the first roots, short enough to stop inside
    // the run: the clock is read once per 8 charges.
    let clock = FireAfter {
        reads: Cell::new(0),
        at: 4,
    };
    let out = engine
        .run(
            &mut cx,
            &es,
            Run::default().with_deadline(Deadline::new(&clock, u64::MAX).with_check_every(8)),
        )
        .unwrap();
    let stopped: Vec<usize> = out
        .roots
        .iter()
        .enumerate()
        .filter(|(_, r)| matches!(r.end, End::BudgetTerminated(Exhausted::Deadline)))
        .map(|(k, _)| k)
        .collect();
    assert!(!stopped.is_empty(), "the deadline stopped nothing");
    // Nothing was salvaged: that walks a root's whole DAG again, which is
    // work the run was told to stop doing (a budget stop still does it).
    assert_eq!(
        out.stats.salvaged, 0,
        "a root was salvaged past the deadline"
    );
    assert_eq!(
        out.stats.not_started as usize,
        stopped.len() - 1,
        "every root after the stopped one is left unstarted"
    );
    // Every root the deadline reached comes back as it was: none was
    // rebuilt after the run was told to stop.
    for &k in &stopped {
        assert!(
            !out.roots[k].changed,
            "root {k} changed after the deadline: {}",
            cx.display(out.roots[k].expr)
        );
    }
    // And the run stopped there: no root after the first stopped one ran.
    let first = stopped[0];
    assert!(
        (first..out.roots.len())
            .all(|k| matches!(out.roots[k].end, End::BudgetTerminated(Exhausted::Deadline))),
        "a root after the deadline still ran"
    );
}

#[test]
fn a_deadline_that_has_passed_runs_nothing() {
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let mut cx = Context::new();
    let es = roots(&mut cx, 16);
    let clock = FireAfter {
        reads: Cell::new(0),
        at: 0,
    };
    let out = engine
        .run(
            &mut cx,
            &es,
            Run::default().with_deadline(Deadline::new(&clock, u64::MAX).with_check_every(1)),
        )
        .unwrap();
    assert!(out.roots.iter().all(|r| !r.changed));
    assert_eq!(out.stats.salvaged, 0);
    assert_eq!(out.stats.not_started, es.len() as u64 - 1);
    assert_eq!(out.stats.new_nodes, 0, "nothing is built past the deadline");
    assert_eq!(out.stats.rewrites, 0);
    // The clock is latched: it is not read once per root.
    assert!(clock.reads.get() <= 2, "{} clock reads", clock.reads.get());
}
