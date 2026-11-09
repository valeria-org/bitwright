//! The driver's accounting: what a call does once a pass has failed verification, once a
//! budget has run out, and when it stops at a cap of its own.

use std::sync::Arc;

use bitwright::engine::{Budget, End, Engine, Exhausted, Phase, Run, Strategy, Verify};
use bitwright::ext::{ExtOp, ExtSig, Registry};
use bitwright::{
    BinOp, BitVec, Bounded, Context, ContextConfig, Expr, KnownBits, ParseOptions, Width,
};

/// `a + 1`, with known bits that say its lowest bit is 0: wrong for every even `a`.
struct LyingIncrement;

impl ExtOp for LyingIncrement {
    fn name(&self) -> &str {
        "t.inc"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a] => Ok(ExtSig::new(&[("r", *a)])),
            _ => Err("one value".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let one = BitVec::one(args[0].width());
        out[0] = BitVec::apply_bin(BinOp::Add, &args[0], &one).unwrap();
    }
    fn known_bits(&self, args: &[KnownBits], out: &mut [KnownBits]) {
        let w = args[0].width();
        out[0] = KnownBits::new(BitVec::one(w), BitVec::zero(w)).unwrap();
    }
}

/// A pass whose rewrite failed verification is quarantined: it runs no more in the call, on
/// any root, and the call after starts clean.
#[test]
fn a_pass_that_failed_verification_runs_no_more_in_the_call() {
    let registry = Registry::builder()
        .register_unchecked(LyingIncrement)
        .unwrap()
        .build();
    let inc = registry.id("t.inc").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), Arc::new(registry));
    let o = ParseOptions::width(Width::W8);
    // The wrong known bits make `inc(x) & 1` fold to 0, which sampling refutes.
    let x = cx.parse("x", &o).unwrap();
    let call = cx.ext(inc, &[x]).unwrap()[0];
    let one = cx.constant_u64(Width::W8, 1).unwrap();
    let wrong = cx.bin(BinOp::And, call, one).unwrap();
    // A fold that is right.
    let right = cx.parse("(y | 0x0f) & 0x0f", &o).unwrap();
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::new("fold", vec![Phase::FactFold]))
        .verify(Verify::default().with_sampled_points(8))
        .build()
        .unwrap();
    let out = engine
        .run(&mut cx, &[wrong, right], Run::default())
        .unwrap();
    assert_eq!(out.stats.quarantined, 1);
    assert_eq!(out.stats.passes["fact_fold"].rejected, 1);
    assert!(!out.roots[0].changed, "the refuted fold was made");
    assert!(
        !out.roots[1].changed,
        "the quarantined pass went on: {}",
        cx.display(out.roots[1].expr)
    );
    // Quarantine is for the call: nothing of it is remembered.
    let out = engine.run(&mut cx, &[right], Run::default()).unwrap();
    assert_eq!(cx.display(out.roots[0].expr).to_string(), "15:8");
}

/// `n` roots over one shared sum: `(a0·b0 + … + rewritten) · k`, where a rule rewrites the
/// last term, the first the walk comes to: the products are below a node it has only reached.
fn roots_over_a_shared_sum(cx: &mut Context, n: usize, terms: usize) -> Vec<Expr> {
    let o = ParseOptions::width(Width::W64);
    let mut shared = cx.parse("a0 * b0", &o).unwrap();
    for i in 1..terms {
        let t = cx.parse(&format!("a{i} * b{i}"), &o).unwrap();
        shared = cx.bin(BinOp::Add, shared, t).unwrap();
    }
    let rewritten = cx.parse("(p & q) + (p | q)", &o).unwrap();
    let shared = cx.bin(BinOp::Add, shared, rewritten).unwrap();
    (1..=n as u64)
        .map(|k| {
            let k = cx.constant_u64(Width::W64, 2 * k + 1).unwrap();
            cx.bin(BinOp::Mul, shared, k).unwrap()
        })
        .collect()
}

fn nodes(cx: &mut Context, e: Expr) -> u64 {
    match cx.dag_size(&[e], u32::MAX).unwrap() {
        Bounded::Exact(n) | Bounded::AtLeast(n) => u64::from(n),
        _ => unreachable!("a size is exact or a bound"),
    }
}

/// A budget stop keeps what the stopped phase did (the root is salvaged), and the walk that
/// does it is node visits like any other: the nodes the stopped phase had reached are charged
/// already, each node below them is a visit, and with none left the root stays as it is.
#[test]
fn salvaging_after_a_budget_stop_is_charged() {
    let engine = Engine::standard();
    let (n, terms) = (48, 400);
    // No rewrite is allowed: every root stops at the first one, with the products of the
    // shared sum not yet walked. Salvaging a root reads them all.
    let stop = Budget::default().with_rewrites(0);
    let mut cx = Context::new();
    let roots = roots_over_a_shared_sum(&mut cx, n, terms);
    let size = nodes(&mut cx, roots[0]);
    let out = engine
        .run(&mut cx, &roots, Run::default().with_per_call(stop))
        .unwrap();
    assert_eq!(out.stats.salvaged, n as u64);
    let stopped = |end: End| end == End::BudgetTerminated(Exhausted::Rewrites);
    assert!(out.roots.iter().all(|r| stopped(r.end) && !r.changed));
    assert!(
        out.stats.node_visits > (n as u64 - 8) * size,
        "{} visits for {n} roots of {size} nodes",
        out.stats.node_visits
    );
    // So visits for a few roots run out, and the roots after that are not read.
    let few = stop.with_node_visits(8 * size);
    let mut cx = Context::new();
    let roots = roots_over_a_shared_sum(&mut cx, n, terms);
    let out = engine
        .run(&mut cx, &roots, Run::default().with_per_call(few))
        .unwrap();
    assert!(stopped(out.roots[0].end));
    assert_eq!(
        out.roots[n - 1].end,
        End::BudgetTerminated(Exhausted::NodeVisits)
    );
    assert!(out.roots.iter().all(|r| !r.changed));
    assert!(out.stats.node_visits <= 8 * size);
}

/// The uses the other roots of a call contribute are counted once per root, and charged when
/// they are counted: a phase run in which the count stands costs nothing for it.
#[test]
fn the_other_roots_are_charged_when_they_are_counted() {
    let engine = Engine::standard();
    let o = ParseOptions::width(Width::W64);
    let small = "((x ^ y) + ((x & y) << 1)) * ((x | y) - (x & ~y))";
    let big: String = (0..600)
        .map(|i| format!("udiv(c{i}, d{i})"))
        .collect::<Vec<_>>()
        .join(" ^ ");
    let alone = |src: &str| {
        let mut cx = Context::new();
        let e = cx.parse(src, &o).unwrap();
        let n = nodes(&mut cx, e);
        (engine.run(&mut cx, &[e], Run::default()).unwrap().stats, n)
    };
    let ((a, na), (b, nb)) = (alone(small), alone(&big));
    let mut cx = Context::new();
    let roots = [cx.parse(small, &o).unwrap(), cx.parse(&big, &o).unwrap()];
    let both = engine.run(&mut cx, &roots, Run::default()).unwrap().stats;
    // Each root counts the other once, at most a unit a node.
    assert!(
        both.pass_work <= a.pass_work + b.pass_work + na + nb,
        "{} for both, {} and {} alone, of {na} and {nb} nodes",
        both.pass_work,
        a.pass_work,
        b.pass_work
    );
}

/// A strategy stops at its cap on rounds whether or not the last one settled the root:
/// `Stats::rounds_capped` tells the two apart.
#[test]
fn stopping_at_the_cap_on_rounds_is_counted() {
    let o = ParseOptions::width(Width::W32);
    let run = |strategy: Strategy, src: &str| {
        let engine = Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap();
        let mut cx = Context::new();
        let e = cx.parse(src, &o).unwrap();
        let out = engine.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(out.roots[0].end, End::Completed);
        (
            out.roots[0].changed,
            out.stats.rounds,
            out.stats.rounds_capped,
        )
    };
    let src = "((x ^ y) + ((x & y) << 1)) - y";
    // One round changes the root, and there is no second to see that it is settled.
    assert_eq!(
        run(Strategy::standard().with_max_rounds(1), src),
        (true, 1, 1)
    );
    // With rounds to spare, the last one changes nothing.
    assert_eq!(run(Strategy::standard(), src), (true, 2, 0));
    // A root no round changes settles in the first.
    assert_eq!(
        run(Strategy::standard().with_max_rounds(1), "x * y"),
        (false, 1, 0)
    );
}

/// `m` roots `(p + q) + (r − q)`, the `q` of each the product of the two sums of the one
/// before. The linear pass's `p + r` is smaller only once those sums have no other use: once
/// the root after has been rewritten. So the roots settle from the last one back, one for
/// each time the call runs them again.
fn roots_waiting_on_the_next(cx: &mut Context, m: usize) -> Vec<Expr> {
    let o = ParseOptions::width(Width::W32);
    let mut q = cx.parse("q", &o).unwrap();
    let mut roots = Vec::new();
    for i in 0..m {
        let p = cx.parse(&format!("p{i}"), &o).unwrap();
        let r = cx.parse(&format!("r{i}"), &o).unwrap();
        let a = cx.bin(BinOp::Add, p, q).unwrap();
        let b = cx.bin(BinOp::Sub, r, q).unwrap();
        roots.push(cx.bin(BinOp::Add, a, b).unwrap());
        q = cx.bin(BinOp::Mul, a, b).unwrap();
    }
    roots
}

/// A call runs the roots that sharing held back again while that changes one, three times at
/// most: `Stats::reruns_capped` says when it stopped there with roots still changing.
#[test]
fn stopping_at_the_cap_on_reruns_is_counted() {
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::new("linear", vec![Phase::Linear]))
        .build()
        .unwrap();
    let run = |m: usize| {
        let mut cx = Context::new();
        let roots = roots_waiting_on_the_next(&mut cx, m);
        let out = engine.run(&mut cx, &roots, Run::default()).unwrap();
        let texts: Vec<String> = out
            .roots
            .iter()
            .map(|r| cx.display(r.expr).to_string())
            .collect();
        // What the call left, run again.
        let left: Vec<Expr> = out.roots.iter().map(|r| r.expr).collect();
        let again = engine.run(&mut cx, &left, Run::default()).unwrap();
        let changed = again.roots.iter().filter(|r| r.changed).count();
        (out.stats.reruns_capped, texts, changed)
    };
    // Four roots: the last settles at once, the others in the three runs after.
    let (capped, texts, changed_again) = run(4);
    assert_eq!(capped, 0);
    assert_eq!(texts, ["p0 + r0", "p1 + r1", "p2 + r2", "p3 + r3"]);
    assert_eq!(changed_again, 0);
    // Five: the first is still as written, and the stat says there was more to do.
    let (capped, texts, changed_again) = run(5);
    assert_eq!(capped, 1);
    assert_eq!(texts[1..], ["p1 + r1", "p2 + r2", "p3 + r3", "p4 + r4"]);
    assert_eq!(texts[0], "p0 + q + (r0 - q)");
    assert_eq!(changed_again, 1);
}
