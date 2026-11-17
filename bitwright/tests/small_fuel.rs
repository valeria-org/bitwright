//! A devirtualizer's questions asked with little fuel (`1 << 14`: sixteen MBA solver calls and
//! 262,144 units of pass work), where what one pass spends decides what the passes after it
//! still get to do.
//!
//! `questions/limb_product_0001.txt` is `x * k ^ c` as a protector's handler computes it, in
//! 26-bit limbs with the carries written out. The simplifier folds the limbs back into one
//! product in its later rounds (the word pass, once the MBA phase has rewritten the limb sum),
//! and the search then proves the rest. Two things kept it from getting there:
//!
//! - the linear-MBA pass's decomposition over the basis of small bitwise functions read every
//!   coefficient of a sum's `2^t` for each residual it scored, 27,296 units for a sum over
//!   seven atoms with a handful of coefficients, and the call ran out of pass work;
//! - the MBA phase's seventeenth question ended the whole call, in its first round.
//!
//! `questions/linear_sum_000*.txt` are sums the same release learned to solve, kept so: a
//! chain of sixteen products that are each as small as they get, and a masked sum over bit
//! tests.
#![cfg(all(feature = "mba", feature = "prove"))]

use bitwright::engine::{Budget, End, Engine, Exhausted, Run, Strategy};
use bitwright::mba::MbaConfig;
use bitwright::prove::{Config, Outcome, Question};
use bitwright::{Bounded, CmpOp, Context, Expr, ParseOptions, Width};

const LIMB_PRODUCT: &str = include_str!("questions/limb_product_0001.txt");
const LINEAR_SUMS: [(&str, u32); 2] = [
    (include_str!("questions/linear_sum_0001.txt"), 26),
    (include_str!("questions/linear_sum_0002.txt"), 24),
];

fn parse(cx: &mut Context, text: &str) -> Expr {
    cx.parse(text, &ParseOptions::width(Width::W64))
        .unwrap_or_else(|err| panic!("{text}: {err}"))
}

fn nodes(cx: &mut Context, e: Expr) -> u32 {
    match cx.dag_size(&[e], u32::MAX).expect("a size") {
        Bounded::Exact(n) => n,
        other => panic!("{other:?}"),
    }
}

/// The limb product and the product it is, as one equality.
fn limb_question(cx: &mut Context) -> (Expr, Expr) {
    let limbs = parse(cx, LIMB_PRODUCT);
    let product = parse(cx, "#0:64 * 0xcfd6dd0294305707 ^ 0x9d96f7387adba9c8");
    (limbs, product)
}

/// The prover as the devirtualizer configures it: fuel `1 << 14`, 20,000 conflicts.
#[test]
fn a_limb_product_is_proved_with_small_fuel() {
    let mut cx = Context::new();
    let (limbs, product) = limb_question(&mut cx);
    let cfg = Config::default()
        .with_simplify_fuel(1 << 14)
        .with_sweeping(false)
        .with_max_conflicts(20_000)
        .with_max_propagations(4_000_000);
    let mut q = Question::equal(&mut cx, limbs, product, &cfg).expect("a question");
    let out = q.solve(&mut cx, cfg.limits()).expect("an answer");
    assert!(matches!(out, Outcome::Proved(_)), "{out:?}");
    // The simplifier did run out of MBA calls: that no longer ends its call.
    let stats = q.stats();
    assert_eq!(stats.simplification.stopped, Some(Exhausted::MbaCalls));
}

/// Out of MBA calls, the engine goes on with what the other passes can still pay for: the
/// limbs are one product after the later rounds (37 nodes here, 24 through the prover's
/// engine; 68 where the call ended at the seventeenth question).
#[test]
fn out_of_mba_calls_the_other_passes_go_on() {
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
        .build()
        .expect("an engine");
    let mut cx = Context::new();
    let (limbs, product) = limb_question(&mut cx);
    let goal = cx.cmp(CmpOp::Eq, limbs, product).expect("an equality");
    let run = Run::default().with_per_call(Budget::fuel(1 << 14));
    let out = engine.run(&mut cx, &[goal], run).expect("a run");
    assert_eq!(out.roots[0].end, End::BudgetTerminated(Exhausted::MbaCalls));
    assert_eq!(out.stats.mba.calls, 16);
    assert!(out.stats.rounds > 1, "{} round(s)", out.stats.rounds);
    let left = nodes(&mut cx, out.roots[0].expr);
    assert!(
        left <= 40,
        "{left} nodes: {}",
        cx.display(out.roots[0].expr)
    );
}

/// The linear-MBA pass's work on the limb question: the decomposition reads the coefficients
/// that are not zero, so the passes after it keep theirs (the call ran out at 262,144).
#[test]
fn the_decomposition_reads_only_what_is_there() {
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .expect("an engine");
    let mut cx = Context::new();
    let (limbs, product) = limb_question(&mut cx);
    let goal = cx.cmp(CmpOp::Eq, limbs, product).expect("an equality");
    let run = Run::default().with_per_call(Budget::fuel(1 << 14));
    let out = engine.run(&mut cx, &[goal], run).expect("a run");
    assert_eq!(out.roots[0].end, End::Completed);
    assert!(
        out.stats.pass_work < 160_000,
        "{} units of pass work",
        out.stats.pass_work
    );
}

/// What 0.32.0 gained stays: each sum is solved whole, to at most the nodes it reached then
/// (123 and 27 before).
#[test]
fn linear_sums_stay_solved() {
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default().with_opaque_sweep(true)))
        .build()
        .expect("an engine");
    for (text, most) in LINEAR_SUMS {
        let mut cx = Context::new();
        let e = parse(&mut cx, text);
        let run = Run::default().with_per_call(Budget::fuel(1 << 21));
        let out = engine.run(&mut cx, &[e], run).expect("a run").roots[0].expr;
        let left = nodes(&mut cx, out);
        assert!(
            left <= most,
            "{left} nodes, over {most}: {}",
            cx.display(out)
        );
    }
}
