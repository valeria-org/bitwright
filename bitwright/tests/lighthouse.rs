//! A devirtualizer's questions from lighthouse.sys (`0x1401a5060`), which 0.31.7 answered and
//! 0.32.1 did not.
//!
//! `questions/lighthouse_fold_000*.txt` are sums the devirtualizer's engine folds to a
//! constant (the stock MBA phase with the opaque sweep, fuel `2^19`). 0.32 left them as sums
//! two ways: the MBA phase kept a fragment with no simpler form back from the questions above
//! it only past 2^16 solver steps ([`Strategy::kept_steps`]), and the larger questions it then
//! asked spent the budget before the ones that fold (six of the eight); and the normal form's
//! answers could be sums over the basis of small bitwise functions
//! ([`NfOptions::basis_sums`]), which the questions above them then no longer fold (the other
//! two). With both as the devirtualizer sets them, each folds.
//!
//! `questions/lighthouse_proved_0001.txt` is a question the prover proves under its facts at
//! its smallest limits on simplifiers that write no basis sums
//! ([`Simplifiers::with_basis_sums`]): 0.32.1 left it unknown at 10,000,000 propagations.
#![cfg(all(feature = "mba", feature = "prove"))]

use std::sync::Arc;

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::{MbaConfig, MbaSolver, NfOptions, NormalFormSolver};
use bitwright::prove::{Config, Outcome, Simplifiers};
use bitwright::{Assumptions, BitVec, Context, ParseOptions, View, Width};

const FOLDS: [&str; 8] = [
    include_str!("questions/lighthouse_fold_0001.txt"),
    include_str!("questions/lighthouse_fold_0002.txt"),
    include_str!("questions/lighthouse_fold_0003.txt"),
    include_str!("questions/lighthouse_fold_0004.txt"),
    include_str!("questions/lighthouse_fold_0005.txt"),
    include_str!("questions/lighthouse_fold_0006.txt"),
    include_str!("questions/lighthouse_fold_0007.txt"),
    include_str!("questions/lighthouse_fold_0008.txt"),
];

const PROVED: &str = include_str!("questions/lighthouse_proved_0001.txt");

/// The engine as the devirtualizer builds it.
fn devirtualizer_engine() -> Engine {
    let solver: Arc<dyn MbaSolver> = Arc::new(NormalFormSolver::new(
        NfOptions::default()
            .with_memo(1 << 14)
            .with_basis_sums(false),
    ));
    let strategy = Strategy::deobfuscate()
        .with_mba(MbaConfig::default().with_opaque_sweep(true))
        .with_basis_sums(false)
        .with_kept_steps(1 << 12);
    Engine::builder()
        .builtin()
        .strategy(strategy)
        .mba_solver(solver)
        .build()
        .expect("an engine")
}

#[test]
fn the_devirtualizers_sums_fold() {
    let engine = devirtualizer_engine();
    for (i, text) in FOLDS.iter().enumerate() {
        let mut cx = Context::new();
        let e = cx
            .parse(text.trim(), &ParseOptions::width(Width::W64))
            .expect("a question");
        let run = Run::default().with_per_call(Budget::fuel(1 << 19));
        let out = engine.run(&mut cx, &[e], run).expect("a run").roots[0].expr;
        assert!(
            matches!(cx.view(out), Ok(View::Const(_))),
            "sum {}: {}",
            i + 1,
            cx.display(out)
        );
    }
}

#[test]
fn the_prover_proves_its_question_at_small_limits() {
    let (mut root, mut facts) = (String::new(), Vec::<(u64, String)>::new());
    for line in PROVED.lines() {
        if line.starts_with("## root") {
            continue;
        }
        if let Some(v) = line.strip_prefix("## assume == ") {
            let v = u64::from_str_radix(v.trim_start_matches("0x"), 16).expect("a value");
            facts.push((v, String::new()));
            continue;
        }
        match facts.last_mut() {
            Some((_, text)) => text.push_str(line),
            None => root.push_str(line),
        }
        match facts.last_mut() {
            Some((_, text)) => text.push('\n'),
            None => root.push('\n'),
        }
    }
    let mut cx = Context::new();
    let opts = ParseOptions::width(Width::W64);
    let e = cx.parse(&root, &opts).expect("the question");
    let w = cx.width(e).expect("a width");
    let k = cx
        .constant(&BitVec::wrapping_from_u64(w, 0x069b_8404_bfa2_9b60))
        .expect("a constant");
    let p = cx.eq(e, k).expect("the equality");
    let mut a = Assumptions::default();
    for (v, text) in &facts {
        let f = cx.parse(text, &opts).expect("a fact");
        let fw = cx.width(f).expect("a width");
        let fv = cx
            .constant(&BitVec::wrapping_from_u64(fw, *v))
            .expect("a value");
        let fp = cx.eq(f, fv).expect("the fact");
        a.assume_true(&mut cx, fp).expect("assumed");
    }
    let mut cfg = Config::default();
    cfg.max_conflicts = 2_000;
    cfg.max_propagations = 20_000;
    let simplifiers = Simplifiers::new()
        .with_basis_sums(false)
        .with_kept_steps(1 << 12);
    let out = bitwright::prove::valid_under_with(&mut cx, p, Some(&a), &cfg, &simplifiers)
        .expect("an answer");
    assert!(matches!(out, Outcome::Proved(_)), "{out:?}");
}
