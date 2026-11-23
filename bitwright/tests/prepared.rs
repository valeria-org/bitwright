//! Per-target assumptions on a shared circuit must not leak even when search is interrupted.
#![cfg(feature = "prove")]

use bitwright::prove::{Config, Model, Prepared, Simplifiers, Unknown};
use bitwright::{BitVec, Context, KnownBits, ParseOptions, Width};

fn byte(x: u64) -> BitVec {
    BitVec::from_u64(Width::W8, x).unwrap()
}

fn ask(cfg: &Config, order: [usize; 3]) -> Vec<Result<Option<Model>, Unknown>> {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let fact = cx.parse("x * 3 == y", &o).unwrap();
    let extra = cx.parse("y == 21", &o).unwrap();
    let x = cx.parse("x", &o).unwrap();
    let mut family = Prepared::new(&mut cx, &[fact], &[x, extra], cfg, &Simplifiers::new())
        .unwrap()
        .unwrap();
    let queries = [
        [(0, byte(7)), (1, BitVec::from_bool(true))],
        [(0, byte(7)), (1, BitVec::from_bool(false))],
        [(0, byte(8)), (1, BitVec::from_bool(false))],
    ];
    let answers: Vec<_> = order
        .iter()
        .map(|&i| family.check(&queries[i]).unwrap())
        .collect();
    drop(family);
    for (&i, answer) in order.iter().zip(&answers) {
        if let Ok(Some(m)) = answer {
            let actual = cx.eval(&[fact, x, extra], m.as_slice()).unwrap();
            assert_eq!(
                actual,
                [BitVec::from_bool(true), queries[i][0].1, queries[i][1].1]
            );
        }
    }
    answers
}

#[test]
fn targets_are_independent_including_when_the_budget_runs_out() {
    let cfg = Config::default().with_sweeping(false).with_samples(0);
    for budget in [1, 100_000] {
        let cfg = cfg.with_max_propagations(budget);
        let forward = ask(&cfg, [0, 1, 2]);
        let mut reverse = ask(&cfg, [2, 1, 0]);
        reverse.reverse();
        assert_eq!(forward, reverse);
        if budget == 1 {
            assert!(
                forward.iter().any(|a| matches!(a, Err(Unknown::Budget { .. })))
            );
        } else {
            assert!(matches!(
                forward.as_slice(),
                [Ok(Some(_)), Ok(None), Ok(Some(_))]
            ));
        }
    }
}

#[test]
fn declared_and_simplified_away_symbols_are_in_original_models() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    cx.declare_known(x, KnownBits::new(byte(0), byte(0x80)).unwrap())
        .unwrap();
    let o = ParseOptions::width(Width::W8);
    let neutral = cx.parse("(x | z) + (x & z) == x + z", &o).unwrap();
    let cfg = Config::default().with_sweeping(false);
    let mut p = Prepared::new(&mut cx, &[neutral], &[x], &cfg, &Simplifiers::new())
        .unwrap()
        .unwrap();
    assert_eq!(p.check(&[(0, byte(0))]).unwrap(), Ok(None));
    let model = p.check(&[(0, byte(0x80))]).unwrap().unwrap().unwrap();
    drop(p);
    assert_eq!(
        cx.eval(&[x, neutral], model.as_slice()).unwrap(),
        [byte(0x80), BitVec::from_bool(true)]
    );
}

#[test]
fn invalid_unsupported_and_too_large_families_do_not_answer_unsat() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let cfg = Config::default().with_sweeping(false);
    let engines = Simplifiers::new();
    assert!(Prepared::new(&mut cx, &[x], &[], &cfg, &engines).is_err());
    for unsupported in [
        cfg.with_certificate(true),
        cfg.with_sweeping(true),
        cfg.with_exhaustive_inputs(8),
    ] {
        assert!(matches!(
            Prepared::new(&mut cx, &[], &[x], &unsupported, &engines).unwrap(),
            Err(Unknown::Unsupported(_))
        ));
    }
    assert!(matches!(
        Prepared::new(&mut cx, &[], &[x], &cfg.with_max_nodes(1), &engines).unwrap(),
        Err(Unknown::TooLarge { .. })
    ));
    let f = cx.bool(false).unwrap();
    let mut p = Prepared::new(&mut cx, &[f], &[x], &cfg, &engines)
        .unwrap()
        .unwrap();
    assert!(p.check(&[(0, BitVec::from_bool(true))]).is_err());
    assert!(p.check(&[(usize::MAX, byte(0))]).is_err());
    assert_eq!(p.check(&[]).unwrap(), Ok(None));
}
