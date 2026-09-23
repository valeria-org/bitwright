//! Extension operations at the edges: every output of every test operation (1 to 3 arguments,
//! 1 to 8 outputs, mixed argument widths, a commutative pair and an opaque call) at boundary
//! argument values of widths from 1 to 512 bits:
//!
//! - a call on constants folds to constants equal to the operation's independent reference
//!   definition;
//! - a call on symbols evaluates to the same values;
//! - a commutative call is one node whichever way its pair is given;
//! - facts under constraints that pin every argument are exactly the reference value.
//!
//! Random DAGs mixing these calls with every built-in operator run through the generic suites
//! (`heavy_exprs`, `heavy_facts`, `heavy_constraints`, `heavy_simplify`, `heavy_roundtrip`),
//! which build a third of their DAGs with calls.

mod common;

use bitwright::{Assumptions, BitVec, CmpOpExt, Expr, SymbolKey};
use common::{
    ExtKind, SMOKE_WIDTHS, Size, WIDTHS, boundary_values, core_values, ext_context, from_ref,
    registry, to_ref, w,
};

/// Argument widths of `kind` when its value operands have `n` bits (and a count has `c` bits).
fn arg_widths(kind: ExtKind, n: u16, c: u16) -> Vec<u16> {
    match kind {
        ExtKind::AddC => vec![n, n, 1],
        ExtKind::DivMod | ExtKind::Flags => vec![n, n],
        ExtKind::Fsh => vec![n, n, c],
        ExtKind::Mix => vec![n],
    }
}

fn calls(size: Size) {
    let reg = registry();
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    let mut checked = 0;
    for kind in ExtKind::ALL {
        let id = reg.id(kind.name()).unwrap();
        for &n in &widths {
            if kind == ExtKind::Fsh && n > 256 {
                continue;
            }
            for c in [1u16, 7, 64, 512] {
                if kind != ExtKind::Fsh && c != 1 {
                    continue;
                }
                let aw = arg_widths(kind, n, c);
                let mut cx = ext_context(&reg);
                let syms: Vec<Expr> = aw
                    .iter()
                    .enumerate()
                    .map(|(k, &b)| cx.symbol(format!("a{k}").as_str(), w(b)).unwrap())
                    .collect();
                let outs = cx.ext(id, &syms).unwrap();
                // Values: the boundary values of each argument's width (a few in smoke runs).
                let vals: Vec<Vec<BitVec>> = aw
                    .iter()
                    .map(|&b| {
                        size.pick(
                            core_values(w(b))[..].iter().take(4).copied().collect(),
                            boundary_values(w(b)),
                        )
                    })
                    .collect();
                for args in combinations(&vals) {
                    let refs: Vec<bitwright_ref::Bits> = args.iter().map(to_ref).collect();
                    let want: Vec<BitVec> = kind
                        .eval_ref(&refs.iter().collect::<Vec<_>>())
                        .iter()
                        .map(from_ref)
                        .collect();
                    let what = format!("{}({args:?})", kind.name());
                    // On constants: folded.
                    let consts: Vec<Expr> = args.iter().map(|a| cx.constant(a).unwrap()).collect();
                    let folded = cx.ext(id, &consts).unwrap();
                    for (o, (e, v)) in folded.iter().zip(&want).enumerate() {
                        assert_eq!(cx.as_const(*e).unwrap(), Some(*v), "{what}[{o}] folded");
                    }
                    // On symbols: evaluated.
                    let env: Vec<(SymbolKey, BitVec)> = args
                        .iter()
                        .enumerate()
                        .map(|(i, a)| (SymbolKey::from(format!("a{i}")), *a))
                        .collect();
                    let got = cx.eval(&outs, &env[..]).unwrap();
                    assert_eq!(got, want, "{what} evaluated");
                    // Facts when constraints pin every argument: exact.
                    let mut a = Assumptions::new();
                    for (s, v) in syms.iter().zip(&args) {
                        let ve = cx.constant(v).unwrap();
                        let p = cx.cmp(CmpOpExt::Eq, *s, ve).unwrap();
                        a.assume_true(&mut cx, p).unwrap();
                    }
                    for (o, (e, v)) in outs.iter().zip(&want).enumerate() {
                        let f = cx.facts_with(*e, &a).unwrap().expect("feasible");
                        assert_eq!(f.as_constant(), Some(*v), "{what}[{o}] pinned facts {f:?}");
                        let base = cx.facts(*e).unwrap();
                        assert!(base.contains(v), "{what}[{o}] facts {base:?}");
                    }
                    // A commutative pair is one node either way round.
                    if kind == ExtKind::AddC {
                        let swapped = cx.ext(id, &[syms[1], syms[0], syms[2]]).unwrap();
                        assert_eq!(swapped, outs, "{what}: the pair is canonical");
                    }
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 100, "only {checked} calls");
}

/// Every value of a single argument; every pair of the first two; the third (a carry or a
/// count) cycling along.
fn combinations(vals: &[Vec<BitVec>]) -> Vec<Vec<BitVec>> {
    match vals {
        [a] => a.iter().map(|x| vec![*x]).collect(),
        [a, b, rest @ ..] => {
            let mut out = Vec::new();
            for (i, x) in a.iter().enumerate() {
                for (j, y) in b.iter().enumerate() {
                    let mut v = vec![*x, *y];
                    if let [c] = rest {
                        v.push(c[(i * b.len() + j) % c.len()]);
                    }
                    out.push(v);
                }
            }
            out
        }
        [] => Vec::new(),
    }
}

#[test]
fn calls_at_boundary_values_match_the_reference_smoke() {
    calls(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn calls_at_boundary_values_match_the_reference_heavy() {
    calls(Size::Heavy);
}
