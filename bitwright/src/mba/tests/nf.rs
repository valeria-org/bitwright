//! The normal-form solver: normal forms and every candidate equal to the input (exhaustively at
//! small widths), certified answers, the catalog, and no regression against the signature
//! solver.

use super::random::*;
use crate::mba::batch::Program;
use crate::mba::certify::{self, Steps};
use crate::mba::nf::inspect;
use crate::mba::{
    Claim, MOp, MbaAnswer, MbaBudget, MbaExpr, MbaSolver, NfOptions, NormalFormSolver,
    SignatureSolver, Verdict,
};
use crate::{BitVec, Width};

/// The nodes an expression's root uses, counting equal subterms once and a shift's amount as
/// the constant node it is once lifted (shared with an equal constant).
fn cost(m: &MbaExpr) -> usize {
    use std::collections::HashMap;
    let mut live = vec![false; m.nodes().len()];
    if let Some(l) = live.last_mut() {
        *l = true;
    }
    for i in (0..m.nodes().len()).rev() {
        if live[i] {
            let n = m.nodes()[i];
            for &k in &n.args[..n.op.arity()] {
                live[k as usize] = true;
            }
        }
    }
    let mut canon: Vec<u32> = Vec::new();
    let mut seen: HashMap<crate::mba::MNode, u32> = HashMap::new();
    let mut count = 0;
    for (i, n) in m.nodes().iter().enumerate() {
        let mut key = *n;
        for k in 0..n.op.arity() {
            key.args[k] = canon[n.args[k] as usize];
        }
        if matches!(key.op, MOp::Add | MOp::Mul | MOp::And | MOp::Or | MOp::Xor)
            && key.args[0] > key.args[1]
        {
            key.args.swap(0, 1);
        }
        let c = *seen.entry(key).or_insert_with(|| {
            count += usize::from(live[i]);
            i as u32
        });
        canon.push(c);
    }
    let mut consts: Vec<BitVec> = m
        .nodes()
        .iter()
        .zip(&live)
        .filter_map(|(n, &l)| match n.op {
            MOp::Const(v) if l => Some(v),
            _ => None,
        })
        .collect();
    for (n, &l) in m.nodes().iter().zip(&live) {
        if let MOp::Shl(k) | MOp::LShr(k) = n.op
            && l
        {
            let v = BitVec::wrapping_from_u64(n.width, u64::from(k));
            if !consts.contains(&v) {
                consts.push(v);
                count += 1;
            }
        }
    }
    count
}

#[test]
fn normal_forms_and_candidates_equal_the_input_exhaustively() {
    let mut checked = 0;
    for w in 1..=6u16 {
        let width = Width::new(w).unwrap();
        let t = if w <= 4 { 3 } else { 2 };
        let vars = vec![width; t as usize];
        for (fi, frag) in [
            Frag::Linear,
            Frag::SemiLinear,
            Frag::Poly,
            Frag::PurePoly,
            Frag::Any,
        ]
        .into_iter()
        .enumerate()
        {
            let mut g = Gen::new(0x9f00 + u64::from(w) * 8 + fi as u64, width, t);
            for _ in 0..40 {
                let e = g.expr(frag, 3);
                let m = e.expr(&vars);
                let Some((naive, cands)) = inspect(&m, &NfOptions::default()) else {
                    continue;
                };
                assert!(
                    equal_everywhere(&m, &naive),
                    "normal form of {e:?}:\n{naive:?}"
                );
                for c in &cands {
                    assert!(equal_everywhere(&m, c), "candidate of {e:?}:\n{c:?}");
                }
                checked += 1 + cands.len();
            }
        }
    }
    assert!(checked > 1000, "{checked}");
}

#[test]
fn answers_are_equal_smaller_and_proved() {
    let solver = NormalFormSolver::default();
    let mut simplified = 0;
    for w in 1..=6u16 {
        let width = Width::new(w).unwrap();
        let t = if w <= 4 { 3 } else { 2 };
        let vars = vec![width; t as usize];
        for (fi, frag) in [
            Frag::Linear,
            Frag::SemiLinear,
            Frag::Poly,
            Frag::PurePoly,
            Frag::Any,
        ]
        .into_iter()
        .enumerate()
        {
            let mut g = Gen::new(0x5a00 + u64::from(w) * 8 + fi as u64, width, t);
            for _ in 0..40 {
                let e = g.expr(frag, 3);
                let m = e.expr(&vars);
                match solver.solve(&m, &MbaBudget::default()) {
                    MbaAnswer::Simplified { expr, claim } => {
                        assert!(equal_everywhere(&m, &expr), "{e:?}\n{expr:?}");
                        assert!(cost(&expr) < cost(&m), "{e:?}\n{expr:?}");
                        // Over abstracted atoms a proof may be out of reach (atoms related in
                        // ways a skeleton cannot see): then only the sample vouches.
                        if frag != Frag::Any {
                            assert_eq!(claim, Claim::Proved);
                        }
                        simplified += 1;
                        // Idempotent: the answer is already as simple.
                        assert_eq!(
                            solver.solve(&expr, &MbaBudget::default()),
                            MbaAnswer::NoSimpler,
                            "{expr:?}"
                        );
                    }
                    MbaAnswer::NoSimpler => {}
                    other => panic!("{e:?}: {other:?}"),
                }
            }
        }
    }
    assert!(simplified > 400, "{simplified}");
    let s = solver.stats();
    assert_eq!(s.declined_internal, 0);
    assert!(s.linear > 0 && s.semilinear > 0 && s.polynomial > 0 && s.candidates > 0);
    assert!(s.abstracted > 0 && s.atoms > 0);
}

/// Solves `e`, checks the answer (by a certificate) and that it is no larger than `want`.
fn solves_to(e: &T, want: &T, vars: &[Width]) -> MbaExpr {
    let m = e.expr(vars);
    let want = want.expr(vars);
    let MbaAnswer::Simplified { expr, claim } =
        NormalFormSolver::default().solve(&m, &MbaBudget::default().with_steps(1 << 26))
    else {
        panic!("not simplified: {e:?}");
    };
    let r = certify::prove(&m, &expr, &mut Steps::new(1 << 26)).unwrap();
    if claim == Claim::Sampled {
        // Only when no certificate is within the effort cap (wide, nonlinear): then the sample
        // agrees, and more points do too.
        assert!(
            r.verdict == Verdict::Unknown && !r.over_budget,
            "{e:?}: {r:?}"
        );
        let mut rng = crate::testutil::Rng(7);
        for _ in 0..2000 {
            let p: Vec<BitVec> = vars
                .iter()
                .map(|&w| BitVec::wrapping_from_limbs(w, &[rng.next(), rng.next(), rng.next()]))
                .collect();
            assert_eq!(m.eval(&p), expr.eval(&p), "{e:?}");
        }
    } else {
        assert_eq!(claim, Claim::Proved, "{e:?}");
        assert_eq!(r.verdict, Verdict::Proved, "{e:?} -> {expr:?}");
    }
    assert!(
        cost(&expr) <= cost(&want),
        "{e:?}\n  gave {expr:?}\n  want {want:?}"
    );
    expr
}

#[test]
fn the_linear_and_semi_linear_catalog() {
    for w in [8u16, 16, 32, 64, 128, 512] {
        let width = Width::new(w).unwrap();
        let vars = [width, width];
        let (x, y) = (V(0), V(1));
        let c = |v: u64| C(BitVec::wrapping_from_u64(width, v));
        let two = || k(width, 2);
        // Linear.
        solves_to(
            &add(
                xor(x.clone(), y.clone()),
                mul(two(), and(x.clone(), y.clone())),
            ),
            &add(x.clone(), y.clone()),
            &vars,
        );
        solves_to(
            &sub(or(x.clone(), y.clone()), and(x.clone(), y.clone())),
            &xor(x.clone(), y.clone()),
            &vars,
        );
        solves_to(
            &sub(
                and(x.clone(), not(y.clone())),
                and(not(x.clone()), y.clone()),
            ),
            &sub(x.clone(), y.clone()),
            &vars,
        );
        // Semi-linear.
        solves_to(
            &add(xor(x.clone(), c(0x10)), mul(two(), and(x.clone(), c(0x10)))),
            &add(x.clone(), c(0x10)),
            &vars,
        );
        if w >= 16 {
            solves_to(
                &add(and(x.clone(), c(0xff)), and(x.clone(), c(0xff00))),
                &and(x.clone(), c(0xffff)),
                &vars,
            );
        }
        let e = solves_to(
            &add(
                mul(k(width, 3), and(x.clone(), c(0x55))),
                mul(k(width, 3), and(x.clone(), c(0xaa))),
            ),
            &mul(k(width, 3), and(x.clone(), c(0xff))),
            &vars,
        );
        if w == 8 {
            // The mask covers every position and disappears.
            assert_eq!(cost(&e), cost(&mul(k(width, 3), x.clone()).expr(&vars)));
        }
    }
}

#[test]
fn the_polynomial_catalog() {
    for w in [8u16, 16, 32, 64, 128, 512] {
        let width = Width::new(w).unwrap();
        let vars = [width, width];
        let (x, y) = (V(0), V(1));
        // (x & y)(x | y) + (x & ~y)(~x & y) = x·y: every product cancels but one.
        let e = add(
            mul(and(x.clone(), y.clone()), or(x.clone(), y.clone())),
            mul(
                and(x.clone(), not(y.clone())),
                and(not(x.clone()), y.clone()),
            ),
        );
        solves_to(&e, &mul(x.clone(), y.clone()), &vars);
        // 2^(W−1)·(x² + x) = 0: x(x + 1) is even.
        let half = C(BitVec::smin(width));
        solves_to(
            &mul(half.clone(), add(mul(x.clone(), x.clone()), x.clone())),
            &k(width, 0),
            &vars,
        );
        // (x + 1)² − x² − 2x = 1.
        let x1 = add(x.clone(), k(width, 1));
        solves_to(
            &sub(
                sub(mul(x1.clone(), x1), mul(x.clone(), x.clone())),
                mul(k(width, 2), x.clone()),
            ),
            &k(width, 1),
            &vars,
        );
        // −x² stays −x², not (2^(W−1) − 1)·x² + 2^(W−1)·x.
        let m = sub(k(width, 0), mul(x.clone(), x.clone())).expr(&vars);
        let (naive, _) = inspect(&m, &NfOptions::default()).unwrap();
        assert!(cost(&naive) <= 3 + 1, "{naive:?}");
        // A product of bitwise terms comes out factored: x·(x&y) + y·(x&y) − (x&y)² is
        // (x | y)·(x & y).
        let a = and(x.clone(), y.clone());
        solves_to(
            &sub(
                add(mul(x.clone(), a.clone()), mul(y.clone(), a.clone())),
                mul(a.clone(), a.clone()),
            ),
            &mul(or(x.clone(), y.clone()), a),
            &vars,
        );
    }
}

#[test]
fn the_abstraction_catalog() {
    for w in [8u16, 16, 32, 64, 128, 512] {
        let width = Width::new(w).unwrap();
        let vars = [width, width, width];
        let (x, y, z) = (V(0), V(1), V(2));
        let sum = || {
            add(
                xor(x.clone(), y.clone()),
                mul(k(width, 2), and(x.clone(), y.clone())),
            )
        };
        // An arithmetic atom that vanishes: (a & z) + (a & ~z) = a.
        let a = add(x.clone(), y.clone());
        solves_to(
            &add(and(a.clone(), z.clone()), and(a.clone(), not(z.clone()))),
            &a,
            &vars,
        );
        // An atom rendered from its own normal form.
        solves_to(&and(sum(), z.clone()), &and(a.clone(), z.clone()), &vars);
        // Arithmetic that is secretly bitwise: (x ^ y) + 2(x & y) − y is x.
        solves_to(
            &and(sub(sum(), y.clone()), z.clone()),
            &and(x.clone(), z.clone()),
            &vars,
        );
        // Two shifts of equal operands are one atom: (s >> 3) + ((x + y) >> 3) = 2((x + y) >> 3).
        solves_to(
            &add(un(MOp::LShr(3), sum()), un(MOp::LShr(3), a.clone())),
            &un(MOp::Shl(1), un(MOp::LShr(3), a.clone())),
            &vars,
        );
    }
}

#[test]
fn known_low_bits_and_atom_reuse() {
    for w in [8u16, 16, 64, 128, 512] {
        let width = Width::new(w).unwrap();
        let vars = [width; 3];
        let (x, y, z) = (V(0), V(1), V(2));
        let c = |v: i128| k(width, v);
        let solver = NormalFormSolver::default();
        let proved = |e: &T, want: &T| {
            let m = e.expr(&vars);
            let a = solver.solve(&m, &MbaBudget::default().with_steps(1 << 26));
            assert!(
                matches!(
                    a,
                    MbaAnswer::Simplified {
                        claim: Claim::Proved,
                        ..
                    }
                ),
                "{e:?}: {a:?}"
            );
            solves_to(e, want, &vars)
        };
        // −2·(z & 1) has a known low bit (0), so `| 1` sets it: 1 − 2·(z & 1), whose square
        // is 1.
        let sign = || or(mul(and(z.clone(), c(1)), c(-2)), c(1));
        let sum = add(x.clone(), y.clone());
        proved(&sign(), &sub(c(1), mul(and(z.clone(), c(1)), c(2))));
        proved(&mul(mul(sum.clone(), sign()), sign()), &sum);
        // The same with the constant clearing and flipping known bits.
        let even = || mul(y.clone(), c(4));
        proved(&and(even(), c(3)), &c(0));
        proved(&xor(add(even(), c(1)), c(3)), &add(even(), c(2)));
        proved(&and(add(even(), c(1)), c(-2)), &even());
        proved(&xor(even(), c(-4)), &not(add(even(), c(3))));
        // The polynomial inside a bitwise operation also appears outside it:
        // p + x + (x ^ 4) − ((x ^ 4) & p) is x + ((x ^ 4) | p).
        let p = add(mul(c(10), y.clone()), c(5));
        let x4 = xor(x.clone(), c(4));
        proved(
            &sub(
                add(add(p.clone(), x.clone()), x4.clone()),
                and(x4.clone(), p.clone()),
            ),
            &add(x.clone(), or(x4.clone(), p.clone())),
        );
        let s = solver.stats();
        assert!(s.known_bits + s.lowered >= 6 && s.reused >= 1, "{s:?}");
        assert_eq!(s.proved, s.calls, "{s:?}");
    }
}

#[test]
fn known_bits_and_reuse_are_exact_exhaustively() {
    let solver = NormalFormSolver::default();
    let (mut checked, mut lowered, mut simplified) = (0, 0, 0);
    for w in 1..=6u16 {
        let width = Width::new(w).unwrap();
        let t = if w <= 4 { 3 } else { 2 };
        let vars = vec![width; t as usize];
        let mut g = Gen::new(0x6b17_0000 + u64::from(w), width, t);
        for _ in 0..60 {
            let e = g.known_bits();
            let m = e.expr(&vars);
            if let Some(l) = certify::lower_known_bits(&m) {
                assert!(equal_everywhere(&m, &l), "lowered {e:?}:\n{l:?}");
                lowered += 1;
            }
            let Some((naive, cands)) = inspect(&m, &NfOptions::default()) else {
                continue;
            };
            assert!(
                equal_everywhere(&m, &naive),
                "normal form of {e:?}:\n{naive:?}"
            );
            for c in &cands {
                assert!(equal_everywhere(&m, c), "candidate of {e:?}:\n{c:?}");
            }
            checked += 1 + cands.len();
            if let MbaAnswer::Simplified { expr, .. } = solver.solve(&m, &MbaBudget::default()) {
                assert!(equal_everywhere(&m, &expr), "{e:?}\n{expr:?}");
                assert!(cost(&expr) < cost(&m), "{e:?}\n{expr:?}");
                simplified += 1;
            }
        }
    }
    let s = solver.stats();
    assert!(
        checked > 2000 && lowered > 100 && simplified > 200,
        "{checked} {lowered} {simplified}"
    );
    assert!(s.known_bits + s.lowered > 150 && s.reused > 30, "{s:?}");
    assert_eq!(s.declined_internal, 0);
}

#[test]
fn high_powers_fold_before_the_degree_cap() {
    // At 8 bits every power from x^10 on is a polynomial of lower degree, so a product over the
    // degree cap is multiplied out after the exact reductions instead of becoming an atom:
    // 128·x^17·(x + 1) is 0 (x^17·(x + 1) is even).
    let w = Width::W8;
    let vars = [w];
    let x = V(0);
    let mut p = x.clone();
    for _ in 1..17 {
        p = mul(p, x.clone());
    }
    solves_to(
        &mul(mul(k(w, 128), p.clone()), add(x.clone(), k(w, 1))),
        &k(w, 0),
        &vars,
    );
    // At 64 bits x^17 stays of degree 17: over the cap, an atom, and the question is declined
    // as no simpler, not answered wrongly.
    let w = Width::W64;
    let vars = [w];
    let mut p = x.clone();
    for _ in 1..17 {
        p = mul(p, x.clone());
    }
    let m = mul(p, add(x.clone(), k(w, 1))).expr(&vars);
    assert!(matches!(
        NormalFormSolver::default().solve(&m, &MbaBudget::default()),
        MbaAnswer::NoSimpler | MbaAnswer::Simplified { .. }
    ));
}

#[test]
fn null_parts_are_dropped_only_when_proved_zero() {
    // 2^(W−1)·((x & y)·(y & z) − (x & y & z)) is zero (the low bit of a product of
    // conjunctions is the conjunction of the low bits), but not by the reductions, which treat
    // symbols as independent: a certificate proves it, and it goes.
    for w in [8u16, 16, 64] {
        let width = Width::new(w).unwrap();
        let vars = [width; 3];
        let (x, y, z) = (V(0), V(1), V(2));
        let null = mul(
            C(BitVec::smin(width)),
            sub(
                mul(and(x.clone(), y.clone()), and(y.clone(), z.clone())),
                and(and(x.clone(), y.clone()), z.clone()),
            ),
        );
        let solver = NormalFormSolver::default();
        let e = add(x.clone(), null.clone());
        let m = e.expr(&vars);
        let MbaAnswer::Simplified { expr, claim } = solver.solve(&m, &MbaBudget::default()) else {
            panic!("w={w}: not simplified");
        };
        assert_eq!(claim, Claim::Proved);
        assert_eq!(cost(&expr), 1, "w={w}: {expr:?}");
        assert_eq!(solver.stats().null_parts, 1);
        // Almost null (2^(W−2)): kept.
        let near = mul(
            C(BitVec::wrapping_from_u64(width, 1 << (w - 2).min(63))),
            sub(
                mul(and(x.clone(), y.clone()), and(y.clone(), z.clone())),
                and(and(x.clone(), y.clone()), z.clone()),
            ),
        );
        let m = add(x.clone(), near).expr(&vars);
        if let MbaAnswer::Simplified { expr, .. } = solver.solve(&m, &MbaBudget::default()) {
            let r = certify::prove(&m, &expr, &mut Steps::new(1 << 26)).unwrap();
            assert_eq!(r.verdict, Verdict::Proved);
            assert!(cost(&expr) > 1);
        }
    }
}

#[test]
fn polynomial_negatives_are_left_alone() {
    let solver = NormalFormSolver::default();
    for w in [8u16, 64] {
        let width = Width::new(w).unwrap();
        let vars = [width, width, width];
        let (x, y, z) = (V(0), V(1), V(2));
        for e in [
            // x·y − (x & y) is not 0.
            sub(mul(x.clone(), y.clone()), and(x.clone(), y.clone())),
            // Neither is (x & ~y)·(~x & y).
            mul(
                and(x.clone(), not(y.clone())),
                and(not(x.clone()), y.clone()),
            ),
            // z must stay: z² − z is not 0.
            sub(add(x.clone(), mul(z.clone(), z.clone())), z.clone()),
        ] {
            let m = e.expr(&vars);
            match solver.solve(&m, &MbaBudget::default()) {
                MbaAnswer::NoSimpler => {}
                MbaAnswer::Simplified { expr, .. } => {
                    // Only ever a provably equal, smaller form.
                    let r = certify::prove(&m, &expr, &mut Steps::new(1 << 26)).unwrap();
                    assert_eq!(r.verdict, Verdict::Proved, "{e:?} -> {expr:?}");
                }
                other => panic!("{e:?}: {other:?}"),
            }
        }
    }
}

#[test]
fn never_costlier_than_the_signature_solver_on_linear_mba() {
    // What each leaves behind: its answer, or the input when it declines; measured by distinct
    // nodes (the signature solver's own test counts nodes as listed, duplicates included).
    let nf = NormalFormSolver::default();
    let (mut compared, mut better) = (0, 0);
    let result = |m: &MbaExpr, a: MbaAnswer| match a {
        MbaAnswer::Simplified { expr, .. } => cost(&expr),
        _ => cost(m),
    };
    for (i, w) in [1u16, 4, 8, 16, 64, 128].into_iter().enumerate() {
        let width = Width::new(w).unwrap();
        for t in 1..=4u32 {
            let vars = vec![width; t as usize];
            let mut g = Gen::new(0x51e0 + i as u64 * 16 + u64::from(t), width, t);
            for _ in 0..40 {
                let e = g.expr(Frag::Linear, 3);
                let m = e.expr(&vars);
                let sig = result(&m, SignatureSolver.solve(&m, &MbaBudget::default()));
                let ours = result(&m, nf.solve(&m, &MbaBudget::default()));
                assert!(ours <= sig, "{e:?}: ours {ours}, signature {sig}");
                compared += 1;
                better += usize::from(ours < sig);
            }
        }
    }
    assert!(better > 100, "{better} of {compared}");
}

#[test]
fn synthesis_finds_products_the_input_multiplied_out() {
    // The renderer factors by common symbols and by the input's own factors; these have
    // neither, and the table has them. Pure polynomials are proved at any width (the grid);
    // the mixed one over three atoms is past every certificate's cap at 512 bits, so there it
    // is a sampled answer (which `solves_to` checks at 2000 more points).
    let one = |w| k(w, 1);
    for bits in [6u16, 8, 64, 512] {
        let w = Width::new(bits).unwrap();
        let two = [w, w];
        let three = [w, w, w];
        let (x, y, z) = (V(0), V(1), V(2));
        solves_to(
            &add(
                add(add(mul(x.clone(), y.clone()), x.clone()), y.clone()),
                one(w),
            ),
            &mul(not(x.clone()), not(y.clone())),
            &two,
        );
        solves_to(
            &add(
                sub(sub(mul(x.clone(), y.clone()), x.clone()), y.clone()),
                one(w),
            ),
            &mul(sub(one(w), x.clone()), sub(one(w), y.clone())),
            &two,
        );
        solves_to(
            &add(
                add(
                    mul(x.clone(), x.clone()),
                    mul(k(w, 2), mul(x.clone(), y.clone())),
                ),
                mul(y.clone(), y.clone()),
            ),
            &mul(add(x.clone(), y.clone()), add(x.clone(), y.clone())),
            &two,
        );
        solves_to(
            &add(
                add(
                    add(mul(x.clone(), y.clone()), mul(x.clone(), z.clone())),
                    y.clone(),
                ),
                z.clone(),
            ),
            &mul(add(x.clone(), one(w)), add(y.clone(), z.clone())),
            &three,
        );
        // (x ^ y)·(x | z), multiplied out: x ^ y = x + y − 2(x & y), x | z = x + z − (x & z).
        let a = [
            (1, x.clone()),
            (1, y.clone()),
            (-2, and(x.clone(), y.clone())),
        ];
        let b = [
            (1, x.clone()),
            (1, z.clone()),
            (-1, and(x.clone(), z.clone())),
        ];
        let mut e: Option<T> = None;
        for (ca, ta) in &a {
            for (cb, tb) in &b {
                let t = mul(k(w, ca * cb), mul(ta.clone(), tb.clone()));
                e = Some(match e {
                    None => t,
                    Some(s) => add(s, t),
                });
            }
        }
        let e = e.unwrap();
        solves_to(
            &e,
            &mul(xor(x.clone(), y.clone()), or(x.clone(), z.clone())),
            &three,
        );
        let solver = NormalFormSolver::default();
        let MbaAnswer::Simplified { claim, .. } =
            solver.solve(&e.expr(&three), &MbaBudget::default())
        else {
            panic!("{bits}");
        };
        // Proved at every width: above 64 bits the grid and sparse tests are too large for
        // three atoms at degree 2, but the hit and the normal form are the same polynomial.
        let s = solver.stats();
        assert_eq!(claim, Claim::Proved);
        assert!(s.synth_proved > 0 && s.synth_sampled == 0, "{s:?}");
    }
    // Off, the table is not asked.
    let w = Width::W64;
    let (x, y) = (V(0), V(1));
    let e = add(add(add(mul(x.clone(), y.clone()), x), y), one(w)).expr(&[w, w]);
    let off = NormalFormSolver::new(NfOptions::default().with_synthesis(false));
    let _ = off.solve(&e, &MbaBudget::default());
    assert_eq!(off.stats().synth_lookups, 0);
    assert!(off.id().ends_with("synth=0"), "{}", off.id());
}

#[test]
fn the_solver_declines_what_it_does_not_take_and_counts_it() {
    let w = Width::W8;
    let solver = NormalFormSolver::new(NfOptions::default().with_max_classes(2));
    // Three classes: 0x0f, 0xf0 and the rest… at 8 bits only two, at 16 three.
    let w16 = Width::W16;
    let e = add(
        and(V(0), C(BitVec::wrapping_from_u64(w16, 0x0f))),
        and(V(0), C(BitVec::wrapping_from_u64(w16, 0xf0))),
    );
    assert!(matches!(
        solver.solve(&e.expr(&[w16]), &MbaBudget::default()),
        MbaAnswer::Unsupported(_)
    ));
    assert_eq!(solver.stats().declined_classes, 1);
    // No budget: exhausted, never a wrong answer.
    let e = add(xor(V(0), V(1)), mul(k(w, 2), and(V(0), V(1))));
    for steps in 0..64 {
        match NormalFormSolver::default()
            .solve(&e.expr(&[w, w]), &MbaBudget::default().with_steps(steps))
        {
            MbaAnswer::Simplified { expr, claim } => {
                assert!(equal_everywhere(&e.expr(&[w, w]), &expr));
                assert!(claim == Claim::Proved || claim == Claim::Sampled);
            }
            MbaAnswer::Exhausted | MbaAnswer::NoSimpler => {}
            other => panic!("{steps}: {other:?}"),
        }
    }
    let _ = Program::new(&e.expr(&[w, w]), false);
}

/// The sum of `c·t` over the pairs.
fn combine(w: Width, terms: &[(i128, T)]) -> T {
    terms
        .iter()
        .map(|(c, t)| mul(k(w, *c), t.clone()))
        .reduce(add)
        .expect("a term")
}

#[test]
fn scaled_two_term_wide_and_grouped_renderings() {
    for w in [8u16, 16, 64] {
        let width = Width::new(w).unwrap();
        let vars2 = [width; 2];
        let (x, y, z, t) = (V(0), V(1), V(2), V(3));
        // 1111·(x ^ 0x2d), multiplied out: an odd scale of a bitwise function.
        let kk = k(width, 0x2d);
        solves_to(
            &combine(
                width,
                &[
                    (1111, x.clone()),
                    (1111, kk.clone()),
                    (-2222, and(x.clone(), kk.clone())),
                ],
            ),
            &mul(xor(x.clone(), kk.clone()), k(width, 1111)),
            &vars2,
        );
        // −7·~y + 4·(x ^ y) = 7 + 4x + 11y − 8(x & y): two terms, read off the corners.
        solves_to(
            &add(
                combine(
                    width,
                    &[
                        (4, x.clone()),
                        (11, y.clone()),
                        (-8, and(x.clone(), y.clone())),
                    ],
                ),
                k(width, 7),
            ),
            &add(
                mul(k(width, -7), not(y.clone())),
                mul(k(width, 4), xor(x.clone(), y.clone())),
            ),
            &vars2,
        );
        // −4·~(x | y | z | t), multiplied out into its 15 conjunctions: one term of four atoms.
        let vars4 = [width; 4];
        let atoms = [x.clone(), y.clone(), z.clone(), t.clone()];
        let mut terms: Vec<(i128, T)> = Vec::new();
        for s in 1..16usize {
            let conj = (0..4)
                .filter(|&i| s >> i & 1 == 1)
                .map(|i| atoms[i].clone())
                .reduce(and)
                .unwrap();
            let sign = if s.count_ones() % 2 == 1 { 4 } else { -4 };
            terms.push((sign, conj));
        }
        solves_to(
            &add(combine(width, &terms), k(width, 4)),
            &mul(
                k(width, -4),
                not(or(or(or(x.clone(), y.clone()), z.clone()), t.clone())),
            ),
            &vars4,
        );
        // 2·(~x & (y ^ z)) + a − 1: independent groups, each rendered on its own.
        let a = t.clone();
        let inner = [
            (2, y.clone()),
            (2, z.clone()),
            (-4, and(y.clone(), z.clone())),
            (-2, and(x.clone(), y.clone())),
            (-2, and(x.clone(), z.clone())),
            (4, and(and(x.clone(), y.clone()), z.clone())),
            (1, a.clone()),
        ];
        solves_to(
            &sub(combine(width, &inner), k(width, 1)),
            &sub(
                add(
                    mul(k(width, 2), and(not(x.clone()), xor(y.clone(), z.clone()))),
                    a.clone(),
                ),
                k(width, 1),
            ),
            &vars4,
        );
    }
}

#[test]
fn atoms_up_to_complement_and_dependence() {
    for w in [8u16, 16, 64] {
        let width = Width::new(w).unwrap();
        let vars2 = [width; 2];
        let vars3 = [width; 3];
        let (x, y, z) = (V(0), V(1), V(2));
        let one = || k(width, 1);
        // (a − 1 | a) + 1: `a − 1` is the complement of `−a`, one atom.
        solves_to(
            &add(or(sub(x.clone(), one()), x.clone()), one()),
            &sub(and(neg(x.clone()), x.clone()), neg(x.clone())),
            &vars2,
        );
        // (((e − 1) & d) − e) & d: `(~a & d) − e` with `a = −e` is `d | a`, so the whole is d.
        solves_to(
            &neg(and(
                sub(and(sub(y.clone(), one()), x.clone()), y.clone()),
                x.clone(),
            )),
            &neg(x.clone()),
            &vars2,
        );
        // x & −(x & −x) is x: −(x & −x) is x | −x, found at the sample and proved.
        solves_to(
            &add(
                and(x.clone(), neg(and(x.clone(), neg(x.clone())))),
                y.clone(),
            ),
            &add(x.clone(), y.clone()),
            &vars2,
        );
        // (y + y) & y & −y is 0: dropped once proved, then −(−y) is y.
        solves_to(
            &sub(
                x.clone(),
                and(
                    not(and(add(y.clone(), y.clone()), y.clone())),
                    neg(y.clone()),
                ),
            ),
            &add(x.clone(), y.clone()),
            &vars2,
        );
        // ((y + 1) & (~y + ~y)) | y | x: the conjunction never has a bit outside y.
        solves_to(
            &or(
                or(
                    and(add(y.clone(), one()), add(not(y.clone()), not(y.clone()))),
                    y.clone(),
                ),
                x.clone(),
            ),
            &or(x.clone(), y.clone()),
            &vars2,
        );
        // ~((a − (n & a))·(n − (n & a))) − (n & a)·(n | a) with n = −z is −1 − a·n: the
        // arithmetic −z read as the atom n.
        let n = || neg(z.clone());
        let na = || and(n(), x.clone());
        let p = mul(sub(x.clone(), na()), sub(n(), na()));
        let q = mul(na(), or(n(), x.clone()));
        solves_to(
            &sub(not(p), q),
            &add(mul(x.clone(), z.clone()), k(width, -1)),
            &vars3,
        );
        // −(−b & b) is b | −b: b + n − (b & n) with n = −b, zero added.
        solves_to(
            &neg(and(neg(x.clone()), x.clone())),
            &or(x.clone(), neg(x.clone())),
            &vars2,
        );
    }
}

/// Without evidence asked for, the same answer comes back unchecked (`Claim::Unverified`), and
/// with it, proved; the two are remembered apart.
#[test]
fn evidence_is_optional() {
    let w = Width::W64;
    let vars = [w, w];
    let (x, y) = (V(0), V(1));
    let e = add(
        mul(and(x.clone(), y.clone()), or(x.clone(), y.clone())),
        mul(
            and(x.clone(), not(y.clone())),
            and(not(x.clone()), y.clone()),
        ),
    )
    .expr(&vars);
    let solver = NormalFormSolver::default();
    let with = solver.solve(&e, &MbaBudget::default());
    let without = solver.solve(&e, &MbaBudget::default().with_evidence(false));
    let (
        MbaAnswer::Simplified { expr: a, claim: ca },
        MbaAnswer::Simplified { expr: b, claim: cb },
    ) = (with, without)
    else {
        panic!("not simplified");
    };
    assert_eq!(a, b);
    assert_eq!((ca, cb), (Claim::Proved, Claim::Unverified));
    assert_eq!(certify::check(&e, &b, u64::MAX).verdict, Verdict::Proved);
}

/// A variable eliminated through an atom's definition must be unmasked: in a form with several
/// bit classes, `v & M` is not `α⁻¹·((n & M) − …)`. This question (random code at 16 bits,
/// six variables, the classes of `0xc98b` and `0xff00`) was answered wrongly without the
/// self-check.
#[test]
fn elimination_through_an_atom_is_unmasked() {
    use crate::mba::{MbaLimits, lower};
    use crate::{Context, ParseOptions};
    let q7 = "((c | b) + a)";
    let q13 = "(a | 0xc98b)";
    let q15 = "((c | b) | a)";
    let q19 = format!("((~({q7} + {q13}) | {q15}) + ({q13} ^ f))");
    let src = format!(
        "((({q19} & {q7}) & 0xff00) ^ (((({q15} * f) - {q7})) ^ ({q19} ^ ((e - 1) ^ (d ^ {q7})))))"
    );
    let w = Width::new(16).unwrap();
    let mut cx = Context::new();
    let e = cx.parse(&src, &ParseOptions::width(w)).unwrap();
    let (m, _) = lower(&cx, e, &MbaLimits::default()).unwrap();
    let solver = NormalFormSolver::default();
    for evidence in [false, true] {
        match solver.solve(&m, &MbaBudget::default().with_evidence(evidence)) {
            MbaAnswer::Simplified { expr, .. } => {
                let points = certify::sample_points(m.vars(), &[&m, &expr], 7);
                assert!(certify::refute(&m, &expr, &points).is_none(), "{expr:?}");
            }
            MbaAnswer::NoSimpler => {}
            other => panic!("{other:?}"),
        }
    }
    assert_eq!(solver.stats().declined_internal, 0);
}

/// Solves `src` at width `w` with the default budget: the answer is checked as `solves_to`
/// checks it and has at most `want` nodes.
fn solves_text(src: &str, w: Width, want: usize) -> MbaExpr {
    use crate::mba::{MbaLimits, lower};
    use crate::{Context, ParseOptions};
    let mut cx = Context::new();
    let e = cx.parse(src, &ParseOptions::width(w)).unwrap();
    let (m, _) = lower(&cx, e, &MbaLimits::default()).unwrap();
    let MbaAnswer::Simplified { expr, claim } =
        NormalFormSolver::default().solve(&m, &MbaBudget::default())
    else {
        panic!("not simplified: {src}");
    };
    let r = certify::prove(&m, &expr, &mut Steps::new(1 << 26)).unwrap();
    if claim == Claim::Sampled {
        let points = certify::sample_points(m.vars(), &[&m, &expr], 7);
        assert!(
            certify::refute(&m, &expr, &points).is_none(),
            "{src}: {expr:?}"
        );
    } else {
        assert_eq!(r.verdict, Verdict::Proved, "{src} -> {expr:?}");
    }
    assert!(
        cost(&expr) <= want,
        "{src}: {} nodes, want {want}: {expr:?}",
        cost(&expr)
    );
    expr
}

/// Renderings and normal forms that take more than one decomposition or normal form: each
/// question is one the engine's passes leave to the solver.
#[test]
fn shared_split_and_factored_renderings() {
    let w64 = Width::W64;
    let w8 = Width::new(8).unwrap();
    // A conjunction proved zero in one class takes the others' coefficient there: `2·(a & y) &
    // ~1` with `a = y + y` (bit 0 of `a` is 0) is `2·(a & y)`, and the whole `1 − (a ^ y)`.
    solves_text("((~((y + y) ^ y) & 1) << 1) - (((y + y) ^ y) ^ 1)", w64, 5);
    // `~(−x) ^ y` is built `~(−x ^ y)`: the rules would read `~(−x)` as `x − 1`, which shares
    // nothing with the `−x` of the product.
    let e = solves_text("((x - 1) ^ y) + -x * y", w64, 7);
    assert!(
        !e.nodes()
            .iter()
            .any(|n| n.op == MOp::Not && e.nodes()[n.args[0] as usize].op == MOp::Neg),
        "{e:?}"
    );
    // An atom `a + a` linear in the variable `a`: zero added to the form with atoms reused
    // splits its coefficient (`2·D − a` beside `a` as `D + a − …`), `(p | (a ^ d)) + (a ^ D)`.
    solves_text("(a * d | a ^ d) + (~a & (a + a)) * 2 - a", w64, 8);
    // Two atoms whose definitions sum to zero: `d + e` added makes the form a bitwise function
    // (`(d & e) − 1` is `~(d | e)` for `e = −d`).
    solves_text("(((c - e) & (e - c)) - 1) ^ e", w64, 7);
    // A table over four atoms read through `u | v`: `f = g(d, s, u | v)`.
    solves_text(
        "(~d & ~((a - d) | (a + (a & d)) | (a + d))) | (d & ((a - d) | (a + (a & d))) & (a + d))",
        w64,
        11,
    );
    // Two terms whose minimum forms share a subterm: `6·~((x | y) | z)` beside the majority as
    // `(x & y) | ((x | y) & z)`.
    solves_text(
        "6*x + 6*y + 6*z - 7*(x&y) - 7*(x&z) - 7*(y&z) + 8*(x&y&z) + 6",
        w64,
        12,
    );
    // One term read through the other: `y ^ w` beside `~w` as `~(y ^ n)`, `n` the node of `~w`.
    solves_text("14*(x&y) - 7*y - 2*x + 2*(x&z) - 2*(x&y&z) - 7", w64, 13);
    // A constant traded for a complement in a two-term decomposition that then shares `y ^ z`.
    solves_text("6*y + (x&z) + 11*(x&y&z) - x - 5*(x&y) - 13*(y&z)", w64, 14);
    // A third term beside two: `(x & z) − 6·~((x & y) | …) − (x & y)` sharing `x & y`.
    solves_text(
        "6 + 6*x + 6*y + 6*z - 7*(x&y) - 11*(x&z) - 12*(y&z) + 18*(x&y&z)",
        w8,
        13,
    );
    // The constant inside a factored sum, as a complement: `6·x − 12·(x & y) − 6` is
    // `(~y + (x ^ y))·6`.
    solves_text("x*6 - (x&y)*12 - 6", w8, 7);
    // A coefficient taken out with the sign its terms have: `−5·(t ^ z) − 5·(z & ~t)` as
    // `((t ^ z) + …)·−5`; and inside a complement traded for the constant: `~(3·g + 3·h)` as
    // `~((g + h)·3)`.
    solves_text("(t & z) * 15 - t * 5 - z * 10", w64, 7);
    solves_text("~(y * 6 + x * 3 - (x & y) * 9)", w64, 8);
    // Halves: `(y + y) ^ ((x ^ z) + x − z)` is `2·t`, `t = y ^ (x & ~z)`, and the whole `t − ~t`.
    solves_text("((y + y) ^ ((x ^ z) + x - z)) + 1", w64, 8);
    // Part of the nonlinear terms factored by a symbol most of them share.
    solves_text("2*c*(a&c) - a*c - c*c - a*a", w64, 7);
    solves_text("b*c + b*b - b*(b&c) + (b|c) - c*e", w64, 8);
    // `p·q` written `(p & q)·(p | q) + (p & ~q)·(~p & q)`: `p` and `q` are sums of the
    // products' operands.
    solves_text(
        "(((a + b) | b) & (-b ^ a)) * (((a + b) | b) | (-b ^ a)) \
         + (((a + b) | b) & ~(-b ^ a)) * (~((a + b) | b) & (-b ^ a))",
        w64,
        7,
    );
}

/// Powers of a shifted variable come back from their expansion (issue #5): `a·(x + s)^k + b`
/// expanded (and, at narrow widths, reduced by the normal form) renders as the power by
/// repeated squaring, at several widths. A near-power (one coefficient off) never becomes a
/// power: every answer is certified, and the result stays equal to the input.
#[test]
fn shifted_powers_come_back_from_their_expansion() {
    use crate::engine::{Engine, Strategy};
    use crate::mba::MbaConfig;
    use crate::{Bounded, Context, ParseOptions};
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
        .build()
        .unwrap();
    // The expansion of a·(x + s)^k + b, term by term.
    let expansion = |w: u16, a: u64, s: i64, k: u32, b: u64, off: Option<u32>| -> String {
        let width = Width::new(w).unwrap();
        let mut coef = vec![BitVec::zero(width); k as usize + 1];
        // Binomial coefficients times s^(k-i), modulo 2^w.
        let s = BitVec::wrapping_from_u64(width, s as u64);
        let mut binom = BitVec::one(width);
        for i in 0..=k {
            let mut spow = BitVec::one(width);
            for _ in 0..(k - i) {
                spow = BitVec::apply_bin(crate::BinOp::Mul, &spow, &s).unwrap();
            }
            let c = BitVec::apply_bin(crate::BinOp::Mul, &binom, &spow).unwrap();
            coef[i as usize] =
                BitVec::apply_bin(crate::BinOp::Mul, &c, &BitVec::wrapping_from_u64(width, a))
                    .unwrap();
            // binom(k, i+1) = binom(k, i)·(k−i)/(i+1), over the integers (small k).
            let exact: u128 =
                (0..=i).fold(1u128, |acc, j| acc * u128::from(k - j) / u128::from(j + 1));
            binom = BitVec::wrapping_from_u64(width, exact as u64);
        }
        coef[0] = BitVec::apply_bin(
            crate::BinOp::Add,
            &coef[0],
            &BitVec::wrapping_from_u64(width, b),
        )
        .unwrap();
        if let Some(i) = off {
            coef[i as usize] =
                BitVec::apply_bin(crate::BinOp::Add, &coef[i as usize], &BitVec::one(width))
                    .unwrap();
        }
        let mut terms = Vec::new();
        for (i, c) in coef.iter().enumerate() {
            if c.is_zero() {
                continue;
            }
            let pow = if i == 0 {
                "1".to_string()
            } else {
                vec!["x"; i].join(" * ")
            };
            terms.push(format!("{} * {pow}", c.to_u64().unwrap()));
        }
        terms.join(" + ")
    };
    let size = |cx: &mut Context, e: crate::Expr| match cx.dag_size(&[e], u32::MAX).unwrap() {
        Bounded::Exact(n) => n,
        _ => u32::MAX,
    };
    for (w, a, s, k, b) in [
        (8u16, 1u64, -1i64, 12u32, 0u64),
        (8, 3, 2, 9, 5),
        (16, 1, -1, 6, 0),
        (16, 5, 3, 5, 7),
        (32, 1, -2, 8, 1),
        (64, 1, -1, 7, 0),
        (64, 9, 4, 6, 11),
    ] {
        let o = ParseOptions::width(Width::new(w).unwrap());
        let mut cx = Context::new();
        let src = expansion(w, a, s, k, b, None);
        let e = cx.parse(&src, &o).unwrap();
        let out = engine.simplify(&mut cx, e).unwrap();
        // x, s, the shift, the squarings and products, a, b and their operations: a handful.
        let n = size(&mut cx, out.expr);
        assert!(
            n <= 16,
            "W={w} a={a} s={s} k={k} b={b}: {} nodes: {}",
            n,
            cx.display(out.expr)
        );
        // One coefficient off: still equal to the input, never the power.
        for off in [0, k - 1] {
            let mut cx = Context::new();
            let src = expansion(w, a, s, k, b, Some(off));
            let e = cx.parse(&src, &o).unwrap();
            let out = engine.simplify(&mut cx, e).unwrap();
            let mut rng = crate::testutil::Rng(w as u64);
            assert!(
                crate::engine::tests::equivalent(&mut cx, e, out.expr, &mut rng),
                "W={w}: {} became {}",
                cx.display(e),
                cx.display(out.expr)
            );
        }
    }
}
