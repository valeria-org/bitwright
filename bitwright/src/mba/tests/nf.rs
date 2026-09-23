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
        let s = solver.stats();
        if bits > 64 {
            assert_eq!(claim, Claim::Sampled);
            assert!(s.synth_unproved > 0 && s.synth_sampled > 0, "{s:?}");
        } else {
            assert_eq!(claim, Claim::Proved);
            assert!(s.synth_proved > 0 && s.synth_sampled == 0, "{s:?}");
        }
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
