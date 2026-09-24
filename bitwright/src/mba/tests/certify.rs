//! The certificates: verdicts against exhaustive evaluation in both directions, planted wrong
//! candidates, the compositional test, sizing and budgets.

use super::random::*;
use crate::mba::certify::{self, Cert, Steps};
use crate::mba::{EquivalenceProver, MOp, MbaBudget, MbaExpr, NativeProver, Verdict};
use crate::{BitVec, Width};

/// The certificate's verdict, checked against the truth: `Proved` only for equal pairs,
/// `Refuted` only for unequal ones with a counterexample that is one.
fn check(a: &MbaExpr, b: &MbaExpr, truth: bool) -> certify::Report {
    let r = certify::prove(a, b, &mut Steps::new(u64::MAX)).unwrap();
    match r.verdict {
        Verdict::Proved => assert!(truth, "proved an unequal pair:\n{a:?}\n{b:?}"),
        Verdict::Refuted => {
            assert!(!truth, "refuted an equal pair:\n{a:?}\n{b:?}");
            let p = r.counterexample.clone().expect("a counterexample");
            assert_ne!(a.eval(&p), b.eval(&p), "not a counterexample: {p:?}");
        }
        _ => {}
    }
    assert_eq!(r.internal, 0);
    r
}

#[test]
fn sparse_point_counts_match_the_enumeration() {
    // Σ_{k≤d} C(W,k)·(2^t − 1)^k.
    assert_eq!(certify::sparse_points(64, 3, 2), 1 + 64 * 7 + 2016 * 49);
    assert_eq!(certify::sparse_points(64, 2, 1), 1 + 64 * 3);
    assert_eq!(certify::sparse_points(1, 3, 5), 1 + 7);
    assert_eq!(certify::sparse_points(8, 0, 3), 1);
    assert_eq!(certify::sparse_points(512, 16, 30), u64::MAX);
    // The points a degree-2 test evaluates are exactly that many.
    let w = Width::new(6).unwrap();
    let vars = [w, w];
    let a = mul(and(V(0), V(1)), V(0)).expr(&vars);
    let b = mul(V(0), and(V(1), V(0))).expr(&vars);
    let r = certify::prove(&a, &b, &mut Steps::new(u64::MAX)).unwrap();
    assert_eq!(r.verdict, Verdict::Proved);
    assert_eq!(r.cert, Some(Cert::Sparse));
    assert_eq!(r.points, certify::sparse_points(6, 2, 2));
    // Without bitwise operators, the grid is smaller: {0, 1, 2}².
    let a = mul(V(0), mul(V(1), V(0))).expr(&vars);
    let b = mul(mul(V(0), V(0)), V(1)).expr(&vars);
    let r = certify::prove(&a, &b, &mut Steps::new(u64::MAX)).unwrap();
    assert_eq!(
        (r.verdict, r.cert, r.points),
        (Verdict::Proved, Some(Cert::Grid), 6)
    );
}

/// Pairs of one fragment at width `w` over `t` variables: equal (rewritten, with zero terms),
/// planted wrong (plus a term that is usually not zero), and independent.
fn pairs(frag: Frag, w: u16, t: u32, seed: u64, n: usize) -> Vec<(MbaExpr, MbaExpr)> {
    let width = Width::new(w).unwrap();
    let vars = vec![width; t as usize];
    let mut g = Gen::new(seed, width, t);
    let mut out = Vec::new();
    for i in 0..n {
        let e = g.expr(frag, 2 + (i % 2) as u32);
        let any = frag == Frag::Any;
        let mut f = g.rewrite(&e, any);
        if g.rng.chance(1, 2) {
            let z = g.zero(frag);
            f = add(f, z);
        }
        match i % 3 {
            0 => out.push((e.expr(&vars), f.expr(&vars))),
            1 => {
                let p = g.nonzero(frag);
                out.push((e.expr(&vars), add(f, p).expr(&vars)));
            }
            _ => {
                let o = g.expr(frag, 2);
                out.push((e.expr(&vars), o.expr(&vars)));
            }
        }
    }
    out
}

#[test]
fn certificates_decide_polynomial_mba_exactly() {
    let (mut proved, mut refuted) = (0, 0);
    for w in 1..=6u16 {
        for (fi, frag) in [Frag::Linear, Frag::SemiLinear, Frag::Poly, Frag::PurePoly]
            .into_iter()
            .enumerate()
        {
            let t = if w <= 4 { 3 } else { 2 };
            for (a, b) in pairs(frag, w, t, 0xce27_0000 + u64::from(w) * 16 + fi as u64, 60) {
                let truth = equal_everywhere(&a, &b);
                let r = check(&a, &b, truth);
                // Complete: polynomial MBA is always decided.
                assert_ne!(r.verdict, Verdict::Unknown, "{frag:?} w={w}\n{a:?}\n{b:?}");
                match r.verdict {
                    Verdict::Proved => proved += 1,
                    _ => refuted += 1,
                }
            }
        }
    }
    assert!(proved > 300 && refuted > 300, "{proved} {refuted}");
}

#[test]
fn every_certificate_agrees_with_exhaustive_truth_when_forced() {
    // Each test on its own (not only the cheapest), both directions.
    let mut runs = [0usize; 5];
    for w in 1..=6u16 {
        for frag in [Frag::Linear, Frag::SemiLinear, Frag::Poly, Frag::PurePoly] {
            let t = if w <= 3 { 3 } else { 2 };
            for (a, b) in pairs(frag, w, t, 0xf07c_0000 + u64::from(w), 30) {
                let truth = equal_everywhere(&a, &b);
                for (k, cert) in [
                    Cert::Signature,
                    Cert::SingleBit,
                    Cert::Sparse,
                    Cert::Grid,
                    Cert::Exhaustive,
                ]
                .into_iter()
                .enumerate()
                {
                    if let Some(v) = certify::prove_with(&a, &b, cert) {
                        runs[k] += 1;
                        assert_eq!(v, truth, "{cert:?} w={w}\n{a:?}\n{b:?}");
                    }
                }
            }
        }
    }
    assert!(runs.iter().all(|&n| n > 50), "{runs:?}");
}

#[test]
fn planted_wrong_candidates_are_never_proved() {
    // At every width, including those no exhaustive check covers: the planted terms are not
    // zero from four bits on (checked exhaustively up to five).
    for (i, w) in [4u16, 5, 6, 8, 16, 32, 64, 65, 128, 200, 512]
        .into_iter()
        .enumerate()
    {
        let width = Width::new(w).unwrap();
        let vars = vec![width; 3];
        let mut g = Gen::new(0x91a7_0000 + i as u64, width, 3);
        // Fewer rounds where lanes are multi-limb (slow in debug builds).
        let rounds = if w <= 64 { 12 } else { 3 };
        for frag in [
            Frag::Linear,
            Frag::SemiLinear,
            Frag::Poly,
            Frag::PurePoly,
            Frag::Any,
        ] {
            for _ in 0..rounds {
                let e = g.expr(frag, 2);
                let f = g.rewrite(&e, frag == Frag::Any);
                let wrong = [
                    k(width, 1),
                    C(BitVec::smin(width)),
                    sub(mul(V(0), V(1)), and(V(0), V(1))),
                    mul(and(V(0), not(V(1))), and(not(V(0)), V(1))),
                    mul(
                        mul(and(V(0), k(width, 1)), and(V(1), k(width, 2))),
                        and(V(2), k(width, 4)),
                    ),
                    mul(C(BitVec::smin(width)), and(V(0), V(1))),
                ];
                for p in wrong {
                    let (a, b) = (e.expr(&vars), add(f.clone(), p).expr(&vars));
                    if w <= 5 {
                        assert!(!equal_everywhere(&a, &b));
                    }
                    let r = certify::prove(&a, &b, &mut Steps::new(1 << 24)).unwrap();
                    assert_ne!(r.verdict, Verdict::Proved, "w={w} {frag:?}\n{a:?}\n{b:?}");
                }
            }
        }
    }
}

#[test]
fn compositional_verdicts_are_sound() {
    let (mut proved, mut refuted, mut unknown) = (0, 0, 0);
    for w in 1..=6u16 {
        let t = if w <= 4 { 3 } else { 2 };
        for (a, b) in pairs(Frag::Any, w, t, 0xc0e5_0000 + u64::from(w), 80) {
            let truth = equal_everywhere(&a, &b);
            let r = check(&a, &b, truth);
            match r.verdict {
                Verdict::Proved => proved += 1,
                Verdict::Refuted => refuted += 1,
                _ => unknown += 1,
            }
        }
    }
    assert!(proved > 50 && refuted > 50, "{proved} {refuted} {unknown}");
}

fn lshr(a: T, s: u16) -> T {
    un(MOp::LShr(s), a)
}

#[test]
fn atoms_are_paired_by_structure_congruence_and_proof() {
    let w = Width::W64;
    let vars = [w; 3];
    let (x, y, z) = (V(0), V(1), V(2));
    let two = || k(w, 2);
    let sum = |x: T, y: T| add(xor(x.clone(), y.clone()), mul(two(), and(x, y)));
    let prove = |a: &T, b: &T| {
        certify::prove(&a.expr(&vars), &b.expr(&vars), &mut Steps::new(1 << 26)).unwrap()
    };
    let cases = [
        // An arithmetic atom, spelled differently on each side.
        (
            and(sum(x.clone(), y.clone()), z.clone()),
            and(add(x.clone(), y.clone()), z.clone()),
        ),
        // The same atom on one side, the whole of the other.
        (
            add(
                and(add(x.clone(), y.clone()), z.clone()),
                and(add(x.clone(), y.clone()), not(z.clone())),
            ),
            add(x.clone(), y.clone()),
        ),
        // Arithmetic that is secretly a variable, or a bitwise function.
        (
            and(sub(sum(x.clone(), y.clone()), y.clone()), z.clone()),
            and(x.clone(), z.clone()),
        ),
        (
            and(
                sub(
                    add(x.clone(), y.clone()),
                    mul(two(), and(x.clone(), y.clone())),
                ),
                z.clone(),
            ),
            and(xor(x.clone(), y.clone()), z.clone()),
        ),
        // Right shifts: congruence, through operands proved equal.
        (
            add(lshr(mul(x.clone(), y.clone()), 3), z.clone()),
            add(z.clone(), lshr(mul(y.clone(), x.clone()), 3)),
        ),
        (
            mul(lshr(sum(x.clone(), y.clone()), 5), z.clone()),
            mul(z.clone(), lshr(add(x.clone(), y.clone()), 5)),
        ),
        // Nested atoms.
        (
            add(
                and(
                    lshr(add(or(x.clone(), y.clone()), and(x.clone(), y.clone())), 2),
                    z.clone(),
                ),
                and(
                    lshr(add(or(x.clone(), y.clone()), and(x.clone(), y.clone())), 2),
                    not(z.clone()),
                ),
            ),
            lshr(add(x.clone(), y.clone()), 2),
        ),
    ];
    for (a, b) in &cases {
        let r = prove(a, b);
        assert_eq!(r.verdict, Verdict::Proved, "{a:?} == {b:?}: {r:?}");
        assert!(r.compositional, "{a:?}");
    }
    // Unequal: never proved.
    for (a, b) in [
        (
            add(lshr(mul(x.clone(), y.clone()), 3), z.clone()),
            add(lshr(mul(x.clone(), y.clone()), 4), z.clone()),
        ),
        (
            add(mul(lshr(x.clone(), 1), two()), and(x.clone(), k(w, 1))),
            add(x.clone(), k(w, 1)),
        ),
        (
            add(
                and(add(x.clone(), y.clone()), z.clone()),
                and(add(x.clone(), y.clone()), not(z.clone())),
            ),
            add(add(x.clone(), y.clone()), k(w, 1)),
        ),
    ] {
        assert_ne!(prove(&a, &b).verdict, Verdict::Proved, "{a:?} == {b:?}");
    }
    // Equal through a relation between atoms (`x >> 1` and `x`) that abstraction loses:
    // unknown, never refuted.
    let a = add(mul(lshr(x.clone(), 1), two()), and(x.clone(), k(w, 1)));
    assert_eq!(prove(&a, &x).verdict, Verdict::Unknown);
}

#[test]
fn a_point_function_is_refuted_by_its_constant_and_never_proved() {
    // x + [x = K] against x: differs at one input in 2^W; the sample reaches it through K.
    for (i, w) in [8u16, 16, 64, 128, 512].into_iter().enumerate() {
        let width = Width::new(w).unwrap();
        let key = BitVec::wrapping_from_limbs(
            width,
            &[
                0x9e37_79b9_7f4a_7c15 ^ i as u64,
                0x1234_5678,
                7,
                1,
                2,
                3,
                4,
                5,
            ],
        );
        let d = xor(V(0), C(key));
        let is_k = un(MOp::LShr(w - 1), not(or(d.clone(), neg(d))));
        let a = add(V(0), is_k).expr(&[width]);
        let b = V(0).expr(&[width]);
        let r = check(&a, &b, false);
        assert_eq!(r.verdict, Verdict::Refuted, "w={w}");
        let prover = NativeProver::default();
        assert_eq!(
            prover.prove_equal(&a, &b, &MbaBudget::default()),
            Verdict::Refuted
        );
    }
}

#[test]
fn certificates_are_sized_and_budgeted() {
    let w = Width::W64;
    let vars = [w, w, w];
    // Degree 2 over three 64-bit variables: 99,233 points.
    let a = add(
        mul(and(V(0), V(1)), or(V(0), V(1))),
        mul(and(V(0), not(V(1))), and(not(V(0)), V(1))),
    );
    let a = add(a, V(2)).expr(&vars);
    let b = add(mul(V(0), V(1)), V(2)).expr(&vars);
    let full = certify::prove(&a, &b, &mut Steps::new(u64::MAX)).unwrap();
    assert_eq!(full.verdict, Verdict::Proved);
    assert_eq!(full.points, certify::sparse_points(64, 3, 2));
    // Every budget from 0 up: never a wrong verdict, and unknown (over budget) below the size.
    let need = full.points * (a.nodes().len() + b.nodes().len()) as u64;
    for budget in [0, 1, 100, need / 2, need - 1, need] {
        let mut m = Steps::new(budget);
        let r = certify::prove(&a, &b, &mut m).unwrap();
        if budget < need {
            assert_eq!(r.verdict, Verdict::Unknown, "{budget}");
            assert!(r.over_budget);
            assert_eq!(m.spent, 0, "nothing is spent on a test that is not run");
        } else {
            assert_eq!(r.verdict, Verdict::Proved);
        }
    }
    // The prover counts it.
    let p = NativeProver::default();
    assert_eq!(
        p.prove_equal(&a, &b, &MbaBudget::default().with_steps(1 << 10)),
        Verdict::Unknown
    );
    assert_eq!(
        p.prove_equal(&a, &b, &MbaBudget::default().with_steps(1 << 24)),
        Verdict::Proved
    );
    let s = p.stats();
    assert_eq!((s.calls, s.proved, s.unknown, s.sparse), (2, 1, 1, 1));
    assert!(s.over_budget >= 1 && s.points > 0);
}

#[test]
fn the_sample_uses_constants_and_single_positions() {
    let w = Width::W32;
    let key = BitVec::wrapping_from_u64(w, 0xdead_beef);
    let a = add(V(0), C(key)).expr(&[w, w]);
    let pts = certify::sample_points(&[w, w], &[&a], 7);
    assert_eq!(pts.len(), certify::SAMPLE_POINTS);
    assert_eq!(pts, certify::sample_points(&[w, w], &[&a], 7));
    for v in [
        key,
        BitVec::wrapping_from_u64(w, 0xdead_bef0),
        BitVec::wrapping_from_u64(w, 0xdead_beee),
    ] {
        assert!(pts.iter().any(|p| p[0] == v) && pts.iter().any(|p| p[1] == v));
    }
    assert!(
        pts.iter()
            .any(|p| p[0] == BitVec::wrapping_from_u64(w, 1 << 16))
    );
    assert!(
        pts.iter()
            .any(|p| p[0] == BitVec::wrapping_from_u64(w, 1 << 31) && p[1].is_zero())
    );
}

/// `m` with every use of variable `v` replaced by `v & mask`.
fn mask_var(m: &MbaExpr, v: u32, mask: BitVec) -> MbaExpr {
    wrap_var(m, v, MOp::And, mask)
}

/// `m` with every use of variable `v` replaced by `v op k`.
fn wrap_var(m: &MbaExpr, v: u32, op: MOp, k: BitVec) -> MbaExpr {
    let mut out = MbaExpr::new(m.vars().to_vec());
    let mut map: Vec<u32> = Vec::new();
    for n in m.nodes() {
        let args: Vec<u32> = n.args[..n.op.arity()]
            .iter()
            .map(|&x| map[x as usize])
            .collect();
        let r = match n.op {
            MOp::Var(x) if x == v => {
                let a = out.push(n.op, &[]).unwrap();
                let c = out.push(MOp::Const(k), &[]).unwrap();
                out.push(op, &[a, c]).unwrap()
            }
            MOp::Zext | MOp::Sext | MOp::Trunc => out.push_cast(n.op, args[0], n.width).unwrap(),
            op => out.push(op, &args).unwrap(),
        };
        map.push(r);
    }
    out
}

#[test]
fn a_variable_read_through_a_narrow_mask_is_split_into_cases() {
    let w = Width::W64;
    let vars = [w; 5];
    let (x1, x2, x3, x4, x5) = (V(0), V(1), V(2), V(3), V(4));
    // 1 − 2·(x & 1) is ±1, so its square is 1; no test on the whole decides it (x3 & 1 is an
    // atom that abstraction frees from being a bit).
    let sign = |x: T| add(k(w, 1), mul(and(x, k(w, 1)), k(w, -2)));
    let sign_or = |x: T| or(mul(and(x, k(w, 1)), k(w, -2)), k(w, 1));
    let sum = add(x1.clone(), x2.clone());
    let cases = [
        mul(mul(sum.clone(), sign(x3.clone())), sign(x3.clone())),
        mul(mul(sum.clone(), sign_or(x3.clone())), sign_or(x3.clone())),
    ];
    for a in &cases {
        let r = check(&a.expr(&vars), &sum.expr(&vars), true);
        assert_eq!(r.verdict, Verdict::Proved, "{a:?}: {r:?}");
        assert!(r.split, "{a:?}");
    }
    // Two variables, one split inside the other.
    let a = add(
        mul(mul(sum.clone(), sign(x3.clone())), sign(x3.clone())),
        mul(
            mul(add(x5.clone(), k(w, 3)), sign(x4.clone())),
            sign(x4.clone()),
        ),
    );
    let b = add(sum.clone(), add(x5.clone(), k(w, 3)));
    let r = check(&a.expr(&vars), &b.expr(&vars), true);
    assert_eq!((r.verdict, r.split), (Verdict::Proved, true), "{r:?}");
    // Wrong: refuted with the variable set to the case that differs (x3 odd).
    let a = mul(sum.clone(), sign(x3.clone())).expr(&vars);
    let r = check(&a, &sum.expr(&vars), false);
    assert_eq!(r.verdict, Verdict::Refuted, "{r:?}");
    // Read whole, but through `x3 ^ 1` only at its low bit: split on that bit, x3 standing for
    // (x3 << 1) + b. (x3 ^ 1) − x3 is 1 − 2·(x3 & 1).
    let flip = || sub(xor(x3.clone(), k(w, 1)), x3.clone());
    let a = mul(mul(sum.clone(), flip()), flip());
    let r = check(&a.expr(&vars), &sum.expr(&vars), true);
    assert_eq!((r.verdict, r.split), (Verdict::Proved, true), "{r:?}");
    let r = check(
        &mul(sum.clone(), flip()).expr(&vars),
        &sum.expr(&vars),
        false,
    );
    assert_eq!(r.verdict, Verdict::Refuted, "{r:?}");
    // Also read whole: split on its low bit instead (`x3 & 1` reads only that).
    let a = add(
        mul(mul(sum.clone(), sign(x3.clone())), sign(x3.clone())),
        x3.clone(),
    );
    let b = add(sum.clone(), x3.clone());
    let r = certify::by_cases(&a.expr(&vars), &b.expr(&vars));
    assert_eq!((r.verdict, r.split), (Verdict::Proved, true), "{r:?}");
    // No bitwise operation with a constant: nothing to split on.
    let a = mul(and(x1.clone(), x2.clone()), x3.clone());
    let b = mul(x3.clone(), and(x2.clone(), x1.clone()));
    assert!(!certify::by_cases(&a.expr(&vars), &b.expr(&vars)).split);
    // The prover counts it.
    let p = NativeProver::default();
    let (a, b) = (cases[0].expr(&vars), sum.expr(&vars));
    assert_eq!(
        p.prove_equal(&a, &b, &MbaBudget::default()),
        Verdict::Proved
    );
    assert_eq!(p.stats().split, 1);
}

#[test]
fn splits_agree_with_exhaustive_truth() {
    let (mut proved, mut refuted, mut split) = (0, 0, 0);
    for w in 2..=6u16 {
        let width = Width::new(w).unwrap();
        let t = if w <= 4 { 3 } else { 2 };
        let masks: Vec<BitVec> = [1u64, 0b101, 1 << (w - 1), 0b1111]
            .iter()
            .map(|&m| BitVec::wrapping_from_u64(width, m))
            .collect();
        for (i, (a, b)) in pairs(Frag::Any, w, t, 0x5b17_0000 + u64::from(w), 60)
            .into_iter()
            .enumerate()
        {
            let mask = masks[i % masks.len()];
            let (ma, mb) = (mask_var(&a, 0, mask), mask_var(&b, 0, mask));
            let other = masks[(i / masks.len()) % masks.len()];
            let flip = BitVec::wrapping_from_i128(width, [1, 3, -2, 5][i % 4]);
            for (x, y) in [
                (ma.clone(), mb.clone()),
                (mask_var(&ma, 1, other), mask_var(&mb, 1, other)),
                (ma.clone(), b.clone()),
                (
                    wrap_var(&a, 0, MOp::Xor, flip),
                    wrap_var(&b, 0, MOp::Xor, flip),
                ),
                (
                    wrap_var(&a, 1, MOp::Or, flip),
                    wrap_var(&b, 1, MOp::Or, flip),
                ),
            ] {
                let truth = equal_everywhere(&x, &y);
                let r = certify::by_cases(&x, &y);
                match r.verdict {
                    Verdict::Proved => {
                        assert!(truth, "split proved an unequal pair:\n{x:?}\n{y:?}");
                        proved += 1;
                    }
                    Verdict::Refuted => {
                        assert!(!truth, "split refuted an equal pair:\n{x:?}\n{y:?}");
                        let p = r.counterexample.clone().expect("a counterexample");
                        assert_ne!(x.eval(&p), y.eval(&p), "not a counterexample: {p:?}");
                        refuted += 1;
                    }
                    Verdict::Unknown => {}
                }
                split += u32::from(r.split);
                assert_eq!(r.internal, 0);
            }
        }
    }
    // Every decided pair was decided by cases.
    assert_eq!(split, proved + refuted);
    assert!(proved > 100 && refuted > 100, "{proved} {refuted}");
}
