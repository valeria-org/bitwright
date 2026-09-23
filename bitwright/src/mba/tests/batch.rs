//! The batched evaluator against `MbaExpr::eval` and the reference evaluator.

use super::random::{Frag, Gen, every_point};
use crate::BitVec;
use crate::Width;
use crate::mba::batch::Program;
use bitwright_ref as r;

fn to_ref(v: &BitVec) -> r::Bits {
    r::Bits::from_limbs(v.width().bits(), v.limbs())
}

#[test]
fn batched_evaluation_matches_eval_and_the_reference_exhaustively() {
    let mut checked = 0;
    for w in 1..=8u16 {
        let width = Width::new(w).unwrap();
        // Fewer variables at larger widths: at most 16 bits in all.
        let t = (16 / w).clamp(1, 3) as u32;
        let mut g = Gen::new(0xba7c_0000 + u64::from(w), width, t);
        let rounds = if w <= 4 { 60 } else { 25 };
        for i in 0..rounds {
            let frag = [Frag::Any, Frag::Poly, Frag::SemiLinear][i % 3];
            let e = g.expr(frag, 3);
            let vars = vec![width; t as usize];
            let m = e.expr(&vars);
            let term = e.to_ref(&vars);
            let pts = every_point(&vars);
            let got = Program::new(&m, false).unwrap().eval_points(&pts);
            for (p, v) in pts.iter().zip(&got) {
                assert_eq!(Some(*v), m.eval(p), "{e:?} at {p:?}");
                let env: Vec<r::Bits> = p.iter().map(to_ref).collect();
                assert_eq!(to_ref(v), term.eval(&env).unwrap(), "{e:?} at {p:?}");
            }
            checked += pts.len();
        }
    }
    assert!(checked > 100_000, "{checked}");
}

#[test]
fn batched_evaluation_matches_eval_at_wide_widths() {
    for (i, w) in [9u16, 31, 63, 64, 65, 100, 127, 128, 129, 200, 256, 511, 512]
        .into_iter()
        .enumerate()
    {
        let width = Width::new(w).unwrap();
        let mut g = Gen::new(0xba7c_1000 + i as u64, width, 3);
        for _ in 0..20 {
            let e = g.expr(Frag::Any, 4);
            let vars = vec![width; 3];
            let m = e.expr(&vars);
            let term = e.to_ref(&vars);
            let pts: Vec<Vec<BitVec>> = (0..300)
                .map(|k| {
                    (0..3)
                        .map(|_| match k % 5 {
                            0 => BitVec::zero(width),
                            1 => BitVec::ones(width),
                            _ => BitVec::wrapping_from_limbs(
                                width,
                                &(0..8).map(|_| g.rng.next()).collect::<Vec<u64>>(),
                            ),
                        })
                        .collect()
                })
                .collect();
            let got = Program::new(&m, false).unwrap().eval_points(&pts);
            for (p, v) in pts.iter().zip(&got) {
                assert_eq!(Some(*v), m.eval(p), "{e:?} at {p:?}");
                let env: Vec<r::Bits> = p.iter().map(to_ref).collect();
                assert_eq!(to_ref(v), term.eval(&env).unwrap(), "{e:?} at {p:?}");
            }
        }
    }
}

#[test]
fn unused_nodes_are_skipped_or_kept_on_request() {
    use crate::mba::{MOp, MbaExpr};
    let w = Width::W8;
    let mut m = MbaExpr::new(vec![w, w]);
    let x = m.push(MOp::Var(0), &[]).unwrap();
    let y = m.push(MOp::Var(1), &[]).unwrap();
    let dead = m.push(MOp::Mul, &[x, y]).unwrap();
    m.push(MOp::Add, &[x, y]).unwrap();
    let p = Program::new(&m, false).unwrap();
    assert_eq!(p.len(), 3);
    assert_eq!(p.reg_of(dead as usize), None);
    let all = Program::new(&m, true).unwrap();
    assert_eq!(all.len(), 4);
    assert!(all.reg_of(dead as usize).is_some());
    assert!(Program::new(&MbaExpr::new(vec![w]), false).is_none());
}
