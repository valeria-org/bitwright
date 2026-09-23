//! The native MBA solver and prover on arbitrary byte-encoded `MbaExpr`s: no panic; without
//! synthesis every `Simplified` answer is exact by construction, so it has the input's
//! variables and width and agrees with it at sampled points (the evidence gate either proves
//! it or refuses it for lack of proof, never for a refutation), and the prover never refutes
//! it. With synthesis, a `Proved` answer is held to the same; a `Sampled` one may be a table
//! hit no certificate could decide, so only its shape is checked. The prover never proves a
//! pair that differs at a sampled point.
#![no_main]

use bitwright::mba::{
    Claim, EquivalenceProver, MOp, MbaAnswer, MbaBudget, MbaExpr, MbaSolver, NativeProver,
    NfOptions, NormalFormSolver, Verdict,
};
use bitwright::{BitVec, Width};
use libfuzzer_sys::fuzz_target;

// Only the byte reader: the expression builder is for the arena.
#[allow(dead_code)]
mod common;
use common::Bytes;

/// An expression over one to three variables of one width, operands picked from earlier nodes.
fn build(b: &mut Bytes<'_>) -> Option<MbaExpr> {
    const WIDTHS: [u16; 8] = [1, 3, 8, 13, 32, 64, 65, 128];
    let w = Width::new(WIDTHS[usize::from(b.byte() % 8)]).ok()?;
    let nv = 1 + usize::from(b.byte() % 3);
    let mut m = MbaExpr::new(vec![w; nv]);
    for v in 0..nv {
        m.push(MOp::Var(v as u32), &[]).ok()?;
    }
    for _ in 0..40 {
        if b.0.is_empty() {
            break;
        }
        let op = b.byte();
        let n = m.nodes().len() as u32;
        let pick = |b: &mut Bytes<'_>| u32::from(b.byte()) % n;
        let r = match op % 14 {
            0 => m.push(MOp::Var(u32::from(b.byte()) % nv as u32), &[]),
            1 => {
                let v = BitVec::wrapping_from_limbs(w, &[b.u64(), b.u64()]);
                m.push(MOp::Const(v), &[])
            }
            2 => {
                let v = match b.byte() % 4 {
                    0 => BitVec::zero(w),
                    1 => BitVec::ones(w),
                    2 => BitVec::one(w),
                    _ => BitVec::wrapping_from_u64(w, u64::from(b.byte())),
                };
                m.push(MOp::Const(v), &[])
            }
            3 => {
                let (x, y) = (pick(b), pick(b));
                m.push(MOp::Add, &[x, y])
            }
            4 => {
                let (x, y) = (pick(b), pick(b));
                m.push(MOp::Sub, &[x, y])
            }
            5 => {
                let (x, y) = (pick(b), pick(b));
                m.push(MOp::Mul, &[x, y])
            }
            6 => {
                let (x, y) = (pick(b), pick(b));
                m.push(MOp::And, &[x, y])
            }
            7 => {
                let (x, y) = (pick(b), pick(b));
                m.push(MOp::Or, &[x, y])
            }
            8 => {
                let (x, y) = (pick(b), pick(b));
                m.push(MOp::Xor, &[x, y])
            }
            9 => {
                let x = pick(b);
                m.push(MOp::Not, &[x])
            }
            10 => {
                let x = pick(b);
                m.push(MOp::Neg, &[x])
            }
            11 => {
                let x = pick(b);
                let k = u16::from(b.byte()) % w.bits();
                m.push(MOp::Shl(k), &[x])
            }
            12 => {
                let x = pick(b);
                let k = u16::from(b.byte()) % w.bits();
                m.push(MOp::LShr(k), &[x])
            }
            _ => {
                // Through a wider view and back.
                let x = pick(b);
                let wide = Width::new(w.bits() + 1 + u16::from(b.byte() % 8)).ok()?;
                let op = if b.byte() % 2 == 0 { MOp::Zext } else { MOp::Sext };
                let y = m.push_cast(op, x, wide).ok()?;
                m.push_cast(MOp::Trunc, y, w)
            }
        };
        if r.is_err() {
            return None;
        }
    }
    Some(m)
}

/// Values at point `k`: zeros, ones, then mixed limbs.
fn point(vars: &[Width], k: u64) -> Vec<BitVec> {
    vars.iter()
        .enumerate()
        .map(|(v, &w)| match k {
            0 => BitVec::zero(w),
            1 => BitVec::ones(w),
            _ => {
                let h = (k ^ (v as u64) << 32).wrapping_mul(0x9e37_79b9_7f4a_7c15);
                BitVec::wrapping_from_limbs(w, &[h, h.rotate_left(29), h >> 7])
            }
        })
        .collect()
}

fuzz_target!(|data: &[u8]| {
    let mut b = Bytes(data);
    let Some(m) = build(&mut b) else {
        return;
    };
    let budget = MbaBudget::default().with_steps(1 << (10 + b.byte() % 12));
    let prover = NativeProver::default();
    for synthesis in [false, true] {
        let solver = NormalFormSolver::new(NfOptions::default().with_synthesis(synthesis));
        if let MbaAnswer::Simplified { expr, claim } = solver.solve(&m, &budget) {
            assert_eq!(expr.vars(), m.vars());
            assert_eq!(expr.width(), m.width());
            if synthesis && claim == Claim::Sampled {
                continue;
            }
            for k in 0..32 {
                let p = point(m.vars(), k);
                assert_eq!(m.eval(&p), expr.eval(&p), "{m:?}\n{expr:?}");
            }
            assert_ne!(prover.prove_equal(&m, &expr, &budget), Verdict::Refuted);
        }
    }
    // The prover against a copy with one more term: never proved when a point differs.
    let mut other = m.clone();
    let root = other.root().unwrap_or(0);
    let v = other.push(MOp::Var(0), &[]).unwrap_or(0);
    let x = other.push(MOp::And, &[v, root]).unwrap_or(0);
    let _ = other.push(MOp::Add, &[root, x]);
    let differs = (0..32).any(|k| {
        let p = point(m.vars(), k);
        m.eval(&p) != other.eval(&p)
    });
    if differs {
        assert_ne!(prover.prove_equal(&m, &other, &budget), Verdict::Proved);
    }
});
