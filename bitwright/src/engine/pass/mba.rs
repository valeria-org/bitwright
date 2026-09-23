//! The MBA phase: lowering, the solver, the evidence gate, lifting (see [`crate::mba`]).

use super::{Fin, PassKind, Runner, Step, Stop, discard, finish};
use crate::BitVec;
use crate::engine::Exhausted;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::combine;
use crate::mba::{
    CacheEntry, CacheKey, Claim, LOWERING_VERSION, MbaAnswer, MbaConfig, MbaExpr, Refusal, Verdict,
    lift_id, lower_id, mobius,
};

/// Exhaustive evaluation is exact evidence up to this many variable bits.
const EXHAUSTIVE_BITS: u32 = 20;

/// Points for the always-on refutation check and for trusted sampling.
const SAMPLE_POINTS: u32 = 64;

fn mixed_op(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::Neg
            | OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Not
    )
}

fn values(m: &MbaExpr, seed: u64, k: u32) -> Vec<BitVec> {
    let mut x = seed ^ u64::from(k).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    m.vars()
        .iter()
        .map(|&w| match k {
            0 => BitVec::zero(w),
            1 => BitVec::ones(w),
            2 => BitVec::one(w),
            3 => BitVec::smin(w),
            _ => {
                let limbs: Vec<u64> = (0..8)
                    .map(|_| {
                        x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
                        let mut z = x;
                        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                        z ^ (z >> 31)
                    })
                    .collect();
                BitVec::wrapping_from_limbs(w, &limbs)
            }
        })
        .collect()
}

/// Charges `evals` evaluations of both sides (their node counts) as pass work.
fn charge(r: &mut Runner<'_, '_>, a: &MbaExpr, b: &MbaExpr, evals: u64) -> Result<(), Stop> {
    let per = (a.nodes().len() + b.nodes().len()) as u64;
    r.meter
        .charge(Counter::PassWork, per.saturating_mul(evals))
        .map_err(Stop::Exhausted)
}

/// Whether `a` and `b` agree at `SAMPLE_POINTS` seeded points.
fn sampled(r: &mut Runner<'_, '_>, a: &MbaExpr, b: &MbaExpr) -> Result<bool, Stop> {
    charge(r, a, b, u64::from(SAMPLE_POINTS))?;
    let seed = a.key()[0];
    Ok((0..SAMPLE_POINTS).all(|k| {
        let v = values(a, seed, k);
        a.eval(&v) == b.eval(&v)
    }))
}

/// Exact evidence that `a == b`, if bitwright can establish it itself. The evaluations are
/// charged as pass work, a block at a time, so a budget or deadline can stop them.
fn exact(r: &mut Runner<'_, '_>, a: &MbaExpr, b: &MbaExpr) -> Result<bool, Stop> {
    if a.vars() != b.vars() {
        return Ok(false);
    }
    // Both linear MBA: equal signatures mean equal expressions.
    if a.is_linear() && b.is_linear() && a.vars().len() <= 12 {
        charge(r, a, b, 1u64 << a.vars().len())?;
        if let (Some(sa), Some(sb)) = (a.corners(), b.corners()) {
            return Ok(mobius(&sa) == mobius(&sb));
        }
    }
    // Small inputs: every assignment.
    let bits: u32 = a.vars().iter().map(|w| u32::from(w.bits())).sum();
    if bits <= EXHAUSTIVE_BITS {
        let vars = a.vars().to_vec();
        const BLOCK: u64 = 4096;
        let total = 1u64 << bits;
        let mut start = 0u64;
        while start < total {
            let end = (start + BLOCK).min(total);
            charge(r, a, b, end - start)?;
            let ok = (start..end).all(|case| {
                let mut rest = case;
                let v: Vec<BitVec> = vars
                    .iter()
                    .map(|&w| {
                        let x = BitVec::wrapping_from_u64(w, rest);
                        rest >>= w.bits();
                        x
                    })
                    .collect();
                a.eval(&v) == b.eval(&v)
            });
            if !ok {
                return Ok(false);
            }
            start = end;
        }
        return Ok(true);
    }
    Ok(false)
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::MbaStats {
    &mut r.stats.mba
}

/// The MBA phase at `n`.
pub(super) fn step(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
) -> Result<Step, Stop> {
    if !mixed_op(cx.node(n).op) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let (m, bindings) = match lower_id(cx, n, &cfg.limits) {
        Ok(x) => x,
        Err(why) => {
            count(r).refused(&why);
            return Ok(Step::Normal(Fin::FINAL));
        }
    };
    let shape = m.shape();
    if !shape.mixed {
        return Ok(Step::Normal(Fin::FINAL));
    }
    if shape.nodes < cfg.limits.min_nodes {
        count(r).refused(&Refusal::TooSmall);
        return Ok(Step::Normal(Fin::FINAL));
    }
    r.meter.charge(Counter::PassWork, u64::from(shape.nodes))?;
    let inner = r.inner;
    let prover_id = inner.mba.prover.as_ref().map_or("", |p| p.id());
    let mut kh = combine(m.key()[0], m.key()[1]);
    for b in inner.mba.solver.id().bytes().chain(prover_id.bytes()) {
        kh = combine(kh, u64::from(b));
    }
    // The trust setting is part of the key: an answer accepted on the backend's word or on
    // sampling must never be reused where that evidence is not accepted.
    kh = combine(
        combine(kh, u64::from(cfg.trust.backend_certificates)),
        u64::from(cfg.trust.sampled),
    );
    let key = CacheKey([
        combine(kh, LOWERING_VERSION),
        combine(kh ^ 0x6361_6368, m.key()[1]),
    ]);
    let (cand, verified) = match inner.mba.cache.get(&key) {
        Some(CacheEntry::NoSimpler) => {
            count(r).cache_hits += 1;
            return Ok(Step::Normal(Fin::FINAL));
        }
        Some(CacheEntry::Simplified(e)) if e.vars() == m.vars() => {
            count(r).cache_hits += 1;
            (e, true)
        }
        _ => {
            r.meter.charge(Counter::MbaCalls, 1)?;
            count(r).calls += 1;
            match inner.mba.solver.solve(&m, &cfg.budget) {
                MbaAnswer::Simplified { expr, claim } => {
                    if expr.vars() != m.vars() || expr.width() != m.width() {
                        count(r).refuted += 1;
                        return Ok(Step::Normal(Fin::FINAL));
                    }
                    // Always: a cheap refutation check.
                    if !sampled(r, &m, &expr)? {
                        count(r).refuted += 1;
                        return Ok(Step::Normal(Fin::FINAL));
                    }
                    let proved = exact(r, &m, &expr)?
                        || inner.mba.prover.as_ref().is_some_and(|p| {
                            p.prove_equal(&m, &expr, &cfg.budget) == Verdict::Proved
                        })
                        || (cfg.trust.backend_certificates && claim >= Claim::Proved)
                        || cfg.trust.sampled;
                    if !proved {
                        count(r).proof_unknown += 1;
                        return Ok(Step::Normal(Fin::FINAL));
                    }
                    inner
                        .mba
                        .cache
                        .put(&key, &CacheEntry::Simplified(expr.clone()));
                    (expr, false)
                }
                MbaAnswer::NoSimpler => {
                    count(r).no_simpler += 1;
                    inner.mba.cache.put(&key, &CacheEntry::NoSimpler);
                    return Ok(Step::Normal(Fin::FINAL));
                }
                MbaAnswer::Unsupported(_) => {
                    count(r).unsupported += 1;
                    return Ok(Step::Normal(Fin::FINAL));
                }
                MbaAnswer::Exhausted => {
                    count(r).exhausted += 1;
                    // More budget might succeed: not final.
                    return Ok(Step::Normal(Fin::capped(Exhausted::MbaCalls)));
                }
            }
        }
    };
    let _ = verified;
    let before = cx.len() as u32;
    let e = r.build(cx, |cx| lift_id(cx, &cand, &bindings))?;
    // The lifted result must agree with the original term (checks lowering and lifting).
    if e != n {
        r.sample(cx, n)?;
        r.sample(cx, e)?;
        if r.samples[&n] != r.samples[&e] {
            count(r).refuted += 1;
            discard(r, cx, before);
            return Ok(Step::Normal(Fin::FINAL));
        }
    }
    let out = finish(
        r,
        cx,
        PassKind::Mba,
        n,
        e,
        before,
        &bindings.atoms,
        Fin::FINAL,
    )?;
    if matches!(out, Step::To(..)) {
        count(r).simplified += 1;
    } else if e != n {
        count(r).not_smaller += 1;
    }
    Ok(out)
}
