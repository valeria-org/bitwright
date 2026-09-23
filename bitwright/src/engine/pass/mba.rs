//! The MBA phase: lowering, the solver, the evidence gate, lifting (see [`crate::mba`]).

use super::{Fin, PassKind, Runner, Step, Stop, discard, finish};
use crate::engine::Exhausted;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::combine;
use crate::mba::certify;
use crate::mba::{
    CacheEntry, CacheKey, Claim, LOWERING_VERSION, MbaAnswer, MbaConfig, MbaExpr, Refusal, Verdict,
    lift_id, lower_id,
};

/// Points for the always-on refutation check and for trusted sampling.
const SAMPLE_POINTS: u32 = certify::SAMPLE_POINTS as u32;

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

/// Charges `evals` evaluations of both sides (their node counts) as pass work.
fn charge(r: &mut Runner<'_, '_>, a: &MbaExpr, b: &MbaExpr, evals: u64) -> Result<(), Stop> {
    let per = (a.nodes().len() + b.nodes().len()) as u64;
    r.meter
        .charge(Counter::PassWork, per.saturating_mul(evals))
        .map_err(Stop::Exhausted)
}

/// Whether `a` and `b` agree at the refutation sample: zero, all-ones, one and the signed
/// minimum, the constants of both sides and their neighbours, single bit positions, and seeded
/// random points (see [`certify::sample_points`]). A filter, never evidence on its own.
fn sampled(r: &mut Runner<'_, '_>, a: &MbaExpr, b: &MbaExpr) -> Result<bool, Stop> {
    charge(r, a, b, u64::from(SAMPLE_POINTS))?;
    let points = certify::sample_points(a.vars(), &[a, b], a.key()[0]);
    Ok(certify::refute(a, b, &points).is_none())
}

/// Pass work as a certificate's meter.
struct Gate<'x, 'r, 'a>(&'x mut Runner<'r, 'a>);

impl certify::Meter for Gate<'_, '_, '_> {
    type Err = Stop;
    fn left(&self) -> u64 {
        self.0.meter.left().pass_work
    }
    fn charge(&mut self, units: u64) -> Result<(), Stop> {
        self.0
            .meter
            .charge(Counter::PassWork, units)
            .map_err(Stop::Exhausted)
    }
}

/// bitwright's own exact evidence about `a == b`: the cheapest certificate that applies (the
/// corner signature, single bit positions, sparse points for degree `d`, the pure-polynomial
/// grid, exhaustive evaluation), over abstracted atoms when a side leaves the polynomial
/// fragment. Charged as pass work, a block at a time, so a budget or deadline can stop it; a
/// certificate larger than what is left is not started (reported as over budget).
fn exact(r: &mut Runner<'_, '_>, a: &MbaExpr, b: &MbaExpr) -> Result<certify::Report, Stop> {
    let report = certify::prove(a, b, &mut Gate(r))?;
    count(r).certificates.record(&report);
    Ok(report)
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
    // A solver that takes polynomials is also asked at constant left shifts (the arena spells
    // `2^k·t` as `t << k`).
    let poly = r.inner.mba.solver.polynomial_fragments();
    let op = cx.node(n).op;
    if !(mixed_op(op) || (poly && op == OpCode::Shl)) {
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
    // Mixed fragments, and polynomials (a product of two non-constants) for a solver that asks
    // for them.
    if !shape.mixed && !(shape.degree >= 2 && poly) {
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
                    let own = exact(r, &m, &expr)?;
                    if own.verdict == Verdict::Refuted {
                        count(r).refuted += 1;
                        return Ok(Step::Normal(Fin::FINAL));
                    }
                    let proved = own.verdict == Verdict::Proved
                        || inner.mba.prover.as_ref().is_some_and(|p| {
                            p.prove_equal(&m, &expr, &cfg.budget) == Verdict::Proved
                        })
                        || (cfg.trust.backend_certificates && claim >= Claim::Proved)
                        || cfg.trust.sampled;
                    if !proved {
                        count(r).proof_unknown += 1;
                        // A certificate skipped for lack of budget might decide with more:
                        // not final.
                        let fin = if own.over_budget {
                            Fin::capped(Exhausted::PassWork)
                        } else {
                            Fin::FINAL
                        };
                        return Ok(Step::Normal(fin));
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
