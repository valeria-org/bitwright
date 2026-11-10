//! The MBA service's extension points: solvers, provers, caches, and the native signature
//! solver.

use std::collections::{HashMap, VecDeque};
use std::sync::Mutex;

use super::expr::{MOp, MbaExpr};
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// What a solver may spend on one question. Solvers treat it as a hint; the engine enforces its
/// own budget on calls.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct MbaBudget {
    /// A work bound in the solver's own units, for one question. In the engine a question
    /// runs within the least of this and what is left of the run's
    /// [`Budget::mba_steps`](crate::engine::Budget::mba_steps).
    pub steps: u64,
    /// Whether answers should carry the solver's own evidence (default true). A caller that
    /// proves every answer itself asks without, and a solver may then skip checking an answer
    /// it built exactly (answering [`Claim::Unverified`]); the engine does so when backend
    /// certificates are not trusted.
    pub evidence: bool,
}

impl Default for MbaBudget {
    fn default() -> Self {
        MbaBudget {
            steps: 1 << 20,
            evidence: true,
        }
    }
}

setters!(MbaBudget {
    with_steps: steps: u64,
    with_evidence: evidence: bool,
});

/// The evidence a solver attaches to an answer.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Claim {
    /// None.
    Unverified,
    /// Agreement at sampled points only.
    Sampled,
    /// Proved (for example by an SMT solver, or by a complete method).
    Proved,
    /// A checked certificate (for example a replayed proof).
    Certified,
}

/// A solver's answer.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum MbaAnswer {
    /// An equivalent expression over the same variables, and the evidence for it.
    Simplified {
        /// The simpler expression.
        expr: MbaExpr,
        /// Its evidence.
        claim: Claim,
    },
    /// The input is already as simple as this solver can make it (a complete answer).
    NoSimpler,
    /// The solver does not handle this input.
    Unsupported(String),
    /// The solver ran out of budget (never cached).
    Exhausted,
}

/// A backend that simplifies MBA expressions.
pub trait MbaSolver: Send + Sync {
    /// A stable name, including anything that changes answers (it keys the caches).
    fn id(&self) -> &str;
    /// Simplifies `p`.
    fn solve(&self, p: &MbaExpr, budget: &MbaBudget) -> MbaAnswer;
    /// Simplifies `p`, and says how many of `budget`'s steps it spent: what the engine charges
    /// the call against [`Budget::mba_steps`](crate::engine::Budget::mba_steps). A solver that
    /// counts its work reports what it spent, and a remembered answer what finding it cost, so
    /// that a charge does not depend on what the solver remembers. This default is
    /// [`solve`](Self::solve) charged its whole limit (`budget.steps`), the most a solver that
    /// keeps to its budget spends.
    fn solve_counted(&self, p: &MbaExpr, budget: &MbaBudget) -> (MbaAnswer, u64) {
        (self.solve(p, budget), budget.steps)
    }
    /// Whether `Phase::Mba` should also ask about polynomials: fragments without bitwise
    /// operators in which two non-constants are multiplied, and fragments rooted at a constant
    /// left shift. By default only mixed fragments (arithmetic and bitwise operators) rooted at
    /// `+ − · neg & | ^ ~` are asked about.
    fn polynomial_fragments(&self) -> bool {
        false
    }
}

/// The outcome of an equivalence proof attempt.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Verdict {
    /// Equal on every input.
    Proved,
    /// Different on some input.
    Refuted,
    /// Not decided.
    Unknown,
}

/// A backend that proves two MBA expressions equal.
pub trait EquivalenceProver: Send + Sync {
    /// A stable name (it keys the caches).
    fn id(&self) -> &str;
    /// Decides whether `a` and `b` are equal on every input.
    fn prove_equal(&self, a: &MbaExpr, b: &MbaExpr, budget: &MbaBudget) -> Verdict;
}

/// A cache key: the input's content hash, the solver and prover ids, and the lowering version.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct CacheKey(pub [u64; 2]);

/// A durable cache entry: only verified results and complete "no simpler" answers.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum CacheEntry {
    /// A verified simpler expression.
    Simplified(MbaExpr),
    /// The solver answered, completely, that nothing is simpler.
    NoSimpler,
}

/// Where the MBA service keeps answers across calls. bitwright performs no IO: persistent
/// stores belong to the host.
pub trait MbaCacheStore: Send + Sync {
    /// The entry for `k`.
    fn get(&self, k: &CacheKey) -> Option<CacheEntry>;
    /// Stores an entry.
    fn put(&self, k: &CacheKey, e: &CacheEntry);
}

/// A cache that keeps nothing.
#[derive(Copy, Clone, Debug, Default)]
pub struct NoCache;

impl MbaCacheStore for NoCache {
    fn get(&self, _: &CacheKey) -> Option<CacheEntry> {
        None
    }
    fn put(&self, _: &CacheKey, _: &CacheEntry) {}
}

/// A bounded in-memory cache (oldest entries evicted first).
#[derive(Debug)]
pub struct MemoryCache {
    capacity: usize,
    inner: Mutex<(HashMap<CacheKey, CacheEntry>, VecDeque<CacheKey>)>,
}

impl MemoryCache {
    /// A cache of at most `capacity` entries.
    pub fn new(capacity: usize) -> MemoryCache {
        MemoryCache {
            capacity,
            inner: Mutex::new((HashMap::new(), VecDeque::new())),
        }
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.inner.lock().map_or(0, |g| g.0.len())
    }

    /// Whether it is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl MbaCacheStore for MemoryCache {
    fn get(&self, k: &CacheKey) -> Option<CacheEntry> {
        self.inner.lock().ok()?.0.get(k).cloned()
    }

    fn put(&self, k: &CacheKey, e: &CacheEntry) {
        let Ok(mut g) = self.inner.lock() else {
            return;
        };
        if self.capacity == 0 {
            return;
        }
        if g.0.insert(*k, e.clone()).is_none() {
            g.1.push_back(*k);
        }
        while g.0.len() > self.capacity {
            match g.1.pop_front() {
                Some(old) => {
                    g.0.remove(&old);
                }
                None => break,
            }
        }
    }
}

/// The native solver: complete for linear MBA (arithmetic over bitwise functions of the
/// variables), from the values at the all-zero/all-ones corners. It answers with the affine form
/// when there is one, or the combination of the variables' conjunctions, and "no simpler" when
/// that is not smaller; other inputs are unsupported.
#[derive(Copy, Clone, Debug, Default)]
pub struct SignatureSolver;

/// The most variables the signature solver takes (2^t corners).
const SIGNATURE_MAX_VARS: usize = 10;

/// Node evaluations per step of the signature solver's work (as the normal-form solver counts
/// its certificates').
const SIGNATURE_EVALS_PER_STEP: u64 = 32;

impl MbaSolver for SignatureSolver {
    fn id(&self) -> &str {
        "bitwright.signature.v1"
    }

    fn solve(&self, p: &MbaExpr, budget: &MbaBudget) -> MbaAnswer {
        self.solve_counted(p, budget).0
    }

    /// Its work is evaluating the input at the 2^t corners, counted as the normal-form solver
    /// counts certificate evaluations (a step per 32 node evaluations); a signature that does
    /// not fit `budget.steps` is not computed (exhausted, nothing spent).
    fn solve_counted(&self, p: &MbaExpr, budget: &MbaBudget) -> (MbaAnswer, u64) {
        if !p.is_linear() {
            return (MbaAnswer::Unsupported("not a linear MBA".into()), 0);
        }
        let t = p.vars().len();
        if t > SIGNATURE_MAX_VARS || p.vars().iter().any(|&w| Some(w) != p.width()) {
            let why = "too many variables, or mixed widths";
            return (MbaAnswer::Unsupported(why.into()), 0);
        }
        let steps = ((p.nodes().len() as u64) << t).div_ceil(SIGNATURE_EVALS_PER_STEP);
        if steps > budget.steps {
            return (MbaAnswer::Exhausted, 0);
        }
        let Some(sig) = p.corners() else {
            return (MbaAnswer::Unsupported("no signature".into()), steps);
        };
        let Some(w) = p.width() else {
            return (MbaAnswer::Unsupported("empty".into()), steps);
        };
        let d = mobius(&sig);
        let m = conjunction_form(p.vars(), w, &d);
        let answer = match m {
            Some(m) if m.nodes().len() < p.nodes().len() => MbaAnswer::Simplified {
                expr: m,
                claim: Claim::Proved,
            },
            _ => MbaAnswer::NoSimpler,
        };
        (answer, steps)
    }
}

/// The conjunction coefficients `d_S` from corner values: `−E(p) = Σ_{S ⊆ p} d_S`.
pub(crate) fn mobius(sig: &[BitVec]) -> Vec<BitVec> {
    let mut d: Vec<BitVec> = sig
        .iter()
        .map(|v| BitVec::un_unchecked(UnOp::Neg, v))
        .collect();
    let n = d.len();
    let mut bit = 1;
    while bit < n {
        for p in 0..n {
            if p & bit != 0 {
                d[p] = BitVec::bin_unchecked(BinOp::Sub, &d[p], &d[p ^ bit]);
            }
        }
        bit <<= 1;
    }
    d
}

/// `Σ_S d_S · AND_S` (with `AND_∅ = −1`) as an expression: the constant first, then each
/// conjunction with its coefficient.
fn conjunction_form(vars: &[Width], w: Width, d: &[BitVec]) -> Option<MbaExpr> {
    let mut m = MbaExpr::new(vars.to_vec());
    let var_nodes: Vec<u32> = (0..vars.len() as u32)
        .map(|i| m.push(MOp::Var(i), &[]))
        .collect::<Result<_, _>>()
        .ok()?;
    let konst = BitVec::un_unchecked(UnOp::Neg, &d[0]);
    let mut acc = m.push(MOp::Const(konst), &[]).ok()?;
    let one = BitVec::one(w);
    for (s, ds) in d.iter().enumerate().skip(1) {
        if ds.is_zero() {
            continue;
        }
        let mut conj: Option<u32> = None;
        for (j, &v) in var_nodes.iter().enumerate() {
            if s >> j & 1 == 1 {
                conj = Some(match conj {
                    None => v,
                    Some(c) => m.push(MOp::And, &[c, v]).ok()?,
                });
            }
        }
        let conj = conj?;
        let term = if *ds == one {
            conj
        } else {
            let k = m.push(MOp::Const(*ds), &[]).ok()?;
            m.push(MOp::Mul, &[conj, k]).ok()?
        };
        acc = m.push(MOp::Add, &[acc, term]).ok()?;
    }
    Some(m)
}
