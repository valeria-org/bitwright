//! The MBA service (feature `mba`): simplification of mixed Boolean-arithmetic expressions by a
//! pluggable solver, behind an evidence gate. See `docs/design.md` §9.
//!
//! The engine lowers a fragment of the arena (`+ − * neg & | ^ ~`, constant shifts, casts) into
//! an [`MbaExpr`] over its atoms, asks the configured [`MbaSolver`], and accepts an answer only
//! with exact evidence: the linear-MBA signature (complete for linear MBA), exhaustive
//! evaluation for small inputs, an [`EquivalenceProver`], or, if the configuration trusts them,
//! the backend's certificate or sampling. The lifted result must also agree with the original
//! expression at seeded points, and it replaces the node only when the DAG gets smaller.
//!
//! ```
//! use bitwright::engine::{Engine, Phase, Strategy};
//! use bitwright::mba::MbaConfig;
//! use bitwright::{Context, ParseOptions, Width};
//!
//! let engine = Engine::builder()
//!     .builtin()
//!     .strategy(Strategy::new("mba", vec![Phase::Mba(MbaConfig::default())]))
//!     .build()?;
//! let mut cx = Context::new();
//! let e = cx.parse("(x ^ y) + 2 * (x & y) + ((x | y) - (x & y) - (x ^ y))", &ParseOptions::width(Width::W64))?;
//! let out = engine.simplify(&mut cx, e)?;
//! let want = cx.parse("x + y", &ParseOptions::width(Width::W64))?;
//! assert_eq!(out.expr, want);
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

mod batch;
pub(crate) mod certify;
// casts taken out of a question (see `decast`).
mod decast;
mod expr;
mod lower;
mod nf;
mod solve;
mod threaded;

pub use crate::engine::CertStats;
pub use certify::NativeProver;
pub use nf::{NfOptions, NfStats, NormalFormSolver};
pub use threaded::ThreadedSolver;

pub(crate) use decast::decast;
pub use expr::{MNode, MOp, MbaError, MbaExpr, Shape};
pub use lower::{Bindings, MbaLimits, Refusal, lift, lower};
pub(crate) use lower::{
    Reading, cuts, fits_nodes, lift_id, lower_id, lower_id_over, lower_id_reading, lower_id_whole,
    shared_nodes, shared_nodes_whole,
};
pub use solve::{
    CacheEntry, CacheKey, Claim, EquivalenceProver, MbaAnswer, MbaBudget, MbaCacheStore, MbaSolver,
    MemoryCache, NoCache, SignatureSolver, Verdict,
};

/// Which evidence beyond bitwright's own checks is accepted.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct MbaTrust {
    /// Accept a solver's `Proved` or `Certified` claim.
    pub backend_certificates: bool,
    /// Accept agreement at sampled points (not a proof).
    pub sampled: bool,
}

setters!(MbaTrust {
    with_backend_certificates: backend_certificates: bool,
    with_sampled: sampled: bool,
});

impl Default for MbaTrust {
    /// Neither: answers are accepted on bitwright's own certificates, or on the proof of a
    /// configured [`EquivalenceProver`], only.
    fn default() -> Self {
        MbaTrust {
            backend_certificates: false,
            sampled: false,
        }
    }
}

/// The configuration of a `Phase::Mba`.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct MbaConfig {
    /// What is lowered and asked about.
    pub limits: MbaLimits,
    /// Which evidence is accepted.
    pub trust: MbaTrust,
    /// Passed to the solver.
    pub budget: MbaBudget,
    /// Run the exact opaque-constant sweep before ordinary MBA phases. Off unless asked.
    pub opaque_sweep: bool,
    /// read noise forms used by obfuscated expressions. A rotate's
    /// slices (`x >>u k`, `x << k`) are asked as masks of one rotation where a fragment reads
    /// several (see `engine::pass::mba`); a root is read with what its conditions fix put into
    /// the operands they guard, and a piece that depends on one or two conditions alone is
    /// written as the table of its values (see `engine::pass::context`). The root the rounds
    /// settle on is read once more on either side of the condition its selects test most,
    /// each side simplified in turn, and the smaller of the two forms is the result: an
    /// obfuscator picks between two masked values by a flag, and with the flag fixed what is
    /// computed from one of them folds. Off unless asked.
    pub noise_forms: bool,
    /// the opaque-constant sweep asks a narrower reading its free atoms refute again
    /// with their known bits written out (`(v & unknown) | ones`), proves a root constant one
    /// case of the condition it tests at a time, and reconstructs a varying noise block as a
    /// select when each side is proved constant (see `engine::pass::mba`). Off unless asked.
    pub known_atoms: bool,
}

setters!(MbaConfig {
    with_limits: limits: MbaLimits,
    with_trust: trust: MbaTrust,
    with_budget: budget: MbaBudget,
    with_opaque_sweep: opaque_sweep: bool,
    with_noise_forms: noise_forms: bool,
    with_known_atoms: known_atoms: bool,
});

/// The version of the lowering (part of every cache key).
pub(crate) const LOWERING_VERSION: u64 = 1;

/// What [`decide`] makes of two expressions.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Decided {
    /// Equal at every value (at every value the facts allow, when facts were given).
    Equal,
    /// Different at these values of the symbols, at which the facts hold: evaluated, not
    /// inferred.
    Differ(Vec<(crate::SymbolKey, crate::BitVec)>),
    /// Not decided here.
    Unknown,
}

/// The points [`decide`] evaluates at in search of a witness, besides the corners.
const WITNESS_SAMPLES: u64 = 64;

/// [`equal`] as a decision procedure: with facts, and with a witness.
///
/// `zeros` are expressions known to be zero. Where they are bitwise functions of the same
/// parts as the two sides (the conjunction of two parts that share no bit, a part under the
/// complement of its mask), two linear MBAs over those parts are equal under them exactly
/// when they agree wherever the facts can hold, which is tested; other facts are only used
/// to rule witnesses out. A difference is reported with values of the symbols at which the
/// two sides evaluate differently and every fact is zero, looked for where every symbol is
/// zero or all ones and at a few other points: not finding one decides nothing.
///
/// ```
/// use bitwright::mba::{self, Decided, MbaBudget, MbaLimits};
/// use bitwright::{Context, ParseOptions, Width};
///
/// let mut cx = Context::new();
/// let o = ParseOptions::width(Width::W64);
/// let (limits, budget) = (MbaLimits::default(), MbaBudget::default());
/// // Two fields of a word, by their masks: no bit in common, so a sum is a disjunction.
/// let (s, t) = (cx.parse("x * y", &o)?, cx.parse("z >>u 3", &o)?);
/// let sum = cx.parse("x * y + (z >>u 3)", &o)?;
/// let or = cx.parse("x * y | (z >>u 3)", &o)?;
/// let overlap = cx.bin(bitwright::BinOp::And, s, t)?;
/// assert!(matches!(mba::decide(&mut cx, sum, or, &[], &limits, &budget)?, Decided::Differ(_)));
/// assert_eq!(mba::decide(&mut cx, sum, or, &[overlap], &limits, &budget)?, Decided::Equal);
/// # Ok::<(), bitwright::Error>(())
/// ```
pub fn decide(
    cx: &mut crate::Context,
    a: crate::Expr,
    b: crate::Expr,
    zeros: &[crate::Expr],
    limits: &MbaLimits,
    budget: &MbaBudget,
) -> Result<Decided, crate::Error> {
    if a == b {
        return Ok(Decided::Equal);
    }
    // For every value: the procedures, when the difference is in their fragment.
    if matches!(equal(cx, a, b, limits, budget), Ok(Verdict::Proved)) {
        return Ok(Decided::Equal);
    }
    // Under the facts: the corners they leave.
    if !zeros.is_empty() && crate::engine::corners_equal_given(cx, a, b, zeros)? {
        return Ok(Decided::Equal);
    }
    // A witness: values of the symbols, at which the facts hold and the sides differ.
    let mut roots = vec![a, b];
    roots.extend_from_slice(zeros);
    let mut symbols = Vec::new();
    for id in cx.symbols_in(&roots)? {
        if let (Some(k), Some(w)) = (cx.symbol_key(id).cloned(), cx.symbol_width(id)) {
            symbols.push((k, w));
        }
    }
    let corners = 1u64 << symbols.len().min(10);
    for point in 0..corners + WITNESS_SAMPLES {
        let model: Vec<(crate::SymbolKey, crate::BitVec)> = (symbols.iter().enumerate())
            .map(|(j, (k, w))| {
                let v = if point < corners {
                    if point >> (j % 10) & 1 == 1 {
                        crate::BitVec::ones(*w)
                    } else {
                        crate::BitVec::zero(*w)
                    }
                } else {
                    let h = crate::hash::mix64(
                        k.structural_hash() ^ point.wrapping_mul(0x9e37_79b9_7f4a_7c15),
                    );
                    crate::BitVec::wrapping_from_limbs(
                        *w,
                        &[h, h.rotate_left(17), !h, h.rotate_left(41)],
                    )
                };
                (k.clone(), v)
            })
            .collect();
        let Ok(values) = cx.eval(&roots, &model[..]) else {
            break;
        };
        if values[0] != values[1] && values[2..].iter().all(crate::BitVec::is_zero) {
            return Ok(Decided::Differ(model));
        }
    }
    Ok(Decided::Unknown)
}

#[cfg(test)]
#[rustfmt::skip] // Published source omits this test module; dependency formatting must not traverse it.
mod tests;

/// Whether `a` and `b` are equal for every value of their symbols, by the MBA procedures
/// alone: no engine, no circuit, no search. Their difference is lowered to an MBA
/// expression (sums, products and bitwise operations over atoms: every other subterm is a
/// variable) and tested against zero by the native prover, which decides linear and
/// semi-linear MBA and polynomials of low degree completely within `budget`.
///
/// [`Verdict::Proved`] is a proof for every value of the atoms, so of the expressions;
/// [`Verdict::Refuted`] is of the atoms as free variables, which they may not be (two atoms
/// may be related): together with [`Verdict::Unknown`] it means "not decided here". An error
/// when the difference is not in the fragment or is over `limits`.
///
/// ```
/// use bitwright::mba::{self, MbaBudget, MbaLimits, Verdict};
/// use bitwright::{Context, ParseOptions, Width};
///
/// let mut cx = Context::new();
/// let o = ParseOptions::width(Width::W64);
/// // Products of bitwise terms over an atom that is not a symbol (a quotient).
/// let a = cx.parse("(udiv(p, 7) ^ q) * (udiv(p, 7) & q) + (udiv(p, 7) & q) * (udiv(p, 7) & q)", &o)?;
/// let b = cx.parse("(udiv(p, 7) | q) * (udiv(p, 7) & q)", &o)?;
/// let (limits, budget) = (MbaLimits::default(), MbaBudget::default());
/// assert_eq!(mba::equal(&mut cx, a, b, &limits, &budget)?, Verdict::Proved);
/// let c = cx.parse("(udiv(p, 7) | q) * (udiv(p, 7) ^ q)", &o)?;
/// assert_ne!(mba::equal(&mut cx, a, c, &limits, &budget)?, Verdict::Proved);
/// # Ok::<(), bitwright::Error>(())
/// ```
pub fn equal(
    cx: &mut crate::Context,
    a: crate::Expr,
    b: crate::Expr,
    limits: &MbaLimits,
    budget: &MbaBudget,
) -> Result<Verdict, crate::Error> {
    let difference = cx.bin(crate::BinOp::Sub, a, b)?;
    let (lowered, _) = lower(cx, difference, limits)?;
    let Some(width) = lowered.width() else {
        return Ok(Verdict::Unknown);
    };
    let mut zero = MbaExpr::new(lowered.vars().to_vec());
    zero.push(MOp::Const(crate::BitVec::zero(width)), &[])
        .map_err(|e| crate::Error::Unsupported(format!("{e:?}")))?;
    Ok(NativeProver::new().prove_equal(&lowered, &zero, budget))
}
