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
    Reading, fits_nodes, lift_id, lower_id, lower_id_over, lower_id_reading, lower_id_whole,
    shared_nodes,
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
    /// written as the table of its values (see `engine::pass::context`). Off unless asked.
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

#[cfg(test)]
#[rustfmt::skip] // Published source omits this test module; dependency formatting must not traverse it.
mod tests;
