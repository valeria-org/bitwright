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
#[cfg(feature = "cobra")]
mod cobra;
mod expr;
mod lower;
mod nf;
mod solve;
mod threaded;

pub use crate::engine::CertStats;
pub use certify::NativeProver;
#[cfg(feature = "cobra")]
pub use cobra::{CobraOptions, CobraSolver};
pub use nf::{NfOptions, NfStats, NormalFormSolver};
pub use threaded::ThreadedSolver;

pub use expr::{MNode, MOp, MbaError, MbaExpr, Shape};
pub use lower::{Bindings, MbaLimits, Refusal, lift, lower};
pub(crate) use lower::{fits, lift_id, lower_id};
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
    /// Backend certificates yes, sampling no.
    fn default() -> Self {
        MbaTrust {
            backend_certificates: true,
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
}

setters!(MbaConfig {
    with_limits: limits: MbaLimits,
    with_trust: trust: MbaTrust,
    with_budget: budget: MbaBudget,
});

/// The version of the lowering (part of every cache key).
pub(crate) const LOWERING_VERSION: u64 = 1;

#[cfg(test)]
mod tests;
