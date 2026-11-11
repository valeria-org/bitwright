//! What a pass asks of a prover, without naming one: whether two expressions of a scratch
//! context are equal, by a circuit and a search under caps. The engine does not know the
//! prover (which runs the engine as its simplifier); the crate gives it one
//! ([`crate::circuit_equality`]) where the feature `prove` is on.

use crate::error::Error;
use crate::expr::{Context, Expr};

/// The caps of one question.
#[derive(Copy, Clone, Debug)]
pub(crate) struct EqualityCaps {
    /// Points at which the two are evaluated before any search (a refutation there is one).
    pub(crate) samples: u32,
    /// The gates the circuit may have.
    pub(crate) max_nodes: usize,
    /// The propagations the search may make.
    pub(crate) max_propagations: u64,
}

/// What came of a question.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum EqualityVerdict {
    /// Equal at every value.
    Proved,
    /// Different at some value.
    Refuted,
    /// The search stopped at its propagations.
    Budget,
    /// Not decided for another reason (the circuit too large, an operator it does not read).
    Unknown,
}

/// A verdict with what it cost.
#[derive(Copy, Clone, Debug)]
pub(crate) struct EqualityAnswer {
    pub(crate) verdict: EqualityVerdict,
    /// The gates of the circuit (those it would have needed, when that was too many).
    pub(crate) nodes: usize,
    pub(crate) propagations: u64,
}

/// A prover of equalities: `cx` is a scratch context the question was copied into.
pub(crate) type EqualityProver =
    fn(cx: &mut Context, a: Expr, b: Expr, caps: &EqualityCaps) -> Result<EqualityAnswer, Error>;
