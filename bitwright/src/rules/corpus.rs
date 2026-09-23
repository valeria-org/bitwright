//! The built-in rule corpus: embedded source, compiled at run time, and its proof ledger.

/// The source of the built-in rules.
pub(crate) const CORE: &str = include_str!("corpus/core.bwr");

/// The ledger that vouches for them.
pub(crate) const CORE_LEDGER: &str = include_str!("corpus/core.bwr.proof");

/// The identities of the equality-saturation search service.
pub(crate) const EQSAT: &str = include_str!("corpus/eqsat.bwr");

/// The ledger that vouches for them.
pub(crate) const EQSAT_LEDGER: &str = include_str!("corpus/eqsat.bwr.proof");
