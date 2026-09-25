//! Symbols: free variables identified by a caller key and a fixed width.

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use crate::Width;
use crate::hash::{bytes, combine};

/// The identity of a symbol within a context.
///
/// Keys are opaque to bitwright. A key has exactly one width per context. The derived order
/// (integers, then strings, then fresh keys) is part of the canonical operand order, so it is
/// the same in every context.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[non_exhaustive]
pub enum SymbolKey {
    /// An integer key chosen by the caller (for example a register or variable number).
    U64(u64),
    /// A name.
    Str(Arc<str>),
    /// A key from [`Context::fresh_symbol`](crate::Context::fresh_symbol).
    Fresh(u64),
}

impl SymbolKey {
    pub(crate) fn structural_hash(&self) -> u64 {
        match self {
            SymbolKey::U64(k) => combine(1, *k),
            SymbolKey::Str(s) => bytes(2, s.as_bytes()),
            SymbolKey::Fresh(k) => combine(3, *k),
        }
    }

    /// Whether a string key can be printed as a bare identifier.
    pub(crate) fn is_plain_identifier(s: &str) -> bool {
        let mut chars = s.chars();
        matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
            && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '.')
            && !crate::text::is_reserved(s)
    }
}

impl fmt::Display for SymbolKey {
    /// The spelling used by the expression printer and accepted by the parser.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymbolKey::U64(k) => write!(f, "#{k}"),
            SymbolKey::Str(s) if SymbolKey::is_plain_identifier(s) => f.write_str(s),
            SymbolKey::Str(s) => {
                // An escaping the lexer reads back: \" \\ \n \t \r \0 and \u{hex}.
                f.write_str("\"")?;
                for c in s.chars() {
                    match c {
                        '"' => f.write_str("\\\"")?,
                        '\\' => f.write_str("\\\\")?,
                        '\n' => f.write_str("\\n")?,
                        '\t' => f.write_str("\\t")?,
                        '\r' => f.write_str("\\r")?,
                        '\0' => f.write_str("\\0")?,
                        c if c.is_ascii_graphic() || c == ' ' => write!(f, "{c}")?,
                        c => write!(f, "\\u{{{:x}}}", c as u32)?,
                    }
                }
                f.write_str("\"")
            }
            SymbolKey::Fresh(k) => write!(f, "${k}"),
        }
    }
}

impl From<u64> for SymbolKey {
    fn from(k: u64) -> Self {
        SymbolKey::U64(k)
    }
}

impl From<&str> for SymbolKey {
    fn from(s: &str) -> Self {
        SymbolKey::Str(Arc::from(s))
    }
}

impl From<String> for SymbolKey {
    fn from(s: String) -> Self {
        SymbolKey::Str(Arc::from(s))
    }
}

impl From<Arc<str>> for SymbolKey {
    fn from(s: Arc<str>) -> Self {
        SymbolKey::Str(s)
    }
}

/// A symbol's index within its context.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SymbolId(pub(crate) u32);

impl SymbolId {
    /// The index, dense from 0 in creation order within one context generation.
    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Debug)]
pub(crate) struct SymEntry {
    pub(crate) key: SymbolKey,
    pub(crate) width: Width,
    pub(crate) node: u32,
    /// What the host declared of the symbol's value ([`Context::declare_known`]).
    ///
    /// [`Context::declare_known`]: crate::Context::declare_known
    pub(crate) known: Option<crate::KnownBits>,
}

/// Lookup only; never iterated for a decision, so the std hasher is fine.
#[derive(Clone, Debug, Default)]
pub(crate) struct SymbolTable {
    pub(crate) entries: Vec<SymEntry>,
    pub(crate) index: HashMap<SymbolKey, u32>,
    pub(crate) next_fresh: u64,
}

impl SymbolTable {
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.index.clear();
        self.next_fresh = 0;
    }
}
