//! Error types shared across the crate.

use core::fmt;

/// A width, or a combination of widths, that the requested operation does not accept.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum WidthError {
    /// A width outside `1..=512`.
    Invalid {
        /// The rejected width.
        bits: u32,
    },
    /// Two operands that must have the same width do not.
    Mismatch {
        /// Width of the left operand.
        left: u16,
        /// Width of the right operand.
        right: u16,
    },
    /// Byte reversal of a width that is not a multiple of 8.
    NotByteMultiple {
        /// The operand width.
        bits: u16,
    },
    /// An extension to a width that is not larger than the operand.
    NotWider {
        /// The operand width.
        from: u16,
        /// The requested width.
        to: u16,
    },
    /// An extraction `[lo, lo + len)` that does not fit in the operand.
    ExtractRange {
        /// The operand width.
        width: u16,
        /// First extracted bit.
        lo: u16,
        /// Number of extracted bits.
        len: u16,
    },
    /// A concatenation wider than the maximum width.
    ConcatTooWide {
        /// Width of the high part.
        hi: u16,
        /// Width of the low part.
        lo: u16,
    },
    /// A selection condition that is not 1 bit wide.
    ConditionWidth {
        /// The condition width.
        bits: u16,
    },
    /// A floating-point format outside `2 ≤ eb ≤ 31`, `sb ≥ 2`, `eb + sb ≤ 512`.
    FpFormat {
        /// Exponent bits.
        eb: u32,
        /// Significand bits, the hidden bit included.
        sb: u32,
    },
}

impl fmt::Display for WidthError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Invalid { bits } => write!(f, "width {bits} is outside 1..=512"),
            Self::Mismatch { left, right } => write!(
                f,
                "operand widths differ ({left} vs {right}); insert an explicit zext/sext/trunc"
            ),
            Self::NotByteMultiple { bits } => {
                write!(f, "bswap needs a width that is a multiple of 8, got {bits}")
            }
            Self::NotWider { from, to } => {
                write!(f, "extension from {from} bits to {to} bits does not widen")
            }
            Self::ExtractRange { width, lo, len } => write!(
                f,
                "extract of bits [{lo}, {lo}+{len}) does not fit in a {width}-bit value"
            ),
            Self::ConcatTooWide { hi, lo } => {
                write!(f, "concatenation of {hi} and {lo} bits exceeds 512 bits")
            }
            Self::ConditionWidth { bits } => {
                write!(f, "select condition must be 1 bit wide, got {bits}")
            }
            Self::FpFormat { eb, sb } => write!(
                f,
                "floating-point format ({eb}, {sb}) is outside 2 <= eb <= 31, sb >= 2, eb + sb <= 512"
            ),
        }
    }
}

impl std::error::Error for WidthError {}

/// A value that cannot be represented at the requested width.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum ValueError {
    /// The width itself is invalid.
    Width(WidthError),
    /// The value needs more bits than the width provides.
    DoesNotFit {
        /// The requested width.
        width: u16,
    },
}

impl From<WidthError> for ValueError {
    fn from(e: WidthError) -> Self {
        Self::Width(e)
    }
}

impl fmt::Display for ValueError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Width(e) => e.fmt(f),
            Self::DoesNotFit { width } => write!(
                f,
                "value does not fit in {width} bits; use a wrapping constructor to truncate"
            ),
        }
    }
}

impl std::error::Error for ValueError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Width(e) => Some(e),
            Self::DoesNotFit { .. } => None,
        }
    }
}

/// Failure to parse a textual bit-vector literal.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum ParseError {
    /// The literal has no `:width` suffix (and is not in `N'hXX` form).
    MissingWidth,
    /// A malformed width.
    BadWidth(WidthError),
    /// A digit that is not valid in the literal's radix, or an empty digit string.
    BadDigit {
        /// Byte offset of the offending character.
        at: usize,
    },
    /// The value does not fit in the declared width.
    DoesNotFit {
        /// The declared width.
        width: u16,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingWidth => write!(f, "literal needs a width, e.g. `0xff:8`"),
            Self::BadWidth(e) => e.fmt(f),
            Self::BadDigit { at } => write!(f, "invalid digit at byte {at}"),
            Self::DoesNotFit { width } => write!(f, "literal does not fit in {width} bits"),
        }
    }
}

impl std::error::Error for ParseError {}

/// Errors from building, inspecting, evaluating or parsing expressions.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum Error {
    /// A width rule was violated (operand mismatch, bad cast, …).
    Width(WidthError),
    /// A value does not fit.
    Value(ValueError),
    /// A handle from this context, but from before the last [`Context::clear`](crate::Context::clear).
    StaleExpr,
    /// A handle from a different context.
    ForeignExpr,
    /// A symbol key was requested at a width different from the one it already has.
    SymbolWidthConflict {
        /// The symbol key.
        key: crate::SymbolKey,
        /// The width the symbol already has.
        have: crate::Width,
        /// The width that was requested.
        want: crate::Width,
    },
    /// The arena reached its configured node limit.
    ArenaFull {
        /// The configured limit.
        limit: u32,
    },
    /// Evaluation reached a symbol the environment does not bind.
    UnboundSymbol {
        /// The symbol key.
        key: crate::SymbolKey,
    },
    /// The environment bound a symbol to a value of the wrong width.
    EnvWidth {
        /// The symbol key.
        key: crate::SymbolKey,
        /// The symbol's width.
        expected: crate::Width,
        /// The width of the supplied value.
        got: crate::Width,
    },
    /// A syntax or typing error in expression text.
    Syntax(crate::text::SyntaxError),
    /// `substitute` was given the same expression to replace twice.
    DuplicateSubstitution,
    /// The operation does not support this input (the reason).
    Unsupported(String),
    /// An internal contract was violated: a library defect, or an unsound rule linked without a
    /// proof (the description).
    Contract(String),
}

impl From<WidthError> for Error {
    fn from(e: WidthError) -> Self {
        Self::Width(e)
    }
}

impl From<ValueError> for Error {
    fn from(e: ValueError) -> Self {
        Self::Value(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Width(e) => e.fmt(f),
            Self::Value(e) => e.fmt(f),
            Self::StaleExpr => write!(
                f,
                "expression handle is from before the context was cleared"
            ),
            Self::ForeignExpr => write!(f, "expression handle belongs to a different context"),
            Self::SymbolWidthConflict { key, have, want } => {
                write!(f, "symbol {key} already has width {have}; requested {want}")
            }
            Self::ArenaFull { limit } => write!(f, "arena is full ({limit} nodes)"),
            Self::UnboundSymbol { key } => write!(f, "symbol {key} is not bound"),
            Self::EnvWidth { key, expected, got } => write!(
                f,
                "symbol {key} has width {expected} but was bound to a {got}-bit value"
            ),
            Self::Syntax(e) => e.fmt(f),
            Self::DuplicateSubstitution => write!(f, "substitution replaces one expression twice"),
            Self::Unsupported(why) => write!(f, "unsupported: {why}"),
            Self::Contract(what) => write!(f, "contract violation: {what}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Width(e) => Some(e),
            Self::Value(e) => Some(e),
            Self::Syntax(e) => Some(e),
            _ => None,
        }
    }
}
