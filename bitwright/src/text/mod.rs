//! The expression syntax: a parser and a bounded printer.
//!
//! Hacker's-Delight-style infix with explicit signedness and Rust precedence:
//!
//! ```text
//! | ^ &  << >>u >>s  + -  *  ~x -x   == != <u <=u >u >=u <s <=s >s >=s
//! udiv urem sdiv srem rotl rotr umulhi smulhi pdep pext popcnt clz ctz bswap bitrev
//! zext<N>(x) sext<N>(x) trunc<N>(x) extract<LO, N>(x) concat(h, l) select(c, a, b)
//! umin umax smin smax andn orn xnor abs add_carry sub_borrow sadd_overflow ssub_overflow
//! add_sat_u add_sat_s sub_sat_u sub_sat_s
//! literals: 42  0xff  0b1010  true  false   width ascription: e:W
//! symbols: name  #123 (integer key)  $7 (fresh key)  "any name"
//! let %0 = x + 1; %0 * %0
//! ```
//!
//! A bare `>>` is an error (write `>>u` or `>>s`); a bare `<` only opens width arguments.
//! Comparisons do not chain. Literal and symbol widths are inferred from context where
//! possible; `ParseOptions::default_width` covers the rest.

pub(crate) mod lex;
mod parse;
mod print;

use core::fmt;

pub use parse::ParseOptions;
pub use print::{Display, PrintOptions};

/// A syntax or typing error with a byte span into the source.
#[derive(Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub struct SyntaxError {
    /// What went wrong.
    pub message: String,
    /// Start byte offset.
    pub start: usize,
    /// End byte offset (exclusive).
    pub end: usize,
}

impl SyntaxError {
    pub(crate) fn new(message: &str, start: usize, end: usize) -> Self {
        SyntaxError {
            message: message.to_string(),
            start,
            end,
        }
    }
}

impl fmt::Display for SyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} (at bytes {}..{})",
            self.message, self.start, self.end
        )
    }
}

impl std::error::Error for SyntaxError {}

/// Function names of the expression syntax.
pub(crate) const FUNCTIONS: &[&str] = &[
    "udiv",
    "urem",
    "sdiv",
    "srem",
    "rotl",
    "rotr",
    "umulhi",
    "smulhi",
    "pdep",
    "pext",
    "popcnt",
    "clz",
    "ctz",
    "bswap",
    "bitrev",
    "zext",
    "sext",
    "trunc",
    "extract",
    "concat",
    "select",
    "umin",
    "umax",
    "smin",
    "smax",
    "andn",
    "orn",
    "xnor",
    "abs",
    "add_carry",
    "sub_borrow",
    "sadd_overflow",
    "ssub_overflow",
    "add_sat_u",
    "add_sat_s",
    "sub_sat_u",
    "sub_sat_s",
];

/// Words of the rule language that may appear inside expressions (literals and guard
/// predicates). They are reserved in the expression syntax too, so printed text stays valid
/// wherever it is pasted.
pub(crate) const RULE_WORDS: &[&str] = &[
    "ones",
    "zero",
    "one",
    "smin_lit",
    "smax_lit",
    "lowmask",
    "bit",
    "proves",
    "zero_bits",
    "one_bits",
    "nonzero",
    "disjoint",
    "is_pow2",
    "is_lowmask",
    "is_shifted_mask",
];

/// Whether a name is a keyword or function name (so cannot be a bare symbol or `let` name).
/// Every name that starts with `fp.` is reserved for the floating-point operations.
pub(crate) fn is_reserved(s: &str) -> bool {
    matches!(s, "let" | "true" | "false")
        || FUNCTIONS.contains(&s)
        || RULE_WORDS.contains(&s)
        || s.starts_with("fp.")
}
