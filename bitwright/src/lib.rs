//! Hash-consed fixed-width bit-vector expressions: exact evaluation, bit-level facts, and
//! verified simplification.
//!
//! A guide with tested examples is in the repository's `book/`; the design reference is
//! `docs/design.md`.
//!
//! - [`BitVec`]: exact values of 1..=512 bits with total, SMT-LIB QF_BV semantics for every
//!   operator ([`UnOp`], [`BinOp`], [`CmpOp`], casts, [`BitVec::select`]).
//! - [`Context`]: a hash-consed expression arena with construction-time canonicalization,
//!   symbols, O(1) structural metadata, iterative traversal, evaluation and substitution, and a
//!   text syntax ([`Context::parse`], [`Context::display`]).
//! - [`Facts`]: known bits and unsigned/signed ranges per node (a reduced product), computed
//!   lazily and iteratively under a work cap, and tri-state proofs ([`Context::prove`]), also
//!   under consumer-defined constraints ([`Assumptions`]: facts and 1-bit predicates, propagated
//!   to operands, with the constraints each result relies on reported as a [`Reliance`]).
//! - [`rules`]: the `.bwr` rule language and its compiler; `check` (feature `check`, default):
//!   the soundness checker and proof ledgers.
//! - [`engine`]: the simplifier: proven rules and normal-form passes (linear, xor, bitwise,
//!   comparisons, casts, demanded bits, equalities through invertible maps, and for
//!   deobfuscation linear MBA and bit shuffles), applied bottom-up under caller-owned budgets,
//!   with a memo, telemetry and host hooks. [`Query::Injective`] and [`Query::Bijective`] ask
//!   whether an expression is an invertible function of one of its subexpressions.
//! - [`ext`]: host-defined extension operations (multi-output, total), registered in a
//!   [`Registry`](ext::Registry) and built with [`Context::ext`].
//! - `mba` (feature `mba`): the MBA service with an evidence gate and bitwright's own solvers;
//!   `eqsat` (feature `eqsat`): a bounded equality-saturation search; `smtlib` (feature
//!   `smtlib`): SMT-LIB export, import and rule obligations.
//!
//! ```
//! use bitwright::{BinOp, BitVec, Width};
//!
//! let x = BitVec::from_u64(Width::W8, 200)?;
//! let y = BitVec::from_u64(Width::W8, 100)?;
//! assert_eq!(BitVec::apply_bin(BinOp::Add, &x, &y)?.to_u64(), Some(44)); // mod 2^8
//! assert!(BitVec::apply_bin(BinOp::UDiv, &x, &BitVec::zero(Width::W8))?.is_ones()); // total
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```
//!
//! ```
//! use bitwright::{Context, ParseOptions, Width};
//!
//! let mut cx = Context::new();
//! let a = cx.parse("y + x", &ParseOptions::width(Width::W32))?;
//! let b = cx.parse("x + y", &ParseOptions::width(Width::W32))?;
//! assert_eq!(a, b); // canonical operand order: one node
//! // Construction canonicalizes and folds constants, but does not simplify further.
//! let c = cx.parse("(x - (2 + 3)) + 5", &ParseOptions::width(Width::W32))?;
//! assert_eq!(cx.display(c).to_string(), "x - 5 + 5");
//! # Ok::<(), bitwright::Error>(())
//! ```

/// `with_*` setters for configuration structs, one per listed field:
/// `setters!(Type { with_a: a: T, with_b: b ? U, })`, where `?` stores `Some(value)`. Every
/// entry ends with a comma.
macro_rules! setters {
    ($t:ident $(<$lt:lifetime>)? { $($body:tt)* }) => {
        impl$(<$lt>)? $t$(<$lt>)? {
            setters!(@items $t; $($body)*);
        }
    };
    (@items $t:ident; ) => {};
    (@items $t:ident; $set:ident : $field:ident ? $fty:ty, $($rest:tt)*) => {
        #[doc = concat!("Sets [`", stringify!($field), "`](", stringify!($t), "::", stringify!($field), ").")]
        #[must_use]
        pub fn $set(mut self, value: $fty) -> Self {
            self.$field = Some(value);
            self
        }
        setters!(@items $t; $($rest)*);
    };
    (@items $t:ident; $set:ident : $field:ident : $fty:ty, $($rest:tt)*) => {
        #[doc = concat!("Sets [`", stringify!($field), "`](", stringify!($t), "::", stringify!($field), ").")]
        #[must_use]
        pub fn $set(mut self, value: $fty) -> Self {
            self.$field = value;
            self
        }
        setters!(@items $t; $($rest)*);
    };
}

#[cfg(feature = "check")]
pub mod check;
pub mod engine;
#[cfg(feature = "eqsat")]
pub mod eqsat;
mod error;
mod expr;
pub mod ext;
mod facts;
mod hash;
mod invert;
#[cfg(feature = "mba")]
pub mod mba;
mod ops;
pub mod rules;
#[cfg(feature = "smtlib")]
pub mod smtlib;
#[cfg(test)]
mod testutil;

/// The README's and the book's examples (`book/src`), compiled and run as doctests.
#[cfg(doctest)]
mod book {
    #[doc = include_str!("../../README.md")]
    struct Readme;
    #[doc = include_str!("../../book/src/getting-started.md")]
    struct GettingStarted;
    #[doc = include_str!("../../book/src/semantics.md")]
    struct Semantics;
    #[doc = include_str!("../../book/src/facts.md")]
    struct Facts;
    #[doc = include_str!("../../book/src/constraints.md")]
    struct Constraints;
    #[doc = include_str!("../../book/src/extensions.md")]
    struct Extensions;
    #[doc = include_str!("../../book/src/simplifying.md")]
    struct Simplifying;
    #[cfg(feature = "check")]
    #[doc = include_str!("../../book/src/rules.md")]
    struct Rules;
    #[cfg(feature = "check")]
    #[doc = include_str!("../../book/src/checking.md")]
    struct Checking;
    #[cfg(feature = "mba")]
    #[doc = include_str!("../../book/src/deobfuscation.md")]
    struct Deobfuscation;
    #[doc = include_str!("../../book/src/invertibility.md")]
    struct Invertibility;
    #[cfg(feature = "eqsat")]
    #[doc = include_str!("../../book/src/eqsat.md")]
    struct Eqsat;
    #[cfg(feature = "smtlib")]
    #[doc = include_str!("../../book/src/smtlib.md")]
    struct Smtlib;
    #[doc = include_str!("../../book/src/stability.md")]
    struct Stability;
}
pub mod text;
mod value;

pub use error::{Error, ParseError, ValueError, WidthError};
pub use expr::traps;
pub use expr::{
    ArenaCounters, Bounded, Context, ContextConfig, Env, Expr, ExprMap, ExprSet, FnEnv, Mark,
    Substitution, SymbolId, SymbolKey, View,
};
pub use facts::{
    Assumptions, ConstraintId, Facts, KnownBits, Proof, Query, Reliance, SRange, Truth, URange,
};
pub use ops::{BinOp, CmpOp, CmpOpExt, UnOp};
pub use text::{ParseOptions, PrintOptions};
pub use value::{BitVec, Width};
