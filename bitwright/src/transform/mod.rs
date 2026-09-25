//! Verifying compiler transformations: that a target program refines a source program under
//! LLVM's semantics of poison, undefined behavior and floating point, for peephole
//! transformations written in the transformation syntax the Alive paper introduced (Lopes et
//! al., PLDI 2015), and for pairs of functions in a subset of LLVM IR (translation
//! validation). Feature `prove`.
//!
//! ```
//! use bitwright::transform::{Config, Verdict, parse_transforms, verify};
//!
//! let t = parse_transforms(
//!     "Name: add of a not
//!      %a = xor %x, -1
//!      %r = add %a, 1
//!        =>
//!      %r = sub 0, %x",
//! )?;
//! assert!(matches!(verify(&t[0], &Config::default()).verdict(), Verdict::Valid));
//! # Ok::<(), bitwright::transform::SyntaxError>(())
//! ```
//!
//! Each value is its bits and a poison flag; each program has an undefined-behavior condition;
//! each nondeterministic choice (an `undef` use, a `freeze` of poison, a NaN's sign and
//! payload, a zero's sign under `nsz`) is a leaf, chosen by the source existentially and by the
//! target universally. Types left open are checked at each width (1 to 8, 16, 32, 64) and
//! format (half, float, double) they may take. The rewrite-based fast-math flags (`reassoc`,
//! `arcp`, `contract`, `afn`) are not modeled: a transformation that needs them is checked
//! against exact IEEE semantics.

mod alive;
pub(crate) mod encode;
mod infer;
pub mod ir;
mod lex;
pub(crate) mod llvm;
mod parse;
#[cfg(test)]
mod tests;
pub(crate) mod types;
mod value;
mod verify;

pub use alive::parse_transforms;
pub use infer::{Inference, infer};
pub use lex::SyntaxError;
pub use llvm::{FnText, function_pair, functions, pairs};
pub use types::Assignment;
pub use verify::{Config, Counterexample, Mismatch, Report, Shown, Verdict, verify};
