//! SMT-LIB 2.6 (QF_BV) export and import (feature `smtlib`).
//!
//! bitwright's semantics are SMT-LIB's (total division, shifts past the width), so every
//! expression has an exact QF_BV counterpart: operators map directly, and the ones QF_BV lacks
//! (population count, leading and trailing zeros, byte swap, bit reverse, `pdep`, `pext`, the high
//! half of a product, rotations by a symbolic count) are expanded. Any SMT-LIB 2.6 solver can
//! then evaluate an expression, check an equivalence, or prove a rule at any widths
//! ([`rule_obligation`]). [`import`] reads a QF_BV subset back.
//!
//! ```
//! use bitwright::{Context, ParseOptions, Width};
//! let mut cx = Context::new();
//! let e = cx.parse("udiv(x, y) + (x << 3)", &ParseOptions::width(Width::W8))?;
//! let smt = bitwright::smtlib::export(&mut cx, &[e])?;
//! assert!(smt.contains("(declare-const |x| (_ BitVec 8))"));
//! assert!(smt.contains("bvudiv"));
//! assert!(smt.contains("(define-fun root0 () (_ BitVec 8)"));
//!
//! // And back, into another context. (Operators SMT-LIB lacks come back expanded.)
//! let mut other = Context::new();
//! let script = bitwright::smtlib::import(&mut other, &smt)?;
//! let back = script.definition("root0").unwrap();
//! assert_eq!(other.display(back).to_string(), cx.display(e).to_string());
//! # Ok::<(), bitwright::Error>(())
//! ```

mod export;
mod import;
mod obligation;
#[cfg(test)]
mod tests;

pub use import::{Import, import};
pub use obligation::rule_obligation;

use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::facts::{Assumptions, Facts, Reliance};

/// The expressions as SMT-LIB 2.6: a `declare-const` per symbol, a `define-fun` per node
/// (operands first, so sharing is kept; the names `n…` are internal), and `define-fun rootK` for
/// the `K`-th root. Symbols keep their names where SMT-LIB can spell them (see [`import`] for
/// integer and fresh keys); others are named `sym!id`.
pub fn export(cx: &mut Context, roots: &[Expr]) -> Result<String, Error> {
    export::emit(cx, roots)
}

/// A complete script asking whether `a` and `b` can differ: `unsat` from a solver proves them
/// equal at their width; with `sat`, the model is a counterexample, unless the expressions
/// contain extension operations exported as uninterpreted functions (then the script says
/// `QF_UFBV`, and a model may rest on values the real operation never takes).
pub fn equivalence_query(cx: &mut Context, a: Expr, b: Expr) -> Result<String, Error> {
    if cx.width(a)? != cx.width(b)? {
        return Err(Error::Unsupported("different widths".into()));
    }
    let body = export::emit(cx, &[a, b])?;
    let mut s = logic(&body);
    s.push_str(&body);
    s.push_str("(assert (not (= root0 root1)))\n(check-sat)\n");
    Ok(s)
}

/// [`equivalence_query`] where the constraints of `assumptions` in `relied` hold: each is
/// asserted, so `unsat` proves `a` and `b` equal wherever they hold. Pass the
/// [`relies_on`](crate::engine::RootOutcome::relies_on) of a rewrite to check it independently
/// under exactly what it relied on.
pub fn equivalence_query_under(
    cx: &mut Context,
    a: Expr,
    b: Expr,
    assumptions: &Assumptions,
    relied: Reliance,
) -> Result<String, Error> {
    if cx.width(a)? != cx.width(b)? {
        return Err(Error::Unsupported("different widths".into()));
    }
    let mut roots = vec![a, b];
    let mut constraints = Vec::new();
    for (id, e, f) in assumptions.constraints() {
        if relied.may_use(id) {
            roots.push(e);
            constraints.push(f);
        }
    }
    let body = export::emit(cx, &roots)?;
    let mut s = logic(&body);
    s.push_str(&body);
    for (k, f) in constraints.iter().enumerate() {
        s.push_str(&facts_assertion(&format!("root{}", k + 2), f));
    }
    s.push_str("(assert (not (= root0 root1)))\n(check-sat)\n");
    Ok(s)
}

/// The `set-logic` line for a script: `QF_BV`, or `QF_UFBV` when extension operations without an
/// SMT-LIB definition were declared as uninterpreted functions. (Then `unsat` still proves
/// equality, but `sat` may be an artefact of the uninterpreted function, not a counterexample.)
fn logic(body: &str) -> String {
    if body.contains("(declare-fun ") {
        String::from("(set-logic QF_UFBV)\n")
    } else {
        String::from("(set-logic QF_BV)\n")
    }
}

/// `(assert …)` lines stating that `term` satisfies `f`.
fn facts_assertion(term: &str, f: &Facts) -> String {
    use crate::BitVec;
    let w = f.width();
    let lit = export::literal;
    let mut s = String::new();
    let k = f.known();
    if !k.known().is_zero() {
        s.push_str(&format!(
            "(assert (= (bvand {term} {}) {}))\n",
            lit(&k.known()),
            lit(&k.known_one())
        ));
    }
    let (u, sr) = (f.urange(), f.srange());
    if !u.lo().is_zero() {
        s.push_str(&format!("(assert (bvule {} {term}))\n", lit(&u.lo())));
    }
    if !u.hi().is_ones() {
        s.push_str(&format!("(assert (bvule {term} {}))\n", lit(&u.hi())));
    }
    if sr.lo() != BitVec::smin(w) {
        s.push_str(&format!("(assert (bvsle {} {term}))\n", lit(&sr.lo())));
    }
    if sr.hi() != BitVec::smax(w) {
        s.push_str(&format!("(assert (bvsle {term} {}))\n", lit(&sr.hi())));
    }
    s
}
