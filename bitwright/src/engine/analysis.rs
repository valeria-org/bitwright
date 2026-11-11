//! What the engine's procedures find out about an expression, without rewriting it: the
//! analyses the passes run before they decide whether to write anything.
//!
//! A pass is an analysis (the form an expression has), an emission (the form written out as
//! nodes) and a commit rule (whether the nodes replace the expression: only when the result
//! is smaller). A caller that wants the form itself, to compare two expressions, to solve
//! for a term, to hand a prover a normal form, has no use for the last two. These are the
//! analyses on their own: the same code the passes run, with the facts of the context, and
//! nothing is written.

use super::budget::Meter;
use super::{Budget, Engine, Runner, Stop};
use crate::BitVec;
use crate::error::Error;
use crate::expr::{Context, Expr};

/// An expression as a sum: `constant + Σ coefficient · term` modulo two to the width.
///
/// The terms are subexpressions that are not sums, differences, negations, products by a
/// constant or shifts left by one (and what the linear pass reads as those: a complement, a
/// disjunction of disjoint parts): each occurs once, with a coefficient that is not zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearForm {
    /// The constant term.
    pub constant: BitVec,
    /// Each coefficient with its term.
    pub terms: Vec<(BitVec, Expr)>,
}

/// An expression as an exclusive or: `constant ^ ⊕ (mask & term)`.
///
/// The terms are subexpressions that are not exclusive ors, complements, or conjunctions and
/// disjunctions with a constant: each occurs once, with a mask that is not zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct XorForm {
    /// The constant term.
    pub constant: BitVec,
    /// Each mask with its term.
    pub terms: Vec<(BitVec, Expr)>,
}

/// An expression as a bitwise function of at most three terms: on the bit positions of each
/// mask, the truth table the expression has there.
///
/// Entry `p` of a table (bit `p` of the byte) is the expression's bit where term `k` has bit
/// `k` of `p`: with terms `[x, y]`, `0b0110` is `x ^ y` and `0b1000` is `x & y`. The masks
/// are disjoint and cover every position; constants in the expression are what makes the
/// table differ from one class of positions to another.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BitwiseForm {
    /// The terms: subexpressions that are not `&`, `|`, `^` or `~` (three at most).
    pub terms: Vec<Expr>,
    /// Each class of bit positions, as a mask, with the truth table there.
    pub classes: Vec<(BitVec, u8)>,
}

/// What a predicate (a 1-bit expression made of comparisons and Boolean operators) says.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PredicateForm {
    /// The same at every value.
    Constant(bool),
    /// A set of values of one term: the predicate holds exactly when the term is in one of
    /// the intervals (unsigned, inclusive, in order, apart).
    Values {
        /// The term.
        of: Expr,
        /// The intervals.
        intervals: Vec<(BitVec, BitVec)>,
    },
    /// A set of relations of two terms: the predicate holds exactly when `left` is to
    /// `right` in one of them. Bit 0 of `relations`: equal; bit 1: below unsigned and below
    /// signed; bit 2: below unsigned, above signed; bit 3: above unsigned, below signed;
    /// bit 4: above both.
    Relation {
        /// The first term.
        left: Expr,
        /// The second term.
        right: Expr,
        /// The relations, as bits.
        relations: u8,
    },
    /// Nothing the comparison pass reads (a relation of floats included).
    Opaque,
}

impl Engine {
    /// What the 1-bit `e` says about its operands: the comparison pass's reading of a
    /// predicate, which is exact. Comparisons of one term with constants, joined by Boolean
    /// operators, are a set of the term's values; comparisons of two terms are a set of the
    /// ways two values can be ordered.
    ///
    /// ```
    /// use bitwright::engine::{Engine, PredicateForm};
    /// use bitwright::{Context, ParseOptions, Width};
    ///
    /// let mut cx = Context::new();
    /// let o = ParseOptions::width(Width::W8);
    /// let e = cx.parse("(x >u 10) & ~(x >=u 20) | (x == 200)", &o)?;
    /// let PredicateForm::Values { intervals, .. } = Engine::standard().predicate_form(&mut cx, e)?
    /// else {
    ///     panic!("a set of values of x");
    /// };
    /// let ends: Vec<(u64, u64)> = (intervals.iter())
    ///     .map(|(a, b)| (a.to_u64().unwrap(), b.to_u64().unwrap()))
    ///     .collect();
    /// assert_eq!(ends, [(11, 19), (200, 200)]);
    /// // Not below and not equal, unsigned: above.
    /// let e = cx.parse("~(x <u y) & (x != y)", &o)?;
    /// let PredicateForm::Relation { relations, .. } = Engine::standard().predicate_form(&mut cx, e)?
    /// else {
    ///     panic!("a relation of x and y");
    /// };
    /// assert!(relations == 0b11000 || relations == 0b00110);
    /// # Ok::<(), bitwright::Error>(())
    /// ```
    pub fn predicate_form(&self, cx: &mut Context, e: Expr) -> Result<PredicateForm, Error> {
        use super::pass::compares::Info;
        let id = cx.id(e)?;
        let mut runner = self.analyst(id);
        Ok(match super::pass::compares::info_of(&mut runner, cx, id) {
            Ok(Info::Const(b)) => PredicateForm::Constant(b),
            Ok(Info::Values(x, set, _)) => PredicateForm::Values {
                of: cx.handle(x),
                intervals: set,
            },
            Ok(Info::Pair(x, y, relations)) => PredicateForm::Relation {
                left: cx.handle(x),
                right: cx.handle(y),
                relations,
            },
            Ok(_) | Err(Stop::Exhausted(_)) => PredicateForm::Opaque,
            Err(Stop::Error(e)) => return Err(e),
        })
    }

    /// `e` as a bitwise function of at most three terms and some constants: the bitwise
    /// pass's reading of it, which is exact. `None` when it is no such function (more
    /// terms, more constants or a larger region than the pass reads).
    ///
    /// ```
    /// use bitwright::engine::Engine;
    /// use bitwright::{Context, ParseOptions, Width};
    ///
    /// let mut cx = Context::new();
    /// let o = ParseOptions::width(Width::W8);
    /// // On the low nibble `x & y`, on the high one `x | y`.
    /// let e = cx.parse("(x & y) | ((x | y) & 0xf0)", &o)?;
    /// let form = Engine::standard().bitwise_form(&mut cx, e)?.unwrap();
    /// assert_eq!(form.terms.len(), 2);
    /// let mut classes: Vec<(u64, u8)> = (form.classes.iter())
    ///     .map(|(m, t)| (m.to_u64().unwrap(), t & 0b1111))
    ///     .collect();
    /// classes.sort();
    /// assert_eq!(classes, [(0x0f, 0b1000), (0xf0, 0b1110)]);
    /// # Ok::<(), bitwright::Error>(())
    /// ```
    pub fn bitwise_form(&self, cx: &mut Context, e: Expr) -> Result<Option<BitwiseForm>, Error> {
        let id = cx.id(e)?;
        let mut runner = self.analyst(id);
        match super::pass::bitwise::masked(&mut runner, cx, &[id]) {
            Ok(Some(m)) => {
                let (atoms, classes) = m.atoms_classes();
                Ok(Some(BitwiseForm {
                    terms: atoms.iter().map(|&a| cx.handle(a)).collect(),
                    classes: classes.map(|(m, t)| (*m, t)).collect(),
                }))
            }
            Ok(None) | Err(Stop::Exhausted(_)) => Ok(None),
            Err(Stop::Error(e)) => Err(e),
        }
    }

    /// `e` as a sum of constant multiples of terms: the linear pass's reading of it, which
    /// is exact (`e` equals the sum at every value). An expression the pass does not read as
    /// a sum is the one term, once.
    ///
    /// ```
    /// use bitwright::engine::Engine;
    /// use bitwright::{Context, ParseOptions, Width};
    ///
    /// let mut cx = Context::new();
    /// let o = ParseOptions::width(Width::W32);
    /// let e = cx.parse("3 * (x + 5) - (y << 2) + x - ~z", &o)?;
    /// let form = Engine::standard().linear_form(&mut cx, e)?;
    /// // 4x - 4y + z + 16
    /// assert_eq!(form.constant.to_u64(), Some(16));
    /// let mut terms: Vec<(i32, String)> = (form.terms.iter())
    ///     .map(|(c, t)| (c.to_u64().unwrap() as u32 as i32, cx.display(*t).to_string()))
    ///     .collect();
    /// terms.sort();
    /// assert_eq!(terms, [(-4, "y".into()), (1, "z".into()), (4, "x".into())]);
    /// # Ok::<(), bitwright::Error>(())
    /// ```
    pub fn linear_form(&self, cx: &mut Context, e: Expr) -> Result<LinearForm, Error> {
        let id = cx.id(e)?;
        let mut runner = self.analyst(id);
        let (constant, terms) = match super::pass::linear::form_of(&mut runner, cx, id) {
            Ok(form) => {
                let (k, ts) = form.konst_terms();
                (*k, ts.to_vec())
            }
            Err(Stop::Error(e)) => return Err(e),
            // Out of the work an analysis is allowed: the expression as it is.
            Err(Stop::Exhausted(_)) => {
                let w = cx.width(e)?;
                (BitVec::zero(w), vec![(id, BitVec::wrapping_from_u64(w, 1))])
            }
        };
        Ok(LinearForm {
            constant,
            terms: (terms.into_iter())
                .map(|(t, c)| (c, cx.handle(t)))
                .collect(),
        })
    }

    /// `e` as an exclusive or of masked terms: the xor pass's reading of it, which is exact.
    /// An expression the pass does not read as one is the one term under a mask of all
    /// ones.
    ///
    /// ```
    /// use bitwright::engine::Engine;
    /// use bitwright::{Context, ParseOptions, Width};
    ///
    /// let mut cx = Context::new();
    /// let o = ParseOptions::width(Width::W8);
    /// let e = cx.parse("~(x ^ 0x0f) ^ (y & 0x3c) ^ x ^ (z | 0xf0)", &o)?;
    /// let form = Engine::standard().xor_form(&mut cx, e)?;
    /// // x cancels: (y & 0x3c) ^ (z & 0x0f) ^ 0x00
    /// assert_eq!(form.constant.to_u64(), Some(0x00));
    /// let mut terms: Vec<(u64, String)> = (form.terms.iter())
    ///     .map(|(m, t)| (m.to_u64().unwrap(), cx.display(*t).to_string()))
    ///     .collect();
    /// terms.sort();
    /// assert_eq!(terms, [(0x0f, "z".into()), (0x3c, "y".into())]);
    /// # Ok::<(), bitwright::Error>(())
    /// ```
    pub fn xor_form(&self, cx: &mut Context, e: Expr) -> Result<XorForm, Error> {
        let id = cx.id(e)?;
        let mut runner = self.analyst(id);
        let (constant, terms) = match super::pass::xor::form_of(&mut runner, cx, id) {
            Ok(form) => {
                let (k, ts) = form.konst_terms();
                (*k, ts.to_vec())
            }
            Err(Stop::Error(e)) => return Err(e),
            Err(Stop::Exhausted(_)) => {
                let w = cx.width(e)?;
                (BitVec::zero(w), vec![(id, BitVec::ones(w))])
            }
        };
        Ok(XorForm {
            constant,
            terms: (terms.into_iter())
                .map(|(t, m)| (m, cx.handle(t)))
                .collect(),
        })
    }

    /// An expression equal to `e` on the bits of `mask` (and anything on the others): what
    /// the demanded-bits pass makes of an operand of which only those bits are read. A part
    /// that cannot reach the bits is dropped, and a part whose bits there are known is a
    /// constant. The result may be `e` itself.
    ///
    /// ```
    /// use bitwright::engine::Engine;
    /// use bitwright::{BitVec, Context, ParseOptions, Width};
    ///
    /// let mut cx = Context::new();
    /// let o = ParseOptions::width(Width::W32);
    /// // Only the low byte is read: the high parts do not reach it.
    /// let e = cx.parse("((x | 0xff00) + (y << 8)) ^ (z & 0xffff0000)", &o)?;
    /// let low = BitVec::wrapping_from_u64(Width::W32, 0xff);
    /// let out = Engine::standard().under_mask(&mut cx, e, &low)?;
    /// assert_eq!(cx.display(out).to_string(), "x");
    /// # Ok::<(), bitwright::Error>(())
    /// ```
    pub fn under_mask(&self, cx: &mut Context, e: Expr, mask: &BitVec) -> Result<Expr, Error> {
        let id = cx.id(e)?;
        if cx.width(e)? != mask.width() {
            return Err(Error::Contract(
                "the mask is not of the expression's width".into(),
            ));
        }
        let mut runner = self.analyst(id);
        match super::pass::demanded::under_mask(&mut runner, cx, id, mask) {
            Ok(out) => Ok(cx.handle(out)),
            Err(Stop::Exhausted(_)) => Ok(e),
            Err(Stop::Error(e)) => Err(e),
        }
    }

    /// A runner for an analysis: the engine's rules and facts, the default budget, no
    /// observer, hooks or assumptions.
    fn analyst(&self, root: u32) -> Runner<'_, 'static> {
        let meter = Meter::new(Budget::default(), None);
        Runner::new(&self.inner, meter, None, None, None, &[root])
    }
}
