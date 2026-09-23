//! The linear pass: `c + Σ kᵢ·aᵢ` over Z/2^W.
//!
//! A node's *form* is computed from its operands' forms: `+`, `−`, negation, `~a = −a − 1`,
//! multiplication by a constant, shifts left by a constant (scaling), and `|`/`^` of operands
//! the facts prove disjoint (both are `+` then). Anything else is an *atom* with coefficient 1.
//! A form with more than [`MAX_TERMS`] terms is atomized. The form is re-emitted canonically
//! (terms in the context's canonical order, positive coefficients first, power-of-two
//! coefficients as shifts, the constant last), and the emission replaces the node only when
//! the region above the atoms gets strictly smaller.

use super::{Fin, PassKind, Runner, Step, Stop, facts, finish, worth_building};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::facts::known::bv_and;
use crate::ops::{BinOp, UnOp};

/// The most terms a form keeps before its node is treated as an atom.
pub(crate) const MAX_TERMS: usize = 64;

/// A linear form: `konst + Σ coeff·atom`, terms sorted by atom index, no zero coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Form {
    konst: BitVec,
    terms: Vec<(u32, BitVec)>,
    fin: Fin,
}

impl Form {
    /// `konst + Σ coeff·atom` (terms in any order; zero coefficients dropped, repeats merged).
    pub(super) fn of(konst: BitVec, terms: &[(u32, BitVec)]) -> Form {
        let mut f = Form {
            konst,
            terms: Vec::new(),
            fin: Fin::FINAL,
        };
        let w = konst.width();
        for &(a, k) in terms {
            let t = Form {
                konst: BitVec::zero(w),
                terms: if k.is_zero() {
                    Vec::new()
                } else {
                    vec![(a, k)]
                },
                fin: Fin::FINAL,
            };
            f = f.add(&t);
        }
        f
    }

    fn atom(n: u32, w: crate::Width) -> Form {
        Form {
            konst: BitVec::zero(w),
            terms: vec![(n, BitVec::one(w))],
            fin: Fin::FINAL,
        }
    }

    fn is_atom_of(&self, n: u32) -> bool {
        self.konst.is_zero()
            && self.terms.len() == 1
            && self.terms[0].0 == n
            && self.terms[0].1 == BitVec::one(self.konst.width())
    }

    fn scale(&self, k: &BitVec) -> Form {
        let terms = self
            .terms
            .iter()
            .map(|(a, c)| (*a, BitVec::bin_unchecked(BinOp::Mul, c, k)))
            .filter(|(_, c)| !c.is_zero())
            .collect();
        Form {
            konst: BitVec::bin_unchecked(BinOp::Mul, &self.konst, k),
            terms,
            fin: self.fin,
        }
    }

    fn add(&self, o: &Form) -> Form {
        let mut terms = Vec::with_capacity(self.terms.len() + o.terms.len());
        let (mut i, mut j) = (0, 0);
        while i < self.terms.len() || j < o.terms.len() {
            let pick = match (self.terms.get(i), o.terms.get(j)) {
                (Some(a), Some(b)) if a.0 == b.0 => {
                    let c = BitVec::bin_unchecked(BinOp::Add, &a.1, &b.1);
                    i += 1;
                    j += 1;
                    (a.0, c)
                }
                (Some(a), Some(b)) if a.0 < b.0 => {
                    i += 1;
                    *a
                }
                (Some(a), None) => {
                    i += 1;
                    *a
                }
                (_, Some(b)) => {
                    j += 1;
                    *b
                }
                (None, None) => break,
            };
            if !pick.1.is_zero() {
                terms.push(pick);
            }
        }
        Form {
            konst: BitVec::bin_unchecked(BinOp::Add, &self.konst, &o.konst),
            terms,
            fin: self.fin.and(o.fin),
        }
    }

    fn neg(&self) -> Form {
        let w = self.konst.width();
        self.scale(&BitVec::ones(w))
    }
}

/// An upper bound on the nodes [`emit`] creates for `form`: a constant and an operator per scaled
/// term, an operator per extra term, a negation when no term is positive, and the constant with
/// its add.
pub(super) fn estimate(form: &Form) -> u32 {
    let w = form.konst.width();
    let one = BitVec::one(w);
    let t = form.terms.len() as u32;
    let scaled = form
        .terms
        .iter()
        .filter(|(_, k)| *k != one && BitVec::un_unchecked(UnOp::Neg, k) != one)
        .count() as u32;
    let all_negative = t > 0 && form.terms.iter().all(|(_, k)| k.msb());
    let konst = match (t, form.konst.is_zero()) {
        (0, _) => 1,
        (_, true) => 0,
        _ => 2,
    };
    2 * scaled + t.saturating_sub(1) + u32::from(all_negative) + konst
}

/// Whether the node's operator can be part of a linear region.
fn linear_op(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Add
            | OpCode::Sub
            | OpCode::Neg
            | OpCode::Not
            | OpCode::Mul
            | OpCode::Shl
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Const
    )
}

/// The form of `root`, computing (iteratively) and caching the forms below it.
fn form_of(r: &mut Runner<'_, '_>, cx: &mut Context, root: u32) -> Result<Form, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.linear.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        if !linear_op(node.op) {
            r.linear.insert(i, Form::atom(i, cx.width_of(i)));
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if !r.linear.contains_key(&c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        let f = compute(r, cx, i)?;
        let f = if f.terms.len() > MAX_TERMS {
            r.stats.passes.entry("linear").or_default().atomized += 1;
            Form {
                fin: f.fin,
                ..Form::atom(i, cx.width_of(i))
            }
        } else {
            f
        };
        r.linear.insert(i, f);
    }
    Ok(r.linear[&root].clone())
}

/// The form of `i` from its operands' (cached) forms.
fn compute(r: &mut Runner<'_, '_>, cx: &mut Context, i: u32) -> Result<Form, Stop> {
    let node = cx.node(i);
    let w = cx.width_of(i);
    let get = |r: &Runner<'_, '_>, j: u32| r.linear[&j].clone();
    Ok(match node.op {
        OpCode::Const => Form {
            konst: cx.const_val(i).unwrap_or(BitVec::zero(w)),
            terms: Vec::new(),
            fin: Fin::FINAL,
        },
        OpCode::Add => get(r, node.a).add(&get(r, node.b)),
        OpCode::Sub => get(r, node.a).add(&get(r, node.b).neg()),
        OpCode::Neg => get(r, node.a).neg(),
        OpCode::Not => {
            let mut f = get(r, node.a).neg();
            f.konst = BitVec::bin_unchecked(BinOp::Sub, &f.konst, &BitVec::one(w));
            f
        }
        OpCode::Mul => match (cx.const_val(node.a), cx.const_val(node.b)) {
            (Some(k), _) => get(r, node.b).scale(&k),
            (_, Some(k)) => get(r, node.a).scale(&k),
            _ => Form::atom(i, w),
        },
        OpCode::Shl => match cx.const_val(node.b) {
            Some(k) => {
                let one = BitVec::one(w);
                // A count of W or more gives 0, and so does the scaling (2^k mod 2^W).
                let scale = BitVec::bin_unchecked(BinOp::Shl, &one, &k);
                get(r, node.a).scale(&scale)
            }
            None => Form::atom(i, w),
        },
        OpCode::Or | OpCode::Xor => {
            let (fa, fina) = facts(r, cx, node.a)?;
            let (fb, finb) = facts(r, cx, node.b)?;
            let disjoint = match (fa, fb) {
                (Some(a), Some(b)) => {
                    bv_and(&a.known().maybe_one(), &b.known().maybe_one()).is_zero()
                }
                _ => false,
            };
            if disjoint {
                // The sum relies on what proved the operands disjoint.
                let mut f = get(r, node.a).add(&get(r, node.b));
                f.fin = f.fin.and(fina).and(finb);
                f
            } else {
                Form {
                    fin: fina.and(finb).unchanged(),
                    ..Form::atom(i, w)
                }
            }
        }
        _ => Form::atom(i, w),
    })
}

/// Emits `form` canonically.
pub(super) fn emit(r: &mut Runner<'_, '_>, cx: &mut Context, form: &Form) -> Result<u32, Stop> {
    let w = form.konst.width();
    let mut terms = form.terms.clone();
    terms.sort_by(|a, b| cx.order(a.0, b.0));
    // Positive (signed non-negative) coefficients first, in canonical order; then the negated.
    let (pos, neg): (Vec<_>, Vec<_>) = terms.into_iter().partition(|(_, k)| !k.msb());
    let term =
        |r: &mut Runner<'_, '_>, cx: &mut Context, a: u32, k: &BitVec| -> Result<u32, Stop> {
            r.meter.charge(Counter::PassWork, 1)?;
            if *k == BitVec::one(w) {
                return Ok(a);
            }
            if crate::facts::known::count_ones(k) == 1 {
                let sh = BitVec::apply_un(UnOp::Ctz, k).map_err(|e| Stop::Error(e.into()))?;
                return r.build(cx, |cx| {
                    let s = cx.mk_const(&sh)?;
                    cx.c_bin(BinOp::Shl, a, s)
                });
            }
            r.build(cx, |cx| {
                let c = cx.mk_const(k)?;
                cx.c_bin(BinOp::Mul, a, c)
            })
        };
    let mut acc: Option<u32> = None;
    for (a, k) in &pos {
        let t = term(r, cx, *a, k)?;
        acc = Some(match acc {
            None => t,
            Some(x) => r.build(cx, |cx| cx.c_bin(BinOp::Add, x, t))?,
        });
    }
    for (a, k) in &neg {
        let nk = BitVec::un_unchecked(UnOp::Neg, k);
        let t = term(r, cx, *a, &nk)?;
        acc = Some(match acc {
            None => r.build(cx, |cx| cx.c_un(UnOp::Neg, t))?,
            Some(x) => r.build(cx, |cx| cx.c_bin(BinOp::Sub, x, t))?,
        });
    }
    let konst = form.konst;
    r.meter.check()?;
    match acc {
        None => r.build(cx, |cx| cx.mk_const(&konst)),
        Some(x) if konst.is_zero() => Ok(x),
        Some(x) => r.build(cx, |cx| {
            let c = cx.mk_const(&konst)?;
            cx.c_bin(BinOp::Add, x, c)
        }),
    }
}

/// The linear pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let op = cx.node(n).op;
    if !linear_op(op) || op == OpCode::Const {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let form = form_of(r, cx, n)?;
    if form.is_atom_of(n) {
        return Ok(Step::Normal(form.fin));
    }
    let mut atoms: Vec<u32> = form.terms.iter().map(|t| t.0).collect();
    atoms.sort_unstable();
    let estimate = estimate(&form);
    if let Some(f) = worth_building(r, cx, n, &atoms, estimate)? {
        r.stats.passes.entry("linear").or_default().rejected_cost += 1;
        return Ok(Step::Normal(form.fin.and(f)));
    }
    let before = cx.len() as u32;
    let e = emit(r, cx, &form)?;
    finish(r, cx, PassKind::Linear, n, e, before, &atoms, form.fin)
}
