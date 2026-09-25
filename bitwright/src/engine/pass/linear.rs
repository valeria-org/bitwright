//! The linear pass: `c + Σ kᵢ·aᵢ` over Z/2^W.
//!
//! A node's *form* is computed from its operands' forms: `+`, `−`, negation, `~a = −a − 1`,
//! multiplication by a constant, shifts left by a constant (scaling), and `|`/`^` of operands
//! the facts prove disjoint (both are `+` then). Anything else is an *atom* with coefficient 1.
//! A form with more than [`MAX_TERMS`] terms is atomized. The form is re-emitted canonically
//! (terms in the context's canonical order, positive coefficients first, power-of-two
//! coefficients as shifts, the constant last), and the emission replaces the node only when
//! the region above the atoms gets strictly smaller.

use super::{Fin, PassKind, Runner, Step, Stop, disjoint, finish, worth_building};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::facts::known::count_ones;
use crate::ops::{BinOp, UnOp};

/// The most terms a form keeps before its node is treated as an atom.
pub(crate) const MAX_TERMS: usize = 64;

/// A linear form: `konst + Σ coeff·atom`, terms sorted by atom index, no zero coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Form {
    konst: BitVec,
    terms: Vec<(u32, BitVec)>,
    pub(super) fin: Fin,
}

impl super::forms::Parts for Form {
    fn parts(&self) -> (&BitVec, &[(u32, BitVec)], Fin) {
        (&self.konst, &self.terms, self.fin)
    }

    fn from_parts(konst: BitVec, terms: Vec<(u32, BitVec)>, fin: Fin) -> Form {
        Form { konst, terms, fin }
    }
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

    pub(super) fn is_atom_of(&self, n: u32) -> bool {
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
/// term, an operator per extra term, a `~` for a term the constant is folded into, and the
/// constant with its operator (or a negation when no term is positive and there is no
/// constant).
pub(super) fn estimate(form: &Form) -> u32 {
    // Which term takes the constant in does not change the count.
    count(&plan(form, &form.terms))
}

/// What [`emit`] writes for a form: the constant and the terms `(atom, coefficient, under ~)`,
/// the whole complemented when `not`.
struct Plan {
    konst: BitVec,
    terms: Vec<(u32, BitVec, bool)>,
    not: bool,
}

/// The nodes [`emit`] creates for `plan`: a constant and an operator per scaled term, an
/// operator per extra term, a `~` per complemented term and for the whole, and the constant
/// with its operator (or a negation when no term is positive and there is no constant).
fn count(plan: &Plan) -> u32 {
    let (konst, terms) = (&plan.konst, &plan.terms);
    let w = konst.width();
    let one = BitVec::one(w);
    let t = terms.len() as u32;
    let two = BitVec::wrapping_from_u64(w, 2);
    let doubled = |k: &BitVec| *k == two || BitVec::un_unchecked(UnOp::Neg, k) == two;
    let scaled = terms
        .iter()
        .filter(|(_, k, _)| *k != one && BitVec::un_unchecked(UnOp::Neg, k) != one && !doubled(k))
        .count() as u32;
    // `a + a` is one node.
    let doubles = terms.iter().filter(|(_, k, _)| doubled(k)).count() as u32;
    let nots = terms.iter().filter(|(_, _, not)| *not).count() as u32;
    let minus_one = BitVec::ones(w);
    // With no positive term and no constant, a negation only when every coefficient is −1.
    let negation = t > 0 && terms.iter().all(|(_, k, _)| *k == minus_one);
    let konst = match (t, konst.is_zero()) {
        (0, _) => 1,
        (_, true) => u32::from(negation),
        _ => 2,
    };
    2 * scaled + doubles + t.saturating_sub(1) + nots + konst + u32::from(plan.not)
}

/// What [`emit`] writes for `form`, terms in the given order: the cheapest of trading the
/// constant for complements (ties to the plain sum). The first term whose coefficient equals
/// the constant takes it in, `k·a + k = (−k)·~a`, when the constant is negative (`−x − 1` is
/// `~x`) or a power of two from 2 (`2·y + 2` is `~y·−2`, where the shift's amount would be a
/// second constant); a constant 1 goes into a term of coefficient 1 beside another term
/// (`a + t + 1` is `a − ~t`) or splits one of coefficient 2 (`2·t + 1` is `t − ~t`); and a
/// constant −1 complements the negated rest (`−1 − 2·x` is `~(x + x)`).
fn plan(form: &Form, order: &[(u32, BitVec)]) -> Plan {
    let w = form.konst.width();
    let neg = |k: &BitVec| BitVec::un_unchecked(UnOp::Neg, k);
    let one = BitVec::one(w);
    let mut konst = form.konst;
    let mut terms: Vec<(u32, BitVec, bool)> = order.iter().map(|&(a, k)| (a, k, false)).collect();
    let pow2 = !konst.msb() && count_ones(&konst) == 1 && konst != one;
    if (konst.msb() || pow2)
        && let Some(t) = terms.iter_mut().find(|(_, k, _)| *k == konst)
    {
        t.1 = neg(&t.1);
        t.2 = true;
        konst = BitVec::zero(w);
    }
    let base = Plan {
        konst,
        terms,
        not: false,
    };
    let plain: Vec<(u32, BitVec, bool)> = order.iter().map(|&(a, k)| (a, k, false)).collect();
    let mut best = base;
    let consider = |p: Plan, best: &mut Plan| {
        if count(&p) < count(best) {
            *best = p;
        }
    };
    if form.konst == one {
        if plain.len() >= 2
            && let Some(i) = plain.iter().position(|(_, k, _)| *k == one)
        {
            let mut t = plain.clone();
            t[i] = (t[i].0, neg(&one), true);
            consider(
                Plan {
                    konst: BitVec::zero(w),
                    terms: t,
                    not: false,
                },
                &mut best,
            );
        }
        let two = BitVec::wrapping_from_u64(w, 2);
        if let Some(i) = plain.iter().position(|(_, k, _)| *k == two) {
            let mut t = plain.clone();
            let a = t[i].0;
            t[i] = (a, one, false);
            t.push((a, neg(&one), true));
            consider(
                Plan {
                    konst: BitVec::zero(w),
                    terms: t,
                    not: false,
                },
                &mut best,
            );
        }
    }
    if form.konst == BitVec::ones(w) && !plain.is_empty() {
        consider(
            Plan {
                konst: BitVec::zero(w),
                terms: plain.iter().map(|&(a, k, _)| (a, neg(&k), false)).collect(),
                not: true,
            },
            &mut best,
        );
    }
    best
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
            | OpCode::Concat
    )
}

/// The form of `root`, computing (iteratively) and caching the forms below it.
pub(super) fn form_of(r: &mut Runner<'_, '_>, cx: &mut Context, root: u32) -> Result<Form, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.linear.contains(i) {
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
                if !r.linear.contains(c) {
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
    Ok(r.linear
        .get(root)
        .expect("the root's form was just computed"))
}

/// The form of `i` from its operands' (cached) forms.
fn compute(r: &mut Runner<'_, '_>, cx: &mut Context, i: u32) -> Result<Form, Stop> {
    let node = cx.node(i);
    let w = cx.width_of(i);
    let get =
        |r: &Runner<'_, '_>, j: u32| r.linear.get(j).expect("operands' forms are computed first");
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
        // `concat(trunc(x), c)` with `x` of the full width is `x·2^|c| + c`: the bits of `x`
        // the truncation drops shift out.
        OpCode::Concat => {
            let hi = cx.node(node.a);
            match cx.const_val(node.b) {
                Some(c) if hi.op == OpCode::Extract && hi.b == 0 && cx.width_of(hi.a) == w => {
                    let j = u32::from(cx.width_of(node.b).bits());
                    let scale = crate::facts::known::bv_shl(&BitVec::one(w), j);
                    let mut f = Form::atom(hi.a, w).scale(&scale);
                    let lo = c.zext(w).unwrap_or(BitVec::zero(w));
                    f.konst = BitVec::bin_unchecked(BinOp::Add, &f.konst, &lo);
                    f
                }
                _ => Form::atom(i, w),
            }
        }
        OpCode::Or | OpCode::Xor => {
            let (disjoint, fina, finb) = disjoint(r, cx, node.a, node.b)?;
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
    let mut order = form.terms.clone();
    order.sort_by(|a, b| cx.order(a.0, b.0));
    let Plan {
        konst,
        mut terms,
        not: complemented,
    } = plan(form, &order);
    let w = konst.width();
    for (a, _, not) in terms.iter_mut() {
        if *not {
            let x = *a;
            *a = r.build(cx, |cx| cx.c_un(UnOp::Not, x))?;
        }
    }
    terms.sort_by(|a, b| cx.order(a.0, b.0));
    // Positive (signed non-negative) coefficients first, in canonical order; then the negated.
    let (pos, neg): (Vec<_>, Vec<_>) = terms.into_iter().partition(|(_, k, _)| !k.msb());
    let term =
        |r: &mut Runner<'_, '_>, cx: &mut Context, a: u32, k: &BitVec| -> Result<u32, Stop> {
            r.meter.charge(Counter::PassWork, 1)?;
            if *k == BitVec::one(w) {
                return Ok(a);
            }
            // `a + a`: one node, where a shift needs its amount too.
            if *k == BitVec::wrapping_from_u64(w, 2) {
                return r.build(cx, |cx| cx.c_bin(BinOp::Add, a, a));
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
    for (a, k, _) in &pos {
        let t = term(r, cx, *a, k)?;
        acc = Some(match acc {
            None => t,
            Some(x) => r.build(cx, |cx| cx.c_bin(BinOp::Add, x, t))?,
        });
    }
    // With no positive term, the constant starts the sum (`5 − 3·x`), or else the first
    // negative term is a product by its (negative) coefficient, one node cheaper than negating
    // it (`y·−2` for `−(y << 1)`); a coefficient of −1 stays a negation.
    let mut konst_left = konst;
    let mut first = None;
    if acc.is_none() && !neg.is_empty() {
        if !konst.is_zero() {
            acc = Some(r.build(cx, |cx| cx.mk_const(&konst))?);
            konst_left = BitVec::zero(w);
        } else if let Some(i) = neg.iter().position(|(_, k, _)| *k != BitVec::ones(w)) {
            let (a, k, _) = neg[i];
            r.meter.charge(Counter::PassWork, 1)?;
            acc = Some(r.build(cx, |cx| {
                let c = cx.mk_const(&k)?;
                cx.c_bin(BinOp::Mul, a, c)
            })?);
            first = Some(i);
        }
    }
    for (i, (a, k, _)) in neg.iter().enumerate() {
        if first == Some(i) {
            continue;
        }
        let nk = BitVec::un_unchecked(UnOp::Neg, k);
        let t = term(r, cx, *a, &nk)?;
        acc = Some(match acc {
            None => r.build(cx, |cx| cx.c_un(UnOp::Neg, t))?,
            Some(x) => r.build(cx, |cx| cx.c_bin(BinOp::Sub, x, t))?,
        });
    }
    r.meter.check()?;
    let sum = match acc {
        None => r.build(cx, |cx| cx.mk_const(&konst_left)),
        Some(x) if konst_left.is_zero() => Ok(x),
        Some(x) => r.build(cx, |cx| {
            let c = cx.mk_const(&konst_left)?;
            cx.c_bin(BinOp::Add, x, c)
        }),
    }?;
    if complemented {
        r.build(cx, |cx| cx.c_un(UnOp::Not, sum))
    } else {
        Ok(sum)
    }
}

/// The linear pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let op = cx.node(n).op;
    // A case split on a condition mask the node reads, first (see `cases`).
    let before = cx.len() as u32;
    if let Some((e, f)) = super::cases::split(r, cx, n)?
        && let Step::To(x, fin) = finish(r, cx, PassKind::Linear, n, e, before, &[], f)?
    {
        return Ok(Step::To(x, fin));
    }
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
    // A constant always commits (see `shrinks`).
    if !form.terms.is_empty()
        && let Some(f) = worth_building(r, cx, n, &atoms, estimate)?
    {
        r.stats.passes.entry("linear").or_default().rejected_cost += 1;
        return Ok(Step::Normal(form.fin.and(f)));
    }
    let before = cx.len() as u32;
    let e = emit(r, cx, &form)?;
    finish(r, cx, PassKind::Linear, n, e, before, &atoms, form.fin)
}
