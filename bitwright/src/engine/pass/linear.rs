//! The linear pass: `c + Σ kᵢ·aᵢ` over Z/2^W.
//!
//! A node's *form* is computed from its operands' forms: `+`, `−`, negation, `~a = −a − 1`,
//! multiplication by a constant, shifts left by a constant (scaling), `|`/`^` of operands the
//! facts prove disjoint (both are `+` then). Anything else is an *atom* with coefficient 1,
//! except that a sum with both `sext(c)` and `zext(c)` of a 1-bit `c` reads the first as
//! `−zext(c)`.
//! A form with more than [`MAX_TERMS`] terms is atomized. The form is re-emitted canonically
//! (terms in the context's canonical order, positive coefficients first, power-of-two
//! coefficients as shifts, the constant last), and the emission replaces the node only when
//! the region above the atoms gets strictly smaller.

use super::{Fin, PassKind, Runner, Step, Stop, disjoint, finish, worth_building};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, Node, OpCode};
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

    /// The form modulo `2^j` (`j` up to the width): the constant and coefficients by their low
    /// `j` bits, sign-extended, and terms whose coefficient that makes 0 dropped.
    pub(super) fn reduce(&self, j: crate::Width) -> Form {
        let w = self.konst.width();
        let low = |v: &BitVec| v.trunc(j).and_then(|t| t.sext(w)).unwrap_or(*v);
        let terms: Vec<(u32, BitVec)> = self.terms.iter().map(|&(a, k)| (a, low(&k))).collect();
        let mut f = Form::of(low(&self.konst), &terms);
        f.fin = self.fin;
        f
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
        OpCode::Add => merge_complements(cx, merge_signs(cx, get(r, node.a).add(&get(r, node.b)))),
        OpCode::Sub => merge_complements(
            cx,
            merge_signs(cx, get(r, node.a).add(&get(r, node.b).neg())),
        ),
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

/// `form` with each term `k·sext(c)` of a 1-bit `c` (`0` or `−1`) moved to `−k·zext(c)` when
/// the form has that atom too, so the two readings of a condition cancel. Only then: building a
/// `zext` for a lone `sext` would make the emission look cheaper than it is.
fn merge_signs(cx: &Context, form: Form) -> Form {
    let w = form.konst.width();
    let mut moves = Vec::new();
    for &(a, k) in &form.terms {
        let n = cx.node(a);
        if n.op == OpCode::Sext
            && cx.width_of(n.a).bits() == 1
            && let Some(z) = cx.find(&Node::new(OpCode::Zext, w.bits(), n.a, 0, 0))
            && form.terms.binary_search_by_key(&z, |t| t.0).is_ok()
        {
            let minus_k = BitVec::un_unchecked(UnOp::Neg, &k);
            moves.push((a, z, minus_k));
        }
    }
    if moves.is_empty() {
        return form;
    }
    let fin = form.fin;
    let mut f = form;
    for (a, z, minus_k) in moves {
        f = f.add(&Form::of(BitVec::zero(w), &[(a, minus_k), (z, minus_k)]));
    }
    f.fin = fin;
    f
}

/// `form` with each term `k·zext(~t)` moved to `k·lowmask(W) − k·zext(t)` and each
/// `k·sext(~t)` to `−k − k·sext(t)` when the form has the extension of `t` as a term too, so
/// the two cancel: `sext(a) + sext(~a)` is `−1`. Only then, as [`merge_signs`]: the extension
/// found in the arena may be a dead node, and a rewrite over it would look cheaper than it is.
fn merge_complements(cx: &Context, form: Form) -> Form {
    let w = form.konst.width();
    let mut moves = Vec::new();
    for &(a, k) in &form.terms {
        let n = cx.node(a);
        if !matches!(n.op, OpCode::Zext | OpCode::Sext) {
            continue;
        }
        let inner = cx.node(n.a);
        if inner.op == OpCode::Not
            && let Some(z) = cx.find(&Node::new(n.op, w.bits(), inner.a, 0, 0))
            && form.terms.binary_search_by_key(&z, |t| t.0).is_ok()
        {
            let c = if n.op == OpCode::Zext {
                crate::facts::known::low_mask(w, u32::from(cx.width_of(n.a).bits()))
            } else {
                BitVec::ones(w)
            };
            moves.push((a, z, k, c));
        }
    }
    if moves.is_empty() {
        return form;
    }
    let fin = form.fin;
    let mut f = form;
    for (a, z, k, c) in moves {
        let minus_k = BitVec::un_unchecked(UnOp::Neg, &k);
        let kc = BitVec::bin_unchecked(BinOp::Mul, &k, &c);
        f = f.add(&Form::of(kc, &[(a, minus_k), (z, minus_k)]));
    }
    f.fin = fin;
    f
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

/// multiplicative leaves of one term, bounded so factor search never turns a large
/// product into pass work proportional to its tree.
#[derive(Copy, Clone)]
struct Product {
    factors: [u32; MAX_PRODUCT_FACTORS],
    len: usize,
}

const MAX_PRODUCT_FACTORS: usize = 8;

fn product(cx: &Context, n: u32) -> Option<Product> {
    fn collect(cx: &Context, n: u32, out: &mut Product) -> Option<()> {
        let node = cx.node(n);
        if node.op == OpCode::Mul {
            collect(cx, node.a, out)?;
            collect(cx, node.b, out)
        } else if out.len < out.factors.len() {
            out.factors[out.len] = n;
            out.len += 1;
            Some(())
        } else {
            None
        }
    }

    let mut out = Product {
        factors: [0; MAX_PRODUCT_FACTORS],
        len: 0,
    };
    collect(cx, n, &mut out)?;
    Some(out)
}

/// Additive terms of one sum, bounded for the same reason as [`Product`].
#[derive(Copy, Clone)]
struct Sum {
    terms: [u32; MAX_SUM_TERMS],
    len: usize,
}

const MAX_SUM_TERMS: usize = 16;

fn sum(cx: &Context, n: u32) -> Option<Sum> {
    fn collect(cx: &Context, n: u32, out: &mut Sum) -> Option<()> {
        let node = cx.node(n);
        if node.op == OpCode::Add {
            collect(cx, node.a, out)?;
            collect(cx, node.b, out)
        } else if out.len < out.terms.len() {
            out.terms[out.len] = n;
            out.len += 1;
            Some(())
        } else {
            None
        }
    }

    let mut out = Sum {
        terms: [0; MAX_SUM_TERMS],
        len: 0,
    };
    collect(cx, n, &mut out)?;
    Some(out)
}

/// A structurally shared factor and its position in every product, preferring a non-constant.
fn common_factor(cx: &Context, products: &[Product]) -> Option<(u32, [usize; MAX_SUM_TERMS])> {
    let first = products.first()?;
    for constants in [false, true] {
        for &factor in &first.factors[..first.len] {
            if cx.is_const(factor) != constants {
                continue;
            }
            let mut positions = [0; MAX_SUM_TERMS];
            let mut found = true;
            for (i, p) in products.iter().enumerate() {
                let Some(j) = p.factors[..p.len].iter().position(|&x| x == factor) else {
                    found = false;
                    break;
                };
                positions[i] = j;
            }
            if found {
                return Some((factor, positions));
            }
        }
    }
    None
}

/// `a·x + a·~x`, including extra factors shared by both products, is `-a`.
///
/// Do this directly rather than through [`factor_sum`]'s one-factor-at-a-time rewrite. When
/// both products are also used elsewhere, the intermediate factored form does not shrink the
/// live DAG and is correctly rejected before the complementary cofactors meet.
fn complementary_products(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    products: &[Product],
) -> Result<Option<Step>, Stop> {
    let [left, right] = products else {
        return Ok(None);
    };
    let mut used = [false; MAX_PRODUCT_FACTORS];
    let mut common = [0; MAX_PRODUCT_FACTORS];
    let mut common_len = 0;
    let mut left_only = None;
    for &factor in &left.factors[..left.len] {
        if let Some(i) = right.factors[..right.len]
            .iter()
            .enumerate()
            .position(|(i, other)| !used[i] && *other == factor)
        {
            used[i] = true;
            common[common_len] = factor;
            common_len += 1;
        } else if left_only.replace(factor).is_some() {
            return Ok(None);
        }
    }
    let mut right_only = None;
    for (i, &factor) in right.factors[..right.len].iter().enumerate() {
        if !used[i] && right_only.replace(factor).is_some() {
            return Ok(None);
        }
    }
    let Some((a, b)) = left_only.zip(right_only) else {
        return Ok(None);
    };
    let complements = (cx.node(a).op == OpCode::Not && cx.node(a).a == b)
        || (cx.node(b).op == OpCode::Not && cx.node(b).a == a);
    if !complements {
        return Ok(None);
    }

    let before = cx.len() as u32;
    let mut shared = match common[..common_len].split_first() {
        Some((&first, rest)) => {
            let mut out = first;
            for &factor in rest {
                out = r.build(cx, |cx| cx.c_bin(BinOp::Mul, out, factor))?;
            }
            out
        }
        None => {
            let one = BitVec::one(cx.width_of(n));
            r.build(cx, |cx| cx.mk_const(&one))?
        }
    };
    shared = r.build(cx, |cx| cx.c_un(UnOp::Neg, shared))?;
    let mut atoms = [0; MAX_PRODUCT_FACTORS * 2];
    let mut count = 0;
    for product in products {
        for &factor in &product.factors[..product.len] {
            if !atoms[..count].contains(&factor) {
                atoms[count] = factor;
                count += 1;
            }
        }
    }
    Ok(Some(finish(
        r,
        cx,
        PassKind::Linear,
        n,
        shared,
        before,
        &atoms[..count],
        Fin::FINAL,
    )?))
}

/// A product rebuilt without one of its factors. A caller supplies a product of at least two
/// leaves, so one always remains.
fn without_factor(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    p: &Product,
    skip: usize,
) -> Result<u32, Stop> {
    if p.len == 1 {
        let one = BitVec::one(cx.width_of(p.factors[0]));
        return r.build(cx, |cx| cx.mk_const(&one));
    }
    let first = usize::from(skip == 0);
    let mut out = p.factors[first];
    for (i, &f) in p.factors[..p.len].iter().enumerate() {
        if i == skip || i == first {
            continue;
        }
        out = r.build(cx, |cx| cx.c_bin(BinOp::Mul, out, f))?;
    }
    Ok(out)
}

/// `a·x + a·y + …` written as `a·(x + y + …)`, including where products group more factors.
/// The commit rule keeps the rewrite only when it shrinks the live DAG. Factoring the whole
/// bounded sum avoids rejecting an intermediate pair when its product is shared elsewhere.
fn factor_sum(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Option<Step>, Stop> {
    let Some(sum) = sum(cx, n) else {
        return Ok(None);
    };
    if sum.len < 2 {
        return Ok(None);
    }
    let mut products = [Product {
        factors: [0; MAX_PRODUCT_FACTORS],
        len: 0,
    }; MAX_SUM_TERMS];
    for (slot, &term) in products.iter_mut().zip(&sum.terms[..sum.len]) {
        let Some(p) = product(cx, term) else {
            return Ok(None);
        };
        *slot = p;
    }
    let products = &products[..sum.len];
    if let Some(step @ Step::To(..)) = complementary_products(r, cx, n, products)? {
        return Ok(Some(step));
    }
    let Some((factor, positions)) = common_factor(cx, products) else {
        return Ok(None);
    };
    let before = cx.len() as u32;
    let mut rest = None;
    for (i, p) in products.iter().enumerate() {
        let q = without_factor(r, cx, p, positions[i])?;
        rest = Some(match rest {
            None => q,
            Some(a) => r.build(cx, |cx| cx.c_bin(BinOp::Add, a, q))?,
        });
    }
    let Some(rest) = rest else {
        return Ok(None);
    };
    let factored = r.build(cx, |cx| cx.c_bin(BinOp::Mul, factor, rest))?;
    let mut atoms = [0; MAX_PRODUCT_FACTORS * MAX_SUM_TERMS];
    let mut count = 0;
    for p in products {
        for a in &p.factors[..p.len] {
            if !atoms[..count].contains(a) {
                atoms[count] = *a;
                count += 1;
            }
        }
    }
    Ok(Some(finish(
        r,
        cx,
        PassKind::Linear,
        n,
        factored,
        before,
        &atoms[..count],
        Fin::FINAL,
    )?))
}

/// The linear pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let op = cx.node(n).op;
    if let Some(step @ Step::To(..)) = factor_sum(r, cx, n)? {
        return Ok(step);
    }
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
    // Terms reading one condition, merged first (see `conditions`).
    let merged = match super::conditions::step(r, cx, n, &form)? {
        Ok(s) => return Ok(s),
        Err(f) => f,
    };
    Ok(match plain(r, cx, n, form)? {
        Step::Normal(f) => Step::Normal(f.and(merged)),
        s => s,
    })
}

/// The linear pass at `n` over its form as computed.
fn plain(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32, form: Form) -> Result<Step, Stop> {
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

/// the sum `n` taken apart into groups of terms whose bitwise parts share no
/// atom (the operands of `& | ^` that are not themselves bitwise), each group with several
/// terms simplified alone by `part` (the MBA phase), and the sum built again from the results;
/// `None` when the sum has one group or no group changes. An identity hidden in a sum beside
/// other terms (`(z | k) − (z & k) − (z ^ k)`, nothing, next to a polynomial in `x` and `y`;
/// `(t ^ k) + 2 (t & k)`, which is `t + k`, of a sum `t`) is then decided on its own atoms.
#[cfg(feature = "mba")]
pub(super) fn by_groups(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    part: &mut impl FnMut(&mut Runner<'_, '_>, &mut Context, u32) -> Result<Option<u32>, Stop>,
) -> Result<Option<Step>, Stop> {
    if !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) {
        return Ok(None);
    }
    let form = form_of(r, cx, n)?;
    if form.terms.len() < 3 {
        return Ok(None);
    }
    let mut sets = Vec::with_capacity(form.terms.len());
    for &(a, _) in &form.terms {
        match bitwise_atoms(cx, a) {
            Some(s) => sets.push(s),
            None => return Ok(None),
        }
    }
    fn find(up: &mut [usize], mut i: usize) -> usize {
        while up[i] != i {
            up[i] = up[up[i]];
            i = up[i];
        }
        i
    }
    let k = sets.len();
    let mut up: Vec<usize> = (0..k).collect();
    for i in 0..k {
        for j in i + 1..k {
            if sets[i].iter().any(|l| sets[j].binary_search(l).is_ok()) {
                let (a, b) = (find(&mut up, i), find(&mut up, j));
                up[a.max(b)] = a.min(b);
            }
        }
    }
    let mut groups: std::collections::BTreeMap<usize, Vec<usize>> = Default::default();
    for i in 0..k {
        let g = find(&mut up, i);
        groups.entry(g).or_default().push(i);
    }
    if groups.len() < 2 || groups.values().all(|g| g.len() < 2) {
        return Ok(None);
    }
    let w = form.konst.width();
    let before = cx.len() as u32;
    let mut total = Form::of(form.konst, &[]);
    let mut fin = form.fin;
    let mut changed = false;
    for idx in groups.values() {
        let terms: Vec<(u32, BitVec)> = idx.iter().map(|&i| form.terms[i]).collect();
        let mut f = Form::of(BitVec::zero(w), &terms);
        if idx.len() >= 2 {
            let s = emit(r, cx, &f)?;
            if let Some(e) = part(r, cx, s)?
                && e != s
            {
                f = form_of(r, cx, e)?;
                fin = fin.and(f.fin);
                changed = true;
            }
        }
        total = total.add(&f);
    }
    if !changed {
        super::discard(r, cx, before);
        return Ok(None);
    }
    let e = emit(r, cx, &total)?;
    // The nodes from before the rewrite that it reads.
    let mut stops = Vec::new();
    let mut seen = crate::hash::IdMap::<u32, ()>::default();
    let mut todo = vec![e];
    while let Some(i) = todo.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if i < before {
            stops.push(i);
        } else {
            todo.extend(cx.node(i).children());
        }
    }
    finish(r, cx, PassKind::Mba, n, e, before, &stops, fin).map(Some)
}

/// The atoms of `e`'s bitwise part, sorted: the operands under its `& | ^ ~` that are not
/// themselves bitwise (constants aside), or `e` itself when it is not bitwise; `None` past a
/// few hundred nodes.
#[cfg(feature = "mba")]
fn bitwise_atoms(cx: &Context, e: u32) -> Option<Vec<u32>> {
    const MAX_SEEN: usize = 512;
    let bitwise = |op: OpCode| matches!(op, OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not);
    if !bitwise(cx.node(e).op) {
        return Some(vec![e]);
    }
    let mut seen = crate::hash::IdMap::<u32, ()>::default();
    let mut out = Vec::new();
    let mut todo = vec![e];
    while let Some(i) = todo.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if seen.len() > MAX_SEEN {
            return None;
        }
        let node = cx.node(i);
        if bitwise(node.op) {
            todo.extend(node.children());
        } else if node.op != OpCode::Const {
            out.push(i);
        }
    }
    out.sort_unstable();
    out.dedup();
    Some(out)
}

/// the sum `n` with terms that spell a sum `A` its bitwise parts read as an atom
/// (`2 (A & k) − x·x − y` where `A = x·x + y`) written as `A` itself, then simplified by `part`
/// (the MBA phase): an atom and its expansion are otherwise unrelated to the solver. `None`
/// when no such sum is spelled out.
#[cfg(feature = "mba")]
pub(super) fn by_sums(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    part: &mut impl FnMut(&mut Runner<'_, '_>, &mut Context, u32) -> Result<Option<u32>, Stop>,
) -> Result<Option<Step>, Stop> {
    if !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) {
        return Ok(None);
    }
    let form = form_of(r, cx, n)?;
    let mut sums: Vec<u32> = Vec::new();
    for &(t, _) in &form.terms {
        if !matches!(cx.node(t).op, OpCode::And | OpCode::Or | OpCode::Xor) {
            continue;
        }
        for a in bitwise_atoms(cx, t).unwrap_or_default() {
            if matches!(cx.node(a).op, OpCode::Add | OpCode::Sub) && !sums.contains(&a) {
                sums.push(a);
            }
        }
    }
    let w = form.konst.width();
    let one = BitVec::one(w);
    let minus_one = BitVec::ones(w);
    let mut konst = form.konst;
    let mut terms = form.terms.clone();
    let mut changed = false;
    for a in sums {
        let fa = form_of(r, cx, a)?;
        if fa.terms.len() < 2 || fa.terms.iter().any(|(_, k)| *k != one && *k != minus_one) {
            continue;
        }
        let coeff = |terms: &[(u32, BitVec)], atom: u32| {
            terms
                .binary_search_by_key(&atom, |t| t.0)
                .ok()
                .map(|i| terms[i].1)
        };
        // The scale `c` with `c · fa`'s terms among the sum's.
        let (t0, k0) = fa.terms[0];
        let Some(c0) = coeff(&terms, t0) else {
            continue;
        };
        let c = if k0 == one {
            c0
        } else {
            BitVec::un_unchecked(UnOp::Neg, &c0)
        };
        let scaled = |k: &BitVec| BitVec::bin_unchecked(BinOp::Mul, &c, k);
        if !fa
            .terms
            .iter()
            .all(|(t, k)| coeff(&terms, *t) == Some(scaled(k)))
        {
            continue;
        }
        // `c·Σ` is `c·A − c·kA`.
        let mut rest: Vec<(u32, BitVec)> = terms
            .iter()
            .filter(|(t, _)| fa.terms.binary_search_by_key(t, |x| x.0).is_err())
            .copied()
            .collect();
        rest.push((a, c));
        konst = BitVec::bin_unchecked(BinOp::Sub, &konst, &scaled(&fa.konst));
        let f = Form::of(konst, &rest);
        terms = f.terms.clone();
        konst = f.konst;
        changed = true;
    }
    if !changed {
        return Ok(None);
    }
    let before = cx.len() as u32;
    let s = emit(r, cx, &Form::of(konst, &terms))?;
    let e = part(r, cx, s)?.unwrap_or(s);
    let mut stops = Vec::new();
    let mut seen = crate::hash::IdMap::<u32, ()>::default();
    let mut todo = vec![e];
    while let Some(i) = todo.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if i < before {
            stops.push(i);
        } else {
            todo.extend(cx.node(i).children());
        }
    }
    finish(r, cx, PassKind::Mba, n, e, before, &stops, form.fin).map(Some)
}
