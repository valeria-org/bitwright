//! The linear pass: `c + Σ kᵢ·aᵢ` over Z/2^W.
//!
//! A node's *form* is computed from its operands' forms: `+`, `−`, negation, `~a = −a − 1`,
//! multiplication by a constant, shifts left by a constant (scaling), `|`/`^` of operands the
//! facts prove disjoint (both are `+` then), `^` of operands one of which the facts prove to
//! have bits only where the other has them (a `−` then). Anything else is an *atom* with
//! coefficient 1.
//! Terms that read one value two ways are moved to one reading where the sum has both, so
//! they cancel ([`merge`]): `sext(c)` beside `zext(c)` of a 1-bit `c` is `−zext(c)`, an
//! extension of `~t` beside that of `t` is a constant less it, and `2^j·(x >>u j)` beside the
//! low field `x & (2^j − 1)` is `x` less that field.
//!
//! A form with more than [`MAX_TERMS`] terms is atomized: its node is an atom of the forms
//! over it, which keeps every form small. Such a sum keeps its *whole* form
//! ([`Whole`](super::forms::Whole), up to 1024 terms), and a sum in which a term meets one
//! inside it is taken apart ([`sum_of`]), so terms cancel through sums of that length:
//! `(v0 + … + v99) − v0` is the other 99 terms.
//!
//! The form is re-emitted canonically (terms in the context's canonical order, positive
//! coefficients first, power-of-two coefficients as shifts, the constant last), and the
//! emission replaces the node only when the region above the atoms gets strictly smaller.
//!
//! Around the forms: a sum of products with a common factor is factored ([`factor_sum`]),
//! terms that count bits of one value are one population count ([`bit_count`]), and a
//! product of three or more values is written with its factors in the context's order
//! ([`sort_chain`](super::sort_chain)), so two writings of one product are one atom.

use super::{Fin, PassKind, Runner, Step, Stop, disjoint, finish, within, worth_building};
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

impl Form {
    /// The constant and the terms (atom, coefficient).
    pub(crate) fn konst_terms(&self) -> (&BitVec, &[(u32, BitVec)]) {
        (&self.konst, &self.terms)
    }
}

impl super::forms::Parts for Form {
    fn parts(&self) -> (&BitVec, &[(u32, BitVec)], Fin) {
        (&self.konst, &self.terms, self.fin)
    }

    fn from_parts(konst: BitVec, terms: Vec<(u32, BitVec)>, fin: Fin) -> Form {
        Form { konst, terms, fin }
    }
}

impl super::forms::Sum for Form {
    fn join(a: &BitVec, b: &BitVec) -> BitVec {
        BitVec::bin_unchecked(BinOp::Add, a, b)
    }

    fn scale(outer: &BitVec, inner: &BitVec) -> BitVec {
        BitVec::bin_unchecked(BinOp::Mul, outer, inner)
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

    pub(super) fn scale(&self, k: &BitVec) -> Form {
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

    pub(super) fn add(&self, o: &Form) -> Form {
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

    pub(super) fn neg(&self) -> Form {
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
    let scaled = terms
        .iter()
        .filter(|(_, k, _)| *k != one && BitVec::un_unchecked(UnOp::Neg, k) != one)
        .count() as u32;
    let nots = terms.iter().filter(|(_, _, not)| *not).count() as u32;
    let minus_one = BitVec::ones(w);
    // With no positive term and no constant, a negation only when every coefficient is −1.
    let negation = t > 0 && terms.iter().all(|(_, k, _)| *k == minus_one);
    let konst = match (t, konst.is_zero()) {
        (0, _) => 1,
        (_, true) => u32::from(negation),
        _ => 2,
    };
    2 * scaled + t.saturating_sub(1) + nots + konst + u32::from(plan.not)
}

/// What [`emit`] writes for `form`, terms in the given order: the cheapest of trading the
/// constant for complements (ties to the plain sum). The first term whose coefficient equals
/// the constant takes it in, `k·a + k = (−k)·~a`, when the constant is negative (`−x − 1` is
/// `~x`) or a power of two from 2 (`2·y + 2` is `~y·−2`, where the shift's amount would be a
/// second constant); a constant 1 goes into a term of coefficient 1 beside another term
/// (`a + t + 1` is `a − ~t`) or splits one of coefficient 2 (`2·t + 1` is `t − ~t`); and a
/// constant −1 complements the negated rest (`−1 − 2·x` is `~(x << 1)`).
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
pub(in crate::engine) fn form_of(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
) -> Result<Form, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.linear.cache.contains(i) {
            continue;
        }
        let node = cx.node(i);
        if !linear_op(node.op) {
            r.linear.cache.insert(i, Form::atom(i, cx.width_of(i)));
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if !r.linear.cache.contains(c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        let (f, met) = compute(r, cx, i)?;
        if f.terms.len() <= MAX_TERMS {
            r.linear.cache.insert(i, f);
            continue;
        }
        // Over the cap: an atom, which keeps its whole form for the sums over it.
        r.stats.passes.entry("linear").or_default().atomized += 1;
        let atom = Form {
            fin: f.fin,
            ..Form::atom(i, cx.width_of(i))
        };
        r.linear.cache.insert(i, atom);
        let mut read = 0;
        r.linear.whole.keep(i, f, met, &mut read);
        r.meter.charge(Counter::PassWork, read / MAX_TERMS as u64)?;
    }
    Ok(r.linear
        .cache
        .get(root)
        .expect("the root's form was just computed"))
}

/// Low `bits` of `x`, when fixed, including any reliance on scoped facts.
fn fixed_low(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    bits: u16,
) -> Result<Option<(BitVec, Fin)>, Stop> {
    let (facts, fin) = super::known(r, cx, x)?;
    let Some(facts) = facts else { return Ok(None) };
    let mask = crate::facts::known::low_mask(cx.width_of(x), u32::from(bits));
    Ok((crate::facts::known::bv_and(&facts.known(), &mask) == mask)
        .then(|| (crate::facts::known::bv_and(&facts.known_one(), &mask), fin)))
}

/// Scaling a right shift by a multiple of 2^j discards the same wrapped
/// bits as scaling a right rotation. Both are `(k >> j) * (x - low_j(x))`.
fn scaled_high(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    atom: u32,
    k: &BitVec,
) -> Result<Option<Form>, Stop> {
    use crate::facts::known::{bv_lshr, trailing_zeros};
    let n = cx.node(atom);
    let w = u64::from(n.width);
    let (x, shift) = match n.op {
        OpCode::RotL | OpCode::RotR | OpCode::LShr => {
            let Some(j) = cx.const_val(n.b).and_then(|x| x.to_u64()) else {
                return Ok(None);
            };
            let shift = match n.op {
                OpCode::RotL => (w - j % w) % w,
                OpCode::RotR => j % w,
                _ => j,
            };
            (n.a, shift)
        }
        OpCode::Zext => {
            let field = cx.node(n.a);
            if field.op != OpCode::Extract || cx.wid(field.a) != n.width
                || field.b + u32::from(field.width) != u32::from(n.width)
            {
                return Ok(None);
            }
            (field.a, u64::from(field.b))
        }
        _ => return Ok(None),
    };
    if shift == 0 || shift >= w || k.is_zero() || shift > u64::from(trailing_zeros(k)) {
        return Ok(None);
    }
    let Some((lo, fin)) = fixed_low(r, cx, x, shift as u16)? else {
        return Ok(None);
    };
    let q = bv_lshr(k, shift as u32);
    let bias = BitVec::un_unchecked(UnOp::Neg, &BitVec::bin_unchecked(BinOp::Mul, &lo, &q));
    Ok(Some(Form { konst: bias, terms: vec![(x, q)], fin }))
}

/// In `concat(h + Σ c_i·high(x_i), low)`, the implicit left shift cancels
/// each extraction. Narrow additions and products may wrap: that wrap
/// becomes a multiple of 2^W in the result.
fn aligned_concat(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    mut hi: Form,
    low: &BitVec,
    w: crate::Width,
) -> Result<Option<Form>, Stop> {
    let j = low.width().bits();
    if hi.terms.is_empty() || hi.terms.iter().any(|&(i, _)| {
        let n = cx.node(i);
        n.op != OpCode::Extract || n.b != u32::from(j) || cx.width_of(n.a) != w
    }) {
        return Ok(None);
    }
    hi.konst = BitVec::concat(&hi.konst, low).expect("original concat width");
    for (atom, coeff) in &mut hi.terms {
        let x = cx.node(*atom).a;
        let Some((lo, fin)) = fixed_low(r, cx, x, j)? else {
            return Ok(None);
        };
        hi.fin = hi.fin.and(fin);
        *atom = x;
        *coeff = coeff.sext(w).expect("wider concat");
        let correction = BitVec::bin_unchecked(BinOp::Mul, &lo, coeff);
        hi.konst = BitVec::bin_unchecked(BinOp::Sub, &hi.konst, &correction);
    }
    // Different high fields with the same width and offset have different
    // sources (the context interns extracts). Only the ordering changes.
    hi.terms.sort_unstable_by_key(|t| t.0);
    Ok(Some(hi))
}

/// The form of `i` from its operands' (cached) forms, and whether terms met in it (see
/// [`sum_of`]).
fn compute(r: &mut Runner<'_, '_>, cx: &mut Context, i: u32) -> Result<(Form, bool), Stop> {
    let node = cx.node(i);
    let w = cx.width_of(i);
    let get = |r: &Runner<'_, '_>, j: u32| {
        r.linear
            .cache
            .get(j)
            .expect("operands' forms are computed first")
    };
    let form = match node.op {
        OpCode::Const => Form {
            konst: cx.const_val(i).unwrap_or(BitVec::zero(w)),
            terms: Vec::new(),
            fin: Fin::FINAL,
        },
        OpCode::Add => return sum_of(r, cx, &get(r, node.a), &get(r, node.b)),
        OpCode::Sub => return sum_of(r, cx, &get(r, node.a), &get(r, node.b).neg()),
        OpCode::Neg => get(r, node.a).neg(),
        OpCode::Not => {
            let mut f = get(r, node.a).neg();
            f.konst = BitVec::bin_unchecked(BinOp::Sub, &f.konst, &BitVec::one(w));
            f
        }
        OpCode::Mul => match (cx.const_val(node.a), cx.const_val(node.b)) {
            (Some(k), _) => {
                let f = scaled_high(r, cx, node.b, &k)?.unwrap_or_else(|| get(r, node.b).scale(&k));
                strip_annihilated_terms(r, cx, i, f)?
            }
            (_, Some(k)) => {
                let f = scaled_high(r, cx, node.a, &k)?.unwrap_or_else(|| get(r, node.a).scale(&k));
                strip_annihilated_terms(r, cx, i, f)?
            }
            _ => Form::atom(i, w),
        },
        OpCode::Shl => match cx.const_val(node.b) {
            Some(k) => {
                let one = BitVec::one(w);
                // A count of W or more gives 0, and so does the scaling (2^k mod 2^W).
                let scale = BitVec::bin_unchecked(BinOp::Shl, &one, &k);
                scaled_high(r, cx, node.a, &scale)?.unwrap_or_else(|| get(r, node.a).scale(&scale))
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
                Some(c) => aligned_concat(r, cx, get(r, node.a), &c, w)?.unwrap_or_else(|| Form::atom(i, w)),
                _ => Form::atom(i, w),
            }
        }
        OpCode::Or | OpCode::Xor => {
            if node.op == OpCode::Xor && w.bits() > 1 {
                let smin = BitVec::smin(w);
                if cx.const_val(node.a) == Some(smin) || cx.const_val(node.b) == Some(smin) {
                    let (f, met) = sum_of(r, cx, &get(r, node.a), &get(r, node.b))?;
                    return Ok((f, met));
                }
            }
            let (disjoint, fina, finb) = disjoint(r, cx, node.a, node.b)?;
            if disjoint {
                // The sum relies on what proved the operands disjoint.
                let (mut f, met) = sum_of(r, cx, &get(r, node.a), &get(r, node.b))?;
                f.fin = f.fin.and(fina).and(finb);
                return Ok((f, met));
            }
            // Constant OR / XOR over bits whose values are completely known in the variable
            // operand (`(c & !known(x)) == 0`, or `((~c) & !known(x)) == 0` for XOR):
            // - `x | c == x + (c & kz_x)`
            // - `x ^ c == x + (c & kz_x) - (c & ko_x)`
            // - `x ^ c == (~x) ^ (~c) == (-1 + (~c & ko_x) - (~c & kz_x)) - x`
            let const_pair = match (cx.const_val(node.a), cx.const_val(node.b)) {
                (None, Some(c)) => Some((node.a, c)),
                (Some(c), None) => Some((node.b, c)),
                _ => None,
            };
            if let Some((x_id, c_bv)) = const_pair {
                let (kb_opt, xfin) = super::known(r, cx, x_id)?;
                if let Some(kb) = kb_opt {
                    let unk = kb.unknown_mask();
                    let kz = kb.known_zero();
                    let ko = kb.known_one();
                    if crate::facts::known::bv_and(&c_bv, &unk).is_zero() {
                        let add_part = crate::facts::known::bv_and(&c_bv, &kz);
                        let delta = if node.op == OpCode::Or {
                            add_part
                        } else {
                            let sub_part = crate::facts::known::bv_and(&c_bv, &ko);
                            BitVec::bin_unchecked(BinOp::Sub, &add_part, &sub_part)
                        };
                        let c_form = Form {
                            konst: delta,
                            terms: Vec::new(),
                            fin: xfin,
                        };
                        let (mut f, met) = sum_of(r, cx, &get(r, x_id), &c_form)?;
                        f.fin = f.fin.and(xfin);
                        return Ok((f, met));
                    }
                    if node.op == OpCode::Xor {
                        let nc = crate::facts::known::bv_not(&c_bv);
                        if crate::facts::known::bv_and(&nc, &unk).is_zero() {
                            let add_part = crate::facts::known::bv_and(&nc, &ko);
                            let sub_part = crate::facts::known::bv_and(&nc, &kz);
                            let bias = BitVec::bin_unchecked(
                                BinOp::Sub,
                                &BitVec::bin_unchecked(BinOp::Add, &BitVec::ones(w), &add_part),
                                &sub_part,
                            );
                            let c_form = Form {
                                konst: bias,
                                terms: Vec::new(),
                                fin: xfin,
                            };
                            let (mut f, met) = sum_of(r, cx, &c_form, &get(r, x_id).neg())?;
                            f.fin = f.fin.and(xfin);
                            return Ok((f, met));
                        }
                    }
                }
            }
            // A xor that only clears bits its other operand has set is their difference
            // (`c ^ t` with `t ⊆ c` is `c − t`: no borrow), so a sum cancels through it as it
            // does through the subtraction the rules write that way (`sub_within`).
            if node.op == OpCode::Xor {
                for (whole, part) in [(node.a, node.b), (node.b, node.a)] {
                    let (inside, finw, finp) = within(r, cx, whole, part)?;
                    if inside {
                        let (mut f, met) = sum_of(r, cx, &get(r, whole), &get(r, part).neg())?;
                        f.fin = f.fin.and(finw).and(finp);
                        return Ok((f, met));
                    }
                }
            }
            Form {
                fin: fina.and(finb).unchanged(),
                ..Form::atom(i, w)
            }
        }
        _ => Form::atom(i, w),
    };
    Ok((form, false))
}

/// Drop scaled linear terms `(atom, coef)` whose 2-adic valuation `ctz(coef) + ctz(atom) >= W`
/// makes `coef * atom ≡ 0 (mod 2^W)` for every input.
fn strip_annihilated_terms(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    owner: u32,
    mut f: Form,
) -> Result<Form, Stop> {
    if f.terms.is_empty() || !r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(owner))) {
        return Ok(f);
    }
    let wb = u32::from(f.konst.width().bits());
    let mut kept = Vec::with_capacity(f.terms.len());
    for &(atom, ref coef) in &f.terms {
        let tz_c = crate::facts::known::trailing_zeros(coef);
        if tz_c == 0 {
            kept.push((atom, *coef));
            continue;
        }
        let (kb_opt, kfin) = super::known(r, cx, atom)?;
        let tz_a = kb_opt.map_or(0, |kb| kb.trailing_known_zeros());
        if tz_c.saturating_add(tz_a) >= wb {
            f.fin = f.fin.and(kfin);
        } else {
            f.fin = f.fin.and(kfin.unchanged());
            kept.push((atom, *coef));
        }
    }
    f.terms = kept;
    Ok(f)
}

/// The sum of the forms `a` and `b` of a node's operands, and whether terms met in it: two
/// terms of one atom, in the forms themselves or out of sight, one of them inside a sum over
/// [`MAX_TERMS`] that is an atom here (see [`Whole`](super::forms::Whole)). Those sums are
/// then taken apart, so the terms cancel: `(v0 + … + v99) − v0` is the other 99 terms.
fn sum_of(r: &mut Runner<'_, '_>, cx: &Context, a: &Form, b: &Form) -> Result<(Form, bool), Stop> {
    let f = merge_masks(r, cx, merge(cx, a.add(b)));
    let met = f.terms.len() < a.terms.len() + b.terms.len();
    let mut read = 0;
    let whole = r.linear.whole.meeting(a, b, &f, &mut read);
    r.meter.charge(Counter::PassWork, read / MAX_TERMS as u64)?;
    Ok(match whole {
        // (`merge_fields` reads every term for each shifted one: within the cap only.)
        Some(whole) if whole.terms.len() <= MAX_TERMS => (merge(cx, whole), true),
        Some(whole) => (whole, true),
        None => (f, met),
    })
}

/// `form` with the terms that read one value two ways moved to one reading, so they cancel.
fn merge(cx: &Context, form: Form) -> Form {
    merge_fields(cx, merge_complements(cx, merge_signs(cx, form)))
}

/// `form` with each term `k·2^j·(x >>u j)` moved to `k·x − k·(x & (2^j − 1))` when the form
/// has that low field of `x` as a term too: `(x >>u 3)·24 + (x & 7)·3` is `x·3`. Only then, as
/// [`merge_signs`].
fn merge_fields(cx: &Context, form: Form) -> Form {
    let w = form.konst.width();
    let mut moves = Vec::new();
    for &(a, k) in &form.terms {
        let n = cx.node(a);
        if n.op != OpCode::LShr {
            continue;
        }
        let Some(j) = cx.const_val(n.b).and_then(|j| j.to_u64()) else {
            continue;
        };
        if j == 0 || j >= u64::from(w.bits()) {
            continue;
        }
        let j = j as u32;
        let q = crate::facts::known::bv_lshr(&k, j);
        if crate::facts::known::bv_shl(&q, j) != k {
            continue;
        }
        let mask = crate::facts::known::low_mask(w, j);
        let low = form.terms.iter().map(|t| t.0).find(|&t| {
            let m = cx.node(t);
            m.op == OpCode::And && m.a == n.a && cx.const_val(m.b) == Some(mask)
        });
        if let Some(low) = low {
            moves.push((a, k, n.a, low, q));
        }
    }
    if moves.is_empty() {
        return form;
    }
    let fin = form.fin;
    let mut f = form;
    for (a, k, x, low, q) in moves {
        let neg = |v: &BitVec| BitVec::un_unchecked(UnOp::Neg, v);
        f = f.add(&Form::of(
            BitVec::zero(w),
            &[(a, neg(&k)), (x, q), (low, neg(&q))],
        ));
    }
    f.fin = fin;
    f
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
        if n.op == OpCode::Xor
            && let Some((base, c_id)) = with_const(cx, a)
            && let Some(cv) = cx.const_val(c_id)
            && cv.msb()
        {
            let pos_c = crate::facts::known::bv_not(&cv);
            if let Some(&(z, _)) = form.terms.iter().find(|&&(z, _)| {
                z != a
                    && cx.node(z).op == OpCode::Xor
                    && with_const(cx, z)
                        .is_some_and(|(zb, zc)| zb == base && cx.const_val(zc) == Some(pos_c))
            }) {
                moves.push((a, z, k, BitVec::ones(w)));
            }
            continue;
        }
        if !matches!(n.op, OpCode::Zext | OpCode::Sext) {
            continue;
        }
        let inner = cx.node(n.a);
        let z_match = if inner.op == OpCode::Not {
            cx.find(&Node::new(n.op, w.bits(), inner.a, 0, 0))
                .filter(|z| form.terms.binary_search_by_key(z, |t| t.0).is_ok())
        } else if inner.op == OpCode::Xor
            && let Some((base, c_id)) = with_const(cx, n.a)
            && let Some(cv) = cx.const_val(c_id)
            && cv.msb()
        {
            let pos_c = crate::facts::known::bv_not(&cv);
            form.terms
                .iter()
                .map(|&(z, _)| z)
                .find(|&z| {
                    let zn = cx.node(z);
                    z != a
                        && zn.op == n.op
                        && cx.node(zn.a).op == OpCode::Xor
                        && with_const(cx, zn.a)
                            .is_some_and(|(zb, zc)| zb == base && cx.const_val(zc) == Some(pos_c))
                })
        } else {
            None
        };
        if let Some(z) = z_match {
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

/// `a` and the constant node `c` when `i` is `a op c`.
fn with_const(cx: &Context, i: u32) -> Option<(u32, u32)> {
    let n = cx.node(i);
    match (cx.is_const(n.a), cx.is_const(n.b)) {
        (false, true) => Some((n.a, n.b)),
        (true, false) => Some((n.b, n.a)),
        _ => None,
    }
}

/// `form` with each term `k·(a ^ c)` and `k·(a | c)`, `c` a constant, written over `a & c`
/// when the form has that as a term too and gets no more terms by it: bit by bit `a ^ c` is
/// `a + c − 2·(a & c)` and `a | c` is `a + c − (a & c)`, so `(a ^ c) + 2·(a & c)` is `a + c`,
/// and a sum that spells an XOR with a constant (`x + y + c − 2·(x & c)`) meets the XOR
/// itself. Only then, as [`merge_signs`]: the conjunction found in the arena is a term of the
/// form, so the reading does not depend on what else was built.
fn merge_masks(r: &Runner<'_, '_>, cx: &Context, form: Form) -> Form {
    let w = form.konst.width();
    let mut f = form;
    // One term at a time, the first in the canonical order that the form allows (the result
    // does not depend on node indices); each takes an XOR or an OR out of the form and puts
    // in terms from below it only, so this ends.
    loop {
        let mut masks: Vec<(u32, BitVec)> = f
            .terms
            .iter()
            .filter(|t| matches!(cx.node(t.0).op, OpCode::Xor | OpCode::Or))
            .copied()
            .collect();
        if masks.is_empty() {
            return f;
        }
        masks.sort_by(|a, b| cx.order(a.0, b.0));
        let mut moved = None;
        for (t, k) in masks {
            let Some((a, c)) = with_const(cx, t) else {
                continue;
            };
            let and = |x: u32, y: u32| cx.find(&Node::new(OpCode::And, w.bits(), x, y, 0));
            let Some(m) = and(a, c).or_else(|| and(c, a)) else {
                continue;
            };
            if f.terms.binary_search_by_key(&m, |t| t.0).is_err() {
                continue;
            }
            let (Some(fa), Some(cv)) = (r.linear.cache.get(a), cx.const_val(c)) else {
                continue;
            };
            // `k·(a ^ c)` is `k·a + k·c − 2k·(a & c)`; `k·(a | c)` is `k·a + k·c − k·(a & c)`.
            let minus_k = BitVec::un_unchecked(UnOp::Neg, &k);
            let km = if cx.node(t).op == OpCode::Xor {
                BitVec::bin_unchecked(BinOp::Add, &minus_k, &minus_k)
            } else {
                minus_k
            };
            let kc = BitVec::bin_unchecked(BinOp::Mul, &k, &cv);
            let g = f
                .add(&Form::of(kc, &[(t, minus_k), (m, km)]))
                .add(&fa.scale(&k));
            if g.terms.len() <= f.terms.len() {
                moved = Some(g);
                break;
            }
        }
        match moved {
            Some(g) => f = g,
            None => return f,
        }
    }
}

/// `form` with a term `k·(a ^ c)` or `k·(a | c)`, `c` a constant, written over `a & c` (see
/// [`merge_masks`]) where that leaves it fewer terms, the conjunction built if it is not
/// there: `(a + c) − (a ^ c)` is `2·(a & c)`. For a form that is a question of its own (the
/// difference of a carry's sides), not for the form of a node: what is built does not enter
/// any other reading. `None` when no term is taken.
#[cfg(feature = "prove")]
pub(super) fn unmasked(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    form: &Form,
) -> Result<Option<Form>, Stop> {
    let mut f = form.clone();
    let mut any = false;
    // One term at a time, the first in the canonical order that the form allows; each takes
    // an XOR or an OR out and leaves fewer terms, so this ends.
    loop {
        let mut masks: Vec<(u32, BitVec)> = f
            .terms
            .iter()
            .filter(|t| matches!(cx.node(t.0).op, OpCode::Xor | OpCode::Or))
            .copied()
            .collect();
        masks.sort_by(|a, b| cx.order(a.0, b.0));
        let mut moved = None;
        for (t, k) in masks {
            let Some((a, c)) = with_const(cx, t) else {
                continue;
            };
            let Some(cv) = cx.const_val(c) else {
                continue;
            };
            let xor = cx.node(t).op == OpCode::Xor;
            let m = r.build(cx, |cx| cx.c_bin(BinOp::And, a, c))?;
            let (fa, fm) = (form_of(r, cx, a)?, form_of(r, cx, m)?);
            r.meter.charge(
                Counter::PassWork,
                (fa.terms.len() + fm.terms.len()) as u64 + 1,
            )?;
            // `k·(a ^ c)` is `k·a + k·c − 2k·(a & c)`; `k·(a | c)` is `k·a + k·c − k·(a & c)`.
            let minus_k = BitVec::un_unchecked(UnOp::Neg, &k);
            let km = if xor {
                BitVec::bin_unchecked(BinOp::Add, &minus_k, &minus_k)
            } else {
                minus_k
            };
            let kc = BitVec::bin_unchecked(BinOp::Mul, &k, &cv);
            let g = f
                .add(&Form::of(kc, &[(t, minus_k)]))
                .add(&fm.scale(&km))
                .add(&fa.scale(&k));
            if g.terms.len() < f.terms.len() {
                moved = Some(g);
                break;
            }
        }
        match moved {
            Some(g) => {
                f = g;
                any = true;
            }
            None => return Ok(any.then_some(f)),
        }
    }
}

/// `form` with its terms that spell an XOR or an OR with a constant written as that: for a
/// term `q·(a & c)`, `c` a constant, the form is `rest + k·(a ^ c)` with `k = −q/2` (either
/// half), and `rest + k·(a | c)` with `k = −q` (see [`merge_masks`]), and is written so where
/// that leaves it fewer terms (the terms of `a` cancel). With the nodes the commit rule's
/// region stops at; `None` when nothing is spelled so.
fn masked(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    form: &Form,
) -> Result<Option<(Form, Vec<u32>)>, Stop> {
    let w = form.konst.width();
    let mut ands: Vec<u32> = form
        .terms
        .iter()
        .map(|t| t.0)
        .filter(|&t| cx.node(t).op == OpCode::And && with_const(cx, t).is_some())
        .collect();
    if ands.is_empty() {
        return Ok(None);
    }
    ands.sort_by(|a, b| cx.order(*a, *b));
    let mut f = form.clone();
    let mut leaves: Vec<u32> = Vec::new();
    let mut taken: Vec<u32> = Vec::new();
    // Collapse pairs of disjoint constant-mask terms on the same base `a` (`cv1 & cv2 == 0`):
    // - `k · (a & cv1) + k · (a & cv2) == k · (a & (cv1 | cv2))`
    // - `k · (a & cv1) - k · (a & cv2) == k · ((a & (cv1 | cv2)) ^ cv2) - k · cv2`
    for i in 0..ands.len() {
        let m1 = ands[i];
        let Ok(at1) = f.terms.binary_search_by_key(&m1, |t| t.0) else {
            continue;
        };
        let k1 = f.terms[at1].1;
        let Some((a1, c1_id)) = with_const(cx, m1) else {
            continue;
        };
        let Some(cv1) = cx.const_val(c1_id) else {
            continue;
        };
        for &m2 in &ands[i + 1..] {
            let Ok(at2) = f.terms.binary_search_by_key(&m2, |t| t.0) else {
                continue;
            };
            let k2 = f.terms[at2].1;
            let Some((a2, c2_id)) = with_const(cx, m2) else {
                continue;
            };
            if a1 != a2 {
                continue;
            }
            let Some(cv2) = cx.const_val(c2_id) else {
                continue;
            };
            if !crate::facts::known::bv_and(&cv1, &cv2).is_zero() {
                continue;
            }
            let same_sign = k1 == k2;
            let opp_sign = !same_sign && BitVec::bin_unchecked(BinOp::Add, &k1, &k2).is_zero();
            if !same_sign && !opp_sign {
                continue;
            }
            let cv_union = crate::facts::known::bv_or(&cv1, &cv2);
            let atom = r.build(cx, |cx| {
                let cu = cx.mk_const(&cv_union)?;
                let masked_u = cx.c_bin(BinOp::And, a1, cu)?;
                if same_sign {
                    Ok(masked_u)
                } else {
                    cx.c_bin(BinOp::Xor, masked_u, c2_id)
                }
            })?;
            let minus_k1 = BitVec::un_unchecked(UnOp::Neg, &k1);
            let minus_k2 = BitVec::un_unchecked(UnOp::Neg, &k2);
            let bias = if same_sign {
                BitVec::zero(w)
            } else {
                BitVec::bin_unchecked(BinOp::Mul, &minus_k1, &cv2)
            };
            f = f.add(&Form::of(
                bias,
                &[(m1, minus_k1), (m2, minus_k2), (atom, k1)],
            ));
            leaves.push(a1);
            taken.push(m1);
            taken.push(m2);
            break;
        }
    }
    for m in ands {
        let Ok(at) = f.terms.binary_search_by_key(&m, |t| t.0) else {
            continue;
        };
        let q = f.terms[at].1;
        let Some((a, c)) = with_const(cx, m) else {
            continue;
        };
        let Some(cv) = cx.const_val(c) else {
            continue;
        };
        let fa = form_of(r, cx, a)?;
        r.meter
            .charge(Counter::PassWork, fa.terms.len() as u64 + 1)?;
        let minus_q = BitVec::un_unchecked(UnOp::Neg, &q);
        let mut options = vec![(BinOp::Or, minus_q)];
        if q.bit(0) == Some(false) && w.bits() > 1 {
            let half = crate::facts::known::bv_lshr(&minus_q, 1);
            let top = crate::facts::known::bv_shl(&BitVec::one(w), u32::from(w.bits()) - 1);
            options.push((BinOp::Xor, half));
            options.push((BinOp::Xor, crate::facts::known::bv_or(&half, &top)));
        }
        let mut best: Option<(Form, BinOp, BitVec)> = None;
        for (op, k) in options {
            // `form − k·(a + c) − q·(a & c)`.
            let minus_k = BitVec::un_unchecked(UnOp::Neg, &k);
            let kc = BitVec::bin_unchecked(BinOp::Mul, &minus_k, &cv);
            let rest = f
                .add(&fa.scale(&minus_k))
                .add(&Form::of(kc, &[(m, minus_q)]));
            // (Only where the sum's constant is the one the identity gives it: `x − 2·(x &
            // c)` is `(x ^ c) − c`, the spelling of a sign extension, and a constant left
            // beside the XOR hides a wider one from the passes that read known bits.)
            if rest.konst.is_zero()
                && rest.terms.len() + 1 < f.terms.len()
                && best
                    .as_ref()
                    .is_none_or(|b| rest.terms.len() < b.0.terms.len())
            {
                best = Some((rest, op, k));
            }
        }
        let Some((rest, op, k)) = best else {
            continue;
        };
        let atom = r.build(cx, |cx| cx.c_bin(op, a, c))?;
        f = rest.add(&Form::of(BitVec::zero(w), &[(atom, k)]));
        leaves.push(a);
        taken.push(m);
    }
    if taken.is_empty() {
        return Ok(None);
    }
    leaves.extend(
        form.terms
            .iter()
            .map(|t| t.0)
            .filter(|t| !taken.contains(t)),
    );
    leaves.sort_unstable();
    leaves.dedup();
    Ok(Some((f, leaves)))
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

/// The leaves of the tree of `op` at `n`, left to right, when there are at most `N`. It reads
/// from the top and stops as soon as the nodes it holds must give more: a tree of `k` leaves
/// takes `2k − 1` steps and a larger one at most `2N`, however deep it is. (Read by recursion
/// to the bottom first, every node of a chain of 128 000 additions cost its depth, 29 s in
/// all, and one of 80 000 overflowed a 2 MiB stack.)
fn leaves<const N: usize>(cx: &Context, n: u32, op: OpCode) -> Option<([u32; N], usize)> {
    let mut out = [0; N];
    let mut len = 0;
    // The nodes still to read, the next one last. Each gives at least one leaf, so `len + top`
    // never passes `N`.
    let mut todo = [0; N];
    let mut top = 1;
    *todo.first_mut()? = n;
    while top > 0 {
        top -= 1;
        let i = todo[top];
        let node = cx.node(i);
        if node.op == op {
            if len + top + 2 > N {
                return None;
            }
            todo[top] = node.b;
            todo[top + 1] = node.a;
            top += 2;
        } else {
            out[len] = i;
            len += 1;
        }
    }
    Some((out, len))
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
    let (factors, len) = leaves(cx, n, OpCode::Mul)?;
    Some(Product { factors, len })
}

/// Additive terms of one sum, bounded for the same reason as [`Product`].
#[derive(Copy, Clone)]
struct Sum {
    terms: [u32; MAX_SUM_TERMS],
    len: usize,
}

const MAX_SUM_TERMS: usize = 16;

fn sum(cx: &Context, n: u32) -> Option<Sum> {
    let (terms, len) = leaves(cx, n, OpCode::Add)?;
    Some(Sum { terms, len })
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
    if !cx.are_bitwise_complements(a, b) {
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

/// A product rebuilt without one of its factors.
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
/// `None` when `n` is no such sum; a `Normal` step is what the candidates it declined
/// contribute.
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
    let declined = match complementary_products(r, cx, n, products)? {
        Some(Step::Normal(f)) => f,
        Some(step) => return Ok(Some(step)),
        None => Fin::FINAL,
    };
    let Some((factor, positions)) = common_factor(cx, products) else {
        return Ok(Some(Step::Normal(declined)));
    };
    let before = cx.len() as u32;
    let mut extra_atoms: Vec<u32> = Vec::new();
    let mut rest = None;
    for (i, p) in products.iter().enumerate() {
        let q = without_factor(r, cx, p, positions[i])?;
        rest = Some(match rest {
            None => q,
            Some(a) => {
                // Fold `(c1 ± y) + c2` directly so `(-2 - y) * x + x` simplifies to `~y * x`
                // instead of building an unsimplified `((-2 - y) + 1) * x`.
                let fold_const_sum = |cx: &mut Context,
                                      lhs: u32,
                                      c2: BitVec|
                 -> Result<Option<u32>, crate::Error> {
                    let ln = cx.node(lhs);
                    if ln.op == OpCode::Sub
                        && let Some(c1) = cx.const_val(ln.a)
                    {
                        let c = BitVec::bin_unchecked(BinOp::Add, &c1, &c2);
                        return Ok(Some(if c.is_zero() {
                            cx.c_un(UnOp::Neg, ln.b)?
                        } else if c.is_ones() {
                            cx.c_un(UnOp::Not, ln.b)?
                        } else {
                            let ck = cx.mk_const(&c)?;
                            cx.c_bin(BinOp::Sub, ck, ln.b)?
                        }));
                    }
                    if ln.op == OpCode::Add
                        && let Some(c1) = cx.const_val(ln.b)
                    {
                        let c = BitVec::bin_unchecked(BinOp::Add, &c1, &c2);
                        return Ok(Some(if c.is_zero() {
                            ln.a
                        } else {
                            let ck = cx.mk_const(&c)?;
                            cx.c_bin(BinOp::Add, ln.a, ck)?
                        }));
                    }
                    Ok(None)
                };
                let record_folded = |cx: &Context, id: u32, extra: &mut Vec<u32>| {
                    if id < before {
                        extra.push(id);
                    } else {
                        for c in cx.node(id).children() {
                            if c < before {
                                extra.push(c);
                            }
                        }
                    }
                };
                if let Some(cq) = cx.const_val(q) {
                    if let Some(folded) = r.build(cx, |cx| fold_const_sum(cx, a, cq))? {
                        record_folded(cx, folded, &mut extra_atoms);
                        folded
                    } else {
                        r.build(cx, |cx| cx.c_bin(BinOp::Add, a, q))?
                    }
                } else if let Some(ca) = cx.const_val(a) {
                    if let Some(folded) = r.build(cx, |cx| fold_const_sum(cx, q, ca))? {
                        record_folded(cx, folded, &mut extra_atoms);
                        folded
                    } else {
                        r.build(cx, |cx| cx.c_bin(BinOp::Add, a, q))?
                    }
                } else {
                    r.build(cx, |cx| cx.c_bin(BinOp::Add, a, q))?
                }
            }
        });
    }
    let Some(rest) = rest else {
        return Ok(Some(Step::Normal(declined)));
    };
    let factored = r.build(cx, |cx| cx.c_bin(BinOp::Mul, factor, rest))?;
    let mut atoms = [0; MAX_PRODUCT_FACTORS * MAX_SUM_TERMS + 8];
    let mut count = 0;
    for p in products {
        for a in &p.factors[..p.len] {
            if !atoms[..count].contains(a) {
                atoms[count] = *a;
                count += 1;
            }
        }
    }
    for a in extra_atoms {
        if a < before && count < atoms.len() && !atoms[..count].contains(&a) {
            atoms[count] = a;
            count += 1;
        }
    }
    Ok(Some(
        match finish(
            r,
            cx,
            PassKind::Linear,
            n,
            factored,
            before,
            &atoms[..count],
            Fin::FINAL,
        )? {
            Step::Normal(f) => Step::Normal(f.and(declined)),
            step => step,
        },
    ))
}

/// Evaluate the sum down matching arms of its selects. A shift inside an arm scales
/// its coefficient just as it would outside the select. Thus a select of `4*x` and
/// `4*y` cancels four times the select of `x` and `y`, even with nested choices or
/// pre-folded constant arms. Only walk choices already present in *every* remaining
/// term; never specialize an expression on an unrelated guard.
fn selected_constant(
    cx: &Context,
    terms: &[(u32, BitVec)],
    konst: BitVec,
    fuel: &mut u32,
) -> Option<BitVec> {
    let guard = cx.node(terms.first()?.0).a;
    if !terms.iter().all(|&(a, _)| {
        let n = cx.node(a);
        n.op == OpCode::Select && n.a == guard
    }) {
        return None;
    }
    let mut answer = None;
    for truth in [true, false] {
        let mut offset = konst;
        let mut out = [(0, BitVec::zero(konst.width())); SELECT_TERMS];
        let mut len = 0;
        for &(a, mut k) in terms {
            let s = cx.node(a);
            let mut v = if truth { s.b } else { s.c };
            loop {
                *fuel = fuel.checked_sub(1)?;
                let n = cx.node(v);
                if n.op == OpCode::Shl
                    && let Some(j) = cx.const_val(n.b)
                {
                    k = BitVec::bin_unchecked(BinOp::Shl, &k, &j);
                    v = n.a;
                } else if n.op == OpCode::Mul
                    && let Some((x, c)) = with_const(cx, v)
                {
                    k = BitVec::bin_unchecked(BinOp::Mul, &k, &cx.const_val(c)?);
                    v = x;
                } else {
                    break;
                }
            }
            if k.is_zero() {
                continue;
            }
            if let Some(c) = cx.const_val(v) {
                let d = BitVec::bin_unchecked(BinOp::Mul, &k, &c);
                offset = BitVec::bin_unchecked(BinOp::Add, &offset, &d);
            } else if let Some(i) = out[..len].iter().position(|(x, _)| *x == v) {
                let coef = BitVec::bin_unchecked(BinOp::Add, &out[i].1, &k);
                if coef.is_zero() {
                    len -= 1;
                    out[i] = out[len];
                } else {
                    out[i].1 = coef;
                }
            } else {
                out[len] = (v, k);
                len += 1;
            }
        }
        let value = if len == 0 {
            offset
        } else {
            selected_constant(cx, &out[..len], offset, fuel)?
        };
        if answer.is_some_and(|v| v != value) {
            return None;
        }
        answer = Some(value);
    }
    answer
}

const SELECT_TERMS: usize = 8;
const SELECT_WORK: u32 = 48;

/// The linear pass at `n`. It tries several candidates in turn, and what each one it declines
/// contributes stays in the result: a candidate rejected only because a part of the node has
/// another user is not rejected for good (the user may go), whichever candidate it was. Kept
/// of the last candidate alone, the node was remembered as final in a form the next call, in a
/// context without that memory, rewrote.
/// Canonicalize additive 2-bit selector tables into flat sums of 1-bit selects:
/// - `select(a, select(b, c10 + c01, c10), select(b, c01, 0))` -> `select(a, c10, 0) + select(b, c01, 0)`
/// - `select(a, s + k, s)` (where `s` is a constant-armed `select`) -> `s + select(a, k, 0)`
fn additive_select(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Option<Step>, Stop> {
    let node = cx.node(n);
    if node.op != OpCode::Select {
        return Ok(None);
    }
    let w = cx.width_of(n);
    let zero = BitVec::zero(w);
    let (cond, t, f) = (node.a, node.b, node.c);

    let bit_key = |id: u32| -> (u32, u16) {
        let bn = cx.node(id);
        if bn.op == OpCode::Extract && bn.width == 1 {
            if bn.b == 0 && cx.node(bn.a).op == OpCode::LShr {
                let sn = cx.node(bn.a);
                if let Some(s) = cx.const_val(sn.b).and_then(|v| v.to_u64())
                    && s < u64::from(cx.wid(sn.a))
                {
                    return (sn.a, s as u16);
                }
            }
            return (bn.a, bn.b as u16);
        }
        (id, 0)
    };
    let scaled_bit_arm = |arm: u32| -> Option<((u32, u16), BitVec)> {
        let an = cx.node(arm);
        let one = BitVec::from_u64(w, 1).ok()?;
        let (unit, scale) = match an.op {
            OpCode::Sext if cx.wid(an.a) == 1 => return Some((bit_key(an.a), BitVec::ones(w))),
            OpCode::Mul => {
                if let Some(k) = cx.const_val(an.b) {
                    (an.a, k)
                } else {
                    (an.b, cx.const_val(an.a)?)
                }
            }
            OpCode::Shl => {
                let s = cx.const_val(an.b)?.to_u64()?;
                if s >= u64::from(w.bits()) {
                    return None;
                }
                (an.a, crate::facts::known::bv_shl(&one, s as u32))
            }
            _ => (arm, one),
        };
        let un = cx.node(unit);
        let is_one_const = |id: u32| cx.const_val(id).and_then(|v| v.to_u64()) == Some(1);
        let key = if un.op == OpCode::Zext && cx.wid(un.a) == 1 {
            bit_key(un.a)
        } else if un.op == OpCode::And && (is_one_const(un.a) || is_one_const(un.b)) {
            let v = if is_one_const(un.b) { un.a } else { un.b };
            let vn = cx.node(v);
            if vn.op == OpCode::LShr
                && let Some(s) = cx.const_val(vn.b).and_then(|v| v.to_u64())
                && s < u64::from(cx.wid(vn.a))
            {
                (vn.a, s as u16)
            } else {
                (v, 0)
            }
        } else {
            return None;
        };
        Some((key, scale))
    };

    // Pattern 1: `select(a, s + k, s)` or `select(a, s, s + k)` where `s` is a constant-armed
    // select or a 1-bit scaled arm (also matching disjoint `s | k` / `s ^ k`).
    let base_known_mask = |id: u32| -> Option<BitVec> {
        let sn = cx.node(id);
        if sn.op == OpCode::Select
            && let (Some(c1), Some(c0)) = (cx.const_val(sn.b), cx.const_val(sn.c))
        {
            return Some(BitVec::bin_unchecked(BinOp::Or, &c1, &c0));
        }
        scaled_bit_arm(id).map(|(_, scale)| scale)
    };
    let add_const_of = |sum_id: u32, base_id: u32, base_mask: &BitVec| -> Option<BitVec> {
        let sn = cx.node(sum_id);
        match sn.op {
            OpCode::Add if sn.a == base_id => cx.const_val(sn.b),
            OpCode::Add if sn.b == base_id => cx.const_val(sn.a),
            OpCode::Sub if sn.a == base_id => {
                cx.const_val(sn.b).map(|k| BitVec::un_unchecked(UnOp::Neg, &k))
            }
            OpCode::Or | OpCode::Xor if sn.a == base_id => cx
                .const_val(sn.b)
                .filter(|k| BitVec::bin_unchecked(BinOp::And, k, base_mask).is_zero()),
            OpCode::Or | OpCode::Xor if sn.b == base_id => cx
                .const_val(sn.a)
                .filter(|k| BitVec::bin_unchecked(BinOp::And, k, base_mask).is_zero()),
            _ => None,
        }
    };
    if let Some(mask) = base_known_mask(f)
        && let Some(k) = add_const_of(t, f, &mask)
    {
        let before = cx.len() as u32;
        let kv = r.build(cx, |cx| cx.mk_const(&k))?;
        let zv = r.build(cx, |cx| cx.mk_const(&zero))?;
        let e = r.build(cx, |cx| {
            let sel = cx.c_select(cond, kv, zv)?;
            cx.c_bin(BinOp::Add, f, sel)
        })?;
        let mut stops = vec![cond, f];
        if kv < before {
            stops.push(kv);
        }
        if zv < before {
            stops.push(zv);
        }
        return super::finish_with(r, cx, PassKind::Linear, n, e, before, &stops, Fin::FINAL, true)
            .map(Some);
    }
    if let Some(mask) = base_known_mask(t)
        && let Some(k) = add_const_of(f, t, &mask)
    {
        let before = cx.len() as u32;
        let kv = r.build(cx, |cx| cx.mk_const(&k))?;
        let zv = r.build(cx, |cx| cx.mk_const(&zero))?;
        let e = r.build(cx, |cx| {
            let sel = cx.c_select(cond, zv, kv)?;
            cx.c_bin(BinOp::Add, t, sel)
        })?;
        let mut stops = vec![cond, t];
        if kv < before {
            stops.push(kv);
        }
        if zv < before {
            stops.push(zv);
        }
        return super::finish_with(r, cx, PassKind::Linear, n, e, before, &stops, Fin::FINAL, true)
            .map(Some);
    }

    // Pattern 2: `select(a, select(b, c11, c10), select(b', f1, f0))` where `b' == b` or `~b`
    // and `c11 + c00 == c10 + c01 (mod 2^w)`.
    let (tn, fn_) = (cx.node(t), cx.node(f));
    if tn.op == OpCode::Select && fn_.op == OpCode::Select {
        let (Some(c11), Some(c10), Some(f1), Some(f0)) = (
            cx.const_val(tn.b),
            cx.const_val(tn.c),
            cx.const_val(fn_.b),
            cx.const_val(fn_.c),
        ) else {
            return Ok(None);
        };
        let b = tn.a;
        let (c01, c00) = if fn_.a == b {
            (f1, f0)
        } else if super::bitwise::complementary_conds(cx, fn_.a, b) {
            (f0, f1)
        } else {
            return Ok(None);
        };
        let lhs = BitVec::bin_unchecked(BinOp::Add, &c11, &c00);
        let rhs = BitVec::bin_unchecked(BinOp::Add, &c10, &c01);
        if lhs == rhs {
            let split_consts = if c00.is_zero() {
                Some(((c10, zero), (c01, zero)))
            } else if c01.is_zero() {
                Some(((c11, zero), (zero, c00)))
            } else if c10.is_zero() {
                Some(((zero, c00), (c11, zero)))
            } else if c11.is_zero() {
                Some(((zero, c01), (zero, c10)))
            } else {
                None
            };
            if let Some(((a_t, a_f), (b_t, b_f))) = split_consts {
                let before = cx.len() as u32;
                let ka_t = r.build(cx, |cx| cx.mk_const(&a_t))?;
                let ka_f = r.build(cx, |cx| cx.mk_const(&a_f))?;
                let kb_t = r.build(cx, |cx| cx.mk_const(&b_t))?;
                let kb_f = r.build(cx, |cx| cx.mk_const(&b_f))?;
                let e = r.build(cx, |cx| {
                    let s1 = cx.c_select(cond, ka_t, ka_f)?;
                    let s2 = cx.c_select(b, kb_t, kb_f)?;
                    cx.c_bin(BinOp::Add, s1, s2)
                })?;
                let mut stops = vec![cond, b];
                for c in [ka_t, ka_f, kb_t, kb_f] {
                    if c < before && !stops.contains(&c) {
                        stops.push(c);
                    }
                }
                return super::finish_with(
                    r,
                    cx,
                    PassKind::Linear,
                    n,
                    e,
                    before,
                    &stops,
                    Fin::FINAL,
                    true,
                )
                .map(Some);
            }
        }
    }

    // Pattern 2b: `select(a, select(b, c11, c10), f)` (or symmetric) where `f` is already a
    // canonical 1-bit scaled value of `b` equal to `c11 - c10` (e.g. `zext(b) * d`, `zext(b) << k`,
    // or `(x >>u lo & 1) * d` when `b` is `extract<lo, 1>(x)`), rewriting to `select(a, c10, 0) + f`.
    if tn.op == OpCode::Select
        && let (Some(c11), Some(c10)) = (cx.const_val(tn.b), cx.const_val(tn.c))
        && let Some((fkey, fscale)) = scaled_bit_arm(f)
        && fkey == bit_key(tn.a)
        && fscale == BitVec::bin_unchecked(BinOp::Sub, &c11, &c10)
    {
        let before = cx.len() as u32;
        let zv = r.build(cx, |cx| cx.mk_const(&zero))?;
        let k1 = r.build(cx, |cx| cx.mk_const(&c10))?;
        let e = r.build(cx, |cx| {
            let s1 = cx.c_select(cond, k1, zv)?;
            cx.c_bin(BinOp::Add, s1, f)
        })?;
        let mut stops = vec![cond, f];
        for c in [zv, k1] {
            if c < before && !stops.contains(&c) {
                stops.push(c);
            }
        }
        return super::finish_with(r, cx, PassKind::Linear, n, e, before, &stops, Fin::FINAL, true)
            .map(Some);
    }
    if fn_.op == OpCode::Select
        && let (Some(c01), Some(c00)) = (cx.const_val(fn_.b), cx.const_val(fn_.c))
        && let Some((tkey, tscale)) = scaled_bit_arm(t)
        && tkey == bit_key(fn_.a)
        && tscale == BitVec::bin_unchecked(BinOp::Sub, &c01, &c00)
    {
        let before = cx.len() as u32;
        let zv = r.build(cx, |cx| cx.mk_const(&zero))?;
        let k0 = r.build(cx, |cx| cx.mk_const(&c00))?;
        let e = r.build(cx, |cx| {
            let s1 = cx.c_select(cond, zv, k0)?;
            cx.c_bin(BinOp::Add, s1, t)
        })?;
        let mut stops = vec![cond, t];
        for c in [zv, k0] {
            if c < before && !stops.contains(&c) {
                stops.push(c);
            }
        }
        return super::finish_with(r, cx, PassKind::Linear, n, e, before, &stops, Fin::FINAL, true)
            .map(Some);
    }
    // Pattern 3: `select(c, k1 * base, k2 * base)` -> `base * select(c, k1, k2)`.
    // Works even when one arm's multiplier is even (where `scaled_base` shifts out trailing zeros
    // and halves the modulus) by dividing by the odd arm's pivot coefficient and verifying exact
    // equality modulo `2^w` on the other arm.
    #[cfg(feature = "mba")]
    if cx.const_val(t).is_none()
        && cx.const_val(f).is_none()
        && (linear_op(cx.node(t).op) || linear_op(cx.node(f).op))
    {
        let ft = form_of(r, cx, t)?;
        let ff = form_of(r, cx, f)?;
        if !ft.terms.is_empty()
            && ft.terms.len() <= BASE_TERMS
            && ft.terms.len() == ff.terms.len()
            && ft.terms.iter().zip(&ff.terms).all(|(&(a, _), &(b, _))| a == b)
        {
            type ScaledSelectMatch = (BitVec, BitVec, BitVec, Vec<(u32, BitVec)>);
            let matched = (|| -> Option<ScaledSelectMatch> {
                let (k0_t, k0_f) = (ft.terms[0].1, ff.terms[0].1);
                if k0_t == k0_f {
                    return None;
                }
                if let Some(inv) = crate::invert::mul_inverse(&k0_t) {
                    let base_k = BitVec::bin_unchecked(BinOp::Mul, &ft.konst, &inv);
                    let base: Vec<(u32, BitVec)> = ft
                        .terms
                        .iter()
                        .map(|&(a, k)| (a, BitVec::bin_unchecked(BinOp::Mul, &k, &inv)))
                        .collect();
                    if BitVec::bin_unchecked(BinOp::Mul, &base_k, &k0_f) == ff.konst
                        && base
                            .iter()
                            .zip(&ff.terms)
                            .all(|(&(_, bk), &(_, fk))| {
                                BitVec::bin_unchecked(BinOp::Mul, &bk, &k0_f) == fk
                            })
                    {
                        return Some((k0_t, k0_f, base_k, base));
                    }
                }
                if let Some(inv) = crate::invert::mul_inverse(&k0_f) {
                    let base_k = BitVec::bin_unchecked(BinOp::Mul, &ff.konst, &inv);
                    let base: Vec<(u32, BitVec)> = ff
                        .terms
                        .iter()
                        .map(|&(a, k)| (a, BitVec::bin_unchecked(BinOp::Mul, &k, &inv)))
                        .collect();
                    if BitVec::bin_unchecked(BinOp::Mul, &base_k, &k0_t) == ft.konst
                        && base
                            .iter()
                            .zip(&ft.terms)
                            .all(|(&(_, bk), &(_, tk))| {
                                BitVec::bin_unchecked(BinOp::Mul, &bk, &k0_t) == tk
                            })
                    {
                        return Some((k0_t, k0_f, base_k, base));
                    }
                }
                if ft.konst.is_zero()
                    && ff.konst.is_zero()
                    && let (Some((kt, bt)), Some((kf, bf))) = (scaled_base(&ft), scaled_base(&ff))
                    && bt == bf
                    && kt != kf
                {
                    return Some((kt, kf, zero, bt));
                }
                None
            })();
            if let Some((kt, kf, bk, bt)) = matched {
                let before = cx.len() as u32;
                let base = emit(r, cx, &Form::of(bk, &bt))?;
                let sel = r.build(cx, |cx| {
                    let c1 = cx.mk_const(&kt)?;
                    let c2 = cx.mk_const(&kf)?;
                    cx.c_select(cond, c1, c2)
                })?;
                let e = r.build(cx, |cx| cx.c_bin(BinOp::Mul, base, sel))?;
                let mut stops: Vec<u32> = bt.iter().map(|&(a, _)| a).collect();
                stops.push(cond);
                return finish(
                    r,
                    cx,
                    PassKind::Linear,
                    n,
                    e,
                    before,
                    &stops,
                    ft.fin.and(ff.fin),
                )
                .map(Some);
            }
        }
    }

    Ok(None)
}

/// Whether `part` is syntactically a bitwise subset of `whole` (`part & ~whole == 0`),
/// detected by checking if any `And`-conjunct of `part` is an `Or`-disjunct of `whole`.
fn syntactic_bitwise_subset(cx: &Context, part: u32, whole: u32) -> bool {
    let mut disjuncts = Vec::with_capacity(8);
    let mut stack = vec![whole];
    while let Some(i) = stack.pop() {
        if disjuncts.len() >= 16 {
            break;
        }
        let n = cx.node(i);
        if n.op == OpCode::Or {
            stack.push(n.a);
            stack.push(n.b);
        } else {
            disjuncts.push(i);
        }
    }
    let mut cstack = vec![part];
    let mut seen = 0usize;
    while let Some(i) = cstack.pop() {
        if disjuncts.contains(&i) {
            return true;
        }
        seen += 1;
        if seen >= 16 {
            break;
        }
        let n = cx.node(i);
        if n.op == OpCode::And {
            cstack.push(n.a);
            cstack.push(n.b);
        }
    }
    false
}

pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let op = node.op;
    if op == OpCode::Select
        && let Some(step) = additive_select(r, cx, n)?
    {
        return Ok(step);
    }
    let mut pre_declined = Fin::FINAL;
    // Borrow-free subtraction from a constant superset: whenever `z <=_bitwise c` at every bit
    // (`known_zero(z) | c == all_ones`), `c - z == z ^ c` at any width with zero borrows.
    if op == OpCode::Sub
        && let Some(c_bv) = cx.const_val(node.a)
        && cx.const_val(node.b).is_none()
    {
        let (kb_opt, kfin) = super::known(r, cx, node.b)?;
        if let Some(kb) = kb_opt
            && BitVec::bin_unchecked(BinOp::Or, &kb.known_zero(), &c_bv).is_ones()
        {
            let before = cx.len() as u32;
            let e = r.build(cx, |cx| cx.c_bin(BinOp::Xor, node.b, node.a))?;
            let mut stops = vec![node.b];
            if node.a < before {
                stops.push(node.a);
            }
            match super::finish_with(r, cx, PassKind::Linear, n, e, before, &stops, kfin, true)? {
                Step::Normal(f) => pre_declined = pre_declined.and(f),
                done => return Ok(done),
            }
        } else {
            pre_declined = pre_declined.and(kfin.unchanged());
        }
    }
    if matches!(op, OpCode::Add | OpCode::Sub) {
        if op == OpCode::Add
            && let Some(step) =
                super::bitwise::merge_complementary_arms(r, cx, PassKind::Linear, n, node.a, node.b)?
        {
            match step {
                Step::Normal(f) => pre_declined = pre_declined.and(f),
                done => return Ok(done),
            }
        }
        // Carry/borrow-free `(x ^ c1) ± c2 -> x ^ k` and `c2 - (x ^ c1) -> x ^ k` (plus `select`
        // constants) when the constant offset carries nowhere into the possible ones `u` of `x`
        // (for `c2 - y`, via `c2 - y == ~((~c2) + y)`).
        if node.width <= 64 {
            let mask = u64::MAX >> (64 - node.width);
            let pairs: [(u32, u32, bool); 2] = if op == OpCode::Add {
                [(node.a, node.b, false), (node.b, node.a, false)]
            } else {
                // `(x ^ c1) - c2` (`neg_xor = false`, `c2` negated) and `c2 - (x ^ c1)` (`neg_xor = true`).
                [(node.a, node.b, false), (node.b, node.a, true)]
            };
            for (xor_id, other_id, neg_xor) in pairs {
                let xn = cx.node(xor_id);
                if xn.op != OpCode::Xor {
                    continue;
                }
                let Some((x, c1)) = (match (cx.const_val(xn.a), cx.const_val(xn.b)) {
                    (None, Some(k)) => k.to_u64().map(|c| (xn.a, c & mask)),
                    (Some(k), None) => k.to_u64().map(|c| (xn.b, c & mask)),
                    _ => None,
                }) else {
                    continue;
                };
                let (kb_opt, kfin) = super::known(r, cx, x)?;
                let kz = kb_opt
                    .and_then(|kb| kb.known_zero().to_u64())
                    .unwrap_or(0);
                let u = (!kz) & mask;
                if u == mask && !neg_xor {
                    pre_declined = pre_declined.and(kfin.unchanged());
                    continue;
                }
                if let Some(c2_raw) = cx.const_val(other_id).and_then(|v| v.to_u64()) {
                    let add_c = if neg_xor {
                        (!c2_raw) & mask
                    } else if op == OpCode::Sub {
                        c2_raw.wrapping_neg() & mask
                    } else {
                        c2_raw & mask
                    };
                    let k_hi = (c1 & !u).wrapping_add(add_c) & mask;
                    if (k_hi & u) == 0 {
                        let before = cx.len() as u32;
                        let kv_inner = (c1 & u) | k_hi;
                        let kv = if neg_xor {
                            (!kv_inner) & mask
                        } else {
                            kv_inner
                        };
                        let e = r.build(cx, |cx| {
                            let kc = cx.mk_const_u64(node.width, kv)?;
                            cx.c_bin(BinOp::Xor, x, kc)
                        })?;
                        match super::finish_with(
                            r,
                            cx,
                            PassKind::Linear,
                            n,
                            e,
                            before,
                            &[x],
                            kfin,
                            true,
                        )? {
                            Step::Normal(f) => pre_declined = pre_declined.and(f),
                            done => return Ok(done),
                        }
                    } else {
                        pre_declined = pre_declined.and(kfin.unchanged());
                    }
                } else if cx.node(other_id).op == OpCode::Select {
                    let sn = cx.node(other_id);
                    if let (Some(tv_raw), Some(fv_raw)) = (
                        cx.const_val(sn.b).and_then(|v| v.to_u64()),
                        cx.const_val(sn.c).and_then(|v| v.to_u64()),
                    ) {
                        let map_c = |v: u64| {
                            if neg_xor {
                                (!v) & mask
                            } else if op == OpCode::Sub {
                                v.wrapping_neg() & mask
                            } else {
                                v & mask
                            }
                        };
                        let kt_hi = (c1 & !u).wrapping_add(map_c(tv_raw)) & mask;
                        let kf_hi = (c1 & !u).wrapping_add(map_c(fv_raw)) & mask;
                        if (kt_hi & u) == 0 && (kf_hi & u) == 0 {
                            let before = cx.len() as u32;
                            let mut kt = (c1 & u) | kt_hi;
                            let mut kf = (c1 & u) | kf_hi;
                            if neg_xor {
                                kt = (!kt) & mask;
                                kf = (!kf) & mask;
                            }
                            let e = r.build(cx, |cx| {
                                let ct = cx.mk_const_u64(node.width, kt)?;
                                let cf = cx.mk_const_u64(node.width, kf)?;
                                let sel = cx.c_select(sn.a, ct, cf)?;
                                cx.c_bin(BinOp::Xor, x, sel)
                            })?;
                            let mut stops = vec![x, sn.a];
                            stops.sort_unstable();
                            stops.dedup();
                            match super::finish_with(
                                r,
                                cx,
                                PassKind::Linear,
                                n,
                                e,
                                before,
                                &stops,
                                kfin,
                                true,
                            )? {
                                Step::Normal(f) => pre_declined = pre_declined.and(f),
                                done => return Ok(done),
                            }
                        } else {
                            pre_declined = pre_declined.and(kfin.unchanged());
                        }
                    }
                } else {
                    pre_declined = pre_declined.and(kfin.unchanged());
                }
            }
        }
    }
    // `-((-x) * y) -> x * y` and `-(x * (-y)) -> x * y`.
    if op == OpCode::Neg {
        let inner = cx.node(node.a);
        if inner.op == OpCode::Mul {
            let pair = if cx.node(inner.a).op == OpCode::Neg {
                Some((cx.node(inner.a).a, inner.b))
            } else if cx.node(inner.b).op == OpCode::Neg {
                Some((inner.a, cx.node(inner.b).a))
            } else {
                None
            };
            if let Some((x, y)) = pair {
                let before = cx.len() as u32;
                let e = r.build(cx, |cx| cx.c_bin(BinOp::Mul, x, y))?;
                match finish(r, cx, PassKind::Linear, n, e, before, &[x, y], Fin::FINAL)? {
                    Step::Normal(_) => {}
                    step => return Ok(step),
                }
            }
        }
    }
    let mut declined = match factor_sum(r, cx, n)? {
        Some(Step::Normal(f)) => pre_declined.and(f),
        Some(step) => return Ok(step),
        None => pre_declined,
    };
    // A case split on a condition mask the node reads, first (see `cases`).
    let before = cx.len() as u32;
    if let Some((e, f)) = super::cases::split(r, cx, n)? {
        match finish(r, cx, PassKind::Linear, n, e, before, &[], f)? {
            Step::Normal(f) => declined = declined.and(f),
            step => return Ok(step),
        }
    }
    if !linear_op(op) || op == OpCode::Const {
        return Ok(Step::Normal(declined));
    }
    // A product of values, its factors in order (see `sort_chain`).
    if op == OpCode::Mul {
        if node.width == 1 {
            let before = cx.len() as u32;
            let e = r.build(cx, |cx| cx.c_bin(BinOp::And, node.a, node.b))?;
            let mut stops = vec![node.a, node.b];
            stops.sort_unstable();
            stops.dedup();
            match super::finish_with(
                r,
                cx,
                PassKind::Linear,
                n,
                e,
                before,
                &stops,
                Fin::FINAL,
                true,
            )? {
                Step::Normal(f) => declined = declined.and(f),
                step => return Ok(step),
            }
        }
        // 0/1 boolean idempotence (`b * b == b`, `(x * b) * b == x * b`, `b * (b ^ c) == b * (c ^ 1)`,
        // and `(c0 + c1 * b) * b == (c0 + c1) * b`) when `b` is known to be 0 or 1 (`zero_bits(b, ~1)`).
        if node.width <= 64 && node.width > 1 {
            let high_mask = (u64::MAX >> (64 - node.width)) & !1u64;
            for (b_id, other_id) in [(node.a, node.b), (node.b, node.a)] {
                if cx.const_val(b_id).is_some() {
                    continue;
                }
                let (kw, bfin) = super::known_words(r, cx, b_id)?;
                if kw.is_some_and(|[z, _]| (z & high_mask) == high_mask) {
                    if other_id == b_id {
                        let before = cx.len() as u32;
                        match finish(r, cx, PassKind::Linear, n, b_id, before, &[b_id], bfin)? {
                            Step::Normal(f) => declined = declined.and(f),
                            step => return Ok(step),
                        }
                    } else {
                        let on = cx.node(other_id);
                        if on.op == OpCode::Mul && (on.a == b_id || on.b == b_id) {
                            let before = cx.len() as u32;
                            match finish(
                                r,
                                cx,
                                PassKind::Linear,
                                n,
                                other_id,
                                before,
                                &[other_id],
                                bfin,
                            )? {
                                Step::Normal(f) => declined = declined.and(f),
                                step => return Ok(step),
                            }
                        }
                        if on.op == OpCode::Xor {
                            let xor_c = if on.a == b_id {
                                cx.const_val(on.b)
                            } else if on.b == b_id {
                                cx.const_val(on.a)
                            } else {
                                None
                            };
                            if let Some(c_bv) = xor_c {
                                let c_flip = BitVec::bin_unchecked(
                                    BinOp::Xor,
                                    &c_bv,
                                    &BitVec::one(c_bv.width()),
                                );
                                let before = cx.len() as u32;
                                let e = r.build(cx, |cx| {
                                    let ck = cx.mk_const(&c_flip)?;
                                    cx.c_bin(BinOp::Mul, b_id, ck)
                                })?;
                                match finish(
                                    r,
                                    cx,
                                    PassKind::Linear,
                                    n,
                                    e,
                                    before,
                                    &[b_id],
                                    bfin,
                                )? {
                                    Step::Normal(f) => declined = declined.and(f),
                                    step => return Ok(step),
                                }
                            }
                        }
                        let fo = form_of(r, cx, other_id)?;
                        if fo.terms.len() == 1 && fo.terms[0].0 == b_id {
                            let c_sum = BitVec::bin_unchecked(BinOp::Add, &fo.konst, &fo.terms[0].1);
                            let before = cx.len() as u32;
                            let e = r.build(cx, |cx| {
                                let ck = cx.mk_const(&c_sum)?;
                                cx.c_bin(BinOp::Mul, b_id, ck)
                            })?;
                            match finish(
                                r,
                                cx,
                                PassKind::Linear,
                                n,
                                e,
                                before,
                                &[b_id],
                                bfin.and(fo.fin),
                            )? {
                                Step::Normal(f) => declined = declined.and(f),
                                step => return Ok(step),
                            }
                        }
                    }
                } else {
                    declined = declined.and(bfin.unchanged());
                }
            }
        }
        match super::sort_chain(r, cx, PassKind::Linear, n)? {
            Step::Normal(f) => declined = declined.and(f),
            step => return Ok(step),
        }
    }
    let form = form_of(r, cx, n)?;
    #[cfg(feature = "mba")]
    if matches!(op, OpCode::Add | OpCode::Sub)
        && let Some(value) = super::mba::truncated_constant(r, cx, &form.terms, &form.konst)?
    {
        let before = cx.len() as u32;
        let e = r.build(cx, |cx| cx.mk_const(&value))?;
        match finish(r, cx, PassKind::Linear, n, e, before, &[], form.fin)? {
            Step::Normal(f) => declined = declined.and(f),
            step => return Ok(step),
        }
    }
    if matches!(op, OpCode::Add | OpCode::Sub)
        && (2..=SELECT_TERMS).contains(&form.terms.len())
        && cx.node(form.terms[0].0).op == OpCode::Select
    {
        let mut fuel = SELECT_WORK;
        let value = selected_constant(cx, &form.terms, form.konst, &mut fuel);
        r.meter.charge(Counter::PassWork, u64::from(1 + SELECT_WORK - fuel))?;
        if let Some(value) = value {
            let before = cx.len() as u32;
            let e = r.build(cx, |cx| cx.mk_const(&value))?;
            match finish(r, cx, PassKind::Linear, n, e, before, &[], form.fin)? {
                Step::Normal(f) => declined = declined.and(f),
                step => return Ok(step),
            }
        }
    }
    let last = if form.is_atom_of(n) {
        // A sum over the cap in which terms met is written out again, from its whole form.
        match r.linear.whole.met(n) {
            Some(whole) => plain(r, cx, n, whole)?,
            None => Step::Normal(form.fin),
        }
    } else {
        // Bits of one value counted, first (see `bit_count`).
        match bit_count(r, cx, n, &form)? {
            Some(Step::Normal(f)) => declined = declined.and(f),
            Some(step) => return Ok(step),
            None => {}
        }
        // Terms reading one condition, merged first (see `conditions`).
        match super::conditions::step(r, cx, n, &form)? {
            Ok(step) => step,
            Err(f) => {
                declined = declined.and(f);
                // Limbs of one word, joined (see `limbs`).
                match super::limbs::step(r, cx, n, &form)? {
                    Ok(s) => return Ok(s),
                    Err(f) => declined = declined.and(f),
                }
                // A slice of a sum plus a constant, the constant taken into the sum (see
                // `limbs`).
                match super::limbs::folded(r, cx, n, &form)? {
                    Ok(s) => return Ok(s),
                    Err(f) => declined = declined.and(f),
                }
                // Combine nearly-complementary constant-XOR pairs `k1 * (x ^ c1) + k2 * (x ^ c2)`
                // using `(x ^ c1) + (x ^ c2) == (c1 ^ c2) + (((x ^ c1) & ~(c1 ^ c2)) << 1)` when
                // `~(c1 ^ c2)` has at most 1 unknown bit in `x`.
                if let Some(step) = merge_xor_pairs(r, cx, n, &form)? {
                    match step {
                        Step::To(x, fin) => return Ok(Step::To(x, fin)),
                        Step::Normal(fin) => declined = declined.and(fin),
                    }
                }
                if let Some(step) = merge_not_masks(r, cx, n, &form)? {
                    match step {
                        Step::To(x, fin) => return Ok(Step::To(x, fin)),
                        Step::Normal(fin) => declined = declined.and(fin),
                    }
                }
                // A sum that spells an XOR or an OR with a constant (see `masked`).
                let before = cx.len() as u32;
                if let Some((f, leaves)) = masked(r, cx, &form)? {
                    let e = emit(r, cx, &f)?;
                    match finish(r, cx, PassKind::Linear, n, e, before, &leaves, f.fin)? {
                        Step::To(x, fin) => return Ok(Step::To(x, fin)),
                        Step::Normal(fin) => declined = declined.and(fin),
                    }
                }
                plain(r, cx, n, form)?
            }
        }
    };
    // Fallback when linear cancellation declined: `a - b -> a ^ b` when `b` is syntactically
    // a bitwise subset of `a` (zero borrows; `Xor` ranks strictly below `Sub` in the termination
    // order). Running after `plain` ensures disjoint `(a | b) - b` still cancels to `a` first.
    if matches!(last, Step::Normal(_))
        && op == OpCode::Sub
        && cx.node(node.b).op == OpCode::And
        && syntactic_bitwise_subset(cx, node.b, node.a)
    {
        let (a, b) = (node.a, node.b);
        let before = cx.len() as u32;
        let e = r.build(cx, |cx| cx.c_bin(BinOp::Xor, a, b))?;
        match super::finish_with(r, cx, PassKind::Linear, n, e, before, &[a, b], Fin::FINAL, true)?
        {
            Step::Normal(_) => {}
            step => return Ok(step),
        }
    }
    Ok(match last {
        Step::Normal(f) => Step::Normal(f.and(declined)),
        step => step,
    })
}

/// The fewest bits of one value [`bit_count`] writes as a population count.
const COUNTED_BITS: u32 = 3;

/// The term `t` as a count of bits of a value, at `t`'s width: the value and the bits (among
/// its low 128). One bit (`extract<i, 1>(y)` extended, `y & 1`, `(y >>u i) & 1`, the top bit
/// shifted down) or a population count of a field (`popcnt(y & m)`, extended or truncated);
/// a bit of a slice or of a zero extension is a bit of its operand.
fn counted(cx: &Context, t: u32) -> Option<(u32, u128)> {
    let n = cx.node(t);
    let w = u32::from(n.width);
    let shift = |i: u32| cx.const_val(i).and_then(|k| k.to_u64());
    let masked = |a: u32, b: u32| match (cx.const_val(a), cx.const_val(b)) {
        (None, Some(k)) => Some((a, k.to_u128()?)),
        (Some(k), None) => Some((b, k.to_u128()?)),
        _ => None,
    };
    // A count of the bits `m` of `y`, before `y` is traced to the value it reads.
    let bit = |i: u32| (i < 128).then(|| 1u128 << i);
    // (A truncation of a population count to one bit is that count, not a bit of a value.)
    let truncated_count = n.op == OpCode::Extract && n.b == 0 && cx.node(n.a).op == OpCode::Popcnt;
    let (mut y, mut m): (u32, u128) = match n.op {
        OpCode::Extract if w == 1 && !truncated_count => (n.a, bit(n.b)?),
        OpCode::Extract | OpCode::Zext | OpCode::Popcnt => {
            // A population count through a cast, or a bit extended.
            let inner = match n.op {
                OpCode::Popcnt => t,
                OpCode::Extract if n.b != 0 => return None,
                _ => n.a,
            };
            let e = cx.node(inner);
            match e.op {
                OpCode::Extract if e.width == 1 && n.op == OpCode::Zext => (e.a, bit(e.b)?),
                OpCode::Popcnt => {
                    if cx.wid(e.a) > 128 {
                        return None;
                    }
                    let f = cx.node(e.a);
                    let ones = u128::MAX >> (128 - u32::from(f.width));
                    match (f.op == OpCode::And).then(|| masked(f.a, f.b)).flatten() {
                        Some((v, k)) => (v, k & ones),
                        None => (e.a, ones),
                    }
                }
                _ => return None,
            }
        }
        OpCode::And => {
            let (v, k) = masked(n.a, n.b)?;
            if k != 1 {
                return None;
            }
            let s = cx.node(v);
            match (s.op == OpCode::LShr).then(|| shift(s.b)).flatten() {
                Some(k) if k < u64::from(w) => (s.a, bit(k as u32)?),
                _ => (v, 1),
            }
        }
        OpCode::LShr if w > 1 && shift(n.b) == Some(u64::from(w) - 1) => (n.a, bit(w - 1)?),
        _ => return None,
    };
    loop {
        let s = cx.node(y);
        match s.op {
            OpCode::Extract => {
                if s.b >= 128 || m.leading_zeros() < s.b {
                    return None;
                }
                m <<= s.b;
                y = s.a;
            }
            // The extension's high bits are zero: they count nothing.
            OpCode::Zext => {
                m &= u128::MAX >> (128 - u32::from(cx.wid(s.a)).min(128));
                y = s.a;
            }
            OpCode::LShr => {
                let Some(k) = shift(s.b) else { break };
                let wa = u64::from(cx.wid(s.a)).min(128);
                let top_plus_1 = u64::from(128 - m.leading_zeros());
                if k >= wa || top_plus_1 + k > wa {
                    return None;
                }
                m <<= k;
                y = s.a;
            }
            _ => break,
        }
    }
    (m != 0).then_some((y, m))
}

/// The sum `n` (whose form is `form`) with its terms that count bits of one value, with one
/// coefficient and no bit twice, written as one term: the population count of those bits
/// (`Σ c·bitᵢ(x)` is `c·popcnt(x & m)`, the bits a slice of `x` where they are one run). The
/// operand of a parity flag is spelled this way, a bit at a time, and its low bit is then a
/// sum of eight slices at one bit. Three bits or more, from two terms or more.
fn bit_count(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    form: &Form,
) -> Result<Option<Step>, Stop> {
    if form.terms.len() < 2 {
        return Ok(None);
    }
    // Per term: the value and the bits, where it counts some.
    let bits: Vec<Option<(u32, u128)>> = form.terms.iter().map(|&(t, _)| counted(cx, t)).collect();
    // The value and coefficient most such terms share.
    let mut best: Option<(usize, u32, BitVec)> = None;
    for (j, b) in bits.iter().enumerate() {
        let Some((x, _)) = *b else { continue };
        let k = form.terms[j].1;
        let count = bits
            .iter()
            .zip(&form.terms)
            .filter(|(b, t)| b.is_some_and(|(y, _)| y == x) && t.1 == k)
            .count();
        if best.as_ref().is_none_or(|(c, ..)| count > *c) {
            best = Some((count, x, k));
        }
    }
    let Some((_, x, k)) = best else {
        return Ok(None);
    };
    // Its bits (a term with a bit already counted stays a term), and the other terms.
    let (mut set, mut merged) = (0u128, 0usize);
    let mut rest: Vec<(u32, BitVec)> = Vec::new();
    for (b, &term) in bits.iter().zip(&form.terms) {
        match *b {
            Some((y, m)) if y == x && term.1 == k && set & m == 0 => {
                set |= m;
                merged += 1;
            }
            _ => rest.push(term),
        }
    }
    if merged < 2 || set.count_ones() < COUNTED_BITS {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, form.terms.len() as u64)?;
    let lo = set.trailing_zeros();
    let span = 128 - set.leading_zeros() - lo;
    let run = set >> lo == u128::MAX >> (128 - span);
    if span > 64 && !run {
        return Ok(None);
    }
    let w = form.konst.width();
    let before = cx.len() as u32;
    let count = r.build(cx, |cx| {
        let mut field = cx.c_extract(x, lo as u16, span as u16)?;
        if !run {
            let mask = cx.mk_const_u64(cx.wid(field), (set >> lo) as u64)?;
            field = cx.c_bin(BinOp::And, field, mask)?;
        }
        let p = cx.c_un(UnOp::Popcnt, field)?;
        match cx.wid(p).cmp(&w.bits()) {
            core::cmp::Ordering::Less => cx.c_zext(p, w.bits()),
            core::cmp::Ordering::Equal => Ok(p),
            core::cmp::Ordering::Greater => cx.c_extract(p, 0, w.bits()),
        }
    })?;
    rest.push((count, k));
    let mut f = Form::of(form.konst, &rest);
    f.fin = form.fin;
    let e = emit(r, cx, &f)?;
    let mut leaves: Vec<u32> = rest.iter().map(|t| t.0).filter(|&t| t != count).collect();
    leaves.push(x);
    leaves.sort_unstable();
    leaves.dedup();
    finish(r, cx, PassKind::Linear, n, e, before, &leaves, f.fin).map(Some)
}

/// Combine `k1 * (x ^ c1) + k2 * (x ^ c2)` in `form` when `~(c1 ^ c2)` has at most 1 unknown
/// bit in `x`, eliminating at least one constant-XOR atom (both when `k1 == k2`).
fn merge_xor_pairs(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    form: &Form,
) -> Result<Option<Step>, Stop> {
    let w = form.konst.width();
    if w.bits() == 0 || w.bits() > 64 || form.terms.len() < 2 || form.terms.len() > 16 {
        return Ok(None);
    }
    let mask = u64::MAX >> (64 - w.bits());
    let xor_or_base = |cx: &Context, id: u32| -> (u32, u64, bool) {
        let xn = cx.node(id);
        if xn.op == OpCode::Xor {
            match (cx.const_val(xn.a), cx.const_val(xn.b)) {
                (None, Some(k)) if let Some(c) = k.to_u64() => return (xn.a, c & mask, true),
                (Some(k), None) if let Some(c) = k.to_u64() => return (xn.b, c & mask, true),
                _ => {}
            }
        }
        (id, 0, false)
    };
    let mut declined = Fin::FINAL;
    for i in 0..form.terms.len() {
        let (x, c1, is_x1) = xor_or_base(cx, form.terms[i].0);
        for j in (i + 1)..form.terms.len() {
            let (x2, c2, is_x2) = xor_or_base(cx, form.terms[j].0);
            if (!is_x1 && !is_x2) || x != x2 || c1 == c2 {
                continue;
            }
            let diff = (c1 ^ c2) & mask;
            let same = (!diff) & mask;
            let (kw_opt, xfin) = super::known_words(r, cx, x)?;
            let (kz, ko) = kw_opt.map_or((0, 0), |[z, o]| (z & mask, o & mask));
            let known_mask = kz | ko;
            let rem_same = same & !known_mask;
            if rem_same.count_ones() > 1 {
                declined = declined.and(xfin.unchanged());
                continue;
            }
            let (t1, k1) = form.terms[i];
            let (t2, k2) = form.terms[j];
            // `(x ^ c1) + (x ^ c2)` = `pair_const + pair_var_coef * (x & rem_same)`.
            let known_same_ones = (ko ^ c1) & same & known_mask;
            let mut pair_const_u64 = diff.wrapping_add(known_same_ones.wrapping_shl(1)) & mask;
            let mut bit_coef_i64 = 0i64;
            if rem_same != 0 {
                if (c1 & rem_same) == 0 {
                    bit_coef_i64 = 2;
                } else {
                    pair_const_u64 = pair_const_u64.wrapping_add(rem_same.wrapping_shl(1)) & mask;
                    bit_coef_i64 = -2;
                }
            }
            let before = cx.len() as u32;
            // Choose which of `(t1, k1)` / `(t2, k2)` to eliminate (`elim` has coeff `ke`, `keep` has `kk - ke`);
            // always prefer keeping a bare `x` over `x ^ c`.
            let both_gone = k1 == k2;
            let (ke, kk_rem, keep_id) = if both_gone {
                (k1, BitVec::zero(w), t2)
            } else if !is_x1 {
                (k2, BitVec::bin_unchecked(BinOp::Sub, &k1, &k2), t1)
            } else if !is_x2 {
                (k1, BitVec::bin_unchecked(BinOp::Sub, &k2, &k1), t2)
            } else {
                super::refresh_uses(r, cx)?;
                let u1 = r.life.live.uses(t1).unwrap_or(1);
                let u2 = r.life.live.uses(t2).unwrap_or(1);
                if u1 <= u2 {
                    (k1, BitVec::bin_unchecked(BinOp::Sub, &k2, &k1), t2)
                } else {
                    (k2, BitVec::bin_unchecked(BinOp::Sub, &k1, &k2), t1)
                }
            };
            let pair_const_bv = BitVec::wrapping_from_u64(w, pair_const_u64);
            let add_konst = BitVec::bin_unchecked(BinOp::Mul, &ke, &pair_const_bv);
            let mut new_konst = BitVec::bin_unchecked(BinOp::Add, &form.konst, &add_konst);
            let mut new_terms: Vec<(u32, BitVec)> = form
                .terms
                .iter()
                .enumerate()
                .filter_map(|(idx, &tk)| (idx != i && idx != j).then_some(tk))
                .collect();
            if !kk_rem.is_zero() {
                new_terms.push((keep_id, kk_rem));
            }
            let mut used_x = false;
            if rem_same != 0 && bit_coef_i64 != 0 {
                let bit_node = r.build(cx, |cx| {
                    let mc = cx.mk_const_u64(w.bits(), rem_same)?;
                    cx.c_bin(BinOp::And, x, mc)
                })?;
                let two = BitVec::wrapping_from_u64(w, 2);
                let scale = if bit_coef_i64 > 0 {
                    BitVec::bin_unchecked(BinOp::Mul, &ke, &two)
                } else {
                    BitVec::un_unchecked(UnOp::Neg, &BitVec::bin_unchecked(BinOp::Mul, &ke, &two))
                };
                if !scale.is_zero() {
                    if let Some(c_bit) = cx.const_val(bit_node) {
                        new_konst = BitVec::bin_unchecked(
                            BinOp::Add,
                            &new_konst,
                            &BitVec::bin_unchecked(BinOp::Mul, &c_bit, &scale),
                        );
                    } else if let Some(slot) = new_terms.iter_mut().find(|(id, _)| *id == bit_node) {
                        slot.1 = BitVec::bin_unchecked(BinOp::Add, &slot.1, &scale);
                        used_x = true;
                    } else {
                        new_terms.push((bit_node, scale));
                        used_x = true;
                    }
                }
            }
            new_terms.retain(|(_, k)| !k.is_zero());
            let mut f = Form::of(new_konst, &new_terms);
            f.fin = form.fin.and(xfin);
            let e = emit(r, cx, &f)?;
            let mut stops: Vec<u32> = form
                .terms
                .iter()
                .enumerate()
                .filter_map(|(idx, &(id, _))| (idx != i && idx != j).then_some(id))
                .collect();
            if used_x {
                stops.push(x);
            }
            if !both_gone {
                stops.push(keep_id);
            }
            stops.sort_unstable();
            stops.dedup();
            match super::finish_with(
                r,
                cx,
                PassKind::Linear,
                n,
                e,
                before,
                &stops,
                f.fin,
                both_gone || !is_x1 || !is_x2,
            )? {
                Step::Normal(df) => declined = declined.and(df),
                done => return Ok(Some(done)),
            }
        }
    }
    Ok((declined != Fin::FINAL).then_some(Step::Normal(declined)))
}

/// Rewrite `k * (~x & M)` terms in `form` as `k * M - k * (x & M)` when `form` already carries a
/// constant offset or `x & M`, eliminating `~x` and unifying `K + (~x & M)` with `(K + M) - (x & M)`.
fn merge_not_masks(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    form: &Form,
) -> Result<Option<Step>, Stop> {
    if form.terms.len() < 2 || form.terms.len() > 16 {
        return Ok(None);
    }
    let not_mask_of = |cx: &Context, id: u32| -> Option<(u32, u32, BitVec)> {
        let an = cx.node(id);
        if an.op != OpCode::And {
            return None;
        }
        let (not_id, m_id, m_bv) = match (cx.const_val(an.a), cx.const_val(an.b)) {
            (None, Some(m)) if !m.is_zero() && !m.is_ones() => (an.a, an.b, m),
            (Some(m), None) if !m.is_zero() && !m.is_ones() => (an.b, an.a, m),
            _ => return None,
        };
        let nn = cx.node(not_id);
        (nn.op == OpCode::Not).then_some((nn.a, m_id, m_bv))
    };
    let mut found: Vec<(usize, u32, u32, BitVec)> = Vec::new();
    for (idx, &(tid, _)) in form.terms.iter().enumerate() {
        if let Some((x, m_id, m_bv)) = not_mask_of(cx, tid) {
            let w_bits = form.konst.width().bits();
            let pos_exists = cx
                .find(&Node::new(OpCode::And, w_bits, x, m_id, 0))
                .or_else(|| cx.find(&Node::new(OpCode::And, w_bits, m_id, x, 0)))
                .is_some_and(|pid| form.terms.binary_search_by_key(&pid, |t| t.0).is_ok());
            if !form.konst.is_zero() || pos_exists {
                found.push((idx, x, m_id, m_bv));
            }
        }
    }
    if found.is_empty() {
        return Ok(None);
    }
    let before = cx.len() as u32;
    let mut new_konst = form.konst;
    let mut new_terms: Vec<(u32, BitVec)> = Vec::with_capacity(form.terms.len());
    let mut stops: Vec<u32> = Vec::new();
    for (idx, &(tid, k)) in form.terms.iter().enumerate() {
        if let Some(&(_, x, m_id, ref m_bv)) = found.iter().find(|&&(i, ..)| i == idx) {
            let add_k = BitVec::bin_unchecked(BinOp::Mul, &k, m_bv);
            new_konst = BitVec::bin_unchecked(BinOp::Add, &new_konst, &add_k);
            let pos_and = r.build(cx, |cx| cx.c_bin(BinOp::And, x, m_id))?;
            let neg_k = BitVec::un_unchecked(UnOp::Neg, &k);
            new_terms.push((pos_and, neg_k));
            stops.push(x);
            stops.push(m_id);
        } else {
            new_terms.push((tid, k));
            stops.push(tid);
        }
    }
    let mut f = Form::of(new_konst, &new_terms);
    f.fin = form.fin;
    let e = emit(r, cx, &f)?;
    stops.sort_unstable();
    stops.dedup();
    finish(r, cx, PassKind::Linear, n, e, before, &stops, f.fin).map(Some)
}

/// The linear pass at `n` over its form as computed.
fn plain(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32, form: Form) -> Result<Step, Stop> {
    let mut atoms: Vec<u32> = form.terms.iter().map(|t| t.0).collect();
    atoms.sort_unstable();
    // Detect whether `n` is a 3+-term `Add`/`Sub` tree containing a single-use disjoint `Or`
    // that `form_of` flattened into additive terms, so `... + (a | b) + ...` canonicalizes to
    // the flat `Add` order even on an operator-count tie.
    let mut flattened_disjoint_or = false;
    let mut shared_disjoint_or = false;
    if matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) && form.terms.len() >= 3 {
        super::refresh_uses(r, cx)?;
        let mut st = vec![n];
        let mut seen = 0usize;
        while let Some(cur) = st.pop() {
            seen += 1;
            if seen > 48 {
                break;
            }
            let cn = cx.node(cur);
            if matches!(cn.op, OpCode::Add | OpCode::Sub) {
                st.push(cn.a);
                st.push(cn.b);
            } else if cn.op == OpCode::Or && atoms.binary_search(&cur).is_err() {
                if super::alone(r)
                    || (!r.life.dead.contains(cur) && r.life.live.uses(cur) == Some(1))
                {
                    flattened_disjoint_or = true;
                    break;
                } else {
                    shared_disjoint_or = true;
                }
            }
        }
    }
    let fin = if shared_disjoint_or {
        form.fin.and(Fin::PROVISIONAL)
    } else {
        form.fin
    };
    let estimate = estimate(&form);
    // A constant always commits (see `shrinks`).
    if !form.terms.is_empty()
        && !flattened_disjoint_or
        && let Some(f) = worth_building(r, cx, n, &atoms, estimate)?
    {
        r.stats.passes.entry("linear").or_default().rejected_cost += 1;
        return Ok(Step::Normal(fin.and(f)));
    }
    let before = cx.len() as u32;
    let e = emit(r, cx, &form)?;
    r.explain_with(|| crate::engine::Explanation::Linear {
        konst: form.konst,
        terms: form.terms.iter().map(|&(a, k)| (cx.handle(a), k)).collect(),
    });
    if flattened_disjoint_or && matches!(cx.node(e).op, OpCode::Add | OpCode::Sub) {
        let mut any_disjoint_add = false;
        let mut fin_disj = fin;
        let mut st = vec![e];
        while let Some(cur) = st.pop() {
            if atoms.binary_search(&cur).is_ok() {
                continue;
            }
            let cn = cx.node(cur);
            if cn.op == OpCode::Add {
                let (d, dfa, dfb) = disjoint(r, cx, cn.a, cn.b)?;
                fin_disj = fin_disj.and(dfa).and(dfb);
                if d {
                    any_disjoint_add = true;
                    break;
                }
            }
            if matches!(cn.op, OpCode::Add | OpCode::Sub) {
                st.push(cn.a);
                st.push(cn.b);
            }
        }
        if !any_disjoint_add {
            return super::finish_with(r, cx, PassKind::Linear, n, e, before, &atoms, fin_disj, true);
        }
    }
    finish(r, cx, PassKind::Linear, n, e, before, &atoms, fin)
}

/// The sum `konst + Σ coeff·term` taken apart into groups of terms whose bitwise parts share
/// no atom, each group with several terms simplified alone by `part`: the sum of the results,
/// or `None` when there is one group or no group changes (what was built is then retired).
#[cfg(feature = "mba")]
fn grouped(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    konst: &BitVec,
    terms: &[(u32, BitVec)],
    fin: Fin,
    part: &mut impl FnMut(&mut Runner<'_, '_>, &mut Context, u32) -> Result<Option<u32>, Stop>,
) -> Result<Option<(Form, Fin)>, Stop> {
    if terms.len() < 3 {
        return Ok(None);
    }
    let mut sets = Vec::with_capacity(terms.len());
    for &(a, _) in terms {
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
    let w = konst.width();
    let before = cx.len() as u32;
    let mut total = Form::of(*konst, &[]);
    let mut fin = fin;
    let mut changed = false;
    for idx in groups.values() {
        let part_terms: Vec<(u32, BitVec)> = idx.iter().map(|&i| terms[i]).collect();
        let mut f = Form::of(BitVec::zero(w), &part_terms);
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
    Ok(Some((total, fin)))
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
    let before = cx.len() as u32;
    let Some((total, fin)) = grouped(r, cx, &form.konst, &form.terms, form.fin, part)? else {
        return Ok(None);
    };
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

/// The most terms of a sum [`common_factors`] reads, and the most factors of one of them.
#[cfg(feature = "mba")]
const FACTOR_TERMS: usize = 48;
#[cfg(feature = "mba")]
const FACTOR_LEAVES: usize = 8;

/// The product `t` as a constant times its non-constant factors (sorted), read through
/// products, negations and left shifts by a constant, shared or not; `None` past
/// [`FACTOR_LEAVES`] factors.
#[cfg(feature = "mba")]
pub(super) fn scaled_factors(cx: &Context, t: u32) -> Option<(BitVec, Vec<u32>)> {
    let w = cx.width_of(t);
    let mut k = BitVec::one(w);
    let mut out: Vec<u32> = Vec::new();
    let mut todo = vec![t];
    let mut steps = 0usize;
    while let Some(i) = todo.pop() {
        steps += 1;
        if steps > 4 * FACTOR_LEAVES {
            return None;
        }
        let node = cx.node(i);
        match node.op {
            OpCode::Const => {
                k = BitVec::bin_unchecked(BinOp::Mul, &k, &cx.const_val(i)?);
            }
            OpCode::Mul => todo.extend([node.a, node.b]),
            OpCode::Neg => {
                k = BitVec::un_unchecked(UnOp::Neg, &k);
                todo.push(node.a);
            }
            OpCode::Shl if cx.const_val(node.b).is_some() => {
                let scale =
                    BitVec::bin_unchecked(BinOp::Shl, &BitVec::one(w), &cx.const_val(node.b)?);
                k = BitVec::bin_unchecked(BinOp::Mul, &k, &scale);
                todo.push(node.a);
            }
            _ => {
                if out.len() == FACTOR_LEAVES {
                    return None;
                }
                out.push(i);
            }
        }
    }
    out.sort_unstable();
    Some((k, out))
}

/// The sum `n` with terms that are products with the same non-constant factors
/// (`Σ (cᵢ·f)·tᵢ + rest`), as those factors, the sum of those terms without them, `Σ cᵢ·tᵢ`
/// (built), and the rest of the sum: the products are read through negations, constants and
/// shared subproducts, so a coefficient spelled as a product of its own with the factor
/// (`(f·a)·t₁ − (f·b)·t₂`) is seen. The terms are the ones with the factor most of them have
/// (an obfuscator scales an MBA by a value and adds the result to something else); `None`
/// when no two terms share one.
#[cfg(feature = "mba")]
fn common_factors(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<Factored>, Stop> {
    if !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) {
        return Ok(None);
    }
    let form = form_of(r, cx, n)?;
    if form.terms.len() < 2 || form.terms.len() > FACTOR_TERMS {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, form.terms.len() as u64)?;
    // Each term's factors (none for one past the limits), and how many terms have each.
    let mut products: Vec<Option<(BitVec, Vec<u32>)>> = Vec::with_capacity(form.terms.len());
    let mut terms_with: Vec<(u32, u32)> = Vec::new();
    for &(t, k) in &form.terms {
        let p = scaled_factors(cx, t).map(|(c, f)| (BitVec::bin_unchecked(BinOp::Mul, &k, &c), f));
        if let Some((_, factors)) = &p {
            for (j, f) in factors.iter().enumerate() {
                if factors[..j].contains(f) {
                    continue;
                }
                match terms_with.iter_mut().find(|(x, _)| x == f) {
                    Some((_, count)) => *count += 1,
                    None => terms_with.push((*f, 1)),
                }
            }
        }
        products.push(p);
    }
    // The factor in the most terms (the first made among equals).
    let Some(&(factor, count)) = terms_with
        .iter()
        .max_by_key(|&&(f, count)| (count, core::cmp::Reverse(f)))
    else {
        return Ok(None);
    };
    if count < 2 {
        return Ok(None);
    }
    // What the terms with it have in common (a multiset: sorted, repeats kept), and the
    // other terms.
    let mut common: Option<Vec<u32>> = None;
    let mut rest: Vec<(u32, BitVec)> = Vec::new();
    for (p, &term) in products.iter_mut().zip(&form.terms) {
        match p {
            Some((_, factors)) if factors.contains(&factor) => {
                common = Some(match common {
                    None => factors.clone(),
                    Some(old) => {
                        let mut left = factors.clone();
                        old.into_iter()
                            .filter(|f| match left.iter().position(|x| x == f) {
                                Some(j) => {
                                    left.swap_remove(j);
                                    true
                                }
                                None => false,
                            })
                            .collect()
                    }
                });
            }
            _ => {
                *p = None;
                rest.push(term);
            }
        }
    }
    let Some(common) = common else {
        return Ok(None);
    };
    let w = form.konst.width();
    let mut konst = BitVec::zero(w);
    let mut terms: Vec<(u32, BitVec)> = Vec::with_capacity(products.len());
    for (k, mut factors) in products.into_iter().flatten() {
        for f in &common {
            if let Some(j) = factors.iter().position(|x| x == f) {
                factors.remove(j);
            }
        }
        let mut left: Option<u32> = None;
        for f in factors {
            left = Some(match left {
                None => f,
                Some(a) => r.build(cx, |cx| cx.c_bin(BinOp::Mul, a, f))?,
            });
        }
        match left {
            Some(x) => terms.push((x, k)),
            None => konst = BitVec::bin_unchecked(BinOp::Add, &konst, &k),
        }
    }
    let inner = emit(r, cx, &Form::of(konst, &terms))?;
    Ok(Some(Factored {
        common,
        inner,
        rest: Form::of(form.konst, &rest),
        fin: form.fin,
    }))
}

/// A sum with the factors some of its terms share taken out of them (see
/// [`common_factors`]): `common · inner + rest`.
#[cfg(feature = "mba")]
struct Factored {
    common: Vec<u32>,
    inner: u32,
    rest: Form,
    fin: Fin,
}

/// `inner` times each of `common`, plus `rest`, committed for `n` by the commit rule (as
/// `kind`'s).
#[cfg(feature = "mba")]
#[allow(clippy::too_many_arguments)]
fn commit_factored(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    kind: PassKind,
    n: u32,
    common: &[u32],
    inner: u32,
    rest: &Form,
    before: u32,
    fin: Fin,
) -> Result<Step, Stop> {
    let mut e = inner;
    for &f in common {
        e = r.build(cx, |cx| cx.c_bin(BinOp::Mul, f, e))?;
    }
    if !rest.terms.is_empty() || !rest.konst.is_zero() {
        let other = emit(r, cx, rest)?;
        e = r.build(cx, |cx| cx.c_bin(BinOp::Add, e, other))?;
    }
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
    finish(r, cx, kind, n, e, before, &stops, fin)
}

/// the sum `n` with terms that are products with the same non-constant factors
/// (an obfuscator scales an MBA by a value, each coefficient spelled as a product of its own
/// with it, and adds the result to other terms) written as the factors times the sum of those
/// terms without them, plus the rest, that inner sum simplified by `part` (the MBA phase). The
/// whole is a polynomial over what the factor is made of, where the inner sum is linear over
/// the atoms of its terms alone. `None` when no two terms share a factor.
#[cfg(feature = "mba")]
pub(super) fn by_factor(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    part: &mut impl FnMut(&mut Runner<'_, '_>, &mut Context, u32) -> Result<Option<u32>, Stop>,
) -> Result<Option<Step>, Stop> {
    let before = cx.len() as u32;
    let Some(Factored {
        common,
        inner: s,
        rest,
        fin,
    }) = common_factors(r, cx, n)?
    else {
        return Ok(None);
    };
    // The factor is taken out also where `part` leaves the inner sum as it is, when that
    // is smaller: the linear pass's `factor_sum` reads a negated or shared subproduct as a
    // factor of its own, and (tried there on every sum, before the MBA phase has asked about
    // it) taking the factor out first left 23 of 140 measured questions larger.
    let inner = part(r, cx, s)?.unwrap_or(s);
    commit_factored(r, cx, PassKind::Mba, n, &common, inner, &rest, before, fin).map(Some)
}

/// The most terms of a value the factors of [`by_multiplicand`] are read over.
#[cfg(feature = "mba")]
const BASE_TERMS: usize = 8;

/// The non-constant part of `form` as `α · base`, `base`'s terms: the coefficients divided
/// by the power of two they share and by the odd part of the first of them, which is 1 in
/// `base`, so two forms that differ by a constant and an odd scale have one `base`. `None`
/// for a constant or a form of more than [`BASE_TERMS`] terms.
#[cfg(feature = "mba")]
fn scaled_base(form: &Form) -> Option<(BitVec, Vec<(u32, BitVec)>)> {
    use crate::facts::known::{bv_lshr, bv_shl, trailing_zeros};
    let (_, k0) = *form.terms.first()?;
    if form.terms.len() > BASE_TERMS {
        return None;
    }
    let shared = form.terms.iter().map(|(_, k)| trailing_zeros(k)).min()?;
    let odd = bv_lshr(&k0, trailing_zeros(&k0));
    // (Most factors are the value itself or the value and a constant: no division.)
    if shared == 0 && odd == BitVec::one(odd.width()) {
        return Some((odd, form.terms.clone()));
    }
    let inverse = crate::invert::mul_inverse(&odd)?;
    let base = (form.terms.iter())
        .map(|(a, k)| {
            let k = BitVec::bin_unchecked(BinOp::Mul, &bv_lshr(k, shared), &inverse);
            (*a, k)
        })
        .collect();
    Some((bv_shl(&odd, shared), base))
}

/// A value the factors of a sum's products are read over (see [`by_multiplicand`]).
#[cfg(feature = "mba")]
struct Base {
    /// Its terms (see [`scaled_base`]).
    terms: Vec<(u32, BitVec)>,
    /// How many products have a factor over it.
    products: u32,
    /// Whether one of those factors is not the value itself.
    other: bool,
}

/// A product of a sum, as [`by_multiplicand`] reads it.
#[cfg(feature = "mba")]
struct Multiplied {
    /// Its constant.
    konst: BitVec,
    /// Its other factors.
    factors: Vec<u32>,
    /// Of each factor the value it is affine in (its place among the [`Base`]s) with the
    /// scale and the offset (`α`, `β`); `None` for a factor over no one value.
    affine: Vec<Option<(usize, BitVec, BitVec)>>,
}

/// the sum `n` with the products that have a factor affine in one value `t`
/// (`(αᵢ·t + βᵢ)·gᵢ`, each with its coefficient) multiplied out over that factor:
/// `t·Σ αᵢ·gᵢ + (Σ βᵢ·gᵢ + rest)`, each of the two sums simplified by `part` (the MBA
/// phase). `t` is the value most products have such a factor over, an atom of the linear
/// forms or a sum of several (see [`scaled_base`]); a factor that is `t` itself is one of
/// them (`α = 1`, `β = 0`).
///
/// An obfuscator multiplies a linear MBA term by term with values it derives from one
/// value: `(c₁·t + k₁)·(~r ^ y) + (c₂·t + k₂)·(~r & ~y) + ~y·(c₃·(y & r) + k₃)` over a
/// `y = k − t`. The whole is a polynomial over what `t` is made of, a question as large as
/// `t` is; the two cofactor sums are linear MBAs over the atoms of the `gᵢ` alone, and a
/// variable every `gᵢ` reads (`r`) that the sum does not depend on is gone from each.
/// `x·a + x·~a` is the smallest case: the cofactor sum `a + ~a` is `−1`.
///
/// The two sums are `n` by the ring laws alone, whatever `part` makes of them, and the
/// result is committed by the commit rule. `None` when fewer than two products have a
/// factor over one value, or every such factor is the value itself (see [`by_factor`]).
#[cfg(feature = "mba")]
pub(super) fn by_multiplicand(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    part: &mut impl FnMut(&mut Runner<'_, '_>, &mut Context, u32) -> Result<Option<u32>, Stop>,
) -> Result<Option<Step>, Stop> {
    if !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) {
        return Ok(None);
    }
    let form = form_of(r, cx, n)?;
    if form.terms.len() < 2 || form.terms.len() > FACTOR_TERMS {
        return Ok(None);
    }
    // (Read only where two terms are products of values: most sums have none.)
    let product = |t: u32| {
        let node = cx.node(t);
        node.op == OpCode::Mul && !cx.is_const(node.a) && !cx.is_const(node.b)
    };
    if form.terms.iter().filter(|(t, _)| product(*t)).count() < 2 {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, form.terms.len() as u64)?;
    let w = form.konst.width();
    let one = BitVec::one(w);
    let is_comp_node = |cx: &Context, a: u32, b: u32| cx.are_bitwise_complements(a, b);
    let unwrap_masked_xor = |cx: &Context, aid: u32, mask_w: u64| -> Option<(u32, u64, u64)> {
        let an = cx.node(aid);
        if an.op != OpCode::Xor {
            return None;
        }
        let (inner, c) = match (cx.const_val(an.a), cx.const_val(an.b)) {
            (None, Some(k)) => (an.a, k.to_u64()? & mask_w),
            (Some(k), None) => (an.b, k.to_u64()? & mask_w),
            _ => return None,
        };
        let in_node = cx.node(inner);
        if in_node.op == OpCode::And {
            match (cx.const_val(in_node.a), cx.const_val(in_node.b)) {
                (None, Some(m)) if let Some(mv) = m.to_u64() => {
                    return Some((in_node.a, mv & mask_w, c));
                }
                (Some(m), None) if let Some(mv) = m.to_u64() => {
                    return Some((in_node.b, mv & mask_w, c));
                }
                _ => {}
            }
        }
        Some((inner, mask_w, c))
    };
    let mask_w = if w.bits() <= 64 {
        u64::MAX >> (64 - w.bits())
    } else {
        0
    };
    let mut all_or_atoms: Vec<u32> = Vec::new();
    let mut all_xor_atoms: Vec<(u32, u32, u64, u64)> = Vec::new();
    let mut all_zext_xor_atoms: Vec<(u32, u32, u16, u64)> = Vec::new();
    let unwrap_zext_xor = |cx: &Context, aid: u32| -> Option<(u32, u16, u64)> {
        let an = cx.node(aid);
        if an.op != OpCode::Zext {
            return None;
        }
        let iw = cx.wid(an.a);
        if iw == 0 || iw >= an.width || an.width > 64 {
            return None;
        }
        let imask = u64::MAX >> (64 - iw);
        let inner = cx.node(an.a);
        match inner.op {
            OpCode::Xor => match (cx.const_val(inner.a), cx.const_val(inner.b)) {
                (None, Some(k)) => Some((inner.a, iw, k.to_u64()? & imask)),
                (Some(k), None) => Some((inner.b, iw, k.to_u64()? & imask)),
                _ => None,
            },
            OpCode::Not => Some((inner.a, iw, imask)),
            _ => Some((an.a, iw, 0)),
        }
    };
    for &(t, _) in &form.terms {
        if let Some((_, factors)) = scaled_factors(cx, t).filter(|(_, f)| f.len() >= 2) {
            for f in factors {
                let ff = form_of(r, cx, f)?;
                for &(aid, _) in &ff.terms {
                    let an = cx.node(aid);
                    if an.op == OpCode::Or && !all_or_atoms.contains(&aid) {
                        all_or_atoms.push(aid);
                    } else if w.bits() <= 64
                        && an.op == OpCode::Xor
                        && !all_xor_atoms.iter().any(|x| x.0 == aid)
                        && let Some((v_id, m_v, c_v)) = unwrap_masked_xor(cx, aid, mask_w)
                    {
                        all_xor_atoms.push((aid, v_id, m_v, c_v));
                    } else if w.bits() <= 64
                        && an.op == OpCode::Zext
                        && !all_zext_xor_atoms.iter().any(|x| x.0 == aid)
                        && let Some((v_id, iw, c_v)) = unwrap_zext_xor(cx, aid)
                    {
                        all_zext_xor_atoms.push((aid, v_id, iw, c_v));
                    }
                }
            }
        }
    }
    // The values the factors are read over.
    let mut bases: Vec<Base> = Vec::new();
    let mut products: Vec<Option<Multiplied>> = Vec::with_capacity(form.terms.len());
    let mut fin = form.fin;
    for &(t, _) in &form.terms {
        let Some((c, factors)) = scaled_factors(cx, t).filter(|(_, f)| f.len() >= 2) else {
            products.push(None);
            continue;
        };
        let mut affine: Vec<Option<(usize, BitVec, BitVec)>> = Vec::with_capacity(factors.len());
        for &f in &factors {
            let mut ff = form_of(r, cx, f)?;
            r.meter.charge(Counter::PassWork, ff.terms.len() as u64)?;
            // Recognize De Morgan `(~u) & (~v) == -1 - (u | v)`, 1-bit `b ^ C == C ± b`,
            // complementary constant-XOR pairs `(x ^ c2) == K - (x ^ c1)` when `~(c1 ^ c2)` is
            // covered by `known(x)`, and narrow `zext(x ^ ~c) == (2^iw - 1) - zext(x ^ c)`.
            if ff.terms.len() == 1 {
                let (atom0, coef0) = ff.terms[0];
                let fn_node = cx.node(atom0);
                if atom0 == f && coef0 == one && fn_node.op == OpCode::And
                    && let Some(&or_id) = all_or_atoms.iter().find(|&&oid| {
                        let on = cx.node(oid);
                        (is_comp_node(cx, fn_node.a, on.a) && is_comp_node(cx, fn_node.b, on.b))
                            || (is_comp_node(cx, fn_node.a, on.b)
                                && is_comp_node(cx, fn_node.b, on.a))
                    })
                {
                    let neg_one = BitVec::ones(w);
                    let mut dm = Form::of(
                        BitVec::bin_unchecked(BinOp::Sub, &ff.konst, &one),
                        &[(or_id, neg_one)],
                    );
                    dm.fin = ff.fin;
                    ff = dm;
                } else if fn_node.op == OpCode::Zext
                    && w.bits() <= 64
                    && let Some((v_id, iw, c2)) = unwrap_zext_xor(cx, atom0)
                {
                    let imask = u64::MAX >> (64 - iw);
                    if let Some(&(canon_id, _, _, _)) = all_zext_xor_atoms
                        .iter()
                        .find(|&&(aid, vid, aiw, c1)| {
                            aid < atom0 && vid == v_id && aiw == iw && (c1 ^ c2) == imask
                        })
                    {
                        let sum_bv = BitVec::wrapping_from_u64(w, imask);
                        let delta = BitVec::bin_unchecked(BinOp::Mul, &coef0, &sum_bv);
                        let neg_coef = BitVec::un_unchecked(UnOp::Neg, &coef0);
                        let mut zp = Form::of(
                            BitVec::bin_unchecked(BinOp::Add, &ff.konst, &delta),
                            &[(canon_id, neg_coef)],
                        );
                        zp.fin = ff.fin;
                        ff = zp;
                    }
                } else if fn_node.op == OpCode::Xor && w.bits() <= 64 && w.bits() > 1 {
                    let xor_pair = match (cx.const_val(fn_node.a), cx.const_val(fn_node.b)) {
                        (None, Some(k)) => Some((fn_node.a, k)),
                        (Some(k), None) => Some((fn_node.b, k)),
                        _ => None,
                    };
                    if let Some((b_id, k_bv)) = xor_pair {
                        let mask = u64::MAX >> (64 - w.bits());
                        let high_mask = mask & !1u64;
                        let (kw, bfin) = super::known_words(r, cx, b_id)?;
                        if atom0 == f && coef0 == one && kw.is_some_and(|[z, _]| (z & high_mask) == high_mask) {
                            let coef = if k_bv.bit(0) == Some(true) {
                                BitVec::ones(w)
                            } else {
                                one
                            };
                            let mut xb = Form::of(
                                BitVec::bin_unchecked(BinOp::Add, &ff.konst, &k_bv),
                                &[(b_id, coef)],
                            );
                            xb.fin = ff.fin.and(bfin);
                            ff = xb;
                        } else if let Some((v_id, m2, c2)) = unwrap_masked_xor(cx, atom0, mask) {
                            let (vkw, vfin) = if v_id == b_id {
                                (kw, bfin)
                            } else {
                                super::known_words(r, cx, v_id)?
                            };
                            let (kz, ko) = vkw.map_or((0, 0), |[z, o]| (z & mask, o & mask));
                            let known_mask = kz | ko;
                            if let Some(&(canon_id, _, m1, c1)) =
                                all_xor_atoms.iter().find(|&&(aid, vid, m1, c1)| {
                                    if aid >= atom0 || vid != v_id {
                                        return false;
                                    }
                                    let varying =
                                        (!known_mask) & ((m1 ^ m2) | (m1 & m2 & !(c1 ^ c2))) & mask;
                                    varying == 0
                                })
                            {
                                let val1 = ((ko & m1) ^ c1) & mask;
                                let val2 = ((ko & m2) ^ c2) & mask;
                                let sum_u64 = val1.wrapping_add(val2) & mask;
                                let sum_bv = BitVec::wrapping_from_u64(w, sum_u64);
                                let delta = BitVec::bin_unchecked(BinOp::Mul, &coef0, &sum_bv);
                                let neg_coef = BitVec::un_unchecked(UnOp::Neg, &coef0);
                                let mut xp = Form::of(
                                    BitVec::bin_unchecked(BinOp::Add, &ff.konst, &delta),
                                    &[(canon_id, neg_coef)],
                                );
                                xp.fin = ff.fin.and(vfin);
                                ff = xp;
                            } else {
                                fin = fin.and(vfin.unchanged());
                            }
                        }
                    }
                }
            }
            let Some((alpha, base)) = scaled_base(&ff) else {
                affine.push(None);
                continue;
            };
            fin = fin.and(ff.fin);
            let other = alpha != one || !ff.konst.is_zero();
            let at = match bases.iter().position(|b| b.terms == base) {
                Some(at) => at,
                None => {
                    bases.push(Base {
                        terms: base,
                        products: 0,
                        other: false,
                    });
                    bases.len() - 1
                }
            };
            let first = !affine.iter().any(|x| x.is_some_and(|(b, ..)| b == at));
            bases[at].products += u32::from(first);
            bases[at].other |= other;
            affine.push(Some((at, alpha, ff.konst)));
        }
        products.push(Some(Multiplied {
            konst: c,
            factors,
            affine,
        }));
    }
    // The value most products have a factor over (the first met among equals).
    let Some(at) = (0..bases.len())
        .filter(|&i| bases[i].products >= 2 && bases[i].other)
        .max_by_key(|&i| (bases[i].products, core::cmp::Reverse(i)))
    else {
        return Ok(None);
    };
    let before = cx.len() as u32;
    let base = emit(r, cx, &Form::of(BitVec::zero(w), &bases[at].terms))?;
    // `base · scaled + offset`: the cofactors by their factors' scales, and by their offsets
    // with the terms that have no factor over the value.
    let mut scaled = Form::of(BitVec::zero(w), &[]);
    let mut offset = Form::of(form.konst, &[]);
    for (p, &(term, k)) in products.into_iter().zip(&form.terms) {
        let split = p.and_then(|p| {
            let j = (p.affine.iter()).position(|a| a.is_some_and(|(b, ..)| b == at))?;
            let (_, alpha, beta) = p.affine[j]?;
            Some((p.konst, p.factors, j, alpha, beta))
        });
        let Some((c, factors, j, alpha, beta)) = split else {
            offset = offset.add(&Form::of(BitVec::zero(w), &[(term, k)]));
            continue;
        };
        let mut rest: Option<u32> = None;
        for (i, &f) in factors.iter().enumerate() {
            if i == j {
                continue;
            }
            rest = Some(match rest {
                None => f,
                Some(a) => r.build(cx, |cx| cx.c_bin(BinOp::Mul, a, f))?,
            });
        }
        let Some(rest) = rest else {
            super::discard(r, cx, before);
            return Ok(None);
        };
        let g = form_of(r, cx, rest)?;
        let k = BitVec::bin_unchecked(BinOp::Mul, &k, &c);
        scaled = scaled.add(&g.scale(&BitVec::bin_unchecked(BinOp::Mul, &k, &alpha)));
        offset = offset.add(&g.scale(&BitVec::bin_unchecked(BinOp::Mul, &k, &beta)));
    }
    fin = fin.and(scaled.fin).and(offset.fin);
    let mut simplified = |r: &mut Runner<'_, '_>, cx: &mut Context, f: &Form| {
        let e = emit(r, cx, f)?;
        if f.terms.is_empty() {
            return Ok::<u32, Stop>(e);
        }
        Ok(part(r, cx, e)?.unwrap_or(e))
    };
    let a = simplified(r, cx, &scaled)?;
    let b = simplified(r, cx, &offset)?;
    // `base · a + b`, as one sum: a cofactor sum that is a constant scales `base`, whose
    // terms then meet the ones of `b`.
    let product = match cx.const_val(a) {
        Some(c) => form_of(r, cx, base)?.scale(&c),
        None => {
            let m = r.build(cx, |cx| cx.c_bin(BinOp::Mul, base, a))?;
            form_of(r, cx, m)?
        }
    };
    let total = product.add(&form_of(r, cx, b)?);
    fin = fin.and(total.fin);
    let e = emit(r, cx, &total)?;
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
    let mut seen = super::Lease::new(cx.len());
    let mut met = 0usize;
    let mut out = Vec::new();
    let mut todo = vec![e];
    while let Some(i) = todo.pop() {
        if seen.insert(i, 0) {
            continue;
        }
        met += 1;
        if met > MAX_SEEN {
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
    // Whole; or, where that is no simpler, a group of its terms at a time, the sums still
    // atoms (`A + p·q + B − (A & B)` with `A` a sum of products: the whole is a polynomial over
    // what `A` is made of, the group `A + B − (A & B)` is `A | B` over two values).
    let e = match part(r, cx, s)? {
        Some(e) => e,
        None => {
            // (The whole sum is retired first: what it built would count as readers of the
            // groups' nodes.)
            super::discard(r, cx, before);
            match grouped(r, cx, &konst, &terms, form.fin, part)? {
                Some((total, _)) => emit(r, cx, &total)?,
                None => emit(r, cx, &Form::of(konst, &terms))?,
            }
        }
    };
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

#[cfg(test)]
mod extra_tests {
    use crate::{Context, ParseOptions, Width};

    #[test]
    fn linear_additive_select_neg_mul_and_subset_sub() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Pattern 1: select(a, s + k, s) == s + select(a, k, 0)
            "let s = select(b == 0, 100:64, 0); select(a == 0, s + 42, s) == s + select(a == 0, 42:64, 0)",
            // Pattern 2 with complementary sign comparisons (<s 0 vs 0 <=s)
            "select(a == 0, select(x <s 0, 15:64, 10), select(0 <=s x, 0:64, 5)) == select(a == 0, 10:64, 0) + select(x <s 0, 5:64, 0)",
            // Pattern 3 with non-zero konst (~x) and an even multiplier on one arm
            "select(c == 0, ~x * 7 + y * 7, ~x * 4 + y * 4) == (~x + y) * select(c == 0, 7:64, 4)",
            // Neg(Mul(Neg(x), y)) -> x * y
            "-((-x) * y) == x * y",
            // Syntactic bitwise subset subtraction: (a | b) - (c & b) == (a | b) ^ (c & b)
            "(a | b) - (c & b) == (a | b) ^ (c & b)",
        ] {
            let e = cx.parse(text, &opt).unwrap();
            let out = crate::prove::valid_under_with(&mut cx, e, None, &cfg, &prover).unwrap();
            assert!(
                matches!(out, crate::prove::Outcome::Proved(_)),
                "expected Proved for {text}, got {out:?}"
            );
        }
    }

    #[test]
    fn linear_rejects_unsound_select_and_subset_sub() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Pattern 2 with non-additive table (c11 != c10 + c01)
            "select(a == 0, select(b == 0, 16:64, 10), select(b == 0, 5:64, 0)) == select(a == 0, 10:64, 0) + select(b == 0, 5:64, 0)",
            // Pattern 3 with mismatched constant term
            "select(c == 0, ~x * 7 + y * 7 + 1, ~x * 4 + y * 4) == (~x + y) * select(c == 0, 7:64, 4)",
            // Non-subset subtraction is NOT xor
            "(a | b) - (c & d) == (a | b) ^ (c & d)",
        ] {
            let e = cx.parse(text, &opt).unwrap();
            let out = crate::prove::valid_under_with(&mut cx, e, None, &cfg, &prover).unwrap();
            assert!(
                matches!(out, crate::prove::Outcome::Refuted(_)),
                "expected Refuted for {text}, got {out:?}"
            );
        }
    }
}
