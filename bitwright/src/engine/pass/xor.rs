//! The xor pass: `k ⊕ ⊕ᵢ (aᵢ & mᵢ)` over GF(2)^W.
//!
//! A node's form is computed from its operands' forms: `^`, `~x = x ⊕ ones`, `&` with a
//! constant (masks every term), `|` with a constant (`x | c = (x & ~c) ⊕ c`), and `|` of
//! operands the facts prove disjoint. Anything else is an atom with mask all-ones. Forms over
//! [`MAX_TERMS`] atoms are atomized. The form is re-emitted canonically (atoms in the context's
//! order, a full mask as the bare atom, the constant last, an all-ones constant as `~`) and
//! replaces the node only when the region above the atoms gets strictly smaller. Cancels
//! boolean (xor) masking.

use super::{Fin, PassKind, Runner, Step, Stop, facts, finish, worth_building};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::facts::known::{bv_and, bv_not, bv_xor};
use crate::ops::{BinOp, UnOp};

/// The most terms a form keeps before its node is treated as an atom.
pub(crate) const MAX_TERMS: usize = 64;

/// `konst ⊕ ⊕ (atom & mask)`, terms sorted by atom index, no zero masks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Form {
    konst: BitVec,
    terms: Vec<(u32, BitVec)>,
    fin: Fin,
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
    fn atom(n: u32, w: crate::Width) -> Form {
        Form {
            konst: BitVec::zero(w),
            terms: vec![(n, BitVec::ones(w))],
            fin: Fin::FINAL,
        }
    }

    fn is_atom_of(&self, n: u32) -> bool {
        self.konst.is_zero()
            && self.terms.len() == 1
            && self.terms[0].0 == n
            && self.terms[0].1.is_ones()
    }

    fn mask(&self, m: &BitVec) -> Form {
        Form {
            konst: bv_and(&self.konst, m),
            terms: self
                .terms
                .iter()
                .map(|(a, k)| (*a, bv_and(k, m)))
                .filter(|(_, k)| !k.is_zero())
                .collect(),
            fin: self.fin,
        }
    }

    fn xor(&self, o: &Form) -> Form {
        let mut terms = Vec::with_capacity(self.terms.len() + o.terms.len());
        let (mut i, mut j) = (0, 0);
        while i < self.terms.len() || j < o.terms.len() {
            let pick = match (self.terms.get(i), o.terms.get(j)) {
                (Some(a), Some(b)) if a.0 == b.0 => {
                    i += 1;
                    j += 1;
                    (a.0, bv_xor(&a.1, &b.1))
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
            konst: bv_xor(&self.konst, &o.konst),
            terms,
            fin: self.fin.and(o.fin),
        }
    }

    fn xor_const(&self, c: &BitVec) -> Form {
        Form {
            konst: bv_xor(&self.konst, c),
            ..self.clone()
        }
    }
}

fn xor_op(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Xor | OpCode::Not | OpCode::And | OpCode::Or | OpCode::Const
    )
}

fn form_of(r: &mut Runner<'_, '_>, cx: &mut Context, root: u32) -> Result<Form, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.xor.contains(i) {
            continue;
        }
        let node = cx.node(i);
        if !xor_op(node.op) {
            r.xor.insert(i, Form::atom(i, cx.width_of(i)));
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if !r.xor.contains(c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        let f = compute(r, cx, i)?;
        let f = if f.terms.len() > MAX_TERMS {
            r.stats.passes.entry("xor").or_default().atomized += 1;
            Form {
                fin: f.fin,
                ..Form::atom(i, cx.width_of(i))
            }
        } else {
            f
        };
        r.xor.insert(i, f);
    }
    Ok(r.xor.get(root).expect("the root's form was just computed"))
}

fn compute(r: &mut Runner<'_, '_>, cx: &mut Context, i: u32) -> Result<Form, Stop> {
    let node = cx.node(i);
    let w = cx.width_of(i);
    let get =
        |r: &Runner<'_, '_>, j: u32| r.xor.get(j).expect("operands' forms are computed first");
    Ok(match node.op {
        OpCode::Const => Form {
            konst: cx.const_val(i).unwrap_or(BitVec::zero(w)),
            terms: Vec::new(),
            fin: Fin::FINAL,
        },
        OpCode::Xor => get(r, node.a).xor(&get(r, node.b)),
        OpCode::Not => get(r, node.a).xor_const(&BitVec::ones(w)),
        OpCode::And => match (cx.const_val(node.a), cx.const_val(node.b)) {
            (Some(m), _) => get(r, node.b).mask(&m),
            (_, Some(m)) => get(r, node.a).mask(&m),
            _ => Form::atom(i, w),
        },
        OpCode::Or => match (cx.const_val(node.a), cx.const_val(node.b)) {
            (Some(c), _) => get(r, node.b).mask(&bv_not(&c)).xor_const(&c),
            (_, Some(c)) => get(r, node.a).mask(&bv_not(&c)).xor_const(&c),
            _ => {
                let (fa, fina) = facts(r, cx, node.a)?;
                let (fb, finb) = facts(r, cx, node.b)?;
                let disjoint = match (fa, fb) {
                    (Some(a), Some(b)) => {
                        bv_and(&a.known().maybe_one(), &b.known().maybe_one()).is_zero()
                    }
                    _ => false,
                };
                if disjoint {
                    // The form relies on what proved the operands disjoint.
                    let mut f = get(r, node.a).xor(&get(r, node.b));
                    f.fin = f.fin.and(fina).and(finb);
                    f
                } else {
                    Form {
                        fin: fina.and(finb).unchanged(),
                        ..Form::atom(i, w)
                    }
                }
            }
        },
        _ => Form::atom(i, w),
    })
}

/// Whether `form` is emitted as `(⊕ (aᵢ & (mᵢ | k))) | k`: its constant `k` misses every mask
/// (the terms are 0 where `k` is 1, so or and xor agree), and some mask covers everything `k`
/// does not, so that term needs no mask (`x | c`, read as `(x & ~c) ⊕ c`, comes back as itself).
fn or_form(form: &Form) -> bool {
    let k = &form.konst;
    !k.is_zero()
        && form.terms.iter().all(|(_, m)| bv_and(m, k).is_zero())
        && form
            .terms
            .iter()
            .any(|(_, m)| crate::facts::known::bv_or(m, k).is_ones())
}

fn emit(r: &mut Runner<'_, '_>, cx: &mut Context, form: &Form) -> Result<u32, Stop> {
    let or = or_form(form);
    let mut terms = form.terms.clone();
    if or {
        for (_, m) in terms.iter_mut() {
            *m = crate::facts::known::bv_or(m, &form.konst);
        }
    }
    terms.sort_by(|a, b| cx.order(a.0, b.0));
    let mut acc: Option<u32> = None;
    for (a, m) in &terms {
        r.meter.charge(Counter::PassWork, 1)?;
        let t = if m.is_ones() {
            *a
        } else {
            let (a, m) = (*a, *m);
            r.build(cx, |cx| {
                let c = cx.mk_const(&m)?;
                cx.c_bin(BinOp::And, a, c)
            })?
        };
        acc = Some(match acc {
            None => t,
            Some(x) => r.build(cx, |cx| cx.c_bin(BinOp::Xor, x, t))?,
        });
    }
    let k = form.konst;
    r.meter.check()?;
    match acc {
        None => r.build(cx, |cx| cx.mk_const(&k)),
        Some(x) if k.is_zero() => Ok(x),
        Some(x) if or => r.build(cx, |cx| {
            let c = cx.mk_const(&k)?;
            cx.c_bin(BinOp::Or, x, c)
        }),
        Some(x) if k.is_ones() => r.build(cx, |cx| cx.c_un(UnOp::Not, x)),
        Some(x) => r.build(cx, |cx| {
            let c = cx.mk_const(&k)?;
            cx.c_bin(BinOp::Xor, x, c)
        }),
    }
}

/// The xor pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let op = cx.node(n).op;
    if !xor_op(op) || op == OpCode::Const {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let form = form_of(r, cx, n)?;
    if form.is_atom_of(n) {
        return Ok(Step::Normal(form.fin));
    }
    let mut atoms: Vec<u32> = form.terms.iter().map(|t| t.0).collect();
    atoms.sort_unstable();
    // Upper bound (it follows `emit`): a constant and an and per partial mask (masks covering
    // the constant in the or form), an xor per extra term, and the constant (a `~` for
    // all-ones, a constant and an xor or an or otherwise).
    let t = form.terms.len() as u32;
    let or = or_form(&form);
    let masked = form
        .terms
        .iter()
        .filter(|(_, m)| {
            !if or {
                crate::facts::known::bv_or(m, &form.konst).is_ones()
            } else {
                m.is_ones()
            }
        })
        .count() as u32;
    let konst = if t == 0 {
        1
    } else if form.konst.is_zero() {
        0
    } else if form.konst.is_ones() {
        1
    } else {
        2
    };
    let estimate = 2 * masked + t.saturating_sub(1) + konst;
    // A constant always commits (see `shrinks`).
    if !form.terms.is_empty()
        && let Some(f) = worth_building(r, cx, n, &atoms, estimate)?
    {
        r.stats.passes.entry("xor").or_default().rejected_cost += 1;
        return Ok(Step::Normal(form.fin.and(f)));
    }
    let before = cx.len() as u32;
    let e = emit(r, cx, &form)?;
    finish(r, cx, PassKind::Xor, n, e, before, &atoms, form.fin)
}
