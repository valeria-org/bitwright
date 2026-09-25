//! Case splits on a condition mask (called by the linear pass): an operation that reads a
//! value which is all ones or zero by a 1-bit condition `c` (`sext(c)`, `-zext(c)`, the sign
//! mask `x >>s (W − 1)` of `x <s 0`) is `select(c, E1, E0)`, with `E1` and `E0` the operation
//! with the mask replaced by all ones and by zero, each in linear normal form. Branchless code
//! spells choices this way: `(x ^ m) - m` negates `x` exactly when `m` is all ones, so it is
//! `select(c, -x, x)`. The select replaces the node only when it is smaller.

use super::{Fin, Runner, Stop, linear};
use crate::BitVec;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::CmpOp;

/// A mask of a condition among the operands of `n` (and theirs): the mask node and its
/// condition (`None` when the condition is the sign of the mask's operand, built on demand).
fn mask_in(cx: &Context, n: u32) -> Option<(u32, Option<u32>)> {
    let is_mask = |m: u32| -> Option<(u32, Option<u32>)> {
        let node = cx.node(m);
        if node.width < 2 {
            return None;
        }
        match node.op {
            OpCode::Sext if cx.wid(node.a) == 1 => Some((m, Some(node.a))),
            OpCode::Neg => {
                let z = cx.node(node.a);
                (z.op == OpCode::Zext && cx.wid(z.a) == 1).then_some((m, Some(z.a)))
            }
            OpCode::AShr => (cx.const_val(node.b).and_then(|v| v.to_u64())
                == Some(u64::from(node.width) - 1))
            .then_some((m, None)),
            _ => None,
        }
    };
    let node = cx.node(n);
    for c in node.children() {
        if let Some(m) = is_mask(c) {
            return Some(m);
        }
        for g in cx.node(c).children() {
            if let Some(m) = is_mask(g) {
                return Some(m);
            }
        }
    }
    None
}

/// `n` split on a condition mask it reads, in linear normal form per case, if that is a
/// select: `(select, atoms, finality)`.
pub(super) fn split(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<(u32, Fin)>, Stop> {
    let node = cx.node(n);
    if node.width < 2
        || !matches!(
            node.op,
            OpCode::Add | OpCode::Sub | OpCode::Xor | OpCode::Or | OpCode::And
        )
    {
        return Ok(None);
    }
    let Some((m, cond)) = mask_in(cx, n) else {
        return Ok(None);
    };
    let mut fin = Fin::FINAL;
    let mut arm = |r: &mut Runner<'_, '_>, cx: &mut Context, v: BitVec| -> Result<u32, Stop> {
        let k = r.build(cx, |cx| cx.mk_const(&v))?;
        let mut repl: IdMap<u32, u32> = IdMap::default();
        repl.insert(m, k);
        let e = r.build(cx, |cx| Ok(cx.substitute_ids(&[n], &repl)?[0]))?;
        if !matches!(
            cx.node(e).op,
            OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Not | OpCode::Xor | OpCode::Or
        ) {
            return Ok(e);
        }
        let form = linear::form_of(r, cx, e)?;
        fin = fin.and(form.fin);
        if form.is_atom_of(e) {
            return Ok(e);
        }
        linear::emit(r, cx, &form)
    };
    // The mask's own width (it may be an operand of an operand of another width).
    let mw = cx.width_of(m);
    let e1 = arm(r, cx, BitVec::ones(mw))?;
    let e0 = arm(r, cx, BitVec::zero(mw))?;
    let c = match cond {
        Some(c) => c,
        None => {
            let x = cx.node(m).a;
            r.build(cx, |cx| {
                let z = cx.mk_const(&BitVec::zero(mw))?;
                cx.c_cmp(CmpOp::Slt, x, z)
            })?
        }
    };
    let s = r.build(cx, |cx| cx.c_select(c, e1, e0))?;
    Ok(Some((s, fin)))
}
