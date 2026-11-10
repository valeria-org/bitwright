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

/// The most nodes of an operation [`by_cases`] looks through for selects.
#[cfg(feature = "mba")]
const CASE_NODES: usize = 48;

/// How far below a select's side [`related`] looks for a value another side reads.
#[cfg(feature = "mba")]
const SIDE_DEPTH: u32 = 3;

/// Whether `a` and `b` read one non-constant value within [`SIDE_DEPTH`] operators of each
/// (or are it).
#[cfg(feature = "mba")]
fn related(cx: &Context, a: u32, b: u32) -> bool {
    let below = |root: u32| {
        let mut out: Vec<u32> = Vec::new();
        let mut stack = vec![(root, 0u32)];
        while let Some((i, d)) = stack.pop() {
            if cx.const_val(i).is_some() || out.contains(&i) {
                continue;
            }
            out.push(i);
            if d < SIDE_DEPTH {
                stack.extend(cx.node(i).children().map(|c| (c, d + 1)));
            }
        }
        out
    };
    let seen = below(a);
    below(b).iter().any(|i| seen.contains(i))
}

/// The operation `n` that reads two or more selects on one condition `c`, written as
/// `select(c, E1, E0)`: `E1` and `E0` are `n` with every such select replaced by its side, each
/// simplified by `part` (the MBA phase). An identity written over a value that is a select
/// (`(v | k) + (v & k)`, which is `v + k`) holds on each side, and is hidden once a pass has
/// written one of its terms into the select's sides (`select(c, a & k, b & k)`): the terms then
/// read two selects no test relates. The select replaces the node only when it is smaller;
/// `None` when no two selects of `n` share a condition and read one value on each side.
#[cfg(feature = "mba")]
pub(super) fn by_cases(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    part: &mut impl FnMut(&mut Runner<'_, '_>, &mut Context, u32) -> Result<Option<u32>, Stop>,
) -> Result<Option<super::Step>, Stop> {
    let node = cx.node(n);
    if node.width < 2
        || !matches!(
            node.op,
            OpCode::Add | OpCode::Sub | OpCode::Xor | OpCode::Or | OpCode::And
        )
    {
        return Ok(None);
    }
    // The selects below `n`, through the operators of a fragment and casts.
    let mut selects: Vec<u32> = Vec::new();
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack: Vec<u32> = node.children().collect();
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if seen.len() > CASE_NODES {
            return Ok(None);
        }
        let m = cx.node(i);
        match m.op {
            OpCode::Select => selects.push(i),
            OpCode::Add
            | OpCode::Sub
            | OpCode::Neg
            | OpCode::Not
            | OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Mul
            | OpCode::Shl
            | OpCode::Zext
            | OpCode::Sext
            | OpCode::Extract => stack.extend(m.children()),
            _ => {}
        }
    }
    // A condition two of them read, with sides that read one value: the same value written
    // two ways is what an identity over it reads (selects between unrelated values, or
    // between constants, are left to the passes that merge those).
    let mut found = None;
    'pairs: for (i, &s) in selects.iter().enumerate() {
        let a = cx.node(s);
        for &t in &selects[i + 1..] {
            let b = cx.node(t);
            if a.a == b.a && related(cx, a.b, b.b) && related(cx, a.c, b.c) {
                found = Some(a.a);
                break 'pairs;
            }
        }
    }
    let Some(c) = found else {
        return Ok(None);
    };
    r.meter
        .charge(crate::engine::budget::Counter::PassWork, seen.len() as u64)?;
    let before = cx.len() as u32;
    let mut side =
        |r: &mut Runner<'_, '_>, cx: &mut Context, then: bool| -> Result<Option<u32>, Stop> {
            let mut repl: IdMap<u32, u32> = IdMap::default();
            for &s in &selects {
                let m = cx.node(s);
                if m.a == c {
                    repl.insert(s, if then { m.b } else { m.c });
                }
            }
            let e = r.build(cx, |cx| Ok(cx.substitute_ids(&[n], &repl)?[0]))?;
            part(r, cx, e)
        };
    // Only where each side is an identity the MBA phase reads: a split of any operation
    // over two selects, taken where it was smaller, left 38 of 140 measured questions larger
    // (the selects' sides are shared with what the rounds after would have folded).
    let (Some(e1), Some(e0)) = (side(r, cx, true)?, side(r, cx, false)?) else {
        super::discard(r, cx, before);
        return Ok(None);
    };
    let e = r.build(cx, |cx| cx.c_select(c, e1, e0))?;
    // The nodes from before the rewrite that it reads.
    let mut stops = Vec::new();
    let mut seen: IdMap<u32, ()> = IdMap::default();
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
    super::finish(
        r,
        cx,
        super::PassKind::Mba,
        n,
        e,
        before,
        &stops,
        Fin::FINAL,
    )
    .map(Some)
}
