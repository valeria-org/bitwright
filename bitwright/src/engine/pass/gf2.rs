//! Linear maps over GF(2) (called by the xor pass): an expression built from one atom `x` by
//! `^`, `~`, masks, shifts and rotations by constants, byte swaps and bit reversals is
//! `M·x ⊕ c` over GF(2), and `M` is, uniquely, the xor of rotations of `x` masked by its
//! diagonals: `⊕_k (rotl(x, k) & d_k)`. That form is emitted, each term as the rotation, shift
//! or mask it is, when it is smaller: an involution such as `y ^ (y >>u 5) ^ (y >>u 7)` with
//! `y = x ^ (x >>u 5) ^ (x >>u 7)` is `x`, and rotations composed with xors of themselves
//! cancel.

use super::{PassKind, Runner, Step, Stop, finish, worth_building};
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::invert::gf2;
use crate::ops::BinOp;
use crate::{BitVec, Width};

/// The most nodes of the expression.
const MAX_NODES: usize = 64;

/// Whether `op` is linear over GF(2) at one width (masks and counts checked later).
fn linear_op(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Xor
            | OpCode::Not
            | OpCode::And
            | OpCode::Or
            | OpCode::Shl
            | OpCode::LShr
            | OpCode::AShr
            | OpCode::RotL
            | OpCode::RotR
            | OpCode::Bswap
            | OpCode::BitRev
    )
}

/// The operands of linear node `node` that are part of its linear map (not shift counts).
fn linear_operands(node: &crate::expr::Node) -> impl Iterator<Item = u32> + '_ {
    let counted = matches!(
        node.op,
        OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR
    );
    node.children().filter(move |&c| !(counted && c == node.b))
}

/// Whether the linear part below `n` reads a single atom, from its operands' answers
/// (remembered for the call, per node): `u32::MAX` when it reads several.
fn one_atom(r: &mut Runner<'_, '_>, cx: &Context, n: u32) -> u32 {
    const MANY: u32 = u32::MAX;
    const NONE: u32 = u32::MAX - 1;
    // (Not a node: arenas stay below it.)
    const UNKNOWN: u32 = u32::MAX - 2;
    let memo = &mut r.gf2_atoms;
    if memo.len() < cx.len() {
        memo.resize(cx.len(), UNKNOWN);
    }
    let known = |memo: &Vec<u32>, i: u32| Some(memo[i as usize]).filter(|&a| a != UNKNOWN);
    let set = |memo: &mut Vec<u32>, i: u32, a: u32| memo[i as usize] = a;
    if let Some(a) = known(memo, n) {
        return a;
    }
    let mut stack = std::mem::take(&mut r.gf2_stack);
    let memo = &mut r.gf2_atoms;
    stack.clear();
    stack.push((n, false));
    let w = cx.wid(n);
    while let Some((i, done)) = stack.pop() {
        if known(memo, i).is_some() {
            continue;
        }
        let node = cx.node(i);
        if cx.const_val(i).is_some() {
            set(memo, i, NONE);
            continue;
        }
        if !linear_op(node.op) || node.width != w {
            set(memo, i, i);
            continue;
        }
        if !done {
            stack.push((i, true));
            for c in linear_operands(&node) {
                if known(memo, c).is_none() {
                    stack.push((c, false));
                }
            }
            continue;
        }
        let mut atom = NONE;
        for c in linear_operands(&node) {
            let a = known(memo, c).unwrap_or(MANY);
            atom = match (atom, a) {
                (_, MANY) | (MANY, _) => MANY,
                (NONE, a) => a,
                (x, NONE) => x,
                (x, a) if x == a => x,
                _ => MANY,
            };
        }
        set(memo, i, atom);
    }
    r.gf2_stack = stack;
    known(&r.gf2_atoms, n).unwrap_or(MANY)
}

/// The one atom below `n` and the nodes between (ascending), if the expression is a linear map
/// of one atom with something to gain (a shift, rotation or permutation of the atom).
fn region(cx: &Context, n: u32) -> Option<(u32, Vec<u32>)> {
    let w = cx.wid(n);
    let mut atom: Option<u32> = None;
    let mut nodes: Vec<u32> = Vec::new();
    let mut stack = vec![n];
    let mut seen: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    let mut moves = false;
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        let node = cx.node(i);
        if cx.const_val(i).is_some() {
            continue;
        }
        if !linear_op(node.op) || node.width != w {
            match atom {
                None => atom = Some(i),
                Some(a) if a == i => {}
                Some(_) => return None,
            }
            continue;
        }
        moves |= matches!(
            node.op,
            OpCode::Shl
                | OpCode::LShr
                | OpCode::AShr
                | OpCode::RotL
                | OpCode::RotR
                | OpCode::Bswap
                | OpCode::BitRev
        );
        nodes.push(i);
        if nodes.len() > MAX_NODES {
            return None;
        }
        for c in node.children() {
            // Counts are part of their operation.
            if matches!(
                node.op,
                OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR
            ) && c == node.b
            {
                cx.const_val(c)?;
                continue;
            }
            stack.push(c);
        }
    }
    let atom = atom?;
    if !moves || nodes.len() < 2 {
        return None;
    }
    nodes.sort_unstable();
    Some((atom, nodes))
}

/// One term of the diagonal form: `rotl(x, k) & d`.
fn term(cx: &mut Context, x: u32, k: u32, d: &BitVec, w: Width) -> Result<u32, crate::Error> {
    let wb = u32::from(w.bits());
    let ones = BitVec::ones(w);
    let count = |cx: &mut Context, v: u32| cx.mk_const(&BitVec::wrapping_from_u64(w, u64::from(v)));
    if k == 0 {
        if d.is_ones() {
            return Ok(x);
        }
        let m = cx.mk_const(d)?;
        return cx.c_bin(BinOp::And, x, m);
    }
    let shl_mask = BitVec::apply_bin(
        BinOp::Shl,
        &ones,
        &BitVec::wrapping_from_u64(w, u64::from(k)),
    )
    .unwrap_or(ones);
    let low_mask = BitVec::apply_un(crate::UnOp::Not, &shl_mask).unwrap_or(ones);
    if *d == shl_mask {
        let c = count(cx, k)?;
        return cx.c_bin(BinOp::Shl, x, c);
    }
    if *d == low_mask {
        let c = count(cx, wb - k)?;
        return cx.c_bin(BinOp::LShr, x, c);
    }
    let c = count(cx, k)?;
    let r = cx.c_bin(BinOp::RotL, x, c)?;
    if d.is_ones() {
        return Ok(r);
    }
    let m = cx.mk_const(d)?;
    cx.c_bin(BinOp::And, r, m)
}

/// The xor pass's linear reading of `n`, if it applies.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Option<Step>, Stop> {
    let w = cx.width_of(n);
    // (A node not linear itself is its own atom, with no region.)
    if w.bits() > 128 || w.bits() < 2 || !linear_op(cx.node(n).op) {
        return Ok(None);
    }
    // Most regions read several atoms: known at once from the operands.
    if one_atom(r, cx, n) >= u32::MAX - 1 {
        return Ok(None);
    }
    let Some((x, nodes)) = region(cx, n) else {
        return Ok(None);
    };
    // A form of one term costs 4 nodes, and replacing `n` frees at most the region's operators
    // and their constant operands (see below): too small a region never pays.
    if 2 * nodes.len() <= 4 {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, nodes.len() as u64 * 4)?;
    let Some(map) = gf2::rows(cx, x, &nodes) else {
        return Ok(None);
    };
    let Some(rows) = map.get(&n) else {
        return Ok(None);
    };
    let wb = usize::from(w.bits());
    let Some(c) = crate::invert::eval_region(cx, &nodes, x, &BitVec::zero(w)) else {
        return Ok(None);
    };
    // The diagonals: d_k has bit i when output bit i reads input bit (i − k) mod W.
    let mut terms: Vec<(u32, BitVec)> = Vec::new();
    for k in 0..wb {
        let mut limbs = [0u64; 8];
        for (i, row) in rows.iter().enumerate() {
            let j = (i + wb - k) % wb;
            if row >> j & 1 == 1 {
                limbs[i / 64] |= 1 << (i % 64);
            }
        }
        let d = BitVec::wrapping_from_limbs(w, &limbs);
        if !d.is_zero() {
            terms.push((k as u32, d));
        }
    }
    // Each term is at most a rotation or shift with its count, a mask; an xor joins each.
    let estimate = terms.len() as u32 * 4 + if c.is_zero() { 0 } else { 2 };
    // Replacing `n` frees at most the region's operators and their constant operands: a
    // form this large can never pay (and the xor pass goes on either way).
    if estimate >= 2 * nodes.len() as u32 {
        return Ok(None);
    }
    if let Some(f) = worth_building(r, cx, n, &[x], estimate)? {
        return Ok(Some(Step::Normal(f)));
    }
    let before = cx.len() as u32;
    let e = r.build(cx, |cx| {
        let mut acc: Option<u32> = None;
        for (k, d) in &terms {
            let t = term(cx, x, *k, d, w)?;
            acc = Some(match acc {
                None => t,
                Some(a) => cx.c_bin(BinOp::Xor, a, t)?,
            });
        }
        let body = match acc {
            Some(a) => a,
            None => return cx.mk_const(&c),
        };
        if c.is_zero() {
            Ok(body)
        } else {
            let k = cx.mk_const(&c)?;
            cx.c_bin(BinOp::Xor, body, k)
        }
    })?;
    Ok(Some(finish(
        r,
        cx,
        PassKind::Xor,
        n,
        e,
        before,
        &[x],
        super::Fin::FINAL,
    )?))
}
