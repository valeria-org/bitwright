//! a question's casts taken out, so the normal form sees through them.
//!
//! The normal form works at one width and takes a cast as an atom it cannot see into, so
//! `zext<64>(~trunc<32>(x ^ k) & 39)` is unrelated to `x` there. Lifters write every 32-bit
//! operation of x86 that way, and an MBA spelled over a register and its low half does not
//! simplify.
//!
//! The low `n` bits of `+ − · neg ~ & | ^` and of a left shift by a constant depend only on the
//! low `n` bits of their operands. So every node narrower than the root can be computed at the
//! root's width, with whatever bits above `n` that gives; only a reader of those bits needs
//! them exact: a zero extension, a right shift, a sign extension (through its sign bit) and
//! the root. Exact bits are the low form masked with `2^n − 1`, unless they are already zero
//! (a constant extended with zeros, a conjunction with one, a right shift, an extension). A
//! truncation is then its operand's low form, and the question has no casts but the zero
//! extensions of variables narrower than the root, which stay atoms.
//!
//! The question returned is equal to the input at every input, by the property above. The
//! normal-form solver normalizes it instead of the input, and certificates compare both sides
//! without casts when they do not decide with them.

use super::expr::{MOp, MbaExpr};
use crate::ops::BinOp;
use crate::{BitVec, Width};

/// The question with its casts taken out, when it has any and no node is wider than the root.
pub(crate) fn decast(p: &MbaExpr) -> Option<MbaExpr> {
    let w = p.width()?;
    let nodes = p.nodes();
    if !nodes
        .iter()
        .any(|n| matches!(n.op, MOp::Zext | MOp::Sext | MOp::Trunc))
        || nodes.iter().any(|n| n.width > w)
    {
        return None;
    }
    let mut m = MbaExpr::new(p.vars().to_vec());
    // Per input node: its low form (a node of width `w` whose low bits are the input node's
    // value), whether the bits above the input node's width are zero there, and its exact
    // form once one is built.
    let mut low: Vec<u32> = Vec::with_capacity(nodes.len());
    let mut zero_above: Vec<bool> = Vec::with_capacity(nodes.len());
    let mut exact: Vec<Option<u32>> = vec![None; nodes.len()];
    let mut exact_of =
        |m: &mut MbaExpr, low: &[u32], zero_above: &[bool], i: usize, nw: Width| -> Option<u32> {
            if nw == w || zero_above[i] {
                return Some(low[i]);
            }
            if let Some(e) = exact[i] {
                return Some(e);
            }
            let mask = BitVec::ones(nw).zext(w).ok()?;
            let k = m.push(MOp::Const(mask), &[]).ok()?;
            let e = m.push(MOp::And, &[low[i], k]).ok()?;
            exact[i] = Some(e);
            Some(e)
        };
    for n in nodes {
        let nw = n.width;
        let a = n.args[0] as usize;
        let b = n.args[1] as usize;
        let (v, z) = match n.op {
            MOp::Const(c) => (m.push(MOp::Const(c.zext(w).ok()?), &[]).ok()?, true),
            MOp::Var(k) => {
                let x = m.push(MOp::Var(k), &[]).ok()?;
                if nw == w {
                    (x, true)
                } else {
                    (m.push_cast(MOp::Zext, x, w).ok()?, true)
                }
            }
            MOp::Add | MOp::Sub | MOp::Mul => (m.push(n.op, &[low[a], low[b]]).ok()?, false),
            MOp::And => (
                m.push(n.op, &[low[a], low[b]]).ok()?,
                zero_above[a] || zero_above[b],
            ),
            MOp::Or | MOp::Xor => (
                m.push(n.op, &[low[a], low[b]]).ok()?,
                zero_above[a] && zero_above[b],
            ),
            MOp::Neg | MOp::Not | MOp::Shl(_) => (m.push(n.op, &[low[a]]).ok()?, false),
            MOp::LShr(_) => {
                let e = exact_of(&mut m, &low, &zero_above, a, nodes[a].width)?;
                (m.push(n.op, &[e]).ok()?, true)
            }
            // The low bits of a truncation are its operand's.
            MOp::Trunc => (low[a], false),
            MOp::Zext => (
                exact_of(&mut m, &low, &zero_above, a, nodes[a].width)?,
                true,
            ),
            // `sext(v)` from `s + 1` bits is `(v ^ 2^s) − 2^s` over `v` extended with zeros.
            MOp::Sext => {
                let aw = nodes[a].width;
                let e = exact_of(&mut m, &low, &zero_above, a, aw)?;
                let one = BitVec::wrapping_from_u64(w, 1);
                let by = BitVec::wrapping_from_u64(w, u64::from(aw.bits() - 1));
                let s = BitVec::bin_unchecked(BinOp::Shl, &one, &by);
                let k = m.push(MOp::Const(s), &[]).ok()?;
                let f = m.push(MOp::Xor, &[e, k]).ok()?;
                (m.push(MOp::Sub, &[f, k]).ok()?, nw == w)
            }
        };
        low.push(v);
        zero_above.push(z);
    }
    let r = exact_of(&mut m, &low, &zero_above, nodes.len() - 1, w)?;
    // The root is the last node: a root that is an earlier node (an extension of a value
    // already exact) is added to zero.
    if m.root() != Some(r) {
        let z = m.push(MOp::Const(BitVec::zero(w)), &[]).ok()?;
        m.push(MOp::Add, &[r, z]).ok()?;
    }
    Some(m)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::combine;

    fn same_values(p: &MbaExpr) {
        let d = decast(p).expect("casts");
        assert!(
            d.nodes()
                .iter()
                .all(|n| !matches!(n.op, MOp::Trunc | MOp::Sext))
        );
        for s in 0..64u64 {
            let vals: Vec<BitVec> = p
                .vars()
                .iter()
                .enumerate()
                .map(|(v, &w)| {
                    BitVec::wrapping_from_u64(
                        w,
                        combine(s, v as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15),
                    )
                })
                .collect();
            assert_eq!(p.eval(&vals), d.eval(&vals), "{p:?} at sample {s}");
        }
    }

    #[test]
    fn a_question_without_its_casts_has_its_values() {
        let (w8, w32, w64) = (Width::W8, Width::new(32).unwrap(), Width::W64);
        // `sext(trunc32(x) * 5 + (trunc32(x) >> 3)) + zext(~trunc8(trunc32(x) ^ k)) - y`, and
        // a narrow variable.
        let mut p = MbaExpr::new(vec![w64, w64, Width::new(1).unwrap()]);
        let x = p.push(MOp::Var(0), &[]).unwrap();
        let y = p.push(MOp::Var(1), &[]).unwrap();
        let f = p.push(MOp::Var(2), &[]).unwrap();
        let t = p.push_cast(MOp::Trunc, x, w32).unwrap();
        let five = p
            .push(MOp::Const(BitVec::wrapping_from_u64(w32, 5)), &[])
            .unwrap();
        let m = p.push(MOp::Mul, &[t, five]).unwrap();
        let s = p.push(MOp::LShr(3), &[t]).unwrap();
        let a = p.push(MOp::Add, &[m, s]).unwrap();
        let a = p.push_cast(MOp::Sext, a, w64).unwrap();
        let kk = p
            .push(MOp::Const(BitVec::wrapping_from_u64(w32, 0xdead_beef)), &[])
            .unwrap();
        let xk = p.push(MOp::Xor, &[t, kk]).unwrap();
        let b8 = p.push_cast(MOp::Trunc, xk, w8).unwrap();
        let nb = p.push(MOp::Not, &[b8]).unwrap();
        let z = p.push_cast(MOp::Zext, nb, w64).unwrap();
        let fz = p.push_cast(MOp::Zext, f, w64).unwrap();
        let fz = p.push(MOp::Shl(6), &[fz]).unwrap();
        let r = p.push(MOp::Add, &[a, z]).unwrap();
        let r = p.push(MOp::Sub, &[r, y]).unwrap();
        p.push(MOp::Or, &[r, fz]).unwrap();
        same_values(&p);
    }

    #[test]
    fn a_root_that_is_an_extension_is_the_last_node() {
        let mut p = MbaExpr::new(vec![Width::W64]);
        let x = p.push(MOp::Var(0), &[]).unwrap();
        let t = p.push_cast(MOp::Trunc, x, Width::new(16).unwrap()).unwrap();
        p.push_cast(MOp::Zext, t, Width::W64).unwrap();
        same_values(&p);
    }
}
