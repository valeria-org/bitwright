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
//! To the certificates, a register read through its low bits only is a narrow variable too
//! ([`decast_narrow`]). When the root depends on the low `n` bits of a root-width variable `x`
//! alone (every path from `x` to the root passes a truncation or a mask to `n` bits before
//! anything reads higher bits: the demanded bits of `x` are a low prefix), `x` is replaced by
//! the atom `zext(trunc<n>(x))`, which agrees with it on those bits, and the masks to `n` bits
//! over values known zero above `n` are dropped. The question over `trunc<32>(x)` and
//! `x & 0xffffffff` is then the question over a 32-bit variable, which the certificates take
//! as a polynomial over atoms, not a register behind masks (two bit classes, no polynomial
//! test). The solver's normal form keeps the registers (see [`decast_narrow`]).
//!
//! The question returned is equal to the input at every input, by the properties above. The
//! normal-form solver normalizes it instead of the input, and certificates compare both sides
//! without casts when they do not decide with them.

use super::expr::{MOp, MbaExpr};
use crate::ops::BinOp;
use crate::{BitVec, Width};

/// The number of low bits of each node the root depends on (0 for a node nothing reads):
/// arithmetic and bitwise operators pass their demand down, a left shift lowers it, a right
/// shift raises it, a mask to a constant caps it at the constant's length, a truncation keeps
/// it, extensions cap it at the operand's width (a sign extension read above its operand reads
/// the whole operand). A prefix, so a demand within the low bits is never missed.
fn demanded(p: &MbaExpr) -> (Vec<u16>, Vec<u16>) {
    let nodes = p.nodes();
    let mut d = vec![0u16; nodes.len()];
    // The least any reader demands (`u16::MAX` where nothing reads the node).
    let mut least = vec![u16::MAX; nodes.len()];
    if let Some(root) = nodes.last() {
        d[nodes.len() - 1] = root.width.bits();
        least[nodes.len() - 1] = root.width.bits();
    }
    for i in (0..nodes.len()).rev() {
        let n = nodes[i];
        let need = d[i];
        if need == 0 {
            continue;
        }
        let (a, b) = (n.args[0] as usize, n.args[1] as usize);
        let mut raise = |k: usize, by: u16| {
            let cap = nodes[k].width.bits();
            let by = by.min(cap);
            d[k] = d[k].max(by);
            if by > 0 {
                least[k] = least[k].min(by);
            }
        };
        match n.op {
            MOp::Const(_) | MOp::Var(_) => {}
            MOp::Add | MOp::Sub | MOp::Mul | MOp::Or | MOp::Xor => {
                raise(a, need);
                raise(b, need);
            }
            MOp::And => {
                // A mask reads of the other operand only the bits it keeps.
                let len = |k: usize| match nodes[k].op {
                    MOp::Const(c) => Some(bit_length(&c)),
                    _ => None,
                };
                raise(a, len(b).map_or(need, |l| need.min(l)));
                raise(b, len(a).map_or(need, |l| need.min(l)));
            }
            MOp::Neg | MOp::Not | MOp::Trunc => raise(a, need),
            MOp::Shl(k) => raise(a, need.saturating_sub(k)),
            MOp::LShr(k) => raise(a, need.saturating_add(k)),
            MOp::Zext => raise(a, need),
            MOp::Sext => {
                let aw = nodes[a].width.bits();
                raise(a, if need > aw { aw } else { need });
            }
        }
    }
    (d, least)
}

/// The number of low bits that may be set in `c` (0 for zero).
fn bit_length(c: &BitVec) -> u16 {
    let w = c.width().bits();
    let clz = BitVec::apply_un(crate::ops::UnOp::Clz, c)
        .ok()
        .and_then(|v| v.to_u64())
        .unwrap_or(u64::from(w));
    w.saturating_sub(clz as u16)
}

/// Per node: the width `n` of the narrow atom `zext(trunc<n>(x))` a root-width variable node
/// `x` stands for, when every reader of the variable demands the same strict low prefix of
/// its bits, in a question that multiplies two non-constants. A variable read at several
/// widths (`trunc<8>(x)` beside `trunc<32>(x)`) stays a register behind masks: an atom of the
/// widest read would leave the narrower masks in place, bit classes over an atom the tests
/// cannot see into. A question without a product keeps its registers too: the signature and
/// the bit classes decide it over the masks, and over atoms a test would spend a try on
/// independent values of `zext(trunc<1>(z))` where the mask said `z & 1` is 0 or 1. A
/// polynomial question is different: masks take it out of the fragment the polynomial
/// certificates and the symbolic comparison decide, and atoms put it back.
fn narrow_registers(p: &MbaExpr, w: Width) -> Vec<Option<Width>> {
    let nodes = p.nodes();
    let polynomial = nodes.iter().any(|n| {
        n.op == MOp::Mul
            && n.args[..2]
                .iter()
                .all(|&k| !matches!(nodes[k as usize].op, MOp::Const(_)))
    });
    if !polynomial {
        return vec![None; nodes.len()];
    }
    let (d, least) = demanded(p);
    // Per variable: the most and the least demanded over its nodes' readers.
    let mut per_var: Vec<(u16, u16)> = vec![(0, u16::MAX); p.vars().len()];
    for (i, n) in nodes.iter().enumerate() {
        if let MOp::Var(v) = n.op
            && n.width == w
            && d[i] > 0
            && let Some(m) = per_var.get_mut(v as usize)
        {
            m.0 = m.0.max(d[i]);
            m.1 = m.1.min(least[i]);
        }
    }
    nodes
        .iter()
        .map(|n| match n.op {
            MOp::Var(v) if n.width == w => {
                let (most, least) = per_var.get(v as usize).copied().unwrap_or((0, 0));
                (most > 0 && most == least && most < w.bits())
                    .then(|| Width::new(most).ok())
                    .flatten()
            }
            _ => None,
        })
        .collect()
}

/// The question with its casts taken out, when it has any and no node is wider than the root.
pub(crate) fn decast(p: &MbaExpr) -> Option<MbaExpr> {
    decast_in(p, false).map(|(m, _)| m)
}

/// [`decast`], with the registers read through their low bits only made narrow atoms (see
/// the module notes), and whether any was: for the certificates. The solver's normal form
/// keeps the registers: over the masks its bit classes know `z & 1` is 0 or 1 where an atom
/// `zext(trunc<1>(z))` is opaque to them, and a semi-linear question renders with one mask
/// over the whole where atoms would carry one each.
pub(crate) fn decast_narrow(p: &MbaExpr) -> Option<(MbaExpr, bool)> {
    decast_in(p, true)
}

fn decast_in(p: &MbaExpr, narrowing: bool) -> Option<(MbaExpr, bool)> {
    let w = p.width()?;
    let nodes = p.nodes();
    if nodes.iter().any(|n| n.width > w) {
        return None;
    }
    let narrow = if narrowing {
        narrow_registers(p, w)
    } else {
        vec![None; nodes.len()]
    };
    let narrowed = narrow.iter().any(Option::is_some);
    if !nodes
        .iter()
        .any(|n| matches!(n.op, MOp::Zext | MOp::Sext | MOp::Trunc))
        && !narrowed
    {
        return None;
    }
    let mut m = MbaExpr::new(p.vars().to_vec());
    // Per input node: its low form (a node of width `w` whose low bits are the input node's
    // value), the bit index from which the low form is known to be zero (`None`: unknown; `w`
    // says nothing), and its exact form once one is built.
    let mut low: Vec<u32> = Vec::with_capacity(nodes.len());
    let mut zeros_from: Vec<Option<u16>> = Vec::with_capacity(nodes.len());
    let mut exact: Vec<Option<u32>> = vec![None; nodes.len()];
    let wb = w.bits();
    let mut exact_of =
        |m: &mut MbaExpr, low: &[u32], zf: &[Option<u16>], i: usize, nw: Width| -> Option<u32> {
            if nw == w || zf[i].is_some_and(|z| z <= nw.bits()) {
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
    // Whether input node `k` is a constant equal to the low mask of `n` bits.
    let lowmask_of = |k: usize| -> Option<u16> {
        match nodes[k].op {
            MOp::Const(c) => {
                let n = bit_length(&c);
                (n > 0
                    && n < c.width().bits()
                    && c == BitVec::ones(Width::new(n).ok()?).zext(c.width()).ok()?)
                .then_some(n)
            }
            _ => None,
        }
    };
    for (i, n) in nodes.iter().enumerate() {
        let nw = n.width;
        let a = n.args[0] as usize;
        let b = n.args[1] as usize;
        let (v, z): (u32, Option<u16>) = match n.op {
            MOp::Const(c) => (
                m.push(MOp::Const(c.zext(w).ok()?), &[]).ok()?,
                Some(bit_length(&c)),
            ),
            MOp::Var(k) => {
                let x = m.push(MOp::Var(k), &[]).ok()?;
                match narrow[i] {
                    // A register read through its low `n` bits only: the atom `zext(trunc<n>(x))`.
                    Some(nn) => {
                        let t = m.push_cast(MOp::Trunc, x, nn).ok()?;
                        (m.push_cast(MOp::Zext, t, w).ok()?, Some(nn.bits()))
                    }
                    None if nw == w => (x, None),
                    None => (m.push_cast(MOp::Zext, x, w).ok()?, Some(nw.bits())),
                }
            }
            MOp::Add | MOp::Sub | MOp::Mul => (m.push(n.op, &[low[a], low[b]]).ok()?, None),
            MOp::And => {
                // A mask to `n` bits over a value known zero from `n` on changes nothing.
                let dropped = match (lowmask_of(a), lowmask_of(b)) {
                    (Some(k), _) if zeros_from[b].is_some_and(|z| z <= k) => Some(b),
                    (_, Some(k)) if zeros_from[a].is_some_and(|z| z <= k) => Some(a),
                    _ => None,
                };
                match dropped {
                    Some(t) => (low[t], zeros_from[t]),
                    None => (
                        m.push(n.op, &[low[a], low[b]]).ok()?,
                        match (zeros_from[a], zeros_from[b]) {
                            (Some(x), Some(y)) => Some(x.min(y)),
                            (x, y) => x.or(y),
                        },
                    ),
                }
            }
            MOp::Or | MOp::Xor => (
                m.push(n.op, &[low[a], low[b]]).ok()?,
                match (zeros_from[a], zeros_from[b]) {
                    (Some(x), Some(y)) => Some(x.max(y)),
                    _ => None,
                },
            ),
            MOp::Neg | MOp::Not | MOp::Shl(_) => (m.push(n.op, &[low[a]]).ok()?, None),
            MOp::LShr(k) => {
                let e = exact_of(&mut m, &low, &zeros_from, a, nodes[a].width)?;
                (
                    m.push(n.op, &[e]).ok()?,
                    Some(nodes[a].width.bits().saturating_sub(k)),
                )
            }
            // The low bits of a truncation are its operand's; what is known zero of the
            // operand's low form below the truncation's width stays known.
            MOp::Trunc => (low[a], zeros_from[a].filter(|&z| z <= nw.bits())),
            MOp::Zext => (
                exact_of(&mut m, &low, &zeros_from, a, nodes[a].width)?,
                Some(nodes[a].width.bits()),
            ),
            // `sext(v)` from `s + 1` bits is `(v ^ 2^s) − 2^s` over `v` extended with zeros.
            MOp::Sext => {
                let aw = nodes[a].width;
                let e = exact_of(&mut m, &low, &zeros_from, a, aw)?;
                let one = BitVec::wrapping_from_u64(w, 1);
                let by = BitVec::wrapping_from_u64(w, u64::from(aw.bits() - 1));
                let s = BitVec::bin_unchecked(BinOp::Shl, &one, &by);
                let k = m.push(MOp::Const(s), &[]).ok()?;
                let f = m.push(MOp::Xor, &[e, k]).ok()?;
                (m.push(MOp::Sub, &[f, k]).ok()?, None)
            }
        };
        low.push(v);
        zeros_from.push(z.map(|z| z.min(wb)));
    }
    let r = exact_of(&mut m, &low, &zeros_from, nodes.len() - 1, w)?;
    // The root is the last node: a root that is an earlier node (an extension of a value
    // already exact, a mask dropped) is added to zero.
    if m.root() != Some(r) {
        let z = m.push(MOp::Const(BitVec::zero(w)), &[]).ok()?;
        m.push(MOp::Add, &[r, z]).ok()?;
    }
    Some((m, narrowed))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::combine;

    /// Checks `decast(p)` against `p` at 64 seeded points; the result has no sign extension
    /// and no truncation but the one inside a narrow register's atom `zext(trunc(x))`.
    fn same_values(p: &MbaExpr) -> MbaExpr {
        let (d, narrowed) = decast_narrow(p).expect("casts");
        // The solver's reading narrows nothing, and agrees too.
        let plain = decast(p);
        assert_eq!(
            plain.is_some(),
            !narrowed
                || p.nodes()
                    .iter()
                    .any(|n| matches!(n.op, MOp::Zext | MOp::Sext | MOp::Trunc))
        );
        if let Some(plain) = &plain {
            assert!(!plain.nodes().iter().any(|n| n.op == MOp::Trunc));
        }
        let nodes = d.nodes();
        assert!(nodes.iter().all(|n| n.op != MOp::Sext));
        for (i, n) in nodes.iter().enumerate() {
            if n.op == MOp::Trunc {
                assert!(
                    nodes
                        .iter()
                        .any(|u| u.op == MOp::Zext && u.args[0] as usize == i),
                    "a truncation outside an atom in {d:?}"
                );
                assert!(matches!(nodes[n.args[0] as usize].op, MOp::Var(_)));
            }
        }
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
            if let Some(plain) = &plain {
                assert_eq!(p.eval(&vals), plain.eval(&vals), "{p:?} at sample {s}");
            }
        }
        d
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

    /// `((x & y) & M) · ((x | y) & M)` with `M` the low 32 bits: `x` and `y` are read through
    /// their low halves only, so they become narrow atoms and the masks go.
    #[test]
    fn registers_read_through_masks_are_narrow_atoms() {
        let w = Width::W64;
        let mut p = MbaExpr::new(vec![w, w]);
        let x = p.push(MOp::Var(0), &[]).unwrap();
        let y = p.push(MOp::Var(1), &[]).unwrap();
        let mask = p
            .push(MOp::Const(BitVec::wrapping_from_u64(w, 0xffff_ffff)), &[])
            .unwrap();
        let and = p.push(MOp::And, &[x, y]).unwrap();
        let and = p.push(MOp::And, &[and, mask]).unwrap();
        let or = p.push(MOp::Or, &[x, y]).unwrap();
        let or = p.push(MOp::And, &[or, mask]).unwrap();
        p.push(MOp::Mul, &[and, or]).unwrap();
        let d = same_values(&p);
        let ops: Vec<MOp> = d.nodes().iter().map(|n| n.op).collect();
        assert_eq!(ops.iter().filter(|o| **o == MOp::Trunc).count(), 2);
        assert_eq!(ops.iter().filter(|o| **o == MOp::Zext).count(), 2);
        // The masks are gone: the only `And` left is `x & y` (the mask constant is pushed,
        // unused).
        assert_eq!(ops.iter().filter(|o| **o == MOp::And).count(), 1);
        assert!(!d.nodes().iter().any(|n| {
            n.op == MOp::And
                && n.args
                    .iter()
                    .any(|&a| matches!(ops[a as usize], MOp::Const(_)))
        }));
    }

    /// A register also read whole stays a register: `(x & M) + x`.
    #[test]
    fn a_register_read_whole_is_not_narrowed() {
        let w = Width::W64;
        let mut p = MbaExpr::new(vec![w]);
        let x = p.push(MOp::Var(0), &[]).unwrap();
        let mask = p
            .push(MOp::Const(BitVec::wrapping_from_u64(w, 0xffff_ffff)), &[])
            .unwrap();
        let t = p.push_cast(MOp::Trunc, x, Width::new(32).unwrap()).unwrap();
        let z = p.push_cast(MOp::Zext, t, w).unwrap();
        let _ = mask;
        p.push(MOp::Add, &[z, x]).unwrap();
        let d = same_values(&p);
        assert!(!d.nodes().iter().any(|n| n.op == MOp::Trunc));
    }

    /// Two widths of reads keep the register: `trunc<8>(x) · trunc<32>(x)` over `x`, both
    /// extended, stays a question over `x` behind masks.
    #[test]
    fn reads_at_two_widths_keep_the_register() {
        let w = Width::W64;
        let mut p = MbaExpr::new(vec![w]);
        let x = p.push(MOp::Var(0), &[]).unwrap();
        let t8 = p.push_cast(MOp::Trunc, x, Width::W8).unwrap();
        let t32 = p.push_cast(MOp::Trunc, x, Width::new(32).unwrap()).unwrap();
        let z8 = p.push_cast(MOp::Zext, t8, w).unwrap();
        let z32 = p.push_cast(MOp::Zext, t32, w).unwrap();
        p.push(MOp::Mul, &[z8, z32]).unwrap();
        let d = same_values(&p);
        assert!(!d.nodes().iter().any(|n| n.op == MOp::Trunc));
    }

    /// A shift right reads higher bits: `((x >> 8) & 0xff) · (y & 0xffff)` reads the low 16
    /// bits of `x` and of `y`.
    #[test]
    fn a_right_shift_raises_the_demand() {
        let w = Width::W64;
        let mut p = MbaExpr::new(vec![w, w]);
        let x = p.push(MOp::Var(0), &[]).unwrap();
        let y = p.push(MOp::Var(1), &[]).unwrap();
        let s = p.push(MOp::LShr(8), &[x]).unwrap();
        let mask = p
            .push(MOp::Const(BitVec::wrapping_from_u64(w, 0xff)), &[])
            .unwrap();
        let hx = p.push(MOp::And, &[s, mask]).unwrap();
        let mask16 = p
            .push(MOp::Const(BitVec::wrapping_from_u64(w, 0xffff)), &[])
            .unwrap();
        let ly = p.push(MOp::And, &[y, mask16]).unwrap();
        p.push(MOp::Mul, &[hx, ly]).unwrap();
        let d = same_values(&p);
        let atoms: Vec<Width> = d
            .nodes()
            .iter()
            .filter(|n| n.op == MOp::Trunc)
            .map(|n| n.width)
            .collect();
        assert_eq!(atoms, vec![Width::new(16).unwrap(); 2]);
    }

    /// Without a product the bit classes do better: `(x & M) ^ (y & M)` keeps its registers.
    #[test]
    fn a_semi_linear_question_keeps_its_registers() {
        let w = Width::W64;
        let mut p = MbaExpr::new(vec![w, w]);
        let x = p.push(MOp::Var(0), &[]).unwrap();
        let y = p.push(MOp::Var(1), &[]).unwrap();
        let mask = p
            .push(MOp::Const(BitVec::wrapping_from_u64(w, 0xffff_ffff)), &[])
            .unwrap();
        let mx = p.push(MOp::And, &[x, mask]).unwrap();
        let my = p.push(MOp::And, &[y, mask]).unwrap();
        p.push(MOp::Xor, &[mx, my]).unwrap();
        assert!(decast_narrow(&p).is_none());
    }
}
