//! The demanded-bits pass: a node that observes only some bits of an operand (`x & c`, `x | c`,
//! an extract, a shift by a constant) simplifies that operand under the *demanded mask* `m`: it
//! is replaced by any `x'` with `x' & m = x & m`.
//!
//! Under a mask, `a & k` with `k ⊇ m` is `a`; `a | k` with `k ∩ m = ∅` is `a`, and with `k ⊇ m`
//! is `k`; an operand whose demanded bits the facts know is that constant; arithmetic demands
//! only the low prefix of its operands; shifts, extensions and `concat` re-index the mask. The
//! simplified region replaces the node only when it is strictly smaller.

use crate::engine::budget::Counter;
use crate::hash::IdMap;

use super::{Fin, PassKind, Runner, Step, Stop, facts, finish};
use crate::BitVec;
use crate::expr::{Context, OpCode};
use crate::facts::known::{bv_and, bv_not, low_mask};
use crate::ops::{BinOp, UnOp};

/// The most nodes one simplification visits.
const MAX_VISITS: u32 = 256;

/// A node and a demanded mask: hashed by the mask's active limbs only (one for 64 bits), not
/// all eight a `BitVec` stores.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Key(u32, BitVec);

impl core::hash::Hash for Key {
    fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
        h.write_u32(self.0);
        for &l in self.1.limbs() {
            h.write_u64(l);
        }
    }
}

struct Demand {
    memo: IdMap<Key, u32>,
    stops: Vec<u32>,
    visits: u32,
    fin: Fin,
}

/// The low prefix covering every bit of `m` (the bits arithmetic depends on).
fn low_prefix(m: &BitVec) -> BitVec {
    let w = m.width();
    let clz = BitVec::apply_un(UnOp::Clz, m)
        .ok()
        .and_then(|v| v.to_u64())
        .unwrap_or(0) as u32;
    low_mask(w, u32::from(w.bits()) - clz)
}

fn subset(a: &BitVec, b: &BitVec) -> bool {
    bv_and(a, &bv_not(b)).is_zero()
}

/// A node equal to `x` on the bits of `m`.
fn simplify(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    st: &mut Demand,
    x: u32,
    m: &BitVec,
) -> Result<u32, Stop> {
    let w = m.width();
    if m.is_zero() {
        return r.build(cx, |cx| cx.mk_const(&BitVec::zero(w)));
    }
    if let Some(&v) = st.memo.get(&Key(x, *m)) {
        return Ok(v);
    }
    st.visits += 1;
    r.meter.charge(Counter::PassWork, 1)?;
    r.meter.check()?;
    let node = cx.node(x);
    let stop = |st: &mut Demand| -> Result<u32, Stop> {
        st.stops.push(x);
        Ok(x)
    };
    if st.visits > MAX_VISITS || cx.const_val(x).is_some() {
        let v = stop(st)?;
        st.memo.insert(Key(x, *m), v);
        return Ok(v);
    }
    // Known demanded bits make the operand a constant.
    let (f, fin) = facts(r, cx, x)?;
    // What the facts relied on counts only if they fold the operand.
    st.fin = st.fin.and(fin.unchanged());
    if let Some(f) = f {
        let k = f.known();
        let known = bv_and(&bv_not(&k.maybe_one()), m);
        let known = crate::facts::known::bv_or(&known, &bv_and(&k.known_one(), m));
        let allowed = r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(x)));
        if known == *m && allowed {
            st.fin = st.fin.and(fin);
            let v = bv_and(&k.known_one(), m);
            let c = r.build(cx, |cx| cx.mk_const(&v))?;
            st.memo.insert(Key(x, *m), c);
            return Ok(c);
        }
    }
    let bin = |r: &mut Runner<'_, '_>, cx: &mut Context, op: BinOp, a: u32, b: u32| {
        r.build(cx, |cx| cx.c_bin(op, a, b))
    };
    let konst = |cx: &Context, j: u32| cx.const_val(j);
    let v = match node.op {
        OpCode::And => match (konst(cx, node.a), konst(cx, node.b)) {
            (Some(k), _) | (_, Some(k)) => {
                let a = if konst(cx, node.a).is_some() {
                    node.b
                } else {
                    node.a
                };
                if subset(m, &k) {
                    simplify(r, cx, st, a, m)?
                } else {
                    let a2 = simplify(r, cx, st, a, &bv_and(m, &k))?;
                    let kc = r.build(cx, |cx| cx.mk_const(&k))?;
                    bin(r, cx, BinOp::And, a2, kc)?
                }
            }
            _ => {
                let a = simplify(r, cx, st, node.a, m)?;
                let b = simplify(r, cx, st, node.b, m)?;
                bin(r, cx, BinOp::And, a, b)?
            }
        },
        OpCode::Or => match (konst(cx, node.a), konst(cx, node.b)) {
            (Some(k), _) | (_, Some(k)) => {
                let a = if konst(cx, node.a).is_some() {
                    node.b
                } else {
                    node.a
                };
                if bv_and(m, &k).is_zero() {
                    simplify(r, cx, st, a, m)?
                } else if subset(m, &k) {
                    r.build(cx, |cx| cx.mk_const(&k))?
                } else {
                    let a2 = simplify(r, cx, st, a, &bv_and(m, &bv_not(&k)))?;
                    let kc = r.build(cx, |cx| cx.mk_const(&k))?;
                    bin(r, cx, BinOp::Or, a2, kc)?
                }
            }
            _ => {
                let a = simplify(r, cx, st, node.a, m)?;
                let b = simplify(r, cx, st, node.b, m)?;
                bin(r, cx, BinOp::Or, a, b)?
            }
        },
        OpCode::Xor => {
            let a = simplify(r, cx, st, node.a, m)?;
            let b = simplify(r, cx, st, node.b, m)?;
            bin(r, cx, BinOp::Xor, a, b)?
        }
        OpCode::Not => {
            let a = simplify(r, cx, st, node.a, m)?;
            r.build(cx, |cx| cx.c_un(UnOp::Not, a))?
        }
        OpCode::Add | OpCode::Sub | OpCode::Mul => {
            let p = low_prefix(m);
            let a = simplify(r, cx, st, node.a, &p)?;
            let b = simplify(r, cx, st, node.b, &p)?;
            let op = node.op.as_bin().unwrap_or(BinOp::Add);
            bin(r, cx, op, a, b)?
        }
        OpCode::Neg => {
            let a = simplify(r, cx, st, node.a, &low_prefix(m))?;
            r.build(cx, |cx| cx.c_un(UnOp::Neg, a))?
        }
        OpCode::Shl | OpCode::LShr if konst(cx, node.b).is_some() => {
            let k = konst(cx, node.b).unwrap_or(BitVec::zero(w));
            let (op, back) = if node.op == OpCode::Shl {
                (BinOp::Shl, BinOp::LShr)
            } else {
                (BinOp::LShr, BinOp::Shl)
            };
            // The operand bits that reach the demanded ones.
            let ma = BitVec::bin_unchecked(back, m, &k);
            let a = simplify(r, cx, st, node.a, &ma)?;
            let kb = node.b;
            bin(r, cx, op, a, kb)?
        }
        OpCode::Zext => {
            let wa = cx.width_of(node.a);
            let ml = m.trunc(wa).map_err(|e| Stop::Error(e.into()))?;
            let a = simplify(r, cx, st, node.a, &ml)?;
            r.build(cx, |cx| cx.c_zext(a, w.bits()))?
        }
        OpCode::Concat => {
            let (wh, wl) = (cx.width_of(node.a), cx.width_of(node.b));
            let ml = m.trunc(wl).map_err(|e| Stop::Error(e.into()))?;
            let mh = m
                .extract(wl.bits(), wh)
                .map_err(|e| Stop::Error(e.into()))?;
            let h = simplify(r, cx, st, node.a, &mh)?;
            let l = simplify(r, cx, st, node.b, &ml)?;
            r.build(cx, |cx| cx.c_concat(h, l))?
        }
        _ => stop(st)?,
    };
    st.memo.insert(Key(x, *m), v);
    Ok(v)
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry("demanded").or_default()
}

/// The demanded-bits pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let w = cx.width_of(n);
    // The operand observed through a mask, and the mask.
    let (operand, mask): (u32, BitVec) = match node.op {
        OpCode::And | OpCode::Or => match (cx.const_val(node.a), cx.const_val(node.b)) {
            (Some(k), None) | (None, Some(k)) => {
                let x = if cx.const_val(node.a).is_some() {
                    node.b
                } else {
                    node.a
                };
                let m = if node.op == OpCode::And {
                    k
                } else {
                    bv_not(&k)
                };
                (x, m)
            }
            _ => return Ok(Step::Normal(Fin::FINAL)),
        },
        OpCode::Extract => {
            let wa = cx.width_of(node.a);
            let lo = BitVec::wrapping_from_u64(wa, u64::from(node.b));
            let m = BitVec::bin_unchecked(BinOp::Shl, &low_mask(wa, u32::from(w.bits())), &lo);
            (node.a, m)
        }
        OpCode::Shl | OpCode::LShr => match cx.const_val(node.b) {
            Some(k) => {
                let back = if node.op == OpCode::Shl {
                    BinOp::LShr
                } else {
                    BinOp::Shl
                };
                (node.a, BitVec::bin_unchecked(back, &BitVec::ones(w), &k))
            }
            None => return Ok(Step::Normal(Fin::FINAL)),
        },
        _ => return Ok(Step::Normal(Fin::FINAL)),
    };
    let before = cx.len() as u32;
    let mut st = Demand {
        memo: IdMap::default(),
        stops: Vec::new(),
        visits: 0,
        fin: Fin::FINAL,
    };
    let x2 = simplify(r, cx, &mut st, operand, &mask)?;
    if st.visits > MAX_VISITS {
        count(r).atomized += 1;
    }
    let fin = st.fin;
    if x2 == operand {
        count(r).noop += 1;
        return Ok(Step::Normal(fin));
    }
    let mut kids = [node.a, node.b, node.c];
    for k in kids.iter_mut().take(node.op.arity()) {
        if *k == operand {
            *k = x2;
        }
    }
    let e = r.build(cx, |cx| cx.rebuild(n, kids))?;
    finish(r, cx, PassKind::Demanded, n, e, before, &st.stops, fin)
}
