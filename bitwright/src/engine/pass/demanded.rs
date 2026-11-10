//! The demanded-bits pass: a node that observes only some bits of an operand (`x & c`, `x | c`,
//! an extract, a shift by a constant) simplifies that operand under the *demanded mask* `m`: it
//! is replaced by any `x'` with `x' & m = x & m`.
//!
//! Under a mask, `a & k` with `k ⊇ m` is `a`; `a | k` with `k ∩ m = ∅` is `a`, and with `k ⊇ m`
//! is `k`; an operand whose demanded bits the facts know is that constant; arithmetic demands
//! only the low prefix of its operands; shifts, extensions and `concat` re-index the mask. A
//! sum whose terms read one condition several ways is read with them merged, modulo the low
//! prefix (see `conditions`), and one whose terms are limbs of one word with them joined (see
//! `limbs`). The simplified region replaces the node only when it is strictly smaller.
//!
//! A node read under several masks is written once for each: a word each of its limbs reads
//! becomes a copy a limb, its constants reduced to that limb's bits. So the operand is
//! simplified a second time with every node read on the bits any of its users below the
//! operand reads, and one that something else reads whole left as it is (see `unions`); that
//! result is the candidate where it frees no fewer nodes. A limb held in a register wider than
//! it is, read through truncations of several widths, is then one value on the limb's bits,
//! where the carry in its sum is read as the high digits it completes (see `borrows`).

use crate::engine::budget::Counter;
use crate::hash::IdMap;

use super::{Fin, PassKind, Runner, Step, Stop, finish, known, known_words};
use crate::expr::{Context, OpCode};
use crate::facts::known::{bv_and, bv_not, bv_or, low_mask};
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// The most nodes one simplification visits.
const MAX_VISITS: u32 = 256;

/// A node and a demanded mask: hashed by the mask's active limbs only (one for 64 bits), not
/// all eight a `BitVec` stores.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct Key(u32, BitVec);

impl core::hash::Hash for Key {
    fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
        h.write_u32(self.0);
        for &l in self.1.limbs() {
            h.write_u64(l);
        }
    }
}

/// Results per node and demanded mask, for one simplification (kept by the runner and reused).
pub(crate) type Memo = IdMap<Key, u32>;

/// The operands a phase run's simplifications found nothing to simplify under a mask, each
/// with the leaves its walk stopped at (the region boundary a later walk must report the
/// same, for the commit rule to count what a candidate reuses below it as reused).
#[derive(Default)]
pub(crate) struct Same {
    /// Per (node, mask): the range of its leaves in `leaves`.
    map: IdMap<Key, (u32, u32)>,
    leaves: Vec<u32>,
    /// Per node: whether a sum with a carry term is at or below it, through the operators the
    /// simplification reads through (see [`unions`]).
    carried: IdMap<u32, bool>,
}

impl Same {
    pub(crate) fn clear(&mut self) {
        self.map.clear();
        self.leaves.clear();
        self.carried.clear();
    }
}

/// Sorts `v` and moves its distinct values to the front: how many there are.
fn sorted_distinct(v: &mut [u32]) -> usize {
    v.sort_unstable();
    let mut kept = 0;
    for i in 0..v.len() {
        if kept == 0 || v[i] != v[kept - 1] {
            v[kept] = v[i];
            kept += 1;
        }
    }
    kept
}

struct Demand {
    memo: Memo,
    /// The most nodes one simplification visits (the strategy may lower [`MAX_VISITS`]).
    cap: u32,
    stops: Vec<u32>,
    visits: u32,
    fin: Fin,
    /// The arena length when the simplification began: a node from here on was built by it.
    before: u32,
    /// The operand the simplification began at.
    root: u32,
    /// each `a ^ k` built so far, as its operand `a`, `k`, the mask it was built
    /// under and the node (see the `Xor` arm).
    xors: Vec<(u32, BitVec, BitVec, u32)>,
    /// The identities found (a node unchanged under a mask), each with the range of `stops`
    /// its walk pushed: kept for the phase run once the step is done (see [`Same`]).
    identities: Vec<(Key, u32, u32)>,
    /// The nodes below the operand that the simplification reads on more bits than it is
    /// asked: each with the bits its users below the operand read of it, all of them together
    /// (see [`unions`]). Empty in the simplification that reads each as it is asked.
    union: IdMap<u32, BitVec>,
}

/// The operands [`simplify`] reads at `x` under the mask `m`, each with the mask it is read
/// under (the arms of its `match`, without what they build or fold).
#[cfg_attr(not(feature = "prove"), allow(dead_code))]
fn reads(cx: &Context, x: u32, m: &BitVec, out: &mut Vec<(u32, BitVec)>) {
    out.clear();
    if m.is_zero() || cx.const_val(x).is_some() {
        return;
    }
    let node = cx.node(x);
    let w = m.width();
    let konst = |j: u32| cx.const_val(j);
    match node.op {
        OpCode::And | OpCode::Or | OpCode::Xor => match (konst(node.a), konst(node.b)) {
            (Some(k), _) | (_, Some(k)) => {
                let a = if konst(node.a).is_some() {
                    node.b
                } else {
                    node.a
                };
                match node.op {
                    OpCode::And if subset(m, &k) => out.push((a, *m)),
                    OpCode::And => out.push((a, bv_and(m, &k))),
                    OpCode::Or if bv_and(m, &k).is_zero() => out.push((a, *m)),
                    OpCode::Or if subset(m, &k) => {}
                    OpCode::Or => out.push((a, bv_and(m, &bv_not(&k)))),
                    _ => out.push((a, *m)),
                }
            }
            _ => out.extend([(node.a, *m), (node.b, *m)]),
        },
        OpCode::Not => out.push((node.a, *m)),
        OpCode::Add | OpCode::Sub | OpCode::Mul => {
            let p = low_prefix(m);
            out.extend([(node.a, p), (node.b, p)]);
        }
        OpCode::Neg => out.push((node.a, low_prefix(m))),
        OpCode::Shl | OpCode::LShr => {
            if let Some(k) = konst(node.b) {
                let back = if node.op == OpCode::Shl {
                    BinOp::LShr
                } else {
                    BinOp::Shl
                };
                out.push((node.a, BitVec::bin_unchecked(back, m, &k)));
            }
        }
        OpCode::Zext => {
            if let Ok(ml) = m.trunc(cx.width_of(node.a)) {
                out.push((node.a, ml));
            }
        }
        OpCode::Extract => {
            let wa = cx.width_of(node.a);
            let lo = BitVec::wrapping_from_u64(wa, u64::from(node.b));
            if let Ok(ma) = m.zext(wa) {
                out.push((node.a, BitVec::bin_unchecked(BinOp::Shl, &ma, &lo)));
            }
        }
        OpCode::Sext => {
            let wa = cx.width_of(node.a);
            let above = Width::new(w.bits() - wa.bits())
                .ok()
                .and_then(|d| m.extract(wa.bits(), d).ok());
            if let (Ok(ml), Some(above)) = (m.trunc(wa), above) {
                let ml = if above.is_zero() {
                    ml
                } else {
                    let sign = BitVec::bin_unchecked(
                        BinOp::Shl,
                        &BitVec::wrapping_from_u64(wa, 1),
                        &BitVec::wrapping_from_u64(wa, u64::from(wa.bits() - 1)),
                    );
                    bv_or(&ml, &sign)
                };
                out.push((node.a, ml));
            }
        }
        OpCode::Concat => {
            let (wh, wl) = (cx.width_of(node.a), cx.width_of(node.b));
            if let (Ok(ml), Ok(mh)) = (m.trunc(wl), m.extract(wl.bits(), wh)) {
                out.extend([(node.a, mh), (node.b, ml)]);
            }
        }
        _ => {}
    }
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

/// `x` on the bits of `m`, when they are among the lowest [`RESIDUE_BITS`] and `x`'s residues
/// show them constant or equal to a leaf's.
fn by_residues(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    m: &BitVec,
) -> Result<Option<u32>, Stop> {
    let Some(mv) = m.to_u64() else {
        return Ok(None);
    };
    let k = 64 - mv.leading_zeros();
    if k == 0
        || k > RESIDUE_BITS
        || !matches!(cx.node(x).op, OpCode::Mul | OpCode::Add | OpCode::Sub)
    {
        return Ok(None);
    }
    if !super::residue::may_fold(r, cx, x, k, mv) {
        return Ok(None);
    }
    let Some(t) = super::residue::residues(r, cx, x, k)? else {
        return Ok(None);
    };
    let first = t.values[0] & mv;
    let allowed = r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(x)));
    if allowed && t.values.iter().all(|&v| v & mv == first) {
        let c = BitVec::wrapping_from_u64(m.width(), first);
        return Ok(Some(r.build(cx, |cx| cx.mk_const(&c))?));
    }
    Ok((0..t.leaves.len())
        .find(|&i| {
            t.values
                .iter()
                .enumerate()
                .all(|(c, &v)| v & mv == t.leaf(c, i) & mv)
        })
        .map(|i| t.leaves[i]))
}

/// The most low bits read by residues.
const RESIDUE_BITS: u32 = 4;

/// The constant equal to `c` on the low prefix `m` (`2^k − 1`, `k` below the width) with the
/// fewest significant bits: `c`'s residue modulo `2^k`, extended with zeros or with its sign,
/// whichever is the smaller in magnitude (zeros on a tie). `None` when `m` is no such prefix
/// or `c` already is that residue, either way extended; and when the residue is 0, which is
/// the facts' to fold (a product with it is known zero there, under the host's
/// [`fold_known`](crate::engine::Hooks::fold_known)) or `dropped_constant`'s (a sum).
fn prefix_residue(c: &BitVec, m: &BitVec) -> Option<BitVec> {
    let w = c.width();
    let k = crate::facts::known::count_ones(m);
    if k == 0 || k >= u32::from(w.bits()) || low_prefix(m) != *m {
        return None;
    }
    let kw = Width::new(k as u16).ok()?;
    let t = c.trunc(kw).ok()?;
    let (u, s) = (t.zext(w).ok()?, t.sext(w).ok()?);
    if t.is_zero() || *c == u || *c == s {
        return None;
    }
    // A negative residue `t` is `−(2^k − t)`, the smaller when `2^k − t <u t`.
    let neg = BitVec::un_unchecked(UnOp::Neg, &t);
    if t.msb() && BitVec::cmp_unchecked(crate::CmpOp::Ult, &neg, &t) {
        Some(s)
    } else {
        Some(u)
    }
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
    // A node with several users is read once, on the bits any of them reads (see `unions`).
    let wide;
    let m = match st.union.get(&x) {
        Some(u) if subset(m, u) => {
            wide = *u;
            &wide
        }
        _ => m,
    };
    let w = m.width();
    if m.is_zero() {
        return r.build(cx, |cx| cx.mk_const(&BitVec::zero(w)));
    }
    if let Some(&v) = st.memo.get(&Key(x, *m)) {
        return Ok(v);
    }
    // Found nothing to simplify under this mask in an earlier step of the phase run: the same
    // leaves as then.
    if let Some(&(from, len)) = r.demanded_same.map.get(&Key(x, *m)) {
        let (from, len) = (from as usize, len as usize);
        st.stops
            .extend_from_slice(&r.demanded_same.leaves[from..from + len]);
        st.memo.insert(Key(x, *m), x);
        return Ok(x);
    }
    let stops0 = st.stops.len() as u32;
    st.visits += 1;
    r.meter.charge(Counter::PassWork, 1)?;
    r.meter.check()?;
    let node = cx.node(x);
    let stop = |cx: &Context, st: &mut Demand| -> Result<u32, Stop> {
        stop_at(cx, st, x);
        Ok(x)
    };
    // A constant read on a low prefix only is its residue there: `x · 0x200001` under
    // `& 0x1ffff` is `x · 1`, an inverse modulo `2^17` that is none at the full width.
    if let Some(c) = cx.const_val(x)
        && let Some(c2) = prefix_residue(&c, m)
    {
        let v = r.build(cx, |cx| cx.mk_const(&c2))?;
        st.memo.insert(Key(x, *m), v);
        return Ok(v);
    }
    if st.visits > st.cap || cx.const_val(x).is_some() {
        let v = stop(cx, st)?;
        st.memo.insert(Key(x, *m), v);
        return Ok(v);
    }
    // Known demanded bits make the operand a constant: the value on them, if all are known.
    let (fold, fin) = if w.bits() <= 64 {
        let (k, fin) = known_words(r, cx, x)?;
        let mw = m.limbs()[0];
        let fold = k.map(|[zero, one]| {
            ((zero | one) & mw == mw).then(|| BitVec::from_canonical_u64(w, one & mw))
        });
        (fold, fin)
    } else {
        let (k, fin) = known(r, cx, x)?;
        let fold = k.map(|k| {
            let known = bv_and(&bv_or(&k.known_zero(), &k.known_one()), m);
            (known == *m).then(|| bv_and(&k.known_one(), m))
        });
        (fold, fin)
    };
    // What the facts relied on counts only if they fold the operand.
    st.fin = st.fin.and(fin.unchanged());
    if let Some(fold) = fold {
        let allowed = r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(x)));
        if let Some(v) = fold.filter(|_| allowed) {
            st.fin = st.fin.and(fin);
            let c = r.build(cx, |cx| cx.mk_const(&v))?;
            st.memo.insert(Key(x, *m), c);
            return Ok(c);
        }
    }
    // Demanded bits among the lowest few: the residues of `x` decide them (a constant, or a
    // leaf equal to `x` there).
    if let Some(v) = by_residues(r, cx, x, m)? {
        st.memo.insert(Key(x, *m), v);
        return Ok(v);
    }
    let bin = |r: &mut Runner<'_, '_>, cx: &mut Context, op: BinOp, a: u32, b: u32| {
        r.build(cx, |cx| cx.c_bin(op, a, b))
    };
    let konst = |cx: &Context, j: u32| cx.const_val(j);
    // Arithmetic reading one condition several ways, merged and taken modulo the demanded
    // prefix (see `conditions`), at the operand observed (every operand a mask, an extraction
    // or a shift observes is one, in the pass's step at its user).
    if x == st.root
        && matches!(node.op, OpCode::Add | OpCode::Sub)
        && let Some(v) = merged(r, cx, st, x, m)?
    {
        st.memo.insert(Key(x, *m), v);
        return Ok(v);
    }
    // A sum with carries, read on a low prefix: the carries as the high digits they complete,
    // where the prefix is narrow enough for them (see `borrows`). The prefix is that of all
    // the sum's users (see `unions`), so the limb it becomes is the one each of them reads.
    #[cfg(feature = "prove")]
    if st.union.contains_key(&x) && carries(cx, x) {
        let j = crate::facts::known::count_ones(&low_prefix(m)) as u16;
        if j < w.bits()
            && let Some((e, fin, stops, _)) = super::borrows::expanded(r, cx, x, j, false)?
        {
            st.fin = st.fin.and(fin);
            for s in stops {
                stop_at(cx, st, s);
            }
            let v = r.build(cx, |cx| cx.c_zext(e, w.bits()))?;
            st.memo.insert(Key(x, *m), v);
            return Ok(v);
        }
    }
    // A slice of a sum with its carry out (`zext(a) + zext(b)`) read below the carry: the
    // slice of the sum at the operands' width, which is the word the other limbs are of.
    #[cfg(feature = "prove")]
    if node.op == OpCode::Extract
        && node.b > 0
        && let Some(low) = super::casts::live_word(r, cx, node.a)?
    {
        let (lo, n, below) = (node.b as u16, node.width, cx.wid(low));
        let j = crate::facts::known::count_ones(&low_prefix(m)) as u16;
        if lo + j <= below && below < lo + n {
            stop_at(cx, st, low);
            let v = r.build(cx, |cx| {
                let e = cx.c_extract(low, lo, j)?;
                cx.c_zext(e, n)
            })?;
            st.memo.insert(Key(x, *m), v);
            return Ok(v);
        }
    }
    // The limbs of one word in a sum, joined modulo the demanded prefix (see `limbs`): a
    // coefficient that is 0 there reads nothing, and one with trailing zeros a narrower limb.
    if matches!(node.op, OpCode::Add | OpCode::Sub)
        && let Some(v) = joined(r, cx, st, x, m)?
    {
        st.memo.insert(Key(x, *m), v);
        return Ok(v);
    }
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
        // under the mask, `a ^ k` is `a` where `k` has none of its bits and `~a`
        // where `k` has all of them (`(y ^ 63)` read by `& 63`).
        OpCode::Xor => match (konst(cx, node.a), konst(cx, node.b)) {
            (Some(k), _) | (_, Some(k)) if bv_and(m, &k).is_zero() || subset(m, &k) => {
                let a = if konst(cx, node.a).is_some() {
                    node.b
                } else {
                    node.a
                };
                let a2 = simplify(r, cx, st, a, m)?;
                if bv_and(m, &k).is_zero() {
                    a2
                } else {
                    r.build(cx, |cx| cx.c_un(UnOp::Not, a2))?
                }
            }
            // `a ^ k2` is `~(a ^ k1)` where `k1 ^ k2` has every bit of the mask: one
            // `a ^ k1` built under a mask that has this one's bits is shared, and a sum that
            // reads both sees `y` and `~y`: `(t ^ c) + (t ^ c) + x - ~(t ^ c') -
            // (x & (t ^ c)) - (x & (t ^ c'))`, with `c' = ~c` on the low 40 bits,
            // read by bit 18.
            (Some(k), _) | (_, Some(k)) => {
                let a = if konst(cx, node.a).is_some() {
                    node.b
                } else {
                    node.a
                };
                let twin = st.xors.iter().find(|(a1, k1, m1, _)| {
                    *a1 == a && subset(m, m1) && subset(m, &bv_or(k1, &k)) && {
                        let both = bv_and(k1, &k);
                        bv_and(&both, m).is_zero()
                    }
                });
                if let Some(&(_, _, _, y)) = twin {
                    r.build(cx, |cx| cx.c_un(UnOp::Not, y))?
                } else {
                    let a2 = simplify(r, cx, st, a, m)?;
                    let kc = r.build(cx, |cx| cx.mk_const(&k))?;
                    let y = bin(r, cx, BinOp::Xor, a2, kc)?;
                    st.xors.push((a, k, *m, y));
                    y
                }
            }
            _ => {
                let a = simplify(r, cx, st, node.a, m)?;
                let b = simplify(r, cx, st, node.b, m)?;
                bin(r, cx, BinOp::Xor, a, b)?
            }
        },
        OpCode::Not => {
            let a = simplify(r, cx, st, node.a, m)?;
            r.build(cx, |cx| cx.c_un(UnOp::Not, a))?
        }
        OpCode::Add | OpCode::Sub | OpCode::Mul => {
            let p = low_prefix(m);
            let a = simplify(r, cx, st, node.a, &p)?;
            let b = simplify(r, cx, st, node.b, &p)?;
            let op = node.op.as_bin().unwrap_or(BinOp::Add);
            // a constant addend with none of the demanded bits goes (`63 - ~y`
            // is `y + 64`, which is `y` on the low six bits).
            let ones = |j: u32| cx.const_val(j).is_some_and(|k| k.is_ones());
            match dropped_constant(cx, node.op, a, b, &p) {
                Some(t) => t,
                // A factor that is −1 on the prefix (`0x3ffff` read by `& 0x1ffff`) negates.
                None if node.op == OpCode::Mul && (ones(a) || ones(b)) => {
                    let t = if ones(a) { b } else { a };
                    r.build(cx, |cx| cx.c_un(UnOp::Neg, t))?
                }
                None => bin(r, cx, op, a, b)?,
            }
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
        // an extraction reads the operand's bits it takes; a sign extension the
        // operand's own bits, and its sign bit for any demanded bit above them.
        OpCode::Extract => {
            let wa = cx.width_of(node.a);
            let lo = BitVec::wrapping_from_u64(wa, u64::from(node.b));
            let ma = m.zext(wa).map_err(|e| Stop::Error(e.into()))?;
            let ma = BitVec::bin_unchecked(BinOp::Shl, &ma, &lo);
            let a = simplify(r, cx, st, node.a, &ma)?;
            let (b, c) = (node.b, node.c);
            r.build(cx, |cx| cx.rebuild(x, [a, b, c]))?
        }
        OpCode::Sext => {
            let wa = cx.width_of(node.a);
            let ml = m.trunc(wa).map_err(|e| Stop::Error(e.into()))?;
            let above = m
                .extract(
                    wa.bits(),
                    Width::new(w.bits() - wa.bits()).map_err(|e| Stop::Error(e.into()))?,
                )
                .map_err(|e| Stop::Error(e.into()))?;
            let ml = if above.is_zero() {
                ml
            } else {
                let sign = BitVec::bin_unchecked(
                    BinOp::Shl,
                    &BitVec::wrapping_from_u64(wa, 1),
                    &BitVec::wrapping_from_u64(wa, u64::from(wa.bits() - 1)),
                );
                bv_or(&ml, &sign)
            };
            let a = simplify(r, cx, st, node.a, &ml)?;
            r.build(cx, |cx| cx.c_sext(a, w.bits()))?
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
        _ => stop(cx, st)?,
    };
    st.memo.insert(Key(x, *m), v);
    // (Not above a sum with carries: what it is read as depends on its other users.)
    if v == x && x < st.before && r.demanded_same.carried.get(&x) != Some(&true) {
        st.identities
            .push((Key(x, *m), stops0, st.stops.len() as u32));
    }
    Ok(v)
}

/// Records `x` as a node the simplification stops at: a node it built itself is no leaf of the
/// region (the commit rule counts it), so the nodes below it that existed are.
fn stop_at(cx: &Context, st: &mut Demand, x: u32) {
    if x < st.before {
        st.stops.push(x);
        return;
    }
    let mut stack = vec![x];
    while let Some(i) = stack.pop() {
        if i < st.before {
            st.stops.push(i);
        } else {
            stack.extend(cx.node(i).children());
        }
    }
}

/// `x` on the bits of `m` from its linear form with the conditions its terms read merged, the
/// form taken modulo `2^j` for the `j` low bits arithmetic depends on: a condition whose
/// coefficient that makes 0 is not read at all. `None` when no two terms read one condition
/// or every bit is demanded (the linear pass reads that case).
fn merged(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    st: &mut Demand,
    x: u32,
    m: &BitVec,
) -> Result<Option<u32>, Stop> {
    let w = m.width();
    let p = low_prefix(m);
    let j = crate::facts::known::count_ones(&p);
    if j >= u32::from(w.bits()) || !super::conditions::may_merge(cx, x) {
        return Ok(None);
    }
    let form = super::linear::form_of(r, cx, x)?;
    let Some((f, _)) = super::conditions::merge(r, cx, &form)? else {
        return Ok(None);
    };
    let jw = crate::Width::new(j as u16).map_err(|e| Stop::Error(e.into()))?;
    let f = f.reduce(jw);
    st.fin = st.fin.and(f.fin);
    let (konst, terms, _) = super::forms::Parts::parts(&f);
    let (konst, terms) = (*konst, terms.to_vec());
    let mut out = Vec::with_capacity(terms.len());
    for (a, k) in terms {
        out.push((simplify(r, cx, st, a, &p)?, k));
    }
    let f = super::linear::Form::of(konst, &out);
    Ok(Some(super::linear::emit(r, cx, &f)?))
}

/// `x` on the bits of `m` from its linear form modulo `2^j`, for the `j` low bits arithmetic
/// depends on, with the terms that are limbs of one word joined (see `limbs`). `None` when
/// none join or every bit is demanded (the linear pass reads that case).
fn joined(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    st: &mut Demand,
    x: u32,
    m: &BitVec,
) -> Result<Option<u32>, Stop> {
    let w = m.width();
    let p = low_prefix(m);
    let j = crate::facts::known::count_ones(&p);
    if j >= u32::from(w.bits()) || w.bits() > 64 {
        return Ok(None);
    }
    let form = super::linear::form_of(r, cx, x)?;
    let Some((f, _)) = super::limbs::joined(r, cx, &form, j as u16)? else {
        return Ok(None);
    };
    st.fin = st.fin.and(f.fin);
    let (konst, terms, _) = super::forms::Parts::parts(&f);
    let (konst, terms) = (*konst, terms.to_vec());
    let mut out = Vec::with_capacity(terms.len());
    for (a, k) in terms {
        out.push((simplify(r, cx, st, a, &p)?, k));
    }
    let f = super::linear::Form::of(konst, &out);
    Ok(Some(super::linear::emit(r, cx, &f)?))
}

/// `x & k` is `x` when the bits `k` clears are among the lowest
/// [`RESIDUE_BITS`] and `x`'s residues show them zero for every input: `(z·z + z) & ~1`, the
/// product of two consecutive numbers being even (the known bits of a sum cannot see that its
/// two low bits are always equal).
fn clears_known_zeros(r: &mut Runner<'_, '_>, cx: &Context, n: u32) -> Result<Option<u32>, Stop> {
    let node = cx.node(n);
    if node.op != OpCode::And || cx.wid(n) > 64 {
        return Ok(None);
    }
    let (x, k) = match (cx.const_val(node.a), cx.const_val(node.b)) {
        (None, Some(k)) => (node.a, k),
        (Some(k), None) => (node.b, k),
        _ => return Ok(None),
    };
    let Some(kv) = k.to_u64() else {
        return Ok(None);
    };
    let wbits = u32::from(cx.wid(n));
    let all = if wbits >= 64 {
        u64::MAX
    } else {
        (1 << wbits) - 1
    };
    let cleared = !kv & all;
    let bits = 64 - cleared.leading_zeros();
    if cleared == 0
        || bits > RESIDUE_BITS
        || !matches!(cx.node(x).op, OpCode::Mul | OpCode::Add | OpCode::Sub)
    {
        return Ok(None);
    }
    let Some(t) = super::residue::residues(r, cx, x, bits)? else {
        return Ok(None);
    };
    Ok(t.values.iter().all(|&v| v & cleared == 0).then_some(x))
}

/// `t` when `a op b` (an `add` or `sub`) is `t` plus a constant with none of the
/// bits of the prefix `p`; `k - ~t` is `t + (k + 1)`.
fn dropped_constant(cx: &Context, op: OpCode, a: u32, b: u32, p: &BitVec) -> Option<u32> {
    let (t, k) = match (op, cx.const_val(a), cx.const_val(b)) {
        (OpCode::Sub, Some(k), None) if cx.node(b).op == OpCode::Not => {
            let one = BitVec::one(k.width());
            (cx.node(b).a, BitVec::bin_unchecked(BinOp::Add, &k, &one))
        }
        (OpCode::Add | OpCode::Sub, None, Some(k)) => (a, k),
        (OpCode::Add, Some(k), None) => (b, k),
        _ => return None,
    };
    bv_and(&k, p).is_zero().then_some(t)
}

/// a node equal to `x` on every bit, each operand taken on the bits its users read
/// and folded to a constant where those bits are all known, within `cap` visits. The
/// opaque-constant sweep asks it of a candidate before its readings: under `t << 42` only `t`'s
/// low 22 bits are read, and a value whose noise reaches only higher bits (the left half of a
/// rotate) is a constant there.
#[cfg(feature = "mba")]
pub(super) fn reduced(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    cap: u32,
) -> Result<u32, Stop> {
    let w = cx.width_of(x);
    let mut st = Demand {
        memo: Memo::default(),
        cap,
        stops: Vec::new(),
        visits: 0,
        fin: Fin::FINAL,
        before: cx.len() as u32,
        root: x,
        xors: Vec::new(),
        identities: Vec::new(),
        union: IdMap::default(),
    };
    simplify(r, cx, &mut st, x, &BitVec::ones(w))
}

/// The most nodes below an operand whose users' demands are added up.
#[cfg(feature = "prove")]
const MAX_CONE: usize = 2048;

/// Whether the simplification reads through `i` into its operands.
#[cfg(feature = "prove")]
fn reads_through(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    match n.op {
        OpCode::And
        | OpCode::Or
        | OpCode::Xor
        | OpCode::Not
        | OpCode::Add
        | OpCode::Sub
        | OpCode::Mul
        | OpCode::Neg
        | OpCode::Zext
        | OpCode::Sext
        | OpCode::Extract
        | OpCode::Concat => true,
        OpCode::Shl | OpCode::LShr => cx.const_val(n.b).is_some(),
        _ => false,
    }
}

/// Whether `i` is a sum with a carry term, or with high digits (see `borrows`).
#[cfg(feature = "prove")]
fn carries(cx: &Context, i: u32) -> bool {
    matches!(cx.node(i).op, OpCode::Add | OpCode::Sub)
        && cx.wid(i) <= 64
        && super::borrows::may_expand(cx, i)
}

/// Whether a sum with a carry term is at or below `x` through the operators the
/// simplification reads through, remembered for the phase run.
#[cfg(feature = "prove")]
fn carried(r: &mut Runner<'_, '_>, cx: &Context, x: u32) -> Result<bool, Stop> {
    let mut stack = vec![(x, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.demanded_same.carried.contains_key(&i) {
            continue;
        }
        if carries(cx, i) {
            r.demanded_same.carried.insert(i, true);
            continue;
        }
        if !reads_through(cx, i) {
            r.demanded_same.carried.insert(i, false);
            continue;
        }
        let node = cx.node(i);
        if expanded {
            let any = node
                .children()
                .any(|c| r.demanded_same.carried.get(&c) == Some(&true));
            r.demanded_same.carried.insert(i, any);
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        stack.push((i, true));
        for c in node.children() {
            if !r.demanded_same.carried.contains_key(&c) {
                stack.push((c, false));
            }
        }
    }
    Ok(r.demanded_same.carried.get(&x) == Some(&true))
}

/// For each node below `operand` that the simplification reads through to, the bits of it
/// that are read when `operand` is read on `mask`: by all its users below `operand` together,
/// and every bit where something else reads it too (a node outside, or one the simplification
/// does not read through), into `st.union`.
///
/// A limb is computed in a register wider than it is and read by several users, each through
/// a truncation or a mask of its own that is wider than the limb, while the bits that reach
/// the operand are the limb's alone. Simplified under each user's own mask, the limb's sum
/// is written once per user, each copy with its constants reduced to that user's bits, and a
/// carry in it is read by none of them; under the union of what they read it is written
/// once, on the limb's bits, where its carries are read (see `simplify`). A node something
/// else reads whole stays as it is: a second copy of it would be shared with nobody.
///
/// The union only widens a mask the simplification was given, so what is returned under it
/// is right under the mask too. Nothing is added up below more than [`MAX_CONE`] nodes.
#[cfg(feature = "prove")]
fn unions(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    st: &mut Demand,
    operand: u32,
    mask: &BitVec,
) -> Result<(), Stop> {
    // (Which nodes have a sum with carries below them is remembered: see `simplify`.)
    carried(r, cx, operand)?;
    // The nodes read through, operands first.
    let mut order: Vec<u32> = Vec::new();
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack = vec![(operand, false)];
    while let Some((i, expanded)) = stack.pop() {
        if expanded {
            order.push(i);
            continue;
        }
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if seen.len() > MAX_CONE {
            return Ok(());
        }
        stack.push((i, true));
        if reads_through(cx, i) {
            for c in cx.node(i).children() {
                if !seen.contains_key(&c) {
                    stack.push((c, false));
                }
            }
        }
    }
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    let mut read: IdMap<u32, BitVec> = IdMap::default();
    read.insert(operand, *mask);
    // The uses of each node from the nodes below the operand (and the observer's of it).
    let mut inside: IdMap<u32, u32> = IdMap::default();
    inside.insert(operand, 1);
    super::refresh_uses(r, cx)?;
    for &x in &order {
        for c in cx.node(x).children() {
            *inside.entry(c).or_default() += 1;
        }
    }
    let give = |read: &mut IdMap<u32, BitVec>, c: u32, m: BitVec| {
        if cx.const_val(c).is_none() && m.width() == cx.width_of(c) {
            read.entry(c).and_modify(|v| *v = bv_or(v, &m)).or_insert(m);
        }
    };
    // Users first: each node's mask is whole when its operands' are taken from it.
    for &x in order.iter().rev() {
        // A node read by something outside, or by a node that is not read through, is read
        // whole.
        if r.live.uses(x).unwrap_or(0) > inside.get(&x).copied().unwrap_or(0) {
            read.insert(x, BitVec::ones(cx.width_of(x)));
        }
        if !reads_through(cx, x) {
            for c in cx.node(x).children() {
                if seen.contains_key(&c) && cx.const_val(c).is_none() {
                    read.insert(c, BitVec::ones(cx.width_of(c)));
                }
            }
        }
        let Some(m) = read.get(&x).copied() else {
            continue;
        };
        if m.is_zero() || !reads_through(cx, x) {
            continue;
        }
        let node = cx.node(x);
        let konst = |j: u32| cx.const_val(j);
        match node.op {
            OpCode::And | OpCode::Or => {
                let k = konst(node.a).or(konst(node.b));
                let ma = match (node.op, k) {
                    (OpCode::And, Some(k)) => bv_and(&m, &k),
                    (_, Some(k)) => bv_and(&m, &bv_not(&k)),
                    _ => m,
                };
                give(&mut read, node.a, ma);
                give(&mut read, node.b, ma);
            }
            OpCode::Xor => {
                give(&mut read, node.a, m);
                give(&mut read, node.b, m);
            }
            OpCode::Not => give(&mut read, node.a, m),
            OpCode::Add | OpCode::Sub | OpCode::Mul => {
                let p = low_prefix(&m);
                give(&mut read, node.a, p);
                give(&mut read, node.b, p);
            }
            OpCode::Neg => give(&mut read, node.a, low_prefix(&m)),
            OpCode::Shl | OpCode::LShr => {
                let Some(k) = konst(node.b) else {
                    continue;
                };
                let back = if node.op == OpCode::Shl {
                    BinOp::LShr
                } else {
                    BinOp::Shl
                };
                give(&mut read, node.a, BitVec::bin_unchecked(back, &m, &k));
            }
            OpCode::Zext | OpCode::Sext => {
                let wa = cx.width_of(node.a);
                let Ok(mut ml) = m.trunc(wa) else {
                    continue;
                };
                if node.op == OpCode::Sext && ml.zext(m.width()).ok() != Some(m) {
                    let sign = BitVec::bin_unchecked(
                        BinOp::Shl,
                        &BitVec::wrapping_from_u64(wa, 1),
                        &BitVec::wrapping_from_u64(wa, u64::from(wa.bits() - 1)),
                    );
                    ml = bv_or(&ml, &sign);
                }
                give(&mut read, node.a, ml);
            }
            OpCode::Extract => {
                let wa = cx.width_of(node.a);
                let lo = BitVec::wrapping_from_u64(wa, u64::from(node.b));
                let Ok(ma) = m.zext(wa) else {
                    continue;
                };
                give(
                    &mut read,
                    node.a,
                    BitVec::bin_unchecked(BinOp::Shl, &ma, &lo),
                );
            }
            OpCode::Concat => {
                let (wh, wl) = (cx.width_of(node.a), cx.width_of(node.b));
                if let (Ok(ml), Ok(mh)) = (m.trunc(wl), m.extract(wl.bits(), wh)) {
                    give(&mut read, node.a, mh);
                    give(&mut read, node.b, ml);
                }
            }
            _ => {}
        }
    }
    for &x in &order {
        if let Some(m) = read.get(&x) {
            st.union.insert(x, *m);
        }
    }
    Ok(())
}

/// The most nodes below a root whose demands are added up (see [`whole`]).
#[cfg(feature = "prove")]
const MAX_WHOLE: usize = 4096;

/// The nodes below `root`, operands first, and the bits of each that reach `root`: what
/// [`unions`] adds up below an observed operand, below the root, which nothing is outside
/// of. An operator the simplification does not read through reads its operands whole, and a
/// `select` its arms on the bits read of it. `None` beyond [`MAX_WHOLE`] nodes.
#[cfg(feature = "prove")]
#[allow(clippy::type_complexity)]
fn demands(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    root: u32,
) -> Result<Option<(Vec<u32>, IdMap<u32, BitVec>)>, Stop> {
    let mut order: Vec<u32> = Vec::new();
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if expanded {
            order.push(i);
            continue;
        }
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if seen.len() > MAX_WHOLE {
            return Ok(None);
        }
        stack.push((i, true));
        for c in cx.node(i).children() {
            if !seen.contains_key(&c) {
                stack.push((c, false));
            }
        }
    }
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    let mut read: IdMap<u32, BitVec> = IdMap::default();
    read.insert(root, BitVec::ones(cx.width_of(root)));
    let mut below = Vec::new();
    // Users first: each node's bits are all there when its operands' are taken from them.
    for &x in order.iter().rev() {
        let Some(m) = read.get(&x).copied() else {
            continue;
        };
        if m.is_zero() {
            continue;
        }
        if reads_through(cx, x) {
            reads(cx, x, &m, &mut below);
        } else {
            let node = cx.node(x);
            below.clear();
            for (s, c) in node.children().enumerate() {
                let arm = node.op == OpCode::Select && s > 0;
                let whole = BitVec::ones(cx.width_of(c));
                below.push((c, if arm { m } else { whole }));
            }
        }
        for (c, cm) in below.drain(..) {
            read.entry(c)
                .and_modify(|v| *v = bv_or(v, &cm))
                .or_insert(cm);
        }
    }
    Ok(Some((order, read)))
}

/// A sum with carries below a root, read on the bits of it that reach the root.
#[cfg(feature = "prove")]
#[derive(Clone)]
struct Limb {
    /// The sum.
    x: u32,
    /// What it is read as: equal to it on the bits that reach the root.
    e: u32,
    /// What the reading relied on, and the nodes its narrowing stopped at.
    fin: Fin,
    stops: Vec<u32>,
    /// Whether the commit rule takes the reading for the sum, every reader of the sum
    /// reading it instead; otherwise it would were the sum's operands the sum's alone.
    pays: bool,
    /// What the commit rule counts for it there: the nodes freed less the nodes needed.
    shared: i64,
    /// Whether it leaves the sum no fewer terms.
    tied: bool,
}

/// `root` with each sum of `limbs` (those that pay only, with `paying`) replaced by its
/// reading in every node of `order` (the nodes below `root`, operands first) that reads it,
/// and those nodes written again over their new operands; with the nodes the commit rule
/// stops at: what the nodes written again read and is as it was, and where each reading's
/// narrowing stopped. A reading is taken as it was built: no sum is replaced inside one.
#[cfg(feature = "prove")]
fn replaced(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    order: &[u32],
    root: u32,
    limbs: &[Limb],
    paying: bool,
) -> Result<(u32, Vec<u32>), Stop> {
    let mut to: IdMap<u32, u32> = IdMap::default();
    let mut atoms: Vec<u32> = Vec::new();
    for l in limbs.iter().filter(|l| l.pays || !paying) {
        to.insert(l.x, l.e);
        atoms.extend_from_slice(&l.stops);
    }
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    for &x in order {
        if to.contains_key(&x) {
            continue;
        }
        let node = cx.node(x);
        let mut kids = [node.a, node.b, node.c];
        let arity = node.op.arity();
        let mut changed = false;
        for k in kids.iter_mut().take(arity) {
            if let Some(&t) = to.get(k) {
                *k = t;
                changed = true;
            }
        }
        if !changed {
            continue;
        }
        for (k, c) in kids.iter().zip(node.children()) {
            if *k == c {
                atoms.push(c);
            }
        }
        let y = r.build(cx, |cx| cx.rebuild(x, kids))?;
        to.insert(x, y);
    }
    Ok((to.get(&root).copied().unwrap_or(root), atoms))
}

/// The reading `low` of the sum `x` on its `j` low bits (see `borrows`), at the width of
/// `x`: each of its terms that is a term of `x` narrowed is that term as `x` has it, the
/// others are zero-extended. Equal to `x` on the `j` bits, and with the terms the reading
/// left alone not written again narrower (their operands, which other nodes read, as they
/// were). `None` when no term is one of `x`'s.
#[cfg(feature = "prove")]
fn lifted(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    low: u32,
    j: u16,
) -> Result<Option<u32>, Stop> {
    let w = cx.width_of(x);
    let form = super::linear::form_of(r, cx, x)?;
    let (konst, terms, _) = super::forms::Parts::parts(&form);
    let (konst, terms) = (*konst, terms.to_vec());
    // The sum's terms as the reading narrowed them.
    let mut own: Vec<(u32, u32)> = Vec::with_capacity(terms.len());
    for &(t, _) in &terms {
        if let Some((h, _, _)) = super::casts::narrowed_from(r, cx, t, 0, j)? {
            own.push((h, t));
        }
    }
    let read = super::linear::form_of(r, cx, low)?;
    let (k2, t2, _) = super::forms::Parts::parts(&read);
    let (k2, t2) = (*k2, t2.to_vec());
    let wide = |v: &BitVec| v.sext(w).map_err(|e| Stop::Error(e.into()));
    let mut out: Vec<(u32, BitVec)> = Vec::with_capacity(t2.len());
    let mut kept = false;
    for (h, c) in t2 {
        // (Of two terms narrowed to one node, the first in the canonical order: not the
        // first as the form happens to list them.)
        let same = own.iter().filter(|&&(n, _)| n == h).map(|&(_, t)| t);
        let t = match same.min_by(|a, b| cx.order(*a, *b)) {
            Some(t) => {
                kept = true;
                t
            }
            None => r.build(cx, |cx| cx.c_zext(h, w.bits()))?,
        };
        out.push((t, wide(&c)?));
    }
    if !kept {
        return Ok(None);
    }
    // The sum's own constant where the reading's is that on the `j` bits.
    let k = if konst.trunc(k2.width()).ok() == Some(k2) {
        konst
    } else {
        wide(&k2)?
    };
    let f = super::linear::Form::of(k, &out);
    Ok(Some(super::linear::emit(r, cx, &f)?))
}

/// The most sums read on a low prefix that are looked for as a word (see [`words`]), the
/// most sums each is compared with, and the most nodes below a word looked at.
#[cfg(feature = "prove")]
const MAX_NARROW: usize = 16;
#[cfg(feature = "prove")]
const MAX_FULL: usize = 48;
#[cfg(feature = "prove")]
const MAX_BELOW: usize = 512;

/// Whether one of `targets` is `from` or below it, or more than [`MAX_BELOW`] nodes are.
#[cfg(feature = "prove")]
fn holds_any(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    from: u32,
    targets: &[u32],
) -> Result<bool, Stop> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack = vec![from];
    let mut found = false;
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if targets.contains(&i) || seen.len() > MAX_BELOW {
            found = true;
            break;
        }
        stack.extend(cx.node(i).children());
    }
    r.meter.charge(Counter::PassWork, seen.len() as u64)?;
    Ok(found)
}

/// One word for the sums below a root that are its low bits.
///
/// A word computed limb by limb is written once for each reader: the product with its
/// constant reduced to the reader's bits, the limbs' own partial products, the word plus
/// another constant. Below the root each node may be replaced by any value equal to it on
/// the bits of it that reach the root ([`demands`]). So a sum `x` that only sums do not read
/// and that reaches the root on its low `j` bits only is written over another such sum `y`
/// of its width that reaches it on more (or on as many, the first in the canonical order):
/// `x = ±y + R` modulo `2^j`, with `R` the difference of their forms there, its limbs
/// joined (see `limbs`), where `y` takes all its terms out of `x` (`R` and `y` together
/// have no more terms than `x`); of several such `y`, the one that leaves `R` the fewest.
/// Every reader of `x` then reads the one word, and what only `x` read is gone.
///
/// A `y` that one of the sums replaced is below is not taken (the new sums would read each
/// other). The root so written replaces the root under the commit rule.
#[cfg(feature = "prove")]
fn words(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    order: &[u32],
    read: &IdMap<u32, BitVec>,
) -> Result<Option<Step>, Stop> {
    use super::forms::Parts;
    use super::linear::{self, Form};
    let konst = |cx: &Context, i: u32| cx.const_val(i).is_some();
    let sum = |cx: &Context, i: u32| {
        let n = cx.node(i);
        n.width <= 64
            && match n.op {
                OpCode::Add | OpCode::Sub | OpCode::Neg => true,
                OpCode::Mul | OpCode::Shl => konst(cx, n.a) || konst(cx, n.b),
                _ => false,
            }
    };
    // The sums something other than a sum reads, each with the low bits that reach the root.
    let mut outer: IdMap<u32, ()> = IdMap::default();
    outer.insert(root, ());
    for &u in order {
        if !sum(cx, u) {
            for c in cx.node(u).children() {
                outer.insert(c, ());
            }
        }
    }
    let mut full: Vec<(u32, u16)> = order
        .iter()
        .filter(|&&x| sum(cx, x) && outer.contains_key(&x))
        .filter_map(|&x| {
            let j = crate::facts::known::count_ones(&low_prefix(read.get(&x)?)) as u16;
            (j > 0).then_some((x, j))
        })
        .collect();
    if !full.iter().any(|&(x, j)| j < cx.wid(x)) || full.len() < 2 {
        return Ok(None);
    }
    full.sort_by(|a, b| cx.order(a.0, b.0));
    let mut narrow: Vec<(u32, u16)> = full.iter().filter(|v| v.1 < cx.wid(v.0)).copied().collect();
    narrow.truncate(MAX_NARROW);
    full.truncate(MAX_FULL);
    let before = cx.len() as u32;
    let mut fin = Fin::FINAL;
    // Each sum with the word it is written over, and as what.
    let mut found: Vec<(u32, u32, u32)> = Vec::new();
    for &(x, j) in &narrow {
        let w = cx.wid(x);
        let jw = Width::new(j).map_err(|e| Stop::Error(e.into()))?;
        let full_x = linear::form_of(r, cx, x)?;
        let fx = full_x.reduce(jw);
        let tx = fx.parts().1.len();
        if tx == 0 {
            continue;
        }
        // The fewest terms left, then no constant, then the most bits read.
        #[allow(clippy::type_complexity)]
        let mut best: Option<((usize, bool, u16), u32, bool, Form)> = None;
        for &(y, jy) in &full {
            if y == x || cx.wid(y) != w || jy < j || (jy == j && !cx.order(y, x).is_lt()) {
                continue;
            }
            r.meter.charge(Counter::PassWork, 16)?;
            let whole = linear::form_of(r, cx, y)?;
            let fy = whole.reduce(jw);
            let ty = fy.parts().1.len();
            if ty == 0 {
                continue;
            }
            for minus in [false, true] {
                // (Not a word whose terms are the sum's as they stand: the sum has it.)
                let plain = if minus {
                    full_x.add(&whole)
                } else {
                    full_x.add(&whole.neg())
                };
                if plain.parts().1.len() + ty <= tx {
                    continue;
                }
                let over = if minus {
                    fx.add(&fy)
                } else {
                    fx.add(&fy.neg())
                };
                let over = over.reduce(jw);
                let rest = match super::limbs::joined(r, cx, &over, j)? {
                    Some((f, _)) => f,
                    None => over,
                };
                let left = rest.parts().1.len();
                if left + ty > tx {
                    continue;
                }
                let score = (left, !rest.parts().0.is_zero(), w - jy);
                if best.as_ref().is_none_or(|b| score < b.0) && !holds_any(r, cx, y, &[x])? {
                    best = Some((score, y, minus, rest));
                }
            }
        }
        let Some((_, y, minus, rest)) = best else {
            continue;
        };
        fin = fin.and(fx.fin).and(rest.fin);
        let (k, terms, _) = rest.parts();
        let mut terms = terms.to_vec();
        let one = BitVec::one(cx.width_of(x));
        terms.push((
            y,
            if minus {
                BitVec::un_unchecked(UnOp::Neg, &one)
            } else {
                one
            },
        ));
        let e = linear::emit(r, cx, &Form::of(*k, &terms))?;
        if e != x {
            found.push((x, y, e));
        }
    }
    // No word that a sum replaced is below.
    let all: Vec<u32> = found.iter().map(|v| v.0).collect();
    let mut kept = Vec::with_capacity(found.len());
    for &(x, y, e) in &found {
        if !holds_any(r, cx, y, &all)? {
            kept.push((x, e));
        }
    }
    if kept.is_empty() {
        super::discard(r, cx, before);
        return Ok(None);
    }
    // The root over the sums as written: each node below it once, operands first. A sum as
    // written is taken as it was built: no sum is replaced inside one (it may read another
    // of the sums on more bits than reach the root from that one, and the two agree only
    // there).
    let to: IdMap<u32, u32> = kept.iter().copied().collect();
    let mut done: IdMap<u32, u32> = IdMap::default();
    let mut atoms: Vec<u32> = Vec::new();
    let mut walk = vec![(root, false)];
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    while let Some((u, expanded)) = walk.pop() {
        if done.contains_key(&u) {
            continue;
        }
        if let Some(&e) = to.get(&u) {
            done.insert(u, e);
            continue;
        }
        let node = cx.node(u);
        if !expanded {
            walk.push((u, true));
            walk.extend(node.children().map(|c| (c, false)));
            continue;
        }
        let mut kids = [node.a, node.b, node.c];
        let mut changed = false;
        for k in kids.iter_mut().take(node.op.arity()) {
            if let Some(&t) = done.get(k)
                && t != *k
            {
                *k = t;
                changed = true;
            }
        }
        if !changed {
            done.insert(u, u);
            continue;
        }
        for (k, c) in kids.iter().zip(node.children()) {
            if *k == c {
                atoms.push(c);
            }
        }
        let v = r.build(cx, |cx| cx.rebuild(u, kids))?;
        done.insert(u, v);
    }
    let e = done.get(&root).copied().unwrap_or(root);
    if e == root {
        super::discard(r, cx, before);
        return Ok(None);
    }
    // What the sums as written read and is as it was: the nodes below the root as it is. By
    // the root's own nodes, not by what the arena held before: a node an earlier candidate
    // left there is as new to the root as one built now.
    let below: IdMap<u32, ()> = order.iter().map(|&i| (i, ())).collect();
    let mut seen: IdMap<u32, ()> = IdMap::default();
    for &(_, e) in &kept {
        let mut stack = vec![e];
        while let Some(i) = stack.pop() {
            if seen.insert(i, ()).is_some() {
                continue;
            }
            r.meter.charge(Counter::PassWork, 1)?;
            if below.contains_key(&i) {
                atoms.push(i);
            } else {
                stack.extend(cx.node(i).children());
            }
        }
    }
    super::discard_but(r, cx, before, e);
    r.explain_with(|| crate::engine::Explanation::Demanded {
        operand: cx.handle(root),
        mask: BitVec::ones(cx.width_of(root)),
    });
    let tree = |i: u32| cx.meta[i as usize].tree;
    let tie = tree(root) != u32::MAX && tree(e) < tree(root);
    Ok(
        match super::finish_with(r, cx, PassKind::Demanded, root, e, before, &atoms, fin, tie)? {
            Step::To(e, f) => Some(Step::To(e, f)),
            Step::Normal(_) => None,
        },
    )
}

/// The demanded-bits pass at the root of a walk, once the walk is done.
///
/// A rewrite replaces a node by an equal one, so a sum cannot be replaced by a value that
/// agrees with it only on the bits its users read: the pass rewrites at each user instead,
/// under that user's bits (or those of all the users below one observed operand, see
/// [`unions`]), and a user whose rewrite leaves the sum to the others does not pay. The root
/// is the one node below which every user of every node is: its value stays what it was when
/// each node below it is replaced by a value equal to that node on the bits of it that
/// reach the root ([`demands`]). So a sum with carries is read here on those bits, where
/// they are few enough for its carries (see `borrows`), every user of it reads the reading,
/// and the commit rule counts the sum as gone.
///
/// Each reading is first costed at its sum, as if it were a rewrite there (the users are
/// written again one for one). The readings that pay there, and those that would if nothing
/// else read the sum's operands (the limbs of one word share the code each of them would
/// free), are put into the root together; where that does not pay, or pays less, only the
/// former are. The root so written replaces the root under the commit rule, as any rewrite.
///
/// The readings that leave a sum no fewer terms (see `borrows::expanded`) are taken last:
/// with `late` (the late stage of the rounds, see `Runner::rounds`), and where the others
/// leave the root as it is, they are put in with them. The digits such a reading leaves may
/// meet those of another sum, or be slices of words that are there: only the root shows
/// which. So each is kept whatever it costs at its own sum, a reading that leaves fewer
/// terms goes before one that does not where one sum is a term of the other, and the root
/// is costed whole: no node is taken as given (such a reading stops at nodes it built
/// itself), every node the new root needs counts against every node the old one frees.
/// Taken before the rounds are done, such a reading is in the way of what the passes read
/// better (the slice of a word, the readings above, the sum a term of its own is in).
///
/// A rewrite with such readings leaves the DAG smaller, or as large and the root a smaller
/// tree, as every rewrite of the step: (DAG nodes, tree size) decreases, and nothing is
/// read back as the carries it was read from.
#[cfg(feature = "prove")]
pub(crate) fn whole(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    late: bool,
) -> Result<Step, Stop> {
    read(r, cx, root, late, false)
}

/// Whether [`whole`] would rewrite `root` with the readings of the late stage: costed as it
/// costs them, nothing rewritten (what is built is taken back).
#[cfg(feature = "prove")]
pub(crate) fn late(r: &mut Runner<'_, '_>, cx: &mut Context, root: u32) -> Result<bool, Stop> {
    Ok(matches!(read(r, cx, root, true, true)?, Step::To(..)))
}

/// [`whole`]; with `dry`, only whether the readings of the late stage would rewrite the
/// root (`Step::To` then, of a node that is taken back).
#[cfg(feature = "prove")]
fn read(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    late: bool,
    dry: bool,
) -> Result<Step, Stop> {
    let Some((order, read)) = demands(r, cx, root)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    // One word for the sums that are a word's low bits, first (see `words`).
    if !dry && let Some(step) = words(r, cx, root, &order, &read)? {
        return Ok(step);
    }
    let mut fin = Fin::FINAL;
    // (What the readings that leave their sums no fewer terms relied on.)
    let mut fin_tied = Fin::FINAL;
    let mut limbs: Vec<Limb> = Vec::new();
    // The nodes something other than a sum reads: a sum only sums read is terms of theirs.
    let mut outer: IdMap<u32, ()> = IdMap::default();
    outer.insert(root, ());
    for &u in &order {
        let node = cx.node(u);
        if !matches!(node.op, OpCode::Add | OpCode::Sub | OpCode::Neg) {
            for c in node.children() {
                outer.insert(c, ());
            }
        }
    }
    for &x in &order {
        if !carries(cx, x) {
            continue;
        }
        let Some(m) = read.get(&x) else {
            continue;
        };
        let w = cx.wid(x);
        let j = crate::facts::known::count_ones(&low_prefix(m)) as u16;
        if j == 0 {
            continue;
        }
        let before = cx.len() as u32;
        let Some((low, f, stops, tied)) = super::borrows::expanded(r, cx, x, j, late)? else {
            continue;
        };
        // (A reading that leaves no fewer terms is costed whole: it stops at nodes it built.)
        let stops = if tied { Vec::new() } else { stops };
        if tied {
            fin_tied = fin_tied.and(f.unchanged());
        } else {
            fin = fin.and(f.unchanged());
        }
        // The reading at the sum's width: extended, or over the sum's own terms. Each is
        // costed with nothing else there.
        let e = if j < w {
            r.build(cx, |cx| cx.c_zext(low, w))?
        } else {
            low
        };
        let slack = i64::from(super::carries::slack(cx, x, e, before));
        let mut best = super::margins(r, cx, x, e, &stops)?.map(|(s, a)| (e, s, a, slack));
        super::discard(r, cx, before);
        if j < w
            && let Some(e) = lifted(r, cx, x, low, j)?
        {
            let slack = i64::from(super::carries::slack(cx, x, e, before));
            let m = super::margins(r, cx, x, e, &stops)?;
            super::discard(r, cx, before);
            // (One the commit rule could take at all, before one it would take sooner.)
            if let Some((s, a)) = m
                && best.is_none_or(|(_, bs, ba, bk)| (a + slack > 0, s, a) > (ba + bk > 0, bs, ba))
            {
                best = Some((e, s, a, slack));
            }
        }
        let Some((e, shared, alone, slack)) = best else {
            continue;
        };
        // (One that leaves no fewer terms pays in the root or nowhere.)
        if e == x || (alone + slack <= 0 && !tied) {
            continue;
        }
        let pays = shared + slack > 0;
        if !pays {
            if tied {
                fin_tied = fin_tied.and(Fin::PROVISIONAL);
            } else {
                fin = fin.and(Fin::PROVISIONAL);
            }
        }
        limbs.push(Limb {
            x,
            e,
            fin: f,
            stops,
            pays,
            shared,
            tied,
        });
    }
    if limbs.iter().all(|l| !l.tied) {
        // (Asked for the late readings alone: there is none.)
        if dry {
            return Ok(Step::Normal(fin));
        }
        return taken(r, cx, &order, &outer, root, limbs, fin, false);
    }
    // The readings that leave their sums fewer terms first (the step has asked for them
    // before the late ones are asked about: not again for the answer alone).
    if !dry {
        let strict: Vec<Limb> = limbs.iter().filter(|l| !l.tied).cloned().collect();
        match taken(r, cx, &order, &outer, root, strict, fin, false)? {
            Step::Normal(f) => fin = f,
            step => return Ok(step),
        }
    }
    taken(r, cx, &order, &outer, root, limbs, fin.and(fin_tied), dry)
}

/// The root with the readings `limbs` of the sums below it, under the commit rule (see
/// [`whole`]); `fin` is what reading them relied on. With `dry`, only whether the rule
/// would take it.
#[cfg(feature = "prove")]
#[allow(clippy::too_many_arguments)]
fn taken(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    order: &[u32],
    outer: &IdMap<u32, ()>,
    root: u32,
    mut limbs: Vec<Limb>,
    mut fin: Fin,
    dry: bool,
) -> Result<Step, Stop> {
    // A sum only sums read is terms of theirs, and its reading goes where theirs is taken: of
    // two such readings the one that leaves fewer terms, then the one that pays (then the
    // one that pays more, then the outer one) stays.
    let mut dropped = vec![false; limbs.len()];
    let mut stack = Vec::new();
    let mut seen: IdMap<u32, ()> = IdMap::default();
    for u in 0..limbs.len() {
        stack.clear();
        seen.clear();
        stack.push(limbs[u].x);
        while let Some(i) = stack.pop() {
            r.meter.charge(Counter::PassWork, 1)?;
            for c in cx.node(i).children() {
                let sum = matches!(cx.node(c).op, OpCode::Add | OpCode::Sub | OpCode::Neg);
                if !sum || outer.contains_key(&c) || seen.insert(c, ()).is_some() {
                    continue;
                }
                if let Some(l) = limbs.iter().position(|l| l.x == c) {
                    let (below, above) = (&limbs[l], &limbs[u]);
                    let key = |l: &Limb| (!l.tied, l.pays, l.shared);
                    if key(below) > key(above) {
                        dropped[u] = true;
                    } else {
                        dropped[l] = true;
                    }
                }
                stack.push(c);
            }
        }
    }
    let mut k = 0;
    limbs.retain(|_| {
        k += 1;
        !dropped[k - 1]
    });
    if limbs.is_empty() {
        return Ok(Step::Normal(fin));
    }
    let before = cx.len() as u32;
    let some = limbs.iter().any(|l| l.pays);
    let all = limbs.iter().all(|l| l.pays);
    // With a reading that leaves no fewer terms, the root is costed whole: nothing below it
    // is taken as given.
    let whole = limbs.iter().any(|l| l.tied);
    let given = |atoms: Vec<u32>| if whole { Vec::new() } else { atoms };
    // Every reading, costed and taken back; then those that pay at their sums.
    let (e, atoms) = replaced(r, cx, order, root, &limbs, false)?;
    let atoms = given(atoms);
    let every = if e == root {
        None
    } else {
        super::margin(r, cx, root, e, &atoms)?
    };
    let mut paying = false;
    if some && !all {
        super::discard(r, cx, before);
        let (e, atoms) = replaced(r, cx, order, root, &limbs, true)?;
        let atoms = given(atoms);
        let few = if e == root {
            None
        } else {
            super::margin(r, cx, root, e, &atoms)?
        };
        paying = few.is_some_and(|b| every.is_none_or(|a| b > a));
    }
    super::discard(r, cx, before);
    let (e, atoms) = replaced(r, cx, order, root, &limbs, paying)?;
    let atoms = given(atoms);
    super::discard_but(r, cx, before, e);
    for l in limbs.iter().filter(|l| l.pays || !paying) {
        fin = fin.and(l.fin);
    }
    // Also where the DAG stays the size it was and the root becomes a smaller tree (a reading
    // is not read back as the carries it was read from, so no two such rewrites undo each
    // other; see `finish_with`).
    let tree = |i: u32| cx.meta[i as usize].tree;
    let tie = tree(root) != u32::MAX && tree(e) < tree(root);
    if dry {
        let pays = e != root
            && super::margin(r, cx, root, e, &atoms)?.is_some_and(|m| m + i64::from(tie) > 0);
        super::discard(r, cx, before);
        return Ok(if pays {
            Step::To(e, fin)
        } else {
            Step::Normal(fin)
        });
    }
    r.explain_with(|| crate::engine::Explanation::Demanded {
        operand: cx.handle(root),
        mask: BitVec::ones(cx.width_of(root)),
    });
    super::finish_with(r, cx, PassKind::Demanded, root, e, before, &atoms, fin, tie)
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry("demanded").or_default()
}

/// The demanded-bits pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let w = cx.width_of(n);
    if let Some(x) = clears_known_zeros(r, cx, n)? {
        let before = cx.len() as u32;
        return finish(r, cx, PassKind::Demanded, n, x, before, &[x], Fin::FINAL);
    }
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
        memo: std::mem::take(&mut r.demanded),
        cap: MAX_VISITS.min(super::region_cap(r)),
        stops: Vec::new(),
        visits: 0,
        fin: Fin::FINAL,
        before,
        root: operand,
        xors: Vec::new(),
        identities: Vec::new(),
        union: IdMap::default(),
    };
    // (Before anything is simplified: the identities remembered below depend on where the
    // sums with carries are, which this finds.)
    #[cfg(feature = "prove")]
    unions(r, cx, &mut st, operand, &mask)?;
    let union = std::mem::take(&mut st.union);
    let x2 = simplify(r, cx, &mut st, operand, &mask)?;
    // The operands this step found nothing to simplify under their masks are remembered for
    // the phase run (every mask over one shared chain re-walked it, once per mask, and asked
    // the facts again at every node): their values are fixed, so the answer is too. Not when
    // the cap cut the walk short (an answer of more budget may differ), and not the
    // simplifications, whose nodes a rejection retires.
    if st.visits <= st.cap {
        for &(key, from, to) in &st.identities {
            if r.demanded_same.map.contains_key(&key) {
                continue;
            }
            // Each leaf once. A range holds what the hits below it copied, the leaves of each
            // operand; operands share leaves in a DAG, so a range kept with its repeats was
            // the sum of its operands' ranges, and on a ripple chain the ranges doubled at
            // every level (2^48 at 48 bits). The leaves are read as a set.
            let at = r.demanded_same.leaves.len();
            r.demanded_same
                .leaves
                .extend_from_slice(&st.stops[from as usize..to as usize]);
            let kept = sorted_distinct(&mut r.demanded_same.leaves[at..]);
            r.demanded_same.leaves.truncate(at + kept);
            r.demanded_same.map.insert(key, (at as u32, kept as u32));
        }
    }
    st.memo.clear();
    let capped = st.visits > st.cap;
    if capped {
        count(r).atomized += 1;
    }
    let rebuilt = |r: &mut Runner<'_, '_>, cx: &mut Context, x: u32| {
        let mut kids = [node.a, node.b, node.c];
        for k in kids.iter_mut().take(node.op.arity()) {
            if *k == operand {
                *k = x;
            }
        }
        r.build(cx, |cx| cx.rebuild(n, kids))
    };
    let (mut x2, mut fin, mut stops) = (x2, st.fin, std::mem::take(&mut st.stops));
    // A node read under several masks was written once for each (a word each of its limbs
    // reads, its constants reduced to each reader's bits: one copy a reader). A second
    // simplification writes it once, on the bits any of its users reads, and stays where it
    // frees no fewer nodes: what it keeps of the word, every reader shares.
    if !union.is_empty() && !capped {
        let mut st2 = Demand {
            memo: std::mem::take(&mut st.memo),
            cap: st.cap,
            stops: Vec::new(),
            visits: 0,
            fin: Fin::FINAL,
            before,
            root: operand,
            xors: Vec::new(),
            identities: Vec::new(),
            union,
        };
        let x3 = simplify(r, cx, &mut st2, operand, &mask)?;
        st2.memo.clear();
        st.memo = std::mem::take(&mut st2.memo);
        if x3 != x2 && st2.visits <= st2.cap {
            let (e2, e3) = (rebuilt(r, cx, x2)?, rebuilt(r, cx, x3)?);
            let m2 = super::margin(r, cx, n, e2, &stops)?;
            let m3 = super::margin(r, cx, n, e3, &st2.stops)?;
            if m3.is_some_and(|b| m2.is_none_or(|a| b >= a)) {
                (x2, fin, stops) = (x3, st2.fin, st2.stops);
            }
        }
        // (What the other simplification built is no use of the nodes below it.)
        let keep = rebuilt(r, cx, x2)?;
        super::discard_but(r, cx, before, keep);
    }
    r.demanded = std::mem::take(&mut st.memo);
    if x2 == operand {
        count(r).noop += 1;
        return Ok(Step::Normal(fin));
    }
    let e = rebuilt(r, cx, x2)?;
    r.explain_with(|| crate::engine::Explanation::Demanded {
        operand: cx.handle(operand),
        mask,
    });
    finish(r, cx, PassKind::Demanded, n, e, before, &stops, fin)
}
