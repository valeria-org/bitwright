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
    /// The nodes asked before their operands were walked, and every node such a question
    /// read (see [`first`]); `marking` while one is asked.
    first: IdMap<u32, ()>,
    marking: bool,
}

impl Same {
    pub(crate) fn clear(&mut self) {
        self.map.clear();
        self.leaves.clear();
        self.carried.clear();
        self.first.clear();
        self.marking = false;
    }
}

/// The height from which a node that observes an operand is asked before its operands are
/// walked (see [`first`]): a deep expression, where levels may be out of every mask's reach.
const FIRST_HEIGHT: u32 = 64;

/// The operand `n` observes through a mask, and the mask: `x & k`, `x | k`, an extraction, a
/// shift by a constant.
fn observed(cx: &Context, n: u32) -> Option<(u32, BitVec)> {
    let node = cx.node(n);
    let w = cx.width_of(n);
    match node.op {
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
                Some((x, m))
            }
            _ => None,
        },
        OpCode::Extract => {
            let wa = cx.width_of(node.a);
            let lo = BitVec::wrapping_from_u64(wa, u64::from(node.b));
            let m = BitVec::bin_unchecked(BinOp::Shl, &low_mask(wa, u32::from(w.bits())), &lo);
            Some((node.a, m))
        }
        OpCode::Shl | OpCode::LShr => cx.const_val(node.b).map(|k| {
            let back = if node.op == OpCode::Shl {
                BinOp::LShr
            } else {
                BinOp::Shl
            };
            (node.a, BitVec::bin_unchecked(back, &BitVec::ones(w), &k))
        }),
        _ => None,
    }
}

/// Whether the walk asks `n` before it walks `n`'s operands (see [`first`]).
pub(crate) fn asks_first(r: &Runner<'_, '_>, cx: &Context, n: u32) -> bool {
    cx.meta[n as usize].height >= FIRST_HEIGHT
        && !r.demanded.same.first.contains_key(&n)
        && observed(cx, n).is_some()
}

/// The pass at a tall node that observes an operand, before the walk has come to that operand:
/// `Some` rewrite when it is taken, and the walk goes on from it. The walk is operands first,
/// and so it simplified every level of a deep expression under the masks of the levels just
/// above it before it reached the node whose mask leaves most of them unread: under
/// `(e << k) | s` nested 3000 times only the last 64 bits' worth of levels reach the result,
/// and each of the others was rebuilt over a window of 32 levels in turn, 6 s in all. Asked
/// at the top first, the levels out of reach are never walked. One question covers what it
/// read: the nodes in it are not asked first again, so a deep expression with nothing to drop
/// is asked once per stretch of it, not once per node.
pub(crate) fn first(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<(u32, Fin)>, Stop> {
    r.demanded.same.first.insert(n, ());
    r.demanded.same.marking = true;
    let out = super::step(r, cx, PassKind::Demanded, n);
    r.demanded.same.marking = false;
    Ok(match out? {
        Step::To(x, fin) => Some((x, fin)),
        Step::Normal(_) => None,
    })
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
    /// Results of earlier simplifications that this one reads and does not write (see
    /// [`reduced`]); empty for the pass's own steps.
    base: Memo,
    /// The results found before the cap cut the walk short, where they are kept for later
    /// simplifications (`None` for the pass's own steps): each was found with every operand
    /// below it read in full, so more visits would not change it.
    whole: Option<Vec<(Key, u32)>>,
    /// Whether a sum's constant stays one constant under every mask (see [`same_on`]).
    whole_sums: bool,
    /// The most nodes one simplification visits (the strategy may lower [`MAX_VISITS`]).
    cap: u32,
    /// Whether this simplification records region-boundary `stops` and `identities` (`true` for
    /// `demanded::step`; `false` for `reduced`, `under_mask`, and `prove_masked_equal`, which
    /// discard `stops`).
    track_stops: bool,
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
    /// Whether a sum was read as a xor (see [`carried`]): the result is then taken at the
    /// same size too.
    ties: bool,
}

impl Demand {
    /// Remembers `v` as the result for `key`.
    fn note(&mut self, key: Key, v: u32) {
        self.memo.insert(key, v);
        if self.visits <= self.cap
            && let Some(whole) = &mut self.whole
        {
            whole.push((key, v));
        }
    }
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
        OpCode::RotL | OpCode::RotR => {
            if let Some(k) = konst(node.b) {
                let back = if node.op == OpCode::RotL {
                    BinOp::RotR
                } else {
                    BinOp::RotL
                };
                out.push((node.a, BitVec::bin_unchecked(back, m, &k)));
            }
        }
        OpCode::Select => {
            out.extend([
                (node.b, *m),
                (node.c, *m),
                (node.a, BitVec::one(Width::W1)),
            ]);
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

/// The most constants kept per operand by [`same_on`].
const SUM_CONSTANTS: usize = 8;

/// The constant `kc` (value `k`) of a sum over the operand `key.0` (`key.1`: `t + k`, `t − k`
/// or `k − t`), read on the prefix `p`: the first constant this call's reductions added to
/// that operand so that agrees with `k` on `p`, else `kc` itself, which is then kept.
fn same_on(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    key: (u32, u8),
    kc: u32,
    k: &BitVec,
    p: &BitVec,
) -> u32 {
    let seen = r.demanded.sum_constants.entry(key).or_default();
    for &c in seen.iter() {
        if let Some(v) = cx.const_val(c)
            && bv_and(&BitVec::bin_unchecked(BinOp::Xor, &v, k), p).is_zero()
        {
            return c;
        }
    }
    if seen.len() < SUM_CONSTANTS {
        seen.push(kc);
    }
    kc
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
    if let Some(&v) = st
        .memo
        .get(&Key(x, *m))
        .or_else(|| st.base.get(&Key(x, *m)))
    {
        return Ok(v);
    }
    // Found nothing to simplify under this mask in an earlier step of the phase run: the same
    // leaves as then.
    if let Some(&(from, len)) = r.demanded.same.map.get(&Key(x, *m)) {
        if st.track_stops {
            let (from, len) = (from as usize, len as usize);
            st.stops
                .extend_from_slice(&r.demanded.same.leaves[from..from + len]);
        }
        st.note(Key(x, *m), x);
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
        st.note(Key(x, *m), v);
        return Ok(v);
    }
    if st.visits > st.cap || cx.const_val(x).is_some() {
        let v = stop(cx, st)?;
        st.note(Key(x, *m), v);
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
            st.note(Key(x, *m), c);
            return Ok(c);
        }
    }
    // Demanded bits among the lowest few: the residues of `x` decide them (a constant, or a
    // leaf equal to `x` there).
    if let Some(v) = by_residues(r, cx, x, m)? {
        if !cx.is_const(v) {
            stop_at(cx, st, v);
        }
        st.note(Key(x, *m), v);
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
        st.note(Key(x, *m), v);
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
            st.note(Key(x, *m), v);
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
            st.note(Key(x, *m), v);
            return Ok(v);
        }
    }
    // The limbs of one word in a sum, joined modulo the demanded prefix (see `limbs`): a
    // coefficient that is 0 there reads nothing, and one with trailing zeros a narrower limb.
    if matches!(node.op, OpCode::Add | OpCode::Sub)
        && let Some(v) = joined(r, cx, st, x, m)?
    {
        st.note(Key(x, *m), v);
        return Ok(v);
    }
    let mut skip_same_cache = false;
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
                    // Over an operand written anew the mask is new too, and is the bits of
                    // it that are read: `(t & 0x2441201) · c` under `& 0x7f` reads bit 0 of
                    // `t`, and `t & 1` says so to what reads the result next. Over the
                    // operand as it is, only where nothing else reads the masked value (it
                    // stays one node for its other readers): the narrower mask is then a
                    // constant for a constant, smaller where the candidate has it already.
                    let narrow = bv_and(m, &k);
                    let narrowed_once = narrow != k && read_once(r, cx, x)?;
                    let k_use = if a2 != a || narrowed_once {
                        narrow
                    } else {
                        if narrow != k {
                            st.fin = st.fin.and(Fin::PROVISIONAL);
                            skip_same_cache = true;
                        }
                        k
                    };
                    let kc = r.build(cx, |cx| cx.mk_const(&k_use))?;
                    bin(r, cx, BinOp::And, a2, kc)?
                }
            }
            _ => {
                let a = simplify(r, cx, st, node.a, m)?;
                let b = simplify(r, cx, st, node.b, m)?;
                // An operand the demanded bits made a constant: with every demanded bit
                // set the other operand is the result there, and with none of them zero is.
                match (konst(cx, a), konst(cx, b)) {
                    (Some(k), None) if subset(m, &k) => b,
                    (None, Some(k)) if subset(m, &k) => a,
                    (Some(k), None) | (None, Some(k)) if bv_and(m, &k).is_zero() => {
                        r.build(cx, |cx| cx.mk_const(&BitVec::zero(w)))?
                    }
                    _ => bin(r, cx, BinOp::And, a, b)?,
                }
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
                    let narrow = bv_and(m, &k);
                    let narrowed_once = narrow != k && read_once(r, cx, x)?;
                    let k_use = if a2 != a || narrowed_once {
                        narrow
                    } else {
                        if narrow != k {
                            st.fin = st.fin.and(Fin::PROVISIONAL);
                            skip_same_cache = true;
                        }
                        k
                    };
                    let kc = r.build(cx, |cx| cx.mk_const(&k_use))?;
                    bin(r, cx, BinOp::Or, a2, kc)?
                }
            }
            _ => {
                let a = simplify(r, cx, st, node.a, m)?;
                let b = simplify(r, cx, st, node.b, m)?;
                // As for `&`: an operand that became a constant with none of the demanded
                // bits leaves the other, and one with all of them is the result.
                match (konst(cx, a), konst(cx, b)) {
                    (Some(k), None) if bv_and(m, &k).is_zero() => b,
                    (None, Some(k)) if bv_and(m, &k).is_zero() => a,
                    (Some(k), None) if subset(m, &k) => a,
                    (None, Some(k)) if subset(m, &k) => b,
                    _ => bin(r, cx, BinOp::Or, a, b)?,
                }
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
                let same_twin = st.xors.iter().find(|(a1, k1, m1, _)| {
                    *a1 == a
                        && subset(m, m1)
                        && bv_and(&BitVec::bin_unchecked(BinOp::Xor, k1, &k), m).is_zero()
                });
                if let Some(&(_, _, _, y)) = same_twin {
                    stop_at(cx, st, y);
                    y
                } else {
                    let comp_twin = st.xors.iter().find(|(a1, k1, m1, _)| {
                        *a1 == a && subset(m, m1) && subset(m, &bv_or(k1, &k)) && {
                            let both = bv_and(k1, &k);
                            bv_and(&both, m).is_zero()
                        }
                    });
                    if let Some(&(_, _, _, y)) = comp_twin {
                        stop_at(cx, st, y);
                        r.build(cx, |cx| cx.c_un(UnOp::Not, y))?
                    } else {
                        let a2 = simplify(r, cx, st, a, m)?;
                        let narrow = bv_and(m, &k);
                        super::refresh_uses(r, cx)?;
                        let existing_narrow = if narrow != k {
                            narrow
                                .to_u64()
                                .and_then(|v| cx.find_const_u64(w.bits(), v))
                                .and_then(|kc| {
                                    cx.find(&crate::expr::Node::new(
                                        OpCode::Xor,
                                        w.bits(),
                                        a2,
                                        kc,
                                        0,
                                    ))
                                    .or_else(|| {
                                        cx.find(&crate::expr::Node::new(
                                            OpCode::Xor,
                                            w.bits(),
                                            kc,
                                            a2,
                                            0,
                                        ))
                                    })
                                })
                                .filter(|&yid| {
                                    !r.life.dead.contains(yid)
                                        && r.life.live.uses(yid).is_some_and(|u| u > 0)
                                })
                        } else {
                            None
                        };
                        if let Some(yid) = existing_narrow {
                            stop_at(cx, st, yid);
                            if a2 == a {
                                st.ties = true;
                            }
                            st.xors.push((a, narrow, *m, yid));
                            yid
                        } else {
                            let narrowed_once = narrow != k && read_once(r, cx, x)?;
                            let k_use = if a2 != a || narrowed_once {
                                narrow
                            } else {
                                if narrow != k {
                                    st.fin = st.fin.and(Fin::PROVISIONAL);
                                    skip_same_cache = true;
                                }
                                k
                            };
                            let kc = r.build(cx, |cx| cx.mk_const(&k_use))?;
                            let y = bin(r, cx, BinOp::Xor, a2, kc)?;
                            st.xors.push((a, k_use, *m, y));
                            y
                        }
                    }
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
            // One value read under several masks stays one value in the sweep's reductions:
            // a sum's constant is the first one added to that operand in this call that
            // agrees with it on the prefix, not its residue there, which differs from mask to
            // mask (`t + k` under `& 0xff` and under `& 0xffff` would be two sums, each an atom
            // of its own to a certificate, and what cancels through `t + k` is gone).
            let whole_sum = st.whole_sums && node.op != OpCode::Mul;
            let (ka, kb) = (cx.const_val(node.a), cx.const_val(node.b));
            let (a, b) = match (whole_sum, ka, kb) {
                (true, None, Some(k)) => {
                    let a = simplify(r, cx, st, node.a, &p)?;
                    let kind = u8::from(node.op == OpCode::Sub);
                    (a, same_on(r, cx, (a, kind), node.b, &k, &p))
                }
                (true, Some(k), None) => {
                    let b = simplify(r, cx, st, node.b, &p)?;
                    let kind = if node.op == OpCode::Sub { 2 } else { 0 };
                    (same_on(r, cx, (b, kind), node.a, &k, &p), b)
                }
                _ => (
                    simplify(r, cx, st, node.a, &p)?,
                    simplify(r, cx, st, node.b, &p)?,
                ),
            };
            let op = node.op.as_bin().unwrap_or(BinOp::Add);
            // a constant addend with none of the demanded bits goes (`63 - ~y`
            // is `y + 64`, which is `y` on the low six bits).
            // A constant addend whose every carry on the prefix is known flips known bits of
            // the other operand: a xor there (see `carried`).
            let flipped = match (node.op, dropped_constant(cx, node.op, a, b, &p)) {
                (OpCode::Mul, _) | (_, Some(_)) => None,
                // Over the operand as it is written: the same on the prefix, and the xor is
                // then one node for one (the operand read under the prefix is new nodes
                // wherever a constant below it has another residue there).
                _ => {
                    let (ta, tb) = (
                        if cx.const_val(a).is_some() { a } else { node.a },
                        if cx.const_val(b).is_some() { b } else { node.b },
                    );
                    carried(r, cx, st, x, ta, tb, &p)?
                }
            };
            let ones = |j: u32| cx.const_val(j).is_some_and(|k| k.is_ones());
            match dropped_constant(cx, node.op, a, b, &p).or(flipped) {
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
        OpCode::RotL | OpCode::RotR if konst(cx, node.b).is_some() => {
            let k = konst(cx, node.b).unwrap_or(BitVec::zero(w));
            let (op, back) = if node.op == OpCode::RotL {
                (BinOp::RotL, BinOp::RotR)
            } else {
                (BinOp::RotR, BinOp::RotL)
            };
            let ma = BitVec::bin_unchecked(back, m, &k);
            let a = simplify(r, cx, st, node.a, &ma)?;
            bin(r, cx, op, a, node.b)?
        }
        OpCode::Select => {
            let c = simplify(r, cx, st, node.a, &BitVec::one(Width::W1))?;
            let t = simplify(r, cx, st, node.b, m)?;
            let f = simplify(r, cx, st, node.c, m)?;
            if t == f {
                t
            } else {
                r.build(cx, |cx| cx.c_select(c, t, f))?
            }
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
    st.note(Key(x, *m), v);
    // (Not above a sum with carries: what it is read as depends on its other users.)
    if st.track_stops
        && !skip_same_cache
        && v == x
        && x < st.before
        && r.demanded.same.carried.get(&x) != Some(&true)
    {
        st.identities
            .push((Key(x, *m), stops0, st.stops.len() as u32));
    }
    Ok(v)
}

/// Whether `x` has one reader and is no root: what it is read as is that reader's alone.
fn read_once(r: &mut Runner<'_, '_>, cx: &Context, x: u32) -> Result<bool, Stop> {
    super::refresh_uses(r, cx)?;
    Ok(r.life.live.uses(x) == Some(1) && !r.life.live_roots.contains(&x))
}

/// Records `x` as a node the simplification stops at: a node it built itself is no leaf of the
/// region (the commit rule counts it), so the nodes below it that existed are.
fn stop_at(cx: &Context, st: &mut Demand, x: u32) {
    if !st.track_stops {
        return;
    }
    if x < st.before {
        st.stops.push(x);
        return;
    }
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack = vec![x];
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
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

/// `t ^ k'` when `a op b` (an `add` or `sub` of at most 64 bits) is `t` plus or minus a
/// constant, or a constant less `t`, and on the prefix `p` every carry (or borrow) is known
/// from the bits known of `t`: the result then differs from `t` in fixed bits there. An obfuscator writes `t ^ k'` as
/// `t + k` over a `t` it knows bits of (`t + 0x7ff0` where bit 4 of `t` is set and bit 15
/// clear is `t ^ 0x8010`), and a value written both ways is two unrelated atoms to the MBA
/// phase. A carry is known where the constant's bit equals the carry in (it goes on
/// whatever `t` has there) or `t`'s bit is known. Marks the simplification as one that
/// commits at the same size: the xor is what `add_disjoint` and the masks keep, and nothing
/// writes it back as a sum. `x` is the sum itself, which must have no other reader.
fn carried(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    st: &mut Demand,
    x: u32,
    a: u32,
    b: u32,
    p: &BitVec,
) -> Result<Option<u32>, Stop> {
    let w = p.width();
    if w.bits() > 64 {
        return Ok(None);
    }
    let op = cx.node(x).op;
    // `t + k`, or `k − t`: the same walk with a borrow.
    let (t, k, from) = match (op, cx.const_val(a), cx.const_val(b)) {
        (OpCode::Add, None, Some(k)) => (a, k, false),
        (OpCode::Add, Some(k), None) => (b, k, false),
        (OpCode::Sub, None, Some(k)) => (a, BitVec::un_unchecked(UnOp::Neg, &k), false),
        (OpCode::Sub, Some(k), None) => (b, k, true),
        _ => return Ok(None),
    };
    let (pw, kw) = (p.limbs()[0], k.limbs()[0]);
    let (known, fin) = known_words(r, cx, t)?;
    let Some([zero, one]) = known else {
        return Ok(None);
    };
    let n = 64 - pw.leading_zeros();
    let (mut carry, mut flips) = (false, 0u64);
    for j in 0..n {
        let bit = 1u64 << j;
        let kj = kw & bit != 0;
        // The sum's bit is `t ^ k ^ carry`, and so is the difference's with its borrow.
        if kj != carry {
            flips |= bit;
        }
        // A carry out is the constant's bit where the carry in is the same, else `t`'s bit;
        // a borrow out is the borrow in where the constant's bit differs from it (none
        // under a set bit, one under a clear bit that already owes), else `t`'s bit.
        // (The last bit's goes nowhere.)
        let settled = if from { kj != carry } else { kj == carry };
        if !settled && j + 1 < n {
            if (zero | one) & bit == 0 {
                return Ok(None);
            }
            carry = one & bit != 0;
        }
    }
    // A sum that changes nothing on the prefix is the dropped constant's case.
    if flips & pw == 0 && !from {
        return Ok(None);
    }
    // Only a sum this reader alone reads: one read under several masks is one value to all
    // of them (`t + k` under `& 0xff` and under `& 0xffff` flips other bits of `t` under
    // each, and what cancelled through the sum would be gone).
    super::refresh_uses(r, cx)?;
    if r.life.live.uses(x) != Some(1) || r.life.live_roots.contains(&x) {
        return Ok(None);
    }
    st.fin = st.fin.and(fin);
    st.ties = true;
    // The operand is read as it is: a leaf of the result. So is the constant, which stands
    // where the sum's did (the commit rule counts a new constant and no old one).
    st.stops.push(t);
    let kx = BitVec::from_canonical_u64(w, flips & pw);
    let c = r.build(cx, |cx| cx.mk_const(&kx))?;
    st.stops.push(c);
    Ok(Some(r.build(cx, |cx| cx.c_bin(BinOp::Xor, t, c))?))
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
    whole_sums: bool,
) -> Result<u32, Stop> {
    let w = cx.width_of(x);
    let which = usize::from(whole_sums);
    let mut st = Demand {
        memo: Memo::default(),
        base: std::mem::take(&mut r.demanded.reduced[which]),
        whole: Some(Vec::new()),
        whole_sums,
        cap,
        track_stops: false,
        stops: Vec::new(),
        visits: 0,
        fin: Fin::FINAL,
        before: cx.len() as u32,
        root: x,
        xors: Vec::new(),
        identities: Vec::new(),
        union: IdMap::default(),
        ties: false,
    };
    let out = simplify(r, cx, &mut st, x, &BitVec::ones(w));
    // What this simplification found is kept for the call's later ones, up to where the cap
    // cut it short (an answer of more visits may differ). A node's value on a mask is fixed,
    // so the answer is too; the sweep asks this of every candidate, operands first, and each
    // walked the whole of what the ones below it had walked.
    let mut base = std::mem::take(&mut st.base);
    if out.is_ok() {
        base.extend(st.whole.take().unwrap_or_default());
    }
    r.demanded.reduced[which] = base;
    out
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
fn over_carries(r: &mut Runner<'_, '_>, cx: &Context, x: u32) -> Result<bool, Stop> {
    let mut stack = vec![(x, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.demanded.same.carried.contains_key(&i) {
            continue;
        }
        if carries(cx, i) {
            r.demanded.same.carried.insert(i, true);
            continue;
        }
        if !reads_through(cx, i) {
            r.demanded.same.carried.insert(i, false);
            continue;
        }
        let node = cx.node(i);
        if expanded {
            let any = node
                .children()
                .any(|c| r.demanded.same.carried.get(&c) == Some(&true));
            r.demanded.same.carried.insert(i, any);
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        stack.push((i, true));
        for c in node.children() {
            if !r.demanded.same.carried.contains_key(&c) {
                stack.push((c, false));
            }
        }
    }
    Ok(r.demanded.same.carried.get(&x) == Some(&true))
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
    over_carries(r, cx, operand)?;
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
        if r.life.live.uses(x).unwrap_or(0) > inside.get(&x).copied().unwrap_or(0) {
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

/// Narrow constants in `{And, Or, Xor, Add, Sub, Mul}` across `root` where the union
/// `read[&u]` of demanded bits over ALL users of `u` reaching `root` clears high/unread bits.
#[cfg(feature = "prove")]
fn narrow_constants(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    order: &[u32],
    read: &IdMap<u32, BitVec>,
) -> Result<Option<Step>, Stop> {
    super::refresh_uses(r, cx)?;
    let const_op = |cx: &Context, u: u32| -> Option<(OpCode, u32, u32, BitVec, bool)> {
        let n = cx.node(u);
        if !matches!(
            n.op,
            OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Add | OpCode::Sub | OpCode::Mul
        ) {
            return None;
        }
        match (cx.const_val(n.a), cx.const_val(n.b)) {
            (None, Some(k)) => Some((n.op, n.a, n.b, k, false)),
            (Some(k), None) => Some((n.op, n.b, n.a, k, true)),
            _ => None,
        }
    };
    let allow_fold = |cx: &Context, r: &Runner<'_, '_>, u: u32| -> bool {
        r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(u)))
    };
    let arith_narrow =
        |cx: &Context, r: &Runner<'_, '_>, u: u32, m: &BitVec, k_id: u32, k: &BitVec| -> Option<BitVec> {
            let p = low_prefix(m);
            if p.is_ones() {
                return None;
            }
            if bv_and(&p, k).is_zero() && !k.is_zero() {
                return allow_fold(cx, r, u).then(|| BitVec::zero(m.width()));
            }
            let k2 = prefix_residue(k, &p)?;
            let k2_exists = k2
                .to_u64()
                .and_then(|v| cx.find_const_u64(m.width().bits(), v))
                .is_some();
            let k_single = !r.life.dead.contains(k_id) && r.life.live.uses(k_id) == Some(1);
            (k2_exists || k_single).then_some(k2)
        };
    let needs_narrow =
        |cx: &Context, r: &Runner<'_, '_>, u: u32, m: &BitVec, op: OpCode, k_id: u32, k: &BitVec| -> bool {
            if matches!(op, OpCode::Add | OpCode::Sub | OpCode::Mul) {
                return arith_narrow(cx, r, u, m, k_id, k).is_some();
            }
            let folds_to_const = (op == OpCode::And && bv_and(m, k).is_zero())
                || (op == OpCode::Or && subset(m, &bv_and(m, k)));
            if folds_to_const && !allow_fold(cx, r, u) {
                return false;
            }
            bv_and(m, k) != *k
                || (op == OpCode::And && (subset(m, k) || bv_and(m, k).is_zero()))
                || (op == OpCode::Or && (bv_and(m, k).is_zero() || subset(m, k)))
                || (op == OpCode::Xor && (bv_and(m, k).is_zero() || subset(m, k)))
        };
    let any_narrow = order.iter().any(|&u| {
        read.get(&u).is_some_and(|m| {
            !m.is_zero()
                && const_op(cx, u)
                    .is_some_and(|(op, _, k_id, k, _)| needs_narrow(cx, r, u, m, op, k_id, &k))
        })
    });
    if !any_narrow {
        return Ok(None);
    }
    let before = cx.len() as u32;
    let mut done: IdMap<u32, u32> = IdMap::default();
    let mut atoms: Vec<u32> = Vec::new();
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    for &u in order {
        if let Some(m) = read.get(&u)
            && !m.is_zero()
            && let Some((op, arg_orig, k_id, k, k_first)) = const_op(cx, u)
        {
            let arg = done.get(&arg_orig).copied().unwrap_or(arg_orig);
            if needs_narrow(cx, r, u, m, op, k_id, &k) {
                let mut reads_arg = true;
                let v = if matches!(op, OpCode::Add | OpCode::Sub | OpCode::Mul) {
                    let k2 = arith_narrow(cx, r, u, m, k_id, &k).unwrap_or(k);
                    if k2.is_zero() {
                        match op {
                            OpCode::Mul => {
                                reads_arg = false;
                                r.build(cx, |cx| cx.mk_const(&k2))?
                            }
                            OpCode::Sub if k_first => r.build(cx, |cx| cx.c_un(UnOp::Neg, arg))?,
                            _ => arg,
                        }
                    } else {
                        let kc = r.build(cx, |cx| cx.mk_const(&k2))?;
                        let bin_op = op.as_bin().unwrap_or(BinOp::Add);
                        let (lhs, rhs) = if k_first { (kc, arg) } else { (arg, kc) };
                        r.build(cx, |cx| cx.c_bin(bin_op, lhs, rhs))?
                    }
                } else {
                    let narrow = bv_and(m, &k);
                    match op {
                        OpCode::Xor => {
                            if narrow.is_zero() {
                                arg
                            } else if subset(m, &narrow) {
                                r.build(cx, |cx| cx.c_un(UnOp::Not, arg))?
                            } else {
                                let kc = r.build(cx, |cx| cx.mk_const(&narrow))?;
                                r.build(cx, |cx| cx.c_bin(BinOp::Xor, arg, kc))?
                            }
                        }
                        OpCode::Or => {
                            if narrow.is_zero() {
                                arg
                            } else if subset(m, &narrow) {
                                reads_arg = false;
                                r.build(cx, |cx| cx.mk_const(&narrow))?
                            } else {
                                let kc = r.build(cx, |cx| cx.mk_const(&narrow))?;
                                r.build(cx, |cx| cx.c_bin(BinOp::Or, arg, kc))?
                            }
                        }
                        _ => {
                            if subset(m, &narrow) {
                                arg
                            } else if narrow.is_zero() {
                                reads_arg = false;
                                let z = BitVec::zero(m.width());
                                r.build(cx, |cx| cx.mk_const(&z))?
                            } else {
                                let kc = r.build(cx, |cx| cx.mk_const(&narrow))?;
                                r.build(cx, |cx| cx.c_bin(BinOp::And, arg, kc))?
                            }
                        }
                    }
                };
                if reads_arg && arg == arg_orig && arg < before {
                    atoms.push(arg);
                }
                if v != u {
                    done.insert(u, v);
                }
                continue;
            }
        }
        let node = cx.node(u);
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
        if changed {
            for (k_new, c_orig) in kids.iter().zip(node.children()) {
                if *k_new == c_orig && c_orig < before {
                    atoms.push(c_orig);
                }
            }
            let v = r.build(cx, |cx| cx.rebuild(u, kids))?;
            if v != u {
                done.insert(u, v);
            }
        }
    }
    let Some(&e) = done.get(&root) else {
        super::discard(r, cx, before);
        return Ok(None);
    };
    if e == root {
        super::discard(r, cx, before);
        return Ok(None);
    }
    atoms.sort_unstable();
    atoms.dedup();
    super::discard_but(r, cx, before, e);
    r.explain_with(|| crate::engine::Explanation::Demanded {
        operand: cx.handle(root),
        mask: BitVec::ones(cx.width_of(root)),
    });
    let tree = |i: u32| cx.meta[i as usize].tree;
    let tie = tree(root) != u32::MAX && tree(e) < tree(root);
    Ok(
        match super::finish_with(
            r,
            cx,
            PassKind::Demanded,
            root,
            e,
            before,
            &atoms,
            Fin::FINAL,
            tie,
        )? {
            Step::To(e, f) => Some(Step::To(e, f)),
            Step::Normal(_) => None,
        },
    )
}

/// Fast structural gate for whether `root` is non-trivial enough to consider `dedup_root`.
#[cfg(feature = "prove")]
pub(crate) fn worth_dedup(cx: &Context, root: u32) -> bool {
    !cx.is_const(root) && cx.meta[root as usize].height >= 3 && cx.meta[root as usize].tree >= 6
}

/// Narrow constants in `And`/`Or`/`Xor` across `root` whose bits outside `read[&u]` never reach `root`.
#[cfg(feature = "prove")]
pub(crate) fn narrow_root(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
) -> Result<Option<(u32, Fin)>, Stop> {
    if r.assumptions.is_some_and(|a| !a.store.seeds.is_empty()) || r.life.live_roots.len() > 1 {
        return Ok(None);
    }
    let Some((order, read)) = demands(r, cx, root)? else {
        return Ok(None);
    };
    Ok(match narrow_constants(r, cx, root, &order, &read)? {
        Some(Step::To(e, f)) => Some((e, f)),
        _ => None,
    })
}

/// Deterministic 4-lane simulation signature + algebraic equivalence sweep over `root`:
/// merges interior nodes `(u, v)` (`u` earlier than `v` in topological `order`) that agree on
/// all demanded bits `read[&v]` (including across `32`-bit / `64`-bit prefix widths) whenever
/// proven equal by `demanded::simplify`, `poly::equal_mod`, `bitwise::equal`, `linear_mba::equal`,
/// or `mba::equal_sums`, strictly shrinking the whole DAG.
#[cfg(feature = "prove")]
pub(crate) fn dedup_root(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
) -> Result<Option<(u32, Fin)>, Stop> {
    if cx.is_const(root)
        || r.assumptions.is_some_and(|a| !a.store.seeds.is_empty())
        || r.life.live_roots.len() > 1
    {
        return Ok(None);
    }
    let Some((order, read)) = demands(r, cx, root)? else {
        return Ok(None);
    };
    if order.len() < 4 || order.len() > 2048 {
        return Ok(None);
    }
    r.meter
        .charge(Counter::PassWork, (order.len() as u64) * 2)?;

    const LANES: usize = 16;
    let splitmix = |mut z: u64| -> u64 {
        z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    let mut sigs: IdMap<u32, [u64; LANES]> = IdMap::default();
    for &u in &order {
        let nd = cx.node(u);
        let w = nd.width;
        if w == 0 || w > 64 {
            let base = (u64::from(u) << 8) ^ 0x517c_c1b7_2722_0a95;
            let mut arr = [0u64; LANES];
            for (k, slot) in arr.iter_mut().enumerate() {
                *slot = splitmix(base.wrapping_add(k as u64));
            }
            sigs.insert(u, arr);
            continue;
        }
        let mask = u64::MAX >> (64 - w);
        if let Some(cv) = cx.const_val(u).and_then(|v| v.to_u64()) {
            let c = cv & mask;
            sigs.insert(u, [c; LANES]);
            continue;
        }
        let get_s = |id: u32| sigs.get(&id).copied().unwrap_or([0; LANES]);
        let sa = get_s(nd.a);
        let sb = if nd.op.arity() >= 2 {
            get_s(nd.b)
        } else {
            [0; LANES]
        };
        let sc = if nd.op.arity() >= 3 {
            get_s(nd.c)
        } else {
            [0; LANES]
        };
        let mut out = [0u64; LANES];
        let wa = if nd.op.arity() >= 1 { cx.wid(nd.a) } else { w };
        let wb = if nd.op.arity() >= 2 { cx.wid(nd.b) } else { w };
        let mut opaque = false;
        for lane in 0..LANES {
            let (a, b, c) = (sa[lane], sb[lane], sc[lane]);
            out[lane] = match nd.op {
                OpCode::Add => a.wrapping_add(b) & mask,
                OpCode::Sub => a.wrapping_sub(b) & mask,
                OpCode::Mul => a.wrapping_mul(b) & mask,
                OpCode::Neg => a.wrapping_neg() & mask,
                OpCode::Not => (!a) & mask,
                OpCode::And => (a & b) & mask,
                OpCode::Or => (a | b) & mask,
                OpCode::Xor => (a ^ b) & mask,
                OpCode::Shl => {
                    if b >= u64::from(w) {
                        0
                    } else {
                        (a << b) & mask
                    }
                }
                OpCode::LShr => {
                    if b >= u64::from(w) {
                        0
                    } else {
                        (a >> b) & mask
                    }
                }
                OpCode::AShr => {
                    let sign_bit = 1u64 << (w - 1);
                    let sext_a = if (a & sign_bit) != 0 {
                        a | !mask
                    } else {
                        a
                    };
                    if b >= u64::from(w) {
                        if (a & sign_bit) != 0 { mask } else { 0 }
                    } else {
                        ((sext_a as i64 >> b) as u64) & mask
                    }
                }
                OpCode::RotL => {
                    let r_amt = (b % u64::from(w)) as u32;
                    if r_amt == 0 {
                        a & mask
                    } else {
                        ((a << r_amt) | (a >> (u32::from(w) - r_amt))) & mask
                    }
                }
                OpCode::RotR => {
                    let r_amt = (b % u64::from(w)) as u32;
                    if r_amt == 0 {
                        a & mask
                    } else {
                        ((a >> r_amt) | (a << (u32::from(w) - r_amt))) & mask
                    }
                }
                OpCode::Zext => a & mask,
                OpCode::Sext => {
                    if wa == 0 || wa > 64 {
                        opaque = true;
                        0
                    } else {
                        let sb_in = 1u64 << (wa - 1);
                        let low_in = u64::MAX >> (64 - wa);
                        if (a & sb_in) != 0 {
                            (a | !low_in) & mask
                        } else {
                            a & low_in & mask
                        }
                    }
                }
                OpCode::Extract => {
                    if wa > 64 {
                        opaque = true;
                        0
                    } else {
                        (a >> nd.b) & mask
                    }
                }
                OpCode::Concat => {
                    if wa > 64 || wb >= 64 {
                        opaque = true;
                        0
                    } else {
                        ((a << wb) | (b & (u64::MAX >> (64 - wb)))) & mask
                    }
                }
                OpCode::Select => {
                    if (a & 1) != 0 {
                        b & mask
                    } else {
                        c & mask
                    }
                }
                OpCode::Eq if wa <= 64 => u64::from(a == b),
                OpCode::Ne if wa <= 64 => u64::from(a != b),
                OpCode::Ult if wa <= 64 => u64::from(a < b),
                OpCode::Ule if wa <= 64 => u64::from(a <= b),
                OpCode::Slt | OpCode::Sle if wa > 0 && wa <= 64 => {
                    let sb_in = 1u64 << (wa - 1);
                    let sa_i = (a ^ sb_in) & (u64::MAX >> (64 - wa));
                    let sb_i = (b ^ sb_in) & (u64::MAX >> (64 - wa));
                    u64::from(if nd.op == OpCode::Slt {
                        sa_i < sb_i
                    } else {
                        sa_i <= sb_i
                    })
                }
                OpCode::Popcnt => u64::from((a & mask).count_ones()) & mask,
                _ => {
                    opaque = true;
                    0
                }
            };
        }
        // For rare point-equality guards (`Eq`/`Ne` at width >= 4) that never hit on random
        // samples, derive a deterministic mixed 0/1 truth vector from the commutative XOR
        // difference `sa ^ sb` so downstream `Select(guard, T, F)` exercises both `T` and `F`.
        if !opaque && matches!(nd.op, OpCode::Eq | OpCode::Ne) && wa >= 4 {
            let first = out[0];
            let all_same = out.iter().all(|&x| x == first);
            let diff_varies = (1..LANES).any(|k| (sa[k] ^ sb[k]) != (sa[0] ^ sb[0]));
            if all_same && diff_varies {
                let mut h = 0x243f_6a88_85a3_08d3u64;
                for k in 0..LANES {
                    h = splitmix(h ^ (sa[k] ^ sb[k]));
                }
                let mut bits = (h as u16 | 1) & !2u16;
                if nd.op == OpCode::Ne {
                    bits = !bits;
                }
                for (k, slot) in out.iter_mut().enumerate() {
                    *slot = u64::from((bits >> k) & 1);
                }
            }
        }
        if opaque {
            let base = (u64::from(u) << 8) ^ 0x9e37_79b9_7f4a_7c15;
            let (kz, ko) = if nd.op == OpCode::Sym {
                super::known_words(r, cx, u)?
                    .0
                    .map_or((0, 0), |[z, o]| (z & mask, o & mask))
            } else {
                (0, 0)
            };
            for (k, slot) in out.iter_mut().enumerate() {
                let raw = splitmix(base.wrapping_add(k as u64)) & mask;
                *slot = (raw & !kz) | ko;
            }
        }
        sigs.insert(u, out);
    }

    let before = cx.len() as u32;
    let mut buckets: std::collections::HashMap<(u16, u64, [u64; LANES]), Vec<u32>> =
        std::collections::HashMap::new();
    let mut done: IdMap<u32, u32> = IdMap::default();
    let mut fin = Fin::FINAL;
    let mut proofs_tried = 0u32;
    const MAX_DEDUP_PROOFS: u32 = 48;

    for &v in &order {
        let node = cx.node(v);
        let mut kids = [node.a, node.b, node.c];
        let mut kids_changed = false;
        for k in kids.iter_mut().take(node.op.arity()) {
            if let Some(&t) = done.get(k)
                && t != *k
            {
                *k = t;
                kids_changed = true;
            }
        }
        let v_cur = if kids_changed {
            r.build(cx, |cx| cx.rebuild(v, kids))?
        } else {
            v
        };
        if v_cur != v {
            done.insert(v, v_cur);
        }
        if v == root || cx.is_const(v_cur) {
            continue;
        }
        let w_v = cx.wid(v_cur);
        if w_v == 0 || w_v > 64 {
            continue;
        }
        let Some(m_v) = read.get(&v).copied().filter(|m| !m.is_zero()) else {
            continue;
        };
        let Some(mw) = m_v.to_u64() else {
            continue;
        };
        let Some(&sv) = sigs.get(&v) else {
            continue;
        };
        let mut masked_sig = [0u64; LANES];
        for (dst, &src) in masked_sig.iter_mut().zip(sv.iter()) {
            *dst = src & mw;
        }
        // Constant signature check: skip all-identical-lane constants (already handled by sweeps).
        if masked_sig.iter().all(|&x| x == masked_sig[0]) {
            continue;
        }
        let ones = mw.count_ones();
        let is_prefix = ones > 0 && ones == 64 - mw.leading_zeros();
        let key = if is_prefix {
            (ones as u16, 0u64, masked_sig)
        } else {
            (w_v, mw, masked_sig)
        };
        let mut matched: Option<(u32, Fin)> = None;
        if proofs_tried < MAX_DEDUP_PROOFS
            && let Some(cands) = buckets.get(&key)
        {
            for &u_orig in cands.iter().take(3) {
                let u_cur = done.get(&u_orig).copied().unwrap_or(u_orig);
                if u_cur == v_cur {
                    matched = Some((u_cur, Fin::FINAL));
                    break;
                }
                let w_u = cx.wid(u_cur);
                if w_u != w_v && !is_prefix {
                    continue;
                }
                proofs_tried += 1;
                let mark = cx.len() as u32;
                let u_at_v = match w_u.cmp(&w_v) {
                    core::cmp::Ordering::Equal => u_cur,
                    core::cmp::Ordering::Less => r.build(cx, |cx| cx.c_zext(u_cur, w_v))?,
                    core::cmp::Ordering::Greater => {
                        r.build(cx, |cx| cx.c_extract(u_cur, 0, w_v))?
                    }
                };
                if let Some(pf) = prove_masked_equal(r, cx, u_at_v, v_cur, &m_v, is_prefix, ones as u16)?
                {
                    super::discard_but(r, cx, mark, u_at_v);
                    matched = Some((u_at_v, pf));
                    break;
                }
                super::discard(r, cx, mark);
                if proofs_tried >= MAX_DEDUP_PROOFS {
                    break;
                }
            }
        }
        if let Some((rep, pf)) = matched {
            fin = fin.and(pf);
            done.insert(v, rep);
        } else {
            buckets.entry(key).or_default().push(v);
        }
    }

    let Some(&new_root) = done.get(&root) else {
        super::discard(r, cx, before);
        return Ok(None);
    };
    if new_root == root {
        super::discard(r, cx, before);
        return Ok(None);
    }
    super::discard_but(r, cx, before, new_root);
    let old_sz = match cx.dag_size(&[cx.handle(root)], 1 << 20).map_err(Stop::Error)? {
        crate::expr::Bounded::Exact(n) => n,
        _ => {
            super::discard(r, cx, before);
            return Ok(None);
        }
    };
    let shrunk = matches!(
        cx.dag_size(&[cx.handle(new_root)], old_sz - 1)
            .map_err(Stop::Error)?,
        crate::expr::Bounded::Exact(_)
    );
    if !shrunk {
        super::discard(r, cx, before);
        return Ok(None);
    }
    match r.accept(
        cx,
        crate::engine::By::Pass("demanded"),
        true,
        root,
        new_root,
        fin.rel,
    )? {
        crate::engine::Accept::Yes => {
            r.stats.passes.entry("demanded").or_default().changed += 1;
            Ok(Some((new_root, fin)))
        }
        _ => {
            super::discard(r, cx, before);
            Ok(None)
        }
    }
}

#[cfg(feature = "prove")]
fn prove_masked_equal(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
    m: &BitVec,
    is_prefix: bool,
    prefix_bits: u16,
) -> Result<Option<Fin>, Stop> {
    if a == b {
        return Ok(Some(Fin::FINAL));
    }
    if is_prefix && prefix_bits > 1 && super::poly::equal_mod(r, cx, a, b, prefix_bits)? {
        return Ok(Some(Fin::FINAL));
    }
    // Simplify both sides under `m` via `demanded::simplify` (exposes high-bit constant noise
    // differences like `0x63007002b3 - x` vs `0x7002b3 - x` inside `Select`/`And`/`Or`).
    let mk_demand = |root: u32, before: u32| Demand {
        memo: Memo::default(),
        base: Memo::default(),
        whole: None,
        whole_sums: false,
        cap: 64,
        track_stops: false,
        stops: Vec::new(),
        visits: 0,
        fin: Fin::FINAL,
        before,
        root,
        xors: Vec::new(),
        identities: Vec::new(),
        union: IdMap::default(),
        ties: false,
    };
    let mut fin = Fin::FINAL;
    let mut st_a = mk_demand(a, cx.len() as u32);
    let sa = simplify(r, cx, &mut st_a, a, m)?;
    let mut st_b = mk_demand(b, cx.len() as u32);
    let sb = simplify(r, cx, &mut st_b, b, m)?;
    fin = fin.and(st_a.fin).and(st_b.fin);
    if sa == sb {
        return Ok(Some(fin));
    }
    let (am, bm) = if m.is_ones() {
        (sa, sb)
    } else {
        let mc = r.build(cx, |cx| cx.mk_const(m))?;
        (
            r.build(cx, |cx| cx.c_bin(BinOp::And, sa, mc))?,
            r.build(cx, |cx| cx.c_bin(BinOp::And, sb, mc))?,
        )
    };
    if am == bm {
        return Ok(Some(fin));
    }
    if let (Some(true), bf) = super::bitwise::equal(r, cx, am, bm)? {
        return Ok(Some(fin.and(bf)));
    }
    if super::poly::equal(r, cx, am, bm)? || super::linear_mba::equal(r, cx, am, bm)? {
        return Ok(Some(fin));
    }
    Ok(None)
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
    if !dry && let Some(step) = narrow_constants(r, cx, root, &order, &read)? {
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

/// A node equal to `x` on the bits of `m`, as the pass simplifies an operand of which only
/// those bits are read: the pass's analysis on its own (see `Engine::under_mask`).
pub(in crate::engine) fn under_mask(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    m: &BitVec,
) -> Result<u32, Stop> {
    let mut st = Demand {
        memo: Memo::default(),
        base: Memo::default(),
        whole: None,
        whole_sums: false,
        cap: MAX_VISITS,
        track_stops: false,
        stops: Vec::new(),
        visits: 0,
        fin: Fin::FINAL,
        before: cx.len() as u32,
        root: x,
        xors: Vec::new(),
        identities: Vec::new(),
        union: IdMap::default(),
        ties: false,
    };
    simplify(r, cx, &mut st, x, m)
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry("demanded").or_default()
}

/// The demanded-bits pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    if let Some(x) = clears_known_zeros(r, cx, n)? {
        let before = cx.len() as u32;
        return finish(r, cx, PassKind::Demanded, n, x, before, &[x], Fin::FINAL);
    }
    // The operand observed through a mask, and the mask.
    let Some((operand, mask)) = observed(cx, n) else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    let before = cx.len() as u32;
    let mut st = Demand {
        base: Memo::default(),
        whole: None,
        whole_sums: false,
        memo: std::mem::take(&mut r.demanded.memo),
        cap: MAX_VISITS.min(super::region_cap(r)),
        track_stops: true,
        stops: Vec::new(),
        visits: 0,
        fin: Fin::FINAL,
        before,
        root: operand,
        xors: Vec::new(),
        identities: Vec::new(),
        union: IdMap::default(),
        ties: false,
    };
    // (Before anything is simplified: the identities remembered below depend on where the
    // sums with carries are, which this finds.)
    #[cfg(feature = "prove")]
    unions(r, cx, &mut st, operand, &mask)?;
    let union = std::mem::take(&mut st.union);
    let x2 = simplify(r, cx, &mut st, operand, &mask)?;
    if r.demanded.same.marking {
        for key in st.memo.keys() {
            r.demanded.same.first.insert(key.0, ());
        }
    }
    // The operands this step found nothing to simplify under their masks are remembered for
    // the phase run (every mask over one shared chain re-walked it, once per mask, and asked
    // the facts again at every node): their values are fixed, so the answer is too. Not when
    // the cap cut the walk short (an answer of more budget may differ), and not the
    // simplifications, whose nodes a rejection retires.
    if st.visits <= st.cap {
        for &(key, from, to) in &st.identities {
            if r.demanded.same.map.contains_key(&key) {
                continue;
            }
            // Each leaf once. A range holds what the hits below it copied, the leaves of each
            // operand; operands share leaves in a DAG, so a range kept with its repeats was
            // the sum of its operands' ranges, and on a ripple chain the ranges doubled at
            // every level (2^48 at 48 bits). The leaves are read as a set.
            let at = r.demanded.same.leaves.len();
            r.demanded
                .same
                .leaves
                .extend_from_slice(&st.stops[from as usize..to as usize]);
            let kept = sorted_distinct(&mut r.demanded.same.leaves[at..]);
            r.demanded.same.leaves.truncate(at + kept);
            r.demanded.same.map.insert(key, (at as u32, kept as u32));
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
    let mut tie = st.ties;
    // A node read under several masks was written once for each (a word each of its limbs
    // reads, its constants reduced to each reader's bits: one copy a reader). A second
    // simplification writes it once, on the bits any of its users reads, and stays where it
    // frees no fewer nodes: what it keeps of the word, every reader shares.
    if !union.is_empty() && !capped {
        let mut st2 = Demand {
            base: Memo::default(),
            whole: None,
            whole_sums: false,
            memo: std::mem::take(&mut st.memo),
            cap: st.cap,
            track_stops: true,
            stops: Vec::new(),
            visits: 0,
            fin: Fin::FINAL,
            before,
            root: operand,
            xors: Vec::new(),
            identities: Vec::new(),
            union,
            ties: false,
        };
        let x3 = simplify(r, cx, &mut st2, operand, &mask)?;
        st2.memo.clear();
        st.memo = std::mem::take(&mut st2.memo);
        if x3 != x2 && st2.visits <= st2.cap {
            let (e2, e3) = (rebuilt(r, cx, x2)?, rebuilt(r, cx, x3)?);
            let m2 = super::margin(r, cx, n, e2, &stops)?;
            let m3 = super::margin(r, cx, n, e3, &st2.stops)?;
            if m3.is_some_and(|b| m2.is_none_or(|a| b >= a)) {
                (x2, fin, stops, tie) = (x3, st2.fin, st2.stops, st2.ties);
            }
        }
        // (What the other simplification built is no use of the nodes below it.)
        let keep = rebuilt(r, cx, x2)?;
        super::discard_but(r, cx, before, keep);
    }
    r.demanded.memo = std::mem::take(&mut st.memo);
    if x2 == operand {
        count(r).noop += 1;
        return Ok(Step::Normal(fin));
    }
    let kept = sorted_distinct(&mut stops);
    stops.truncate(kept);
    let e = rebuilt(r, cx, x2)?;
    r.explain_with(|| crate::engine::Explanation::Demanded {
        operand: cx.handle(operand),
        mask,
    });
    super::finish_with(r, cx, PassKind::Demanded, n, e, before, &stops, fin, tie)
}

/// The pass's state for a call.
#[derive(Default)]
pub(crate) struct State {
    /// The demanded-bits pass's memo, empty between calls.
    pub(crate) memo: Memo,
    /// The operands the demanded-bits pass found nothing to simplify under a mask, for the
    /// phase run (a node's value is fixed, so neither is the answer; see `demanded::step`).
    pub(crate) same: Same,
    /// What the opaque-constant sweep's reductions of its candidates found, per node and
    /// demanded mask, for the call (see `pass::demanded::reduced`).
    #[cfg(feature = "mba")]
    pub(crate) reduced: [Memo; 2],
    /// The constants those reductions added to each operand (see `pass::demanded::same_on`).
    pub(crate) sum_constants: IdMap<(u32, u8), Vec<u32>>,
    /// Number of `dedup_root` sweeps attempted on the current call's root.
    pub(crate) dedup_runs: u8,
    /// Last root on which `dedup_root` found nothing to merge.
    pub(crate) dedup_tried: Option<u32>,
}
