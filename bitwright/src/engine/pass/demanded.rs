//! The demanded-bits pass: a node that observes only some bits of an operand (`x & c`, `x | c`,
//! an extract, a shift by a constant) simplifies that operand under the *demanded mask* `m`: it
//! is replaced by any `x'` with `x' & m = x & m`.
//!
//! Under a mask, `a & k` with `k ⊇ m` is `a`; `a | k` with `k ∩ m = ∅` is `a`, and with `k ⊇ m`
//! is `k`; an operand whose demanded bits the facts know is that constant; arithmetic demands
//! only the low prefix of its operands; shifts, extensions and `concat` re-index the mask. A sum whose terms read one condition several ways is read with them merged,
//! modulo the low prefix (see `conditions`). The simplified region replaces the node only when
//! it is strictly smaller.

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
}

impl Same {
    pub(crate) fn clear(&mut self) {
        self.map.clear();
        self.leaves.clear();
    }
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
            match dropped_constant(cx, node.op, a, b, &p) {
                Some(t) => t,
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
    if v == x && x < st.before {
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
    };
    simplify(r, cx, &mut st, x, &BitVec::ones(w))
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
    };
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
            let at = r.demanded_same.leaves.len() as u32;
            r.demanded_same
                .leaves
                .extend_from_slice(&st.stops[from as usize..to as usize]);
            r.demanded_same.map.insert(key, (at, to - from));
        }
    }
    st.memo.clear();
    r.demanded = std::mem::take(&mut st.memo);
    if st.visits > st.cap {
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
