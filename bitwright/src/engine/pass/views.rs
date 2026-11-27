//! Full-width and complement relations across widths `1..=512` in a settled DAG.
//!
//! Candidate pairs are nominated by deterministic sample buckets (favoring representatives already
//! kept alive by other roots in multi-root runs, then smaller trees in `Context::order`), and
//! discharged through a tiered proof ladder:
//! 1. Bit-provenance (`shuffle::decide_cmp_by_bits`),
//! 2. Ring polynomials with slice/mask refinement (`poly::equal`),
//! 3. Bitwise truth tables (`bitwise::equal`),
//! 4. Linear MBA corner signatures (`linear_mba::equal`),
//! 5. Non-destructive integer-floor forms (`words::prove_equal`),
//! 6. Bounded circuit equivalence (`circuit_equality`), caching refutations so refuted pairs are
//!    never re-queried across rounds.

use super::{Fin, PassKind, Runner, Step, Stop, finish};
use crate::BitVec;
use crate::engine::Sharing;
use crate::engine::budget::Counter;
use crate::engine::dispatch::bit;
use crate::engine::oracle::{EqualityCaps, EqualityVerdict};
use crate::expr::{Context, OpCode};
use crate::hash::{IdMap, combine};
use crate::ops::{CmpOp, UnOp};

/// A full-width proof from this run can also answer comparisons and masked queries on the same
/// words, preserving any assumption reliance `Fin`.
pub(super) fn known(r: &Runner<'_, '_>, a: u32, b: u32) -> Option<Fin> {
    if a == b {
        return Some(Fin::FINAL);
    }
    r.demanded.view_equal.get(&(a.min(b), a.max(b))).copied()
}

const VIEWS: u128 =
    bit(OpCode::Extract) | bit(OpCode::Zext) | bit(OpCode::Sext) | bit(OpCode::Concat);
const MIN_CAP: u64 = 256;
pub(super) const LANES: usize = 8;

fn hash_bv(v: &BitVec) -> u64 {
    v.limbs()
        .iter()
        .fold(u64::from(v.width().bits()), |h, &w| combine(h, w))
}

fn view_point(seed: u64, w: crate::Width, k: usize) -> BitVec {
    match k {
        0 => BitVec::zero(w),
        1 => BitVec::ones(w),
        _ => {
            let mut x = seed ^ (k as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let mut limbs = [0u64; 8];
            for slot in &mut limbs {
                x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = x;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                *slot = z ^ (z >> 31);
            }
            BitVec::wrapping_from_limbs(w, &limbs)
        }
    }
}

/// Evaluates deterministic `BitVec` signatures across `order` at widths `1..=512` into
/// `r.demanded.view_sigs`, charging only `Counter::PassWork` for newly evaluated nodes (never
/// `Counter::NodeVisits`, preserving phase-memoized visit counts).
pub(super) fn eval_sigs(r: &mut Runner<'_, '_>, cx: &Context, order: &[u32]) -> Result<(), Stop> {
    let mut fresh = 0u64;
    for &i in order {
        if !r.demanded.view_sigs.contains_key(&i) {
            fresh += 1;
        }
    }
    if fresh == 0 {
        return Ok(());
    }
    r.meter.charge(Counter::PassWork, fresh * LANES as u64)?;
    for &i in order {
        if r.demanded.view_sigs.contains_key(&i) {
            continue;
        }
        let seed = cx.meta[i as usize].shash;
        let declared = cx.declared_at(i);
        let w = cx.width_of(i);
        let mut kids: [(u32, Option<[BitVec; LANES]>); 3] = [(u32::MAX, None); 3];
        for (slot, c) in cx.node(i).children().enumerate() {
            kids[slot] = (c, r.demanded.view_sigs.get(&c).copied());
        }
        let mut vals = [BitVec::zero(w); LANES];
        for (k, out) in vals.iter_mut().enumerate() {
            let at = |j: u32| -> BitVec {
                for &(cid, ref opt) in &kids {
                    if cid == j
                        && let Some(arr) = opt
                    {
                        return arr[k];
                    }
                }
                r.demanded
                    .view_sigs
                    .get(&j)
                    .map_or_else(|| BitVec::zero(cx.width_of(j)), |arr| arr[k])
            };
            let sym = |_: &crate::SymbolKey, sw: crate::Width| {
                let v = view_point(seed, sw, k);
                Some(declared.map_or(v, |d| d.fit(&v)))
            };
            *out = cx.eval_node(i, at, sym).map_err(Stop::Error)?;
        }
        r.demanded.view_sigs.insert(i, vals);
    }
    Ok(())
}

/// Tiered full-width equality prover across widths `1..=512`.
/// Positive answers are cached with their `Fin` reliance; refuted pairs are cached in
/// `view_refuted` so later sweeps skip them immediately.
pub(super) fn prove_pair(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
    remaining: &mut u8,
) -> Result<Option<Fin>, Stop> {
    if a == b {
        return Ok(Some(Fin::FINAL));
    }
    if cx.wid(a) != cx.wid(b) {
        return Ok(None);
    }
    let key = (a.min(b), a.max(b));
    if let Some(&fin) = r.demanded.view_equal.get(&key) {
        return Ok(Some(fin));
    }
    if r.demanded.view_refuted.contains_key(&key) {
        return Ok(None);
    }
    let (ma, mb) = (cx.meta[a as usize], cx.meta[b as usize]);
    let ops = ma.ops | mb.ops;
    if ops >= bit(OpCode::Ext1o0) {
        return Ok(None);
    }

    // Tier 1: Bit-provenance (`1..=512`).
    match super::shuffle::decide_cmp_by_bits(r, cx, CmpOp::Eq, a, b)? {
        Some(true) => {
            r.demanded.view_equal.insert(key, Fin::FINAL);
            return Ok(Some(Fin::FINAL));
        }
        Some(false) => {
            r.demanded.view_refuted.insert(key, ());
            return Ok(None);
        }
        None => {}
    }

    // Tier 2: Ring polynomials + slice/mask basis refinement (`1..=512`).
    if super::poly::equal(r, cx, a, b)? {
        r.demanded.view_equal.insert(key, Fin::FINAL);
        return Ok(Some(Fin::FINAL));
    }

    // Tier 3: Bitwise truth tables (`1..=512`).
    match super::bitwise::equal(r, cx, a, b)? {
        (Some(true), fin) => {
            r.demanded.view_equal.insert(key, fin);
            return Ok(Some(fin));
        }
        (Some(false), fin) if fin.rel.is_none() => {
            r.demanded.view_refuted.insert(key, ());
            return Ok(None);
        }
        _ => {}
    }

    // Tier 4: Linear MBA corner signatures (`1..=512`).
    if super::linear_mba::equal(r, cx, a, b)? {
        r.demanded.view_equal.insert(key, Fin::FINAL);
        return Ok(Some(Fin::FINAL));
    }

    // Tier 5: Non-destructive Z-floor (`words`) lens (`1..=128`).
    if let Some(fin) = super::words::prove_equal(r, cx, a, b, cx.wid(a))? {
        r.demanded.view_equal.insert(key, fin);
        return Ok(Some(fin));
    }

    // Tier 6: Bounded circuit equality (`1..=512`), reserved for mixed-width view expressions
    // within the small-tree region cap so large multiplier/limb DAGs stay with `Phase::Words`.
    if ops & VIEWS == 0 || ma.tree.saturating_add(mb.tree) > 48.min(r.inner.strategy.max_region) {
        return Ok(None);
    }
    let left = r.meter.left_in(|b| b.pass_work);
    let allowance = (r.meter.limit.pass_work / 32).saturating_sub(r.demanded.view_work);
    let cap = (allowance / 2).min(left / 24).min(1 << 16);
    if *remaining == 0 || cap < MIN_CAP {
        return Ok(None);
    }
    *remaining -= 1;
    r.meter.deadline_now()?;
    let mut scratch = Context::new();
    let terms = scratch
        .import(cx, &[cx.handle(a), cx.handle(b)])
        .map_err(Stop::Error)?;
    let caps = EqualityCaps {
        samples: 0,
        max_nodes: cap as usize,
        max_propagations: cap,
    };
    let proof =
        crate::circuit_equality()(&mut scratch, terms[0], terms[1], &caps).map_err(Stop::Error)?;
    let cost = (proof.nodes as u64).saturating_add(proof.propagations);
    r.demanded.view_work = r.demanded.view_work.saturating_add(cost);
    r.meter.charge(Counter::PassWork, cost.min(left))?;
    match proof.verdict {
        EqualityVerdict::Proved => {
            r.demanded.view_equal.insert(key, Fin::FINAL);
            Ok(Some(Fin::FINAL))
        }
        EqualityVerdict::Refuted | EqualityVerdict::Budget => {
            r.demanded.view_refuted.insert(key, ());
            Ok(None)
        }
        EqualityVerdict::Unknown => Ok(None),
    }
}

/// Nodes reachable from live roots other than `r.active`, so multi-root runs prefer merging onto
/// subterms already pinned by sibling roots.
pub(super) fn other_roots_reach(r: &Runner<'_, '_>, cx: &Context) -> IdMap<u32, ()> {
    let mut reach = IdMap::default();
    if r.inner.strategy.sharing != Sharing::Roots || r.life.live_roots.len() <= 1 {
        return reach;
    }
    let mut stack: Vec<u32> = r
        .life
        .live_roots
        .iter()
        .enumerate()
        .filter_map(|(idx, &rt)| (idx != r.active).then_some(rt))
        .collect();
    while let Some(i) = stack.pop() {
        if reach.len() >= 4096 || reach.insert(i, ()).is_some() {
            continue;
        }
        stack.extend(cx.node(i).children());
    }
    reach
}

/// At a settled root (`1..=512` bits), discover and merge full-word and bitwise-complement
/// equivalences across the DAG.
pub(super) fn merge(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    remaining: &mut u8,
) -> Result<Option<(u32, Fin)>, Stop> {
    let meta = cx.meta[root as usize];
    let limit = 64.min(r.inner.strategy.max_region);
    if meta.height > limit
        || meta.ops >= bit(OpCode::Ext1o0)
        || r.meter.left_in(|b| b.pass_work) < 16 * MIN_CAP
    {
        return Ok(None);
    }
    let size = cx
        .dag_size(&[cx.handle(root)], limit)
        .map_err(Stop::Error)?;
    let crate::expr::Bounded::Exact(size) = size else {
        r.meter.charge(Counter::PassWork, u64::from(limit) + 1)?;
        return Ok(None);
    };
    r.meter.charge(Counter::PassWork, u64::from(size) * 2)?;
    let order = cx.post_order_ids(&[root]);
    eval_sigs(r, cx, &order)?;
    let pinned = other_roots_reach(r, cx);
    let mut by_size = order.clone();
    by_size.sort_by(|&a, &b| {
        let pa = !pinned.contains_key(&a);
        let pb = !pinned.contains_key(&b);
        pa.cmp(&pb)
            .then_with(|| cx.meta[a as usize].tree.cmp(&cx.meta[b as usize].tree))
            .then_with(|| cx.order(a, b))
    });
    let mut pairs: Vec<(u32, u32, bool)> = Vec::new();
    let mut buckets: IdMap<(u16, u64, u64), Vec<u32>> = IdMap::default();
    for b in by_size {
        let values = r.demanded.view_sigs[&b];
        // Skip nodes that appear constant across all lanes (handled by constant sweeps, and
        // point-equalities `x == c` at wide widths evaluate to `0` at every random point).
        if values.iter().all(|v| *v == values[0]) {
            continue;
        }
        let w = cx.wid(b);
        let key = (w, hash_bv(&values[2]), hash_bv(&values[3]));
        if cx.node(b).op.arity() != 0 {
            if let Some(bucket) = buckets.get(&key) {
                r.meter.charge(Counter::PassWork, 1 + bucket.len() as u64)?;
                for &a in bucket {
                    if r.demanded.view_sigs[&a] == values {
                        pairs.push((a, b, false));
                    }
                }
            }
            if w > 1 && cx.node(b).op != OpCode::Not {
                let comp2 = BitVec::un_unchecked(UnOp::Not, &values[2]);
                let comp3 = BitVec::un_unchecked(UnOp::Not, &values[3]);
                let comp_key = (w, hash_bv(&comp2), hash_bv(&comp3));
                if let Some(bucket) = buckets.get(&comp_key) {
                    for &a in bucket {
                        if cx.meta[a as usize].tree.saturating_add(1) <= cx.meta[b as usize].tree
                            && r.demanded.view_sigs[&a]
                                .iter()
                                .zip(values.iter())
                                .all(|(va, vb)| BitVec::un_unchecked(UnOp::Not, va) == *vb)
                        {
                            pairs.push((a, b, true));
                        }
                    }
                }
            }
        }
        let bucket = buckets.entry(key).or_default();
        if bucket.len() < 4 {
            bucket.push(b);
        }
    }
    let before = cx.len() as u32;
    let root_vals = r.demanded.view_sigs[&root];
    if meta.ops & VIEWS != 0 && cx.wid(root) == 1 && root_vals.iter().all(|v| *v == root_vals[0]) {
        let v = root_vals[0];
        let c = r.build(cx, |cx| cx.mk_const(&v))?;
        pairs.push((c, root, false));
    }
    let mut reps: IdMap<u32, u32> = IdMap::default();
    let mut merge_fin = Fin::FINAL;
    for (a, b, is_comp) in pairs {
        if reps.contains_key(&b)
            || (!is_comp
                && cx.is_const(a)
                && r.hooks.is_some_and(|h| !h.fold_known(cx, cx.handle(b))))
        {
            continue;
        }
        let mark = cx.len() as u32;
        let cand_a = if is_comp {
            r.build(cx, |cx| cx.c_un(UnOp::Not, a))?
        } else {
            a
        };
        if let Some(pf) = prove_pair(r, cx, cand_a, b, remaining)? {
            merge_fin = merge_fin.and(pf);
            reps.insert(b, cand_a);
            if b == root {
                break;
            }
        } else if is_comp {
            super::discard(r, cx, mark);
        }
    }
    if reps.is_empty() {
        super::discard(r, cx, before);
        return Ok(None);
    }
    for i in order {
        if reps.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        let mut kids = [node.a, node.b, node.c];
        let mut changed = false;
        for child in kids.iter_mut().take(node.op.arity()) {
            if let Some(&e) = reps.get(child) {
                changed |= e != *child;
                *child = e;
            }
        }
        if changed {
            let e = r.build(cx, |cx| cx.rebuild(i, kids))?;
            reps.insert(i, e);
        }
    }
    if let Some(&e) = reps.get(&root)
        && !(cx.is_const(e) && r.hooks.is_some_and(|h| !h.fold_known(cx, cx.handle(root))))
    {
        super::discard_but(r, cx, before, e);
        if let Step::To(e, f) = finish(r, cx, PassKind::Demanded, root, e, before, &[], merge_fin)?
        {
            return Ok(Some((e, f)));
        }
    } else {
        super::discard(r, cx, before);
    }
    Ok(None)
}
