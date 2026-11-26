//! Full-width relations between small mixed-width expressions in a settled DAG.

use super::{Fin, PassKind, Runner, Step, Stop, finish};
use crate::engine::budget::Counter;
use crate::engine::dispatch::bit;
use crate::engine::oracle::{EqualityCaps, EqualityVerdict};
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;

/// A full-width proof from this run can also answer a masked query on the same words.
pub(super) fn known(r: &Runner<'_, '_>, a: u32, b: u32) -> bool {
    r.demanded.view_equal.contains_key(&(a.min(b), a.max(b)))
}

const VIEWS: u128 =
    bit(OpCode::Extract) | bit(OpCode::Zext) | bit(OpCode::Sext) | bit(OpCode::Concat);
const MIN_CAP: u64 = 256;

/// Ask about words at the same width, including explicit masked projections.
/// Only positive answers enter the run's cache. All callers in one sweep share fuel.
fn prove(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    a: u32,
    b: u32,
    remaining: &mut u8,
) -> Result<bool, Stop> {
    if known(r, a, b) {
        return Ok(true);
    }
    let left = r.meter.left_in(|b| b.pass_work);
    // Reserve most of the call for the word procedures. Both circuit gates
    // and propagations count, including work on unsuccessful candidates.
    let allowance = (r.meter.limit.pass_work / 32).saturating_sub(r.demanded.view_work);
    let cap = (allowance / 2).min(left / 24).min(1 << 16);
    if *remaining == 0 || cap < MIN_CAP {
        return Ok(false);
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
    if proof.verdict == EqualityVerdict::Proved {
        r.demanded.view_equal.insert((a.min(b), a.max(b)), ());
        return Ok(true);
    }
    Ok(false)
}

/// The surrounding DAG can be large when a demanded-bits bucket has already
/// identified two small candidate subexpressions.
pub(super) fn prove_pair(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    a: u32,
    b: u32,
    remaining: &mut u8,
) -> Result<bool, Stop> {
    let (ma, mb) = (cx.meta[a as usize], cx.meta[b as usize]);
    let ops = ma.ops | mb.ops;
    if ops & VIEWS == 0
        || ops >= bit(OpCode::Ext1o0)
        || ma.tree.saturating_add(mb.tree) > 48.min(r.inner.strategy.max_region)
    {
        return Ok(false);
    }
    prove(r, cx, a, b, remaining)
}

/// At a settled mixed-width root, try full-word relations first. These also hold
/// when another output observes different bits. Real samples nominate pairs;
/// only a circuit proof can authorize substituting one for the other.
pub(super) fn merge(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    remaining: &mut u8,
) -> Result<Option<(u32, Fin)>, Stop> {
    let meta = cx.meta[root as usize];
    let limit = 48.min(r.inner.strategy.max_region);
    if meta.height > limit
        || meta.ops & VIEWS == 0
        || meta.ops >= bit(OpCode::Ext1o0)
        || r.meter.left_in(|b| b.pass_work) < 24 * MIN_CAP
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
    if order.iter().any(|&i| cx.wid(i) > 64) {
        return Ok(None);
    }
    r.sample(cx, root)?;
    // Compare full signatures before importing any circuit. Prefer small existing
    // representatives, including the output itself being equal to one of its leaves.
    let mut by_size = order.clone();
    by_size.sort_by_key(|&i| cx.meta[i as usize].tree);
    let mut pairs = Vec::new();
    let mut buckets: IdMap<(u16, u64, u64), Vec<u32>> = IdMap::default();
    for b in by_size {
        let values = &r.samples[&b];
        let key = (cx.wid(b), values[2].limbs()[0], values[3].limbs()[0]);
        let bucket = buckets.entry(key).or_default();
        r.meter.charge(Counter::PassWork, 1 + bucket.len() as u64)?;
        if cx.node(b).op.arity() != 0 {
            for &a in bucket.iter() {
                if r.samples[&a] == *values {
                    pairs.push((a, b));
                }
            }
        }
        if bucket.len() < 3 {
            bucket.push(b);
        }
    }
    let before = cx.len() as u32;
    if cx.wid(root) == 1 && r.samples[&root].iter().all(|v| *v == r.samples[&root][0]) {
        let v = r.samples[&root][0];
        let c = r.build(cx, |cx| cx.mk_const(&v))?;
        pairs.push((c, root));
    }
    let mut reps = IdMap::default();
    for (a, b) in pairs {
        if reps.contains_key(&b)
            || (cx.is_const(a) && r.hooks.is_some_and(|h| !h.fold_known(cx, cx.handle(b))))
        {
            continue;
        }
        if prove(r, cx, a, b, remaining)? {
            reps.insert(b, a);
            if b == root {
                break;
            }
        }
    }
    if reps.is_empty() {
        super::discard(r, cx, before);
        return Ok(None);
    }
    // Representatives can be from a sibling visited later. They are already
    // equal as originally built, so a single rebuild needs no substitution chase.
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
        if let Step::To(e, f) = finish(r, cx, PassKind::Demanded, root, e, before, &[], Fin::FINAL)?
        {
            return Ok(Some((e, f)));
        }
    } else {
        super::discard(r, cx, before);
    }
    Ok(None)
}
