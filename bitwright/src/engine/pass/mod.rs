//! Normal-form passes (design §8): each is a deterministic function from a node (whose operands
//! are already normal) to a candidate replacement, committed only when it is strictly smaller.

pub(crate) mod bitwise;
pub(super) mod casts;
pub(super) mod compares;
pub(super) mod demanded;
pub(super) mod forms;
pub(super) mod invert;
pub(super) mod linear;
pub(super) mod linear_mba;
#[cfg(feature = "mba")]
pub(super) mod mba;
pub(super) mod shuffle;
#[cfg(test)]
mod tests;
pub(super) mod xor;

use super::{Accept, By, Fin, Reject, Runner, Step, Stop};
use crate::engine::Exhausted;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::facts::{Facts, Reliance};
use crate::hash::IdMap;

/// A normal-form pass.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum PassKind {
    FactFold,
    Linear,
    Bitwise,
    Xor,
    Compares,
    Casts,
    Demanded,
    LinearMba,
    Shuffle,
    Invert,
    /// The MBA service (the configuration lives in the phase).
    #[cfg_attr(not(feature = "mba"), allow(dead_code))]
    Mba,
}

impl PassKind {
    pub(crate) fn name(self) -> &'static str {
        match self {
            PassKind::FactFold => "fact_fold",
            PassKind::Linear => "linear",
            PassKind::Bitwise => "bitwise",
            PassKind::Xor => "xor",
            PassKind::Compares => "compares",
            PassKind::Casts => "casts",
            PassKind::Demanded => "demanded",
            PassKind::LinearMba => "linear_mba",
            PassKind::Shuffle => "shuffle",
            PassKind::Invert => "invert",
            PassKind::Mba => "mba",
        }
    }
}

/// Runs `kind` at `n`.
pub(super) fn step(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    kind: PassKind,
    n: u32,
) -> Result<Step, Stop> {
    r.stats.passes.entry(kind.name()).or_default().calls += 1;
    r.meter.charge(Counter::PassWork, 1)?;
    match kind {
        PassKind::FactFold => fold(r, cx, n),
        PassKind::Linear => linear::step(r, cx, n),
        PassKind::Bitwise => bitwise::step(r, cx, n),
        PassKind::Xor => xor::step(r, cx, n),
        PassKind::Compares => compares::step(r, cx, n),
        PassKind::Casts => casts::step(r, cx, n),
        PassKind::Demanded => demanded::step(r, cx, n),
        PassKind::LinearMba => linear_mba::step(r, cx, n),
        PassKind::Shuffle => shuffle::step(r, cx, n),
        PassKind::Invert => invert::step(r, cx, n),
        // Dispatched with its configuration by the engine.
        PassKind::Mba => Ok(Step::Normal(Fin::FINAL)),
    }
}

/// The MBA phase at `n` (its configuration comes from the phase).
#[cfg(feature = "mba")]
pub(super) fn mba_step(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &crate::mba::MbaConfig,
    n: u32,
) -> Result<Step, Stop> {
    if r.quarantined_passes.contains(&PassKind::Mba) {
        return Ok(Step::Normal(Fin::PROVISIONAL));
    }
    // Asked before the operands were walked, which left them as they are: the same question.
    if let Some(Some(fin)) = r.first.get(&n) {
        return Ok(Step::Normal(*fin));
    }
    // Inside a chain of sums (or of products) the question at the chain's top covers the node:
    // asking at every link would ask the same fragment again and again, each time a little
    // larger (a sum of n terms is n questions). So a link is not asked when the question at its
    // user in the chain is (and that one's fragment, which contains the link's, is within the
    // limits). Not final: a later call may ask it.
    let additive = |op: OpCode| matches!(op, OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Shl);
    if let Some(&p) = r.chain_parent.get(&n) {
        let (op, up) = (cx.node(n).op, cx.node(p).op);
        if ((matches!(op, OpCode::Add | OpCode::Sub) && additive(up))
            || (op == OpCode::Mul && up == OpCode::Mul))
            && mba::asks(r, cx, cfg, p)?
        {
            return Ok(Step::Normal(Fin::PROVISIONAL));
        }
    }
    r.stats.passes.entry("mba").or_default().calls += 1;
    r.meter.charge(Counter::PassWork, 1)?;
    mba::step(r, cx, cfg, n)
}

/// The question at the top of a fragment (a node whose user in the walk is not asked, or a
/// root), asked before the MBA phase walks its operands: an answer to a part can hide what only
/// the whole shows (a relation between atoms that rewrites one factor of a product identity).
/// `Some` rewrite when it is taken; otherwise the operands are walked as usual, and the question
/// is asked again only if one of them changed.
#[cfg(feature = "mba")]
pub(super) fn mba_first(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &crate::mba::MbaConfig,
    n: u32,
) -> Result<Option<(u32, Fin)>, Stop> {
    let top = match r.chain_parent.get(&n) {
        None => true,
        Some(&p) => !mba::asks(r, cx, cfg, p)?,
    };
    if !top || !mba::asks(r, cx, cfg, n)? {
        r.first.insert(n, None);
        return Ok(None);
    }
    match mba_step(r, cx, cfg, n)? {
        Step::To(x, fin) => {
            r.first.insert(n, None);
            Ok(Some((x, fin)))
        }
        Step::Normal(fin) => {
            r.first.insert(n, Some(fin));
            Ok(None)
        }
    }
}

/// Facts about `n` for a pass, under the call's fact budget and the run's assumptions.
/// `Ok((None, fin))` when a cap declined the query; `Err` when the call's own budget ran out.
pub(super) fn facts(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<(Option<Facts>, Fin), Stop> {
    if let Some(v) = cx.const_val(n) {
        return Ok((Some(Facts::constant(&v)), Fin::FINAL));
    }
    let left = r.meter.left().fact_work;
    let cap = u32::try_from(left).unwrap_or(u32::MAX);
    if cap == 0 {
        return Err(Stop::Exhausted(Exhausted::FactWork));
    }
    let (work0, capped0) = (cx.facts.work, cx.facts.capped);
    let e = cx.handle(n);
    // Infeasible assumptions prove anything; the engine proves nothing from them.
    let (f, rel) = match r.assumptions {
        Some(a) => match cx.facts_under_cap(e, a, cap).map_err(Stop::Error)? {
            Ok((f, rel)) => (Some(f), rel),
            Err(_) => (None, Reliance::NONE),
        },
        None => (
            cx.try_facts_cap(e, cap).map_err(Stop::Error)?,
            Reliance::NONE,
        ),
    };
    r.meter.spent.fact_work += cx.facts.work - work0;
    if cx.facts.capped != capped0 {
        if cap < cx.config().fact_work {
            return Err(Stop::Exhausted(Exhausted::FactWork));
        }
        r.stats.degraded += 1;
        return Ok((None, Fin::capped(Exhausted::FactWork)));
    }
    r.meter.check()?;
    Ok((f, Fin::relying(rel)))
}

/// Fact folding: a node whose facts pin one value becomes that constant.
fn fold(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    if cx.const_val(n).is_some() {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let (f, fin) = facts(r, cx, n)?;
    let Some(v) = f.and_then(|f| f.as_constant()) else {
        r.stats.passes.entry("fact_fold").or_default().noop += 1;
        return Ok(Step::Normal(fin));
    };
    if let Some(h) = r.hooks
        && !h.fold_known(cx, cx.handle(n))
    {
        r.stats.hook_vetoes += 1;
        return Ok(Step::Normal(fin));
    }
    let before = cx.len() as u32;
    let c = r.build(cx, |cx| cx.mk_const(&v))?;
    finish(r, cx, PassKind::FactFold, n, c, before, &[], fin)
}

/// Use counts (parent edges) of the live DAG: counted once per phase run over the current
/// version of every root of the call (nodes only replaced ones reach are not live), then kept
/// up to date as nodes are created (counted) and replaced (uncounted, see `Runner::retire`). A
/// node a counted node uses is counted too, so one replaced and then used again is live again.
fn refresh_uses(r: &mut Runner<'_, '_>, cx: &Context) -> Result<(), Stop> {
    if r.uses.is_none() {
        let mut uses: IdMap<u32, u32> = IdMap::default();
        let mut seen: IdMap<u32, ()> = IdMap::default();
        let mut stack: Vec<u32> = r.live_roots.clone();
        while let Some(i) = stack.pop() {
            if seen.insert(i, ()).is_some() || r.dead.contains_key(&i) {
                continue;
            }
            if let Err(e) = r.meter.charge(Counter::PassWork, 1) {
                // Nothing counted yet (`uses` is still unset): keep `counted` consistent.
                r.counted.clear();
                return Err(e.into());
            }
            for c in cx.node(i).children() {
                *uses.entry(c).or_default() += 1;
                stack.push(c);
            }
            r.counted.insert(i, ());
        }
        r.uses = Some(uses);
        r.uses_upto = r.phase_start;
    }
    let len = cx.len() as u32;
    let from = r.uses_upto.min(len);
    r.meter.charge(Counter::PassWork, u64::from(len - from))?;
    let mut stack: Vec<u32> = (from..len)
        .rev()
        .filter(|i| !r.dead.contains_key(i) && !r.counted.contains_key(i))
        .collect();
    while let Some(i) = stack.pop() {
        if r.counted.insert(i, ()).is_some() {
            continue;
        }
        r.dead.remove(&i);
        r.meter.charge(Counter::PassWork, 1)?;
        if let Some(uses) = r.uses.as_mut() {
            for c in cx.node(i).children() {
                *uses.entry(c).or_default() += 1;
                if !r.counted.contains_key(&c) {
                    stack.push(c);
                }
            }
        }
    }
    r.uses_upto = len;
    Ok(())
}

/// The region of `n`: the nodes reachable from it without entering `atoms` (sorted), at most
/// [`REGION_CAP`] of them (the ones nearest `n`), in descending index order. Operands always
/// have lower indices than their users, so this order lists every user before its operands.
fn region(r: &mut Runner<'_, '_>, cx: &Context, n: u32, atoms: &[u32]) -> Result<Vec<u32>, Stop> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut queue = std::collections::VecDeque::from([n]);
    let mut out: Vec<u32> = Vec::new();
    while let Some(i) = queue.pop_front() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        out.push(i);
        if out.len() >= REGION_CAP as usize {
            break;
        }
        for c in cx.node(i).children() {
            if atoms.binary_search(&c).is_err() {
                queue.push_back(c);
            }
        }
    }
    out.sort_unstable_by(|a, b| b.cmp(a));
    Ok(out)
}

/// How many nodes of `order` (the region of `n`, users first) stop being used when `n` is
/// replaced, counting at most `limit`: `n`, and every node all of whose uses come from nodes
/// that stop being used; nodes in `kept` (reused by the replacement) stay. A truncated region
/// gives a lower bound.
///
/// With `shared = false`, uses from outside the region are ignored: the count a context-free
/// decision would make, used to tell whether a rejection depended on sharing.
fn dying_in(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    order: &[u32],
    kept: &IdMap<u32, ()>,
    limit: u32,
    shared: bool,
) -> Result<u32, Stop> {
    let in_region: IdMap<u32, ()> = order.iter().map(|&i| (i, ())).collect();
    let local_uses: IdMap<u32, u32>;
    let uses = if shared {
        refresh_uses(r, cx)?;
        r.uses.as_ref()
    } else {
        let mut u: IdMap<u32, u32> = IdMap::default();
        for &i in order {
            for c in cx.node(i).children() {
                if in_region.contains_key(&c) {
                    *u.entry(c).or_default() += 1;
                }
            }
        }
        local_uses = u;
        Some(&local_uses)
    };
    let mut from_dying: IdMap<u32, u32> = IdMap::default();
    let mut count = 0u32;
    for &i in order {
        if kept.contains_key(&i) {
            continue;
        }
        let dies = i == n
            || from_dying.get(&i).copied().unwrap_or(0)
                >= uses.and_then(|u| u.get(&i).copied()).unwrap_or(u32::MAX);
        if !dies {
            continue;
        }
        count += 1;
        if count >= limit {
            return Ok(count);
        }
        for c in cx.node(i).children() {
            if in_region.contains_key(&c) {
                *from_dying.entry(c).or_default() += 1;
            }
        }
    }
    Ok(count)
}

/// A candidate's cost: the nodes it needs, and the region nodes it reuses.
type Needed = (u32, IdMap<u32, ()>);

/// The nodes candidate `e` needs that are neither atoms nor in `region` (the region of the
/// node it replaces), and the region nodes it reuses; `None` if more than [`REGION_CAP`].
/// Counted against the structure, not the arena, so the decision never depends on which nodes
/// happen to exist already.
fn needed(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    e: u32,
    atoms: &[u32],
    region: &IdMap<u32, ()>,
) -> Result<Option<Needed>, Stop> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut kept: IdMap<u32, ()> = IdMap::default();
    let mut new = 0u32;
    let mut stack = vec![e];
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() || atoms.binary_search(&i).is_ok() {
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        if region.contains_key(&i) {
            kept.insert(i, ());
            continue;
        }
        new += 1;
        if new > REGION_CAP {
            r.meter.check()?;
            return Ok(None);
        }
        stack.extend(cx.node(i).children());
    }
    r.meter.check()?;
    Ok(Some((new, kept)))
}

/// The most nodes the commit rule examines on either side.
pub(super) const REGION_CAP: u32 = 1024;

/// Whether building a candidate of at most `estimate` nodes can pay: fewer than the nodes
/// replacing `n` would free. Checked before building, so rejected candidates cost no nodes.
/// `Ok(None)` to build; `Ok(Some(fin))` not to, with what that decision contributes to the
/// node's finality (not final when only sharing made it).
pub(super) fn worth_building(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    atoms: &[u32],
    estimate: u32,
) -> Result<Option<Fin>, Stop> {
    let mut sorted = atoms.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    let order = region(r, cx, n, &sorted)?;
    r.meter.check()?;
    let none = IdMap::default();
    if dying_in(r, cx, n, &order, &none, estimate.saturating_add(1), true)? > estimate {
        return Ok(None);
    }
    let alone = dying_in(r, cx, n, &order, &none, estimate.saturating_add(1), false)?;
    Ok(Some(if alone > estimate {
        Fin::PROVISIONAL
    } else {
        Fin::FINAL
    }))
}

/// Whether replacing `n` by `e` (already built) makes the DAG strictly smaller: `e` needs fewer
/// nodes than replacing `n` frees. `Err(fin)` when it does not, with what that contributes to
/// the node's finality: a rejection that only sharing caused may flip once other users of the
/// region are simplified away later in the walk, so it is not final and a later round decides
/// again. A constant always replaces a node that is not one: it frees the node's operator for a
/// constant, which rewrites nothing further (so the non-constant nodes strictly decrease), and
/// it lets the users fold (`~x + x` is -1 even beside `~x ^ …`, which then is `x`).
pub(super) fn shrinks(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    e: u32,
    atoms: &[u32],
) -> Result<Result<(), Fin>, Stop> {
    if cx.node(e).op == OpCode::Const && cx.node(n).op != OpCode::Const {
        return Ok(Ok(()));
    }
    let mut sorted = atoms.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    let order = region(r, cx, n, &sorted)?;
    r.meter.check()?;
    let set: IdMap<u32, ()> = order.iter().map(|&i| (i, ())).collect();
    let Some((new, kept)) = needed(r, cx, e, &sorted, &set)? else {
        return Ok(Err(Fin::FINAL));
    };
    let freed = dying_in(r, cx, n, &order, &kept, new.saturating_add(1), true)?;
    if new >= freed {
        let alone = dying_in(r, cx, n, &order, &kept, new.saturating_add(1), false)?;
        return Ok(Err(if new < alone {
            Fin::PROVISIONAL
        } else {
            Fin::FINAL
        }));
    }
    Ok(Ok(()))
}

/// Commits `e` (built from arena index `before` on) for `n` when it makes the DAG strictly
/// smaller (it needs fewer nodes than replacing `n` frees) and passes the postconditions and
/// the host veto.
#[allow(clippy::too_many_arguments)]
pub(super) fn finish(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    kind: PassKind,
    n: u32,
    e: u32,
    before: u32,
    atoms: &[u32],
    fin: Fin,
) -> Result<Step, Stop> {
    let name = kind.name();
    if e == n {
        r.stats.passes.entry(name).or_default().noop += 1;
        return Ok(Step::Normal(fin));
    }
    if let Err(more) = shrinks(r, cx, n, e, atoms)? {
        // A rejection that only sharing caused is not final (see `shrinks`).
        r.stats.passes.entry(name).or_default().rejected_cost += 1;
        discard(r, cx, before);
        return Ok(Step::Normal(fin.and(more)));
    }
    match r.accept(cx, By::Pass(name), true, n, e, fin.rel)? {
        Accept::Yes => {
            r.stats.passes.entry(name).or_default().changed += 1;
            Ok(Step::To(e, fin))
        }
        Accept::Vetoed => {
            r.stats.passes.entry(name).or_default().rejected += 1;
            discard(r, cx, before);
            Ok(Step::Normal(fin))
        }
        Accept::Rejected(reason) => {
            r.stats.passes.entry(name).or_default().rejected += 1;
            discard(r, cx, before);
            if matches!(reason, Reject::Width | Reject::Verify | Reject::Tripwire) {
                r.quarantined_passes.push(kind);
                r.stats.quarantined += 1;
            }
            Ok(Step::Normal(fin))
        }
    }
}

/// Marks the nodes a rejected candidate built (arena index at least `before`) as unused, so
/// they do not count as uses of their operands.
pub(super) fn discard(r: &mut Runner<'_, '_>, cx: &Context, before: u32) {
    for i in before..cx.len() as u32 {
        r.retire(cx, i);
    }
}
