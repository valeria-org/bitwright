//! Normal-form passes (design §8): each is a deterministic function from a node (whose operands
//! are already normal) to a candidate replacement, committed only when it is strictly smaller.

pub(crate) mod bitwise;
mod cases;
pub(super) mod casts;
pub(super) mod compares;
pub(super) mod demanded;
pub(super) mod forms;
mod gf2;
pub(super) mod invert;
pub(super) mod linear;
pub(super) mod linear_mba;
#[cfg(feature = "mba")]
pub(super) mod mba;
mod order;
mod poly;
pub(super) mod residue;
pub(super) mod shuffle;
#[cfg(test)]
mod tests;
pub(super) mod xor;

use super::{Accept, By, Fin, Reject, Runner, Step, Stop};
use crate::engine::Exhausted;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::facts::{Facts, KnownBits, Reliance};

/// A set of node indices emptied in constant time (by a new epoch; a stamp of 0 is never
/// current): the engine's per-node scratch, kept by the runner and reused instead of hash sets.
/// It grows to any index it is given.
pub(crate) struct Marks {
    stamp: Vec<u32>,
    epoch: u32,
}

impl Default for Marks {
    fn default() -> Self {
        Marks {
            stamp: Vec::new(),
            epoch: 1,
        }
    }
}

impl Marks {
    /// Empties the set, sized for indices below `len`.
    pub(crate) fn begin(&mut self, len: usize) {
        if self.stamp.len() < len {
            self.stamp.resize(len, 0);
        }
        self.clear();
    }

    /// Empties the set.
    pub(crate) fn clear(&mut self) {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.stamp.fill(0);
            self.epoch = 1;
        }
    }

    /// Adds `i`: whether it was not in the set.
    #[inline]
    pub(crate) fn insert(&mut self, i: u32) -> bool {
        let i = i as usize;
        if i >= self.stamp.len() {
            self.stamp.resize(i + 1, 0);
        }
        let fresh = self.stamp[i] != self.epoch;
        self.stamp[i] = self.epoch;
        fresh
    }

    /// Removes `i`: whether it was in the set.
    #[inline]
    pub(crate) fn remove(&mut self, i: u32) -> bool {
        match self.stamp.get_mut(i as usize) {
            Some(s) if *s == self.epoch => {
                *s = 0;
                true
            }
            _ => false,
        }
    }

    #[inline]
    pub(crate) fn contains(&self, i: u32) -> bool {
        self.stamp.get(i as usize) == Some(&self.epoch)
    }
}

/// Counts per node index, emptied in constant time like [`Marks`]; an index not counted since
/// then has none (which is not a count of 0).
pub(crate) struct Counts {
    stamp: Vec<u32>,
    val: Vec<u32>,
    epoch: u32,
}

impl Default for Counts {
    fn default() -> Self {
        Counts {
            stamp: Vec::new(),
            val: Vec::new(),
            epoch: 1,
        }
    }
}

impl Counts {
    /// Empties the counts, sized for indices below `len`.
    pub(crate) fn begin(&mut self, len: usize) {
        if self.stamp.len() < len {
            self.stamp.resize(len, 0);
            self.val.resize(len, 0);
        }
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.stamp.fill(0);
            self.epoch = 1;
        }
    }

    #[inline]
    pub(crate) fn get(&self, i: u32) -> Option<u32> {
        let i = i as usize;
        (self.stamp.get(i) == Some(&self.epoch)).then(|| self.val[i])
    }

    /// Counts one more for `i`.
    #[inline]
    pub(crate) fn add(&mut self, i: u32) {
        let i = i as usize;
        if i >= self.stamp.len() {
            self.stamp.resize(i + 1, 0);
            self.val.resize(i + 1, 0);
        }
        if self.stamp[i] != self.epoch {
            self.stamp[i] = self.epoch;
            self.val[i] = 0;
        }
        self.val[i] += 1;
    }

    /// Sets `i`'s count to `v`.
    #[inline]
    pub(crate) fn set(&mut self, i: u32, v: u32) {
        let i = i as usize;
        if i >= self.stamp.len() {
            self.stamp.resize(i + 1, 0);
            self.val.resize(i + 1, 0);
        }
        self.stamp[i] = self.epoch;
        self.val[i] = v;
    }
}

/// The commit rule's scratch (see [`shrinks`]).
#[derive(Default)]
pub(crate) struct Scratch {
    /// The region of the node being replaced.
    region: Marks,
    /// Nodes a candidate needs, visited.
    seen: Marks,
    /// Region nodes the candidate reuses.
    kept: Marks,
    /// Uses from nodes that stop being used.
    dying: Counts,
    /// Uses from inside the region.
    local: Counts,
    /// The atoms of the region.
    atoms: Marks,
    /// Region nodes nothing live uses.
    zeros: Vec<u32>,
    queue: std::collections::VecDeque<u32>,
    stack: Vec<u32>,
    heap: std::collections::BinaryHeap<u32>,
}

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
    query(r, cx, n, |f| f, Context::try_facts_cap)
}

/// The known bits of [`facts`], without building the other facts where no assumptions apply.
pub(super) fn known(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<(Option<KnownBits>, Fin), Stop> {
    if let Some(v) = cx.const_val(n) {
        return Ok((Some(KnownBits::constant(&v)), Fin::FINAL));
    }
    query(r, cx, n, |f| f.known(), Context::try_known_cap)
}

/// [`known`] of a node of at most 64 bits, as its known-zero and known-one words.
pub(super) fn known_words(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<(Option<[u64; 2]>, Fin), Stop> {
    let words = |k: &KnownBits| [k.known_zero().limbs()[0], k.known_one().limbs()[0]];
    if let Some(v) = cx.const_val(n) {
        return Ok((Some(words(&KnownBits::constant(&v))), Fin::FINAL));
    }
    query(
        r,
        cx,
        n,
        |f| words(&f.known()),
        Context::try_known_words_cap,
    )
}

/// Whether the facts prove that `a` and `b` (of one width) never have a bit set in both, with
/// what the facts of each relied on.
pub(super) fn disjoint(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
) -> Result<(bool, Fin, Fin), Stop> {
    let bits = cx.width_of(a).bits();
    if bits <= 64 {
        let (ka, fa) = known_words(r, cx, a)?;
        let (kb, fb) = known_words(r, cx, b)?;
        let mask = u64::MAX >> (64 - bits);
        let d = matches!((ka, kb), (Some([za, _]), Some([zb, _])) if !za & !zb & mask == 0);
        return Ok((d, fa, fb));
    }
    let (ka, fa) = known(r, cx, a)?;
    let (kb, fb) = known(r, cx, b)?;
    let d = match (ka, kb) {
        (Some(x), Some(y)) => crate::facts::known::bv_and(&x.maybe_one(), &y.maybe_one()).is_zero(),
        _ => false,
    };
    Ok((d, fa, fb))
}

/// [`facts`] of a node that is not a constant, read by `of` under assumptions and by `base`
/// from the base facts otherwise.
fn query<T>(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    of: impl FnOnce(Facts) -> T,
    base: impl FnOnce(&mut Context, crate::Expr, u32) -> Result<Option<T>, crate::Error>,
) -> Result<(Option<T>, Fin), Stop> {
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
            Ok((f, rel)) => (Some(of(f)), rel),
            Err(_) => (None, Reliance::NONE),
        },
        None => (base(cx, e, cap).map_err(Stop::Error)?, Reliance::NONE),
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
///
/// The roots other than the active one do not change while it is processed: their part is
/// counted once per root ([`Live`]) and stands in every phase run in which none of the nodes
/// they reach was retired (a count from scratch skips retired nodes, and what only they reach).
fn refresh_uses(r: &mut Runner<'_, '_>, cx: &Context) -> Result<(), Stop> {
    if !r.uses_on {
        r.live.clear();
        r.scratch.seen.begin(cx.len());
        let others = others_hold(r, cx);
        let mut stack: Vec<u32> = if others {
            if let Err(e) = charge_each(&mut r.meter, r.live.others.nodes as u64) {
                r.live.clear();
                return Err(e.into());
            }
            // (Off when the other roots reach nothing: then it adds nothing.)
            r.live.base = r.live.others.nodes > 0;
            r.live_roots.get(r.active).copied().into_iter().collect()
        } else {
            r.live_roots.clone()
        };
        while let Some(i) = stack.pop() {
            if (others && r.live.others.reach.contains(i))
                || !r.scratch.seen.insert(i)
                || r.dead.contains(i)
            {
                continue;
            }
            if let Err(e) = r.meter.charge(Counter::PassWork, 1) {
                // Nothing counted yet (`uses` is still off): keep the counted set consistent.
                r.live.clear();
                return Err(e.into());
            }
            for c in cx.node(i).children() {
                r.live.add(c);
                stack.push(c);
            }
            r.live.count(i);
        }
        r.uses_on = true;
        r.uses_upto = r.phase_start;
    }
    let len = cx.len() as u32;
    let from = r.uses_upto.min(len);
    r.meter.charge(Counter::PassWork, u64::from(len - from))?;
    let mut stack: Vec<u32> = (from..len)
        .rev()
        .filter(|&i| !r.dead.contains(i) && !r.live.counted(i))
        .collect();
    while let Some(i) = stack.pop() {
        if !r.live.count(i) {
            continue;
        }
        r.dead.remove(i);
        r.meter.charge(Counter::PassWork, 1)?;
        for c in cx.node(i).children() {
            r.live.add(c);
            if !r.live.counted(c) {
                stack.push(c);
            }
        }
    }
    r.uses_upto = len;
    Ok(())
}

/// Charges `n` units of pass work as `n` charges of one would: on failure, what was left is
/// spent.
fn charge_each(meter: &mut crate::engine::budget::Meter, n: u64) -> Result<(), Exhausted> {
    if meter.charge(Counter::PassWork, n).is_err() {
        for _ in 0..n {
            meter.charge(Counter::PassWork, 1)?;
        }
    }
    Ok(())
}

/// The uses the live roots other than the active one contribute, counted once per root.
#[derive(Default)]
pub(crate) struct Others {
    /// The entry of `live_roots` they were counted for.
    active: Option<usize>,
    /// The nodes the other roots reach, and how many.
    reach: Marks,
    nodes: u32,
    /// The uses from those nodes.
    uses: Counts,
}

/// The use counts and the set of nodes whose edges they count ("counted"), for the commit
/// rule: when `base` is on, the other roots' part ([`Others`]) with this phase run's changes on
/// top, else the changes alone. Answers as one [`Counts`] and one [`Marks`] would.
#[derive(Default)]
pub(crate) struct Live {
    others: Others,
    base: bool,
    /// Counted nodes outside the base, and base nodes no longer counted.
    counted: Marks,
    uncounted: Marks,
    /// Changes of the use counts (signed), stamped as in [`Counts`].
    stamp: Vec<u32>,
    delta: Vec<i32>,
    epoch: u32,
}

impl Live {
    /// Empties it: nothing counted, no uses, the base off.
    pub(crate) fn clear(&mut self) {
        self.base = false;
        self.counted.clear();
        self.uncounted.clear();
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.stamp.fill(0);
            self.epoch = 1;
        }
    }

    #[inline]
    fn in_base(&self, i: u32) -> bool {
        self.base && self.others.reach.contains(i)
    }

    #[inline]
    fn delta(&self, i: u32) -> Option<i32> {
        let i = i as usize;
        (self.stamp.get(i) == Some(&self.epoch)).then(|| self.delta[i])
    }

    #[inline]
    fn change(&mut self, i: u32, by: i32) {
        let i = i as usize;
        if i >= self.stamp.len() {
            self.stamp.resize(i + 1, 0);
            self.delta.resize(i + 1, 0);
        }
        if self.stamp[i] != self.epoch {
            self.stamp[i] = self.epoch;
            self.delta[i] = 0;
        }
        self.delta[i] += by;
    }

    /// The uses of `i`, if it has a count.
    #[inline]
    pub(crate) fn uses(&self, i: u32) -> Option<u32> {
        let d = self.delta(i);
        if !self.base {
            return d.map(|d| d.max(0) as u32);
        }
        match (self.others.uses.get(i), d) {
            (None, None) => None,
            (b, d) => Some((i64::from(b.unwrap_or(0)) + i64::from(d.unwrap_or(0))).max(0) as u32),
        }
    }

    /// Counts one more use of `i`.
    #[inline]
    pub(crate) fn add(&mut self, i: u32) {
        self.change(i, 1);
    }

    /// Counts one use less of `i` (not below 0), if it has a count: the count left.
    #[inline]
    pub(crate) fn dec(&mut self, i: u32) -> Option<u32> {
        let n = self.uses(i)?;
        if n > 0 {
            self.change(i, -1);
        }
        Some(n.saturating_sub(1))
    }

    /// Whether `i`'s edges are counted.
    #[inline]
    pub(crate) fn counted(&self, i: u32) -> bool {
        (self.in_base(i) && !self.uncounted.contains(i)) || self.counted.contains(i)
    }

    /// Counts `i`'s edges from now on: whether they were not.
    #[inline]
    pub(crate) fn count(&mut self, i: u32) -> bool {
        if self.counted(i) {
            return false;
        }
        if self.in_base(i) {
            self.uncounted.remove(i);
        } else {
            self.counted.insert(i);
        }
        true
    }

    /// Stops counting `i`'s edges: whether they were.
    #[inline]
    pub(crate) fn uncount(&mut self, i: u32) -> bool {
        if self.counted.remove(i) {
            return true;
        }
        self.in_base(i) && self.uncounted.insert(i)
    }
}

/// Whether the other roots' part holds in this phase run, counting it first if it is for
/// another root: no node the other roots reach was retired in the run.
fn others_hold(r: &mut Runner<'_, '_>, cx: &Context) -> bool {
    let o = &mut r.live.others;
    if o.active != Some(r.active) {
        o.active = Some(r.active);
        // (Sized as they grow: often the other roots reach nothing.)
        o.reach.clear();
        o.uses.begin(0);
        o.nodes = 0;
        let mut stack: Vec<u32> = r
            .live_roots
            .iter()
            .enumerate()
            .filter(|&(k, _)| k != r.active)
            .map(|(_, &i)| i)
            .collect();
        while let Some(i) = stack.pop() {
            if !o.reach.insert(i) {
                continue;
            }
            o.nodes += 1;
            for c in cx.node(i).children() {
                o.uses.add(c);
                stack.push(c);
            }
        }
    }
    !r.dead_log.iter().any(|&d| o.reach.contains(d))
}

/// The region of `n`: the nodes reachable from it without entering `atoms`, at most
/// [`REGION_CAP`] of them (the ones nearest `n`), left as `r.scratch.region` (and the atoms as
/// `r.scratch.atoms`). Also counts in `r.scratch.local` each region node's uses from region
/// nodes, and lists in `r.scratch.zeros` the region nodes no live node uses (see [`dying_in`]).
fn region(r: &mut Runner<'_, '_>, cx: &Context, n: u32, atoms: &[u32]) -> Result<(), Stop> {
    let sc = &mut r.scratch;
    sc.atoms.begin(cx.len());
    for &a in atoms {
        sc.atoms.insert(a);
    }
    sc.region.begin(cx.len());
    sc.local.begin(cx.len());
    sc.zeros.clear();
    sc.queue.clear();
    sc.queue.push_back(n);
    let mut size = 0u32;
    let mut last = None;
    while let Some(i) = sc.queue.pop_front() {
        if !sc.region.insert(i) {
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        if r.uses_on && r.live.uses(i) == Some(0) {
            sc.zeros.push(i);
        }
        size += 1;
        if size >= REGION_CAP {
            last = Some(i);
            break;
        }
        // Every operand's use is counted, whether or not the operand joins the region: only
        // region nodes' counts are read.
        for c in cx.node(i).children() {
            if !sc.atoms.contains(c) {
                sc.local.add(c);
                sc.queue.push_back(c);
            }
        }
    }
    // The node the cap stopped at uses region nodes too.
    if let Some(i) = last {
        for c in cx.node(i).children() {
            if sc.region.contains(c) {
                sc.local.add(c);
            }
        }
    }
    Ok(())
}

/// How many nodes of the region of `n` (left by [`region`]) stop being used when `n` is
/// replaced, counting at most `limit`: `n`, and every node all of whose uses come from nodes
/// that stop being used; with `kept`, nodes in `r.scratch.kept` (reused by the replacement)
/// stay. A truncated region gives a lower bound.
///
/// With `shared = false`, uses from outside the region are ignored: the count a context-free
/// decision would make, used to tell whether a rejection depended on sharing.
///
/// Operands have lower indices than their users, so taking the nodes that may stop being used
/// highest index first decides each after all its users. A node may stop being used only if
/// one of its users does, or if nothing uses it (only nodes `region` listed in `zeros`: counting
/// the uses since only adds; a region node's uses from the region are never none).
fn dying_in(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    kept: bool,
    limit: u32,
    shared: bool,
) -> Result<u32, Stop> {
    if shared {
        refresh_uses(r, cx)?;
    }
    let sc = &mut r.scratch;
    sc.dying.begin(cx.len());
    sc.heap.clear();
    sc.heap.push(n);
    if shared {
        sc.heap.extend(sc.zeros.iter().copied());
    }
    let mut count = 0u32;
    let mut last = None;
    while let Some(i) = sc.heap.pop() {
        // Copies of a node come out together (nothing larger is added after it).
        if last == Some(i) {
            continue;
        }
        last = Some(i);
        if kept && sc.kept.contains(i) {
            continue;
        }
        let uses = if shared {
            r.live.uses(i)
        } else {
            sc.local.get(i)
        };
        let dies = i == n || sc.dying.get(i).unwrap_or(0) >= uses.unwrap_or(u32::MAX);
        if !dies {
            continue;
        }
        count += 1;
        if count >= limit {
            return Ok(count);
        }
        for c in cx.node(i).children() {
            if sc.region.contains(c) {
                sc.dying.add(c);
                sc.heap.push(c);
            }
        }
    }
    Ok(count)
}

/// The nodes candidate `e` needs that are neither atoms nor in the region (`r.scratch.atoms`
/// and `r.scratch.region`, of the node it replaces), leaving the region nodes it reuses in
/// `r.scratch.kept`; `None` if more than [`REGION_CAP`]. Counted against the structure, not the
/// arena, so the decision never depends on which nodes happen to exist already.
fn needed(r: &mut Runner<'_, '_>, cx: &Context, e: u32) -> Result<Option<u32>, Stop> {
    let sc = &mut r.scratch;
    sc.seen.begin(cx.len());
    sc.kept.begin(cx.len());
    sc.stack.clear();
    sc.stack.push(e);
    let mut new = 0u32;
    while let Some(i) = sc.stack.pop() {
        if !sc.seen.insert(i) || sc.atoms.contains(i) {
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        if sc.region.contains(i) {
            sc.kept.insert(i);
            continue;
        }
        new += 1;
        if new > REGION_CAP {
            r.meter.check()?;
            return Ok(None);
        }
        sc.stack.extend(cx.node(i).children());
    }
    r.meter.check()?;
    Ok(Some(new))
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
    region(r, cx, n, atoms)?;
    r.meter.check()?;
    if dying_in(r, cx, n, false, estimate.saturating_add(1), true)? > estimate {
        return Ok(None);
    }
    let alone = dying_in(r, cx, n, false, estimate.saturating_add(1), false)?;
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
    region(r, cx, n, atoms)?;
    r.meter.check()?;
    let Some(new) = needed(r, cx, e)? else {
        return Ok(Err(Fin::FINAL));
    };
    let freed = dying_in(r, cx, n, true, new.saturating_add(1), true)?;
    if new >= freed {
        let alone = dying_in(r, cx, n, true, new.saturating_add(1), false)?;
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
