//! Normal-form passes (design §8): each is a deterministic function from a node (whose operands
//! are already normal) to a candidate replacement, committed only when it is strictly smaller.

pub(crate) mod bitwise;
#[cfg(feature = "prove")]
mod borrows;
#[cfg(feature = "prove")]
pub(super) mod carries;
mod cases;
pub(super) mod casts;
pub(super) mod compares;
mod conditions;
#[cfg(feature = "mba")]
mod context;
pub(super) mod demanded;
mod division;
pub(super) mod forms;
mod gf2;
pub(super) mod invert;
mod limbs;
pub(super) mod linear;
pub(super) mod linear_mba;
#[cfg(feature = "mba")]
pub(super) mod mba;
mod order;
mod poly;
pub(crate) mod predicate;
pub(super) mod residue;
pub(super) mod shuffle;
#[cfg(feature = "prove")]
mod slices;
#[cfg(test)]
mod tests;
pub(super) mod xor;

use super::{Accept, By, Fin, Reject, Runner, Sharing, Step, Stop};
use crate::engine::budget::Counter;
use crate::engine::{Exhausted, Explanation};
use crate::expr::{Context, OpCode};
use crate::facts::{Facts, KnownBits, Reliance};
#[cfg(feature = "mba")]
use crate::{BitVec, Width};

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
    /// Region nodes found to stop being used, not yet propagated.
    dead: Vec<u32>,
    /// Region nodes decided to stop being used.
    decided: Marks,
    /// What the region left in `region`, `local`, `zeros` and `atoms` is of: the node, a hash
    /// of its atoms, and the state the counts depend on (see [`region`]).
    region_for: Option<(u32, u64, bool, usize, u32)>,
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
    Division,
    /// The MBA service (the configuration lives in the phase).
    #[cfg_attr(not(feature = "mba"), allow(dead_code))]
    Mba,
    /// Carry and borrow networks, proved by the native prover.
    #[cfg(feature = "prove")]
    Carries,
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
            PassKind::Division => "division",
            PassKind::Mba => "mba",
            #[cfg(feature = "prove")]
            PassKind::Carries => "carries",
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
        PassKind::Division => division::step(r, cx, n),
        #[cfg(feature = "prove")]
        PassKind::Carries => carries::step(r, cx, n),
        // Dispatched with its configuration by the engine.
        PassKind::Mba => Ok(Step::Normal(Fin::FINAL)),
    }
}

/// `root` with what its conditions fix put into the operands they guard (see
/// `context::push`), within `max_new` new nodes.
#[cfg(feature = "mba")]
pub(super) fn push_context(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    max_new: u32,
) -> Result<Option<u32>, Stop> {
    r.build(cx, |cx| context::push(cx, root, max_new))
}

/// `root` with its pieces that depend only on a few conditions written as tables
/// of their values (see `context::cut`), evaluating at most `fuel` nodes.
#[cfg(feature = "mba")]
pub(super) fn cut_cases(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    fuel: u64,
) -> Result<Option<u32>, Stop> {
    r.build(cx, |cx| context::cut(cx, root, fuel))
}

/// the opaque-constant sweep before the first phase (see `mba::sweep`).
#[cfg(feature = "mba")]
pub(super) fn mba_sweep(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &crate::mba::MbaConfig,
    root: u32,
) -> Result<u32, Stop> {
    mba::sweep(r, cx, cfg, root)
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
        // A cast between a link and its user is part of the user's fragment (`zext(t ^ k)`
        // beside other terms): the link is covered by the question above the cast.
        let (p, up) = match up {
            OpCode::Zext | OpCode::Sext | OpCode::Extract => match r.chain_parent.get(&p) {
                Some(&q) => (q, cx.node(q).op),
                None => (p, up),
            },
            _ => (p, up),
        };
        if ((matches!(op, OpCode::Add | OpCode::Sub) && additive(up))
            || (op == OpCode::Mul && up == OpCode::Mul)
            || (matches!(op, OpCode::Xor | OpCode::And | OpCode::Or) && up == op))
            && mba::asks(r, cx, cfg, p)?
        {
            return Ok(Step::Normal(Fin::PROVISIONAL));
        }
    }
    r.stats.passes.entry("mba").or_default().calls += 1;
    r.meter.charge(Counter::PassWork, 1)?;
    let whole = mba::step(r, cx, cfg, n, false)?;
    if matches!(whole, Step::To(..)) {
        return Ok(whole);
    }
    // a sum whose groups of terms share no leaf, each asked alone.
    let mut part =
        |r: &mut Runner<'_, '_>, cx: &mut Context, s: u32| -> Result<Option<u32>, Stop> {
            Ok(match mba::step(r, cx, cfg, s, true)? {
                Step::To(e, _) => Some(e),
                Step::Normal(_) => None,
            })
        };
    if let Some(step @ Step::To(..)) = linear::by_sums(r, cx, n, &mut part)? {
        return Ok(step);
    }
    Ok(match linear::by_groups(r, cx, n, &mut part)? {
        Some(step @ Step::To(..)) => step,
        _ => whole,
    })
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
        if !d && let Some(by) = disjoint_by_residues(r, cx, a, b)? {
            return Ok((by, fa, fb));
        }
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

/// a constant whose bits are all among the lowest four, and a product or sum whose
/// residues show those bits zero for every input (`(z·z + z) | 1`, the left operand even), are
/// disjoint; `None` when the operands are not of that shape.
fn disjoint_by_residues(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    a: u32,
    b: u32,
) -> Result<Option<bool>, Stop> {
    const LOW_BITS: u32 = 4;
    let (x, k) = match (cx.const_val(a), cx.const_val(b)) {
        (None, Some(k)) => (a, k),
        (Some(k), None) => (b, k),
        _ => return Ok(None),
    };
    let Some(kv) = k.to_u64() else {
        return Ok(None);
    };
    let bits = 64 - kv.leading_zeros();
    if kv == 0
        || bits > LOW_BITS
        || !matches!(cx.node(x).op, OpCode::Mul | OpCode::Add | OpCode::Sub)
    {
        return Ok(None);
    }
    let Some(t) = residue::residues(r, cx, x, bits)? else {
        return Ok(None);
    };
    Ok(Some(t.values.iter().all(|&v| v & kv == 0)))
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
    let left = r.meter.left_in(|b| b.fact_work);
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
    if let Some(f) = f {
        r.explain_with(|| Explanation::Fold {
            known_zero: f.known().known_zero(),
            known_one: f.known().known_one(),
            value: v,
        });
    }
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
pub(super) fn refresh_uses(r: &mut Runner<'_, '_>, cx: &Context) -> Result<(), Stop> {
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

    /// Drops the other roots' part (they changed: it is counted again when next needed).
    pub(crate) fn forget_others(&mut self) {
        self.others.active = None;
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
    // The same region as last time (a pass asks whether building pays, builds, then asks
    // whether the result pays: twice per candidate): still there, while no node was retired
    // and the use counts are as they were (new nodes only add uses, which `dying_in` reads
    // afresh). A phase run starts over.
    let key = (
        n,
        atoms.iter().fold(0x7265_6769_6f6e_u64, |h, &a| {
            crate::hash::combine(h, u64::from(a))
        }),
        r.uses_on,
        r.dead_log.len(),
        r.phase_start,
    );
    if r.scratch.region_for == Some(key) {
        return Ok(());
    }
    r.scratch.region_for = None;
    let cap = region_cap(r);
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
        if size >= cap {
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
    sc.region_for = Some(key);
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
/// A node stops being used once as many of its uses come from nodes that stop being used as it
/// has, so it is decided when the last of those is (in any order); or at once if nothing uses
/// it (only nodes `region` listed in `zeros` can be: counting the uses since only adds, and a
/// region node's uses from the region are never none).
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
    sc.decided.begin(cx.len());
    sc.dead.clear();
    let uses = |sc: &Scratch, live: &Live, i: u32| {
        if shared {
            live.uses(i)
        } else {
            sc.local.get(i)
        }
    };
    // `n`, and the region nodes nothing uses (only those `region` listed can be).
    if !(kept && sc.kept.contains(n)) {
        sc.decided.insert(n);
        sc.dead.push(n);
    }
    if shared {
        for k in 0..sc.zeros.len() {
            let z = sc.zeros[k];
            if !(kept && sc.kept.contains(z))
                && uses(sc, &r.live, z) == Some(0)
                && sc.decided.insert(z)
            {
                sc.dead.push(z);
            }
        }
    }
    let mut count = 0u32;
    while let Some(i) = sc.dead.pop() {
        count += 1;
        if count >= limit {
            return Ok(count);
        }
        for c in cx.node(i).children() {
            if !sc.region.contains(c) {
                continue;
            }
            sc.dying.add(c);
            if sc.decided.contains(c) || (kept && sc.kept.contains(c)) {
                continue;
            }
            if sc.dying.get(c).unwrap_or(0) >= uses(sc, &r.live, c).unwrap_or(u32::MAX) {
                sc.decided.insert(c);
                sc.dead.push(c);
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
    let cap = region_cap(r);
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
        if new > cap {
            r.meter.check()?;
            return Ok(None);
        }
        sc.stack.extend(cx.node(i).children());
    }
    r.meter.check()?;
    Ok(Some(new))
}

/// The most nodes the commit rule examines on either side, by default
/// ([`Strategy::max_region`](crate::engine::Strategy::max_region)).
pub(crate) const REGION_CAP: u32 = 1024;

/// The strategy's cap on the nodes the commit rule examines on either side.
pub(super) fn region_cap(r: &Runner<'_, '_>) -> u32 {
    r.inner.strategy.max_region.max(1)
}

/// Whether the commit rule ignores sharing ([`Sharing::Ignored`]).
pub(super) fn alone(r: &Runner<'_, '_>) -> bool {
    r.inner.strategy.sharing == Sharing::Ignored
}

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
    if alone(r) {
        // Decided on the region alone: final either way.
        let freed = dying_in(r, cx, n, false, estimate.saturating_add(1), false)?;
        if freed > estimate {
            return Ok(None);
        }
        r.not_smaller(cx, n, None, estimate, freed, false);
        return Ok(Some(Fin::FINAL));
    }
    let freed = dying_in(r, cx, n, false, estimate.saturating_add(1), true)?;
    if freed > estimate {
        return Ok(None);
    }
    let alone = dying_in(r, cx, n, false, estimate.saturating_add(1), false)?;
    r.not_smaller(cx, n, None, estimate, freed, alone > estimate);
    Ok(Some(if alone > estimate {
        Fin::PROVISIONAL
    } else {
        Fin::FINAL
    }))
}

/// The most nodes replacing `n` may free for [`cannot_pay`] to decide.
#[cfg(feature = "mba")]
const PAY_FREED: u32 = 3;

/// The most operands [`two_operators`] pairs (a question with more is asked).
#[cfg(feature = "mba")]
const PAY_LEAVES: usize = 64;

/// Whether no form over `atoms` can replace `n` under [`shrinks`], whatever the form is: so a
/// question about `n` (the fragment between it and `atoms`) need not be put to a solver.
/// Replacing `n` frees the nodes only `n` holds alive, `f` of them, and a form that is committed
/// needs fewer nodes than that besides `atoms` and the nodes below `n` (or is a constant), a
/// node below `n` that it keeps being one freed less. So with `f = 1` it is an atom or a node
/// below `n`; with `f = 2` it may also be one operator over those that stay (every node the
/// constructors `lift_id` calls can make: `~ − + · & | ^ << >>u`, an extension, a slice); with
/// `f = 3` one operator may also read one of the two nodes that go with `n` (where the other
/// still goes), and the form may have two nodes of its own over those that stay: two
/// operators, or one and a constant ([`two_operators`]). Equal forms agree at the
/// verification points, so when `n` is not a constant there and none of these forms agrees
/// with it, no answer can be committed: `Some`, with what the decision contributes to the
/// node's finality (sharing made it unless the nodes below `n` alone give the same count).
/// `None` when more than `most` nodes (at most [`PAY_FREED`]) are freed, the region is not
/// whole, or a form agrees: the question is asked.
///
/// With `free` (the question is of `n`'s own fragment, and only a proved answer is committed),
/// a form that agrees at the verification points is compared again where the atoms take
/// independent values ([`free_values`]): an answer is an identity over the atoms, so a form
/// that agrees with `n` only because of how its atoms are related is none (a limb that is a
/// slice of a word below it agrees with that slice at every point, and no solver's answer
/// says so).
///
/// The count is of the expression as it is: for a node that is no part of it (a sum written
/// again to be asked part by part) the callers keep `most` at 2 and `free` off, as the rule
/// was when those parts' commits were measured.
#[cfg(feature = "mba")]
pub(super) fn cannot_pay(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    atoms: &[u32],
    most: u32,
    free: bool,
) -> Result<Option<Fin>, Stop> {
    region(r, cx, n, atoms)?;
    let shared = !alone(r);
    let most = most.min(PAY_FREED);
    let freed = dying_in(r, cx, n, false, most + 1, shared)?;
    if freed > most {
        return Ok(None);
    }
    // The operands a form may have at no cost: the atoms and the nodes below `n`.
    let cap = region_cap(r);
    let mut leaves: Vec<u32> = Vec::new();
    {
        let sc = &mut r.scratch;
        sc.seen.begin(cx.len());
        sc.stack.clear();
        sc.stack.push(n);
        while let Some(i) = sc.stack.pop() {
            if !sc.seen.insert(i) {
                continue;
            }
            if i != n {
                leaves.push(i);
            }
            if sc.atoms.contains(i) {
                continue;
            }
            // A region cut short by its cap undercounts what is freed.
            if !sc.region.contains(i) || leaves.len() as u32 >= cap {
                return Ok(None);
            }
            sc.stack.extend(cx.node(i).children());
        }
        // (Atoms of a rewrite of `n` that `n` does not read are atoms of the form too.)
        for &a in atoms {
            if a != n && sc.seen.insert(a) {
                leaves.push(a);
            }
        }
    }
    r.meter.charge(Counter::PassWork, leaves.len() as u64 + 1)?;
    r.sample(cx, n)?;
    for &a in atoms {
        r.sample(cx, a)?;
    }
    // The nodes that stop being used with `n` (kept, they are not freed), and those that
    // stay: `n` as it is is none of either.
    let (dying, stay): (Vec<u32>, Vec<u32>) =
        leaves.iter().partition(|&&i| r.scratch.decided.contains(i));
    let mut one = stay.clone();
    if freed == 3 {
        // One operator pays for two freed nodes: it may read one node that goes with `n`
        // if the other still goes then.
        for &d in &dying {
            r.scratch.kept.begin(cx.len());
            r.scratch.kept.insert(d);
            if dying_in(r, cx, n, true, 3, shared)? >= 2 {
                one.push(d);
            }
        }
    }
    // The same comparison as one made earlier in the call (the node asked again in a later
    // round, with the same nodes going and staying): its answer.
    let known = r.paid.get(&n).and_then(|asked| {
        asked
            .iter()
            .find(|p| {
                p.free == free
                    && p.freed == freed
                    && *p.atoms == *atoms
                    && *p.stay == *stay
                    && *p.one == *one
            })
            .map(|p| p.found)
    });
    let found = match known {
        Some(found) => found,
        None => {
            let forms = Forms {
                n,
                leaves: &leaves,
                one: &one,
                apart: one.len() - stay.len(),
                stay: &stay,
                freed,
            };
            // The forms of one node at most first, at the verification points (they are
            // there); then every form where the atoms are free, if one agreed or two
            // operators are to be tried (as many agree only by how the atoms are related as
            // do not: half the search); at the verification points where no such values are.
            let (mut found, work) = Forms {
                freed: freed.min(2),
                ..forms
            }
            .agree(&r.samples, cx);
            r.meter.charge(Counter::PassWork, work)?;
            if found || freed == 3 {
                let values = if free {
                    free_values(r, cx, n, atoms)?
                } else {
                    None
                };
                if values.is_some() || !found {
                    let (again, work) = forms.agree(values.as_ref().unwrap_or(&r.samples), cx);
                    r.meter.charge(Counter::PassWork, work)?;
                    found = again;
                }
            }
            r.paid.entry(n).or_default().push(Paid {
                atoms: atoms.into(),
                free,
                freed,
                stay: stay.into(),
                one: one.into(),
                found,
            });
            found
        }
    };
    if found {
        return Ok(None);
    }
    let lone = if shared {
        dying_in(r, cx, n, false, most + 1, false)?
    } else {
        freed
    };
    Ok(Some(if lone == freed {
        Fin::FINAL
    } else {
        Fin::PROVISIONAL
    }))
}

/// A comparison [`cannot_pay`] made at a node: what decides it besides the node (the atoms,
/// whether they took free values, the nodes freed, those that stay and those one operator
/// may read), and whether a form agreed.
#[cfg(feature = "mba")]
pub(crate) struct Paid {
    atoms: Box<[u32]>,
    free: bool,
    freed: u32,
    stay: Box<[u32]>,
    one: Box<[u32]>,
    found: bool,
}

/// The forms [`cannot_pay`] compares with `n`: of no node of their own over `leaves`, of one
/// over `one` (no two of the last `apart` under it), of two over `stay`; as many as `freed`
/// allows.
#[cfg(feature = "mba")]
struct Forms<'a> {
    n: u32,
    leaves: &'a [u32],
    one: &'a [u32],
    apart: usize,
    stay: &'a [u32],
    freed: u32,
}

#[cfg(feature = "mba")]
impl Forms<'_> {
    /// Whether `n` is a constant at every point of `values` or a form agrees with it there,
    /// and the work it took.
    fn agree(&self, values: &crate::hash::IdMap<u32, Box<[BitVec]>>, cx: &Context) -> (bool, u64) {
        let n = self.n;
        let w = cx.wid(n);
        let vn = &values[&n];
        let mut work = self.leaves.len() as u64;
        if vn.iter().all(|v| *v == vn[0])
            || self
                .leaves
                .iter()
                .any(|i| cx.wid(*i) == w && values[i] == *vn)
        {
            return (true, work);
        }
        if self.freed >= 2 {
            let (found, more) = one_operator(values, cx, n, self.one, self.apart);
            work += more;
            if found {
                return (true, work);
            }
        }
        if self.freed >= 3 {
            let (found, more) = two_operators(values, cx, n, self.stay);
            work += more;
            if found {
                return (true, work);
            }
        }
        (false, work)
    }
}

/// The points [`free_values`] evaluates at.
#[cfg(feature = "mba")]
const FREE_POINTS: usize = 16;

/// The values of `n` and of the nodes between it and `atoms` at [`FREE_POINTS`] points where
/// the atoms take independent values (seeded by what they are): what an identity over the
/// atoms holds at. Two atoms stay related: a comparison and its negation, because `~` of a
/// comparison is built as the negated comparison, which is then the other atom. `None` where
/// that cannot be evaluated (a node below `n` that is neither an atom nor computed from them),
/// or an atom is one the constructors read through otherwise.
#[cfg(feature = "mba")]
#[allow(clippy::type_complexity)]
fn free_values(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    atoms: &[u32],
) -> Result<Option<crate::hash::IdMap<u32, Box<[BitVec]>>>, Stop> {
    use crate::ops::{CmpOp, UnOp};
    let mut values: crate::hash::IdMap<u32, Box<[BitVec]>> = Default::default();
    for &a in atoms {
        let node = cx.node(a);
        if matches!(
            node.op,
            OpCode::Const
                | OpCode::Not
                | OpCode::Neg
                | OpCode::Zext
                | OpCode::Sext
                | OpCode::Extract
                | OpCode::Concat
        ) {
            return Ok(None);
        }
        let seed = cx.meta[a as usize].shash ^ 0x6672_6565_6174_6f6d;
        let w = cx.width_of(a);
        values.insert(
            a,
            (0..FREE_POINTS)
                .map(|k| super::point_value(seed, w, k + 2))
                .collect(),
        );
    }
    for (at, &a) in atoms.iter().enumerate() {
        let node = cx.node(a);
        let Some(op) = node.op.as_cmp() else {
            continue;
        };
        // (An equality of one bit with a constant is built as the bit or its complement.)
        if matches!(op, CmpOp::Eq | CmpOp::Ne)
            && cx.wid(node.a) == 1
            && (cx.const_val(node.a).is_some() || cx.const_val(node.b).is_some())
        {
            return Ok(None);
        }
        let (not, swap) = op.negated().canonical();
        let (x, y) = if swap {
            (node.b, node.a)
        } else {
            (node.a, node.b)
        };
        let not = OpCode::from_cmp(not);
        for &b in &atoms[at + 1..] {
            let other = cx.node(b);
            if other.op == not && other.a == x && other.b == y {
                let flipped = values[&a]
                    .iter()
                    .map(|v| BitVec::un_unchecked(UnOp::Not, v))
                    .collect();
                values.insert(b, flipped);
            }
        }
    }
    let mut stack: Vec<(u32, bool)> = vec![(n, false)];
    while let Some((i, expanded)) = stack.pop() {
        if values.contains_key(&i) {
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in cx.node(i).children() {
                if !values.contains_key(&c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, FREE_POINTS as u64)?;
        let at: Result<Box<[BitVec]>, crate::Error> = (0..FREE_POINTS)
            .map(|k| cx.eval_node(i, |j| values[&j][k], |_, _| None))
            .collect();
        match at {
            Ok(v) => values.insert(i, v),
            Err(_) => return Ok(None),
        };
    }
    Ok(Some(values))
}

/// Whether one operator over `leaves` agrees with `n` at every point of `samples` (see
/// [`cannot_pay`]), and the work it took (a unit per candidate screened): no two of the last
/// `apart` leaves under one operator. Values up to 64 bits are compared as words, at one
/// seeded point first; a wider `n` is taken to have one.
#[cfg(feature = "mba")]
fn one_operator(
    samples: &crate::hash::IdMap<u32, Box<[BitVec]>>,
    cx: &Context,
    n: u32,
    leaves: &[u32],
    apart: usize,
) -> (bool, u64) {
    let w = cx.wid(n);
    let Ok(wn) = Width::new(w) else {
        return (true, 0);
    };
    if w > 64 {
        return (true, 0);
    }
    let mask = u64::MAX >> (64 - w);
    let lane = |i: u32| -> Option<Vec<u64>> { samples[&i].iter().map(BitVec::to_u64).collect() };
    let Some(t) = lane(n) else {
        return (true, 0);
    };
    // The first two points are all zeros and all ones: screen at a seeded one.
    let k = 2.min(t.len() - 1);
    let mut work = 0u64;
    let mut same: Vec<(Vec<u64>, bool)> = Vec::new();
    for (at, &i) in leaves.iter().enumerate() {
        let wi = cx.wid(i);
        work += 1;
        if wi > 64 {
            // A slice of a wide value.
            let vi = &samples[&i];
            work += u64::from(wi - w);
            if (0..=wi - w).any(|lo| {
                vi.iter()
                    .zip(samples[&n].iter())
                    .all(|(v, x)| v.extract(lo, wn).ok().as_ref() == Some(x))
            }) {
                return (true, work);
            }
            continue;
        }
        let Some(v) = lane(i) else {
            return (true, work);
        };
        let all =
            |f: &dyn Fn(u64) -> u64| f(v[k]) == t[k] && v.iter().zip(&t).all(|(&x, &y)| f(x) == y);
        if wi == w {
            if all(&|x| !x & mask) || all(&|x| x.wrapping_neg() & mask) {
                return (true, work);
            }
            same.push((v, at >= leaves.len() - apart));
        } else if wi < w {
            let sign = 1u64 << (wi - 1);
            if all(&|x| x) || all(&|x| ((x ^ sign).wrapping_sub(sign)) & mask) {
                return (true, work);
            }
        } else {
            work += u64::from(wi - w);
            if (0..=wi - w).any(|lo| all(&|x| (x >> lo) & mask)) {
                return (true, work);
            }
        }
    }
    let shl = |x: u64, y: u64| if y < u64::from(w) { x << y } else { 0 };
    let shr = |x: u64, y: u64| if y < u64::from(w) { x >> y } else { 0 };
    let ops: [&dyn Fn(u64, u64) -> u64; 11] = [
        &|x, y| x.wrapping_add(y),
        &|x, y| x.wrapping_sub(y),
        &|x, y| y.wrapping_sub(x),
        &|x, y| x.wrapping_mul(y),
        &|x, y| x & y,
        &|x, y| x | y,
        &|x, y| x ^ y,
        &shl,
        &|x, y| shl(y, x),
        &shr,
        &|x, y| shr(y, x),
    ];
    for (j, (a, x)) in same.iter().enumerate() {
        for (b, y) in &same[j..] {
            if *x && *y && !core::ptr::eq(a, b) {
                continue;
            }
            work += 1;
            for f in ops {
                if f(a[k], b[k]) & mask == t[k]
                    && a.iter()
                        .zip(b)
                        .zip(&t)
                        .all(|((&x, &y), &z)| f(x, y) & mask == z)
                {
                    return (true, work);
                }
            }
        }
    }
    (false, work)
}

/// A mask of the low `bits` bits.
#[cfg(feature = "mba")]
fn low_ones(bits: u32) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// `x`, a value of `bits` bits (1 to 64), sign-extended to 64.
#[cfg(feature = "mba")]
fn signed(x: u64, bits: u32) -> u64 {
    let s = 64 - bits;
    (((x << s) as i64) >> s) as u64
}

/// The operators of two operands of one width a form may have, by number, on values of
/// `w` bits (the result is not masked): `+`, `−` both ways, `·`, `&`, `|`, `^`, `<<` and `>>u`
/// both ways.
#[cfg(feature = "mba")]
fn bin_value(o: u8, x: u64, y: u64, w: u32) -> u64 {
    let w = u64::from(w);
    match o {
        0 => x.wrapping_add(y),
        1 => x.wrapping_sub(y),
        2 => y.wrapping_sub(x),
        3 => x.wrapping_mul(y),
        4 => x & y,
        5 => x | y,
        6 => x ^ y,
        7 if y < w => x << y,
        8 if x < w => y << x,
        9 if y < w => x >> y,
        10 if x < w => y >> x,
        _ => 0,
    }
}

/// How many operators [`bin_value`] numbers.
#[cfg(feature = "mba")]
const BIN_VALUES: u8 = 11;

/// The inverse of an odd `a` modulo `2^64`.
#[cfg(feature = "mba")]
fn odd_inverse(a: u64) -> u64 {
    // (Correct to three bits; each step doubles them.)
    let mut x = a;
    for _ in 0..5 {
        x = x.wrapping_mul(2u64.wrapping_sub(a.wrapping_mul(x)));
    }
    x
}

/// The operands of `n`'s width by their value at one verification point: open addressing,
/// filled in the operands' order (so what it finds, and in which order, is the values' alone).
#[cfg(feature = "mba")]
struct ByValue {
    slots: Vec<(u64, u32)>,
    shift: u32,
}

#[cfg(feature = "mba")]
impl ByValue {
    fn new(values: impl ExactSizeIterator<Item = u64>) -> Self {
        let size = (values.len() * 4).next_power_of_two().max(16);
        let mut t = ByValue {
            slots: vec![(0, u32::MAX); size],
            shift: 64 - size.trailing_zeros(),
        };
        for (i, v) in values.enumerate() {
            let mut at = t.home(v);
            while t.slots[at].1 != u32::MAX {
                at = (at + 1) & (size - 1);
            }
            t.slots[at] = (v, i as u32);
        }
        t
    }

    fn home(&self, v: u64) -> usize {
        (v.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> self.shift) as usize
    }

    /// The operands whose value is `v`.
    fn of(&self, v: u64) -> impl Iterator<Item = usize> + '_ {
        let mut at = self.home(v);
        core::iter::from_fn(move || {
            loop {
                let (x, i) = self.slots[at];
                if i == u32::MAX {
                    return None;
                }
                at = (at + 1) & (self.slots.len() - 1);
                if x == v {
                    return Some(i as usize);
                }
            }
        })
    }

    /// Whether an operand's value is `v`.
    fn has(&self, v: u64) -> bool {
        let mut at = self.home(v);
        loop {
            let (x, i) = self.slots[at];
            if i == u32::MAX {
                return false;
            }
            if x == v {
                return true;
            }
            at = (at + 1) & (self.slots.len() - 1);
        }
    }
}

/// Whether a form of two nodes of its own over `leaves` agrees with `n` at every verification
/// point (see [`cannot_pay`]; `n` is taken to have one where it or a leaf is wider than 64
/// bits, or the leaves are more than [`PAY_LEAVES`]), and the work it took (a unit per
/// candidate screened). The forms, `l` a leaf and `c` a constant that is no leaf:
///
/// - one operator and a constant: `l + c` (which `l − c` is), `c − l`, `l ^ c`, `l & c`,
///   `l | c`, `l · c` (which `l << c` is), `l >>u c`, `c << l`, `c >>u l`. The constant is
///   computed, not searched: from one point for the invertible operators; the least mask for
///   `&` and `|`; for `·` from a point where `l` has the fewest trailing zeros (any other
///   solution differs from it in bits no point reads), and so for a constant shifted by `l`
///   from the point of the least count;
/// - two operators of one operand over one leaf: `~` and `−` with an extension or a slice,
///   either way round; a slice of the leaf extended by zeros or by its sign (which an
///   extension of a slice and a slice across the end of an extension are: only the shortest
///   slice that holds every value of `n` needs trying); a sign extension extended by zeros;
/// - an operator of one operand over an operator of two over two leaves of one width;
/// - an operator of two operands over a leaf and an operator over leaves, or over that
///   operator twice. The inner values are enumerated; the leaf is looked up by its value at
///   one point where the outer operator is invertible (`+ − ^`), and elsewhere taken from the
///   few leaves the operator admits at every point (`r & l = n` needs `n ⊆ l`).
///
/// Values are compared as words, at one seeded point first: wider than 64 bits (`n` or a
/// leaf), or with more than [`PAY_LEAVES`] leaves, a form is taken to agree.
#[cfg(feature = "mba")]
fn two_operators(
    samples: &crate::hash::IdMap<u32, Box<[BitVec]>>,
    cx: &Context,
    n: u32,
    leaves: &[u32],
) -> (bool, u64) {
    let w = u32::from(cx.wid(n));
    if w > 64 || leaves.len() > PAY_LEAVES {
        return (true, 0);
    }
    let lane = |i: u32| -> Option<Vec<u64>> { samples[&i].iter().map(BitVec::to_u64).collect() };
    let Some(t) = lane(n) else {
        return (true, 0);
    };
    let mask = low_ones(w);
    // The first two points are all zeros and all ones: screen at a seeded one.
    let k = 2.min(t.len() - 1);
    let tk = t[k];
    let mut work = leaves.len() as u64;
    // The leaves of `n`'s width, and the others.
    let mut same: Vec<Vec<u64>> = Vec::new();
    let mut other: Vec<(u32, Vec<u64>)> = Vec::new();
    for &i in leaves {
        let wi = u32::from(cx.wid(i));
        let v = if wi > 64 { None } else { lane(i) };
        let Some(v) = v else {
            return (true, work);
        };
        if wi == w {
            same.push(v);
        } else {
            other.push((wi, v));
        }
    }
    let all =
        |f: &dyn Fn(usize) -> u64| f(k) & mask == tk && (0..t.len()).all(|i| f(i) & mask == t[i]);
    let zeros = |x: u64| x.trailing_zeros().min(w);
    // Every bit some value of `n` has; the fewest bits that hold every value of `n` as an
    // unsigned number, and as a signed one.
    let t_or = t.iter().fold(0, |a, &x| a | x);
    let t_bits = (64 - t_or.leading_zeros()).max(1);
    let t_signed = t
        .iter()
        .map(|&x| {
            let v = signed(x, w);
            65 - (v ^ (((v as i64) >> 63) as u64)).leading_zeros()
        })
        .max()
        .unwrap_or(1)
        .min(w);

    // One operator and a constant.
    for x in &same {
        work += 4;
        let (plus, from, xor) = (
            t[0].wrapping_sub(x[0]),
            t[0].wrapping_add(x[0]),
            t[0] ^ x[0],
        );
        let or = t.iter().zip(x).fold(0, |a, (&y, &x)| a | (y & !x));
        if all(&|i| x[i].wrapping_add(plus))
            || all(&|i| from.wrapping_sub(x[i]))
            || all(&|i| x[i] ^ xor)
            || all(&|i| x[i] & t_or)
            || all(&|i| x[i] | or)
        {
            return (true, work);
        }
        // (The point where the leaf has the fewest trailing zeros.)
        if let Some(i) = (0..t.len()).min_by_key(|&i| zeros(x[i]))
            && zeros(x[i]) < w
        {
            let z = zeros(x[i]);
            let c = (t[i] >> z).wrapping_mul(odd_inverse(x[i] >> z));
            if all(&|i| x[i].wrapping_mul(c)) {
                return (true, work);
            }
        }
        for c in 1..=(w - t_bits).min(w - 1) {
            work += 1;
            if all(&|i| x[i] >> c) {
                return (true, work);
            }
        }
        // (The point where the leaf, a count, is least.)
        if let Some(i) = (0..t.len()).min_by_key(|&i| x[i])
            && x[i] < u64::from(w)
        {
            let (left, right) = (t[i] >> x[i], (t[i] << x[i]) & mask);
            if all(&|i| bin_value(8, x[i], left, w)) || all(&|i| bin_value(10, x[i], right, w)) {
                return (true, work);
            }
        }
    }

    // Two operators of one operand over one leaf.
    for (wl, x) in same
        .iter()
        .map(|x| (w, x))
        .chain(other.iter().map(|(wl, x)| (*wl, x)))
    {
        let ml = low_ones(wl);
        let sx = |v: u64| signed(v, wl);
        if wl < w {
            work += u64::from(w - wl) + 7;
            if all(&|i| !x[i] & ml)
                || all(&|i| x[i].wrapping_neg() & ml)
                || all(&|i| !x[i])
                || all(&|i| x[i].wrapping_neg())
                || all(&|i| !sx(x[i]))
                || all(&|i| sx(x[i].wrapping_neg() & ml))
                || all(&|i| sx(x[i]).wrapping_neg())
                || (wl + 1..w).any(|mid| all(&|i| sx(x[i]) & low_ones(mid)))
            {
                return (true, work);
            }
        }
        if wl > w {
            work += 3 * u64::from(wl - w + 1);
            if (0..=wl - w).any(|lo| {
                all(&|i| !(x[i] >> lo))
                    || all(&|i| (x[i] >> lo).wrapping_neg())
                    || all(&|i| (x[i].wrapping_neg() & ml) >> lo)
            }) {
                return (true, work);
            }
        }
        // A slice of the leaf extended by zeros, and by its sign.
        work += 2 * u64::from(wl);
        if (0..wl).any(|lo| {
            (lo + t_bits <= wl && all(&|i| (x[i] >> lo) & low_ones(t_bits)))
                || (lo + t_signed <= wl
                    && all(&|i| signed((x[i] >> lo) & low_ones(t_signed), t_signed)))
        }) {
            return (true, work);
        }
    }

    // An operator of one operand over an operator of two over two leaves of another width.
    for (j, (wl, a)) in other.iter().enumerate() {
        let (wl, ml) = (*wl, low_ones(*wl));
        for (_, b) in other[j..].iter().filter(|(wb, _)| *wb == wl) {
            work += u64::from(BIN_VALUES) * u64::from(if wl < w { 2 } else { 1 + w / 8 });
            for o in 0..BIN_VALUES {
                let v = |i: usize| bin_value(o, a[i], b[i], wl) & ml;
                let found = if wl < w {
                    all(&v) || all(&|i| signed(v(i), wl))
                } else {
                    // Every slice at once: bit `lo` of `at` says that the slice from `lo`
                    // is `n`'s value at the points so far (the screening point first).
                    let mut at = low_ones(wl - w + 1);
                    for i in core::iter::once(k).chain(0..t.len()) {
                        let x = v(i);
                        for j in 0..w {
                            at &= if t[i] >> j & 1 == 1 {
                                x >> j
                            } else {
                                !(x >> j)
                            };
                        }
                        if at == 0 {
                            break;
                        }
                    }
                    at != 0
                };
                if found {
                    return (true, work);
                }
            }
        }
    }

    // An operator over a value `v` of one operator (`at` its value at the screening point)
    // and a leaf, or over `v` twice, or of one operand. Without `v`: whether one may agree,
    // by the screening point alone.
    let by_value = ByValue::new(same.iter().map(|x| x[k]));
    // The leaves an operator that is not invertible admits, as its right and its left operand.
    let admits = |f: &dyn Fn(u64, u64) -> bool| -> Vec<usize> {
        (0..same.len())
            .filter(|&c| same[c].iter().zip(&t).all(|(&c, &y)| f(c, y)))
            .collect()
    };
    let and = admits(&|c, y| y & !c == 0);
    let or = admits(&|c, y| c & !y == 0);
    let mul = admits(&|c, y| zeros(y) >= zeros(c));
    let shl_by = admits(&|c, y| {
        if c >= u64::from(w) {
            y == 0
        } else {
            y & low_ones(c as u32) == 0
        }
    });
    let shr_by = admits(&|c, y| {
        if c >= u64::from(w) {
            y == 0
        } else {
            y & !(mask >> c) == 0
        }
    });
    let shl_of = admits(&|c, y| {
        y == 0 || (c != 0 && zeros(y) >= zeros(c) && (c << (zeros(y) - zeros(c))) & mask == y)
    });
    let shr_of = admits(&|c, y| {
        y == 0
            || (c != 0
                && y.leading_zeros() >= c.leading_zeros()
                && c >> (y.leading_zeros() - c.leading_zeros()) == y)
    });
    let with: [(u8, &[usize]); 7] = [
        (4, &and),
        (5, &or),
        (3, &mul),
        (7, &shl_by),
        (9, &shr_by),
        (8, &shl_of),
        (10, &shr_of),
    ];
    let over = |v: &dyn Fn(usize) -> u64| -> bool {
        let agrees = |f: &dyn Fn(u64, usize) -> u64| -> bool { all(&|i| f(v(i), i)) };
        if agrees(&|x, _| !x) || agrees(&|x, _| x.wrapping_neg()) {
            return true;
        }
        if [0, 3, 7, 9]
            .iter()
            .any(|&o| agrees(&|x, _| bin_value(o, x, x, w)))
        {
            return true;
        }
        // `v + l`, `v − l`, `l − v`, `v ^ l`: the leaf's value is the others'.
        let at = v(k);
        let keys = [
            tk.wrapping_sub(at) & mask,
            at.wrapping_sub(tk) & mask,
            tk.wrapping_add(at) & mask,
            tk ^ at,
        ];
        for (o, key) in [0u8, 1, 2, 6].into_iter().zip(keys) {
            for c in by_value.of(key) {
                if agrees(&|x, i| bin_value(o, x, same[c][i], w)) {
                    return true;
                }
            }
        }
        with.iter().any(|&(o, admitted)| {
            admitted
                .iter()
                .any(|&c| agrees(&|x, i| bin_value(o, x, same[c][i], w)))
        })
    };
    // Whether a value that is `at` at the screening point may pass `over`: what `over` tests,
    // at that point alone (most values end here).
    let admitted = with.iter().any(|(_, l)| !l.is_empty());
    let may = |at: u64| -> bool {
        !at & mask == tk
            || at.wrapping_neg() & mask == tk
            || at.wrapping_add(at) & mask == tk
            || at.wrapping_mul(at) & mask == tk
            || bin_value(7, at, at, w) & mask == tk
            || bin_value(9, at, at, w) & mask == tk
            || by_value.has(tk.wrapping_sub(at) & mask)
            || by_value.has(at.wrapping_sub(tk) & mask)
            || by_value.has(tk.wrapping_add(at) & mask)
            || by_value.has(tk ^ at)
            || (admitted
                && with.iter().any(|&(o, l)| {
                    l.iter()
                        .any(|&c| bin_value(o, at, same[c][k], w) & mask == tk)
                }))
    };
    // (A value that is zero at the screening point is common: a shift past the width.)
    let zero = may(0);
    let tried = |at: u64, v: &dyn Fn(usize) -> u64, work: &mut u64| -> bool {
        *work += 1;
        let at = at & mask;
        debug_assert!(may(at) || !over(v));
        (at != 0 || zero) && may(at) && over(v)
    };
    for x in &same {
        if tried(!x[k], &|i| !x[i] & mask, &mut work)
            || tried(
                x[k].wrapping_neg(),
                &|i| x[i].wrapping_neg() & mask,
                &mut work,
            )
        {
            return (true, work);
        }
    }
    for (wl, x) in &other {
        let wl = *wl;
        let found = if wl < w {
            tried(x[k], &|i| x[i], &mut work)
                || tried(signed(x[k], wl), &|i| signed(x[i], wl) & mask, &mut work)
        } else {
            (0..=wl - w).any(|lo| tried(x[k] >> lo, &|i| (x[i] >> lo) & mask, &mut work))
        };
        if found {
            return (true, work);
        }
    }
    for (j, a) in same.iter().enumerate() {
        for b in &same[j..] {
            for o in 0..BIN_VALUES {
                if tried(
                    bin_value(o, a[k], b[k], w),
                    &|i| bin_value(o, a[i], b[i], w) & mask,
                    &mut work,
                ) {
                    return (true, work);
                }
            }
        }
    }
    (false, work)
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
    pays(r, cx, n, e, atoms, 0)
}

/// Whether replacing `n` by `e` leaves the DAG no larger and makes `n` a strictly smaller tree:
/// for a candidate nothing rewrites back, where rewrites that each only tie, because they share
/// what they would free, together make the DAG smaller (two comparisons narrowed from the same
/// wide operand). Each such step still decreases (DAG size, tree size), so they terminate.
pub(super) fn ties_smaller(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    e: u32,
    atoms: &[u32],
) -> Result<Result<(), Fin>, Stop> {
    let tree = |i: u32| cx.meta[i as usize].tree;
    let tie = tree(n) != u32::MAX && tree(e) < tree(n);
    pays(r, cx, n, e, atoms, u32::from(tie))
}

/// Whether replacing `n` by `e` frees more nodes than it needs less `slack`: [`shrinks`]
/// without any, with 1 also where the DAG stays the same size, with 2 where it grows by one.
fn pays(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    e: u32,
    atoms: &[u32],
    slack: u32,
) -> Result<Result<(), Fin>, Stop> {
    if cx.node(e).op == OpCode::Const && cx.node(n).op != OpCode::Const {
        return Ok(Ok(()));
    }
    region(r, cx, n, atoms)?;
    r.meter.check()?;
    let Some(new) = needed(r, cx, e)? else {
        return Ok(Err(Fin::FINAL));
    };
    let gain = |freed: u32| new < freed.saturating_add(slack);
    if alone(r) {
        let freed = dying_in(r, cx, n, true, new.saturating_add(1), false)?;
        if gain(freed) {
            return Ok(Ok(()));
        }
        r.not_smaller(cx, n, Some(e), new, freed, false);
        return Ok(Err(Fin::FINAL));
    }
    let freed = dying_in(r, cx, n, true, new.saturating_add(1), true)?;
    if !gain(freed) {
        let alone = dying_in(r, cx, n, true, new.saturating_add(1), false)?;
        r.not_smaller(cx, n, Some(e), new, freed, gain(alone));
        return Ok(Err(if gain(alone) {
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
    finish_with(r, cx, kind, n, e, before, atoms, fin, false)
}

/// [`finish`], with `tie` also committing a candidate that leaves the DAG the same size: for a
/// pass whose result is a normal form nothing rewrites back (a division in place of the
/// multiply-high that computes it), so no two rewrites can undo each other.
#[allow(clippy::too_many_arguments)]
pub(super) fn finish_with(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    kind: PassKind,
    n: u32,
    e: u32,
    before: u32,
    atoms: &[u32],
    fin: Fin,
    tie: bool,
) -> Result<Step, Stop> {
    finish_within(r, cx, kind, n, e, before, atoms, fin, u32::from(tie))
}

/// [`finish`], committing a candidate that needs fewer nodes than replacing `n` frees plus
/// `slack` (see [`pays`]). With 2 the DAG may grow by one node: only for a form no pass reads
/// again as what it was and that the other readers of what it leaves behind are rewritten to
/// as well (a limb as the slice of its word: the limb's arithmetic dies with its last
/// reader), so the growth is at most one node a rewrite and none in the end.
#[allow(clippy::too_many_arguments)]
pub(super) fn finish_within(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    kind: PassKind,
    n: u32,
    e: u32,
    before: u32,
    atoms: &[u32],
    fin: Fin,
    slack: u32,
) -> Result<Step, Stop> {
    let name = kind.name();
    if e == n {
        r.explain = None;
        r.stats.passes.entry(name).or_default().noop += 1;
        return Ok(Step::Normal(fin));
    }
    let pays = if slack == 0 {
        shrinks(r, cx, n, e, atoms)?
    } else {
        pays(r, cx, n, e, atoms, slack)?
    };
    if let Err(more) = pays {
        // A rejection that only sharing caused is not final (see `shrinks`).
        r.explain = None;
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

/// [`discard`], but for the nodes `keep` reaches: for a pass that built two candidates and
/// goes on with one.
pub(super) fn discard_but(r: &mut Runner<'_, '_>, cx: &Context, before: u32, keep: u32) {
    let mut kept = crate::hash::IdMap::default();
    let mut stack = vec![keep];
    while let Some(i) = stack.pop() {
        if i >= before && kept.insert(i, ()).is_none() {
            stack.extend(cx.node(i).children());
        }
    }
    for i in before..cx.len() as u32 {
        if !kept.contains_key(&i) {
            r.retire(cx, i);
        }
    }
}

/// The nodes replacing `n` by `e` frees less the nodes it needs, as the commit rule counts
/// them ([`pays`]): for a pass that chooses between two candidates. `None` when `e` needs more
/// than the commit rule examines.
pub(super) fn margin(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    e: u32,
    atoms: &[u32],
) -> Result<Option<i64>, Stop> {
    region(r, cx, n, atoms)?;
    r.meter.check()?;
    let Some(new) = needed(r, cx, e)? else {
        return Ok(None);
    };
    let shared = !alone(r);
    let freed = dying_in(r, cx, n, true, u32::MAX, shared)?;
    Ok(Some(i64::from(freed) - i64::from(new)))
}

/// [`margin`], and the same with the uses from outside the region of `n` ignored (what the
/// commit rule would count were `n` alone): a candidate that pays only by the second is
/// refused because of sharing.
#[cfg(feature = "prove")]
pub(super) fn margins(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    e: u32,
    atoms: &[u32],
) -> Result<Option<(i64, i64)>, Stop> {
    region(r, cx, n, atoms)?;
    r.meter.check()?;
    let Some(new) = needed(r, cx, e)? else {
        return Ok(None);
    };
    let lone = dying_in(r, cx, n, true, u32::MAX, false)?;
    let freed = if alone(r) {
        lone
    } else {
        dying_in(r, cx, n, true, u32::MAX, true)?
    };
    let new = i64::from(new);
    Ok(Some((i64::from(freed) - new, i64::from(lone) - new)))
}
