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
pub(crate) mod gf2;
pub(super) mod invert;
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
pub(super) mod words;
pub(super) mod xor;

use super::{Accept, By, Fin, Reject, Runner, Sharing, Step, Stop};
use crate::engine::budget::Counter;
use crate::engine::{Exhausted, Explanation};
use crate::expr::{Context, OpCode};
use crate::facts::{Facts, KnownBits, Reliance};

/// A value per node index, for the engine's per-node scratch: emptied in constant time, and
/// costing what it holds, not what the context holds. A query of a few nodes in a context of
/// millions touches a few entries, so those are kept in a hash map; once it holds more than a
/// fraction of the context's nodes it becomes a dense table (a stamp per index, emptied by a
/// new epoch; a stamp of 0 is never current), whose size is then paid for by what filled it.
pub(crate) struct Slots<T> {
    few: crate::hash::IdMap<u32, T>,
    stamp: Vec<u32>,
    val: Vec<T>,
    epoch: u32,
    dense: bool,
    /// The context's node count when last begun: what the dense table is sized for.
    len: usize,
}

impl<T> Default for Slots<T> {
    fn default() -> Self {
        Slots {
            few: Default::default(),
            stamp: Vec::new(),
            val: Vec::new(),
            epoch: 1,
            // (Dense until it is known to be of a large context: see `begin` and `set_slow`.)
            dense: true,
            len: 0,
        }
    }
}

impl<T: Copy + Default> Slots<T> {
    /// The entries a hash map holds before the table turns dense: at least this many, and
    /// one in this many of the context's nodes.
    const FEW: usize = 1024;
    const FRACTION: usize = 32;
    /// A context of at most this many nodes gets the dense table at once.
    const SMALL: usize = 1 << 14;

    /// Empties it, for indices below `len` (it grows to any index it is given).
    pub(crate) fn begin(&mut self, len: usize) {
        self.len = self.len.max(len);
        self.clear();
        // A small context is cheaper as a table from the start: the table is no larger than
        // the map would grow, and indexing it does not hash. (A table kept for that reason
        // is given up when the context has outgrown it.)
        if self.len <= Self::SMALL {
            self.dense = true;
        } else if self.dense && self.stamp.len() <= Self::SMALL {
            self.dense = false;
            self.few.clear();
        }
    }

    /// Empties it.
    pub(crate) fn clear(&mut self) {
        if self.dense {
            self.epoch = self.epoch.wrapping_add(1);
            if self.epoch == 0 {
                self.stamp.fill(0);
                self.epoch = 1;
            }
        } else {
            self.few.clear();
        }
    }

    #[inline]
    pub(crate) fn get(&self, i: u32) -> Option<T> {
        if self.dense {
            let i = i as usize;
            (self.stamp.get(i) == Some(&self.epoch)).then(|| self.val[i])
        } else {
            self.few.get(&i).copied()
        }
    }

    #[inline]
    pub(crate) fn contains(&self, i: u32) -> bool {
        if self.dense {
            self.stamp.get(i as usize) == Some(&self.epoch)
        } else {
            self.few.contains_key(&i)
        }
    }

    /// Sets `i`'s value: whether it had none.
    #[inline]
    pub(crate) fn set(&mut self, i: u32, v: T) -> bool {
        let at = i as usize;
        if self.dense && at < self.stamp.len() {
            let fresh = self.stamp[at] != self.epoch;
            self.stamp[at] = self.epoch;
            self.val[at] = v;
            return fresh;
        }
        self.set_slow(i, v)
    }

    #[inline(never)]
    fn set_slow(&mut self, i: u32, v: T) -> bool {
        // A table that was dense for a small context, given an index beyond one: what it
        // holds goes to the map, as in a context that was large from the start.
        if self.dense && self.stamp.len() <= Self::SMALL && i as usize >= Self::SMALL {
            self.dense = false;
            self.few.clear();
            for (at, s) in self.stamp.iter_mut().enumerate() {
                if *s == self.epoch {
                    self.few.insert(at as u32, self.val[at]);
                }
                *s = 0;
            }
        }
        if !self.dense {
            if self.few.len() < Self::FEW.max(self.len / Self::FRACTION) {
                return self.few.insert(i, v).is_none();
            }
            self.densify();
        }
        let at = i as usize;
        if at >= self.stamp.len() {
            let to = (at + 1).max(self.len).max(self.stamp.len() * 2);
            self.stamp.resize(to, 0);
            self.val.resize(to, T::default());
        }
        let fresh = self.stamp[at] != self.epoch;
        self.stamp[at] = self.epoch;
        self.val[at] = v;
        fresh
    }

    #[cold]
    fn densify(&mut self) {
        self.dense = true;
        let top = self.few.keys().max().map_or(0, |&m| m as usize + 1);
        let to = top.max(self.len);
        if self.stamp.len() < to {
            self.stamp.resize(to, 0);
            self.val.resize(to, T::default());
        }
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.stamp.fill(0);
            self.epoch = 1;
        }
        for (i, v) in self.few.drain() {
            self.stamp[i as usize] = self.epoch;
            self.val[i as usize] = v;
        }
    }

    /// Removes `i`'s value: whether it had one.
    #[inline]
    pub(crate) fn remove(&mut self, i: u32) -> bool {
        if self.dense {
            match self.stamp.get_mut(i as usize) {
                Some(s) if *s == self.epoch => {
                    *s = 0;
                    true
                }
                _ => false,
            }
        } else {
            self.few.remove(&i).is_some()
        }
    }
}

/// A set of node indices emptied in constant time: the engine's per-node scratch, kept by the
/// runner and reused instead of hash sets. It grows to any index it is given.
#[derive(Default)]
pub(crate) struct Marks(Slots<()>);

impl Marks {
    /// Empties the set, sized for indices below `len`.
    pub(crate) fn begin(&mut self, len: usize) {
        self.0.begin(len);
    }

    /// Empties the set.
    pub(crate) fn clear(&mut self) {
        self.0.clear();
    }

    /// Adds `i`: whether it was not in the set.
    #[inline]
    pub(crate) fn insert(&mut self, i: u32) -> bool {
        self.0.set(i, ())
    }

    /// Removes `i`: whether it was in the set.
    #[inline]
    pub(crate) fn remove(&mut self, i: u32) -> bool {
        self.0.remove(i)
    }

    #[inline]
    pub(crate) fn contains(&self, i: u32) -> bool {
        self.0.contains(i)
    }
}

/// Counts per node index, emptied in constant time like [`Marks`]; an index not counted since
/// then has none (which is not a count of 0).
#[derive(Default)]
pub(crate) struct Counts(Slots<u32>);

impl Counts {
    /// Empties the counts, sized for indices below `len`.
    pub(crate) fn begin(&mut self, len: usize) {
        self.0.begin(len);
    }

    #[inline]
    pub(crate) fn get(&self, i: u32) -> Option<u32> {
        self.0.get(i)
    }

    /// Counts one more for `i`.
    #[inline]
    pub(crate) fn add(&mut self, i: u32) {
        let n = self.0.get(i).unwrap_or(0);
        self.0.set(i, n + 1);
    }

    /// Sets `i`'s count to `v`.
    #[inline]
    pub(crate) fn set(&mut self, i: u32, v: u32) {
        self.0.set(i, v);
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
    /// Limb arithmetic read as arithmetic on the words.
    Words,
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
            PassKind::Words => "words",
        }
    }
}

/// Runs `kind` at `n`, unless a rewrite of its failed a postcondition earlier in the call: the
/// pass is quarantined then, and the node's result not final.
pub(super) fn step(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    kind: PassKind,
    n: u32,
) -> Result<Step, Stop> {
    if r.quarantined_passes.contains(&kind) {
        return Ok(Step::Normal(Fin::PROVISIONAL));
    }
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
        PassKind::Words => words::step(r, cx, n),
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

/// `root` as a select on the condition its selects test most, each arm `root` with what that
/// case fixes put in (`context::sides`), when each arm is one value at every sample point:
/// what is left of a value an obfuscator mixed one condition through is a constant on either
/// side of it, which the phases fold once the condition is gone from the arm. The samples only
/// say when to split: `select(c, t, f)` is `root` whatever the arms are. (At random inputs a
/// condition like `x != y` holds every time, so the root looks like one constant and is not;
/// the arm for the other case is read at the same inputs with the condition put in.)
#[cfg(feature = "mba")]
pub(super) fn split_cases(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
) -> Result<Option<u32>, Stop> {
    let before = cx.len() as u32;
    let Some((c, t, f)) = r.build(cx, |cx| context::sides(cx, root))? else {
        return Ok(None);
    };
    // Already split on it.
    let node = cx.node(root);
    if node.op == OpCode::Select && node.a == c {
        discard(r, cx, before);
        return Ok(None);
    }
    for side in [t, f] {
        if cx.const_val(side).is_some() {
            continue;
        }
        r.sample(cx, side)?;
        let vals = &r.samples[&side];
        if vals.iter().any(|v| *v != vals[0]) {
            discard(r, cx, before);
            return Ok(None);
        }
    }
    let e = r.build(cx, |cx| cx.c_select(c, t, f))?;
    Ok((e != root).then_some(e))
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
        // A truncation between a link and its user is part of the user's fragment
        // (`trunc(a + b) + c` is one sum at the narrow width): the link is covered by the
        // question above it. Not an extension or a slice: the question above reads the link
        // through a mask or a shift, where the link's own is a sum at its width
        // (`zext<64>(s) + k` with `s` a 32-bit MBA that is a constant only modulo `2^32`).
        let (p, up) = match up {
            OpCode::Extract if cx.node(p).b == 0 => match r.chain_parent.get(&p) {
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
    // What each candidate declined contributes stays in the result (see the linear pass's
    // `step`).
    let mut declined = match mba::step(r, cx, cfg, n)? {
        Step::Normal(f) => f,
        step => return Ok(step),
    };
    // a sum whose groups of terms share no leaf, each asked alone.
    let mut part =
        |r: &mut Runner<'_, '_>, cx: &mut Context, s: u32| -> Result<Option<u32>, Stop> {
            Ok(match mba::step(r, cx, cfg, s)? {
                Step::To(e, _) => Some(e),
                Step::Normal(_) => None,
            })
        };
    match linear::by_sums(r, cx, n, &mut part)? {
        Some(Step::Normal(f)) => declined = declined.and(f),
        Some(step) => return Ok(step),
        None => {}
    }
    let mut small =
        |r: &mut Runner<'_, '_>, cx: &mut Context, s: u32| -> Result<Option<u32>, Stop> {
            Ok(match mba::step_part(r, cx, cfg, s)? {
                Step::To(e, _) => Some(e),
                Step::Normal(_) => None,
            })
        };
    match linear::by_factor(r, cx, n, &mut small)? {
        Some(Step::Normal(f)) => declined = declined.and(f),
        Some(step) => return Ok(step),
        None => {}
    }
    let mut side =
        |r: &mut Runner<'_, '_>, cx: &mut Context, s: u32| -> Result<Option<u32>, Stop> {
            Ok(match mba::step_side(r, cx, cfg, s)? {
                Step::To(e, _) => Some(e),
                Step::Normal(_) => None,
            })
        };
    match cases::by_cases(r, cx, n, &mut side)? {
        Some(Step::Normal(f)) => declined = declined.and(f),
        Some(step) => return Ok(step),
        None => {}
    }
    Ok(match linear::by_groups(r, cx, n, &mut part)? {
        Some(Step::Normal(f)) => Step::Normal(declined.and(f)),
        Some(step) => step,
        None => Step::Normal(declined),
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
    // A sum too large to ask whole is still taken apart first (see `linear::by_groups`), at
    // the top of its chain: its terms asked one at a time are the questions of the groups
    // they belong to, each a part of an identity that only the group shows.
    let sum_top = matches!(cx.node(n).op, OpCode::Add | OpCode::Sub)
        && r.chain_parent.get(&n).is_none_or(|&p| {
            !matches!(
                cx.node(p).op,
                OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Shl
            )
        });
    if !top || !(mba::asks(r, cx, cfg, n)? || sum_top) {
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

/// Whether the facts prove that every bit `b` may have set is one `a` has set (of one width),
/// so that `a − b` borrows nothing and is `a ^ b`; with what the facts of each relied on.
pub(super) fn within(
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
        let w = matches!((ka, kb), (Some([_, oa]), Some([zb, _])) if !oa & !zb & mask == 0);
        return Ok((w, fa, fb));
    }
    let (ka, fa) = known(r, cx, a)?;
    let (kb, fb) = known(r, cx, b)?;
    let w = match (ka, kb) {
        (Some(x), Some(y)) => {
            let free = crate::facts::known::bv_not(&x.known_one());
            crate::facts::known::bv_and(&free, &y.maybe_one()).is_zero()
        }
        _ => false,
    };
    Ok((w, fa, fb))
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
/// node a counted node uses is counted too, so one replaced and then used again is live again;
/// and so is a node that takes another's place, which the arena may have held before the
/// phase run, where no new node would count it.
///
/// The roots other than the active one do not change while it is processed: their part is
/// counted once per root ([`Live`]) and stands in every phase run in which none of the nodes
/// they reach was retired (a count from scratch skips retired nodes, and what only they reach).
/// Each count is a unit of pass work per node counted; a part that stands costs nothing.
pub(super) fn refresh_uses(r: &mut Runner<'_, '_>, cx: &Context) -> Result<(), Stop> {
    if !r.life.uses_on {
        r.life.live.clear();
        r.scratch.seen.begin(cx.len());
        let others = others_hold(r, cx)?;
        let mut stack: Vec<u32> = if others {
            // (Off when the other roots reach nothing: then it adds nothing.)
            r.life.live.base = r.life.live.others.nodes > 0;
            r.life
                .live_roots
                .get(r.active)
                .copied()
                .into_iter()
                .collect()
        } else {
            r.life.live_roots.clone()
        };
        while let Some(i) = stack.pop() {
            if (others && r.life.live.others.reach.contains(i))
                || !r.scratch.seen.insert(i)
                || r.life.dead.contains(i)
            {
                continue;
            }
            if let Err(e) = r.meter.charge(Counter::PassWork, 1) {
                // Nothing counted yet (`uses` is still off): keep the counted set consistent.
                r.life.live.clear();
                return Err(e.into());
            }
            for c in cx.node(i).children() {
                r.life.live.add(c);
                stack.push(c);
            }
            r.life.live.count(i);
        }
        r.life.uses_on = true;
        r.life.uses_upto = r.life.phase_start;
    }
    let len = cx.len() as u32;
    let from = r.life.uses_upto.min(len);
    r.meter.charge(Counter::PassWork, u64::from(len - from))?;
    let mut stack: Vec<u32> = (from..len)
        .rev()
        .filter(|&i| !r.life.dead.contains(i) && !r.life.live.counted(i))
        .collect();
    let arrived = std::mem::take(&mut r.life.live.arrived);
    stack.extend(
        arrived
            .iter()
            .copied()
            .filter(|&i| !r.life.dead.contains(i) && !r.life.live.counted(i)),
    );
    r.life.live.arrived = arrived;
    r.life.live.arrived.clear();
    while let Some(i) = stack.pop() {
        if !r.life.live.count(i) {
            continue;
        }
        r.life.dead.remove(i);
        r.meter.charge(Counter::PassWork, 1)?;
        for c in cx.node(i).children() {
            r.life.live.add(c);
            if !r.life.live.counted(c) {
                stack.push(c);
            }
        }
    }
    r.life.uses_upto = len;
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
///
/// A node that takes the place of another in a phase run ([`replace`](Live::replace)) is not
/// yet used by the users of the one it replaced: the walk rebuilds them later. Their uses
/// count for it meanwhile, or a node shared by several users would look like one a single
/// rewrite could free until the last of them was rebuilt.
#[derive(Default)]
pub(crate) struct Live {
    others: Others,
    base: bool,
    /// Counted nodes outside the base, and base nodes no longer counted.
    counted: Marks,
    uncounted: Marks,
    /// Changes of the use counts (signed).
    delta: Slots<i32>,
    /// Per node replaced in this phase run, the node that took its place.
    heirs: crate::hash::IdMap<u32, u32>,
    /// The nodes that took another's place since the last count (see `refresh_uses`).
    arrived: Vec<u32>,
}

impl Live {
    /// The longest chain of replacements followed.
    const MAX_HEIRS: usize = 16;

    /// Starts a phase run: [`clear`](Live::clear), and no node has taken the place of another.
    pub(crate) fn begin(&mut self) {
        self.heirs.clear();
        self.arrived.clear();
        self.clear();
    }

    /// `new` takes the place of `old`: the uses of `old` (by users not rebuilt yet) count for
    /// `new` too, now and as they are counted or stop counting. Not when the chain of
    /// replacements from `new` is long or leads back to `old`.
    pub(crate) fn replace(&mut self, old: u32, new: u32) {
        self.arrived.push(new);
        let mut at = new;
        for _ in 0..Self::MAX_HEIRS {
            if at == old {
                return;
            }
            match self.heirs.get(&at) {
                Some(&next) => at = next,
                None => {
                    let uses = self.uses(old).unwrap_or(0);
                    self.heirs.insert(old, new);
                    if uses > 0 {
                        self.change(new, uses as i32);
                    }
                    return;
                }
            }
        }
    }

    /// Empties it: nothing counted, no uses, the base off.
    pub(crate) fn clear(&mut self) {
        self.base = false;
        self.counted.clear();
        self.uncounted.clear();
        self.delta.clear();
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
        self.delta.get(i)
    }

    /// Changes the uses of `i` by `by`, and so those of the nodes that took its place.
    #[inline]
    fn change(&mut self, mut i: u32, by: i32) {
        loop {
            let d = self.delta.get(i).unwrap_or(0);
            self.delta.set(i, d + by);
            if self.heirs.is_empty() {
                return;
            }
            match self.heirs.get(&i) {
                Some(&next) => i = next,
                None => return,
            }
        }
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

/// Whether the other roots' part holds in this phase run, counting it first (a unit of pass
/// work per node) if it is for another root: no node the other roots reach was retired in the
/// run.
fn others_hold(r: &mut Runner<'_, '_>, cx: &Context) -> Result<bool, Exhausted> {
    let o = &mut r.life.live.others;
    if o.active != Some(r.active) {
        // (For no root until it is counted whole: a budget may stop the count.)
        o.active = None;
        // (Sized as they grow: often the other roots reach nothing.)
        o.reach.clear();
        o.uses.begin(0);
        o.nodes = 0;
        let mut stack: Vec<u32> = r
            .life
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
            r.meter.charge(Counter::PassWork, 1)?;
            o.nodes += 1;
            for c in cx.node(i).children() {
                o.uses.add(c);
                stack.push(c);
            }
        }
        o.active = Some(r.active);
    }
    Ok(!r.life.dead_log.iter().any(|&d| o.reach.contains(d)))
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
        r.life.uses_on,
        r.life.dead_log.len(),
        r.life.phase_start,
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
        if r.life.uses_on && r.life.live.uses(i) == Some(0) {
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
/// A constant's uses from outside the region are never counted.
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
    // A constant is counted as the region's own: whether some unrelated expression happens to
    // use the same constant says nothing about this rewrite, and would make the decision
    // depend on it (a constant rewrites nothing further, so nothing is undone by it).
    let uses = |sc: &Scratch, live: &Live, i: u32| {
        if shared && cx.node(i).op != OpCode::Const {
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
                && uses(sc, &r.life.live, z) == Some(0)
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
            if sc.dying.get(c).unwrap_or(0) >= uses(sc, &r.life.live, c).unwrap_or(u32::MAX) {
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
    // The words pass replaces a whole root by what a chain of identities gives: its rewrites
    // are compared at the verification points as an unproven rule's are (zero, all ones and
    // seeded values; `Verify::unproven_points`), and a difference there quarantines it.
    let proven = kind != PassKind::Words;
    match r.accept(cx, By::Pass(name), proven, n, e, fin.rel)? {
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

/// The most operands of a chain put in order.
pub(crate) const MAX_CHAIN: usize = 256;

/// What [`sort_chain`] found a chain's node to be.
#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) enum Chain {
    /// As `sort_chain` writes its chain.
    Sorted,
    /// Of more than [`MAX_CHAIN`] operands.
    Long,
}

/// The chain `n` of `·`, `&` or `|` over values (no constant among them) with its operands in
/// the context's canonical order, joined left to right: one node for a chain however it was
/// parenthesized and ordered, so `a·b·c − c·b·a` and `(a & b & … & g) ^ (g & … & b & a)`
/// cancel. An operand of `&` or `|` is kept once, and one beside its complement decides the
/// chain (0, or all-ones). The result is no larger than `n` unless a part of the chain has
/// another use, and nothing rewrites it back, so it replaces `n` at the same size too.
///
/// `Step::Normal` when `n` is in order already, is not a chain of three operands or more, or
/// has more than [`MAX_CHAIN`]. Both are remembered (`Runner::chains`): the chains a sorted
/// one is made of are not read again, and a chain over a long one is long.
pub(super) fn sort_chain(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    kind: PassKind,
    n: u32,
) -> Result<Step, Stop> {
    let op = cx.node(n).op;
    let bin = match op {
        OpCode::Mul => crate::ops::BinOp::Mul,
        OpCode::And => crate::ops::BinOp::And,
        OpCode::Or => crate::ops::BinOp::Or,
        _ => return Ok(Step::Normal(Fin::FINAL)),
    };
    if r.chains.contains_key(&n) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let mut operands = Vec::new();
    let mut stack = vec![n];
    while let Some(i) = stack.pop() {
        let node = cx.node(i);
        let inner = node.op == op && !cx.is_const(node.a) && !cx.is_const(node.b);
        if inner && r.chains.get(&i) != Some(&Chain::Long) {
            stack.push(node.b);
            stack.push(node.a);
        } else if inner || operands.len() == MAX_CHAIN {
            r.chains.insert(n, Chain::Long);
            r.meter.charge(Counter::PassWork, operands.len() as u64)?;
            return Ok(Step::Normal(Fin::FINAL));
        } else {
            operands.push(i);
        }
    }
    if operands.len() < 3 {
        return Ok(Step::Normal(Fin::FINAL));
    }
    r.meter.charge(Counter::PassWork, operands.len() as u64)?;
    operands.sort_by(|&a, &b| cx.order(a, b));
    // (Equal in the order is the same node.)
    let mut atoms = operands.clone();
    atoms.dedup();
    let before = cx.len() as u32;
    let w = cx.width_of(n);
    let decided = op != OpCode::Mul && {
        let mut ids = atoms.clone();
        ids.sort_unstable();
        atoms.iter().any(|&a| {
            let node = cx.node(a);
            node.op == OpCode::Not && ids.binary_search(&node.a).is_ok()
        })
    };
    let mut links = Vec::new();
    let e = r.build(cx, |cx| {
        if decided {
            return cx.mk_const(&match op {
                OpCode::And => crate::BitVec::zero(w),
                _ => crate::BitVec::ones(w),
            });
        }
        // A product keeps a repeated factor; `&` and `|` do not.
        let chain = if op == OpCode::Mul { &operands } else { &atoms };
        let mut e = chain[0];
        for &f in &chain[1..] {
            e = cx.c_bin(bin, e, f)?;
            links.push(e);
        }
        Ok(e)
    })?;
    for l in links {
        r.chains.insert(l, Chain::Sorted);
    }
    if e == n {
        return Ok(Step::Normal(Fin::FINAL));
    }
    finish_with(r, cx, kind, n, e, before, &atoms, Fin::FINAL, true)
}

/// What is live in a call: the use counts of the live DAG and how far they are counted, the
/// nodes retired, and the call's roots.
pub(crate) struct Liveness {
    /// Use counts (parent edges of live nodes) for the passes' commit rule, and the nodes whose
    /// edges they count, per phase run, computed on first need (`uses_on`).
    pub(crate) live: Live,
    pub(crate) uses_on: bool,
    /// Arena nodes whose edges `live` already counts.
    pub(crate) uses_upto: u32,
    /// The arena length when the current phase run began.
    pub(crate) phase_start: u32,
    /// Nodes replaced (or built and discarded) in the current phase run: not parents.
    pub(crate) dead: Marks,
    /// The nodes `dead` took in the current phase run, in order.
    pub(crate) dead_log: Vec<u32>,
    /// The current version of every distinct root of the call (for use counts).
    pub(crate) live_roots: Vec<u32>,
}
