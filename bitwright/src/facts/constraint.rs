//! Consumer-defined constraints: facts and predicates a caller guarantees about the values that
//! occur (a path condition, an ABI invariant, a trap known not to happen).
//!
//! A constraint restricts values; it never changes what an operator means. Every proof made under
//! a set of constraints is valid wherever those constraints hold, and the engine reports which
//! constraints each result relied on ([`Reliance`]), so a caller can tell a rewrite valid
//! everywhere from one valid only on the path whose conditions it assumed.
//!
//! Adding a constraint propagates it: backwards from the constrained expression to its operands
//! (so assuming `x + 8 <u 64` bounds `x`, and assuming `(rsp & 15) == 0` makes `rsp`'s low bits
//! known), and between comparisons of the same two expressions (assuming `x <u y` decides
//! `x <=u y` and `y == x`). Propagation is bounded (a fixed number of steps per constraint);
//! stopping early only loses precision.

use core::fmt;
use std::sync::Arc;

use super::backward::{backward, holding};
use super::{FactMap, Facts};
use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::hash::IdMap;
use crate::ops::CmpOp;
use crate::{BitVec, Width};

/// Identifies a constraint of an [`Assumptions`] set: the `k`-th one added is `k`, from 0.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ConstraintId(u32);

impl ConstraintId {
    /// The position of the constraint in its set (0 for the first one added).
    pub fn index(self) -> u32 {
        self.0
    }
}

/// The constraints a result may rely on: every constraint it relies on is included, and possibly
/// others (the set over-approximates). Constraints from the 64th on are tracked together.
///
/// A result with an empty reliance holds everywhere; one relying only on constraints that hold
/// in some scope (for example program-wide invariants, added first) holds in that scope.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
pub struct Reliance(u64);

/// The bit standing for every constraint from index 63 on.
const REST: u64 = 1 << 63;

impl Reliance {
    /// Relies on nothing.
    pub const NONE: Reliance = Reliance(0);

    pub(crate) fn of(id: ConstraintId) -> Reliance {
        Reliance(if id.0 >= 63 { REST } else { 1 << id.0 })
    }

    /// Whether the result relies on no constraint (it holds everywhere).
    pub fn is_none(self) -> bool {
        self.0 == 0
    }

    /// Whether the result may rely on constraint `id`. `false` is definite.
    pub fn may_use(self, id: ConstraintId) -> bool {
        self.0 & Reliance::of(id).0 != 0
    }

    /// Whether every constraint the result relies on was added before `id` (so the result holds
    /// wherever the constraints before `id` hold). `true` is definite.
    pub fn all_before(self, id: ConstraintId) -> bool {
        if id.0 >= 63 {
            // Constraints from 63 on are tracked together: only "none of them" is definite.
            self.0 & REST == 0
        } else {
            self.0 >> id.0 == 0
        }
    }

    /// The constraints either relies on.
    #[must_use]
    pub fn union(self, o: Reliance) -> Reliance {
        Reliance(self.0 | o.0)
    }

    /// The indices of the constraints it may rely on, below 63; and whether it may rely on some
    /// constraint from 63 on.
    pub fn indices(self) -> (impl Iterator<Item = u32>, bool) {
        let bits = self.0 & !REST;
        (
            (0..63u32).filter(move |i| bits >> i & 1 == 1),
            self.0 & REST != 0,
        )
    }
}

impl core::ops::BitOr for Reliance {
    type Output = Reliance;
    fn bitor(self, o: Reliance) -> Reliance {
        self.union(o)
    }
}

impl core::ops::BitOrAssign for Reliance {
    fn bitor_assign(&mut self, o: Reliance) {
        *self = self.union(o);
    }
}

impl fmt::Debug for Reliance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (low, rest) = self.indices();
        let mut l = f.debug_set();
        l.entries(low);
        if rest {
            l.entry(&format_args!("63.."));
        }
        l.finish()
    }
}

/// Orderings two values can have: each world is an unsigned and a signed order (`<`, `==`, `>`;
/// equal in one means equal in both). A set of worlds is a mask of these bits.
pub(crate) mod worlds {
    use crate::ops::CmpOp;

    const LT_LT: u8 = 1;
    const LT_GT: u8 = 2;
    const GT_LT: u8 = 4;
    const GT_GT: u8 = 8;
    const EQ: u8 = 16;
    pub(crate) const ALL: u8 = 31;

    /// The worlds where `op(a, b)` holds.
    pub(crate) const fn holding(op: CmpOp) -> u8 {
        match op {
            CmpOp::Eq => EQ,
            CmpOp::Ne => LT_LT | LT_GT | GT_LT | GT_GT,
            CmpOp::Ult => LT_LT | LT_GT,
            CmpOp::Ule => LT_LT | LT_GT | EQ,
            CmpOp::Slt => LT_LT | GT_LT,
            CmpOp::Sle => LT_LT | GT_LT | EQ,
        }
    }

    /// The same worlds seen from `(b, a)`.
    pub(crate) const fn swap(m: u8) -> u8 {
        (m & EQ) | ((m & LT_LT) << 3) | ((m & GT_GT) >> 3) | ((m & LT_GT) << 1) | ((m & GT_LT) >> 1)
    }

    /// `op(a, b)` in every world of `m`, if it has one value in all of them.
    pub(crate) const fn decide(m: u8, op: CmpOp) -> Option<bool> {
        let h = holding(op);
        if m & !h == 0 {
            Some(true)
        } else if m & h == 0 {
            Some(false)
        } else {
            None
        }
    }
}

/// An assumed ordering of two expressions (`a` has the lower index): the worlds left, and the
/// constraints that removed the others.
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct Relation {
    pub(crate) a: Expr,
    pub(crate) b: Expr,
    pub(crate) worlds: u8,
    pub(crate) rel: Reliance,
}

/// The contents of an [`Assumptions`] set.
#[derive(Clone, Debug, Default)]
pub(crate) struct Store {
    /// The constraints as added: an expression and facts its value satisfies.
    pub(crate) seeds: Vec<(Expr, Facts)>,
    /// Facts known per expression (the seeds and what propagation derived from them).
    pub(crate) entries: Vec<(Expr, Facts, Reliance)>,
    /// Assumed orderings between two classes of equal expressions (by their representatives),
    /// sorted.
    pub(crate) relations: Vec<Relation>,
    /// Expressions assumed equal to another: each member with its class representative (the
    /// member of lowest index) and the constraints the equality rests on, sorted.
    pub(crate) classes: Vec<(Expr, Expr, Reliance)>,
    /// Set when the constraints contradict each other, with the ones that do.
    pub(crate) infeasible: Option<Reliance>,
    /// Set when propagation stopped at its step bound (some consequences are not derived).
    pub(crate) truncated: bool,
    /// The same, by node index (derived from the fields above).
    pub(crate) env: Env,
}

impl Store {
    /// Rewrites the sorted lists of orderings and classes from the index.
    fn publish(&mut self, cx: &Context) {
        let mut relations: Vec<Relation> = self
            .env
            .relations
            .iter()
            .map(|(&(a, b), &(worlds, rel))| Relation {
                a: cx.handle(a),
                b: cx.handle(b),
                worlds,
                rel,
            })
            .collect();
        relations.sort_unstable_by_key(|r| (r.a.index(), r.b.index()));
        self.relations = relations;
        let mut classes: Vec<(Expr, Expr, Reliance)> = self
            .env
            .root
            .iter()
            .map(|(&m, &(r, rel))| (cx.handle(m), cx.handle(r), rel))
            .collect();
        classes.sort_unstable_by_key(|c| c.0.index());
        self.classes = classes;
    }
}

impl PartialEq for Store {
    fn eq(&self, o: &Store) -> bool {
        // `env` is derived from the rest.
        self.seeds == o.seeds
            && self.entries == o.entries
            && self.relations == o.relations
            && self.classes == o.classes
            && self.infeasible == o.infeasible
            && self.truncated == o.truncated
    }
}

/// Constraints assumed to hold, layered over the facts the context derives: facts about
/// expressions ([`assume`](Self::assume)) and 1-bit predicates assumed true or false
/// ([`assume_true`](Self::assume_true), [`assume_false`](Self::assume_false)).
///
/// Cloning is cheap (the contents are shared until one of the clones changes), so a set of
/// invariants can be built once and extended per path: constraints keep their ids in the clone.
/// Conflicting constraints make the set infeasible. A set belongs to the context whose
/// expressions it mentions.
#[derive(Clone, Default)]
pub struct Assumptions {
    pub(crate) store: Arc<Store>,
}

impl PartialEq for Assumptions {
    fn eq(&self, o: &Assumptions) -> bool {
        Arc::ptr_eq(&self.store, &o.store) || *self.store == *o.store
    }
}

impl fmt::Debug for Assumptions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Assumptions")
            .field("constraints", &self.store.seeds)
            .field("infeasible", &self.store.infeasible)
            .finish_non_exhaustive()
    }
}

/// Steps (operand refinements examined) per constraint added.
const STEPS: u32 = 4096;
/// Rounds of re-propagating everything known after a constraint changed something.
const ROUNDS: u32 = 3;

impl Assumptions {
    /// No assumptions.
    pub fn new() -> Self {
        Self::default()
    }

    /// Assumes that the value of `e` satisfies `facts`, and propagates it. The widths must
    /// match; a contradiction marks the set infeasible.
    pub fn assume(
        &mut self,
        cx: &mut Context,
        e: Expr,
        facts: Facts,
    ) -> Result<ConstraintId, Error> {
        let w = cx.width(e)?;
        if facts.width() != w {
            return Err(crate::WidthError::Mismatch {
                left: w.bits(),
                right: facts.width().bits(),
            }
            .into());
        }
        self.add(cx, e, facts)
    }

    /// Assumes that the 1-bit predicate `p` holds (for example a branch condition on the path
    /// taken, or `(rsp & 15) == 0`), and propagates it.
    pub fn assume_true(&mut self, cx: &mut Context, p: Expr) -> Result<ConstraintId, Error> {
        self.predicate(cx, p, true)
    }

    /// Assumes that the 1-bit predicate `p` does not hold (for example a branch condition on the
    /// path not taken, or a [trap guard](crate::traps) on a path that does not fault).
    pub fn assume_false(&mut self, cx: &mut Context, p: Expr) -> Result<ConstraintId, Error> {
        self.predicate(cx, p, false)
    }

    fn predicate(&mut self, cx: &mut Context, p: Expr, v: bool) -> Result<ConstraintId, Error> {
        let w = cx.width(p)?;
        if w != Width::W1 {
            return Err(crate::WidthError::Mismatch {
                left: w.bits(),
                right: 1,
            }
            .into());
        }
        self.add(cx, p, Facts::constant(&BitVec::from_bool(v)))
    }

    fn add(&mut self, cx: &mut Context, e: Expr, facts: Facts) -> Result<ConstraintId, Error> {
        let n = cx.id(e)?;
        self.check_context(cx)?;
        let id = self.next_id();
        // The context's fact overlay may hold this very set as its key: drop that, so the set
        // is changed in place instead of copied.
        cx.facts.forget(self);
        let store = Arc::make_mut(&mut self.store);
        store.seeds.push((e, facts));
        if store.infeasible.is_none() {
            let mut p = Propagation {
                overlay: FactMap::default(),
                changed: Vec::new(),
                steps: STEPS,
                store,
                work: Vec::new(),
            };
            p.work.push((n, facts, Reliance::of(id)));
            if p.drain(cx)? {
                for _ in 0..ROUNDS {
                    if !p.sweep(cx)? {
                        break;
                    }
                }
            }
            store.publish(cx);
        }
        Ok(id)
    }

    /// Checks (best effort, like every handle check) that the set belongs to `cx`.
    pub(crate) fn check_context(&self, cx: &Context) -> Result<(), Error> {
        if let Some((e, _)) = self.store.seeds.first() {
            cx.id(*e)?;
        }
        Ok(())
    }

    /// Whether the constraints contradict each other.
    pub fn is_infeasible(&self) -> bool {
        self.store.infeasible.is_some()
    }

    /// The constraints that contradict each other, if they do.
    pub fn conflict(&self) -> Option<Reliance> {
        self.store.infeasible
    }

    /// Whether there are no constraints.
    pub fn is_empty(&self) -> bool {
        self.store.seeds.is_empty()
    }

    /// The number of constraints.
    pub fn len(&self) -> usize {
        self.store.seeds.len()
    }

    /// The id the next constraint added will get.
    pub fn next_id(&self) -> ConstraintId {
        ConstraintId(u32::try_from(self.store.seeds.len()).unwrap_or(u32::MAX))
    }

    /// Constraint `id`: the expression and the facts assumed about it (a predicate assumed true
    /// is its expression with the facts of the constant 1).
    pub fn constraint(&self, id: ConstraintId) -> Option<(Expr, Facts)> {
        self.store.seeds.get(id.0 as usize).copied()
    }

    /// The constraints in order.
    pub fn constraints(&self) -> impl Iterator<Item = (ConstraintId, Expr, Facts)> + '_ {
        self.store
            .seeds
            .iter()
            .enumerate()
            .map(|(i, (e, f))| (ConstraintId(i as u32), *e, *f))
    }

    /// Whether propagation stopped at its bound for some constraint, so some consequences were
    /// not derived (results stay sound, just less precise).
    pub fn is_truncated(&self) -> bool {
        self.store.truncated
    }
}

/// The assumptions in the form the fact overlay reads: assumed facts and orderings by node.
#[derive(Clone, Debug)]
pub(crate) struct Env {
    pub(crate) assumed: IdMap<u32, (Facts, Reliance)>,
    /// Orderings, keyed by `(lower index, higher index)`.
    pub(crate) relations: IdMap<(u32, u32), (u8, Reliance)>,
    /// The lowest node index any assumption mentions (nothing below it can depend on one).
    pub(crate) min: u32,
    pub(crate) infeasible: Option<Reliance>,
    /// Positions in `Store::entries`.
    entry_slot: IdMap<u32, usize>,
    /// Equality classes: each member (never a representative) with its representative and the
    /// constraints the equality rests on.
    root: IdMap<u32, (u32, Reliance)>,
    /// The members of each class, by representative.
    members: IdMap<u32, Vec<u32>>,
}

impl Default for Env {
    fn default() -> Self {
        Env {
            assumed: IdMap::default(),
            relations: IdMap::default(),
            entry_slot: IdMap::default(),
            root: IdMap::default(),
            members: IdMap::default(),
            min: u32::MAX,
            infeasible: None,
        }
    }
}

impl Env {
    pub(crate) fn is_empty(&self) -> bool {
        self.assumed.is_empty() && self.relations.is_empty()
    }

    /// The representative of `a`'s equality class, and what the equality rests on.
    pub(crate) fn find(&self, a: u32) -> (u32, Reliance) {
        self.root.get(&a).copied().unwrap_or((a, Reliance::NONE))
    }

    /// The orderings assumed between `a` and `b`, seen from `(a, b)`.
    pub(crate) fn relation(&self, a: u32, b: u32) -> Option<(u8, Reliance)> {
        let ((ra, xa), (rb, xb)) = (self.find(a), self.find(b));
        if ra == rb {
            return (a != b).then_some((worlds::holding(CmpOp::Eq), xa | xb));
        }
        let (m, r) = if ra < rb {
            *self.relations.get(&(ra, rb))?
        } else {
            let (m, r) = *self.relations.get(&(rb, ra))?;
            (worlds::swap(m), r)
        };
        Some((m, r | xa | xb))
    }
}

/// Propagation of one new constraint.
struct Propagation<'p> {
    /// Facts under the assumptions so far (the part above a change is dropped whenever one
    /// happens).
    overlay: FactMap,
    /// Nodes whose facts or orderings changed since the last sweep.
    changed: Vec<u32>,
    steps: u32,
    store: &'p mut Store,
    /// Pending requirements: node, facts it must satisfy, and what they rely on.
    work: Vec<(u32, Facts, Reliance)>,
}

impl Propagation<'_> {
    /// Facts of `n` under the assumptions so far; `None` if they are infeasible.
    fn current(&mut self, cx: &mut Context, n: u32) -> Option<(Facts, Reliance)> {
        if let Some(v) = cx.const_val(n) {
            return Some((Facts::constant(&v), Reliance::NONE));
        }
        let cap = cx.config().fact_work;
        match cx.overlay_facts(&self.store.env, &mut self.overlay, n, cap) {
            Ok(f) => Some(f),
            Err(rel) => {
                self.infeasible(rel);
                None
            }
        }
    }

    fn infeasible(&mut self, rel: Reliance) {
        let prev = self.store.infeasible.unwrap_or(Reliance::NONE);
        self.store.infeasible = Some(prev | rel);
        self.store.env.infeasible = self.store.infeasible;
        self.work.clear();
    }

    /// Processes pending requirements; whether anything was learned.
    fn drain(&mut self, cx: &mut Context) -> Result<bool, Error> {
        let mut changed = false;
        while let Some((n, req, rel)) = self.work.pop() {
            if self.steps == 0 {
                self.store.truncated = true;
                self.work.clear();
                break;
            }
            self.steps -= 1;
            let Some((cur, cur_rel)) = self.current(cx, n) else {
                self.infeasible(rel);
                return Ok(changed);
            };
            let Some(new) = cur.meet(&req) else {
                self.infeasible(rel | cur_rel);
                return Ok(true);
            };
            if new == cur {
                continue;
            }
            let rel = rel | cur_rel;
            self.record(cx, n, new, rel);
            changed = true;
            if !self.backward(cx, n, new, rel)? {
                return Ok(true);
            }
        }
        Ok(changed)
    }

    /// Stores refined facts for `n`.
    fn record(&mut self, cx: &Context, n: u32, f: Facts, rel: Reliance) {
        let e = cx.handle(n);
        match self.store.env.entry_slot.get(&n) {
            Some(&k) => self.store.entries[k] = (e, f, rel),
            None => {
                self.store
                    .env
                    .entry_slot
                    .insert(n, self.store.entries.len());
                self.store.entries.push((e, f, rel));
            }
        }
        self.store.env.assumed.insert(n, (f, rel));
        self.store.env.min = self.store.env.min.min(n);
        self.invalidate_from(n);
        self.changed.push(n);
    }

    /// Drops the cached facts that can depend on node `n`: those of `n` and above (operands
    /// always have lower indices than their users).
    fn invalidate_from(&mut self, n: u32) {
        self.overlay.retain_below(n);
    }

    /// Queues what `n`'s operands must satisfy given `r` about `n`, and records an assumed
    /// comparison. `false` if that is infeasible.
    fn backward(
        &mut self,
        cx: &mut Context,
        n: u32,
        r: Facts,
        rel: Reliance,
    ) -> Result<bool, Error> {
        let node = cx.node(n);
        let arity = node.op.arity();
        if arity == 0 {
            return Ok(true);
        }
        let kids: Vec<u32> = node.children().collect();
        let mut facts = [Facts::top(Width::W1); 3];
        let mut all = rel;
        for (k, &c) in kids.iter().enumerate() {
            let Some((f, r)) = self.current(cx, c) else {
                self.infeasible(all);
                return Ok(false);
            };
            facts[k] = f;
            all |= r;
        }
        let op = cx.top_of(n);
        let refs: [&Facts; 3] = [&facts[0], &facts[1], &facts[2]];
        let Some(out) = backward(&op, &r, &refs[..arity]) else {
            self.infeasible(all);
            return Ok(false);
        };
        if let (Some(cmp), Some(v)) = (node.op.as_cmp(), r.as_constant())
            && !self.relate(cmp, kids[0], kids[1], !v.is_zero(), all)
        {
            return Ok(false);
        }
        for (k, f) in out.iter().enumerate().take(arity) {
            if let Some(f) = f {
                self.work.push((kids[k], *f, all));
            }
        }
        Ok(true)
    }

    /// Records that `op(a, b)` has the value `v`. `false` if that is infeasible.
    fn relate(&mut self, op: CmpOp, a: u32, b: u32, v: bool, rel: Reliance) -> bool {
        let (held, swap) = holding(op, v);
        let (a, b) = if swap { (b, a) } else { (a, b) };
        let env = &self.store.env;
        let ((ra, xa), (rb, xb)) = (env.find(a), env.find(b));
        let rel = rel | xa | xb;
        let mut m = worlds::holding(held);
        if ra == rb {
            if m & worlds::holding(CmpOp::Eq) == 0 {
                self.infeasible(rel);
                return false;
            }
            return true;
        }
        let (lo, hi) = if ra < rb {
            (ra, rb)
        } else {
            m = worlds::swap(m);
            (rb, ra)
        };
        self.store.env.min = self.store.env.min.min(a.min(b));
        self.narrow(lo, hi, m, rel)
    }

    /// Narrows the orderings between the classes `lo < hi` to `m`, merging them if only
    /// equality is left. `false` if nothing is left.
    fn narrow(&mut self, lo: u32, hi: u32, m: u8, rel: Reliance) -> bool {
        let (old, old_rel) = self
            .store
            .env
            .relations
            .get(&(lo, hi))
            .copied()
            .unwrap_or((worlds::ALL, Reliance::NONE));
        let new = old & m;
        if new == 0 {
            self.infeasible(rel | old_rel);
            return false;
        }
        if new == old {
            return true;
        }
        let rel = rel | old_rel;
        // Comparisons over the two classes change: their members all have indices at least
        // their representatives'.
        self.invalidate_from(lo.min(hi));
        self.mark_classes(lo, hi);
        if new == worlds::holding(CmpOp::Eq) {
            self.store.env.relations.remove(&(lo, hi));
            return self.merge(lo, hi, rel);
        }
        self.store.env.relations.insert((lo, hi), (new, rel));
        true
    }

    /// Records every member of the classes of `a` and `b` as changed (their comparisons are).
    fn mark_classes(&mut self, a: u32, b: u32) {
        let env = &self.store.env;
        for r in [a, b] {
            let (rep, _) = env.find(r);
            self.changed.push(rep);
            if let Some(ms) = env.members.get(&rep) {
                self.changed.extend(ms.iter().copied());
            }
        }
    }

    /// Merges the class of `hi` into the class of `lo` (both representatives), because they
    /// are equal by `rel`. `false` if that is infeasible.
    fn merge(&mut self, lo: u32, hi: u32, rel: Reliance) -> bool {
        let env = &mut self.store.env;
        let mut moved = env.members.remove(&hi).unwrap_or_default();
        moved.push(hi);
        for &x in &moved {
            let (_, xr) = env.find(x);
            env.root.insert(x, (lo, xr | rel));
        }
        env.members.entry(lo).or_default().extend(moved);
        // Orderings with `hi` become orderings with `lo`.
        let mut rekey: Vec<((u32, u32), (u8, Reliance))> = env
            .relations
            .iter()
            .filter(|((a, b), _)| *a == hi || *b == hi)
            .map(|(&k, &v)| (k, v))
            .collect();
        rekey.sort_unstable_by_key(|&(k, _)| k);
        for &(k, _) in &rekey {
            env.relations.remove(&k);
        }
        for ((a, b), (m, r)) in rekey {
            // Seen from (hi, other) after the swap below. A merge made by an earlier iteration
            // may have moved either class again, so both sides are looked up afresh.
            let (other, m) = if a == hi {
                (b, m)
            } else {
                (a, worlds::swap(m))
            };
            let env = &self.store.env;
            let ((x, xr), (y, yr)) = (env.find(hi), env.find(other));
            let rel = r | rel | xr | yr;
            let ok = if x == y {
                m & worlds::holding(CmpOp::Eq) != 0 || {
                    self.infeasible(rel);
                    false
                }
            } else if x < y {
                self.narrow(x, y, m, rel)
            } else {
                self.narrow(y, x, worlds::swap(m), rel)
            };
            if !ok {
                return false;
            }
        }
        true
    }

    /// Re-propagates from the recorded facts a change since the last sweep can reach (an entry
    /// whose operands have a changed node below them); whether anything new was learned. Each
    /// entry revisited costs a step.
    fn sweep(&mut self, cx: &mut Context) -> Result<bool, Error> {
        let changed = core::mem::take(&mut self.changed);
        let Some(&lo) = changed.iter().min() else {
            return Ok(false);
        };
        let hit: IdMap<u32, ()> = changed.iter().map(|&c| (c, ())).collect();
        // Whether a node has a changed node at or below it (memoized; only nodes at or above
        // `lo` can).
        let mut reach: IdMap<u32, bool> = IdMap::default();
        let mut reaches = |cx: &Context, n: u32| -> bool {
            let mut stack = vec![(n, false)];
            while let Some((i, expanded)) = stack.pop() {
                if reach.contains_key(&i) {
                    continue;
                }
                if i < lo || hit.contains_key(&i) {
                    reach.insert(i, i >= lo);
                    continue;
                }
                let node = cx.node(i);
                if !expanded {
                    stack.push((i, true));
                    stack.extend(node.children().map(|c| (c, false)));
                    continue;
                }
                let r = node.children().any(|c| reach.get(&c) == Some(&true));
                reach.insert(i, r);
            }
            reach[&n]
        };
        let mut learned = false;
        let entries: Vec<Expr> = self.store.entries.iter().map(|(e, _, _)| *e).collect();
        for e in entries {
            if self.store.infeasible.is_some() {
                break;
            }
            if self.steps == 0 {
                self.store.truncated = true;
                break;
            }
            let n = cx.id(e)?;
            if n < lo || !cx.node(n).children().any(|c| reaches(cx, c)) {
                continue;
            }
            self.steps -= 1;
            let Some((f, rel)) = self.current(cx, n) else {
                return Ok(true);
            };
            if !self.backward(cx, n, f, rel)? {
                return Ok(true);
            }
            learned |= self.drain(cx)?;
        }
        Ok(learned)
    }
}
