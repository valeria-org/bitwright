//! The MBA phase: lowering, the solver, the evidence gate, lifting (see [`crate::mba`]).

use super::{Fin, PassKind, Runner, Step, Stop, discard, finish, shrinks};
use crate::engine::Exhausted;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::combine;
use crate::mba::certify;
use crate::mba::{
    Bindings, CacheEntry, CacheKey, Claim, LOWERING_VERSION, MOp, MbaAnswer, MbaConfig, MbaExpr,
    Reading, Refusal, Verdict, lift_id, lower_id, lower_id_reading, shared_nodes,
};
use crate::{BinOp, UnOp};

/// Points for the always-on refutation check and for trusted sampling.
const SAMPLE_POINTS: u32 = certify::SAMPLE_POINTS as u32;

fn mixed_op(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::Neg
            | OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Not
    )
}

/// Charges `evals` evaluations of both sides (their node counts) as pass work.
fn charge(r: &mut Runner<'_, '_>, a: &MbaExpr, b: &MbaExpr, evals: u64) -> Result<(), Stop> {
    let per = (a.nodes().len() + b.nodes().len()) as u64;
    r.meter
        .charge(Counter::PassWork, per.saturating_mul(evals))
        .map_err(Stop::Exhausted)
}

/// Whether `a` and `b` agree at the refutation sample: zero, all-ones, one and the signed
/// minimum, the constants of both sides and their neighbours, single bit positions, and seeded
/// random points (see [`certify::sample_points`]). A filter, never evidence on its own.
fn sampled(r: &mut Runner<'_, '_>, a: &MbaExpr, b: &MbaExpr, seed: u64) -> Result<bool, Stop> {
    charge(r, a, b, u64::from(SAMPLE_POINTS))?;
    let points = certify::sample_points(a.vars(), &[a, b], seed);
    Ok(certify::refute(a, b, &points).is_none())
}

/// Pass work as a certificate's meter, at most `share` of it.
struct Gate<'x, 'r, 'a> {
    r: &'x mut Runner<'r, 'a>,
    share: u64,
}

impl<'x, 'r, 'a> Gate<'x, 'r, 'a> {
    /// A meter for the certificate of `a == b`: at most [`GATE_SHARE`] of the call's pass
    /// work, or what a direct test of the pair costs (twice: with its casts taken out and
    /// without) where that is more.
    fn new(r: &'x mut Runner<'r, 'a>, a: &MbaExpr, b: &MbaExpr) -> Self {
        let limit = r.meter.limit.pass_work;
        let direct = certify::direct_cost(a, b).unwrap_or(0).saturating_mul(2);
        let share = (limit / GATE_SHARE).max(GATE_SHARE_MIN).max(direct);
        Gate { r, share }
    }
}

/// One answer's certificate spends at most this fraction of the call's pass work (and at least
/// [`GATE_SHARE_MIN`] units), unless a direct test, which decides when it runs, costs more.
/// Without a share one answer the tests cannot decide took the whole call: a compositional
/// test over two variables and 112 nodes spent 7.5M of a call's 8.4M units, undecided, and the
/// phases after it had none left. A compositional proof can need much of a call (a sparse test
/// on a skeleton over three 32-bit variables, 20M of 67M units), so the share is half.
const GATE_SHARE: u64 = 2;

/// See [`GATE_SHARE`].
const GATE_SHARE_MIN: u64 = 1 << 20;

impl certify::Meter for Gate<'_, '_, '_> {
    type Err = Stop;
    fn left(&self) -> u64 {
        self.r.meter.left_in(|b| b.pass_work).min(self.share)
    }
    fn charge(&mut self, units: u64) -> Result<(), Stop> {
        self.share = self.share.saturating_sub(units);
        self.r
            .meter
            .charge(Counter::PassWork, units)
            .map_err(Stop::Exhausted)
    }
}

/// bitwright's own exact evidence about `a == b`: the cheapest certificate that applies (the
/// corner signature, single bit positions, sparse points for degree `d`, the pure-polynomial
/// grid, exhaustive evaluation; equal polynomials over symbols first where that test would
/// take far longer), over abstracted atoms when a side leaves the polynomial fragment. Charged
/// as pass work, a block at a time, so a budget or deadline can stop it; a certificate larger
/// than what is left is not started (reported as over budget).
fn exact(r: &mut Runner<'_, '_>, a: &MbaExpr, b: &MbaExpr) -> Result<certify::Report, Stop> {
    let report = certify::prove(a, b, &mut Gate::new(r, a, b))?;
    count(r).certificates.record(&report);
    Ok(report)
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::MbaStats {
    &mut r.stats.mba
}

/// Whether the MBA phase asks the question at `n`: its operator is one it asks at and its
/// fragment is one it lowers (within the limits); remembered for the phase run. A link of a
/// chain below `n` is then not asked (see `pass::mba_step`).
pub(super) fn asks(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    cfg: &MbaConfig,
    n: u32,
) -> Result<bool, Stop> {
    if let Some(&a) = r.asks.get(&n) {
        return Ok(a);
    }
    let poly = r.inner.mba.solver.polynomial_fragments();
    let op = cx.node(n).op;
    let qualifies = |op: OpCode| mixed_op(op) || (poly && op == OpCode::Shl);
    let a = if qualifies(op) {
        match crate::mba::fits_nodes(cx, n, &cfg.limits) {
            Ok(order) => {
                r.meter.charge(Counter::PassWork, order.len() as u64)?;
                // A fragment within the limits: so is the fragment of every node inside it
                // (a part of it), which is not scanned again when the walk reaches it (along
                // a chain of n sums that was n scans of n links).
                for &i in &order {
                    if i != n && qualifies(cx.node(i).op) {
                        r.asks.entry(i).or_insert(true);
                    }
                }
                true
            }
            Err(_) => false,
        }
    } else {
        false
    };
    r.asks.insert(n, a);
    Ok(a)
}

/// opaque constants. Obfuscators hide constants (a dispatch target, a key, a hash
/// multiplier) as MBA over values that cancel, often values the code never wrote, and build
/// later constants from earlier ones: a hash of a hidden value, every round a hidden
/// multiplier. The normal form sees such a chain only whole, and a certificate over the whole
/// takes a value read through a right shift or a high byte for an independent atom, so neither
/// decides it; the phases before the MBA phase spend their work on the noise.
///
/// So before the first phase, one sweep over the DAG below `root`, operands first: the
/// engine's verification samples (each node evaluated once per call) name constant and
/// two-valued candidates. A node whose operands are all constants is that value (a function of
/// them). Any other constant is taken only when bitwright's exact certificate proves its
/// fragment, with the constants found below it written as constants, equal to the value.
/// Agreement by chance costs one certificate, never an answer. A varying block is reconstructed
/// as a select only after each side is separately proved constant. The DAG is rebuilt once over
/// every proved result.
///
/// A node that varies is also an MBA block over noise when it is a sum (the obfuscator writes
/// `t ^ k`, or `t` itself beside noise that cancels, as `Σ cᵢ·fᵢ(t, n)`) over a subterm `t`
/// that is no atom to the solver (a rotate, a cast): it is asked with its most shared subterm
/// cut off as one atom ([`sweep_cut`]), and replaced by the answer before the nodes above it are
/// read. The constants above then take few readings.
pub(super) fn sweep(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    root: u32,
) -> Result<u32, Stop> {
    sweep_inner(r, cx, cfg, root, true)
}

/// [`sweep`], optionally reconstructing piecewise constants. A case side disables that recursion:
/// the selected condition is gone, and its ordinary opaque-constant sweep is the useful part.
fn sweep_inner(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    root: u32,
    fold_cases: bool,
) -> Result<u32, Stop> {
    // The DAG below `root`, operands first.
    let mut order: Vec<u32> = Vec::new();
    let mut seen: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if expanded {
            order.push(i);
            continue;
        }
        if seen.insert(i, ()).is_some() {
            continue;
        }
        stack.push((i, true));
        for c in cx.node(i).children() {
            stack.push((c, false));
        }
    }
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    r.sample(cx, root)?;
    // links of a chain of sums, every user of which is a sum too: a noise block is
    // asked about only at the top of its chain (see `sweep_cut`).
    let mut links: crate::hash::IdMap<u32, bool> = crate::hash::IdMap::default();
    for &i in &order {
        let additive = matches!(cx.node(i).op, OpCode::Add | OpCode::Sub | OpCode::Neg);
        for c in cx.node(i).children() {
            let all = links.entry(c).or_insert(true);
            *all &= additive;
        }
    }
    // Each node rebuilt over its operands' results (the constructors fold what constants make
    // trivial: `t & 0`, a product with zero), then asked about.
    let mut to: crate::hash::IdMap<u32, u32> = crate::hash::IdMap::default();
    let mut failures = 0usize;
    // A varying noise block that has one value on each side of a selector is reconstructed as
    // that selector after both sides are proved constant. Keep this narrow: the sweep already
    // visits every node, while a side proof asks several readings.
    let mut case_attempts = 0usize;
    // The varying nodes met so far by their samples, and the related pairs no proof was found
    // for (see `Classes`).
    let mut classes = Classes::default();
    let mut unrelated = 0usize;
    // the run's budget ending in a question keeps what the sweep proved before it;
    // the nodes left are rebuilt over those results, not asked about.
    let mut spent = false;
    macro_rules! asked {
        ($l:lifetime, $e:expr) => {
            match $e {
                Ok(v) => v,
                Err(Stop::Exhausted(_)) => {
                    spent = true;
                    continue $l;
                }
                Err(e) => return Err(e),
            }
        };
    }
    // The node examined last, recorded in `r.swept` once the next one begins (unless the
    // budget ended while it was asked about, which left it unexamined).
    let mut pending: Option<u32> = None;
    'nodes: for &i in &order {
        if let Some(p) = pending.take()
            && !spent
        {
            r.swept.insert(p, to.get(&p).copied().unwrap_or(p));
        }
        // Examined by an earlier sweep of this call (of another root, or of a case's other
        // side): its result is equal to it, and asking again finds what that sweep found.
        if let Some(&done) = r.swept.get(&i) {
            to.insert(i, done);
            if done == i {
                classes.note(&r.samples[&i], i);
            }
            continue;
        }
        let node = cx.node(i);
        let mut kids = [0u32; 3];
        let mut changed = false;
        for (k, c) in node.children().enumerate() {
            kids[k] = to.get(&c).copied().unwrap_or(c);
            changed |= kids[k] != c;
        }
        let cur = if changed {
            r.build(cx, |cx| cx.rebuild(i, kids))?
        } else {
            i
        };
        to.insert(i, cur);
        if spent || cx.const_val(cur).is_some() {
            continue;
        }
        // A leaf is never taken (a symbol's samples follow what the host declared of it), nor
        // an extension operator (it may not be a function of its operands alone).
        if node.children().next().is_none() || node.op.as_ext().is_some() {
            if cur == i {
                classes.note(&r.samples[&i], i);
            }
            continue;
        }
        pending = Some(i);
        let vals = &r.samples[&i];
        let k = vals[0];
        if vals.iter().any(|v| *v != k) {
            // A node the samples relate to one met before it (see `related`).
            let found = match unrelated < SWEEP_UNRELATED {
                true => classes.find(vals),
                false => Vec::new(),
            };
            for (rep, relation, d) in found {
                let rep = to.get(&rep).copied().unwrap_or(rep);
                match asked!('nodes, related(r, cx, cfg, cur, rep, relation, &d)) {
                    Related::Proved(e) => {
                        to.insert(i, e);
                        continue 'nodes;
                    }
                    Related::Written => {}
                    Related::Open => {
                        unrelated += 1;
                        break;
                    }
                }
            }
            classes.note(&r.samples[&i], i);
            let vals = &r.samples[&i];
            let top = !links.get(&i).copied().unwrap_or(false);
            let mut rewritten = None;
            if top
                && fold_cases
                && cfg.known_atoms
                && case_attempts < SWEEP_CASE_BLOCKS
                && exactly_two(vals)
            {
                rewritten = asked!(
                    'nodes,
                    cases_fold(r, cx, cfg, cur, &mut case_attempts)
                );
            }
            if rewritten.is_none() && top {
                rewritten = asked!('nodes, sweep_cut(r, cx, cfg, cur));
            }
            if let Some(e) = rewritten {
                to.insert(i, e);
            }
            continue;
        }
        let op = cx.node(cur).op;
        let all_constant = cx.node(cur).children().all(|c| cx.const_val(c).is_some());
        let mixed = mixed_op(op) || op == OpCode::Shl;
        // a one-bit node of any operator (an opaque predicate: one bit of an MBA
        // block, a compare) is taken too, for the known bits and the enumeration only. A masked
        // dispatch selector can pick an arm by `select(extract<13, 1>(…), a, b)`, the bit 1 over
        // 13 bits of one word.
        let predicate = cx.width_of(cur).bits() == 1;
        if !all_constant && (!(mixed || predicate) || failures >= SWEEP_FAILURES) {
            continue;
        }
        // Over constants alone it is that value. Otherwise its fragment is read several ways:
        // whole; semi-linear, semi-linear over bitwise functions of atoms, linear, and
        // semi-linear with a subterm many of its nodes read cut off as one atom (every other
        // subterm an independent atom, so an identity of a reading holds for the node). The cheapest first by the test it takes
        // (`2^t` corners for a linear reading, else `64·(2^t − 1)` single-bit points, times its
        // nodes), and none over a certificate's share of the work, so one large question does
        // not starve the others. A refutation decides only for the whole fragment: the other
        // readings free more atoms.
        let mut decided = all_constant;
        let mut refuted = false;
        // a node whose bits are all known is that value, which no reading needs
        // proving (`~(x & k) >>u 42` over a 32-bit `x` keeps only `k`'s bits).
        if !decided
            && let (Some(kb), _) = asked!('nodes, super::known(r, cx, cur))
            && kb.known().is_ones()
            && kb.known_one() == k
        {
            decided = true;
            count(r).opaque_known += 1;
        }
        // the candidate with each operand taken on the bits its users read, and
        // folded where those are known (the half of a rotate a shift keeps); its readings are of
        // what is left, and a few bits of symbols left are enumerated.
        let mut subject = cur;
        if !decided {
            subject = asked!(
                'nodes,
                super::demanded::reduced(r, cx, cur, SWEEP_DEMAND_VISITS)
            );
            if let Some(v) = cx.const_val(subject) {
                if v == k {
                    decided = true;
                    count(r).opaque_known += 1;
                } else {
                    refuted = true;
                }
            } else if let Some(holds) = asked!('nodes, exhaustive(r, cx, subject, &k)) {
                if holds {
                    decided = true;
                    count(r).opaque_exhausted += 1;
                } else {
                    refuted = true;
                }
            }
        }
        if !decided && !refuted && mixed {
            let seen;
            (decided, refuted, seen) = asked!('nodes, readings_prove(r, cx, cfg, subject, &k));
            // The candidate as it is written, where the reduced one was not decided: taking
            // each operand on the bits its user reads writes one value read under several
            // masks once per mask, each a variable of its own, and what the terms cancel
            // through (the one value they all read) is gone.
            if !decided && !refuted && subject != cur {
                let again = asked!('nodes, readings_prove(r, cx, cfg, cur, &k));
                decided = again.0;
            }
            // the root, a constant some reading's free atoms refute, one case of
            // the condition it tests at a time (see `cases_prove`). The root only: inner
            // candidates are what the readings fold, and splitting each of them doubled the
            // sweep's time on the slow retries for no other constant.
            if !decided && !refuted && seen && cfg.known_atoms && i == root {
                decided = asked!('nodes, cases_prove(r, cx, cfg, subject, &k));
                if decided {
                    count(r).opaque_cases += 1;
                }
            }
        }
        if decided {
            if !all_constant {
                count(r).opaque_proved += 1;
            }
            let e = asked!('nodes, r.build(cx, |cx| cx.mk_const(&k)));
            to.insert(i, e);
        } else if !refuted {
            failures += 1;
        }
    }
    if let Some(p) = pending
        && !spent
    {
        r.swept.insert(p, to.get(&p).copied().unwrap_or(p));
    }
    Ok(to.get(&root).copied().unwrap_or(root))
}

/// How the samples relate a node to one met before it: `rep + d`, `d − rep` or `rep ^ d`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Relation {
    Sum,
    Difference,
    Xor,
}

/// The varying nodes of a sweep by their samples, up to a constant: the nodes met with each
/// sequence of differences from the first sample (`v[j] − v[0]`; the first met with each
/// `v[j] ^ v[0]`), each with its first sample. Two nodes a constant apart (added, or xored), or
/// whose sum is constant, agree there; so do two that are equal, a constant of zero apart.
#[derive(Default)]
struct Classes {
    sums: std::collections::HashMap<Box<[crate::BitVec]>, Vec<(u32, crate::BitVec)>>,
    xors: std::collections::HashMap<Box<[crate::BitVec]>, (u32, crate::BitVec)>,
}

impl Classes {
    fn key(vals: &[crate::BitVec], op: BinOp, flip: bool) -> Box<[crate::BitVec]> {
        let first = &vals[0];
        vals.iter()
            .map(|v| match flip {
                false => crate::BitVec::bin_unchecked(op, v, first),
                true => crate::BitVec::bin_unchecked(op, first, v),
            })
            .collect()
    }

    /// Whether nodes of this width are kept: a narrow one takes few values, and agrees with
    /// many others on every sample.
    fn kept(vals: &[crate::BitVec]) -> bool {
        vals.first()
            .is_some_and(|v| v.width().bits() >= SWEEP_RELATED_BITS)
    }

    /// Records `i` (samples `vals`).
    fn note(&mut self, vals: &[crate::BitVec], i: u32) {
        if !Self::kept(vals) || vals.iter().all(|v| *v == vals[0]) {
            return;
        }
        let class = self
            .sums
            .entry(Self::key(vals, BinOp::Sub, false))
            .or_default();
        if class.len() < SWEEP_CLASS {
            class.push((i, vals[0]));
        }
        self.xors
            .entry(Self::key(vals, BinOp::Xor, false))
            .or_insert((i, vals[0]));
    }

    /// The nodes recorded that a node with samples `vals` is related to on every sample, how,
    /// and the constant `d` of each relation: one equal to it, one that is its complement,
    /// then the first met a constant from it, the first met whose sum with it is constant, the
    /// first met a constant xored from it.
    fn find(&self, vals: &[crate::BitVec]) -> Vec<(u32, Relation, crate::BitVec)> {
        use crate::BitVec;
        let mut found = Vec::new();
        if !Self::kept(vals) {
            return found;
        }
        let same = self.sums.get(&Self::key(vals, BinOp::Sub, false));
        let opposite = self.sums.get(&Self::key(vals, BinOp::Sub, true));
        let zero = BitVec::zero(vals[0].width());
        if let Some(&(rep, _)) = same.and_then(|c| c.iter().find(|(_, first)| *first == vals[0])) {
            found.push((rep, Relation::Sum, zero));
        }
        let sum = |first: &BitVec| BitVec::bin_unchecked(BinOp::Add, &vals[0], first);
        if let Some(&(rep, first)) =
            opposite.and_then(|c| c.iter().find(|(_, first)| sum(first).is_ones()))
        {
            found.push((rep, Relation::Difference, sum(&first)));
        }
        if let Some(&(rep, first)) = same.and_then(|c| c.first())
            && first != vals[0]
        {
            let d = BitVec::bin_unchecked(BinOp::Sub, &vals[0], &first);
            found.push((rep, Relation::Sum, d));
        }
        if let Some(&(rep, first)) = opposite.and_then(|c| c.first())
            && !sum(&first).is_ones()
        {
            found.push((rep, Relation::Difference, sum(&first)));
        }
        if let Some((rep, first)) = self.xors.get(&Self::key(vals, BinOp::Xor, false)) {
            let d = BitVec::bin_unchecked(BinOp::Xor, &vals[0], first);
            found.push((*rep, Relation::Xor, d));
        }
        found
    }
}

/// What [`related`] found of a node and the one its samples relate it to.
enum Related {
    /// Proved: the node written over the other.
    Proved(u32),
    /// The node is already written over the other.
    Written,
    /// No proof.
    Open,
}

/// One value written twice. An obfuscator computes a value again where it reads it again:
/// `(t ^ a) + b` here, `c − (t ^ a')` there, `~(e − (t ^ a))` in a third place, equal through the
/// bits known of `t`. Each is its own atom to every reading above, so a sum over them that
/// cancels is not seen to (the certificate takes atoms for independent), and no rule relates
/// two nodes it is not looking at. The samples do: `cur`, which they show to be `rep + d`,
/// `d − rep` or `rep ^ d` for a node `rep` met before it, is asked about as an opaque constant
/// is (the difference of the two, whether it is zero), and written that way once proved. The
/// sums above then read one atom, and the linear passes collect its terms.
fn related(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    cur: u32,
    rep: u32,
    relation: Relation,
    d: &crate::BitVec,
) -> Result<Related, Stop> {
    // Written over `rep` and constants alone: nothing to relate.
    let node = cx.node(cur);
    if cur == rep
        || (node.children().any(|c| c == rep)
            && node
                .children()
                .all(|c| c == rep || cx.const_val(c).is_some()))
    {
        return Ok(Related::Written);
    }
    let zero = crate::BitVec::zero(d.width());
    let e = r.build(cx, |cx| {
        let k = cx.mk_const(d)?;
        match relation {
            Relation::Sum if d.is_zero() => Ok(rep),
            Relation::Sum => cx.c_bin(BinOp::Add, rep, k),
            Relation::Difference if d.is_zero() => cx.c_un(UnOp::Neg, rep),
            Relation::Difference if d.is_ones() => cx.c_un(UnOp::Not, rep),
            Relation::Difference => cx.c_bin(BinOp::Sub, k, rep),
            Relation::Xor => cx.c_bin(BinOp::Xor, rep, k),
        }
    })?;
    if e == cur {
        return Ok(Related::Written);
    }
    let op = match relation {
        Relation::Xor => BinOp::Xor,
        _ => BinOp::Sub,
    };
    let diff = r.build(cx, |cx| cx.c_bin(op, cur, e))?;
    let proved = |v: crate::BitVec| match v.is_zero() {
        true => Related::Proved(e),
        false => Related::Open,
    };
    if let Some(v) = cx.const_val(diff) {
        return Ok(proved(v));
    }
    let subject = super::demanded::reduced(r, cx, diff, SWEEP_DEMAND_VISITS)?;
    if let Some(v) = cx.const_val(subject) {
        return Ok(proved(v));
    }
    if let Some(holds) = exhaustive(r, cx, subject, &zero)? {
        count(r).opaque_exhausted += u64::from(holds);
        return Ok(if holds {
            Related::Proved(e)
        } else {
            Related::Open
        });
    }
    let (decided, _, _) = readings_prove(r, cx, cfg, subject, &zero)?;
    if decided {
        count(r).opaque_proved += 1;
        return Ok(Related::Proved(e));
    }
    Ok(Related::Open)
}

/// The related pairs a sweep asks about without a proof before it asks about no more.
const SWEEP_UNRELATED: usize = 64;

/// The most nodes a sweep keeps of those a constant apart.
const SWEEP_CLASS: usize = 16;

/// The narrowest node a sweep relates to another by its samples.
const SWEEP_RELATED_BITS: u16 = 8;

/// whether `root` is `k` at every point, decided by evaluating it at every value of
/// the bits of its symbols that reach it, when those number at most [`EXHAUSTIVE_BITS`]: a byte
/// `trunc<8>(x)` of a symbol is 256 values whatever `x`'s width, and `zext<64>(x) & m` reads
/// `m`'s bits of `x`. The bits that reach the root are what the demanded-bits transfers below let
/// through from the root down (each a superset); a symbol's other bits are taken as zero, which
/// no node can tell from any other value. Charged to the MBA solver's steps as the sweep's
/// certificates are, within [`EXHAUSTIVE_SHARE`]. `None` when it does not apply or would cost
/// more.
fn exhaustive(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    k: &crate::BitVec,
) -> Result<Option<bool>, Stop> {
    use crate::BitVec;
    // The DAG below `root`, operands first; every node at most 64 bits.
    let mut order: Vec<u32> = Vec::new();
    let mut at: crate::hash::IdMap<u32, usize> = crate::hash::IdMap::default();
    let mut seen: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if expanded {
            at.insert(i, order.len());
            order.push(i);
            continue;
        }
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if cx.width_of(i).bits() > 64 {
            return Ok(None);
        }
        stack.push((i, true));
        for c in cx.node(i).children() {
            stack.push((c, false));
        }
    }
    // The bits of each node that reach the root, from the root down.
    let ones = |w: u16| if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let konst = |j: u32| cx.const_val(j).and_then(|v| v.to_u64());
    let mut demand: Vec<u64> = vec![0; order.len()];
    demand[at[&root]] = ones(cx.width_of(root).bits());
    for idx in (0..order.len()).rev() {
        let i = order[idx];
        let m = demand[idx];
        if m == 0 {
            continue;
        }
        let n = cx.node(i);
        let w = cx.width_of(i).bits();
        let low_prefix = ones(64 - m.leading_zeros() as u16);
        let mut give = |c: u32, d: u64| {
            let wc = cx.width_of(c).bits();
            demand[at[&c]] |= d & ones(wc);
        };
        match n.op {
            OpCode::And | OpCode::Or => {
                for (c, o) in [(n.a, n.b), (n.b, n.a)] {
                    let d = match (konst(o), n.op) {
                        (Some(k), OpCode::And) => m & k,
                        (Some(k), _) => m & !k,
                        _ => m,
                    };
                    give(c, d);
                }
            }
            OpCode::Xor => {
                give(n.a, m);
                give(n.b, m);
            }
            OpCode::Not => give(n.a, m),
            OpCode::Add | OpCode::Sub | OpCode::Mul => {
                give(n.a, low_prefix);
                give(n.b, low_prefix);
            }
            OpCode::Neg => give(n.a, low_prefix),
            OpCode::Shl | OpCode::LShr if konst(n.b).is_some_and(|s| s < u64::from(w)) => {
                let s = konst(n.b).unwrap_or(0);
                give(
                    n.a,
                    if n.op == OpCode::Shl {
                        m >> s
                    } else {
                        (m << s) & ones(w)
                    },
                );
                give(n.b, u64::MAX);
            }
            OpCode::Zext => give(n.a, m),
            OpCode::Extract => give(n.a, m << n.b),
            // a rotate by a constant moves the demand the other way; a `concat`
            // splits it between its halves.
            OpCode::RotL | OpCode::RotR if konst(n.b).is_some() && w <= 64 && w > 0 => {
                let s = (konst(n.b).unwrap_or(0) % u64::from(w)) as u32;
                let rot = |v: u64, by: u32, left: bool| {
                    let by = by % u32::from(w);
                    if by == 0 {
                        return v;
                    }
                    let v = v & ones(w);
                    if left {
                        ((v << by) | (v >> (u32::from(w) - by))) & ones(w)
                    } else {
                        ((v >> by) | (v << (u32::from(w) - by))) & ones(w)
                    }
                };
                give(n.a, rot(m, s, n.op == OpCode::RotR));
                give(n.b, u64::MAX);
            }
            OpCode::Concat => {
                let wl = cx.width_of(n.b).bits();
                give(n.b, m & ones(wl));
                give(n.a, if wl >= 64 { 0 } else { m >> wl });
            }
            _ => {
                for c in n.children() {
                    give(c, u64::MAX);
                }
            }
        }
    }
    let mut syms: Vec<(u32, u64)> = Vec::new();
    for (idx, &i) in order.iter().enumerate() {
        if cx.node(i).op == OpCode::Sym {
            syms.push((i, demand[idx]));
        }
    }
    let mut total: u32 = syms.iter().map(|(_, m)| m.count_ones()).sum();
    // The bits set in every value enumerated, and whether the values are a node's (not the
    // symbols'): a node may take fewer values than its unknown bits allow, so a value the root
    // differs at decides nothing.
    let (mut base, mut cut_at) = (0u64, false);
    let (order, at) = if total > EXHAUSTIVE_BITS {
        // too many symbol bits; a node every demanded path from them passes
        // through, with few bits of its own, is enumerated instead.
        let Some(cut) = bottleneck(cx, &order, &at, &demand) else {
            return Ok(None);
        };
        // Over the values it can take: the bits known of it are those values' (a sum
        // that is constant only for them is constant), and a value it never takes refutes
        // nothing.
        let [z, o] = super::known_words(r, cx, order[cut])?.0.unwrap_or([0, 0]);
        syms = vec![(order[cut], demand[cut] & !(z | o))];
        base = o & demand[cut];
        cut_at = true;
        total = syms[0].1.count_ones();
        above(cx, &order, order[cut])
    } else {
        (order, at)
    };
    let points = 1u64 << total;
    let inputs: Vec<u32> = syms.iter().map(|(s, _)| *s).collect();
    let prog = program64(cx, &order, &at, &inputs);
    // A word program's evaluation costs a fraction of a generic one's (measured, see
    // [`WORD_EVALS`]); charged as that many generic evaluations.
    let work = points
        .saturating_mul(order.len() as u64)
        .div_ceil(if prog.is_some() { WORD_EVALS } else { 1 });
    let mut meter = Steps::new(r, EXHAUSTIVE_SHARE);
    if work > certify::Meter::left(&meter) {
        return Ok(None);
    }
    certify::Meter::charge(&mut meter, work)?;
    if let Some(prog) = prog {
        let mut vals: Vec<u64> = vec![0; order.len()];
        let ku = k.to_u64();
        for p in 0..points {
            let mut left = p;
            for &(s, m) in &syms {
                let mut v = base;
                let mut mm = m;
                while mm != 0 {
                    let b = mm & mm.wrapping_neg();
                    if left & 1 == 1 {
                        v |= b;
                    }
                    left >>= 1;
                    mm &= mm - 1;
                }
                vals[at[&s]] = v;
            }
            run64(&prog, &mut vals);
            if Some(vals[at[&root]]) != ku {
                return Ok((!cut_at).then_some(false));
            }
        }
        return Ok(Some(true));
    }
    let mut vals: Vec<BitVec> = vec![BitVec::zero(crate::Width::W1); order.len()];
    for p in 0..points {
        // Spread the point's bits over each symbol's bits that reach the root.
        let mut left = p;
        for &(s, m) in &syms {
            let mut v = base;
            let mut mm = m;
            while mm != 0 {
                let b = mm & mm.wrapping_neg();
                if left & 1 == 1 {
                    v |= b;
                }
                left >>= 1;
                mm &= mm - 1;
            }
            vals[at[&s]] = BitVec::wrapping_from_u64(cx.width_of(s), v);
        }
        for (idx, &i) in order.iter().enumerate() {
            if inputs.contains(&i) {
                continue;
            }
            // A symbol that is no input: zero, as in [`program64`].
            vals[idx] = cx
                .eval_node(i, |j| vals[at[&j]], |_, w| Some(BitVec::zero(w)))
                .map_err(Stop::Error)?;
        }
        if vals[at[&root]] != *k {
            return Ok((!cut_at).then_some(false));
        }
    }
    Ok(Some(true))
}

/// the node of `order` (operands first, the root last) that every demanded path
/// from the symbols to the root passes through, nearest the symbols with at most
/// [`EXHAUSTIVE_BITS`] demanded bits; not the root or a symbol. The root is a function of its
/// demanded bits alone. A reconstructed address can take a few bits of sums over `k - t` and
/// `t + k'`: 22 bits of the two symbols in `t` reach them, 11 bits of `t`.
fn bottleneck(
    cx: &Context,
    order: &[u32],
    at: &crate::hash::IdMap<u32, usize>,
    demand: &[u64],
) -> Option<usize> {
    let n = order.len();
    let root = n.checked_sub(1)?;
    let mut idom = vec![usize::MAX; n];
    let mut depth = vec![0u32; n];
    let meet = |idom: &[usize], depth: &[u32], mut a: usize, mut b: usize| {
        while a != b {
            if depth[a] >= depth[b] {
                a = idom[a];
            } else {
                b = idom[b];
            }
        }
        a
    };
    idom[root] = root;
    // Parents first: every operand comes after each node that reads it.
    for idx in (0..n).rev() {
        if idom[idx] == usize::MAX || demand[idx] == 0 {
            continue;
        }
        if idx != root {
            depth[idx] = depth[idom[idx]] + 1;
        }
        for c in cx.node(order[idx]).children() {
            let ci = at[&c];
            if demand[ci] == 0 {
                continue;
            }
            idom[ci] = match idom[ci] {
                usize::MAX => idx,
                d => meet(&idom, &depth, d, idx),
            };
        }
    }
    let mut cut: Option<usize> = None;
    for (idx, &i) in order.iter().enumerate() {
        if cx.node(i).op == OpCode::Sym && demand[idx] != 0 && idom[idx] != usize::MAX {
            cut = Some(match cut {
                None => idx,
                Some(c) => meet(&idom, &depth, c, idx),
            });
        }
    }
    let mut c = cut?;
    loop {
        if c == root {
            return None;
        }
        if cx.node(order[c]).op != OpCode::Sym && demand[c].count_ones() <= EXHAUSTIVE_BITS {
            return Some(c);
        }
        c = idom[c];
    }
}

/// `order` with only the nodes the root reads without passing below `cut`, and their indices.
#[allow(clippy::type_complexity)]
fn above(cx: &Context, order: &[u32], cut: u32) -> (Vec<u32>, crate::hash::IdMap<u32, usize>) {
    let mut keep: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    let mut stack: Vec<u32> = order.last().copied().into_iter().collect();
    while let Some(i) = stack.pop() {
        if keep.insert(i, ()).is_some() || i == cut {
            continue;
        }
        stack.extend(cx.node(i).children());
    }
    let order: Vec<u32> = order
        .iter()
        .copied()
        .filter(|i| keep.contains_key(i))
        .collect();
    let at = order.iter().enumerate().map(|(k, i)| (*i, k)).collect();
    (order, at)
}

/// one node of a word program ([`program64`]): operands are indices of earlier
/// nodes, and every value is kept masked to its node's width.
#[derive(Clone, Copy)]
enum Op64 {
    Keep,
    Const(u64),
    Bin(crate::BinOp, usize, usize),
    Not(usize),
    Neg(usize),
    Zext(usize),
    Sext(usize, u16),
    Extract(usize, u16),
    Cmp(crate::CmpOp, usize, usize, u16),
    Select(usize, usize, usize),
    /// `concat(hi, lo)`, with the low half's width.
    Concat(usize, usize, u16),
}

/// `order` (operands first, every node at most 64 bits) as a program over `u64` words, with
/// each node's width mask; `None` when an operator is not one it evaluates. An input's word
/// (a symbol's, or a cut node's) is set before each run.
fn program64(
    cx: &Context,
    order: &[u32],
    at: &crate::hash::IdMap<u32, usize>,
    inputs: &[u32],
) -> Option<Vec<(Op64, u64)>> {
    use crate::{BinOp, CmpOp, UnOp};
    let ones = |w: u16| if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let mut prog = Vec::with_capacity(order.len());
    for &i in order {
        let n = cx.node(i);
        let w = cx.width_of(i).bits();
        let arg = |j: u32| at.get(&j).copied();
        let op = match n.op {
            _ if inputs.contains(&i) => Op64::Keep,
            // A symbol past a bottleneck cut that is no input reaches the root only through a
            // node with no demanded bits: any value, zero as the uncut enumeration gives it.
            OpCode::Sym => Op64::Const(0),
            OpCode::Const => Op64::Const(cx.const_val(i)?.to_u64()?),
            OpCode::Zext => Op64::Zext(arg(n.a)?),
            OpCode::Sext => Op64::Sext(arg(n.a)?, cx.width_of(n.a).bits()),
            OpCode::Extract => Op64::Extract(arg(n.a)?, n.b as u16),
            OpCode::Select => Op64::Select(arg(n.a)?, arg(n.b)?, arg(n.c)?),
            OpCode::Concat => Op64::Concat(arg(n.a)?, arg(n.b)?, cx.width_of(n.b).bits()),
            op => {
                if let Some(u) = op.as_un() {
                    match u {
                        UnOp::Not => Op64::Not(arg(n.a)?),
                        UnOp::Neg => Op64::Neg(arg(n.a)?),
                        _ => return None,
                    }
                } else if let Some(b) = op.as_bin() {
                    match b {
                        BinOp::Add
                        | BinOp::Sub
                        | BinOp::Mul
                        | BinOp::And
                        | BinOp::Or
                        | BinOp::Xor
                        | BinOp::Shl
                        | BinOp::LShr
                        | BinOp::AShr
                        | BinOp::RotL
                        | BinOp::RotR => Op64::Bin(b, arg(n.a)?, arg(n.b)?),
                        _ => return None,
                    }
                } else {
                    let c = op.as_cmp()?;
                    match c {
                        CmpOp::Eq
                        | CmpOp::Ne
                        | CmpOp::Ult
                        | CmpOp::Ule
                        | CmpOp::Slt
                        | CmpOp::Sle => Op64::Cmp(c, arg(n.a)?, arg(n.b)?, cx.width_of(n.a).bits()),
                    }
                }
            }
        };
        prog.push((op, ones(w)));
    }
    Some(prog)
}

/// Runs a word program over `vals` (the symbols' words already set).
fn run64(prog: &[(Op64, u64)], vals: &mut [u64]) {
    use crate::{BinOp, CmpOp};
    let sext = |v: u64, w: u16| -> i64 {
        let sh = 64 - u32::from(w);
        ((v << sh) as i64) >> sh
    };
    for (idx, &(op, mask)) in prog.iter().enumerate() {
        let w = 64 - mask.leading_zeros();
        let v = match op {
            Op64::Keep => continue,
            Op64::Const(c) => c,
            Op64::Not(a) => !vals[a],
            Op64::Neg(a) => vals[a].wrapping_neg(),
            Op64::Zext(a) => vals[a],
            Op64::Sext(a, wa) => sext(vals[a], wa) as u64,
            Op64::Extract(a, lo) => vals[a] >> lo,
            Op64::Select(c, t, f) => {
                if vals[c] & 1 == 1 {
                    vals[t]
                } else {
                    vals[f]
                }
            }
            Op64::Concat(hi, lo, wl) => {
                if wl >= 64 {
                    vals[lo]
                } else {
                    (vals[hi] << wl) | vals[lo]
                }
            }
            Op64::Cmp(c, a, b, wa) => {
                let (x, y) = (vals[a], vals[b]);
                u64::from(match c {
                    CmpOp::Eq => x == y,
                    CmpOp::Ne => x != y,
                    CmpOp::Ult => x < y,
                    CmpOp::Ule => x <= y,
                    CmpOp::Slt => sext(x, wa) < sext(y, wa),
                    CmpOp::Sle => sext(x, wa) <= sext(y, wa),
                })
            }
            Op64::Bin(b, a, c) => {
                let (x, y) = (vals[a], vals[c]);
                match b {
                    BinOp::Add => x.wrapping_add(y),
                    BinOp::Sub => x.wrapping_sub(y),
                    BinOp::Mul => x.wrapping_mul(y),
                    BinOp::And => x & y,
                    BinOp::Or => x | y,
                    BinOp::Xor => x ^ y,
                    BinOp::Shl => {
                        if y >= u64::from(w) {
                            0
                        } else {
                            x << y
                        }
                    }
                    BinOp::LShr => {
                        if y >= u64::from(w) {
                            0
                        } else {
                            x >> y
                        }
                    }
                    BinOp::RotL | BinOp::RotR if w > 0 => {
                        let by = (y % u64::from(w)) as u32;
                        let by = if b == BinOp::RotR { (w - by) % w } else { by };
                        if by == 0 {
                            x
                        } else {
                            (x << by) | (x >> (w - by))
                        }
                    }
                    _ => {
                        let s = sext(x, w as u16);
                        (s >> y.min(u64::from(w) - 1)) as u64
                    }
                }
            }
        };
        vals[idx] = v & mask;
    }
}

/// Word-program evaluations ([`run64`]) charged as one generic node evaluation
/// (`Context::eval_node`). On representative reconstructed addresses (44 and 71 nodes, 4,096
/// points) a word program ran 4 to 38 times as fast as the generic evaluator, about 20 times
/// typically; this charges the low end.
const WORD_EVALS: u64 = 8;

/// The most bits [`exhaustive`] enumerates.
const EXHAUSTIVE_BITS: u32 = 16;

/// The node evaluations one [`exhaustive`] decision may take: `2^13` points of a 64-node
/// candidate.
const EXHAUSTIVE_SHARE: u64 = 1 << 20;

/// the varying sum `n` with its most shared subterm cut off as one atom,
/// simplified (`Σ cᵢ·fᵢ(t)` over a rotated value `t` is `t ^ k`). `Some` node when the solver's
/// answer is smaller and passes the gates the phase's answers do: agreement at the refutation
/// sample, and an exact certificate within the sweep's share. Within the limits below, so a
/// sweep asks only blocks the size an obfuscator writes, each at a small fixed cost.
fn sweep_cut(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
) -> Result<Option<u32>, Stop> {
    if !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) {
        return Ok(None);
    }
    for c in shared_nodes(cx, n, &cfg.limits, SWEEP_CUTS) {
        if let Some(e) = sweep_cut_at(r, cx, cfg, n, c)? {
            return Ok(Some(e));
        }
    }
    drop_noise(r, cx, cfg, n)
}

/// the block `n` with each atom it does not depend on written as zero, read with
/// arithmetic under its bitwise operators as atoms (the two halves of a rotate, `t << 22` and
/// `t >>u 42`, each with its known bits) and every atom through the bits known of it: noise that
/// cancels only given those bits (a value mixed in that cancels for `t`'s low 22 bits zero). An
/// exact certificate proves each drop; the solver need not find the simpler form, and the
/// constants above no longer read the noise.
fn drop_noise(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
) -> Result<Option<u32>, Stop> {
    let Ok((m, bindings)) = lower_id_reading(cx, n, &cfg.limits, Reading::Shallow) else {
        return Ok(None);
    };

    if m.nodes().len() < SWEEP_CUT_NODES || m.vars().len() > SWEEP_DROP_VARS || !m.shape().mixed {
        return Ok(None);
    }
    let mut read = m;
    for (v, &atom) in bindings.atoms.iter().enumerate() {
        if let (Some(kb), _) = super::known(r, cx, atom)?
            && !kb.known().is_zero()
            && let Some(m2) = with_known_bits(&read, v as u32, &kb.unknown_mask(), &kb.known_one())
        {
            read = m2;
        }
    }
    let mut dropped = false;
    for v in 0..read.vars().len() as u32 {
        let Some(m0) = with_constant(&read, v) else {
            continue;
        };
        if !sampled(r, &read, &m0, read.key()[0])? {
            continue;
        }
        let report = certify::prove(&read, &m0, &mut Steps::new(r, SWEEP_SHARE))?;
        count(r).certificates.record(&report);
        if report.verdict == Verdict::Proved {
            read = m0;
            dropped = true;
        }
    }
    if !dropped {
        return Ok(None);
    }
    count(r).noise_atoms += 1;
    Ok(Some(r.build(cx, |cx| lift_id(cx, &read, &bindings))?))
}

/// The most atoms [`drop_noise`] reads a block over.
const SWEEP_DROP_VARS: usize = 6;

/// [`sweep_cut`] with `c` cut off.
fn sweep_cut_at(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
    c: u32,
) -> Result<Option<u32>, Stop> {
    let Ok((m, bindings)) = lower_id_reading(cx, n, &cfg.limits, Reading::CutWhole(c)) else {
        return Ok(None);
    };

    if m.nodes().len() < SWEEP_CUT_NODES || m.vars().len() > SWEEP_CUT_VARS || !m.shape().mixed {
        return Ok(None);
    }
    let size = m.nodes().len();
    if let Some(expr) = cut_answer(r, &m, size, cfg, SWEEP_CUT_STEPS)? {
        return Ok(Some(r.build(cx, |cx| lift_id(cx, &expr, &bindings))?));
    }
    Ok(None)
}

/// `m` with variable `v` replaced by zero.
fn with_constant(m: &MbaExpr, v: u32) -> Option<MbaExpr> {
    let w = *m.vars().get(v as usize)?;
    let mut out = MbaExpr::new(m.vars().to_vec());
    let mut map: Vec<u32> = Vec::with_capacity(m.nodes().len());
    for n in m.nodes() {
        let args: Vec<u32> = n.args[..n.op.arity()]
            .iter()
            .map(|&k| map[k as usize])
            .collect();
        let id = match n.op {
            MOp::Var(i) if i == v => out.push(MOp::Const(crate::BitVec::zero(w)), &[]).ok()?,
            MOp::Zext | MOp::Sext | MOp::Trunc => out.push_cast(n.op, args[0], n.width).ok()?,
            op => out.push(op, &args).ok()?,
        };
        map.push(id);
    }
    Some(out)
}

/// The solver's answer to the noise block `m`, when it has fewer nodes than `size` and passes
/// the refutation sample and an exact certificate within the sweep's share.
fn cut_answer(
    r: &mut Runner<'_, '_>,
    m: &MbaExpr,
    size: usize,
    cfg: &MbaConfig,
    steps: u64,
) -> Result<Option<MbaExpr>, Stop> {
    let limit = steps.min(r.meter.left_in(|b| b.mba_steps));
    if limit == 0 {
        return Ok(None);
    }
    let budget = cfg.budget.with_evidence(false).with_steps(limit);
    let (answer, spent) = r.inner.mba.solver.solve_counted(m, &budget);
    let spent = spent.min(r.meter.left_in(|b| b.mba_steps));
    r.meter.charge(Counter::MbaSteps, spent)?;
    let MbaAnswer::Simplified { expr, .. } = answer else {
        return Ok(None);
    };
    if expr.vars() != m.vars()
        || expr.width() != m.width()
        || expr.nodes().len() >= size
        || !sampled(r, m, &expr, m.key()[0])?
    {
        return Ok(None);
    }
    let report = certify::prove(m, &expr, &mut Steps::new(r, SWEEP_SHARE))?;
    count(r).certificates.record(&report);
    if report.verdict != Verdict::Proved {
        return Ok(None);
    }
    count(r).noise_blocks += 1;
    Ok(Some(expr))
}

/// the sweep's readings of `subject` asked whether it is `k`: whether one proves it
/// (`decided`), whether its whole fragment is refuted (`refuted`), and whether some narrower
/// reading was refuted over its free atoms (a constant only through how its atoms relate).
fn readings_prove(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    subject: u32,
    k: &crate::BitVec,
) -> Result<(bool, bool, bool), Stop> {
    let (mut decided, mut refuted, mut seen) = (false, false, false);
    let mut readings: Vec<(u64, Option<Reading>, MbaExpr, Bindings)> = Vec::new();
    let cuts = shared_nodes(cx, subject, &cfg.limits, SWEEP_CUTS);
    let kinds = [Reading::SemiLinear, Reading::Shallow, Reading::Linear];
    let all = std::iter::once(None)
        .chain(kinds.into_iter().map(Some))
        .chain(
            cuts.into_iter()
                .flat_map(|c| [Some(Reading::Cut(c)), Some(Reading::CutWhole(c))]),
        );
    for reading in all {
        let lowered = match reading {
            None => lower_id(cx, subject, &cfg.limits),
            Some(rd) => lower_id_reading(cx, subject, &cfg.limits, rd),
        };
        let Ok((m, bindings)) = lowered else {
            continue;
        };
        if readings.iter().any(|(_, _, o, _)| *o == m) {
            continue;
        }
        let t = m.vars().len().min(32) as u32;
        let points = match reading {
            Some(Reading::Linear) => 1u64 << t,
            _ => 64 * ((1u64 << t) - 1),
        };
        readings.push((
            points.saturating_mul(m.nodes().len() as u64),
            reading,
            m,
            bindings,
        ));
    }
    readings.sort_by_key(|(cost, _, _, _)| *cost);
    'readings: for (cost, reading, m, bindings) in readings {
        if cost > SWEEP_SHARE {
            break;
        }
        let mut c = MbaExpr::new(m.vars().to_vec());
        if c.push(MOp::Const(*k), &[]).is_err() {
            continue;
        }
        // a narrower reading refuted over free atoms is asked again with its atoms
        // read through the bits known of them, where asked and where no input with those bits
        // is seen to refute it (see `known_reading`). A reading the certificate could not
        // decide is no easier with more nodes, and asking every refuted one again spends the
        // run's steps (1,500 times in one measured question, none proved, with two constants
        // left unfolded).
        let mut m = m;
        let mut known = false;
        loop {
            count(r).opaque_asked += 1;
            let report = certify::prove(&m, &c, &mut Steps::new(r, SWEEP_SHARE))?;
            count(r).certificates.record(&report);
            match report.verdict {
                Verdict::Proved => {
                    decided = true;
                    break 'readings;
                }
                Verdict::Refuted if reading.is_none() => {
                    refuted = true;
                    break 'readings;
                }
                Verdict::Refuted if !known => {
                    seen = true;
                    if !cfg.known_atoms {
                        break;
                    }
                    known = true;
                    let Some(at) = report.counterexample.as_deref() else {
                        break;
                    };
                    match known_reading(r, cx, &m, &bindings, at, k)? {
                        Some(read) => m = read,
                        None => break,
                    }
                }
                _ => break,
            }
        }
    }
    Ok((decided, refuted, seen))
}

/// Whether `values` contains exactly two distinct values.
fn exactly_two(values: &[crate::BitVec]) -> bool {
    let Some((&first, rest)) = values.split_first() else {
        return false;
    };
    let Some(second) = rest.iter().copied().find(|v| *v != first) else {
        return false;
    };
    values.iter().all(|v| *v == first || *v == second)
}

/// A varying block proved constant on each side of its most-used condition, reconstructed as a
/// select of those constants. Sampling only admits a candidate; each side needs exact evidence.
fn cases_fold(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
    attempts: &mut usize,
) -> Result<Option<u32>, Stop> {
    let Some((c, t, f)) = r.build(cx, |cx| super::context::sides(cx, n))? else {
        return Ok(None);
    };
    *attempts += 1;
    let mut sides = [t, f];
    let mut values = [crate::BitVec::zero(cx.width_of(n)); 2];
    for (slot, side) in values.iter_mut().zip(&mut sides) {
        *side = sweep_inner(r, cx, cfg, *side, false)?;
        if let Some(k) = cx.const_val(*side) {
            *slot = k;
            continue;
        }
        r.sample(cx, *side)?;
        let samples = &r.samples[side];
        let Some(&k) = samples.first() else {
            return Ok(None);
        };
        if samples.iter().any(|v| *v != k) {
            return Ok(None);
        }
        *slot = k;
    }
    for (side, k) in sides.into_iter().zip(values) {
        if cx.const_val(side).is_none() && !readings_prove(r, cx, cfg, side, &k)?.0 {
            return Ok(None);
        }
    }
    let e = r.build(cx, |cx| {
        let t = cx.mk_const(&values[0])?;
        let f = cx.mk_const(&values[1])?;
        cx.c_select(c, t, f)
    })?;
    if e == n {
        return Ok(None);
    }
    count(r).piecewise_blocks += 1;
    Ok(Some(e))
}

/// whether `n` is `k` one case of a condition at a time: the condition its selects
/// test most, each side `n` with what that case fixes put in (`context::sides`), each proved `k`
/// by the readings (their atoms' known bits included). Sound as `select(c, n[c], n[!c])` is `n`.
/// Obfuscated expressions can mix one condition (`trunc<32>(x) == 0`) through a constant's
/// noise: on either side the selects are gone and the low half of `x` is known, and both are
/// `k`. Each side must be `k` at every sample point before a certificate is asked.
fn cases_prove(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
    k: &crate::BitVec,
) -> Result<bool, Stop> {
    let Some((_, t, f)) = r.build(cx, |cx| super::context::sides(cx, n))? else {
        return Ok(false);
    };
    for side in [t, f] {
        if cx.const_val(side).is_some() {
            if cx.const_val(side) != Some(*k) {
                return Ok(false);
            }
            continue;
        }
        r.sample(cx, side)?;
        if r.samples[&side].iter().any(|v| v != k) {
            return Ok(false);
        }
    }
    for side in [t, f] {
        if cx.const_val(side).is_none() && !readings_prove(r, cx, cfg, side, k)?.0 {
            return Ok(false);
        }
    }
    Ok(true)
}

/// the reading `m` of a fragment with each atom some of whose bits are known read
/// as `(v & unknown) | ones` ([`with_known_bits`]), to be proved equal to `k`; `None` when no
/// atom's bits are known, or an input with them is seen where `m` is not `k`: the input `at`
/// that refuted `m` and [`KNOWN_SCREEN`] others, each with every atom's known bits written in.
/// An opaque constant is often one only through such bits: under its bitwise operators,
/// `(x & 0xffffffff00000000) * 0x8000001 + 0xc00081fe00001000` (low byte 0) and a rotate's
/// product (low byte 0x52) cancel to a constant, as two free atoms they do not.
fn known_reading(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    m: &MbaExpr,
    bindings: &Bindings,
    at: &[crate::BitVec],
    k: &crate::BitVec,
) -> Result<Option<MbaExpr>, Stop> {
    use crate::facts::known::{bv_and, bv_or};
    let mut read: Option<MbaExpr> = None;
    let mut bits: Vec<Option<(crate::BitVec, crate::BitVec)>> = vec![None; m.vars().len()];
    for (v, &atom) in bindings.atoms.iter().enumerate() {
        if let (Some(kb), _) = super::known(r, cx, atom)?
            && !kb.known().is_zero()
            && let Some(m2) = with_known_bits(
                read.as_ref().unwrap_or(m),
                v as u32,
                &kb.unknown_mask(),
                &kb.known_one(),
            )
        {
            bits[v] = Some((kb.unknown_mask(), kb.known_one()));
            read = Some(m2);
        }
    }
    if read.is_none() || at.len() != m.vars().len() {
        return Ok(None);
    }
    // `at`, then pseudo-random points (splitmix64 of the variable and the point), each atom's
    // value with its known bits written in.
    let point = |p: u64| -> Vec<crate::BitVec> {
        (0..m.vars().len())
            .map(|v| {
                let x = if p == 0 {
                    at[v]
                } else {
                    let mut z = ((v as u64) << 32 ^ p).wrapping_add(0x9e37_79b9_7f4a_7c15);
                    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                    crate::BitVec::wrapping_from_u64(m.vars()[v], z ^ (z >> 31))
                };
                match &bits[v] {
                    Some((unknown, ones)) => bv_or(&bv_and(&x, unknown), ones),
                    None => x,
                }
            })
            .collect()
    };
    for p in 0..=KNOWN_SCREEN {
        if m.eval(&point(p)).is_some_and(|v| v != *k) {
            return Ok(None);
        }
    }
    Ok(read)
}

/// Pseudo-random inputs [`known_reading`] screens a reading at, besides its counterexample.
const KNOWN_SCREEN: u64 = 8;

/// `m` with variable `v` read as `(v & unknown) | ones`, its known bits written out.
/// An identity of the result holds for every value with those known bits, so for the atom the
/// variable stands for, which has them.
fn with_known_bits(
    m: &MbaExpr,
    v: u32,
    unknown: &crate::BitVec,
    ones: &crate::BitVec,
) -> Option<MbaExpr> {
    let mut out = MbaExpr::new(m.vars().to_vec());
    let x = out.push(MOp::Var(v), &[]).ok()?;
    let u = out.push(MOp::Const(*unknown), &[]).ok()?;
    let a = out.push(MOp::And, &[x, u]).ok()?;
    let o = out.push(MOp::Const(*ones), &[]).ok()?;
    let read = out.push(MOp::Or, &[a, o]).ok()?;
    let mut map: Vec<u32> = Vec::with_capacity(m.nodes().len());
    for n in m.nodes() {
        let args: Vec<u32> = n.args[..n.op.arity()]
            .iter()
            .map(|&k| map[k as usize])
            .collect();
        let id = match n.op {
            MOp::Var(i) if i == v => read,
            MOp::Zext | MOp::Sext | MOp::Trunc => out.push_cast(n.op, args[0], n.width).ok()?,
            op => out.push(op, &args).ok()?,
        };
        map.push(id);
    }
    Some(out)
}

/// The fewest nodes a block [`sweep_cut`] asks about has.
const SWEEP_CUT_NODES: usize = 16;

/// The most atoms a block [`sweep_cut`] asks about has.
const SWEEP_CUT_VARS: usize = 4;

/// The solver steps one [`sweep_cut`] question takes.
const SWEEP_CUT_STEPS: u64 = 1 << 12;

/// The most nodes the sweep's demanded-bits reduction of one candidate visits.
const SWEEP_DEMAND_VISITS: u32 = 4096;

/// The most candidates per sweep that certificates leave undecided before the rest are left to
/// the phases (a refuted one is decided, and cheap). 256, not 16. The run's budget
/// bounds the sweep, and a sweep it stops keeps what it proved. Behind 16 undecided candidates,
/// a large dispatch expression kept the constants its address guards are built of: six of its ten
/// guards fold with them (about 450,000 MBA steps each).
const SWEEP_FAILURES: usize = 256;

/// The most shared subterms a sweep cuts a candidate's fragment at, one reading each.
const SWEEP_CUTS: usize = 3;

/// The most two-valued blocks one sweep tries to prove piecewise.
const SWEEP_CASE_BLOCKS: usize = 256;

/// The node evaluations one sweep certificate may take.
const SWEEP_SHARE: u64 = 1 << 18;

/// Node evaluations per MBA solver step: a sweep certificate is charged as the normal-form
/// solver charges its own (batched evaluations, a fraction of a nanosecond each).
const EVALS_PER_STEP: u64 = 32;

/// A sweep certificate's meter: node evaluations, charged to the run's MBA solver steps at
/// [`EVALS_PER_STEP`], at most `share` of them.
struct Steps<'x, 'r, 'a> {
    r: &'x mut Runner<'r, 'a>,
    share: u64,
    /// Evaluations not yet charged as a whole step.
    owed: u64,
}

impl<'x, 'r, 'a> Steps<'x, 'r, 'a> {
    fn new(r: &'x mut Runner<'r, 'a>, share: u64) -> Self {
        Steps { r, share, owed: 0 }
    }
}

impl certify::Meter for Steps<'_, '_, '_> {
    type Err = Stop;
    fn left(&self) -> u64 {
        let steps = self.r.meter.left_in(|b| b.mba_steps);
        steps
            .saturating_mul(EVALS_PER_STEP)
            .saturating_sub(self.owed)
            .min(self.share)
    }
    fn charge(&mut self, units: u64) -> Result<(), Stop> {
        self.share = self.share.saturating_sub(units);
        self.owed += units;
        let steps = self.owed / EVALS_PER_STEP;
        self.owed %= EVALS_PER_STEP;
        self.r
            .meter
            .charge(Counter::MbaSteps, steps)
            .map_err(Stop::Exhausted)
    }
}

/// The MBA phase at `n`.
pub(super) fn step(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
) -> Result<Step, Stop> {
    // A solver that takes polynomials is also asked at constant left shifts (the arena spells
    // `2^k·t` as `t << k`).
    let poly = r.inner.mba.solver.polynomial_fragments();
    let op = cx.node(n).op;
    if !(mixed_op(op) || (poly && op == OpCode::Shl)) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let out = ask(r, cx, cfg, n, n)?;
    // a fragment that reads slices of one rotated value, asked again with them
    // written as masks of that rotation (see [`sliced`]).
    if cfg.noise_forms
        && let Step::Normal(fin) = &out
        && fin.done
    {
        let before = cx.len() as u32;
        if let Some(root) = r.build(cx, |cx| sliced(cx, n, cfg.limits.max_nodes))? {
            let again = ask(r, cx, cfg, n, root)?;
            if matches!(again, Step::To(..)) {
                return Ok(again);
            }
        }
        discard(r, cx, before);
    }
    Ok(out)
}

/// the slice of one value a rotate or constant shift chain over node `i` is, as
/// `(base, r, mask)` with `i == rotl(base, r) & mask` at `i`'s width (at most 64 bits): a left
/// shift by `k` is the rotation by `k` with its low `k` bits cleared, a logical right shift the
/// rotation by `-k` with its high `k` bits cleared. A node of no such chain is `(i, 0, ones)`.
fn slice_of(cx: &Context, i: u32) -> (u32, u32, u64) {
    let w = u32::from(cx.width_of(i).bits());
    if w > 64 {
        return (i, 0, u64::MAX);
    }
    let ones = u64::MAX >> (64 - w);
    let n = cx.node(i);
    let k = match n.op {
        OpCode::RotL | OpCode::Shl | OpCode::LShr if cx.width_of(n.a) == cx.width_of(i) => cx
            .const_val(n.b)
            .and_then(|c| c.to_u64())
            .filter(|&k| k > 0 && k < u64::from(w)),
        _ => None,
    };
    let Some(k) = k else {
        return (i, 0, ones);
    };
    let k = k as u32;
    let rot = |m: u64, by: u32| match by % w {
        0 => m,
        b => (m << b | m >> (w - b)) & ones,
    };
    let (base, r, m) = slice_of(cx, n.a);
    match n.op {
        OpCode::RotL => (base, (r + k) % w, rot(m, k)),
        OpCode::Shl => (base, (r + k) % w, rot(m, k) & (ones << k & ones)),
        _ => (base, (r + w - k) % w, rot(m, w - k) & (ones >> k)),
    }
}

/// node `n`'s fragment (its MBA operators, down to their atoms) with each rotate
/// or constant shift that cuts the same rotation of one value written as a mask of that
/// rotation. `rotl(x, 32) >>u 30`, `rotl(x, 32) << 34` and `rotl(x, 2)` are the low 34 bits,
/// the high 30 bits and the whole of `rotl(x, 2)`, but three unrelated atoms to the solver:
/// obfuscators can write a rotate as such shifts beside the rotate itself in MBAs that cancel.
/// `None` when no two slices are of one rotation of one value, or past `max_nodes`.
fn sliced(cx: &mut Context, n: u32, max_nodes: u32) -> Result<Option<u32>, crate::Error> {
    use crate::ops::BinOp;
    let mut groups: std::collections::BTreeMap<(u32, u32), Vec<(u32, u64)>> =
        std::collections::BTreeMap::new();
    let mut seen: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    let mut stack = vec![n];
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if seen.len() as u32 > max_nodes {
            return Ok(None);
        }
        let node = cx.node(i);
        if matches!(node.op, OpCode::RotL | OpCode::Shl | OpCode::LShr) {
            let (base, r, mask) = slice_of(cx, i);
            if base != i {
                groups.entry((base, r)).or_default().push((i, mask));
            }
        } else if mixed_op(node.op) {
            stack.extend(node.children());
        }
    }
    let mut repl: crate::hash::IdMap<u32, u32> = crate::hash::IdMap::default();
    for ((base, r), slices) in groups.into_iter().filter(|(_, s)| s.len() >= 2) {
        let w = cx.width_of(base).bits();
        let ones = u64::MAX >> (64 - u32::from(w));
        let whole = if r == 0 {
            base
        } else {
            let k = cx.mk_const_u64(w, u64::from(r))?;
            cx.c_bin(BinOp::RotL, base, k)?
        };
        for (i, mask) in slices {
            let v = if mask == ones {
                whole
            } else {
                let k = cx.mk_const_u64(w, mask)?;
                cx.c_bin(BinOp::And, whole, k)?
            };
            repl.insert(i, v);
        }
    }
    if repl.is_empty() {
        return Ok(None);
    }
    Ok(Some(cx.substitute_ids(&[n], &repl)?[0]))
}

/// Whether the fragment under `root` holds one the solver already declined in this call for
/// its size (too many atoms, variables or bit classes): a fragment that holds it has as many,
/// and the solver would spend the same steps finding that out. An obfuscated value read by a
/// chain of operations asks once at the first of them where it asked at every one (27
/// questions of 820 nodes in one measured question, 310,000 steps each, half the run's steps).
fn outgrown(r: &Runner<'_, '_>, cx: &Context, root: u32, bindings: &Bindings) -> bool {
    if r.mba_outgrown.is_empty() {
        return false;
    }
    let mut seen: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    for &a in &bindings.atoms {
        seen.insert(a, ());
    }
    let mut stack = vec![root];
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if r.mba_outgrown.contains_key(&i) {
            return true;
        }
        stack.extend(cx.node(i).children());
    }
    false
}

/// [`step`]'s question at node `n`, lowered from `root` (`n` itself, or an equal rewrite of it):
/// the answer replaces `n`.
fn ask(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
    root: u32,
) -> Result<Step, Stop> {
    let poly = r.inner.mba.solver.polynomial_fragments();
    let (m, bindings) = match lower_id(cx, root, &cfg.limits) {
        Ok(x) => x,
        Err(why) => {
            count(r).refused(&why);
            return Ok(Step::Normal(Fin::FINAL));
        }
    };
    let shape = m.shape();
    // Mixed fragments, and polynomials (a product of two non-constants) for a solver that asks
    // for them. A fragment whose casts hide the mix (`sext(a) + sext(~a)` is a xor, a
    // subtraction and a mask once its sign extensions are written out) is judged without them
    // (see `decast`), as the solver and the certificates read it.
    let mixed = shape.mixed
        || crate::mba::decast(&m).is_some_and(|d| {
            let s = d.shape();
            s.mixed || (s.degree >= 2 && poly)
        });
    if !mixed && !(shape.degree >= 2 && poly) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    if shape.nodes < cfg.limits.min_nodes {
        count(r).refused(&Refusal::TooSmall);
        return Ok(Step::Normal(Fin::FINAL));
    }
    r.meter.charge(Counter::PassWork, u64::from(shape.nodes))?;
    if outgrown(r, cx, root, &bindings) {
        count(r).unsupported += 1;
        return Ok(Step::Normal(Fin::FINAL));
    }
    let inner = r.inner;
    let prover_id = inner.mba.prover.as_ref().map_or("", |p| p.id());
    // The question's content hash, once (it hashes every node).
    let mk = m.key();
    let mut kh = combine(mk[0], mk[1]);
    for b in inner.mba.solver.id().bytes().chain(prover_id.bytes()) {
        kh = combine(kh, u64::from(b));
    }
    // The trust setting is part of the key: an answer accepted on the backend's word or on
    // sampling must never be reused where that evidence is not accepted.
    kh = combine(
        combine(kh, u64::from(cfg.trust.backend_certificates)),
        u64::from(cfg.trust.sampled),
    );
    let key = CacheKey([
        combine(kh, LOWERING_VERSION),
        combine(kh ^ 0x6361_6368, mk[1]),
    ]);
    // An answer the gate could not prove earlier in this call (not for lack of budget): the
    // same question would get the same answer and the same verdict.
    if r.mba_unproved.contains_key(&key) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    // What vouched for the answer (for an explanation): an answer from the cache was proved
    // when it was found.
    let mut evidence: (&'static str, Option<&'static str>, u64) = ("cache", None, 0);
    // The answer, and where it was lifted if it already was.
    let (cand, lifted) = match inner.mba.cache.get(&key) {
        Some(CacheEntry::NoSimpler) => {
            count(r).cache_hits += 1;
            return Ok(Step::Normal(Fin::FINAL));
        }
        Some(CacheEntry::Simplified(e)) if e.vars() == m.vars() => {
            count(r).cache_hits += 1;
            (e, None)
        }
        _ => {
            // A question asked earlier in this call whose answer was not committed then (not
            // smaller, say): the same answer (every answer but running short is complete).
            let answer = match r.mba_answers.get(&key).cloned() {
                Some(a) => {
                    count(r).cache_hits += 1;
                    a
                }
                None => {
                    // The solver works within its own limit and what is left of the run's
                    // account of its steps, and is charged the steps it spent. With nothing
                    // left the question is not asked: over budget, so not final.
                    let limit = cfg.budget.steps.min(r.meter.left_in(|b| b.mba_steps));
                    if limit == 0 {
                        count(r).exhausted += 1;
                        return Ok(Step::Normal(Fin::capped(Exhausted::MbaSteps)));
                    }
                    r.meter.charge(Counter::MbaCalls, 1)?;
                    count(r).calls += 1;
                    // The solver's own evidence counts only where backend certificates are
                    // trusted: elsewhere the gate proves every answer itself.
                    let budget = cfg
                        .budget
                        .with_evidence(cfg.budget.evidence && cfg.trust.backend_certificates)
                        .with_steps(limit);
                    let (a, spent) = inner.mba.solver.solve_counted(&m, &budget);
                    let spent = spent.min(r.meter.left_in(|b| b.mba_steps));
                    r.meter.charge(Counter::MbaSteps, spent)?;
                    if a == MbaAnswer::Exhausted && limit < cfg.budget.steps {
                        // Run short within what the account left it: more budget might
                        // decide.
                        count(r).exhausted += 1;
                        return Ok(Step::Normal(Fin::capped(Exhausted::MbaSteps)));
                    }
                    if a != MbaAnswer::Exhausted {
                        r.mba_answers.insert(key, a.clone());
                    }
                    if matches!(&a, MbaAnswer::Unsupported(why) if why.starts_with("too many")) {
                        r.mba_outgrown.insert(root, ());
                    }
                    a
                }
            };
            match answer {
                MbaAnswer::Simplified { expr, claim } => {
                    if expr.vars() != m.vars() || expr.width() != m.width() {
                        count(r).refuted += 1;
                        return Ok(Step::Normal(Fin::FINAL));
                    }
                    // Always: a cheap refutation check.
                    if !sampled(r, &m, &expr, mk[0])? {
                        count(r).refuted += 1;
                        return Ok(Step::Normal(Fin::FINAL));
                    }
                    // Cheap before expensive: an answer that would not make the DAG smaller is
                    // not worth proving (every check is still required to commit one).
                    let before = cx.len() as u32;
                    let e = r.build(cx, |cx| lift_id(cx, &expr, &bindings))?;
                    if e == n {
                        return Ok(Step::Normal(Fin::FINAL));
                    }
                    if let Err(fin) = shrinks(r, cx, n, e, &bindings.atoms)? {
                        count(r).not_smaller += 1;
                        r.stats.passes.entry("mba").or_default().rejected_cost += 1;
                        discard(r, cx, before);
                        return Ok(Step::Normal(fin));
                    }
                    let own = exact(r, &m, &expr)?;
                    if own.verdict == Verdict::Refuted {
                        count(r).refuted += 1;
                        discard(r, cx, before);
                        return Ok(Step::Normal(Fin::FINAL));
                    }
                    let by =
                        if own.verdict == Verdict::Proved {
                            Some("certificate")
                        } else if inner.mba.prover.as_ref().is_some_and(|p| {
                            p.prove_equal(&m, &expr, &cfg.budget) == Verdict::Proved
                        }) {
                            Some("prover")
                        } else if cfg.trust.backend_certificates && claim >= Claim::Proved {
                            Some("backend")
                        } else if cfg.trust.sampled {
                            Some("sampled")
                        } else {
                            None
                        };
                    let proved = by.is_some();
                    if let Some(by) = by {
                        let test = own
                            .cert
                            .filter(|_| by == "certificate")
                            .map(crate::mba::certify::Cert::name);
                        evidence = (by, test, own.points);
                    }
                    if !proved {
                        count(r).proof_unknown += 1;
                        discard(r, cx, before);
                        // A certificate skipped for lack of budget might decide with more:
                        // not final.
                        let fin = if own.over_budget {
                            Fin::capped(Exhausted::PassWork)
                        } else {
                            r.mba_unproved.insert(key, ());
                            Fin::FINAL
                        };
                        return Ok(Step::Normal(fin));
                    }
                    inner
                        .mba
                        .cache
                        .put(&key, &CacheEntry::Simplified(expr.clone()));
                    (expr, Some((e, before)))
                }
                MbaAnswer::NoSimpler => {
                    count(r).no_simpler += 1;
                    inner.mba.cache.put(&key, &CacheEntry::NoSimpler);
                    return Ok(Step::Normal(Fin::FINAL));
                }
                MbaAnswer::Unsupported(_) => {
                    count(r).unsupported += 1;
                    return Ok(Step::Normal(Fin::FINAL));
                }
                MbaAnswer::Exhausted => {
                    count(r).exhausted += 1;
                    // More budget might succeed: not final.
                    return Ok(Step::Normal(Fin::capped(Exhausted::MbaCalls)));
                }
            }
        }
    };
    let (e, before) = match lifted {
        Some(x) => x,
        None => {
            let before = cx.len() as u32;
            (r.build(cx, |cx| lift_id(cx, &cand, &bindings))?, before)
        }
    };
    // The lifted result must agree with the original term (checks lowering and lifting).
    if e != n {
        r.sample(cx, n)?;
        r.sample(cx, e)?;
        if r.samples[&n] != r.samples[&e] {
            count(r).refuted += 1;
            discard(r, cx, before);
            return Ok(Step::Normal(Fin::FINAL));
        }
    }
    r.explain_with(|| crate::engine::Explanation::Mba {
        atoms: bindings.atoms.iter().map(|&a| cx.handle(a)).collect(),
        evidence: evidence.0,
        test: evidence.1,
        points: evidence.2,
    });
    let out = finish(
        r,
        cx,
        PassKind::Mba,
        n,
        e,
        before,
        &bindings.atoms,
        Fin::FINAL,
    )?;
    if matches!(out, Step::To(..)) {
        count(r).simplified += 1;
    } else if e != n {
        count(r).not_smaller += 1;
    }
    Ok(out)
}
