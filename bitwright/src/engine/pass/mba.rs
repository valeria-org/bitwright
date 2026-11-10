//! The MBA phase: lowering, the solver, the evidence gate, lifting (see [`crate::mba`]).

use super::{Fin, PassKind, Runner, Step, Stop, discard, finish, shrinks};
use crate::engine::Exhausted;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::combine;
use crate::mba::certify;
use crate::mba::{
    Bindings, CacheEntry, CacheKey, Claim, LOWERING_VERSION, MOp, MbaAnswer, MbaConfig, MbaExpr,
    Reading, Refusal, Verdict, lift_id, lower_id, lower_id_over, lower_id_reading, lower_id_whole,
    shared_nodes,
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
    fn new(r: &'x mut Runner<'r, 'a>, a: &MbaExpr, b: &MbaExpr, part: u64) -> Self {
        let limit = r.meter.limit.pass_work;
        let direct = certify::direct_cost(a, b).unwrap_or(0).saturating_mul(2);
        let share = (limit / part)
            .max(GATE_SHARE_MIN / (part / GATE_SHARE))
            .max(direct);
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
fn exact(
    r: &mut Runner<'_, '_>,
    a: &MbaExpr,
    b: &MbaExpr,
    part: u64,
) -> Result<certify::Report, Stop> {
    let report = certify::prove(a, b, &mut Gate::new(r, a, b, part))?;
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
    // For each node, the nodes it or one below it was asked to be related to with no proof
    // found (see `related`).
    let mut unproved: crate::hash::IdMap<u32, Vec<u32>> = crate::hash::IdMap::default();
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
            // What the nodes below this one were not proved related to.
            let mut below: Vec<u32> = Vec::new();
            for c in cx.node(cur).children() {
                for &x in unproved.get(&c).map_or(&[][..], |v| v) {
                    if !below.contains(&x) && below.len() < SWEEP_UNPROVED {
                        below.push(x);
                    }
                }
            }
            if !below.is_empty() {
                unproved.insert(cur, below.clone());
            }
            let reps: Vec<u32> = found.iter().map(|f| f.0).collect();
            for (rep, relation, d) in found {
                // A node below this one was asked to be related to `rep` (or to a node the
                // samples relate to it as they do this one) and no proof was found: this one,
                // built on it, would be asked the same thing through it, and is not. Where
                // `f(a)` could not be proved to be `rep + d`, `g(f(a))` failed for the same
                // reason at the cost of a full certificate (of 5,030 such questions in 140
                // measured calls, 124 had been proved). It counts as a pair left open.
                if below.contains(&rep) {
                    unrelated += 1;
                    break;
                }
                let rep = to.get(&rep).copied().unwrap_or(rep);
                match asked!('nodes, related(r, cx, cfg, cur, rep, relation, &d)) {
                    Related::Proved(e) => {
                        to.insert(i, e);
                        continue 'nodes;
                    }
                    Related::Written => {}
                    Related::Open => {
                        unrelated += 1;
                        let v = unproved.entry(cur).or_default();
                        for &x in &reps {
                            if !v.contains(&x) && v.len() < SWEEP_UNPROVED {
                                v.push(x);
                            }
                        }
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
                rewritten = asked!('nodes, cases_fold(r, cx, cfg, cur, &mut case_attempts)
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
        //
        // And a truncation, for the same: the low bits of a product that only a few bits of
        // its operands reach are a shift count an obfuscator computes, constant where the
        // product is not. Not a slice above the low bits: those are the fields of one value,
        // read together again by what joins them, and with some of them folded and others
        // not, the value under the rest is rewritten on the bits they read and what proved
        // the whole no longer applies (six of 47 measured constants were lost that way).
        let predicate =
            cx.width_of(cur).bits() == 1 || (op == OpCode::Extract && cx.node(cur).b == 0);
        if !all_constant && (!(mixed || predicate) || failures >= SWEEP_FAILURES) {
            continue;
        }
        // Not `k` at an input an earlier candidate differed at: no constant.
        if !all_constant && asked!('nodes, witnessed(r, cx, cur, &k)) {
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
            subject = asked!('nodes, super::demanded::reduced(r, cx, cur, SWEEP_DEMAND_VISITS, true)
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
            (decided, refuted, seen) =
                asked!('nodes, readings_prove(r, cx, cfg, subject, &k, SWEEP_SHARE));
            // The candidate as it is written, where the reduced one was not decided: taking
            // each operand on the bits its user reads writes one value read under several
            // masks once per mask, each a variable of its own, and what the terms cancel
            // through (the one value they all read) is gone.
            if !decided && !refuted && subject != cur {
                let again = asked!('nodes, readings_prove(r, cx, cfg, cur, &k, SWEEP_SHARE));
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
///
/// A sequence is kept as a 128-bit digest of its values, not the values: two sequences that
/// collide name a pair that is not related, which costs the proof that fails and no answer.
#[derive(Default)]
struct Classes {
    sums: crate::hash::IdMap<[u64; 2], Vec<(u32, crate::BitVec)>>,
    xors: crate::hash::IdMap<[u64; 2], (u32, crate::BitVec)>,
}

impl Classes {
    fn key(vals: &[crate::BitVec], op: BinOp, flip: bool) -> [u64; 2] {
        let first = &vals[0];
        let mut h = [u64::from(first.width().bits()), 0x9e37_79b9_7f4a_7c15];
        for v in vals {
            let d = match flip {
                false => crate::BitVec::bin_unchecked(op, v, first),
                true => crate::BitVec::bin_unchecked(op, first, v),
            };
            for &l in d.limbs() {
                h[0] = combine(h[0], l);
                h[1] = combine(h[1] ^ l, h[0]);
            }
        }
        h
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
    if witnessed(r, cx, diff, &zero)? {
        return Ok(Related::Open);
    }
    let whole_sums = relation != Relation::Xor;
    let subject = super::demanded::reduced(r, cx, diff, SWEEP_DEMAND_VISITS, whole_sums)?;
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
    let (decided, _, _) = readings_prove(r, cx, cfg, subject, &zero, SWEEP_SHARE)?;
    if decided {
        count(r).opaque_proved += 1;
        return Ok(Related::Proved(e));
    }
    Ok(Related::Open)
}

/// The most nodes kept per node of those it was not proved related to (see `sweep_inner`).
const SWEEP_UNPROVED: usize = 8;

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
/// certificates are, within [`EXHAUSTIVE_SHARE`], for the points it evaluates: an enumeration
/// that would not fit is not begun, and one that meets a difference stops there. `None` when it
/// does not apply or would cost more.
fn exhaustive(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    k: &crate::BitVec,
) -> Result<Option<bool>, Stop> {
    // The call's buffers, taken for the decision (nothing below asks another).
    let mut sc = std::mem::take(&mut r.exhaust);
    let out = exhaustive_in(r, cx, &mut sc, root, k);
    r.exhaust = sc;
    out
}

/// [`exhaustive`], over the call's buffers.
fn exhaustive_in(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    sc: &mut Exhaust,
    root: u32,
    k: &crate::BitVec,
) -> Result<Option<bool>, Stop> {
    use crate::BitVec;
    // The DAG below `root`, operands first, every node at most 64 bits; and the bits of each
    // node that reach the root, from the root down.
    let swept = sc.sweep(cx, root);
    match swept {
        Swept::Wide | Swept::Open => return Ok(None),
        // Not met with (a node is made after its operands): the same by a walk from the root.
        Swept::Unordered => {
            if !sc.walk(cx, root) {
                return Ok(None);
            }
            sc.demands(cx);
        }
        Swept::Whole => {}
    }
    let total: u32 = sc.syms.iter().map(|(_, m)| m.count_ones()).sum();
    // The points of an enumeration over several symbols are numbered by the symbols' bits in
    // the order a walk from the root meets the symbols.
    if total <= EXHAUSTIVE_BITS && swept == Swept::Whole && sc.syms.len() > 1 {
        sc.walk(cx, root);
        sc.demands(cx);
    }
    // Too many symbol bits: places every demanded path from them passes through, with few
    // bits of their own, are enumerated instead. First one place, over the values the bits
    // known of it leave; then, where the root differs at one of those (a value the place may
    // never take), several places nearer the symbols.
    if total > EXHAUSTIVE_BITS {
        let one = bottleneck(&sc.below, &sc.demand, &mut sc.live, &mut sc.over);
        if let Some(c) = one {
            // Over the values it can take: the bits known of it are those values' (a sum
            // that is constant only for them is constant), and a value it never takes
            // refutes nothing.
            let [z, o] = super::known_words(r, cx, sc.order[c])?.0.unwrap_or([0, 0]);
            sc.syms.clear();
            sc.syms.push((c as u32, sc.demand[c] & !(z | o)));
            sc.bases.clear();
            sc.bases.push(o & sc.demand[c]);
            sc.above(Some(c));
            match enumerated(r, cx, sc, k)? {
                Some(None) => return Ok(Some(true)),
                Some(Some(_)) => {}
                None => return Ok(None),
            }
        }
        let Some(mut front) = frontier(&sc.below, &sc.demand, &mut sc.over) else {
            return Ok(None);
        };
        // The one place again: no more an answer.
        if let ([(p, _)], Some(c)) = (&front[..], one)
            && *p as usize == c
        {
            return Ok(None);
        }
        sc.bases.clear();
        for (p, m) in front.iter_mut() {
            let [z, o] = match sc.below[*p as usize].0.op {
                OpCode::Sym => [0, 0],
                _ => super::known_words(r, cx, sc.order[*p as usize])?
                    .0
                    .unwrap_or([0, 0]),
            };
            sc.bases.push(o & *m);
            *m &= !(z | o);
        }
        sc.syms = front;
        sc.above_inputs();
        // A value the root differs at: of places that may not take it together, no answer.
        return Ok(match enumerated(r, cx, sc, k)? {
            Some(None) => Some(true),
            _ => None,
        });
    }
    sc.bases.clear();
    sc.above(None);
    let Some(missed) = enumerated(r, cx, sc, k)? else {
        return Ok(None);
    };
    let Some(p) = missed else {
        return Ok(Some(true));
    };
    // The symbols' values there are an input the root is not `k` at: kept, for the candidates
    // after this one that differ there too (an obfuscator builds one value from another, and
    // a chain of them that are `k` but for one value of a 16-bit field was enumerated up to
    // that value at every link).
    let mut left = p;
    let fixed = sc
        .syms
        .iter()
        .map(|&(place, m)| {
            let s = sc.order[place as usize];
            let v = spread(&mut left, m);
            (s, BitVec::wrapping_from_u64(cx.width_of(s), v))
        })
        .collect();
    note_witness(r, cx, fixed);
    // A value of the symbols the root differs at: a refutation.
    Ok(Some(false))
}

/// The enumeration of [`exhaustive`] over the places of `sc.syms`, each at its base (of
/// `sc.bases`, zero where there is none) with every value of its bits there, of the places
/// `sc.kept`: the first point the root is not `k` at (`Some(None)` when it is `k` at all of
/// them), or `None` when the points would cost more than [`EXHAUSTIVE_SHARE`] or the steps
/// left.
fn enumerated(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    sc: &mut Exhaust,
    k: &crate::BitVec,
) -> Result<Option<Option<u64>>, Stop> {
    use crate::BitVec;
    let total: u32 = sc.syms.iter().map(|(_, m)| m.count_ones()).sum();
    let points = 1u64 << total;
    let word = sc.program(cx);
    // A word program's evaluation costs a fraction of a generic one's (measured, see
    // [`WORD_EVALS`]); charged as that many generic evaluations.
    let rate = if word { WORD_EVALS } else { 1 };
    let len = sc.kept.len();
    let cost = |n: u64| n.saturating_mul(len as u64).div_ceil(rate);
    let mut meter = Steps::new(r, EXHAUSTIVE_SHARE);
    if cost(points) > certify::Meter::left(&meter) {
        return Ok(None);
    }
    let ku = k.to_u64();
    // The point the enumeration ended at, where the root differs.
    let missed = if word {
        sc.lanes_for(points);
        first_miss(&mut meter, total, &cost, |span| {
            Ok(match span {
                Span::At(points) => sc.miss_at(points, ku),
                Span::From(start, count) => sc.miss_from(start, count, ku),
            })
        })
    } else {
        let sc = &*sc;
        let mut vals: Vec<BitVec> = vec![BitVec::zero(crate::Width::W1); len];
        // Whether the root is `k` at point `p`, its bits spread over each input's bits that
        // reach the root.
        let mut agrees = |p: u64| -> Result<bool, Stop> {
            let mut left = p;
            for (j, &(place, m)) in sc.syms.iter().enumerate() {
                let v = sc.bases.get(j).copied().unwrap_or(0) | spread(&mut left, m);
                let s = sc.order[place as usize];
                vals[sc.slot[place as usize] as usize] =
                    BitVec::wrapping_from_u64(cx.width_of(s), v);
            }
            for (slot, &place) in sc.kept.iter().enumerate() {
                if sc.input[place as usize] {
                    continue;
                }
                // A symbol that is no input: zero, as in the word program.
                vals[slot] = cx
                    .eval_node(
                        sc.order[place as usize],
                        |j| vals[sc.slot[sc.place[j as usize] as usize] as usize],
                        |_, w| Some(BitVec::zero(w)),
                    )
                    .map_err(Stop::Error)?;
            }
            Ok(vals[len - 1] == *k)
        };
        first_miss(&mut meter, total, &cost, |span| {
            match span {
                Span::At(points) => {
                    for &p in points {
                        if !agrees(p)? {
                            return Ok(Some(p));
                        }
                    }
                }
                Span::From(start, count) => {
                    for p in start..start + count {
                        if !agrees(p)? {
                            return Ok(Some(p));
                        }
                    }
                }
            }
            Ok(None)
        })
    };
    Ok(Some(missed?))
}

/// The low bits of `left`, one for each bit of `m` from its lowest, at `m`'s bits; they are
/// taken from `left`.
fn spread(left: &mut u64, m: u64) -> u64 {
    let (mut v, mut mm) = (0u64, m);
    while mm != 0 {
        if *left & 1 == 1 {
            v |= mm & mm.wrapping_neg();
        }
        *left >>= 1;
        mm &= mm - 1;
    }
    v
}

/// The points [`first_miss`] asks about at once: the ones listed, or `.1` of them from `.0` up.
enum Span<'a> {
    At(&'a [u64]),
    From(u64, u64),
}

/// The first point of [`exhaustive`]'s enumeration of `2^total` that `miss` finds in a span
/// (the first of the span the root is not `k` at), each span charged to `meter` by `cost`
/// before it is asked about.
fn first_miss(
    meter: &mut Steps<'_, '_, '_>,
    total: u32,
    cost: &dyn Fn(u64) -> u64,
    mut miss: impl FnMut(Span<'_>) -> Result<Option<u64>, Stop>,
) -> Result<Option<u64>, Stop> {
    let points = 1u64 << total;
    let mut missed: Option<u64> = None;
    // The points a candidate that is not `k` most often differs at, before the enumeration is
    // paid for: each bit alone, all of them, and a few mixed. The samples leave candidates that
    // are `k` unless some one bit is set, and counting up from zero reaches an input's top bit
    // only at half the points (87 of 98 enumerations in one measured question ended there, and
    // were four fifths of its sweep's steps).
    if total > EXHAUSTIVE_SCREEN_BITS {
        let mixed = (1..=EXHAUSTIVE_MIXED)
            .map(|j: u64| j.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> (64 - total));
        let mut probes = [0u64; (EXHAUSTIVE_BITS as usize) + 1 + (EXHAUSTIVE_MIXED as usize)];
        let mut count = 0usize;
        for p in (0..total)
            .map(|j| 1u64 << j)
            .chain(std::iter::once(points - 1))
            .chain(mixed)
        {
            probes[count] = p;
            count += 1;
        }
        certify::Meter::charge(meter, cost(u64::from(total) + 1 + EXHAUSTIVE_MIXED))?;
        missed = miss(Span::At(&probes[..count]))?;
    }
    let mut start = 0u64;
    while missed.is_none() && start < points {
        let n = EXHAUSTIVE_BLOCK.min(points - start);
        certify::Meter::charge(meter, cost(n))?;
        missed = miss(Span::From(start, n))?;
        start += n;
    }
    Ok(missed)
}

/// An input at which a candidate of the opaque-constant sweep was found to differ from what
/// its samples showed: the symbols it fixes (every other symbol has its value at one of the
/// verification points), and the nodes evaluated at it so far. The samples are few, and a value
/// that is constant but for one input of `2^16` is constant on all of them; what tells it
/// from a constant is that input, and it tells the same of every node built on that value.
#[derive(Default)]
pub(crate) struct Witness {
    fixed: crate::hash::IdMap<u32, crate::BitVec>,
    point: usize,
    vals: crate::hash::IdMap<u32, crate::BitVec>,
}

/// The most witnesses a call keeps.
const WITNESSES: usize = 32;

/// Keeps the input that gives the symbols `fixed` their values there as a witness of the call.
fn note_witness(r: &mut Runner<'_, '_>, cx: &Context, fixed: Vec<(u32, crate::BitVec)>) {
    if r.witnesses.len() >= WITNESSES {
        return;
    }
    // A symbol's value agrees with what the host declared of it, as its samples do.
    let fixed: crate::hash::IdMap<u32, crate::BitVec> = fixed
        .into_iter()
        .map(|(s, v)| (s, cx.declared_at(s).map_or(v, |d| d.fit(&v))))
        .collect();
    if r.witnesses.iter().any(|w| w.fixed == fixed) {
        return;
    }
    r.witnesses.push(Witness {
        fixed,
        point: 2 + r.witnesses.len(),
        vals: crate::hash::IdMap::default(),
    });
}

/// Whether `n` is not `k` at one of the call's witnesses (each node is evaluated once at
/// each, charged as pass work).
fn witnessed(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    k: &crate::BitVec,
) -> Result<bool, Stop> {
    for w in 0..r.witnesses.len() {
        let mut wit = std::mem::take(&mut r.witnesses[w]);
        let mut work = 0u64;
        let mut out = Ok(());
        let mut stack: Vec<(u32, bool)> = vec![(n, false)];
        while let Some((i, expanded)) = stack.pop() {
            if wit.vals.contains_key(&i) {
                continue;
            }
            if !expanded {
                stack.push((i, true));
                for c in cx.node(i).children() {
                    if !wit.vals.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
                continue;
            }
            work += 1;
            let v = match wit.fixed.get(&i) {
                Some(v) => Ok(*v),
                None => {
                    let seed = cx.meta[i as usize].shash;
                    let declared = cx.declared_at(i);
                    cx.eval_node(
                        i,
                        |j| wit.vals[&j],
                        |_, w| {
                            let v = crate::engine::point_value(seed, w, wit.point);
                            Some(declared.map_or(v, |d| d.fit(&v)))
                        },
                    )
                }
            };
            match v {
                Ok(v) => {
                    wit.vals.insert(i, v);
                }
                Err(e) => {
                    out = Err(Stop::Error(e));
                    break;
                }
            }
        }
        let differs = wit.vals.get(&n).is_some_and(|v| v != k);
        r.witnesses[w] = wit;
        r.meter.charge(Counter::PassWork, work)?;
        out?;
        if differs {
            return Ok(true);
        }
    }
    Ok(false)
}

/// The fewest bits [`exhaustive`] screens an enumeration of (fewer are as cheap to enumerate).
const EXHAUSTIVE_SCREEN_BITS: u32 = 6;

/// The mixed points of [`exhaustive`]'s screen.
const EXHAUSTIVE_MIXED: u64 = 16;

/// The points [`exhaustive`] is charged for at a time.
const EXHAUSTIVE_BLOCK: u64 = 1 << 10;

/// No place: of a node that is not evaluated.
const NO_PLACE: u32 = u32::MAX;

/// A node of the DAG below [`exhaustive`]'s root, with its operands' places in that DAG's order.
type Placed = (crate::expr::Node, [u32; 3]);

/// [`exhaustive`]'s working storage, the call's. A sweep asks it of thousands of candidates
/// over one DAG, each time of the DAG below the candidate, and most enumerate nothing: tables
/// keyed by node, built for each, were most of what those cost. What is kept per node while the
/// DAG is read is in tables over the arena that are left clear (or stamped, never cleared), and
/// everything after is indexed by a node's place among those read.
#[derive(Default)]
pub(crate) struct Exhaust {
    /// Per arena node: whether the sweep under way has met it and not yet reached it (a bit
    /// each, and a bit for each word of those that has one set), and the bits of it found to
    /// reach the root so far. All zero between sweeps.
    marks: Vec<u64>,
    heads: Vec<u64>,
    reach: Vec<u64>,
    /// Per arena node: its place in `order`, of the nodes in it.
    place: Vec<u32>,
    /// Per arena node: the walk that met it last.
    met: Vec<u32>,
    walk: u32,
    stack: Vec<(u32, bool)>,
    /// The DAG below the root, operands first (the root last).
    order: Vec<u32>,
    /// Each node of `order`, with its operands' places.
    below: Vec<Placed>,
    /// The bits of each that reach the root.
    demand: Vec<u64>,
    /// The places enumerated (the symbols, a bottleneck, or a cut of several places), with the
    /// bits enumerated of each; and for each, the bits set in every value enumerated of it
    /// (none, for all zero).
    syms: Vec<(u32, u64)>,
    bases: Vec<u64>,
    /// Of [`bottleneck`]: whether a place is on a demanded path from a symbol to the root, and
    /// the steps of those paths that begin to pass over places at each place, less those that
    /// cease to.
    live: Vec<bool>,
    over: Vec<u32>,
    /// The places evaluated (all, or those the root reads without passing below a
    /// bottleneck), and each place's index among them ([`NO_PLACE`] of the others).
    kept: Vec<u32>,
    slot: Vec<u32>,
    /// Whether a place is enumerated.
    input: Vec<bool>,
    /// The places evaluated as a program over words (see [`Exhaust::program`]).
    prog: Vec<Ins>,
    /// Per place evaluated: whether its value is the same at every point (1; 2 when an
    /// instruction reads it as lanes), and the value.
    fixed: Vec<(u8, u64)>,
    /// Per place evaluated: the place whose lanes hold its values (its own, or those of the
    /// operand it is at every point: a zero extension's), and the root's.
    home: Vec<u32>,
    root: usize,
    /// The places enumerated that take more than one value: index among those evaluated, the
    /// bits enumerated and the bits set in every value.
    inputs: Vec<(u32, u64, u64)>,
    /// For each of `inputs`, its bits at the first `most` points.
    spreads: Vec<u64>,
    /// The values of every place evaluated at the `width` points of a pass, a place's side by
    /// side; `most` is the widest pass of the enumeration under way.
    lanes: Vec<u64>,
    width: usize,
    most: usize,
}

/// What [`Exhaust::sweep`] came to.
#[derive(PartialEq)]
enum Swept {
    /// The whole DAG.
    Whole,
    /// A node of more than 64 bits.
    Wide,
    /// More bits of the symbols than are enumerated, and no bottleneck.
    Open,
    /// An operand numbered after its user.
    Unordered,
}

/// The bits of each operand of `n` that reach its bits `m` (a superset; of the operand's width
/// or more), given to `give` by the operand's index. `konst` is an operand's value where it is
/// a constant, `wide` its width.
fn demanded(
    n: &crate::expr::Node,
    m: u64,
    konst: impl Fn(usize) -> Option<u64>,
    wide: impl Fn(usize) -> u16,
    mut give: impl FnMut(usize, u64),
) {
    let ones = |w: u16| if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let w = n.width;
    let low_prefix = ones(64 - m.leading_zeros() as u16);
    match n.op {
        OpCode::And | OpCode::Or => {
            for (c, o) in [(0, 1), (1, 0)] {
                let d = match (konst(o), n.op) {
                    (Some(k), OpCode::And) => m & k,
                    (Some(k), _) => m & !k,
                    _ => m,
                };
                give(c, d);
            }
        }
        OpCode::Xor => {
            give(0, m);
            give(1, m);
        }
        OpCode::Not => give(0, m),
        OpCode::Add | OpCode::Sub | OpCode::Mul => {
            give(0, low_prefix);
            give(1, low_prefix);
        }
        OpCode::Neg => give(0, low_prefix),
        OpCode::Shl | OpCode::LShr if konst(1).is_some_and(|s| s < u64::from(w)) => {
            let s = konst(1).unwrap_or(0);
            give(
                0,
                if n.op == OpCode::Shl {
                    m >> s
                } else {
                    (m << s) & ones(w)
                },
            );
            give(1, u64::MAX);
        }
        OpCode::Zext => give(0, m),
        // A `select` reads its condition, and of its arms the bits read of it.
        OpCode::Select => {
            give(0, 1);
            give(1, m);
            give(2, m);
        }
        OpCode::Extract => give(0, m << n.b),
        // a rotate by a constant moves the demand the other way; a `concat`
        // splits it between its halves.
        OpCode::RotL | OpCode::RotR if konst(1).is_some() && w <= 64 && w > 0 => {
            let s = (konst(1).unwrap_or(0) % u64::from(w)) as u32;
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
            give(0, rot(m, s, n.op == OpCode::RotR));
            give(1, u64::MAX);
        }
        OpCode::Concat => {
            let wl = wide(1);
            give(1, m & ones(wl));
            give(0, if wl >= 64 { 0 } else { m >> wl });
        }
        _ => {
            for j in 0..n.op.arity() {
                give(j, u64::MAX);
            }
        }
    }
}

/// The value of a constant node of at most 64 bits (which is stored in the node).
fn word_of(cx: &Context, i: u32, n: &crate::expr::Node) -> Option<u64> {
    if n.op != OpCode::Const {
        return None;
    }
    if n.aux & crate::expr::AUX_POOLED != 0 {
        return cx.const_val(i).and_then(|v| v.to_u64());
    }
    Some(u64::from(n.a) | (u64::from(n.b) << 32))
}

impl Exhaust {
    /// The DAG below `root` into `order` and `below`, operands first, with the bits of each
    /// node that reach the root in `demand`, and the symbols with theirs. A node is numbered
    /// after its operands, so from the highest number down every node comes after its users,
    /// with all the bits they read of it: one pass, no walk. Stops short at a node of more than
    /// 64 bits, and where no enumeration can follow: more than [`EXHAUSTIVE_BITS`] bits of the
    /// symbols already reach the root, and no node reached so far but the root has as few of
    /// its own. (A [`bottleneck`] is such a node on every demanded path from the symbols to the
    /// root; a node not yet reached is not on the path that gave a symbol its bits.)
    fn sweep(&mut self, cx: &Context, root: u32) -> Swept {
        let ones = |w: u16| if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
        let len = cx.nodes.len();
        if self.reach.len() < len {
            self.reach.resize(len, 0);
            self.place.resize(len, 0);
            self.marks.resize(len.div_ceil(64), 0);
            self.heads.resize(len.div_ceil(64).div_ceil(64), 0);
        }
        let Exhaust {
            marks,
            heads,
            reach,
            place,
            order,
            below,
            demand,
            syms,
            ..
        } = self;
        order.clear();
        below.clear();
        demand.clear();
        syms.clear();
        // The highest node marked at or below word `at`, unmarked.
        fn next(marks: &mut [u64], heads: &mut [u64], at: &mut usize) -> u32 {
            if marks[*at] == 0 {
                let mut h = *at / 64;
                let mut word = heads[h] & (u64::MAX >> (63 - *at % 64));
                while word == 0 {
                    h -= 1;
                    word = heads[h];
                }
                *at = h * 64 + 63 - word.leading_zeros() as usize;
            }
            let bit = 63 - marks[*at].leading_zeros();
            marks[*at] &= !(1u64 << bit);
            if marks[*at] == 0 {
                heads[*at / 64] &= !(1u64 << (*at % 64));
            }
            (*at * 64) as u32 + bit
        }
        let mut at = root as usize / 64;
        marks[at] |= 1u64 << (root % 64);
        heads[at / 64] |= 1u64 << (at % 64);
        reach[root as usize] = ones(cx.node(root).width);
        // The nodes marked, the symbols' bits that reach the root so far, and whether a node
        // that could be a bottleneck was met.
        let (mut marked, mut bits, mut narrow) = (1usize, 0u32, false);
        let mut out = Swept::Whole;
        'nodes: while marked > 0 {
            let i = next(marks, heads, &mut at);
            marked -= 1;
            let n = cx.node(i);
            let m = std::mem::take(&mut reach[i as usize]);
            if n.width > 64 {
                out = Swept::Wide;
                break;
            }
            order.push(i);
            below.push((n, [0; 3]));
            demand.push(m);
            let kids = [n.a, n.b, n.c];
            let arity = n.op.arity();
            for &c in &kids[..arity] {
                if c >= i {
                    out = Swept::Unordered;
                    break 'nodes;
                }
                let (word, bit) = (c as usize / 64, 1u64 << (c % 64));
                marked += usize::from(marks[word] & bit == 0);
                marks[word] |= bit;
                heads[word / 64] |= 1u64 << (word % 64);
            }
            if m == 0 || arity == 0 {
                continue;
            }
            narrow |= i != root && m.count_ones() <= EXHAUSTIVE_BITS;
            demanded(
                &n,
                m,
                |j| word_of(cx, kids[j], &cx.node(kids[j])),
                |j| cx.node(kids[j]).width,
                |j, d| {
                    let c = cx.node(kids[j]);
                    let had = reach[kids[j] as usize];
                    let now = had | (d & ones(c.width));
                    if c.op == OpCode::Sym {
                        bits += now.count_ones() - had.count_ones();
                    }
                    reach[kids[j] as usize] = now;
                },
            );
            if bits > EXHAUSTIVE_BITS && !narrow {
                out = Swept::Open;
                break;
            }
        }
        while marked > 0 {
            let i = next(marks, heads, &mut at);
            reach[i as usize] = 0;
            marked -= 1;
        }
        if out != Swept::Whole {
            return out;
        }
        order.reverse();
        below.reverse();
        demand.reverse();
        for (p, &i) in order.iter().enumerate() {
            place[i as usize] = p as u32;
        }
        for (p, (n, kids)) in below.iter_mut().enumerate() {
            for (k, c) in n.children().enumerate() {
                kids[k] = place[c as usize];
            }
            if n.op == OpCode::Sym {
                syms.push((p as u32, demand[p]));
            }
        }
        out
    }

    /// The DAG below `root` into `order` and `below`, operands first, in the order a walk from
    /// the root leaves its nodes; `false` at a node of more than 64 bits.
    fn walk(&mut self, cx: &Context, root: u32) -> bool {
        if self.met.len() < cx.nodes.len() {
            self.met.resize(cx.nodes.len(), 0);
        }
        if self.place.len() < cx.nodes.len() {
            self.place.resize(cx.nodes.len(), 0);
        }
        self.walk = self.walk.wrapping_add(1);
        if self.walk == 0 {
            self.met.fill(0);
            self.walk = 1;
        }
        let walk = self.walk;
        self.order.clear();
        self.below.clear();
        self.stack.clear();
        self.stack.push((root, false));
        while let Some((i, expanded)) = self.stack.pop() {
            let n;
            if expanded {
                n = cx.node(i);
            } else {
                if self.met[i as usize] == walk {
                    continue;
                }
                self.met[i as usize] = walk;
                n = cx.node(i);
                if n.width > 64 {
                    return false;
                }
                if n.op.arity() != 0 {
                    self.stack.push((i, true));
                    for c in n.children() {
                        if self.met[c as usize] != walk {
                            self.stack.push((c, false));
                        }
                    }
                    continue;
                }
            }
            let mut kids = [0u32; 3];
            for (k, c) in n.children().enumerate() {
                kids[k] = self.place[c as usize];
            }
            self.place[i as usize] = self.order.len() as u32;
            self.order.push(i);
            self.below.push((n, kids));
        }
        true
    }

    /// The bits of each node of a [`walk`](Exhaust::walk) that reach the root, from the root
    /// down, and the symbols with theirs.
    fn demands(&mut self, cx: &Context) {
        let ones = |w: u16| if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
        let (order, below, demand) = (&self.order, &self.below, &mut self.demand);
        let last = below.len() - 1;
        demand.clear();
        demand.resize(below.len(), 0);
        demand[last] = ones(below[last].0.width);
        for idx in (0..=last).rev() {
            let m = demand[idx];
            if m == 0 {
                continue;
            }
            let (n, kids) = &below[idx];
            demanded(
                n,
                m,
                |j| word_of(cx, order[kids[j] as usize], &below[kids[j] as usize].0),
                |j| below[kids[j] as usize].0.width,
                |j, d| demand[kids[j] as usize] |= d & ones(below[kids[j] as usize].0.width),
            );
        }
        self.syms.clear();
        for (idx, (n, _)) in below.iter().enumerate() {
            if n.op == OpCode::Sym {
                self.syms.push((idx as u32, demand[idx]));
            }
        }
    }

    /// The places evaluated into `kept` and `slot`: every place, or with a bottleneck at `cut`
    /// the ones the root reads without passing below it.
    fn above(&mut self, cut: Option<usize>) {
        let n = self.below.len();
        self.kept.clear();
        self.slot.clear();
        let Some(cut) = cut else {
            self.kept.extend(0..n as u32);
            self.slot.extend(0..n as u32);
            return;
        };
        // Users first: a place read is marked before it is reached.
        self.slot.resize(n, NO_PLACE);
        self.slot[n - 1] = 0;
        for p in (0..n).rev() {
            if self.slot[p] == NO_PLACE || p == cut {
                continue;
            }
            let (node, kids) = self.below[p];
            for &c in &kids[..node.op.arity()] {
                self.slot[c as usize] = 0;
            }
        }
        for p in 0..n {
            if self.slot[p] != NO_PLACE {
                self.slot[p] = self.kept.len() as u32;
                self.kept.push(p as u32);
            }
        }
    }

    /// [`above`](Exhaust::above) with the places of `syms` for the cut (see [`frontier`]): the
    /// places the root reads without passing below one of them.
    fn above_inputs(&mut self) {
        let n = self.below.len();
        self.kept.clear();
        self.slot.clear();
        self.input.clear();
        self.input.resize(n, false);
        for &(p, _) in &self.syms {
            self.input[p as usize] = true;
        }
        self.slot.resize(n, NO_PLACE);
        self.slot[n - 1] = 0;
        for p in (0..n).rev() {
            if self.slot[p] == NO_PLACE || self.input[p] {
                continue;
            }
            let (node, kids) = self.below[p];
            for &c in &kids[..node.op.arity()] {
                self.slot[c as usize] = 0;
            }
        }
        for p in 0..n {
            if self.slot[p] != NO_PLACE {
                self.slot[p] = self.kept.len() as u32;
                self.kept.push(p as u32);
            }
        }
    }

    /// The places evaluated (operands first, every node at most 64 bits) as a program over
    /// `u64` words, each instruction with its node's width mask; `false` when an operator is
    /// not one it evaluates. A place enumerated is given its words before each run; a value
    /// that is the same at every point (a constant, a symbol past a bottleneck, a place
    /// enumerated with no bit unknown, which is its base) is an instruction's operand where the
    /// instruction has a form that takes one, and is written out once otherwise.
    fn program(&mut self, cx: &Context) -> bool {
        use crate::{BinOp, CmpOp, UnOp};
        let ones = |w: u16| if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
        let Exhaust {
            order,
            below,
            syms,
            bases,
            kept,
            slot,
            input,
            prog,
            fixed,
            home,
            inputs,
            ..
        } = self;
        prog.clear();
        inputs.clear();
        fixed.clear();
        fixed.resize(kept.len(), (0, 0));
        home.clear();
        home.extend(0..kept.len() as u32);
        input.clear();
        input.resize(below.len(), false);
        for (j, &(p, m)) in syms.iter().enumerate() {
            input[p as usize] = true;
            let s = slot[p as usize];
            let base = bases.get(j).copied().unwrap_or(0);
            if m == 0 {
                fixed[s as usize] = (1, base);
            } else {
                inputs.push((s, m, base));
            }
        }
        // An operand read as lanes: one that is the same at every point is written out.
        fn lane(fixed: &mut [(u8, u64)], s: u32) -> u32 {
            if fixed[s as usize].0 == 1 {
                fixed[s as usize].0 = 2;
            }
            s
        }
        let known = |fixed: &[(u8, u64)], s: u32| {
            let (is, v) = fixed[s as usize];
            (is != 0).then_some(v)
        };
        for (s, &p) in kept.iter().enumerate() {
            if input[p as usize] {
                continue;
            }
            let (n, kids) = below[p as usize];
            let (w, mask) = (u32::from(n.width), ones(n.width));
            if w == 0 {
                return false;
            }
            let wide = |j: usize| below[kids[j] as usize].0.width;
            let arg = |j: usize| home[slot[kids[j] as usize] as usize];
            // A node that is its operand `j` at every point: the operand's lanes, or its value.
            macro_rules! same {
                ($j:expr) => {{
                    let a = arg($j);
                    match known(fixed, a) {
                        Some(v) => fixed[s] = (1, v),
                        None => home[s] = a,
                    }
                    continue;
                }};
            }
            let ins = |kind: Kind, sh: u32, a: u32, b: u32, c: u32, k: u64| Ins {
                kind,
                sh,
                dst: s as u32,
                a,
                b,
                c,
                mask,
                k,
            };
            let one = |fixed: &mut [(u8, u64)], kind: Kind, sh: u32, k: u64| {
                ins(kind, sh, lane(fixed, arg(0)), 0, 0, k)
            };
            let two = |fixed: &mut [(u8, u64)], kind: Kind, sh: u32| {
                ins(kind, sh, lane(fixed, arg(0)), lane(fixed, arg(1)), 0, 0)
            };
            let i = match n.op {
                // A symbol past a bottleneck cut that is no input reaches the root only through
                // a node with no demanded bits: any value, zero as the uncut enumeration gives it.
                OpCode::Sym => {
                    fixed[s] = (1, 0);
                    continue;
                }
                OpCode::Const => {
                    let Some(v) = word_of(cx, order[p as usize], &n) else {
                        return false;
                    };
                    fixed[s] = (1, v & mask);
                    continue;
                }
                OpCode::Zext => same!(0),
                OpCode::Sext => one(fixed, Kind::Sext, u32::from(wide(0)), 0),
                OpCode::Extract => one(fixed, Kind::Extract, u32::from(n.b as u16), 0),
                OpCode::Select => {
                    let (c, t, f) = (
                        lane(fixed, arg(0)),
                        lane(fixed, arg(1)),
                        lane(fixed, arg(2)),
                    );
                    ins(Kind::Select, 0, c, t, f, 0)
                }
                // `concat(hi, lo)`, shifted by the low half's width.
                OpCode::Concat if wide(1) >= 64 => same!(1),
                OpCode::Concat => two(fixed, Kind::Concat, u32::from(wide(1))),
                op => {
                    if let Some(u) = op.as_un() {
                        match u {
                            UnOp::Not => one(fixed, Kind::Not, 0, 0),
                            UnOp::Neg => one(fixed, Kind::Neg, 0, 0),
                            _ => return false,
                        }
                    } else if let Some(b) = op.as_bin() {
                        let (x, y) = (known(fixed, arg(0)), known(fixed, arg(1)));
                        // The other operand's lanes, with the known one as the instruction's.
                        let with = |fixed: &mut [(u8, u64)], kind: Kind, plain: Kind| match (x, y) {
                            (_, Some(y)) => ins(kind, 0, lane(fixed, arg(0)), 0, 0, y),
                            (Some(x), _) => ins(kind, 0, lane(fixed, arg(1)), 0, 0, x),
                            _ => two(fixed, plain, 0),
                        };
                        match (b, y) {
                            (BinOp::Add, _) => with(fixed, Kind::AddK, Kind::Add),
                            (BinOp::Mul, _) => with(fixed, Kind::MulK, Kind::Mul),
                            (BinOp::And, _) => with(fixed, Kind::AndK, Kind::And),
                            (BinOp::Or, _) => with(fixed, Kind::OrK, Kind::Or),
                            (BinOp::Xor, _) => with(fixed, Kind::XorK, Kind::Xor),
                            (BinOp::Sub, Some(y)) => one(fixed, Kind::AddK, 0, y.wrapping_neg()),
                            (BinOp::Sub, None) => match x {
                                Some(x) => ins(Kind::RSubK, 0, lane(fixed, arg(1)), 0, 0, x),
                                None => two(fixed, Kind::Sub, 0),
                            },
                            // A count of the width or more leaves nothing.
                            (BinOp::Shl | BinOp::LShr, Some(y)) if y >= u64::from(w) => {
                                fixed[s] = (1, 0);
                                continue;
                            }
                            (BinOp::Shl, Some(y)) => one(fixed, Kind::ShlK, y as u32, 0),
                            (BinOp::LShr, Some(y)) => one(fixed, Kind::LShrK, y as u32, 0),
                            (BinOp::AShr, Some(y)) => {
                                one(fixed, Kind::AShrK, y.min(u64::from(w) - 1) as u32, 0)
                            }
                            (BinOp::RotL | BinOp::RotR, Some(y)) => {
                                let by = (y % u64::from(w)) as u32;
                                let by = if b == BinOp::RotR { (w - by) % w } else { by };
                                match by {
                                    0 => same!(0),
                                    _ => one(fixed, Kind::RotK, by, 0),
                                }
                            }
                            (BinOp::Shl, None) => two(fixed, Kind::Shl, 0),
                            (BinOp::LShr, None) => two(fixed, Kind::LShr, 0),
                            (BinOp::AShr, None) => two(fixed, Kind::AShr, 0),
                            (BinOp::RotL, None) => two(fixed, Kind::RotL, 0),
                            (BinOp::RotR, None) => two(fixed, Kind::RotR, 0),
                            _ => return false,
                        }
                    } else {
                        let Some(c) = op.as_cmp() else {
                            return false;
                        };
                        let (x, y) = (known(fixed, arg(0)), known(fixed, arg(1)));
                        let wa = u32::from(wide(0));
                        match (c, x, y) {
                            (CmpOp::Eq, _, Some(y)) => one(fixed, Kind::EqK, 0, y),
                            (CmpOp::Ne, _, Some(y)) => one(fixed, Kind::NeK, 0, y),
                            (CmpOp::Eq, Some(x), _) => {
                                ins(Kind::EqK, 0, lane(fixed, arg(1)), 0, 0, x)
                            }
                            (CmpOp::Ne, Some(x), _) => {
                                ins(Kind::NeK, 0, lane(fixed, arg(1)), 0, 0, x)
                            }
                            (CmpOp::Eq, ..) => two(fixed, Kind::Eq, 0),
                            (CmpOp::Ne, ..) => two(fixed, Kind::Ne, 0),
                            (CmpOp::Ult, ..) => two(fixed, Kind::Ult, 0),
                            (CmpOp::Ule, ..) => two(fixed, Kind::Ule, 0),
                            (CmpOp::Slt, ..) => two(fixed, Kind::Slt, wa),
                            (CmpOp::Sle, ..) => two(fixed, Kind::Sle, wa),
                        }
                    }
                }
            };
            prog.push(i);
        }
        // The root's lanes are read at every point.
        self.root = lane(fixed, home[kept.len() - 1]) as usize;
        true
    }

    /// Sets the most points a pass of the program evaluates, for an enumeration of `points`.
    fn lanes_for(&mut self, points: u64) {
        let len = self.kept.len();
        let fit = (EXHAUSTIVE_LANE_WORDS / len).clamp(1, EXHAUSTIVE_LANES);
        // A power of two, as `points` is: a block is whole passes.
        let most = (1usize << fit.ilog2()).min(usize::try_from(points).unwrap_or(usize::MAX));
        self.most = most;
        self.width = 0;
        if self.lanes.len() < len * most {
            self.lanes.resize(len * most, 0);
        }
        // The inputs' bits at the first `most` points: at a point `p + l` past a multiple `p`
        // of `most`, an input's are its bits at `p` with its bits at `l`. Counted up in the
        // inputs' bits (`(v | !m) + 1 & m` is the next value of the bits `m`, zero after the
        // last, when the next input counts).
        self.spreads.clear();
        self.spreads.resize(self.inputs.len() * most, 0);
        for l in 1..most {
            let mut carry = true;
            for (j, &(_, m, _)) in self.inputs.iter().enumerate() {
                let was = self.spreads[j * most + l - 1];
                let now = if carry {
                    (was | !m).wrapping_add(1) & m
                } else {
                    was
                };
                carry &= now == 0;
                self.spreads[j * most + l] = now;
            }
        }
    }

    /// Lays the lanes out for passes of `width` points (at most `most`), with the values that
    /// are the same at every point written out.
    fn pass_of(&mut self, width: usize) {
        if self.width == width {
            return;
        }
        self.width = width;
        for (s, &(is, v)) in self.fixed.iter().enumerate() {
            if is == 2 {
                self.lanes[s * width..][..width].fill(v);
            }
        }
    }

    /// The first lane of the first `valid` at which the root is not `k`, after a pass.
    fn differs(&self, valid: usize, k: Option<u64>) -> Option<usize> {
        let Some(k) = k else {
            return Some(0);
        };
        let root = &self.lanes[self.root * self.width..][..valid];
        if root.iter().fold(0, |any, &x| any | (x ^ k)) == 0 {
            return None;
        }
        root.iter().position(|&x| x != k)
    }

    /// The first of `points` the root is not `k` at.
    fn miss_at(&mut self, points: &[u64], k: Option<u64>) -> Option<u64> {
        // A pass no wider than the points: a pass's cost is its width's.
        let width = points.len().min(self.most);
        self.pass_of(width);
        for pass in points.chunks(width) {
            for l in 0..width {
                // A short pass evaluates its last point again.
                let mut left = pass[l.min(pass.len() - 1)];
                for &(s, m, base) in &self.inputs {
                    self.lanes[s as usize * width + l] = base | spread(&mut left, m);
                }
            }
            run_lanes(&self.prog, &mut self.lanes, width);
            if let Some(l) = self.differs(pass.len(), k) {
                return Some(pass[l]);
            }
        }
        None
    }

    /// The first of the `count` points from `start` up the root is not `k` at; `start` is a
    /// multiple of `most`.
    fn miss_from(&mut self, start: u64, count: u64, k: Option<u64>) -> Option<u64> {
        let width = self.most;
        self.pass_of(width);
        let (mut p, end) = (start, start + count);
        while p < end {
            let mut left = p;
            for (j, &(s, m, base)) in self.inputs.iter().enumerate() {
                let at = base | spread(&mut left, m);
                let out = &mut self.lanes[s as usize * width..][..width];
                for (o, &low) in out.iter_mut().zip(&self.spreads[j * width..][..width]) {
                    *o = at | low;
                }
            }
            run_lanes(&self.prog, &mut self.lanes, width);
            let valid = (end - p).min(width as u64) as usize;
            if let Some(l) = self.differs(valid, k) {
                return Some(p + l as u64);
            }
            p += width as u64;
        }
        None
    }
}

/// The most points one pass of a word program evaluates ([`run_lanes`]): a block
/// ([`EXHAUSTIVE_BLOCK`]), and a power of two. An instruction's operator is read once a pass,
/// which is most of what a narrow pass costs: on programs of 30 to 2,000 instructions a point
/// took 0.33 to 0.40 ns an instruction at 64 points a pass, 0.25 to 0.29 ns at 256, and a
/// little less at 1,024.
const EXHAUSTIVE_LANES: usize = EXHAUSTIVE_BLOCK as usize;

/// The words of lanes a pass works in while it can, fewer points at once for a longer program:
/// past a few megabytes a pass was slower for being wider.
const EXHAUSTIVE_LANE_WORDS: usize = 1 << 17;

/// the place of `below` (operands first, the root last) that every demanded path
/// from the symbols to the root passes through, nearest the symbols with at most
/// [`EXHAUSTIVE_BITS`] demanded bits; not the root or a symbol. The root is a function of its
/// demanded bits alone. A reconstructed address can take a few bits of sums over `k - t` and
/// `t + k'`: 22 bits of the two symbols in `t` reach them, 11 bits of `t`.
fn bottleneck(
    below: &[Placed],
    demand: &[u64],
    live: &mut Vec<bool>,
    over: &mut Vec<u32>,
) -> Option<usize> {
    let n = below.len();
    let root = n.checked_sub(1)?;
    live.clear();
    live.resize(n, false);
    over.clear();
    over.resize(n + 1, 0);
    // A place is on a demanded path from a symbol to the root when it has demanded bits and is
    // a symbol or reads a place that is on one. A step of such a path, from a place to one it
    // reads, passes over the places between the two in the order; a symbol's path begins below
    // every place, so passes over all before the symbol. `over` takes one at the first place a
    // step passes over and gives one back past the last.
    for (p, (node, kids)) in below.iter().enumerate() {
        if demand[p] == 0 {
            continue;
        }
        if node.op == OpCode::Sym {
            live[p] = true;
            over[0] = over[0].wrapping_add(1);
            over[p] = over[p].wrapping_sub(1);
            continue;
        }
        for &c in &kids[..node.op.arity()] {
            let c = c as usize;
            if live[c] {
                live[p] = true;
                over[c + 1] = over[c + 1].wrapping_add(1);
                over[p] = over[p].wrapping_sub(1);
            }
        }
    }
    // A place on a demanded path that no step passes over is on every one of them (a path
    // that missed it would step over it); the first such is the nearest the symbols.
    let mut open = 0u32;
    for p in 0..root {
        open = open.wrapping_add(over[p]);
        if open == 0
            && live[p]
            && below[p].0.op != OpCode::Sym
            && demand[p].count_ones() <= EXHAUSTIVE_BITS
        {
            return Some(p);
        }
    }
    None
}

/// The most bits [`exhaustive`] enumerates of a cut of several places (see [`frontier`]), and
/// the most places it reads to find one. A cut is tried after an enumeration over one place
/// failed, and a deeper one costs its points whether or not it decides.
const FRONTIER_BITS: u32 = 10;
const FRONTIER_STEPS: usize = 256;

/// places of `below` (operands first, the root last) that every demanded path from
/// the symbols to the root passes through one of, with at most [`FRONTIER_BITS`] demanded
/// bits between them: each with those bits. The root is a function of the demanded bits of
/// such places alone, so one that is `k` at every value of them is `k`; they are taken as
/// free, where the places may take fewer values together, so a value the root differs at
/// decides nothing. (A [`bottleneck`] is one place; a shift count read from the low bits of a
/// product of a value two unrelated conditions each give one bit of has none that takes only
/// the values it can.)
///
/// The cut starts at the root's operands and moves toward the symbols a place at a time (the
/// place whose operands add the fewest bits first), while that adds no bits or leaves the
/// cut within the limit: the values the root takes over a cut nearer the symbols are among
/// those it takes over one above it, so the deepest cut that can be enumerated decides the
/// most. `mark` is scratch.
fn frontier(below: &[Placed], demand: &[u64], mark: &mut Vec<u32>) -> Option<Vec<(u32, u64)>> {
    let n = below.len();
    let root = n.checked_sub(1)?;
    // 0: not reached; 1: in the cut; 2: above it.
    mark.clear();
    mark.resize(n, 0);
    let bits = |p: usize| demand[p].count_ones() as i64;
    let leaf = |p: usize| matches!(below[p].0.op, OpCode::Sym | OpCode::Const);
    let mut front: Vec<usize> = Vec::new();
    let mut total = 0i64;
    // Moves the cut below `p`: the bits that adds.
    let open = |mark: &mut [u32], front: &mut Vec<usize>, p: usize| -> i64 {
        let (node, kids) = &below[p];
        let mut delta = if mark[p] == 1 { -bits(p) } else { 0 };
        mark[p] = 2;
        front.retain(|&q| q != p);
        for &c in &kids[..node.op.arity()] {
            let c = c as usize;
            if mark[c] == 0 && below[c].0.op != OpCode::Const {
                mark[c] = 1;
                front.push(c);
                delta += bits(c);
            }
        }
        delta
    };
    total += open(mark, &mut front, root);
    for _ in 0..FRONTIER_STEPS {
        // The place of the cut whose operands add the fewest bits; the nearest the root of
        // those.
        let mut best: Option<(i64, usize)> = None;
        for &p in &front {
            if leaf(p) {
                continue;
            }
            let (node, kids) = &below[p];
            let mut delta = -bits(p);
            let mut met = [usize::MAX; 3];
            for (j, &c) in kids[..node.op.arity()].iter().enumerate() {
                let c = c as usize;
                if mark[c] == 0 && below[c].0.op != OpCode::Const && !met.contains(&c) {
                    met[j] = c;
                    delta += bits(c);
                }
            }
            if best.is_none_or(|(d, q)| delta < d || (delta == d && p > q)) {
                best = Some((delta, p));
            }
        }
        let Some((delta, p)) = best else {
            break;
        };
        if delta > 0 && total + delta > i64::from(FRONTIER_BITS) {
            break;
        }
        total += open(mark, &mut front, p);
    }
    if total > i64::from(FRONTIER_BITS) {
        return None;
    }
    front.sort_unstable();
    Some(front.into_iter().map(|p| (p as u32, demand[p])).collect())
}

/// What an instruction of a word program computes ([`Ins`]); the forms in `K` take the
/// instruction's own word for an operand that is the same at every point, or its count for a
/// shift by one.
#[derive(Clone, Copy)]
enum Kind {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
    RotL,
    RotR,
    AddK,
    /// `k - a`.
    RSubK,
    MulK,
    AndK,
    OrK,
    XorK,
    ShlK,
    LShrK,
    AShrK,
    /// A rotate left by `sh`, neither zero nor the width.
    RotK,
    Not,
    Neg,
    /// From `sh` bits.
    Sext,
    /// From bit `sh` up.
    Extract,
    Eq,
    Ne,
    Ult,
    Ule,
    /// Of `sh` bits.
    Slt,
    Sle,
    EqK,
    NeK,
    /// `a`'s low bit picks `b` or `c`.
    Select,
    /// `a` above the `sh` bits of `b`.
    Concat,
}

/// One instruction of a word program ([`Exhaust::program`]): the place it computes and its
/// operands' are indices among the places evaluated, operands before, and every value is kept
/// masked to its node's width.
#[derive(Clone, Copy)]
struct Ins {
    kind: Kind,
    sh: u32,
    dst: u32,
    a: u32,
    b: u32,
    c: u32,
    mask: u64,
    k: u64,
}

/// Runs a word program at `width` points at once: `lanes` holds `width` words for each place
/// (the inputs' and the fixed values' already set), and each instruction is one loop over its
/// operands' lanes, its operator read once.
fn run_lanes(prog: &[Ins], lanes: &mut [u64], width: usize) {
    #[inline(always)]
    fn one(v: &mut [u64], n: usize, d: u32, a: u32) -> (&mut [u64], &[u64]) {
        let (lo, hi) = v.split_at_mut(d as usize * n);
        (&mut hi[..n], &lo[a as usize * n..][..n])
    }
    #[inline(always)]
    fn two(v: &mut [u64], n: usize, d: u32, a: u32, b: u32) -> (&mut [u64], &[u64], &[u64]) {
        let (lo, hi) = v.split_at_mut(d as usize * n);
        (
            &mut hi[..n],
            &lo[a as usize * n..][..n],
            &lo[b as usize * n..][..n],
        )
    }
    let sext = |v: u64, w: u32| -> i64 {
        let sh = 64 - w;
        ((v << sh) as i64) >> sh
    };
    for i in prog {
        let (m, k, sh) = (i.mask, i.k, i.sh);
        let w = 64 - m.leading_zeros();
        macro_rules! un {
            (|$x:ident| $e:expr) => {{
                let (o, a) = one(lanes, width, i.dst, i.a);
                for (o, &$x) in o.iter_mut().zip(a) {
                    *o = ($e) & m;
                }
            }};
        }
        macro_rules! bin {
            (|$x:ident, $y:ident| $e:expr) => {{
                let (o, a, b) = two(lanes, width, i.dst, i.a, i.b);
                for ((o, &$x), &$y) in o.iter_mut().zip(a).zip(b) {
                    *o = ($e) & m;
                }
            }};
        }
        match i.kind {
            Kind::Add => bin!(|x, y| x.wrapping_add(y)),
            Kind::Sub => bin!(|x, y| x.wrapping_sub(y)),
            Kind::Mul => bin!(|x, y| x.wrapping_mul(y)),
            Kind::And => bin!(|x, y| x & y),
            Kind::Or => bin!(|x, y| x | y),
            Kind::Xor => bin!(|x, y| x ^ y),
            Kind::Shl => bin!(|x, y| if y >= u64::from(w) { 0 } else { x << y }),
            Kind::LShr => bin!(|x, y| if y >= u64::from(w) { 0 } else { x >> y }),
            Kind::AShr => bin!(|x, y| (sext(x, w) >> y.min(u64::from(w) - 1)) as u64),
            Kind::RotL | Kind::RotR => {
                let right = matches!(i.kind, Kind::RotR);
                bin!(|x, y| {
                    let by = (y % u64::from(w)) as u32;
                    let by = if right { (w - by) % w } else { by };
                    if by == 0 {
                        x
                    } else {
                        (x << by) | (x >> (w - by))
                    }
                })
            }
            Kind::AddK => un!(|x| x.wrapping_add(k)),
            Kind::RSubK => un!(|x| k.wrapping_sub(x)),
            Kind::MulK => un!(|x| x.wrapping_mul(k)),
            Kind::AndK => un!(|x| x & k),
            Kind::OrK => un!(|x| x | k),
            Kind::XorK => un!(|x| x ^ k),
            Kind::ShlK => un!(|x| x << sh),
            Kind::LShrK => un!(|x| x >> sh),
            Kind::AShrK => un!(|x| (sext(x, w) >> sh) as u64),
            Kind::RotK => un!(|x| (x << sh) | (x >> (w - sh))),
            Kind::Not => un!(|x| !x),
            Kind::Neg => un!(|x| x.wrapping_neg()),
            Kind::Sext => un!(|x| sext(x, sh) as u64),
            Kind::Extract => un!(|x| x >> sh),
            Kind::Eq => bin!(|x, y| u64::from(x == y)),
            Kind::Ne => bin!(|x, y| u64::from(x != y)),
            Kind::Ult => bin!(|x, y| u64::from(x < y)),
            Kind::Ule => bin!(|x, y| u64::from(x <= y)),
            Kind::Slt => bin!(|x, y| u64::from(sext(x, sh) < sext(y, sh))),
            Kind::Sle => bin!(|x, y| u64::from(sext(x, sh) <= sext(y, sh))),
            Kind::EqK => un!(|x| u64::from(x == k)),
            Kind::NeK => un!(|x| u64::from(x != k)),
            Kind::Concat => bin!(|x, y| (x << sh) | y),
            Kind::Select => {
                let (lo, hi) = lanes.split_at_mut(i.dst as usize * width);
                let o = &mut hi[..width];
                let c = &lo[i.a as usize * width..][..width];
                let t = &lo[i.b as usize * width..][..width];
                let f = &lo[i.c as usize * width..][..width];
                for (((o, &c), &t), &f) in o.iter_mut().zip(c).zip(t).zip(f) {
                    let pick = (c & 1).wrapping_neg();
                    *o = ((t & pick) | (f & !pick)) & m;
                }
            }
        }
    }
}

/// Word-program evaluations ([`run_lanes`]) charged as one generic node evaluation
/// (`Context::eval_node`). On representative reconstructed addresses (44 and 71 nodes, 4,096
/// points) a word program run point by point was 4 to 38 times as fast as the generic
/// evaluator, and run a block of points at a time it is about twenty times as fast again
/// (the same enumerations took a twentieth of the time); this charges the low end of the
/// two together. Charged at the point-by-point rate, enumerations that take a millisecond
/// were declined for their cost, and six of 140 measured questions ran out of steps a
/// third of the way from where they now finish.
const WORD_EVALS: u64 = 64;

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
    for c in shared_nodes(cx, n, &cfg.limits, SWEEP_CUTS, &Default::default()) {
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
        // One input first: a block whose value there changes when the atom is zero reads
        // the atom, and no certificate proves the drop. (Nearly every atom is read: the
        // refutation sample of 64 points, built and evaluated for each, was three quarters
        // of the time spent here.)
        if reads_var(r, &read, v)? {
            continue;
        }
        let Some(m0) = with_constant(&read, v) else {
            continue;
        };
        let agree = sampled(r, &read, &m0, read.key()[0])?;
        if !agree {
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

/// Whether `m` is seen to read variable `v`: its value at one input (pseudo-random, splitmix64
/// of each variable's index) differs from its value there with `v` zero. Charged as pass work.
/// A filter, never evidence: `false` says nothing.
fn reads_var(r: &mut Runner<'_, '_>, m: &MbaExpr, v: u32) -> Result<bool, Stop> {
    let Some(&width) = m.vars().get(v as usize) else {
        return Ok(false);
    };
    charge(r, m, m, 1)?;
    let mut at: Vec<crate::BitVec> = m
        .vars()
        .iter()
        .zip(0u64..)
        .map(|(&w, i)| {
            let mut z = i.wrapping_add(1).wrapping_mul(0x9e37_79b9_7f4a_7c15);
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            crate::BitVec::wrapping_from_u64(w, z ^ (z >> 31))
        })
        .collect();
    let with = m.eval(&at);
    at[v as usize] = crate::BitVec::zero(width);
    let without = m.eval(&at);
    Ok(matches!((with, without), (Some(a), Some(b)) if a != b))
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
    // A block that contains one the solver was asked about with the same node cut off, and
    // ran out of its steps on (or does not take), is not asked about: the inner block is
    // part of this question as it was asked, and the solver has no more steps for the whole
    // than it had for the part. The sweep meets a tower of blocks operands first, each a
    // top of its own chain of sums, and each fragment holds the ones below it whole: a
    // tower of `k` blocks the solver cannot take was `k` questions of growing size. (Of
    // 3,404 questions in 140 slow questions, 1,066 held a block declined at the same cut:
    // asked all the same, none of those was answered; 333 of the others were.)
    let over = over_declined(r, cx, n, c, &bindings.atoms);
    if over {
        r.cut_declined.entry(c).or_default().insert(n, ());
        return Ok(None);
    }
    let answer = cut_answer(r, &m, size, cfg, SWEEP_CUT_STEPS)?;
    match answer {
        Cut::Proved(expr) => Ok(Some(r.build(cx, |cx| lift_id(cx, &expr, &bindings))?)),
        Cut::Declined => {
            r.cut_declined.entry(c).or_default().insert(n, ());
            Ok(None)
        }
        Cut::Open => Ok(None),
    }
}

/// Whether the block `n` with `c` cut off (the atoms of its lowering are `atoms`) is, or
/// holds, a block the solver declined in this call with `c` cut off (`Runner::cut_declined`).
/// A declined block's root is above its cut, so it is found only inside the fragment: not
/// below the cut, nor below an atom.
fn over_declined(r: &Runner<'_, '_>, cx: &Context, n: u32, c: u32, atoms: &[u32]) -> bool {
    let Some(declined) = r.cut_declined.get(&c) else {
        return false;
    };
    let mut seen: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    let mut stack = vec![n];
    while let Some(i) = stack.pop() {
        if i == c || atoms.contains(&i) || seen.insert(i, ()).is_some() {
            continue;
        }
        if declined.contains_key(&i) {
            return true;
        }
        stack.extend(cx.node(i).children());
    }
    false
}

/// What [`cut_answer`] has of a noise block.
enum Cut {
    /// A smaller equivalent, proved.
    Proved(MbaExpr),
    /// The solver did not answer: it ran out of its steps, or does not take the block.
    Declined,
    /// An answer that is no smaller or not proved, or no steps left to ask with.
    Open,
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
) -> Result<Cut, Stop> {
    let limit = steps.min(r.meter.left_in(|b| b.mba_steps));
    if limit == 0 {
        return Ok(Cut::Open);
    }
    let budget = cfg.budget.with_evidence(false).with_steps(limit);
    let (answer, spent) = r.inner.mba.solver.solve_counted(m, &budget);
    let spent = spent.min(r.meter.left_in(|b| b.mba_steps));
    r.meter.charge(Counter::MbaSteps, spent)?;
    let expr = match answer {
        MbaAnswer::Simplified { expr, .. } => expr,
        MbaAnswer::Exhausted | MbaAnswer::Unsupported(_) => {
            return Ok(Cut::Declined);
        }
        MbaAnswer::NoSimpler => {
            return Ok(Cut::Open);
        }
    };
    if expr.vars() != m.vars() || expr.width() != m.width() || expr.nodes().len() >= size {
        return Ok(Cut::Open);
    }
    if !sampled(r, m, &expr, m.key()[0])? {
        return Ok(Cut::Open);
    }
    let report = certify::prove(m, &expr, &mut Steps::new(r, SWEEP_SHARE))?;
    count(r).certificates.record(&report);
    if report.verdict != Verdict::Proved {
        return Ok(Cut::Open);
    }
    count(r).noise_blocks += 1;
    Ok(Cut::Proved(expr))
}

/// the sweep's readings of `subject` asked whether it is `k`: whether one proves it
/// (`decided`), whether its whole fragment is refuted (`refuted`), and whether some narrower
/// reading was refuted over its free atoms (a constant only through how its atoms relate) or
/// the readings were cut short.
///
/// A candidate below `subject` whose readings were asked in this call and decided nothing is
/// an atom to every reading here (`Runner::mba_undecided`). The sweep meets a constant's
/// operands first, and an obfuscator builds one constant from another: where the lower one
/// stays open, each node above it that the samples hold constant holds its fragment whole,
/// and the certificates would spend a share on the same question at every one of them (ten
/// links of one chain in a measured question, a share each; nine tenths of what the sweeps
/// of 140 questions spent went to certificates that decided nothing, most of it this way).
/// What an upper constant is beyond the open one, the readings over it as an atom still
/// prove; a `subject` that is itself open is not asked again.
///
/// The readings are asked cheapest first, and they end at the first whose certificate takes
/// most of its share and leaves the question open: the ones after it are larger. (Of 22,555
/// proofs in the sweeps of those questions, six came after such a reading of the same
/// candidate; half of what the undecided certificates spent did.)
fn readings_prove(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    subject: u32,
    k: &crate::BitVec,
    share: u64,
) -> Result<(bool, bool, bool), Stop> {
    let (mut decided, mut refuted, mut seen) = (false, false, false);
    // Each reading with its cost, and whether a refutation of it is one of `subject` (the
    // whole fragment, no open candidate cut out of it).
    let mut readings: Vec<(u64, bool, MbaExpr, Bindings)> = Vec::new();
    let open = &r.mba_undecided;
    if open.contains_key(&subject) {
        return Ok((false, false, false));
    }
    let cuts = shared_nodes(cx, subject, &cfg.limits, SWEEP_CUTS, open);
    let kinds = [Reading::SemiLinear, Reading::Shallow, Reading::Linear];
    let all = std::iter::once(None)
        .chain(kinds.into_iter().map(Some))
        .chain(
            cuts.into_iter()
                .flat_map(|c| [Some(Reading::Cut(c)), Some(Reading::CutWhole(c))]),
        );
    // A fragment that is semi-linear as it is has one lowering for the whole and the
    // semi-linear reading, and one per cut.
    let mut semi = false;
    for reading in all {
        let lowered = match reading {
            None => lower_id_whole(cx, subject, &cfg.limits, open).map(|(m, bindings, s)| {
                semi = s;
                (m, bindings)
            }),
            Some(Reading::SemiLinear | Reading::CutWhole(_)) if semi => continue,
            _ => lower_id_over(cx, subject, &cfg.limits, reading, open),
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
        let whole = reading.is_none() && bindings.atoms.iter().all(|a| !open.contains_key(a));
        readings.push((
            points.saturating_mul(m.nodes().len() as u64),
            whole,
            m,
            bindings,
        ));
    }
    // Whether a certificate was asked and left the question open.
    let mut open_asked = false;
    readings.sort_by_key(|(cost, _, _, _)| *cost);
    'readings: for (cost, whole, m, bindings) in readings {
        if cost > share {
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
            let mut meter = Steps::new(r, share);
            let report = certify::prove(&m, &c, &mut meter)?;
            // The certificate took most of its share and left the question open: the readings
            // not yet asked are larger, and theirs would too. (Not the same reading asked
            // again through its atoms' known bits: that is one more question of this
            // reading, and the next reading has its own.)
            let burned = !known && meter.share < share / 2;
            count(r).certificates.record(&report);
            match report.verdict {
                Verdict::Proved => {
                    decided = true;
                    break 'readings;
                }
                Verdict::Refuted if whole => {
                    refuted = true;
                    break 'readings;
                }
                Verdict::Refuted if !known => {
                    open_asked = true;
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
                _ => {
                    open_asked = true;
                    if burned {
                        // What the readings left unasked might have been refuted over their
                        // free atoms: the root's cases are tried as if one was.
                        seen = true;
                        break 'readings;
                    }
                    break;
                }
            }
        }
    }
    if !decided && !refuted && open_asked {
        r.mba_undecided.insert(subject, ());
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
/// `attempts` counts the blocks whose sides were built.
fn cases_fold(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
    attempts: &mut usize,
) -> Result<Option<u32>, Stop> {
    let Some(c) = r.build(cx, |cx| super::context::most_tested(cx, n))? else {
        return Ok(None);
    };
    // The samples first, before a side is built or swept: a side that varies at them is not
    // proved constant, and its sweep keeps its value (wherever the run's assumptions hold,
    // so only the samples where they do are read), so it varies after its sweep as before.
    // (Of 3,404 blocks with a condition in 140 slow questions, 2,658 were swept to find a
    // side that varied at the samples it began with: five sixths of the time spent here.)
    //
    // Before the sides are built, the block's own samples: where `c` holds the first side
    // is `n`, elsewhere the second is (`context::sides_on`), so a block with two values
    // where `c` holds, or two where it does not, has a side with both.
    r.sample(cx, n)?;
    r.sample(cx, c)?;
    let points = r.samples[&n].len();
    let held = held_points(r, cx, points)?;
    let (vn, vc) = (&r.samples[&n], &r.samples[&c]);
    let where_c = |holds: bool| -> Vec<bool> {
        let at = |(held, c): (&bool, &crate::BitVec)| *held && c.is_zero() != holds;
        held.iter().zip(vc.iter()).map(at).collect()
    };
    if varies_at(vn, &where_c(true)) || varies_at(vn, &where_c(false)) {
        return Ok(None);
    }
    let got = r.build(cx, |cx| super::context::sides_on(cx, n, c))?;
    let Some((t, f)) = got else {
        return Ok(None);
    };
    *attempts += 1;
    let mut sides = [t, f];
    // Then each side's samples (those where the other case holds too).
    for side in sides {
        if cx.const_val(side).is_some() {
            continue;
        }
        r.sample(cx, side)?;
        if varies_at(&r.samples[&side], &held) {
            return Ok(None);
        }
    }
    // Each side swept and proved before the other is swept: a first side left unproved
    // ends the attempt, and the second side's sweep with it (548 of the 654 blocks whose
    // sides were constant at the samples and not proved ended at the first side, after
    // both were swept). What proves a side does not read the other's sweep: the nodes below
    // it are all examined by its own.
    let mut values = [crate::BitVec::zero(cx.width_of(n)); 2];
    for (slot, side) in values.iter_mut().zip(&mut sides) {
        // A side an earlier sweep of this call examined (the side of a block below this
        // one, where the condition fixes what the two differ in) is that sweep's result:
        // every node below it was examined before it, and a sweep would only walk them.
        *side = match r.swept.get(side) {
            Some(&done) => done,
            None => sweep_inner(r, cx, cfg, *side, false)?,
        };
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
        let proved = readings_prove(r, cx, cfg, *side, &k, SWEEP_SHARE)?.0;
        if !proved {
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

/// Whether every constraint of the run's assumptions holds, at each of the `points` sample
/// points (all of them without assumptions): where a rewrite that relies on them keeps a
/// node's value.
fn held_points(r: &mut Runner<'_, '_>, cx: &Context, points: usize) -> Result<Vec<bool>, Stop> {
    use crate::facts::Reliance;
    let Some(a) = r.assumptions else {
        return Ok(vec![true; points]);
    };
    let all = a.constraints().fold(Reliance::NONE, |rel, (id, _, _)| {
        rel.union(Reliance::of(id))
    });
    r.constraints_hold(cx, all, points)
}

/// Whether `vals` differ at two of the sample points `at` keeps.
fn varies_at(vals: &[crate::BitVec], at: &[bool]) -> bool {
    let mut kept = vals.iter().zip(at).filter(|(_, at)| **at).map(|(v, _)| v);
    kept.next().is_some_and(|k| kept.any(|v| v != k))
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
        if cx.const_val(side).is_none() && !readings_prove(r, cx, cfg, side, k, SWEEP_SHARE)?.0 {
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

/// The most atoms a block [`sweep_cut`] asks about has. (With four, the solver was asked
/// about several hundred more blocks in 140 measured questions and answered none of them.)
const SWEEP_CUT_VARS: usize = 3;

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
    let out = ask(r, cx, cfg, n, n, None, u64::MAX)?;
    if let Step::Normal(fin) = &out
        && fin.done
    {
        // a fragment that reads slices of one rotated value, asked again with them
        // written as masks of that rotation (see [`sliced`]).
        let before = cx.len() as u32;
        let slices = r.build(cx, |cx| sliced(cx, n, cfg.limits.max_nodes))?;
        if let Some(root) = slices {
            let again = ask(r, cx, cfg, n, root, None, u64::MAX)?;
            if matches!(again, Step::To(..)) {
                return Ok(again);
            }
        }
        // And with a value most of its terms read cut off as one atom: an obfuscator writes
        // `Σ cᵢ·fᵢ(t)` over a `t` that is a fragment of its own, and the whole question is
        // then over what `t` is made of, where the cut one is over `t` alone.
        for root in slices.into_iter().chain([n]) {
            let cuts = shared_nodes(cx, root, &cfg.limits, CUTS, &Default::default());
            for c in cuts {
                let again = ask(r, cx, cfg, n, root, Some(c), CUT_STEPS)?;
                if matches!(again, Step::To(..)) {
                    return Ok(again);
                }
            }
        }
        discard(r, cx, before);
    }
    Ok(out)
}

/// The MBA phase at `n`, a part of a question written another way (a sum with its common
/// factor taken out): the node's own question alone, within the steps a retried one takes
/// (see [`CUT_STEPS`]). What an obfuscator scaled is a small question; what is not takes the
/// steps the questions after it need.
pub(super) fn step_part(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
) -> Result<Step, Stop> {
    let poly = r.inner.mba.solver.polynomial_fragments();
    let op = cx.node(n).op;
    if !(mixed_op(op) || (poly && op == OpCode::Shl)) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    ask(r, cx, cfg, n, n, None, CUT_STEPS)
}

/// The most shared values the MBA phase cuts a fragment at, one question each.
const CUTS: usize = 2;

/// The solver steps one of those questions takes. (At four times this, the questions that
/// ran out left 140 measured calls twice the nodes; at a quarter, they answered half as many.)
const CUT_STEPS: u64 = 1 << 14;

/// The share of the call's pass work the certificate of a retried question's answer takes
/// (see [`GATE_SHARE`]): one in this many.
const RETRY_GATE_SHARE: u64 = 32;

/// A node as bits of one rotation of another: `(rotl(base, rot) & mask) ^ flip`, at the
/// node's width (at most 64 bits). Every node built over one value by shifts and rotations by
/// constants, complements, and `& | ^` with constants or with another such node of the same
/// rotation of the same value has this shape: each of its bits is 0, 1, a bit of the rotation
/// or that bit's complement. A left shift by `k` is the rotation by `k` with its low `k` bits
/// cleared, a logical right shift the rotation by `−k` with its high `k` bits cleared.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct Slice {
    base: u32,
    rot: u32,
    mask: u64,
    flip: u64,
}

/// The most operators one [`slice_of`] reads below a node.
const SLICE_DEPTH: u32 = 48;

/// Node `i` as a [`Slice`]; a node that is no such function of another is its own base, whole
/// (`rot` 0, every bit, no flip).
fn slice_of(cx: &Context, i: u32, memo: &mut crate::hash::IdMap<u32, Slice>, depth: u32) -> Slice {
    let w = u32::from(cx.width_of(i).bits());
    let ones = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    let whole = Slice {
        base: i,
        rot: 0,
        mask: ones,
        flip: 0,
    };
    if w > 64 || depth > SLICE_DEPTH {
        return whole;
    }
    if let Some(&s) = memo.get(&i) {
        return s;
    }
    let n = cx.node(i);
    let konst = |j: u32| cx.const_val(j).and_then(|c| c.to_u64());
    let rotl = |m: u64, by: u32| match by % w {
        0 => m,
        b => (m << b | m >> (w - b)) & ones,
    };
    // A shift or rotation count: a constant below the width, of an operand of the same width.
    let count = |j: u32| {
        konst(j)
            .filter(|&k| k > 0 && k < u64::from(w))
            .map(|k| k as u32)
    };
    let same_width = |j: u32| cx.width_of(j) == cx.width_of(i);
    let s = match n.op {
        OpCode::Not => {
            let a = slice_of(cx, n.a, memo, depth + 1);
            Slice {
                flip: !a.flip & ones,
                ..a
            }
        }
        OpCode::And | OpCode::Or | OpCode::Xor => {
            let (x, k) = match (konst(n.a), konst(n.b)) {
                (None, Some(k)) => (n.a, Some(k)),
                (Some(k), None) => (n.b, Some(k)),
                _ => (n.a, None),
            };
            let a = slice_of(cx, x, memo, depth + 1);
            // The other operand at each bit of the rotation: a constant's bit either way, or
            // another slice of the same rotation.
            let other = match k {
                Some(k) => Some((0, k)),
                None if konst(n.a).is_none() => {
                    let b = slice_of(cx, n.b, memo, depth + 1);
                    (b.base == a.base && b.rot == a.rot).then_some((b.mask, b.flip))
                }
                None => None,
            };
            match other {
                Some((mb, fb)) => {
                    let op = |p: u64, q: u64| match n.op {
                        OpCode::And => p & q,
                        OpCode::Or => p | q,
                        _ => p ^ q,
                    };
                    // The value where the rotation's bit is 0, and where it is 1.
                    let at0 = op(a.flip, fb);
                    let at1 = op(a.flip ^ a.mask, fb ^ mb);
                    Slice {
                        mask: (at0 ^ at1) & ones,
                        flip: at0 & ones,
                        ..a
                    }
                }
                None => whole,
            }
        }
        OpCode::Shl if same_width(n.a) => match count(n.b) {
            Some(k) => {
                let a = slice_of(cx, n.a, memo, depth + 1);
                Slice {
                    base: a.base,
                    rot: (a.rot + k) % w,
                    mask: a.mask << k & ones,
                    flip: a.flip << k & ones,
                }
            }
            None => whole,
        },
        OpCode::LShr if same_width(n.a) => match count(n.b) {
            Some(k) => {
                let a = slice_of(cx, n.a, memo, depth + 1);
                Slice {
                    base: a.base,
                    rot: (a.rot + w - k) % w,
                    mask: a.mask >> k,
                    flip: a.flip >> k,
                }
            }
            None => whole,
        },
        OpCode::RotL | OpCode::RotR if same_width(n.a) => match count(n.b) {
            Some(k) => {
                let k = if n.op == OpCode::RotL { k } else { w - k };
                let a = slice_of(cx, n.a, memo, depth + 1);
                Slice {
                    base: a.base,
                    rot: (a.rot + k) % w,
                    mask: rotl(a.mask, k),
                    flip: rotl(a.flip, k),
                }
            }
            None => whole,
        },
        _ => whole,
    };
    memo.insert(i, s);
    s
}

/// node `n`'s fragment (its MBA operators, down to their atoms) with every part that reads
/// one rotation of one value written over that rotation: `(rotl(x, r) & mask) ^ flip` (see
/// [`Slice`]). `rotl(x, 32) >>u 30`, `rotl(x, 32) << 34` and `rotl(x, 2)` are the low 34
/// bits, the high 30 bits and the whole of `rotl(x, 2)`, but three unrelated atoms to the
/// solver: obfuscators write a rotate as such shifts beside the rotate itself in MBAs that
/// cancel, and mask and complement the halves before they shift them.
///
/// A part whose low `k` bits are clear is also that many bits lower of the rotation by `k`
/// less, shifted up (`rotl(x, 9) & 0x…42` is `(rotl(x, 8) & 0x…21) << 1`), and a product by a
/// constant with low zero bits is its operand shifted up times the rest
/// (`(x & m) · (c · 2^k)` is `((x & m) << k) · c`). Each part is read at the rotation the
/// most parts of the fragment can be read at, so a term an obfuscator doubled, or a pass
/// wrote as a shift, stays a multiple of the atom the other terms read.
///
/// `None` when no two parts read one rotation of one value, when the fragment is written
/// that way already, or past `max_nodes`.
fn sliced(cx: &mut Context, n: u32, max_nodes: u32) -> Result<Option<u32>, crate::Error> {
    use crate::ops::BinOp;
    /// One part of the fragment: the node; the slice its operand is (the node's own, for a
    /// part that is no product); and for a product, its constant.
    struct Part {
        node: u32,
        slice: Slice,
        factor: Option<u64>,
    }
    let mut memo: crate::hash::IdMap<u32, Slice> = crate::hash::IdMap::default();
    let mut parts: Vec<Part> = Vec::new();
    // How many parts can be read at each rotation of each value.
    let mut readers: std::collections::BTreeMap<(u32, u32), u32> =
        std::collections::BTreeMap::new();
    let mut seen: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    let mut stack = vec![n];
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() || cx.const_val(i).is_some() {
            continue;
        }
        if seen.len() as u32 > max_nodes {
            return Ok(None);
        }
        let node = cx.node(i);
        let slice = slice_of(cx, i, &mut memo, 0);
        if slice.base != i {
            if slice.mask | slice.flip != 0 {
                parts.push(Part {
                    node: i,
                    slice,
                    factor: None,
                });
            }
            continue;
        }
        // Read as it is: one reader of itself, unrotated.
        *readers.entry((i, 0)).or_default() += 1;
        if mixed_op(node.op) {
            if node.op == OpCode::Mul && cx.width_of(i).bits() <= 64 {
                let konst = |j: u32| cx.const_val(j).and_then(|c| c.to_u64());
                let product = match (konst(node.a), konst(node.b)) {
                    (None, Some(c)) => Some((node.a, c)),
                    (Some(c), None) => Some((node.b, c)),
                    _ => None,
                };
                if let Some((x, c)) = product
                    && c != 0
                    && c & 1 == 0
                {
                    parts.push(Part {
                        node: i,
                        slice: slice_of(cx, x, &mut memo, 0),
                        factor: Some(c),
                    });
                }
            }
            stack.extend(node.children());
        }
    }
    // The readings of a part: the slice at each rotation it can be read at, with the shift
    // that makes the part of it (a product's operand shifted up by `k` of its constant's low
    // zero bits, the rest of the constant a factor; any other part's slice `k` bits lower,
    // shifted up).
    let readings = |cx: &Context, p: &Part| -> Vec<(Slice, u32)> {
        let w = u32::from(cx.width_of(p.node).bits());
        let ones = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
        let s = p.slice;
        match p.factor {
            Some(c) => (0..=c.trailing_zeros().min(w - 1))
                .map(|k| {
                    let up = Slice {
                        rot: (s.rot + k) % w,
                        mask: s.mask << k & ones,
                        flip: s.flip << k & ones,
                        ..s
                    };
                    (up, k)
                })
                .filter(|(up, _)| up.mask | up.flip != 0)
                .collect(),
            None => (0..=(s.mask | s.flip).trailing_zeros().min(w - 1))
                .map(|k| {
                    let down = Slice {
                        rot: (s.rot + w - k) % w,
                        mask: s.mask >> k,
                        flip: s.flip >> k,
                        ..s
                    };
                    (down, k)
                })
                .collect(),
        }
    };
    for p in &parts {
        for (s, _) in readings(cx, p) {
            *readers.entry((s.base, s.rot)).or_default() += 1;
        }
    }
    // A slice as a node over its rotation.
    let over = |cx: &mut Context, s: &Slice| -> Result<u32, crate::Error> {
        let w = cx.width_of(s.base).bits();
        let ones = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
        let mut v = match s.rot {
            0 => s.base,
            r => {
                let k = cx.mk_const_u64(w, u64::from(r))?;
                cx.c_bin(BinOp::RotL, s.base, k)?
            }
        };
        if s.mask != ones {
            let k = cx.mk_const_u64(w, s.mask)?;
            v = cx.c_bin(BinOp::And, v, k)?;
        }
        if s.flip != 0 {
            let k = cx.mk_const_u64(w, s.flip)?;
            v = cx.c_bin(BinOp::Xor, v, k)?;
        }
        Ok(v)
    };
    let mut repl: crate::hash::IdMap<u32, u32> = crate::hash::IdMap::default();
    // Whether some part is read through a shift or a rotation (else the fragment reads its
    // values as they are, and there is nothing to relate).
    let mut moved = false;
    for p in &parts {
        // The rotation the most parts read, the part's own first among equals.
        let best = readings(cx, p)
            .into_iter()
            .map(|(s, k)| (readers.get(&(s.base, s.rot)).copied().unwrap_or(0), s, k))
            .filter(|(votes, _, _)| *votes >= 2)
            .min_by_key(|(votes, _, k)| (u32::MAX - votes, *k));
        let Some((_, s, k)) = best else {
            continue;
        };
        if p.factor.is_some() && k == 0 {
            continue;
        }
        let w = cx.width_of(p.node).bits();
        let x = over(cx, &s)?;
        let v = match p.factor {
            Some(c) => {
                let rest = cx.mk_const_u64(w, c >> k)?;
                cx.c_bin(BinOp::Mul, x, rest)?
            }
            None if k == 0 => x,
            None => {
                let by = cx.mk_const_u64(w, u64::from(k))?;
                cx.c_bin(BinOp::Shl, x, by)?
            }
        };
        moved |= s.rot != 0 || k != 0;
        if v != p.node {
            repl.insert(p.node, v);
        }
    }
    if repl.is_empty() || !moved {
        return Ok(None);
    }
    let root = cx.substitute_ids(&[n], &repl)?[0];
    Ok((root != n).then_some(root))
}

/// Whether the fragment under `root` holds, below `root`, one the MBA phase asked about in
/// this call and kept as it is (`Runner::mba_kept`): the solver declined it for its size (too
/// many atoms, variables or bit classes), or its answer would not have made the DAG smaller,
/// or the gate could not prove it. The larger fragment is then not asked. It has as many
/// atoms as the one inside it; the solver would pay for the inner fragment's normal form
/// again, at a cost that grows with the fragment; and what kept the inner answer back (its
/// nodes are shared, its normal form is as large, no certificate decides it) keeps back an
/// answer that holds it. An obfuscated value read by a chain of operations asks once at the
/// first of them where it asked at every one (27 questions of 820 nodes in one measured
/// question, 310,000 steps each, half the run's steps), and so do fragments that share a core
/// whose answer was no smaller (five of 110 to 197 nodes in another, 2.5 million steps and no
/// rewrite). `root` itself is asked again: the call remembers its answer, and what kept it
/// back may be gone in a later round.
fn holds_kept(r: &Runner<'_, '_>, cx: &Context, root: u32, bindings: &Bindings) -> bool {
    if r.mba_kept.is_empty() {
        return false;
    }
    let mut seen: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    for &a in &bindings.atoms {
        seen.insert(a, ());
    }
    let mut stack: Vec<u32> = cx.node(root).children().collect();
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if r.mba_kept.contains_key(&i) {
            return true;
        }
        stack.extend(cx.node(i).children());
    }
    false
}

/// One question to the solver takes at most this fraction of the call's solver steps (and at
/// least [`SOLVE_SHARE_MIN`]). The solver's own limit is a million steps whatever the call
/// has, so in a call of two million one question that ran out took half of them, a fragment
/// holding it took the other half, and the rounds after had none. Of the answers committed
/// in 140 measured questions none took more than a quarter of its call's steps; 26 questions
/// that took more than that ended with nothing (out of steps, not smaller, or unproved).
const SOLVE_SHARE: u64 = 4;

/// See [`SOLVE_SHARE`].
const SOLVE_SHARE_MIN: u64 = 1 << 16;

/// The solver steps from which a fragment with no simpler form is kept from the questions
/// above it (see [`holds_kept`]).
const KEPT_STEPS: u64 = 1 << 12;

/// [`step`]'s question at node `n`, lowered from `root` (`n` itself, or an equal rewrite of it):
/// the answer replaces `n`.
fn ask(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &MbaConfig,
    n: u32,
    root: u32,
    cut: Option<u32>,
    cap: u64,
) -> Result<Step, Stop> {
    let poly = r.inner.mba.solver.polynomial_fragments();
    // The whole fragment, or its semi-linear reading with the node `cut` an atom (and an
    // operand that is the atom less a constant written over it, see `lower_id_over`).
    let lowered = match cut {
        None => lower_id(cx, root, &cfg.limits),
        Some(c) => lower_id_over(
            cx,
            root,
            &cfg.limits,
            Some(Reading::Cut(c)),
            &crate::hash::IdMap::default(),
        ),
    };
    let (m, bindings) = match lowered {
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
    if holds_kept(r, cx, root, &bindings) {
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
                    //
                    // One question takes at most a share of the call's steps (see
                    // `SOLVE_SHARE`), and one the solver ran out of steps on is not asked
                    // again in this call with no more of them: the answer is the same.
                    let share = (r.meter.limit.mba_steps / SOLVE_SHARE).max(SOLVE_SHARE_MIN);
                    let limit = cfg
                        .budget
                        .steps
                        .min(share)
                        .min(cap)
                        .min(r.meter.left_in(|b| b.mba_steps));
                    if limit == 0 || r.mba_exhausted.get(&key).is_some_and(|&l| limit <= l) {
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
                    if a == MbaAnswer::Exhausted {
                        // A fragment that holds this one is no smaller a question.
                        r.mba_exhausted.insert(key, limit);
                        r.mba_kept.insert(root, ());
                    }
                    if a == MbaAnswer::Exhausted && limit < cfg.budget.steps {
                        // Run short within what the account left it: more budget might
                        // decide.
                        count(r).exhausted += 1;
                        return Ok(Step::Normal(Fin::capped(Exhausted::MbaSteps)));
                    }
                    if a != MbaAnswer::Exhausted {
                        r.mba_answers.insert(key, a.clone());
                    }
                    let kept = match &a {
                        MbaAnswer::Unsupported(why) => why.starts_with("too many"),
                        MbaAnswer::NoSimpler => spent >= KEPT_STEPS,
                        _ => false,
                    };
                    if kept {
                        r.mba_kept.insert(root, ());
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
                        r.mba_kept.insert(root, ());
                        count(r).not_smaller += 1;
                        r.stats.passes.entry("mba").or_default().rejected_cost += 1;
                        discard(r, cx, before);
                        return Ok(Step::Normal(fin));
                    }
                    // A question asked again another way (slices, a cut) proves its answer
                    // within a smaller share: the node's own question had the large one, and
                    // two retries that each took half the call's pass work left the root as
                    // it was (eleven of 140 measured questions).
                    let part = match cut.is_some() || root != n {
                        true => RETRY_GATE_SHARE,
                        false => GATE_SHARE,
                    };
                    let own = exact(r, &m, &expr, part)?;
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
                            r.mba_kept.insert(root, ());
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
        r.mba_kept.insert(root, ());
    }
    Ok(out)
}
