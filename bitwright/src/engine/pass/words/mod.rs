//! Limb arithmetic read as arithmetic on the words.
//!
//! Code that computes on a wide value digit by digit (an obfuscator's virtual machine, a
//! multi-precision routine) writes each digit of a result as a sum of digits of the operands,
//! with the carries and borrows between digits as comparisons of the digits below: for `a + b`
//! split at bit `k`,
//!
//! ```text
//! (a >>u k) + (b >>u k) + zext((a + b & 2^k − 1) <u (a & 2^k − 1))
//! ```
//!
//! is the high digit of `a + b`. The passes that read sums, masks and comparisons one at a
//! time see no sum of `a` and `b` there. This pass reads every node as an integer:
//!
//! - A node's unsigned value is written as a *form* `c + Σ kᵢ·tᵢ` over the integers, the `tᵢ`
//!   being values of the expression, `floor(F / 2^k)` of a form, the AND of two forms modulo
//!   `2^p`, the XOR of any number of forms, and a choice between two forms ([`form`]).
//! - Every operator has such a form ([`lift`]). A slice is two floors; a sum that may wrap at
//!   `w` bits is `S − 2^w·floor(S / 2^w)`, the floor dropped where the bounds of `S` say it is
//!   0; `x <u y` is `−floor((x − y) / 2^k)`; a carry or a borrow written with the one below
//!   coming in (`[y = all ones] & c | [s <u x]`) is the sum of the two; and a choice between
//!   two values a constant apart is the one plus the constant where the condition holds.
//! - Floors are kept in one shape: `floor((E + 2^k·Q) / 2^k) = floor(E / 2^k) + Q` moves every
//!   multiple of `2^k` out, `floor((floor(E / 2^a) + R) / 2^k) = floor((E + 2^a·R) / 2^(a + k))`
//!   joins a floor inside a floor, and `floor((−E − 1) / 2^k) = −floor(E / 2^k) − 1` fixes the
//!   sign.
//!
//! In that shape the digit sum above is `floor((a + b) / 2^k)`: the carry is `floor((a + b) /
//! 2^k) − floor(a / 2^k) − floor(b / 2^k)`, and the digits of `a` and `b` cancel. Nothing is
//! matched and nothing is proved: each step is an identity of the integers, and what cancels
//! does so by collecting terms. A chain of operations done in digits (several XORs each
//! written `x + y − 2·(x & y)`, a product by a constant, a constant added limb by limb)
//! collapses the same way, one operation after the other, into a slice of the word.
//!
//! An XOR has two forms, and a root is asked with each (see `ask`). As an *atom* of its
//! operands (any number of them, each once and in one order, two of one gone) it is one
//! value however it was grouped, and a slice of it is the XOR of the slices: bitwise code is
//! read by that, of 3 values as of 100, in whatever order each place XORs them. An AND then
//! has the relation `2·(x & y) = x + y − (x ^ y)` with the atom, and a form is kept at the
//! member of its class with the fewest terms, so the XOR spelled `x + y − 2·(x & y)` is the
//! same atom. As the *sum* `x + y − 2·(x & y)` it is what arithmetic done on an XOR is read
//! by: its carries are the sum's. The operands of an atom that are truncations of wider words
//! are in turn taken as the words (which the sums around them are of) and as the values. A
//! chain of ANDs or of ORs is read with its operands in one order as well, and a sum is one
//! form whatever its order: an operation of many operands is one value. With the atoms a
//! choice against a constant is also taken apart, `c ? K : b` being `K·c + (c ? 0 : b)`: the
//! slices of the other arm are then slices of the one choice, whatever digits of the constant
//! each limb is chosen against.
//!
//! What is written back is decided on the whole expression ([`write`]). From the root down,
//! each node's form is written out as nodes again (floors of one form as slices of that one
//! word, `x + y − 2·(x & y)` as `x ^ y`, any part that a node below already is as that node),
//! at the node's width and at the low bits of it that its users read, and the node is
//! replaced where that leaves the root's DAG smaller. The limbs of a word share their carries,
//! so no limb alone frees them; the search replaces a node for all its users at once, and
//! the root's size decides. The result replaces the root by the passes' commit rule: only if
//! the DAG gets strictly smaller. It is compared with the root at the engine's verification
//! points first, as the application of a rule linked without a proof is: the derivation does
//! not rest on that, but a defect of the pass would be seen there and the pass set aside for
//! the call.
//!
//! The reading uses the facts (bounds and known bits) of the nodes, so a result relies on
//! what they relied on. Coefficients, shifts, the terms of a form, the nodes under a root and
//! the work of one question are bounded ([`form`] and [`write`]): past a bound a node is the
//! value it is, or the question is not asked, which no budget changes.

mod form;
mod lift;
#[cfg(test)]
mod tests;
mod write;

use super::{Marks, PassKind, finish};
use crate::engine::budget::Counter;
use crate::engine::{Fin, Runner, Step, Stop};
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;

/// The most nodes under a root that is asked.
const MAX_CONE: usize = 1024;
/// The most roots whose nodes are counted and found too many in a phase run, before none is
/// asked any more: the counting is then at most this many times [`MAX_CONE`] node visits.
/// (A root taller than `MAX_CONE` is too large without a count.)
const MAX_LARGE: u32 = 4096;
/// The most work of the pass's questions in a call (see `write`): past it none is asked, so
/// the pass alone does not use up a call's budget.
const MAX_WORK: u64 = 1 << 26;
/// What a root's second question may take beyond twice the work of its first (see `ask`).
const SECOND_SLACK: u64 = 1 << 14;
/// The most work of second questions whose answers were not taken, in a call: past it none
/// is asked (the plain forms are not what reads the call's XORs).
const MAX_LOST: u64 = 1 << 23;

/// The pass's state for a call.
#[derive(Default)]
pub(crate) struct State {
    build: write::Build,
    /// Nodes not asked (again) in this phase run: asked, or under a node that was.
    covered: Marks,
    /// What the ask at a node contributes to its finality, for the phase run.
    asked: IdMap<u32, Fin>,
    /// The roots the search found nothing for in this call, with what the facts it read
    /// relied on: the nodes under a node never change, so neither does the answer.
    quiet: IdMap<u32, Fin>,
    large: u32,
    work: u64,
    /// The work of second questions whose answers were not taken (see `ask`).
    lost: u64,
}

impl State {
    /// A phase run starts.
    pub(crate) fn begin(&mut self) {
        self.covered.clear();
        self.asked.clear();
        self.large = 0;
    }
}

/// Whether the walk asks `n` before it walks `n`'s operands (see [`first`]).
pub(crate) fn asks_first(r: &Runner<'_, '_>, cx: &Context, n: u32) -> bool {
    !r.words.covered.contains(n)
        && r.words.large < MAX_LARGE
        && r.words.work < MAX_WORK
        && !matches!(cx.node(n).op, OpCode::Const | OpCode::Sym)
        && !r.quarantined_passes.contains(&PassKind::Words)
}

/// The nodes under `n` when there are at most [`MAX_CONE`], operands before what uses them, in
/// an order that does not depend on how the expression was built: by height, then in the
/// context's canonical order. Otherwise whether they were counted to find that out.
fn cone(r: &mut Runner<'_, '_>, cx: &Context, n: u32) -> Result<Result<Vec<u32>, bool>, Stop> {
    // (A chain longer than the bound is more nodes than it.)
    if cx.meta[n as usize].height as usize >= MAX_CONE {
        return Ok(Err(false));
    }
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack = vec![n];
    let mut out = Vec::new();
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        out.push(i);
        if out.len() > MAX_CONE {
            r.meter.charge(Counter::PassWork, out.len() as u64)?;
            return Ok(Err(true));
        }
        stack.extend(cx.node(i).children());
    }
    r.meter.charge(Counter::PassWork, 2 * out.len() as u64)?;
    let height = |i: u32| cx.meta[i as usize].height;
    out.sort_by(|&a, &b| height(a).cmp(&height(b)).then_with(|| cx.order(a, b)));
    Ok(Ok(out))
}

/// The pass at a root, before the walk has come to its operands: `Some` rewrite when one is
/// taken, and the walk asks what the root became in turn, until nothing is found. The nodes
/// under a root that was asked are not asked in the phase run.
pub(crate) fn first(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<(u32, Fin)>, Stop> {
    r.words.covered.insert(n);
    let nodes = match cone(r, cx, n)? {
        Ok(nodes) => nodes,
        Err(counted) => {
            // (Too large to ask, which no budget changes; its operands are asked in turn.)
            r.words.large += u32::from(counted);
            r.words.asked.insert(n, Fin::FINAL);
            return Ok(None);
        }
    };
    for &i in &nodes {
        r.words.covered.insert(i);
    }
    if let Some(&fin) = r.words.quiet.get(&n) {
        r.words.asked.insert(n, fin);
        return Ok(None);
    }
    r.stats
        .passes
        .entry(PassKind::Words.name())
        .or_default()
        .calls += 1;
    let mut build = core::mem::take(&mut r.words.build);
    let out = ask(r, cx, &mut build, n, nodes);
    r.words.build = build;
    let (step, found) = out?;
    Ok(match step {
        Step::To(e, fin) => {
            // (Asked in turn, also where it is a node that was under the root.)
            r.words.covered.remove(e);
            Some((e, fin))
        }
        Step::Normal(fin) => {
            if !found {
                r.words.quiet.insert(n, fin);
            }
            r.words.asked.insert(n, fin);
            None
        }
    })
}

/// The search at root `n` over `nodes`, and whether it found anything (which the commit rule
/// may still refuse).
fn ask(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    build: &mut write::Build,
    n: u32,
    nodes: Vec<u32>,
) -> Result<(Step, bool), Stop> {
    let before = cx.len() as u32;
    // The forms are read anew for each root: what is found depends on the nodes under it
    // and nothing else. A root is asked up to three times, each with its own kind of forms
    // (see `form`): with XORs as atoms over the words truncations are of; where that took
    // an operand for what is not its value, with them over the values; and where
    // arithmetic was done on XORs, with XORs as sums without twice the AND, as before
    // there were atoms. Bitwise code is read by the atoms, arithmetic on an XOR by the
    // sums, and which operands read better depends on what is done with the truncations.
    // The smallest root is taken; of two as small, the later one's. (A later question may
    // take about twice the work of the first: where it would take more, its forms are the
    // ones that grow. And once the questions not taken have cost a call [`MAX_LOST`], only
    // the first is asked.)
    let mut lift = lift::Lift::default();
    let mut search = write::Search::new(&mut lift, build, nodes.clone());
    let found = search.run(r, cx);
    r.words.work += search.work();
    let found = found?;
    let mut fin = search.lift.fin.unwrap_or(Fin::FINAL);
    let allow = 2 * search.work() + SECOND_SLACK;
    let mut forked = search.lift.alg.forked();
    let (mut lift2, mut lift3) = (lift::Lift::values(), lift::Lift::plain());
    let (mut scratch2, mut scratch3) = (write::Build::default(), write::Build::default());
    let mut later = [None, None];
    if search.lift.alg.wordy() && r.words.lost < MAX_LOST {
        let mut second = write::Search::new(&mut lift2, &mut scratch2, nodes.clone());
        second.limit(allow);
        let other = second.run(r, cx);
        r.words.work += second.work();
        let other = other?;
        fin = fin.and(second.lift.fin.unwrap_or(Fin::FINAL));
        forked |= second.lift.alg.forked();
        later[0] = Some((second, other));
    }
    if forked && r.words.lost < MAX_LOST {
        let mut third = write::Search::new(&mut lift3, &mut scratch3, nodes);
        third.limit(allow);
        let other = third.run(r, cx);
        r.words.work += third.work();
        let other = other?;
        fin = fin.and(third.lift.fin.unwrap_or(Fin::FINAL));
        later[1] = Some((third, other));
    }
    let mut pick = None;
    let mut least = found.map(|f| f.1);
    for (i, leg) in later.iter().enumerate() {
        if let Some((_, Some((_, size)))) = leg
            && least.is_none_or(|x| *size <= x)
        {
            (pick, least) = (Some(i), Some(*size));
        }
    }
    for (i, leg) in later.iter().enumerate() {
        if let Some((s, _)) = leg
            && pick != Some(i)
        {
            r.words.lost += s.work();
        }
    }
    let e = match pick.and_then(|i| later[i].take()) {
        Some((mut taken, Some((root, _)))) => taken.export(r, cx, root)?,
        _ => {
            let Some((root, _)) = found else {
                r.stats
                    .passes
                    .entry(PassKind::Words.name())
                    .or_default()
                    .noop += 1;
                return Ok((Step::Normal(fin), false));
            };
            search.export(r, cx, root)?
        }
    };
    Ok((
        finish(r, cx, PassKind::Words, n, e, before, &[], fin)?,
        true,
    ))
}

/// The pass at `n` once its operands are walked: what [`first`] found for it. A node that was
/// not asked (it is under one that was) has no answer of its own: asked as a root, it may
/// have one.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &Context, n: u32) -> Result<Step, Stop> {
    let fin = match r.words.asked.get(&n) {
        Some(&fin) => fin,
        None if matches!(cx.node(n).op, OpCode::Const | OpCode::Sym) => Fin::FINAL,
        None => Fin::PROVISIONAL,
    };
    Ok(Step::Normal(fin))
}
