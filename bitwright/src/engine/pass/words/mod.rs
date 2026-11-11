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
//! Of a root's answers the smallest is taken, the sums' of two as small. An answer is asked
//! in turn, and the sums find in several steps what they find, so where the atoms' answer
//! is the smaller both are followed to where nothing more is found (the sums' with the sums
//! alone, as before there were atoms) and the smaller end is taken: what the atoms read
//! better at a root's first question is not taken for what the sums read better in the
//! end.
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
//! The pass asks in a round over a root the other phases left as it was (the engine's
//! `rounds`), and what it writes goes back to them: its reading is of the whole root, and a
//! root they are still folding is not yet the one to read.
//!
//! Words of up to 128 bits are read. The integers the pass computes in have 256 bits
//! ([`int`]): a word, a coefficient and a shift on top of it need more than 128. A question
//! with no node above 64 bits is read within the bounds the pass was made with for 64-bit
//! words, so that it finds what it found; a wider one within bounds that hold its words.
//!
//! The reading uses the facts (bounds and known bits) of the nodes, so a result relies on
//! what they relied on. Coefficients, shifts, the terms of a form, the nodes under a root and
//! the work of one question are bounded ([`form`] and [`write`]): past a bound a node is the
//! value it is, or the question is not asked, which no budget changes.

mod form;
mod int;
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
/// What a root's later questions may each take beyond twice the work of its first (see
/// `answers`).
const SECOND_SLACK: u64 = 1 << 14;
/// The most work of later questions whose answers were not taken, in a call: past it none
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
    /// The work of later questions whose answers were not taken (see `answers`).
    lost: u64,
    /// The root the sums' answer was taken for last: the sums are asked there whatever the
    /// atoms read (see `ask`).
    sums_at: Option<u32>,
    /// Whether the pass asks in this round: only in one over a root the other phases left as
    /// it was (see the engine's `rounds`). What it writes is a reading of the whole root, and
    /// written while the other phases were still at work it took the forms their questions
    /// read: in 140 measured calls over obfuscated code (no limb arithmetic in them) seven of
    /// 47 constants and four of 16 proofs the opaque-constant sweep finds in a later round
    /// were lost, at half again the time.
    pub(crate) turn: bool,
}

impl State {
    /// A phase run starts.
    pub(crate) fn begin(&mut self) {
        self.covered.clear();
        self.asked.clear();
        self.large = 0;
        self.sums_at = None;
    }
}

/// What the questions at a root found (see `answers`).
struct Answers {
    first: Leg,
    values: Option<Leg>,
    sums: Option<Leg>,
    /// The atoms' answer is the values'.
    second: bool,
    fin: Fin,
}

impl Answers {
    /// The atoms' answer: the smaller of the two, the values' of two as small. The
    /// question, the root and the size of its DAG.
    fn atoms(&self) -> Option<(&Leg, u32, u32)> {
        let l = match &self.values {
            Some(v) if self.second => v,
            _ => &self.first,
        };
        l.found.map(|f| (l, f.0, f.1))
    }

    /// The sums' answer.
    fn sums(&self) -> Option<(&Leg, u32, u32)> {
        let l = self.sums.as_ref()?;
        l.found.map(|f| (l, f.0, f.1))
    }

    /// The smallest answer, the sums' of two as small.
    fn least(&self) -> Option<(&Leg, u32, u32)> {
        match (self.atoms(), self.sums()) {
            (Some(a), Some(s)) => Some(if s.2 <= a.2 { s } else { a }),
            (a, s) => s.or(a),
        }
    }

    /// Whether `l` is the sums' question.
    fn of_sums(&self, l: &Leg) -> bool {
        self.sums.as_ref().is_some_and(|s| core::ptr::eq(s, l))
    }
}

/// What a question found: the root in its scratch DAG and the size of its DAG, when it is
/// another than the root asked.
struct Leg {
    build: write::Build,
    found: Option<(u32, u32)>,
    work: u64,
    fin: Fin,
    forked: bool,
    wordy: bool,
}

/// One question: the search over `nodes` with the forms of `lift`, in `build`, within
/// `limit` of work when one is given.
fn leg(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    mut lift: lift::Lift,
    mut build: write::Build,
    nodes: Vec<u32>,
    limit: Option<u64>,
) -> Result<Leg, Stop> {
    let mut search = write::Search::new(&mut lift, &mut build, nodes);
    if let Some(limit) = limit {
        search.limit(limit);
    }
    let found = search.run(r, cx);
    let work = search.work();
    r.words.work += work;
    let found = found?;
    Ok(Leg {
        build,
        found,
        work,
        fin: lift.fin.unwrap_or(Fin::FINAL),
        forked: lift.alg.forked(),
        wordy: lift.alg.wordy(),
    })
}

/// Whether the walk asks `n` before it walks `n`'s operands (see [`first`]).
pub(crate) fn asks_first(r: &Runner<'_, '_>, cx: &Context, n: u32) -> bool {
    r.words.turn
        && !r.words.covered.contains(n)
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

/// The questions at a root over `nodes`, the first in `build`. A root is asked up to three
/// times, each with its own kind of forms (see `form`): with XORs as atoms over the words
/// truncations are of; where that took an operand for what is not its value, with them over
/// the values; and where arithmetic was done on XORs (or `with_sums`: the root is the sums'
/// own answer), with XORs as sums without twice the AND, as before there were atoms.
/// Bitwise code is read by the atoms, arithmetic on an XOR by the sums, and which operands
/// read better depends on what is done with the truncations. (A later question may take
/// about twice the work of the first: where it would take more, its forms are the ones
/// that grow, though the sums' question is cut short at times where they do not. And once
/// the questions not taken have cost a call [`MAX_LOST`], only the first is asked.)
fn answers(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    build: write::Build,
    nodes: Vec<u32>,
    with_sums: bool,
) -> Result<Answers, Stop> {
    let first = leg(r, cx, lift::Lift::default(), build, nodes.clone(), None)?;
    let mut fin = first.fin;
    let allow = 2 * first.work + SECOND_SLACK;
    let mut forked = first.forked || with_sums;
    let mut values = None;
    if first.wordy && r.words.lost < MAX_LOST {
        let l = leg(
            r,
            cx,
            lift::Lift::values(),
            write::Build::default(),
            nodes.clone(),
            Some(allow),
        )?;
        fin = fin.and(l.fin);
        forked |= l.forked;
        values = Some(l);
    }
    let mut sums = None;
    if forked && r.words.lost < MAX_LOST {
        let l = leg(
            r,
            cx,
            lift::Lift::plain(),
            write::Build::default(),
            nodes,
            // (At their own answer the sums are asked as before there were atoms.)
            (!with_sums).then_some(allow),
        )?;
        fin = fin.and(l.fin);
        if l.found.is_none() {
            r.words.lost += l.work;
        }
        sums = Some(l);
    }
    let size = |l: &Leg| l.found.map(|f| f.1);
    let second = match (size(&first), values.as_ref().and_then(size)) {
        (_, None) => false,
        (None, Some(_)) => true,
        (Some(a), Some(v)) => v <= a,
    };
    if let Some(v) = &values
        && !second
    {
        r.words.lost += v.work;
    }
    Ok(Answers {
        first,
        values,
        sums,
        second,
        fin,
    })
}

/// The root the answers come to from `e`, a node made for the question that is no one's
/// yet: asked until nothing is found, with the sums alone (`alone`) or with every kind of
/// forms, the smallest answer taken (and the sums asked on at a root that is their own
/// answer, as `ask` does). The roots on the way are made in the context and are no one's
/// either. Each has a smaller DAG than the one before, as the commit rule has it of the
/// roots that are taken: an answer that is not smaller once the context has built it is
/// not followed, so the answers end.
fn chase(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    mut e: u32,
    alone: bool,
    fin: &mut Fin,
) -> Result<u32, Stop> {
    let mut with_sums = false;
    // The root `e` is the answer at, and the size of its DAG.
    let mut from: Option<(u32, usize)> = None;
    while !matches!(cx.node(e).op, OpCode::Const | OpCode::Sym) {
        let nodes = match cone(r, cx, e)? {
            Ok(nodes) if from.is_none_or(|(_, size)| nodes.len() < size) => nodes,
            _ => {
                if let Some((before, _)) = from {
                    e = before;
                }
                break;
            }
        };
        if r.words.work >= MAX_WORK {
            break;
        }
        from = Some((e, nodes.len()));
        if alone {
            let l = leg(
                r,
                cx,
                lift::Lift::plain(),
                write::Build::default(),
                nodes,
                None,
            )?;
            *fin = fin.and(l.fin);
            let Some((root, _)) = l.found else {
                break;
            };
            e = l.build.write(r, cx, root)?;
        } else {
            let a = answers(r, cx, write::Build::default(), nodes, with_sums)?;
            *fin = fin.and(a.fin);
            let Some((l, root, _)) = a.least() else {
                // (Nothing is found at `e`, which no later question changes.)
                r.words.quiet.insert(e, a.fin);
                break;
            };
            with_sums = a.of_sums(l);
            e = l.build.write(r, cx, root)?;
        }
    }
    Ok(e)
}

/// The size of the DAG of `e`, a root an answer was written as; `or` where it is too large
/// to be asked.
fn dag(r: &mut Runner<'_, '_>, cx: &Context, e: u32, or: u32) -> Result<u32, Stop> {
    Ok(match cone(r, cx, e)? {
        Ok(nodes) => nodes.len() as u32,
        Err(_) => or,
    })
}

/// The nodes made since there were `before` that `e` does not reach are no one's: they do
/// not count as uses of their operands (as a refused candidate's do not; see `discard`).
fn unused(r: &mut Runner<'_, '_>, cx: &Context, before: u32, e: u32) -> Result<(), Stop> {
    let len = cx.len() as u32;
    r.meter
        .charge(Counter::PassWork, u64::from(len.saturating_sub(before)))?;
    let mut reached: IdMap<u32, ()> = IdMap::default();
    let mut stack = vec![e];
    while let Some(i) = stack.pop() {
        if i >= before && reached.insert(i, ()).is_none() {
            stack.extend(cx.node(i).children());
        }
    }
    for i in before..len {
        if !reached.contains_key(&i) {
            r.retire(cx, i);
        }
    }
    Ok(())
}

/// The answer `e` for `n` under the commit rule, and whether it stands as found: with
/// [`Strategy::words_proved`](crate::engine::Strategy::words_proved), an answer no circuit
/// and search prove is not one.
fn committed(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    e: u32,
    before: u32,
    fin: Fin,
) -> Result<(Step, bool), Stop> {
    if r.inner.strategy.words_proved && e != n && !proved(r, cx, n, e)? {
        r.stats
            .passes
            .entry(PassKind::Words.name())
            .or_default()
            .noop += 1;
        return Ok((Step::Normal(fin), false));
    }
    Ok((
        finish(r, cx, PassKind::Words, n, e, before, &[], fin)?,
        true,
    ))
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
    // A question with a node of more than 64 bits is read within the wider bounds.
    let wide = nodes.iter().any(|&i| cx.node(i).width > 64);
    let _bounds = form::Wide::set(wide);
    // The forms are read anew for each root: what is found depends on the nodes under it
    // and nothing else. The smallest answer is taken, the sums' of two as small, and the
    // root the sums' answer is, is asked with the sums as well whatever the atoms read
    // there: a root nothing but sums read is read as before there were atoms, each step of
    // it.
    //
    // Where the atoms' answer is the smaller one, the smallest is not known yet: an answer
    // is asked in turn, and the sums find in several steps what they find, each from the
    // root the one before left, where the atoms' smaller root may be one nothing more is
    // found from. So both are followed to where nothing is found, the sums' answer with the
    // sums alone (what was done before there were atoms) and the atoms' with every kind,
    // and the end with the smaller DAG is taken, the atoms' of two as small. What was made
    // on the way to the other is no one's.
    let with_sums = r.words.sums_at.take() == Some(n);
    let a = answers(r, cx, core::mem::take(build), nodes, with_sums)?;
    let mut fin = a.fin;
    let out = match (a.atoms(), a.sums()) {
        (Some((la, ra, sa)), Some((ls, rs, ss))) if sa < ss => {
            // (The questions on the way to the end that is not taken are questions whose
            // answers were not taken.)
            let es = ls.build.write(r, cx, rs)?;
            let asked = r.words.work;
            let es = chase(r, cx, es, true, &mut fin)?;
            let of_sums = r.words.work - asked;
            let (asked, lost) = (r.words.work, r.words.lost);
            let ea = la.build.write(r, cx, ra)?;
            let ea = chase(r, cx, ea, false, &mut fin)?;
            let e = if dag(r, cx, es, ss)? < dag(r, cx, ea, sa)? {
                r.words.lost = lost + (r.words.work - asked);
                es
            } else {
                r.words.lost += ls.work + of_sums;
                ea
            };
            unused(r, cx, before, e)?;
            committed(r, cx, n, e, before, fin)?
        }
        _ => match a.least() {
            Some((l, root, _)) => {
                let e = l.build.write(r, cx, root)?;
                let (step, found) = committed(r, cx, n, e, before, fin)?;
                if let Step::To(e, _) = step
                    && a.of_sums(l)
                {
                    r.words.sums_at = Some(e);
                }
                (step, found)
            }
            None => {
                r.stats
                    .passes
                    .entry(PassKind::Words.name())
                    .or_default()
                    .noop += 1;
                (Step::Normal(fin), false)
            }
        },
    };
    *build = a.first.build;
    Ok(out)
}

/// The gates of a proof's circuit and the propagations of its search, at most
/// ([`Strategy::words_proved`](crate::engine::Strategy::words_proved)).
#[cfg(feature = "prove")]
const PROOF_NODES: usize = 1 << 18;
/// See [`PROOF_NODES`].
#[cfg(feature = "prove")]
const PROOF_PROPAGATIONS: u64 = 1 << 23;

/// Whether what the pass made of `n` is proved equal to it, by a prover that knows nothing
/// of the pass: a circuit of both and a search, over a scratch copy.
#[cfg(feature = "prove")]
fn proved(r: &mut Runner<'_, '_>, cx: &Context, n: u32, e: u32) -> Result<bool, Stop> {
    use crate::engine::oracle::{EqualityCaps, EqualityVerdict};
    let mut scx = Context::new();
    let both = match scx.import(cx, &[cx.handle(n), cx.handle(e)]) {
        Ok(both) => both,
        // (An extension operation: a scratch context has no registry.)
        Err(crate::Error::Unsupported(_)) => return Ok(false),
        Err(e) => return Err(Stop::Error(e)),
    };
    let caps = EqualityCaps {
        samples: 64,
        max_nodes: PROOF_NODES,
        max_propagations: PROOF_PROPAGATIONS,
    };
    let out =
        (crate::circuit_equality())(&mut scx, both[0], both[1], &caps).map_err(Stop::Error)?;
    let left = r.meter.left_in(|b| b.pass_work);
    r.meter
        .charge(Counter::PassWork, (out.nodes as u64).min(left))?;
    Ok(out.verdict == EqualityVerdict::Proved)
}

/// Without a prover nothing is proved.
#[cfg(not(feature = "prove"))]
fn proved(_: &mut Runner<'_, '_>, _: &Context, _: u32, _: u32) -> Result<bool, Stop> {
    Ok(false)
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
