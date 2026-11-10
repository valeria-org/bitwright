//! Limbs read as slices of the word they are limbs of.
//!
//! Arithmetic done in limbs computes its lowest limb at the register's full width and masks
//! it (`R0 = F(A, B) & M`), and each higher limb digit by digit, with the carries and borrows
//! between them taken by comparisons of the limbs below. The word `F(A, B)` is therefore a node
//! below every limb, and limb `i` is `extract<off_i, k_i>` of it: three limbs of `(w + k) ^ c`
//! are ninety nodes of digits, carries and borrows, and the top one is `extract<24, 8>(w + k ^
//! c)`.
//!
//! For a value with a carry below it, every wide arithmetic node `B` below and every offset
//! `o` a limb may start at (the bits the nodes between shift, slice and mask by, and the sums
//! of two of them) is a candidate `extract<o, j>(B)`. Those that agree with the value at
//! every verification sample are tried, words before values that hold comparisons themselves
//! (a limb is as often the slice of another handler's unfinished sum, which then is one node
//! for both) and smaller ones first, and the first one the native prover proves equal
//! replaces the value. Only a proof commits. The proof is of the two copied into a scratch
//! context, without the engine's simplification (so no recursion into the engine), within an
//! AIG-node cap and a propagation cap and what is left of the pass work.
//!
//! # Proofs that are not asked
//!
//! A proof that ends undecided at its cap costs fifty times what the median proved one does,
//! and four fifths of the propagations went to such proofs. They come in runs: a limb several
//! handlers above its word is hard, and so is every other read of its sum and every limb
//! built on it. So what one undecided proof says is kept for the call:
//!
//! - the candidate after one left undecided is not tried (of 189 such second candidates on
//!   600 limb windows, 3 were proved);
//! - the sums and comparisons a question has of its own (those of the value that are not
//!   below the candidate: the limb code the proof has to see through) are remembered when
//!   it ends undecided, and a question most of whose own are among them is not asked: it is
//!   the same limb code read at other bits, or under one more digit;
//! - a call whose proofs keep running into the caps asks no more of them, and leaves the
//!   values it did not ask about provisional.
//!
//! # Products in the copy
//!
//! A limb's proof against its word is over the handler, whatever computes its operands: a
//! product or a shift by a variable below both sides is copied as a fresh symbol (an identity
//! over a free symbol holds at every value the node takes), which keeps the multiplier out of
//! the search. Where that copy is refuted (the limbs compute the product themselves, digit
//! by digit, or need its low zeros), the two are copied as they are.
//!
//! # Words that are no node
//!
//! A handler that adds a constant adds it limb by limb: the node its low limb is masked from
//! is `B + c_lo`, right in its low bits only, and a higher limb is `extract<k, j>(B + c_lo) +
//! c_hi`, a slice of the word `B + (c_hi << k | c_lo)`, which nothing computes. And a limb's
//! raw sum read wider than the limb holds the carry out of its register: it is a slice of the
//! sum of the operands zero-extended. So where no slice of a node is proved, the candidates
//! are slices of such words: for each wide node `B` and offset, `B` without its own constant
//! plus the constant the samples give (the difference at one sample, checked at the rest;
//! where the difference takes two values one apart, the higher one exactly where the bits
//! below the slice are the larger, the constant also has low bits, taken among the constants
//! the cone adds); and for a slice that reaches past `B`'s width, `B`'s operands
//! zero-extended to 64 bits, added or subtracted, plus such a constant. Only over nodes with
//! no comparison below them (words, not unfinished sums), one candidate a value (the
//! smallest, in the canonical order), proved under a lower cap (nine in ten of those proved
//! take no search: with the sums written one way the two sides are the same sums), and
//! committed where the DAG gets no larger. The word is then one node for the other limbs to
//! be slices of.
//!
//! Such a word is over nodes below the sum read, and never that sum's own operand over
//! another constant: the slice of a word made is made again only over nodes further down, or
//! over one of its two operands alone, so a chain of these ends.

use super::{Fin, PassKind, Runner, Step, Stop, finish_within};
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::BinOp;
use crate::prove::{self, Outcome, Unknown};
use crate::{BitVec, SymbolKey, Width};

/// The most nodes walked below a value.
const MAX_CONE: usize = 512;

/// The most candidates proved for one value. The first is the likeliest: on a sample of 2,500
/// limb windows, a second took the nodes saved from 7.5% to 7.7%.
const MAX_PROOFS: usize = 2;

/// The most AIG nodes a proof may build.
const MAX_AIG_NODES: usize = 1 << 15;

/// The most SAT propagations a proof may take, and how many of them go first to the
/// question with its sums written one way on both sides ([`prove::Config::shared_sums`]: a
/// limb whose word adds the same digits is then proved with few or none); the rest go to
/// the question as asked. What is not proved by then is mostly a limb several handlers
/// above its word. (One allowance for both: a question left undecided costs what it did.)
const SHARED_PROPAGATIONS: u64 = 1 << 14;
const ASKED_PROPAGATIONS: u64 = 1 << 17;

const _: () = assert!(SHARED_PROPAGATIONS <= ASKED_PROPAGATIONS);

/// The proofs a call may leave undecided at their caps beyond the number it has proved (on
/// the corpus of 58,530 windows: 0.3% more nodes than without the limit, for an eighth less
/// time).
const MAX_UNDECIDED: u32 = 8;

/// Units of pass work charged per SAT propagation (as the carries pass charges them).
const PROPAGATION_RATE: u64 = 4;

/// The fewest sums and comparisons of its own a question is judged by (see [`own`]): with
/// fewer, what the undecided proofs before it left says little.
const MIN_OWN: usize = 8;

/// A value read: `n` holds bits `[lo, lo + len)` of `s`, `k` bits up, and nothing else (a
/// truncation, mask, slice or left shift of the sum `s`; or `s` itself, of which those bits
/// are all that is not known to be zero).
#[derive(Clone, Copy)]
pub(super) struct Read {
    pub n: u32,
    pub s: u32,
    pub lo: u16,
    pub len: u16,
    pub k: u16,
    /// Whether its proofs count apart from those of the truncations, masks and shifts of a
    /// sum and of a sum read whole (see [`MAX_UNDECIDED`]): a slice above the low bits, a
    /// value made with `|` or `concat`.
    pub apart: bool,
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry(PassKind::Carries.name()).or_default()
}

/// Whether `op` computes a word a limb may be a slice of.
fn word(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Neg
            | OpCode::Not
    )
}

fn ones(bits: u16) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1 << bits) - 1
    }
}

fn low(v: &BitVec) -> u64 {
    v.limbs()[0]
}

/// The nodes below a value, and what they say of limbs.
struct Cone {
    /// At most [`MAX_CONE`], nearest first.
    nodes: Vec<u32>,
    /// The offsets a limb may start at: the bits the nodes shift by, slice from and to, and
    /// mask to, and the sums of two of those (the third limb starts where the first two end,
    /// which no node need spell out).
    offsets: Vec<u16>,
    /// Whether one of them is a comparison, or a slice above the low bits of a sum (what a
    /// carry the borrows pass read becomes: the high digits of the sums compared).
    compares: bool,
}

fn cone(cx: &Context, n: u32) -> Cone {
    let mut nodes = vec![n];
    let mut seen = IdMap::default();
    seen.insert(n, ());
    let mut cuts: Vec<u16> = Vec::new();
    let mut compares = false;
    let mut at = 0;
    while at < nodes.len() && nodes.len() < MAX_CONE {
        let i = nodes[at];
        at += 1;
        let node = cx.node(i);
        compares |= node.op == OpCode::Ult
            || (node.op == OpCode::Extract
                && node.b > 0
                && matches!(cx.node(node.a).op, OpCode::Add | OpCode::Sub));
        match node.op {
            OpCode::Extract => {
                cuts.extend([node.b as u16, node.b as u16 + node.width]);
            }
            OpCode::Shl | OpCode::LShr => {
                if let Some(k) = cx.const_val(node.b).and_then(|k| k.to_u64()) {
                    cuts.extend(u16::try_from(k).ok());
                }
            }
            OpCode::And if node.width <= 64 => {
                for c in [node.a, node.b] {
                    if let Some(m) = cx.const_val(c).map(|m| m.limbs()[0]) {
                        let k = m.trailing_ones();
                        if k > 0 && k < u32::from(node.width) && m >> k == 0 {
                            cuts.push(k as u16);
                        }
                    }
                }
            }
            _ => {}
        }
        for c in node.children() {
            if seen.insert(c, ()).is_none() {
                nodes.push(c);
            }
        }
    }
    cuts.retain(|&k| k > 0 && k < 64);
    cuts.sort_unstable();
    cuts.dedup();
    let mut offsets = cuts.clone();
    for (x, &a) in cuts.iter().enumerate() {
        offsets.extend(cuts[x..].iter().map(|&b| a + b).filter(|&k| k < 64));
    }
    offsets.sort_unstable();
    offsets.dedup();
    Cone {
        nodes,
        offsets,
        compares,
    }
}

/// Whether a comparison is below `i`, among the nodes of `below` (a cone's).
fn holds_compare(cx: &Context, i: u32, memo: &mut IdMap<u32, bool>) -> bool {
    if let Some(&v) = memo.get(&i) {
        return v;
    }
    // (Marked first: the DAG has no cycles, and a node met again while open is below itself
    // in no way.)
    memo.insert(i, false);
    let node = cx.node(i);
    let v = node.op == OpCode::Ult || node.children().any(|c| holds_compare(cx, c, memo));
    memo.insert(i, v);
    v
}

/// The sums and comparisons of the cone that are not below the candidate (below `below`, its
/// operands): what the question has of its own, the limb code the proof has to see through
/// (what is below the candidate is one circuit for both sides); with the nodes walked. (Below
/// the candidate at most four cones' worth is walked: a node of the cone further down counts
/// as the question's own.)
fn own(cx: &Context, cone: &Cone, below: &[u32]) -> (Vec<u32>, u64) {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack = below.to_vec();
    while let Some(i) = stack.pop() {
        if seen.len() >= 4 * MAX_CONE {
            break;
        }
        if seen.insert(i, ()).is_none() {
            stack.extend(cx.node(i).children());
        }
    }
    let nodes = cone
        .nodes
        .iter()
        .copied()
        .filter(|i| {
            matches!(
                cx.node(*i).op,
                OpCode::Add | OpCode::Sub | OpCode::Ult | OpCode::Eq
            ) && !seen.contains_key(i)
        })
        .collect();
    (nodes, (seen.len() + cone.nodes.len()) as u64)
}

/// Whether a proof copies `i` as a fresh symbol (see the module): a product, or a shift by a
/// variable. (Not a product by a power of two or by its negation, which is a shift: the
/// limbs of `a + b − 2·(a & b)` read into it.)
fn opaque(cx: &Context, i: u32) -> bool {
    let node = cx.node(i);
    let shift = |c: u32| {
        cx.const_val(c).is_some_and(|v| {
            let v = v.limbs()[0] & ones(node.width.min(64));
            let n = v.wrapping_neg() & ones(node.width.min(64));
            v.is_power_of_two() || n.is_power_of_two()
        })
    };
    match node.op {
        OpCode::Mul => node.width > 64 || !(shift(node.a) || shift(node.b)),
        OpCode::Shl | OpCode::LShr | OpCode::AShr => !cx.is_const(node.b),
        _ => false,
    }
}

/// A word a limb may be a slice of: the node `a`, or a word that is no node yet (see the
/// module): `a`, or with `with` the sum or difference of `a` and a second node, each
/// zero-extended to 64 bits first where `wide`, plus the constant `k`.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Word {
    a: u32,
    with: Option<(BinOp, u32)>,
    wide: bool,
    k: u64,
}

impl Word {
    fn node(a: u32) -> Self {
        Word {
            a,
            with: None,
            wide: false,
            k: 0,
        }
    }

    /// The nodes it is over.
    fn operands(&self) -> impl Iterator<Item = u32> {
        core::iter::once(self.a).chain(self.with.map(|(_, b)| b))
    }

    /// Its value where the operands are `x` and `y`, at `w` bits.
    fn value(&self, w: u16, x: u64, y: u64) -> u64 {
        let v = match self.with {
            None => x,
            Some((BinOp::Sub, _)) => x.wrapping_sub(y),
            Some(_) => x.wrapping_add(y),
        };
        v.wrapping_add(self.k) & ones(if self.wide { 64 } else { w })
    }

    /// The word in `cx`, over `a` and `b` for its operands (themselves, or their copies in
    /// another context).
    fn build(&self, cx: &mut Context, a: u32, b: Option<u32>) -> Result<u32, crate::Error> {
        let w = if self.wide { 64 } else { cx.wid(a) };
        let mut e = cx.c_zext(a, w)?;
        if let (Some((op, _)), Some(b)) = (self.with, b) {
            let y = cx.c_zext(b, w)?;
            e = cx.c_bin(op, e, y)?;
        }
        if self.k != 0 {
            let k = cx.mk_const_u64(w, self.k)?;
            e = cx.c_bin(BinOp::Add, e, k)?;
        }
        Ok(e)
    }
}

/// What the prover says of bits `[lo, lo + len)` of `s` and `extract<o, len>` of `word`
/// being equal, over a scratch copy of both, within `propagations`: with the AIG nodes built,
/// the propagations taken, and the nodes the copy has fresh symbols for (the highest
/// [`opaque`] nodes below the two but those of `uncut`; none without it).
fn asked(
    cx: &Context,
    (s, lo): (u32, u16),
    (word, o): (&Word, u16),
    len: u16,
    uncut: Option<&IdMap<u32, ()>>,
    propagations: u64,
) -> Result<(Outcome, u64, u64, Vec<u32>), crate::Error> {
    let mut scx = Context::new();
    let mut pre: Vec<(u32, u32)> = Vec::new();
    if let Some(uncut) = uncut {
        // The highest opaque nodes below the two, in the order a walk meets them. (Keys no
        // symbol of the context has: the copy shares its symbols.)
        let mut seen: IdMap<u32, ()> = IdMap::default();
        let mut stack: Vec<u32> = word.operands().skip(1).chain([word.a, s]).collect();
        let mut key = 0u64;
        while let Some(i) = stack.pop() {
            if seen.insert(i, ()).is_some() {
                continue;
            }
            if !opaque(cx, i) || uncut.contains_key(&i) {
                stack.extend(cx.node(i).children());
                continue;
            }
            let k = loop {
                let k = SymbolKey::U64(key);
                key += 1;
                if cx.find_symbol(&k).is_none() {
                    break k;
                }
            };
            let e = scx.symbol(k, cx.width_of(i))?;
            pre.push((i, scx.id(e)?));
        }
    }
    let roots: Vec<_> = core::iter::once(s)
        .chain(word.operands())
        .map(|i| cx.handle(i))
        .collect();
    let both = scx.import_mapped(cx, &roots, &pre)?;
    let jw = Width::new(len)?;
    let lhs = scx.extract(both[0], lo, jw)?;
    let (a, b) = (
        scx.id(both[1])?,
        both.get(2).map(|&b| scx.id(b)).transpose()?,
    );
    let made = word.build(&mut scx, a, b)?;
    let rhs = scx.extract(scx.handle(made), o, jw)?;
    let cfg = prove::Config::default()
        .with_simplify(false)
        .with_certificate(false)
        // (A candidate that only agrees at the few verification samples is refuted by these
        // before any search.)
        .with_samples(256)
        .with_max_nodes(MAX_AIG_NODES)
        .with_max_conflicts(u64::MAX)
        .with_max_propagations(propagations.min(ASKED_PROPAGATIONS))
        // (Measured on 600 limb windows: with these two encodings 31 more of 2,762 proofs
        // that pass the samples are decided, in 8% fewer propagations.)
        .with_carry_save_multiplication(true)
        .with_xor3_encoding(true);
    // The sums written one way first, under its own cap; then the question as asked, with
    // what the first left (in the same search where writing the sums again changed nothing).
    let grown = scx.len();
    let cfg1 = cfg
        .with_shared_sums(true)
        .with_max_propagations(propagations.min(SHARED_PROPAGATIONS));
    let mut q = prove::Question::equal(&mut scx, lhs, rhs, &cfg1)?;
    let mut out = q.solve(&mut scx, cfg1.limits())?;
    let mut early: Option<(usize, u64)> = None;
    if let Outcome::Unknown(Unknown::Budget { .. }) = &out {
        let rest = propagations - q.stats().propagations.min(propagations);
        if rest != 0 && q.stats().rewritten {
            early = Some((q.stats().nodes, q.stats().propagations));
            let cfg2 = cfg.with_samples(0).with_max_propagations(rest);
            q = prove::Question::equal(&mut scx, lhs, rhs, &cfg2)?;
            out = q.solve(&mut scx, cfg2.limits())?;
        } else if rest != 0 {
            let limits = prove::Limits {
                conflicts: u64::MAX,
                propagations: rest,
            };
            out = q.solve(&mut scx, limits)?;
        }
    }
    let grown = scx.len() - grown;
    let mut stats = q.stats();
    let mut nodes = match &out {
        Outcome::Unknown(Unknown::TooLarge { nodes }) => *nodes,
        _ => stats.nodes,
    };
    // (Both circuits and both searches are charged, and the nodes the sums were written in.)
    nodes += grown;
    if let Some((n, p)) = early {
        nodes += n;
        stats.propagations += p;
    }
    Ok((
        out,
        nodes as u64,
        stats.propagations,
        pre.into_iter().map(|(i, _)| i).collect(),
    ))
}

/// What a question came to.
enum Said {
    Proved,
    Refuted,
    /// Not decided within the pass's own caps (the same under any budget), or not asked
    /// because the undecided proofs before it say it would not be (see the module).
    Undecided,
}

/// A question's shape: its own sums and comparisons by their operations and widths and their
/// operands' (constants by value), and the bits asked, whatever is below. The limb code of an
/// undecided question has it again once a later round has rewritten something under it.
fn shape(cx: &Context, own: &[u32], lo: u16, o: u16, len: u16) -> u64 {
    let mix = |h: u64, x: u64| {
        let mut z = (h ^ x).wrapping_add(0x9e37_79b9_7f4a_7c15);
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    // (Sums of the nodes' and of the operands' hashes: in no order.)
    let sig = |i: u32| {
        let node = cx.node(i);
        let top = mix(node.op as u64, u64::from(node.width));
        node.children().fold(top, |h, c| {
            let kid = cx.node(c);
            let v = cx.const_val(c).map_or(0, |v| v.limbs()[0]);
            h.wrapping_add(mix(mix(kid.op as u64, u64::from(kid.width)), v))
        })
    };
    let bits = u64::from(lo) << 32 | u64::from(o) << 16 | u64::from(len);
    own.iter().fold(mix(bits, own.len() as u64), |h, &i| {
        h.wrapping_add(mix(sig(i), 1))
    })
}

/// Whether bits `[lo, lo + len)` of `s` (whose cone is `cone`) equal `extract<o, len>` of
/// `word`, by the native prover over a scratch copy of both within `cap` propagations: first
/// with the products below them fresh symbols, then, where that is refuted (a fresh symbol
/// takes values its node never does, or the limbs compute the product themselves), of the
/// two as they are. `Err` when the proof was not asked, with what that makes of the node's
/// finality: for lack of pass work, or because the call's proofs keep running into their
/// caps (another call may ask it).
#[allow(clippy::too_many_arguments)]
fn proved(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    cone: &Cone,
    (s, lo): (u32, u16),
    (word, o): (&Word, u16),
    len: u16,
    class: usize,
    cap: u64,
) -> Result<Result<Said, Fin>, Stop> {
    // The limbs of a call are alike: where the prover keeps running into its caps (limbs
    // several handlers deep), the next proof would too.
    let (proofs, undecided) = r.carries.fits[class];
    if undecided >= MAX_UNDECIDED + proofs {
        return Ok(Err(Fin::PROVISIONAL));
    }
    // The limb code this question has of its own: where most of it is what an undecided
    // proof had, or all of it has the shape of what one had, this is that question again
    // (another read of the sum, one more digit, the same limbs over operands rewritten).
    let below: Vec<u32> = word.operands().collect();
    let (own, walked) = own(cx, cone, &below);
    r.meter.charge(Counter::PassWork, walked)?;
    let hard = own
        .iter()
        .filter(|i| r.carries.hard.contains_key(i))
        .count();
    let shape = shape(cx, &own, lo, o, len);
    if (own.len() >= MIN_OWN && 4 * hard >= 3 * own.len())
        || (2 * own.len() >= MIN_OWN && r.carries.shapes.contains_key(&shape))
    {
        return Ok(Ok(Said::Undecided));
    }
    let mut cut = true;
    // The fresh symbols of a copy that was refuted.
    let mut failed: Vec<u32> = Vec::new();
    loop {
        let left = r.meter.left_in(|b| b.pass_work);
        let propagations = cap.min(left.saturating_sub(MAX_AIG_NODES as u64) / PROPAGATION_RATE);
        if propagations == 0 {
            return Ok(Err(Fin::capped(crate::engine::Exhausted::PassWork)));
        }
        let (out, nodes, taken, fresh) = asked(
            cx,
            (s, lo),
            (word, o),
            len,
            cut.then_some(&r.carries.uncut),
            propagations,
        )
        .map_err(Stop::Error)?;
        let cost = nodes
            .saturating_add(taken.saturating_mul(PROPAGATION_RATE))
            .min(left);
        r.meter.charge(Counter::PassWork, cost)?;
        // (A copy with fresh symbols that is refuted says nothing of the two.)
        if !fresh.is_empty() && matches!(out, Outcome::Refuted(_)) {
            cut = false;
            failed = fresh;
            continue;
        }
        // Not refuted as they are: it was the fresh symbols, which the limbs of this call
        // read into (the next copy keeps those products).
        if !matches!(out, Outcome::Refuted(_)) {
            r.carries.uncut.extend(failed.drain(..).map(|i| (i, ())));
        }
        let c = count(r);
        c.proofs += 1;
        return Ok(match out {
            Outcome::Proved(_) => {
                c.proved += 1;
                r.carries.fits[class].0 += 1;
                Ok(Said::Proved)
            }
            Outcome::Refuted(_) => {
                c.refuted += 1;
                Ok(Said::Refuted)
            }
            // Stopped short of the pass's own cap: more pass work may decide it.
            Outcome::Unknown(Unknown::Budget { .. }) if propagations < cap => {
                c.unknown += 1;
                Err(Fin::capped(crate::engine::Exhausted::PassWork))
            }
            Outcome::Unknown(why) => {
                c.unknown += 1;
                // (A circuit too large says nothing of the search, and neither does a
                // search under a lower cap.)
                if cap == ASKED_PROPAGATIONS {
                    r.carries.fits[class].1 += 1;
                    if why.is_budget() {
                        r.carries.shapes.insert(shape, ());
                        r.carries.hard.extend(own.into_iter().map(|i| (i, ())));
                    }
                }
                Ok(Said::Undecided)
            }
        });
    }
}

/// `e` zero-extended to `w` bits and shifted left by `k`: a limb's low bits as the node that
/// read them holds them.
pub(super) fn held(cx: &mut Context, e: u32, w: u16, k: u16) -> Result<u32, crate::Error> {
    let e = cx.c_zext(e, w)?;
    if k == 0 {
        return Ok(e);
    }
    let by = cx.mk_const(&BitVec::wrapping_from_u64(Width::new(w)?, u64::from(k)))?;
    cx.c_bin(BinOp::Shl, e, by)
}

/// A candidate: `extract<o, len>` of `b` for the bits read.
#[derive(Clone, Copy)]
struct Fit {
    compares: bool,
    tree: u32,
    b: u32,
    o: u16,
}

/// Candidates examined per unit of pass work (a candidate is a few words compared).
const MADE_PER_UNIT: u64 = 4;

/// The most words that are no node proved for one value: the first is over the smallest
/// node (on 600 limb windows a second saved 3 nodes of 59,110 for a seventh more proofs).
const MAX_MADE: usize = 1;

/// The most SAT propagations the proof of such a word may take: nine in ten of those proved
/// take none (the sums written one way are the same sums), and what 2^12 do not decide is
/// left as often by 2^14.
const MADE_PROPAGATIONS: u64 = 1 << 12;

/// The fewest bits of a slice above a word's low bits that is looked for with a constant.
const MIN_MADE: u16 = 4;

/// `x` and `c` where `i` is `x + c`, `c` a constant.
fn plus(cx: &Context, i: u32) -> Option<(u32, u64)> {
    let node = cx.node(i);
    if node.op != OpCode::Add || node.width > 64 {
        return None;
    }
    match (cx.const_val(node.a), cx.const_val(node.b)) {
        (None, Some(c)) => Some((node.a, low(&c))),
        (Some(c), None) => Some((node.b, low(&c))),
        _ => None,
    }
}

/// The constant `c` for which bits `[o, o + len)` of `z + c` are `own` at every point, `z` a
/// word's values. Where the difference of the two is one value at every point, `c` has
/// nothing below `o` (and is 0 where the slice is the value as it is). Where it takes two
/// values one apart, the higher one at exactly the points whose bits below `o` are the
/// larger, `c` also has bits below `o`, which carry there: the least of `consts` that does.
fn constant(
    z: impl Fn(usize) -> u64,
    own: &[u64],
    o: u16,
    len: u16,
    consts: &[u64],
) -> Option<u64> {
    let mask = ones(len);
    let d = |k: usize| own[k].wrapping_sub(z(k) >> o) & mask;
    // (The first two points are all zeros and all ones: two others say more.)
    let (d2, d3) = (d(2), d(3));
    let step = d2.wrapping_sub(d3) & mask;
    if step != 0 && (o == 0 || consts.is_empty() || (step != 1 && step != mask)) {
        return None;
    }
    if (0..own.len()).all(|k| d(k) == d2) {
        return Some(d2 << o);
    }
    if o == 0 || consts.is_empty() {
        return None;
    }
    let lows = ones(o);
    'hi: for hi in [d2, d2.wrapping_sub(1) & mask] {
        let up = hi.wrapping_add(1) & mask;
        // The most the low bits are without a carry, and the least with one.
        let (mut most, mut least) = (None::<u64>, None::<u64>);
        for k in 0..own.len() {
            let (x, l) = (d(k), z(k) & lows);
            if x == hi {
                most = Some(most.map_or(l, |m| m.max(l)));
            } else if x == up {
                least = Some(least.map_or(l, |m| m.min(l)));
            } else {
                continue 'hi;
            }
        }
        let (Some(most), Some(least)) = (most, least) else {
            continue;
        };
        if most >= least {
            continue;
        }
        // A carry where the low bits plus `c` reach `2^o`.
        let (from, to) = (lows + 1 - least, lows - most);
        let c = consts
            .iter()
            .map(|&c| c & lows)
            .filter(|c| (from..=to).contains(c))
            .min();
        if let Some(c) = c {
            return Some(hi << o | c);
        }
    }
    None
}

/// The words that are no node of the cone and of which the bits read are a slice at every
/// verification sample, each with the slice's offset, likeliest first; and the candidates
/// examined.
fn made(
    r: &Runner<'_, '_>,
    cx: &Context,
    cone: &Cone,
    read: Read,
    own: &[u64],
    offsets: &[u16],
) -> (Vec<(Word, u16)>, u64) {
    let Read { n, s, len, .. } = read;
    // The constants the cone adds.
    let mut consts: Vec<u64> = Vec::new();
    for &i in &cone.nodes {
        let node = cx.node(i);
        if node.width > 64 {
            continue;
        }
        match node.op {
            OpCode::Add => consts.extend(plus(cx, i).map(|(_, c)| c)),
            OpCode::Sub => consts.extend(
                cx.const_val(node.b)
                    .map(|c| low(&c).wrapping_neg() & ones(node.width)),
            ),
            _ => {}
        }
    }
    consts.sort_unstable();
    consts.dedup();
    // The sum read without its constants: the same over another constant is no other word
    // (and so a word made is never made again from its own slice).
    let base = terms(cx, s).0;
    let mut memo = IdMap::default();
    let tree = |i: u32| cx.meta[i as usize].tree;
    // (size, the word, its offset)
    let mut found: Vec<(u32, Word, u16)> = Vec::new();
    let mut work = 0u64;
    for &b in &cone.nodes {
        let node = cx.node(b);
        let bw = node.width;
        if b == n || !word(node.op) || bw > 64 {
            continue;
        }
        // The two words `b` may be a part of. For a slice within its width, a constant split
        // by limb: the node without its own constants, plus one.
        let (x, k0) = terms(cx, b);
        let narrow = (x != base).then_some(Word {
            a: x,
            with: None,
            wide: false,
            k: k0,
        });
        // For a slice that reaches past the register: the sum of the operands zero-extended,
        // with its carry out.
        let wider = if bw == 64 {
            None
        } else if let Some((x, k0)) = plus(cx, b) {
            Some(Word {
                a: x,
                with: None,
                wide: true,
                k: k0,
            })
        } else if matches!(node.op, OpCode::Add | OpCode::Sub) {
            let op = if node.op == OpCode::Add {
                BinOp::Add
            } else {
                BinOp::Sub
            };
            Some(Word {
                a: node.a,
                with: Some((op, node.b)),
                wide: true,
                k: 0,
            })
        } else {
            None
        };
        // (Each with its operands' values.)
        let values = |w: Word| {
            let vy = match w.with {
                Some((_, y)) => Some(r.samples.get(&y)?),
                None => None,
            };
            Some((w, r.samples.get(&w.a)?, vy))
        };
        let (narrow, wider) = (narrow.and_then(values), wider.and_then(values));
        for &o in offsets {
            if o >= bw || u32::from(o) + u32::from(len) > 64 {
                continue;
            }
            let wide = o + len > bw;
            let Some((mut w, va, vy)) = (if wide { wider } else { narrow }) else {
                continue;
            };
            work += 1;
            let z = |k: usize| w.value(bw, low(&va[k]), vy.map_or(0, |v| low(&v[k])));
            let Some(c) = constant(z, own, o, len, &consts) else {
                continue;
            };
            w.k = w.k.wrapping_add(c) & ones(if wide { 64 } else { bw });
            // The slice as it is was tried; and above the low bits a constant with nothing
            // below the slice, or a slice of a few bits, is seldom a word's (of 300 such
            // candidates on 800 limb windows, 42 were proved).
            let plain = !wide && (c == 0 || (o > 0 && (len < MIN_MADE || w.k & ones(o) == 0)));
            if plain || (w.k == 0 && w.with.is_none()) {
                continue;
            }
            // Over words only: an unfinished sum taken for a word keeps the limbs above it
            // from their own (and its proofs are the ones that run into the cap).
            if w.operands().any(|i| holds_compare(cx, i, &mut memo)) {
                continue;
            }
            found.push((w.operands().map(tree).sum(), w, o));
        }
    }
    // The word at its own width first, then smaller ones, then in the canonical order of
    // the nodes (not their indices).
    found.sort_by(|x, y| {
        (x.1.wide, x.0, x.1.with.is_some())
            .cmp(&(y.1.wide, y.0, y.1.with.is_some()))
            .then_with(|| cx.order(x.1.a, y.1.a))
            .then_with(|| match (x.1.with, y.1.with) {
                (Some((p, i)), Some((q, j))) => (p as u8).cmp(&(q as u8)).then(cx.order(i, j)),
                _ => core::cmp::Ordering::Equal,
            })
            .then((x.2, x.1.k).cmp(&(y.2, y.1.k)))
    });
    found.dedup_by(|x, y| x.1 == y.1 && x.2 == y.2);
    (found.into_iter().map(|f| (f.1, f.2)).collect(), work)
}

/// `x` and `c` where `i` is `x` plus constants that come to `c` (`i` and 0 where it adds
/// none).
fn terms(cx: &Context, mut i: u32) -> (u32, u64) {
    let mut k = 0u64;
    while let Some((x, c)) = plus(cx, i) {
        k = k.wrapping_add(c);
        i = x;
    }
    (i, k)
}

/// The node of `read` with the bits it reads as a slice of a word below the sum, where one is
/// proved: the pass's step then, and otherwise what the search contributes to the node's
/// finality (a proof not asked for lack of pass work is not final).
pub(super) fn fitted(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    read: Read,
) -> Result<Result<Step, Fin>, Stop> {
    let Read {
        n,
        s,
        lo,
        len,
        k,
        apart,
    } = read;
    let w = cx.wid(n);
    let ws = cx.wid(s);
    if len == 0
        || u32::from(lo) + u32::from(len) > u32::from(ws)
        || w > 64
        || ws > 64
        || r.carries.unfit.contains_key(&n)
    {
        return Ok(Err(Fin::FINAL));
    }
    // A value whose made word waits for the late stage (below): its cone is what it was.
    if !r.late && r.carries.waiting.contains_key(&n) {
        return Ok(Err(r.hold()));
    }
    let cone = cone(cx, s);
    r.meter.charge(Counter::PassWork, cone.nodes.len() as u64)?;
    if !cone.compares {
        return Ok(Err(Fin::FINAL));
    }
    r.sample(cx, s)?;
    let mask = ones(len);
    let own: Vec<u64> = r.samples[&s].iter().map(|v| low(v) >> lo & mask).collect();
    // A slice that is the value read as it already is says nothing: `s` itself under a read
    // of it, an operand of `s` where `s` is what is replaced.
    let direct = if n == s {
        cx.node(n).children().collect::<Vec<_>>()
    } else {
        vec![s]
    };
    // The offsets a slice may start at: where a limb may (0, and the cone's), and for a read
    // above the low bits of the sum also that far into each such limb.
    let mut offsets: Vec<u16> = core::iter::once(0)
        .chain(cone.offsets.iter().copied())
        .flat_map(|o| [o, o + lo])
        .filter(|&o| o < 64)
        .collect();
    offsets.sort_unstable();
    offsets.dedup();
    let mut fits: Vec<Fit> = Vec::new();
    let mut memo = IdMap::default();
    for &b in &cone.nodes {
        let bw = cx.wid(b);
        if b == n || !word(cx.node(b).op) || bw > 64 {
            continue;
        }
        let Some(of) = r.samples.get(&b) else {
            continue;
        };
        for &o in &offsets {
            if (o == lo && direct.contains(&b)) || u32::from(o) + u32::from(len) > u32::from(bw) {
                continue;
            }
            if of
                .iter()
                .zip(&own)
                .all(|(v, &x)| (low(v) >> o ^ x) & mask == 0)
            {
                let compares = holds_compare(cx, b, &mut memo);
                let tree = cx.meta[b as usize].tree;
                fits.push(Fit {
                    compares,
                    tree,
                    b,
                    o,
                });
            }
        }
    }
    // Words first, then smaller ones, then in the canonical order of the nodes (not their
    // indices: the choice does not depend on how the input was built).
    fits.sort_unstable_by(|x, y| {
        (x.compares, x.tree)
            .cmp(&(y.compares, y.tree))
            .then_with(|| cx.order(x.b, y.b))
            .then(x.o.cmp(&y.o))
    });
    let mut fin = Fin::FINAL;
    let mut open = true;
    for &Fit { b, o, .. } in fits.iter().take(MAX_PROOFS) {
        let cap = ASKED_PROPAGATIONS;
        match proved(
            r,
            cx,
            &cone,
            (s, lo),
            (&Word::node(b), o),
            len,
            usize::from(apart),
            cap,
        )? {
            Ok(Said::Proved) => {
                let before = cx.len() as u32;
                let e = r.build(cx, |cx| {
                    let e = cx.c_extract(b, o, len)?;
                    held(cx, e, w, k)
                })?;
                // (One node more than it frees at most, as any limb read as its slice: see
                // `finish_within`.)
                let step = finish_within(r, cx, PassKind::Carries, n, e, before, &[b], fin, 2)?;
                return Ok(Ok(step));
            }
            Ok(Said::Refuted) => {}
            // The next candidate is of the same limb code: no likelier to be decided.
            Ok(Said::Undecided) => {
                open = false;
                break;
            }
            Err(more) => fin = fin.and(more),
        }
    }
    // No slice of a node: of a word that is no node yet (not after a proof left undecided:
    // the word would be over the same limb code). Such a word is made in the late stage of
    // the rounds only: made below, it stands in the way of the slice of a node the rounds
    // would prove above it (a sum of product digits made a word of its own, where the sums
    // above are slices of the product).
    let (proofs, undecided) = r.carries.fits[usize::from(apart)];
    if open && undecided < MAX_UNDECIDED + proofs {
        let (words, work) = made(r, cx, &cone, read, &own, &offsets);
        r.meter
            .charge(Counter::PassWork, work.div_ceil(MADE_PER_UNIT))?;
        let words = if r.late {
            words
        } else {
            if !words.is_empty() {
                r.carries.waiting.insert(n, ());
                fin = fin.and(r.hold());
            }
            Vec::new()
        };
        for (word, o) in words.into_iter().take(MAX_MADE) {
            let cap = MADE_PROPAGATIONS;
            match proved(
                r,
                cx,
                &cone,
                (s, lo),
                (&word, o),
                len,
                usize::from(apart),
                cap,
            )? {
                Ok(Said::Proved) => {
                    let before = cx.len() as u32;
                    let e = r.build(cx, |cx| {
                        let made = word.build(cx, word.a, word.with.map(|(_, b)| b))?;
                        let e = cx.c_extract(made, o, len)?;
                        held(cx, e, w, k)
                    })?;
                    let stops: Vec<u32> = word.operands().collect();
                    match finish_within(r, cx, PassKind::Carries, n, e, before, &stops, fin, 1)? {
                        Step::Normal(f) => fin = fin.and(f),
                        step => return Ok(Ok(step)),
                    }
                }
                Ok(Said::Refuted) => {}
                Ok(Said::Undecided) => break,
                Err(more) => fin = fin.and(more),
            }
        }
    }
    if fin.done {
        r.carries.unfit.insert(n, ());
    }
    Ok(Err(fin))
}
