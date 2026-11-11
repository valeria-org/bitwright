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
//! AIG-node cap and a propagation cap and what is left of the pass work. A call whose proofs
//! keep running into those caps (limbs several handlers above their words) asks no more of
//! them, and leaves the values it did not ask about provisional.

use super::{Fin, PassKind, Runner, Step, Stop, finish_within};
use crate::Width;
use crate::engine::budget::Counter;
use crate::engine::oracle::{EqualityCaps, EqualityVerdict};
use crate::expr::{Context, OpCode};

/// The most nodes walked below a value.
const MAX_CONE: usize = 512;

/// The most candidates proved for one value. The first is the likeliest: on a sample of 2,500
/// limb windows, a second took the nodes saved from 7.5% to 7.7%.
const MAX_PROOFS: usize = 2;

/// The most AIG nodes a proof may build.
const MAX_AIG_NODES: usize = 1 << 15;

/// The most SAT propagations a proof may take. What is not proved by then is mostly a limb
/// several handlers above its word: on the same sample, four times as many and a third proof
/// saved 8.9% for more than twice the time.
const PROPAGATIONS: u64 = 1 << 17;

/// The proofs a call may leave undecided at their caps beyond the number it has proved (on
/// the corpus of 58,530 windows: 0.3% more nodes than without the limit, for an eighth less
/// time).
const MAX_UNDECIDED: u32 = 8;

/// Units of pass work charged per SAT propagation (as the carries pass charges them).
const PROPAGATION_RATE: u64 = 4;

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

/// The nodes below `n` (at most [`MAX_CONE`], nearest first), the offsets a limb of theirs may
/// start at, and whether one of them is a comparison. The offsets are the bits the nodes
/// shift by, slice from and to, and mask to, and the sums of two of those (the third limb
/// starts where the first two end, which no node need spell out).
fn cone(cx: &Context, n: u32) -> (Vec<u32>, Vec<u16>, bool) {
    let mut nodes = vec![n];
    let mut seen = crate::hash::IdMap::default();
    seen.insert(n, ());
    let mut cuts: Vec<u16> = Vec::new();
    let mut compares = false;
    let mut at = 0;
    while at < nodes.len() && nodes.len() < MAX_CONE {
        let i = nodes[at];
        at += 1;
        let node = cx.node(i);
        compares |= node.op == OpCode::Ult;
        match node.op {
            OpCode::Extract => cuts.extend([node.b as u16, node.b as u16 + node.width]),
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
    (nodes, offsets, compares)
}

/// Whether a comparison is below `i`, among the nodes of `below` (a cone's).
fn holds_compare(cx: &Context, i: u32, memo: &mut crate::hash::IdMap<u32, bool>) -> bool {
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

/// Whether the low `j` bits of `n` equal `extract<o, j>(b)`, by the native prover over a
/// scratch copy of both. `Ok(false)` when refuted or not decided within the pass's own caps
/// (the same under any budget); `Err` when the proof was not asked, with what that makes of
/// the node's finality: for lack of pass work, or because the call's proofs keep running into
/// their caps (another call may ask it).
fn proved(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    b: u32,
    o: u16,
    j: u16,
) -> Result<Result<bool, Fin>, Stop> {
    let left = r.meter.left_in(|b| b.pass_work);
    let propagations =
        PROPAGATIONS.min(left.saturating_sub(MAX_AIG_NODES as u64) / PROPAGATION_RATE);
    if propagations == 0 {
        return Ok(Err(Fin::capped(crate::engine::Exhausted::PassWork)));
    }
    // The limbs of a call are alike: where the prover keeps running into its caps (limbs
    // several handlers deep), the next proof would too.
    let (proofs, undecided) = r.carries.fits;
    if undecided >= MAX_UNDECIDED + proofs {
        return Ok(Err(Fin::PROVISIONAL));
    }
    // What a fresh context cannot hold (an extension operation: it has no registry) the
    // prover is not asked about: not decided, under any budget.
    let mut scx = Context::new();
    let both = match scx.import(cx, &[cx.handle(n), cx.handle(b)]) {
        Ok(both) => both,
        Err(crate::Error::Unsupported(_)) => return Ok(Ok(false)),
        Err(e) => return Err(Stop::Error(e)),
    };
    count(r).proofs += 1;
    let jw = Width::new(j).map_err(|e| Stop::Error(e.into()))?;
    let lhs = scx.extract(both[0], 0, jw).map_err(Stop::Error)?;
    let rhs = scx.extract(both[1], o, jw).map_err(Stop::Error)?;
    // (A candidate that only agrees at the few verification samples is refuted by the
    // samples before any search.)
    let caps = EqualityCaps {
        samples: 256,
        max_nodes: MAX_AIG_NODES,
        max_propagations: propagations,
    };
    let out = (crate::circuit_equality())(&mut scx, lhs, rhs, &caps).map_err(Stop::Error)?;
    let nodes = out.nodes;
    let cost = (nodes as u64)
        .saturating_add(out.propagations.saturating_mul(PROPAGATION_RATE))
        .min(left);
    r.meter.charge(Counter::PassWork, cost)?;
    let c = count(r);
    Ok(match out.verdict {
        EqualityVerdict::Proved => {
            c.proved += 1;
            r.carries.fits.0 += 1;
            Ok(true)
        }
        EqualityVerdict::Refuted => {
            c.refuted += 1;
            Ok(false)
        }
        // Stopped short of the pass's own cap: more pass work may decide it.
        EqualityVerdict::Budget if propagations < PROPAGATIONS => {
            c.unknown += 1;
            Err(Fin::capped(crate::engine::Exhausted::PassWork))
        }
        EqualityVerdict::Budget | EqualityVerdict::Unknown => {
            c.unknown += 1;
            r.carries.fits.1 += 1;
            Ok(false)
        }
    })
}

/// `e` zero-extended to `w` bits and shifted left by `k`: a limb's low bits as the node that
/// read them holds them.
pub(super) fn held(cx: &mut Context, e: u32, w: u16, k: u16) -> Result<u32, crate::Error> {
    let e = cx.c_zext(e, w)?;
    if k == 0 {
        return Ok(e);
    }
    let by = cx.mk_const(&crate::BitVec::wrapping_from_u64(
        Width::new(w)?,
        u64::from(k),
    ))?;
    cx.c_bin(crate::ops::BinOp::Shl, e, by)
}

/// `n`, which holds the low `j` bits of `s` `k` bits up and nothing else (`s` itself, of
/// which the low `j` bits are all that is not zero, or a truncation, mask or left shift of
/// it), with those bits as a slice of a word below `s`, where one is proved: the pass's step
/// then, and otherwise what the search contributes to the node's finality (a proof not asked
/// for lack of pass work is not final).
pub(super) fn fitted(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    s: u32,
    j: u16,
    k: u16,
) -> Result<Result<Step, Fin>, Stop> {
    let w = cx.wid(n);
    let ws = cx.wid(s);
    if j == 0 || j > ws || w > 64 || ws > 64 || r.carries.unfit.contains_key(&n) {
        return Ok(Err(Fin::FINAL));
    }
    let (nodes, offsets, compares) = cone(cx, s);
    r.meter.charge(Counter::PassWork, nodes.len() as u64)?;
    if !compares {
        return Ok(Err(Fin::FINAL));
    }
    r.sample(cx, s)?;
    let jw = Width::new(j).map_err(|e| Stop::Error(e.into()))?;
    let own: Vec<_> = r.samples[&s]
        .iter()
        .map(|v| v.extract(0, jw).ok())
        .collect();
    // A slice that is the value read as it already is says nothing: `s` itself under a read
    // of it, an operand of `s` where `s` is what is replaced.
    let direct = if n == s {
        cx.node(n).children().collect::<Vec<_>>()
    } else {
        vec![s]
    };
    let mut fits: Vec<(bool, u32, u32, u16)> = Vec::new();
    let mut memo = crate::hash::IdMap::default();
    for &b in &nodes {
        let bw = cx.wid(b);
        if b == n || !word(cx.node(b).op) || bw > 64 {
            continue;
        }
        let Some(of) = r.samples.get(&b) else {
            continue;
        };
        for &o in core::iter::once(&0).chain(&offsets) {
            if u32::from(o) + u32::from(j) > u32::from(bw) || (o == 0 && direct.contains(&b)) {
                continue;
            }
            if of
                .iter()
                .zip(&own)
                .all(|(v, x)| v.extract(o, jw).ok() == *x)
            {
                let tree = cx.meta[b as usize].tree;
                fits.push((holds_compare(cx, b, &mut memo), tree, b, o));
            }
        }
    }
    // Words first, then smaller ones, then in the canonical order of the nodes (not their
    // indices: the choice does not depend on how the input was built).
    fits.sort_unstable_by(|x, y| {
        (x.0, x.1)
            .cmp(&(y.0, y.1))
            .then_with(|| cx.order(x.2, y.2))
            .then(x.3.cmp(&y.3))
    });
    let mut fin = Fin::FINAL;
    for &(_, _, b, o) in fits.iter().take(MAX_PROOFS) {
        match proved(r, cx, s, b, o, j)? {
            Ok(true) => {
                let before = cx.len() as u32;
                let e = r.build(cx, |cx| {
                    let e = cx.c_extract(b, o, j)?;
                    held(cx, e, w, k)
                })?;
                // (One node more than it frees at most, as any limb read as its slice: see
                // `finish_within`.)
                let step = finish_within(r, cx, PassKind::Carries, n, e, before, &[b], fin, 2)?;
                return Ok(Ok(step));
            }
            Ok(false) => {}
            Err(more) => fin = fin.and(more),
        }
    }
    if fin.done {
        r.carries.unfit.insert(n, ());
    }
    Ok(Err(fin))
}
