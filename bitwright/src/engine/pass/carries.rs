//! The carries pass: carry and borrow networks (parallel-prefix adders and subtractors, ripple
//! chains written out with shifts) over at most [`MAX_ATOMS`] atoms become the affine form
//! `c + Σ aᵢ·xᵢ` they compute, when the native prover proves them equal.
//!
//! The region below a node is its `& | ^ ~` and constant left shifts down to atoms (constants
//! are leaves); it is read when a bitwise operator in it reads a shift (what carries are), or
//! when it is only shifts of one atom, `a << k = 2^k·a` exactly (`a << 1` is written `a + a`,
//! which needs no constant). Otherwise, read as a function `f` of its atoms, the only affine
//! form it can be is `c = f(0, …, 0)`, `aᵢ = f(eᵢ) − c` (atom `i` 1, the others 0). The form
//! is compared with `f` at a fixed set of points (boundary values, points near the region's
//! constants, where a sum with one carries far, and seeded pseudo-random ones; a quarter of
//! them first), which rejects almost every region that is not affine, a truncated or miswired
//! prefix tree and the partial sums of a chain among them; it is costed against the region
//! before anything is proved, and only a form that would make the DAG smaller is proved. The
//! proof is of the region copied into a scratch context with a fresh symbol for each atom (an
//! identity over free symbols holds at any values of the atoms), by the native prover without
//! the engine's simplification (so no recursion into the engine), within an AIG-node cap and a
//! propagation cap and within what is left of the pass work. Only a proof commits: a network
//! that differs from the form at inputs the points miss is refuted, and one the prover does not
//! decide within its caps (a ripple chain of 48 bits or more) is left as it is, and so is every
//! region holding it.

use super::{Counts, Fin, PassKind, Runner, Step, Stop, finish, linear, worth_building};
use crate::engine::Exhausted;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};
use crate::prove::{self, Outcome, Unknown};
use crate::{BitVec, Error, SymbolKey};

/// The most atoms.
const MAX_ATOMS: usize = 3;

/// The most region nodes (interior nodes, atoms and constants) examined per node.
const MAX_REGION: u32 = 256;

/// Points per evaluation: the fit's `1 + t` (all atoms 0, then each alone 1) and the filter's
/// samples after them.
const LANES: usize = 64;

/// The lanes evaluated first (the fit's and the first points): a region that fails the filter
/// there is not evaluated at the others.
const QUICK: usize = 16;

/// Lanes evaluated per unit of pass work: a node's 64 lanes are one tight loop (measured at
/// 5 ns a unit so counted, against 20 to 40 ns a unit of the other passes: the charge errs
/// high).
const LANES_PER_UNIT: u64 = 8;

/// The most AIG nodes a proof may build (then the prover answers `TooLarge`). A 64-bit
/// prefix subtractor against `x − y` takes 2,544.
pub(super) const MAX_AIG_NODES: usize = 1 << 16;

/// The most SAT propagations a proof may take: 3.4 times what the 64-bit prefix subtractor
/// against `x − y` takes (1,237,226; the adder 537,328), about 0.4 s. A ripple chain written
/// out is harder: the 40-bit adder takes about 3.2 M, and from 48 bits on it is past the cap.
const PROPAGATIONS: u64 = 1 << 22;

/// Units of pass work charged per SAT propagation: what one costs in units of the other
/// passes' work (measured on the prefix adders and subtractors of 8 to 64 bits: 85 to 100 ns a
/// propagation, blasting and encoding included, against 20 to 40 ns a unit of the linear pass
/// and of this one with its proofs so charged). An AIG node built costs one unit.
const PROPAGATION_RATE: u64 = 4;

/// The region's constants that get points of their own, at most: `c`, `−c`, `c + 1` and `~c`,
/// near which a sum with `c` carries far (none of the other points need be).
const MAX_CONSTS: usize = 4;

/// The walk's and evaluation's buffers, kept by the runner and reused, and what the call's
/// proofs left undecided.
#[derive(Default)]
pub(crate) struct Scratch {
    /// Per region node reached: its row in `rows` once rows are assigned (atoms first, in the
    /// canonical order, then the interior nodes in post-order).
    seen: Counts,
    stack: Vec<(u32, bool)>,
    /// The interior nodes, operands first.
    order: Vec<u32>,
    atoms: Vec<u32>,
    /// The region's constants but 0 and all-ones, sorted, at most [`MAX_CONSTS`].
    consts: Vec<u64>,
    /// `LANES` values per row.
    rows: Vec<u64>,
    /// Nodes whose proof was not decided within the pass's caps: a region holding one is larger
    /// still, and is not read.
    undecided: IdMap<u32, ()>,
}

fn interior(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    match n.op {
        OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not => true,
        OpCode::Shl => cx.is_const(n.b),
        _ => false,
    }
}

/// The region below `n` into `s.order`, `s.atoms` and `s.consts`: whether it is within the
/// caps, holds no node left undecided, and either a bitwise operator reads a shift or it is
/// only shifts of an atom (`a << 1` is written `a + a`, which needs no constant), and which of
/// the two (only shifts: a chain); with the nodes reached. Otherwise it is a bitwise function
/// (which the bitwise pass decides) or one shifted, `g << k`, affine only when `g` is an atom's
/// complement or a constant (forms the other passes give) or when only its lowest bit is kept
/// (`k = W − 1`, where the form is no smaller than a minimal `g << k`).
fn walk(cx: &Context, n: u32, s: &mut Scratch) -> (bool, bool, u32) {
    s.seen.begin(cx.len());
    s.order.clear();
    s.atoms.clear();
    s.consts.clear();
    s.stack.clear();
    s.stack.push((n, false));
    let mut reached = 0u32;
    let (mut carried, mut bitwise) = (false, false);
    while let Some((i, expanded)) = s.stack.pop() {
        if expanded {
            s.order.push(i);
            continue;
        }
        if s.seen.get(i).is_some() {
            continue;
        }
        s.seen.set(i, u32::MAX);
        reached += 1;
        if reached > MAX_REGION {
            return (false, false, reached);
        }
        if let Some(v) = cx.const_val(i) {
            if !v.is_zero() && !v.is_ones() {
                s.consts.push(v.limbs()[0]);
            }
            continue;
        }
        if !interior(cx, i) {
            s.atoms.push(i);
            if s.atoms.len() > MAX_ATOMS {
                return (false, false, reached);
            }
            continue;
        }
        if s.undecided.contains_key(&i) {
            return (false, false, reached);
        }
        s.stack.push((i, true));
        let node = cx.node(i);
        if node.op == OpCode::Shl {
            s.stack.push((node.a, false));
        } else {
            bitwise = true;
            for c in node.children() {
                carried |= cx.node(c).op == OpCode::Shl && interior(cx, c);
                s.stack.push((c, false));
            }
        }
    }
    s.consts.sort_unstable();
    s.consts.dedup();
    s.consts.truncate(MAX_CONSTS);
    (
        (carried || !bitwise) && !s.atoms.is_empty(),
        !bitwise,
        reached,
    )
}

/// splitmix64.
fn mix(z: u64) -> u64 {
    let mut z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Atom `j`'s value (of `t` atoms) in lane `k`: lane 0 all atoms 0, lane `1 + j` atom `j` 1 and
/// the others 0 (the fit), then the boundary values 0, 1, all-ones, the sign bit and all-ones
/// without it (a grid of them over two atoms or three), then the points near each of the
/// region's constants `consts` (`c`, `−c`, `c + 1`, `~c` on one atom, the others 0, where a
/// sum with `c` carries far), then seeded pseudo-random values, plain, sparse (the conjunction
/// of two) and dense (the disjunction of two), so long runs of ones and of zeros (long carries
/// and borrows) are among them.
fn lane_value(t: usize, j: usize, k: usize, mask: u64, consts: &[u64]) -> u64 {
    if k <= t {
        return u64::from(k == j + 1);
    }
    let m = k - t - 1;
    let sign = (mask >> 1) + 1;
    let boundary = [0, 1, mask, sign, mask >> 1];
    let grid = if t == 1 { 5 } else { 25 };
    if m < grid {
        let digit = match j {
            0 => m % 5,
            1 => m / 5,
            _ => (m % 5 + m / 5) % 5,
        };
        return boundary[digit];
    }
    let q = m - grid;
    if q < 4 * consts.len() {
        let c = consts[q / 4];
        let v = [c, c.wrapping_neg(), c.wrapping_add(1), !c][q % 4] & mask;
        return if j == q % t { v } else { 0 };
    }
    let seed = (k as u64) << 8 | j as u64;
    let (a, b) = (mix(seed), mix(seed ^ 0x5555_0000));
    (match m % 3 {
        0 => a,
        1 => a & b,
        _ => a | b,
    }) & mask
}

/// Evaluates the region (left by [`walk`]) at `lanes`, the rows assigned and sized when they
/// start at 0 (atoms in `s.atoms`' order): the root's values are the last row.
fn evaluate(cx: &Context, s: &mut Scratch, mask: u64, lanes: core::ops::Range<usize>) {
    let t = s.atoms.len();
    if lanes.start == 0 {
        s.rows.clear();
        s.rows.resize((t + s.order.len()) * LANES, 0);
        for (j, &a) in s.atoms.iter().enumerate() {
            s.seen.set(a, j as u32);
        }
        for (row, &i) in s.order.iter().enumerate() {
            s.seen.set(i, (t + row) as u32);
        }
    }
    for j in 0..t {
        for k in lanes.clone() {
            s.rows[j * LANES + k] = lane_value(t, j, k, mask, &s.consts);
        }
    }
    let bits = 64 - u64::from(mask.leading_zeros());
    for (row, &i) in s.order.iter().enumerate() {
        let row = t + row;
        let n = cx.node(i);
        let (done, rest) = s.rows.split_at_mut(row * LANES);
        let out = &mut rest[lanes.clone()];
        // An operand's values: its row, or a constant (lane-independent).
        let operand = |x: u32| -> Result<&[u64], u64> {
            match cx.const_val(x) {
                Some(v) => Err(v.limbs()[0]),
                None => {
                    let r = s.seen.get(x).unwrap_or(0) as usize * LANES;
                    Ok(&done[r + lanes.start..r + lanes.end])
                }
            }
        };
        match n.op {
            OpCode::Not => match operand(n.a) {
                Ok(a) => out.iter_mut().zip(a).for_each(|(o, &x)| *o = !x & mask),
                Err(c) => out.fill(!c & mask),
            },
            OpCode::Shl => {
                let c = cx.const_val(n.b).map_or(bits, |v| v.limbs()[0]);
                match operand(n.a) {
                    Ok(a) if c < bits => out
                        .iter_mut()
                        .zip(a)
                        .for_each(|(o, &x)| *o = (x << c) & mask),
                    Err(x) if c < bits => out.fill((x << c) & mask),
                    _ => out.fill(0),
                }
            }
            op => {
                let f: fn(u64, u64) -> u64 = match op {
                    OpCode::And => |x, y| x & y,
                    OpCode::Or => |x, y| x | y,
                    _ => |x, y| x ^ y,
                };
                match (operand(n.a), operand(n.b)) {
                    (Ok(a), Ok(b)) => out
                        .iter_mut()
                        .zip(a.iter().zip(b))
                        .for_each(|(o, (&x, &y))| *o = f(x, y)),
                    (Ok(a), Err(c)) | (Err(c), Ok(a)) => {
                        out.iter_mut().zip(a).for_each(|(o, &x)| *o = f(x, c));
                    }
                    (Err(x), Err(y)) => out.fill(f(x, y) & mask),
                }
            }
        }
    }
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry(PassKind::Carries.name()).or_default()
}

/// What the prover said about the region and the form.
enum Verdict {
    Proved,
    /// Not proved: refuted, or not decided within the pass's own caps (the same under any
    /// budget).
    No,
    /// Not decided for lack of pass work: not started, or stopped by what was left.
    Unpaid,
}

/// The region (left by [`walk`] and [`evaluate`]) and the form `konst + Σ coeffs[j]·atom j`
/// built in `scx`, atom `j` the fresh symbol `j`.
fn copy(
    cx: &Context,
    s: &Scratch,
    scx: &mut Context,
    w: crate::Width,
    konst: u64,
    coeffs: &[u64],
) -> Result<(u32, u32), Error> {
    let mut map: Vec<u32> = Vec::with_capacity(s.atoms.len() + s.order.len());
    for j in 0..s.atoms.len() {
        let e = scx.symbol(SymbolKey::from(j as u64), w)?;
        map.push(scx.id(e)?);
    }
    let operand = |scx: &mut Context, map: &[u32], x: u32| -> Result<u32, Error> {
        match cx.const_val(x) {
            Some(v) => scx.mk_const(&v),
            None => Ok(map[s.seen.get(x).unwrap_or(0) as usize]),
        }
    };
    for &i in &s.order {
        let node = cx.node(i);
        let a = operand(scx, &map, node.a)?;
        let e = match node.op {
            OpCode::Not => scx.c_un(UnOp::Not, a)?,
            op => {
                let b = operand(scx, &map, node.b)?;
                let bop = match op {
                    OpCode::And => BinOp::And,
                    OpCode::Or => BinOp::Or,
                    OpCode::Xor => BinOp::Xor,
                    _ => BinOp::Shl,
                };
                scx.c_bin(bop, a, b)?
            }
        };
        map.push(e);
    }
    let lhs = *map.last().unwrap_or(&0);
    let mut rhs = scx.mk_const(&BitVec::wrapping_from_u64(w, konst))?;
    for (j, &k) in coeffs.iter().enumerate() {
        if k != 0 {
            let k = scx.mk_const(&BitVec::wrapping_from_u64(w, k))?;
            let term = scx.c_bin(BinOp::Mul, map[j], k)?;
            rhs = scx.c_bin(BinOp::Add, rhs, term)?;
        }
    }
    Ok((lhs, rhs))
}

/// Whether the region of `n` (left by [`walk`] and [`evaluate`]) equals `konst + Σ coeffs[j]·atom
/// j`, by the native prover over a scratch copy with a fresh symbol per atom: within the pass's
/// caps and what is left of the pass work, and charged its AIG nodes and [`PROPAGATION_RATE`] per
/// propagation.
fn proved(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    konst: u64,
    coeffs: &[u64],
) -> Result<Verdict, Stop> {
    let left = r.meter.left_in(|b| b.pass_work);
    let propagations =
        PROPAGATIONS.min(left.saturating_sub(MAX_AIG_NODES as u64) / PROPAGATION_RATE);
    if propagations == 0 {
        return Ok(Verdict::Unpaid);
    }
    count(r).proofs += 1;
    let w = cx.width_of(n);
    let mut scx = Context::new();
    let (lhs, rhs) = copy(cx, &r.carries, &mut scx, w, konst, coeffs).map_err(Stop::Error)?;
    let cfg = prove::Config::default()
        .with_simplify(false)
        .with_certificate(false)
        .with_samples(0)
        .with_max_nodes(MAX_AIG_NODES)
        .with_max_conflicts(u64::MAX)
        .with_max_propagations(propagations);
    let (lhs, rhs) = (scx.handle(lhs), scx.handle(rhs));
    let mut q = prove::Question::equal(&mut scx, lhs, rhs, &cfg).map_err(Stop::Error)?;
    let out = q.solve(&mut scx, cfg.limits()).map_err(Stop::Error)?;
    let stats = q.stats();
    let nodes = match &out {
        Outcome::Unknown(Unknown::TooLarge { nodes }) => *nodes,
        _ => stats.nodes,
    };
    let cost = (nodes as u64)
        .saturating_add(stats.propagations.saturating_mul(PROPAGATION_RATE))
        .min(left);
    r.meter.charge(Counter::PassWork, cost)?;
    let c = count(r);
    Ok(match out {
        Outcome::Proved(_) => {
            c.proved += 1;
            Verdict::Proved
        }
        Outcome::Refuted(_) => {
            c.refuted += 1;
            Verdict::No
        }
        // Stopped short of the pass's own cap: more pass work may decide it.
        Outcome::Unknown(Unknown::Budget { .. }) if propagations < PROPAGATIONS => {
            c.unknown += 1;
            Verdict::Unpaid
        }
        Outcome::Unknown(_) => {
            c.unknown += 1;
            r.carries.undecided.insert(n, ());
            Verdict::No
        }
    })
}

/// The affine form the region (left by [`walk`]) can only be, `konst + Σ coeffs[j]·atom j`,
/// when it agrees with the region at every point; `None` otherwise.
fn fit(r: &mut Runner<'_, '_>, cx: &Context, mask: u64) -> Result<Option<(u64, Vec<u64>)>, Stop> {
    let t = r.carries.atoms.len();
    let rows = (t + r.carries.order.len()) as u64;
    // The fit and the first points, then the rest: almost every region that is not affine
    // shows it among the first.
    r.meter.charge(
        Counter::PassWork,
        (rows * QUICK as u64).div_ceil(LANES_PER_UNIT),
    )?;
    evaluate(cx, &mut r.carries, mask, 0..QUICK);
    let s = &r.carries;
    let f = (t + s.order.len() - 1) * LANES;
    let konst = s.rows[f];
    let coeffs: Vec<u64> = (0..t)
        .map(|j| s.rows[f + 1 + j].wrapping_sub(konst) & mask)
        .collect();
    // The filter: the form at every point.
    let affine = |s: &Scratch, mut lanes: core::ops::Range<usize>| {
        lanes.all(|k| {
            let v = coeffs.iter().enumerate().fold(konst, |acc, (j, &a)| {
                acc.wrapping_add(a.wrapping_mul(s.rows[j * LANES + k]))
            });
            v & mask == s.rows[f + k]
        })
    };
    if !affine(s, t + 1..QUICK) {
        return Ok(None);
    }
    r.meter.charge(
        Counter::PassWork,
        (rows * (LANES - QUICK) as u64).div_ceil(LANES_PER_UNIT),
    )?;
    evaluate(cx, &mut r.carries, mask, QUICK..LANES);
    Ok(affine(&r.carries, QUICK..LANES).then_some((konst, coeffs)))
}

/// The carries pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let bits = cx.wid(n);
    if bits > 64 || !interior(cx, n) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let (fits, chain, reached) = walk(cx, n, &mut r.carries);
    r.meter.charge(Counter::PassWork, u64::from(reached))?;
    if !fits {
        return Ok(Step::Normal(Fin::FINAL));
    }
    // The canonical order of the atoms, independent of node indices: the points do not depend
    // on how the input was built.
    r.carries.atoms.sort_by(|a, b| cx.order(*a, *b));
    let mask = u64::MAX >> (64 - bits);
    // The form, and whether it is exact by construction.
    let (konst, coeffs, exact) = if chain {
        // Shifts of one atom: `a << k` is `2^k·a`, and 0 once `k` reaches the width.
        let k = r.carries.order.iter().fold(0u64, |k, &i| {
            let c = cx.const_val(cx.node(i).b);
            k.saturating_add(c.map_or(u64::from(bits), |v| v.limbs()[0]))
        });
        // One shift by 2 or more is its own form (`a << k`); `a << 1` is written `a + a`.
        if r.carries.order.len() == 1 && (2..u64::from(bits)).contains(&k) {
            return Ok(Step::Normal(Fin::FINAL));
        }
        let coeff = if k < u64::from(bits) { 1u64 << k } else { 0 };
        (0, vec![coeff], true)
    } else {
        match fit(r, cx, mask)? {
            Some((konst, coeffs)) => (konst, coeffs, false),
            None => return Ok(Step::Normal(Fin::FINAL)),
        }
    };
    let w = cx.width_of(n);
    let atoms = r.carries.atoms.clone();
    let terms: Vec<(u32, BitVec)> = atoms
        .iter()
        .zip(&coeffs)
        .map(|(&a, &k)| (a, BitVec::wrapping_from_u64(w, k)))
        .collect();
    let form = linear::Form::of(BitVec::wrapping_from_u64(w, konst), &terms);
    // Cheap before expensive: a form the commit rule would refuse is not proved.
    if let Some(fin) = worth_building(r, cx, n, &atoms, linear::estimate(&form))? {
        count(r).rejected_cost += 1;
        return Ok(Step::Normal(fin));
    }
    if !exact {
        match proved(r, cx, n, konst, &coeffs)? {
            Verdict::Proved => {}
            // Refuted, too large, or undecided within the pass's own caps, which no budget
            // changes: final.
            Verdict::No => return Ok(Step::Normal(Fin::FINAL)),
            // Not asked for lack of pass work: more budget may prove it, so not final.
            Verdict::Unpaid => return Ok(Step::Normal(Fin::capped(Exhausted::PassWork))),
        }
    }
    let before = cx.len() as u32;
    let e = linear::emit(r, cx, &form)?;
    finish(r, cx, PassKind::Carries, n, e, before, &atoms, Fin::FINAL)
}
