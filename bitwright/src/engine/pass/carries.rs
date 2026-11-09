//! The carries pass: carry and borrow networks (parallel-prefix adders and subtractors, ripple
//! chains written out with shifts) over at most [`MAX_ATOMS`] atoms become the affine form
//! `c + Σ aᵢ·xᵢ` they compute, when the native prover proves them equal.
//!
//! The region below a node is its `& | ^ ~` and constant left shifts down to atoms (constants
//! are leaves); it is read when a bitwise operator in it reads a shift (what carries are), or
//! when it is only shifts of one atom, `a << k = 2^k·a` exactly (one shift is its own form).
//! Otherwise, read as a function `f` of its atoms, the only affine form it can be is
//! `c = f(0, …, 0)`, `aᵢ = f(eᵢ) − c` (atom `i` 1, the others 0). The form
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
//!
//! Below a `concat`, the region is instead read through slices: `+ − neg`, `concat`, `extract`,
//! `zext`, `sext` and `<u` as well, down to atoms of the `concat`'s own width. A sum split at a
//! boundary of any width, its two halves added apart and the carry between them written out
//! (`concat(extract<17, 47>(x) + extract<17, 47>(y) + zext<47>(c), trunc<17>(s))`, with `s` the
//! 18-bit sum of the low halves and `c` its top bit), is fitted, proved and becomes `x + y`.
//! Such a region is read only when it takes a slice and adds.
//!
//! A right shift by a constant or a mask whose region is one value through `& | ^ ~ + − neg *`
//! and constant shifts (at least [`MIN_COUNT_REGION`] nodes, multiplying, or shifting right and
//! adding: how bits are counted in parallel) is compared at the same points with `popcnt`,
//! `ctz` and `clz` of that value, and becomes the one that agrees everywhere once the prover
//! proves it: the SWAR population count is `popcnt(x)`, and counted after a smear or a mask of
//! the trailing zeros, `clz(x)` or `ctz(x)`.

use super::{Counts, Fin, PassKind, Runner, Step, Stop, finish, linear, worth_building};
use crate::engine::Exhausted;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::prove::{self, Outcome, Unknown};
use crate::{BitVec, Error, SymbolKey};

/// The most atoms.
const MAX_ATOMS: usize = 3;

/// The fewest interior nodes of a region read as a bit count (a count spelled out is long; a
/// short region is no smaller than its count).
const MIN_COUNT_REGION: usize = 6;

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

/// How a region is read: through bitwise operators and left shifts (carry networks), through
/// slices as well (below a `concat`), or as a function of one value through arithmetic and
/// shifts both ways (bit counts).
#[derive(Copy, Clone, PartialEq, Eq)]
enum Mode {
    Bitwise,
    Slices,
    Counts,
}

/// Whether `i` is interior to a region read as a bit count: `& | ^ ~ + − neg *` and shifts by
/// constants, of at most 64 bits.
fn counted(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    match n.op {
        OpCode::Shl | OpCode::LShr | OpCode::AShr => cx.is_const(n.b) && cx.wid(i) <= 64,
        OpCode::And
        | OpCode::Or
        | OpCode::Xor
        | OpCode::Not
        | OpCode::Add
        | OpCode::Sub
        | OpCode::Neg
        | OpCode::Mul => cx.wid(i) <= 64,
        _ => false,
    }
}

/// Whether `i` is interior to a region read through slices (below a `concat`): the bitwise
/// region's operators, and `+ − neg`, `concat`, `extract`, `zext`, `sext` and `<u` of at most
/// 64 bits, whose values a lane holds.
fn sliced(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    let small = |j: u32| cx.wid(j) <= 64;
    match n.op {
        OpCode::Add
        | OpCode::Sub
        | OpCode::Neg
        | OpCode::Concat
        | OpCode::Extract
        | OpCode::Zext
        | OpCode::Sext => small(i) && small(n.a),
        OpCode::Ult => small(n.a),
        _ => interior(cx, i),
    }
}

/// The region below `n` into `s.order`, `s.atoms` and `s.consts`: whether it is within the
/// caps, holds no node left undecided, and either a bitwise operator reads a shift or it is
/// only shifts of an atom, and which of the two (only shifts: a chain); with the nodes
/// reached. Otherwise it is a bitwise function
/// (which the bitwise pass decides) or one shifted, `g << k`, affine only when `g` is an atom's
/// complement or a constant (forms the other passes give) or when only its lowest bit is kept
/// (`k = W − 1`, where the form is no smaller than a minimal `g << k`).
///
/// In [`Mode::Slices`], the region is read through [`sliced`] nodes instead, down to atoms of
/// `n`'s width only, and fits when it both takes a slice (an `extract`) and adds (`+ −` or
/// `<u`, a carry written out); never a chain. In [`Mode::Counts`], through [`counted`] nodes
/// down to one atom of `n`'s width, and fits when it multiplies, or shifts right and adds (how
/// bits are counted in parallel), over at least [`MIN_COUNT_REGION`] nodes.
fn walk(cx: &Context, n: u32, s: &mut Scratch, mode: Mode) -> (bool, bool, u32) {
    let slices = mode == Mode::Slices;
    s.seen.begin(cx.len());
    s.order.clear();
    s.atoms.clear();
    s.consts.clear();
    s.stack.clear();
    s.stack.push((n, false));
    let mut reached = 0u32;
    let (mut carried, mut bitwise) = (false, false);
    let (mut sliced_any, mut added) = (false, false);
    let (mut multiplied, mut lowered) = (false, false);
    let w = cx.wid(n);
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
        if !(match mode {
            Mode::Slices => sliced(cx, i),
            Mode::Counts => counted(cx, i),
            Mode::Bitwise => interior(cx, i),
        }) {
            s.atoms.push(i);
            let most = if mode == Mode::Counts { 1 } else { MAX_ATOMS };
            if s.atoms.len() > most || (mode != Mode::Bitwise && cx.wid(i) != w) {
                return (false, false, reached);
            }
            continue;
        }
        if s.undecided.contains_key(&i) {
            return (false, false, reached);
        }
        s.stack.push((i, true));
        let node = cx.node(i);
        if mode == Mode::Counts {
            multiplied |= node.op == OpCode::Mul;
            lowered |= matches!(node.op, OpCode::LShr | OpCode::AShr);
            added |= matches!(node.op, OpCode::Add | OpCode::Sub);
            if matches!(node.op, OpCode::Shl | OpCode::LShr | OpCode::AShr) {
                s.stack.push((node.a, false));
            } else {
                for c in node.children() {
                    s.stack.push((c, false));
                }
            }
        } else if slices {
            sliced_any |= node.op == OpCode::Extract;
            added |= matches!(node.op, OpCode::Add | OpCode::Sub | OpCode::Ult);
            for c in node.children() {
                s.stack.push((c, false));
            }
        } else if node.op == OpCode::Shl {
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
    if slices {
        return (sliced_any && added && !s.atoms.is_empty(), false, reached);
    }
    if mode == Mode::Counts {
        let fits = s.atoms.len() == 1
            && s.order.len() >= MIN_COUNT_REGION
            && (multiplied || (lowered && added));
        return (fits, false, reached);
    }
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
    for (row, &i) in s.order.iter().enumerate() {
        let row = t + row;
        let n = cx.node(i);
        // The node's own width: a region read through slices mixes them.
        let bits = u64::from(n.width);
        let mask = u64::MAX >> (64 - bits);
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
            OpCode::Add
            | OpCode::Sub
            | OpCode::Neg
            | OpCode::Mul
            | OpCode::LShr
            | OpCode::AShr
            | OpCode::Concat
            | OpCode::Extract
            | OpCode::Zext
            | OpCode::Sext
            | OpCode::Ult => {
                let at = |x: u32, k: usize| match operand(x) {
                    Ok(a) => a[k - lanes.start],
                    Err(c) => c,
                };
                let wa = u64::from(cx.wid(n.a));
                for k in lanes.clone() {
                    let x = at(n.a, k);
                    let v = match n.op {
                        OpCode::Add => x.wrapping_add(at(n.b, k)),
                        OpCode::Sub => x.wrapping_sub(at(n.b, k)),
                        OpCode::Neg => x.wrapping_neg(),
                        OpCode::Mul => x.wrapping_mul(at(n.b, k)),
                        OpCode::LShr => {
                            let c = at(n.b, k);
                            if c >= bits { 0 } else { x >> c }
                        }
                        OpCode::AShr => {
                            // The value read as signed at its width, shifted by at most W - 1.
                            let signed = ((x << (64 - bits)) as i64) >> (64 - bits);
                            (signed >> at(n.b, k).min(bits - 1)) as u64
                        }
                        // The low part is narrower than the 64 bits of the whole.
                        OpCode::Concat => (x << cx.wid(n.b)) | at(n.b, k),
                        OpCode::Extract => x >> n.b,
                        OpCode::Sext if x >> (wa - 1) & 1 == 1 => x | !(u64::MAX >> (64 - wa)),
                        OpCode::Ult => u64::from(x < at(n.b, k)),
                        _ => x,
                    };
                    out[k - lanes.start] = v & mask;
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
/// What a region is proved equal to.
#[derive(Clone, Copy)]
enum Target<'a> {
    /// `konst + Σ coeffs[j]·atom j`.
    Affine(u64, &'a [u64]),
    /// A bit count of the one atom.
    Count(UnOp),
}

fn copy(
    cx: &Context,
    s: &Scratch,
    scx: &mut Context,
    w: crate::Width,
    target: Target<'_>,
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
            OpCode::Neg => scx.c_un(UnOp::Neg, a)?,
            OpCode::Extract => scx.c_extract(a, node.b as u16, node.width)?,
            OpCode::Zext => scx.c_zext(a, node.width)?,
            OpCode::Sext => scx.c_sext(a, node.width)?,
            op => {
                let b = operand(scx, &map, node.b)?;
                match op {
                    OpCode::Concat => scx.c_concat(a, b)?,
                    OpCode::Ult => scx.c_cmp(CmpOp::Ult, a, b)?,
                    op => {
                        let bop = match op {
                            OpCode::And => BinOp::And,
                            OpCode::Or => BinOp::Or,
                            OpCode::Xor => BinOp::Xor,
                            OpCode::Add => BinOp::Add,
                            OpCode::Sub => BinOp::Sub,
                            OpCode::Mul => BinOp::Mul,
                            OpCode::LShr => BinOp::LShr,
                            OpCode::AShr => BinOp::AShr,
                            _ => BinOp::Shl,
                        };
                        scx.c_bin(bop, a, b)?
                    }
                }
            }
        };
        map.push(e);
    }
    let lhs = *map.last().unwrap_or(&0);
    let rhs = match target {
        Target::Count(op) => scx.c_un(op, map[0])?,
        Target::Affine(konst, coeffs) => {
            let mut rhs = scx.mk_const(&BitVec::wrapping_from_u64(w, konst))?;
            for (j, &k) in coeffs.iter().enumerate() {
                if k != 0 {
                    let k = scx.mk_const(&BitVec::wrapping_from_u64(w, k))?;
                    let term = scx.c_bin(BinOp::Mul, map[j], k)?;
                    rhs = scx.c_bin(BinOp::Add, rhs, term)?;
                }
            }
            rhs
        }
    };
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
    target: Target<'_>,
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
    let (lhs, rhs) = copy(cx, &r.carries, &mut scx, w, target).map_err(Stop::Error)?;
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

/// The bit count of its one atom the region (left by [`walk`] in [`Mode::Counts`]) can only
/// be: `popcnt`, `ctz` or `clz`, when it agrees with the region at every point; `None`
/// otherwise.
fn fit_count(r: &mut Runner<'_, '_>, cx: &Context, bits: u16) -> Result<Option<UnOp>, Stop> {
    let mask = u64::MAX >> (64 - u32::from(bits));
    let rows = (1 + r.carries.order.len()) as u64;
    let w = u32::from(bits);
    let count = |op: UnOp, v: u64| -> u64 {
        match op {
            UnOp::Popcnt => u64::from(v.count_ones()),
            UnOp::Ctz if v == 0 => u64::from(w),
            UnOp::Ctz => u64::from(v.trailing_zeros()),
            UnOp::Clz if v == 0 => u64::from(w),
            _ => u64::from(v.leading_zeros() - (64 - w)),
        }
    };
    let agree = |s: &Scratch, op: UnOp, lanes: core::ops::Range<usize>| {
        let f = s.order.len() * LANES;
        lanes
            .into_iter()
            .all(|k| count(op, s.rows[k] & mask) == s.rows[f + k] & mask)
    };
    r.meter.charge(
        Counter::PassWork,
        (rows * QUICK as u64).div_ceil(LANES_PER_UNIT),
    )?;
    evaluate(cx, &mut r.carries, mask, 0..QUICK);
    let Some(op) = [UnOp::Popcnt, UnOp::Ctz, UnOp::Clz]
        .into_iter()
        .find(|&op| agree(&r.carries, op, 0..QUICK))
    else {
        return Ok(None);
    };
    r.meter.charge(
        Counter::PassWork,
        (rows * (LANES - QUICK) as u64).div_ceil(LANES_PER_UNIT),
    )?;
    evaluate(cx, &mut r.carries, mask, QUICK..LANES);
    Ok(agree(&r.carries, op, QUICK..LANES).then_some(op))
}

/// The carries pass at `n` for a region read as a bit count ([`Mode::Counts`]): replaced by
/// `popcnt`, `ctz` or `clz` of its atom when the fit says so and the prover proves it.
fn step_count(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let bits = cx.wid(n);
    let (fits, _, reached) = walk(cx, n, &mut r.carries, Mode::Counts);
    r.meter.charge(Counter::PassWork, u64::from(reached))?;
    if !fits {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let Some(op) = fit_count(r, cx, bits)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    let atoms = r.carries.atoms.clone();
    if let Some(fin) = worth_building(r, cx, n, &atoms, 1)? {
        count(r).rejected_cost += 1;
        return Ok(Step::Normal(fin));
    }
    match proved(r, cx, n, Target::Count(op))? {
        Verdict::Proved => {}
        Verdict::No => return Ok(Step::Normal(Fin::FINAL)),
        Verdict::Unpaid => return Ok(Step::Normal(Fin::capped(Exhausted::PassWork))),
    }
    let before = cx.len() as u32;
    let x = atoms[0];
    let e = r.build(cx, |cx| cx.c_un(op, x))?;
    finish(r, cx, PassKind::Carries, n, e, before, &atoms, Fin::FINAL)
}

/// Whether node `n` can end a bit count spelled out: a right shift by a constant (the counts
/// gathered into the top byte, shifted down) or a mask (a count kept in the low bits).
fn ends_count(cx: &Context, n: u32) -> bool {
    let node = cx.node(n);
    matches!(node.op, OpCode::LShr | OpCode::And) && cx.is_const(node.b)
}

/// The carries pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let bits = cx.wid(n);
    let slices = cx.node(n).op == OpCode::Concat;
    if bits > 64 {
        return Ok(Step::Normal(Fin::FINAL));
    }
    if !(slices || interior(cx, n)) {
        if ends_count(cx, n) {
            return step_count(r, cx, n);
        }
        return Ok(Step::Normal(Fin::FINAL));
    }
    let mode = if slices { Mode::Slices } else { Mode::Bitwise };
    let (fits, chain, reached) = walk(cx, n, &mut r.carries, mode);
    r.meter.charge(Counter::PassWork, u64::from(reached))?;
    if !fits {
        if ends_count(cx, n) {
            return step_count(r, cx, n);
        }
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
        // One shift is its own form (`a << k`).
        if r.carries.order.len() == 1 && (1..u64::from(bits)).contains(&k) {
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
        match proved(r, cx, n, Target::Affine(konst, &coeffs))? {
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
    r.explain_with(|| crate::engine::Explanation::Carries {
        konst: BitVec::wrapping_from_u64(w, konst),
        terms: terms.iter().map(|&(a, k)| (cx.handle(a), k)).collect(),
        proved: !exact,
    });
    finish(r, cx, PassKind::Carries, n, e, before, &atoms, Fin::FINAL)
}
