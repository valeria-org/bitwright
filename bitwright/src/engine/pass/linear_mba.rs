//! The linear-MBA pass: linear combinations of bitwise functions of at most [`MAX_ATOMS`]
//! atoms, `E = c + Σ aᵢ·fᵢ(x₁, …, xₜ)`.
//!
//! Every bitwise function is an integer combination of conjunctions,
//! `f(x) = Σ_S c_S · AND_S(x)` (with `AND_∅ = −1`), bit by bit and therefore exactly in
//! Z/2^W. So a linear MBA is determined by its *signature*: its values at the 2^t corners
//! where every atom is 0 or all-ones (`AND_S = −1` exactly when every atom of `S` is set). The
//! pass recognizes the fragment (linear operators over bitwise functions of atoms, with only 0
//! and all-ones constants inside the bitwise parts), evaluates the signature, and emits the
//! cheaper of:
//!
//! - the affine form `c + Σ kⱼ·xⱼ`, when no conjunction of two or more atoms has a coefficient;
//! - `u₀ + Σₖ (u₀ − uₖ)·gₖ`, where `u₀, u₁, …` are the distinct signature values and `gₖ` is
//!   the minimum form of the bitwise function true exactly at the corners with value `uₖ`
//!   (three atoms or fewer, from the bitwise pass's table);
//! - the conjunction form `c + Σ_S k_S·AND_S` itself, read off the Möbius transform (any number
//!   of atoms), when a conjunction of two or more atoms remains.
//!
//! Both have the input's signature and are linear MBAs, so they are equal to it. The result
//! replaces the node when the DAG gets smaller.
//!
//! *Extensions.* A fragment reaches through `sext` and `zext` of bitwise functions of narrower
//! values (a lifter's `sext<64>(a & b)` over 32-bit `a`, `b`): the function is read over the
//! narrow atoms lifted to the root's width by the same cast, since `sext(f(a, b))` is
//! `f(sext a, sext b)` for every bitwise `f`, and `zext(f(a, b))` is `f(zext a, zext b)` when
//! `f` is 0 at 0, else that plus `2^W` (see [`interior`]). The emission is over the lifted
//! atoms, which it builds; the commit rule's boundary stays at the narrow atoms, so they count.

use super::{
    Counts, Fin, Marks, PassKind, Runner, Step, Stop, bitwise, finish, linear, worth_building,
};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};

/// The most atoms (the signature has 2^t entries).
pub(crate) const MAX_ATOMS: usize = 6;

/// The most fragment nodes examined per candidate.
const MAX_REGION: usize = 256;

/// The fragment below `root`: its atoms (in the context's canonical order), its interior nodes
/// in post-order, and whether it mixes linear and bitwise operators.
struct Region {
    /// The atoms the signature and the emission are over, in the canonical order: nodes of
    /// the root's width, among them the lifted atoms of the narrow atoms under casts.
    atoms: Vec<u32>,
    /// The interior nodes, operands first: the root's width, and under a cast its operand's.
    order: Vec<u32>,
    mixed: bool,
    /// The region's boundary for the commit rule: the atoms, with each narrow atom in place of
    /// its lifted one (which the emission builds, so it counts as new).
    bounds: Vec<u32>,
    /// Per narrow atom (under a cast): the lifted atom standing for it.
    lifts: Vec<(u32, u32)>,
}

fn is_linear(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Mul | OpCode::Shl
    )
}

fn is_bitwise(op: OpCode) -> bool {
    matches!(op, OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not)
}

/// How a node is read by its user: as a term of a linear combination, or as an operand of a
/// bitwise function (which must itself be a bitwise function of atoms).
#[derive(Copy, Clone, PartialEq, Eq)]
enum Mode {
    Linear,
    Bitwise,
}

/// Whether node `i` is interior when read in `mode` (otherwise it is an atom).
///
/// A cast is interior too (see the module notes on extensions): its operand is read as a
/// bitwise function at the narrower width, over narrow atoms the emission lifts. A sign
/// extension of a bitwise function is the function of the sign extensions (sign replication
/// commutes with every bitwise operator); a zero extension of one is the function of the zero
/// extensions when the function is 0 at 0 (above the operand's width every lifted atom is 0),
/// and that plus `2^W` when it is all ones there (`zext(~a)` is `~zext(a) + 2^W`, i.e.
/// `lowmask(W) − zext(a)`), which is a term but no operand of a bitwise function.
fn interior(cx: &Context, i: u32, mode: Mode) -> bool {
    let n = cx.node(i);
    if let Some(v) = cx.const_val(i) {
        // Inside bitwise functions only 0 and all-ones are uniform across bit positions.
        return mode == Mode::Linear || v.is_zero() || v.is_ones();
    }
    match n.op {
        OpCode::Sext => true,
        OpCode::Zext => mode == Mode::Linear || !at_zero(cx, n.a),
        // Linear operators are terms, never operands of a bitwise function.
        OpCode::Mul => {
            mode == Mode::Linear && (cx.const_val(n.a).is_some() || cx.const_val(n.b).is_some())
        }
        OpCode::Shl => mode == Mode::Linear && cx.const_val(n.b).is_some(),
        op if is_linear(op) => mode == Mode::Linear,
        // A bitwise operator whose constant operands are all 0 or all-ones.
        op if is_bitwise(op) => n
            .children()
            .all(|c| cx.const_val(c).is_none_or(|v| v.is_zero() || v.is_ones())),
        _ => false,
    }
}

/// Whether the bitwise function at `i` (over 0/all-ones constants and atoms) is all ones when
/// every atom is 0: its value above the operand's width once zero-extended.
fn at_zero(cx: &Context, i: u32) -> bool {
    fn go(cx: &Context, i: u32, depth: u32) -> bool {
        let n = cx.node(i);
        if let Some(v) = cx.const_val(i) {
            return v.is_ones();
        }
        if depth > 64 {
            return false;
        }
        match n.op {
            OpCode::Not => !go(cx, n.a, depth + 1),
            OpCode::And => go(cx, n.a, depth + 1) && go(cx, n.b, depth + 1),
            OpCode::Or => go(cx, n.a, depth + 1) || go(cx, n.b, depth + 1),
            OpCode::Xor => go(cx, n.a, depth + 1) ^ go(cx, n.b, depth + 1),
            _ => false,
        }
    }
    go(cx, i, 0)
}

/// The mode in which node `i`'s operands are read, when `i` is read in `mode`.
fn operand_mode(cx: &Context, i: u32, mode: Mode) -> Mode {
    match cx.node(i).op {
        OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Zext | OpCode::Sext => Mode::Bitwise,
        // `~x` is `−x − 1` among terms and a bitwise function among bitwise operands.
        OpCode::Not => mode,
        _ => Mode::Linear,
    }
}

enum Walk {
    /// A node is interior in one reading and an atom in another: it must be an atom.
    Conflict(u32),
    Over,
}

/// A walk's stack entry: the node, its mode, whether its operands are listed, and the cast it
/// is under (its kind and the cast node).
type Frame = (u32, Mode, bool, Option<(OpCode, u32)>);

/// The walks' and signatures' buffers, kept by the runner and reused.
#[derive(Default)]
pub(crate) struct Scratch {
    /// In a walk, per node reached: bit 0 whether it is interior, bit 1 + mode the readings
    /// seen, bit 3 whether it is in the post-order. In a signature, per region node: its row
    /// of corner values in `words`.
    seen: Counts,
    /// Nodes that must be atoms.
    forced: Marks,
    stack: Vec<Frame>,
    words: Vec<u64>,
    /// In a walk, per node under a cast: the kind of cast it was first reached under, and that
    /// cast. A node reached under casts of two kinds would be two functions of the lifted
    /// atoms: the second cast is an atom.
    under: IdMap<u32, (OpCode, u32)>,
}

/// The `seen` bit of a node in the post-order.
const LISTED: u32 = 8;

fn walk(cx: &Context, root: u32, s: &mut Scratch) -> Result<Region, Walk> {
    s.seen.begin(cx.len());
    s.under.clear();
    let mut reached = 0usize;
    let mut order = Vec::new();
    let mut atoms = Vec::new();
    // Narrow atoms, each with the kind of cast it is under (lifted after the walk).
    let mut narrow: Vec<(u32, OpCode)> = Vec::new();
    let (mut lin, mut bit) = (false, false);
    s.stack.clear();
    s.stack.push((root, Mode::Linear, false, None));
    while let Some((i, mode, expanded, lift)) = s.stack.pop() {
        if expanded {
            order.push(i);
            continue;
        }
        let op = cx.node(i).op;
        // Under a cast: bitwise operators over uniform constants, nothing else (a cast there
        // is an atom too, lifted by the outer one).
        let inner = !s.forced.contains(i)
            && interior(cx, i, mode)
            && (lift.is_none() || is_bitwise(op) || cx.const_val(i).is_some());
        if let Some((kind, cast)) = lift {
            match s.under.get(&i) {
                Some(&(k, _)) if k != kind => return Err(Walk::Conflict(cast)),
                Some(_) => {}
                None => {
                    s.under.insert(i, (kind, cast));
                }
            }
        }
        let read = 2 << mode as u32;
        match s.seen.get(i) {
            Some(state) => {
                if (state & 1 == 1) != inner {
                    return Err(Walk::Conflict(i));
                }
                if state & read != 0 {
                    continue;
                }
                s.seen.set(i, state | read);
                if !inner {
                    continue;
                }
            }
            None => {
                s.seen.set(i, u32::from(inner) | read);
                reached += 1;
                if reached > MAX_REGION {
                    return Err(Walk::Over);
                }
                if !inner {
                    match lift {
                        Some((kind, _)) => narrow.push((i, kind)),
                        None => atoms.push(i),
                    }
                    if atoms.len() + narrow.len() > MAX_ATOMS {
                        return Err(Walk::Over);
                    }
                    continue;
                }
                s.stack.push((i, mode, true, lift));
            }
        }
        lin |= is_linear(op);
        // (A complement under a cast counts: `zext(~a)` is a term the linear pass cannot read
        // without the extension of `a`.)
        bit |= matches!(op, OpCode::And | OpCode::Or | OpCode::Xor)
            || (op == OpCode::Not && lift.is_some());
        let m = operand_mode(cx, i, mode);
        let under = match op {
            OpCode::Zext | OpCode::Sext => Some((op, i)),
            _ => lift,
        };
        for c in cx.node(i).children() {
            s.stack.push((c, m, false, under));
        }
    }
    // Keep each interior node once, operands first (a node read in both modes was pushed twice).
    order.retain(|&i| {
        let state = s.seen.get(i).unwrap_or(0);
        s.seen.set(i, state | LISTED);
        state & LISTED == 0
    });
    // The canonical order of the atoms, independent of node indices.
    atoms.sort_by(|a, b| cx.order(*a, *b));
    Ok(Region {
        bounds: atoms
            .iter()
            .copied()
            .chain(narrow.iter().map(|&(a, _)| a))
            .collect(),
        atoms,
        order,
        mixed: lin && bit,
        // The kinds, until the atoms are lifted (see `lift`).
        lifts: narrow.iter().map(|&(a, k)| (a, k as u32)).collect(),
    })
}

/// Lifts the region's narrow atoms: each becomes the cast of its kind to the root's width
/// (built, so counted as new by the commit rule, the narrow atom staying the boundary), and
/// joins the atoms in the canonical order.
fn lift(r: &mut Runner<'_, '_>, cx: &mut Context, reg: &mut Region, w: u16) -> Result<(), Stop> {
    let kinds = core::mem::take(&mut reg.lifts);
    for (a, kind) in kinds {
        let sext = kind == OpCode::Sext as u32;
        let l = r.build(cx, |cx| {
            if sext {
                cx.c_sext(a, w)
            } else {
                cx.c_zext(a, w)
            }
        })?;
        reg.lifts.push((a, l));
        if !reg.atoms.contains(&l) {
            reg.atoms.push(l);
        }
    }
    reg.atoms.sort_by(|a, b| cx.order(*a, *b));
    Ok(())
}

fn region(cx: &Context, root: u32, s: &mut Scratch) -> Option<Region> {
    s.forced.begin(cx.len());
    for _ in 0..32 {
        match walk(cx, root, s) {
            Ok(r) => return Some(r),
            Err(Walk::Conflict(i)) if i != root => {
                s.forced.insert(i);
            }
            Err(_) => return None,
        }
    }
    None
}

/// The values of the root at the 2^t corners (corner `p`: atom `j` is all-ones when bit `j` of
/// `p` is set).
fn signature(cx: &Context, reg: &Region, root: u32, s: &mut Scratch) -> Vec<BitVec> {
    let w = cx.width_of(root);
    let bits = u64::from(w.bits());
    if bits > 64 {
        return signature_wide(cx, reg, root);
    }
    // Every region node has the root's width: a row of words per node, masked to it.
    let mask = u64::MAX >> (64 - bits);
    let t = reg.atoms.len();
    let corners = 1usize << t;
    s.seen.begin(cx.len());
    s.words.clear();
    s.words.resize((t + reg.order.len()) * corners, 0);
    for (j, &a) in reg.atoms.iter().enumerate() {
        s.seen.set(a, j as u32);
        for (p, v) in s.words[j * corners..(j + 1) * corners]
            .iter_mut()
            .enumerate()
        {
            if p >> j & 1 == 1 {
                *v = mask;
            }
        }
    }
    // A narrow atom reads as its lifted atom: under its cast, the nodes are evaluated at the
    // root's width over the lifted atoms (bitwise operators act by position).
    for &(a, l) in &reg.lifts {
        match s.seen.get(l) {
            Some(j) => s.seen.set(a, j),
            None => return signature_wide(cx, reg, root),
        }
    }
    for (k, &i) in reg.order.iter().enumerate() {
        let at = (t + k) * corners;
        s.seen.set(i, (t + k) as u32);
        let (done, rest) = s.words.split_at_mut(at);
        let out = &mut rest[..corners];
        if let Some(c) = cx.const_val(i) {
            // A uniform constant under a cast at the root's width.
            out.fill(if c.is_ones() { mask } else { c.limbs()[0] });
            continue;
        }
        let n = cx.node(i);
        let operand = |x: u32| {
            s.seen
                .get(x)
                .map(|r| &done[r as usize * corners..(r as usize + 1) * corners])
        };
        let Some(a) = operand(n.a) else {
            return signature_wide(cx, reg, root);
        };
        match n.op {
            OpCode::Sext => out.copy_from_slice(a),
            // The function of the lifted atoms, plus `2^W` where it is all ones at 0 (above
            // the operand's width, where the lifted atoms are 0).
            OpCode::Zext => {
                let above = if a[0] == mask {
                    1u64 << cx.width_of(n.a).bits()
                } else {
                    0
                };
                out.iter_mut()
                    .zip(a)
                    .for_each(|(o, &x)| *o = x.wrapping_add(above) & mask);
            }
            OpCode::Not => out.iter_mut().zip(a).for_each(|(o, &x)| *o = !x & mask),
            OpCode::Neg => out
                .iter_mut()
                .zip(a)
                .for_each(|(o, &x)| *o = x.wrapping_neg() & mask),
            op => {
                let Some(b) = operand(n.b) else {
                    return signature_wide(cx, reg, root);
                };
                let f: fn(u64, u64, u64) -> u64 = match op {
                    OpCode::Add => |x, y, _| x.wrapping_add(y),
                    OpCode::Sub => |x, y, _| x.wrapping_sub(y),
                    OpCode::Mul => |x, y, _| x.wrapping_mul(y),
                    OpCode::Shl => |x, y, bits| if y < bits { x << y } else { 0 },
                    OpCode::And => |x, y, _| x & y,
                    OpCode::Or => |x, y, _| x | y,
                    OpCode::Xor => |x, y, _| x ^ y,
                    _ => return signature_wide(cx, reg, root),
                };
                for (o, (&x, &y)) in out.iter_mut().zip(a.iter().zip(b)) {
                    *o = f(x, y, bits) & mask;
                }
            }
        }
    }
    let r = (t + reg.order.len() - 1) * corners;
    match s.seen.get(root) {
        Some(k) if k as usize * corners == r => s.words[r..r + corners]
            .iter()
            .map(|&v| BitVec::wrapping_from_u64(w, v))
            .collect(),
        _ => signature_wide(cx, reg, root),
    }
}

/// [`signature`] in `BitVec`s, for any width.
fn signature_wide(cx: &Context, reg: &Region, root: u32) -> Vec<BitVec> {
    let w = cx.width_of(root);
    let t = reg.atoms.len();
    let corners = 1usize << t;
    let mut vals: IdMap<u32, Vec<BitVec>> = IdMap::default();
    for (j, &a) in reg.atoms.iter().enumerate() {
        let v = (0..corners)
            .map(|p| {
                if p >> j & 1 == 1 {
                    BitVec::ones(w)
                } else {
                    BitVec::zero(w)
                }
            })
            .collect();
        vals.insert(a, v);
    }
    for &(a, l) in &reg.lifts {
        let v = vals.get(&l).cloned().unwrap_or_default();
        vals.insert(a, v);
    }
    for &i in &reg.order {
        let n = cx.node(i);
        let v: Vec<BitVec> = if let Some(c) = cx.const_val(i) {
            let c = if c.is_ones() {
                BitVec::ones(w)
            } else {
                c.zext(w).unwrap_or(c)
            };
            vec![c; corners]
        } else {
            let above = (n.op == OpCode::Zext && vals[&n.a][0].is_ones()).then(|| {
                crate::facts::known::bv_shl(&BitVec::one(w), u32::from(cx.width_of(n.a).bits()))
            });
            (0..corners)
                .map(|p| {
                    let get = |j: u32| vals[&j][p];
                    match n.op {
                        OpCode::Sext => get(n.a),
                        OpCode::Zext => match &above {
                            Some(k) => BitVec::bin_unchecked(BinOp::Add, &get(n.a), k),
                            None => get(n.a),
                        },
                        OpCode::Not => BitVec::un_unchecked(UnOp::Not, &get(n.a)),
                        OpCode::Neg => BitVec::un_unchecked(UnOp::Neg, &get(n.a)),
                        op => {
                            let b = op.as_bin().unwrap_or(BinOp::Add);
                            BitVec::bin_unchecked(b, &get(n.a), &get(n.b))
                        }
                    }
                })
                .collect()
        };
        vals.insert(i, v);
    }
    vals.remove(&root).unwrap_or_default()
}

/// The conjunction coefficients `d_S` from the signature: `−E(p) = Σ_{S ⊆ p} d_S`.
fn mobius(sig: &[BitVec]) -> Vec<BitVec> {
    let mut d: Vec<BitVec> = sig
        .iter()
        .map(|v| BitVec::un_unchecked(UnOp::Neg, v))
        .collect();
    let n = d.len();
    let mut bit = 1;
    while bit < n {
        for p in 0..n {
            if p & bit != 0 {
                d[p] = BitVec::bin_unchecked(BinOp::Sub, &d[p], &d[p ^ bit]);
            }
        }
        bit <<= 1;
    }
    d
}

/// The candidate forms, cheapest first by an estimate of new nodes.
enum Candidate {
    /// `konst + Σ k·atom` (atoms by position).
    Affine(BitVec, Vec<(usize, BitVec)>),
    /// `u0 + Σ (u0 − uk)·gk`: the base value, and per other value its coefficient and table.
    Indicators(BitVec, Vec<(BitVec, u8)>),
    /// `konst + Σ k·AND_S`: per nonempty atom set (a bit mask over positions), its coefficient.
    Conjunctions(BitVec, Vec<(usize, BitVec)>),
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry("linear_mba").or_default()
}

/// The linear-MBA pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    Ok(solve(r, cx, n, true)?.0)
}

/// The cheapest form of the linear MBA at `n`, built whatever it costs and committed nowhere:
/// for a caller that measures the result itself. `None` when `n` is no mixed fragment.
#[cfg(feature = "prove")]
pub(super) fn normal(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<u32>, Stop> {
    Ok(solve(r, cx, n, false)?.1)
}

/// [`step`] when `commit`; else the form alone ([`normal`]).
fn solve(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    commit: bool,
) -> Result<(Step, Option<u32>), Stop> {
    let op = cx.node(n).op;
    if !(is_linear(op) || is_bitwise(op)) || !interior(cx, n, Mode::Linear) {
        return Ok((Step::Normal(Fin::FINAL), None));
    }
    let Some(mut reg) = region(cx, n, &mut r.linear_mba) else {
        count(r).atomized += 1;
        return Ok((Step::Normal(Fin::FINAL), None));
    };
    // Pure linear or pure bitwise regions belong to those passes.
    if !reg.mixed || reg.bounds.is_empty() {
        return Ok((Step::Normal(Fin::FINAL), None));
    }
    let w = cx.width_of(n);
    // The lifted atoms are built now: `before` lets a rejection discard them.
    let before = cx.len() as u32;
    lift(r, cx, &mut reg, w.bits())?;
    let t = reg.atoms.len();
    if t > MAX_ATOMS {
        count(r).atomized += 1;
        return Ok((Step::Normal(Fin::FINAL), None));
    }
    let lifted = reg.lifts.len() as u32;
    r.meter
        .charge(Counter::PassWork, (reg.order.len() << t) as u64)?;
    let sig = signature(cx, &reg, n, &mut r.linear_mba);
    let d = mobius(&sig);
    // (The atoms, and so the corners, are already in the canonical order.)
    let canon = reg.atoms.clone();
    let mut cands: Vec<(u32, Candidate)> = Vec::new();
    if (0..d.len()).all(|s| (s as u32).count_ones() < 2 || d[s].is_zero()) {
        let konst = BitVec::un_unchecked(UnOp::Neg, &d[0]);
        let terms: Vec<(usize, BitVec)> = (0..t)
            .filter(|&j| !d[1 << j].is_zero())
            .map(|j| (j, d[1 << j]))
            .collect();
        let placeholder: Vec<(u32, BitVec)> =
            terms.iter().map(|(j, k)| (reg.atoms[*j], *k)).collect();
        let est = linear::estimate(&linear::Form::of(konst, &placeholder));
        cands.push((est, Candidate::Affine(konst, terms)));
    }
    if (0..d.len()).any(|s| (s as u32).count_ones() >= 2 && !d[s].is_zero()) {
        let konst = BitVec::un_unchecked(UnOp::Neg, &d[0]);
        let terms: Vec<(usize, BitVec)> = (1..d.len())
            .filter(|&s| !d[s].is_zero())
            .map(|s| (s, d[s]))
            .collect();
        // Each conjunction of m atoms costs m − 1 ands (an upper bound: none are shared).
        let ands: u32 = terms
            .iter()
            .map(|&(s, _)| (s as u32).count_ones() - 1)
            .sum();
        let placeholder: Vec<(u32, BitVec)> = terms
            .iter()
            .enumerate()
            .map(|(k, &(_, c))| (u32::MAX - k as u32, c))
            .collect();
        let est = ands + linear::estimate(&linear::Form::of(konst, &placeholder));
        cands.push((est, Candidate::Conjunctions(konst, terms)));
    }
    if t <= 3 {
        // Distinct values, in order of first appearance; each as the base in turn.
        let mut distinct: Vec<BitVec> = Vec::new();
        for v in &sig {
            if !distinct.contains(v) {
                distinct.push(*v);
            }
        }
        // Corners in the canonical variable order.
        let pos: Vec<usize> = canon
            .iter()
            .map(|a| reg.atoms.iter().position(|b| b == a).unwrap_or(0))
            .collect();
        for &u0 in &distinct {
            let mut ind: Vec<(BitVec, u8)> = Vec::new();
            let mut funcs = 0u32;
            let mut placeholder: Vec<(u32, BitVec)> = Vec::new();
            for &uk in distinct.iter().filter(|&&u| u != u0) {
                let mut tt = 0u8;
                for i in 0..8usize {
                    // Canonical corner `i` → region corner.
                    let mut p = 0usize;
                    for (k, &j) in pos.iter().enumerate() {
                        p |= ((i >> k) & 1) << j;
                    }
                    if sig[p & ((1 << t) - 1)] == uk {
                        tt |= 1 << i;
                    }
                }
                // The function's operators and constants, plus its term in the sum.
                funcs += bitwise::min_forms().forms[tt as usize]
                    .0
                    .iter()
                    .filter(|t| !matches!(t, bitwise::T::Var(_)))
                    .count() as u32;
                let k = BitVec::bin_unchecked(BinOp::Sub, &u0, &uk);
                // (Distinct placeholder atoms: the estimate only needs the coefficients.)
                placeholder.push((u32::MAX - placeholder.len() as u32, k));
                ind.push((k, tt));
            }
            let est = funcs + linear::estimate(&linear::Form::of(u0, &placeholder));
            cands.push((est, Candidate::Indicators(u0, ind)));
        }
    }
    cands.sort_by_key(|c| c.0);
    let Some((est, cand)) = cands.into_iter().next() else {
        super::discard(r, cx, before);
        return Ok((Step::Normal(Fin::FINAL), None));
    };
    if commit && let Some(f) = worth_building(r, cx, n, &reg.bounds, est + lifted)? {
        count(r).rejected_cost += 1;
        super::discard(r, cx, before);
        return Ok((Step::Normal(f), None));
    }
    let kind = match &cand {
        Candidate::Affine(..) => "affine",
        Candidate::Indicators(..) => "indicators",
        Candidate::Conjunctions(..) => "conjunctions",
    };
    let form = match cand {
        Candidate::Affine(konst, terms) => {
            let terms: Vec<(u32, BitVec)> =
                terms.iter().map(|(j, k)| (reg.atoms[*j], *k)).collect();
            linear::Form::of(konst, &terms)
        }
        Candidate::Indicators(u0, ind) => {
            let mut terms = Vec::new();
            for (k, tt) in ind {
                let g = bitwise::emit(r, cx, tt, &canon)?;
                terms.push((g, k));
            }
            linear::Form::of(u0, &terms)
        }
        Candidate::Conjunctions(konst, sets) => {
            let mut terms = Vec::new();
            for (set, k) in sets {
                // The atoms of the set, in the canonical order, and-ed together.
                let mut acc: Option<u32> = None;
                for (j, &a) in reg.atoms.iter().enumerate() {
                    if set & (1 << j) != 0 {
                        acc = Some(match acc {
                            None => a,
                            Some(x) => r.build(cx, |cx| cx.c_bin(BinOp::And, x, a))?,
                        });
                    }
                }
                if let Some(g) = acc {
                    terms.push((g, k));
                }
            }
            linear::Form::of(konst, &terms)
        }
    };
    let e = linear::emit(r, cx, &form)?;
    if !commit {
        return Ok((Step::Normal(Fin::FINAL), Some(e)));
    }
    r.explain_with(|| crate::engine::Explanation::LinearMba {
        atoms: reg.atoms.iter().map(|&a| cx.handle(a)).collect(),
        corners: sig.clone(),
        form: kind,
    });
    let step = finish(
        r,
        cx,
        PassKind::LinearMba,
        n,
        e,
        before,
        &reg.bounds,
        Fin::FINAL,
    )?;
    Ok((step, None))
}
