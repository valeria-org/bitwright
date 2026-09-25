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
    atoms: Vec<u32>,
    order: Vec<u32>,
    mixed: bool,
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
fn interior(cx: &Context, i: u32, mode: Mode) -> bool {
    let n = cx.node(i);
    if let Some(v) = cx.const_val(i) {
        // Inside bitwise functions only 0 and all-ones are uniform across bit positions.
        return mode == Mode::Linear || v.is_zero() || v.is_ones();
    }
    match n.op {
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

/// The mode in which node `i`'s operands are read, when `i` is read in `mode`.
fn operand_mode(cx: &Context, i: u32, mode: Mode) -> Mode {
    match cx.node(i).op {
        OpCode::And | OpCode::Or | OpCode::Xor => Mode::Bitwise,
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

/// The walks' and signatures' buffers, kept by the runner and reused.
#[derive(Default)]
pub(crate) struct Scratch {
    /// In a walk, per node reached: bit 0 whether it is interior, bit 1 + mode the readings
    /// seen, bit 3 whether it is in the post-order. In a signature, per region node: its row
    /// of corner values in `words`.
    seen: Counts,
    /// Nodes that must be atoms.
    forced: Marks,
    stack: Vec<(u32, Mode, bool)>,
    words: Vec<u64>,
}

/// The `seen` bit of a node in the post-order.
const LISTED: u32 = 8;

fn walk(cx: &Context, root: u32, s: &mut Scratch) -> Result<Region, Walk> {
    s.seen.begin(cx.len());
    let mut reached = 0usize;
    let mut order = Vec::new();
    let mut atoms = Vec::new();
    let (mut lin, mut bit) = (false, false);
    s.stack.clear();
    s.stack.push((root, Mode::Linear, false));
    while let Some((i, mode, expanded)) = s.stack.pop() {
        if expanded {
            order.push(i);
            continue;
        }
        let inner = !s.forced.contains(i) && interior(cx, i, mode);
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
                    atoms.push(i);
                    if atoms.len() > MAX_ATOMS {
                        return Err(Walk::Over);
                    }
                    continue;
                }
                s.stack.push((i, mode, true));
            }
        }
        let op = cx.node(i).op;
        lin |= is_linear(op);
        bit |= matches!(op, OpCode::And | OpCode::Or | OpCode::Xor);
        let m = operand_mode(cx, i, mode);
        for c in cx.node(i).children() {
            s.stack.push((c, m, false));
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
        atoms,
        order,
        mixed: lin && bit,
    })
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
    for (k, &i) in reg.order.iter().enumerate() {
        let at = (t + k) * corners;
        s.seen.set(i, (t + k) as u32);
        let (done, rest) = s.words.split_at_mut(at);
        let out = &mut rest[..corners];
        if let Some(c) = cx.const_val(i) {
            out.fill(c.limbs()[0]);
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
    for &i in &reg.order {
        let n = cx.node(i);
        let v: Vec<BitVec> = if let Some(c) = cx.const_val(i) {
            vec![c; corners]
        } else {
            (0..corners)
                .map(|p| {
                    let get = |j: u32| vals[&j][p];
                    match n.op {
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
    let op = cx.node(n).op;
    if !(is_linear(op) || is_bitwise(op)) || !interior(cx, n, Mode::Linear) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let Some(reg) = region(cx, n, &mut r.linear_mba) else {
        count(r).atomized += 1;
        return Ok(Step::Normal(Fin::FINAL));
    };
    // Pure linear or pure bitwise regions belong to those passes.
    if !reg.mixed || reg.atoms.is_empty() {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let t = reg.atoms.len();
    r.meter
        .charge(Counter::PassWork, (reg.order.len() << t) as u64)?;
    let sig = signature(cx, &reg, n, &mut r.linear_mba);
    let w = cx.width_of(n);
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
        return Ok(Step::Normal(Fin::FINAL));
    };
    if let Some(f) = worth_building(r, cx, n, &reg.atoms, est)? {
        count(r).rejected_cost += 1;
        return Ok(Step::Normal(f));
    }
    let before = cx.len() as u32;
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
    let _ = w;
    let e = linear::emit(r, cx, &form)?;
    finish(
        r,
        cx,
        PassKind::LinearMba,
        n,
        e,
        before,
        &reg.atoms,
        Fin::FINAL,
    )
}
