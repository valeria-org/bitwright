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
//! replaces the node when the DAG gets smaller, or stays the same size and the node becomes a
//! smaller tree (an XOR written as a sum whose parts something else reads).
//!
//! *Extensions.* A fragment reaches through `sext` and `zext` of bitwise functions of narrower
//! values (a lifter's `sext<64>(a & b)` over 32-bit `a`, `b`): the function is read over the
//! narrow atoms lifted to the root's width by the same cast, since `sext(f(a, b))` is
//! `f(sext a, sext b)` for every bitwise `f`, and `zext(f(a, b))` is `f(zext a, zext b)` when
//! `f` is 0 at 0, else that plus `2^W` (see [`interior`]). The emission is over the lifted
//! atoms, which it builds; the commit rule's boundary stays at the narrow atoms, so they count.

use super::{
    Counts, Fin, Marks, PassKind, Runner, Step, Stop, bitwise, finish_with, linear, worth_building,
};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};

/// The most atoms (the signature has 2^t entries).
pub(crate) const MAX_ATOMS: usize = 8;

/// The part of a call's pass work one decomposition over the basis of small bitwise
/// functions may read (see [`solve`]): 1,024 units with fuel `1 << 14`, where a sum over
/// five or six atoms reads up to 13,000 and the forty-three sums of one question read more
/// than the call's other passes had left; 262,144 at the default.
const COBRA_SHARE: u64 = 256;

/// The fraction of a call's pass work all deferred links of one declined chain may spend in
/// [`held_back`], and its floor.
const HELD_BACK_SHARE: u64 = 32;
const HELD_BACK_MIN: u64 = 2048;

/// The most fragment nodes examined per candidate.
const MAX_REGION: usize = 2048;

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
    /// Atoms proved to be equal (`negate = false`) or the bitwise complement (`negate = true`,
    /// `a + b == -1`) of an earlier atom: `(alias_atom, base_atom, negate)`. Evaluated as
    /// `base_atom` or `!base_atom` in the signature without spending a fresh variable column.
    complements: Vec<(u32, u32, bool)>,
    /// Atoms proved to be the disjoint bitwise union of two other atoms (`rotl(x, k) ==
    /// (x << k) | (x >>u (w - k))`): `(rot_atom, shl_atom, lshr_atom)`. Evaluated as
    /// `shl_atom | lshr_atom` in the signature without spending a fresh variable column.
    rot_unions: Vec<(u32, u32, u32)>,
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
    interior_ext(cx, i, mode, None, false)
}

fn interior_ext(
    cx: &Context,
    i: u32,
    mode: Mode,
    forced: Option<&Marks>,
    allow_const_atoms: bool,
) -> bool {
    let n = cx.node(i);
    if let Some(v) = cx.const_val(i) {
        // Inside bitwise functions only 0 and all-ones are uniform across bit positions.
        return mode == Mode::Linear || v.is_zero() || v.is_ones();
    }
    let unforced_const =
        |c: u32| cx.const_val(c).is_some() && !forced.is_some_and(|f| f.contains(c));
    match n.op {
        OpCode::Sext => true,
        OpCode::Zext => mode == Mode::Linear || !at_zero(cx, n.a),
        // Linear operators are terms, never operands of a bitwise function.
        OpCode::Mul => mode == Mode::Linear && (unforced_const(n.a) || unforced_const(n.b)),
        OpCode::Shl => mode == Mode::Linear && unforced_const(n.b),
        op if is_linear(op) => mode == Mode::Linear,
        // A bitwise operator whose constant operands are all 0 or all-ones (or treated as shared
        // constant atoms in proof-only `difference_is_zero` checks).
        op if is_bitwise(op) => {
            allow_const_atoms
                || n.children()
                    .all(|c| cx.const_val(c).is_none_or(|v| v.is_zero() || v.is_ones()))
        }
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
    /// In a phase run, per link of an additive chain that left its solve to its user: that
    /// user (see [`step`]).
    deferred: IdMap<u32, u32>,
    /// Nodes whose `solve` declined on cost (`worth_building`) in this call, with their region
    /// boundary and candidate cost ceiling `(bounds, most)`. Re-checking `worth_building` on
    /// subsequent rounds avoids recomputing identical signatures and CoBRA decompositions while
    /// refcounts have not dropped.
    declined: IdMap<u32, (Vec<u32>, u32)>,
}

impl Scratch {
    /// A phase run begins: what the chains deferred was of the one before.
    pub(crate) fn begin(&mut self) {
        self.deferred.clear();
    }
}

/// The `seen` bit of a node in the post-order.
const LISTED: u32 = 8;

fn walk<const QUICK: bool>(
    cx: &Context,
    root: u32,
    s: &mut Scratch,
    visits: &mut usize,
    allow_slice_rot: bool,
    allow_const_atoms: bool,
) -> Result<Region, Walk> {
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
        let inner = (!QUICK || !matches!(op, OpCode::Sext | OpCode::Zext))
            && !s.forced.contains(i)
            && interior_ext(
                cx,
                i,
                mode,
                Some(&s.forced),
                allow_const_atoms && lift.is_none(),
            )
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
                if QUICK {
                    *visits += 1;
                }
                if reached > if QUICK { 160 } else { MAX_REGION } {
                    return Err(Walk::Over);
                }
                if !inner {
                    match lift {
                        Some((kind, _)) => narrow.push((i, kind)),
                        None => atoms.push(i),
                    }
                    if atoms.len() + narrow.len() > if QUICK { 5 } else { MAX_ATOMS + 4 } {
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
    let mut reg = Region {
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
        complements: Vec::new(),
        rot_unions: Vec::new(),
    };
    if !QUICK {
        merge_rot_union_atoms(cx, &mut reg, allow_slice_rot);
        merge_complement_atoms(cx, &mut reg);
    }
    if reg.atoms.len() + reg.lifts.len() > if QUICK { 5 } else { MAX_ATOMS } {
        return Err(Walk::Over);
    }
    Ok(reg)
}

/// Canonical leaf key `(node, low_mask)` for `flatten_affine`, unifying `x & m` with
/// `zext<w>(extract<0, k>(x))` (`m = 2^k - 1`).
fn affine_leaf(cx: &Context, i: u32, w: u16, full: u64) -> (u32, u64) {
    let n = cx.node(i);
    match n.op {
        OpCode::Zext if n.width == w => {
            let inner = cx.node(n.a);
            if inner.op == OpCode::Extract
                && inner.b == 0
                && cx.wid(inner.a) == w
                && inner.width < w
            {
                let m = (1u64 << inner.width) - 1;
                return (inner.a, m);
            }
        }
        OpCode::And => {
            if let Some(m) = cx.const_val(n.b).and_then(|v| v.to_u64()) {
                return (n.a, m & full);
            }
            if let Some(m) = cx.const_val(n.a).and_then(|v| v.to_u64()) {
                return (n.b, m & full);
            }
        }
        _ => {}
    }
    (i, full)
}

/// Flatten a small additive node (`<= 64` bits) into `(sorted_terms, bias)` mod `2^w`,
/// expanding disjoint `Or` (`a | b == a + b`) and subset `Xor` with a constant (`c ^ x == c - x`).
fn flatten_affine(cx: &Context, root: u32, w: u16) -> Option<AffineForm> {
    let mask = u64::MAX >> (64 - w);
    let mut bias = 0u64;
    let mut parts: Vec<((u32, u64), u64)> = Vec::new();
    let mut stack: Vec<(u32, u64, u8)> = vec![(root, 1, 16)];
    let mut steps = 0usize;
    while let Some((i, k, depth)) = stack.pop() {
        steps += 1;
        if steps > 64 || parts.len() > 24 {
            return None;
        }
        let n = cx.node(i);
        if depth == 0 {
            parts.push((affine_leaf(cx, i, w, mask), k));
            continue;
        }
        match n.op {
            OpCode::Const => {
                bias = bias.wrapping_add(k.wrapping_mul(cx.const_val(i)?.to_u64()?));
            }
            OpCode::Add => {
                stack.push((n.a, k, depth - 1));
                stack.push((n.b, k, depth - 1));
            }
            OpCode::Sub => {
                stack.push((n.a, k, depth - 1));
                stack.push((n.b, k.wrapping_neg(), depth - 1));
            }
            OpCode::Neg => {
                stack.push((n.a, k.wrapping_neg(), depth - 1));
            }
            OpCode::Not => {
                bias = bias.wrapping_sub(k);
                stack.push((n.a, k.wrapping_neg(), depth - 1));
            }
            OpCode::Mul if cx.const_val(n.b).and_then(|v| v.to_u64()).is_some() => {
                let c = cx.const_val(n.b)?.to_u64()?;
                stack.push((n.a, k.wrapping_mul(c), depth - 1));
            }
            OpCode::Mul if cx.const_val(n.a).and_then(|v| v.to_u64()).is_some() => {
                let c = cx.const_val(n.a)?.to_u64()?;
                stack.push((n.b, k.wrapping_mul(c), depth - 1));
            }
            OpCode::Shl
                if cx
                    .const_val(n.b)
                    .and_then(|v| v.to_u64())
                    .is_some_and(|s| s < u64::from(w)) =>
            {
                let s = cx.const_val(n.b)?.to_u64()?;
                stack.push((n.a, k << s, depth - 1));
            }
            OpCode::Or if (atom_may_one(cx, n.a, 8) & atom_may_one(cx, n.b, 8) & mask) == 0 => {
                stack.push((n.a, k, depth - 1));
                stack.push((n.b, k, depth - 1));
            }
            OpCode::Xor if cx.const_val(n.b).and_then(|v| v.to_u64()).is_some() => {
                let c = cx.const_val(n.b)?.to_u64()? & mask;
                if (atom_may_one(cx, n.a, 8) & !c & mask) == 0 {
                    bias = bias.wrapping_add(k.wrapping_mul(c));
                    stack.push((n.a, k.wrapping_neg(), depth - 1));
                } else {
                    parts.push((affine_leaf(cx, i, w, mask), k));
                }
            }
            OpCode::Xor if cx.const_val(n.a).and_then(|v| v.to_u64()).is_some() => {
                let c = cx.const_val(n.a)?.to_u64()? & mask;
                if (atom_may_one(cx, n.b, 8) & !c & mask) == 0 {
                    bias = bias.wrapping_add(k.wrapping_mul(c));
                    stack.push((n.b, k.wrapping_neg(), depth - 1));
                } else {
                    parts.push((affine_leaf(cx, i, w, mask), k));
                }
            }
            _ => parts.push((affine_leaf(cx, i, w, mask), k)),
        }
    }
    parts.sort_unstable_by_key(|&(key, _)| key);
    parts.dedup_by(|next, prev| {
        if next.0 != prev.0 {
            return false;
        }
        prev.1 = prev.1.wrapping_add(next.1);
        true
    });
    parts.retain(|(_, c)| *c & mask != 0);
    for (_, c) in &mut parts {
        *c &= mask;
    }
    Some((parts, bias & mask))
}

type AffineForm = (Vec<((u32, u64), u64)>, u64);

/// Detect pairs of atoms `a, b` in `reg.atoms` that are equal (`a == b`) or bitwise complements
/// (`a + b == -1 (mod 2^w)`, i.e. `b == ~a`), either via bit-provenance across all widths
/// `1..=512` or via flattened affine forms (`x * (-C) - 1` beside `x * C`).
fn merge_complement_atoms(cx: &Context, reg: &mut Region) {
    if reg.atoms.len() < 2 {
        return;
    }
    let w = cx.wid(reg.atoms[0]);
    if w == 0 {
        return;
    }
    merge_bit_provenance_atoms(cx, reg, w);
    if reg.atoms.len() >= 2 && w <= 64 {
        merge_complement_atoms_at(cx, reg, w);
    }
    // Resolve any 2-step chains (`comp -> mid -> base`) so every `base` in `reg.complements`
    // is guaranteed to remain in `reg.atoms`.
    if reg.complements.len() >= 2 {
        let snap = reg.complements.clone();
        for entry in &mut reg.complements {
            while let Some(&(_, next_base, next_neg)) = snap.iter().find(|&&(c, _, _)| c == entry.1)
            {
                if next_base == entry.1 {
                    break;
                }
                entry.1 = next_base;
                entry.2 ^= next_neg;
            }
        }
    }
}

fn merge_bit_provenance_atoms(cx: &Context, reg: &mut Region, w: u16) {
    if reg.atoms.len() < 2 || w == 0 || w > super::shuffle::MAX_WIDTH {
        return;
    }
    if !reg.atoms.iter().all(|&a| cx.wid(a) == w) {
        return;
    }
    let runs: Vec<Option<Vec<super::shuffle::BitRun>>> = reg
        .atoms
        .iter()
        .map(|&a| super::shuffle::bit_runs_of(cx, a, 24))
        .collect();
    let mut dropped = vec![false; reg.atoms.len()];
    for j in 1..reg.atoms.len() {
        let Some(rj) = &runs[j] else { continue };
        let inv_rj = super::shuffle::runs_invert(rj);
        for i in 0..j {
            if dropped[i] {
                continue;
            }
            let Some(ri) = &runs[i] else { continue };
            if ri == rj {
                reg.complements.push((reg.atoms[j], reg.atoms[i], false));
                dropped[j] = true;
                break;
            }
            if *ri == inv_rj {
                reg.complements.push((reg.atoms[j], reg.atoms[i], true));
                dropped[j] = true;
                break;
            }
        }
    }
    if dropped.iter().any(|&d| d) {
        let mut idx = 0;
        reg.atoms.retain(|_| {
            let keep = !dropped[idx];
            idx += 1;
            keep
        });
    }
}

fn merge_complement_atoms_at(cx: &Context, reg: &mut Region, eff_w: u16) {
    if reg.atoms.len() < 2 || eff_w == 0 || eff_w > 64 {
        return;
    }
    let full_w = cx.wid(reg.atoms[0]);
    if full_w < eff_w || full_w > 64 {
        return;
    }
    if !reg.atoms.iter().any(|&a| {
        matches!(
            cx.node(a).op,
            OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Const
        )
    }) {
        return;
    }
    let mask = u64::MAX >> (64 - eff_w);
    let forms: Vec<Option<AffineForm>> = reg
        .atoms
        .iter()
        .map(|&a| {
            (cx.wid(a) == full_w)
                .then(|| flatten_affine(cx, a, eff_w))
                .flatten()
        })
        .collect();
    let mut dropped = vec![false; reg.atoms.len()];
    for j in 1..reg.atoms.len() {
        let Some((pj, bj)) = &forms[j] else { continue };
        for i in 0..j {
            if dropped[i] {
                continue;
            }
            let Some((pi, bi)) = &forms[i] else { continue };
            if pi.len() != pj.len() {
                continue;
            }
            let same = *bi == *bj && pi == pj;
            let comp = bi.wrapping_add(*bj) & mask == mask
                && pi
                    .iter()
                    .zip(pj)
                    .all(|(&(ta, ca), &(tb, cb))| ta == tb && ca.wrapping_add(cb) & mask == 0);
            if same || comp {
                reg.complements.push((reg.atoms[j], reg.atoms[i], comp));
                dropped[j] = true;
                break;
            }
        }
    }
    if !reg.complements.is_empty() {
        let mut idx = 0;
        reg.atoms.retain(|_| {
            let keep = !dropped[idx];
            idx += 1;
            keep
        });
    }
}

/// Detect any atom `u` proved equal to `a | b` for two other kept atoms `a, b` in `reg.atoms`
/// across widths `2..=512` (including `rotl(x, s) == (x << s) | (x >>u (w - s))`, bit-affine
/// masked/flipped rotations when `allow_slice_rot` is enabled, and limb concatenations
/// `concat(hi, lo) == (zext(hi) << k) | zext(lo)`). Evaluated as `a | b` in the signature
/// without spending an extra variable column.
fn merge_rot_union_atoms(cx: &Context, reg: &mut Region, allow_slice_rot: bool) {
    if reg.atoms.len() < 3 {
        return;
    }
    let w = cx.wid(reg.atoms[0]);
    if !(2..=super::shuffle::MAX_WIDTH).contains(&w) {
        return;
    }
    let has_rot_or_concat = reg.atoms.iter().any(|&a| {
        matches!(
            cx.node(a).op,
            OpCode::RotL | OpCode::RotR | OpCode::Concat | OpCode::Bswap | OpCode::BitRev
        )
    });
    if !allow_slice_rot && !has_rot_or_concat {
        return;
    }
    let runs: Vec<Option<Vec<super::shuffle::BitRun>>> = reg
        .atoms
        .iter()
        .map(|&a| {
            (cx.wid(a) == w)
                .then(|| super::shuffle::bit_runs_of(cx, a, 24))
                .flatten()
        })
        .collect();
    let mut dropped = vec![false; reg.atoms.len()];
    let mut used = vec![false; reg.atoms.len()];
    let n = reg.atoms.len();
    for u in 0..n {
        if dropped[u] || used[u] {
            continue;
        }
        if !allow_slice_rot
            && !matches!(
                cx.node(reg.atoms[u]).op,
                OpCode::RotL | OpCode::RotR | OpCode::Concat | OpCode::Bswap | OpCode::BitRev
            )
        {
            continue;
        }
        let Some(ru) = &runs[u] else { continue };
        'pair: for i in 0..n {
            if i == u || dropped[i] {
                continue;
            }
            let Some(ri) = &runs[i] else { continue };
            for j in (i + 1)..n {
                if j == u || dropped[j] {
                    continue;
                }
                let Some(rj) = &runs[j] else { continue };
                if super::shuffle::runs_is_or(ru, ri, rj) {
                    reg.rot_unions
                        .push((reg.atoms[u], reg.atoms[i], reg.atoms[j]));
                    dropped[u] = true;
                    used[i] = true;
                    used[j] = true;
                    break 'pair;
                }
            }
        }
    }
    if !reg.rot_unions.is_empty() {
        let mut idx = 0;
        reg.atoms.retain(|_| {
            let keep = !dropped[idx];
            idx += 1;
            keep
        });
    }
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
    region_with(cx, root, s, false)
}

fn region_with(cx: &Context, root: u32, s: &mut Scratch, allow_slice_rot: bool) -> Option<Region> {
    region_ext(cx, root, s, allow_slice_rot, false)
}

fn region_ext(
    cx: &Context,
    root: u32,
    s: &mut Scratch,
    allow_slice_rot: bool,
    allow_const_atoms: bool,
) -> Option<Region> {
    s.forced.begin(cx.len());
    for _ in 0..32 {
        match walk::<false>(cx, root, s, &mut 0, allow_slice_rot, allow_const_atoms) {
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
    match signature_words(cx, reg, root, s) {
        Some(row) => row
            .iter()
            .map(|&v| BitVec::wrapping_from_u64(w, v))
            .collect(),
        None => signature_wide(cx, reg, root),
    }
}

fn signature_words<'a>(
    cx: &Context,
    reg: &Region,
    root: u32,
    s: &'a mut Scratch,
) -> Option<&'a [u64]> {
    let bits = u64::from(cx.wid(root));
    if bits > 64 {
        return None;
    }
    // Every region node has the root's width: a row of words per node, masked to it.
    let mask = u64::MAX >> (64 - bits);
    let t = reg.atoms.len();
    let nc = reg.complements.len();
    let nr = reg.rot_unions.len();
    let corners = 1usize << t;
    s.seen.begin(cx.len());
    s.words.clear();
    s.words.resize((t + nc + nr + reg.order.len()) * corners, 0);
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
    for (ci, &(comp, base, negate)) in reg.complements.iter().enumerate() {
        let base_row = s.seen.get(base)?;
        let row_idx = t + ci;
        s.seen.set(comp, row_idx as u32);
        let (done, rest) = s.words.split_at_mut(row_idx * corners);
        let src = &done[base_row as usize * corners..(base_row as usize + 1) * corners];
        for (o, &x) in rest[..corners].iter_mut().zip(src) {
            *o = if negate { !x & mask } else { x & mask };
        }
    }
    for (ri, &(rot, shl, lshr)) in reg.rot_unions.iter().enumerate() {
        let r_shl = s.seen.get(shl)? as usize;
        let r_lshr = s.seen.get(lshr)? as usize;
        let row_idx = t + nc + ri;
        s.seen.set(rot, row_idx as u32);
        let (done, rest) = s.words.split_at_mut(row_idx * corners);
        let s1 = &done[r_shl * corners..(r_shl + 1) * corners];
        let s2 = &done[r_lshr * corners..(r_lshr + 1) * corners];
        for (o, (&x, &y)) in rest[..corners].iter_mut().zip(s1.iter().zip(s2)) {
            *o = (x | y) & mask;
        }
    }
    // A narrow atom reads as its lifted atom: under its cast, the nodes are evaluated at the
    // root's width over the lifted atoms (bitwise operators act by position).
    for &(a, l) in &reg.lifts {
        s.seen.set(a, s.seen.get(l)?);
    }
    for (k, &i) in reg.order.iter().enumerate() {
        let at = (t + nc + nr + k) * corners;
        s.seen.set(i, (t + nc + nr + k) as u32);
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
        let a = operand(n.a)?;
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
                let b = operand(n.b)?;
                let f: fn(u64, u64, u64) -> u64 = match op {
                    OpCode::Add => |x, y, _| x.wrapping_add(y),
                    OpCode::Sub => |x, y, _| x.wrapping_sub(y),
                    OpCode::Mul => |x, y, _| x.wrapping_mul(y),
                    OpCode::Shl => |x, y, bits| if y < bits { x << y } else { 0 },
                    OpCode::And => |x, y, _| x & y,
                    OpCode::Or => |x, y, _| x | y,
                    OpCode::Xor => |x, y, _| x ^ y,
                    _ => return None,
                };
                for (o, (&x, &y)) in out.iter_mut().zip(a.iter().zip(b)) {
                    *o = f(x, y, bits) & mask;
                }
            }
        }
    }
    let r = (t + nc + nr + reg.order.len() - 1) * corners;
    (s.seen.get(root)? as usize * corners == r).then_some(&s.words[r..r + corners])
}

/// Endpoints of a constant or one-variable signature. In particular, agreement
/// at zero and at each singleton is insufficient: a joint corner can differ.
#[cfg(feature = "mba")]
fn one_axis(sig: &[u64], vars: usize) -> Option<(u64, Option<usize>, u64)> {
    let bias = sig[0];
    let axis = (0..vars).find(|&j| sig[1 << j] != bias);
    let other = axis.map_or(bias, |j| sig[1 << j]);
    sig.iter()
        .enumerate()
        .all(|(p, &v)| {
            v == if axis.is_some_and(|j| p & (1 << j) != 0) {
                other
            } else {
                bias
            }
        })
        .then_some((bias, axis, other))
}

/// A cheap exact reading for the large-expression sweep. A linear MBA that agrees
/// with `k + c*x` on every corner *is* `k + c*x` for arbitrary word inputs. Only
/// that one-word form (or a constant) is interesting here: no basis search, no
/// lifting through casts, and no dynamic enumeration of the word inputs.
#[cfg(feature = "mba")]
pub(super) fn one_word(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    left: &mut u64,
) -> Result<Option<u32>, Stop> {
    let w = cx.wid(root);
    if w > 64 || !matches!(cx.node(root).op, OpCode::Add | OpCode::Sub) {
        return Ok(None);
    }
    let s = &mut r.linear_mba;
    s.forced.begin(cx.len());
    for _ in 0..3 {
        // walk::<true> stops at the 161st distinct node. A conflict can only
        // add another walk after the node has been fixed as a common cut.
        if *left < 161 {
            break;
        }
        let mut visits = 0;
        let region = walk::<true>(cx, root, s, &mut visits, false, false);
        *left -= visits as u64;
        let reg = match region {
            Ok(reg) => reg,
            Err(Walk::Conflict(i)) if i != root => {
                s.forced.insert(i);
                continue;
            }
            Err(_) => break,
        };
        if reg.order.len() < 2 {
            break;
        }
        let rows = 1usize << reg.atoms.len();
        let cost = ((reg.order.len() + reg.atoms.len() + 2) * rows) as u64;
        if cost > *left {
            break;
        }
        *left -= cost;
        let Some(sig) = signature_words(cx, &reg, root, s) else {
            break;
        };
        let Some((bias, axis, other)) = one_axis(sig, reg.atoms.len()) else {
            break;
        };
        let mask = u64::MAX >> (64 - w);
        let atom = axis.map(|j| reg.atoms[j]);
        return r.build(cx, |cx| {
            let k = cx.mk_const_u64(w, bias)?;
            let Some(x) = atom else { return Ok(Some(k)) };
            let coeff = bias.wrapping_sub(other) & mask;
            let out = if coeff == mask {
                cx.c_bin(BinOp::Sub, k, x)?
            } else {
                let c = cx.mk_const_u64(w, coeff)?;
                let term = cx.c_bin(BinOp::Mul, x, c)?;
                cx.c_bin(BinOp::Add, term, k)?
            };
            Ok((out != root).then_some(out))
        });
    }
    Ok(None)
}

#[cfg(all(test, feature = "mba"))]
#[test]
fn one_word_keeps_mixed_corners_in_its_proof() {
    let mut cx = Context::new();
    let opts = crate::ParseOptions::width(crate::Width::W8);
    let mut s = Scratch::default();
    for (text, fits) in [
        ("3 * (a & b) + 3 * (a & ~b) + 7", true),
        ("3 * (a & b) + 3 * (a & ~b) + (a & b) + 7", false),
    ] {
        let root = cx.parse(text, &opts).unwrap().index();
        s.forced.begin(cx.len());
        let reg = walk::<true>(&cx, root, &mut s, &mut 0, false, false)
            .ok()
            .unwrap();
        let row = signature_words(&cx, &reg, root, &mut s).unwrap();
        let answer = one_axis(row, reg.atoms.len());
        assert_eq!(answer.is_some(), fits);
        if let Some((bias, Some(axis), other)) = answer {
            assert_eq!(bias, 7);
            assert_eq!(bias.wrapping_sub(other) & 255, 3);
            assert_eq!(reg.atoms[axis], cx.parse("a", &opts).unwrap().index());
        }
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
    for &(comp, base, negate) in &reg.complements {
        let v: Vec<BitVec> = vals
            .get(&base)
            .map(|row| {
                row.iter()
                    .map(|x| {
                        if negate {
                            BitVec::un_unchecked(UnOp::Not, x)
                        } else {
                            *x
                        }
                    })
                    .collect()
            })
            .unwrap_or_default();
        vals.insert(comp, v);
    }
    for &(rot, shl, lshr) in &reg.rot_unions {
        if let (Some(r1), Some(r2)) = (vals.get(&shl), vals.get(&lshr)) {
            let v: Vec<BitVec> = r1
                .iter()
                .zip(r2)
                .map(|(x, y)| BitVec::bin_unchecked(BinOp::Or, x, y))
                .collect();
            vals.insert(rot, v);
        }
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
    /// CoBRA change-of-basis decomposition `konst + Σ k·B` over compact Boolean basis ops.
    Cobra(BitVec, Vec<(crate::cobra::BasisOp, BitVec)>),
    /// `konst + Σ k·AND_S`: per nonempty atom set (a bit mask over positions), its coefficient.
    Conjunctions(BitVec, Vec<(usize, BitVec)>),
}

/// A basis function over the region's atoms, as the pass's nodes (see `BasisOp::lower`).
fn emit_basis_op(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    op: &crate::cobra::BasisOp,
    atoms: &[u32],
) -> Result<u32, Stop> {
    op.lower(&mut Gates { r, cx, atoms })
}

/// The engine's nodes as the gates of a basis function.
struct Gates<'g, 'r, 'i> {
    r: &'g mut Runner<'r, 'i>,
    cx: &'g mut Context,
    atoms: &'g [u32],
}

impl crate::cobra::Gates for Gates<'_, '_, '_> {
    type Err = Stop;
    fn input(&mut self, i: usize) -> Result<u32, Stop> {
        Ok(self.atoms[i])
    }
    fn table(&mut self, tt8: u8, args: [u32; 3]) -> Result<u32, Stop> {
        bitwise::emit(self.r, self.cx, tt8, &args)
    }
    fn and(&mut self, a: u32, b: u32) -> Result<u32, Stop> {
        self.r.build(self.cx, |cx| cx.c_bin(BinOp::And, a, b))
    }
    fn or(&mut self, a: u32, b: u32) -> Result<u32, Stop> {
        self.r.build(self.cx, |cx| cx.c_bin(BinOp::Or, a, b))
    }
    fn not(&mut self, a: u32) -> Result<u32, Stop> {
        self.r.build(self.cx, |cx| cx.c_un(UnOp::Not, a))
    }
    fn ones(&mut self) -> Result<u32, Stop> {
        let ones = BitVec::ones(self.cx.width_of(self.atoms[0]));
        self.r.build(self.cx, |cx| cx.mk_const(&ones))
    }
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry("linear_mba").or_default()
}

/// The linear-MBA pass at `n`.
///
/// An interior link of an additive chain whose user is itself a fitting linear-MBA region is
/// left to that user: the whole sum is solved once instead of at every partial prefix. The
/// user's solve can still decline (the lifted atoms are too many, the form is no smaller),
/// and the walk does not come back to the link: the user then solves the links it held back
/// (see [`held_back`]).
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    if let Some(p) = defers(r, cx, n) {
        r.linear_mba.deferred.insert(n, p);
        return Ok(Step::Normal(Fin::PROVISIONAL));
    }
    r.linear_mba.deferred.remove(&n);
    match solve(r, cx, n, true, None)?.0 {
        Step::Normal(fin) => held_back(r, cx, n, fin),
        step => Ok(step),
    }
}

/// The user in the chain that the link `n` leaves its solve to, if any (see [`step`]).
fn defers(r: &mut Runner<'_, '_>, cx: &Context, n: u32) -> Option<u32> {
    let node = cx.node(n);
    if !matches!(node.op, OpCode::Add | OpCode::Sub) {
        return None;
    }
    let p = *r.chain_parent.get(&n)?;
    if !matches!(cx.node(p).op, OpCode::Add | OpCode::Sub | OpCode::Neg)
        || !interior(cx, p, Mode::Linear)
    {
        return None;
    }
    match region(cx, p, &mut r.linear_mba) {
        Some(pr) => {
            (pr.mixed && !pr.bounds.is_empty() && pr.bounds.len() <= MAX_ATOMS).then_some(p)
        }
        // When the parent overflows `MAX_ATOMS`, still defer mixed chain links up to the top of
        // the chain so `solve_split_orthogonal` can solve the whole sum once instead of every
        // 7/8-atom interior prefix paying `2^t` signature work (if the top declines, `held_back`
        // solves deferred links under the bounded `HELD_BACK_SHARE` budget).
        None => (r.linear_mba.deferred.contains_key(&node.a)
            || r.linear_mba.deferred.contains_key(&node.b)
            || is_bitwise(cx.node(node.a).op)
            || is_bitwise(cx.node(node.b).op))
        .then_some(p),
    }
}

/// Once `n`'s own solve declined (with `fin`): the links of its chain that left their solve to
/// it, each solved alone, down the chain (a link that declines in turn hands on to those that
/// left theirs to it). The first that is rewritten is rebuilt into `n`, as the walk would have
/// rebuilt `n` over it, and `n` is rewritten to that where it makes the DAG smaller (a link on
/// the way that something else reads stays for that reader).
fn held_back(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32, mut fin: Fin) -> Result<Step, Stop> {
    let before = cx.len() as u32;
    // Bound the total signature/decomposition work one declined chain's deferred links may spend,
    // so an irreducible wide sum does not spend O(L^2 * 2^t) pass work on every prefix link.
    // Expensive links are skipped while still descending into smaller sub-chains below them.
    let mut hb_left = (r.meter.limit.pass_work / HELD_BACK_SHARE).max(HELD_BACK_MIN);
    // The links solved, each with the index of its user here (`n` has none).
    let mut links: Vec<(u32, usize)> = vec![(n, usize::MAX)];
    let mut at = 0;
    while at < links.len() {
        let u = links[at].0;
        let node = cx.node(u);
        let kids = [node.a, node.b, node.c];
        for &c in &kids[..node.op.arity()] {
            // (Removed once solved: an operand read twice is solved once.)
            if r.linear_mba.deferred.get(&c) != Some(&u) {
                continue;
            }
            r.linear_mba.deferred.remove(&c);
            let spent_before = r.meter.spent.pass_work;
            let step = solve(r, cx, c, true, Some(hb_left))?.0;
            hb_left = hb_left.saturating_sub(r.meter.spent.pass_work - spent_before);
            match step {
                Step::Normal(f) => {
                    fin = fin.and(f);
                    links.push((c, at));
                }
                Step::To(e, _) => {
                    // `c` is `e`: so is every user up the chain, rebuilt over it.
                    let (mut old, mut new, mut i) = (c, e, at);
                    loop {
                        let (v, up) = links[i];
                        let node = cx.node(v);
                        let mut kids = [node.a, node.b, node.c];
                        for k in kids.iter_mut().take(node.op.arity()) {
                            if *k == old {
                                *k = new;
                            }
                        }
                        new = r.build(cx, |cx| cx.rebuild(v, kids))?;
                        if up == usize::MAX {
                            break;
                        }
                        (old, i) = (v, up);
                    }
                    if new == n {
                        super::discard(r, cx, before);
                        return Ok(Step::Normal(fin));
                    }
                    // What `new` reads that was there before: where the count of its nodes
                    // stops.
                    let mut stops = Vec::new();
                    let mut seen: IdMap<u32, ()> = IdMap::default();
                    let mut todo = vec![new];
                    while let Some(i) = todo.pop() {
                        if seen.insert(i, ()).is_some() {
                            continue;
                        }
                        if i < before {
                            stops.push(i);
                        } else {
                            todo.extend(cx.node(i).children());
                        }
                    }
                    let tree = |i: u32| cx.meta[i as usize].tree;
                    let tie = tree(n) != u32::MAX && tree(new) < tree(n);
                    let kind = PassKind::LinearMba;
                    return Ok(
                        match finish_with(r, cx, kind, n, new, before, &stops, Fin::FINAL, tie)? {
                            Step::Normal(f) => Step::Normal(fin.and(f)),
                            step => step,
                        },
                    );
                }
            }
        }
        at += 1;
    }
    Ok(Step::Normal(fin))
}

/// The cheapest form of the linear MBA at `n`, built whatever it costs and committed nowhere:
/// for a caller that measures the result itself. `None` when `n` is no mixed fragment.
#[cfg(feature = "prove")]
pub(super) fn normal(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<u32>, Stop> {
    Ok(solve(r, cx, n, false, None)?.1)
}

/// Whether `a` and `b` are equal for every value of the symbols because their difference is a
/// linear MBA whose signature is zero: at every corner of its atoms it is 0, so every
/// coefficient of its form is, whatever the atoms are. `false` decides nothing (the
/// difference is no mixed fragment, has too many atoms, or is not zero at some corner, which
/// atoms that depend on each other may never reach).
///
/// The two sides of such an equality are often each as small as they get (`s + t` and
/// `s | t` for disjoint `s` and `t`), so that neither is rewritten into the other and only
/// their difference shows that they are the same function.
pub(super) fn equal(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
) -> Result<bool, Stop> {
    equal_within(r, cx, a, b, MAX_ATOMS)
}

/// Like [`equal`], but only evaluates signatures up to `max_atoms` atoms (e.g., for cheap
/// speculative equivalence checks during the opaque-constant sweep).
#[cfg(feature = "mba")]
pub(super) fn equal_bounded(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
    max_atoms: usize,
) -> Result<bool, Stop> {
    equal_within(r, cx, a, b, max_atoms)
}

fn equal_within(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
    max_atoms: usize,
) -> Result<bool, Stop> {
    // What this builds (the difference, the atoms lifted to its width) is of this test
    // only: retired whatever the answer, so that it never counts as a use of the operands.
    let before = cx.len() as u32;
    let zero = difference_is_zero(r, cx, a, b, max_atoms);
    super::discard(r, cx, before);
    zero
}

/// Exact upper bound on which bits of `i` (`w <= 64`) can ever be 1 (0 bits are known zero).
fn atom_may_one(cx: &Context, i: u32, depth: u8) -> u64 {
    let n = cx.node(i);
    let w = n.width;
    if w == 0 || w > 64 {
        return u64::MAX;
    }
    let mask = u64::MAX >> (64 - w);
    if depth == 0 {
        return mask;
    }
    match n.op {
        OpCode::Const => cx.const_val(i).and_then(|v| v.to_u64()).unwrap_or(mask) & mask,
        OpCode::Shl => match cx.const_val(n.b).and_then(|v| v.to_u64()) {
            Some(s) if s >= u64::from(w) => 0,
            Some(s) => (atom_may_one(cx, n.a, depth - 1) << s) & mask,
            None => mask,
        },
        OpCode::LShr => match cx.const_val(n.b).and_then(|v| v.to_u64()) {
            Some(s) if s >= u64::from(w) => 0,
            Some(s) => atom_may_one(cx, n.a, depth - 1) >> s,
            None => mask,
        },
        OpCode::And => atom_may_one(cx, n.a, depth - 1) & atom_may_one(cx, n.b, depth - 1) & mask,
        OpCode::Or | OpCode::Xor => {
            (atom_may_one(cx, n.a, depth - 1) | atom_may_one(cx, n.b, depth - 1)) & mask
        }
        OpCode::Zext => atom_may_one(cx, n.a, depth - 1) & mask,
        OpCode::Extract if cx.wid(n.a) <= 64 => (atom_may_one(cx, n.a, depth - 1) >> n.b) & mask,
        OpCode::Select => {
            (atom_may_one(cx, n.b, depth - 1) | atom_may_one(cx, n.c, depth - 1)) & mask
        }
        OpCode::Add => {
            let ma = atom_may_one(cx, n.a, depth - 1);
            let mb = atom_may_one(cx, n.b, depth - 1);
            if (ma & mb & mask) == 0 {
                (ma | mb) & mask
            } else if let Some(c) = cx.const_val(n.a).and_then(|v| v.to_u64())
                && mb.is_power_of_two()
            {
                (c | c.wrapping_add(mb)) & mask
            } else if let Some(c) = cx.const_val(n.b).and_then(|v| v.to_u64())
                && ma.is_power_of_two()
            {
                (c | c.wrapping_add(ma)) & mask
            } else {
                mask
            }
        }
        OpCode::Sub => {
            if let Some(c) = cx.const_val(n.a).and_then(|v| v.to_u64()) {
                let mb = atom_may_one(cx, n.b, depth - 1);
                if (mb & !c & mask) == 0 {
                    c & mask
                } else if mb.is_power_of_two() {
                    (c | c.wrapping_sub(mb)) & mask
                } else {
                    mask
                }
            } else if let Some(c) = cx.const_val(n.b).and_then(|v| v.to_u64()) {
                let ma = atom_may_one(cx, n.a, depth - 1);
                if ma.is_power_of_two() {
                    (c.wrapping_neg() | ma.wrapping_sub(c)) & mask
                } else {
                    mask
                }
            } else {
                mask
            }
        }
        OpCode::Mul => {
            let (x, k) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => (n.a, k.to_u64()),
                (Some(k), None) => (n.b, k.to_u64()),
                _ => return mask,
            };
            let Some(k) = k else { return mask };
            if k == 0 {
                return 0;
            }
            let mx = atom_may_one(cx, x, depth - 1);
            if mx == 0 {
                return 0;
            }
            let tz = k.trailing_zeros() + mx.trailing_zeros();
            if tz >= u32::from(w) {
                0
            } else {
                (mask << tz) & mask
            }
        }
        _ => mask,
    }
}

/// Drop conjunction terms `d[S] * AND_S` that vanish identically because the atoms in `S` have
/// disjoint `may_one` masks (`AND_S == 0`) or trailing zeros annihilating `d[S]` (`d[S] << tz == 0`),
/// and transfer a purely linear atom `x` scaled by `k` into an existing shifted atom `y = x << s`
/// whenever `k` has at least `s` trailing zeros (`k * x == (k >> s) * (x << s)` mod `2^w`).
/// Returns whether any coefficient changed.
fn transfer_shifted_linear_atoms(cx: &Context, atoms: &[u32], d: &mut [BitVec]) -> bool {
    let t = atoms.len();
    if t == 0 {
        return false;
    }
    let w = cx.width_of(atoms[0]);
    let wb = u64::from(w.bits());
    let mut moved = false;

    // 1. Precompute sound `may_one` bitmasks (for `w <= 64`) and zero out any conjunction
    //    `AND_S` that is identically 0 or whose trailing zeros annihilate `d[S]`.
    let mut may_one = [u64::MAX; MAX_ATOMS];
    let use_masks = w.bits() <= 64;
    if use_masks {
        let full = u64::MAX >> (64 - w.bits());
        let mut any_restricted = false;
        for (j, &a) in atoms.iter().enumerate().take(MAX_ATOMS) {
            let m = atom_may_one(cx, a, 6);
            may_one[j] = m;
            any_restricted |= m != full;
        }
        if any_restricted {
            for (s, coeff) in d.iter_mut().enumerate().skip(1) {
                if coeff.is_zero() {
                    continue;
                }
                let mut cm = full;
                for (j, &mj) in may_one.iter().enumerate().take(t) {
                    if (s >> j) & 1 != 0 {
                        cm &= mj;
                    }
                }
                if cm == 0 {
                    *coeff = BitVec::zero(w);
                    moved = true;
                    continue;
                }
                let tz = cm.trailing_zeros();
                if tz > 0
                    && (u64::from(tz) >= wb
                        || BitVec::bin_unchecked(
                            BinOp::Shl,
                            coeff,
                            &BitVec::wrapping_from_u64(w, u64::from(tz)),
                        )
                        .is_zero())
                {
                    *coeff = BitVec::zero(w);
                    moved = true;
                }
            }
        }
    }

    // 2. Transfer purely linear `k * x` into an existing `y = x << s` atom when `2^s | k`.
    for i in 0..t {
        let bit_i = 1usize << i;
        if d[bit_i].is_zero() {
            continue;
        }
        // Only transfer when atom `i` has zero coefficients on all conjunctions of size >= 2.
        if (0..d.len()).any(|s| s != bit_i && (s & bit_i) != 0 && !d[s].is_zero()) {
            continue;
        }
        let x = atoms[i];
        let k = d[bit_i];
        for (j, &y) in atoms.iter().enumerate() {
            if j == i {
                continue;
            }
            let ny = cx.node(y);
            if ny.op != OpCode::Shl || ny.a != x {
                continue;
            }
            let Some(shift) = cx.const_val(ny.b).and_then(|v| v.to_u64()) else {
                continue;
            };
            if shift == 0 || shift >= wb {
                continue;
            }
            let sh = BitVec::wrapping_from_u64(w, shift);
            let q = BitVec::bin_unchecked(BinOp::LShr, &k, &sh);
            let back = BitVec::bin_unchecked(BinOp::Shl, &q, &sh);
            if back == k {
                let bit_j = 1usize << j;
                d[bit_j] = BitVec::bin_unchecked(BinOp::Add, &d[bit_j], &q);
                d[bit_i] = BitVec::zero(w);
                if BitVec::bin_unchecked(BinOp::Shl, &d[bit_j], &sh).is_zero() {
                    d[bit_j] = BitVec::zero(w);
                }
                moved = true;
                break;
            }
        }
    }
    moved
}

/// When `n = a - b` exceeds `max_atoms` because orthogonal linear terms are mixed with a
/// smaller bitwise-mixed sub-sum (`M + P`), check whether `M` collapses to an affine form
/// `c0 + Σ c_j * atom_j` over `<= max_atoms` atoms such that `c0 + Σ c_j * atom_j + P == 0`.
fn difference_is_zero_split(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    max_atoms: usize,
) -> Result<bool, Stop> {
    if !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) {
        return Ok(false);
    }
    let Some((bias, terms)) = flatten_top_linear(cx, n) else {
        return Ok(false);
    };
    let mut mixed: Vec<(u32, BitVec)> = Vec::new();
    let mut plain: Vec<(u32, BitVec)> = Vec::new();
    for (t, k) in terms {
        let tn = cx.node(t);
        let is_bw_term = match tn.op {
            OpCode::And | OpCode::Or | OpCode::Xor => interior(cx, t, Mode::Bitwise),
            OpCode::Not => is_bitwise(cx.node(tn.a).op) && interior(cx, tn.a, Mode::Bitwise),
            OpCode::Zext | OpCode::Sext => interior(cx, tn.a, Mode::Bitwise),
            _ => false,
        };
        if is_bw_term {
            mixed.push((t, k));
        } else {
            plain.push((t, k));
        }
    }
    if mixed.is_empty() || plain.is_empty() {
        return Ok(false);
    }
    let w = cx.width_of(n);
    let m_only = linear::emit(r, cx, &linear::Form::of(BitVec::zero(w), &mixed))?;
    let Some(reg) = region_with(cx, m_only, &mut r.linear_mba, true) else {
        return Ok(false);
    };
    if !reg.mixed
        || reg.bounds.is_empty()
        || !reg.lifts.is_empty()
        || reg.atoms.len() > max_atoms.min(MAX_ATOMS)
    {
        return Ok(false);
    }
    let atom_affines: Vec<Option<AffineForm>> = if w.bits() <= 64 {
        reg.atoms
            .iter()
            .map(|&a| flatten_affine(cx, a, w.bits()))
            .collect()
    } else {
        Vec::new()
    };
    let mask = if w.bits() <= 64 {
        u64::MAX >> (64 - w.bits())
    } else {
        0
    };
    let is_coupled = |a: u32| -> bool {
        if reg.atoms.contains(&a)
            || reg.bounds.contains(&a)
            || reg.complements.iter().any(|&(c, _, _)| c == a)
            || reg.rot_unions.iter().any(|&(rot, _, _)| rot == a)
        {
            return true;
        }
        if w.bits() <= 64
            && let Some((pa, ba)) = flatten_affine(cx, a, w.bits())
            && !pa.is_empty()
        {
            for af in atom_affines.iter().flatten() {
                if af.0.len() != pa.len() {
                    continue;
                }
                let same = af.1 == ba && af.0 == pa;
                let comp =
                    af.1.wrapping_add(ba) & mask == mask
                        && af.0.iter().zip(&pa).all(|(&(ta, ca), &(tb, cb))| {
                            ta == tb && ca.wrapping_add(cb) & mask == 0
                        });
                if same || comp {
                    return true;
                }
            }
        }
        false
    };
    let mut coupled: Vec<(u32, BitVec)> = Vec::new();
    let mut ortho: Vec<(u32, BitVec)> = Vec::new();
    for (a, k) in plain {
        if is_coupled(a) {
            coupled.push((a, k));
        } else {
            ortho.push((a, k));
        }
    }
    if ortho.is_empty() {
        return Ok(false);
    }
    mixed.extend(coupled);
    let m_full = linear::emit(r, cx, &linear::Form::of(bias, &mixed))?;
    let Some(reg) = region_with(cx, m_full, &mut r.linear_mba, true) else {
        return Ok(false);
    };
    let t = reg.atoms.len();
    if !reg.mixed || reg.bounds.is_empty() || !reg.lifts.is_empty() || t > max_atoms.min(MAX_ATOMS)
    {
        return Ok(false);
    }
    let sig_work = (reg.order.len() << t) as u64;
    if max_atoms < MAX_ATOMS && sig_work > 16384 {
        return Ok(false);
    }
    r.meter.charge(Counter::PassWork, sig_work)?;
    let sig = signature(cx, &reg, m_full, &mut r.linear_mba);
    let mut d = mobius(&sig);
    transfer_shifted_linear_atoms(cx, &reg.atoms, &mut d);
    if (0..d.len()).any(|s| (s as u32).count_ones() >= 2 && !d[s].is_zero()) {
        return Ok(false);
    }
    let konst = BitVec::un_unchecked(UnOp::Neg, &d[0]);
    let mut rem_terms = ortho;
    for j in 0..t {
        if !d[1 << j].is_zero() {
            rem_terms.push((reg.atoms[j], d[1 << j]));
        }
    }
    let rem = linear::emit(r, cx, &linear::Form::of(konst, &rem_terms))?;
    if cx.const_val(rem).is_some_and(|v| v.is_zero()) {
        return Ok(true);
    }
    let zero = r.build(cx, |cx| cx.mk_const(&BitVec::zero(w)))?;
    #[cfg_attr(not(feature = "mba"), allow(unused_mut))]
    let mut eq = super::poly::equal(r, cx, rem, zero)?;
    #[cfg(feature = "mba")]
    if !eq && w.bits() <= 64 {
        eq = super::mba::equal_lanes(r, cx, rem, zero, w.bits())?;
    }
    Ok(eq)
}

#[cfg(feature = "mba")]
fn difference_is_zero_const_atoms(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<bool, Stop> {
    let w = cx.width_of(n);
    if w.bits() > 64 {
        return Ok(false);
    }
    let Some(reg) = region_ext(cx, n, &mut r.linear_mba, true, true) else {
        return Ok(false);
    };
    let t = reg.atoms.len();
    if !reg.mixed || reg.bounds.is_empty() || !reg.lifts.is_empty() || t > 5 {
        return Ok(false);
    }
    let sig_work = (reg.order.len() << t) as u64;
    if sig_work > 2048 {
        return Ok(false);
    }
    r.meter.charge(Counter::PassWork, sig_work)?;
    let sig = signature(cx, &reg, n, &mut r.linear_mba);
    if sig.iter().all(BitVec::is_zero) {
        return Ok(true);
    }
    let mut d = mobius(&sig);
    transfer_shifted_linear_atoms(cx, &reg.atoms, &mut d);
    if d.iter().all(BitVec::is_zero) {
        return Ok(true);
    }
    if (0..d.len()).all(|s| (s as u32).count_ones() < 2 || d[s].is_zero()) {
        let konst = BitVec::un_unchecked(UnOp::Neg, &d[0]);
        let terms: Vec<(u32, BitVec)> = (0..t)
            .filter(|&j| !d[1 << j].is_zero())
            .map(|j| (reg.atoms[j], d[1 << j]))
            .collect();
        let rem = linear::emit(r, cx, &linear::Form::of(konst, &terms))?;
        if cx.const_val(rem).is_some_and(|v| v.is_zero()) {
            return Ok(true);
        }
        let zero = r.build(cx, |cx| cx.mk_const(&BitVec::zero(w)))?;
        if super::poly::equal(r, cx, rem, zero)? {
            return Ok(true);
        }
        #[cfg(feature = "mba")]
        if super::mba::equal_lanes(r, cx, rem, zero, w.bits())? {
            return Ok(true);
        }
    }
    Ok(false)
}

#[cfg(feature = "mba")]
pub(super) fn equal_const_atoms(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
) -> Result<bool, Stop> {
    let before = cx.len() as u32;
    let n = r.build(cx, |cx| cx.c_bin(crate::BinOp::Sub, a, b));
    let zero = match n {
        Ok(diff) => difference_is_zero_const_atoms(r, cx, diff),
        Err(e) => Err(e),
    };
    super::discard(r, cx, before);
    zero
}

fn difference_is_zero(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
    max_atoms: usize,
) -> Result<bool, Stop> {
    let n = r.build(cx, |cx| cx.c_bin(crate::BinOp::Sub, a, b))?;
    let op = cx.node(n).op;
    if !(is_linear(op) || is_bitwise(op)) || !interior(cx, n, Mode::Linear) {
        return Ok(false);
    }
    let Some(mut reg) = region_with(cx, n, &mut r.linear_mba, true) else {
        return difference_is_zero_split(r, cx, n, max_atoms);
    };
    if !reg.mixed || reg.bounds.is_empty() {
        return Ok(false);
    }
    lift(r, cx, &mut reg, cx.width_of(n).bits())?;
    let t = reg.atoms.len();
    if t > max_atoms.min(MAX_ATOMS) {
        return Ok(false);
    }
    r.meter
        .charge(Counter::PassWork, (reg.order.len() << t) as u64)?;
    let sig = signature(cx, &reg, n, &mut r.linear_mba);
    if sig.iter().all(BitVec::is_zero) {
        return Ok(true);
    }
    let mut d = mobius(&sig);
    transfer_shifted_linear_atoms(cx, &reg.atoms, &mut d);
    if d.iter().all(BitVec::is_zero) {
        return Ok(true);
    }
    // If all degree >= 2 conjunctions cancelled, the difference is purely affine over `reg.atoms`:
    // check whether that affine combination vanishes through underlying linear/polynomial relations
    // among the atoms (e.g. `-(a * C1) - (a * C2) + a * (C1 + C2) == 0`).
    if (0..d.len()).all(|s| (s as u32).count_ones() < 2 || d[s].is_zero()) {
        let w = cx.width_of(n);
        let konst = BitVec::un_unchecked(UnOp::Neg, &d[0]);
        let terms: Vec<(u32, BitVec)> = (0..t)
            .filter(|&j| !d[1 << j].is_zero())
            .map(|j| (reg.atoms[j], d[1 << j]))
            .collect();
        let rem = linear::emit(r, cx, &linear::Form::of(konst, &terms))?;
        if cx.const_val(rem).is_some_and(|v| v.is_zero()) {
            return Ok(true);
        }
        let zero = r.build(cx, |cx| cx.mk_const(&BitVec::zero(w)))?;
        if super::poly::equal(r, cx, rem, zero)? {
            return Ok(true);
        }
        #[cfg(feature = "mba")]
        if w.bits() <= 64 && super::mba::equal_lanes(r, cx, rem, zero, w.bits())? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Flatten top-level linear terms (`Add`, `Sub`, `Neg`, `Mul(_, const)`, `Shl(_, const)`) of
/// `root` into `(bias, sorted_combined_terms)`, stopping at all other operators.
fn flatten_top_linear(cx: &Context, root: u32) -> Option<(BitVec, Vec<(u32, BitVec)>)> {
    let w = cx.width_of(root);
    let wb = u64::from(w.bits());
    let mut bias = BitVec::zero(w);
    let mut terms: Vec<(u32, BitVec)> = Vec::new();
    let mut stack: Vec<(u32, BitVec, u8)> = vec![(root, BitVec::one(w), 64)];
    let mut steps = 0usize;
    while let Some((i, k, depth)) = stack.pop() {
        steps += 1;
        if steps > 256 || terms.len() > 96 {
            return None;
        }
        if k.is_zero() {
            continue;
        }
        let n = cx.node(i);
        if depth == 0 {
            terms.push((i, k));
            continue;
        }
        if let Some(c) = cx.const_val(i) {
            let prod = BitVec::bin_unchecked(BinOp::Mul, &k, &c);
            bias = BitVec::bin_unchecked(BinOp::Add, &bias, &prod);
            continue;
        }
        match n.op {
            OpCode::Add => {
                stack.push((n.a, k, depth - 1));
                stack.push((n.b, k, depth - 1));
            }
            OpCode::Sub => {
                let nk = BitVec::un_unchecked(UnOp::Neg, &k);
                stack.push((n.a, k, depth - 1));
                stack.push((n.b, nk, depth - 1));
            }
            OpCode::Neg => {
                let nk = BitVec::un_unchecked(UnOp::Neg, &k);
                stack.push((n.a, nk, depth - 1));
            }
            OpCode::Mul if cx.const_val(n.b).is_some() => {
                let c = cx.const_val(n.b)?;
                let nk = BitVec::bin_unchecked(BinOp::Mul, &k, &c);
                stack.push((n.a, nk, depth - 1));
            }
            OpCode::Mul if cx.const_val(n.a).is_some() => {
                let c = cx.const_val(n.a)?;
                let nk = BitVec::bin_unchecked(BinOp::Mul, &k, &c);
                stack.push((n.b, nk, depth - 1));
            }
            OpCode::Shl if cx.const_val(n.b).and_then(|v| v.to_u64()).is_some() => {
                let s = cx.const_val(n.b)?.to_u64()?;
                if s < wb {
                    let sh = BitVec::wrapping_from_u64(w, s);
                    let nk = BitVec::bin_unchecked(BinOp::Shl, &k, &sh);
                    stack.push((n.a, nk, depth - 1));
                }
            }
            _ => terms.push((i, k)),
        }
    }
    terms.sort_unstable_by_key(|&(id, _)| id);
    terms.dedup_by(|next, prev| {
        if next.0 != prev.0 {
            return false;
        }
        prev.1 = BitVec::bin_unchecked(BinOp::Add, &prev.1, &next.1);
        true
    });
    terms.retain(|(_, c)| !c.is_zero());
    Some((bias, terms))
}

/// Emit a chosen [`Candidate`] over `atoms` (in canonical order) as a node in `cx`.
fn emit_candidate(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    atoms: &[u32],
    cand: Candidate,
) -> Result<u32, Stop> {
    let form = match cand {
        Candidate::Affine(konst, terms) => {
            let terms: Vec<(u32, BitVec)> = terms.iter().map(|(j, k)| (atoms[*j], *k)).collect();
            linear::Form::of(konst, &terms)
        }
        Candidate::Indicators(u0, ind) => {
            let mut terms = Vec::new();
            for (k, tt) in ind {
                let g = bitwise::emit(r, cx, tt, atoms)?;
                terms.push((g, k));
            }
            linear::Form::of(u0, &terms)
        }
        Candidate::Cobra(konst, ops) => {
            let mut terms = Vec::with_capacity(ops.len());
            for (op, k) in ops {
                let g = emit_basis_op(r, cx, &op, atoms)?;
                terms.push((g, k));
            }
            linear::Form::of(konst, &terms)
        }
        Candidate::Conjunctions(konst, sets) => {
            let mut terms = Vec::new();
            for (set, k) in sets {
                let mut acc: Option<u32> = None;
                for (j, &a) in atoms.iter().enumerate() {
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
    linear::emit(r, cx, &form)
}

/// Evaluate `n`'s linear-MBA signature (assuming no narrow casts to lift) and pick the cheapest
/// [`Candidate`] purely as data without committing or leaving nodes alive.
type PlainCandidate = (Vec<u32>, Vec<u32>, Candidate);

fn best_candidate_plain(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    max_sig_work: Option<u64>,
) -> Result<Option<PlainCandidate>, Stop> {
    let op = cx.node(n).op;
    if !(is_linear(op) || is_bitwise(op)) || !interior(cx, n, Mode::Linear) {
        return Ok(None);
    }
    let Some(reg) = region(cx, n, &mut r.linear_mba) else {
        return Ok(None);
    };
    if !reg.mixed || reg.bounds.is_empty() || !reg.lifts.is_empty() || reg.atoms.len() > MAX_ATOMS {
        return Ok(None);
    }
    let t = reg.atoms.len();
    let sig_work = (reg.order.len() << t) as u64;
    if max_sig_work.is_some_and(|cap| sig_work > cap) {
        return Ok(None);
    }
    let w = cx.width_of(n);
    r.meter.charge(Counter::PassWork, sig_work)?;
    let sig = signature(cx, &reg, n, &mut r.linear_mba);
    let mut d = mobius(&sig);
    let shifted_atoms = transfer_shifted_linear_atoms(cx, &reg.atoms, &mut d);
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
        if r.inner.strategy.basis_sums && t >= 3 {
            let share = (r.meter.limit.pass_work / COBRA_SHARE).max(1);
            let allow = r.meter.left_in(|b| b.pass_work).min(share);
            let mut left = allow;
            let cobra = crate::cobra::decompose(t, w, u32::from(w.bits()), &d, &mut left);
            let spent = if cobra.is_err() { allow } else { allow - left };
            r.meter.charge(Counter::PassWork, spent)?;
            if let Ok(Some(cobra_terms)) = cobra {
                let gates: u32 = cobra_terms.iter().map(|(op, _)| op.gate_cost()).sum();
                let ph: Vec<(u32, BitVec)> = cobra_terms
                    .iter()
                    .enumerate()
                    .map(|(idx, (_, c))| (u32::MAX - idx as u32, *c))
                    .collect();
                let est = gates + linear::estimate(&linear::Form::of(konst, &ph));
                cands.push((est, Candidate::Cobra(konst, cobra_terms)));
            }
        }
    }
    if t <= 3 && !shifted_atoms {
        let mut distinct: Vec<BitVec> = Vec::new();
        for v in &sig {
            if !distinct.contains(v) {
                distinct.push(*v);
            }
        }
        for &u0 in &distinct {
            let mut ind: Vec<(BitVec, u8)> = Vec::new();
            let mut funcs = 0u32;
            let mut placeholder: Vec<(u32, BitVec)> = Vec::new();
            for &uk in distinct.iter().filter(|&&u| u != u0) {
                let mut tt = 0u8;
                for i in 0..8usize {
                    if sig[i & ((1 << t) - 1)] == uk {
                        tt |= 1 << i;
                    }
                }
                funcs += bitwise::min_forms().forms[tt as usize]
                    .0
                    .iter()
                    .filter(|t| !matches!(t, bitwise::T::Var(_)))
                    .count() as u32;
                let k = BitVec::bin_unchecked(BinOp::Sub, &u0, &uk);
                placeholder.push((u32::MAX - placeholder.len() as u32, k));
                ind.push((k, tt));
            }
            let est = funcs + linear::estimate(&linear::Form::of(u0, &placeholder));
            cands.push((est, Candidate::Indicators(u0, ind)));
        }
    }
    cands.sort_by_key(|c| c.0);
    let Some((_, cand)) = cands.into_iter().next() else {
        return Ok(None);
    };
    Ok(Some((reg.atoms, reg.bounds, cand)))
}

/// When an additive sum exceeds [`MAX_ATOMS`] because purely linear terms are added alongside a
/// bitwise-mixed MBA sub-sum (`M + P`), solve `M` (together with any linear terms coupled to
/// `M`'s atoms) over `M`'s smaller atom set and add the orthogonal linear terms `P` back.
fn solve_split_orthogonal(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    max_sig_work: Option<u64>,
    max_atoms_cap: usize,
) -> Result<Option<Step>, Stop> {
    if !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) {
        return Ok(None);
    }
    // Only split at the top of an additive chain so intermediate prefix links of a wide sum
    // do not repeat the same partial-region work O(L) times.
    if r.chain_parent
        .get(&n)
        .is_some_and(|&p| matches!(cx.node(p).op, OpCode::Add | OpCode::Sub | OpCode::Neg))
    {
        return Ok(None);
    }
    let Some((bias, terms)) = flatten_top_linear(cx, n) else {
        return Ok(None);
    };
    let mut mixed: Vec<(u32, BitVec)> = Vec::new();
    let mut plain: Vec<(u32, BitVec)> = Vec::new();
    for (t, k) in terms {
        let tn = cx.node(t);
        let is_bw_term = match tn.op {
            OpCode::And | OpCode::Or | OpCode::Xor => interior(cx, t, Mode::Bitwise),
            OpCode::Not => is_bitwise(cx.node(tn.a).op) && interior(cx, tn.a, Mode::Bitwise),
            OpCode::Zext | OpCode::Sext => interior(cx, tn.a, Mode::Bitwise),
            _ => false,
        };
        if is_bw_term {
            mixed.push((t, k));
        } else {
            plain.push((t, k));
        }
    }
    if mixed.len() < 3 || plain.is_empty() {
        return Ok(None);
    }
    // Probe the mixed sub-sum's region, then immediately retire the temporary sum so live
    // reference counts on `n`'s children stay untouched for `finish_with`.
    let w = cx.width_of(n);
    let before_probe = cx.len() as u32;
    let m_only = linear::emit(r, cx, &linear::Form::of(BitVec::zero(w), &mixed))?;
    let probe = region(cx, m_only, &mut r.linear_mba);
    super::discard(r, cx, before_probe);
    let Some(reg) = probe else {
        return Ok(None);
    };
    if !reg.mixed
        || reg.bounds.is_empty()
        || !reg.lifts.is_empty()
        || reg.atoms.len() > max_atoms_cap.min(MAX_ATOMS)
    {
        return Ok(None);
    }
    // Check which `plain` terms share an atom (or complement) with `m_only`.
    let atom_affines: Vec<Option<AffineForm>> = if w.bits() <= 64 {
        reg.atoms
            .iter()
            .map(|&a| flatten_affine(cx, a, w.bits()))
            .collect()
    } else {
        Vec::new()
    };
    let mask = if w.bits() <= 64 {
        u64::MAX >> (64 - w.bits())
    } else {
        0
    };
    let is_coupled = |a: u32| -> bool {
        if reg.atoms.contains(&a)
            || reg.bounds.contains(&a)
            || reg.complements.iter().any(|&(c, _, _)| c == a)
            || reg.rot_unions.iter().any(|&(rot, _, _)| rot == a)
        {
            return true;
        }
        if w.bits() <= 64
            && let Some((pa, ba)) = flatten_affine(cx, a, w.bits())
            && !pa.is_empty()
        {
            for af in atom_affines.iter().flatten() {
                if af.0.len() != pa.len() {
                    continue;
                }
                let same = af.1 == ba && af.0 == pa;
                let comp =
                    af.1.wrapping_add(ba) & mask == mask
                        && af.0.iter().zip(&pa).all(|(&(ta, ca), &(tb, cb))| {
                            ta == tb && ca.wrapping_add(cb) & mask == 0
                        });
                if same || comp {
                    return true;
                }
            }
        }
        false
    };
    let mut coupled: Vec<(u32, BitVec)> = Vec::new();
    let mut ortho: Vec<(u32, BitVec)> = Vec::new();
    for (a, k) in plain {
        if is_coupled(a) {
            coupled.push((a, k));
        } else {
            ortho.push((a, k));
        }
    }
    if ortho.is_empty() {
        return Ok(None);
    }
    mixed.extend(coupled);
    // Compute the simplified candidate over `m_full`, then immediately retire `m_full` before
    // emitting the final rewritten node so `dying_in(n)` sees true refcounts on `n`'s children.
    let before_m = cx.len() as u32;
    let m_full = linear::emit(r, cx, &linear::Form::of(bias, &mixed))?;
    let solved = best_candidate_plain(r, cx, m_full, max_sig_work);
    super::discard(r, cx, before_m);
    let Some((atoms, mut stops, cand)) = solved? else {
        return Ok(None);
    };
    let before = cx.len() as u32;
    let m_simp = emit_candidate(r, cx, &atoms, cand)?;
    let mut combined = Vec::with_capacity(ortho.len() + 1);
    combined.push((m_simp, BitVec::one(w)));
    combined.extend(ortho.iter().copied());
    let e = linear::emit(r, cx, &linear::Form::of(BitVec::zero(w), &combined))?;
    for &(a, _) in &ortho {
        if !stops.contains(&a) {
            stops.push(a);
        }
    }
    let step = finish_with(
        r,
        cx,
        PassKind::LinearMba,
        n,
        e,
        before,
        &stops,
        Fin::FINAL,
        false,
    )?;
    Ok(Some(step))
}

/// Exact partition-masked linear MBA solver over `1..=512`-bit words.
///
/// For a top-level linear combination `bias + Σ a_j · f_j(x_1, …, x_t; m_1, …, m_r)` where
/// `1 <= t <= 4` non-constant atoms and arbitrary constant masks `m_k` appear inside bitwise
/// terms `f_j`, refine the bit positions into pairwise disjoint partition masks `P_1, …, P_q`
/// (`q <= 16`) on which every `m_k` is uniform. On each `P_p`, every `f_j & P_p` has an exact
/// Möbius expansion `Σ_S β_{j,p,S} · (AND_S(x) & P_p)`. When all degree `>= 2` coefficients
/// vanish modulo `2^(W - tz(P_p))` and each variable's degree-1 coefficient agrees across every
/// partition modulo `2^(W - tz(P_p))`, the entire sum collapses exactly to a constant or affine
/// form without calling the heavier `Phase::Mba` solver.
fn solve_masked_linear_mba(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<Step>, Stop> {
    if !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) {
        return Ok(None);
    }
    if r.chain_parent
        .get(&n)
        .is_some_and(|&p| matches!(cx.node(p).op, OpCode::Add | OpCode::Sub | OpCode::Neg))
    {
        return Ok(None);
    }
    let Some((const_part, affine_terms, vars, _)) = masked_linear_form(r, cx, n, cx.wid(n))? else {
        return Ok(None);
    };
    let before = cx.len() as u32;
    let e = linear::emit(r, cx, &linear::Form::of(const_part, &affine_terms))?;
    if e == n {
        super::discard(r, cx, before);
        return Ok(None);
    }
    let step = finish_with(
        r,
        cx,
        PassKind::LinearMba,
        n,
        e,
        before,
        &vars,
        Fin::FINAL,
        false,
    )?;
    Ok(Some(step))
}

/// [`masked_linear_form`]'s answer: the constant, the affine terms, the atoms, and how many
/// terms the sum had.
type MaskedForm = (BitVec, Vec<(u32, BitVec)>, Vec<u32>, usize);

/// The constant-or-affine form [`solve_masked_linear_mba`] reads off the sum `n`, valid on its
/// low `k` bits (`k == width` for exact equality): `(constant, [(atom, coefficient)], atoms)`.
/// Constant masks are read on their low `k` bits only, so a sum whose constants the demanded
/// pass narrowed to a prefix still partitions into a few uniform classes there.
fn masked_linear_form(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    k: u16,
) -> Result<Option<MaskedForm>, Stop> {
    const MAX_MASKED_VARS: usize = 4;
    const MAX_MASKED_PARTS: usize = 16;
    const MAX_MASKED_NODES: usize = 256;

    if !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub) || k == 0 || k > cx.wid(n) {
        return Ok(None);
    }
    let Some((bias, terms)) = flatten_top_linear(cx, n) else {
        return Ok(None);
    };
    if terms.len() < 2 {
        return Ok(None);
    }

    let w = cx.width_of(n);
    let wb = w.bits();
    let low = if k >= wb {
        BitVec::ones(w)
    } else {
        let sh = BitVec::wrapping_from_u64(w, u64::from(wb - k));
        BitVec::bin_unchecked(BinOp::LShr, &BitVec::ones(w), &sh)
    };
    let mut order: Vec<u32> = Vec::new();
    let mut slot_of: IdMap<u32, usize> = IdMap::default();
    let mut vars: Vec<u32> = Vec::new();
    let mut masks: Vec<BitVec> = Vec::new();
    let mut stack: Vec<(u32, bool)> = Vec::new();
    for &(t_id, _) in &terms {
        stack.push((t_id, false));
    }
    while let Some((id, expanded)) = stack.pop() {
        if expanded {
            let idx = order.len();
            if let std::collections::hash_map::Entry::Vacant(slot) = slot_of.entry(id) {
                slot.insert(idx);
                order.push(id);
            }
            continue;
        }
        if slot_of.contains_key(&id) {
            continue;
        }
        if order.len() + stack.len() > MAX_MASKED_NODES {
            return Ok(None);
        }
        if let Some(v) = cx.const_val(id) {
            let v = BitVec::bin_unchecked(BinOp::And, &v, &low);
            if !v.is_zero() && v != low && !masks.contains(&v) {
                if masks.len() >= MAX_MASKED_PARTS {
                    return Ok(None);
                }
                masks.push(v);
            }
            let idx = order.len();
            slot_of.insert(id, idx);
            order.push(id);
            continue;
        }
        let node = cx.node(id);
        if is_bitwise(node.op) {
            stack.push((id, true));
            for c in node.children() {
                stack.push((c, false));
            }
        } else {
            if !vars.contains(&id) {
                if vars.len() >= MAX_MASKED_VARS {
                    return Ok(None);
                }
                vars.push(id);
            }
            let idx = order.len();
            slot_of.insert(id, idx);
            order.push(id);
        }
    }
    if vars.is_empty() || masks.is_empty() {
        return Ok(None);
    }

    let mut parts: Vec<BitVec> = vec![BitVec::ones(w)];
    for m in &masks {
        let nm = BitVec::un_unchecked(UnOp::Not, m);
        let mut next = Vec::with_capacity(parts.len() * 2);
        for p in &parts {
            let lo = BitVec::bin_unchecked(BinOp::And, p, m);
            if !lo.is_zero() {
                next.push(lo);
            }
            let hi = BitVec::bin_unchecked(BinOp::And, p, &nm);
            if !hi.is_zero() {
                next.push(hi);
            }
            if next.len() > MAX_MASKED_PARTS {
                return Ok(None);
            }
        }
        parts = next;
    }
    let rep_bits: Vec<u16> = parts
        .iter()
        .map(|p| (0..wb).find(|&b| p.bit(b) == Some(true)).unwrap_or(0))
        .collect();

    let t = vars.len();
    let corners = 1usize << t;
    let work = ((order.len() + terms.len() + parts.len()) << t) as u64;
    r.meter.charge(Counter::PassWork, work)?;

    let zero = BitVec::zero(w);
    let ones = BitVec::ones(w);
    let mut vals: Vec<BitVec> = vec![zero; order.len() * corners];
    for (idx, &id) in order.iter().enumerate() {
        let base = idx * corners;
        if let Some(v) = cx.const_val(id) {
            vals[base..base + corners].fill(v);
            continue;
        }
        let node = cx.node(id);
        if is_bitwise(node.op) {
            let a_base = slot_of[&node.a] * corners;
            match node.op {
                OpCode::Not => {
                    for c in 0..corners {
                        vals[base + c] = BitVec::un_unchecked(UnOp::Not, &vals[a_base + c]);
                    }
                }
                OpCode::And | OpCode::Or | OpCode::Xor => {
                    let bin = match node.op {
                        OpCode::And => BinOp::And,
                        OpCode::Or => BinOp::Or,
                        _ => BinOp::Xor,
                    };
                    let b_base = slot_of[&node.b] * corners;
                    for c in 0..corners {
                        vals[base + c] =
                            BitVec::bin_unchecked(bin, &vals[a_base + c], &vals[b_base + c]);
                    }
                }
                _ => unreachable!(),
            }
        } else {
            let j = vars.iter().position(|&v| v == id).unwrap();
            for c in 0..corners {
                vals[base + c] = if (c >> j) & 1 == 1 { ones } else { zero };
            }
        }
    }

    let mut acc: Vec<BitVec> = vec![zero; parts.len() * corners];
    for &(t_id, coeff) in &terms {
        let t_base = slot_of[&t_id] * corners;
        for (p, &rep_bit) in rep_bits.iter().enumerate() {
            let mut mu = [0i32; 16];
            for c in 0..corners {
                mu[c] = i32::from(vals[t_base + c].bit(rep_bit) == Some(true));
            }
            for bit in 0..t {
                let step = 1usize << bit;
                for s in 0..corners {
                    if s & step != 0 {
                        mu[s] -= mu[s ^ step];
                    }
                }
            }
            let p_base = p * corners;
            for (s, &m_i) in mu.iter().enumerate().take(corners) {
                if m_i == 0 {
                    continue;
                }
                let m_bv = if m_i > 0 {
                    BitVec::wrapping_from_u64(w, m_i as u64)
                } else {
                    let pos = BitVec::wrapping_from_u64(w, (-m_i) as u64);
                    BitVec::un_unchecked(UnOp::Neg, &pos)
                };
                let delta = BitVec::bin_unchecked(BinOp::Mul, &coeff, &m_bv);
                acc[p_base + s] = BitVec::bin_unchecked(BinOp::Add, &acc[p_base + s], &delta);
            }
        }
    }

    // `c · 2^tz ≡ 0 (mod 2^k)`.
    let vanishes = |c: &BitVec, tz: u16| -> bool {
        let shift = u32::from(tz) + u32::from(wb - k);
        if shift >= u32::from(wb) {
            true
        } else if shift == 0 {
            c.is_zero()
        } else {
            let sh = BitVec::wrapping_from_u64(w, u64::from(shift));
            BitVec::bin_unchecked(BinOp::Shl, c, &sh).is_zero()
        }
    };
    for (p, &tz) in rep_bits.iter().enumerate() {
        let p_base = p * corners;
        for s in 1..corners {
            if (s as u32).count_ones() >= 2 && !vanishes(&acc[p_base + s], tz) {
                return Ok(None);
            }
        }
    }

    // Partition covering bit 0 has `rep_bits[p0] == 0` (exact mod 2^W).
    let p0 = rep_bits.iter().position(|&b| b == 0).unwrap_or(0);
    let mut affine_terms: Vec<(u32, BitVec)> = Vec::new();
    for (j, &var) in vars.iter().enumerate() {
        let s = 1usize << j;
        let k_j = acc[p0 * corners + s];
        for (p, &tz) in rep_bits.iter().enumerate() {
            let diff = BitVec::bin_unchecked(BinOp::Sub, &acc[p * corners + s], &k_j);
            if !vanishes(&diff, tz) {
                return Ok(None);
            }
        }
        if !k_j.is_zero() {
            affine_terms.push((var, k_j));
        }
    }

    let mut const_part = bias;
    for (p, mask) in parts.iter().enumerate() {
        let c0 = &acc[p * corners];
        if !c0.is_zero() {
            let term = BitVec::bin_unchecked(BinOp::Mul, c0, mask);
            const_part = BitVec::bin_unchecked(BinOp::Add, &const_part, &term);
        }
    }

    Ok(Some((const_part, affine_terms, vars, terms.len())))
}

/// [`step`] when `commit`; else the form alone ([`normal`]).
/// When `max_sig_work` is `Some(cap)`, skip evaluating signatures whose cost exceeds `cap`.
fn solve(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    commit: bool,
    max_sig_work: Option<u64>,
) -> Result<(Step, Option<u32>), Stop> {
    let op = cx.node(n).op;
    if !(is_linear(op) || is_bitwise(op)) || !interior(cx, n, Mode::Linear) {
        return Ok((Step::Normal(Fin::FINAL), None));
    }
    if commit && let Some((bounds, most)) = r.linear_mba.declined.get(&n).cloned() {
        if let Some(f) = worth_building(r, cx, n, &bounds, most)? {
            count(r).rejected_cost += 1;
            return Ok((Step::Normal(f), None));
        }
        r.linear_mba.declined.remove(&n);
    }
    let Some(mut reg) = region(cx, n, &mut r.linear_mba) else {
        if commit && let Some(step @ Step::To(..)) = solve_masked_linear_mba(r, cx, n)? {
            return Ok((step, None));
        }
        if commit && let Some(step) = solve_split_orthogonal(r, cx, n, max_sig_work, MAX_ATOMS)? {
            return Ok((step, None));
        }
        count(r).atomized += 1;
        return Ok((Step::Normal(Fin::FINAL), None));
    };
    // Pure linear or pure bitwise regions belong to those passes (unless a top-level sum hides
    // constant-masked bitwise terms that `region` stopped at).
    if !reg.mixed || reg.bounds.is_empty() {
        if commit && let Some(step @ Step::To(..)) = solve_masked_linear_mba(r, cx, n)? {
            return Ok((step, None));
        }
        return Ok((Step::Normal(Fin::FINAL), None));
    }
    let w = cx.width_of(n);
    // The lifted atoms are built now: `before` lets a rejection discard them.
    let before = cx.len() as u32;
    lift(r, cx, &mut reg, w.bits())?;
    let t = reg.atoms.len();
    if t > MAX_ATOMS {
        super::discard(r, cx, before);
        count(r).atomized += 1;
        return Ok((Step::Normal(Fin::FINAL), None));
    }
    // For wide sums (`t >= 6`) with orthogonal plain linear terms, splitting off the orthogonal
    // terms first avoids evaluating `2^t` corners (and running CoBRA over `t` atoms) when the
    // bitwise-mixed sub-sum lives over strictly fewer atoms.
    if commit
        && t >= 5
        && reg.lifts.is_empty()
        && let Some(step @ Step::To(..)) = solve_split_orthogonal(r, cx, n, max_sig_work, t - 1)?
    {
        return Ok((step, None));
    }
    let sig_work = (reg.order.len() << t) as u64;
    if max_sig_work.is_some_and(|cap| sig_work > cap) {
        super::discard(r, cx, before);
        return Ok((Step::Normal(Fin::FINAL), None));
    }
    let lifted = reg.lifts.len() as u32;
    r.meter.charge(Counter::PassWork, sig_work)?;
    let sig = signature(cx, &reg, n, &mut r.linear_mba);
    let mut d = mobius(&sig);
    let shifted_atoms = transfer_shifted_linear_atoms(cx, &reg.atoms, &mut d);
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
    let mut cobra_short = false;
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

        // A form over the atoms the sum depends on has an operator fewer than there are of
        // them, at least: where replacing `n` frees no more than that, no form over the basis
        // commits, and the decomposition (the most this pass reads) is not looked for.
        let depends = (0..t)
            .filter(|&j| (1..d.len()).any(|s| s >> j & 1 == 1 && !d[s].is_zero()))
            .count() as u32;
        let least = (depends.saturating_sub(1) + lifted).saturating_sub(1);
        // (What the decomposition reads is pass work, within a share of the call's and what
        // is left of it: one that runs out of its share is no candidate, and the call goes
        // on. A chain's top that declines hands every link below it a decomposition of its
        // own.)
        let cobra = if r.inner.strategy.basis_sums
            && t >= 3
            && (!commit || super::can_pay(r, cx, n, &reg.bounds, least)?)
        {
            let share = (r.meter.limit.pass_work / COBRA_SHARE).max(1);
            let allow = r.meter.left_in(|b| b.pass_work).min(share);
            let mut left = allow;
            let terms = crate::cobra::decompose(t, w, u32::from(w.bits()), &d, &mut left);
            // An attempt cut short costs this pass its whole share.
            let spent = if terms.is_err() {
                if allow < share {
                    cobra_short = true;
                }
                allow
            } else {
                allow - left
            };
            r.meter.charge(Counter::PassWork, spent)?;
            terms.ok().flatten()
        } else {
            None
        };
        if let Some(cobra_terms) = cobra {
            let push_cobra =
                |cands: &mut Vec<(u32, Candidate)>,
                 k0: BitVec,
                 ts: Vec<(crate::cobra::BasisOp, BitVec)>| {
                    let gates: u32 = ts.iter().map(|(op, _)| op.gate_cost()).sum();
                    let ph: Vec<(u32, BitVec)> = ts
                        .iter()
                        .enumerate()
                        .map(|(idx, (_, c))| (u32::MAX - idx as u32, *c))
                        .collect();
                    let est = gates + linear::estimate(&linear::Form::of(k0, &ph));
                    cands.push((est, Candidate::Cobra(k0, ts)));
                };
            if !konst.is_zero() {
                let mut k_traded = konst;
                let mut t_traded = cobra_terms.clone();
                crate::cobra::trade_unmasked_constant(&mut k_traded, &mut t_traded);
                if k_traded.is_zero() {
                    push_cobra(&mut cands, k_traded, t_traded);
                }
            }
            push_cobra(&mut cands, konst, cobra_terms);
        }
    }
    if t <= 3 && !shifted_atoms {
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
    // (A form that only ties may still commit below: one node fewer is asked of it here.)
    let most = (est + lifted).saturating_sub(1);
    if commit && let Some(f) = worth_building(r, cx, n, &reg.bounds, most)? {
        count(r).rejected_cost += 1;
        if !cobra_short {
            r.linear_mba.declined.insert(n, (reg.bounds, most));
        }
        super::discard(r, cx, before);
        return Ok((Step::Normal(f), None));
    }
    let kind = match &cand {
        Candidate::Affine(..) => "affine",
        Candidate::Indicators(..) => "indicators",
        Candidate::Cobra(..) => "cobra",
        Candidate::Conjunctions(..) => "conjunctions",
    };
    let mut extra_stops: Vec<u32> = Vec::new();
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
        Candidate::Cobra(konst, ops) => {
            let mut terms = Vec::with_capacity(ops.len());
            for (op, k) in ops {
                let g = emit_basis_op(r, cx, &op, &reg.atoms)?;
                terms.push((g, k));
            }
            linear::Form::of(konst, &terms)
        }
        Candidate::Conjunctions(konst, sets) => {
            // Recombine disjoint shift pairs `(AND_S & shl) + (AND_S & lshr) == AND_S & rot`
            // whenever `reg.rot_unions` recorded `(rot, shl, lshr)` and both halves share the same
            // coefficient `k`.
            let rot_bits: Vec<(u32, usize, usize)> = reg
                .rot_unions
                .iter()
                .filter_map(|&(rot, shl, lshr)| {
                    let i = reg.atoms.iter().position(|&a| a == shl)?;
                    let j = reg.atoms.iter().position(|&a| a == lshr)?;
                    Some((rot, 1usize << i, 1usize << j))
                })
                .collect();
            let mut used = vec![false; sets.len()];
            let mut terms = Vec::new();
            for idx in 0..sets.len() {
                if used[idx] {
                    continue;
                }
                let (set, k) = sets[idx];
                let mut recombined = None;
                for &(rot, b1, b2) in &rot_bits {
                    let partner_opt = if (set & b1) != 0 && (set & b2) == 0 {
                        Some((set ^ b1, (set ^ b1) | b2))
                    } else if (set & b2) != 0 && (set & b1) == 0 {
                        Some((set ^ b2, (set ^ b2) | b1))
                    } else {
                        None
                    };
                    if let Some((base, partner)) = partner_opt
                        && let Some(j) = sets.iter().enumerate().position(|(j, &(s2, k2))| {
                            j > idx && !used[j] && s2 == partner && k2 == k
                        })
                    {
                        used[j] = true;
                        recombined = Some((base, rot));
                        if !extra_stops.contains(&rot) {
                            extra_stops.push(rot);
                        }
                        break;
                    }
                }
                let mut acc: Option<u32> = None;
                let (mask_bits, extra) = match recombined {
                    Some((base, rot)) => (base, Some(rot)),
                    None => (set, None),
                };
                for (j, &a) in reg.atoms.iter().enumerate() {
                    if mask_bits & (1 << j) != 0 {
                        acc = Some(match acc {
                            None => a,
                            Some(x) => r.build(cx, |cx| cx.c_bin(BinOp::And, x, a))?,
                        });
                    }
                }
                if let Some(rot) = extra {
                    acc = Some(match acc {
                        None => rot,
                        Some(x) => r.build(cx, |cx| cx.c_bin(BinOp::And, x, rot))?,
                    });
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
    // The form is the cheapest of its kind and nothing writes it back as the sum it was, so
    // it also commits where the DAG only ties and the tree gets smaller: `a + b - 2(a & b)`
    // whose `a + b` and `a & b` something else reads (the carries of limb arithmetic) frees
    // one node for the `a ^ b` it becomes, and every sum built on it then reads an XOR.
    let tree = |i: u32| cx.meta[i as usize].tree;
    let tie = tree(n) != u32::MAX && tree(e) < tree(n);
    let mut stops = reg.bounds;
    stops.extend(extra_stops);
    let step = finish_with(
        r,
        cx,
        PassKind::LinearMba,
        n,
        e,
        before,
        &stops,
        Fin::FINAL,
        tie,
    )?;
    Ok((step, None))
}

/// Simplifies causal linear-MBA sum `n` (`width <= 64`) modulo `2^k` (`1 <= k < width`),
/// returning an expression at `n`'s width that agrees identically with `n` on the low `k` bits
/// whenever the modulo-`2^k` normal form strictly shrinks `n`'s interior operator count.
pub(super) fn simplify_prefix(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    k: u16,
    exact_prefix: bool,
) -> Result<Option<u32>, Stop> {
    let w_bits = cx.wid(n);
    if k == 0
        || k >= w_bits
        || w_bits > 64
        || !matches!(cx.node(n).op, OpCode::Add | OpCode::Sub)
        || !interior(cx, n, Mode::Linear)
    {
        return Ok(None);
    }
    let Some(mut reg) = region(cx, n, &mut r.linear_mba) else {
        // Too many atoms for a signature: constant masks the demanded pass narrowed to the
        // prefix may still split the bits into a few uniform classes (see
        // [`masked_linear_form`]), where the sum is a constant or affine form on the prefix.
        if let Some((konst, terms, _, original)) = masked_linear_form(r, cx, n, k)?
            && terms.len() < original
        {
            let e = linear::emit(r, cx, &linear::Form::of(konst, &terms))?;
            return Ok((e != n).then_some(e));
        }
        return Ok(None);
    };
    if !reg.mixed || !reg.lifts.is_empty() || reg.atoms.is_empty() || reg.order.len() < 3 {
        return Ok(None);
    }
    // Also merge atoms that become equal or bitwise complements modulo `2^k` after `demanded`
    // narrowed constants on the `k`-bit prefix.
    merge_complement_atoms_at(cx, &mut reg, k);
    let t = reg.atoms.len();
    if t == 0 || t > MAX_ATOMS {
        return Ok(None);
    }
    let kmask = u64::MAX >> (64 - k);
    // When `n` is observed directly on its entire `k`-bit prefix (`exact_prefix`, e.g. `n & (2^k - 1)`
    // or `trunc<k>(n)`) and `Phase::Mba` (`nf`'s multi-class `low_read`) is active, defer sums
    // with >= 2 non-uniform constant-masked bitwise atoms so `nf` can unify bit classes across
    // shared underlying variables instead of treating each masked term as an independent atom.
    #[cfg(feature = "mba")]
    if exact_prefix
        && !r.quarantined_passes.contains(&PassKind::Mba)
        && r.inner
            .strategy
            .phases
            .iter()
            .any(|ph| matches!(ph, crate::engine::Phase::Mba(_)))
    {
        let masked_atoms = reg
            .atoms
            .iter()
            .filter(|&&a| {
                let an = cx.node(a);
                matches!(an.op, OpCode::And | OpCode::Or | OpCode::Xor)
                    && cx
                        .const_val(an.a)
                        .or_else(|| cx.const_val(an.b))
                        .and_then(|v| v.to_u64())
                        .is_some_and(|cv| {
                            let cm = cv & kmask;
                            cm != 0 && cm != kmask
                        })
            })
            .count();
        if masked_atoms >= 1 {
            return Ok(None);
        }
    }
    #[cfg(not(feature = "mba"))]
    let _ = exact_prefix;
    let sig_work = (reg.order.len() << t) as u64;
    if sig_work > 8192 {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, sig_work)?;
    let kw = crate::Width::new(k).map_err(|e| Stop::Error(e.into()))?;
    let w = cx.width_of(n);
    let sig_k: Vec<BitVec> = {
        let Some(row) = signature_words(cx, &reg, n, &mut r.linear_mba) else {
            return Ok(None);
        };
        row.iter()
            .map(|&v| BitVec::wrapping_from_u64(kw, v & kmask))
            .collect()
    };
    let lift_coeff = |ck: &BitVec| -> BitVec {
        if ck.is_zero() {
            return BitVec::zero(w);
        }
        let neg_ck = BitVec::un_unchecked(UnOp::Neg, ck);
        if crate::facts::known::count_ones(&neg_ck) < crate::facts::known::count_ones(ck)
            && let Ok(zn) = neg_ck.zext(w)
        {
            return BitVec::un_unchecked(UnOp::Neg, &zn);
        }
        ck.zext(w).unwrap_or_else(|_| BitVec::zero(w))
    };

    let d = mobius(&sig_k);
    let canon = reg.atoms.clone();
    let mut cands: Vec<(u32, Candidate)> = Vec::new();
    if (0..d.len()).all(|s| (s as u32).count_ones() < 2 || d[s].is_zero()) {
        let konst = lift_coeff(&BitVec::un_unchecked(UnOp::Neg, &d[0]));
        let terms: Vec<(usize, BitVec)> = (0..t)
            .filter(|&j| !d[1 << j].is_zero())
            .map(|j| (j, lift_coeff(&d[1 << j])))
            .collect();
        let placeholder: Vec<(u32, BitVec)> =
            terms.iter().map(|(j, c)| (reg.atoms[*j], *c)).collect();
        let est = linear::estimate(&linear::Form::of(konst, &placeholder));
        cands.push((est, Candidate::Affine(konst, terms)));
    } else {
        let konst = lift_coeff(&BitVec::un_unchecked(UnOp::Neg, &d[0]));
        let terms: Vec<(usize, BitVec)> = (1..d.len())
            .filter(|&s| !d[s].is_zero())
            .map(|s| (s, lift_coeff(&d[s])))
            .collect();
        let ands: u32 = terms
            .iter()
            .map(|&(s, _)| (s as u32).count_ones().saturating_sub(1))
            .sum();
        let placeholder: Vec<(u32, BitVec)> = terms
            .iter()
            .enumerate()
            .map(|(idx, &(_, c))| (u32::MAX - idx as u32, c))
            .collect();
        let est = ands + linear::estimate(&linear::Form::of(konst, &placeholder));
        cands.push((est, Candidate::Conjunctions(konst, terms)));

        if r.inner.strategy.basis_sums && t >= 3 {
            let share = (r.meter.limit.pass_work / COBRA_SHARE).max(1);
            let allow = r.meter.left_in(|b| b.pass_work).min(share);
            let mut left = allow;
            let cobra_res = crate::cobra::decompose(t, kw, u32::from(k), &d, &mut left);
            let spent = if cobra_res.is_err() {
                allow
            } else {
                allow - left
            };
            r.meter.charge(Counter::PassWork, spent)?;
            if let Ok(Some(cobra_terms)) = cobra_res {
                let lifted_ts: Vec<(crate::cobra::BasisOp, BitVec)> = cobra_terms
                    .into_iter()
                    .map(|(op, c)| (op, lift_coeff(&c)))
                    .collect();
                let gates: u32 = lifted_ts.iter().map(|(op, _)| op.gate_cost()).sum();
                let ph: Vec<(u32, BitVec)> = lifted_ts
                    .iter()
                    .enumerate()
                    .map(|(idx, (_, c))| (u32::MAX - idx as u32, *c))
                    .collect();
                let est = gates + linear::estimate(&linear::Form::of(konst, &ph));
                cands.push((est, Candidate::Cobra(konst, lifted_ts)));
            }
        }
    }

    if t <= 3 {
        let mut distinct: Vec<BitVec> = Vec::new();
        for v in &sig_k {
            if !distinct.contains(v) {
                distinct.push(*v);
            }
        }
        let pos: Vec<usize> = canon
            .iter()
            .map(|a| reg.atoms.iter().position(|b| b == a).unwrap_or(0))
            .collect();
        for &u0 in &distinct {
            let u0_w = lift_coeff(&u0);
            let mut ind: Vec<(BitVec, u8)> = Vec::new();
            let mut funcs = 0u32;
            let mut placeholder: Vec<(u32, BitVec)> = Vec::new();
            for &uk in distinct.iter().filter(|&&u| u != u0) {
                let mut tt = 0u8;
                for i in 0..8usize {
                    let mut p = 0usize;
                    for (ci, &j) in pos.iter().enumerate() {
                        p |= ((i >> ci) & 1) << j;
                    }
                    if sig_k[p & ((1 << t) - 1)] == uk {
                        tt |= 1 << i;
                    }
                }
                funcs += bitwise::min_forms().forms[tt as usize]
                    .0
                    .iter()
                    .filter(|tok| !matches!(tok, bitwise::T::Var(_)))
                    .count() as u32;
                let diff_w = lift_coeff(&BitVec::bin_unchecked(BinOp::Sub, &u0, &uk));
                placeholder.push((u32::MAX - placeholder.len() as u32, diff_w));
                ind.push((diff_w, tt));
            }
            let est = funcs + linear::estimate(&linear::Form::of(u0_w, &placeholder));
            cands.push((est, Candidate::Indicators(u0_w, ind)));
        }
    }

    cands.sort_by_key(|c| c.0);
    let Some((est, cand)) = cands.into_iter().next() else {
        return Ok(None);
    };
    if est.saturating_add(1) >= reg.order.len() as u32 {
        return Ok(None);
    }
    let before = cx.len() as u32;
    let form = match cand {
        Candidate::Affine(konst, terms) => {
            let terms: Vec<(u32, BitVec)> =
                terms.iter().map(|(j, c)| (reg.atoms[*j], *c)).collect();
            linear::Form::of(konst, &terms)
        }
        Candidate::Indicators(u0, ind) => {
            let mut terms = Vec::new();
            for (c, tt) in ind {
                let g = bitwise::emit(r, cx, tt, &canon)?;
                terms.push((g, c));
            }
            linear::Form::of(u0, &terms)
        }
        Candidate::Cobra(konst, ops) => {
            let mut terms = Vec::with_capacity(ops.len());
            for (op, c) in ops {
                let g = emit_basis_op(r, cx, &op, &reg.atoms)?;
                terms.push((g, c));
            }
            linear::Form::of(konst, &terms)
        }
        Candidate::Conjunctions(konst, sets) => {
            let mut terms = Vec::new();
            for (set, c) in sets {
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
                    terms.push((g, c));
                }
            }
            linear::Form::of(konst, &terms)
        }
    };
    let e = linear::emit(r, cx, &form)?;
    if e == n {
        super::discard(r, cx, before);
        return Ok(None);
    }
    Ok(Some(e))
}

#[cfg(test)]
mod extra_tests {
    use crate::engine::{Budget, Engine, Run, Strategy};
    use crate::{Context, ParseOptions, View, Width};

    #[test]
    fn proves_complement_atom_and_disjoint_shift_scale_equal() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let engine = Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap();

        // Expanded complement `a * (-C) - 1 == ~(a * C)` merges into a single atom column.
        let comp = "let %0 = x * 0x123456789abcdef1; \
                    let %1 = x * 0xedcba9876543210f - 1; \
                    (%0 | y) + (%0 & y) + (~%1 ^ y) * 2 == (%0 + y) * 3 - (%0 & y) * 4";
        let e1 = cx.parse(comp, &opt).unwrap();
        let out1 = engine
            .run(
                &mut cx,
                &[e1],
                Run::default().with_per_call(Budget::fuel(1 << 14)),
            )
            .unwrap();
        assert!(matches!(cx.view(out1.roots[0].expr).unwrap(), View::Const(v) if !v.is_zero()));

        // Disjoint shifted halves (`(x << 6) & (x >>u 58) == 0`) plus shift-scale transfer
        // `x * (5 << 6) == (x << 6) * 5`, and `2^62 * ((x << 6) & y) == 0`.
        let shift = "let %0 = x >>u 58; let %1 = x << 6; \
                     (%1 & %0) * 0xdeadbeef + (%1 & y) * 0x400000000000000a \
                     + (%1 & ~y) * 5 + (y & ~%1) * 5 == x * 0x140 + y * 5";
        let e2 = cx.parse(shift, &opt).unwrap();
        let out2 = engine
            .run(
                &mut cx,
                &[e2],
                Run::default().with_per_call(Budget::fuel(1 << 14)),
            )
            .unwrap();
        assert!(matches!(cx.view(out2.roots[0].expr).unwrap(), View::Const(v) if !v.is_zero()));
    }

    #[test]
    fn proves_equal_affine_atoms_through_disjoint_or_and_subset_xor() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let s = r#"
let %0 = #4294967296 + 0x35f9c8925e0c9046 | 0x7d77deffbfdbef77;
let %1 = %0 * 0x629b1e1e3cc3fe54;
let %2 = %0 * 0xa3fbf9b0c587df45;
let %3 = %1 & %2;
let %4 = %0 * 0x15ebb07b3718d004;
let %5 = %0 * 0x7e9a1541094fe1af;
let %6 = %4 & %5;
let %7 = %5 & (%4 & %1);
let %8 = #4294967300 & 0x3c7300;
let %9 = (#4294967297 & 1) << 2;
let %10 = zext<64>(#4294967299 + 3872 == #4294967298 | 0xffff000000000000) << 6;
let %11 = %0 * 0x273849cc4174b75 * 0x1cd4d30c & 0xffffffff;
let %12 = %0 * 0xddc254deb1929446 + (%8 | %9 ^ 6 | %10) + %11 - 3994;
let %13 = %12 & %1;
let %14 = %12 & %4;
let %15 = %1 & %5;
let %16 = %2 & %6;
let %17 = %0 * 0x1fe9c349b6a17bf9;
let %18 = %0 * 0x30cc30b6ca5a7408;
let %19 = %11 + (%8 | %10) - %9 - %0 * 0x223dab214e6d6bba - 3988;
~(%3 + %6 + (%2 & %7) + (%2 & (%5 & %13)) + (%2 & (%5 & %14)) + %15 - %1 - %5 - (%2 & %15) - %7 - %16 - (%2 & (%5 & (%1 & %14))) - (%2 & %13) + 0x18753c9efc59fa95 & %17) | %18 == ~(%6 + (~(%19 | %5) & %3) + %15 + %0 * 0x1ecacca0b9ec1ffd - (~%19 & %16) - (%2 & (%5 & (%1 & (%19 & %4)))) - (~%2 & %7) + 0x18753c9efc59fa95 & %17) | %18
"#;
        let e = cx.parse(s, &opt).unwrap();
        let engine = Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate().with_basis_sums(false))
            .build()
            .unwrap();
        let out = engine
            .run(
                &mut cx,
                &[e],
                Run::default().with_per_call(Budget::fuel(1 << 14)),
            )
            .unwrap();
        assert!(matches!(cx.view(out.roots[0].expr).unwrap(), View::Const(v) if !v.is_zero()));
    }

    #[test]
    #[cfg(feature = "prove")]
    fn proves_peeled_masked_congruence_and_nonuniform_mask_atoms() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 15);
        for text in [
            // Shared non-constant Xor/And wrapper over mod-2^32 equivalent MBA subterms
            "let u1 = (a ^ b) + 2 * (a & b); let u2 = (a | b) + (a & b) + 0x100000000; \
             ((w ^ u1) & 0xffffffff) == ((w ^ u2) & 0xffffffff)",
            // Shared non-uniform sparse mask atom inside peeled non-constant wrapper
            "let m1 = ((a ^ b) + 2 * (a & b)) & 0x8afbc799; \
             let m2 = ((a | b) + (a & b)) & 0x8afbc799; \
             ((w ^ (m1 + c)) & 0x8afbc799) == ((w ^ (m2 + c)) & 0x8afbc799)",
        ] {
            let e = cx.parse(text, &opt).unwrap();
            let outcome = crate::prove::valid_under_with(&mut cx, e, None, &cfg, &prover).unwrap();
            assert!(
                matches!(outcome, crate::prove::Outcome::Proved(_)),
                "expected Proved for {text}, got {outcome:?}"
            );
        }
    }

    #[test]
    #[cfg(feature = "prove")]
    fn rejects_unsound_affine_atoms_and_non_complementary_rot_unions() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Non-disjoint Or is NOT Add (`(x & 6) | (y & 2)` overlaps at bit 1)
            "let a = (x & 6) | (y & 2); let b = (x & 6) + (y & 2); (a & z) + (a | z) == (b & z) + (b | z)",
            // Non-subset Xor is NOT Sub (`(x & 8)` is NOT a subset of 6)
            "let a = (x & 8) ^ 6; let b = 6 - (x & 8); (a & z) + (a | z) == (b & z) + (b | z)",
            // Non-complementary shifts do NOT form a rotate union
            "let r = rotl(x, 6); let s1 = x << 5; let s2 = x >>u 58; (r & y) + (r | y) == ((s1 | s2) & y) + ((s1 | s2) | y)",
            // Non-zero affine remainder after degree >= 2 cancellation
            "let a = x * 3; let b = x * 5; (a & y) + (a | y) + b == y + x * 9",
            // Peeled masked congruence must reject difference inside the live mask (bit 31)
            "let u1 = (a ^ b) + 2 * (a & b); let u2 = (a | b) + (a & b) + 0x80000000; \
             ((w ^ u1) & 0xffffffff) == ((w ^ u2) & 0xffffffff)",
        ] {
            let e = cx.parse(text, &opt).unwrap();
            let outcome = crate::prove::valid_under_with(&mut cx, e, None, &cfg, &prover).unwrap();
            assert!(
                matches!(outcome, crate::prove::Outcome::Refuted(_)),
                "expected Refuted for {text}, got {outcome:?}"
            );
        }
    }

    /// A lifted handler's 201-node selector: masked MBA over two words whose constants the
    /// demanded pass narrows to the low 32 bits, read through `trunc<32>(…) >>u 13 & 0x60201`.
    /// Its value is 1 for every input. With the walk's engine (deobfuscate, opaque sweep) at
    /// `fuel(1 << 14)` it was left at 83 nodes; the prefix-masked linear form folds it there.
    #[test]
    #[cfg(feature = "mba")]
    fn narrowed_masked_selector_folds_at_small_fuel() {
        let src = "\
            let %0 = a:64 ^ b:64;
            let %1 = (%0 | 0x70900289080063f8) & 0x7fd237dd3e3ee7fb;
            let %2 = zext<64>(p1:8 & 102) << 8 | zext<64>(p0:8 & -71) | zext<64>(p2:8 & 63) << 16 | zext<64>(p3:8 & -111) << 24 | zext<64>(p4:8 & -3 & 3) << 32 | zext<64>(p5:8 & -118) << 48 | zext<64>(p6:8 & 96) << 56;
            let %3 = zext<64>(trunc<32>((zext<64>(extract<48, 16>(%2)) << 48 | zext<64>(trunc<40>(%2))) >>u 55) & 1);
            let %4 = %1 * %3;
            let %5 = ~b;
            let %6 = ~a;
            let %7 = %6 & 0xe228580b1603ac80;
            let %8 = ~(a & 0x1dd7a7f4e9fc537f) & ~%7;
            let %9 = (a | b) & 0x1dd7a7f4e9fc537f;
            let %10 = %5 & 0x1dd7a7f4e9fc5379;
            let %11 = (b | 6) & 0xe228580b1603ac80;
            let %12 = b & -7;
            let %13 = %4 * 0x6db6db6db6db6db7 + %1 * (~(%5 & 6) & %7) * (%3 * 0xb6db6db6db6db6dc) + %4 * 0xdb6db6db6db6db6e * (~(~(%5 & a) & ~(%6 & b) & -7) & (zext<64>(trunc<8>(~(%0 & 6) & 0x1dd7a7f4e9fc537f)) | 0x1dd7a7f4e9fc5300)) + %4 * (%8 & 6 ^ b) * 0x2492492492492492 + %1 * (%9 ^ -7) * %3 * 0x9249249249249249 + %4 * (b & 0xe228580b1603ac86 & (%6 ^ a) ^ a) * 0x6db6db6db6db6db7 + %4 * b * 0x6db6db6db6db6db7 + %1 * (~%10 & ~%11 & a | %6 & (%11 | %10)) * %3 * 0x6db6db6db6db6db7 + ~(%12 & %8) * %4 * 0xb6db6db6db6db6db + ~((%9 | %5 & %7) & 6) * %4 * 0xb6db6db6db6db6db + %4 * (~((%12 | 0xe228580b1603ac80) & a) & ~(%6 & (~%12 & 0x1dd7a7f4e9fc537f))) * 0xb6db6db6db6db6db + (a & 0xe228580b1603ac86 | b) * %3 * %1 * 0x9249249249249249 + (%6 & ((b ^ 0xe228580b1603ac80) & 6)) * %3 * %1 * 0xb6db6db6db6db6db;
            let %14 = %13 | 0xa2002003001a722c;
            let %15 = %13 ^ 0xa2002003001a722c;
            trunc<32>(%14 * %15 * -1 + ~%15 * %14 * -1) >>u 13 & 0x60201";
        let engine = Engine::builder()
            .builtin()
            .strategy(
                Strategy::deobfuscate()
                    .with_mba(crate::mba::MbaConfig::default().with_opaque_sweep(true)),
            )
            .build()
            .unwrap();
        for fuel in [1u64 << 14, 1 << 19] {
            let mut cx = Context::new();
            let e = cx.parse(src, &ParseOptions::width(Width::W64)).unwrap();
            let out = engine
                .run(
                    &mut cx,
                    &[e],
                    Run::default().with_per_call(Budget::fuel(fuel)),
                )
                .unwrap();
            assert_eq!(
                cx.view(out.roots[0].expr).unwrap(),
                View::Const(crate::BitVec::one(Width::W32)),
                "fuel {fuel}"
            );
            assert_eq!(out.stats.mba.calls, 0, "folded before the MBA phase");
        }
    }

    #[test]
    fn signed_complementary_products_and_partition_masked_linear_mba() {
        let mut cx = Context::new();
        let o64 = ParseOptions::width(Width::W64);
        let engine = Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap();

        // 1. Signed complementary products: `-(a * b) - (~b * a) == a`,
        //    `a * b * -1 + ~b * a * -1 == a`, `-(a * b) + -(~b * a) == a`.
        for (src, want) in [
            ("-(a * b) - (~b * a)", "a"),
            ("a * b * -1 + ~b * a * -1", "a"),
            ("-(a * b) + -(~b * a)", "a"),
            ("(a * b) - -(~b * a)", "-a"),
        ] {
            let e = cx.parse(src, &o64).unwrap();
            let expected = cx.parse(want, &o64).unwrap();
            let out = engine
                .run(
                    &mut cx,
                    &[e],
                    Run::default().with_per_call(Budget::fuel(1 << 14)),
                )
                .unwrap();
            assert_eq!(out.roots[0].expr, expected, "failed on {src}");
        }

        // 2. Partition-masked 2-variable linear MBA collapsing to a constant and to an affine form
        //    at 64-bit and 128-bit widths within `fuel(16384)` and without `Phase::Mba`.
        let masked_const = "\
            let m0 = 0x1dd7a7f4e9fc5379; \
            let m1 = 0xe228580b1603ac80; \
            let m2 = 6; \
            let a = (x & m0) + (~x & m0) + (y & m1) + (~y & m1) + ((x ^ y) & m2) + (~(x ^ y) & m2) + 2; \
            a";
        let e_mc = cx.parse(masked_const, &o64).unwrap();
        let out_mc = engine
            .run(
                &mut cx,
                &[e_mc],
                Run::default().with_per_call(Budget::fuel(1 << 14)),
            )
            .unwrap();
        assert_eq!(
            cx.view(out_mc.roots[0].expr).unwrap(),
            View::Const(crate::BitVec::one(Width::W64))
        );

        let masked_affine = "\
            let m0 = 0x0f0f0f0f0f0f0f0f; \
            let m1 = 0xf0f0f0f0f0f0f0f0; \
            ((x & m0) | (y & m0)) + ((x & m0) & (y & m0)) \
            + ((x & m1) ^ (y & m1)) + 2 * ((x & m1) & (y & m1))";
        let e_ma = cx.parse(masked_affine, &o64).unwrap();
        let want_ma = cx.parse("x + y", &o64).unwrap();
        let out_ma = engine
            .run(
                &mut cx,
                &[e_ma],
                Run::default().with_per_call(Budget::fuel(1 << 14)),
            )
            .unwrap();
        assert_eq!(out_ma.roots[0].expr, want_ma);

        // 128-bit masked constant.
        let o128 = ParseOptions::width(Width::W128);
        let masked_128 = "((p & 0x00ff00ff00ff00ff00ff00ff00ff00ff) + (~p & 0x00ff00ff00ff00ff00ff00ff00ff00ff)) \
                        + ((q & 0xff00ff00ff00ff00ff00ff00ff00ff00) + (~q & 0xff00ff00ff00ff00ff00ff00ff00ff00)) + 1";
        let e_128 = cx.parse(masked_128, &o128).unwrap();
        let out_128 = engine
            .run(
                &mut cx,
                &[e_128],
                Run::default().with_per_call(Budget::fuel(1 << 14)),
            )
            .unwrap();
        assert_eq!(
            cx.view(out_128.roots[0].expr).unwrap(),
            View::Const(crate::BitVec::zero(Width::W128))
        );

        // 3. Soundness guard: `(x & 1) * 2 - (x & 2)` vanishes at `x = 0` and `x = -1`,
        //    but NOT at `x = 1` (equals 2); must NOT fold to 0.
        let non_const = cx.parse("(x & 1) * 2 - (x & 2)", &o64).unwrap();
        let out_nc = engine
            .run(
                &mut cx,
                &[non_const],
                Run::default().with_per_call(Budget::fuel(1 << 14)),
            )
            .unwrap();
        assert!(
            !matches!(cx.view(out_nc.roots[0].expr).unwrap(), View::Const(_)),
            "must not mis-fold non-constant masked expression"
        );
    }
}
