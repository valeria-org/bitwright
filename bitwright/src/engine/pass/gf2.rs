//! Affine maps over GF(2) across widths `1..=512` and up to [`MAX_ATOMS`] atoms (called by the
//! xor pass): an expression built from atoms `x_0, ..., x_{K-1}` by `^`, `~`, constant `&`/`|`,
//! constant shifts and rotations, byte swaps, bit reversals, slices, zero/sign extensions, and
//! concatenations is `c ⊕ ⊕_m M_m·x_m` over GF(2).
//!
//! Each surviving atom's matrix `M_m` is emitted in its smallest structural representation —
//! identity, unary permutation/extension/slice, arithmetic shift, or diagonal rotation-mask
//! decomposition (over `x_m`, `bswap(x_m)`, or `bitrev(x_m)`, and across width changes via
//! `zext`/`sext`/`extract`) — whenever the canonical form strictly shrinks the DAG. Multi-atom
//! homomorphisms (`((x ^ y) >>u k) ^ (x >>u k) -> y >>u k`, `bswap(x ^ y) ^ bswap(x) -> bswap(y)`,
//! CRC/SPN/ARX linear mixes, and 256/512-bit xorshift involutions) collapse in one pass.

use super::{Fin, PassKind, Runner, Step, Stop, finish, worth_building};
use crate::engine::budget::Counter;
use crate::expr::{Context, Node, OpCode};
use crate::invert::gf2::{self, Row, Rows, ZERO_ROW, row_bit, row_is_zero, row_set};
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// Maximum interior GF(2) nodes in one analyzed region.
const MAX_NODES: usize = 64;

/// Maximum distinct non-constant leaf atoms in one analyzed region.
const MAX_ATOMS: usize = 8;

/// Fast per-node summary cached for the call so ordinary expressions without bit movement or
/// with too many atoms exit in `O(1)` without allocating.
#[derive(Clone, Copy, Default)]
pub(crate) struct Summary {
    /// 64-bit Bloom filter of leaf atom IDs below this node.
    bloom: u64,
    /// Saturated count of GF(2)-interior operations below this node.
    ops: u16,
    /// Whether any bit-moving or width-changing operation appears inside the region.
    moves: bool,
    /// Whether this slot has been populated.
    ready: bool,
}

#[inline]
fn atom_bit(id: u32) -> u64 {
    1u64 << (id.wrapping_mul(0x9E37_79B9) >> 26)
}

/// Whether `node` (at `id`) is a valid interior GF(2)-affine operator (masks and shift counts
/// must be constants).
fn interior_op(cx: &Context, node: &Node) -> bool {
    if node.width == 0 || node.width > gf2::MAX_BITS {
        return false;
    }
    match node.op {
        OpCode::Xor
        | OpCode::Not
        | OpCode::Bswap
        | OpCode::BitRev
        | OpCode::Extract
        | OpCode::Zext
        | OpCode::Sext
        | OpCode::Concat => true,
        OpCode::Add | OpCode::Sub | OpCode::Neg => node.width == 1,
        OpCode::And | OpCode::Or => cx.is_const(node.a) || cx.is_const(node.b),
        OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR => {
            cx.is_const(node.b)
        }
        _ => false,
    }
}

#[inline]
fn moves_bits(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Shl
            | OpCode::LShr
            | OpCode::AShr
            | OpCode::RotL
            | OpCode::RotR
            | OpCode::Bswap
            | OpCode::BitRev
            | OpCode::Extract
            | OpCode::Zext
            | OpCode::Sext
            | OpCode::Concat
    )
}

/// Varying children of an interior GF(2) node (excludes constant shift counts and masks).
fn varying_children<'a>(cx: &'a Context, node: &'a Node) -> impl Iterator<Item = u32> + 'a {
    let counted = matches!(
        node.op,
        OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR
    );
    node.children()
        .filter(move |&c| !(counted && c == node.b) && !cx.is_const(c))
}

/// Whether `n` can be the root of a worthwhile GF(2) region (called from `xor::step`).
#[inline]
pub(super) fn can_root(cx: &Context, n: u32) -> bool {
    let node = cx.node(n);
    if !interior_op(cx, &node) {
        return false;
    }
    // Bare cast of an atom (`zext(x)`, `extract(x)`) is already canonical unless its operand is
    // itself an interior GF(2) op.
    if matches!(
        node.op,
        OpCode::Extract
            | OpCode::Zext
            | OpCode::Sext
            | OpCode::Bswap
            | OpCode::BitRev
            | OpCode::Not
    ) {
        let child = cx.node(node.a);
        return interior_op(cx, &child);
    }
    true
}

fn summary_of(r: &mut Runner<'_, '_>, cx: &Context, n: u32) -> Summary {
    if r.gf2.summaries.len() < cx.len() {
        r.gf2.summaries.resize(cx.len(), Summary::default());
    }
    if r.gf2.summaries[n as usize].ready {
        return r.gf2.summaries[n as usize];
    }
    let mut stack = core::mem::take(&mut r.gf2.stack);
    stack.clear();
    stack.push((n, false));
    while let Some((i, done)) = stack.pop() {
        if r.gf2.summaries[i as usize].ready {
            continue;
        }
        if cx.is_const(i) {
            r.gf2.summaries[i as usize] = Summary {
                bloom: 0,
                ops: 0,
                moves: false,
                ready: true,
            };
            continue;
        }
        let node = cx.node(i);
        if !interior_op(cx, &node) {
            r.gf2.summaries[i as usize] = Summary {
                bloom: atom_bit(i),
                ops: 0,
                moves: false,
                ready: true,
            };
            continue;
        }
        if !done {
            stack.push((i, true));
            for c in varying_children(cx, &node) {
                if !r.gf2.summaries[c as usize].ready {
                    stack.push((c, false));
                }
            }
            continue;
        }
        let mut bloom = 0u64;
        let mut ops = 1u16;
        let mut moves = moves_bits(node.op);
        for c in varying_children(cx, &node) {
            let cs = r.gf2.summaries[c as usize];
            bloom |= cs.bloom;
            ops = ops.saturating_add(cs.ops);
            moves |= cs.moves;
        }
        r.gf2.summaries[i as usize] = Summary {
            bloom,
            ops,
            moves,
            ready: true,
        };
    }
    r.gf2.stack = stack;
    r.gf2.summaries[n as usize]
}

/// Collects the leaf `atoms` (sorted in canonical `cx.order`) and topological interior `nodes`
/// below `n` when within `[1..=MAX_ATOMS]` atoms and `[2..=MAX_NODES]` interior nodes.
fn collect_region(cx: &Context, n: u32) -> Option<(Vec<u32>, Vec<u32>)> {
    let mut atoms: Vec<u32> = Vec::new();
    let mut nodes: Vec<u32> = Vec::new();
    let mut seen: crate::hash::IdMap<u32, u8> = crate::hash::IdMap::default();
    let mut stack: Vec<(u32, bool)> = vec![(n, false)];
    let mut moves = false;
    while let Some((i, expanded)) = stack.pop() {
        if expanded {
            if seen.get(&i) == Some(&1) {
                seen.insert(i, 2);
                nodes.push(i);
            }
            continue;
        }
        if seen.contains_key(&i) || cx.is_const(i) {
            continue;
        }
        let node = cx.node(i);
        if !interior_op(cx, &node) {
            if node.width == 0 || node.width > gf2::MAX_BITS {
                return None;
            }
            if !atoms.contains(&i) {
                if atoms.len() >= MAX_ATOMS {
                    return None;
                }
                atoms.push(i);
            }
            seen.insert(i, 2);
            continue;
        }
        if nodes.len() >= MAX_NODES {
            return None;
        }
        moves |= moves_bits(node.op);
        seen.insert(i, 1);
        stack.push((i, true));
        for c in varying_children(cx, &node) {
            if !seen.contains_key(&c) {
                stack.push((c, false));
            }
        }
    }
    if !moves || atoms.is_empty() || nodes.len() < 2 || nodes.len() > MAX_NODES {
        return None;
    }
    atoms.sort_by(|a, b| cx.order(*a, *b));
    Some((atoms, nodes))
}

// ----- matrix planning & compact emission -------------------------------------------------------

/// Pre-planned emission for one square `W × W` matrix over a base node of width `W` whose bits
/// `[valid_bits..W)` are known to be zero (`valid_bits == W` when arbitrary).
enum SquarePlan {
    /// Exact identity (`base` itself, 0 new nodes).
    Identity,
    /// Arithmetic right shift `base >>s s` (`s > 0`, 2 new nodes).
    AShr(u32),
    /// Cyclic diagonals over `base`, `bswap(base)`, or `bitrev(base)`.
    Diags {
        pre: Option<UnOp>,
        terms: Vec<DiagTerm>,
    },
}

enum DiagTerm {
    /// `base` (unmasked, `k == 0`).
    Id,
    /// `base & mask`.
    Mask(BitVec),
    /// `base << k`.
    Shl(u32),
    /// `base >>u s`.
    LShr(u32),
    /// `rotl(base, k)`.
    RotL(u32),
    /// `rotl(base, k) & mask`.
    RotLMask(u32, BitVec),
}

impl DiagTerm {
    fn cost(&self) -> u32 {
        match self {
            DiagTerm::Id => 0,
            DiagTerm::Mask(_) | DiagTerm::Shl(_) | DiagTerm::LShr(_) | DiagTerm::RotL(_) => 2,
            DiagTerm::RotLMask(_, _) => 4,
        }
    }

    fn emit(&self, cx: &mut Context, base: u32, w: Width) -> Result<u32, crate::Error> {
        let count =
            |cx: &mut Context, v: u32| cx.mk_const(&BitVec::wrapping_from_u64(w, u64::from(v)));
        match self {
            DiagTerm::Id => Ok(base),
            DiagTerm::Mask(d) => {
                let m = cx.mk_const(d)?;
                cx.c_bin(BinOp::And, base, m)
            }
            DiagTerm::Shl(k) => {
                let c = count(cx, *k)?;
                cx.c_bin(BinOp::Shl, base, c)
            }
            DiagTerm::LShr(s) => {
                let c = count(cx, *s)?;
                cx.c_bin(BinOp::LShr, base, c)
            }
            DiagTerm::RotL(k) => {
                let c = count(cx, *k)?;
                cx.c_bin(BinOp::RotL, base, c)
            }
            DiagTerm::RotLMask(k, d) => {
                let c = count(cx, *k)?;
                let r = cx.c_bin(BinOp::RotL, base, c)?;
                let m = cx.mk_const(d)?;
                cx.c_bin(BinOp::And, r, m)
            }
        }
    }
}

impl SquarePlan {
    fn cost(&self) -> u32 {
        match self {
            SquarePlan::Identity => 0,
            SquarePlan::AShr(_) => 2,
            SquarePlan::Diags { pre, terms } => {
                let pre_cost = u32::from(pre.is_some());
                let body: u32 = terms.iter().map(DiagTerm::cost).sum();
                let joins = (terms.len() as u32).saturating_sub(1);
                pre_cost + body + joins
            }
        }
    }

    fn emit(&self, cx: &mut Context, base: u32, w: Width) -> Result<u32, crate::Error> {
        match self {
            SquarePlan::Identity => Ok(base),
            SquarePlan::AShr(s) => {
                let c = cx.mk_const(&BitVec::wrapping_from_u64(w, u64::from(*s)))?;
                cx.c_bin(BinOp::AShr, base, c)
            }
            SquarePlan::Diags { pre, terms } => {
                let src = match pre {
                    Some(op) => cx.c_un(*op, base)?,
                    None => base,
                };
                let mut acc: Option<u32> = None;
                for t in terms {
                    let e = t.emit(cx, src, w)?;
                    acc = Some(match acc {
                        None => e,
                        Some(a) => cx.c_bin(BinOp::Xor, a, e)?,
                    });
                }
                Ok(acc.unwrap_or(src))
            }
        }
    }
}

fn is_unit_row(r: &Row, col: usize) -> bool {
    let mut expected = ZERO_ROW;
    row_set(&mut expected, col);
    *r == expected
}

/// Decomposes `rows` (`wb × wb`) into cyclic diagonals over a `w`-bit value whose bits
/// `[valid_bits..wb)` are known zero (`valid_bits == wb` when arbitrary).
fn build_diags(rows: &[Row], w: Width, valid_bits: usize) -> Vec<DiagTerm> {
    let wb = usize::from(w.bits());
    let ones = BitVec::ones(w);
    let mut terms = Vec::new();
    for k in 0..wb {
        let mut d_limbs = [0u64; 8];
        let mut z_limbs = [0u64; 8];
        let mut any = false;
        for (i, row) in rows.iter().enumerate() {
            let j = (i + wb - k) % wb;
            if j >= valid_bits {
                z_limbs[i >> 6] |= 1u64 << (i & 63);
            } else if row_bit(row, j) {
                d_limbs[i >> 6] |= 1u64 << (i & 63);
                any = true;
            }
        }
        if !any {
            continue;
        }
        let d = BitVec::wrapping_from_limbs(w, &d_limbs);
        let z = BitVec::wrapping_from_limbs(w, &z_limbs);
        let d_or_z = BitVec::bin_unchecked(BinOp::Or, &d, &z);
        if k == 0 {
            if d_or_z.is_ones() {
                terms.push(DiagTerm::Id);
            } else {
                terms.push(DiagTerm::Mask(d));
            }
            continue;
        }
        let shl_mask =
            BitVec::bin_unchecked(BinOp::Shl, &ones, &BitVec::wrapping_from_u64(w, k as u64));
        let low_mask = BitVec::un_unchecked(UnOp::Not, &shl_mask);
        // `base << k` is zero below `k` and equals `rotl(base, k)` at `>= k`; positions where
        // `rotl(base, k)` is already known zero (`z`) need no mask.
        if BitVec::bin_unchecked(BinOp::And, &d, &low_mask).is_zero()
            && BitVec::bin_unchecked(BinOp::Or, &d_or_z, &low_mask).is_ones()
        {
            terms.push(DiagTerm::Shl(k as u32));
            continue;
        }
        // `base >>u (wb - k)` is zero at `>= k` and equals `rotl(base, k)` below `k`.
        if BitVec::bin_unchecked(BinOp::And, &d, &shl_mask).is_zero()
            && BitVec::bin_unchecked(BinOp::Or, &d_or_z, &shl_mask).is_ones()
        {
            terms.push(DiagTerm::LShr((wb - k) as u32));
            continue;
        }
        if d_or_z.is_ones() {
            terms.push(DiagTerm::RotL(k as u32));
        } else {
            terms.push(DiagTerm::RotLMask(k as u32, d));
        }
    }
    terms
}

fn permute_cols_bswap(rows: &[Row], wb: usize) -> Rows {
    let bytes = wb / 8;
    rows.iter()
        .map(|r| {
            let mut out = ZERO_ROW;
            for j in 0..wb {
                if row_bit(r, j) {
                    let dst = (bytes - 1 - j / 8) * 8 + (j % 8);
                    row_set(&mut out, dst);
                }
            }
            out
        })
        .collect()
}

fn permute_cols_bitrev(rows: &[Row], wb: usize) -> Rows {
    rows.iter()
        .map(|r| {
            let mut out = ZERO_ROW;
            for j in 0..wb {
                if row_bit(r, j) {
                    row_set(&mut out, wb - 1 - j);
                }
            }
            out
        })
        .collect()
}

fn plan_square(rows: &[Row], w: Width, valid_bits: usize) -> SquarePlan {
    let wb = usize::from(w.bits());
    if valid_bits == wb && (0..wb).all(|i| is_unit_row(&rows[i], i)) {
        return SquarePlan::Identity;
    }
    // Exact arithmetic right shift `x >>s s` (`1 <= s < wb`).
    if valid_bits == wb && wb >= 2 && is_unit_row(&rows[wb - 1], wb - 1) {
        let mut first_col = None;
        for c in 0..wb {
            if is_unit_row(&rows[0], c) {
                first_col = Some(c);
                break;
            }
        }
        if let Some(s) = first_col
            && s > 0
            && (0..wb).all(|i| is_unit_row(&rows[i], (i + s).min(wb - 1)))
        {
            return SquarePlan::AShr(s as u32);
        }
    }
    let plain_terms = build_diags(rows, w, valid_bits);
    let plain_len = plain_terms.len();
    let mut best = SquarePlan::Diags {
        pre: None,
        terms: plain_terms,
    };
    if valid_bits == wb && best.cost() > 1 {
        if wb >= 16 && wb.is_multiple_of(8) {
            let bs_terms = build_diags(&permute_cols_bswap(rows, wb), w, wb);
            if bs_terms.len() < plain_len || (wb > 16 && bs_terms.len() == 1) {
                let bs = SquarePlan::Diags {
                    pre: Some(UnOp::Bswap),
                    terms: bs_terms,
                };
                if bs.cost() < best.cost() {
                    best = bs;
                }
            }
        }
        if best.cost() > 1 && wb >= 2 {
            let br_terms = build_diags(&permute_cols_bitrev(rows, wb), w, wb);
            if br_terms.len() < plain_len || br_terms.len() == 1 {
                let br = SquarePlan::Diags {
                    pre: Some(UnOp::BitRev),
                    terms: br_terms,
                };
                if br.cost() < best.cost() {
                    best = br;
                }
            }
        }
    }
    best
}

enum AtomPlan {
    Same(u32, SquarePlan),
    Zext(u32, SquarePlan),
    Sext(u32),
    Slices(Vec<(u32, u16, u16, bool, SquarePlan)>),
}

impl AtomPlan {
    fn cost(&self) -> u32 {
        match self {
            AtomPlan::Same(_, p) => p.cost(),
            AtomPlan::Zext(_, p) => 1 + p.cost(),
            AtomPlan::Sext(_) => 1,
            AtomPlan::Slices(chunks) => {
                let sum: u32 = chunks
                    .iter()
                    .map(|(_, _, _, need_zext, p)| 1 + u32::from(*need_zext) + p.cost())
                    .sum();
                sum + (chunks.len() as u32).saturating_sub(1)
            }
        }
    }

    fn emit(&self, cx: &mut Context, w: Width) -> Result<u32, crate::Error> {
        let wb = w.bits();
        match self {
            AtomPlan::Same(x, p) => p.emit(cx, *x, w),
            AtomPlan::Zext(x, p) => {
                let z = cx.c_zext(*x, wb)?;
                p.emit(cx, z, w)
            }
            AtomPlan::Sext(x) => cx.c_sext(*x, wb),
            AtomPlan::Slices(chunks) => {
                let mut acc: Option<u32> = None;
                for (x, lo, len, need_zext, p) in chunks {
                    let s = cx.c_extract(*x, *lo, *len)?;
                    let base = if *need_zext { cx.c_zext(s, wb)? } else { s };
                    let e = p.emit(cx, base, w)?;
                    acc = Some(match acc {
                        None => e,
                        Some(a) => cx.c_bin(BinOp::Xor, a, e)?,
                    });
                }
                Ok(acc.expect("non-empty slices"))
            }
        }
    }
}

fn shift_cols_right(rows: &[Row], base: usize, len: usize) -> Rows {
    rows.iter()
        .map(|r| {
            let mut out = ZERO_ROW;
            for j in 0..len {
                if row_bit(r, base + j) {
                    row_set(&mut out, j);
                }
            }
            out
        })
        .collect()
}

fn col_bounds(rows: &[Row], wx: usize) -> Option<(usize, usize)> {
    let (mut lo, mut hi) = (wx, 0usize);
    for r in rows {
        if row_is_zero(r) {
            continue;
        }
        for j in 0..wx {
            if row_bit(r, j) {
                lo = lo.min(j);
                hi = hi.max(j);
            }
        }
    }
    (lo <= hi).then_some((lo, hi))
}

fn plan_atom(x: u32, wx: usize, rows: &[Row], w: Width) -> Option<AtomPlan> {
    let wb = usize::from(w.bits());
    let (lo_col, hi_col) = col_bounds(rows, wx)?;
    if wx == wb {
        return Some(AtomPlan::Same(x, plan_square(rows, w, wb)));
    }
    if wx < wb {
        // Exact `sext<wb>(x)`: low `wx` rows are identity and high rows all read `wx - 1`.
        if (0..wx).all(|i| is_unit_row(&rows[i], i))
            && (wx..wb).all(|i| is_unit_row(&rows[i], wx - 1))
        {
            return Some(AtomPlan::Sext(x));
        }
        return Some(AtomPlan::Zext(x, plan_square(rows, w, wx)));
    }
    // `wx > wb`: if every used column fits in one `wb`-bit slice, extract once at width `wb`.
    if hi_col - lo_col < wb {
        let base = lo_col.min(wx - wb);
        let shifted = shift_cols_right(rows, base, wb);
        return Some(AtomPlan::Slices(vec![(
            x,
            base as u16,
            wb as u16,
            false,
            plan_square(&shifted, w, wb),
        )]));
    }
    // Otherwise partition `[0..wx)` into chunks of width `<= wb`.
    let mut chunks = Vec::new();
    let mut start = 0usize;
    while start < wx {
        let len = (wx - start).min(wb);
        let sub = shift_cols_right(rows, start, len);
        if sub.iter().any(|r| !row_is_zero(r)) {
            let need_zext = len < wb;
            chunks.push((
                x,
                start as u16,
                len as u16,
                need_zext,
                plan_square(&sub, w, len),
            ));
        }
        start += len;
    }
    (!chunks.is_empty()).then_some(AtomPlan::Slices(chunks))
}

/// The xor pass's GF(2)-affine canonicalizer at `n`, if it applies.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Option<Step>, Stop> {
    let w = cx.width_of(n);
    if w.bits() == 0 || w.bits() > gf2::MAX_BITS || !can_root(cx, n) {
        return Ok(None);
    }
    let sum = summary_of(r, cx, n);
    if !sum.moves || sum.ops < 2 || sum.bloom.count_ones() as usize > MAX_ATOMS {
        return Ok(None);
    }
    let Some((atoms, nodes)) = collect_region(cx, n) else {
        return Ok(None);
    };
    r.meter.charge(
        Counter::PassWork,
        (nodes.len() * atoms.len().max(1) * 3) as u64,
    )?;
    let Some(aff) = gf2::affine(cx, &atoms, &nodes) else {
        return Ok(None);
    };
    let mut plans: Vec<AtomPlan> = Vec::new();
    for (idx, &x) in atoms.iter().enumerate() {
        if let Some(rows) = &aff.mats[idx]
            && let Some(p) = plan_atom(x, usize::from(cx.wid(x)), rows, w)
        {
            plans.push(p);
        }
    }
    let konst_cost = if plans.is_empty() {
        1
    } else if aff.konst.is_zero() {
        0
    } else if aff.konst.is_ones() {
        1
    } else {
        2
    };
    let body_cost: u32 = plans.iter().map(AtomPlan::cost).sum();
    let joins = (plans.len() as u32).saturating_sub(1);
    let estimate = body_cost + joins + konst_cost;
    // Constant collapse (`plans.is_empty()`) always commits; otherwise pre-reject when clearly
    // larger than everything the region could free.
    if !plans.is_empty() {
        if estimate >= 2 * nodes.len() as u32 {
            return Ok(None);
        }
        if let Some(f) = worth_building(r, cx, n, &atoms, estimate)? {
            r.stats
                .passes
                .entry(PassKind::Xor.name())
                .or_default()
                .rejected_cost += 1;
            return Ok(Some(Step::Normal(f)));
        }
    }
    let before = cx.len() as u32;
    let konst = aff.konst;
    let e = r.build(cx, |cx| {
        let mut acc: Option<u32> = None;
        for p in &plans {
            let t = p.emit(cx, w)?;
            acc = Some(match acc {
                None => t,
                Some(a) => cx.c_bin(BinOp::Xor, a, t)?,
            });
        }
        let Some(body) = acc else {
            return cx.mk_const(&konst);
        };
        if konst.is_zero() {
            Ok(body)
        } else if konst.is_ones() {
            cx.c_un(UnOp::Not, body)
        } else {
            let k = cx.mk_const(&konst)?;
            cx.c_bin(BinOp::Xor, body, k)
        }
    })?;
    Ok(Some(finish(
        r,
        cx,
        PassKind::Xor,
        n,
        e,
        before,
        &atoms,
        Fin::FINAL,
    )?))
}

/// Scratch state kept across a single `Runner` call.
#[derive(Default)]
pub(crate) struct State {
    pub(crate) summaries: Vec<Summary>,
    pub(crate) stack: Vec<(u32, bool)>,
}
