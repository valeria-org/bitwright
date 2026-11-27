//! Polynomial equality and vanishing-ideal canonicalization (called by the compares pass, sweep
//! relation checks, and whole-DAG polynomial canonicalization): expressions built from `+ − * neg ~`,
//! left shifts by constants, bitwise OR/XOR with constants, slices, extensions, and shuffles over a
//! few leaves are expanded into sums of monomials modulo `2^W` and reduced modulo the 2-adic
//! Smarandache–Kempner–Carlitz falling-factorial null ideal (`2^(W − Σ(eᵢ·tzᵢ + v₂(eᵢ!))) · Π (xᵢ)_{eᵢ,2^{tzᵢ}} ≡ 0`).
//! Equal polynomial functions over `Z/2^W` (including vanishing polynomials such as `2^(W−1)·(x² + x)`
//! and `2^(W−3)·x(x−1)(x−2)(x−3)`) reduce to identical normal forms across widths `1..=512`.

use super::{Runner, Stop};
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::BinOp;
use crate::{BitVec, Width};

/// The most leaves per polynomial width.
const MAX_LEAVES: usize = 24;

/// The most monomials a polynomial keeps.
const MAX_TERMS: usize = 128;

/// The most degree per leaf.
const MAX_DEGREE: u8 = 6;

/// Maximum recursive expansion steps per `equal` call.
const MAX_STEPS: u32 = 512;

/// A monomial: the exponent of each leaf.
type Mono = [u8; MAX_LEAVES];

/// A polynomial: monomials with nonzero coefficients, sorted.
type Poly = Vec<(Mono, BitVec)>;

/// Canonical leaf identity at a given modulus width `mod_w`.
#[derive(Clone, PartialEq, Eq)]
enum LeafKey {
    /// An unexpanded node (mod `2^mod_w`).
    Node(u32),
    /// Contiguous bit slice `extract<lo, len>(src)` (`len > 0`), zero-extended to `mod_w`.
    Slice { src: u32, lo: u16, len: u16 },
    /// `base & mask` (mod `2^mod_w`) for multi-run masks, with `0 < mask < 2^mod_w - 1`.
    Masked(u32, BitVec),
    /// A zero-extended narrow polynomial `zext(p)` of width `k < mod_w`, unifying
    /// `zext<W>(P_k)` with `P_W & ((1 << k) - 1)` when both have the same mod-`2^k` polynomial.
    LowPoly(u16, Poly),
}

/// Shared leaf tables per modulus width so both sides assign identical indices to matching leaves.
#[derive(Default)]
struct LeafTables {
    by_width: Vec<(u16, Vec<LeafKey>)>,
}

impl LeafTables {
    fn intern(&mut self, mod_w: u16, key: LeafKey) -> Option<usize> {
        let table = match self.by_width.iter_mut().find(|(w, _)| *w == mod_w) {
            Some((_, t)) => t,
            None => {
                self.by_width.push((mod_w, Vec::new()));
                &mut self.by_width.last_mut()?.1
            }
        };
        if let Some(i) = table.iter().position(|k| *k == key) {
            return Some(i);
        }
        if table.len() >= MAX_LEAVES {
            return None;
        }
        table.push(key);
        Some(table.len() - 1)
    }
}

fn resize_bv(v: &BitVec, w: Width) -> BitVec {
    match v.width().bits().cmp(&w.bits()) {
        core::cmp::Ordering::Equal => *v,
        core::cmp::Ordering::Less => v.zext(w).unwrap_or_else(|_| BitVec::zero(w)),
        core::cmp::Ordering::Greater => v.trunc(w).unwrap_or_else(|_| BitVec::zero(w)),
    }
}

fn leaf_poly(tables: &mut LeafTables, mod_w: Width, key: LeafKey) -> Option<Poly> {
    let i = tables.intern(mod_w.bits(), key)?;
    let mut m = [0u8; MAX_LEAVES];
    m[i] = 1;
    Some(vec![(m, BitVec::one(mod_w))])
}

/// Guaranteed 2-adic valuation (trailing zero bits) of every value represented by `key`.
fn leaf_tz(cx: &Context, mod_w: Width, key: &LeafKey) -> u32 {
    let bits = u32::from(mod_w.bits());
    match key {
        LeafKey::Masked(_, mask) => {
            if mask.is_zero() {
                bits
            } else {
                crate::facts::known::trailing_zeros(mask).min(bits)
            }
        }
        LeafKey::LowPoly(_, sub) => sub
            .iter()
            .map(|(_, c)| crate::facts::known::trailing_zeros(c))
            .min()
            .unwrap_or(bits),
        LeafKey::Node(id) => {
            let m = resize_bv(&possible_ones_bv(cx, *id, 3), mod_w);
            if m.is_zero() {
                bits
            } else {
                crate::facts::known::trailing_zeros(&m).min(bits)
            }
        }
        LeafKey::Slice { src, lo, len } => {
            let p = crate::facts::known::bv_lshr(&possible_ones_bv(cx, *src, 3), u32::from(*lo));
            let keep = crate::facts::known::low_mask(p.width(), u32::from(*len));
            let m = crate::facts::known::bv_and(&p, &keep);
            if m.is_zero() {
                bits
            } else {
                crate::facts::known::trailing_zeros(&m).min(bits)
            }
        }
    }
}

/// Signed Stirling numbers of the first kind `s(e, j)` for `0 <= e, j <= MAX_DEGREE` (`6`),
/// satisfying `(u)_e = u(u - 1)...(u - e + 1) = Σ_{j=1}^e s(e, j) · u^j`.
const STIRLING1: [[i64; 7]; 7] = [
    [1, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0],
    [0, -1, 1, 0, 0, 0, 0],
    [0, 2, -3, 1, 0, 0, 0],
    [0, -6, 11, -6, 1, 0, 0],
    [0, 24, -50, 35, -10, 1, 0],
    [0, -120, 274, -225, 85, -15, 1],
];

/// 2-adic valuation `v_2(e!)` for `0 <= e <= MAX_DEGREE` (`6`).
const V2_FACT: [u32; 7] = [0, 0, 1, 1, 3, 3, 4];

/// Canonical 2-adic & falling-factorial null-ideal reduction over `Z/2^bits`:
/// For each leaf `x_i = 2^{t_i} · u_i` (`t_i = tz(leaf_i)`), the `2^{t_i}`-stepped falling
/// factorial `Π_{r=0}^{e_i - 1} (x_i - r·2^{t_i}) = 2^{e_i·t_i} · (u_i)_{e_i}` has guaranteed
/// 2-adic valuation `e_i·t_i + v_2(e_i!)`. Reducing from highest total degree down brings every
/// coefficient into `[0, 2^{max(0, bits - Σ_i (e_i·t_i + v_2(e_i!)))})`, pushing high-bit
/// multiples into lower-degree monomials via `STIRLING1`.
fn reduce_2adic(cx: &Context, tables: &LeafTables, mod_w: Width, p: &mut Poly) {
    if p.is_empty() {
        return;
    }
    let bits = u32::from(mod_w.bits());
    let mut tzs = [0u32; MAX_LEAVES];
    let mut any_tz = false;
    if let Some((_, keys)) = tables.by_width.iter().find(|(w, _)| *w == mod_w.bits()) {
        for (i, k) in keys.iter().enumerate() {
            let tz = leaf_tz(cx, mod_w, k);
            tzs[i] = tz;
            any_tz |= tz > 0;
        }
    }
    let any_higher = p.iter().any(|(m, _)| m.iter().any(|&e| e >= 2));
    if !any_tz && !any_higher {
        return;
    }
    let mono_deg = |m: &Mono| -> u32 { m.iter().map(|&e| u32::from(e)).sum() };
    let top_deg = p.iter().map(|(m, _)| mono_deg(m)).max().unwrap_or(0);
    let mut moves: Vec<(Vec<(usize, u8)>, BitVec)> = Vec::new();

    for d in (1..=top_deg).rev() {
        let cur_len = p.len();
        for (m, c) in p.iter_mut() {
            if c.is_zero() || mono_deg(m) != d {
                continue;
            }
            let mut tau = 0u32;
            let mut v_fact = 0u32;
            for (i, &e) in m.iter().enumerate() {
                if e != 0 {
                    tau = tau.saturating_add(u32::from(e).saturating_mul(tzs[i]));
                    v_fact = v_fact.saturating_add(V2_FACT[usize::from(e)]);
                }
            }
            if tau >= bits {
                *c = BitVec::zero(mod_w);
                continue;
            }
            let m1 = bits - tau;
            let c1 = if m1 < bits {
                crate::facts::known::bv_and(c, &crate::facts::known::low_mask(mod_w, m1))
            } else {
                *c
            };
            if v_fact == 0 || c1.is_zero() {
                *c = c1;
                continue;
            }
            let m2 = m1.saturating_sub(v_fact);
            let r = if m2 == 0 {
                BitVec::zero(mod_w)
            } else {
                crate::facts::known::bv_and(&c1, &crate::facts::known::low_mask(mod_w, m2))
            };
            let moved = BitVec::bin_unchecked(BinOp::Sub, &c1, &r);
            if moved.is_zero() {
                *c = r;
                continue;
            }
            let active: Vec<(usize, u8)> = m
                .iter()
                .copied()
                .enumerate()
                .filter(|&(_, e)| e > 0)
                .collect();
            let combos = active
                .iter()
                .fold(1usize, |acc, &(_, e)| acc.saturating_mul(usize::from(e)));
            if combos <= 64 && cur_len.saturating_add(combos) <= MAX_TERMS * 2 {
                *c = r;
                moves.push((active, moved));
            } else {
                *c = c1;
            }
        }
        p.retain(|(_, c)| !c.is_zero());

        for (active, moved) in moves.drain(..) {
            let neg_moved = BitVec::un_unchecked(crate::UnOp::Neg, &moved);
            let mut idx: Vec<u8> = vec![1; active.len()];
            loop {
                let is_top = idx.iter().zip(&active).all(|(&j, &(_, e))| j == e);
                if !is_top {
                    let mut coef = neg_moved;
                    let mut mono = [0u8; MAX_LEAVES];
                    let mut vanished = false;
                    for (k, &(leaf_i, e_k)) in active.iter().enumerate() {
                        let j_k = idx[k];
                        mono[leaf_i] = j_k;
                        let sh = u32::from(e_k - j_k).saturating_mul(tzs[leaf_i]);
                        if sh >= bits {
                            vanished = true;
                            break;
                        }
                        let st_bv = BitVec::wrapping_from_i128(
                            mod_w,
                            i128::from(STIRLING1[usize::from(e_k)][usize::from(j_k)]),
                        );
                        coef = BitVec::bin_unchecked(BinOp::Mul, &coef, &st_bv);
                        if sh > 0 {
                            coef = crate::facts::known::bv_shl(&coef, sh);
                        }
                        if coef.is_zero() {
                            vanished = true;
                            break;
                        }
                    }
                    if !vanished && !coef.is_zero() {
                        match p.binary_search_by(|(k, _)| k.cmp(&mono)) {
                            Ok(pos) => {
                                p[pos].1 = BitVec::bin_unchecked(BinOp::Add, &p[pos].1, &coef);
                            }
                            Err(pos) => p.insert(pos, (mono, coef)),
                        }
                    }
                }
                let mut k = 0;
                while k < idx.len() {
                    if idx[k] < active[k].1 {
                        idx[k] += 1;
                        break;
                    }
                    idx[k] = 1;
                    k += 1;
                }
                if k == idx.len() {
                    break;
                }
            }
            p.retain(|(_, c)| !c.is_zero());
        }
    }
}

fn add(a: &Poly, b: &Poly, sub: bool) -> Poly {
    let mut out: Poly = a.clone();
    for (m, c) in b {
        let c = if sub {
            BitVec::apply_un(crate::UnOp::Neg, c).unwrap_or(*c)
        } else {
            *c
        };
        match out.binary_search_by(|(k, _)| k.cmp(m)) {
            Ok(i) => {
                out[i].1 = BitVec::apply_bin(BinOp::Add, &out[i].1, &c).unwrap_or(c);
            }
            Err(i) => out.insert(i, (*m, c)),
        }
    }
    out.retain(|(_, c)| !c.is_zero());
    out
}

fn mul(a: &Poly, b: &Poly) -> Option<Poly> {
    let mut out: Poly = Vec::new();
    for (ma, ca) in a {
        for (mb, cb) in b {
            let mut m = [0u8; MAX_LEAVES];
            for i in 0..MAX_LEAVES {
                m[i] = ma[i].checked_add(mb[i]).filter(|&d| d <= MAX_DEGREE)?;
            }
            let c = BitVec::apply_bin(BinOp::Mul, ca, cb).ok()?;
            out = add(&out, &vec![(m, c)], false);
            if out.len() > MAX_TERMS {
                return None;
            }
        }
    }
    Some(out)
}

/// Sound over-approximation of bits that may be 1 in `x` across all widths `1..=512`.
fn possible_ones_bv(cx: &Context, x: u32, depth: u8) -> BitVec {
    let w = cx.width_of(x);
    let full = BitVec::ones(w);
    if depth == 0 {
        return full;
    }
    let n = cx.node(x);
    match n.op {
        OpCode::Const => cx.const_val(x).unwrap_or(full),
        OpCode::Zext => resize_bv(&possible_ones_bv(cx, n.a, depth - 1), w),
        OpCode::Extract => {
            let p = crate::facts::known::bv_lshr(&possible_ones_bv(cx, n.a, depth - 1), n.b);
            resize_bv(&p, w)
        }
        OpCode::Concat => {
            let lo_w = u32::from(cx.wid(n.b));
            let hi = crate::facts::known::bv_shl(
                &resize_bv(&possible_ones_bv(cx, n.a, depth - 1), w),
                lo_w,
            );
            let lo = resize_bv(&possible_ones_bv(cx, n.b, depth - 1), w);
            crate::facts::known::bv_or(&hi, &lo)
        }
        OpCode::And => crate::facts::known::bv_and(
            &possible_ones_bv(cx, n.a, depth - 1),
            &possible_ones_bv(cx, n.b, depth - 1),
        ),
        OpCode::Or | OpCode::Xor => crate::facts::known::bv_or(
            &possible_ones_bv(cx, n.a, depth - 1),
            &possible_ones_bv(cx, n.b, depth - 1),
        ),
        OpCode::Shl => match cx.const_val(n.b).and_then(|v| v.to_u64()) {
            Some(s) if s < u64::from(w.bits()) => {
                crate::facts::known::bv_shl(&possible_ones_bv(cx, n.a, depth - 1), s as u32)
            }
            Some(_) => BitVec::zero(w),
            None => full,
        },
        OpCode::LShr => match cx.const_val(n.b).and_then(|v| v.to_u64()) {
            Some(s) if s < u64::from(w.bits()) => {
                crate::facts::known::bv_lshr(&possible_ones_bv(cx, n.a, depth - 1), s as u32)
            }
            Some(_) => BitVec::zero(w),
            None => full,
        },
        OpCode::Add => {
            let ma = possible_ones_bv(cx, n.a, depth - 1);
            let mb = possible_ones_bv(cx, n.b, depth - 1);
            if crate::facts::known::bv_and(&ma, &mb).is_zero() {
                crate::facts::known::bv_or(&ma, &mb)
            } else if let Some(c) = cx.const_val(n.a)
                && crate::facts::known::count_ones(&mb) == 1
            {
                crate::facts::known::bv_or(&c, &BitVec::bin_unchecked(BinOp::Add, &c, &mb))
            } else if let Some(c) = cx.const_val(n.b)
                && crate::facts::known::count_ones(&ma) == 1
            {
                crate::facts::known::bv_or(&c, &BitVec::bin_unchecked(BinOp::Add, &c, &ma))
            } else {
                full
            }
        }
        OpCode::Sub => {
            if let Some(c) = cx.const_val(n.a) {
                let mb = possible_ones_bv(cx, n.b, depth - 1);
                if crate::facts::known::bv_and(&mb, &crate::facts::known::bv_not(&c)).is_zero() {
                    c
                } else if crate::facts::known::count_ones(&mb) == 1 {
                    crate::facts::known::bv_or(&c, &BitVec::bin_unchecked(BinOp::Sub, &c, &mb))
                } else {
                    full
                }
            } else if let Some(c) = cx.const_val(n.b) {
                let ma = possible_ones_bv(cx, n.a, depth - 1);
                if crate::facts::known::count_ones(&ma) == 1 {
                    let neg_c = BitVec::un_unchecked(crate::UnOp::Neg, &c);
                    crate::facts::known::bv_or(&neg_c, &BitVec::bin_unchecked(BinOp::Sub, &ma, &c))
                } else {
                    full
                }
            } else {
                full
            }
        }
        _ => full,
    }
}

/// Sound under-approximation of bits guaranteed to be 1 in `x` across all widths `1..=512`.
fn guaranteed_ones_bv(cx: &Context, x: u32, depth: u8) -> BitVec {
    let w = cx.width_of(x);
    if depth == 0 {
        return BitVec::zero(w);
    }
    let n = cx.node(x);
    match n.op {
        OpCode::Const => cx.const_val(x).unwrap_or_else(|| BitVec::zero(w)),
        OpCode::Not => crate::facts::known::bv_not(&possible_ones_bv(cx, n.a, depth - 1)),
        OpCode::Zext => resize_bv(&guaranteed_ones_bv(cx, n.a, depth - 1), w),
        OpCode::Extract => {
            let g = crate::facts::known::bv_lshr(&guaranteed_ones_bv(cx, n.a, depth - 1), n.b);
            resize_bv(&g, w)
        }
        OpCode::Concat => {
            let lo_w = u32::from(cx.wid(n.b));
            let hi = crate::facts::known::bv_shl(
                &resize_bv(&guaranteed_ones_bv(cx, n.a, depth - 1), w),
                lo_w,
            );
            let lo = resize_bv(&guaranteed_ones_bv(cx, n.b, depth - 1), w);
            crate::facts::known::bv_or(&hi, &lo)
        }
        OpCode::Or => crate::facts::known::bv_or(
            &guaranteed_ones_bv(cx, n.a, depth - 1),
            &guaranteed_ones_bv(cx, n.b, depth - 1),
        ),
        OpCode::And => crate::facts::known::bv_and(
            &guaranteed_ones_bv(cx, n.a, depth - 1),
            &guaranteed_ones_bv(cx, n.b, depth - 1),
        ),
        _ => BitVec::zero(w),
    }
}

fn single_node_leaf(cx: &Context, tables: &LeafTables, mod_bits: u16, p: &Poly) -> Option<u32> {
    if p.len() != 1 || p[0].1 != BitVec::one(p[0].1.width()) {
        return None;
    }
    let (_, keys) = tables.by_width.iter().find(|(w, _)| *w == mod_bits)?;
    let mut active = None;
    for (idx, &exp) in p[0].0.iter().enumerate() {
        if exp == 1 && active.is_none() {
            active = Some(idx);
        } else if exp != 0 {
            return None;
        }
    }
    match keys.get(active?)? {
        LeafKey::Node(id) if cx.wid(*id) == mod_bits => Some(*id),
        _ => None,
    }
}

/// Evaluates `x` modulo `2^bits` in the canonical falling-factorial polynomial ring when `x`
/// collapses to a constant or to a single existing DAG node leaf (`2^63·(x² + x) + y -> y`).
pub(super) fn fold_vanishing(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    bits: u16,
) -> Result<Option<u32>, Stop> {
    let w_full = cx.wid(x);
    if bits == 0 || bits > w_full {
        return Ok(None);
    }
    let Ok(mod_w) = Width::new(bits) else {
        return Ok(None);
    };
    let mut tables = LeafTables::default();
    let mut memo = IdMap::default();
    let mut steps = 0u32;
    let p_opt = poly_of(cx, x, mod_w, &mut tables, &mut memo, &mut steps);
    r.meter.charge(Counter::PassWork, u64::from(steps))?;
    let Some(p) = p_opt else {
        return Ok(None);
    };
    let out_w = cx.width_of(x);
    if p.is_empty() {
        let zv = BitVec::zero(out_w);
        return r.build(cx, |cx| cx.mk_const(&zv)).map(Some);
    }
    if p.len() == 1 && p[0].0 == [0u8; MAX_LEAVES] {
        let kv = resize_bv(&p[0].1, out_w);
        return r.build(cx, |cx| cx.mk_const(&kv)).map(Some);
    }
    if bits == w_full
        && let Some(leaf_id) = single_node_leaf(cx, &tables, bits, &p)
        && leaf_id != x
    {
        return Ok(Some(leaf_id));
    }
    Ok(None)
}

fn lift_sub_poly(sub: Poly, sub_bits: u16, mod_w: Width, tables: &mut LeafTables) -> Option<Poly> {
    if sub.is_empty() {
        Some(Vec::new())
    } else if sub.len() == 1 && sub[0].0 == [0u8; MAX_LEAVES] {
        let c = resize_bv(&sub[0].1, mod_w);
        Some(vec![([0u8; MAX_LEAVES], c)])
    } else {
        leaf_poly(tables, mod_w, LeafKey::LowPoly(sub_bits, sub))
    }
}

#[allow(clippy::too_many_arguments)]
fn slice_poly(
    cx: &Context,
    src: u32,
    lo: u16,
    len: u16,
    mod_w: Width,
    tables: &mut LeafTables,
    memo: &mut IdMap<(u32, u16), Poly>,
    steps: &mut u32,
) -> Option<Poly> {
    let bits = mod_w.bits();
    let src_w = cx.wid(src);
    if lo == 0 && len >= bits && src_w >= bits {
        return poly_of(cx, src, mod_w, tables, memo, steps);
    }
    if lo == 0
        && len <= src_w
        && matches!(
            cx.node(src).op,
            OpCode::Add
                | OpCode::Sub
                | OpCode::Neg
                | OpCode::Not
                | OpCode::Mul
                | OpCode::Shl
                | OpCode::Or
                | OpCode::Xor
                | OpCode::Concat
        )
        && let Ok(sub_w) = Width::new(len)
        && let Some(sub) = poly_of(cx, src, sub_w, tables, memo, steps)
        && single_node_leaf(cx, tables, len, &sub) != Some(src)
    {
        return lift_sub_poly(sub, len, mod_w, tables);
    }
    if lo > 0
        && lo + len <= src_w
        && matches!(cx.node(src).op, OpCode::Add | OpCode::Sub)
        && let Ok(sub_w) = Width::new(len)
    {
        let sn = cx.node(src);
        let src_wt = cx.width_of(src);
        let low_lo = crate::facts::known::low_mask(src_wt, u32::from(lo));
        let no_carry = if sn.op == OpCode::Add {
            let ma = possible_ones_bv(cx, sn.a, 4);
            let mb = possible_ones_bv(cx, sn.b, 4);
            crate::facts::known::bv_and(&crate::facts::known::bv_and(&ma, &mb), &low_lo).is_zero()
        } else {
            let ga = guaranteed_ones_bv(cx, sn.a, 4);
            let mb = possible_ones_bv(cx, sn.b, 4);
            crate::facts::known::bv_and(
                &crate::facts::known::bv_and(&mb, &crate::facts::known::bv_not(&ga)),
                &low_lo,
            )
            .is_zero()
        };
        if no_carry
            && let (Some(pa), Some(pb)) = (
                slice_poly(cx, sn.a, lo, len, sub_w, tables, memo, steps),
                slice_poly(cx, sn.b, lo, len, sub_w, tables, memo, steps),
            )
        {
            let comb = add(&pa, &pb, sn.op == OpCode::Sub);
            if comb.len() <= MAX_TERMS {
                return lift_sub_poly(comb, len, mod_w, tables);
            }
        }
    }
    if lo == 0 && len == bits && src_w == bits {
        return leaf_poly(tables, mod_w, LeafKey::Node(src));
    }
    leaf_poly(tables, mod_w, LeafKey::Slice { src, lo, len })
}

fn set_mask_range(limbs: &mut [u64; 8], off: u16, len: u16) {
    let start = usize::from(off);
    let end = start + usize::from(len);
    let mut pos = start;
    while pos < end {
        let word = pos / 64;
        let bit = pos % 64;
        let chunk = (end - pos).min(64 - bit);
        let m = if chunk == 64 {
            u64::MAX
        } else {
            ((1u64 << chunk) - 1) << bit
        };
        limbs[word] |= m;
        pos += chunk;
    }
}

/// Decomposes a bit-shaping node `x` modulo `2^mod_w` via canonical bit-provenance runs.
fn try_bit_runs_poly(
    cx: &Context,
    x: u32,
    mod_w: Width,
    tables: &mut LeafTables,
    memo: &mut IdMap<(u32, u16), Poly>,
    steps: &mut u32,
) -> Option<Poly> {
    use super::shuffle::BitRun;
    let bits = mod_w.bits();
    let raw = super::shuffle::bit_runs_of(cx, x, 32)?;
    let mut trunc_runs: Vec<BitRun> = Vec::with_capacity(raw.len());
    let mut rem = bits;
    for r in raw {
        if rem == 0 {
            break;
        }
        match r {
            BitRun::Const { val, len } => {
                let take = len.min(rem);
                trunc_runs.push(BitRun::Const { val, len: take });
                rem -= take;
            }
            BitRun::Slice { src, lo, len, inv } => {
                let take = len.min(rem);
                trunc_runs.push(BitRun::Slice {
                    src,
                    lo,
                    len: take,
                    inv,
                });
                rem -= take;
            }
        }
    }
    if matches!(
        trunc_runs.as_slice(),
        &[BitRun::Slice {
            src,
            lo: 0,
            len,
            inv: false
        }] if src == x && len == bits
    ) {
        return None;
    }

    // Group consecutive repeated 1-bit slices (from `Sext` / `AShr` sign-bit replication) into
    // `(off, weight_runs, BitRun)` entries so replicated sign bits take 1 term instead of `W`.
    enum Piece {
        ConstOne {
            off: u16,
            len: u16,
        },
        Slice {
            off: u16,
            rep: u16,
            src: u32,
            lo: u16,
            len: u16,
            inv: bool,
        },
    }
    let mut pieces: Vec<Piece> = Vec::with_capacity(trunc_runs.len());
    let mut off = 0u16;
    for r in &trunc_runs {
        match *r {
            BitRun::Const { val: false, len } => off += len,
            BitRun::Const { val: true, len } => {
                pieces.push(Piece::ConstOne { off, len });
                off += len;
            }
            BitRun::Slice { src, lo, len, inv } => {
                if len == 1
                    && let Some(Piece::Slice {
                        off: prev_off,
                        rep,
                        src: ps,
                        lo: plo,
                        len: 1,
                        inv: pinv,
                    }) = pieces.last_mut()
                    && *ps == src
                    && *plo == lo
                    && *pinv == inv
                    && *prev_off + *rep == off
                {
                    *rep += 1;
                } else {
                    pieces.push(Piece::Slice {
                        off,
                        rep: 1,
                        src,
                        lo,
                        len,
                        inv,
                    });
                }
                off += len;
            }
        }
    }

    let slice_count = pieces
        .iter()
        .filter(|p| matches!(p, Piece::Slice { .. }))
        .count();

    if slice_count <= 8 {
        let mut acc: Poly = Vec::new();
        let mut const_limbs = [0u64; 8];
        for p in pieces {
            match p {
                Piece::ConstOne { off, len } => set_mask_range(&mut const_limbs, off, len),
                Piece::Slice {
                    off,
                    rep,
                    src,
                    lo,
                    len,
                    inv,
                } => {
                    if rep == 1 && !inv && lo == 0 && off + len == bits && cx.wid(src) >= bits {
                        let sub = poly_of(cx, src, mod_w, tables, memo, steps)?;
                        let scale =
                            crate::facts::known::bv_shl(&BitVec::one(mod_w), u32::from(off));
                        let scaled = mul(&sub, &vec![([0u8; MAX_LEAVES], scale)])?;
                        acc = add(&acc, &scaled, false);
                        if acc.len() > MAX_TERMS {
                            return None;
                        }
                        continue;
                    }
                    let base = slice_poly(cx, src, lo, len, mod_w, tables, memo, steps)?;
                    let weight = if rep > 1 {
                        // `rep` copies of 1-bit slice starting at `off` have weight `(2^rep - 1) << off`.
                        crate::facts::known::bv_shl(
                            &crate::facts::known::low_mask(mod_w, u32::from(rep)),
                            u32::from(off),
                        )
                    } else {
                        crate::facts::known::bv_shl(&BitVec::one(mod_w), u32::from(off))
                    };
                    if inv {
                        let span_bits = if rep > 1 { rep } else { len };
                        set_mask_range(&mut const_limbs, off, span_bits);
                        let scaled = mul(&base, &vec![([0u8; MAX_LEAVES], weight)])?;
                        acc = add(&acc, &scaled, true);
                    } else {
                        let scaled = mul(&base, &vec![([0u8; MAX_LEAVES], weight)])?;
                        acc = add(&acc, &scaled, false);
                    }
                    if acc.len() > MAX_TERMS {
                        return None;
                    }
                }
            }
        }
        let c_bv = BitVec::wrapping_from_limbs(mod_w, &const_limbs);
        if !c_bv.is_zero() {
            acc = add(&acc, &vec![([0u8; MAX_LEAVES], c_bv)], false);
        }
        return (acc.len() <= MAX_TERMS).then_some(acc);
    }

    // Multi-run single-source in-place mask/XOR (`(s & m) ^ c`):
    // `((~s) & neg_mask) == neg_mask - (s & neg_mask)`, so value is
    // `(ones_mask + neg_mask) + Masked(s, pos_mask) - Masked(s, neg_mask)`.
    let mut single_src: Option<u32> = None;
    let mut pos_limbs = [0u64; 8];
    let mut neg_limbs = [0u64; 8];
    let mut one_limbs = [0u64; 8];
    let mut cur_off = 0u16;
    for r in &trunc_runs {
        match *r {
            BitRun::Const { val: false, len } => cur_off += len,
            BitRun::Const { val: true, len } => {
                set_mask_range(&mut one_limbs, cur_off, len);
                cur_off += len;
            }
            BitRun::Slice { src, lo, len, inv } => {
                if lo != cur_off {
                    return None;
                }
                if let Some(prev) = single_src {
                    if prev != src {
                        return None;
                    }
                } else {
                    single_src = Some(src);
                }
                if inv {
                    set_mask_range(&mut neg_limbs, cur_off, len);
                } else {
                    set_mask_range(&mut pos_limbs, cur_off, len);
                }
                cur_off += len;
            }
        }
    }
    let s = single_src?;
    let pos_mask = BitVec::wrapping_from_limbs(mod_w, &pos_limbs);
    let neg_mask = BitVec::wrapping_from_limbs(mod_w, &neg_limbs);
    let one_mask = BitVec::wrapping_from_limbs(mod_w, &one_limbs);
    let bias = BitVec::bin_unchecked(BinOp::Add, &one_mask, &neg_mask);
    let mut acc = if bias.is_zero() {
        Vec::new()
    } else {
        vec![([0u8; MAX_LEAVES], bias)]
    };
    let s_bits = cx.wid(s);
    let mask_term = |m: BitVec,
                     tables: &mut LeafTables,
                     memo: &mut IdMap<(u32, u16), Poly>,
                     steps: &mut u32|
     -> Option<Poly> {
        if m.is_zero() {
            return Some(Vec::new());
        }
        if m.is_ones() && s_bits >= bits {
            return poly_of(cx, s, mod_w, tables, memo, steps);
        }
        if s_bits < bits && m == crate::facts::known::low_mask(mod_w, u32::from(s_bits)) {
            return slice_poly(cx, s, 0, s_bits, mod_w, tables, memo, steps);
        }
        leaf_poly(tables, mod_w, LeafKey::Masked(s, m))
    };
    let pos_p = mask_term(pos_mask, tables, memo, steps)?;
    acc = add(&acc, &pos_p, false);
    let neg_p = mask_term(neg_mask, tables, memo, steps)?;
    acc = add(&acc, &neg_p, true);
    (acc.len() <= MAX_TERMS).then_some(acc)
}

/// The polynomial of `x` modulo `2^mod_w` over `tables`, if it is one within the caps.
fn poly_of(
    cx: &Context,
    x: u32,
    mod_w: Width,
    tables: &mut LeafTables,
    memo: &mut IdMap<(u32, u16), Poly>,
    steps: &mut u32,
) -> Option<Poly> {
    let bits = mod_w.bits();
    if let Some(p) = memo.get(&(x, bits)) {
        return Some(p.clone());
    }
    *steps += 1;
    if *steps > MAX_STEPS {
        return None;
    }
    let node = cx.node(x);
    let p = if let Some(v) = cx.const_val(x) {
        let v = resize_bv(&v, mod_w);
        if v.is_zero() {
            Vec::new()
        } else {
            vec![([0u8; MAX_LEAVES], v)]
        }
    } else {
        match node.op {
            OpCode::Add | OpCode::Sub => {
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                let b = poly_of(cx, node.b, mod_w, tables, memo, steps)?;
                let p = add(&a, &b, node.op == OpCode::Sub);
                (p.len() <= MAX_TERMS).then_some(p)?
            }
            OpCode::Neg => {
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                add(&Vec::new(), &a, true)
            }
            OpCode::Not => {
                // ~a == -a - 1 (mod 2^mod_w)
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                let neg_a = add(&Vec::new(), &a, true);
                let minus_one = vec![([0u8; MAX_LEAVES], BitVec::ones(mod_w))];
                let p = add(&neg_a, &minus_one, false);
                (p.len() <= MAX_TERMS).then_some(p)?
            }
            OpCode::Mul => {
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                let b = poly_of(cx, node.b, mod_w, tables, memo, steps)?;
                mul(&a, &b)?
            }
            OpCode::Shl if cx.const_val(node.b).is_some() => {
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                let s = cx.const_val(node.b)?;
                let Some(sv) = s.to_u64().filter(|&v| v < u64::from(bits)) else {
                    return Some(Vec::new());
                };
                let k = crate::facts::known::bv_shl(&BitVec::one(mod_w), sv as u32);
                mul(&a, &vec![([0u8; MAX_LEAVES], k)])?
            }
            OpCode::Extract if node.b == 0 && node.width >= bits => {
                poly_of(cx, node.a, mod_w, tables, memo, steps)?
            }
            OpCode::Zext if cx.wid(node.a) >= bits => {
                poly_of(cx, node.a, mod_w, tables, memo, steps)?
            }
            OpCode::Or if cx.const_val(node.a).is_none() && cx.const_val(node.b).is_none() => {
                let pa_may = resize_bv(&possible_ones_bv(cx, node.a, 4), mod_w);
                let pb_may = resize_bv(&possible_ones_bv(cx, node.b, 4), mod_w);
                let ga = resize_bv(&guaranteed_ones_bv(cx, node.a, 4), mod_w);
                let gb = resize_bv(&guaranteed_ones_bv(cx, node.b, 4), mod_w);
                if crate::facts::known::bv_and(&pb_may, &crate::facts::known::bv_not(&ga)).is_zero()
                {
                    poly_of(cx, node.a, mod_w, tables, memo, steps)?
                } else if crate::facts::known::bv_and(&pa_may, &crate::facts::known::bv_not(&gb))
                    .is_zero()
                {
                    poly_of(cx, node.b, mod_w, tables, memo, steps)?
                } else if crate::facts::known::bv_and(&pa_may, &pb_may).is_zero() {
                    if let (Some(a), Some(b)) = (
                        poly_of(cx, node.a, mod_w, tables, memo, steps),
                        poly_of(cx, node.b, mod_w, tables, memo, steps),
                    ) {
                        let p = add(&a, &b, false);
                        if p.len() <= MAX_TERMS {
                            p
                        } else if let Some(rp) =
                            try_bit_runs_poly(cx, x, mod_w, tables, memo, steps)
                        {
                            rp
                        } else {
                            leaf_poly(tables, mod_w, LeafKey::Node(x))?
                        }
                    } else if let Some(rp) = try_bit_runs_poly(cx, x, mod_w, tables, memo, steps) {
                        rp
                    } else {
                        leaf_poly(tables, mod_w, LeafKey::Node(x))?
                    }
                } else if let Some(rp) = try_bit_runs_poly(cx, x, mod_w, tables, memo, steps) {
                    rp
                } else {
                    leaf_poly(tables, mod_w, LeafKey::Node(x))?
                }
            }
            OpCode::Xor if cx.const_val(node.a).is_some() || cx.const_val(node.b).is_some() => {
                let (other, cv) = match cx.const_val(node.b) {
                    Some(c) => (node.a, resize_bv(&c, mod_w)),
                    None => (node.b, resize_bv(&cx.const_val(node.a)?, mod_w)),
                };
                let p_may = resize_bv(&possible_ones_bv(cx, other, 4), mod_w);
                if crate::facts::known::bv_and(&p_may, &cv).is_zero() {
                    let base_p = poly_of(cx, other, mod_w, tables, memo, steps)?;
                    let p = add(&base_p, &vec![([0u8; MAX_LEAVES], cv)], false);
                    (p.len() <= MAX_TERMS).then_some(p)?
                } else if crate::facts::known::bv_and(&p_may, &crate::facts::known::bv_not(&cv))
                    .is_zero()
                {
                    let base_p = poly_of(cx, other, mod_w, tables, memo, steps)?;
                    let p = add(&vec![([0u8; MAX_LEAVES], cv)], &base_p, true);
                    (p.len() <= MAX_TERMS).then_some(p)?
                } else if let Some(rp) = try_bit_runs_poly(cx, x, mod_w, tables, memo, steps) {
                    rp
                } else {
                    leaf_poly(tables, mod_w, LeafKey::Node(x))?
                }
            }
            OpCode::Or if cx.const_val(node.a).is_some() || cx.const_val(node.b).is_some() => {
                if let Some(rp) = try_bit_runs_poly(cx, x, mod_w, tables, memo, steps) {
                    rp
                } else {
                    let (other, cv) = match cx.const_val(node.b) {
                        Some(c) => (node.a, resize_bv(&c, mod_w)),
                        None => (node.b, resize_bv(&cx.const_val(node.a)?, mod_w)),
                    };
                    let keep = crate::facts::known::bv_not(&cv);
                    let base_poly = if keep.is_zero() {
                        Vec::new()
                    } else if keep.is_ones() {
                        poly_of(cx, other, mod_w, tables, memo, steps)?
                    } else {
                        leaf_poly(tables, mod_w, LeafKey::Masked(other, keep))?
                    };
                    let p = add(&base_poly, &vec![([0u8; MAX_LEAVES], cv)], false);
                    (p.len() <= MAX_TERMS).then_some(p)?
                }
            }
            OpCode::Concat => {
                if let Some(rp) = try_bit_runs_poly(cx, x, mod_w, tables, memo, steps) {
                    rp
                } else {
                    let lo_bits = cx.wid(node.b);
                    if lo_bits >= bits {
                        poly_of(cx, node.b, mod_w, tables, memo, steps)?
                    } else {
                        let hi_bits = bits - lo_bits;
                        let hi_w = Width::new(hi_bits).ok()?;
                        let lo_w = Width::new(lo_bits).ok()?;
                        if let (Some(hi_sub), Some(lo_sub)) = (
                            poly_of(cx, node.a, hi_w, tables, memo, steps),
                            poly_of(cx, node.b, lo_w, tables, memo, steps),
                        ) && let (Some(hi_lifted), Some(lo_lifted)) = (
                            lift_sub_poly(hi_sub, hi_bits, mod_w, tables),
                            lift_sub_poly(lo_sub, lo_bits, mod_w, tables),
                        ) {
                            let scale = crate::facts::known::bv_shl(
                                &BitVec::one(mod_w),
                                u32::from(lo_bits),
                            );
                            if let Some(hi_scaled) =
                                mul(&hi_lifted, &vec![([0u8; MAX_LEAVES], scale)])
                            {
                                let p = add(&hi_scaled, &lo_lifted, false);
                                if p.len() <= MAX_TERMS {
                                    p
                                } else {
                                    leaf_poly(tables, mod_w, LeafKey::Node(x))?
                                }
                            } else {
                                leaf_poly(tables, mod_w, LeafKey::Node(x))?
                            }
                        } else {
                            leaf_poly(tables, mod_w, LeafKey::Node(x))?
                        }
                    }
                }
            }
            OpCode::Zext
            | OpCode::Sext
            | OpCode::Extract
            | OpCode::And
            | OpCode::Xor
            | OpCode::LShr
            | OpCode::AShr
            | OpCode::RotL
            | OpCode::RotR
            | OpCode::Bswap
            | OpCode::BitRev => {
                if let Some(rp) = try_bit_runs_poly(cx, x, mod_w, tables, memo, steps) {
                    rp
                } else {
                    leaf_poly(tables, mod_w, LeafKey::Node(x))?
                }
            }
            _ => leaf_poly(tables, mod_w, LeafKey::Node(x))?,
        }
    };
    let mut p = p;
    reduce_2adic(cx, tables, mod_w, &mut p);
    memo.insert((x, bits), p.clone());
    Some(p)
}

/// Refines overlapping `Slice` intervals (via cut-points) and overlapping `Masked` bitsets (via
/// Venn-diagram disjoint basis refinement) per shared `src` so split/merged masks and slices unify.
fn refine_equal(
    cx: &Context,
    mod_w: Width,
    tables: &LeafTables,
    pa: &Poly,
    pb: &Poly,
) -> Option<bool> {
    let bits = mod_w.bits();
    let (_, keys) = tables.by_width.iter().find(|(w, _)| *w == bits)?;
    if keys.len() < 2 {
        return None;
    }

    // Collect sources that appear in >= 2 Slice/Masked/Node keys.
    let src_of = |k: &LeafKey| -> Option<u32> {
        match *k {
            LeafKey::Slice { src, .. } | LeafKey::Masked(src, _) => Some(src),
            LeafKey::Node(id) => Some(id),
            LeafKey::LowPoly(..) => None,
        }
    };
    let mut shared_srcs: Vec<u32> = Vec::new();
    for (i, ki) in keys.iter().enumerate() {
        let Some(s) = src_of(ki) else { continue };
        let has_slice_or_mask = matches!(ki, LeafKey::Slice { .. } | LeafKey::Masked(..));
        for kj in &keys[i + 1..] {
            if src_of(kj) == Some(s)
                && (has_slice_or_mask || matches!(kj, LeafKey::Slice { .. } | LeafKey::Masked(..)))
                && !shared_srcs.contains(&s)
            {
                shared_srcs.push(s);
            }
        }
    }
    if shared_srcs.is_empty() {
        return None;
    }

    let mut new_tables = LeafTables::default();
    let mut subst: Vec<Poly> = vec![Vec::new(); keys.len()];
    let mut refined_any = false;

    for &s in &shared_srcs {
        let s_bits = cx.wid(s);
        let has_masked = keys
            .iter()
            .any(|k| matches!(k, LeafKey::Masked(src, _) if *src == s));
        let all_aligned = keys.iter().all(|k| match *k {
            LeafKey::Masked(src, _) if src == s => true,
            LeafKey::Slice { src, lo, .. } if src == s => lo == 0,
            LeafKey::Node(id) if id == s => s_bits <= bits,
            _ => true,
        });

        if has_masked && all_aligned {
            // Venn-diagram disjoint bitmask refinement on `s`.
            let mask_of_key = |k: &LeafKey| -> Option<BitVec> {
                match k {
                    LeafKey::Masked(src, m) if *src == s => Some(*m),
                    LeafKey::Slice { src, lo: 0, len } if *src == s => {
                        Some(crate::facts::known::low_mask(mod_w, u32::from(*len)))
                    }
                    LeafKey::Node(id) if *id == s && s_bits <= bits => {
                        Some(crate::facts::known::low_mask(mod_w, u32::from(s_bits)))
                    }
                    _ => None,
                }
            };
            let mut basis: Vec<BitVec> = Vec::new();
            for k in keys {
                let Some(mut rem) = mask_of_key(k) else {
                    continue;
                };
                let mut next_basis: Vec<BitVec> = Vec::with_capacity(basis.len() + 2);
                for b in basis {
                    let inter = crate::facts::known::bv_and(&b, &rem);
                    if inter.is_zero() {
                        next_basis.push(b);
                    } else {
                        let b_only =
                            crate::facts::known::bv_and(&b, &crate::facts::known::bv_not(&rem));
                        if !b_only.is_zero() {
                            next_basis.push(b_only);
                        }
                        next_basis.push(inter);
                        rem = crate::facts::known::bv_and(&rem, &crate::facts::known::bv_not(&b));
                    }
                }
                if !rem.is_zero() {
                    next_basis.push(rem);
                }
                if next_basis.len() > MAX_LEAVES {
                    return None;
                }
                basis = next_basis;
            }
            for (idx, k) in keys.iter().enumerate() {
                let Some(km) = mask_of_key(k) else { continue };
                let mut sum: Poly = Vec::new();
                let mut parts = 0usize;
                for b in &basis {
                    if !crate::facts::known::bv_and(&km, b).is_zero() {
                        let lp = leaf_poly(&mut new_tables, mod_w, LeafKey::Masked(s, *b))?;
                        sum = add(&sum, &lp, false);
                        parts += 1;
                    }
                }
                refined_any |= parts > 1;
                subst[idx] = sum;
            }
            continue;
        }

        // Interval cut-point refinement on `Slice` / `Node` of `s`.
        let iv_of_key = |k: &LeafKey| -> Option<(u16, u16)> {
            match *k {
                LeafKey::Slice { src, lo, len } if src == s => Some((lo, lo + len)),
                LeafKey::Node(id) if id == s => Some((0, s_bits.min(bits))),
                _ => None,
            }
        };
        let mut cuts: Vec<u16> = Vec::new();
        for k in keys {
            if let Some((a, b)) = iv_of_key(k) {
                cuts.push(a);
                cuts.push(b);
            }
        }
        cuts.sort_unstable();
        cuts.dedup();
        if cuts.len() < 3 || cuts.len() - 1 > MAX_LEAVES {
            continue;
        }
        for (idx, k) in keys.iter().enumerate() {
            let Some((lo, hi)) = iv_of_key(k) else {
                continue;
            };
            let mut sum: Poly = Vec::new();
            let mut parts = 0usize;
            for win in cuts.windows(2) {
                let (c0, c1) = (win[0], win[1]);
                if c0 >= lo && c1 <= hi && c1 > c0 {
                    let lp = leaf_poly(
                        &mut new_tables,
                        mod_w,
                        LeafKey::Slice {
                            src: s,
                            lo: c0,
                            len: c1 - c0,
                        },
                    )?;
                    let shift = u32::from(c0 - lo);
                    let scaled = if shift == 0 {
                        lp
                    } else if shift >= u32::from(bits) {
                        Vec::new()
                    } else {
                        let wv = crate::facts::known::bv_shl(&BitVec::one(mod_w), shift);
                        mul(&lp, &vec![([0u8; MAX_LEAVES], wv)])?
                    };
                    sum = add(&sum, &scaled, false);
                    parts += 1;
                }
            }
            refined_any |= parts > 1;
            subst[idx] = sum;
        }
    }

    if !refined_any {
        return None;
    }
    for (idx, k) in keys.iter().enumerate() {
        if subst[idx].is_empty() {
            subst[idx] = leaf_poly(&mut new_tables, mod_w, k.clone())?;
        }
    }

    let eval_subst = |p: &Poly| -> Option<Poly> {
        let mut out: Poly = Vec::new();
        for (mono, coef) in p {
            let mut term: Poly = vec![([0u8; MAX_LEAVES], *coef)];
            for (i, &exp) in mono.iter().enumerate() {
                if exp == 0 {
                    continue;
                }
                let base = subst.get(i)?;
                for _ in 0..exp {
                    term = mul(&term, base)?;
                }
            }
            out = add(&out, &term, false);
            if out.len() > MAX_TERMS {
                return None;
            }
        }
        reduce_2adic(cx, &new_tables, mod_w, &mut out);
        Some(out)
    };

    let ra = eval_subst(pa)?;
    let rb = eval_subst(pb)?;
    Some(ra == rb)
}

/// Whether `a` and `b` expand to the same polynomial modulo `2^bits` (and at least one has a
/// product, which is what the linear forms do not expand).
pub(super) fn equal_mod(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    a: u32,
    b: u32,
    bits: u16,
) -> Result<bool, Stop> {
    if bits == 0 {
        return Ok(true);
    }
    if cx.wid(a) != cx.wid(b) || bits > cx.wid(a) {
        return Ok(false);
    }
    let has_mul = |x: u32| {
        let mut stack = vec![x];
        let mut seen = 0;
        while let Some(i) = stack.pop() {
            seen += 1;
            if seen > 96 {
                return false;
            }
            let n = cx.node(i);
            if n.op == OpCode::Mul {
                return true;
            }
            if matches!(
                n.op,
                OpCode::Add
                    | OpCode::Sub
                    | OpCode::Neg
                    | OpCode::Not
                    | OpCode::Shl
                    | OpCode::RotL
                    | OpCode::RotR
                    | OpCode::Zext
                    | OpCode::Extract
                    | OpCode::Concat
                    | OpCode::Or
            ) || (matches!(n.op, OpCode::And | OpCode::Xor)
                && (cx.const_val(n.a).is_some() || cx.const_val(n.b).is_some()))
            {
                stack.extend(n.children());
            }
        }
        false
    };
    if !has_mul(a) && !has_mul(b) {
        // Also decide pure linear + bit-shuffle/slice/sext identities that `linear` leaves as
        // distinct atoms (e.g. `(zext<64>(x:8) ^ 0x80) - 0x80 == sext<64>(x:8)` or limb sums).
        let has_bit_view = |x: u32| {
            matches!(
                cx.node(x).op,
                OpCode::Zext
                    | OpCode::Sext
                    | OpCode::Extract
                    | OpCode::Concat
                    | OpCode::Bswap
                    | OpCode::BitRev
                    | OpCode::RotL
                    | OpCode::RotR
                    | OpCode::AShr
                    | OpCode::LShr
            ) || cx.node(x).children().any(|c| {
                matches!(
                    cx.node(c).op,
                    OpCode::Zext
                        | OpCode::Sext
                        | OpCode::Extract
                        | OpCode::Concat
                        | OpCode::Bswap
                        | OpCode::BitRev
                        | OpCode::RotL
                        | OpCode::RotR
                        | OpCode::AShr
                        | OpCode::LShr
                        | OpCode::Xor
                        | OpCode::And
                        | OpCode::Or
                )
            })
        };
        if !has_bit_view(a) && !has_bit_view(b) {
            return Ok(false);
        }
    }
    let Ok(w) = Width::new(bits) else {
        return Ok(false);
    };
    let mut tables = LeafTables::default();
    let mut memo = IdMap::default();
    let mut steps = 0u32;
    let pa = poly_of(cx, a, w, &mut tables, &mut memo, &mut steps);
    let pb = poly_of(cx, b, w, &mut tables, &mut memo, &mut steps);
    r.meter.charge(Counter::PassWork, u64::from(steps))?;
    let (Some(pa), Some(pb)) = (pa, pb) else {
        return Ok(false);
    };
    if pa == pb {
        return Ok(true);
    }
    if let Some(eq) = refine_equal(cx, w, &tables, &pa, &pb) {
        r.meter.charge(Counter::PassWork, 16)?;
        return Ok(eq);
    }
    Ok(false)
}

/// Whether `a` and `b` expand to the same polynomial (and at least one has a product, which is
/// what the linear forms do not expand).
pub(super) fn equal(r: &mut Runner<'_, '_>, cx: &Context, a: u32, b: u32) -> Result<bool, Stop> {
    equal_mod(r, cx, a, b, cx.wid(a))
}

#[cfg(feature = "mba")]
fn poly_hash(w: u16, p: &Poly) -> u64 {
    let mut h = crate::hash::combine(0x706f_6c79, u64::from(w));
    for (m, c) in p {
        for &b in m {
            h = crate::hash::combine(h, u64::from(b));
        }
        for &limb in c.limbs() {
            h = crate::hash::combine(h, limb);
        }
    }
    h
}

/// Bottom-up polynomial subterm canonicalization over `order`: unifies distinct sub-DAGs that
/// expand to the same polynomial (or bitwise complement `-p - 1` when smaller) modulo `2^w`,
/// exposing shared atoms to `cofactors`, `linear_mba`, and `mba`. Commits only when the whole
/// DAG strictly shrinks.
#[cfg(feature = "mba")]
pub(super) fn canonicalize_dag(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    order: &[u32],
) -> Result<Option<u32>, Stop> {
    if !(4..=2048).contains(&order.len()) {
        return Ok(None);
    }
    let budget = r.meter.left_in(|b| b.pass_work) / 8;
    if budget < (order.len() as u64) * 8 {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    let mut tables = LeafTables::default();
    let mut memo: IdMap<(u32, u16), Poly> = IdMap::default();
    let mut buckets: IdMap<u64, Vec<(u16, Poly, u32)>> = IdMap::default();
    let mut to: IdMap<u32, u32> = IdMap::default();
    let mut has_poly_mul: IdMap<u32, ()> = IdMap::default();
    let mut live_nodes: IdMap<u32, ()> = IdMap::default();
    for &id in order {
        live_nodes.insert(id, ());
    }
    let mut total_steps = 0u64;
    let mut merged_any = false;

    for &i in order {
        let node = cx.node(i);
        let mut kids = [0u32; 3];
        let mut changed = false;
        let mut child_mul = false;
        for (k, c) in node.children().enumerate() {
            let mapped = to.get(&c).copied().unwrap_or(c);
            kids[k] = mapped;
            changed |= mapped != c;
            child_mul |= has_poly_mul.contains_key(&mapped);
        }
        let mut cur = if changed {
            r.build(cx, |cx| cx.rebuild(i, kids))?
        } else {
            i
        };
        let mut cn = cx.node(cur);
        if !r.mba.swept.is_empty()
            && cn.op == OpCode::Zext
            && cn.width <= 64
            && cx.wid(cn.a) < cn.width
        {
            let full_w = u64::MAX >> (64 - cn.width);
            for wide in super::casts::find_wide_masked(cx, cn.a, cn.width, full_w, 5) {
                if wide != cur && live_nodes.contains_key(&wide) {
                    cur = wide;
                    cn = cx.node(cur);
                    merged_any = true;
                    break;
                }
            }
        }
        let w = cn.width;
        let op = cn.op;
        let own_mul = op == OpCode::Mul && !cx.is_const(cn.a) && !cx.is_const(cn.b);
        let poly_cone = own_mul
            || (child_mul
                && matches!(
                    op,
                    OpCode::Add
                        | OpCode::Sub
                        | OpCode::Neg
                        | OpCode::Not
                        | OpCode::Mul
                        | OpCode::Shl
                ));
        let indexable = poly_cone
            || matches!(
                op,
                OpCode::Add
                    | OpCode::Sub
                    | OpCode::Neg
                    | OpCode::Not
                    | OpCode::Shl
                    | OpCode::LShr
                    | OpCode::RotL
                    | OpCode::RotR
            );
        if indexable
            && w >= 2
            && cx.const_val(cur).is_none()
            && let Ok(wt) = Width::new(w)
        {
            let mut steps = 0u32;
            let p_opt = poly_of(cx, cur, wt, &mut tables, &mut memo, &mut steps);
            total_steps += u64::from(steps);
            if total_steps > budget {
                break;
            }
            if let Some(p) = p_opt {
                if poly_cone && p.is_empty() {
                    let zv = BitVec::zero(wt);
                    cur = r.build(cx, |cx| cx.mk_const(&zv))?;
                    merged_any = true;
                } else if poly_cone && p.len() == 1 && p[0].0 == [0u8; MAX_LEAVES] {
                    let kv = p[0].1;
                    cur = r.build(cx, |cx| cx.mk_const(&kv))?;
                    merged_any = true;
                } else if poly_cone
                    && let Some(leaf_id) = single_node_leaf(cx, &tables, w, &p)
                    && leaf_id != cur
                    && live_nodes.contains_key(&leaf_id)
                {
                    cur = leaf_id;
                    merged_any = true;
                } else {
                    let h = poly_hash(w, &p);
                    let found = buckets
                        .get(&h)
                        .and_then(|v| v.iter().find(|(bw, bp, _)| *bw == w && *bp == p))
                        .map(|&(_, _, rep)| rep);
                    if let Some(rep) = found {
                        if poly_cone
                            && rep != cur
                            && cx.meta[rep as usize].tree
                                <= cx.meta[cur as usize]
                                    .tree
                                    .saturating_mul(2)
                                    .saturating_add(4)
                        {
                            cur = rep;
                            merged_any = true;
                        }
                    } else {
                        // Also check bitwise complement `~p == -p - 1`: e.g. `C - a - 1 == ~rep`.
                        let comp = if poly_cone && op != OpCode::Not {
                            let neg_p = add(&Vec::new(), &p, true);
                            let minus_one = vec![([0u8; MAX_LEAVES], BitVec::ones(wt))];
                            let mut cp = add(&neg_p, &minus_one, false);
                            reduce_2adic(cx, &tables, wt, &mut cp);
                            let ch = poly_hash(w, &cp);
                            buckets
                                .get(&ch)
                                .and_then(|v| v.iter().find(|(bw, bp, _)| *bw == w && *bp == cp))
                                .map(|&(_, _, rep)| rep)
                        } else {
                            None
                        };
                        if let Some(rep) = comp
                            && let Some(not_rep) =
                                cx.find(&crate::expr::Node::new(OpCode::Not, w, rep, 0, 0))
                            && cx.meta[not_rep as usize].tree
                                <= cx.meta[cur as usize]
                                    .tree
                                    .saturating_mul(2)
                                    .saturating_add(4)
                        {
                            cur = not_rep;
                            merged_any = true;
                        }
                        let entry = buckets.entry(h).or_default();
                        if entry.len() < 8 {
                            entry.push((w, p, cur));
                        }
                    }
                }
            }
        }
        if poly_cone && cx.const_val(cur).is_none() {
            has_poly_mul.insert(cur, ());
        }
        live_nodes.insert(cur, ());
        to.insert(i, cur);
    }
    r.meter.charge(Counter::PassWork, total_steps)?;
    if !merged_any {
        return Ok(None);
    }
    let Some(&out) = to.get(&root) else {
        return Ok(None);
    };
    if out == root {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    Ok(matches!(
        cx.dag_size(&[cx.handle(out)], order.len() as u32 - 1)
            .map_err(Stop::Error)?,
        crate::expr::Bounded::Exact(_)
    )
    .then_some(out))
}

#[cfg(test)]
mod tests {
    use crate::engine::{Engine, Run, Strategy};
    use crate::{Context, ParseOptions, Width};

    fn simplifies_to_true(expr: &str) -> bool {
        let mut cx = Context::new();
        let e = cx.parse(expr, &ParseOptions::width(Width::W64)).unwrap();
        let eng = Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap().roots[0].expr;
        cx.as_const(out).unwrap().is_some_and(|v| !v.is_zero())
    }

    #[test]
    fn poly_handles_not_or_const_and_narrow_trunc_zext() {
        // ~y * x + x == -y * x
        assert!(simplifies_to_true("~y * x + x == -y * x"));
        // x | c == (x & ~c) + c inside a narrow 32-bit zext/trunc product
        assert!(simplifies_to_true(
            "zext<64>(trunc<32>((zext<64>(trunc<32>(x) | -18689) * 0x9940dd132333686b) * (a + b)) * 0xb7326e10) \
             == ((a + b) * ((x & 18688) * 0x2bfa80b0 + 0x65534f50) & 0xffffffff)"
        ));
        // Partial-width mod-2^57 polynomial equality with rotl decomposition and subsumed Or
        assert!(simplifies_to_true(
            "let r = rotl(x, 6); let lo = r & 63; \
             extract<56, 1>(y + r + 0x35f9c8925e0c9045 + (z + 0xca06376da1f36fba) * lo) \
             == extract<56, 1>(z * lo + y + x * 0x7e72249783241180 - r * 0x35f9c8925e0c9045 + 0x35f9c8925e0c9045)"
        ));
        // Subsumed Or: ~(x << 6) | (x >>u 58) == ~(x << 6)
        assert!(simplifies_to_true(
            "(~(x << 6) | (x >>u 58)) * y + (rotl(x, 6)) * y == ((x >>u 58) - 1) * y"
        ));
        // DAG polynomial canonicalization unifies equivalent and complemented subterms across bitwise ops
        assert!(simplifies_to_true(
            "let p1 = (x + y) * (x + y); let p2 = x * x + 2 * x * y + y * y; \
             ((p1 ^ z) & 0xff) == ((p2 ^ z) & 0xff)"
        ));
        assert!(simplifies_to_true(
            "let p1 = x * y + z; let p2 = x * (-y) - z - 1; \
             ((p1 & w) ^ p1) == ((~p2 & w) ^ ~p2)"
        ));
        assert!(simplifies_to_true(
            "let v0 = zext<64>(d:32) & 0xc4ca4796; \
             let v1 = concat(zext<62>(~(trunc<1>(a:64) ^ extract<3, 1>(a))), 0:2); \
             let v2 = (a & 128 | b:64 & 0x3c7300 | v1) + 0x5e124156224aa1e7; \
             let v3 = v2 >>u 4; \
             let v4 = v1 * 0x3000000000000000; \
             let v5 = rotl(v2, 60); \
             let v6 = v4 + 0x8fffffffffffffff; \
             let v7 = v5 * 0x110a53cdc4dd8bdd; \
             ((v0 + v3) * 0x110a53cdc4dd8bdd + 0x37309649008bcd8 - v4 + 0x5f27cce5e9fd7e9c) * v5 \
             + v6 * (v7 + v0 * 0x40e947a1b54bcc4d + 0x1eede61ec3450e29) \
             + (v6 + v5) * 0x40e947a1b54bcc4d * (v0 ^ 0xfffd7d57e6caf79e) \
             + v4 + 0x9c1d50602ced70af \
             + (v0 * 0x2fdef3d3f06e4070 - v7 + 0x31401341e12eede4) * v3 == v5"
        ));
    }

    #[test]
    fn poly_rejects_unequal_narrow_and_or_expressions() {
        // Differs in bit 32 (overflows low 32 bits)
        assert!(!simplifies_to_true("zext<64>(trunc<32>(x * y)) == x * y"));
        // Non-disjoint Or is not equal to Add
        assert!(!simplifies_to_true(
            "((x << 5) | (x >>u 58)) * y == ((x << 5) + (x >>u 58)) * y"
        ));
        // Wrong constant in Or decomposition
        assert!(!simplifies_to_true(
            "(x | 0x10) * y == ((x & ~0x10) + 0x20) * y"
        ));
        // Missing cross term 2*x*y in DAG polynomial subterm
        assert!(!simplifies_to_true(
            "let p1 = (x + y) * (x + y); let p2 = x * x + y * y; \
             ((p1 ^ z) & 0xff) == ((p2 ^ z) & 0xff)"
        ));
    }
}
