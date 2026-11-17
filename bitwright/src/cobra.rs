//! CoBRA (Coefficient-Based Reduction of MBA) change-of-basis decomposition for linear and
//! semi-linear Mixed Boolean-Arithmetic polynomials over `Z / 2^P Z`.
//!
//! Given conjunction (Möbius) coefficients `alpha[S]` (`∅ ≠ S ⊆ {0..s-1}`) modulo `2^prec`,
//! iteratively eliminates top-degree monomials against a library of minimal 1-, 2-, and 3-input
//! Boolean basis functions (with `f(0) = 0`) and multi-literal clauses, using lookahead alignment
//! on lower-degree shared subsets so overlapping arbitrary-coefficient terms (`5*(x^y) + 7*(x|z)
//! - 5*(y|z)`) unmix cleanly in `O(k)` basis steps.

use std::sync::OnceLock;

use crate::BitVec;
use crate::engine::pass::bitwise::min_forms;
use crate::ops::{BinOp, UnOp};

/// Maximum atom support handled by dense CoBRA Möbius tables (`2^10 = 1024` subsets).
pub(crate) const MAX_COBRA_ATOMS: usize = 10;

/// Maximum basis terms emitted before bailing out (prevents pathological blowup on random tables).
const MAX_BASIS_TERMS: usize = 48;

/// One Boolean basis element over support indices `0..s` (every variant satisfies `f(0, …, 0) = 0`,
/// except `Not` which wraps an inner `f(0) = 0` basis element after constant trading).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BasisOp {
    /// Single input `x_i`.
    Var(usize),
    /// Minimal 2-input Boolean function (`tt8` in `min_forms()` over `[vars[0], vars[1], 0]`).
    Table2 { vars: [usize; 2], tt8: u8 },
    /// Minimal 3-input Boolean function (`tt8` in `min_forms()` over `vars`).
    Table3 { vars: [usize; 3], tt8: u8 },
    /// Multi-literal conjunction `⋀_k (if neg_mask >> k & 1 == 1 { ~x_{vars[k]} } else { x_{vars[k]} })`
    /// with at least one positive literal (`neg_mask != (1 << vars.len()) - 1`).
    ClauseAnd { vars: Vec<usize>, neg_mask: u16 },
    /// Multi-way disjunction `⋁_k x_{vars[k]}` (`vars.len() >= 4`).
    OrAll { vars: Vec<usize> },
    /// Bitwise complement `~inner` (produced when trading the constant offset against a term).
    Not(Box<BasisOp>),
}

impl BasisOp {
    /// Estimated gate count (excluding leaf atoms).
    pub(crate) fn gate_cost(&self) -> u32 {
        match self {
            BasisOp::Var(_) => 0,
            BasisOp::Table2 { tt8, .. } | BasisOp::Table3 { tt8, .. } => {
                u32::from(min_forms().forms[usize::from(*tt8)].1)
            }
            BasisOp::ClauseAnd { vars, neg_mask } => {
                let ands = (vars.len() as u32).saturating_sub(1);
                let negs = neg_mask.count_ones();
                // Multiple negated inputs fold by De Morgan into `~(a | b | ...)` (`k` gates total).
                ands + negs.min(2)
            }
            BasisOp::OrAll { vars } => (vars.len() as u32).saturating_sub(1),
            BasisOp::Not(inner) => match inner.as_ref() {
                BasisOp::Table2 { tt8, .. } | BasisOp::Table3 { tt8, .. } => {
                    u32::from(min_forms().forms[usize::from(!*tt8)].1)
                }
                _ => inner.gate_cost() + 1,
            },
        }
    }
}

/// Precomputed 2-var and 3-var Boolean basis templates with `f(0) = 0` and non-zero top Möbius.
struct BasisEntry {
    tt8: u8,
    ops: u8,
    mobius: [i8; 8],
}

struct BasisLibrary {
    two: Vec<BasisEntry>,
    three: Vec<BasisEntry>,
}

fn library() -> &'static BasisLibrary {
    static LIB: OnceLock<BasisLibrary> = OnceLock::new();
    LIB.get_or_init(|| {
        let forms = min_forms();
        let mut two = Vec::new();
        for t4 in 1u8..16 {
            if t4 & 1 != 0 {
                continue;
            }
            // Must depend on both input 0 and input 1.
            if (t4 & 0x5) == ((t4 >> 1) & 0x5) || (t4 & 0x3) == ((t4 >> 2) & 0x3) {
                continue;
            }
            let mut m = [0i8; 8];
            for (q, slot) in m.iter_mut().enumerate().take(4) {
                *slot = ((t4 >> q) & 1) as i8;
            }
            for b in 0..2 {
                for q in 0..4usize {
                    if (q >> b) & 1 == 1 {
                        m[q] -= m[q ^ (1 << b)];
                    }
                }
            }
            if m[3] == 0 {
                continue;
            }
            let tt8 = t4 | (t4 << 4);
            let ops = forms.forms[usize::from(tt8)].1;
            two.push(BasisEntry {
                tt8,
                ops,
                mobius: m,
            });
        }

        let mut three = Vec::new();
        for tt8 in 1u8..=254 {
            if tt8 & 1 != 0 {
                continue;
            }
            // Must depend on all three inputs 0, 1, 2.
            if (tt8 & 0x55) == ((tt8 >> 1) & 0x55)
                || (tt8 & 0x33) == ((tt8 >> 2) & 0x33)
                || (tt8 & 0x0F) == ((tt8 >> 4) & 0x0F)
            {
                continue;
            }
            let ops = forms.forms[usize::from(tt8)].1;
            if ops > 4 {
                continue;
            }
            let mut m = [0i8; 8];
            for (q, slot) in m.iter_mut().enumerate() {
                *slot = ((tt8 >> q) & 1) as i8;
            }
            for b in 0..3 {
                for q in 0..8usize {
                    if (q >> b) & 1 == 1 {
                        m[q] -= m[q ^ (1 << b)];
                    }
                }
            }
            if m[7] == 0 {
                continue;
            }
            three.push(BasisEntry {
                tt8,
                ops,
                mobius: m,
            });
        }
        BasisLibrary { two, three }
    })
}

fn low_mask(w: crate::Width, bits: u32) -> BitVec {
    let wb = u32::from(w.bits());
    if bits == 0 {
        BitVec::zero(w)
    } else if bits >= wb {
        BitVec::ones(w)
    } else {
        let mut limbs = [0u64; 8];
        let full = (bits / 64) as usize;
        for slot in limbs.iter_mut().take(full) {
            *slot = u64::MAX;
        }
        let rem = bits % 64;
        if rem > 0 {
            limbs[full] = (1u64 << rem) - 1;
        }
        BitVec::wrapping_from_limbs(w, &limbs)
    }
}

fn single_bit(w: crate::Width, pos: u32) -> BitVec {
    let mut limbs = [0u64; 8];
    if pos < u32::from(w.bits()) {
        limbs[(pos / 64) as usize] = 1u64 << (pos % 64);
    }
    BitVec::wrapping_from_limbs(w, &limbs)
}

fn signed_bv(w: crate::Width, v: i8) -> BitVec {
    if v >= 0 {
        BitVec::wrapping_from_u64(w, v as u64)
    } else {
        BitVec::un_unchecked(UnOp::Neg, &BitVec::wrapping_from_u64(w, (-v) as u64))
    }
}

fn odd_inverse_3(w: crate::Width) -> BitVec {
    let three = BitVec::wrapping_from_u64(w, 3);
    let two = BitVec::wrapping_from_u64(w, 2);
    let mut inv = BitVec::one(w);
    for _ in 0..9 {
        let prod = BitVec::bin_unchecked(BinOp::Mul, &three, &inv);
        let factor = BitVec::bin_unchecked(BinOp::Sub, &two, &prod);
        inv = BitVec::bin_unchecked(BinOp::Mul, &inv, &factor);
    }
    inv
}

fn trailing_zeros(v: &BitVec) -> u32 {
    let wb = u32::from(v.width().bits());
    for (i, &limb) in v.limbs().iter().enumerate() {
        let base = (i as u32) * 64;
        if base >= wb {
            break;
        }
        if limb != 0 {
            return (base + limb.trailing_zeros()).min(wb);
        }
    }
    wb
}

/// Solves `w * lead ≡ target (mod 2^prec)` for nonzero `target` masked to `pmask`.
fn solve_weights(
    w: crate::Width,
    prec: u32,
    pmask: &BitVec,
    target: &BitVec,
    lead: i8,
) -> Vec<BitVec> {
    let abs_lead = lead.unsigned_abs();
    let rhs = if lead < 0 {
        BitVec::bin_unchecked(BinOp::And, &BitVec::un_unchecked(UnOp::Neg, target), pmask)
    } else {
        *target
    };
    match abs_lead {
        1 => vec![rhs],
        3 => {
            let inv3 = odd_inverse_3(w);
            vec![BitVec::bin_unchecked(
                BinOp::And,
                &BitVec::bin_unchecked(BinOp::Mul, &rhs, &inv3),
                pmask,
            )]
        }
        2 => {
            if rhs.bit(0).unwrap_or(false) || prec < 2 {
                return Vec::new();
            }
            let shift1 = BitVec::one(w);
            let w0 = BitVec::bin_unchecked(BinOp::LShr, &rhs, &shift1);
            let hi = single_bit(w, prec - 1);
            vec![w0, BitVec::bin_unchecked(BinOp::Xor, &w0, &hi)]
        }
        4 => {
            if rhs.bit(0).unwrap_or(false) || rhs.bit(1).unwrap_or(false) || prec < 3 {
                return Vec::new();
            }
            let shift2 = BitVec::wrapping_from_u64(w, 2);
            let w0 = BitVec::bin_unchecked(BinOp::LShr, &rhs, &shift2);
            let step = single_bit(w, prec - 2);
            let mut out = Vec::with_capacity(4);
            let mut cur = w0;
            for _ in 0..4 {
                out.push(BitVec::bin_unchecked(BinOp::And, &cur, pmask));
                cur = BitVec::bin_unchecked(BinOp::Add, &cur, &step);
            }
            out
        }
        _ => Vec::new(),
    }
}

fn scale_cost(c: &BitVec, prec: u32, pmask: &BitVec) -> u32 {
    let w = c.width();
    let one = BitVec::one(w);
    if *c == one || *c == *pmask {
        return 0;
    }
    let neg_c = BitVec::bin_unchecked(BinOp::And, &BitVec::un_unchecked(UnOp::Neg, c), pmask);
    for cand in [c, &neg_c] {
        let tz = trailing_zeros(cand);
        if tz > 0 && tz < prec && *cand == single_bit(w, tz) {
            return 1;
        }
    }
    2
}

/// Spends `n` units of `work`; `None` (and nothing left) where it does not cover them.
fn spend(work: &mut u64, n: u64) -> Option<()> {
    match work.checked_sub(n) {
        Some(left) => {
            *work = left;
            Some(())
        }
        None => {
            *work = 0;
            None
        }
    }
}

/// Checks whether a residual coefficient `rem` at subset `sub_q` aligns with any active higher
/// monomial `q2` (`q2` not inside `pivot_q`, `q2 ⊃ sub_q`) so a later CoBRA step will absorb it.
/// Spends a unit of `work` per coefficient it reads; `None` where that runs out.
fn aligns_with_other(
    alpha: &[BitVec],
    pivot_q: usize,
    sub_q: usize,
    rem: &BitVec,
    pmask: &BitVec,
    work: &mut u64,
) -> Option<bool> {
    spend(work, (alpha.len() - sub_q) as u64)?;
    let w = rem.width();
    let neg_rem = BitVec::bin_unchecked(BinOp::And, &BitVec::un_unchecked(UnOp::Neg, rem), pmask);
    let two = BitVec::wrapping_from_u64(w, 2);
    let dbl = BitVec::bin_unchecked(
        BinOp::And,
        &BitVec::bin_unchecked(BinOp::Mul, rem, &two),
        pmask,
    );
    let neg_dbl = BitVec::bin_unchecked(BinOp::And, &BitVec::un_unchecked(UnOp::Neg, &dbl), pmask);
    for (q2, a2) in alpha.iter().enumerate().skip(sub_q + 1) {
        if a2.is_zero() || (q2 & !pivot_q) == 0 || (q2 & sub_q) != sub_q {
            continue;
        }
        if *a2 == *rem || *a2 == neg_rem || *a2 == dbl || *a2 == neg_dbl {
            return Some(true);
        }
    }
    Some(false)
}

/// Decomposes conjunction coefficients `alpha[0 .. 1 << s]` (`alpha[0]` ignored; pass `konst`
/// separately) over `s` atoms (`1 <= s <= MAX_COBRA_ATOMS`) modulo `2^prec`.
///
/// Returns `Some(terms)` with `Σ_k weight_k · op_k ≡ Σ_{q>0} alpha[q] · AND_q (mod 2^prec)`.
///
/// `work` is what it may spend, a unit per coefficient it reads, and is left with what it did
/// not (the caller charges the difference): `None` where it runs out. A pivot over three
/// atoms tries every library entry and weight against the others' coefficients, so a
/// decomposition over ten atoms can read millions of them.
pub(crate) fn decompose(
    s: usize,
    w: crate::Width,
    prec: u32,
    alpha_in: &[BitVec],
    work: &mut u64,
) -> Option<Vec<(BasisOp, BitVec)>> {
    if s == 0 || s > MAX_COBRA_ATOMS || prec == 0 || alpha_in.len() != (1usize << s) {
        return None;
    }
    spend(work, 1 << s)?;
    let pmask = low_mask(w, prec);
    let mut alpha: Vec<BitVec> = alpha_in
        .iter()
        .enumerate()
        .map(|(q, c)| {
            if q == 0 {
                BitVec::zero(w)
            } else {
                BitVec::bin_unchecked(BinOp::And, c, &pmask)
            }
        })
        .collect();

    let mut terms: Vec<(BasisOp, BitVec)> = Vec::new();
    let lib = library();

    loop {
        spend(work, 1 << s)?;
        // Find maximum cardinality among remaining nonzero subsets, breaking ties by fewest
        // trailing zeros (odd coefficients first: unique modular lifts).
        let mut pivot: Option<(u32, u32, usize)> = None;
        for (q, c) in alpha.iter().enumerate().skip(1) {
            if c.is_zero() {
                continue;
            }
            let d = (q as u32).count_ones();
            let tz = trailing_zeros(c);
            let key = (d, u32::MAX - tz, usize::MAX - q);
            if pivot.is_none_or(|best| key > best) {
                pivot = Some(key);
            }
        }
        let Some((d, _, inv_q)) = pivot else {
            break;
        };
        if terms.len() >= MAX_BASIS_TERMS {
            return None;
        }
        let q_star = usize::MAX - inv_q;
        let d_usize = d as usize;

        if d_usize == 1 {
            let v = q_star.trailing_zeros() as usize;
            let weight = alpha[q_star];
            alpha[q_star] = BitVec::zero(w);
            push_term(&mut terms, BasisOp::Var(v), weight, &pmask);
            continue;
        }

        let mut vars = Vec::with_capacity(d_usize);
        for v in 0..s {
            if (q_star >> v) & 1 == 1 {
                vars.push(v);
            }
        }

        if d_usize == 2 || d_usize == 3 {
            let sub_len = 1usize << d_usize;
            let mut idx = [0usize; 8];
            for (u, slot) in idx.iter_mut().enumerate().take(sub_len) {
                let mut gq = 0usize;
                for (bit, &v) in vars.iter().enumerate() {
                    if (u >> bit) & 1 == 1 {
                        gq |= 1 << v;
                    }
                }
                *slot = gq;
            }

            let entries = if d_usize == 2 { &lib.two } else { &lib.three };
            let target = alpha[q_star];
            let full_u = sub_len - 1;
            let mut best: Option<(u32, u8, [i8; 8], BitVec)> = None;

            for entry in entries {
                let lead = entry.mobius[full_u];
                for weight in solve_weights(w, prec, &pmask, &target, lead) {
                    if weight.is_zero() {
                        continue;
                    }
                    spend(work, sub_len as u64)?;
                    let mut rem_cost = 0u32;
                    for u in 1..full_u {
                        let mu = entry.mobius[u];
                        let cur = alpha[idx[u]];
                        let rem = if mu == 0 {
                            cur
                        } else {
                            let delta =
                                BitVec::bin_unchecked(BinOp::Mul, &weight, &signed_bv(w, mu));
                            BitVec::bin_unchecked(
                                BinOp::And,
                                &BitVec::bin_unchecked(BinOp::Sub, &cur, &delta),
                                &pmask,
                            )
                        };
                        if !rem.is_zero()
                            && !aligns_with_other(&alpha, q_star, idx[u], &rem, &pmask, work)?
                        {
                            rem_cost += 2 + ((u as u32).count_ones() - 1);
                        }
                    }
                    let score = u32::from(entry.ops) + scale_cost(&weight, prec, &pmask) + rem_cost;
                    if best.as_ref().is_none_or(|b| score < b.0) {
                        best = Some((score, entry.tt8, entry.mobius, weight));
                    }
                }
            }

            let Some((_, tt8, mob, weight)) = best else {
                // Fallback: raw conjunction `AND_{q_star}`.
                alpha[q_star] = BitVec::zero(w);
                push_term(
                    &mut terms,
                    BasisOp::ClauseAnd { vars, neg_mask: 0 },
                    target,
                    &pmask,
                );
                continue;
            };

            for u in 1..sub_len {
                let mu = mob[u];
                if mu == 0 {
                    continue;
                }
                let delta = BitVec::bin_unchecked(BinOp::Mul, &weight, &signed_bv(w, mu));
                alpha[idx[u]] = BitVec::bin_unchecked(
                    BinOp::And,
                    &BitVec::bin_unchecked(BinOp::Sub, &alpha[idx[u]], &delta),
                    &pmask,
                );
            }
            let op = if d_usize == 2 {
                BasisOp::Table2 {
                    vars: [vars[0], vars[1]],
                    tt8,
                }
            } else {
                BasisOp::Table3 {
                    vars: [vars[0], vars[1], vars[2]],
                    tt8,
                }
            };
            push_term(&mut terms, op, weight, &pmask);
            continue;
        }

        // `d >= 4`: test multi-way `OrAll` and negated-literal `ClauseAnd` against plain `AND_{q*}`.
        // (The sub-cube is read at most four times.)
        spend(work, 4 << d_usize)?;
        let target = alpha[q_star];
        let neg_target = BitVec::bin_unchecked(
            BinOp::And,
            &BitVec::un_unchecked(UnOp::Neg, &target),
            &pmask,
        );

        // 1. Check `OrAll(vars)`: `m[U] = (-1)^{|U|-1}`, so `m[q*] = (-1)^{d-1}`.
        let or_weight = if d_usize % 2 == 1 { target } else { neg_target };
        let sub_len = 1usize << d_usize;
        let map_sub = |u: usize| -> usize {
            let mut gq = 0usize;
            for (bit, &v) in vars.iter().enumerate() {
                if (u >> bit) & 1 == 1 {
                    gq |= 1 << v;
                }
            }
            gq
        };
        let mut before_nnz = 0usize;
        let mut or_after_nnz = 0usize;
        for u in 1..sub_len {
            let gq = map_sub(u);
            if !alpha[gq].is_zero() {
                before_nnz += 1;
            }
            let expected = if (u as u32).count_ones() % 2 == 1 {
                or_weight
            } else {
                BitVec::bin_unchecked(
                    BinOp::And,
                    &BitVec::un_unchecked(UnOp::Neg, &or_weight),
                    &pmask,
                )
            };
            if alpha[gq] != expected {
                or_after_nnz += 1;
            }
        }
        if or_after_nnz + 2 <= before_nnz {
            for u in 1..sub_len {
                let gq = map_sub(u);
                let delta = if (u as u32).count_ones() % 2 == 1 {
                    or_weight
                } else {
                    BitVec::bin_unchecked(
                        BinOp::And,
                        &BitVec::un_unchecked(UnOp::Neg, &or_weight),
                        &pmask,
                    )
                };
                alpha[gq] = BitVec::bin_unchecked(
                    BinOp::And,
                    &BitVec::bin_unchecked(BinOp::Sub, &alpha[gq], &delta),
                    &pmask,
                );
            }
            push_term(&mut terms, BasisOp::OrAll { vars }, or_weight, &pmask);
            continue;
        }

        // 2. Check `ClauseAnd` with negated literals (`alpha[q* \ {v}] == -alpha[q*]`).
        let mut neg_mask = 0u16;
        for (bit, &v) in vars.iter().enumerate() {
            if alpha[q_star ^ (1 << v)] == neg_target {
                neg_mask |= 1u16 << bit;
            }
        }
        let all_bits = (1u16 << d_usize) - 1;
        if neg_mask != 0 && neg_mask != all_bits {
            let pos_mask = all_bits ^ neg_mask;
            let clause_w = if neg_mask.count_ones().is_multiple_of(2) {
                target
            } else {
                neg_target
            };
            let neg_clause_w = BitVec::bin_unchecked(
                BinOp::And,
                &BitVec::un_unchecked(UnOp::Neg, &clause_w),
                &pmask,
            );
            let mut clause_after_nnz = 0usize;
            for u in 1..sub_len {
                let u16_mask = u as u16;
                let gq = map_sub(u);
                if (u16_mask & pos_mask) == pos_mask {
                    let expected = if (u16_mask & neg_mask).count_ones().is_multiple_of(2) {
                        clause_w
                    } else {
                        neg_clause_w
                    };
                    if alpha[gq] != expected {
                        clause_after_nnz += 1;
                    }
                } else if !alpha[gq].is_zero() {
                    clause_after_nnz += 1;
                }
            }
            if clause_after_nnz < before_nnz {
                for u in 1..sub_len {
                    let u16_mask = u as u16;
                    if (u16_mask & pos_mask) != pos_mask {
                        continue;
                    }
                    let gq = map_sub(u);
                    let delta = if (u16_mask & neg_mask).count_ones().is_multiple_of(2) {
                        clause_w
                    } else {
                        neg_clause_w
                    };
                    alpha[gq] = BitVec::bin_unchecked(
                        BinOp::And,
                        &BitVec::bin_unchecked(BinOp::Sub, &alpha[gq], &delta),
                        &pmask,
                    );
                }
                push_term(
                    &mut terms,
                    BasisOp::ClauseAnd { vars, neg_mask },
                    clause_w,
                    &pmask,
                );
                continue;
            }
        }

        // 3. Plain conjunction `AND_{q*}`.
        alpha[q_star] = BitVec::zero(w);
        push_term(
            &mut terms,
            BasisOp::ClauseAnd { vars, neg_mask: 0 },
            target,
            &pmask,
        );
    }

    Some(terms)
}

fn push_term(terms: &mut Vec<(BasisOp, BitVec)>, op: BasisOp, weight: BitVec, pmask: &BitVec) {
    if weight.is_zero() {
        return;
    }
    if let Some((_, existing)) = terms.iter_mut().find(|(o, _)| *o == op) {
        *existing = BitVec::bin_unchecked(
            BinOp::And,
            &BitVec::bin_unchecked(BinOp::Add, existing, &weight),
            pmask,
        );
        if existing.is_zero() {
            terms.retain(|(_, w)| !w.is_zero());
        }
        return;
    }
    terms.push((op, weight));
}

/// For unmasked (`FULL`) decompositions `konst + Σ c_i · B_i`, if `konst == c_i` for some term,
/// `c + c · B = (-c) · (~B)` eliminates the constant (`-7 - 7·(x | y) = 7·~(x | y)`).
pub(crate) fn trade_unmasked_constant(konst: &mut BitVec, terms: &mut [(BasisOp, BitVec)]) {
    if konst.is_zero() {
        return;
    }
    if let Some(i) = terms.iter().position(|(_, c)| *c == *konst) {
        let neg_c = BitVec::un_unchecked(UnOp::Neg, &terms[i].1);
        let old_op = core::mem::replace(&mut terms[i].0, BasisOp::Var(0));
        terms[i].0 = match old_op {
            BasisOp::Not(inner) => *inner,
            other => BasisOp::Not(Box::new(other)),
        };
        terms[i].1 = neg_c;
        *konst = BitVec::zero(konst.width());
    }
}
