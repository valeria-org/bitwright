//! Whole-DAG associative-commutative common sub-sum, linear-recurrence, and constant-multiplier
//! factoring (`share_sums`).
//!
//! Iterative round functions (ARX mixers, cryptographic compression rounds, Feistel networks,
//! multi-round accumulators) create two major circuit-bloat patterns when unrolled and flattened:
//!
//! 1. **Flattened linear recurrences**: State recurrences ($e_r = d_{r-1} + T_1(r)$, message
//!    schedules $W_t = W_{t-16} + \sigma_0 + W_{t-7} + \sigma_1$) unroll into hundreds of
//!    overlapping linear combinations with Fibonacci-like scalar multiples (`13, 21, 34, 55,
//!    89, ...`) over earlier round atoms, plus disjoint choice terms `(e & f) + (~e & g)`.
//!    [`recover_linear_recurrences`] computes canonical bounded linear forms over non-linear base
//!    atoms in topological order, folds disjoint complementary-mask pairs `(p & r) + (~p & s)`
//!    into bitwise `(p & r) | (~p & s)`, and reduces later flattened forms against earlier
//!    materialized forms ($F(u) \leftarrow (F(u) - s \cdot F(p)) + s \cdot p$) whenever weighted
//!    circuit cost strictly drops.
//! 2. **Unshared `Add` spines & dominated constant products**: [`factor_const_muls`] groups
//!    dominated `Mul(x_i, C)` nodes sharing `(width, C, parent_bag_signature)` into
//!    `(x_1 + ... + x_k) * C`, and [`share_sums`] runs windowed multiset Re-Pair pair factoring
//!    across all single-use `Add` bags per bit-width (`1..=512`).

use core::cmp::Ordering;

use super::Lease;
use crate::BitVec;
use crate::error::Error;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};

/// Minimum `Add` nodes in the live cone before scanning for cross-sum sharing.
const MIN_CONE_ADDS: usize = 64;

/// Maximum leaves flattened into a single `Add` bag (any deeper single-use `Add` child becomes
/// its own bag root, preserving completeness while keeping per-bag work linear).
const MAX_BAG: usize = 1024;

/// Maximum base atoms tracked in a canonical linear recurrence form.
const MAX_FORM_ATOMS: usize = 2048;

/// Maximum factoring rounds per bit-width group.
const MAX_ROUNDS: usize = 20;

/// Marker bit distinguishing virtual pair IDs from arena node IDs.
const VIRT_BIT: u32 = 1 << 31;

struct Bag {
    root: u32,
    width: u16,
    items: Vec<u32>,
    owned_adds: Vec<u32>,
    modified: bool,
}

#[inline]
fn mix_hash(a: u64, b: u64) -> u64 {
    let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
    let mut x = lo.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ hi.wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x ^ (x >> 31)
}

#[inline]
fn item_hash(cx: &Context, vhash: &[u64], id: u32) -> u64 {
    if id & VIRT_BIT == 0 {
        cx.meta[id as usize].shash
    } else {
        vhash[(id & !VIRT_BIT) as usize]
    }
}

#[inline]
fn cmp_item(cx: &Context, vhash: &[u64], a: u32, b: u32) -> Ordering {
    if a == b {
        return Ordering::Equal;
    }
    let ha = item_hash(cx, vhash, a);
    let hb = item_hash(cx, vhash, b);
    ha.cmp(&hb)
        .then_with(|| match (a & VIRT_BIT == 0, b & VIRT_BIT == 0) {
            (true, true) => cx.order(a, b),
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => ((a & !VIRT_BIT) as usize).cmp(&((b & !VIRT_BIT) as usize)),
        })
}

/// Factors linear recurrences, disjoint choice sums, dominated constant multipliers, and common
/// sub-sums across `Add` chains in `roots`, spending at most `max_work` bag-element inspections.
pub(crate) fn share_sums(
    cx: &mut Context,
    roots: &[u32],
    max_work: usize,
) -> Result<Option<(Vec<u32>, u64)>, Error> {
    if roots.is_empty() || max_work == 0 {
        return Ok(None);
    }
    let orig_order = cx.post_order_ids(roots);
    let orig_adds = orig_order
        .iter()
        .filter(|&&id| cx.node(id).op == OpCode::Add)
        .count();
    if orig_adds < MIN_CONE_ADDS {
        return Ok(None);
    }
    let old_size = orig_order.len() as u32;

    // Stage 1: Recover unrolled linear recurrences and fold disjoint `(p & r) + (~p & s)` muxes.
    let (rec_roots, mut mux_folded) = recover_linear_recurrences(cx, roots)?;
    let stage1_roots: &[u32] = rec_roots.as_deref().unwrap_or(roots);

    // Stage 2: Factor dominated `Mul(x_i, C)` summands sharing `(width, C, parent_bag_set)` so
    // `(x_1 + ... + x_k)` sums become visible to cross-bag sub-sum sharing below.
    let pre_roots = factor_const_muls(cx, stage1_roots)?;
    let cur_vec: Option<Vec<u32>> = pre_roots.or(rec_roots);
    let cur_roots: &[u32] = cur_vec.as_deref().unwrap_or(roots);
    let order = if cur_vec.is_some() {
        cx.post_order_ids(cur_roots)
    } else {
        orig_order
    };

    let mut uses: IdMap<u32, u32> = IdMap::default();
    for &r in cur_roots {
        *uses.entry(r).or_default() += 1;
    }
    for &id in &order {
        for c in cx.node(id).children() {
            *uses.entry(c).or_default() += 1;
        }
    }

    // Extract maximal single-use `Add` bags top-down from `cur_roots` so any chain exceeding
    // `MAX_BAG` naturally splits its unvisited tail into a child bag root.
    let mut claimed_interior: IdMap<u32, ()> = IdMap::default();
    let mut bags: Vec<Bag> = Vec::new();
    let mut todo: Vec<u32> = Vec::new();
    for &u in order.iter().rev() {
        if cx.node(u).op != OpCode::Add || claimed_interior.contains_key(&u) {
            continue;
        }
        let un = cx.node(u);
        todo.clear();
        todo.push(un.b);
        todo.push(un.a);
        let mut items = Vec::new();
        let mut owned_adds = Vec::new();
        while let Some(x) = todo.pop() {
            if cx.node(x).op == OpCode::Add
                && uses.get(&x).copied().unwrap_or(0) == 1
                && items.len() + todo.len() + 2 <= MAX_BAG
            {
                claimed_interior.insert(x, ());
                owned_adds.push(x);
                let xn = cx.node(x);
                todo.push(xn.b);
                todo.push(xn.a);
            } else {
                items.push(x);
            }
        }
        if items.len() >= 2 {
            // Fold disjoint choice summand pairs `(p & r) + (~p & s) -> (p & r) | (~p & s)`
            // directly in the bag if any remain.
            let folded_here = fold_bag_disjoint_mux_pairs(cx, &mut items)?;
            if folded_here > 0 {
                mux_folded += folded_here;
            }
            bags.push(Bag {
                root: u,
                width: un.width,
                items,
                owned_adds,
                modified: folded_here > 0,
            });
        }
    }

    let check_accept = |cx: &mut Context,
                        cand: &[u32],
                        mux_count: usize,
                        work: usize|
     -> Result<Option<(Vec<u32>, u64)>, Error> {
        if cand == roots {
            return Ok(None);
        }
        let new_handles: Vec<_> = cand.iter().map(|&r| cx.handle(r)).collect();
        let cap = if mux_count > 0 {
            old_size
        } else {
            old_size.saturating_sub(1)
        };
        let ok = matches!(
            cx.dag_size(&new_handles, cap)?,
            crate::expr::Bounded::Exact(_)
        );
        Ok(ok.then(|| (cand.to_vec(), work as u64)))
    };

    if bags.is_empty() {
        return match cur_vec {
            Some(ref r) => check_accept(cx, r, mux_folded, order.len()),
            None => Ok(None),
        };
    }

    let mut by_width: IdMap<u16, Vec<usize>> = IdMap::default();
    for (idx, bag) in bags.iter().enumerate() {
        by_width.entry(bag.width).or_default().push(idx);
    }
    let mut groups: Vec<(u16, Vec<usize>)> = by_width
        .into_iter()
        .filter(|(_, idxs)| idxs.iter().filter(|&&i| bags[i].items.len() >= 3).count() >= 2)
        .collect();
    groups.sort_unstable_by_key(|&(w, _)| w);

    const WINDOW: usize = 32;
    let mut virt_pairs: Vec<(u32, u32)> = Vec::new();
    let mut vhash: Vec<u64> = Vec::new();
    let mut work = 0usize;

    for (_, group) in &groups {
        for &bi in group {
            bags[bi].items.sort_by(|&a, &b| cmp_item(cx, &vhash, a, b));
            if bags[bi].items.windows(2).any(|pair| pair[0] == pair[1]) {
                bags[bi].modified = true;
            }
        }

        for _ in 0..MAX_ROUNDS {
            if work >= max_work {
                break;
            }
            let mut pair_counts: IdMap<(u32, u32), (u32, usize)> = IdMap::default();
            for &bi in group {
                let items = &bags[bi].items;
                let len = items.len();
                if len < 2 {
                    continue;
                }
                work += len * 2;
                for p in 0..len {
                    let u = items[p];
                    let lim = (p + 1 + WINDOW).min(len);
                    for &v in &items[(p + 1)..lim] {
                        let entry = pair_counts.entry((u, v)).or_insert((0, usize::MAX));
                        if entry.1 != bi {
                            entry.0 += 1;
                            entry.1 = bi;
                        }
                    }
                }
                if work >= max_work {
                    break;
                }
            }

            let mut cands: Vec<(u32, u32, u32)> = pair_counts
                .into_iter()
                .filter_map(|((u, v), (cnt, _))| (cnt >= 2).then_some((cnt, u, v)))
                .collect();
            if cands.is_empty() {
                break;
            }
            cands.sort_by(|&(c1, u1, v1), &(c2, u2, v2)| {
                c2.cmp(&c1)
                    .then_with(|| cmp_item(cx, &vhash, u1, u2))
                    .then_with(|| cmp_item(cx, &vhash, v1, v2))
            });

            // Greedily pick element-disjoint pairs so every selected pair is guaranteed to
            // match without conflict in every bag where it was counted.
            let mut claimed: IdMap<u32, ()> = IdMap::default();
            let mut selected: IdMap<(u32, u32), u32> = IdMap::default();
            for (_, u, v) in cands {
                if claimed.contains_key(&u) || claimed.contains_key(&v) {
                    continue;
                }
                if (virt_pairs.len() as u32) >= (VIRT_BIT - 1) {
                    break;
                }
                claimed.insert(u, ());
                claimed.insert(v, ());
                let vid = VIRT_BIT | (virt_pairs.len() as u32);
                let h = mix_hash(item_hash(cx, &vhash, u), item_hash(cx, &vhash, v));
                virt_pairs.push((u, v));
                vhash.push(h);
                selected.insert((u, v), vid);
            }
            if selected.is_empty() {
                break;
            }

            let mut any_applied = false;
            let mut taken = [false; MAX_BAG];
            for &bi in group {
                if !bags[bi].items.iter().any(|x| claimed.contains_key(x)) {
                    continue;
                }
                let len = bags[bi].items.len();
                taken[..len].fill(false);
                let mut next_items = Vec::with_capacity(len);
                let mut bag_changed = false;
                for p in 0..len {
                    if taken[p] {
                        continue;
                    }
                    let u = bags[bi].items[p];
                    let mut matched = None;
                    if claimed.contains_key(&u) {
                        let lim = (p + 1 + WINDOW).min(len);
                        for q in (p + 1)..lim {
                            if !taken[q]
                                && let Some(&vid) = selected.get(&(u, bags[bi].items[q]))
                            {
                                matched = Some((q, vid));
                                break;
                            }
                        }
                    }
                    if let Some((q, vid)) = matched {
                        taken[p] = true;
                        taken[q] = true;
                        next_items.push(vid);
                        bag_changed = true;
                    } else {
                        next_items.push(u);
                    }
                }
                if bag_changed {
                    bags[bi].items = next_items;
                    bags[bi].items.sort_by(|&a, &b| cmp_item(cx, &vhash, a, b));
                    bags[bi].modified = true;
                    any_applied = true;
                }
            }
            if !any_applied {
                break;
            }
        }
    }

    if virt_pairs.is_empty() && !bags.iter().any(|b| b.modified) {
        return match cur_vec {
            Some(ref r) => check_accept(cx, r, mux_folded, work.max(order.len())),
            None => Ok(None),
        };
    }

    let mut mod_bag_of_root: IdMap<u32, usize> = IdMap::default();
    let mut dead_interior: IdMap<u32, ()> = IdMap::default();
    for (bi, bag) in bags.iter().enumerate() {
        if bag.modified {
            mod_bag_of_root.insert(bag.root, bi);
            for &inner in &bag.owned_adds {
                dead_interior.insert(inner, ());
            }
        }
    }

    let mut became = Lease::new(cx.len());
    let mut virt_real: Vec<Option<u32>> = vec![None; virt_pairs.len()];
    let mut vstack: Vec<(usize, bool)> = Vec::new();

    let resolve_item = |cx: &mut Context,
                        became: &Lease,
                        virt_real: &mut [Option<u32>],
                        vstack: &mut Vec<(usize, bool)>,
                        id: u32|
     -> Result<u32, Error> {
        if id & VIRT_BIT == 0 {
            return Ok(became.get(id).unwrap_or(id));
        }
        let top = (id & !VIRT_BIT) as usize;
        if let Some(real) = virt_real[top] {
            return Ok(real);
        }
        vstack.clear();
        vstack.push((top, false));
        while let Some((vi, ready)) = vstack.pop() {
            if virt_real[vi].is_some() {
                continue;
            }
            let (u, v) = virt_pairs[vi];
            if !ready {
                vstack.push((vi, true));
                for child in [v, u] {
                    if child & VIRT_BIT != 0 {
                        let ci = (child & !VIRT_BIT) as usize;
                        if virt_real[ci].is_none() {
                            vstack.push((ci, false));
                        }
                    }
                }
                continue;
            }
            let ru = if u & VIRT_BIT == 0 {
                became.get(u).unwrap_or(u)
            } else {
                virt_real[(u & !VIRT_BIT) as usize].expect("child virtual pair materialized")
            };
            let rv = if v & VIRT_BIT == 0 {
                became.get(v).unwrap_or(v)
            } else {
                virt_real[(v & !VIRT_BIT) as usize].expect("child virtual pair materialized")
            };
            let built = cx.c_bin(BinOp::Add, ru, rv)?;
            virt_real[vi] = Some(built);
        }
        Ok(virt_real[top].expect("root virtual pair materialized"))
    };

    for &id in &order {
        if dead_interior.contains_key(&id) {
            continue;
        }
        if let Some(&bi) = mod_bag_of_root.get(&id) {
            let w = bags[bi].width;
            let width = crate::Width::new(w)?;
            let mut raw_items = Vec::with_capacity(bags[bi].items.len());
            for &it in &bags[bi].items {
                raw_items.push(resolve_item(cx, &became, &mut virt_real, &mut vstack, it)?);
            }
            raw_items.sort_by(|&a, &b| cx.order(a, b));
            // Combine duplicate occurrences `m * x` into power-of-two left shifts (`x << bit`,
            // which cost zero AIG gates when bit-blasted instead of `m - 1` ripple-carry adders).
            let mut real_items = Vec::with_capacity(raw_items.len());
            let mut idx = 0usize;
            while idx < raw_items.len() {
                let x = raw_items[idx];
                let mut end = idx + 1;
                while end < raw_items.len() && raw_items[end] == x {
                    end += 1;
                }
                let mult = (end - idx) as u64;
                idx = end;
                if mult == 1 {
                    real_items.push(x);
                } else if w == 1 {
                    if mult & 1 == 1 {
                        real_items.push(x);
                    }
                } else {
                    let mut rem = mult;
                    while rem != 0 {
                        let bit = rem.trailing_zeros();
                        rem &= rem - 1;
                        if u64::from(w) <= u64::from(bit) {
                            continue;
                        }
                        if bit == 0 {
                            real_items.push(x);
                        } else {
                            let sh_c =
                                cx.mk_const(&BitVec::wrapping_from_u64(width, u64::from(bit)))?;
                            real_items.push(cx.c_bin(BinOp::Shl, x, sh_c)?);
                        }
                    }
                }
            }
            if real_items.is_empty() {
                let z = cx.mk_const(&BitVec::zero(width))?;
                became.insert(id, z);
                continue;
            }
            real_items.sort_by(|&a, &b| cx.order(a, b));
            let mut iter = real_items.into_iter();
            let first = iter.next().expect("bag has at least one item");
            let mut acc = first;
            for x in iter {
                acc = cx.c_bin(BinOp::Add, acc, x)?;
            }
            became.insert(id, acc);
            continue;
        }
        let n = cx.node(id);
        let mut kids = [n.a, n.b, n.c];
        let mut changed = false;
        for (k, c) in n.children().enumerate() {
            let nc = became.get(c).unwrap_or(c);
            changed |= nc != c;
            kids[k] = nc;
        }
        let r = if changed { cx.rebuild(id, kids)? } else { id };
        became.insert(id, r);
    }

    let mut new_roots: Vec<u32> = cur_roots
        .iter()
        .map(|&r| became.get(r).unwrap_or(r))
        .collect();
    if let Some(mul_factored) = factor_const_muls(cx, &new_roots)? {
        new_roots = mul_factored;
    }
    check_accept(cx, &new_roots, mux_folded, work.max(order.len()))
}

/// Checks whether two `And` nodes `a` and `b` are disjoint choice branches `(p & r)` and
/// `(~p & s)` via `cx.are_bitwise_complements`.
fn are_complementary_and_branches(cx: &Context, a: u32, b: u32) -> bool {
    if a == b {
        return false;
    }
    let (na, nb) = (cx.node(a), cx.node(b));
    if na.op != OpCode::And || nb.op != OpCode::And {
        return false;
    }
    cx.are_bitwise_complements(na.a, nb.a)
        || cx.are_bitwise_complements(na.a, nb.b)
        || cx.are_bitwise_complements(na.b, nb.a)
        || cx.are_bitwise_complements(na.b, nb.b)
}

/// Folds disjoint `(p & r) + (~p & s)` pairs inside a unit-coefficient `Add` bag into
/// `(p & r) | (~p & s)`, returning the number of folded pairs.
fn fold_bag_disjoint_mux_pairs(cx: &mut Context, items: &mut Vec<u32>) -> Result<usize, Error> {
    let mut and_positions: Vec<usize> = Vec::new();
    for (idx, &id) in items.iter().enumerate() {
        if cx.node(id).op == OpCode::And {
            and_positions.push(idx);
            if and_positions.len() > 32 {
                return Ok(0);
            }
        }
    }
    if and_positions.len() < 2 {
        return Ok(0);
    }
    let mut used = [false; 32];
    let mut removed = vec![false; items.len()];
    let mut replacements: Vec<(usize, u32)> = Vec::new();
    for i in 0..and_positions.len() {
        if used[i] {
            continue;
        }
        let pi = and_positions[i];
        let ai = items[pi];
        for j in (i + 1)..and_positions.len() {
            if used[j] {
                continue;
            }
            let pj = and_positions[j];
            let aj = items[pj];
            if are_complementary_and_branches(cx, ai, aj) {
                used[i] = true;
                used[j] = true;
                removed[pj] = true;
                let mux = cx.c_bin(BinOp::Or, ai, aj)?;
                replacements.push((pi, mux));
                break;
            }
        }
    }
    if replacements.is_empty() {
        return Ok(0);
    }
    let count = replacements.len();
    for (pos, mux) in replacements {
        items[pos] = mux;
    }
    let mut k = 0usize;
    items.retain(|_| {
        let keep = !removed[k];
        k += 1;
        keep
    });
    Ok(count)
}

/// Multiplicative inverse of an odd `BitVec` modulo `2^W` (`1 <= W <= 512`) via Newton-Raphson.
fn invert_odd_bv(d: &BitVec) -> BitVec {
    let w = d.width();
    if w.bits() == 1 {
        return BitVec::one(w);
    }
    let two = BitVec::wrapping_from_u64(w, 2);
    // Any odd integer satisfies `d * d ≡ 1 (mod 8)` (3 bits); each step doubles precision.
    let mut inv = *d;
    let mut bits = 3u32;
    let target = u32::from(w.bits());
    while bits < target {
        let prod = BitVec::bin_unchecked(BinOp::Mul, d, &inv);
        let corr = BitVec::bin_unchecked(BinOp::Sub, &two, &prod);
        inv = BitVec::bin_unchecked(BinOp::Mul, &inv, &corr);
        bits *= 2;
    }
    inv
}

/// Signed-digit (CSD / Booth) non-zero weight of `c`, bounding how many adders `x * c` requires.
fn coeff_mul_adders(c: &BitVec) -> u32 {
    let w = c.width().bits();
    if c.is_zero() {
        return 0;
    }
    let neg_c = BitVec::un_unchecked(UnOp::Neg, c);
    let min_pop = crate::facts::known::count_ones(c).min(crate::facts::known::count_ones(&neg_c));
    if min_pop <= 1 {
        return 0;
    }
    // CSD weight via `((c ^ (c + (c >> 1)))` approximation on low 64 bits or `min_pop - 1`.
    if w <= 64
        && let Some(v) = c.to_u64()
    {
        let half = v >> 1;
        let sum = v.wrapping_add(half);
        let csd = ((sum ^ half).count_ones()).saturating_sub(1);
        return csd.min(min_pop - 1).max(1);
    }
    (min_pop - 1).min(16)
}

#[inline]
fn coeff_cost(c: &BitVec) -> i64 {
    if c.is_zero() {
        return 0;
    }
    let mul_adds = i64::from(coeff_mul_adders(c));
    if mul_adds == 0 {
        let neg_c = BitVec::un_unchecked(UnOp::Neg, c);
        if crate::facts::known::count_ones(c) == 1 {
            10
        } else if crate::facts::known::count_ones(&neg_c) == 1 {
            11
        } else {
            20
        }
    } else {
        10 + 12 * mul_adds
    }
}

struct Pivot {
    /// Materialized arena node ID representing `konst + Σ terms_i`.
    node: u32,
    konst: BitVec,
    /// Non-zero `(base_atom_id, coeff)` sorted by `base_atom_id`.
    terms: Vec<(u32, BitVec)>,
    /// Up to 2 odd-coefficient `(base_atom_id, odd_inv)` anchors (newest atoms first).
    anchors: [(u32, Option<BitVec>); 2],
    anchor_len: usize,
}

fn add_scaled_terms(
    dst: &mut Vec<(u32, BitVec)>,
    src: &[(u32, BitVec)],
    scale: &BitVec,
    cap: usize,
) -> bool {
    if scale.is_zero() {
        return true;
    }
    for &(atom, ref c) in src {
        let prod = BitVec::bin_unchecked(BinOp::Mul, c, scale);
        if prod.is_zero() {
            continue;
        }
        match dst.binary_search_by_key(&atom, |&(a, _)| a) {
            Ok(idx) => {
                let next = BitVec::bin_unchecked(BinOp::Add, &dst[idx].1, &prod);
                if next.is_zero() {
                    dst.remove(idx);
                } else {
                    dst[idx].1 = next;
                }
            }
            Err(idx) => {
                if dst.len() >= cap {
                    return false;
                }
                dst.insert(idx, (atom, prod));
            }
        }
    }
    true
}

/// Folds complementary disjoint-mask `And` pairs sharing the exact same coefficient inside a
/// canonical `(atom, coeff)` vector: `c * (p & r) + c * (~p & s) -> c * ((p & r) | (~p & s))`.
fn fold_form_disjoint_mux_pairs(
    cx: &mut Context,
    terms: &mut Vec<(u32, BitVec)>,
) -> Result<usize, Error> {
    let mut and_idxs: Vec<usize> = Vec::new();
    for (idx, &(atom, _)) in terms.iter().enumerate() {
        if cx.node(atom).op == OpCode::And {
            and_idxs.push(idx);
            if and_idxs.len() > 48 {
                break;
            }
        }
    }
    if and_idxs.len() < 2 {
        return Ok(0);
    }
    let mut used = vec![false; and_idxs.len()];
    let mut to_remove: Vec<u32> = Vec::new();
    let mut to_add: Vec<(u32, BitVec)> = Vec::new();
    for i in 0..and_idxs.len() {
        if used[i] {
            continue;
        }
        let (ai, ci) = terms[and_idxs[i]];
        for j in (i + 1)..and_idxs.len() {
            if used[j] {
                continue;
            }
            let (aj, cj) = terms[and_idxs[j]];
            if ci == cj && are_complementary_and_branches(cx, ai, aj) {
                used[i] = true;
                used[j] = true;
                let mux = cx.c_bin(BinOp::Or, ai, aj)?;
                to_remove.push(ai);
                to_remove.push(aj);
                to_add.push((mux, ci));
                break;
            }
        }
    }
    if to_add.is_empty() {
        return Ok(0);
    }
    let folded = to_add.len();
    terms.retain(|&(a, _)| !to_remove.contains(&a));
    let one = BitVec::one(to_add[0].1.width());
    for (mux, c) in to_add {
        let _ = add_scaled_terms(terms, &[(mux, c)], &one, MAX_FORM_ATOMS + 64);
    }
    Ok(folded)
}

/// Emits a linear combination `konst + Σ c_i * x_i` compactly, grouping non-power-of-two
/// multipliers that share `|c|` into `(Σ ±x_j) * |c|` and turning `±2^k * x` into shifts.
fn emit_compact_linear_form(
    cx: &mut Context,
    w: crate::Width,
    konst: &BitVec,
    terms: &[(u32, BitVec)],
) -> Result<u32, Error> {
    if terms.is_empty() {
        return cx.mk_const(konst);
    }
    let wb = u32::from(w.bits());
    let mut pos_units: Vec<u32> = Vec::new();
    let mut neg_units: Vec<u32> = Vec::new();
    // Non-power-of-two multiplier groups keyed by canonical positive constant node ID.
    let mut mul_groups: Vec<(u32, BitVec, Vec<u32>, Vec<u32>)> = Vec::new();

    for &(x, ref c) in terms {
        if c.is_zero() {
            continue;
        }
        if w.bits() == 1 {
            pos_units.push(x);
            continue;
        }
        let neg_c = BitVec::un_unchecked(UnOp::Neg, c);
        let c_ones = crate::facts::known::count_ones(c);
        if c_ones == 1 {
            let bit = crate::facts::known::trailing_zeros(c);
            if bit == 0 {
                pos_units.push(x);
            } else if bit < wb {
                let sh = cx.mk_const(&BitVec::wrapping_from_u64(w, u64::from(bit)))?;
                pos_units.push(cx.c_bin(BinOp::Shl, x, sh)?);
            }
            continue;
        }
        let neg_ones = crate::facts::known::count_ones(&neg_c);
        if neg_ones == 1 {
            let bit = crate::facts::known::trailing_zeros(&neg_c);
            if bit == 0 {
                neg_units.push(x);
            } else if bit < wb {
                let sh = cx.mk_const(&BitVec::wrapping_from_u64(w, u64::from(bit)))?;
                neg_units.push(cx.c_bin(BinOp::Shl, x, sh)?);
            }
            continue;
        }
        // Choose canonical sign for grouping `c` vs `-c`: smaller popcount (or `c < -c`).
        let (canon_bv, is_neg) = if neg_ones < c_ones || (neg_ones == c_ones && neg_c < *c) {
            (neg_c, true)
        } else {
            (*c, false)
        };
        let c_id = cx.mk_const(&canon_bv)?;
        match mul_groups.iter_mut().find(|g| g.0 == c_id) {
            Some(g) => {
                if is_neg {
                    g.3.push(x);
                } else {
                    g.2.push(x);
                }
            }
            None => {
                let (mut p, mut n) = (Vec::new(), Vec::new());
                if is_neg {
                    n.push(x);
                } else {
                    p.push(x);
                }
                mul_groups.push((c_id, canon_bv, p, n));
            }
        }
    }

    for (c_id, _, mut p_list, mut n_list) in mul_groups {
        p_list.sort_by(|&a, &b| cx.order(a, b));
        n_list.sort_by(|&a, &b| cx.order(a, b));
        let (all_neg, pos_part, neg_part) = if p_list.is_empty() {
            (true, n_list, Vec::new())
        } else {
            (false, p_list, n_list)
        };
        let mut iter = pos_part.into_iter();
        let mut inner = iter.next().expect("non-empty mul group");
        for item in iter {
            inner = cx.c_bin(BinOp::Add, inner, item)?;
        }
        for item in neg_part {
            inner = cx.c_bin(BinOp::Sub, inner, item)?;
        }
        let prod = cx.c_bin(BinOp::Mul, inner, c_id)?;
        if all_neg {
            neg_units.push(prod);
        } else {
            pos_units.push(prod);
        }
    }

    pos_units.sort_by(|&a, &b| cx.order(a, b));
    neg_units.sort_by(|&a, &b| cx.order(a, b));

    let mut acc: Option<u32> = None;
    for p in pos_units {
        acc = Some(match acc {
            None => p,
            Some(cur) => cx.c_bin(BinOp::Add, cur, p)?,
        });
    }
    for n in neg_units {
        acc = Some(match acc {
            None => cx.c_un(UnOp::Neg, n)?,
            Some(cur) => cx.c_bin(BinOp::Sub, cur, n)?,
        });
    }
    let base = match acc {
        Some(b) => b,
        None => return cx.mk_const(konst),
    };
    if konst.is_zero() {
        Ok(base)
    } else {
        let kc = cx.mk_const(konst)?;
        cx.c_bin(BinOp::Add, base, kc)
    }
}

/// Topological linear-form recurrence recovery and disjoint-choice mux folding.
fn recover_linear_recurrences(
    cx: &mut Context,
    roots: &[u32],
) -> Result<(Option<Vec<u32>>, usize), Error> {
    let orig_cx_len = cx.len() as u32;
    let order = cx.post_order_ids(roots);
    let mut uses: IdMap<u32, u32> = IdMap::default();
    for &r in roots {
        *uses.entry(r).or_default() += 1;
    }
    for &id in &order {
        for c in cx.node(id).children() {
            *uses.entry(c).or_default() += 1;
        }
    }

    let linear_step = |cx: &Context, id: u32| -> bool {
        let n = cx.node(id);
        if n.width < 2 {
            return false;
        }
        match n.op {
            OpCode::Add | OpCode::Sub | OpCode::Neg => true,
            OpCode::Mul => cx.is_const(n.a) ^ cx.is_const(n.b),
            OpCode::Shl => cx
                .const_val(n.b)
                .and_then(|v| v.to_u64())
                .is_some_and(|s| s < u64::from(n.width)),
            _ => false,
        }
    };

    // Identify maximal single-use linear regions top-down so owned interior nodes are skipped
    // during bottom-up reconstruction unless a bag root is left unchanged.
    type RawBag = (BitVec, Vec<(u32, BitVec)>, Vec<u32>);
    let mut claimed: IdMap<u32, ()> = IdMap::default();
    // `(root_id, raw_konst, raw_terms_over_bag_leaves, owned_interior)`
    let mut raw_bags: IdMap<u32, RawBag> = IdMap::default();
    let mut stack: Vec<(u32, BitVec)> = Vec::new();

    for &u in order.iter().rev() {
        let un = cx.node(u);
        if !matches!(un.op, OpCode::Add | OpCode::Sub) || un.width < 2 || claimed.contains_key(&u) {
            continue;
        }
        let Ok(w) = crate::Width::new(un.width) else {
            continue;
        };
        let one = BitVec::one(w);
        let minus_one = BitVec::ones(w);
        let mut konst = BitVec::zero(w);
        let mut terms: Vec<(u32, BitVec)> = Vec::new();
        let mut owned: Vec<u32> = Vec::new();
        stack.clear();
        if un.op == OpCode::Add {
            stack.push((un.b, one));
            stack.push((un.a, one));
        } else {
            stack.push((un.b, minus_one));
            stack.push((un.a, one));
        }
        let mut overflow = false;
        while let Some((x, scale)) = stack.pop() {
            if scale.is_zero() {
                continue;
            }
            if let Some(cv) = cx.const_val(x) {
                let prod = BitVec::bin_unchecked(BinOp::Mul, &cv, &scale);
                konst = BitVec::bin_unchecked(BinOp::Add, &konst, &prod);
                continue;
            }
            if uses.get(&x).copied().unwrap_or(0) == 1
                && linear_step(cx, x)
                && terms.len() + stack.len() + 2 <= MAX_BAG
            {
                let xn = cx.node(x);
                let pushed = match xn.op {
                    OpCode::Add => {
                        stack.push((xn.b, scale));
                        stack.push((xn.a, scale));
                        true
                    }
                    OpCode::Sub => {
                        stack.push((xn.b, BitVec::un_unchecked(UnOp::Neg, &scale)));
                        stack.push((xn.a, scale));
                        true
                    }
                    OpCode::Neg => {
                        stack.push((xn.a, BitVec::un_unchecked(UnOp::Neg, &scale)));
                        true
                    }
                    OpCode::Mul => {
                        let (base, c_id) = if cx.is_const(xn.b) {
                            (xn.a, xn.b)
                        } else {
                            (xn.b, xn.a)
                        };
                        if let Some(cv) = cx.const_val(c_id) {
                            stack.push((base, BitVec::bin_unchecked(BinOp::Mul, &scale, &cv)));
                            true
                        } else {
                            false
                        }
                    }
                    OpCode::Shl => {
                        if let Some(sv) = cx.const_val(xn.b) {
                            let factor = BitVec::bin_unchecked(BinOp::Shl, &one, &sv);
                            stack.push((xn.a, BitVec::bin_unchecked(BinOp::Mul, &scale, &factor)));
                            true
                        } else {
                            false
                        }
                    }
                    _ => false,
                };
                if pushed {
                    claimed.insert(x, ());
                    owned.push(x);
                    continue;
                }
            }
            if !add_scaled_terms(&mut terms, &[(x, one)], &scale, MAX_FORM_ATOMS) {
                overflow = true;
                break;
            }
        }
        if !overflow && terms.len() >= 2 {
            raw_bags.insert(u, (konst, terms, owned));
        }
    }

    if raw_bags.is_empty() {
        return Ok((None, 0));
    }

    // Walk `order` bottom-up, maintaining canonical `base_forms` (expanded over non-linear base
    // atoms) and per-width `pivots` for already-materialized bag roots.
    let mut base_forms: IdMap<u32, (BitVec, Vec<(u32, BitVec)>)> = IdMap::default();
    let mut pivots_by_width: IdMap<u16, Vec<Pivot>> = IdMap::default();
    let mut dead_interior: IdMap<u32, ()> = IdMap::default();
    let mut rewritten_bag: IdMap<u32, (BitVec, Vec<(u32, BitVec)>)> = IdMap::default();
    let mut total_mux_folded = 0usize;
    let mut any_recurrence_reduced = false;

    // First pass: fold disjoint choice muxes in raw bags, build `base_forms`, and compute pivot
    // reductions on flattened bags (`raw_terms.len() >= 4`), marking `dead_interior` ONLY on bags
    // that are actually rewritten so un-rewritten bags keep their original interior nodes intact!
    let bag_roots_in_order: Vec<u32> = order
        .iter()
        .copied()
        .filter(|id| raw_bags.contains_key(id))
        .collect();

    // Virtual placeholder IDs for bag roots in `pivots` are simply the original bag root IDs `u`
    // (remapped via `became` during bottom-up materialization!).
    for u in bag_roots_in_order {
        let (raw_konst, mut raw_terms, owned) = raw_bags.remove(&u).unwrap();
        let w_bits = cx.wid(u);
        let w = crate::Width::new(w_bits)?;
        let one = BitVec::one(w);

        let mux_cnt = fold_form_disjoint_mux_pairs(cx, &mut raw_terms)?;
        total_mux_folded += mux_cnt;

        // Expand `raw_terms` through `base_forms` of any child bag roots to obtain the canonical
        // non-linear base-atom representation `full_terms`.
        let mut full_konst = raw_konst;
        let mut full_terms: Vec<(u32, BitVec)> = Vec::with_capacity(raw_terms.len());
        let mut full_ok = true;
        for &(leaf, ref scale) in &raw_terms {
            if let Some((ck, cterms)) = base_forms.get(&leaf) {
                let prod_k = BitVec::bin_unchecked(BinOp::Mul, ck, scale);
                full_konst = BitVec::bin_unchecked(BinOp::Add, &full_konst, &prod_k);
                if !add_scaled_terms(&mut full_terms, cterms, scale, MAX_FORM_ATOMS) {
                    full_ok = false;
                    break;
                }
            } else if !add_scaled_terms(&mut full_terms, &[(leaf, one)], scale, MAX_FORM_ATOMS) {
                full_ok = false;
                break;
            }
        }
        if full_ok && full_terms.len() >= 2 {
            let extra_mux = fold_form_disjoint_mux_pairs(cx, &mut full_terms)?;
            total_mux_folded += extra_mux;
        }

        let raw_cost: i64 = raw_terms.iter().map(|(_, c)| coeff_cost(c)).sum::<i64>()
            + if raw_konst.is_zero() { 0 } else { 5 };

        let mut chosen_rewrite: Option<(BitVec, Vec<(u32, BitVec)>)> = None;

        if full_ok && full_terms.len() >= 4 {
            let mut cur_konst = full_konst;
            let mut cur_terms = full_terms.clone();
            let mut pivot_terms: Vec<(u32, BitVec)> = Vec::new();
            let pivots = pivots_by_width.entry(w_bits).or_default();

            for _step in 0..16 {
                if cur_terms.len() < 3 || pivots.is_empty() {
                    break;
                }
                let mut best_cand: Option<(usize, BitVec, i64)> = None;
                // Scan up to 192 most recent pivots (newest state words first).
                let start_idx = pivots.len().saturating_sub(192);
                for (pi_offset, piv) in pivots[start_idx..].iter().enumerate().rev() {
                    let pi = start_idx + pi_offset;
                    if piv.terms.len() > cur_terms.len() + 2 {
                        continue;
                    }
                    // Propose scalar `s` from the pivot's odd-coefficient anchor atoms.
                    let mut tried_s: [Option<BitVec>; 2] = [None, None];
                    let mut n_tried = 0usize;
                    for &(anchor_atom, ref inv_opt) in &piv.anchors[..piv.anchor_len] {
                        let Ok(pos) = cur_terms.binary_search_by_key(&anchor_atom, |&(a, _)| a)
                        else {
                            continue;
                        };
                        let c_cur = &cur_terms[pos].1;
                        let s = if let Some(inv) = inv_opt {
                            BitVec::bin_unchecked(BinOp::Mul, c_cur, inv)
                        } else {
                            continue;
                        };
                        if s.is_zero() || tried_s[..n_tried].contains(&Some(s)) {
                            continue;
                        }
                        tried_s[n_tried] = Some(s);
                        n_tried += 1;

                        // Evaluate exact cost delta of replacing `s * piv` with `(piv.node, s)`.
                        // Require `supp(s * piv) ⊆ supp(cur_terms)` so pivot reduction never
                        // introduces spurious variables outside `u`'s true cone of support.
                        let mut saved = -coeff_cost(&s);
                        let mut matched = 0usize;
                        let mut subset_ok = true;
                        for &(b, ref d_b) in &piv.terms {
                            let sub = BitVec::bin_unchecked(BinOp::Mul, &s, d_b);
                            if sub.is_zero() {
                                continue;
                            }
                            match cur_terms.binary_search_by_key(&b, |&(a, _)| a) {
                                Ok(idx) => {
                                    matched += 1;
                                    let old_c = &cur_terms[idx].1;
                                    let new_c = BitVec::bin_unchecked(BinOp::Sub, old_c, &sub);
                                    saved += coeff_cost(old_c) - coeff_cost(&new_c);
                                }
                                Err(_) => {
                                    subset_ok = false;
                                    break;
                                }
                            }
                        }
                        if subset_ok
                            && matched >= 2
                            && saved >= 10
                            && best_cand.as_ref().is_none_or(|b| saved > b.2)
                        {
                            best_cand = Some((pi, s, saved));
                            if saved >= 80 {
                                break;
                            }
                        }
                    }
                    if best_cand.as_ref().is_some_and(|b| b.2 >= 80) {
                        break;
                    }
                }

                let Some((pi, s, _)) = best_cand else {
                    break;
                };
                let piv = &pivots[pi];
                let neg_s = BitVec::un_unchecked(UnOp::Neg, &s);
                let dk = BitVec::bin_unchecked(BinOp::Mul, &s, &piv.konst);
                cur_konst = BitVec::bin_unchecked(BinOp::Sub, &cur_konst, &dk);
                let _ = add_scaled_terms(&mut cur_terms, &piv.terms, &neg_s, MAX_FORM_ATOMS + 64);
                let _ = add_scaled_terms(
                    &mut pivot_terms,
                    &[(piv.node, one)],
                    &s,
                    MAX_FORM_ATOMS + 64,
                );
            }

            if !pivot_terms.is_empty() {
                let mut combined = cur_terms;
                let _ = add_scaled_terms(&mut combined, &pivot_terms, &one, MAX_FORM_ATOMS + 128);
                let new_cost: i64 = combined.iter().map(|(_, c)| coeff_cost(c)).sum::<i64>()
                    + if cur_konst.is_zero() { 0 } else { 5 };
                if new_cost + 10 <= raw_cost {
                    any_recurrence_reduced = true;
                    chosen_rewrite = Some((cur_konst, combined));
                }
            }
        }

        if chosen_rewrite.is_none() && mux_cnt > 0 {
            chosen_rewrite = Some((raw_konst, raw_terms));
        }

        if let Some(rw) = chosen_rewrite {
            for &inner in &owned {
                dead_interior.insert(inner, ());
            }
            rewritten_bag.insert(u, rw);
        }

        // Register `u` in `base_forms` and `pivots_by_width` (if `full_ok && 2 <= len <= 1536`).
        if full_ok && (2..=1536).contains(&full_terms.len()) {
            let mut anchors: [(u32, Option<BitVec>); 2] = [(0, None), (0, None)];
            let mut anchor_len = 0usize;
            // Pick up to 2 odd-coefficient atoms with highest arena IDs (newest round atoms first).
            for &(atom, ref c) in full_terms.iter().rev() {
                if c.bit(0) == Some(true) {
                    let inv = if *c == one {
                        Some(one)
                    } else {
                        Some(invert_odd_bv(c))
                    };
                    anchors[anchor_len] = (atom, inv);
                    anchor_len += 1;
                    if anchor_len == 2 {
                        break;
                    }
                }
            }
            if anchor_len > 0 {
                let pivots = pivots_by_width.entry(w_bits).or_default();
                if pivots.len() < 2048 {
                    pivots.push(Pivot {
                        node: u,
                        konst: full_konst,
                        terms: full_terms.clone(),
                        anchors,
                        anchor_len,
                    });
                }
            }
            base_forms.insert(u, (full_konst, full_terms));
        }
    }

    if !any_recurrence_reduced && total_mux_folded == 0 {
        return Ok((None, 0));
    }

    // Materialize rewritten bags and rebuild ancestors in a single topological pass.
    let mut became = Lease::new(cx.len());
    for &id in &order {
        if dead_interior.contains_key(&id) {
            continue;
        }
        if let Some((konst, terms)) = rewritten_bag.remove(&id) {
            let w = cx.width_of(id);
            let one = BitVec::one(w);
            let mut mapped: Vec<(u32, BitVec)> = Vec::with_capacity(terms.len());
            for (atom, c) in terms {
                let ma = if atom >= orig_cx_len && cx.node(atom).op == OpCode::Or {
                    let mn = cx.node(atom);
                    let la = became.get(mn.a).unwrap_or(mn.a);
                    let lb = became.get(mn.b).unwrap_or(mn.b);
                    cx.c_bin(BinOp::Or, la, lb)?
                } else {
                    became.get(atom).unwrap_or(atom)
                };
                let _ = add_scaled_terms(&mut mapped, &[(ma, one)], &c, MAX_FORM_ATOMS + 128);
            }
            let built = emit_compact_linear_form(cx, w, &konst, &mapped)?;
            became.insert(id, built);
            continue;
        }
        let n = cx.node(id);
        let mut kids = [n.a, n.b, n.c];
        let mut changed = false;
        for (k, c) in n.children().enumerate() {
            let nc = became.get(c).unwrap_or(c);
            changed |= nc != c;
            kids[k] = nc;
        }
        let r = if changed { cx.rebuild(id, kids)? } else { id };
        became.insert(id, r);
    }

    let out: Vec<u32> = roots.iter().map(|&r| became.get(r).unwrap_or(r)).collect();
    Ok(((out != roots).then_some(out), total_mux_folded))
}

/// Factors `Mul(x_i, C)` summands (`k >= 2`) whose live DAG uses are 100% dominated by the exact
/// same multiset of parent `Add` bags into a single shared `(x_1 + ... + x_k) * C` product.
fn factor_const_muls(cx: &mut Context, roots: &[u32]) -> Result<Option<Vec<u32>>, Error> {
    let order = cx.post_order_ids(roots);
    let mut uses: IdMap<u32, u32> = IdMap::default();
    for &r in roots {
        *uses.entry(r).or_default() += 1;
    }
    for &id in &order {
        for c in cx.node(id).children() {
            *uses.entry(c).or_default() += 1;
        }
    }

    let const_mul_parts = |cx: &Context, id: u32| -> Option<(u32, u32)> {
        let n = cx.node(id);
        if n.op != OpCode::Mul {
            return None;
        }
        if cx.is_const(n.b) && !cx.is_const(n.a) {
            Some((n.a, n.b))
        } else if cx.is_const(n.a) && !cx.is_const(n.b) {
            Some((n.b, n.a))
        } else {
            None
        }
    };

    let mut claimed_interior: IdMap<u32, ()> = IdMap::default();
    let mut bags: Vec<(u32, Vec<u32>, Vec<u32>)> = Vec::new();
    let mut todo = Vec::new();
    for &u in order.iter().rev() {
        if cx.node(u).op != OpCode::Add || claimed_interior.contains_key(&u) {
            continue;
        }
        let un = cx.node(u);
        todo.clear();
        todo.push(un.b);
        todo.push(un.a);
        let mut items = Vec::new();
        let mut owned = Vec::new();
        while let Some(x) = todo.pop() {
            if cx.node(x).op == OpCode::Add
                && uses.get(&x).copied().unwrap_or(0) == 1
                && items.len() + todo.len() + 2 <= MAX_BAG
            {
                claimed_interior.insert(x, ());
                owned.push(x);
                let xn = cx.node(x);
                todo.push(xn.b);
                todo.push(xn.a);
            } else {
                items.push(x);
            }
        }
        bags.push((u, items, owned));
    }
    if bags.is_empty() {
        return Ok(None);
    }

    // Count occurrences of each `Mul(base, C)` across all bags.
    let mut mul_bag_occ: IdMap<u32, Vec<(usize, u32)>> = IdMap::default();
    for (bi, (_, items, _)) in bags.iter().enumerate() {
        for &it in items {
            if const_mul_parts(cx, it).is_some() {
                let occ = mul_bag_occ.entry(it).or_default();
                match occ.last_mut() {
                    Some(last) if last.0 == bi => last.1 += 1,
                    _ => occ.push((bi, 1)),
                }
            }
        }
    }

    // Keep only `Mul` nodes whose bag occurrences account for 100% of their live uses, and group
    // them by `(c_id, occ_hash)` + exact occurrence signature verification.
    type OccGroup = (Vec<(usize, u32)>, Vec<u32>);
    let mut groups_by_key: IdMap<(u32, u64), Vec<OccGroup>> = IdMap::default();
    let mut mul_candidates: Vec<u32> = mul_bag_occ.keys().copied().collect();
    mul_candidates.sort_by(|&a, &b| cx.order(a, b));

    for m_id in mul_candidates {
        let occ = &mul_bag_occ[&m_id];
        let bag_total: u32 = occ.iter().map(|&(_, cnt)| cnt).sum();
        if bag_total != uses.get(&m_id).copied().unwrap_or(0) {
            continue;
        }
        let Some((_, c_id)) = const_mul_parts(cx, m_id) else {
            continue;
        };
        let mut h = 0xcbf2_9ce4_8422_2325u64;
        for &(bi, cnt) in occ {
            h = mix_hash(h, ((bi as u64) << 32) | u64::from(cnt));
        }
        let bucket = groups_by_key.entry((c_id, h)).or_default();
        match bucket.iter_mut().find(|(sig, _)| sig == occ) {
            Some((_, members)) => members.push(m_id),
            None => bucket.push((occ.clone(), vec![m_id])),
        }
    }

    // Assign each qualifying group (`members.len() >= 2`) an index; the first member in each bag
    // occurrence emits `(x_1 + ... + x_k) * C` (with multiplicity `cnt`) and the rest are dropped.
    struct MulGroup {
        c_id: u32,
        members: Vec<u32>,
        built: Option<u32>,
    }
    let mut mul_groups: Vec<MulGroup> = Vec::new();
    let mut member_to_group: IdMap<u32, (usize, bool)> = IdMap::default();
    let mut mod_bags: IdMap<usize, ()> = IdMap::default();

    let mut group_keys: Vec<(u32, u64)> = groups_by_key.keys().copied().collect();
    group_keys.sort_by(|&(c1, h1), &(c2, h2)| cx.order(c1, c2).then_with(|| h1.cmp(&h2)));

    for key in group_keys {
        let c_id = key.0;
        for (occ, members) in groups_by_key.remove(&key).unwrap_or_default() {
            if members.len() < 2 {
                continue;
            }
            let gi = mul_groups.len();
            for (idx, &m_id) in members.iter().enumerate() {
                member_to_group.insert(m_id, (gi, idx == 0));
            }
            for &(bi, _) in &occ {
                mod_bags.insert(bi, ());
            }
            mul_groups.push(MulGroup {
                c_id,
                members,
                built: None,
            });
        }
    }

    if mul_groups.is_empty() {
        return Ok(None);
    }

    let mut dead_interior: IdMap<u32, ()> = IdMap::default();
    let mut bag_by_root: IdMap<u32, usize> = IdMap::default();
    for (bi, &(u, _, ref owned)) in bags.iter().enumerate() {
        if mod_bags.contains_key(&bi) {
            bag_by_root.insert(u, bi);
            for &inner in owned {
                dead_interior.insert(inner, ());
            }
        }
    }
    for &m_id in member_to_group.keys() {
        dead_interior.insert(m_id, ());
    }

    let mut became = Lease::new(cx.len());
    for &id in &order {
        if dead_interior.contains_key(&id) {
            continue;
        }
        if let Some(&bi) = bag_by_root.get(&id) {
            let items = &bags[bi].1;
            let mut rest: Vec<u32> = Vec::with_capacity(items.len());
            for &it in items {
                if let Some(&(gi, is_leader)) = member_to_group.get(&it) {
                    if !is_leader {
                        continue;
                    }
                    let prod = match mul_groups[gi].built {
                        Some(p) => p,
                        None => {
                            let c_id = mul_groups[gi].c_id;
                            let mut bases: Vec<u32> = mul_groups[gi]
                                .members
                                .iter()
                                .map(|&m| {
                                    let (b, _) = const_mul_parts(cx, m).unwrap();
                                    became.get(b).unwrap_or(b)
                                })
                                .collect();
                            bases.sort_by(|&a, &b| cx.order(a, b));
                            let mut iter = bases.into_iter();
                            let mut sum = iter.next().unwrap();
                            for b in iter {
                                sum = cx.c_bin(BinOp::Add, sum, b)?;
                            }
                            let p = cx.c_bin(BinOp::Mul, sum, c_id)?;
                            mul_groups[gi].built = Some(p);
                            p
                        }
                    };
                    rest.push(prod);
                } else {
                    rest.push(became.get(it).unwrap_or(it));
                }
            }
            rest.sort_by(|&a, &b| cx.order(a, b));
            let mut iter = rest.into_iter();
            let mut acc = iter.next().expect("non-empty bag");
            for x in iter {
                acc = cx.c_bin(BinOp::Add, acc, x)?;
            }
            became.insert(id, acc);
            continue;
        }
        let n = cx.node(id);
        let mut kids = [n.a, n.b, n.c];
        let mut changed = false;
        for (k, c) in n.children().enumerate() {
            let nc = became.get(c).unwrap_or(c);
            changed |= nc != c;
            kids[k] = nc;
        }
        let r = if changed { cx.rebuild(id, kids)? } else { id };
        became.insert(id, r);
    }
    let out: Vec<u32> = roots.iter().map(|&r| became.get(r).unwrap_or(r)).collect();
    Ok((out != roots).then_some(out))
}
