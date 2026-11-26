//! Whole-DAG associative-commutative common sub-sum factoring (`share_sums`).
//!
//! Iterative round functions (ARX mixers, cryptographic compression rounds, multi-round
//! accumulators) repeatedly add new deltas into live multi-use state sums. When each round's
//! linear region is canonicalized in isolation, changing a single low-ranked summand at the
//! front of a left-associated `Add` chain invalidates hash-consing for every subsequent link
//! in the chain, leaving dozens of copies of the same 40-to-60-term sub-sum as single-use
//! `Add` spines (`uses == 1`).
//!
//! [`share_sums`] collects maximal single-use `Add` bags across the live cone of `roots`,
//! groups them by width (`1..=512`), and runs bounded windowed disjoint-pair factoring
//! (Re-Pair / Wallace-style pair CSE) over virtual pair identifiers before materializing
//! only the modified sums in a single bottom-up pass. Every merged pair appears in at least
//! two distinct sums, so every step strictly reduces the live `Add` count while simultaneously
//! balancing deep linear ripple chains.

use core::cmp::Ordering;

use super::Lease;
use crate::error::Error;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::BinOp;

/// Minimum `Add` nodes in the live cone before scanning for cross-sum sharing.
const MIN_CONE_ADDS: usize = 128;

/// Maximum leaves flattened into a single `Add` bag (any deeper single-use `Add` child becomes
/// its own bag root, preserving completeness while keeping per-bag work linear).
const MAX_BAG: usize = 512;

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

/// Factors common sub-sums across single-use `Add` chains in `roots`, spending at most
/// `max_work` bag-element inspections. Returns `Ok(Some((new_roots, work)))` only when the
/// live multi-root DAG size strictly shrinks.
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

    // Pre-factor single-use `Mul(x_i, C)` summands sharing `C` inside single-use `Add` bags so
    // `(x_1 + ... + x_k)` sums become visible to cross-bag sub-sum sharing below.
    let pre_roots = factor_single_use_const_muls(cx, roots)?;
    let cur_roots: &[u32] = pre_roots.as_deref().unwrap_or(roots);
    let order = if pre_roots.is_some() {
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
            bags.push(Bag {
                root: u,
                width: un.width,
                items,
                owned_adds,
                modified: false,
            });
        }
    }

    let finish_early = |cx: &mut Context,
                        cand: Option<Vec<u32>>,
                        work: usize|
     -> Result<Option<(Vec<u32>, u64)>, Error> {
        let Some(new_roots) = cand else {
            return Ok(None);
        };
        if new_roots == roots {
            return Ok(None);
        }
        let new_handles: Vec<_> = new_roots.iter().map(|&r| cx.handle(r)).collect();
        let shrunk = matches!(
            cx.dag_size(&new_handles, old_size.saturating_sub(1))?,
            crate::expr::Bounded::Exact(_)
        );
        Ok(shrunk.then_some((new_roots, work as u64)))
    };

    if bags.len() < 2 {
        return finish_early(cx, pre_roots, order.len());
    }

    let mut by_width: IdMap<u16, Vec<usize>> = IdMap::default();
    for (idx, bag) in bags.iter().enumerate() {
        by_width.entry(bag.width).or_default().push(idx);
    }
    let mut groups: Vec<(u16, Vec<usize>)> = by_width
        .into_iter()
        .filter(|(_, idxs)| idxs.iter().filter(|&&i| bags[i].items.len() >= 3).count() >= 2)
        .collect();
    if groups.is_empty() {
        return finish_early(cx, pre_roots, order.len());
    }
    groups.sort_unstable_by_key(|&(w, _)| w);

    const WINDOW: usize = 16;
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
        return finish_early(cx, pre_roots, work);
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
                            let sh_c = cx.mk_const(&crate::BitVec::wrapping_from_u64(
                                width,
                                u64::from(bit),
                            ))?;
                            real_items.push(cx.c_bin(BinOp::Shl, x, sh_c)?);
                        }
                    }
                }
            }
            if real_items.is_empty() {
                let z = cx.mk_const(&crate::BitVec::zero(width))?;
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
    if let Some(mul_factored) = factor_single_use_const_muls(cx, &new_roots)? {
        new_roots = mul_factored;
    }
    if new_roots == roots {
        return Ok(None);
    }
    let new_handles: Vec<_> = new_roots.iter().map(|&r| cx.handle(r)).collect();
    let shrunk = matches!(
        cx.dag_size(&new_handles, old_size.saturating_sub(1))?,
        crate::expr::Bounded::Exact(_)
    );
    Ok(shrunk.then_some((new_roots, work as u64)))
}

/// Factors single-use `Mul(x_i, C)` summands sharing the same constant multiplier `C` (`k >= 2`)
/// within maximal single-use `Add` bags into `(x_1 + ... + x_k) * C` (replacing `k` multipliers
/// with `1` multiplier and strictly shrinking both the expression DAG and bit-blasted AIG).
fn factor_single_use_const_muls(
    cx: &mut Context,
    roots: &[u32],
) -> Result<Option<Vec<u32>>, Error> {
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
    let mut dead_interior: IdMap<u32, ()> = IdMap::default();
    let mut bag_plan: IdMap<u32, Vec<u32>> = IdMap::default();
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
        // Check if at least two single-use `Mul(_, C)` summands share `C`.
        let mut by_c: IdMap<u32, usize> = IdMap::default();
        let mut has_group = false;
        for &it in &items {
            if uses.get(&it).copied().unwrap_or(0) == 1
                && let Some((_, c_id)) = const_mul_parts(cx, it)
            {
                let cnt = by_c.entry(c_id).or_default();
                *cnt += 1;
                if *cnt >= 2 {
                    has_group = true;
                }
            }
        }
        if has_group {
            for id in owned {
                dead_interior.insert(id, ());
            }
            bag_plan.insert(u, items);
        }
    }
    if bag_plan.is_empty() {
        return Ok(None);
    }

    let mut became = Lease::new(cx.len());
    for &id in &order {
        if dead_interior.contains_key(&id) {
            continue;
        }
        if let Some(items) = bag_plan.get(&id) {
            let mut groups: IdMap<u32, Vec<u32>> = IdMap::default();
            let mut group_order: Vec<u32> = Vec::new();
            let mut rest: Vec<u32> = Vec::new();
            for &it in items {
                if uses.get(&it).copied().unwrap_or(0) == 1
                    && let Some((base, c_id)) = const_mul_parts(cx, it)
                {
                    let mapped_base = became.get(base).unwrap_or(base);
                    let entry = groups.entry(c_id).or_default();
                    if entry.is_empty() {
                        group_order.push(c_id);
                    }
                    entry.push(mapped_base);
                } else {
                    rest.push(became.get(it).unwrap_or(it));
                }
            }
            for c_id in group_order {
                let mut bases = groups.remove(&c_id).unwrap_or_default();
                if bases.len() == 1 {
                    let prod = cx.c_bin(BinOp::Mul, bases[0], c_id)?;
                    rest.push(prod);
                } else if bases.len() >= 2 {
                    bases.sort_by(|&a, &b| cx.order(a, b));
                    let mut iter = bases.into_iter();
                    let mut sum = iter.next().unwrap();
                    for b in iter {
                        sum = cx.c_bin(BinOp::Add, sum, b)?;
                    }
                    let prod = cx.c_bin(BinOp::Mul, sum, c_id)?;
                    rest.push(prod);
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
