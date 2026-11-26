//! Facts valid on a guard's true branch. A positive Boolean combination of
//! equalities can restrict a symbol to one or two words even when no individual
//! equality is implied. Outside that branch the symbol remains unrestricted.

use super::{Counter, Runner, Stop};
use crate::{BinOp, Context, UnOp, expr::Bounded, expr::OpCode};

// Read only the positive Boolean skeleton. Everything else, including a subtree
// beyond the cap, may be true: a dropped branch must never narrow the domain.
fn walk(cx: &Context, i: u32, left: &mut u32, atom: &mut impl FnMut(u32, u32) -> bool) -> bool {
    if *left == 0 {
        return true;
    }
    *left -= 1;
    let n = cx.node(i);
    match n.op {
        OpCode::And | OpCode::Or => {
            let a = walk(cx, n.a, left, atom);
            let b = walk(cx, n.b, left, atom);
            if n.op == OpCode::And { a && b } else { a || b }
        }
        OpCode::Eq if cx.node(n.a).op == OpCode::Sym && cx.node(n.b).op == OpCode::Const => {
            atom(n.a, n.b)
        }
        _ => true,
    }
}

const LIMIT: u32 = 128;

fn literal(cx: &Context, i: u32) -> (u32, u16, bool) {
    crate::expr::field::bit_literal(cx, i)
}

/// Read only mandatory conjuncts. A cap misses available assumptions; it
/// must never turn a disjunct into an assumption. Leave the original guard
/// itself in the DAG: substitutions in its siblings are only valid under it.
fn select_guard(cx: &Context, body: u32, order: &[u32]) -> Option<(u32, (u32, u16, bool))> {
    let mut stack = vec![body];
    let mut guards = Vec::new();
    for _ in 0..LIMIT {
        let Some(i) = stack.pop() else { break };
        let n = cx.node(i);
        if n.op == OpCode::And {
            stack.extend([n.a, n.b]);
        } else if guards.len() < 8 {
            guards.push((i, literal(cx, i)));
        }
    }
    order.iter().find_map(|&i| {
        let n = cx.node(i);
        if n.op != OpCode::Select {
            return None;
        }
        let (x, bit, _) = literal(cx, n.a);
        guards
            .iter()
            .copied()
            .find(|&(_, (y, j, _))| (x, bit) == (y, j))
    })
}

/// For a value used by both logical shifts, read a surviving constant shift
/// as a masked rotation. Complementary shifts then share one column even
/// when the sum uses the halves separately, never joining them at one node.
fn shift_slice(cx: &mut Context, i: u32) -> Result<u32, crate::Error> {
    let n = cx.node(i);
    let w = n.width;
    let Some(k) = cx.const_val(n.b).and_then(|v| v.to_u64()) else {
        return Ok(i);
    };
    if w > 64 || k == 0 || k >= u64::from(w) {
        return Ok(i);
    }
    let ones = u64::MAX >> (64 - w);
    let (rot, bits) = if n.op == OpCode::Shl {
        (k, (ones << k) & ones)
    } else {
        (u64::from(w) - k, ones >> k)
    };
    let r = cx.mk_const_u64(w, rot)?;
    let x = cx.c_bin(BinOp::RotL, n.a, r)?;
    let m = cx.mk_const_u64(w, bits)?;
    cx.c_bin(BinOp::And, x, m)
}

/// A split rotation is a single opaque word to column analysis. Preserve
/// that boundary when its counts fold in this cofactor, rather than treating
/// its two shifted halves as independently varying words in every sum above.
fn joined_shift(cx: &mut Context, i: u32) -> Result<u32, crate::Error> {
    let n = cx.node(i);
    let (a, b, neg) = match n.op {
        OpCode::Or | OpCode::Xor => (n.a, n.b, false),
        OpCode::And if cx.node(n.a).op == OpCode::Not && cx.node(n.b).op == OpCode::Not => {
            (cx.node(n.a).a, cx.node(n.b).a, true)
        }
        _ => return Ok(i),
    };
    let (na, nb) = (cx.node(a), cx.node(b));
    if n.width <= 64
        && na.op == OpCode::And
        && nb.op == OpCode::And
        && na.a == nb.a
        && let (Some(l), Some(r)) = (cx.const_val(na.b), cx.const_val(nb.b))
        && (l.limbs()[0] ^ r.limbs()[0]) == (u64::MAX >> (64 - n.width))
    {
        return if neg {
            cx.c_un(UnOp::Not, na.a)
        } else {
            Ok(na.a)
        };
    }
    if !neg && let Some((base, left)) = crate::expr::field::rotation_of(cx, i) {
        let k = cx.mk_const_u64(n.width, u64::from(left))?;
        return cx.c_bin(BinOp::RotL, base, k);
    }
    let (l, r) = match (na.op, nb.op) {
        (OpCode::Shl, OpCode::LShr) => (na, nb),
        (OpCode::LShr, OpCode::Shl) => (nb, na),
        _ => return Ok(i),
    };
    let k = |i| cx.const_val(i).and_then(|v| v.to_u64());
    if l.a != r.a
        || !k(l.b)
            .and_then(|a| a.checked_add(k(r.b)?))
            .is_some_and(|s| s == u64::from(n.width))
    {
        return Ok(i);
    }
    let rotation = cx.c_bin(BinOp::RotL, l.a, l.b)?;
    if neg {
        cx.c_un(UnOp::Not, rotation)
    } else {
        Ok(rotation)
    }
}

/// Column proofs can ignore high carries when only a low field is read. A
/// shared node needs the union of *every* user's demands, including guards.
/// The word transfer models up to 64 bits; use full-width proofs otherwise.
fn sum_demands(cx: &Context, order: &[u32]) -> Option<crate::hash::IdMap<u32, u64>> {
    if order.iter().any(|&i| cx.wid(i) > 64) {
        return None;
    }
    let mut masks = crate::hash::IdMap::default();
    masks.insert(*order.last()?, 1);
    for &i in order.iter().rev() {
        let Some(&mask) = masks.get(&i) else { continue };
        let n = cx.node(i);
        let kids = [n.a, n.b, n.c];
        super::demanded(
            &n,
            mask,
            |j| super::word_of(cx, kids[j], &cx.node(kids[j])),
            |j| cx.wid(kids[j]),
            |j, m| {
                let m = m & (u64::MAX >> (64 - cx.wid(kids[j])));
                if m != 0 {
                    *masks.entry(kids[j]).or_default() |= m;
                }
            },
        );
    }
    Some(masks)
}

/// A shared arithmetic word can occur once as a linear term and again under
/// several masks. Opening its addition in the first occurrence but treating
/// it as one atom under masks loses the identity. Try the most-used interior
/// words of the sum, with each word kept intact in *both* readers.
fn cut_candidates(
    cx: &Context,
    root: u32,
    uses: &super::super::Lease,
    work: &mut super::opaque_predicate::Work,
) -> [(u32, u32); 2] {
    let mut best = [(0, 0); 2];
    let mut stack = vec![(root, 0u8)];
    for _ in 0..384 {
        let Some((i, depth)) = stack.pop() else { break };
        if work.take(1).is_none() {
            break;
        }
        let n = cx.node(i);
        if i != root
            && !matches!(n.op, OpCode::Sym | OpCode::Const)
            && let Some(count) = uses.get(i)
            && count >= 2
            && !best.iter().any(|&(k, seen)| k != 0 && seen == i)
        {
            if count > best[0].0 {
                best[1] = best[0];
                best[0] = (count, i);
            } else if count > best[1].0 {
                best[1] = (count, i);
            }
        }
        match n.op {
            OpCode::Add | OpCode::Sub if depth == 0 => stack.extend([(n.a, 0), (n.b, 0)]),
            OpCode::Mul | OpCode::Shl if depth == 0 && cx.is_const(n.b) => stack.push((n.a, 0)),
            OpCode::Neg if depth == 0 => stack.push((n.a, 0)),
            OpCode::Not | OpCode::And | OpCode::Or | OpCode::Xor if depth < 2 => {
                stack.extend(
                    n.children()
                        .filter(|&c| !cx.is_const(c))
                        .map(|c| (c, depth + 1)),
                );
            }
            _ => (),
        }
    }
    best
}

/// Read the constrained cofactor bottom-up. Reconstruct arithmetic over
/// small Boolean bases before it is buried under other operators. No case
/// fact leaves the conjunction; a changed result must also be smaller.
fn select_cofactor(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    body: u32,
    order: &[u32],
) -> Result<Option<u32>, Stop> {
    use super::opaque_predicate::{Work, columns_cut, columns_low};
    let scan = 8 * order.len() as u64 + u64::from(LIMIT);
    let budget = (r.meter.left_in(|b| b.pass_work) / 3).min(1 << 16);
    if budget <= scan {
        return Ok(None);
    }
    let finding = order.len() as u64 + u64::from(LIMIT);
    r.meter.charge(Counter::PassWork, finding)?;
    let Some((guard, (x, bit, on))) = select_guard(cx, body, order) else {
        return Ok(None);
    };
    r.meter.charge(Counter::PassWork, scan - finding)?;
    let budget = budget - scan;
    let mut work = Work::new(budget);
    let demands = sum_demands(cx, order);
    let mut sums = super::super::Lease::new(cx.len());
    let mut uses = super::super::Lease::new(cx.len());
    let mut shifted = super::super::Lease::new(cx.len());
    for &i in order {
        let n = cx.node(i);
        for c in n.children() {
            uses.bump(c);
        }
        if matches!(n.op, OpCode::Shl | OpCode::LShr) {
            let flag = if n.op == OpCode::Shl { 1 } else { 2 };
            shifted.insert(n.a, shifted.get(n.a).unwrap_or(0) | flag);
        }
        if !matches!(n.op, OpCode::Add | OpCode::Sub) {
            for c in n.children() {
                if matches!(cx.node(c).op, OpCode::Add | OpCode::Sub) {
                    sums.insert(c, 0);
                }
            }
        }
    }
    let mut rewrites = super::super::Lease::new(cx.len());
    let mut kernels = super::cofactors::Sums::default();
    let mut parts = Vec::new();
    for &i in order {
        if i == guard {
            continue;
        }
        let n = cx.node(i);
        if n.op == OpCode::Select {
            let (y, j, value) = literal(cx, n.a);
            if (x, bit) == (y, j) {
                let arm = if value == on { n.b } else { n.c };
                rewrites.insert(i, rewrites.get(arm).unwrap_or(arm));
                continue;
            }
        }
        let mut kids = [0; 3];
        let mut changed = false;
        for (j, c) in n.children().enumerate() {
            kids[j] = rewrites.get(c).unwrap_or(c);
            changed |= kids[j] != c;
        }
        let mut cur = if changed {
            r.build(cx, |cx| cx.rebuild(i, kids))?
        } else {
            i
        };
        if matches!(n.op, OpCode::Shl | OpCode::LShr)
            && shifted.get(n.a) == Some(3)
            && matches!(cx.node(cur).op, OpCode::Shl | OpCode::LShr)
        {
            cur = r.build(cx, |cx| shift_slice(cx, cur))?;
        }
        if matches!(cx.node(cur).op, OpCode::And | OpCode::Or | OpCode::Xor) {
            cur = r.build(cx, |cx| joined_shift(cx, cur))?;
        }
        let bits = demands
            .as_ref()
            .and_then(|m| m.get(&i))
            .map_or(cx.wid(cur), |m| 64 - m.leading_zeros() as u16);
        if sums.contains(i)
            && matches!(cx.node(cur).op, OpCode::Add | OpCode::Sub)
            && cx.wid(cur) <= 64
            && work.left != 0
        {
            if let Some(v) = r.build(cx, |cx| kernels.collapse(cx, cur, false, &mut work))? {
                cur = v;
            }
            if matches!(cx.node(cur).op, OpCode::Add | OpCode::Sub) {
                let mut sum = columns_low(cx, cur, bits, &mut parts, &mut work);
                if sum.is_none() && parts.len() >= 3 {
                    for (count, cut) in cut_candidates(cx, cur, &uses, &mut work) {
                        if count == 0 {
                            break;
                        }
                        sum = columns_cut(cx, cur, bits, cut, &mut parts, &mut work);
                        if sum.is_some() {
                            break;
                        }
                    }
                }
                if let Some(s) = sum {
                    cur = s.build(r, cx, cx.wid(cur))?;
                }
            }
        }
        if cur != i {
            rewrites.insert(i, cur);
            if let Some(count) = uses.get(i)
                && count > uses.get(cur).unwrap_or(0)
            {
                uses.insert(cur, count);
            }
        }
    }
    r.meter.charge(Counter::PassWork, budget - work.left)?;
    let Some(out) = rewrites.get(root) else {
        return Ok(None);
    };
    let cap = order.len() as u32 - 1;
    Ok(matches!(
        cx.dag_size(&[cx.handle(out)], cap).map_err(Stop::Error)?,
        Bounded::Exact(_)
    )
    .then_some(out))
}

fn candidates(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    body: u32,
) -> Result<Vec<(u32, Vec<u32>)>, Stop> {
    let mut domains: Vec<(u32, Vec<u32>)> = Vec::new();
    let mut left = LIMIT;
    walk(cx, body, &mut left, &mut |sym, k| {
        if let Some((_, ks)) = domains.iter_mut().find(|(s, _)| *s == sym) {
            if ks.len() < 2 && !ks.contains(&k) {
                ks.push(k);
            }
        } else if domains.len() < 4 {
            domains.push((sym, vec![k]));
        }
        true
    });
    let work = u64::from(LIMIT - left);
    r.meter.charge(Counter::PassWork, work)?;
    Ok(domains)
}

// Can the guard hold outside these labels, even with every other atom true?
// Unlisted labels of this symbol count as possible, including past the cap.
fn closed(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    guard: u32,
    sym: u32,
    ks: &[u32],
) -> Result<bool, Stop> {
    let mut left = LIMIT;
    let outside = walk(cx, guard, &mut left, &mut |s, k| {
        s != sym || !ks.contains(&k)
    });
    r.meter.charge(Counter::PassWork, u64::from(LIMIT - left))?;
    Ok(!outside)
}

pub(super) fn specialize(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &super::MbaConfig,
    root: u32,
    order: &[u32],
) -> Result<Option<u32>, Stop> {
    let node = cx.node(root);
    if node.op != OpCode::Not || node.width != 1 || cx.node(node.a).op != OpCode::And {
        return Ok(None);
    }
    let body = node.a;
    let size = order.len() as u32;
    if let Some(e) = select_cofactor(r, cx, root, body, order)? {
        return Ok(Some(e));
    }
    let domains = candidates(r, cx, body)?;
    let mut paired = Vec::new();
    for (sym, ks) in domains {
        if !closed(r, cx, body, sym, &ks)? {
            continue;
        }
        r.meter
            .charge(Counter::PassWork, u64::from(size) * (1 + ks.len() as u64))?;
        let e = r.build(cx, |cx| {
            let mut branches = None;
            let mut replacements = crate::hash::IdMap::default();
            for &k in &ks {
                replacements.insert(sym, k);
                let reduced = cx.substitute_ids(&[body], &replacements)?[0];
                let guard = cx.c_cmp(crate::CmpOp::Eq, sym, k)?;
                let branch = cx.c_bin(BinOp::And, guard, reduced)?;
                branches = Some(match branches {
                    Some(b) => cx.c_bin(BinOp::Or, b, branch)?,
                    None => branch,
                });
            }
            cx.c_un(UnOp::Not, branches.expect("each domain has a label"))
        })?;
        // Don't expand into a tree of cases on later rounds.
        let cap = size * 3 / 4;
        if matches!(
            cx.dag_size(&[cx.handle(e)], cap).map_err(Stop::Error)?,
            Bounded::Exact(_)
        ) {
            return Ok(Some(e));
        }
        paired.push((sym, ks));
        if paired.len() == 2 {
            break;
        }
    }
    if let [(x, xs), (y, ys)] = paired.as_slice() {
        let mut repl = crate::hash::IdMap::default();
        for &a in xs {
            for &b in ys {
                repl.insert(*x, a);
                repl.insert(*y, b);
                r.meter.charge(Counter::PassWork, u64::from(size))?;
                let body = r.build(cx, |cx| Ok(cx.substitute_ids(&[body], &repl)?[0]))?;
                if !contradiction(r, cx, cfg, body)? {
                    return Ok(None);
                }
            }
        }
        return Ok(Some(r.build(cx, |cx| cx.mk_const_u64(1, 1))?));
    }
    Ok(None)
}

/// An ordered comparison of a select whose discriminator itself reads a select:
/// the outer select and its data often read different fields of the same inner
/// choice. Joining facts at that choice loses their correlation. Propagate
/// ordinary range/known-bit facts separately with its guard false, and true
/// at each value of one symbol whose domain the guard closes. Only a unanimous
/// singleton proves anything. No case facts or temporary DAGs enter the context.
pub(super) fn comparison(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    root: u32,
    order: &[u32],
) -> Result<Option<crate::BitVec>, Stop> {
    let n = cx.node(root);
    if !matches!(n.op, OpCode::Ult | OpCode::Ule | OpCode::Slt | OpCode::Sle) {
        return Ok(None);
    }
    let selected = if cx.is_const(n.a) {
        n.b
    } else if cx.is_const(n.b) {
        n.a
    } else {
        return Ok(None);
    };
    let selected = cx.node(selected);
    if selected.op != OpCode::Select {
        return Ok(None);
    }
    // One bounded look through the discriminator, not a search over DAG splits.
    fn first_guard(cx: &Context, i: u32, left: &mut u32) -> Option<u32> {
        if *left == 0 {
            return None;
        }
        *left -= 1;
        let n = cx.node(i);
        if n.op == OpCode::Select {
            return Some(n.a);
        }
        n.children().find_map(|c| first_guard(cx, c, left))
    }
    let mut left = 32;
    let guard = first_guard(cx, selected.a, &mut left);
    r.meter.charge(Counter::PassWork, 32 - u64::from(left))?;
    let Some(guard) = guard else { return Ok(None) };
    let mut domains = candidates(r, cx, guard)?;
    let mut keep = 0;
    for i in 0..domains.len() {
        if closed(r, cx, guard, domains[i].0, &domains[i].1)? {
            domains.swap(keep, i);
            keep += 1;
        }
    }
    if keep == 0 {
        return Ok(None);
    }

    use crate::{BitVec, Facts, Width};
    let mut places = super::super::Lease::new(cx.len());
    for (j, &i) in order.iter().enumerate() {
        places.insert(i, j as u32);
    }
    let mut facts = Vec::with_capacity(order.len());
    let mut case = |r: &mut Runner<'_, '_>, on: bool, label: Option<(u32, BitVec)>| {
        let cost = order.len() as u64;
        if r.meter.left_in(|b| b.fact_work) < cost {
            return Ok(None);
        }
        r.meter.charge(Counter::PassWork, cost)?;
        r.meter.spent.fact_work += cost;
        facts.clear();
        let top = Facts::top(Width::W1);
        for &i in order {
            let f = if i == guard {
                Facts::constant(&BitVec::from_bool(on))
            } else if let Some((s, k)) = label
                && i == s
            {
                Facts::constant(&k)
            } else {
                let n = cx.node(i);
                let mut args = [&top; 3];
                for (j, c) in n.children().enumerate() {
                    args[j] = &facts[places.get(c).expect("postordered child") as usize];
                }
                cx.transfer_local(i, &args[..n.op.arity()])
            };
            facts.push(f);
        }
        Ok::<_, Stop>(facts.last().and_then(Facts::as_constant))
    };
    let Some(want) = case(r, false, None)? else {
        return Ok(None);
    };
    for (s, ks) in &domains[..keep] {
        let mut all = true;
        for &k in ks {
            let k = cx.const_val(k).expect("guard label");
            if case(r, true, Some((*s, k)))? != Some(want) {
                all = false;
                break;
            }
        }
        if all {
            return Ok(Some(want));
        }
    }
    Ok(None)
}

// A single false conjunct suffices. Samples rank candidates only: the ordinary
// exact opaque sweep must actually produce zero, separately in every cofactor.
fn contradiction(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    cfg: &super::MbaConfig,
    body: u32,
) -> Result<bool, Stop> {
    if let Some(v) = cx.const_val(body) {
        return Ok(v.is_zero());
    }
    r.sample(cx, body)?;
    if !r.samples[&body].iter().all(|v| v.is_zero()) {
        return Ok(false);
    }
    let mut stack = vec![body];
    let mut candidates = Vec::new();
    for _ in 0..128 {
        let Some(i) = stack.pop() else { break };
        r.meter.charge(Counter::PassWork, 1)?;
        if !r.samples[&i].iter().all(|v| v.is_zero()) {
            continue;
        }
        let n = cx.node(i);
        if n.op == OpCode::And {
            stack.extend([n.a, n.b]);
        } else if !candidates.contains(&i) {
            candidates.push(i);
        }
    }
    candidates.sort_by_key(|&i| cx.meta[i as usize].height);
    for &i in candidates.iter().take(2) {
        r.meter.charge(Counter::PassWork, 768)?;
        if !matches!(
            cx.dag_size(&[cx.handle(i)], 768).map_err(Stop::Error)?,
            Bounded::Exact(_)
        ) {
            continue;
        }
        let e = super::sweep_inner(r, cx, cfg, i, false)?;
        if cx.const_val(e).is_some_and(|v| v.is_zero()) {
            return Ok(true);
        }
    }
    Ok(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOptions, Width};

    #[test]
    fn only_mandatory_guard_controls_select() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W8);
        let branch = cx
            .parse("select((trunc<4>(x) & 8) != 0, y, z)", &opt)
            .unwrap();
        let branch = cx.id(branch).unwrap();
        let condition = literal(&cx, cx.node(branch).a);
        for (s, expected) in [
            ("(0 <=s trunc<4>(x)) & (y == 2)", Some(false)),
            ("(trunc<4>(x) <s 0) & (z == 9)", Some(true)),
            ("((0 <=s trunc<4>(x)) | (y == 2)) & (z == 9)", None),
            ("(0 <=s x) & (y == 2)", None),
        ] {
            let body = cx.parse(s, &opt).unwrap();
            let hit = select_guard(&cx, cx.id(body).unwrap(), &[branch]);
            assert_eq!(hit.map(|(_, g)| g.2 == condition.2), expected, "{s}");
        }
    }

    #[test]
    fn normalized_signed_kernel_keeps_unrelated_terms() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W8);
        let mut kernels = super::super::cofactors::Sums::default();
        for k in [5u8, 39, 128, 211] {
            let text = format!("(x & y)*{k} + (x & ~y)*{k} + z*7 - x*{k}");
            let e = cx.parse(&text, &opt).unwrap();
            let e = cx.id(e).unwrap();
            let mut work = super::super::opaque_predicate::Work::new(1 << 14);
            let v = kernels
                .collapse(&mut cx, e, false, &mut work)
                .unwrap()
                .unwrap();
            let want = cx.parse("z * 7", &opt).unwrap();
            assert_eq!(v, cx.id(want).unwrap());
        }
        let e = cx
            .parse("(x & y)*5 + (x & ~z)*5 - x*5 + z*7", &opt)
            .unwrap();
        let e = cx.id(e).unwrap();
        let mut work = super::super::opaque_predicate::Work::new(1 << 14);
        assert!(
            kernels
                .collapse(&mut cx, e, false, &mut work)
                .unwrap()
                .is_none()
        );
        let mut work = super::super::opaque_predicate::Work::new(1);
        assert!(
            kernels
                .collapse(&mut cx, e, false, &mut work)
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn cofactor_demand_unions_shared_fields() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W8);
        let x = cx.parse("x", &opt).unwrap();
        for (s, mask) in [
            ("extract<1, 2>(x) == 1", 6),
            ("(extract<1, 2>(x) == 1) & (extract<5, 1>(x) == 0)", 38),
        ] {
            let e = cx.parse(s, &opt).unwrap();
            let order = cx.post_order_ids(&[cx.id(e).unwrap()]);
            assert_eq!(sum_demands(&cx, &order).unwrap()[&cx.id(x).unwrap()], mask);
        }
    }

    #[test]
    fn complementary_shifts_read_as_one_word() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W8);
        for (s, expected) in [
            ("~(x << 2) & ~(x >>u 6)", Some("~rotl(x, 2)")),
            ("(x << 3) ^ (x >>u 5)", Some("rotl(x, 3)")),
            ("(x << 3) ^ (x >>u 4)", None),
        ] {
            let e = cx.parse(s, &opt).unwrap();
            let i = cx.id(e).unwrap();
            let v = joined_shift(&mut cx, i).unwrap();
            let want = expected.map_or(e, |t| cx.parse(t, &opt).unwrap());
            assert_eq!(v, cx.id(want).unwrap());
        }
        let left = cx.parse("x << 3", &opt).unwrap();
        let right = cx.parse("x >>u 5", &opt).unwrap();
        let (a, b) = (cx.id(left).unwrap(), cx.id(right).unwrap());
        let a = shift_slice(&mut cx, a).unwrap();
        let b = shift_slice(&mut cx, b).unwrap();
        let joined = cx.c_bin(BinOp::Xor, a, b).unwrap();
        let rot = cx.parse("rotl(x, 3)", &opt).unwrap();
        assert_eq!(joined_shift(&mut cx, joined).unwrap(), cx.id(rot).unwrap());
    }

    #[test]
    fn large_conjunction_keeps_the_original_guard() {
        use crate::engine::{Budget, Engine, Run, Strategy};
        use crate::{BitVec, FnEnv, SymbolKey};
        use core::fmt::Write;

        let engine = Engine::builder()
            .builtin()
            .strategy(
                Strategy::deobfuscate()
                    .with_mba(super::super::MbaConfig::default().with_opaque_sweep(true)),
            )
            .build()
            .unwrap();
        // An inactive word with plenty of internal sharing. Its value
        // must not matter, nor may the specialized value escape its guard.
        let mut program = String::from("let h0 = x ^ y; ");
        for i in 1..70 {
            write!(program, "let h{i} = (h{} * x + y) ^ 5; ", i - 1).unwrap();
        }
        for near_miss in [false, true] {
            let mut cx = Context::new();
            let tail = if near_miss { "+ (x & 1)" } else { "" };
            let text = format!(
                "{program} let v = select((x & 8) != 0, h69, \
                (x & y)*5 + (x & ~y)*5 - x*5 {tail}); ~((0 <=s x) & (v == 1))"
            );
            let root = cx
                .parse(&text, &ParseOptions::width(Width::new(4).unwrap()))
                .unwrap();
            let out = engine
                .run(
                    &mut cx,
                    &[root],
                    Run::default().with_per_call(Budget::fuel(1 << 14)),
                )
                .unwrap();
            let result = out.roots[0].expr;
            if !near_miss {
                assert_eq!(cx.as_const(result).unwrap(), Some(BitVec::from_bool(true)));
            } else {
                for x in 0..16 {
                    for y in 0..16 {
                        let env = FnEnv(|key: &SymbolKey, w| {
                            let v = if matches!(key, SymbolKey::Str(s) if s.as_ref() == "x") {
                                x
                            } else {
                                y
                            };
                            Some(BitVec::wrapping_from_u64(w, v))
                        });
                        let values = cx.eval(&[root, result], &env).unwrap();
                        assert_eq!(values[0], BitVec::from_bool(x >= 8 || x & 1 == 0));
                        assert_eq!(values[0], values[1]);
                    }
                }
            }
        }
    }
}
