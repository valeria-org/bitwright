//! A required masked equality can determine select tags even when their fields
//! were extracted at different widths. Keep the equality guarding the cofactor.
use super::{BinOp, Context, Counter, OpCode, Runner, Stop, UnOp};
use crate::expr::Bounded;
use crate::expr::field::{field, project};
use crate::hash::IdMap;

pub(super) fn specialize(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    order: &[u32],
) -> Result<Option<u32>, Stop> {
    let n = cx.node(root);
    if n.op != OpCode::Not || n.width != 1 || cx.node(n.a).op != OpCode::And {
        return Ok(None);
    }
    let body = n.a;
    let mut stack = vec![body];
    let mut guards = Vec::new();
    for _ in 0..64 {
        let Some(i) = stack.pop() else { break };
        r.meter.charge(Counter::PassWork, 1)?;
        let n = cx.node(i);
        if n.op == OpCode::And {
            stack.extend([n.a, n.b]);
        } else if n.op == OpCode::Eq
            && let Some(f) = field(cx, i)
            && f.bias != 0
            && f.mask.count_ones() > 1
        {
            guards.push((i, f));
            if guards.len() == 4 {
                break;
            }
        }
    }
    if guards.is_empty() {
        return Ok(None);
    }
    let mut map = IdMap::default();
    for &i in order {
        let n = cx.node(i);
        if matches!(n.op, OpCode::Or | OpCode::And)
            && n.width > 1
            && n.width <= 64
            && let Some(k) = cx.const_val(n.b).and_then(|k| k.to_u64())
        {
            let all = u64::MAX >> (64 - n.width);
            let free = if n.op == OpCode::And { k } else { all ^ k };
            if free.count_ones() <= 8 {
                let mut todo = free;
                let mut fixed = 0;
                let mut ones = if n.op == OpCode::Or { k } else { 0 };
                r.meter.charge(
                    Counter::PassWork,
                    u64::from(todo.count_ones()) * (32 + guards.len() as u64),
                )?;
                while todo != 0 {
                    let bit = todo.isolate_lowest_one();
                    todo ^= bit;
                    if let Some(test) = project(cx, n.a, bit, bit)
                        && let Some(value) = guards.iter().find_map(|&(_, g)| g.implies(test))
                    {
                        fixed |= bit;
                        if value {
                            ones |= bit;
                        }
                    }
                }
                if fixed != 0 {
                    let replacement = r.build(cx, |cx| {
                        let m = cx.mk_const_u64(n.width, free & !fixed)?;
                        let rest = cx.c_bin(BinOp::And, n.a, m)?;
                        let v = cx.mk_const_u64(n.width, ones)?;
                        cx.c_bin(BinOp::Or, rest, v)
                    })?;
                    map.insert(i, replacement);
                }
            }
        }
        if cx.node(i).op != OpCode::Eq || guards.iter().any(|&(g, _)| g == i) {
            continue;
        }
        r.meter
            .charge(Counter::PassWork, 16 + guards.len() as u64)?;
        let Some(test) = field(cx, i) else {
            continue;
        };
        if let Some(v) = guards.iter().find_map(|&(_, g)| g.implies(test)) {
            let k = r.build(cx, |cx| cx.mk_const_u64(1, u64::from(v)))?;
            map.insert(i, k);
        }
    }
    if map.len() < 2 {
        return Ok(None);
    }
    // A guard can itself contain a substituted test. Reattach the original
    // guards, not rewritten copies, so facts never escape their scope.
    r.meter
        .charge(Counter::PassWork, (order.len() * 2) as u64)?;
    let e = r.build(cx, |cx| {
        let on = cx.mk_const_u64(1, 1)?;
        for &(g, _) in &guards {
            map.insert(g, on);
        }
        let mut b = cx.substitute_ids(&[body], &map)?[0];
        for &(g, _) in &guards {
            b = cx.c_bin(BinOp::And, b, g)?;
        }
        cx.c_un(UnOp::Not, b)
    })?;
    let smaller = matches!(
        cx.dag_size(&[cx.handle(e)], order.len() as u32 * 7 / 8)
            .map_err(Stop::Error)?,
        Bounded::Exact(_)
    );
    if !smaller {
        return Ok(None);
    }
    // Simplify the newly exposed invariant multipliers before generic phases
    // distribute them over their cofactors and lose the shared factor.
    let order = cx.post_order_ids(&[e]);
    r.meter.charge(Counter::PassWork, order.len() as u64 * 3)?;
    let budget = (r.meter.left_in(|b| b.pass_work) / 5).min(32768);
    let mut left = budget;
    let mut rewrites = super::super::Lease::new(cx.len());
    for i in order {
        let n = cx.node(i);
        let mut kids = [0; 3];
        let mut changed = false;
        for (j, c) in n.children().enumerate() {
            kids[j] = rewrites.get(c).unwrap_or(c);
            changed |= kids[j] != c;
        }
        let mut v = if changed {
            r.build(cx, |cx| cx.rebuild(i, kids))?
        } else {
            i
        };
        let op = cx.node(v);
        if op.op == OpCode::Add
            && op.width <= 64
            && [op.a, op.b]
                .iter()
                .all(|&j| matches!(cx.node(j).op, OpCode::Mul | OpCode::Add))
            && let Some((f, k)) = super::opaque_predicate::scaled_sum(cx, v, op.width, &mut left)
        {
            v = r.build(cx, |cx| {
                let k = cx.mk_const_u64(op.width, k)?;
                cx.c_bin(BinOp::Mul, f, k)
            })?;
        }
        if i != v {
            rewrites.insert(i, v);
        }
    }
    r.meter.charge(Counter::PassWork, budget - left)?;
    Ok(Some(rewrites.get(e).unwrap_or(e)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BitVec, ParseOptions, Width};

    #[test]
    fn masked_bias_agrees_only_below_the_first_different_offset_bit() {
        let mut cx = Context::new();
        let p = ParseOptions::default();
        let guard = cx.parse("(extract<2,4>(x:8 + 23) | 5) == 7", &p).unwrap();
        let hit = cx.parse("((trunc<6>(x:8) + 23) & 40) == 8", &p).unwrap();
        let miss = cx.parse("((trunc<6>(x:8) + 23) & 40) == 0", &p).unwrap();
        let ambiguous = cx.parse("((trunc<6>(x:8) + 7) & 40) == 8", &p).unwrap();
        let g = field(&cx, guard.index()).unwrap();
        for (test, expected) in [(hit, Some(true)), (miss, Some(false)), (ambiguous, None)] {
            assert_eq!(g.implies(field(&cx, test.index()).unwrap()), expected);
            let mut seen = [false; 2];
            for x in 0..256 {
                let values = cx
                    .eval(
                        &[guard, test],
                        &[("x".into(), BitVec::from_u64(Width::W8, x).unwrap())][..],
                    )
                    .unwrap();
                if !values[0].is_zero() {
                    seen[usize::from(!values[1].is_zero())] = true;
                }
            }
            assert_eq!(seen, [expected != Some(true), expected != Some(false)]);
        }
    }

    #[test]
    fn rotation_carry_is_local_only_on_the_non_wrapping_slice() {
        let mut cx = Context::new();
        let p = ParseOptions::default();
        let guard = cx.parse("((x:8 + 63) & 136) == 8", &p).unwrap();
        let low = cx.parse("((rotl(x:8 + 7, 5) + 7) & 17) == 1", &p).unwrap();
        let wraps = cx.parse("((rotl(x:8 + 7, 5) + 7) & 49) == 1", &p).unwrap();
        let g = field(&cx, guard.index()).unwrap();
        assert_eq!(g.implies(field(&cx, low.index()).unwrap()), Some(true));
        assert!(field(&cx, wraps.index()).is_none());
        let mut seen = [false; 2];
        for x in 0..256 {
            let values = cx
                .eval(
                    &[guard, low, wraps],
                    &[("x".into(), BitVec::from_u64(Width::W8, x).unwrap())][..],
                )
                .unwrap();
            assert_eq!(values[0], values[1]);
            if !values[0].is_zero() {
                seen[usize::from(!values[2].is_zero())] = true;
            }
        }
        assert_eq!(seen, [true, true]);
    }
}
