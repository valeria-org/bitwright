//! A word assembled from a few Boolean choices may be compared with a label,
//! with additional tests on its carries. Enumerate the *choices*, not their
//! word-sized sources. A cube in that table is a conjunction of literals.

use super::{BinOp, Context, Counter, Exhaust, OpCode, Runner, Stop, UnOp, run_lanes};
use crate::{expr::Bounded, hash::IdMap};

const BITS: usize = 9;

fn sum_test(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    matches!(n.op, OpCode::Eq | OpCode::Ne)
        && matches!(cx.node(n.a).op, OpCode::Add | OpCode::Sub)
        && cx.node(n.b).op == OpCode::Const
}

/// Every path to a nonconstant input must pass through a one-bit cut node.
/// Such nodes are independent here: a cube valid even on impossible rows
/// remains valid after their original expressions are plugged back in.
fn cut(sc: &mut Exhaust) -> Option<usize> {
    sc.over.clear();
    for (n, kids) in &sc.below {
        let closed = n.op == OpCode::Const
            || (n.op.arity() != 0
                && n.op.as_ext().is_none()
                && kids[..n.op.arity()]
                    .iter()
                    .all(|&p| sc.over[p as usize] != 2));
        sc.over.push(if closed {
            0
        } else if n.width == 1 {
            1
        } else {
            2
        });
    }
    if sc.over.last() != Some(&0) {
        return None;
    }
    sc.live.clear();
    sc.live.resize(sc.below.len(), false);
    *sc.live.last_mut()? = true;
    sc.syms.clear();
    let mut choices = 0;
    for p in (0..sc.below.len()).rev() {
        if !sc.live[p] {
            continue;
        }
        if sc.over[p] == 1 {
            if sc.syms.len() == BITS {
                return None;
            }
            sc.syms.push((p as u32, 1));
        } else {
            let (n, kids) = sc.below[p];
            choices += usize::from(n.op == OpCode::Select);
            for &c in &kids[..n.op.arity()] {
                sc.live[c as usize] = true;
            }
        }
    }
    if choices < 2 || sc.syms.is_empty() {
        return None;
    }
    sc.above_inputs();
    Some(sc.syms.len())
}

fn cube(sc: &mut Exhaust, cx: &Context, i: u32, left: &mut u64) -> Option<(usize, usize, bool)> {
    if !sc.walk(cx, i)
        || sc
            .below
            .iter()
            .filter(|(n, _)| n.op == OpCode::Select)
            .take(2)
            .count()
            < 2
    {
        return None;
    }
    // Prefer the actual inputs when small: this preserves correlations
    // between the choices, and can recover an equality on the original word.
    sc.demands(cx);
    let bits = sc
        .syms
        .iter()
        .map(|&(_, m)| m.count_ones() as usize)
        .sum::<usize>();
    let bits = if bits <= BITS {
        sc.above(None);
        bits
    } else {
        cut(sc)?
    };
    let points = 1usize << bits;
    // Keep the complete table in one pass, and charge the compiled word
    // evaluations at the same rate as the exhaustive certificate.
    if points * sc.kept.len() > super::EXHAUSTIVE_LANE_WORDS {
        return None;
    }
    let cost =
        (points as u64 * sc.kept.len() as u64).div_ceil(super::WORD_EVALS) + sc.kept.len() as u64;
    *left = left.checked_sub(cost)?;
    sc.bases.clear();
    if !sc.program(cx) {
        return None;
    }
    sc.lanes_for(points as u64);
    sc.pass_of(points);
    for (j, &(slot, _, _)) in sc.inputs.iter().enumerate() {
        sc.lanes[slot as usize * points..][..points]
            .copy_from_slice(&sc.spreads[j * points..][..points]);
    }
    run_lanes(&sc.prog, &mut sc.lanes, points);
    let row = &sc.lanes[sc.root * points..][..points];
    let ones = row.iter().filter(|&&v| v != 0).count();
    let negated = ones > points / 2;
    let count = if negated { points - ones } else { ones };
    if count == 0 {
        return Some((0, 0, !negated));
    }
    if !count.is_power_of_two() {
        return None;
    }
    let mut all = points - 1;
    let mut any = 0;
    for (j, &v) in row.iter().enumerate() {
        if (v != 0) != negated {
            all &= j;
            any |= j;
        }
    }
    let variable = all ^ any;
    // Every selected row lies in the box. Equal cardinalities prove the
    // converse too, unlike checking just a representative or the corners.
    (count == 1usize << variable.count_ones()).then_some(((points - 1) ^ variable, all, negated))
}

/// Rebuild over the recovered tests. On the arm guarded by `x == k` the
/// *data* reads of x, not just other tests of x, can be replaced by k.
/// Keep that substitution scoped to the arm (or the other conjunct).
fn rebuild(
    cx: &mut Context,
    order: &[u32],
    map: &mut IdMap<u32, u32>,
    left: &mut u64,
    before: u32,
) -> Result<u32, crate::Error> {
    let mut fixed = IdMap::default();
    for &i in order {
        if map.contains_key(&i) {
            continue;
        }
        let n = cx.node(i);
        let mut kids = [0; 3];
        let mut changed = false;
        for (j, c) in n.children().enumerate() {
            kids[j] = map.get(&c).copied().unwrap_or(c);
            changed |= kids[j] != c;
        }
        if !changed {
            continue;
        }
        let guards = match n.op {
            OpCode::Select => 1,
            OpCode::And | OpCode::Or if n.width == 1 => 2,
            _ => 0,
        };
        for j in 0..guards {
            let g = cx.node(kids[j]);
            if !matches!(g.op, OpCode::Eq | OpCode::Ne)
                || cx.node(g.a).op != OpCode::Sym
                || cx.node(g.b).op != OpCode::Const
            {
                continue;
            }
            let arm = match (n.op, g.op) {
                (OpCode::Select, OpCode::Eq) => 1,
                (OpCode::Select, OpCode::Ne) => 2,
                (OpCode::And, OpCode::Eq) | (OpCode::Or, OpCode::Ne) => 1 - j,
                _ => continue,
            };
            if cx.node(kids[arm]).op.arity() == 0 {
                if kids[arm] == g.a {
                    kids[arm] = g.b;
                }
                continue;
            }
            let bound = order.len() as u64 + u64::from(cx.len() as u32 - before);
            if *left < bound {
                break;
            }
            *left -= bound;
            fixed.clear();
            fixed.insert(g.a, g.b);
            kids[arm] = cx.substitute_ids(&[kids[arm]], &fixed)?[0];
        }
        map.insert(i, cx.rebuild(i, kids)?);
    }
    let root = *order.last().expect("a sweep has a root");
    Ok(map.get(&root).copied().unwrap_or(root))
}

pub(super) fn reduce(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    order: &[u32],
) -> Result<Option<u32>, Stop> {
    let budget = (r.meter.left_in(|b| b.pass_work) / 8).min(1 << 16);
    let scan = order.len() as u64;
    if budget < scan * 4 {
        return Ok(None);
    }
    let mut left = budget - scan;
    let mut map = IdMap::default();
    let before = cx.len() as u32;
    for &i in order {
        let n = cx.node(i);
        if !(sum_test(cx, i)
            || (n.width == 1
                && matches!(n.op, OpCode::And | OpCode::Or)
                && (sum_test(cx, n.a) || sum_test(cx, n.b))))
        {
            continue;
        }
        // Each walk is below this sweep's root, including everything below
        // the prospective cut; reserve the walk before beginning it.
        if left < scan * 3 {
            break;
        }
        left -= scan * 3;
        let sc = &mut r.mba.exhaust;
        let Some((mask, bits, negate)) = cube(sc, cx, i, &mut left) else {
            continue;
        };
        let (mut mask, mut bits) = (mask as u64, bits as u64);
        let mut lits = [(0, 0, 0); BITS];
        for (dst, &(slot, m, _)) in lits.iter_mut().zip(&sc.inputs) {
            *dst = (
                sc.order[sc.kept[slot as usize] as usize],
                super::spread(&mut mask, m),
                super::spread(&mut bits, m),
            );
        }
        let e = r.build(cx, |cx| {
            let mut term = cx.mk_const_u64(1, 1)?;
            for &(mut x, mask, bits) in &lits {
                if mask == 0 {
                    continue;
                }
                let width = cx.wid(x);
                let value = if width == 1 {
                    if bits != 0 { x } else { cx.c_un(UnOp::Not, x)? }
                } else {
                    if mask != u64::MAX >> (64 - width) {
                        let m = cx.mk_const_u64(width, mask)?;
                        x = cx.c_bin(BinOp::And, x, m)?;
                    }
                    let k = cx.mk_const_u64(width, bits)?;
                    cx.c_cmp(crate::CmpOp::Eq, x, k)?
                };
                term = cx.c_bin(BinOp::And, term, value)?;
            }
            if negate {
                cx.c_un(UnOp::Not, term)
            } else {
                Ok(term)
            }
        })?;
        if e != i {
            map.insert(i, e);
        }
    }
    let out = if map.is_empty() {
        None
    } else {
        r.meter.charge(Counter::PassWork, scan * 2)?;
        Some(r.build(cx, |cx| rebuild(cx, order, &mut map, &mut left, before))?)
    };
    r.meter.charge(Counter::PassWork, budget - left)?;
    let Some(out) = out else {
        return Ok(None);
    };
    if matches!(
        cx.dag_size(&[cx.handle(out)], order.len() as u32 - 1)
            .map_err(Stop::Error)?,
        Bounded::Exact(_)
    ) {
        Ok(Some(out))
    } else {
        super::discard(r, cx, before);
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BitVec, FnEnv, ParseOptions, SymbolKey, Width};

    // Make an encoded predicate of two comparisons, including one whose true
    // rows form a diagonal rather than a box. A diagonal must not become a cube.
    #[test]
    fn recognizes_a_singleton_but_not_a_diagonal() {
        let mut cx = Context::new();
        let parse = ParseOptions::width(Width::W8);
        let sum = "select((#0:8 & 1:8) == 1:8, 3:8, 0:8) + select((#0:8 & 2:8) == 2:8, 3:8, 0:8)";
        let mut sc = Exhaust::default();
        for (k, expected) in [(6, Some((3, 3, false))), (3, None), (7, Some((0, 0, true)))] {
            let e = cx.parse(&format!("({sum}) == {k}:8"), &parse).unwrap();
            assert_eq!(cube(&mut sc, &cx, cx.id(e).unwrap(), &mut 65536), expected);
        }
    }

    #[test]
    fn a_boolean_cut_must_cover_every_wide_input() {
        let mut cx = Context::new();
        let p = ParseOptions::width(Width::W64);
        let sum = "select(x == y, 3, 0) + select(y == z, 3, 0)";
        let mut sc = Exhaust::default();
        let closed = cx.parse(&format!("({sum}) == 6"), &p).unwrap();
        assert_eq!(
            cube(&mut sc, &cx, cx.id(closed).unwrap(), &mut 65536),
            Some((3, 3, false))
        );
        let open = cx.parse(&format!("({sum} + z) == 6"), &p).unwrap();
        assert_eq!(cube(&mut sc, &cx, cx.id(open).unwrap(), &mut 65536), None);
    }

    #[test]
    fn specializes_data_only_inside_the_guarded_arm() {
        let mut cx = Context::new();
        let p = ParseOptions::width(Width::W8);
        let e = cx
            .parse("select(#1:1, #0:8 + 4:8, #0:8 + 1:8)", &p)
            .unwrap();
        let guard = cx.parse("#0:8 == 3:8", &p).unwrap();
        let old = cx.parse("#1:1", &p).unwrap();
        let order = cx.post_order_ids(&[cx.id(e).unwrap()]);
        let mut map = IdMap::default();
        map.insert(cx.id(old).unwrap(), cx.id(guard).unwrap());
        let before = cx.len() as u32;
        let out = rebuild(&mut cx, &order, &mut map, &mut 65536, before).unwrap();
        for x in 0..=255 {
            let env = FnEnv(|s: &SymbolKey, w: Width| {
                BitVec::from_u64(
                    w,
                    if s == &SymbolKey::U64(0) {
                        x
                    } else {
                        u64::from(x == 3)
                    },
                )
                .ok()
            });
            let vals = cx.eval(&[e, cx.handle(out)], &env).unwrap();
            assert_eq!(vals[0], vals[1]);
        }
    }
}
