//! Prove a disjunction of labels by covering a small superset of its word's image.
//! Only a low prefix is needed below truncation and modular arithmetic. This keeps
//! a sparse mask small even when the discarded high bits are completely unknown.
//! Select arms are joined, and operands combined independently: extra values can
//! only prevent a proof. An incomplete enumeration never supplies a result.

use super::{Counter, Runner, Stop, opaque_predicate};
use crate::{Context, expr::OpCode, value::narrow};

const VALUES: usize = 64;
const WORK: u64 = 1 << 15;

fn spend(left: &mut u64, cost: usize) -> Option<()> {
    *left = left.checked_sub(cost as u64)?;
    Some(())
}

fn scalar(cx: &Context, i: u32) -> Option<u64> {
    cx.const_val(i)?.to_u64()
}

// Collect precisely `word == k₁ || word == k₂ || …` (including De Morgan form).
// Reject mixed words and don't let a heavily shared or deep Boolean DAG unroll.
fn labels(
    cx: &Context,
    i: u32,
    neg: bool,
    word: &mut Option<u32>,
    out: &mut Vec<u64>,
    depth: u8,
    left: &mut u64,
) -> Option<()> {
    spend(left, 1)?;
    let d = depth.checked_sub(1)?;
    let n = cx.node(i);
    match (neg, n.op) {
        (_, OpCode::Not) => labels(cx, n.a, !neg, word, out, d, left),
        (false, OpCode::Or) | (true, OpCode::And) => {
            labels(cx, n.a, neg, word, out, d, left)?;
            labels(cx, n.b, neg, word, out, d, left)
        }
        (false, OpCode::Eq) | (true, OpCode::Ne) if out.len() < VALUES => {
            if *word.get_or_insert(n.a) != n.a || cx.wid(n.a) > 64 {
                return None;
            }
            // Commutative constructors put constants on the right.
            out.push(scalar(cx, n.b)?);
            Some(())
        }
        _ => None,
    }
}

// Enumerate *all* low words with these fixed ones and independent free bits.
fn sparse(ones: u64, free: u64, left: &mut u64) -> Option<Vec<u64>> {
    let count = 1usize.checked_shl(free.count_ones())?;
    if count > VALUES {
        return None;
    }
    spend(left, count)?;
    let mut out = Vec::with_capacity(count);
    let mut sub = free;
    loop {
        out.push(ones | sub);
        if sub == 0 {
            return Some(out);
        }
        sub = sub.wrapping_sub(1) & free;
    }
}

fn map_values(
    mut vals: Vec<u64>,
    mask: u64,
    left: &mut u64,
    f: impl Fn(u64) -> u64,
) -> Option<Vec<u64>> {
    spend(left, vals.len())?;
    for v in &mut vals {
        *v = f(*v) & mask;
    }
    Some(vals)
}

fn image(cx: &Context, i: u32, bits: u16, depth: u8, left: &mut u64) -> Option<Vec<u64>> {
    spend(left, 1)?;
    let d = depth.checked_sub(1)?;
    let n = cx.node(i);
    if bits > n.width || n.width > 64 {
        return None;
    }
    let mask = u64::MAX >> (64 - bits);
    let mut vals = match n.op {
        OpCode::Const => return Some(vec![scalar(cx, i)? & mask]),
        OpCode::Extract => {
            let a = image(cx, n.a, bits.checked_add(n.b as u16)?, d, left)?;
            map_values(a, mask, left, |x| x >> n.b)?
        }
        OpCode::Zext => return image(cx, n.a, bits.min(cx.wid(n.a)), d, left),
        OpCode::Not | OpCode::Neg => {
            let a = image(cx, n.a, bits, d, left)?;
            map_values(a, mask, left, |x| {
                if n.op == OpCode::Neg {
                    x.wrapping_neg()
                } else {
                    !x
                }
            })?
        }
        OpCode::Select => {
            let mut a = image(cx, n.b, bits, d, left)?;
            let b = image(cx, n.c, bits, d, left)?;
            spend(left, b.len())?;
            a.extend(b);
            a
        }
        OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::And | OpCode::Or | OpCode::Xor => {
            if let Some(k) = scalar(cx, n.b) {
                let k = k & mask;
                let fixed = match n.op {
                    OpCode::And => Some((0, k)),
                    OpCode::Or => Some((k, mask ^ k)),
                    _ => None,
                };
                if let Some((ones, free)) = fixed
                    && let Some(a) = sparse(ones, free, left)
                {
                    return Some(a);
                }
                let op = n.op.as_bin()?;
                let a = image(cx, n.a, bits, d, left)?;
                map_values(a, mask, left, |x| {
                    narrow::bin(op, bits, x.into(), k.into()) as u64
                })?
            } else if matches!(n.op, OpCode::Add | OpCode::Sub)
                && let Some((factor, k)) = opaque_predicate::scaled_sum(cx, i, bits, left)
            {
                if k == 0 {
                    return Some(vec![0]);
                }
                let a = image(cx, factor, bits, d, left)?;
                map_values(a, mask, left, |x| x.wrapping_mul(k))?
            } else {
                let a = image(cx, n.a, bits, d, left)?;
                let b = image(cx, n.b, bits, d, left)?;
                let count = a.len() * b.len();
                if count > VALUES {
                    return None;
                }
                spend(left, count)?;
                let op = n.op.as_bin()?;
                let mut out = Vec::with_capacity(count);
                for x in a {
                    for &y in &b {
                        out.push(narrow::bin(op, bits, x.into(), y.into()) as u64);
                    }
                }
                out
            }
        }
        _ => return None,
    };
    spend(left, vals.len() * 7)?;
    vals.sort_unstable();
    vals.dedup();
    (vals.len() <= VALUES).then_some(vals)
}

fn proof(cx: &Context, root: u32, left: &mut u64) -> Option<bool> {
    let mut word = None;
    let mut allowed = Vec::new();
    labels(cx, root, false, &mut word, &mut allowed, 96, left)?;
    let word = word?;
    if allowed.len() < 2 {
        return None;
    }
    let vals = image(cx, word, cx.wid(word), 48, left)?;
    spend(left, 7 * (allowed.len() + vals.len()))?;
    allowed.sort_unstable();
    Some(vals.iter().all(|v| allowed.binary_search(v).is_ok()))
}

pub(super) fn covered(r: &mut Runner<'_, '_>, cx: &Context, root: u32) -> Result<bool, Stop> {
    let n = cx.node(root);
    if n.width != 1
        || !(n.op == OpCode::Or || (n.op == OpCode::Not && cx.node(n.a).op == OpCode::And))
    {
        return Ok(false);
    }
    let budget = WORK.min(r.meter.left_in(|b| b.mba_steps));
    let mut left = budget;
    let covered = proof(cx, root, &mut left) == Some(true);
    r.meter.charge(Counter::MbaSteps, budget - left)?;
    Ok(covered)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Expr, Width};

    fn membership(cx: &mut Context, value: Expr, labels: &[u64], neg: bool) -> Expr {
        let w = cx.width_of(value.index());
        let mut claim = if neg {
            cx.one(Width::W1)
        } else {
            cx.zero(Width::W1)
        }
        .unwrap();
        for &k in labels {
            let k = cx.constant_u64(w, k).unwrap();
            claim = if neg {
                let miss = cx.ne(value, k).unwrap();
                cx.and(claim, miss)
            } else {
                let hit = cx.eq(value, k).unwrap();
                cx.or(claim, hit)
            }
            .unwrap();
        }
        if neg { cx.not(claim).unwrap() } else { claim }
    }

    fn decide(cx: &Context, claim: Expr) -> Option<bool> {
        let mut left = WORK;
        proof(cx, claim.index(), &mut left)
    }

    #[test]
    fn sparse_prefix_select_needs_every_member() {
        let mut cx = Context::new();
        let source = cx.symbol("source", Width::W64).unwrap();
        let guard = cx.symbol("guard", Width::W1).unwrap();
        let ones = cx.constant_u64(Width::W64, 0xf6).unwrap();
        let masked = cx.or(source, ones).unwrap();
        let byte = cx.extract(masked, 0, Width::W8).unwrap();
        let three = cx.constant_u64(Width::W8, 3).unwrap();
        let five = cx.constant_u64(Width::W8, 5).unwrap();
        let factor = cx.select(guard, three, five).unwrap();
        let value = cx.mul(byte, factor).unwrap();
        let mut values: Vec<_> = [0xf6, 0xf7, 0xfe, 0xff]
            .into_iter()
            .flat_map(|x| [(x * 3) & 255, (x * 5) & 255])
            .collect();
        values.sort_unstable();
        values.dedup();
        for neg in [false, true] {
            for omitted in 0..=values.len() {
                let mut labels = values.clone();
                if omitted < values.len() {
                    labels.remove(omitted);
                }
                let claim = membership(&mut cx, value, &labels, neg);
                assert_eq!(decide(&cx, claim), Some(omitted == values.len()));
                assert_eq!(proof(&cx, claim.index(), &mut 2), None);
            }
        }
    }

    #[test]
    fn shared_factor_needs_an_exact_constant_cofactor() {
        let mut cx = Context::new();
        let w = Width::W8;
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let seed = cx.symbol("source", w).unwrap();
        let k = cx.constant_u64(w, 7).unwrap();
        let seed = cx.and(seed, k).unwrap();
        let d = cx.xor(x, y).unwrap();
        let nd = cx.not(d).unwrap();
        let a = cx.mul(seed, d).unwrap();
        let labels: Vec<_> = (0u8..8).map(|v| u64::from(v.wrapping_neg())).collect();
        for (arm, exact) in [(nd, true), (x, false)] {
            let b = cx.mul(arm, seed).unwrap();
            let sum = cx.add(a, b).unwrap();
            let full = membership(&mut cx, sum, &labels, false);
            assert_eq!(decide(&cx, full) == Some(true), exact);
            let missing = membership(&mut cx, sum, &labels[1..], false);
            assert_ne!(decide(&cx, missing), Some(true));
        }
    }

    #[test]
    fn unsupported_width_and_large_mask_are_not_partial_proofs() {
        let mut cx = Context::new();
        let x = cx.symbol("wide", Width::W128).unwrap();
        let high = cx.extract(x, 64, Width::W8).unwrap();
        let x = cx.symbol("byte", Width::W8).unwrap();
        let k = cx.constant_u64(Width::W8, 127).unwrap();
        let large = cx.and(x, k).unwrap();
        for value in [high, large] {
            let claim = membership(&mut cx, value, &[0, 1], false);
            assert_eq!(decide(&cx, claim), None);
        }
    }
}
