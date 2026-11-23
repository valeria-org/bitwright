//! Seed a range test of a weighted sum by keeping one literal weight and clearing
//! its peers. When the multipliers read fields of one word, combine their bit
//! requirements *before* inverting an offset: independent inverses can disagree
//! on carry bits. This is only a seed; evaluation decides whether it is a witness.
use super::{BinOp, Op, Program, UnOp, guard::Target};

fn literal(p: &Program, s: usize) -> Option<u64> {
    if let Op::Constant(v) = p.ops[s].op {
        Some(v)
    } else {
        None
    }
}

fn join(p: &Program, s: usize) -> Option<(usize, usize)> {
    match p.ops[s].op {
        Op::Binary(BinOp::Or, a, b) => Some((a, b)),
        Op::Unary(UnOp::Not, n) => {
            let Op::Binary(BinOp::And, a, b) = p.ops[n].op else {
                return None;
            };
            match (&p.ops[a].op, &p.ops[b].op) {
                (Op::Unary(UnOp::Not, x), Op::Unary(UnOp::Not, y)) => Some((*x, *y)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// A rotate lowered to complementary shifts of the same source. Both syntactic
/// spellings of OR occur before simplification, where guard sampling runs.
pub(super) fn rotation(p: &Program, s: usize) -> Option<(usize, u16)> {
    let (a, b) = join(p, s)?;
    for (l, r) in [(a, b), (b, a)] {
        if let Op::Binary(BinOp::Shl, x, i) = p.ops[l].op
            && let Op::Binary(BinOp::LShr, y, j) = p.ops[r].op
            && x == y
            && let (Some(i), Some(j)) = (literal(p, i), literal(p, j))
            && i < u64::from(p.ops[s].width)
            && j == u64::from(p.ops[s].width) - i
        {
            return Some((x, i as u16));
        }
    }
    None
}

#[derive(Clone, Copy)]
struct Field {
    slot: usize,
    mask: u64,
    ones: u64,
}

// Lift a factor's demanded bits through wiring until the first arithmetic word.
fn field(p: &Program, mut s: usize, mut bits: u64, mut ones: u64) -> Option<Field> {
    for _ in 0..12 {
        let ins = &p.ops[s];
        if ones & !ins.mask != 0 {
            return None;
        }
        bits &= ins.mask;
        match ins.op {
            Op::Unary(UnOp::Not, a) => {
                ones ^= bits;
                s = a;
            }
            Op::Zext(a) => s = a,
            Op::Extract(a, lo) => {
                bits <<= lo;
                ones <<= lo;
                s = a;
            }
            Op::Binary(BinOp::And, a, b) if literal(p, b).is_some() => {
                let k = literal(p, b)?;
                if ones & !k != 0 {
                    return None;
                }
                bits &= k;
                s = a;
            }
            Op::Binary(BinOp::LShr, a, b) => {
                let k = literal(p, b)?;
                if k >= 64 || ones > (ins.mask >> k) {
                    return None;
                }
                bits = (bits << k) & ins.mask;
                ones <<= k;
                s = a;
            }
            _ => {
                return Some(Field {
                    slot: s,
                    mask: bits,
                    ones,
                });
            }
        }
    }
    None
}

fn demand(p: &Program, s: usize, v: u64, plan: &mut Option<Field>) -> bool {
    let Some(f) = field(p, s, p.ops[s].mask, v) else {
        return false;
    };
    match plan {
        Some(old) if old.slot == f.slot && (old.ones ^ f.ones) & old.mask & f.mask == 0 => {
            old.mask |= f.mask;
            old.ones |= f.ones;
        }
        Some(_) => return false,
        None => *plan = Some(f),
    }
    true
}

// Asking a product for one can use all factors equal to one; zero needs just
// one zero factor. Failure/backtracking never carries constraints into a peer.
fn product(
    p: &Program,
    s: usize,
    v: u64,
    plan: &mut Option<Field>,
    round: usize,
    fuel: &mut u8,
) -> bool {
    if *fuel == 0 {
        return false;
    }
    *fuel -= 1;
    if let Some(k) = literal(p, s) {
        return k == v;
    }
    let Op::Binary(BinOp::Mul, a, b) = p.ops[s].op else {
        return demand(p, s, v, plan);
    };
    if v == 1 {
        return product(p, a, 1, plan, round, fuel) && product(p, b, 1, plan, round, fuel);
    }
    let (first, second) = if round & 1 == 0 { (a, b) } else { (b, a) };
    product(p, first, 0, plan, round >> 1, fuel) || product(p, second, 0, plan, round >> 1, fuel)
}

pub(super) fn propose(
    p: &Program,
    values: &[u64],
    root: usize,
    lo: u64,
    hi: u64,
    round: usize,
) -> Option<(usize, u64)> {
    let mut terms = [root; 8];
    let mut len = 1;
    let mut i = 0;
    while i < len {
        let s = terms[i];
        let pair = if let Op::Binary(BinOp::Add, a, b) = p.ops[s].op {
            Some((a, b))
        } else {
            join(p, s)
        };
        if let Some((a, b)) = pair {
            if len == terms.len() {
                return None;
            }
            terms[i] = a;
            terms[len] = b;
            len += 1;
        } else {
            i += 1;
        }
    }
    if len < 2 {
        return None;
    }
    let mut fuel = 48;
    for j in 0..len {
        let active = (j + round) % len;
        let Op::Binary(BinOp::Mul, a, b) = p.ops[terms[active]].op else {
            continue;
        };
        let Some(weight) = literal(p, b) else {
            continue;
        };
        if !(lo..=hi).contains(&weight) {
            continue;
        }
        let mut plan = None;
        if !product(p, a, 1, &mut plan, round, &mut fuel) {
            continue;
        }
        if !(0..len)
            .filter(|&i| i != active)
            .all(|i| product(p, terms[i], 0, &mut plan, round + i, &mut fuel))
        {
            continue;
        }
        let field = plan?;
        let seed = match round % 3 {
            0 => 0,
            1 => p.ops[field.slot].mask,
            _ => values[field.slot],
        };
        let target = Target {
            slot: field.slot,
            value: (seed & !field.mask) | field.ones,
        };
        if let Some(patch) = target.invert(p, values, &mut 32) {
            return Some(patch);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BitVec, Context, ParseOptions, Width};

    #[test]
    fn conflicting_zero_factor_uses_its_peer() {
        let mut cx = Context::new();
        let expr = cx
            .parse(
                "let %0 = ((x:16 << 5) | (x >>u 11)) + 191;
             let %1 = ((%0 >>u 2) & 5) * ((~%0 >>u 6) & 3);
             let %2 = (%0 & 4) * (%0 & 257);
             (%1 * 193 + %2 * z:16) == 193",
                &ParseOptions::width(Width::W16),
            )
            .unwrap();
        let (p, _) = Program::lower(&mut cx, expr.index(), &[], super::super::MAX_NODES).unwrap();
        let Op::Compare(_, lhs, _, _) = p.ops[p.goal].op else {
            panic!()
        };
        let mut values = vec![0; p.ops.len()];
        p.evaluate_with(|_| 23, &mut values);
        assert_eq!(values[p.goal], 0);
        let (s, word) = propose(&p, &values, lhs, 191, 199, 0).unwrap();
        let model: Vec<_> = p
            .symbols
            .iter()
            .enumerate()
            .map(|(i, sym)| {
                (
                    sym.key.clone(),
                    BitVec::from_u64(sym.width, if i == s { word } else { 23 }).unwrap(),
                )
            })
            .collect();
        assert_eq!(
            cx.eval(&[expr], &model[..]).unwrap(),
            [BitVec::from_bool(true)]
        );
    }
}
