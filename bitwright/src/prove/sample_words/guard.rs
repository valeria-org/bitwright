//! Use a lane's intermediate values to change one symbol toward a comparison literal.
//! These are proposals, not inverse facts: another operand (or selector) can share the symbol.

use super::{BinOp, CmpOp, Op, Program, UnOp, binary};

#[derive(Clone, Copy)]
pub(super) struct Target {
    pub(super) slot: usize,
    pub(super) value: u64,
}

impl Target {
    pub(super) fn literal(p: &Program, a: usize, b: usize) -> Option<Self> {
        match (&p.ops[a].op, &p.ops[b].op) {
            (_, Op::Constant(v)) => Some(Self { slot: a, value: *v }),
            (Op::Constant(v), _) => Some(Self { slot: b, value: *v }),
            _ => None,
        }
    }

    pub(super) fn invert(self, p: &Program, values: &[u64], fuel: &mut u8) -> Option<(usize, u64)> {
        let Self { slot, value } = self;
        let ins = &p.ops[slot];
        let delta = values[slot] ^ value;
        if delta == 0 || delta & !ins.mask != 0 {
            return None;
        }
        *fuel = fuel.checked_sub(1)?;
        // Change only bits that differ. In particular, reclaim all unobserved bits
        // from this lane before subtracting an offset; carries then need no guessing.
        let flip = |a: usize, bits| Self { slot: a, value: values[a] ^ bits };
        if matches!(ins.op, Op::Unary(UnOp::Not, _) | Op::Binary(BinOp::Or, ..))
            && let Some((a, n)) = super::weighted::rotation(p, slot)
        {
            let bits = binary(BinOp::RotR, delta, u64::from(n), ins.width) & ins.mask;
            return flip(a, bits).invert(p, values, fuel);
        }
        let next = match ins.op {
            Op::Symbol(s) => return (delta & !p.symbols[s].free == 0).then_some((s, value)),
            Op::Unary(UnOp::Not, a) | Op::Zext(a) => flip(a, delta),
            Op::Extract(a, lo) => flip(a, delta << lo),
            Op::Select(c, t, e) => flip(if values[c] != 0 { t } else { e }, delta),
            Op::Binary(BinOp::Add, a, b) if matches!(p.ops[b].op, Op::Constant(_)) => {
                Self { slot: a, value: value.wrapping_sub(values[b]) & ins.mask }
            }
            Op::Binary(BinOp::Shl | BinOp::LShr, a, b)
                if matches!(p.ops[b].op, Op::Constant(_)) && values[b] < u64::from(ins.width) =>
            {
                let shift = values[b];
                if matches!(ins.op, Op::Binary(BinOp::Shl, ..)) {
                    if delta >> shift << shift != delta { return None; }
                    flip(a, delta >> shift)
                } else {
                    let bits = (delta << shift) & ins.mask;
                    if bits >> shift != delta { return None; }
                    flip(a, bits)
                }
            }
            Op::Binary(op @ (BinOp::RotL | BinOp::RotR), a, b)
                if matches!(p.ops[b].op, Op::Constant(_)) =>
            {
                let inverse = if op == BinOp::RotL { BinOp::RotR } else { BinOp::RotL };
                flip(a, binary(inverse, delta, values[b], ins.width) & ins.mask)
            }
            Op::Binary(op @ (BinOp::And | BinOp::Or), a, b) => {
                // Only flip bits that reach the output with the sibling held fixed.
                // This also follows a shift/OR rotation when the changed bits lie in one arm.
                for (child, other) in [(a, b), (b, a)] {
                    let blocked = if op == BinOp::And { !values[other] } else { values[other] };
                    if delta & blocked == 0
                        && !matches!(p.ops[child].op, Op::Constant(_))
                        && let Some(patch) = flip(child, delta).invert(p, values, fuel)
                    {
                        return Some(patch);
                    }
                }
                return None;
            }
            _ => return None,
        };
        next.invert(p, values, fuel)
    }
}

// The bounds are inclusive in the unsigned order after flipping `sign` (the
// sign bit for signed comparisons, zero otherwise). Only required comparisons
// belong here; comparisons inside negated conjunctions are not requirements.
pub(super) struct Interval {
    slot: usize,
    sign: u64,
    low: u64,
    high: u64,
    free: u64,
}

pub(super) fn intervals(p: &Program, terms: &[(usize, bool)]) -> Vec<Interval> {
    let mut result: Vec<Interval> = Vec::new();
    for &(i, want) in terms {
        let Op::Compare(op, a, b, width) = p.ops[i].op else { continue };
        let sign = match op {
            CmpOp::Ult | CmpOp::Ule => 0,
            CmpOp::Slt | CmpOp::Sle => 1 << (width - 1),
            _ => continue,
        };
        let Some(Target { slot, value }) = Target::literal(p, a, b) else { continue };
        let edge = value ^ sign;
        // x < c and !(c <= x) both impose a strict upper bound.
        let upper = (slot == a) == want;
        let strict = matches!(op, CmpOp::Ult | CmpOp::Slt) == want;
        let mask = p.ops[slot].mask;
        let (low, high) = if upper {
            let Some(high) = edge.checked_sub(u64::from(strict)) else { continue };
            (0, high)
        } else {
            let Some(low) = edge.checked_add(u64::from(strict)) else { continue };
            (low, mask)
        };
        if let Some(prev) = result.iter_mut().find(|r| r.slot == slot && r.sign == sign) {
            prev.low = prev.low.max(low);
            prev.high = prev.high.min(high);
        } else {
            let free = match p.ops[slot].op {
                Op::Symbol(s) => p.symbols[s].free,
                Op::Binary(op @ (BinOp::And | BinOp::Or), a, b) => {
                    Target::literal(p, a, b).map_or(mask, |t| {
                        if op == BinOp::And { t.value } else { !t.value & mask }
                    })
                }
                Op::Zext(a) => p.ops[a].mask,
                _ => mask,
            };
            result.push(Interval { slot, sign, low, high, free });
        }
    }
    result.retain(|r| r.low <= r.high);
    result
}

// Least value >= bound whose fixed bits agree with the lane. At the highest
// fixed-bit mismatch we either already round up, or must carry into the
// nearest higher changeable zero bit. All lower changeable bits can be zero.
fn ceil_masked(bound: u64, lane: u64, free: u64) -> Option<u64> {
    let mismatch = (lane ^ bound) & !free;
    if mismatch == 0 {
        return Some(bound);
    }
    let through = u64::MAX >> mismatch.leading_zeros();
    let fixed = lane & !free;
    if (lane & through) > (bound & through) {
        Some((bound & free & !through) | fixed)
    } else {
        let higher = free & !bound & !through;
        if higher == 0 { return None; }
        let bump = higher & higher.wrapping_neg();
        Some((bound & free & !(bump - 1)) | bump | fixed)
    }
}

impl Interval {
    // If the word hides an addend with unit coefficient, moving that one
    // input by this distance can put the original word inside its interval.
    pub(super) fn offset(&self, values: &[u64]) -> Option<u64> {
        Some(self.target(values)?.value.wrapping_sub(values[self.slot]))
    }
    fn target(&self, values: &[u64]) -> Option<Target> {
        let lane = values[self.slot] ^ self.sign;
        let word = if lane < self.low {
            ceil_masked(self.low, lane, self.free)?
        } else if lane > self.high {
            // Complement reverses unsigned order; rounding up there is rounding down here.
            !ceil_masked(!self.high, !lane, self.free)?
        } else {
            return None;
        };
        (self.low..=self.high).contains(&word).then_some(Target {
            slot: self.slot,
            value: word ^ self.sign,
        })
    }
}

pub(super) fn propose(
    p: &Program,
    values: &[u64],
    required: &[Target],
    ranges: &[Interval],
    cases: &[Target],
    round: usize,
) -> Option<(usize, u64)> {
    let mut fuel = 32;
    // Equality first, then a required interval. Internal case labels are a fallback:
    // they may select a different branch without improving the required conjuncts.
    fn candidates<T>(pool: &[T], round: usize) -> impl Iterator<Item = &T> {
        (0..pool.len().min(4)).map(move |off| &pool[(round + off) % pool.len()])
    }
    if let Some(patch) = candidates(required, round).find_map(|&t| t.invert(p, values, &mut fuel)) {
        return Some(patch);
    }
    let mut weighted = None;
    for r in candidates(ranges, round) {
        if let Some(t) = r.target(values) {
            if let Some(patch) = t.invert(p, values, &mut fuel) {
                return Some(patch);
            }
            if r.sign == 0 && weighted.is_none() {
                weighted = Some(r);
            }
        }
    }
    weighted.and_then(|r| super::weighted::propose(p, values, r.slot, r.low, r.high, round))
        .or_else(|| candidates(cases, round).find_map(|&t| t.invert(p, values, &mut fuel)))
}

#[cfg(test)]
mod tests {
    use super::ceil_masked;

    #[test]
    fn masked_ceiling_matches_small_domains() {
        for free in 0..16u64 {
            for lane in 0..16 {
                for bound in 0..16 {
                    let expected = (bound..16).find(|&v| (v ^ lane) & !free == 0);
                    assert_eq!(ceil_masked(bound, lane, free), expected);
                }
            }
        }
        assert_eq!(ceil_masked(u64::MAX, 0, !1), None);
        assert_eq!(ceil_masked(1 << 63, u64::MAX, 0), Some(u64::MAX));
    }
}
