//! A masked comparison on a word plus a modular offset.
use super::{Context, OpCode};
#[cfg(any(feature = "mba", feature = "prove"))]
#[derive(Clone, Copy)]
pub(crate) struct Field {
    pub(crate) base: u32,
    pub(crate) bias: u64,
    pub(crate) mask: u64,
    bits: u64,
}

// Read an equality as `(base + bias) & mask == bits`, at most 64 bits.
// A truncation only drops high bits. Crossing an addition is sound even for a
// sparse mask: record the offset, don't subtract it independently in each field.
#[cfg(any(feature = "mba", feature = "prove"))]
pub(crate) fn field(cx: &Context, eq: u32) -> Option<Field> {
    let n = cx.node(eq);
    if n.op != OpCode::Eq {
        return None;
    }
    let w = cx.wid(n.a);
    if w > 64 {
        return None;
    }
    project(cx, n.a, u64::MAX >> (64 - w), cx.const_val(n.b)?.to_u64()?)
}

/// Recognize a rotation by a constant, whether spelled `rotl`/`rotr` or as
/// complementary shifts `(x << l) | (x >>u r)`, `(x << l) ^ (x >>u r)`, or
/// De Morgan `~(~(x << l) & ~(x >>u r))`. Returns `(base, left_rot)` with
/// `left_rot < width`.
#[cfg(any(feature = "mba", feature = "prove"))]
pub(crate) fn rotation_of(cx: &Context, x: u32) -> Option<(u32, u32)> {
    let n = cx.node(x);
    let w = u64::from(n.width);
    if w == 0 || w > 64 {
        return None;
    }
    let k = |i| cx.const_val(i)?.to_u64();
    if matches!(n.op, OpCode::RotL | OpCode::RotR) {
        let s = k(n.b)? % w;
        let left = if n.op == OpCode::RotL { s } else { (w - s) % w };
        return Some((n.a, left as u32));
    }
    let (a, b) = match n.op {
        OpCode::Or | OpCode::Xor => (n.a, n.b),
        OpCode::Not => {
            let and = cx.node(n.a);
            if and.op != OpCode::And {
                return None;
            }
            let (l, r) = (cx.node(and.a), cx.node(and.b));
            if l.op != OpCode::Not || r.op != OpCode::Not {
                return None;
            }
            (l.a, r.a)
        }
        _ => return None,
    };
    let (l, r) = if cx.node(a).op == OpCode::Shl {
        (cx.node(a), cx.node(b))
    } else {
        (cx.node(b), cx.node(a))
    };
    if l.op != OpCode::Shl || r.op != OpCode::LShr || l.a != r.a {
        return None;
    }
    let (left, right) = (k(l.b)?, k(r.b)?);
    (left < w && right < w && left + right == w).then_some((l.a, left as u32))
}

/// A Boolean node, or the single bit it tests: `(word, bit_index, polarity)` where
/// `polarity` is the value of that bit making the predicate true. Recognizes all
/// common sign-bit spellings (`x <s 0`, `0 <=s x`, `x <=s -1`, `-1 <s x`,
/// `smin <=u x`, `x <u smin`, `smax <u x`, `x <=u smax`), single-bit mask tests
/// `(x & 2^k) == 2^k` / `!= 0`, `extract<k, 1>(x)`, and negations thereof.
pub(crate) fn bit_literal(cx: &Context, i: u32) -> (u32, u16, bool) {
    use crate::BitVec;
    let n = cx.node(i);
    let scalar = |i| cx.const_val(i).and_then(|k| k.to_u64());
    let bit = |x, j, on| {
        let src = cx.node(x);
        if src.op == OpCode::Extract {
            (src.a, src.b as u16 + j, on)
        } else {
            (x, j, on)
        }
    };
    match n.op {
        OpCode::Slt => {
            if cx.const_val(n.b).is_some_and(|v| v.is_zero()) {
                return bit(n.a, cx.wid(n.a) - 1, true);
            }
            if cx.const_val(n.a).is_some_and(|v| v.is_ones()) {
                return bit(n.b, cx.wid(n.b) - 1, false);
            }
            (i, 0, true)
        }
        OpCode::Sle => {
            if cx.const_val(n.a).is_some_and(|v| v.is_zero()) {
                return bit(n.b, cx.wid(n.b) - 1, false);
            }
            if cx.const_val(n.b).is_some_and(|v| v.is_ones()) {
                return bit(n.a, cx.wid(n.a) - 1, true);
            }
            (i, 0, true)
        }
        OpCode::Ult => {
            let w = cx.width_of(n.a);
            if cx.const_val(n.b) == Some(BitVec::smin(w)) {
                return bit(n.a, w.bits() - 1, false);
            }
            if cx.const_val(n.a) == Some(BitVec::smax(w)) {
                return bit(n.b, w.bits() - 1, true);
            }
            (i, 0, true)
        }
        OpCode::Ule => {
            let w = cx.width_of(n.a);
            if cx.const_val(n.a) == Some(BitVec::smin(w)) {
                return bit(n.b, w.bits() - 1, true);
            }
            if cx.const_val(n.b) == Some(BitVec::smax(w)) {
                return bit(n.a, w.bits() - 1, false);
            }
            (i, 0, true)
        }
        OpCode::Eq | OpCode::Ne => {
            let a = cx.node(n.a);
            if a.op == OpCode::And
                && let Some(m) = scalar(a.b)
                && m.is_power_of_two()
                && let Some(k) = scalar(n.b)
                && (k == m || k == 0)
            {
                return bit(
                    a.a,
                    m.trailing_zeros() as u16,
                    (k == m) == (n.op == OpCode::Eq),
                );
            }
            (i, 0, true)
        }
        OpCode::Not => {
            let (x, j, on) = bit_literal(cx, n.a);
            (x, j, !on)
        }
        _ => bit(i, 0, true),
    }
}

// A rotate's low, non-wrapping field can be read as a right shift.
#[cfg(any(feature = "mba", feature = "prove"))]
fn right_field(cx: &Context, x: u32) -> Option<(u32, u32)> {
    let w = u32::from(cx.wid(x));
    let (base, left) = rotation_of(cx, x)?;
    Some((base, (w - left) % w))
}

#[cfg(any(feature = "mba", feature = "prove"))]
pub(crate) fn project(cx: &Context, mut x: u32, mut mask: u64, mut bits: u64) -> Option<Field> {
    let mut bias = 0u64;
    let mut biased = false;
    for _ in 0..16 {
        let n = cx.node(x);
        if let Some((src, shift)) = right_field(cx, x) {
            if mask > (u64::MAX >> (64 - n.width)) >> shift {
                return None;
            }
            mask <<= shift;
            bits <<= shift;
            bias <<= shift;
            x = src;
            continue;
        }
        match n.op {
            OpCode::And | OpCode::Or if !biased => {
                let k = cx.const_val(n.b)?.to_u64()?;
                let fixed = if n.op == OpCode::And { !k } else { k };
                let ones = if n.op == OpCode::And { 0 } else { k };
                if (bits ^ ones) & mask & fixed != 0 {
                    return None;
                }
                mask &= !fixed;
                bits &= mask;
            }
            OpCode::Zext if !biased => {
                let low = u64::MAX >> (64 - cx.wid(n.a));
                if bits & !low != 0 {
                    return None;
                }
                mask &= low;
            }
            OpCode::Extract if cx.wid(n.a) <= 64 => {
                mask <<= n.b;
                bits <<= n.b;
                bias <<= n.b;
            }
            OpCode::Add => {
                bias = bias.wrapping_add(cx.const_val(n.b)?.to_u64()?);
                biased = true;
            }
            _ => {
                return (mask != 0).then_some(Field {
                    base: x,
                    bias,
                    mask,
                    bits,
                });
            }
        }
        x = n.a;
    }
    None
}

#[cfg(any(feature = "mba", feature = "prove"))]
impl Field {
    #[cfg(feature = "prove")]
    pub(crate) fn seed(self, input: u64) -> u64 {
        ((input.wrapping_add(self.bias) & !self.mask) | self.bits).wrapping_sub(self.bias)
    }

    #[cfg(feature = "mba")]
    pub(crate) fn implies(self, test: Self) -> Option<bool> {
        if self.base != test.base {
            return None;
        }
        // The low k bits agree for every base if offsets agree modulo 2^k.
        let delta = self.bias ^ test.bias;
        let same = if delta == 0 {
            u64::MAX
        } else {
            (delta & delta.wrapping_neg()) - 1
        };
        let known = self.mask & same & test.mask;
        if (self.bits ^ test.bits) & known != 0 {
            Some(false)
        } else if known == test.mask {
            Some(true)
        } else {
            None
        }
    }
}
