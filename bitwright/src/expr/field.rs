//! A masked comparison on a word plus a modular offset.
use super::{Context, OpCode};
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

// A rotate's low, non-wrapping field can be read as a right shift.
fn right_field(cx: &Context, x: u32) -> Option<(u32, u32)> {
    let n = cx.node(x);
    let w = u64::from(n.width);
    let k = |i| cx.const_val(i)?.to_u64();
    if matches!(n.op, OpCode::RotL | OpCode::RotR) {
        let s = k(n.b)? % w;
        return Some((
            n.a,
            (if n.op == OpCode::RotL { (w - s) % w } else { s }) as u32,
        ));
    }
    let (a, b) = match n.op {
        OpCode::Or => (n.a, n.b),
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
    (left < w && right < w && left + right == w).then_some((l.a, right as u32))
}

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
