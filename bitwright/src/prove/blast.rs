//! Bit-blasting: every bit-vector operator as a circuit over the bits of its operands, with
//! bitwright's total semantics (SMT-LIB's): division by zero, shifts past the width, rotations
//! by any count. Bits are little-endian.

use super::aig::{Aig, FALSE, L, TRUE};
use crate::BitVec;

/// A bit-vector: its bits, least significant first.
pub type Bits = Vec<L>;

/// The constant `v`.
pub fn konst(v: &BitVec) -> Bits {
    (0..v.width().bits())
        .map(|i| if v.bit(i) == Some(true) { TRUE } else { FALSE })
        .collect()
}

/// A constant of `w` bits from a `u64` (truncated).
pub fn small(w: usize, v: u64) -> Bits {
    (0..w)
        .map(|i| {
            if i < 64 && (v >> i) & 1 == 1 {
                TRUE
            } else {
                FALSE
            }
        })
        .collect()
}

pub fn not(g: &mut Aig, a: &[L]) -> Bits {
    let _ = g;
    a.iter().map(|&x| x ^ 1).collect()
}

pub fn and(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    a.iter().zip(b).map(|(&x, &y)| g.and(x, y)).collect()
}

pub fn or(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    a.iter().zip(b).map(|(&x, &y)| g.or(x, y)).collect()
}

pub fn xor(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    a.iter().zip(b).map(|(&x, &y)| g.xor(x, y)).collect()
}

pub fn mux(g: &mut Aig, c: L, t: &[L], e: &[L]) -> Bits {
    t.iter().zip(e).map(|(&x, &y)| g.mux(c, x, y)).collect()
}

/// `a + b + cin`, and the carry out.
pub fn add_carry(g: &mut Aig, a: &[L], b: &[L], cin: L) -> (Bits, L) {
    let mut c = cin;
    let mut out = Vec::with_capacity(a.len());
    for (&x, &y) in a.iter().zip(b) {
        let s = g.xor(x, y);
        out.push(g.xor(s, c));
        c = g.maj(x, y, c);
    }
    (out, c)
}

pub fn add(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    add_carry(g, a, b, FALSE).0
}

pub fn sub(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    let nb = not(g, b);
    add_carry(g, a, &nb, TRUE).0
}

pub fn neg(g: &mut Aig, a: &[L]) -> Bits {
    let z = vec![FALSE; a.len()];
    sub(g, &z, a)
}

/// `a <u b`: the borrow out of `a − b`.
pub fn ult(g: &mut Aig, a: &[L], b: &[L]) -> L {
    let nb = not(g, b);
    let (_, carry) = add_carry(g, a, &nb, TRUE);
    carry ^ 1
}

pub fn ule(g: &mut Aig, a: &[L], b: &[L]) -> L {
    ult(g, b, a) ^ 1
}

/// `a <s b`: unsigned with the sign bits flipped.
pub fn slt(g: &mut Aig, a: &[L], b: &[L]) -> L {
    let mut a2 = a.to_vec();
    let mut b2 = b.to_vec();
    if let (Some(x), Some(y)) = (a2.last_mut(), b2.last_mut()) {
        *x ^= 1;
        *y ^= 1;
    }
    ult(g, &a2, &b2)
}

pub fn sle(g: &mut Aig, a: &[L], b: &[L]) -> L {
    slt(g, b, a) ^ 1
}

pub fn eq(g: &mut Aig, a: &[L], b: &[L]) -> L {
    let bits: Vec<L> = a.iter().zip(b).map(|(&x, &y)| g.xnor(x, y)).collect();
    g.and_all(&bits)
}

/// The product modulo `2^w` (shift and add).
pub fn mul(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    let w = a.len();
    let mut acc = vec![FALSE; w];
    for (i, &bi) in b.iter().enumerate() {
        if bi == FALSE {
            continue;
        }
        let mut part = vec![FALSE; w];
        for j in 0..w - i {
            part[i + j] = g.and(a[j], bi);
        }
        acc = add(g, &acc, &part);
    }
    acc
}

/// Quotient and remainder of unsigned division; by zero, all ones and `a` (restoring division
/// gives exactly that).
pub fn udivrem(g: &mut Aig, a: &[L], b: &[L]) -> (Bits, Bits) {
    let w = a.len();
    let mut r: Bits = vec![FALSE; w + 1];
    let mut bw = b.to_vec();
    bw.push(FALSE);
    let mut q = vec![FALSE; w];
    for i in (0..w).rev() {
        // r = r·2 + a_i (w + 1 bits suffice: r < b ≤ 2^w − 1 before the shift).
        let mut shifted = vec![a[i]];
        shifted.extend_from_slice(&r[..w]);
        let ge = ult(g, &shifted, &bw) ^ 1;
        let diff = sub(g, &shifted, &bw);
        r = mux(g, ge, &diff, &shifted);
        q[i] = ge;
    }
    r.truncate(w);
    (q, r)
}

/// `|a|` and whether `a` is negative.
fn abs(g: &mut Aig, a: &[L]) -> (Bits, L) {
    let s = *a.last().unwrap_or(&FALSE);
    let n = neg(g, a);
    (mux(g, s, &n, a), s)
}

/// Signed division truncating toward zero, SMT-LIB's (by zero: 1 for a negative dividend, −1
/// otherwise).
pub fn sdiv(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    let (ua, sa) = abs(g, a);
    let (ub, sb) = abs(g, b);
    let (q, _) = udivrem(g, &ua, &ub);
    let differ = g.xor(sa, sb);
    let nq = neg(g, &q);
    mux(g, differ, &nq, &q)
}

/// Signed remainder with the dividend's sign (by zero: the dividend).
pub fn srem(g: &mut Aig, a: &[L], b: &[L]) -> Bits {
    let (ua, sa) = abs(g, a);
    let (ub, _) = abs(g, b);
    let (_, r) = udivrem(g, &ua, &ub);
    let nr = neg(g, &r);
    mux(g, sa, &nr, &r)
}

/// Whether the count `s` is at least `w` (as an unsigned number).
fn at_least(g: &mut Aig, s: &[L], w: usize) -> L {
    let k = small(s.len(), w as u64);
    if s.len() < 64 && (w as u64) >> s.len() != 0 {
        return FALSE;
    }
    ult(g, s, &k) ^ 1
}

/// A shift by a variable count: `fill` for bits shifted in (`FALSE`, or the sign), `left` for
/// the direction. Counts of at least `w` give all fill.
pub fn shift(g: &mut Aig, a: &[L], s: &[L], left: bool, fill: L) -> Bits {
    let w = a.len();
    let mut cur = a.to_vec();
    let mut k = 0;
    while (1usize << k) < w && k < s.len() {
        let amt = 1usize << k;
        let moved: Bits = (0..w)
            .map(|i| {
                if left {
                    if i >= amt { cur[i - amt] } else { FALSE }
                } else if i + amt < w {
                    cur[i + amt]
                } else {
                    fill
                }
            })
            .collect();
        cur = mux(g, s[k], &moved, &cur);
        k += 1;
    }
    let over = at_least(g, s, w);
    let all = vec![if left { FALSE } else { fill }; w];
    mux(g, over, &all, &cur)
}

/// A rotation by `s mod w`.
pub fn rotate(g: &mut Aig, a: &[L], s: &[L], left: bool) -> Bits {
    let w = a.len();
    // The count modulo w.
    let r = if w.is_power_of_two() {
        let k = w.trailing_zeros() as usize;
        let mut r: Bits = s.iter().copied().take(k).collect();
        r.resize(k.max(1), FALSE);
        r
    } else {
        let wk = small(s.len(), w as u64);
        let (_, r) = udivrem(g, s, &wk);
        r
    };
    let mut cur = a.to_vec();
    for (k, &bit) in r.iter().enumerate() {
        if k >= 64 || (1u64 << k) as usize >= 2 * w {
            break;
        }
        let amt = (1usize << k) % w;
        if amt == 0 {
            continue;
        }
        let moved: Bits = (0..w)
            .map(|i| {
                if left {
                    cur[(i + w - amt) % w]
                } else {
                    cur[(i + amt) % w]
                }
            })
            .collect();
        cur = mux(g, bit, &moved, &cur);
    }
    cur
}

/// The number of set bits of `bits`, in `w` bits.
pub fn count(g: &mut Aig, bits: &[L], w: usize) -> Bits {
    // An adder tree over the single bits.
    let mut vals: Vec<Bits> = bits
        .iter()
        .map(|&b| {
            let mut v = vec![FALSE; w];
            if w > 0 {
                v[0] = b;
            }
            v
        })
        .collect();
    if vals.is_empty() {
        return vec![FALSE; w];
    }
    while vals.len() > 1 {
        let mut next = Vec::with_capacity(vals.len().div_ceil(2));
        for pair in vals.chunks(2) {
            next.push(if pair.len() == 2 {
                add(g, &pair[0], &pair[1])
            } else {
                pair[0].clone()
            });
        }
        vals = next;
    }
    vals.pop().unwrap_or_default()
}

pub fn popcnt(g: &mut Aig, a: &[L]) -> Bits {
    count(g, a, a.len())
}

/// Leading zeros: the number of prefixes (from the top) that are all zero.
pub fn clz(g: &mut Aig, a: &[L]) -> Bits {
    let mut flags = Vec::with_capacity(a.len());
    let mut all_zero = TRUE;
    for &b in a.iter().rev() {
        all_zero = g.and(all_zero, b ^ 1);
        flags.push(all_zero);
    }
    count(g, &flags, a.len())
}

pub fn ctz(g: &mut Aig, a: &[L]) -> Bits {
    let mut flags = Vec::with_capacity(a.len());
    let mut all_zero = TRUE;
    for &b in a {
        all_zero = g.and(all_zero, b ^ 1);
        flags.push(all_zero);
    }
    count(g, &flags, a.len())
}

pub fn bswap(a: &[L]) -> Bits {
    let w = a.len();
    (0..w).map(|k| a[(w / 8 - 1 - k / 8) * 8 + k % 8]).collect()
}

pub fn bitrev(a: &[L]) -> Bits {
    a.iter().rev().copied().collect()
}

/// The high half of the full product (sign or zero extended to twice the width).
pub fn mulhi(g: &mut Aig, a: &[L], b: &[L], signed: bool) -> Bits {
    let w = a.len();
    let ext = |x: &[L]| -> Bits {
        let fill = if signed {
            *x.last().unwrap_or(&FALSE)
        } else {
            FALSE
        };
        let mut v = x.to_vec();
        v.resize(2 * w, fill);
        v
    };
    let (a2, b2) = (ext(a), ext(b));
    let p = mul(g, &a2, &b2);
    p[w..].to_vec()
}

/// Parallel bit deposit: bit `i` of the result is `m_i ∧ x_{c_i}`, `c_i` the number of set bits
/// of `m` below `i`.
pub fn pdep(g: &mut Aig, x: &[L], m: &[L]) -> Bits {
    let w = x.len();
    let cw = (usize::BITS - w.leading_zeros()) as usize + 1;
    let mut out = Vec::with_capacity(w);
    let mut c: Bits = vec![FALSE; cw];
    for &mi in m.iter().take(w) {
        // x at index c (a w-to-1 multiplexer).
        let mut pick = FALSE;
        for (j, &xj) in x.iter().enumerate() {
            let at = eq(g, &c, &small(cw, j as u64));
            let t = g.and(at, xj);
            pick = g.or(pick, t);
        }
        out.push(g.and(mi, pick));
        let mut one = small(cw, 0);
        one[0] = mi;
        c = add(g, &c, &one);
    }
    out
}

/// Parallel bit extract: bit `j` of the result is the OR over `i` of `x_i ∧ m_i ∧ (c_i = j)`.
pub fn pext(g: &mut Aig, x: &[L], m: &[L]) -> Bits {
    let w = x.len();
    let cw = (usize::BITS - w.leading_zeros()) as usize + 1;
    let mut out = vec![FALSE; w];
    let mut c: Bits = vec![FALSE; cw];
    for i in 0..w {
        let src = g.and(x[i], m[i]);
        for (j, o) in out.iter_mut().enumerate() {
            let at = eq(g, &c, &small(cw, j as u64));
            let t = g.and(at, src);
            *o = g.or(*o, t);
        }
        let mut one = small(cw, 0);
        one[0] = m[i];
        c = add(g, &c, &one);
    }
    out
}
