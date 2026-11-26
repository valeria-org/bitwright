//! Polynomial equality (called by the compares pass and sweep relation checks): two sides built
//! from `+ − * neg ~`, left shifts by constants, bitwise OR with constants (`x | c = (x & ~c) + c`),
//! low truncations/zero-extensions, and constants over a few leaves are expanded into sums of
//! monomials with coefficients modulo `2^W`; equal polynomials are equal functions, so `a == b` is
//! true (and `a != b` false). `(x + y)·(x − y) == x·x − y·y` and the sum of cubes are decided this
//! way. Different polynomials may still be equal functions (`2^(W−1)·(x² + x)` is 0), which this
//! leaves undecided.

use super::{Runner, Stop};
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::BinOp;
use crate::{BitVec, Width};

/// The most leaves per polynomial width.
const MAX_LEAVES: usize = 24;

/// The most monomials a polynomial keeps.
const MAX_TERMS: usize = 128;

/// The most degree per leaf.
const MAX_DEGREE: u8 = 6;

/// Maximum recursive expansion steps per `equal` call.
const MAX_STEPS: u32 = 512;

/// A monomial: the exponent of each leaf.
type Mono = [u8; MAX_LEAVES];

/// A polynomial: monomials with nonzero coefficients, sorted.
type Poly = Vec<(Mono, BitVec)>;

/// Canonical leaf identity at a given modulus width `mod_w`.
#[derive(Clone, PartialEq, Eq)]
enum LeafKey {
    /// An unexpanded node (mod `2^mod_w`).
    Node(u32),
    /// `base & mask` (mod `2^mod_w`), with `0 < mask < (1 << mod_w) - 1`, unifying `x | c`
    /// (`(x & ~c) + c`) with `x & ~c`.
    Masked(u32, u64),
    /// `(base & mask) ^ c_canon` (mod `2^mod_w`), with `0 < c_canon < mask` and the top set bit
    /// of `mask` cleared in `c_canon` so complementary masked constant XORs (`(x & m) ^ c` vs
    /// `(x & m) ^ (m ^ c)`) canonicalize to `leaf` and `m - leaf`.
    XorConst(u32, u64, u64),
    /// `base >>u shift` (at full width), unifying `rotl(x, s) = (x << s) + (x >>u (W - s))`
    /// with explicit logical right shifts `x >>u (W - s)`.
    LShr(u32, u16),
    /// A zero-extended narrow polynomial `zext(p)` of width `k < mod_w`, unifying
    /// `zext<W>(P_k)` with `P_W & ((1 << k) - 1)` when both have the same mod-`2^k` polynomial.
    LowPoly(u16, Poly),
}

/// Shared leaf tables per modulus width so both sides assign identical indices to matching leaves.
#[derive(Default)]
struct LeafTables {
    by_width: Vec<(u16, Vec<LeafKey>)>,
}

impl LeafTables {
    fn intern(&mut self, mod_w: u16, key: LeafKey) -> Option<usize> {
        let table = match self.by_width.iter_mut().find(|(w, _)| *w == mod_w) {
            Some((_, t)) => t,
            None => {
                self.by_width.push((mod_w, Vec::new()));
                &mut self.by_width.last_mut()?.1
            }
        };
        if let Some(i) = table.iter().position(|k| *k == key) {
            return Some(i);
        }
        if table.len() >= MAX_LEAVES {
            return None;
        }
        table.push(key);
        Some(table.len() - 1)
    }
}

fn mod_mask_u64(bits: u16) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else if bits == 0 {
        0
    } else {
        (1u64 << bits) - 1
    }
}

fn leaf_poly(tables: &mut LeafTables, mod_w: Width, key: LeafKey) -> Option<Poly> {
    let i = tables.intern(mod_w.bits(), key)?;
    let mut m = [0u8; MAX_LEAVES];
    m[i] = 1;
    Some(vec![(m, BitVec::one(mod_w))])
}

/// Guaranteed 2-adic valuation (trailing zero bits) of every value represented by `key`.
fn leaf_tz(cx: &Context, mod_w: Width, key: &LeafKey) -> u32 {
    let bits = mod_w.bits();
    match key {
        LeafKey::Masked(_, mask) | LeafKey::XorConst(_, mask, _) => {
            if *mask == 0 {
                u32::from(bits)
            } else {
                mask.trailing_zeros()
            }
        }
        LeafKey::LowPoly(_, sub) => sub
            .iter()
            .map(|(_, c)| crate::facts::known::trailing_zeros(c))
            .min()
            .unwrap_or(u32::from(bits)),
        LeafKey::Node(id) => {
            if bits <= 64 {
                let m = possible_ones(cx, *id, 3) & mod_mask_u64(bits);
                if m == 0 {
                    u32::from(bits)
                } else {
                    m.trailing_zeros()
                }
            } else {
                0
            }
        }
        LeafKey::LShr(base, s) => {
            if bits <= 64 {
                let m = (possible_ones(cx, *base, 3) >> s) & mod_mask_u64(bits);
                if m == 0 {
                    u32::from(bits)
                } else {
                    m.trailing_zeros()
                }
            } else {
                0
            }
        }
    }
}

/// Canonical 2-adic quotient: when monomial `M = prod_i leaf_i^{e_i}` has guaranteed valuation
/// `V = sum_i e_i * tz(leaf_i) > 0`, only `coef mod 2^{max(0, bits - V)}` affects `coef * M (mod 2^bits)`.
fn reduce_2adic(cx: &Context, tables: &LeafTables, mod_w: Width, p: &mut Poly) {
    if p.is_empty() {
        return;
    }
    let bits = u32::from(mod_w.bits());
    let Some((_, keys)) = tables.by_width.iter().find(|(w, _)| *w == mod_w.bits()) else {
        return;
    };
    let mut tzs = [0u32; MAX_LEAVES];
    let mut any_tz = false;
    for (i, k) in keys.iter().enumerate() {
        let tz = leaf_tz(cx, mod_w, k);
        tzs[i] = tz;
        any_tz |= tz > 0;
    }
    if !any_tz {
        return;
    }
    for (m, c) in p.iter_mut() {
        let mut v = 0u32;
        for (i, &e) in m.iter().enumerate() {
            if e != 0 {
                v = v.saturating_add(u32::from(e).saturating_mul(tzs[i]));
            }
        }
        if v >= bits {
            *c = BitVec::zero(mod_w);
        } else if v > 0 {
            let keep = crate::facts::known::low_mask(mod_w, bits - v);
            *c = crate::facts::known::bv_and(c, &keep);
        }
    }
    p.retain(|(_, c)| !c.is_zero());
}

fn add(a: &Poly, b: &Poly, sub: bool) -> Poly {
    let mut out: Poly = a.clone();
    for (m, c) in b {
        let c = if sub {
            BitVec::apply_un(crate::UnOp::Neg, c).unwrap_or(*c)
        } else {
            *c
        };
        match out.binary_search_by(|(k, _)| k.cmp(m)) {
            Ok(i) => {
                out[i].1 = BitVec::apply_bin(BinOp::Add, &out[i].1, &c).unwrap_or(c);
            }
            Err(i) => out.insert(i, (*m, c)),
        }
    }
    out.retain(|(_, c)| !c.is_zero());
    out
}

fn mul(a: &Poly, b: &Poly) -> Option<Poly> {
    let mut out: Poly = Vec::new();
    for (ma, ca) in a {
        for (mb, cb) in b {
            let mut m = [0u8; MAX_LEAVES];
            for i in 0..MAX_LEAVES {
                m[i] = ma[i].checked_add(mb[i]).filter(|&d| d <= MAX_DEGREE)?;
            }
            let c = BitVec::apply_bin(BinOp::Mul, ca, cb).ok()?;
            out = add(&out, &vec![(m, c)], false);
            if out.len() > MAX_TERMS {
                return None;
            }
        }
    }
    Some(out)
}

/// Sound over-approximation of bits that may be 1 in `x` (width <= 64).
fn possible_ones(cx: &Context, x: u32, depth: u8) -> u64 {
    let w = cx.wid(x);
    if w == 0 || w > 64 {
        return u64::MAX;
    }
    let full = mod_mask_u64(w);
    if depth == 0 {
        return full;
    }
    let n = cx.node(x);
    let m = match n.op {
        OpCode::Const => cx.const_val(x).and_then(|v| v.to_u64()).unwrap_or(full),
        OpCode::Zext => possible_ones(cx, n.a, depth - 1),
        OpCode::Extract if cx.wid(n.a) <= 64 => {
            if n.b < 64 {
                possible_ones(cx, n.a, depth - 1) >> n.b
            } else {
                0
            }
        }
        OpCode::Concat => {
            let lo_w = cx.wid(n.b);
            let hi = if lo_w < 64 {
                (possible_ones(cx, n.a, depth - 1) << lo_w) & full
            } else {
                0
            };
            hi | possible_ones(cx, n.b, depth - 1)
        }
        OpCode::And => possible_ones(cx, n.a, depth - 1) & possible_ones(cx, n.b, depth - 1),
        OpCode::Or | OpCode::Xor => {
            possible_ones(cx, n.a, depth - 1) | possible_ones(cx, n.b, depth - 1)
        }
        OpCode::Shl => match cx.const_val(n.b).and_then(|v| v.to_u64()) {
            Some(s) if s < 64 => (possible_ones(cx, n.a, depth - 1) << s) & full,
            Some(_) => 0,
            None => full,
        },
        OpCode::LShr => match cx.const_val(n.b).and_then(|v| v.to_u64()) {
            Some(s) if s < 64 => possible_ones(cx, n.a, depth - 1) >> s,
            Some(_) => 0,
            None => full,
        },
        OpCode::Add => {
            let ma = possible_ones(cx, n.a, depth - 1);
            let mb = possible_ones(cx, n.b, depth - 1);
            if ma & mb == 0 {
                ma | mb
            } else if let Some(c) = cx.const_val(n.a).and_then(|v| v.to_u64())
                && mb.is_power_of_two()
            {
                c | c.wrapping_add(mb)
            } else if let Some(c) = cx.const_val(n.b).and_then(|v| v.to_u64())
                && ma.is_power_of_two()
            {
                c | c.wrapping_add(ma)
            } else {
                full
            }
        }
        OpCode::Sub => {
            if let Some(c) = cx.const_val(n.a).and_then(|v| v.to_u64()) {
                let mb = possible_ones(cx, n.b, depth - 1);
                if mb & !c == 0 {
                    c
                } else if mb.is_power_of_two() {
                    c | c.wrapping_sub(mb)
                } else {
                    full
                }
            } else if let Some(c) = cx.const_val(n.b).and_then(|v| v.to_u64()) {
                let ma = possible_ones(cx, n.a, depth - 1);
                if ma.is_power_of_two() {
                    c.wrapping_neg() | ma.wrapping_sub(c)
                } else {
                    full
                }
            } else {
                full
            }
        }
        _ => full,
    };
    m & full
}

/// Sound under-approximation of bits that are guaranteed to be 1 in `x` (width <= 64).
fn guaranteed_ones(cx: &Context, x: u32, depth: u8) -> u64 {
    let w = cx.wid(x);
    if w == 0 || w > 64 || depth == 0 {
        return 0;
    }
    let full = mod_mask_u64(w);
    let n = cx.node(x);
    let m = match n.op {
        OpCode::Const => cx.const_val(x).and_then(|v| v.to_u64()).unwrap_or(0),
        OpCode::Not => !possible_ones(cx, n.a, depth - 1) & full,
        OpCode::Zext => guaranteed_ones(cx, n.a, depth - 1),
        OpCode::Extract if cx.wid(n.a) <= 64 => {
            if n.b < 64 {
                guaranteed_ones(cx, n.a, depth - 1) >> n.b
            } else {
                0
            }
        }
        OpCode::Concat => {
            let lo_w = cx.wid(n.b);
            let hi = if lo_w < 64 {
                (guaranteed_ones(cx, n.a, depth - 1) << lo_w) & full
            } else {
                0
            };
            hi | guaranteed_ones(cx, n.b, depth - 1)
        }
        OpCode::Or => guaranteed_ones(cx, n.a, depth - 1) | guaranteed_ones(cx, n.b, depth - 1),
        OpCode::And => guaranteed_ones(cx, n.a, depth - 1) & guaranteed_ones(cx, n.b, depth - 1),
        _ => 0,
    };
    m & full
}

/// Peel `trunc<w'>` (`w' >= mod_w`), `zext` (`wid(inner) >= mod_w`), and `And` with constant masks
/// that preserve all bits of `mask`, returning canonical `(base, combined_mask)`.
fn peel_masked(cx: &Context, mut x: u32, mut mask: u64, mod_w: u16) -> (u32, u64) {
    let mm = mod_mask_u64(mod_w);
    mask &= mm;
    for _ in 0..8 {
        let n = cx.node(x);
        match n.op {
            OpCode::Extract if n.b == 0 && n.width >= mod_w && cx.wid(n.a) <= 64 => {
                x = n.a;
            }
            OpCode::Zext if cx.wid(n.a) >= mod_w && cx.wid(n.a) <= 64 => {
                x = n.a;
            }
            OpCode::And => {
                if let Some(m) = cx.const_val(n.b).and_then(|v| v.to_u64()) {
                    mask &= m;
                    x = n.a;
                } else if let Some(m) = cx.const_val(n.a).and_then(|v| v.to_u64()) {
                    mask &= m;
                    x = n.b;
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
    (x, mask)
}

/// The polynomial of `x` modulo `2^mod_w` over `tables`, if it is one within the caps.
fn poly_of(
    cx: &Context,
    x: u32,
    mod_w: Width,
    tables: &mut LeafTables,
    memo: &mut IdMap<(u32, u16), Poly>,
    steps: &mut u32,
) -> Option<Poly> {
    let bits = mod_w.bits();
    if let Some(p) = memo.get(&(x, bits)) {
        return Some(p.clone());
    }
    *steps += 1;
    if *steps > MAX_STEPS {
        return None;
    }
    let node = cx.node(x);
    let w = cx.width_of(x);
    let p = if let Some(v) = cx.const_val(x) {
        let v = if bits == w.bits() {
            v
        } else {
            v.trunc(mod_w).ok()?
        };
        if v.is_zero() {
            Vec::new()
        } else {
            vec![([0u8; MAX_LEAVES], v)]
        }
    } else {
        match node.op {
            OpCode::Add | OpCode::Sub => {
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                let b = poly_of(cx, node.b, mod_w, tables, memo, steps)?;
                let p = add(&a, &b, node.op == OpCode::Sub);
                (p.len() <= MAX_TERMS).then_some(p)?
            }
            OpCode::Neg => {
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                add(&Vec::new(), &a, true)
            }
            OpCode::Not => {
                // ~a == -a - 1 (mod 2^mod_w)
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                let neg_a = add(&Vec::new(), &a, true);
                let minus_one = vec![([0u8; MAX_LEAVES], BitVec::ones(mod_w))];
                let p = add(&neg_a, &minus_one, false);
                (p.len() <= MAX_TERMS).then_some(p)?
            }
            OpCode::Mul => {
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                let b = poly_of(cx, node.b, mod_w, tables, memo, steps)?;
                mul(&a, &b)?
            }
            OpCode::Shl if cx.const_val(node.b).is_some() => {
                let a = poly_of(cx, node.a, mod_w, tables, memo, steps)?;
                let s = cx.const_val(node.b)?;
                let s_mod = if bits == w.bits() {
                    s
                } else if s.to_u64().is_some_and(|v| v >= u64::from(bits)) {
                    return Some(Vec::new());
                } else {
                    s.trunc(mod_w).ok()?
                };
                let k = BitVec::apply_bin(BinOp::Shl, &BitVec::one(mod_w), &s_mod).ok()?;
                mul(&a, &vec![([0u8; MAX_LEAVES], k)])?
            }
            OpCode::Extract if node.b == 0 && node.width >= bits && cx.wid(node.a) <= 64 => {
                poly_of(cx, node.a, mod_w, tables, memo, steps)?
            }
            OpCode::Zext if cx.wid(node.a) >= bits && cx.wid(node.a) <= 64 => {
                poly_of(cx, node.a, mod_w, tables, memo, steps)?
            }
            OpCode::Zext if bits <= 64 && cx.wid(node.a) < bits => {
                let sub_w = cx.width_of(node.a);
                let sub_bits = sub_w.bits();
                let sub_mm = mod_mask_u64(sub_bits);
                let inner = cx.node(node.a);
                // When `node.a` is a bitwise complement (`~u` or `u ^ c` with top bit set at
                // `sub_bits`), `zext<mod_w>(~u) == ((1 << sub_bits) - 1) - zext<mod_w>(u)` with
                // zero borrow, unifying `zext(u ^ c)` and `zext(u ^ ~c)` on the same `LowPoly`.
                let comp_sub: Option<Poly> = if inner.op == OpCode::Not {
                    poly_of(cx, inner.a, sub_w, tables, memo, steps)
                } else if inner.op == OpCode::Xor && sub_bits >= 1 {
                    let xor_const = match (cx.const_val(inner.a), cx.const_val(inner.b)) {
                        (None, Some(k)) => k.to_u64().map(|c| (inner.a, c & sub_mm)),
                        (Some(k), None) => k.to_u64().map(|c| (inner.b, c & sub_mm)),
                        _ => None,
                    };
                    if let Some((base, cv)) = xor_const
                        && (cv & (1u64 << (sub_bits - 1))) != 0
                    {
                        xor_const_poly(cx, base, (!cv) & sub_mm, sub_w, tables, memo, steps)
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some(mut pos_sub) = comp_sub {
                    reduce_2adic(cx, tables, sub_w, &mut pos_sub);
                    let max_val = vec![([0u8; MAX_LEAVES], BitVec::wrapping_from_u64(mod_w, sub_mm))];
                    if pos_sub.is_empty() {
                        max_val
                    } else if pos_sub.len() == 1 && pos_sub[0].0 == [0u8; MAX_LEAVES] {
                        let c = pos_sub[0].1.zext(mod_w).ok()?;
                        add(&max_val, &vec![([0u8; MAX_LEAVES], c)], true)
                    } else {
                        let lp = leaf_poly(tables, mod_w, LeafKey::LowPoly(sub_bits, pos_sub))?;
                        add(&max_val, &lp, true)
                    }
                } else if let Some(sub) = poly_of(cx, node.a, sub_w, tables, memo, steps) {
                    if sub.is_empty() {
                        Vec::new()
                    } else if sub.len() == 1 && sub[0].0 == [0u8; MAX_LEAVES] {
                        let c = sub[0].1.zext(mod_w).ok()?;
                        vec![([0u8; MAX_LEAVES], c)]
                    } else {
                        leaf_poly(tables, mod_w, LeafKey::LowPoly(sub_bits, sub))?
                    }
                } else {
                    leaf_poly(tables, mod_w, LeafKey::Node(x))?
                }
            }
            OpCode::Concat if bits <= 64 => {
                let lo_bits = cx.wid(node.b);
                if lo_bits >= bits {
                    poly_of(cx, node.b, mod_w, tables, memo, steps)?
                } else {
                    let hi_bits = bits - lo_bits;
                    let hi_w = Width::new(hi_bits).ok()?;
                    let lo_w = Width::new(lo_bits).ok()?;
                    let lift = |sub: Poly, sb: u16, tables: &mut LeafTables| -> Option<Poly> {
                        if sub.is_empty() {
                            Some(Vec::new())
                        } else if sub.len() == 1 && sub[0].0 == [0u8; MAX_LEAVES] {
                            let c = sub[0].1.zext(mod_w).ok()?;
                            Some(vec![([0u8; MAX_LEAVES], c)])
                        } else {
                            leaf_poly(tables, mod_w, LeafKey::LowPoly(sb, sub))
                        }
                    };
                    if let (Some(hi_sub), Some(lo_sub)) = (
                        poly_of(cx, node.a, hi_w, tables, memo, steps),
                        poly_of(cx, node.b, lo_w, tables, memo, steps),
                    ) && let (Some(hi_lifted), Some(lo_lifted)) =
                        (lift(hi_sub, hi_bits, tables), lift(lo_sub, lo_bits, tables))
                        && let Ok(scale) = BitVec::apply_bin(
                            BinOp::Shl,
                            &BitVec::one(mod_w),
                            &BitVec::wrapping_from_u64(mod_w, u64::from(lo_bits)),
                        )
                        && let Some(hi_scaled) = mul(&hi_lifted, &vec![([0u8; MAX_LEAVES], scale)])
                    {
                        let p = add(&hi_scaled, &lo_lifted, false);
                        if p.len() <= MAX_TERMS {
                            p
                        } else {
                            leaf_poly(tables, mod_w, LeafKey::Node(x))?
                        }
                    } else {
                        leaf_poly(tables, mod_w, LeafKey::Node(x))?
                    }
                }
            }
            OpCode::Xor
                if (1..=64).contains(&bits)
                    && (cx.const_val(node.b).is_some() || cx.const_val(node.a).is_some()) =>
            {
                let (other, cv) = match cx.const_val(node.b).and_then(|v| v.to_u64()) {
                    Some(c) => (node.a, c),
                    None => (node.b, cx.const_val(node.a).and_then(|v| v.to_u64())?),
                };
                xor_const_poly(cx, other, cv, mod_w, tables, memo, steps)?
            }
            OpCode::Or
                if bits <= 64
                    && (cx.const_val(node.b).is_some() || cx.const_val(node.a).is_some()) =>
            {
                // x | c == (x & ~c) + c (exact: disjoint bit masks, zero carry)
                let (other, cv) = match cx.const_val(node.b).and_then(|v| v.to_u64()) {
                    Some(c) => (node.a, c),
                    None => (node.b, cx.const_val(node.a).and_then(|v| v.to_u64())?),
                };
                let mm = mod_mask_u64(bits);
                let c_mod = cv & mm;
                let keep = (!c_mod) & mm;
                let base_poly = if keep == 0 {
                    Vec::new()
                } else if keep == mm {
                    poly_of(cx, other, mod_w, tables, memo, steps)?
                } else {
                    let (base, m) = peel_masked(cx, other, keep, bits);
                    if m == 0 {
                        Vec::new()
                    } else if m == mm {
                        poly_of(cx, base, mod_w, tables, memo, steps)?
                    } else {
                        leaf_poly(tables, mod_w, LeafKey::Masked(base, m))?
                    }
                };
                if c_mod == 0 {
                    base_poly
                } else {
                    let c_term = vec![([0u8; MAX_LEAVES], BitVec::wrapping_from_u64(mod_w, c_mod))];
                    let p = add(&base_poly, &c_term, false);
                    (p.len() <= MAX_TERMS).then_some(p)?
                }
            }
            OpCode::Or if bits <= 64 => {
                let mm = mod_mask_u64(bits);
                let pa_may = possible_ones(cx, node.a, 4) & mm;
                let pb_may = possible_ones(cx, node.b, 4) & mm;
                let ga = guaranteed_ones(cx, node.a, 4) & mm;
                let gb = guaranteed_ones(cx, node.b, 4) & mm;
                if pb_may & !ga == 0 {
                    poly_of(cx, node.a, mod_w, tables, memo, steps)?
                } else if pa_may & !gb == 0 {
                    poly_of(cx, node.b, mod_w, tables, memo, steps)?
                } else if pa_may & pb_may == 0 {
                    // Disjoint bit masks: a | b == a + b (mod 2^mod_w).
                    if let (Some(a), Some(b)) = (
                        poly_of(cx, node.a, mod_w, tables, memo, steps),
                        poly_of(cx, node.b, mod_w, tables, memo, steps),
                    ) {
                        let p = add(&a, &b, false);
                        if p.len() <= MAX_TERMS {
                            p
                        } else {
                            leaf_poly(tables, mod_w, LeafKey::Node(x))?
                        }
                    } else {
                        leaf_poly(tables, mod_w, LeafKey::Node(x))?
                    }
                } else {
                    leaf_poly(tables, mod_w, LeafKey::Node(x))?
                }
            }
            OpCode::And
                if bits <= 64
                    && (cx.const_val(node.b).is_some() || cx.const_val(node.a).is_some()) =>
            {
                let (other, mv) = match cx.const_val(node.b).and_then(|v| v.to_u64()) {
                    Some(m) => (node.a, m),
                    None => (node.b, cx.const_val(node.a).and_then(|v| v.to_u64())?),
                };
                let mm = mod_mask_u64(bits);
                let m = mv & mm;
                if m == 0 {
                    Vec::new()
                } else if m == mm {
                    poly_of(cx, other, mod_w, tables, memo, steps)?
                } else if m.wrapping_add(1).is_power_of_two() && m < mm {
                    // Low k-bit mask `x & ((1 << k) - 1)` == `zext<mod_w>(trunc<k>(x))`.
                    // Also recognize `rotl(a, k) & ((1 << k) - 1) == a >>u (W - k)` directly.
                    let k = m.count_ones() as u16;
                    let on = cx.node(other);
                    let rot_lshr = if matches!(on.op, OpCode::RotL | OpCode::RotR)
                        && on.width <= 64
                        && let Some(s) = cx.const_val(on.b).and_then(|v| v.to_u64())
                    {
                        let ow = on.width;
                        let lsh = if on.op == OpCode::RotL {
                            (s % u64::from(ow)) as u16
                        } else {
                            ((u64::from(ow) - s % u64::from(ow)) % u64::from(ow)) as u16
                        };
                        (lsh == k && k < ow).then_some((on.a, ow - k))
                    } else {
                        None
                    };
                    if let Some((base, rshift)) = rot_lshr {
                        leaf_poly(tables, mod_w, LeafKey::LShr(base, rshift))?
                    } else {
                        let sub_w = Width::new(k).ok()?;
                        if let Some(sub) = poly_of(cx, other, sub_w, tables, memo, steps) {
                            if sub.is_empty() {
                                Vec::new()
                            } else if sub.len() == 1 && sub[0].0 == [0u8; MAX_LEAVES] {
                                let c = sub[0].1.zext(mod_w).ok()?;
                                vec![([0u8; MAX_LEAVES], c)]
                            } else {
                                leaf_poly(tables, mod_w, LeafKey::LowPoly(k, sub))?
                            }
                        } else {
                            let (base, bm) = peel_masked(cx, other, m, bits);
                            leaf_poly(tables, mod_w, LeafKey::Masked(base, bm))?
                        }
                    }
                } else {
                    let (base, bm) = peel_masked(cx, other, m, bits);
                    if bm == 0 {
                        Vec::new()
                    } else if bm == mm {
                        poly_of(cx, base, mod_w, tables, memo, steps)?
                    } else {
                        leaf_poly(tables, mod_w, LeafKey::Masked(base, bm))?
                    }
                }
            }
            OpCode::LShr
                if w.bits() <= 64
                    && cx.const_val(node.b).and_then(|v| v.to_u64()).is_some_and(|s| s > 0 && s < u64::from(w.bits())) =>
            {
                let s = cx.const_val(node.b)?.to_u64()? as u16;
                leaf_poly(tables, mod_w, LeafKey::LShr(node.a, s))?
            }
            OpCode::RotL | OpCode::RotR
                if w.bits() <= 64
                    && cx.const_val(node.b).and_then(|v| v.to_u64()).is_some() =>
            {
                // rotl(a, lsh) == (a << lsh) + (a >>u (W - lsh)) (mod 2^W, hence mod 2^mod_w).
                let ow = w.bits();
                let raw = cx.const_val(node.b)?.to_u64()? % u64::from(ow);
                let lsh = if node.op == OpCode::RotL {
                    raw as u16
                } else {
                    ((u64::from(ow) - raw) % u64::from(ow)) as u16
                };
                if lsh == 0 {
                    poly_of(cx, node.a, mod_w, tables, memo, steps)?
                } else if lsh >= bits {
                    leaf_poly(tables, mod_w, LeafKey::LShr(node.a, ow - lsh))?
                } else if let Some(a) = poly_of(cx, node.a, mod_w, tables, memo, steps)
                    && let Ok(k) = BitVec::apply_bin(
                        BinOp::Shl,
                        &BitVec::one(mod_w),
                        &BitVec::wrapping_from_u64(mod_w, u64::from(lsh)),
                    )
                    && let Some(hi) = mul(&a, &vec![([0u8; MAX_LEAVES], k)])
                    && let Some(lo) = leaf_poly(tables, mod_w, LeafKey::LShr(node.a, ow - lsh))
                {
                    let p = add(&hi, &lo, false);
                    if p.len() <= MAX_TERMS {
                        p
                    } else {
                        leaf_poly(tables, mod_w, LeafKey::Node(x))?
                    }
                } else {
                    leaf_poly(tables, mod_w, LeafKey::Node(x))?
                }
            }
            _ => leaf_poly(tables, mod_w, LeafKey::Node(x))?,
        }
    };
    let mut p = p;
    reduce_2adic(cx, tables, mod_w, &mut p);
    memo.insert((x, bits), p.clone());
    Some(p)
}

/// Polynomial of `other ^ cv` modulo `2^mod_w`, exploiting known-zero/subset structure and
/// canonicalizing complementary masked constant XORs `(x & m) ^ c` vs `(x & m) ^ (m ^ c)`.
fn xor_const_poly(
    cx: &Context,
    other: u32,
    cv: u64,
    mod_w: Width,
    tables: &mut LeafTables,
    memo: &mut IdMap<(u32, u16), Poly>,
    steps: &mut u32,
) -> Option<Poly> {
    let bits = mod_w.bits();
    let mm = mod_mask_u64(bits);
    let c_mod = cv & mm;
    if c_mod == 0 {
        return poly_of(cx, other, mod_w, tables, memo, steps);
    }
    let p_may = possible_ones(cx, other, 4) & mm;
    if (p_may & c_mod) == 0 {
        // Disjoint bits: `other ^ c_mod == other + c_mod`.
        let base_p = poly_of(cx, other, mod_w, tables, memo, steps)?;
        let c_term = vec![([0u8; MAX_LEAVES], BitVec::wrapping_from_u64(mod_w, c_mod))];
        let p = add(&base_p, &c_term, false);
        return (p.len() <= MAX_TERMS).then_some(p);
    }
    if (p_may & !c_mod) == 0 {
        // Every possible 1-bit of `other` is set in `c_mod`: `other ^ c_mod == c_mod - other`.
        let base_p = poly_of(cx, other, mod_w, tables, memo, steps)?;
        let c_term = vec![([0u8; MAX_LEAVES], BitVec::wrapping_from_u64(mod_w, c_mod))];
        let p = add(&c_term, &base_p, true);
        return (p.len() <= MAX_TERMS).then_some(p);
    }
    let (b_peeled, m) = peel_masked(cx, other, mm, bits);
    let c_out = c_mod & !m;
    let c_in = c_mod & m;
    if c_in == 0 {
        let base_p = poly_of(cx, other, mod_w, tables, memo, steps)?;
        let c_term = vec![([0u8; MAX_LEAVES], BitVec::wrapping_from_u64(mod_w, c_out))];
        let p = add(&base_p, &c_term, false);
        return (p.len() <= MAX_TERMS).then_some(p);
    }
    if c_in == m {
        let base_p = poly_of(cx, other, mod_w, tables, memo, steps)?;
        let c_term = vec![([0u8; MAX_LEAVES], BitVec::wrapping_from_u64(mod_w, c_mod))];
        let p = add(&c_term, &base_p, true);
        return (p.len() <= MAX_TERMS).then_some(p);
    }
    let top_bit = 1u64 << (63 - m.leading_zeros());
    let neg_comp = (c_in & top_bit) != 0;
    let c_canon = if neg_comp { m ^ c_in } else { c_in };
    let leaf = leaf_poly(tables, mod_w, LeafKey::XorConst(b_peeled, m, c_canon))?;
    if neg_comp {
        let bias = vec![(
            [0u8; MAX_LEAVES],
            BitVec::wrapping_from_u64(mod_w, c_out | m),
        )];
        let p = add(&bias, &leaf, true);
        (p.len() <= MAX_TERMS).then_some(p)
    } else if c_out == 0 {
        Some(leaf)
    } else {
        let bias = vec![([0u8; MAX_LEAVES], BitVec::wrapping_from_u64(mod_w, c_out))];
        let p = add(&bias, &leaf, false);
        (p.len() <= MAX_TERMS).then_some(p)
    }
}

/// Whether `a` and `b` expand to the same polynomial modulo `2^bits` (and at least one has a
/// product, which is what the linear forms do not expand).
pub(super) fn equal_mod(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    a: u32,
    b: u32,
    bits: u16,
) -> Result<bool, Stop> {
    if bits == 0 {
        return Ok(true);
    }
    if cx.wid(a) != cx.wid(b) || bits > cx.wid(a) {
        return Ok(false);
    }
    let has_mul = |x: u32| {
        let mut stack = vec![x];
        let mut seen = 0;
        while let Some(i) = stack.pop() {
            seen += 1;
            if seen > 96 {
                return false;
            }
            let n = cx.node(i);
            if n.op == OpCode::Mul {
                return true;
            }
            if matches!(
                n.op,
                OpCode::Add
                    | OpCode::Sub
                    | OpCode::Neg
                    | OpCode::Not
                    | OpCode::Shl
                    | OpCode::RotL
                    | OpCode::RotR
                    | OpCode::Zext
                    | OpCode::Extract
                    | OpCode::Concat
                    | OpCode::Or
            ) || (matches!(n.op, OpCode::And | OpCode::Xor)
                && (cx.const_val(n.a).is_some() || cx.const_val(n.b).is_some()))
            {
                stack.extend(n.children());
            }
        }
        false
    };
    if !has_mul(a) && !has_mul(b) {
        return Ok(false);
    }
    let Ok(w) = Width::new(bits) else {
        return Ok(false);
    };
    let mut tables = LeafTables::default();
    let mut memo = IdMap::default();
    let mut steps = 0u32;
    let pa = poly_of(cx, a, w, &mut tables, &mut memo, &mut steps);
    let pb = poly_of(cx, b, w, &mut tables, &mut memo, &mut steps);
    r.meter.charge(Counter::PassWork, u64::from(steps))?;
    Ok(matches!((pa, pb), (Some(pa), Some(pb)) if pa == pb))
}

/// Whether `a` and `b` expand to the same polynomial (and at least one has a product, which is
/// what the linear forms do not expand).
pub(super) fn equal(r: &mut Runner<'_, '_>, cx: &Context, a: u32, b: u32) -> Result<bool, Stop> {
    equal_mod(r, cx, a, b, cx.wid(a))
}

fn poly_hash(w: u16, p: &Poly) -> u64 {
    let mut h = crate::hash::combine(0x706f_6c79, u64::from(w));
    for (m, c) in p {
        for &b in m {
            h = crate::hash::combine(h, u64::from(b));
        }
        for &limb in c.limbs() {
            h = crate::hash::combine(h, limb);
        }
    }
    h
}

/// Bottom-up polynomial subterm canonicalization over `order`: unifies distinct sub-DAGs that
/// expand to the same polynomial (or bitwise complement `-p - 1` when smaller) modulo `2^w`,
/// exposing shared atoms to `cofactors`, `linear_mba`, and `mba`. Commits only when the whole
/// DAG strictly shrinks.
#[cfg(feature = "mba")]
pub(super) fn canonicalize_dag(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    order: &[u32],
) -> Result<Option<u32>, Stop> {
    if !(16..=2048).contains(&order.len()) {
        return Ok(None);
    }
    let budget = r.meter.left_in(|b| b.pass_work) / 8;
    if budget < (order.len() as u64) * 8 {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    let mut tables = LeafTables::default();
    let mut memo: IdMap<(u32, u16), Poly> = IdMap::default();
    let mut buckets: IdMap<u64, Vec<(u16, Poly, u32)>> = IdMap::default();
    let mut to: IdMap<u32, u32> = IdMap::default();
    let mut has_poly_mul: IdMap<u32, ()> = IdMap::default();
    let mut live_nodes: IdMap<u32, ()> = IdMap::default();
    for &id in order {
        live_nodes.insert(id, ());
    }
    let mut total_steps = 0u64;
    let mut merged_any = false;

    for &i in order {
        let node = cx.node(i);
        let mut kids = [0u32; 3];
        let mut changed = false;
        let mut child_mul = false;
        for (k, c) in node.children().enumerate() {
            let mapped = to.get(&c).copied().unwrap_or(c);
            kids[k] = mapped;
            changed |= mapped != c;
            child_mul |= has_poly_mul.contains_key(&mapped);
        }
        let mut cur = if changed {
            r.build(cx, |cx| cx.rebuild(i, kids))?
        } else {
            i
        };
        let mut cn = cx.node(cur);
        if !r.mba.swept.is_empty()
            && cn.op == OpCode::Zext
            && cn.width <= 64
            && cx.wid(cn.a) < cn.width
        {
            let full_w = u64::MAX >> (64 - cn.width);
            for wide in super::casts::find_wide_masked(cx, cn.a, cn.width, full_w, 5) {
                if wide != cur && live_nodes.contains_key(&wide) {
                    cur = wide;
                    cn = cx.node(cur);
                    merged_any = true;
                    break;
                }
            }
        }
        let w = cn.width;
        let op = cn.op;
        let own_mul = op == OpCode::Mul && !cx.is_const(cn.a) && !cx.is_const(cn.b);
        let poly_cone = own_mul
            || (child_mul
                && matches!(
                    op,
                    OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Not | OpCode::Mul | OpCode::Shl
                ));
        let indexable = poly_cone
            || matches!(
                op,
                OpCode::Add
                    | OpCode::Sub
                    | OpCode::Neg
                    | OpCode::Not
                    | OpCode::Shl
                    | OpCode::LShr
                    | OpCode::RotL
                    | OpCode::RotR
            );
        if indexable
            && (2..=64).contains(&w)
            && cx.const_val(cur).is_none()
            && let Ok(wt) = Width::new(w)
        {
            let mut steps = 0u32;
            let p_opt = poly_of(cx, cur, wt, &mut tables, &mut memo, &mut steps);
            total_steps += u64::from(steps);
            if total_steps > budget {
                break;
            }
            if let Some(p) = p_opt {
                if poly_cone && p.is_empty() {
                    cur = r.build(cx, |cx| cx.mk_const_u64(w, 0))?;
                    merged_any = true;
                } else if poly_cone && p.len() == 1 && p[0].0 == [0u8; MAX_LEAVES] {
                    let kv = p[0].1;
                    cur = r.build(cx, |cx| cx.mk_const(&kv))?;
                    merged_any = true;
                } else {
                    let h = poly_hash(w, &p);
                    let found = buckets
                        .get(&h)
                        .and_then(|v| v.iter().find(|(bw, bp, _)| *bw == w && *bp == p))
                        .map(|&(_, _, rep)| rep);
                    if let Some(rep) = found {
                        if poly_cone
                            && rep != cur
                            && cx.meta[rep as usize].tree
                                <= cx.meta[cur as usize].tree.saturating_mul(2).saturating_add(4)
                        {
                            cur = rep;
                            merged_any = true;
                        }
                    } else {
                        // Also check bitwise complement `~p == -p - 1`: e.g. `C - a - 1 == ~rep`.
                        let comp = if poly_cone && op != OpCode::Not {
                            let neg_p = add(&Vec::new(), &p, true);
                            let minus_one = vec![([0u8; MAX_LEAVES], BitVec::ones(wt))];
                            let mut cp = add(&neg_p, &minus_one, false);
                            reduce_2adic(cx, &tables, wt, &mut cp);
                            let ch = poly_hash(w, &cp);
                            buckets
                                .get(&ch)
                                .and_then(|v| v.iter().find(|(bw, bp, _)| *bw == w && *bp == cp))
                                .map(|&(_, _, rep)| rep)
                        } else {
                            None
                        };
                        if let Some(rep) = comp
                            && let Some(not_rep) =
                                cx.find(&crate::expr::Node::new(OpCode::Not, w, rep, 0, 0))
                            && cx.meta[not_rep as usize].tree
                                <= cx.meta[cur as usize].tree.saturating_mul(2).saturating_add(4)
                        {
                            cur = not_rep;
                            merged_any = true;
                        }
                        let entry = buckets.entry(h).or_default();
                        if entry.len() < 8 {
                            entry.push((w, p, cur));
                        }
                    }
                }
            }
        }
        if poly_cone && cx.const_val(cur).is_none() {
            has_poly_mul.insert(cur, ());
        }
        live_nodes.insert(cur, ());
        to.insert(i, cur);
    }
    r.meter.charge(Counter::PassWork, total_steps)?;
    if !merged_any {
        return Ok(None);
    }
    let Some(&out) = to.get(&root) else {
        return Ok(None);
    };
    if out == root {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    Ok(matches!(
        cx.dag_size(&[cx.handle(out)], order.len() as u32 - 1)
            .map_err(Stop::Error)?,
        crate::expr::Bounded::Exact(_)
    )
    .then_some(out))
}

#[cfg(test)]
mod tests {
    use crate::engine::{Engine, Run, Strategy};
    use crate::{Context, ParseOptions, Width};

    fn simplifies_to_true(expr: &str) -> bool {
        let mut cx = Context::new();
        let e = cx.parse(expr, &ParseOptions::width(Width::W64)).unwrap();
        let eng = Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap().roots[0].expr;
        cx.as_const(out).unwrap().is_some_and(|v| !v.is_zero())
    }

    #[test]
    fn poly_handles_not_or_const_and_narrow_trunc_zext() {
        // ~y * x + x == -y * x
        assert!(simplifies_to_true("~y * x + x == -y * x"));
        // x | c == (x & ~c) + c inside a narrow 32-bit zext/trunc product
        assert!(simplifies_to_true(
            "zext<64>(trunc<32>((zext<64>(trunc<32>(x) | -18689) * 0x9940dd132333686b) * (a + b)) * 0xb7326e10) \
             == ((a + b) * ((x & 18688) * 0x2bfa80b0 + 0x65534f50) & 0xffffffff)"
        ));
        // Partial-width mod-2^57 polynomial equality with rotl decomposition and subsumed Or
        assert!(simplifies_to_true(
            "let r = rotl(x, 6); let lo = r & 63; \
             extract<56, 1>(y + r + 0x35f9c8925e0c9045 + (z + 0xca06376da1f36fba) * lo) \
             == extract<56, 1>(z * lo + y + x * 0x7e72249783241180 - r * 0x35f9c8925e0c9045 + 0x35f9c8925e0c9045)"
        ));
        // Subsumed Or: ~(x << 6) | (x >>u 58) == ~(x << 6)
        assert!(simplifies_to_true(
            "(~(x << 6) | (x >>u 58)) * y + (rotl(x, 6)) * y == ((x >>u 58) - 1) * y"
        ));
        // DAG polynomial canonicalization unifies equivalent and complemented subterms across bitwise ops
        assert!(simplifies_to_true(
            "let p1 = (x + y) * (x + y); let p2 = x * x + 2 * x * y + y * y; \
             ((p1 ^ z) & 0xff) == ((p2 ^ z) & 0xff)"
        ));
        assert!(simplifies_to_true(
            "let p1 = x * y + z; let p2 = x * (-y) - z - 1; \
             ((p1 & w) ^ p1) == ((~p2 & w) ^ ~p2)"
        ));
        assert!(simplifies_to_true(
            "let v0 = zext<64>(d:32) & 0xc4ca4796; \
             let v1 = concat(zext<62>(~(trunc<1>(a:64) ^ extract<3, 1>(a))), 0:2); \
             let v2 = (a & 128 | b:64 & 0x3c7300 | v1) + 0x5e124156224aa1e7; \
             let v3 = v2 >>u 4; \
             let v4 = v1 * 0x3000000000000000; \
             let v5 = rotl(v2, 60); \
             let v6 = v4 + 0x8fffffffffffffff; \
             let v7 = v5 * 0x110a53cdc4dd8bdd; \
             ((v0 + v3) * 0x110a53cdc4dd8bdd + 0x37309649008bcd8 - v4 + 0x5f27cce5e9fd7e9c) * v5 \
             + v6 * (v7 + v0 * 0x40e947a1b54bcc4d + 0x1eede61ec3450e29) \
             + (v6 + v5) * 0x40e947a1b54bcc4d * (v0 ^ 0xfffd7d57e6caf79e) \
             + v4 + 0x9c1d50602ced70af \
             + (v0 * 0x2fdef3d3f06e4070 - v7 + 0x31401341e12eede4) * v3 == v5"
        ));
    }

    #[test]
    fn poly_rejects_unequal_narrow_and_or_expressions() {
        // Differs in bit 32 (overflows low 32 bits)
        assert!(!simplifies_to_true(
            "zext<64>(trunc<32>(x * y)) == x * y"
        ));
        // Non-disjoint Or is not equal to Add
        assert!(!simplifies_to_true(
            "((x << 5) | (x >>u 58)) * y == ((x << 5) + (x >>u 58)) * y"
        ));
        // Wrong constant in Or decomposition
        assert!(!simplifies_to_true(
            "(x | 0x10) * y == ((x & ~0x10) + 0x20) * y"
        ));
        // Missing cross term 2*x*y in DAG polynomial subterm
        assert!(!simplifies_to_true(
            "let p1 = (x + y) * (x + y); let p2 = x * x + y * y; \
             ((p1 ^ z) & 0xff) == ((p2 ^ z) & 0xff)"
        ));
    }
}
