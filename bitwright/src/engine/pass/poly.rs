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
const MAX_LEAVES: usize = 12;

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
                if let Some(sub) = poly_of(cx, node.a, sub_w, tables, memo, steps) {
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
    memo.insert((x, bits), p.clone());
    Some(p)
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
            ) || (matches!(n.op, OpCode::And | OpCode::Or)
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
    }
}
