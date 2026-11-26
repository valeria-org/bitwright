//! Collect common multiplicands before proving that the remaining weighted sum of
//! bitwise functions is constant. The proof is local: no fact about a multiplicand,
//! or the arithmetic hidden underneath a bitwise function, is needed.

use super::opaque_predicate::{Work, cancel_parts, rewrite_sums, terms};
use super::{Counter, Runner, Stop};
use crate::expr::{Context, Node, OpCode};
use crate::hash::IdMap;
use crate::{BinOp, Error};

const MAX_TERMS: usize = 96;
const MAX_CODE: usize = 512;
const ATOMS: [u64; 6] = [
    0xaaaaaaaaaaaaaaaa,
    0xcccccccccccccccc,
    0xf0f0f0f0f0f0f0f0,
    0xff00ff00ff00ff00,
    0xffff0000ffff0000,
    0xffffffff00000000,
];

/// Canonicalized affine form of a non-bitwise leaf (`bias + sum c_i * t_i` mod `2^w`),
/// so that an expanded bitwise complement `-X - 1` shares `X`'s column as `~X`.
struct AffineLeaf {
    width: u16,
    bias: u64,
    parts: Vec<(u32, u64)>,
    slot: u32,
}

#[derive(Default)]
struct Table {
    code: Vec<Node>,
    places: IdMap<u32, u32>,
    affines: Vec<AffineLeaf>,
    /// Pre-scanned constant shifts `(base, shift_amount, is_lshr) -> node_id` in the current group
    /// so `rotl(x, k)` decomposes into `(x << k) | (x >>u (w - k))` without allocating a 3rd atom.
    shifts: Vec<(u32, u16, bool, u32)>,
    terms: Vec<(u32, u64)>,
    atoms: usize,
    /// Per atom slot (`0..6`): exact known-zero bitmask (`1` where the atom is always 0).
    atom_zeros: [u64; 6],
    /// Per atom slot (`0..6`): exact known-one bitmask (`1` where the atom is always 1).
    atom_ones: [u64; 6],
}

/// Cheap sound `(known_zeros, known_ones)` bitmasks for a node `i` (`<= 64` bits).
fn node_known_bits(cx: &Context, i: u32, depth: u8) -> (u64, u64) {
    let n = cx.node(i);
    let w = n.width;
    if w == 0 || w > 64 {
        return (0, 0);
    }
    let mask = u64::MAX >> (64 - w);
    if depth == 0 {
        return (0, 0);
    }
    let (z, o) = match n.op {
        OpCode::Const => {
            let v = cx.const_val(i).and_then(|k| k.to_u64()).unwrap_or(0) & mask;
            ((!v) & mask, v)
        }
        OpCode::Shl => match cx.const_val(n.b).and_then(|v| v.to_u64()) {
            Some(s) if s >= u64::from(w) => (mask, 0),
            Some(s) => {
                let (az, ao) = node_known_bits(cx, n.a, depth - 1);
                let low = (1u64 << s) - 1;
                (((az << s) | low) & mask, (ao << s) & mask)
            }
            None => (0, 0),
        },
        OpCode::LShr => match cx.const_val(n.b).and_then(|v| v.to_u64()) {
            Some(s) if s >= u64::from(w) => (mask, 0),
            Some(s) => {
                let (az, ao) = node_known_bits(cx, n.a, depth - 1);
                let hi = mask & !(mask >> s);
                (((az >> s) | hi) & mask, (ao >> s) & mask)
            }
            None => (0, 0),
        },
        OpCode::And => {
            let (az, ao) = node_known_bits(cx, n.a, depth - 1);
            let (bz, bo) = node_known_bits(cx, n.b, depth - 1);
            ((az | bz) & mask, (ao & bo) & mask)
        }
        OpCode::Or => {
            let (az, ao) = node_known_bits(cx, n.a, depth - 1);
            let (bz, bo) = node_known_bits(cx, n.b, depth - 1);
            ((az & bz) & mask, (ao | bo) & mask)
        }
        OpCode::Xor => {
            let (az, ao) = node_known_bits(cx, n.a, depth - 1);
            let (bz, bo) = node_known_bits(cx, n.b, depth - 1);
            (
                ((az & bz) | (ao & bo)) & mask,
                ((az & bo) | (ao & bz)) & mask,
            )
        }
        OpCode::Not => {
            let (az, ao) = node_known_bits(cx, n.a, depth - 1);
            (ao & mask, az & mask)
        }
        OpCode::Zext => {
            let sw = cx.wid(n.a);
            let (az, ao) = node_known_bits(cx, n.a, depth - 1);
            let hi = if sw < 64 {
                mask & !((1u64 << sw) - 1)
            } else {
                0
            };
            ((az | hi) & mask, ao & mask)
        }
        OpCode::Extract if cx.wid(n.a) <= 64 => {
            let (az, ao) = node_known_bits(cx, n.a, depth - 1);
            ((az >> n.b) & mask, (ao >> n.b) & mask)
        }
        OpCode::Select => {
            let (tz, to) = node_known_bits(cx, n.b, depth - 1);
            let (fz, fo) = node_known_bits(cx, n.c, depth - 1);
            ((tz & fz) & mask, (to & fo) & mask)
        }
        OpCode::Add | OpCode::Sub => {
            let known_add = |az: u64, ao: u64, bz: u64, bo: u64| -> (u64, u64) {
                let min_a = u128::from(ao & mask);
                let max_a = u128::from((!az) & mask);
                let min_b = u128::from(bo & mask);
                let max_b = u128::from((!bz) & mask);
                let sum_min = min_a + min_b;
                let sum_max = max_a + max_b;
                let c_min = (sum_min ^ min_a ^ min_b) as u64;
                let c_max = (sum_max ^ max_a ^ max_b) as u64;
                let ua = (!az & !ao) & mask;
                let ub = (!bz & !bo) & mask;
                let uncertain = (ua | ub | (c_min ^ c_max)) & mask;
                let known = (!uncertain) & mask;
                let s = (sum_min as u64) & mask;
                ((!s) & known, s & known)
            };
            let (az, ao) = node_known_bits(cx, n.a, depth - 1);
            let (bz, bo) = node_known_bits(cx, n.b, depth - 1);
            if n.op == OpCode::Add {
                known_add(az, ao, bz, bo)
            } else {
                let (nb_z, nb_o) = known_add(bo & mask, bz & mask, (!1u64) & mask, 1 & mask);
                known_add(az, ao, nb_z, nb_o)
            }
        }
        OpCode::Neg => {
            let (az, ao) = node_known_bits(cx, n.a, depth - 1);
            let min_a = u128::from(az & mask);
            let max_a = u128::from((!ao) & mask);
            let sum_min = min_a + 1;
            let sum_max = max_a + 1;
            let c_min = (sum_min ^ min_a ^ 1) as u64;
            let c_max = (sum_max ^ max_a ^ 1) as u64;
            let ua = (!az & !ao) & mask;
            let uncertain = (ua | (c_min ^ c_max)) & mask;
            let known = (!uncertain) & mask;
            let s = (sum_min as u64) & mask;
            ((!s) & known, s & known)
        }
        OpCode::Mul => {
            let (az, ao) = node_known_bits(cx, n.a, depth - 1);
            let (bz, bo) = node_known_bits(cx, n.b, depth - 1);
            if ((az | ao) & mask) == mask && ((bz | bo) & mask) == mask {
                let p = ao.wrapping_mul(bo) & mask;
                ((!p) & mask, p)
            } else {
                let tz_a = if ((!az) & mask) == 0 {
                    u32::from(w)
                } else {
                    ((!az) & mask).trailing_zeros()
                };
                let tz_b = if ((!bz) & mask) == 0 {
                    u32::from(w)
                } else {
                    ((!bz) & mask).trailing_zeros()
                };
                let tz = tz_a.saturating_add(tz_b).min(u32::from(w));
                let z_low = if tz >= 64 {
                    mask
                } else {
                    ((1u64 << tz) - 1) & mask
                };
                let o_bit = if tz < u32::from(w)
                    && tz_a < 64
                    && tz_b < 64
                    && (ao & (1u64 << tz_a)) != 0
                    && (bo & (1u64 << tz_b)) != 0
                {
                    (1u64 << tz) & mask
                } else {
                    0
                };
                (z_low, o_bit)
            }
        }
        _ => (0, 0),
    };
    (z & mask, o & mask)
}

impl Table {
    fn push_node(&mut self, n: Node) -> Option<u32> {
        if self.code.len() >= MAX_CODE {
            return None;
        }
        let p = self.code.len() as u32;
        self.code.push(n);
        Some(p)
    }

    fn const_node(w: u16, k: u64) -> Node {
        Node {
            op: OpCode::Const,
            width: w,
            a: k as u32,
            b: (k >> 32) as u32,
            c: 0,
            aux: 0,
        }
    }

    fn place_atom(&mut self, cx: &Context, i: u32, depth: u8, work: &mut Work) -> Option<u32> {
        let mut n = cx.node(i);
        let w = n.width;
        // An expanded bitwise complement `-X - 1` (e.g. `a * -1 + b * (-C) - 1`) is `~X`:
        // canonicalize small affine sums so `X` and `~X` share one atom column.
        if w <= 64
            && depth > 1
            && matches!(n.op, OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Mul)
        {
            let mask = u64::MAX >> (64 - w);
            let mut bias = 0u64;
            let mut parts = Vec::new();
            if terms(cx, i, 1, &mut bias, &mut parts, 16, false, work).is_some()
                && parts.len() <= 16
                && cancel_parts(&mut parts, mask, work).is_some()
            {
                let bias = bias & mask;
                for (_, c) in &mut parts {
                    *c &= mask;
                }
                if parts.is_empty() {
                    return self.push_node(Self::const_node(w, bias));
                }
                if parts.len() == 1 && parts[0].1 == 1 && bias == 0 && parts[0].0 != i {
                    return self.place(cx, parts[0].0, depth - 1, work);
                }
                if parts.len() == 1 && parts[0].1 == mask && bias == mask && parts[0].0 != i {
                    let inner = self.place(cx, parts[0].0, depth - 1, work)?;
                    return self.push_node(Node {
                        op: OpCode::Not,
                        width: w,
                        a: inner,
                        b: 0,
                        c: 0,
                        aux: 0,
                    });
                }
                for leaf in &self.affines {
                    if leaf.width != w || leaf.parts.len() != parts.len() {
                        continue;
                    }
                    if leaf.bias == bias && leaf.parts == parts {
                        return Some(leaf.slot);
                    }
                    if leaf.bias.wrapping_add(bias) & mask == mask
                        && leaf
                            .parts
                            .iter()
                            .zip(&parts)
                            .all(|(&(a, ca), &(b, cb))| a == b && ca.wrapping_add(cb) & mask == 0)
                    {
                        return self.push_node(Node {
                            op: OpCode::Not,
                            width: w,
                            a: leaf.slot,
                            b: 0,
                            c: 0,
                            aux: 0,
                        });
                    }
                }
                if self.atoms == ATOMS.len() {
                    return None;
                }
                let (az, ao) = node_known_bits(cx, i, 6);
                self.atom_zeros[self.atoms] = az;
                self.atom_ones[self.atoms] = ao;
                n.op = OpCode::Sym;
                n.a = self.atoms as u32;
                self.atoms += 1;
                let p = self.push_node(n)?;
                self.affines.push(AffineLeaf {
                    width: w,
                    bias,
                    parts,
                    slot: p,
                });
                return Some(p);
            }
        }
        if self.atoms == ATOMS.len() {
            return None;
        }
        let (az, ao) = node_known_bits(cx, i, 6);
        self.atom_zeros[self.atoms] = az;
        self.atom_ones[self.atoms] = ao;
        n.op = OpCode::Sym;
        n.a = self.atoms as u32;
        self.atoms += 1;
        self.push_node(n)
    }

    // Read the bitwise DAG, maintaining the invariant that `place(i)` agrees with `i` on
    // bits `0..wid(i)`. Truncation (`extract<0, w>`) preserves low bits and `zext` clears
    // high bits with a constant mask, so mixed-width masked bitwise terms share atoms.
    fn place(&mut self, cx: &Context, i: u32, depth: u8, work: &mut Work) -> Option<u32> {
        work.take(1)?;
        if let Some(&p) = self.places.get(&i) {
            return Some(p);
        }
        if depth == 0 || self.code.len() >= MAX_CODE {
            return None;
        }
        let mut n = cx.node(i);
        let p = match n.op {
            OpCode::Const => self.push_node(n)?,
            OpCode::Not => {
                n.a = self.place(cx, n.a, depth - 1, work)?;
                self.push_node(n)?
            }
            OpCode::And | OpCode::Or | OpCode::Xor => {
                n.a = self.place(cx, n.a, depth - 1, work)?;
                n.b = self.place(cx, n.b, depth - 1, work)?;
                self.push_node(n)?
            }
            OpCode::Extract if n.b == 0 && cx.wid(n.a) <= 64 => {
                self.place(cx, n.a, depth - 1, work)?
            }
            OpCode::Zext if n.width <= 64 && cx.wid(n.a) < n.width => {
                let sw = cx.wid(n.a);
                let inner = self.place(cx, n.a, depth - 1, work)?;
                let mask_node = self.push_node(Self::const_node(n.width, u64::MAX >> (64 - sw)))?;
                self.push_node(Node {
                    op: OpCode::And,
                    width: n.width,
                    a: inner,
                    b: mask_node,
                    c: 0,
                    aux: 0,
                })?
            }
            OpCode::RotL | OpCode::RotR
                if n.width <= 64 && cx.const_val(n.b).and_then(|v| v.to_u64()).is_some() =>
            {
                let w = n.width;
                let raw = (cx.const_val(n.b)?.to_u64()? % u64::from(w)) as u16;
                let lsh = if n.op == OpCode::RotL {
                    raw
                } else {
                    (w - raw) % w
                };
                if lsh == 0 {
                    self.place(cx, n.a, depth - 1, work)?
                } else {
                    let rsh = w - lsh;
                    let shl_id = self
                        .shifts
                        .iter()
                        .find(|&&(b, s, r, _)| b == n.a && s == lsh && !r)
                        .map(|&(_, _, _, id)| id);
                    let lshr_id = self
                        .shifts
                        .iter()
                        .find(|&&(b, s, r, _)| b == n.a && s == rsh && r)
                        .map(|&(_, _, _, id)| id);
                    if let (Some(hi), Some(lo)) = (shl_id, lshr_id) {
                        let pa = self.place(cx, hi, depth - 1, work)?;
                        let pb = self.place(cx, lo, depth - 1, work)?;
                        self.push_node(Node {
                            op: OpCode::Or,
                            width: w,
                            a: pa,
                            b: pb,
                            c: 0,
                            aux: 0,
                        })?
                    } else {
                        self.place_atom(cx, i, depth, work)?
                    }
                }
            }
            _ => self.place_atom(cx, i, depth, work)?,
        };
        self.places.insert(i, p);
        Some(p)
    }

    /// At each bit position j the sum contributes 2^j times the weighted count of
    /// true terms. Check that count on *every* Boolean assignment, modulo 2^(w-j).
    /// Positions where all bitwise constants have identical bits share a table;
    /// checking its lowest j implies equality at all the others. Testing aggregate
    /// all-zero/all-ones words instead would unsoundly cancel across positions.
    fn constant(
        &mut self,
        cx: &Context,
        parts: &[(u32, u64)],
        w: u16,
        work: &mut Work,
    ) -> Option<u64> {
        self.code.clear();
        self.places.clear();
        self.affines.clear();
        self.shifts.clear();
        self.terms.clear();
        self.atoms = 0;
        let mut scan_stack: Vec<(u32, u8)> = parts.iter().map(|&(i, _)| (i, 12)).collect();
        let mut scanned = 0u32;
        while let Some((cur, d)) = scan_stack.pop() {
            scanned += 1;
            if scanned > 192 {
                break;
            }
            let m = cx.node(cur);
            if matches!(m.op, OpCode::Shl | OpCode::LShr)
                && m.width == w
                && let Some(s) = cx.const_val(m.b).and_then(|v| v.to_u64())
                && s > 0
                && s < u64::from(w)
            {
                let key = (m.a, s as u16, m.op == OpCode::LShr, cur);
                if !self.shifts.contains(&key) && self.shifts.len() < 16 {
                    self.shifts.push(key);
                }
            } else if d > 0
                && matches!(
                    m.op,
                    OpCode::Not
                        | OpCode::And
                        | OpCode::Or
                        | OpCode::Xor
                        | OpCode::Extract
                        | OpCode::Zext
                )
            {
                for c in m.children() {
                    scan_stack.push((c, d - 1));
                }
            }
        }
        for &(i, k) in parts {
            let mut p = self.place(cx, i, 48, work)?;
            let iw = cx.wid(i);
            if iw < w {
                let mask_node = self.push_node(Self::const_node(w, u64::MAX >> (64 - iw)))?;
                p = self.push_node(Node {
                    op: OpCode::And,
                    width: w,
                    a: p,
                    b: mask_node,
                    c: 0,
                    aux: 0,
                })?;
            }
            self.terms.push((p, k));
        }
        let rows = 1usize << self.atoms;
        let all = u64::MAX >> (64 - rows);
        let mask = u64::MAX >> (64 - w);
        let mut remaining = mask;
        let mut result = 0u64;
        let mut values = [0u64; MAX_CODE];
        while remaining != 0 {
            work.take(self.code.len() as u64)?;
            let j = remaining.trailing_zeros();
            let mut class = remaining;
            for (p, n) in self.code.iter().enumerate() {
                values[p] = match n.op {
                    OpCode::Const => {
                        let k = u64::from(n.a) | (u64::from(n.b) << 32);
                        if k & (1 << j) == 0 {
                            class &= !k;
                            0
                        } else {
                            class &= k;
                            all
                        }
                    }
                    OpCode::Sym => {
                        let a = n.a as usize;
                        let z = self.atom_zeros[a];
                        let o = self.atom_ones[a];
                        if z & (1 << j) != 0 {
                            class &= z;
                            0
                        } else if o & (1 << j) != 0 {
                            class &= o;
                            all
                        } else {
                            class &= !(z | o);
                            ATOMS[a]
                        }
                    }
                    OpCode::Not => !values[n.a as usize],
                    OpCode::And => values[n.a as usize] & values[n.b as usize],
                    OpCode::Or => values[n.a as usize] | values[n.b as usize],
                    OpCode::Xor => values[n.a as usize] ^ values[n.b as usize],
                    _ => unreachable!(),
                };
            }
            let mut counts = [0u64; 64];
            for &(p, k) in &self.terms {
                let mut active = values[p as usize] & all;
                work.take(1 + u64::from(active.count_ones()))?;
                while active != 0 {
                    let at = active.trailing_zeros() as usize;
                    counts[at] = counts[at].wrapping_add(k);
                    active &= active - 1;
                }
            }
            work.take(rows as u64)?;
            if counts[1..rows]
                .iter()
                .any(|&v| (v ^ counts[0]) & (mask >> j) != 0)
            {
                return None;
            }
            result = result.wrapping_add(class.wrapping_mul(counts[0]));
            remaining &= !class;
        }
        Some(result & mask)
    }
}

// A repeated sum often reappears multiplied by a different scalar everywhere.
// Keep the proved coefficients divided by an odd unit and by their common
// power of two. Another multiple of that vector can reuse its constant *only*
// after checking every coefficient and the number of surviving bits.
struct Kernel {
    terms: Vec<(u32, u64)>,
    pivot: usize,
    bits: u16,
    value: u64,
}

#[derive(Default)]
pub(super) struct Sums {
    parts: Vec<(u32, u64)>,
    products: Vec<Option<([u32; 2], u64)>>,
    group: Vec<(u32, u64)>,
    scaled: Vec<(u32, u64)>,
    rest: Vec<(u32, u64)>,
    known: Vec<Kernel>,
    table: Table,
}

/// Split a single-variable affine factor `c1 * x + c2` (with constant `c2 != 0`)
/// out of a product `(c1 * x + c2) * y` so the linear term `c1 * x * y` and the
/// unmultiplied term `c2 * y` can each join their own cofactor groups.
fn affine_factor(cx: &Context, id: u32, w: u16) -> Option<(u32, u64, u64)> {
    let n = cx.node(id);
    if !matches!(n.op, OpCode::Add | OpCode::Sub) || n.width != w {
        return None;
    }
    let mask = u64::MAX >> (64 - w);
    let (var, bias, sign) = match (cx.const_val(n.a), cx.const_val(n.b)) {
        (None, Some(k)) => {
            let c = k.to_u64()?;
            (
                n.a,
                if n.op == OpCode::Add {
                    c
                } else {
                    c.wrapping_neg()
                } & mask,
                1u64,
            )
        }
        (Some(k), None) => {
            let c = k.to_u64()? & mask;
            (n.b, c, if n.op == OpCode::Add { 1u64 } else { mask })
        }
        _ => return None,
    };
    if bias == 0 {
        return None;
    }
    let vn = cx.node(var);
    let (base, scale) = match vn.op {
        OpCode::Mul => match (cx.const_val(vn.a), cx.const_val(vn.b)) {
            (None, Some(k)) => (vn.a, k.to_u64()?),
            (Some(k), None) => (vn.b, k.to_u64()?),
            _ => (var, 1),
        },
        OpCode::Shl
            if cx
                .const_val(vn.b)
                .and_then(|v| v.to_u64())
                .is_some_and(|s| s < u64::from(w)) =>
        {
            (vn.a, 1u64 << cx.const_val(vn.b)?.to_u64()?)
        }
        OpCode::Neg => (vn.a, mask),
        _ => (var, 1),
    };
    Some((base, scale.wrapping_mul(sign) & mask, bias))
}

/// Decompose a product node `t` (with outer coefficient `k`) into `(pair_of_factors, combined_scalar)`.
/// Handles nested scalar multipliers, 2-factor products via `scaled_factors`, and 3+-factor
/// products by stripping outer scalar factors to expose the immediate `(lhs, rhs)` pair.
fn product_pair(cx: &Context, t: u32, k: u64, w: u16, work: &mut Work) -> Option<([u32; 2], u64)> {
    if cx.node(t).op != OpCode::Mul {
        return None;
    }
    work.take(32)?;
    if let Some((v, fs)) = super::super::linear::scaled_factors(cx, t) {
        let coeff = k.wrapping_mul(v.limbs()[0]);
        if let &[a, b] = fs.as_slice() {
            return Some(([a, b], coeff));
        }
    }
    // Strip outer constant multiplications to find the top non-constant `a * b`.
    let mut cur = t;
    let mut coeff = k;
    for _ in 0..8 {
        let n = cx.node(cur);
        if n.op != OpCode::Mul {
            return None;
        }
        if let Some(c) = cx.const_val(n.b).and_then(|v| v.to_u64()) {
            coeff = coeff.wrapping_mul(c);
            cur = n.a;
        } else if let Some(c) = cx.const_val(n.a).and_then(|v| v.to_u64()) {
            coeff = coeff.wrapping_mul(c);
            cur = n.b;
        } else {
            let mask = u64::MAX >> (64 - w);
            return Some(([n.a, n.b], coeff & mask));
        }
    }
    None
}

impl Sums {
    fn value(&mut self, cx: &Context, w: u16, work: &mut Work) -> Option<u64> {
        let mask = u64::MAX >> (64 - w);
        work.take((self.group.len() * 6) as u64)?;
        self.group.sort_unstable();
        for known in &self.known {
            if known.terms.len() != self.group.len() {
                continue;
            }
            let k = self.group[known.pivot].1 & mask;
            if u32::from(known.bits) + k.trailing_zeros() >= u32::from(w) {
                work.take(self.group.len() as u64)?;
                if known
                    .terms
                    .iter()
                    .zip(&self.group)
                    .all(|(&(a, v), &(b, t))| a == b && (v.wrapping_mul(k) ^ t) & mask == 0)
                {
                    return Some(k.wrapping_mul(known.value) & mask);
                }
            }
        }
        let (pivot, &(_, k)) = self
            .group
            .iter()
            .enumerate()
            .min_by_key(|(_, p)| (p.1 & mask).trailing_zeros())?;
        let shift = (k & mask).trailing_zeros();
        if shift >= u32::from(w) {
            return Some(0);
        }
        let bits = w - shift as u16;
        let odd = k >> shift;
        let mut inv = odd; // inverse mod 8; Newton doubles correct bits each iteration.
        for _ in 0..5 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(odd.wrapping_mul(inv)));
        }
        let low = mask >> shift;
        for (_, c) in &mut self.group {
            *c = (*c >> shift).wrapping_mul(inv) & low;
        }
        let value = match self.table.constant(cx, &self.group, bits, work) {
            Some(v) => v,
            None => {
                let budget = work.left.min(4096);
                let mut left = budget;
                let v = super::opaque_predicate::constant_parts(cx, &self.group, bits, &mut left);
                work.left -= budget - left;
                v?
            }
        };
        if self.known.len() < 32 {
            self.known.push(Kernel {
                terms: self.group.clone(),
                pivot,
                bits,
                value,
            });
        }
        Some(value.wrapping_mul(k) & mask)
    }

    pub(super) fn collapse(
        &mut self,
        cx: &mut Context,
        i: u32,
        _terminal: bool,
        work: &mut Work,
    ) -> Result<Option<u32>, Error> {
        let w = cx.wid(i);
        if w > 64 {
            return Ok(None);
        }
        let mask = u64::MAX >> (64 - w);
        let mut bias = 0;
        self.parts.clear();
        if terms(cx, i, 1, &mut bias, &mut self.parts, 64, true, work).is_none()
            || self.parts.len() < 2
        {
            return Ok(None);
        }
        // Canonicalize nested scalar-product pairs (e.g. `x * (x * C1) + x * (x * C2)`) and
        // distribute affine-shifted factors `(c1 * x + c2) * y` when a product has an affine side.
        let raw_len = self.parts.len();
        if cancel_parts(&mut self.parts, mask, work).is_none() || self.parts.len() > MAX_TERMS {
            return Ok(None);
        }
        let mut changed = self.parts.len() + 1 < raw_len || self.parts.len() <= 1;
        if self.parts.is_empty() {
            return cx.mk_const_u64(w, bias & mask).map(Some);
        }
        let magnitude = |k: u64| (k & mask).min(k.wrapping_neg() & mask);
        // First try genuine common multiplicands (all of them, not just the largest).
        // Keep unrelated summands: they neither constrain a cofactor nor need to be bitwise.
        self.products.clear();
        for &(t, k) in &self.parts {
            let p = product_pair(cx, t, k, w, work);
            self.products.push(p);
        }
        // Cancel identical factor pairs with opposite/combining scalars (e.g. `a * (b * C1) + a * (b * C2)`).
        if self.products.iter().flatten().count() >= 2 {
            for idx in 0..self.products.len() {
                let Some((mut p1, mut c1)) = self.products[idx] else {
                    continue;
                };
                if p1[0] > p1[1] {
                    p1.swap(0, 1);
                }
                let mut merged = false;
                for j in (idx + 1)..self.products.len() {
                    let Some((mut p2, c2)) = self.products[j] else {
                        continue;
                    };
                    if p2[0] > p2[1] {
                        p2.swap(0, 1);
                    }
                    if p1 == p2 {
                        c1 = c1.wrapping_add(c2) & mask;
                        self.products[j] = None;
                        self.parts[j].1 = 0;
                        merged = true;
                    }
                }
                if merged {
                    changed = true;
                    if c1 == 0 {
                        self.products[idx] = None;
                        self.parts[idx].1 = 0;
                    } else {
                        self.products[idx] = Some((p1, c1));
                        // Rebuild canonical product coefficient only if needed on emit.
                        let prod_id = cx.c_bin(BinOp::Mul, p1[0], p1[1])?;
                        self.parts[idx] = (prod_id, c1);
                    }
                }
            }
            // Reunite distributed factor pairs `k * (g * A) + k * (g * B) == k * (g * K)` when
            // an existing factor `K` in `self.products` equals `A + B` (or `A - B`).
            let mut factor_set: Vec<u32> = Vec::new();
            for &(pair, _) in self.products.iter().flatten() {
                for f in pair {
                    if !factor_set.contains(&f) && factor_set.len() < 32 {
                        factor_set.push(f);
                    }
                }
            }
            for idx in 0..self.products.len() {
                let Some((p1, c1)) = self.products[idx] else {
                    continue;
                };
                for j in (idx + 1)..self.products.len() {
                    let Some((p2, c2)) = self.products[j] else {
                        continue;
                    };
                    let (same_sign, neg_b) = if c1 == c2 {
                        (true, false)
                    } else if c1.wrapping_add(c2) & mask == 0 {
                        (true, true)
                    } else {
                        (false, false)
                    };
                    if !same_sign {
                        continue;
                    }
                    let shared = if p1[0] == p2[0] {
                        Some((p1[0], p1[1], p2[1]))
                    } else if p1[0] == p2[1] {
                        Some((p1[0], p1[1], p2[0]))
                    } else if p1[1] == p2[0] {
                        Some((p1[1], p1[0], p2[1]))
                    } else if p1[1] == p2[1] {
                        Some((p1[1], p1[0], p2[0]))
                    } else {
                        None
                    };
                    let Some((g, fa, fb)) = shared else { continue };
                    let target_k = factor_set.iter().copied().find(|&kf| {
                        if kf == g || kf == fa || kf == fb || cx.wid(kf) != cx.wid(g) {
                            return false;
                        }
                        let kn = cx.node(kf);
                        if !neg_b && kn.op == OpCode::Add {
                            (kn.a == fa && kn.b == fb) || (kn.a == fb && kn.b == fa)
                        } else if neg_b && kn.op == OpCode::Sub {
                            kn.a == fa && kn.b == fb
                        } else {
                            false
                        }
                    });
                    if let Some(kf) = target_k {
                        let prod_id = cx.c_bin(BinOp::Mul, g, kf)?;
                        self.products[idx] = Some(([g, kf], c1));
                        self.parts[idx] = (prod_id, c1);
                        self.products[j] = None;
                        self.parts[j].1 = 0;
                        changed = true;
                        break;
                    }
                }
            }
        }
        // If any product has an affine factor `(c1 * x + c2) * y` where `x` appears in another
        // product or `y` is bitwise, expand it into `c1 * (x * y) + c2 * y` so `x` groups cleanly.
        let has_affine_prod = self.products.iter().flatten().any(|&([a, b], _)| {
            affine_factor(cx, a, w).is_some() || affine_factor(cx, b, w).is_some()
        });
        let saved_parts = if has_affine_prod {
            Some(self.parts.clone())
        } else {
            None
        };
        let mut expanded_any = false;
        if has_affine_prod && self.parts.len() <= MAX_TERMS - 8 {
            let mut extra_parts: Vec<(u32, u64)> = Vec::new();
            let mut extra_prods: Vec<Option<([u32; 2], u64)>> = Vec::new();
            for idx in 0..self.products.len() {
                let Some(([a, b], coeff)) = self.products[idx] else {
                    continue;
                };
                let split = if let Some((x, s, c)) = affine_factor(cx, a, w) {
                    Some((x, s, c, b))
                } else if let Some((x, s, c)) = affine_factor(cx, b, w) {
                    Some((x, s, c, a))
                } else {
                    None
                };
                let Some((x, s, c, other)) = split else {
                    continue;
                };
                if self.parts.len() + extra_parts.len() >= MAX_TERMS {
                    break;
                }
                let lin_coeff = coeff.wrapping_mul(s) & mask;
                let const_coeff = coeff.wrapping_mul(c) & mask;
                let xy = cx.c_bin(BinOp::Mul, x, other)?;
                self.parts[idx] = (xy, lin_coeff);
                self.products[idx] = Some(([x, other], lin_coeff));
                if const_coeff != 0 {
                    extra_parts.push((other, const_coeff));
                    extra_prods.push(None);
                }
                expanded_any = true;
            }
            if expanded_any {
                self.parts.extend(extra_parts);
                self.products.extend(extra_prods);
            }
        }
        self.scaled.clear();
        let mut tried: Vec<u32> = Vec::new();
        let mut counts: Vec<u32> = Vec::with_capacity(self.products.len() * 2);
        for _ in 0..16 {
            counts.clear();
            for &(pair, _) in self.products.iter().flatten() {
                if !tried.contains(&pair[0]) {
                    counts.push(pair[0]);
                }
                if pair[1] != pair[0] && !tried.contains(&pair[1]) {
                    counts.push(pair[1]);
                }
            }
            if counts.len() < 2 {
                break;
            }
            if work.take(counts.len() as u64).is_none() {
                return Ok(None);
            }
            counts.sort_unstable();
            let mut best = (0usize, 0u32);
            let mut run = 0;
            while run < counts.len() {
                let f = counts[run];
                let end = run + counts[run..].partition_point(|&x| x == f);
                if end - run > best.0 {
                    best = (end - run, f);
                }
                run = end;
            }
            if best.0 < 2 {
                break;
            }
            let f = best.1;
            tried.push(f);
            self.group.clear();
            for &([a, b], k) in self.products.iter().flatten() {
                if a == f || b == f {
                    self.group.push((if a == f { b } else { a }, k));
                }
            }
            if cancel_parts(&mut self.group, mask, work).is_none() {
                continue;
            }
            let k = if self.group.is_empty() {
                0
            } else {
                let Some(k) = self.value(cx, w, work) else {
                    continue;
                };
                k
            };
            for ((_, c), p) in self.parts.iter_mut().zip(&mut self.products) {
                if p.is_some_and(|(pair, _)| pair.contains(&f)) {
                    *c = 0;
                    *p = None;
                }
            }
            if k & mask != 0 {
                self.scaled.push((f, k));
            }
            changed = true;
        }
        // If affine expansion did not collapse any product group, restore the original
        // unexpanded terms so we never return a larger distributed form.
        if expanded_any && self.scaled.is_empty() && !changed {
            if let Some(orig) = saved_parts {
                self.parts = orig;
            }
        } else if expanded_any {
            // Merge any non-product terms that now share a node ID (e.g. `other` from expansion
            // matching an existing summand).
            if cancel_parts(&mut self.parts, mask, work).is_none() {
                return Ok(None);
            }
        }
        // First check equal-magnitude groups through the normalized `Kernel` cache:
        // repeated sums with different scalars reuse one exact proof in O(terms).
        if work.take((6 * self.parts.len()) as u64).is_none() {
            return Ok(None);
        }
        self.parts.sort_unstable_by_key(|&(t, k)| (magnitude(k), t));
        let mut lo = 0;
        let mut distinct_mags = 0usize;
        while lo < self.parts.len() {
            let k = magnitude(self.parts[lo].1);
            let hi = lo + self.parts[lo..].partition_point(|&(_, c)| magnitude(c) == k);
            if k != 0 {
                if hi - lo > 1 {
                    self.group.clear();
                    self.group.extend_from_slice(&self.parts[lo..hi]);
                    if let Some(v) = self.value(cx, w, work) {
                        bias = bias.wrapping_add(v);
                        self.parts[lo..hi].fill((0, 0));
                        changed = true;
                        lo = hi;
                        continue;
                    }
                }
                distinct_mags += 1;
            }
            lo = hi;
        }
        // Only if mixed-magnitude non-product terms remain (e.g. a partition alongside an
        // OR-AND-XNOR, or an irreducible mixed-weight Boolean identity), check them jointly.
        if distinct_mags >= 2 {
            self.rest.clear();
            for &(t, k) in &self.parts {
                if k & mask != 0 && cx.node(t).op != OpCode::Mul {
                    self.rest.push((t, k));
                }
            }
            if self.rest.len() >= 2
                && let Some(k) = self.table.constant(cx, &self.rest, w, work)
            {
                bias = bias.wrapping_add(k);
                for (t, c) in &mut self.parts {
                    if cx.node(*t).op != OpCode::Mul {
                        *c = 0;
                    }
                }
                changed = true;
            }
        }
        if !changed {
            return Ok(None);
        }
        self.parts.extend_from_slice(&self.scaled);
        self.scaled.clear();
        if cancel_parts(&mut self.parts, mask, work).is_none() {
            return Ok(None);
        }
        let mut out = cx.mk_const_u64(w, bias & mask)?;
        for &(t, k) in &self.parts {
            let km = k & mask;
            if km == 0 {
                continue;
            }
            let tw = cx.wid(t);
            let tw_node = match tw.cmp(&w) {
                core::cmp::Ordering::Less => cx.c_zext(t, w)?,
                core::cmp::Ordering::Greater => cx.c_extract(t, 0, w)?,
                core::cmp::Ordering::Equal => t,
            };
            let term = if km == 1 {
                tw_node
            } else if km.is_power_of_two() {
                let sc = cx.mk_const_u64(w, u64::from(km.trailing_zeros()))?;
                cx.c_bin(BinOp::Shl, tw_node, sc)?
            } else {
                let c = cx.mk_const_u64(w, km)?;
                cx.c_bin(BinOp::Mul, tw_node, c)?
            };
            out = cx.c_bin(BinOp::Add, out, term)?;
        }
        Ok(Some(out))
    }

    /// Simplify the first additive layer below a compared bitwise expression,
    /// stopping there even when its operands hide a much larger arithmetic DAG.
    /// Only the shallow shell is rebuilt; its original gates retain their polarity.
    fn terminal(
        &mut self,
        cx: &mut Context,
        i: u32,
        depth: u8,
        work: &mut Work,
    ) -> Result<u32, Error> {
        if work.take(1).is_none() {
            return Ok(i);
        }
        let n = cx.node(i);
        match n.op {
            OpCode::Add | OpCode::Sub => Ok(self.collapse(cx, i, true, work)?.unwrap_or(i)),
            OpCode::Not | OpCode::And | OpCode::Or | OpCode::Xor if depth > 0 => {
                let mut kids = [0; 3];
                let mut changed = false;
                for (k, x) in n.children().enumerate() {
                    kids[k] = self.terminal(cx, x, depth - 1, work)?;
                    changed |= kids[k] != x;
                }
                if changed { cx.rebuild(i, kids) } else { Ok(i) }
            }
            _ => Ok(i),
        }
    }

    /// Descend through a shallow Boolean shell (`Not`/`And`/`Or`) to simplify terminal
    /// bitwise comparisons, including queries wrapped in conjunctions with assumptions.
    fn terminal_root(
        &mut self,
        cx: &mut Context,
        i: u32,
        depth: u8,
        work: &mut Work,
    ) -> Result<u32, Error> {
        if work.take(1).is_none() {
            return Ok(i);
        }
        let n = cx.node(i);
        if matches!(n.op, OpCode::Eq | OpCode::Ne)
            && cx.is_const(n.b)
            && matches!(
                cx.node(n.a).op,
                OpCode::Not | OpCode::And | OpCode::Or | OpCode::Xor
            )
        {
            let out = self.terminal(cx, n.a, 4, work)?;
            return if out != n.a {
                cx.rebuild(i, [out, n.b, 0])
            } else {
                Ok(i)
            };
        }
        if depth > 0 && n.width == 1 && matches!(n.op, OpCode::Not | OpCode::And | OpCode::Or) {
            let mut kids = [0; 3];
            let mut changed = false;
            for (k, x) in n.children().enumerate() {
                kids[k] = self.terminal_root(cx, x, depth - 1, work)?;
                changed |= kids[k] != x;
            }
            if changed {
                return cx.rebuild(i, kids);
            }
        }
        Ok(i)
    }
}

pub(super) fn reduce(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
    order: &[u32],
) -> Result<Option<u32>, Stop> {
    if !(16..=32768).contains(&order.len()) || r.mba.swept.contains_key(&root) {
        return Ok(None);
    }
    // When several product sums are present, simplify them together. Reducing
    // just a compared arm can leave other multiples of the same sum hidden
    // inside shifts and truncations (including the shift amount itself).
    let scan = order.len() as u64;
    let budget = (r.meter.left_in(|b| b.pass_work) / 4).min(1 << 18);
    if budget <= 4 * scan {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, scan)?;
    let mut left = budget - scan;
    let prod = |id| {
        let m = cx.node(id);
        m.op == OpCode::Mul && !cx.is_const(m.a) && !cx.is_const(m.b)
    };
    if order.iter().filter(|&&i| prod(i)).take(2).count() == 2 {
        r.meter.charge(Counter::PassWork, 3 * scan)?;
        left -= 3 * scan;
        let mut work = Work::new(left);
        let mut sums = Sums::default();
        let out = rewrite_sums(r, cx, order, |r, cx, i| {
            if work.left == 0 {
                return Ok(None);
            }
            r.build(cx, |cx| sums.collapse(cx, i, false, &mut work))
        })?;
        r.meter.charge(Counter::PassWork, left - work.left)?;
        left = work.left;
        if let Some(e) = out.get(root) {
            r.meter.charge(Counter::PassWork, scan)?;
            left = left.saturating_sub(scan);
            if matches!(
                cx.dag_size(&[cx.handle(e)], order.len() as u32 - 1)
                    .map_err(Stop::Error)?,
                crate::expr::Bounded::Exact(_)
            ) {
                return Ok(Some(e));
            }
        }
    }
    // Without a whole-DAG reduction, read the terminal bitwise comparisons (including
    // under shallow `Not`/`And`/`Or` wrappers). Each operand can be constant even with
    // entirely unrelated weights.
    let n = cx.node(root);
    if n.width == 1
        && matches!(
            n.op,
            OpCode::Eq | OpCode::Ne | OpCode::Not | OpCode::And | OpCode::Or
        )
    {
        let allowance = (left / 4).min(8192);
        let mut work = Work::new(allowance);
        let e = r.build(cx, |cx| {
            Sums::default().terminal_root(cx, root, 4, &mut work)
        })?;
        let used = allowance - work.left;
        r.meter.charge(Counter::PassWork, used)?;
        left -= used;
        if e != root && left >= scan {
            r.meter.charge(Counter::PassWork, scan)?;
            if matches!(
                cx.dag_size(&[cx.handle(e)], order.len() as u32 - 1)
                    .map_err(Stop::Error)?,
                crate::expr::Bounded::Exact(_)
            ) {
                return Ok(Some(e));
            }
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ParseOptions, Width};

    #[test]
    fn scaled_cofactor_and_unrelated_summand() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W8);
        let mut sums = Sums::default();
        for k in [3, 22, 219] {
            let s = format!("f*((x ^ y) & z)*{k} + g + (f*{k})*((x ^ y) & ~z) - (x ^ y)*(f*{k})");
            let e = cx.parse(&s, &opt).unwrap();
            let g = cx.parse("g", &opt).unwrap();
            let i = cx.id(e).unwrap();
            assert_eq!(
                sums.collapse(&mut cx, i, false, &mut Work::new(4096))
                    .unwrap(),
                Some(cx.id(g).unwrap())
            );
        }
    }

    #[test]
    fn terminal_gate_retains_polarity_and_shared_factor() {
        for (w, a, b, k, mask) in [
            (Width::W8, 3u64, 7, 2, 0x53),
            (Width::W16, 22, 18, 11, 0x9441),
            (Width::W32, 219, 99, 17, 0x8ff14),
        ] {
            let mut cx = Context::new();
            let opt = ParseOptions::width(w);
            // OR - AND + XNOR = -1. The partition of x at `mask` adds
            // zero, but its unrelated weight prevents single-scale grouping.
            let e = cx
                .parse(
                    &format!(
                        "~((x | y)*(t*{a}) - (x & y)*{a}*t + (~(x ^ y)*t)*{a}) & \
                 ~((x | y)*{b} - (x & y)*{b} + ~(x ^ y)*{b} + \
                   (x & {mask})*{k} + (x & ~{mask})*{k} - x*{k})"
                    ),
                    &opt,
                )
                .unwrap();
            let minus_a = a.wrapping_neg() & ((1 << w.bits()) - 1);
            let expected = cx
                .parse(&format!("~(t*{minus_a}) & {}", b - 1), &opt)
                .unwrap();
            let i = cx.id(e).unwrap();
            let got = Sums::default()
                .terminal(&mut cx, i, 4, &mut Work::new(4096))
                .unwrap();
            assert_eq!(got, cx.id(expected).unwrap());
        }
    }

    #[test]
    fn mask_classes_cannot_cancel_across_positions() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W8);
        let ids = ["x & 1", "x & 2"].map(|s| {
            let x = cx.parse(s, &opt).unwrap();
            cx.id(x).unwrap()
        });
        // 2*(x&1) - (x&2) agrees at both uniform-word corners.
        let mut table = Table::default();
        assert_eq!(
            table.constant(
                &cx,
                &[(ids[0], 2), (ids[1], u64::MAX)],
                8,
                &mut Work::new(1024)
            ),
            None
        );
    }

    #[test]
    fn collapses_multiple_shared_factors_and_mixed_weight_remainder() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W16);
        let mut sums = Sums::default();
        // Two independent shared product factors (f and g) plus a mixed-weight Boolean
        // remainder (weights 5 and 3) alongside an unrelated summand `h`.
        let src = "f*(x & y)*3 + f*(x & ~y)*3 - f*x*3 \
                 + g*(a | b)*2 - g*(a & b)*2 - g*(a ^ b)*2 \
                 + (x | y)*5 - (x & y)*5 + ~(x ^ y)*5 \
                 + (x & 0x53)*3 + (x & ~0x53)*3 - x*3 + h";
        let e = cx.parse(src, &opt).unwrap();
        let want = cx.parse("h - 5", &opt).unwrap();
        let eid = cx.id(e).unwrap();
        let got = sums
            .collapse(&mut cx, eid, false, &mut Work::new(16384))
            .unwrap();
        assert_eq!(got, Some(cx.id(want).unwrap()));

        // Irreducible mixed weights ({3, -2, -1, -1, -3}) alongside a shared factor `f`:
        // no equal-magnitude subset is constant on its own; only `table.constant` on the
        // non-product remainder proves it zero.
        let mixed = "f*(x | y)*3 - f*(x & y)*3 + f*~(x ^ y)*3 \
                   + (x | y)*3 - (x ^ y)*2 - (x & ~y) - (~x & y) - (x & y)*3";
        let e2 = cx.parse(mixed, &opt).unwrap();
        let want2 = cx.parse("f * 65533", &opt).unwrap();
        let e2id = cx.id(e2).unwrap();
        let got2 = sums
            .collapse(&mut cx, e2id, false, &mut Work::new(16384))
            .unwrap();
        assert_eq!(got2, Some(cx.id(want2).unwrap()));
    }

    #[test]
    fn conjunction_wrapped_terminal_gate_simplifies_under_96_nodes() {
        use crate::engine::{Budget, Engine, Run, Strategy};
        use crate::mba::MbaConfig;

        let strategy =
            Strategy::deobfuscate().with_mba(MbaConfig::default().with_opaque_sweep(true));
        let engine = Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap();
        // Wrapped in `!(eq & guard)` with fewer than 96 nodes: terminal_root descends
        // through the Not/And shell to prove the masked cofactor gate constant.
        let src = "let a = x:16 * x + 3; let b = y:16 ^ 0x1234; \
                   let s = (a | b)*7 - (a & b)*7 + ~(a ^ b)*7 + (a & 0x53)*11 + (a & ~0x53)*11 - a*11; \
                   ~((~s == 6) & (z:16 == 9))";
        let mut cx = Context::new();
        let root = cx.parse(src, &ParseOptions::width(Width::W16)).unwrap();
        let out = engine
            .run(
                &mut cx,
                &[root],
                Run::default().with_per_call(Budget::fuel(1 << 14)),
            )
            .unwrap();
        // `s = -7`, so `~s = 6`, so `~s == 6` is true, leaving `z != 9`.
        let want = cx
            .parse("z:16 != 9", &ParseOptions::width(Width::W16))
            .unwrap();
        assert_eq!(out.roots[0].expr, want);
    }

    #[test]
    fn collapses_expanded_complements_affine_factors_and_disjoint_shifts() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W16);
        let mut sums = Sums::default();

        // Expanded bitwise complement `x * (-C) - 1 == ~(x * C)` alongside affine-shifted
        // factor `(f + 5)` and 3-factor products.
        let src = "let %0 = x * 7; let %1 = x * 65529 - 1; \
                   (f + 5) * (%0 | y) * 3 - (f + 5) * (%0 & y) * 3 + (f + 5) * ~(%1 ^ ~y) * 3";
        let e = cx.parse(src, &opt).unwrap();
        let want = cx.parse("f * 65533 + 65521", &opt).unwrap();
        let eid = cx.id(e).unwrap();
        let got = sums
            .collapse(&mut cx, eid, false, &mut Work::new(16384))
            .unwrap();
        assert!(got.is_some());
        let got_expr = cx.handle(got.unwrap());
        for (xv, yv, fv) in [(0u64, 0u64, 0u64), (17, 42, 9), (0xffff, 0x1234, 0x7777)] {
            let env = [
                ("x".into(), crate::BitVec::from_u64(Width::W16, xv).unwrap()),
                ("y".into(), crate::BitVec::from_u64(Width::W16, yv).unwrap()),
                ("f".into(), crate::BitVec::from_u64(Width::W16, fv).unwrap()),
            ];
            let vals = cx.eval(&[got_expr, want], &env[..]).unwrap();
            assert_eq!(vals[0], vals[1]);
        }

        // Known-zero disjoint shifted halves (`(x << 6) & (x >>u 10) == 0`) inside a cofactor.
        let disjoint = "let %0 = x << 6; let %1 = x >>u 10; \
                        f * (%0 | %1) * 5 - f * (%0 ^ %1) * 5 + g";
        let e2 = cx.parse(disjoint, &opt).unwrap();
        let want2 = cx.parse("g", &opt).unwrap();
        let e2id = cx.id(e2).unwrap();
        let got2 = sums
            .collapse(&mut cx, e2id, false, &mut Work::new(16384))
            .unwrap();
        assert_eq!(got2, Some(cx.id(want2).unwrap()));
    }
}
