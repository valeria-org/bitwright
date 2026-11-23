//! Collect common multiplicands before proving that the remaining weighted sum of
//! bitwise functions is constant. The proof is local: no fact about a multiplicand,
//! or the arithmetic hidden underneath a bitwise function, is needed.

use super::opaque_predicate::{Work, rewrite_sums, terms};
use super::{Counter, Runner, Stop};
use crate::expr::{Context, Node, OpCode};
use crate::hash::IdMap;
use crate::{BinOp, Error};

const MAX_TERMS: usize = 48;
const ATOMS: [u64; 6] = [
    0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
    0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000,
];

#[derive(Default)]
struct Table {
    code: Vec<Node>,
    places: IdMap<u32, u32>,
    terms: Vec<(u32, u64)>,
    atoms: usize,
}

impl Table {
    // Read just the bitwise DAG. A non-bitwise node is one free word, however
    // many inputs it really has. Hash-consing gives all its occurrences one column.
    fn place(&mut self, cx: &Context, i: u32, depth: u8, work: &mut Work) -> Option<u32> {
        work.take(1)?;
        if let Some(&p) = self.places.get(&i) { return Some(p); }
        if depth == 0 || self.code.len() >= 256 { return None; }
        let mut n = cx.node(i);
        match n.op {
            OpCode::Const => (),
            OpCode::Not => n.a = self.place(cx, n.a, depth - 1, work)?,
            OpCode::And | OpCode::Or | OpCode::Xor => {
                n.a = self.place(cx, n.a, depth - 1, work)?;
                n.b = self.place(cx, n.b, depth - 1, work)?;
            }
            _ => {
                if self.atoms == ATOMS.len() { return None; }
                n.op = OpCode::Sym;
                n.a = self.atoms as u32;
                self.atoms += 1;
            }
        }
        if self.code.len() == 256 { return None; }
        let p = self.code.len() as u32;
        self.code.push(n);
        self.places.insert(i, p);
        Some(p)
    }

    /// At each bit position j the sum contributes 2^j times the weighted count of
    /// true terms. Check that count on *every* Boolean assignment, modulo 2^(w-j).
    /// Positions where all bitwise constants have identical bits share a table;
    /// checking its lowest j implies equality at all the others. Testing aggregate
    /// all-zero/all-ones words instead would unsoundly cancel across positions.
    fn constant(&mut self, cx: &Context, parts: &[(u32, u64)], w: u16, work: &mut Work) -> Option<u64> {
        self.code.clear();
        self.places.clear();
        self.terms.clear();
        self.atoms = 0;
        for &(i, k) in parts {
            let p = self.place(cx, i, 48, work)?;
            self.terms.push((p, k));
        }
        let rows = 1usize << self.atoms;
        let all = u64::MAX >> (64 - rows);
        let mask = u64::MAX >> (64 - w);
        let mut remaining = mask;
        let mut result = 0u64;
        let mut values = [0u64; 256];
        while remaining != 0 {
            work.take(self.code.len() as u64)?;
            let j = remaining.trailing_zeros();
            let mut class = remaining;
            for (p, n) in self.code.iter().enumerate() {
                values[p] = match n.op {
                    OpCode::Const => {
                        let k = u64::from(n.a) | (u64::from(n.b) << 32);
                        if k & (1 << j) == 0 { class &= !k; 0 } else { class &= k; all }
                    }
                    OpCode::Sym => ATOMS[n.a as usize],
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
            if counts[1..rows].iter().any(|&v| (v ^ counts[0]) & (mask >> j) != 0) {
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
struct Sums {
    parts: Vec<(u32, u64)>,
    products: Vec<Option<([u32; 2], u64)>>,
    group: Vec<(u32, u64)>,
    known: Vec<Kernel>,
    table: Table,
}

impl Sums {
    fn value(&mut self, cx: &Context, w: u16, work: &mut Work) -> Option<u64> {
        let mask = u64::MAX >> (64 - w);
        work.take((self.group.len() * 6) as u64)?;
        self.group.sort_unstable();
        for known in &self.known {
            if known.terms.len() != self.group.len() { continue; }
            let k = self.group[known.pivot].1 & mask;
            if u32::from(known.bits) + k.trailing_zeros() >= u32::from(w) {
                work.take(self.group.len() as u64)?;
                if known.terms.iter().zip(&self.group).all(|(&(a, v), &(b, t))|
                    a == b && (v.wrapping_mul(k) ^ t) & mask == 0) {
                    return Some(k.wrapping_mul(known.value) & mask);
                }
            }
        }
        let (pivot, &(_, k)) = self.group.iter().enumerate().min_by_key(|(_, p)| (p.1 & mask).trailing_zeros())?;
        let shift = (k & mask).trailing_zeros();
        if shift >= u32::from(w) { return Some(0); }
        let bits = w - shift as u16;
        let odd = k >> shift;
        let mut inv = odd; // inverse mod 8; Newton doubles correct bits each iteration.
        for _ in 0..5 { inv = inv.wrapping_mul(2u64.wrapping_sub(odd.wrapping_mul(inv))); }
        let low = mask >> shift;
        for (_, c) in &mut self.group { *c = (*c >> shift).wrapping_mul(inv) & low; }
        let value = self.table.constant(cx, &self.group, bits, work)?;
        if self.known.len() < 32 {
            self.known.push(Kernel { terms: self.group.clone(), pivot, bits, value });
        }
        Some(value.wrapping_mul(k) & mask)
    }

    fn collapse(&mut self, cx: &mut Context, i: u32, work: &mut Work) -> Result<Option<u32>, Error> {
        let w = cx.wid(i);
        if w > 64 { return Ok(None); }
        let mut bias = 0;
        self.parts.clear();
        if terms(cx, i, 1, &mut bias, &mut self.parts, 64, true, work).is_none()
            || !(2..=MAX_TERMS).contains(&self.parts.len()) { return Ok(None); }
        let mask = u64::MAX >> (64 - w);
        let magnitude = |k: u64| (k & mask).min(k.wrapping_neg() & mask);
        // First try a genuine common multiplicand. Keep unrelated summands: they
        // neither constrain the cofactor nor need to be bitwise themselves.
        self.products.clear();
        let mut best = (0usize, 0u32);
        for &(t, k) in &self.parts {
            let p = if cx.node(t).op == OpCode::Mul {
                if work.take(32).is_none() { return Ok(None); }
                super::super::linear::scaled_factors(cx, t).and_then(|(v, fs)| match fs.as_slice() {
                    &[a, b] => Some(([a, b], k.wrapping_mul(v.limbs()[0]))),
                    _ => None,
                })
            } else { None };
            self.products.push(p);
        }
        for &(pair, _) in self.products.iter().flatten() {
            for f in pair {
                if work.take(self.products.len() as u64).is_none() { return Ok(None); }
                let n = self.products.iter().flatten().filter(|(p, _)| p.contains(&f)).count();
                if n > best.0 { best = (n, f); }
            }
        }
        let mut scaled = None;
        if best.0 >= 2 {
            let f = best.1;
            self.group.clear();
            for &([a, b], k) in self.products.iter().flatten() {
                if a == f || b == f { self.group.push((if a == f { b } else { a }, k)); }
            }
            if let Some(k) = self.value(cx, w, work) {
                for ((_, c), p) in self.parts.iter_mut().zip(&self.products) {
                    if p.is_some_and(|(pair, _)| pair.contains(&f)) { *c = 0; }
                }
                scaled = Some((f, k));
            }
        }
        // The scalar alone may be what a class shares. Sorting groups k and -k
        // together, independently of association and of any intervening summands.
        if work.take((6 * self.parts.len()) as u64).is_none() { return Ok(None); }
        self.parts.sort_unstable_by_key(|&(t, k)| (magnitude(k), t));
        let mut changed = scaled.is_some();
        let mut lo = 0;
        while lo < self.parts.len() {
            let k = magnitude(self.parts[lo].1);
            let hi = lo + self.parts[lo..].partition_point(|&(_, c)| magnitude(c) == k);
            if k != 0 && hi - lo > 1 {
                self.group.clear();
                self.group.extend_from_slice(&self.parts[lo..hi]);
                if let Some(v) = self.value(cx, w, work) {
                    bias = bias.wrapping_add(v);
                    self.parts[lo..hi].fill((0, 0));
                    changed = true;
                }
            }
            lo = hi;
        }
        if !changed { return Ok(None); }
        let mut out = cx.mk_const_u64(w, bias & mask)?;
        for (t, k) in self.parts.iter().copied().chain(scaled) {
            if k & mask == 0 { continue; }
            let c = cx.mk_const_u64(w, k & mask)?;
            let term = cx.c_bin(BinOp::Mul, t, c)?;
            out = cx.c_bin(BinOp::Add, out, term)?;
        }
        Ok(Some(out))
    }
}

pub(super) fn reduce(r: &mut Runner<'_, '_>, cx: &mut Context, root: u32, order: &[u32]) -> Result<Option<u32>, Stop> {
    if !(96..=4096).contains(&order.len()) || r.mba.swept.contains_key(&root) { return Ok(None); }
    // One isolated sum is already handled by the normal-form passes. Look for
    // several sums of products before paying for a whole-DAG traversal and memo.
    let scan = order.len() as u64;
    let budget = (r.meter.left_in(|b| b.pass_work) / 4).min(1 << 17);
    if budget <= 4 * scan { return Ok(None); }
    r.meter.charge(Counter::PassWork, scan)?;
    if order.iter().filter(|&&i| {
        let n = cx.node(i);
        matches!(n.op, OpCode::Add | OpCode::Sub) && cx.node(n.a).op == OpCode::Mul && cx.node(n.b).op == OpCode::Mul
    }).take(4).count() < 4 { return Ok(None); }
    r.meter.charge(Counter::PassWork, 3 * scan)?;
    let budget = budget - 4 * scan;
    let mut work = Work::new(budget);
    let mut sums = Sums::default();
    let out = rewrite_sums(r, cx, order, |r, cx, i| {
        if work.left == 0 { return Ok(None); }
        r.build(cx, |cx| sums.collapse(cx, i, &mut work))
    })?;
    r.meter.charge(Counter::PassWork, budget - work.left)?;
    let Some(out) = out.get(root) else { return Ok(None) };
    let cap = order.len() as u32 - 1;
    r.meter.charge(Counter::PassWork, scan)?;
    Ok(matches!(cx.dag_size(&[cx.handle(out)], cap).map_err(Stop::Error)?, crate::expr::Bounded::Exact(_))
        .then_some(out))
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
            assert_eq!(sums.collapse(&mut cx, i, &mut Work::new(4096)).unwrap(), Some(cx.id(g).unwrap()));
        }
    }

    #[test]
    fn mask_classes_cannot_cancel_across_positions() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W8);
        let ids = ["x & 1", "x & 2"].map(|s| { let x = cx.parse(s, &opt).unwrap(); cx.id(x).unwrap() });
        // 2*(x&1) - (x&2) agrees at both uniform-word corners.
        let mut table = Table::default();
        assert_eq!(table.constant(&cx, &[(ids[0], 2), (ids[1], u64::MAX)], 8, &mut Work::new(1024)), None);
    }
}
