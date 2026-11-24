//! Collect common multiplicands before proving that the remaining weighted sum of
//! bitwise functions is constant. The proof is local: no fact about a multiplicand,
//! or the arithmetic hidden underneath a bitwise function, is needed.

use super::opaque_predicate::{Work, cancel_parts, rewrite_sums, terms};
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
pub(super) struct Sums {
    parts: Vec<(u32, u64)>,
    products: Vec<Option<([u32; 2], u64)>>,
    group: Vec<(u32, u64)>,
    scaled: Vec<(u32, u64)>,
    rest: Vec<(u32, u64)>,
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
            self.known.push(Kernel { terms: self.group.clone(), pivot, bits, value });
        }
        Some(value.wrapping_mul(k) & mask)
    }

    pub(super) fn collapse(&mut self, cx: &mut Context, i: u32, _terminal: bool, work: &mut Work) -> Result<Option<u32>, Error> {
        let w = cx.wid(i);
        if w > 64 { return Ok(None); }
        let mask = u64::MAX >> (64 - w);
        let mut bias = 0;
        self.parts.clear();
        if terms(cx, i, 1, &mut bias, &mut self.parts, 64, true, work).is_none()
            || self.parts.len() < 2
        {
            return Ok(None);
        }
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
            let p = if cx.node(t).op == OpCode::Mul {
                if work.take(32).is_none() { return Ok(None); }
                super::super::linear::scaled_factors(cx, t).and_then(|(v, fs)| match fs.as_slice() {
                    &[a, b] => Some(([a, b], k.wrapping_mul(v.limbs()[0]))),
                    _ => None,
                })
            } else { None };
            self.products.push(p);
        }
        self.scaled.clear();
        for _ in 0..8 {
            let mut best = (0usize, 0u32);
            for &(pair, _) in self.products.iter().flatten() {
                for f in pair {
                    if work.take(self.products.len() as u64).is_none() { return Ok(None); }
                    let n = self.products.iter().flatten().filter(|(p, _)| p.contains(&f)).count();
                    if n > best.0 { best = (n, f); }
                }
            }
            if best.0 < 2 { break; }
            let f = best.1;
            self.group.clear();
            for &([a, b], k) in self.products.iter().flatten() {
                if a == f || b == f { self.group.push((if a == f { b } else { a }, k)); }
            }
            let Some(k) = self.value(cx, w, work) else { break };
            for ((_, c), p) in self.parts.iter_mut().zip(&mut self.products) {
                if p.is_some_and(|(pair, _)| pair.contains(&f)) {
                    *c = 0;
                    *p = None;
                }
            }
            self.scaled.push((f, k));
            changed = true;
        }
        // First check equal-magnitude groups through the normalized `Kernel` cache:
        // repeated sums with different scalars reuse one exact proof in O(terms).
        if work.take((6 * self.parts.len()) as u64).is_none() { return Ok(None); }
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
                    if cx.node(*t).op != OpCode::Mul { *c = 0; }
                }
                changed = true;
            }
        }
        if !changed { return Ok(None); }
        let mut out = cx.mk_const_u64(w, bias & mask)?;
        for &(t, k) in self.parts.iter().chain(&self.scaled) {
            if k & mask == 0 { continue; }
            let c = cx.mk_const_u64(w, k & mask)?;
            let term = cx.c_bin(BinOp::Mul, t, c)?;
            out = cx.c_bin(BinOp::Add, out, term)?;
        }
        Ok(Some(out))
    }

    /// Simplify the first additive layer below a compared bitwise expression,
    /// stopping there even when its operands hide a much larger arithmetic DAG.
    /// Only the shallow shell is rebuilt; its original gates retain their polarity.
    fn terminal(&mut self, cx: &mut Context, i: u32, depth: u8, work: &mut Work) -> Result<u32, Error> {
        if work.take(1).is_none() { return Ok(i); }
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
    fn terminal_root(&mut self, cx: &mut Context, i: u32, depth: u8, work: &mut Work) -> Result<u32, Error> {
        if work.take(1).is_none() { return Ok(i); }
        let n = cx.node(i);
        if matches!(n.op, OpCode::Eq | OpCode::Ne)
            && cx.is_const(n.b)
            && matches!(cx.node(n.a).op, OpCode::Not | OpCode::And | OpCode::Or | OpCode::Xor)
        {
            let out = self.terminal(cx, n.a, 4, work)?;
            return if out != n.a { cx.rebuild(i, [out, n.b, 0]) } else { Ok(i) };
        }
        if depth > 0 && n.width == 1 && matches!(n.op, OpCode::Not | OpCode::And | OpCode::Or) {
            let mut kids = [0; 3];
            let mut changed = false;
            for (k, x) in n.children().enumerate() {
                kids[k] = self.terminal_root(cx, x, depth - 1, work)?;
                changed |= kids[k] != x;
            }
            if changed { return cx.rebuild(i, kids); }
        }
        Ok(i)
    }
}

pub(super) fn reduce(r: &mut Runner<'_, '_>, cx: &mut Context, root: u32, order: &[u32]) -> Result<Option<u32>, Stop> {
    if !(16..=4096).contains(&order.len()) || r.mba.swept.contains_key(&root) { return Ok(None); }
    // When several product sums are present, simplify them together. Reducing
    // just a compared arm can leave other multiples of the same sum hidden
    // inside shifts and truncations (including the shift amount itself).
    let scan = order.len() as u64;
    let budget = (r.meter.left_in(|b| b.pass_work) / 4).min(1 << 17);
    if budget <= 4 * scan { return Ok(None); }
    r.meter.charge(Counter::PassWork, scan)?;
    let mut left = budget - scan;
    if order.iter().any(|&i| {
        let n = cx.node(i);
        let prod = |id| {
            let m = cx.node(id);
            m.op == OpCode::Mul && !cx.is_const(m.a) && !cx.is_const(m.b)
        };
        matches!(n.op, OpCode::Add | OpCode::Sub) && prod(n.a) && prod(n.b)
    }) {
        r.meter.charge(Counter::PassWork, 3 * scan)?;
        left -= 3 * scan;
        let mut work = Work::new(left);
        let mut sums = Sums::default();
        let out = rewrite_sums(r, cx, order, |r, cx, i| {
            if work.left == 0 { return Ok(None); }
            r.build(cx, |cx| sums.collapse(cx, i, false, &mut work))
        })?;
        r.meter.charge(Counter::PassWork, left - work.left)?;
        left = work.left;
        if let Some(e) = out.get(root) {
            r.meter.charge(Counter::PassWork, scan)?;
            left = left.saturating_sub(scan);
            if matches!(cx.dag_size(&[cx.handle(e)], order.len() as u32 - 1).map_err(Stop::Error)?,
                crate::expr::Bounded::Exact(_)) { return Ok(Some(e)); }
        }
    }
    // Without a whole-DAG reduction, read the terminal bitwise comparisons (including
    // under shallow `Not`/`And`/`Or` wrappers). Each operand can be constant even with
    // entirely unrelated weights.
    let n = cx.node(root);
    if n.width == 1 && matches!(n.op, OpCode::Eq | OpCode::Ne | OpCode::Not | OpCode::And | OpCode::Or) {
        let allowance = (left / 4).min(8192);
        let mut work = Work::new(allowance);
        let e = r.build(cx, |cx| Sums::default().terminal_root(cx, root, 4, &mut work))?;
        let used = allowance - work.left;
        r.meter.charge(Counter::PassWork, used)?;
        left -= used;
        if e != root && left >= scan {
            r.meter.charge(Counter::PassWork, scan)?;
            if matches!(cx.dag_size(&[cx.handle(e)], order.len() as u32 - 1).map_err(Stop::Error)?,
                crate::expr::Bounded::Exact(_)) { return Ok(Some(e)); }
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
            assert_eq!(sums.collapse(&mut cx, i, false, &mut Work::new(4096)).unwrap(), Some(cx.id(g).unwrap()));
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
            let e = cx.parse(&format!(
                "~((x | y)*(t*{a}) - (x & y)*{a}*t + (~(x ^ y)*t)*{a}) & \
                 ~((x | y)*{b} - (x & y)*{b} + ~(x ^ y)*{b} + \
                   (x & {mask})*{k} + (x & ~{mask})*{k} - x*{k})"
            ), &opt).unwrap();
            let minus_a = a.wrapping_neg() & ((1 << w.bits()) - 1);
            let expected = cx.parse(&format!("~(t*{minus_a}) & {}", b - 1), &opt).unwrap();
            let i = cx.id(e).unwrap();
            let got = Sums::default().terminal(&mut cx, i, 4, &mut Work::new(4096)).unwrap();
            assert_eq!(got, cx.id(expected).unwrap());
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
        let got = sums.collapse(&mut cx, eid, false, &mut Work::new(16384)).unwrap();
        assert_eq!(got, Some(cx.id(want).unwrap()));

        // Irreducible mixed weights ({3, -2, -1, -1, -3}) alongside a shared factor `f`:
        // no equal-magnitude subset is constant on its own; only `table.constant` on the
        // non-product remainder proves it zero.
        let mixed = "f*(x | y)*3 - f*(x & y)*3 + f*~(x ^ y)*3 \
                   + (x | y)*3 - (x ^ y)*2 - (x & ~y) - (~x & y) - (x & y)*3";
        let e2 = cx.parse(mixed, &opt).unwrap();
        let want2 = cx.parse("f * 65533", &opt).unwrap();
        let e2id = cx.id(e2).unwrap();
        let got2 = sums.collapse(&mut cx, e2id, false, &mut Work::new(16384)).unwrap();
        assert_eq!(got2, Some(cx.id(want2).unwrap()));
    }

    #[test]
    fn conjunction_wrapped_terminal_gate_simplifies_under_96_nodes() {
        use crate::engine::{Budget, Engine, Run, Strategy};
        use crate::mba::MbaConfig;

        let strategy = Strategy::deobfuscate().with_mba(MbaConfig::default().with_opaque_sweep(true));
        let engine = Engine::builder().builtin().strategy(strategy).build().unwrap();
        // Wrapped in `!(eq & guard)` with fewer than 96 nodes: terminal_root descends
        // through the Not/And shell to prove the masked cofactor gate constant.
        let src = "let a = x:16 * x + 3; let b = y:16 ^ 0x1234; \
                   let s = (a | b)*7 - (a & b)*7 + ~(a ^ b)*7 + (a & 0x53)*11 + (a & ~0x53)*11 - a*11; \
                   ~((~s == 6) & (z:16 == 9))";
        let mut cx = Context::new();
        let root = cx.parse(src, &ParseOptions::width(Width::W16)).unwrap();
        let out = engine.run(&mut cx, &[root], Run::default().with_per_call(Budget::fuel(1 << 14))).unwrap();
        // `s = -7`, so `~s = 6`, so `~s == 6` is true, leaving `z != 9`.
        let want = cx.parse("z:16 != 9", &ParseOptions::width(Width::W16)).unwrap();
        assert_eq!(out.roots[0].expr, want);
    }
}
