//! Bounded enumerative synthesis: the smallest expressions over at most three atoms, keyed by
//! their values at a fixed set of probe points.
//!
//! Expressions are built from the atoms `a`, `b`, `c` and the constant 1 with `+ − · & | ^ ~`
//! and negation, bottom-up by size (operators and leaves of the tree), and an expression is
//! kept only when no smaller one has the same values at every probe; among those of one size,
//! the one with the fewest distinct subexpressions (as a DAG, like the solver's costs). These
//! operators never
//! carry information downward, so the low `W` bits of a value depend only on the low `W` bits
//! of the atoms: the table is built once at 64 bits and serves every width, narrower ones by
//! truncating the values, wider ones by their low 64 bits.
//!
//! Agreement at the probes is not equality: a hit is a candidate, which a certificate proves
//! (or refutes) before it is used.

use std::collections::HashMap;
use std::sync::OnceLock;

use crate::mba::expr::{MOp, MbaExpr};
use crate::{BitVec, Width};

/// The largest expression kept, in nodes of the tree (operators and leaves).
pub(crate) const MAX_SIZE: u8 = 7;

/// Probe points.
pub(crate) const PROBES: usize = 24;

/// The atoms' values at probe point `k` (the first three coordinates are `a`, `b`, `c`): the
/// eight corners of 0 and all-ones, then small and seeded random values.
pub(crate) fn probe(k: usize) -> [u64; 3] {
    if k < 8 {
        return [0, 1, 2].map(|j| if k >> j & 1 == 1 { u64::MAX } else { 0 });
    }
    const SMALL: [[u64; 3]; 4] = [[1, 2, 3], [3, 1, 2], [2, 3, 1], [1, 1, 2]];
    if k < 12 {
        return SMALL[k - 8];
    }
    let mut h = 0x243f_6a88_85a3_08d3u64 ^ (k as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
    [0, 1, 2].map(|_| {
        h ^= h >> 31;
        h = h.wrapping_mul(0xbf58_476d_1ce4_e5b9);
        h ^= h >> 29;
        h
    })
}

/// An operator of the table's expressions.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Op {
    Var(u8),
    One,
    Not,
    Neg,
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
}

impl Op {
    pub(crate) fn arity(self) -> usize {
        match self {
            Op::Var(_) | Op::One => 0,
            Op::Not | Op::Neg => 1,
            _ => 2,
        }
    }

    /// The operator as an [`MbaExpr`] one (`None` for the leaves).
    pub(crate) fn mop(self) -> Option<MOp> {
        Some(match self {
            Op::Not => MOp::Not,
            Op::Neg => MOp::Neg,
            Op::Add => MOp::Add,
            Op::Sub => MOp::Sub,
            Op::Mul => MOp::Mul,
            Op::And => MOp::And,
            Op::Or => MOp::Or,
            Op::Xor => MOp::Xor,
            Op::Var(_) | Op::One => return None,
        })
    }
}

/// An expression: an operator over earlier entries.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct Entry {
    pub(crate) op: Op,
    pub(crate) args: [u32; 2],
}

pub(crate) type Values = [u64; PROBES];

/// A hash of values at the probes truncated by `mask`. It only lays out the indexes: an entry
/// is found by its values, compared in full. Four short chains, so that one probe's
/// multiplication does not wait for the previous probe's.
fn fold(v: &Values, mask: u64) -> u64 {
    const K: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut h = [
        0x6a09_e667_f3bc_c908u64,
        0xbb67_ae85_84ca_a73b,
        0x3c6e_f372_fe94_f82b,
        0xa54f_f53a_5f1d_36f1,
    ];
    for x in v.chunks_exact(4) {
        for k in 0..4 {
            h[k] = (h[k].rotate_left(27) ^ (x[k] & mask)).wrapping_mul(K);
        }
    }
    crate::hash::mix64(h[0] ^ h[1].rotate_left(16) ^ h[2].rotate_left(32) ^ h[3].rotate_left(48))
}

/// Whether two value vectors agree at the bits of `mask`.
fn same(a: &Values, b: &Values, mask: u64) -> bool {
    a.iter().zip(b).all(|(x, y)| (x ^ y) & mask == 0)
}

/// The distinct entries an expression uses, itself included (at most [`MAX_SIZE`]).
#[derive(Copy, Clone, Debug, Default)]
struct Reach {
    len: u8,
    ids: [u32; MAX_SIZE as usize],
}

impl Reach {
    fn of(i: u32, parts: &[&Reach]) -> Option<Reach> {
        let mut r = Reach::default();
        for p in parts {
            for &x in &p.ids[..usize::from(p.len)] {
                r.insert(x)?;
            }
        }
        r.insert(i)?;
        Some(r)
    }

    fn insert(&mut self, x: u32) -> Option<()> {
        let n = usize::from(self.len);
        if self.ids[..n].contains(&x) {
            return Some(());
        }
        *self.ids.get_mut(n)? = x;
        self.len += 1;
        Some(())
    }
}

/// Entries by a hash of their values: open addressing with linear probing, a slot holding the
/// hash and the entry ([`FREE`] when empty). The values themselves stay with the caller, who
/// never adds an entry whose values the index already has: a lookup offers the entries whose
/// hash matches until one is taken.
struct Index {
    slots: Vec<(u64, u32)>,
    len: usize,
}

/// An empty slot of an [`Index`].
const FREE: u32 = u32::MAX;

impl Index {
    /// An index with room for `n` entries before it grows.
    fn with_capacity(n: usize) -> Index {
        Index {
            slots: vec![(0, FREE); (2 * n).next_power_of_two().max(16)],
            len: 0,
        }
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.len
    }

    /// The entry with hash `h` that `is` accepts.
    fn find(&self, h: u64, is: impl Fn(u32) -> bool) -> Option<u32> {
        let mask = self.slots.len() - 1;
        let mut at = h as usize & mask;
        loop {
            let (g, i) = self.slots[at];
            if i == FREE {
                return None;
            }
            if g == h && is(i) {
                return Some(i);
            }
            at = (at + 1) & mask;
        }
    }

    /// Adds entry `i` with hash `h`.
    fn insert(&mut self, h: u64, i: u32) {
        if 2 * (self.len + 1) > self.slots.len() {
            let old = core::mem::take(&mut self.slots);
            self.slots = vec![(0, FREE); 2 * old.len()];
            for (g, j) in old {
                if j != FREE {
                    self.place(g, j);
                }
            }
        }
        self.place(h, i);
        self.len += 1;
    }

    fn place(&mut self, h: u64, i: u32) {
        let mask = self.slots.len() - 1;
        let mut at = h as usize & mask;
        while self.slots[at].1 != FREE {
            at = (at + 1) & mask;
        }
        self.slots[at] = (h, i);
    }
}

/// The table: entries in order of size, each the first of its values at the probes.
pub(crate) struct Table {
    entries: Vec<Entry>,
    sizes: Vec<u8>,
    reach: Vec<Reach>,
    values: Vec<Values>,
    /// Per width below 64: the first entry of each value vector truncated to the width, built
    /// when the width is first asked for.
    narrow: [OnceLock<Index>; 64],
    /// At 64 bits and wider: the entry by its values.
    wide: Index,
}

fn apply(op: Op, x: &Values, y: &Values) -> Values {
    let mut out = [0u64; PROBES];
    for k in 0..PROBES {
        out[k] = match op {
            Op::Not => !x[k],
            Op::Neg => x[k].wrapping_neg(),
            Op::Add => x[k].wrapping_add(y[k]),
            Op::Sub => x[k].wrapping_sub(y[k]),
            Op::Mul => x[k].wrapping_mul(y[k]),
            Op::And => x[k] & y[k],
            Op::Or => x[k] | y[k],
            Op::Xor => x[k] ^ y[k],
            Op::Var(v) => probe(k)[usize::from(v)],
            Op::One => 1,
        };
    }
    out
}

impl Table {
    /// Every expression up to `max_size` nodes, the first of each value vector kept.
    pub(crate) fn build(max_size: u8) -> Table {
        let mut t = Table {
            entries: Vec::new(),
            sizes: Vec::new(),
            reach: Vec::new(),
            values: Vec::new(),
            narrow: [const { OnceLock::new() }; 64],
            wide: Index::with_capacity(1 << 15),
        };
        let zero = [0u64; PROBES];
        let mut by_size: Vec<Vec<u32>> = vec![Vec::new(); usize::from(max_size) + 1];
        let leaves = [Op::Var(0), Op::Var(1), Op::Var(2), Op::One];
        for op in leaves {
            let v = apply(op, &zero, &zero);
            if let Some(i) = t.add(Entry { op, args: [0, 0] }, 1, v) {
                by_size[1].push(i);
            }
        }
        for size in 2..=usize::from(max_size) {
            let mut level = Vec::new();
            for &x in &by_size[size - 1] {
                for op in [Op::Not, Op::Neg] {
                    let v = apply(op, &t.values[x as usize], &zero);
                    if let Some(i) = t.add(Entry { op, args: [x, 0] }, size as u8, v) {
                        level.push(i);
                    }
                }
            }
            for s1 in 1..size - 1 {
                let s2 = size - 1 - s1;
                if s2 < s1 {
                    break;
                }
                for (ix, &x) in by_size[s1].iter().enumerate() {
                    let start = if s1 == s2 { ix } else { 0 };
                    for &y in &by_size[s2][start..] {
                        for op in [Op::Add, Op::Mul, Op::And, Op::Or, Op::Xor] {
                            let v = apply(op, &t.values[x as usize], &t.values[y as usize]);
                            if let Some(i) = t.add(Entry { op, args: [x, y] }, size as u8, v) {
                                level.push(i);
                            }
                        }
                        for (p, q) in [(x, y), (y, x)] {
                            let v = apply(Op::Sub, &t.values[p as usize], &t.values[q as usize]);
                            if let Some(i) = t.add(
                                Entry {
                                    op: Op::Sub,
                                    args: [p, q],
                                },
                                size as u8,
                                v,
                            ) {
                                level.push(i);
                            }
                            if x == y {
                                break;
                            }
                        }
                    }
                }
            }
            by_size[size] = level;
        }
        t
    }

    /// Adds an entry unless an earlier one has its values; one of the same size that uses
    /// more distinct subexpressions takes the new form instead (its operands are all of
    /// smaller sizes, so nothing refers to it yet).
    fn add(&mut self, e: Entry, size: u8, v: Values) -> Option<u32> {
        let arity = e.op.arity();
        // The operands' entries (a leaf has none).
        let operand = |k: usize| match k < arity {
            true => self.reach[e.args[k] as usize],
            false => Reach::default(),
        };
        let operands = [operand(0), operand(1)];
        let parts = [&operands[0], &operands[1]];
        let parts = &parts[..arity];
        let h = fold(&v, u64::MAX);
        match self.wide.find(h, |j| self.values[j as usize] == v) {
            Some(j) => {
                if self.sizes[j as usize] == size
                    && let Some(r) = Reach::of(j, parts)
                    && r.len < self.reach[j as usize].len
                {
                    self.entries[j as usize] = e;
                    self.reach[j as usize] = r;
                }
                None
            }
            None => {
                let i = self.entries.len() as u32;
                let r = Reach::of(i, parts)?;
                self.wide.insert(h, i);
                self.entries.push(e);
                self.sizes.push(size);
                self.reach.push(r);
                self.values.push(v);
                Some(i)
            }
        }
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn entry(&self, i: u32) -> Entry {
        self.entries[i as usize]
    }

    #[cfg(test)]
    fn size(&self, i: u32) -> u8 {
        self.sizes[i as usize]
    }

    #[cfg(test)]
    fn values(&self, i: u32) -> &[u64; PROBES] {
        &self.values[i as usize]
    }

    /// The entries entry `i` uses, itself included, operands first (theirs are smaller
    /// indices).
    pub(crate) fn needed(&self, i: u32) -> Vec<u32> {
        let mut need = vec![i];
        let mut k = 0;
        while k < need.len() {
            let e = self.entries[need[k] as usize];
            for &a in &e.args[..e.op.arity()] {
                if !need.contains(&a) {
                    need.push(a);
                }
            }
            k += 1;
        }
        need.sort_unstable();
        need
    }

    /// The smallest entry with these values at `bits` bits (values already truncated).
    pub(crate) fn lookup(&self, bits: u16, v: &Values) -> Option<u32> {
        if bits >= 64 {
            return self
                .wide
                .find(fold(v, u64::MAX), |j| self.values[j as usize] == *v);
        }
        let mask = (1u64 << bits) - 1;
        let index = self.narrow[usize::from(bits)].get_or_init(|| {
            // Entries in order: the first of each truncated value vector is the one kept.
            let mut ix = Index::with_capacity(self.values.len());
            for (i, full) in self.values.iter().enumerate() {
                let h = fold(full, mask);
                if ix
                    .find(h, |j| same(&self.values[j as usize], full, mask))
                    .is_none()
                {
                    ix.insert(h, i as u32);
                }
            }
            ix
        });
        index.find(fold(v, mask), |j| same(&self.values[j as usize], v, mask))
    }

    /// Entry `i` as an expression over `atoms` variables of width `w` (`None` if it uses a
    /// further atom).
    pub(crate) fn expr(&self, i: u32, w: Width, atoms: usize) -> Option<MbaExpr> {
        let mut m = MbaExpr::new(vec![w; atoms]);
        let mut id: HashMap<u32, u32> = HashMap::new();
        for j in self.needed(i) {
            let e = self.entries[j as usize];
            let args: Option<Vec<u32>> = e.args[..e.op.arity()]
                .iter()
                .map(|a| id.get(a).copied())
                .collect();
            let n = match e.op {
                Op::Var(v) if usize::from(v) < atoms => m.push(MOp::Var(u32::from(v)), &[]),
                Op::Var(_) => return None,
                Op::One => m.push(MOp::Const(BitVec::one(w)), &[]),
                op => m.push(op.mop()?, &args?),
            };
            id.insert(j, n.ok()?);
        }
        Some(m)
    }
}

/// The table, built on first use (once per process: it depends on nothing but its bounds).
pub(crate) fn table() -> &'static Table {
    static TABLE: OnceLock<Table> = OnceLock::new();
    TABLE.get_or_init(|| Table::build(MAX_SIZE))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Entry `i` evaluated at every probe point at width `w` (probes truncated or
    /// zero-extended), as the low 64 bits.
    fn eval(t: &Table, i: u32, w: Width) -> Values {
        let e = t.expr(i, w, 3).unwrap();
        core::array::from_fn(|k| {
            let p = probe(k).map(|x| BitVec::wrapping_from_u64(w, x));
            e.eval(&p).unwrap().limbs()[0]
        })
    }

    #[test]
    fn every_entry_has_its_values_and_the_order_is_by_size() {
        let t = table();
        assert!(t.len() > 20_000, "{}", t.len());
        assert_eq!(t.wide.len(), t.len());
        for i in 0..t.len() as u32 {
            assert_eq!(&eval(t, i, Width::W64), t.values(i), "{i}");
            if i > 0 {
                assert!(t.size(i - 1) <= t.size(i));
            }
            let r = t.reach[i as usize];
            assert!(r.len <= t.size(i) && r.ids[..usize::from(r.len)].contains(&i));
        }
    }

    #[test]
    fn narrower_and_wider_widths_read_the_same_table() {
        let t = table();
        // Some entries: the value at W bits is the 64-bit value truncated, and a wider width's
        // low 64 bits are the 64-bit value (the operators never carry downward).
        for i in (0..t.len() as u32).step_by(37) {
            for bits in [1u16, 2, 3, 5, 8, 32, 65, 128, 512] {
                let mask = if bits >= 64 {
                    u64::MAX
                } else {
                    (1 << bits) - 1
                };
                let want = t.values(i).map(|x| x & mask);
                assert_eq!(eval(t, i, Width::new(bits).unwrap()), want, "{i} at {bits}");
            }
        }
        // A lookup gives the first entry with the truncated values.
        for bits in [1u16, 4, 8, 16] {
            let mask = (1u64 << bits) - 1;
            for i in (0..t.len() as u32).step_by(97) {
                let v = t.values(i).map(|x| x & mask);
                let j = t.lookup(bits, &v).unwrap();
                assert!(
                    j <= i && t.values(j).map(|x| x & mask) == v,
                    "{i} {j} at {bits}"
                );
            }
        }
    }

    #[test]
    fn the_table_is_deterministic() {
        let (a, b) = (Table::build(5), Table::build(5));
        assert_eq!(a.entries, b.entries);
        assert_eq!(a.values, b.values);
        let t = table();
        assert_eq!(&t.entries[..a.len()], &a.entries[..]);
    }
}
