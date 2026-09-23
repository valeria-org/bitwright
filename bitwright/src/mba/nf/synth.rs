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
use std::collections::hash_map::Entry as MapEntry;
use std::sync::{Arc, Mutex, OnceLock};

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

/// A 128-bit digest of values at the probes (the tables' key).
fn digest(v: &Values) -> [u64; 2] {
    let mut h = [0x6a09_e667_f3bc_c908u64, 0xbb67_ae85_84ca_a73b];
    for &x in v {
        h[0] = crate::hash::combine(h[0], x);
        h[1] = crate::hash::combine(h[1] ^ 0x5555, x.rotate_left(29));
    }
    h
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

/// Entries by digest of their values.
type Index = HashMap<[u64; 2], u32>;

/// The table: entries in order of size, each the first of its values at the probes.
pub(crate) struct Table {
    entries: Vec<Entry>,
    sizes: Vec<u8>,
    reach: Vec<Reach>,
    values: Vec<Values>,
    /// Per width below 64: the first entry by values truncated to the width.
    narrow: Mutex<HashMap<u16, Arc<Index>>>,
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
            narrow: Mutex::new(HashMap::new()),
            wide: HashMap::new(),
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
        let parts: Vec<&Reach> = e.args[..e.op.arity()]
            .iter()
            .map(|&a| &self.reach[a as usize])
            .collect();
        match self.wide.entry(digest(&v)) {
            MapEntry::Occupied(slot) => {
                let j = *slot.get();
                if self.sizes[j as usize] == size
                    && let Some(r) = Reach::of(j, &parts)
                    && r.len < self.reach[j as usize].len
                {
                    self.entries[j as usize] = e;
                    self.reach[j as usize] = r;
                }
                None
            }
            MapEntry::Vacant(slot) => {
                let i = self.entries.len() as u32;
                let r = Reach::of(i, &parts)?;
                slot.insert(i);
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
            return self.wide.get(&digest(v)).copied();
        }
        let index = {
            let mut narrow = self.narrow.lock().ok()?;
            match narrow.get(&bits) {
                Some(ix) => ix.clone(),
                None => {
                    let mask = (1u64 << bits) - 1;
                    let mut ix = Index::new();
                    for (i, full) in self.values.iter().enumerate() {
                        ix.entry(digest(&full.map(|x| x & mask)))
                            .or_insert(i as u32);
                    }
                    let ix = Arc::new(ix);
                    narrow.insert(bits, ix.clone());
                    ix
                }
            }
        };
        index.get(&digest(v)).copied()
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
