//! Bitwise functions of atoms: one truth table per bit class, over the atoms they depend on.
//!
//! A bitwise function applies, inside each class, one Boolean function `β` at every position.
//! Writing `β` as an integer multilinear polynomial `β(b) = Σ_T a_T·Π_{i∈T} b_i` (Möbius over
//! the table) and summing `2^j·β(x[j])` over the class's positions gives the function exactly
//! in Z/2^W as `Σ_T a_T·(AND_T & M_c)` (with `AND_∅ & M_c = M_c`): see [`Bits::to_poly`]. The
//! converse test, [`Bits::from_linear`], recognizes a degree-≤1 polynomial that is a bitwise
//! function.

use super::classes::Classes;
use super::poly::{Poly, Sym};
use crate::BitVec;
use crate::facts::known::{bv_and, low_mask};
use crate::ops::BinOp;

/// The most atoms one bitwise function may depend on (a table has 2^s entries).
pub(crate) const MAX_SUPPORT: usize = 12;

/// A bitwise operator.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum BitOp {
    And,
    Or,
    Xor,
}

/// A bitwise function of atoms.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Bits {
    /// The atoms it may depend on, ascending (at most [`MAX_SUPPORT`]).
    pub(crate) support: Vec<u32>,
    /// Per class: the truth table (entry `p` is the value when atom `support[k]` has bit `k` of
    /// `p`); `max(1, 2^s / 64)` words, unused bits zero.
    pub(crate) tables: Vec<Vec<u64>>,
}

fn words(s: usize) -> usize {
    (1usize << s).div_ceil(64)
}

pub(crate) fn get(t: &[u64], p: usize) -> bool {
    t[p / 64] >> (p % 64) & 1 == 1
}

fn set(t: &mut [u64], p: usize) {
    t[p / 64] |= 1u64 << (p % 64);
}

/// Clears the bits of a table of 2^s entries beyond its entries.
fn trim(t: &mut [u64], s: usize) {
    if s < 6 {
        t[0] &= (1u64 << (1usize << s)) - 1;
    }
}

impl Bits {
    /// A constant: per class, its bit.
    pub(crate) fn constant(bits: &[bool]) -> Bits {
        Bits {
            support: Vec::new(),
            tables: bits.iter().map(|&b| vec![u64::from(b)]).collect(),
        }
    }

    /// Atom `a` itself.
    pub(crate) fn atom(classes: usize, a: u32) -> Bits {
        Bits {
            support: vec![a],
            tables: vec![vec![0b10]; classes],
        }
    }

    pub(crate) fn not(&self) -> Bits {
        let s = self.support.len();
        Bits {
            support: self.support.clone(),
            tables: self
                .tables
                .iter()
                .map(|t| {
                    let mut n: Vec<u64> = t.iter().map(|w| !w).collect();
                    trim(&mut n, s);
                    n
                })
                .collect(),
        }
    }

    /// The tables over `to` (a superset of the support, ascending).
    fn expand(&self, to: &[u32]) -> Vec<Vec<u64>> {
        let pos: Vec<usize> = self
            .support
            .iter()
            .map(|a| to.iter().position(|b| b == a).unwrap_or(0))
            .collect();
        let n = to.len();
        self.tables
            .iter()
            .map(|t| {
                let mut out = vec![0u64; words(n)];
                for q in 0..1usize << n {
                    let p = pos
                        .iter()
                        .enumerate()
                        .fold(0usize, |p, (k, &j)| p | ((q >> j) & 1) << k);
                    if get(t, p) {
                        set(&mut out, q);
                    }
                }
                out
            })
            .collect()
    }

    /// `a op b`, or `None` when the result would depend on more than [`MAX_SUPPORT`] atoms.
    pub(crate) fn bin(op: BitOp, a: &Bits, b: &Bits) -> Option<Bits> {
        let mut support: Vec<u32> = a.support.iter().chain(&b.support).copied().collect();
        support.sort_unstable();
        support.dedup();
        if support.len() > MAX_SUPPORT {
            return None;
        }
        let (ta, tb) = (a.expand(&support), b.expand(&support));
        let tables = ta
            .iter()
            .zip(&tb)
            .map(|(x, y)| {
                x.iter()
                    .zip(y)
                    .map(|(u, v)| match op {
                        BitOp::And => u & v,
                        BitOp::Or => u | v,
                        BitOp::Xor => u ^ v,
                    })
                    .collect()
            })
            .collect();
        Some(Bits { support, tables }.prune())
    }

    /// Drops the atoms no table depends on.
    pub(crate) fn prune(self) -> Bits {
        let s = self.support.len();
        let keep: Vec<u32> = (0..s)
            .filter(|&k| {
                self.tables.iter().any(|t| {
                    (0..1usize << s).any(|p| p >> k & 1 == 0 && get(t, p) != get(t, p | 1 << k))
                })
            })
            .map(|k| self.support[k])
            .collect();
        if keep.len() == s {
            return self;
        }
        // Read each table with the dropped atoms at 0.
        let pos: Vec<usize> = keep
            .iter()
            .map(|a| self.support.iter().position(|b| b == a).unwrap_or(0))
            .collect();
        let tables = self
            .tables
            .iter()
            .map(|t| {
                let mut out = vec![0u64; words(keep.len())];
                for q in 0..1usize << keep.len() {
                    let p = pos
                        .iter()
                        .enumerate()
                        .fold(0usize, |p, (k, &j)| p | ((q >> k) & 1) << j);
                    if get(t, p) {
                        set(&mut out, q);
                    }
                }
                out
            })
            .collect();
        Bits {
            support: keep,
            tables,
        }
    }

    /// Whether every class has the same table.
    pub(crate) fn uniform(&self) -> bool {
        self.tables.windows(2).all(|w| w[0] == w[1])
    }

    /// The masked-conjunction form: `Σ_c Σ_T a_{c,T}·(AND_T & M_c)`, exact at every width.
    pub(crate) fn to_poly(&self, classes: &Classes) -> Poly {
        let w = classes.width();
        let s = self.support.len();
        let mut out = Poly::zero(w);
        for (c, t) in self.tables.iter().enumerate() {
            let a = mobius(t, s);
            for (q, &k) in a.iter().enumerate() {
                if k == 0 {
                    continue;
                }
                let kv = BitVec::wrapping_from_i128(w, i128::from(k));
                if q == 0 {
                    out.add_term(
                        Vec::new(),
                        &BitVec::bin_unchecked(BinOp::Mul, &kv, classes.mask(c)),
                    );
                    continue;
                }
                let set = (0..s)
                    .filter(|&j| q >> j & 1 == 1)
                    .fold(0u64, |m, j| m | 1u64 << self.support[j]);
                let sym = Sym {
                    set,
                    class: c as u16,
                };
                out.add_term(vec![(sym, 1)], &kv);
            }
        }
        out
    }

    /// The bitwise function a polynomial of degree at most 1 is, if it is one (with respect to
    /// `classes`): in every class `c`, with `k_c` the constant's bit there (the constant must
    /// be 0 or all-ones in each class) and `Δ_c(p) = Σ_{∅≠S⊆p} γ_{c,S}`, `k_c + Δ_c(p)` must be 0
    /// or 1 modulo `2^(W − τ_c)` at every class corner `p`; it is the table's entry.
    pub(crate) fn from_linear(p: &Poly, classes: &Classes) -> Option<Bits> {
        if p.degree() > 1 {
            return None;
        }
        let w = classes.width();
        let atoms = p.atoms();
        let mut support: Vec<u32> = (0..64).filter(|&a| atoms >> a & 1 == 1).collect();
        support.sort_unstable();
        if support.len() > MAX_SUPPORT {
            return None;
        }
        let s = support.len();
        let n = classes.len();
        let konst = p.konst();
        let mut gamma: Vec<Vec<BitVec>> = vec![vec![BitVec::zero(w); 1 << s]; n];
        for (m, c) in p.terms() {
            let Some(&(sym, _)) = m.first() else {
                continue;
            };
            let q = support
                .iter()
                .enumerate()
                .filter(|&(_, &a)| sym.set >> a & 1 == 1)
                .fold(0usize, |q, (j, _)| q | 1 << j);
            let slot = &mut gamma[usize::from(sym.class)][q];
            *slot = BitVec::bin_unchecked(BinOp::Add, slot, c);
        }
        let mut tables = Vec::with_capacity(n);
        for (c, g) in gamma.iter_mut().enumerate() {
            let inside = bv_and(&konst, classes.mask(c));
            let k = if inside.is_zero() {
                BitVec::zero(w)
            } else if inside == *classes.mask(c) {
                BitVec::one(w)
            } else {
                return None;
            };
            // Subset sums: Δ(p) = Σ_{S⊆p} γ_S.
            for b in 0..s {
                for q in 0..1usize << s {
                    if q >> b & 1 == 1 {
                        g[q] = BitVec::bin_unchecked(BinOp::Add, &g[q], &g[q ^ 1 << b]);
                    }
                }
            }
            let prec = u32::from(w.bits()) - u32::from(classes.low(c));
            let lm = low_mask(w, prec);
            let mut t = vec![0u64; words(s)];
            for (q, d) in g.iter().enumerate() {
                let v = bv_and(&BitVec::bin_unchecked(BinOp::Add, &k, d), &lm);
                if v == BitVec::one(w) {
                    set(&mut t, q);
                } else if !v.is_zero() {
                    return None;
                }
            }
            tables.push(t);
        }
        Some(Bits { support, tables }.prune())
    }
}

/// The integer multilinear coefficients of a 0/1 table of 2^s entries: `a_T = Σ_{U⊆T}
/// (−1)^{|T|−|U|}·f(U)`.
pub(crate) fn mobius(t: &[u64], s: usize) -> Vec<i64> {
    let mut a: Vec<i64> = (0..1usize << s).map(|p| i64::from(get(t, p))).collect();
    for b in 0..s {
        for p in 0..1usize << s {
            if p >> b & 1 == 1 {
                a[p] -= a[p ^ 1 << b];
            }
        }
    }
    a
}

/// The algebraic normal form over GF(2) of a table: the subsets whose conjunctions xor to it.
pub(crate) fn anf(t: &[u64], s: usize) -> Vec<usize> {
    let mut a: Vec<bool> = (0..1usize << s).map(|p| get(t, p)).collect();
    for b in 0..s {
        for p in 0..1usize << s {
            if p >> b & 1 == 1 {
                a[p] ^= a[p ^ 1 << b];
            }
        }
    }
    (0..1usize << s).filter(|&p| a[p]).collect()
}

/// A table of at most three atoms as the 8-bit table of the minimum-form library (entry `i`
/// with atom `k` at bit `k` of `i`; unused atoms ignored).
pub(crate) fn table8(t: &[u64], s: usize) -> Option<u8> {
    if s > 3 {
        return None;
    }
    let mut out = 0u8;
    for i in 0..8usize {
        let p = i & ((1 << s) - 1);
        if get(t, p) {
            out |= 1 << i;
        }
    }
    Some(out)
}
