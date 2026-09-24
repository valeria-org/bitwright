//! Polynomials over masked conjunctions, with coefficients in Z/2^W.
//!
//! A *symbol* `(S, c)` stands for `AND_S & M_c`: the conjunction of the atoms in `S`, restricted
//! to the positions of bit class `c`. Products of symbols are multiplied out formally; the
//! result is exact (expanding and collecting are ring operations), though not canonical,
//! because symbols are related (see [`Poly::reduce_core`] for the reductions that are cheap and
//! exact).

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

use super::classes::{Classes, FULL};
use crate::facts::known::low_mask;
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// A masked conjunction `AND_set & M_class` (`set` a mask over atom ids, never empty).
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Sym {
    pub(crate) set: u64,
    pub(crate) class: u16,
}

/// A product of symbols: ascending symbols with positive exponents. Empty for the constant.
pub(crate) type Mono = Vec<(Sym, u32)>;

/// The total degree of a monomial.
pub(crate) fn degree(m: &Mono) -> u32 {
    m.iter().map(|&(_, e)| e).sum()
}

/// The product of two monomials.
pub(crate) fn mono_mul(a: &Mono, b: &Mono) -> Mono {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        match (a.get(i), b.get(j)) {
            (Some(x), Some(y)) if x.0 == y.0 => {
                out.push((x.0, x.1 + y.1));
                i += 1;
                j += 1;
            }
            (Some(x), Some(y)) if x.0 < y.0 => {
                out.push(*x);
                i += 1;
            }
            (Some(x), None) => {
                out.push(*x);
                i += 1;
            }
            (_, Some(y)) => {
                out.push(*y);
                j += 1;
            }
            (None, None) => break,
        }
    }
    out
}

/// `a / b` when `b` divides `a` exponent-wise.
pub(crate) fn mono_div(a: &Mono, b: &Mono) -> Option<Mono> {
    let mut out = Vec::with_capacity(a.len());
    let mut j = 0;
    for &(s, e) in a {
        if let Some(&(t, f)) = b.get(j)
            && t == s
        {
            j += 1;
            if f > e {
                return None;
            }
            if f < e {
                out.push((s, e - f));
            }
            continue;
        }
        if b.get(j).is_some_and(|&(t, _)| t < s) {
            return None;
        }
        out.push((s, e));
    }
    (j == b.len()).then_some(out)
}

/// The graded lexicographic order (a monomial order: compatible with multiplication).
pub(crate) fn grlex(a: &Mono, b: &Mono) -> core::cmp::Ordering {
    degree(a).cmp(&degree(b)).then_with(|| {
        let (mut i, mut j) = (0, 0);
        loop {
            match (a.get(i), b.get(j)) {
                (None, None) => return core::cmp::Ordering::Equal,
                (Some(_), None) => return core::cmp::Ordering::Greater,
                (None, Some(_)) => return core::cmp::Ordering::Less,
                (Some(x), Some(y)) => {
                    if x.0 != y.0 {
                        // A smaller symbol present in only one side makes that side larger.
                        return if x.0 < y.0 {
                            core::cmp::Ordering::Greater
                        } else {
                            core::cmp::Ordering::Less
                        };
                    }
                    if x.1 != y.1 {
                        return x.1.cmp(&y.1);
                    }
                    i += 1;
                    j += 1;
                }
            }
        }
    })
}

/// A monomial ordered by [`grlex`], for the division algorithm.
#[derive(Clone, PartialEq, Eq)]
struct Graded(Mono);

impl Ord for Graded {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        grlex(&self.0, &other.0)
    }
}

impl PartialOrd for Graded {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// A polynomial: monomials with nonzero coefficients (the empty monomial is the constant).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Poly {
    w: Width,
    terms: BTreeMap<Mono, BitVec>,
}

fn add(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Add, a, b)
}

fn mul(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Mul, a, b)
}

/// `v₂(n!)` (Legendre).
fn v2_factorial(n: u32) -> u32 {
    n - n.count_ones()
}

/// The representative of `c` mod 2^m in `(−2^(m−1), 2^(m−1)]` (as a W-bit value; `m ≥ W`
/// leaves `c` as it is, `m = 0` gives 0).
pub(crate) fn signed_rep(c: &BitVec, m: u32) -> BitVec {
    let w = c.width();
    if m >= u32::from(w.bits()) {
        return *c;
    }
    if m == 0 {
        return BitVec::zero(w);
    }
    let t = crate::facts::known::bv_and(c, &low_mask(w, m));
    let half = crate::facts::known::bv_shl(&BitVec::one(w), m - 1);
    if BitVec::cmp_unchecked(crate::ops::CmpOp::Ult, &half, &t) {
        // t − 2^m, mod 2^W.
        let full = crate::facts::known::bv_shl(&BitVec::one(w), m);
        BitVec::bin_unchecked(BinOp::Sub, &t, &full)
    } else {
        t
    }
}

/// The signed Stirling numbers of the first kind `s(e, j)`, `j = 0..=e`, mod 2^W:
/// `(x)_e = Σ_j s(e, j)·x^j`.
fn stirling1(e: u32, w: Width) -> Vec<BitVec> {
    let mut row = vec![BitVec::one(w)];
    for n in 0..e {
        // s(n+1, k) = s(n, k−1) − n·s(n, k).
        let nn = BitVec::wrapping_from_u64(w, u64::from(n));
        let mut next = vec![BitVec::zero(w); row.len() + 1];
        for (k, s) in row.iter().enumerate() {
            next[k + 1] = add(&next[k + 1], s);
            next[k] = BitVec::bin_unchecked(BinOp::Sub, &next[k], &mul(&nn, s));
        }
        row = next;
    }
    row
}

impl Poly {
    pub(crate) fn zero(w: Width) -> Poly {
        Poly {
            w,
            terms: BTreeMap::new(),
        }
    }

    pub(crate) fn constant(v: BitVec) -> Poly {
        let mut p = Poly::zero(v.width());
        p.add_term(Vec::new(), &v);
        p
    }

    /// One monomial.
    pub(crate) fn term(w: Width, m: Mono, c: &BitVec) -> Poly {
        let mut p = Poly::zero(w);
        p.add_term(m, c);
        p
    }

    /// A symbol, coefficient 1.
    pub(crate) fn sym(w: Width, s: Sym) -> Poly {
        Poly::term(w, vec![(s, 1)], &BitVec::one(w))
    }

    pub(crate) fn width(&self) -> Width {
        self.w
    }

    pub(crate) fn terms(&self) -> &BTreeMap<Mono, BitVec> {
        &self.terms
    }

    pub(crate) fn len(&self) -> usize {
        self.terms.len()
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The constant term.
    pub(crate) fn konst(&self) -> BitVec {
        self.terms
            .get(&Vec::new())
            .copied()
            .unwrap_or(BitVec::zero(self.w))
    }

    /// The largest total degree (0 for a constant).
    pub(crate) fn degree(&self) -> u32 {
        self.terms.keys().map(degree).max().unwrap_or(0)
    }

    /// The atoms it mentions.
    pub(crate) fn atoms(&self) -> u64 {
        self.terms
            .keys()
            .flat_map(|m| m.iter())
            .fold(0, |acc, (s, _)| acc | s.set)
    }

    /// The low 64 bits of the value where atom `i` has low 64 bits `atoms[i]` (`None` if it
    /// mentions an atom beyond them). A sum of products of masked conjunctions carries nothing
    /// downward, so they depend on nothing else; at narrower widths, truncate.
    pub(crate) fn eval_low(&self, classes: &Classes, atoms: &[u64]) -> Option<u64> {
        let mut total = 0u64;
        for (m, c) in &self.terms {
            let mut prod = c.limbs()[0];
            for &(s, e) in m {
                let mut v = classes.mask(usize::from(s.class)).limbs()[0];
                let mut set = s.set;
                while set != 0 {
                    v &= *atoms.get(set.trailing_zeros() as usize)?;
                    set &= set - 1;
                }
                prod = prod.wrapping_mul(v.wrapping_pow(e));
            }
            total = total.wrapping_add(prod);
        }
        Some(total)
    }

    /// The same polynomial with atom `i` renamed `map[i]` (a bijection on the atoms it
    /// mentions).
    pub(crate) fn rename_atoms(&self, map: &[u32]) -> Poly {
        let mut out = Poly::zero(self.w);
        for (m, c) in &self.terms {
            let mut n: Mono = m
                .iter()
                .map(|&(s, e)| {
                    let mut set = 0u64;
                    let mut old = s.set;
                    while old != 0 {
                        let a = old.trailing_zeros() as usize;
                        set |= 1 << map.get(a).copied().unwrap_or(a as u32);
                        old &= old - 1;
                    }
                    (
                        Sym {
                            set,
                            class: s.class,
                        },
                        e,
                    )
                })
                .collect();
            n.sort_unstable_by_key(|x| x.0);
            out.add_term(n, c);
        }
        out
    }

    /// How many low bits of the value are known: every monomial but the constant is a
    /// multiple of `2^k` (its coefficient's trailing zeros, plus `τ·e` for each factor `m^e` of
    /// a class whose lowest position is `τ`), so the low `k` bits are the constant term's.
    pub(crate) fn known_low_bits(&self, classes: &Classes) -> u32 {
        let bits = u32::from(self.w.bits());
        self.terms
            .iter()
            .filter(|(m, _)| !m.is_empty())
            .map(|(m, c)| {
                m.iter()
                    .fold(crate::facts::known::trailing_zeros(c), |k, &(s, e)| {
                        let low = u32::from(classes.low(usize::from(s.class)));
                        k.saturating_add(low.saturating_mul(e))
                    })
            })
            .min()
            .unwrap_or(bits)
            .min(bits)
    }

    /// The same function with atom `a`, whose value is `def` (a polynomial in other atoms),
    /// standing for a multiple of its definition: `self − c·def + c·a`, when `self` contains
    /// `c·def`'s every non-constant term. `c` is solved from the term of `def` with the fewest
    /// factors of two (`c·d ≡ n` for its coefficients `d` in `def` and `n` in `self`, unique
    /// modulo `2^(W − v₂(d))`, which then fixes `c·d'` for every other term). `None` otherwise,
    /// or when `def` mentions `a` or is a constant.
    pub(crate) fn substitute(&self, a: u32, def: &Poly) -> Option<Poly> {
        use crate::facts::known::{bv_lshr, trailing_zeros};
        let bits = u32::from(self.w.bits());
        if a >= 64 || def.atoms() >> a & 1 == 1 || def.w != self.w {
            return None;
        }
        let tail = || def.terms.iter().filter(|(m, _)| !m.is_empty());
        let (pm, d) = def.pivot()?;
        let n = self.terms.get(pm)?;
        let v = trailing_zeros(d);
        if trailing_zeros(n) < v {
            return None;
        }
        // The representative nearest zero.
        let c = mul(&bv_lshr(n, v), &odd_inverse(&bv_lshr(d, v)));
        let c = signed_rep(&c, bits - v);
        if !tail().all(|(m, d)| self.terms.get(m) == Some(&mul(&c, d))) {
            return None;
        }
        let mut out = self.sub(&def.scale(&c));
        out.add_term(
            vec![(
                Sym {
                    set: 1 << a,
                    class: FULL,
                },
                1,
            )],
            &c,
        );
        Some(out)
    }

    /// The non-constant term with the fewest factors of two in its coefficient (the first of
    /// them).
    pub(crate) fn pivot(&self) -> Option<(&Mono, &BitVec)> {
        self.terms
            .iter()
            .filter(|(m, _)| !m.is_empty())
            .min_by_key(|(_, c)| crate::facts::known::trailing_zeros(c))
    }

    /// The terms whose degree satisfies `keep`.
    pub(crate) fn part(&self, keep: impl Fn(u32) -> bool) -> Poly {
        Poly {
            w: self.w,
            terms: self
                .terms
                .iter()
                .filter(|(m, _)| keep(degree(m)))
                .map(|(m, c)| (m.clone(), *c))
                .collect(),
        }
    }

    /// Adds `c·m`.
    pub(crate) fn add_term(&mut self, m: Mono, c: &BitVec) {
        if c.is_zero() {
            return;
        }
        match self.terms.entry(m) {
            std::collections::btree_map::Entry::Vacant(v) => {
                v.insert(*c);
            }
            std::collections::btree_map::Entry::Occupied(mut o) => {
                let s = add(o.get(), c);
                if s.is_zero() {
                    o.remove();
                } else {
                    *o.get_mut() = s;
                }
            }
        }
    }

    pub(crate) fn add(&self, o: &Poly) -> Poly {
        let (mut big, small) = if self.len() >= o.len() {
            (self.clone(), o)
        } else {
            (o.clone(), self)
        };
        for (m, c) in &small.terms {
            big.add_term(m.clone(), c);
        }
        big
    }

    pub(crate) fn scale(&self, k: &BitVec) -> Poly {
        let mut out = Poly::zero(self.w);
        for (m, c) in &self.terms {
            out.add_term(m.clone(), &mul(c, k));
        }
        out
    }

    pub(crate) fn neg(&self) -> Poly {
        self.scale(&BitVec::ones(self.w))
    }

    pub(crate) fn sub(&self, o: &Poly) -> Poly {
        self.add(&o.neg())
    }

    /// The product (`self.len() · o.len()` monomial products; size it first).
    pub(crate) fn mul(&self, o: &Poly) -> Poly {
        let mut out = Poly::zero(self.w);
        for (m, c) in &self.terms {
            for (n, d) in &o.terms {
                out.add_term(mono_mul(m, n), &mul(c, d));
            }
        }
        out
    }

    /// The monomial of the largest term in graded lexicographic order, and its coefficient.
    pub(crate) fn leading(&self) -> Option<(&Mono, &BitVec)> {
        self.terms.iter().max_by(|a, b| grlex(a.0, b.0))
    }

    /// `self / f` when `f` divides it exactly and `f`'s leading coefficient is odd (a unit), by
    /// the division algorithm in graded lexicographic order, which then always finds the
    /// quotient: each step cancels the remainder's leading term and adds only smaller ones (a
    /// monomial order is compatible with multiplication).
    ///
    /// Work, in term operations, is charged to `budget`: `self.len()` to start, then
    /// `f.len()` per quotient term; `Err` when it runs out. `Ok(None)`: not divisible so.
    pub(crate) fn div_exact(&self, f: &Poly, budget: &mut u64) -> Result<Option<Poly>, ()> {
        let Some((lm, lc)) = f.leading() else {
            return Ok(None);
        };
        if !lc.bit(0).unwrap_or(false) {
            return Ok(None);
        }
        *budget = budget.checked_sub(self.len() as u64).ok_or(())?;
        let Some((top, _)) = self.leading() else {
            return Ok(Some(Poly::zero(self.w)));
        };
        // Most attempts end here: the leading monomial is not a multiple of `f`'s.
        if mono_div(top, lm).is_none() {
            return Ok(None);
        }
        let inv = odd_inverse(lc);
        let tail: Vec<(&Mono, &BitVec)> = f.terms.iter().filter(|(m, _)| *m != lm).collect();
        let mut rest: BTreeMap<Graded, BitVec> = self
            .terms
            .iter()
            .map(|(m, c)| (Graded(m.clone()), *c))
            .collect();
        let mut q = Poly::zero(self.w);
        while let Some((Graded(m), c)) = rest.pop_last() {
            *budget = budget.checked_sub(f.len() as u64).ok_or(())?;
            let Some(qm) = mono_div(&m, lm) else {
                return Ok(None);
            };
            let qc = mul(&c, &inv);
            for &(n, d) in &tail {
                let v = mul(&qc, d);
                if v.is_zero() {
                    continue;
                }
                match rest.entry(Graded(mono_mul(&qm, n))) {
                    Entry::Occupied(mut e) => {
                        let r = BitVec::bin_unchecked(BinOp::Sub, e.get(), &v);
                        if r.is_zero() {
                            e.remove();
                        } else {
                            *e.get_mut() = r;
                        }
                    }
                    Entry::Vacant(e) => {
                        e.insert(BitVec::un_unchecked(UnOp::Neg, &v));
                    }
                }
            }
            q.add_term(qm, &qc);
        }
        Ok(Some(q))
    }

    /// The one-position rule: a symbol of a class with the single position `j` takes only the
    /// values 0 and `2^j`, so `m^e = 2^{j(e−1)}·m`.
    pub(crate) fn single_positions(&mut self, classes: &Classes) {
        let bits = u32::from(self.w.bits());
        if (0..classes.len()).any(|c| classes.single(c).is_some()) {
            let old = std::mem::take(&mut self.terms);
            for (m, c) in old {
                let mut k = c;
                let mut out: Mono = Vec::with_capacity(m.len());
                for (s, e) in m {
                    match classes.single(usize::from(s.class)) {
                        Some(j) if e > 1 => {
                            let sh = u32::from(j).saturating_mul(e - 1).min(bits);
                            k = crate::facts::known::bv_shl(&k, sh);
                            out.push((s, 1));
                        }
                        _ => out.push((s, e)),
                    }
                }
                self.add_term(out, &k);
            }
        }
    }

    /// Exact, cheap reductions, applied in place (also
    /// [`single_positions`](Self::single_positions)):
    ///
    /// - a monomial with symbols of classes starting at `τ` is a multiple of `2^τ` (the sum over
    ///   its factors), so its coefficient matters only mod `2^(W−τ)`;
    /// - `(x)_κ = Π (x_i)_{κ_i}` is a multiple of `κ! = Π κ_i!` for any integers, so
    ///   `2^(W − v₂(κ!))·(x)_κ = 0`: from the highest degree down, each coefficient is brought
    ///   into `(−2^(m−1), 2^(m−1)]` for the larger of the two moduli, the falling-factorial
    ///   one moving the difference into lower monomials.
    ///
    /// Both hold whatever values the symbols take, so treating symbols as independent is
    /// sound. For a polynomial in independent atoms (no bitwise operator) the result is
    /// canonical: equal polynomial functions reduce to the same terms.
    pub(crate) fn reduce_core(&mut self, classes: &Classes) {
        let w = self.w;
        let bits = u32::from(w.bits());
        let top = self.degree();
        for d in (0..=top).rev() {
            let monos: Vec<Mono> = self
                .terms
                .keys()
                .filter(|m| degree(m) == d)
                .cloned()
                .collect();
            for m in monos {
                let Some(c) = self.terms.get(&m).copied() else {
                    continue;
                };
                let tau: u32 = m
                    .iter()
                    .map(|&(s, e)| u32::from(classes.low(usize::from(s.class))).saturating_mul(e))
                    .fold(0u32, u32::saturating_add);
                if tau >= bits {
                    self.terms.remove(&m);
                    continue;
                }
                let m1 = bits - tau;
                let v: u32 = m.iter().map(|&(_, e)| v2_factorial(e)).sum();
                let m2 = bits.saturating_sub(v);
                if m1 <= m2 {
                    let r = signed_rep(&c, m1);
                    self.set(&m, r);
                    continue;
                }
                let r = signed_rep(&c, m2);
                self.set(&m, r);
                // Move c − r (a multiple of 2^m2) times the lower terms of (x)_κ.
                let moved = BitVec::bin_unchecked(BinOp::Sub, &c, &r);
                if moved.is_zero() {
                    continue;
                }
                let rows: Vec<Vec<BitVec>> = m.iter().map(|&(_, e)| stirling1(e, w)).collect();
                let mut idx: Vec<u32> = m.iter().map(|_| 1).collect();
                loop {
                    let is_top = idx.iter().zip(&m).all(|(&j, &(_, e))| j == e);
                    if !is_top {
                        let mut coef = BitVec::un_unchecked(UnOp::Neg, &moved);
                        let mut mono: Mono = Vec::with_capacity(m.len());
                        for (k, &(s, _)) in m.iter().enumerate() {
                            coef = mul(&coef, &rows[k][idx[k] as usize]);
                            mono.push((s, idx[k]));
                        }
                        self.add_term(mono, &coef);
                    }
                    // Next index vector, each in 1..=e.
                    let mut k = 0;
                    loop {
                        if k == idx.len() {
                            break;
                        }
                        if idx[k] < m[k].1 {
                            idx[k] += 1;
                            break;
                        }
                        idx[k] = 1;
                        k += 1;
                    }
                    if k == idx.len() {
                        break;
                    }
                }
            }
        }
    }

    /// Each unmasked symbol replaced by its masked symbols: `AND_S = Σ_c AND_S & M_c`.
    pub(crate) fn expand_full(&self, classes: &Classes) -> Poly {
        let w = self.w;
        if !self
            .terms
            .keys()
            .any(|m| m.iter().any(|(s, _)| s.class == FULL))
        {
            return self.clone();
        }
        let mut out = Poly::zero(w);
        for (m, c) in &self.terms {
            // The monomials of the expansion, built factor by factor.
            let kept: Mono = m.iter().copied().filter(|(s, _)| s.class != FULL).collect();
            let mut terms: Vec<(Mono, BitVec)> = vec![(kept, *c)];
            for &(s, e) in m.iter().filter(|(s, _)| s.class == FULL) {
                for _ in 0..e {
                    let mut next: Vec<(Mono, BitVec)> =
                        Vec::with_capacity(terms.len() * classes.len());
                    for (t, k) in &terms {
                        for cl in 0..classes.len() {
                            let sym = Sym {
                                set: s.set,
                                class: cl as u16,
                            };
                            next.push((mono_mul(t, &vec![(sym, 1)]), *k));
                        }
                    }
                    terms = next;
                }
            }
            for (t, k) in terms {
                out.add_term(t, &k);
            }
        }
        out
    }

    /// The same function with unmasked symbols wherever the classes allow: for each shape (a
    /// monomial with its classes erased), highest degree first, when subtracting `c` times the
    /// full expansion of the unmasked monomial (`c` its coefficient with every factor in class 0,
    /// which has every precision) leaves no term of that shape (modulo precision), the shape
    /// becomes that one unmasked term. Expansions over `limit` monomials are not tried.
    pub(crate) fn declass(&self, classes: &Classes, limit: usize) -> Poly {
        let w = self.w;
        if classes.len() <= 1 {
            return self.clone();
        }
        let shape = |m: &Mono| -> Vec<(u64, u32)> {
            let mut v: Vec<(u64, u32)> = Vec::new();
            for &(s, e) in m {
                match v.iter_mut().find(|(set, _)| *set == s.set) {
                    Some(x) => x.1 += e,
                    None => v.push((s.set, e)),
                }
            }
            v.sort_unstable();
            v
        };
        // Every monomial by its shape, including those the loop below adds (some may have
        // cancelled since: the part of a shape is what is still present).
        let mut by_shape: BTreeMap<Vec<(u64, u32)>, Vec<Mono>> = BTreeMap::new();
        for m in self.terms.keys().filter(|m| !m.is_empty()) {
            by_shape.entry(shape(m)).or_default().push(m.clone());
        }
        let mut shapes: Vec<Vec<(u64, u32)>> = self
            .terms
            .keys()
            .filter(|m| !m.is_empty() && m.iter().all(|(s, _)| s.class != FULL))
            .map(shape)
            .collect();
        shapes.sort_by(|a, b| {
            let da: u32 = a.iter().map(|x| x.1).sum();
            let db: u32 = b.iter().map(|x| x.1).sum();
            db.cmp(&da).then_with(|| a.cmp(b))
        });
        shapes.dedup();
        let mut rest = self.clone();
        let mut full = Poly::zero(w);
        for sh in shapes {
            let size = sh.iter().fold(1usize, |acc, &(_, e)| {
                acc.saturating_mul(classes.len().saturating_pow(e))
            });
            if size > limit {
                continue;
            }
            let rep: Mono = sh
                .iter()
                .map(|&(set, e)| (Sym { set, class: 0 }, e))
                .collect();
            let Some(c) = rest.terms.get(&rep).copied() else {
                continue;
            };
            let unmasked: Mono = sh
                .iter()
                .map(|&(set, e)| (Sym { set, class: FULL }, e))
                .collect();
            // Only the shape's own terms change: reduce their difference with the expansion
            // (exact reductions of a part are identities of the whole).
            let expansion = Poly::term(w, unmasked.clone(), &c).expand_full(classes);
            let part = Poly {
                w,
                terms: by_shape
                    .get(&sh)
                    .into_iter()
                    .flatten()
                    .filter_map(|m| rest.terms.get(m).map(|c| (m.clone(), *c)))
                    .collect(),
            };
            let mut diff = part.sub(&expansion);
            diff.reduce_core(classes);
            if diff.terms.keys().any(|m| !m.is_empty() && shape(m) == sh) {
                continue;
            }
            for m in part.terms.keys() {
                rest.terms.remove(m);
            }
            for (m, c) in &diff.terms {
                if !m.is_empty() {
                    by_shape.entry(shape(m)).or_default().push(m.clone());
                }
                rest.add_term(m.clone(), c);
            }
            full.add_term(unmasked, &c);
        }
        full.add(&rest)
    }

    fn set(&mut self, m: &Mono, c: BitVec) {
        if c.is_zero() {
            self.terms.remove(m);
        } else {
            self.terms.insert(m.clone(), c);
        }
    }
}

/// The inverse of an odd value mod 2^W (Newton's iteration).
pub(crate) fn odd_inverse(a: &BitVec) -> BitVec {
    let w = a.width();
    let two = BitVec::wrapping_from_u64(w, 2);
    let mut x = *a; // correct to 3 bits for odd a
    for _ in 0..10 {
        // x = x·(2 − a·x)
        let ax = mul(a, &x);
        x = mul(&x, &BitVec::bin_unchecked(BinOp::Sub, &two, &ax));
    }
    x
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A polynomial of up to `n` terms over three symbols, degree at most 3, from `seed`.
    fn random(w: Width, seed: &mut u64, n: usize) -> Poly {
        let mut next = || {
            *seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            *seed >> 33
        };
        let mut p = Poly::zero(w);
        for _ in 0..n {
            let mut m: Mono = Vec::new();
            for set in 1..4u64 {
                let e = (next() % 3) as u32;
                if e > 0 && degree(&m) + e <= 3 {
                    m.push((Sym { set, class: 0 }, e));
                }
            }
            p.add_term(m, &BitVec::wrapping_from_u64(w, next()));
        }
        p
    }

    #[test]
    fn exact_division_finds_the_quotient_and_nothing_else() {
        let mut seed = 7;
        for w in [Width::W8, Width::W64, Width::new(100).unwrap()] {
            for _ in 0..200 {
                let mut f = random(w, &mut seed, 4);
                let q = random(w, &mut seed, 6);
                let Some((lm, lc)) = f.leading().map(|(m, c)| (m.clone(), *c)) else {
                    continue;
                };
                // An odd leading coefficient: the quotient is unique and found.
                if !lc.bit(0).unwrap_or(false) {
                    f.add_term(lm, &BitVec::one(w));
                }
                let p = f.mul(&q);
                let mut budget = u64::MAX;
                assert_eq!(p.div_exact(&f, &mut budget), Ok(Some(q.clone())));
                // Too little budget: refused, not answered.
                if !p.is_zero() {
                    let mut none = p.len() as u64 - 1;
                    assert_eq!(p.div_exact(&f, &mut none), Err(()));
                }
                // Whatever it answers is exact.
                let r = p.add(&random(w, &mut seed, 2));
                let mut budget = u64::MAX;
                if let Ok(Some(q2)) = r.div_exact(&f, &mut budget) {
                    assert_eq!(f.mul(&q2), r);
                }
            }
        }
    }
}
