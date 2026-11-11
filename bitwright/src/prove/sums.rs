//! The sums of a question written one way on both of its sides ([`Config::shared_sums`]).
//!
//! The search does not see through sums: `(a + b) + c` against `a + (b + c)` at 21 bits costs
//! it a hundred thousand propagations, and arithmetic done in limbs is that question over and
//! over (a limb is the sum of its operands' digits and the carries below, its word the same
//! operands added at full width and sliced). So before a question is blasted, both sides are
//! read as linear forms and written again from them.
//!
//! A form is `k + Σ cᵢ·tᵢ` modulo `2^n`, `n` the bits read of it; a term is a slice
//! `x[lo, lo + len)`, zero-extended, of a value `x`.
//!
//! 1. Every `+ − neg not`, product by a constant and shift by a constant is flattened; a
//!    truncation, a mask, a left shift and an extension above a sum only say how many bits
//!    are read. Slices are pushed into what only moves bits (truncations, masks, shifts by
//!    constants, extensions, concatenations, ORs of disjoint values), so one digit spelled
//!    two ways is one term; overlapping slices of one value are cut at each other's ends,
//!    and adjacent ones under `c` and `c·2^len` are one slice.
//! 2. A slice of a sum is no term. Bits `[k, k + len)` of `F = G + 2^k·H`, `G` what `F` has
//!    below bit `k` (each term's bits below, under its coefficient modulo `2^k`), are
//!    `H + ⌊G / 2^k⌋` modulo `2^len`: the terms above, and one **carry** `⌊G / 2^k⌋`, a small
//!    number (the slice above bit `k` of the sum `G` built at its own width). The low bits
//!    of a sum read as a number are `G − 2^k·⌊G / 2^k⌋`.
//! 3. A comparison `lo_k(P) <u lo_k(Q)` is the carry of `Q + (P − Q)` out of `k` bits:
//!    `⌊G_P / 2^k⌋ − ⌊G_Q / 2^k⌋ − ⌊G_D / 2^k⌋ + (G_Q + G_D − G_P) / 2^k`, `D = P − Q`, the
//!    carries of the three low sums (a value that is no sum has none).
//!
//! So a limb (the digits of its operands, plus carries taken step by step) and its word's
//! slice (the same digits, plus the one carry of all the low digits) come to the same terms
//! whatever the order the handler added in, and what both sides hold cancels: `a == b` is
//! asked as `a − b == 0`, the terms left with a negative coefficient moved back to the other
//! side. What is left is written in one order (terms by the height of their values, then by
//! the context's canonical order), so that partial sums are prefixes of the sums they are
//! part of and the and-inverter graph has one circuit for both.
//!
//! Each step is an equality of the bits read at every value of the symbols (see the
//! functions), so the question written again is the question asked.

use crate::error::Error;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::{BinOp, BitVec, CmpOp, UnOp, Width};

/// The most terms a form may have: a sum of more is a value like any other.
const MAX_TERMS: usize = 96;

/// The most steps one question's forms may take; beyond, it is blasted as asked.
const MAX_WORK: u32 = 1 << 15;

/// The deepest the forms nest (a value below is taken as it is).
const MAX_DEPTH: u32 = 120;

fn ones(n: u16) -> u64 {
    if n >= 64 { u64::MAX } else { (1u64 << n) - 1 }
}

/// `c` modulo `2^k` as the representative in `[−2^(k−1), 2^(k−1))`.
fn centered(c: u64, k: u16) -> i64 {
    if k >= 64 {
        return c as i64;
    }
    let v = c & ones(k);
    if v >> (k - 1) != 0 {
        (v as i128 - (1i128 << k)) as i64
    } else {
        v as i64
    }
}

/// Bits `[lo, lo + len)` of `base`, zero-extended.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Atom {
    base: u32,
    lo: u16,
    len: u16,
}

/// A 64-bit form as a number: its constant, and what each bit `(value, bit)` counts.
type Number = (u64, Vec<((u32, u16), i128)>);

/// `konst + Σ coeff·atom` modulo `2^n`.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Form {
    n: u16,
    konst: u64,
    terms: Vec<(Atom, u64)>,
}

impl Form {
    fn zero(n: u16) -> Form {
        Form {
            n,
            konst: 0,
            terms: Vec::new(),
        }
    }

    /// Adds `k·o`. (`o` may be of fewer bits where `k·2^o.n` is 0 modulo `2^n`, and of
    /// more.)
    fn add(&mut self, o: &Form, k: u64) {
        let mask = ones(self.n);
        self.konst = self.konst.wrapping_add(o.konst.wrapping_mul(k)) & mask;
        self.terms
            .extend(o.terms.iter().map(|&(a, c)| (a, c.wrapping_mul(k) & mask)));
    }

    /// Each atom cut to the bits its coefficient reads; equal atoms merged; and nothing left
    /// with a coefficient of 0. Whether anything changed.
    fn merge(&mut self) -> bool {
        let (n, mask) = (self.n, ones(self.n));
        let mut changed = false;
        for (a, c) in &mut self.terms {
            *c &= mask;
            if *c != 0 {
                let read = n - c.trailing_zeros() as u16;
                if a.len > read {
                    a.len = read;
                    changed = true;
                }
            }
        }
        self.terms.sort_unstable_by_key(|t| t.0);
        let mut out: Vec<(Atom, u64)> = Vec::with_capacity(self.terms.len());
        for &(a, c) in &self.terms {
            match out.last_mut() {
                Some((b, k)) if *b == a => {
                    *k = k.wrapping_add(c) & mask;
                    changed = true;
                }
                _ => out.push((a, c)),
            }
        }
        out.retain(|(a, c)| *c != 0 && a.len != 0);
        changed |= out.len() != self.terms.len();
        self.terms = out;
        changed
    }

    /// The form in its one writing: atoms cut to the bits read, slices of one value that
    /// overlap cut at each other's ends (`c·x[lo, hi)` is `c·x[lo, m) + c·2^(m−lo)·x[m, hi)`),
    /// equal ones merged, and adjacent ones under `c` and `c·2^len` joined again.
    fn tidy(&mut self) {
        let mask = ones(self.n);
        self.konst &= mask;
        for _ in 0..64 {
            while self.merge() {}
            // Overlaps: the terms of one base are together, by their low bits.
            let mut cuts: Vec<(Atom, u64)> = Vec::new();
            let mut split = false;
            let mut i = 0;
            while i < self.terms.len() {
                let base = self.terms[i].0.base;
                let end = (i..self.terms.len())
                    .find(|&j| self.terms[j].0.base != base)
                    .unwrap_or(self.terms.len());
                let group = &self.terms[i..end];
                let overlap = group.windows(2).any(|p| p[1].0.lo < p[0].0.lo + p[0].0.len);
                if overlap {
                    let mut at: Vec<u16> = group
                        .iter()
                        .flat_map(|(a, _)| [a.lo, a.lo + a.len])
                        .collect();
                    at.sort_unstable();
                    at.dedup();
                    for &(a, c) in group {
                        let (from, to) = (a.lo, a.lo + a.len);
                        let inside = at.iter().copied().filter(|&p| p > from && p < to);
                        let mut s = from;
                        for p in inside.chain([to]) {
                            let c = (c << (s - from)) & mask;
                            cuts.push((
                                Atom {
                                    base,
                                    lo: s,
                                    len: p - s,
                                },
                                c,
                            ));
                            s = p;
                        }
                    }
                    split = true;
                } else {
                    cuts.extend_from_slice(group);
                }
                i = end;
            }
            if split {
                self.terms = cuts;
                while self.merge() {}
            }
            // Joins.
            let mut joined = false;
            let mut i = 0;
            while i < self.terms.len() {
                let (a, c) = self.terms[i];
                let next = (c << 1 << (a.len - 1)) & mask;
                let found = (i + 1..self.terms.len())
                    .take_while(|&j| self.terms[j].0.base == a.base)
                    .find(|&j| self.terms[j].0.lo == a.lo + a.len && self.terms[j].1 == next);
                match found {
                    Some(j) if next != 0 => {
                        self.terms[i].0.len += self.terms[j].0.len;
                        self.terms.remove(j);
                        joined = true;
                    }
                    _ => i += 1,
                }
            }
            if !joined {
                break;
            }
        }
    }
}

impl Form {
    /// The form as a number, for a 64-bit form read as one (its coefficients two's-complement
    /// numbers, as [`Norm::split`] leaves them): the constant, and what each bit of each
    /// value counts. `None` where that leaves 128 bits.
    fn number(&self) -> Option<Number> {
        let mut bits: Vec<((u32, u16), i128)> = Vec::new();
        for &(a, c) in &self.terms {
            for b in 0..a.len {
                bits.push(((a.base, a.lo + b), i128::from(c as i64) << b));
            }
        }
        bits.sort_unstable_by_key(|b| b.0);
        let mut out: Vec<((u32, u16), i128)> = Vec::with_capacity(bits.len());
        for (at, v) in bits {
            match out.last_mut() {
                Some((last, sum)) if *last == at => *sum = sum.checked_add(v)?,
                _ => out.push((at, v)),
            }
        }
        out.retain(|b| b.1 != 0);
        Some((self.konst, out))
    }

    /// [`tidy`](Self::tidy) for a 64-bit form read as a number: whether it is still that
    /// number. Tidying keeps a form modulo `2^n`, and a slice cut at another's end has its
    /// upper part under the coefficient times a power of two, which wraps modulo `2^64`
    /// where the coefficient is large (`c` near `2^43` cut at bit 21): the residue is kept
    /// and the number is another, of which a quotient by `2^k` says nothing.
    fn tidy_number(&mut self) -> bool {
        let before = self.number();
        self.tidy();
        before.is_some() && before == self.number()
    }
}

/// A carry read: the comparison is `lo_k(p) <u lo_k(q)`.
#[derive(Clone, Copy)]
struct Carry {
    p: u32,
    q: u32,
    k: u16,
}

struct Norm<'c> {
    cx: &'c mut Context,
    /// A node, and the node it is written as.
    norm: IdMap<u32, u32>,
    /// The form of the low `n` bits of a node (`node << 16 | n`): flattened and tidied, with
    /// slices of sums among its terms.
    forms: IdMap<u64, Form>,
    /// The same forms settled: over values that are no sums.
    settled: IdMap<u64, Form>,
    zeros: IdMap<u32, u64>,
    heights: IdMap<u32, u32>,
    /// The comparisons written, as carries.
    carries: IdMap<u32, Carry>,
    /// Values taken as they are: carries, and sums of too many terms.
    leaf: IdMap<u32, ()>,
    work: u32,
    depth: u32,
    over: bool,
}

/// What a form looks through.
fn linear(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    match n.op {
        OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Not => true,
        OpCode::Mul => cx.is_const(n.a) || cx.is_const(n.b),
        OpCode::Shl => cx
            .const_val(n.b)
            .and_then(|v| v.to_u64())
            .is_some_and(|c| c < u64::from(n.width)),
        _ => false,
    }
}

impl Norm<'_> {
    fn step(&mut self) -> Result<(), Error> {
        self.work += 1;
        if self.work > MAX_WORK {
            self.over = true;
            return Err(Error::Unsupported("the sums are too many".into()));
        }
        Ok(())
    }

    /// The low 64 bits of a constant.
    fn low(&self, i: u32) -> Option<u64> {
        self.cx.const_val(i).map(|v| v.limbs()[0])
    }

    /// Bits `[lo, lo + len)` of a constant (`len` at most 64).
    fn const_bits(&self, i: u32, lo: u16, len: u16) -> Option<u64> {
        let v = self.cx.const_val(i)?;
        let limbs = v.limbs();
        let (at, sh) = (usize::from(lo / 64), u32::from(lo % 64));
        let mut out = limbs.get(at).copied().unwrap_or(0) >> sh;
        if sh != 0 {
            out |= limbs.get(at + 1).copied().unwrap_or(0) << (64 - sh);
        }
        Some(out & ones(len))
    }

    /// Whether `x` is a mask of fields: an AND with a constant of at most two runs of ones
    /// (a limb's mask has one; a mask of scattered bits is no slicing).
    fn masked(&self, x: u32) -> bool {
        let n = self.cx.node(x);
        if n.op != OpCode::And {
            return false;
        }
        let c = if self.cx.is_const(n.b) { n.b } else { n.a };
        self.cx.const_val(c).is_some_and(|v| {
            let mut runs = 0;
            let mut last = 0u64;
            for &l in v.limbs() {
                runs += (l & !(l << 1 | last)).count_ones();
                last = l >> 63;
            }
            runs <= 2
        })
    }

    /// A constant shift count below the width.
    fn count(&self, i: u32, w: u16) -> Option<u16> {
        let v = self.cx.const_val(i)?.to_u64()?;
        (v < u64::from(w)).then_some(v as u16)
    }

    /// `x` as `y << c`: a shift by a constant, or a product by a power of two.
    fn shifted(&self, x: u32) -> Option<(u32, u16)> {
        let n = self.cx.node(x);
        match n.op {
            OpCode::Shl => Some((n.a, self.count(n.b, n.width)?)),
            OpCode::Mul if n.width <= 64 => {
                let (y, c) = if self.cx.is_const(n.b) {
                    (n.a, self.low(n.b)?)
                } else {
                    (n.b, self.low(n.a)?)
                };
                c.is_power_of_two()
                    .then(|| (y, c.trailing_zeros() as u16))
                    .filter(|&(_, c)| c < n.width)
            }
            _ => None,
        }
    }

    /// Bits of `x` known to be 0 (of at most 64-bit values; none known of wider ones).
    fn zeros(&mut self, x: u32) -> u64 {
        let n = self.cx.node(x);
        let w = n.width;
        if w > 64 {
            return 0;
        }
        if let Some(&z) = self.zeros.get(&x) {
            return z;
        }
        self.depth += 1;
        let deep = self.depth > MAX_DEPTH;
        let z = match n.op {
            _ if deep => 0,
            OpCode::Const => !self.low(x).unwrap_or(0),
            OpCode::Sym => self
                .cx
                .declared_at(x)
                .map_or(0, |k| k.known_zero().limbs()[0]),
            OpCode::Zext => self.zeros(n.a) | !ones(self.cx.wid(n.a)),
            OpCode::Extract if self.cx.wid(n.a) <= 64 => self.zeros(n.a) >> n.b,
            OpCode::Concat => {
                let wl = self.cx.wid(n.b);
                self.zeros(n.a) << wl | (self.zeros(n.b) & ones(wl))
            }
            OpCode::And => self.zeros(n.a) | self.zeros(n.b),
            OpCode::Or | OpCode::Xor => self.zeros(n.a) & self.zeros(n.b),
            OpCode::Select => self.zeros(n.b) & self.zeros(n.c),
            OpCode::LShr => match self.count(n.b, w) {
                Some(c) => (self.zeros(n.a) & ones(w)) >> c | !(ones(w) >> c),
                None => 0,
            },
            OpCode::Shl | OpCode::Mul => match self.shifted(x) {
                Some((y, c)) => self.zeros(y) << c | ones(c),
                None if n.op == OpCode::Mul => {
                    let low = |z: u64| ones(z.trailing_ones().min(64) as u16);
                    let (za, zb) = (self.zeros(n.a), self.zeros(n.b));
                    let both = (za.trailing_ones() + zb.trailing_ones()).min(64) as u16;
                    low(za) | low(zb) | ones(both)
                }
                None => 0,
            },
            OpCode::Add | OpCode::Sub => {
                let (za, zb) = (self.zeros(n.a), self.zeros(n.b));
                ones(za.trailing_ones().min(zb.trailing_ones()).min(64) as u16)
            }
            _ => 0,
        } & ones(w);
        self.depth -= 1;
        self.zeros.insert(x, z);
        z
    }

    fn height(&mut self, x: u32) -> u32 {
        if let Some(&h) = self.heights.get(&x) {
            return h;
        }
        let n = self.cx.node(x);
        let mut h = 0;
        for c in n.children() {
            h = h.max(self.height(c) + 1);
        }
        self.heights.insert(x, h);
        h
    }

    /// Whether `x` is a sum a form flattens.
    fn sum(&self, x: u32) -> bool {
        linear(self.cx, x) && !self.leaf.contains_key(&x)
    }

    /// Whether [`pieces`](Self::pieces) reads `x` as slices of other values (and so never as
    /// a term of itself).
    fn through(&mut self, x: u32) -> bool {
        if self.leaf.contains_key(&x) {
            return false;
        }
        let n = self.cx.node(x);
        match n.op {
            OpCode::Extract | OpCode::Zext | OpCode::Sext | OpCode::Concat => true,
            OpCode::LShr => self.count(n.b, n.width).is_some(),
            OpCode::And => self.masked(x),
            OpCode::Or | OpCode::Xor => {
                n.width <= 64
                    && (self.zeros(n.a) | self.zeros(n.b)) & ones(n.width) == ones(n.width)
            }
            _ => self.sum(x),
        }
    }

    /// The form of the low `n` bits of `x` (`n` at most 64 and at most the width of `x`):
    /// flattened and tidied, slices of sums among its terms.
    fn form(&mut self, x: u32, n: u16) -> Result<Form, Error> {
        let key = u64::from(x) << 16 | u64::from(n);
        if let Some(f) = self.forms.get(&key) {
            return Ok(f.clone());
        }
        self.step()?;
        self.depth += 1;
        let f = self.form_new(x, n);
        self.depth -= 1;
        let f = f?;
        self.forms.insert(key, f.clone());
        Ok(f)
    }

    /// `x` as a term of its own, whatever it is.
    fn opaque(&mut self, x: u32, n: u16) -> Form {
        self.leaf.insert(x, ());
        let mut f = Form::zero(n);
        f.terms.push((
            Atom {
                base: x,
                lo: 0,
                len: n,
            },
            1,
        ));
        f
    }

    fn form_new(&mut self, x: u32, n: u16) -> Result<Form, Error> {
        let node = self.cx.node(x);
        let mut f = Form::zero(n);
        if self.depth > MAX_DEPTH || self.leaf.contains_key(&x) {
            return Ok(self.opaque(x, n));
        }
        let minus = u64::MAX;
        match node.op {
            OpCode::Const => f.konst = self.low(x).unwrap_or(0) & ones(n),
            // Modulo 2^n the low n bits of a sum are the sum of its operands' low n bits.
            OpCode::Add | OpCode::Sub => {
                let (a, b) = (self.form(node.a, n)?, self.form(node.b, n)?);
                f.add(&a, 1);
                f.add(&b, if node.op == OpCode::Add { 1 } else { minus });
            }
            OpCode::Neg => f.add(&self.form(node.a, n)?, minus),
            // `~a` is `−a − 1`.
            OpCode::Not => {
                f.add(&self.form(node.a, n)?, minus);
                f.konst = f.konst.wrapping_sub(1);
            }
            OpCode::Mul if self.cx.is_const(node.b) || self.cx.is_const(node.a) => {
                let (y, c) = if self.cx.is_const(node.b) {
                    (node.a, node.b)
                } else {
                    (node.b, node.a)
                };
                let c = self.low(c).unwrap_or(0) & ones(n);
                // (Bits of the operand that the coefficient shifts out are not read.)
                let read = n - (c.trailing_zeros() as u16).min(n - 1);
                f.add(&self.form(y, read)?, c);
            }
            OpCode::Shl if self.count(node.b, node.width).is_some() => {
                let c = self.count(node.b, node.width).unwrap_or(0);
                if c < n {
                    f.add(&self.form(node.a, n - c)?, 1u64 << c);
                }
            }
            _ => self.pieces(x, 0, n, 0, &mut f)?,
        }
        self.joined(&mut f)?;
        if f.terms.len() > MAX_TERMS {
            return Ok(self.opaque(x, n));
        }
        Ok(f)
    }

    /// Adds `2^shift · x[lo, lo + len)` to `f` (the slice within `x`, and `shift + len` at
    /// most the form's bits): pushed through whatever only moves bits.
    fn pieces(&mut self, x: u32, lo: u16, len: u16, shift: u16, f: &mut Form) -> Result<(), Error> {
        if len == 0 {
            return Ok(());
        }
        self.step()?;
        let node = self.cx.node(x);
        let w = node.width;
        debug_assert!(lo + len <= w && shift + len <= f.n);
        let end = lo + len;
        if self.leaf.contains_key(&x) {
            f.terms.push((Atom { base: x, lo, len }, 1u64 << shift));
            return Ok(());
        }
        match node.op {
            OpCode::Const => {
                let v = self.const_bits(x, lo, len).unwrap_or(0);
                f.konst = f.konst.wrapping_add(v << shift) & ones(f.n);
                Ok(())
            }
            OpCode::Extract => self.pieces(node.a, lo + node.b as u16, len, shift, f),
            OpCode::Zext | OpCode::Sext => {
                let m = self.cx.wid(node.a);
                if lo < m {
                    self.pieces(node.a, lo, len.min(m - lo), shift, f)?;
                }
                if node.op == OpCode::Sext && end > m {
                    // The bits above are the sign's: `sign · (2^count − 1)` at their place.
                    let from = lo.max(m);
                    let mut sign = Form::zero(f.n);
                    self.pieces(node.a, m - 1, 1, 0, &mut sign)?;
                    f.add(&sign, ones(end - from) << (shift + from - lo));
                }
                Ok(())
            }
            OpCode::LShr if self.count(node.b, w).is_some() => {
                let c = self.count(node.b, w).unwrap_or(0);
                if lo + c < w {
                    self.pieces(node.a, lo + c, len.min(w - lo - c), shift, f)?;
                }
                Ok(())
            }
            OpCode::Shl | OpCode::Mul if self.shifted(x).is_some() => {
                let (y, c) = self.shifted(x).unwrap_or((x, 0));
                if end > c {
                    let from = lo.max(c);
                    self.pieces(y, from - c, end - from, shift + from - lo, f)?;
                }
                Ok(())
            }
            OpCode::And if self.masked(x) => {
                let (y, c) = if self.cx.is_const(node.b) {
                    (node.a, node.b)
                } else {
                    (node.b, node.a)
                };
                // Each run of ones of the mask is a slice of the operand.
                let mut m = self.const_bits(c, lo, len).unwrap_or(0);
                while m != 0 {
                    let s = m.trailing_zeros() as u16;
                    let l = (m >> s).trailing_ones() as u16;
                    self.pieces(y, lo + s, l, shift + s, f)?;
                    m &= !(ones(l) << s);
                }
                Ok(())
            }
            OpCode::Concat => {
                let wl = self.cx.wid(node.b);
                if lo < wl {
                    self.pieces(node.b, lo, len.min(wl - lo), shift, f)?;
                }
                if end > wl {
                    let from = lo.max(wl);
                    self.pieces(node.a, from - wl, end - from, shift + from - lo, f)?;
                }
                Ok(())
            }
            // No bit is 1 in both: the OR, the XOR and the sum are the two side by side.
            OpCode::Or | OpCode::Xor | OpCode::Add
                if w <= 64 && (self.zeros(node.a) | self.zeros(node.b)) & ones(w) == ones(w) =>
            {
                self.pieces(node.a, lo, len, shift, f)?;
                self.pieces(node.b, lo, len, shift, f)
            }
            // The low bits of a sum, read modulo 2^len (nothing of the form is above them).
            _ if lo == 0 && shift + len == f.n && self.sum(x) => {
                let g = self.form(x, len)?;
                f.add(&g, 1u64 << shift);
                Ok(())
            }
            // A slice of a sum, for now ([`settle`](Self::settle) takes it apart).
            _ if self.sum(x) && end <= 64 => {
                f.terms.push((Atom { base: x, lo, len }, 1u64 << shift));
                Ok(())
            }
            _ => {
                let base = if self.depth > MAX_DEPTH {
                    x
                } else {
                    self.norm(x)?
                };
                if base != x {
                    // (Written again it may be a slice, or a constant: `base` is its own
                    // writing, so this ends.)
                    return self.pieces(base, lo, len, shift, f);
                }
                f.terms.push((Atom { base, lo, len }, 1u64 << shift));
                Ok(())
            }
        }
    }

    /// `f` tidied; a term that is the whole of a sum (its low bits, nothing of the form
    /// above them) taken as that sum's terms; and adjacent slices of two sums that are one
    /// sum below the upper slice's end joined into a slice of the upper one.
    fn joined(&mut self, f: &mut Form) -> Result<(), Error> {
        let mask = ones(f.n);
        'again: for _ in 0..32 {
            f.tidy();
            let whole = f.terms.iter().position(|&(a, c)| {
                a.lo == 0 && a.len + c.trailing_zeros() as u16 == f.n && self.sum(a.base)
            });
            if let Some(i) = whole {
                let (a, c) = f.terms.remove(i);
                let g = self.form(a.base, a.len)?;
                f.add(&g, c);
                continue;
            }
            for i in 0..f.terms.len() {
                let (a, c) = f.terms[i];
                if !self.sum(a.base) {
                    continue;
                }
                let (m, next) = (a.lo + a.len, (c << 1 << (a.len - 1)) & mask);
                for j in 0..f.terms.len() {
                    let (b, k) = f.terms[j];
                    if b.lo != m || k != next || k == 0 || b.base == a.base || !self.sum(b.base) {
                        continue;
                    }
                    if self.form(a.base, m)? == self.form(b.base, m)? {
                        f.terms[i].0 = Atom {
                            base: b.base,
                            lo: a.lo,
                            len: a.len + b.len,
                        };
                        f.terms.remove(j);
                        continue 'again;
                    }
                }
            }
            break;
        }
        Ok(())
    }

    /// The settled form of the low `n` bits of `x`.
    fn settled(&mut self, x: u32, n: u16) -> Result<Form, Error> {
        let key = u64::from(x) << 16 | u64::from(n);
        if let Some(f) = self.settled.get(&key) {
            return Ok(f.clone());
        }
        let mut f = self.form(x, n)?;
        self.depth += 1;
        let r = self.settle(&mut f);
        self.depth -= 1;
        r?;
        self.settled.insert(key, f.clone());
        Ok(f)
    }

    /// `f = g + 2^k·h` (as numbers, modulo `2^f.n`): `g` what `f` has below bit `k`, each
    /// term's bits below under its coefficient's representative in `[−2^(k−1), 2^(k−1))`, the
    /// constant's in `[0, 2^k)`; both as 64-bit forms (`g` a number, not a residue). `None`
    /// where `g` cannot be written as one (see [`Form::tidy_number`]).
    fn split(&self, f: &Form, k: u16) -> Option<(Form, Form)> {
        let (mut g, mut h) = (Form::zero(64), Form::zero(64));
        let lowc = f.konst & ones(k);
        g.konst = lowc;
        h.konst = if k >= 64 { 0 } else { f.konst >> k };
        let push = |g: &mut Form, h: &mut Form, t: Atom, c: u64| {
            // (`c` a 64-bit two's-complement number here.)
            let z = c.trailing_zeros() as u16;
            if c == 0 {
                return;
            }
            if z >= k {
                h.terms.push((t, ((c as i64) >> k) as u64));
                return;
            }
            let keep = k - z;
            let mut t = t;
            if t.len > keep {
                let up = Atom {
                    base: t.base,
                    lo: t.lo + keep,
                    len: t.len - keep,
                };
                h.terms.push((up, ((c as i64) >> z) as u64));
                t.len = keep;
            }
            let low = centered(c, k);
            let over = ((c as i64 as i128 - i128::from(low)) >> k) as i64;
            if over != 0 {
                h.terms.push((t, over as u64));
            }
            g.terms.push((t, low as u64));
        };
        for &(t, c) in &f.terms {
            // (The coefficient as the number it is modulo 2^n, sign-extended: any
            // representative does, and this one keeps `−1` small.)
            push(&mut g, &mut h, t, centered(c, f.n) as u64);
        }
        // Merging may leave a coefficient out of range again.
        for _ in 0..8 {
            if !g.tidy_number() {
                return None;
            }
            let terms = core::mem::take(&mut g.terms);
            let mut moved = false;
            for (t, c) in terms {
                let before = h.terms.len();
                push(&mut g, &mut h, t, c);
                moved |= h.terms.len() != before;
            }
            if !moved {
                break;
            }
        }
        if !g.tidy_number() {
            return None;
        }
        h.tidy();
        Some((g, h))
    }

    /// `⌊g / 2^k⌋` for a sum `g` of low terms (a number, as [`split`](Self::split) leaves
    /// it, over values that are no sums): a 64-bit form over the carry's own node, the slice
    /// above bit `k` of `g` built at the width its range needs. `None` where that is more
    /// than 64 bits.
    fn carry_of(&mut self, g: &Form, k: u16) -> Result<Option<Form>, Error> {
        let mut out = Form::zero(64);
        // A common factor 2^t: `⌊2^t·g' / 2^k⌋` is `⌊g' / 2^(k−t)⌋`.
        let t = g
            .terms
            .iter()
            .map(|t| t.1)
            .chain((g.konst != 0).then_some(g.konst))
            .map(|c| c.trailing_zeros() as u16)
            .min()
            .unwrap_or(64)
            .min(k);
        let k = k - t;
        if k == 0 {
            // (All of it is above.)
            out.add(g, 1);
            out.konst = ((out.konst as i64) >> t) as u64;
            out.terms
                .iter_mut()
                .for_each(|c| c.1 = ((c.1 as i64) >> t) as u64);
            return Ok(Some(out));
        }
        let mut low = Form::zero(64);
        low.konst = g.konst >> t;
        low.terms
            .extend(g.terms.iter().map(|&(a, c)| (a, ((c as i64) >> t) as u64)));
        // The range of the sum, and of its carry.
        let (mut min, mut max) = (i128::from(low.konst), i128::from(low.konst));
        for &(a, c) in &low.terms {
            let top = i128::from(c as i64) * i128::from(ones(a.len));
            let sum = if top < 0 {
                min.checked_add(top).map(|s| min = s)
            } else {
                max.checked_add(top).map(|s| max = s)
            };
            if sum.is_none() {
                return Ok(None);
            }
        }
        let (cmin, cmax) = (min >> k, max >> k);
        if cmin == cmax {
            out.konst = cmin as i64 as u64;
            return Ok(Some(out));
        }
        let signed = cmin < 0;
        let m = if signed {
            (1..=64u16)
                .find(|&m| -(1i128 << (m - 1)) <= cmin && cmax < (1i128 << (m - 1)))
                .unwrap_or(65)
        } else {
            (128 - cmax.leading_zeros()) as u16
        };
        // (The sum is built at up to 127 bits: a 64-bit word's low digits under 64-bit
        // coefficients.)
        if m > 64 || k + m > 127 {
            return Ok(None);
        }
        low.n = k + m;
        low.konst &= ones(low.n);
        low.terms.iter_mut().for_each(|c| c.1 &= ones(low.n));
        let sum = self.built(&low)?;
        let carry = self.cx.c_extract(sum, k, m)?;
        if let Some(v) = self.low(carry) {
            out.konst = if signed { centered(v, m) as u64 } else { v };
            return Ok(Some(out));
        }
        self.leaf.insert(carry, ());
        self.norm.insert(carry, carry);
        out.terms.push((
            Atom {
                base: carry,
                lo: 0,
                len: m,
            },
            1,
        ));
        if signed {
            // (Sign-extended: its top bit counts `−2^(m−1)`.)
            out.terms.push((
                Atom {
                    base: carry,
                    lo: m - 1,
                    len: 1,
                },
                (1u64 << m).wrapping_neg(),
            ));
        }
        Ok(Some(out))
    }

    /// The slice `t` of a sum, read on `read` bits (at least its length: zero-extended
    /// where more), over values that are no sums: with `F = G + 2^k·H` the sum's form below
    /// the slice's end ([`split`](Self::split) at the slice's low bit `k`), the slice is
    /// `H + ⌊G / 2^k⌋` modulo `2^len`; and a number `Z` modulo `2^len`, zero-extended, is
    /// `Z' − 2^len·⌊Z' / 2^len⌋`, `Z'` its terms' low `len` bits. `None` where a carry is
    /// too wide.
    fn slice(&mut self, t: Atom, read: u16) -> Result<Option<Form>, Error> {
        let end = t.lo + t.len;
        let f = self.settled(t.base, end)?;
        let mut z = Form::zero(t.len);
        if t.lo == 0 {
            z = f;
        } else {
            let Some((g, h)) = self.split(&f, t.lo) else {
                return Ok(None);
            };
            let Some(c) = self.carry_of(&g, t.lo)? else {
                return Ok(None);
            };
            z.add(&h, 1);
            z.add(&c, 1);
            z.tidy();
        }
        if read <= t.len {
            return Ok(Some(z));
        }
        let Some((g, _)) = self.split(&z, t.len) else {
            return Ok(None);
        };
        let Some(c) = self.carry_of(&g, t.len)? else {
            return Ok(None);
        };
        let mut out = Form::zero(64);
        out.add(&g, 1);
        out.add(&c, (1u64 << t.len).wrapping_neg());
        Ok(Some(out))
    }

    /// The carry `lo_k(p) <u lo_k(q)` as a 64-bit form, a number: with `d = p − q`,
    /// `lo_k(q) + lo_k(d)` is `lo_k(p)` or `2^k` more, which is the comparison; and each low
    /// digit is `G − 2^k·⌊G / 2^k⌋` of its own low sum `G`, so the carry is
    /// `⌊G_p / 2^k⌋ − ⌊G_q / 2^k⌋ − ⌊G_d / 2^k⌋ + (G_q + G_d − G_p) / 2^k`, the last an exact
    /// quotient (the three low sums agree modulo `2^k` term by term).
    fn carry(&mut self, c: Carry) -> Result<Option<Form>, Error> {
        let Carry { p, q, k } = c;
        if k >= 64 {
            return Ok(None);
        }
        let side = |s: &mut Self, x: u32| -> Result<Form, Error> {
            if s.cx.is_const(x) {
                let mut f = Form::zero(k);
                f.konst = s.low(x).unwrap_or(0) & ones(k);
                return Ok(f);
            }
            s.settled(x, k)
        };
        let (fp, fq) = (side(self, p)?, side(self, q)?);
        let mut fd = fp.clone();
        fd.add(&fq, u64::MAX);
        fd.tidy();
        let (Some((gp, _)), Some((gq, _)), Some((gd, _))) =
            (self.split(&fp, k), self.split(&fq, k), self.split(&fd, k))
        else {
            return Ok(None);
        };
        // The exact quotient is of the number `G_q + G_d − G_p`, so it is taken of the number:
        // what each bit of each value counts in the three, added up in 128 bits. (As a
        // 64-bit form the sum is only kept modulo `2^64`: a slice cut at another's end has
        // its upper part under the coefficient times a power of two, and with a coefficient
        // near `2^43` cut at bit 21 that wraps; the quotient of what is left by `2^k` is then
        // off by a multiple of `2^(64 − k)`, which a limb read on more bits than that sees.)
        let mut out = Form::zero(64);
        let (Some(np), Some(nq), Some(nd)) = (gp.number(), gq.number(), gd.number()) else {
            return Ok(None);
        };
        let exact = |c: i128| c.trailing_zeros() >= u32::from(k);
        let konst = i128::from(nq.0) + i128::from(nd.0) - i128::from(np.0);
        if !exact(konst) {
            return Ok(None);
        }
        out.konst = (konst >> k) as u64;
        let mut bits: Vec<((u32, u16), i128)> = Vec::new();
        bits.extend(nq.1.iter().chain(&nd.1).copied());
        bits.extend(np.1.iter().map(|&(at, v)| (at, -v)));
        bits.sort_unstable_by_key(|b| b.0);
        let mut i = 0;
        while i < bits.len() {
            let (at, mut sum) = bits[i];
            i += 1;
            while i < bits.len() && bits[i].0 == at {
                let Some(s) = sum.checked_add(bits[i].1) else {
                    return Ok(None);
                };
                sum = s;
                i += 1;
            }
            if !exact(sum) {
                return Ok(None);
            }
            // (Kept modulo `2^64` from here: the carry is added to forms of at most 64 bits.)
            let c = (sum >> k) as u64;
            if c != 0 {
                let atom = Atom {
                    base: at.0,
                    lo: at.1,
                    len: 1,
                };
                out.terms.push((atom, c));
            }
        }
        // (Bits under `c`, `2c`, `4c` are one slice again.)
        out.tidy();

        for (g, sign) in [(gp, 1), (gq, u64::MAX), (gd, u64::MAX)] {
            let Some(c) = self.carry_of(&g, k)? else {
                return Ok(None);
            };
            out.add(&c, sign);
        }
        out.tidy();
        Ok(Some(out))
    }

    /// `f` over values that are no sums: its slices of sums taken apart
    /// ([`slice`](Self::slice)), and its comparisons as carries ([`carry`](Self::carry))
    /// where that leaves no more terms.
    fn settle(&mut self, f: &mut Form) -> Result<(), Error> {
        let mut refused: Vec<u32> = Vec::new();
        'again: for _ in 0..256 {
            self.joined(f)?;
            self.step()?;
            if let Some(i) = f.terms.iter().position(|t| self.sum(t.0.base)) {
                let (t, c) = f.terms.remove(i);
                let read = f.n - c.trailing_zeros() as u16;
                let fits = t.lo + t.len <= 64 && f.terms.len() < MAX_TERMS;
                let apart = if fits && self.depth <= MAX_DEPTH {
                    self.depth += 1;
                    let r = self.slice(t, read);
                    self.depth -= 1;
                    r?
                } else {
                    None
                };
                match apart {
                    Some(g) => f.add(&g, c),
                    None => {
                        // As it is: a value like any other.
                        let e = self.cx.c_extract(t.base, t.lo, t.len)?;
                        self.leaf.insert(e, ());
                        self.norm.insert(e, e);
                        f.terms.push((
                            Atom {
                                base: e,
                                lo: 0,
                                len: t.len,
                            },
                            c,
                        ));
                    }
                }
                continue;
            }
            for i in 0..f.terms.len() {
                let (a, c) = f.terms[i];
                if self.cx.wid(a.base) != 1 || refused.contains(&a.base) {
                    continue;
                }
                let Some(&carry) = self.carries.get(&a.base) else {
                    continue;
                };
                self.depth += 1;
                let r = if self.depth <= MAX_DEPTH {
                    self.carry(carry)
                } else {
                    Ok(None)
                };
                self.depth -= 1;
                let Some(high) = r? else {
                    refused.push(a.base);
                    continue;
                };
                let mut g = f.clone();
                g.terms.remove(i);
                g.add(&high, c);
                g.tidy();
                if g.terms.len() <= f.terms.len() {
                    *f = g;
                    continue 'again;
                }
                refused.push(a.base);
            }
            break;
        }
        Ok(())
    }

    /// `x` written again: its sums from their forms, anything else over its operands written
    /// again.
    fn norm(&mut self, x: u32) -> Result<u32, Error> {
        if let Some(&y) = self.norm.get(&x) {
            return Ok(y);
        }
        self.step()?;
        let node = self.cx.node(x);
        let w = node.width;
        self.depth += 1;
        let y = match node.op {
            OpCode::Const | OpCode::Sym => Ok(x),
            _ if self.depth > MAX_DEPTH => Ok(x),
            _ if (2..=64).contains(&w) && self.through(x) => match self.settled(x, w) {
                Ok(f) => self.built(&f),
                Err(e) => Err(e),
            },
            _ => self.rebuilt(x),
        };
        self.depth -= 1;
        let y = y?;
        self.norm.insert(x, y);
        self.norm.entry(y).or_insert(y);
        Ok(y)
    }

    /// `x` over its operands written again.
    fn rebuilt(&mut self, x: u32) -> Result<u32, Error> {
        let node = self.cx.node(x);
        let mut k = [0u32; 3];
        let mut same = true;
        for (i, c) in node.children().enumerate() {
            k[i] = self.norm(c)?;
            same &= k[i] == c;
        }
        let y = if same {
            x
        } else if let Some(op) = node.op.as_un() {
            self.cx.c_un(op, k[0])?
        } else if let Some(op) = node.op.as_bin() {
            self.cx.c_bin(op, k[0], k[1])?
        } else if let Some(op) = node.op.as_cmp() {
            self.cx.c_cmp(op, k[0], k[1])?
        } else {
            match node.op {
                OpCode::Zext => self.cx.c_zext(k[0], node.width)?,
                OpCode::Sext => self.cx.c_sext(k[0], node.width)?,
                OpCode::Extract => self.cx.c_extract(k[0], node.b as u16, node.width)?,
                OpCode::Concat => self.cx.c_concat(k[0], k[1])?,
                OpCode::Select => self.cx.c_select(k[0], k[1], k[2])?,
                _ => x,
            }
        };
        if node.op == OpCode::Ult && self.cx.node(y).op == OpCode::Ult {
            // The carry it is, read off the comparison as it was asked: the sides' low
            // digits, and the words they are the digits of.
            let ((p, kp), (q, kq)) = (self.low_of(node.a), self.low_of(node.b));
            let (cp, cq) = (self.cx.is_const(p), self.cx.is_const(q));
            // (A constant side is its own digit.)
            let fits = |s: &Self, c: u32, k: u16| s.low(c).is_some_and(|v| k >= 64 || v >> k == 0);
            let read = match (cp, cq) {
                (true, true) => None,
                (true, false) => fits(self, p, kq).then_some(kq),
                (false, true) => fits(self, q, kp).then_some(kp),
                (false, false) => (kp == kq).then_some(kp),
            };
            if let Some(k) = read {
                self.carries.insert(y, Carry { p, q, k });
            }
        }
        Ok(y)
    }

    /// `x` as the low `k` bits of a value, zero-extended: the value and `k`.
    fn low_of(&self, mut x: u32) -> (u32, u16) {
        let mut k = self.cx.wid(x);
        loop {
            let n = self.cx.node(x);
            match n.op {
                OpCode::Zext => {
                    x = n.a;
                    k = k.min(self.cx.wid(x));
                }
                OpCode::Extract if n.b == 0 => x = n.a,
                OpCode::And if n.width <= 64 && self.cx.is_const(n.b) => {
                    let m = self.low(n.b).unwrap_or(0);
                    if m & m.wrapping_add(1) != 0 || m == 0 {
                        return (x, k);
                    }
                    k = k.min(m.trailing_ones() as u16);
                    x = n.a;
                }
                _ => return (x, k),
            }
        }
    }

    /// The node of a settled form: its terms in one order, by the height of their values
    /// (what a sum is of comes before what is computed from it), then the context's canonical
    /// order, then the slice; added and subtracted in that order from the first that is
    /// added, the constant last.
    fn built(&mut self, f: &Form) -> Result<u32, Error> {
        let n = f.n;
        let mask = ones(n);
        let mut terms: Vec<(u32, Atom, u64)> = Vec::with_capacity(f.terms.len());
        for &(a, c) in &f.terms {
            terms.push((self.height(a.base), a, c));
        }
        let cx = &*self.cx;
        terms.sort_by(|x, y| {
            x.0.cmp(&y.0)
                .then_with(|| cx.order(x.1.base, y.1.base))
                .then_with(|| (x.1.lo, x.1.len).cmp(&(y.1.lo, y.1.len)))
        });
        let width = Width::new(n)?;
        let half = 1u64 << (n - 1).min(63);
        // (A coefficient of the top bit alone is its own negation: added. Above 64 bits the
        // coefficients are 64-bit numbers.)
        let negative = |c: u64| if n > 64 { (c as i64) < 0 } else { c > half };
        let first = terms.iter().position(|t| !negative(t.2));
        let mut acc: Option<u32> = None;
        let order = first
            .into_iter()
            .chain((0..terms.len()).filter(|&i| Some(i) != first));
        for i in order {
            let (_, a, c) = terms[i];
            let mut e = a.base;
            if a.lo != 0 || a.len != self.cx.wid(e) {
                e = self.cx.c_extract(e, a.lo, a.len)?;
            }
            if a.len < n {
                e = self.cx.c_zext(e, n)?;
            } else if a.len > n {
                e = self.cx.c_extract(e, 0, n)?;
            }
            let neg = negative(c);
            let mag = if neg { c.wrapping_neg() & mask } else { c };
            if mag != 1 {
                e = if mag.is_power_of_two() {
                    let by = u64::from(mag.trailing_zeros());
                    let k = self.cx.mk_const(&BitVec::wrapping_from_u64(width, by))?;
                    self.cx.c_bin(BinOp::Shl, e, k)?
                } else {
                    let k = self.cx.mk_const(&BitVec::wrapping_from_u64(width, mag))?;
                    self.cx.c_bin(BinOp::Mul, e, k)?
                };
            }
            acc = Some(match acc {
                None if neg => self.cx.c_un(UnOp::Neg, e)?,
                None => e,
                Some(s) if neg => self.cx.c_bin(BinOp::Sub, s, e)?,
                Some(s) => self.cx.c_bin(BinOp::Add, s, e)?,
            });
        }
        let k = self
            .cx
            .mk_const(&BitVec::wrapping_from_u64(width, f.konst & mask))?;
        Ok(match acc {
            None => k,
            Some(s) if f.konst & mask == 0 => s,
            Some(s) => self.cx.c_bin(BinOp::Add, s, k)?,
        })
    }
}

/// The 1-bit `goal` with its sums written one way (see the module): a node equal to it at
/// every value of its symbols. An equality's two sides are read together: what both hold
/// cancels, and where everything does the answer is the constant.
pub(crate) fn shared(cx: &mut Context, goal: u32) -> Result<u32, Error> {
    let node = cx.node(goal);
    let mut s = Norm {
        cx,
        norm: IdMap::default(),
        forms: IdMap::default(),
        settled: IdMap::default(),
        zeros: IdMap::default(),
        heights: IdMap::default(),
        carries: IdMap::default(),
        leaf: IdMap::default(),
        work: 0,
        depth: 0,
        over: false,
    };
    let out = (|| -> Result<u32, Error> {
        if node.op != OpCode::Eq || s.cx.wid(node.a) > 64 {
            return s.norm(goal);
        }
        let n = s.cx.wid(node.a);
        let (mut fa, fb) = (s.form(node.a, n)?, s.form(node.b, n)?);
        // `a == b` is `a − b == 0`; then what is subtracted goes back to the other side.
        fa.add(&fb, u64::MAX);
        s.settle(&mut fa)?;
        let half = 1u64 << (n - 1);
        let (mut l, mut r) = (Form::zero(n), Form::zero(n));
        l.konst = fa.konst;
        for &(t, c) in &fa.terms {
            if c > half {
                r.terms.push((t, c.wrapping_neg() & ones(n)));
            } else {
                l.terms.push((t, c));
            }
        }
        let (l, r) = (s.built(&l)?, s.built(&r)?);
        s.cx.c_cmp(CmpOp::Eq, l, r)
    })();
    match out {
        Ok(g) => Ok(g),
        // (Too large to read: as asked.)
        Err(_) if s.over => Ok(goal),
        Err(e) => Err(e),
    }
}
