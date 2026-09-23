//! Rendering normal forms as expressions. Candidates are built into one builder with local
//! interning (equal subterms are one node), costed by the nodes reachable from their root, and
//! the cheapest is kept: by node count, then by an operator-weighted size, then by structure.

use std::collections::{BTreeMap, HashMap};

use super::bits::{self, Bits, anf, mobius, table8};
use super::classes::Classes;
use super::poly::{Mono, Poly, Sym};
use crate::engine::pass::bitwise::{T, min_forms};
use crate::facts::known::{bv_and, bv_not, bv_or, count_ones, trailing_zeros};
use crate::mba::expr::{MNode, MOp, MbaExpr};
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
struct BNode {
    op: MOp,
    w: Width,
    args: [u32; 2],
}

/// Nodes with local interning.
#[derive(Clone, Debug)]
pub(crate) struct Builder {
    vars: Vec<Width>,
    nodes: Vec<BNode>,
    memo: HashMap<BNode, u32>,
}

/// A candidate's cost: nodes, then operator weight.
pub(crate) type Cost = (u32, u32);

fn weight(op: &MOp) -> u32 {
    match op {
        MOp::Var(_) => 0,
        MOp::Mul => 4,
        _ => 1,
    }
}

fn commutative(op: &MOp) -> bool {
    matches!(op, MOp::Add | MOp::Mul | MOp::And | MOp::Or | MOp::Xor)
}

impl Builder {
    pub(crate) fn new(vars: Vec<Width>) -> Builder {
        Builder {
            vars,
            nodes: Vec::new(),
            memo: HashMap::new(),
        }
    }

    fn intern(&mut self, n: BNode) -> u32 {
        if let Some(&i) = self.memo.get(&n) {
            return i;
        }
        self.nodes.push(n);
        let i = self.nodes.len() as u32 - 1;
        self.memo.insert(n, i);
        i
    }

    pub(crate) fn width(&self, n: u32) -> Width {
        self.nodes[n as usize].w
    }

    fn cval(&self, n: u32) -> Option<BitVec> {
        match self.nodes[n as usize].op {
            MOp::Const(v) => Some(v),
            _ => None,
        }
    }

    pub(crate) fn var(&mut self, v: u32) -> u32 {
        let w = self.vars[v as usize];
        self.intern(BNode {
            op: MOp::Var(v),
            w,
            args: [0; 2],
        })
    }

    pub(crate) fn konst(&mut self, c: &BitVec) -> u32 {
        self.intern(BNode {
            op: MOp::Const(*c),
            w: c.width(),
            args: [0; 2],
        })
    }

    /// `op a` (`Neg`, `Not`, `Shl(k)`, `LShr(k)`), with the obvious identities.
    pub(crate) fn un(&mut self, op: MOp, a: u32) -> u32 {
        let w = self.width(a);
        let na = self.nodes[a as usize];
        match op {
            MOp::Neg | MOp::Not if na.op == op => return na.args[0],
            MOp::Shl(0) | MOp::LShr(0) => return a,
            _ => {}
        }
        if let Some(v) = self.cval(a) {
            let r = match op {
                MOp::Neg => BitVec::un_unchecked(UnOp::Neg, &v),
                MOp::Not => BitVec::un_unchecked(UnOp::Not, &v),
                MOp::Shl(k) => crate::facts::known::bv_shl(&v, u32::from(k)),
                MOp::LShr(k) => crate::facts::known::bv_lshr(&v, u32::from(k)),
                _ => v,
            };
            return self.konst(&r);
        }
        self.intern(BNode {
            op,
            w,
            args: [a, 0],
        })
    }

    /// `a op b`, with the obvious identities.
    pub(crate) fn bin(&mut self, op: MOp, a: u32, b: u32) -> u32 {
        let w = self.width(a);
        let (ca, cb) = (self.cval(a), self.cval(b));
        if let (Some(x), Some(y)) = (ca, cb) {
            let r = match op {
                MOp::Add => BinOp::Add,
                MOp::Sub => BinOp::Sub,
                MOp::Mul => BinOp::Mul,
                MOp::And => BinOp::And,
                MOp::Or => BinOp::Or,
                _ => BinOp::Xor,
            };
            let v = BitVec::bin_unchecked(r, &x, &y);
            return self.konst(&v);
        }
        let zero = |v: &Option<BitVec>| matches!(v, Some(x) if x.is_zero());
        let ones = |v: &Option<BitVec>| matches!(v, Some(x) if x.is_ones());
        let one = |v: &Option<BitVec>| matches!(v, Some(x) if *x == BitVec::one(w));
        match op {
            MOp::Add | MOp::Or | MOp::Xor if zero(&cb) => return a,
            MOp::Add | MOp::Or | MOp::Xor if zero(&ca) => return b,
            MOp::Sub if zero(&cb) => return a,
            MOp::Sub if zero(&ca) => return self.un(MOp::Neg, b),
            MOp::Mul if one(&cb) => return a,
            MOp::Mul if one(&ca) => return b,
            MOp::Mul | MOp::And if zero(&ca) || zero(&cb) => return self.konst(&BitVec::zero(w)),
            MOp::And if ones(&cb) => return a,
            MOp::And if ones(&ca) => return b,
            MOp::Or if ones(&ca) || ones(&cb) => return self.konst(&BitVec::ones(w)),
            MOp::Xor if ones(&cb) => return self.un(MOp::Not, a),
            MOp::Xor if ones(&ca) => return self.un(MOp::Not, b),
            MOp::And | MOp::Or if a == b => return a,
            MOp::Xor | MOp::Sub if a == b => return self.konst(&BitVec::zero(w)),
            _ => {}
        }
        let (a, b) = if commutative(&op) && a > b {
            (b, a)
        } else {
            (a, b)
        };
        self.intern(BNode {
            op,
            w,
            args: [a, b],
        })
    }

    /// A cast of `a` to width `w`.
    pub(crate) fn cast(&mut self, op: MOp, a: u32, w: Width) -> u32 {
        self.intern(BNode {
            op,
            w,
            args: [a, 0],
        })
    }

    /// Copies `m`'s nodes (those its root uses); its root.
    pub(crate) fn import(&mut self, m: &MbaExpr) -> Option<u32> {
        let mut map: Vec<u32> = Vec::with_capacity(m.nodes().len());
        for n in m.nodes() {
            let a = |k: usize| map[n.args[k] as usize];
            let id = match n.op {
                MOp::Const(v) => self.konst(&v),
                MOp::Var(v) => self.var(v),
                MOp::Zext | MOp::Sext | MOp::Trunc => self.cast(n.op, a(0), n.width),
                op if op.arity() == 1 => self.un(op, a(0)),
                op => self.bin(op, a(0), a(1)),
            };
            map.push(id);
        }
        map.last().copied()
    }

    /// The nodes `root` uses, operands first.
    fn reach(&self, root: u32) -> Vec<u32> {
        let mut seen = vec![false; self.nodes.len()];
        let mut out = Vec::new();
        let mut stack = vec![(root, false)];
        while let Some((i, done)) = stack.pop() {
            if done {
                out.push(i);
                continue;
            }
            if seen[i as usize] {
                continue;
            }
            seen[i as usize] = true;
            stack.push((i, true));
            let n = self.nodes[i as usize];
            for &k in n.args[..n.op.arity()].iter().rev() {
                stack.push((k, false));
            }
        }
        out
    }

    /// The cost of the candidate rooted at `root`.
    pub(crate) fn cost(&self, root: u32) -> Cost {
        let r = self.reach(root);
        let weight: u32 = r.iter().map(|&i| weight(&self.nodes[i as usize].op)).sum();
        (r.len() as u32, weight)
    }

    /// The candidate rooted at `root` as an expression.
    pub(crate) fn finish(&self, root: u32) -> Option<MbaExpr> {
        let mut m = MbaExpr::new(self.vars.clone());
        let mut map: HashMap<u32, u32> = HashMap::new();
        for i in self.reach(root) {
            let n = self.nodes[i as usize];
            let args: Vec<u32> = n.args[..n.op.arity()].iter().map(|a| map[a]).collect();
            let id = match n.op {
                MOp::Zext | MOp::Sext | MOp::Trunc => m.push_cast(n.op, args[0], n.w),
                op => m.push(op, &args),
            }
            .ok()?;
            map.insert(i, id);
        }
        Some(m)
    }
}

/// A total order on expressions of equal cost (the last tie-break).
pub(crate) fn structural(a: &MbaExpr, b: &MbaExpr) -> core::cmp::Ordering {
    let key = |n: &MNode| {
        let (tag, k, c) = match n.op {
            MOp::Const(v) => (0u8, 0u16, Some(v)),
            MOp::Var(i) => (1, i as u16, None),
            MOp::Add => (2, 0, None),
            MOp::Sub => (3, 0, None),
            MOp::Mul => (4, 0, None),
            MOp::Neg => (5, 0, None),
            MOp::And => (6, 0, None),
            MOp::Or => (7, 0, None),
            MOp::Xor => (8, 0, None),
            MOp::Not => (9, 0, None),
            MOp::Shl(k) => (10, k, None),
            MOp::LShr(k) => (11, k, None),
            MOp::Zext => (12, 0, None),
            MOp::Sext => (13, 0, None),
            MOp::Trunc => (14, 0, None),
        };
        (tag, k, c, n.width.bits(), n.args)
    };
    let (ka, kb): (Vec<_>, Vec<_>) = (
        a.nodes().iter().map(key).collect(),
        b.nodes().iter().map(key).collect(),
    );
    ka.cmp(&kb)
}

/// Emission of normal forms into a builder, with the atoms' renderings imported on use.
pub(crate) struct Render<'a> {
    pub(crate) b: Builder,
    classes: &'a Classes,
    atom_exprs: &'a [MbaExpr],
    atom_nodes: Vec<Option<u32>>,
    w: Width,
    /// Candidates built (telemetry).
    pub(crate) built: u64,
}

/// A linear combination to emit: terms and a constant.
#[derive(Clone, Debug, Default)]
pub(crate) struct Sum {
    pub(crate) terms: Vec<(u32, BitVec)>,
    pub(crate) konst: Option<BitVec>,
}

impl<'a> Render<'a> {
    pub(crate) fn new(
        vars: Vec<Width>,
        w: Width,
        classes: &'a Classes,
        atom_exprs: &'a [MbaExpr],
    ) -> Render<'a> {
        Render {
            b: Builder::new(vars),
            classes,
            atom_exprs,
            atom_nodes: vec![None; atom_exprs.len()],
            w,
            built: 0,
        }
    }

    /// Atom `a`'s node.
    pub(crate) fn atom(&mut self, a: u32) -> Option<u32> {
        if let Some(n) = self.atom_nodes.get(a as usize).copied().flatten() {
            return Some(n);
        }
        let n = self.b.import(self.atom_exprs.get(a as usize)?)?;
        self.atom_nodes[a as usize] = Some(n);
        Some(n)
    }

    /// `AND_set` (ascending atoms).
    fn conj(&mut self, set: u64) -> Option<u32> {
        let mut acc: Option<u32> = None;
        for a in 0..64u32 {
            if set >> a & 1 == 1 {
                let n = self.atom(a)?;
                acc = Some(match acc {
                    None => n,
                    Some(x) => self.b.bin(MOp::And, x, n),
                });
            }
        }
        acc
    }

    /// `x & mask` (nothing for all-ones).
    fn masked(&mut self, x: u32, mask: &BitVec) -> u32 {
        if mask.is_ones() {
            return x;
        }
        let m = self.b.konst(mask);
        self.b.bin(MOp::And, x, m)
    }

    /// A symbol.
    #[cfg_attr(not(test), allow(dead_code))] // products arrive with the polynomial form
    pub(crate) fn sym(&mut self, s: Sym) -> Option<u32> {
        let x = self.conj(s.set)?;
        let mask = *self.classes.mask(usize::from(s.class));
        Some(self.masked(x, &mask))
    }

    /// `k·t` for a coefficient `k` (positive in the signed sense): `t`, a shift, or a product.
    fn scaled(&mut self, t: u32, k: &BitVec) -> u32 {
        if *k == BitVec::one(self.w) {
            return t;
        }
        if count_ones(k) == 1 {
            let s = trailing_zeros(k);
            return self.b.un(MOp::Shl(s as u16), t);
        }
        let c = self.b.konst(k);
        self.b.bin(MOp::Mul, t, c)
    }

    /// Emits `Σ kᵢ·tᵢ + c`: positive coefficients first, then the others, subtracted (or added
    /// with their negative coefficient when that constant is needed anyway), powers of two as
    /// shifts, the constant last.
    pub(crate) fn sum(&mut self, s: &Sum) -> u32 {
        let w = self.w;
        let mut acc: Option<u32> = None;
        type Terms = Vec<(u32, BitVec)>;
        let (pos, neg): (Terms, Terms) = s
            .terms
            .iter()
            .copied()
            .filter(|(_, k)| !k.is_zero())
            .partition(|(_, k)| !k.msb());
        let mut k = s.konst.unwrap_or(BitVec::zero(w));
        // Constants the sum needs whatever the signs: its constant and positive coefficients.
        let trivial = |c: &BitVec| *c == BitVec::one(w) || count_ones(c) == 1;
        let mut needed: Vec<BitVec> = pos
            .iter()
            .map(|(_, c)| *c)
            .filter(|c| !trivial(c))
            .collect();
        if !k.is_zero() {
            needed.push(k);
        }
        for (t, c) in pos {
            let x = self.scaled(t, &c);
            acc = Some(match acc {
                None => x,
                Some(a) => self.b.bin(MOp::Add, a, x),
            });
        }
        for (t, c) in neg {
            let nc = BitVec::un_unchecked(UnOp::Neg, &c);
            let reuse = !trivial(&nc) && needed.contains(&c) && !needed.contains(&nc);
            acc = Some(match acc {
                Some(a) if reuse => {
                    let m = self.b.konst(&c);
                    let x = self.b.bin(MOp::Mul, t, m);
                    self.b.bin(MOp::Add, a, x)
                }
                Some(a) => {
                    let x = self.scaled(t, &nc);
                    self.b.bin(MOp::Sub, a, x)
                }
                // Only subtracted terms: start from the constant, or put the sign in the
                // coefficient (`t·k` is no larger than `−(t·|k|)`), or negate.
                None if !k.is_zero() && !reuse => {
                    let a = self.b.konst(&k);
                    k = BitVec::zero(w);
                    let x = self.scaled(t, &nc);
                    self.b.bin(MOp::Sub, a, x)
                }
                None if trivial(&nc) => {
                    let x = self.scaled(t, &nc);
                    self.b.un(MOp::Neg, x)
                }
                None => {
                    let m = self.b.konst(&c);
                    self.b.bin(MOp::Mul, t, m)
                }
            });
            if !trivial(&nc) {
                needed.push(if reuse { c } else { nc });
            }
        }
        match acc {
            None => self.b.konst(&k),
            Some(a) if k.is_zero() => a,
            Some(a) => {
                let c = self.b.konst(&k);
                self.b.bin(MOp::Add, a, c)
            }
        }
    }

    /// The cheapest of `cands` (node count, weight, structure).
    pub(crate) fn best(&self, cands: &[u32]) -> Option<u32> {
        let mut best: Option<(u32, Cost)> = None;
        for &c in cands {
            let cost = self.b.cost(c);
            best = match best {
                None => Some((c, cost)),
                Some((_, bc)) if cost < bc => Some((c, cost)),
                Some((b, bc)) if cost == bc && b != c => {
                    let (x, y) = (self.b.finish(c), self.b.finish(b));
                    match (x, y) {
                        (Some(x), Some(y)) if structural(&x, &y).is_lt() => Some((c, cost)),
                        _ => Some((b, bc)),
                    }
                }
                keep => keep,
            };
        }
        best.map(|(c, _)| c)
    }

    // ----- bitwise functions ---------------------------------------------------------------

    /// A uniform table's renderings (one table for every position).
    fn uniform(&mut self, t: &[u64], support: &[u32]) -> Vec<u32> {
        let w = self.w;
        let s = support.len();
        let mut out = Vec::new();
        if s == 0 {
            let v = if t[0] & 1 == 1 {
                BitVec::ones(w)
            } else {
                BitVec::zero(w)
            };
            out.push(self.b.konst(&v));
            return out;
        }
        let atoms: Option<Vec<u32>> = support.iter().map(|&a| self.atom(a)).collect();
        let Some(atoms) = atoms else {
            return out;
        };
        if let Some(tt) = table8(t, s) {
            out.extend(self.min_form(tt, &atoms));
        }
        // The algebraic normal form, when short.
        let terms = anf(t, s);
        if terms.len() <= 2 * s + 1 {
            let mut acc: Option<u32> = None;
            let mut flip = false;
            for &q in &terms {
                if q == 0 {
                    flip = true;
                    continue;
                }
                let mut c: Option<u32> = None;
                for (j, &a) in atoms.iter().enumerate() {
                    if q >> j & 1 == 1 {
                        c = Some(match c {
                            None => a,
                            Some(x) => self.b.bin(MOp::And, x, a),
                        });
                    }
                }
                if let Some(c) = c {
                    acc = Some(match acc {
                        None => c,
                        Some(x) => self.b.bin(MOp::Xor, x, c),
                    });
                }
            }
            let r = match acc {
                Some(x) if flip => self.b.un(MOp::Not, x),
                Some(x) => x,
                None => self.b.konst(&BitVec::ones(w)),
            };
            out.push(r);
        }
        // The integer conjunction form (always available).
        let a = mobius(t, s);
        let mut sum = Sum {
            terms: Vec::new(),
            konst: Some(BitVec::wrapping_from_i128(w, -i128::from(a[0]))),
        };
        for (q, &k) in a.iter().enumerate().skip(1) {
            if k == 0 {
                continue;
            }
            let set = (0..s)
                .filter(|&j| q >> j & 1 == 1)
                .fold(0u64, |m, j| m | 1u64 << support[j]);
            if let Some(c) = self.conj(set) {
                sum.terms
                    .push((c, BitVec::wrapping_from_i128(w, i128::from(k))));
            }
        }
        out.push(self.sum(&sum));
        self.built += out.len() as u64;
        out
    }

    /// The minimum-size form of an 8-bit table over `atoms` (at most three).
    fn min_form(&mut self, tt: u8, atoms: &[u32]) -> Option<u32> {
        let w = self.w;
        let (tmpl, _) = &min_forms().forms[tt as usize];
        let mut built: Vec<u32> = Vec::with_capacity(tmpl.len());
        for t in tmpl {
            let id = match *t {
                T::Var(k) => *atoms.get(usize::from(k))?,
                T::Zero => self.b.konst(&BitVec::zero(w)),
                T::Ones => self.b.konst(&BitVec::ones(w)),
                T::Not(a) => {
                    let a = built[a as usize];
                    self.b.un(MOp::Not, a)
                }
                T::Bin(op, a, b) => {
                    let op = match op {
                        BinOp::And => MOp::And,
                        BinOp::Or => MOp::Or,
                        _ => MOp::Xor,
                    };
                    let (a, b) = (built[a as usize], built[b as usize]);
                    self.b.bin(op, a, b)
                }
            };
            built.push(id);
        }
        built.last().copied()
    }

    /// The best rendering of a uniform table.
    fn best_uniform(&mut self, t: &[u64], support: &[u32]) -> Option<u32> {
        let c = self.uniform(t, support);
        self.best(&c)
    }

    /// Renderings of a bitwise function (tables per class).
    pub(crate) fn bits(&mut self, f: &Bits) -> Vec<u32> {
        let w = self.w;
        let s = f.support.len();
        if f.uniform() {
            return self.uniform(&f.tables[0], &f.support);
        }
        let n = self.classes.len();
        // Classes grouped by table.
        let mut groups: Vec<(Vec<u64>, BitVec)> = Vec::new();
        for c in 0..n {
            let t = &f.tables[c];
            match groups.iter_mut().find(|(g, _)| g == t) {
                Some((_, m)) => *m = bv_or(m, self.classes.mask(c)),
                None => groups.push((t.clone(), *self.classes.mask(c))),
            }
        }
        let full = |t: &Vec<u64>| (0..1usize << s).all(|p| bits::get(t, p));
        let empty = |t: &Vec<u64>| (0..1usize << s).all(|p| !bits::get(t, p));
        let mut out = Vec::new();
        // The or of the masked groups.
        let mut acc: Option<u32> = None;
        let mut ok = true;
        for (t, m) in &groups {
            if empty(t) {
                continue;
            }
            let x = if full(t) {
                self.b.konst(m)
            } else {
                match self.best_uniform(t, &f.support) {
                    Some(g) => self.masked(g, m),
                    None => {
                        ok = false;
                        break;
                    }
                }
            };
            acc = Some(match acc {
                None => x,
                Some(a) => self.b.bin(MOp::Or, a, x),
            });
        }
        if ok {
            out.push(acc.unwrap_or_else(|| self.b.konst(&BitVec::zero(w))));
        }
        // ((g ^ A) | B) & ~C for a base table g: classes with ¬g in A, all-ones in B, zero in C.
        let bases: Vec<Vec<u64>> = groups
            .iter()
            .filter(|(t, _)| !full(t) && !empty(t))
            .map(|(t, _)| t.clone())
            .collect();
        for g in bases {
            let ng: Vec<u64> = {
                let mut n: Vec<u64> = g.iter().map(|x| !x).collect();
                if s < 6 {
                    n[0] &= (1u64 << (1usize << s)) - 1;
                }
                n
            };
            let (mut a, mut b, mut c) = (BitVec::zero(w), BitVec::zero(w), BitVec::zero(w));
            let mut fits = true;
            for (t, m) in &groups {
                if *t == g {
                } else if *t == ng {
                    a = bv_or(&a, m);
                } else if full(t) {
                    b = bv_or(&b, m);
                } else if empty(t) {
                    c = bv_or(&c, m);
                } else {
                    fits = false;
                }
            }
            if !fits {
                continue;
            }
            let Some(mut x) = self.best_uniform(&g, &f.support) else {
                continue;
            };
            if !a.is_zero() {
                let k = self.b.konst(&a);
                x = self.b.bin(MOp::Xor, x, k);
            }
            if !b.is_zero() {
                let k = self.b.konst(&b);
                x = self.b.bin(MOp::Or, x, k);
            }
            if !c.is_zero() {
                x = self.masked(x, &bv_not(&c));
            }
            out.push(x);
        }
        self.built += out.len() as u64;
        out
    }

    // ----- linear combinations -------------------------------------------------------------

    /// Renderings of `konst + Σ γ·m` (degree at most 1): as a bitwise function when it is one,
    /// and as combinations over groups of classes whose coefficients can be chosen equal.
    pub(crate) fn linear(&mut self, p: &Poly) -> Vec<u32> {
        let w = self.w;
        let mut out = Vec::new();
        if let Some(f) = Bits::from_linear(p, self.classes) {
            out.extend(self.bits(&f));
        }
        // Per class: coefficients by atom set.
        let n = self.classes.len();
        let mut coef: Vec<BTreeMap<u64, BitVec>> = vec![BTreeMap::new(); n];
        for (m, c) in p.terms() {
            if let Some(&(s, _)) = m.first() {
                coef[usize::from(s.class)].insert(s.set, *c);
            }
        }
        let prec = |c: usize| u32::from(w.bits()) - u32::from(self.classes.low(c));
        let same = |a: &BitVec, b: &BitVec, m: u32| {
            let lm = crate::facts::known::low_mask(w, m);
            bv_and(a, &lm) == bv_and(b, &lm)
        };
        // Groups: classes whose coefficients agree (each modulo its own precision) with the
        // group's most precise member, whose coefficients the group uses.
        let mut groups: Vec<Vec<usize>> = Vec::new();
        for c in 0..n {
            if coef[c].values().all(|k| same(k, &BitVec::zero(w), prec(c))) {
                continue;
            }
            let mut placed = false;
            for g in groups.iter_mut() {
                let rep = *g
                    .iter()
                    .chain(core::iter::once(&c))
                    .max_by_key(|&&x| (prec(x), core::cmp::Reverse(x)))
                    .unwrap_or(&c);
                let fits = g.iter().chain(core::iter::once(&c)).all(|&x| {
                    let keys: Vec<&u64> = coef[x].keys().chain(coef[rep].keys()).collect();
                    keys.into_iter().all(|k| {
                        let z = BitVec::zero(w);
                        same(
                            coef[x].get(k).unwrap_or(&z),
                            coef[rep].get(k).unwrap_or(&z),
                            prec(x),
                        )
                    })
                });
                if fits {
                    g.push(c);
                    placed = true;
                    break;
                }
            }
            if !placed {
                groups.push(vec![c]);
            }
        }
        // Each group: the cheapest of its masked conjunction and indicator forms.
        let mut total = Sum {
            terms: Vec::new(),
            konst: Some(p.konst()),
        };
        for g in &groups {
            let rep = *g
                .iter()
                .max_by_key(|&&x| (prec(x), core::cmp::Reverse(x)))
                .unwrap_or(&g[0]);
            let mask = g
                .iter()
                .fold(BitVec::zero(w), |m, &c| bv_or(&m, self.classes.mask(c)));
            let Some(part) = self.group(&coef[rep], &mask) else {
                return out;
            };
            total.terms.extend(part.terms);
            if let Some(k) = part.konst {
                total.konst = Some(BitVec::bin_unchecked(
                    BinOp::Add,
                    &total.konst.unwrap_or(BitVec::zero(w)),
                    &k,
                ));
            }
        }
        out.push(self.sum(&total));
        self.built += 1;
        out
    }

    /// The cheapest rendering of `Σ_S γ_S·(AND_S & mask)` as terms of a sum: the masked
    /// conjunctions, or `b·mask + Σ_{v≠b} (v − b)·(g_v & mask)` over the distinct values `v` of
    /// `Σ_{∅≠S⊆p} γ_S` at the corners `p` (at most three atoms), `g_v` the minimum form of the
    /// corners with value `v`.
    fn group(&mut self, coef: &BTreeMap<u64, BitVec>, mask: &BitVec) -> Option<Sum> {
        let w = self.w;
        let mut options: Vec<Sum> = Vec::new();
        // Masked conjunctions.
        let mut conj = Sum::default();
        for (&set, k) in coef {
            let c = self.conj(set)?;
            let x = self.masked(c, mask);
            conj.terms.push((x, *k));
        }
        options.push(conj);
        // Indicators.
        let support: Vec<u32> = (0..64u32)
            .filter(|&a| coef.keys().any(|s| s >> a & 1 == 1))
            .collect();
        let s = support.len();
        if s <= 3 {
            let atoms: Option<Vec<u32>> = support.iter().map(|&a| self.atom(a)).collect();
            let atoms = atoms?;
            let corners = 1usize << s;
            let mut v = vec![BitVec::zero(w); corners];
            for (&set, k) in coef {
                let q = support
                    .iter()
                    .enumerate()
                    .filter(|&(_, &a)| set >> a & 1 == 1)
                    .fold(0usize, |q, (j, _)| q | 1 << j);
                for (p, vp) in v.iter_mut().enumerate() {
                    if p & q == q {
                        *vp = BitVec::bin_unchecked(BinOp::Add, vp, k);
                    }
                }
            }
            let mut distinct: Vec<BitVec> = Vec::new();
            for x in &v {
                if !distinct.contains(x) {
                    distinct.push(*x);
                }
            }
            for &base in &distinct {
                let mut sum = Sum {
                    terms: Vec::new(),
                    konst: (!base.is_zero())
                        .then(|| BitVec::bin_unchecked(BinOp::Mul, &base, mask)),
                };
                for &val in distinct.iter().filter(|&&x| x != base) {
                    let mut tt = 0u8;
                    for i in 0..8usize {
                        if v[i & (corners - 1)] == val {
                            tt |= 1 << i;
                        }
                    }
                    let g = self.min_form(tt, &atoms)?;
                    let x = self.masked(g, mask);
                    sum.terms
                        .push((x, BitVec::bin_unchecked(BinOp::Sub, &val, &base)));
                }
                options.push(sum);
            }
        }
        // The cheapest, costed on its own.
        let mut best: Option<(Cost, Sum)> = None;
        for o in options {
            let root = self.sum(&o);
            let cost = self.b.cost(root);
            if best.as_ref().is_none_or(|(c, _)| cost < *c) {
                best = Some((cost, o));
            }
        }
        best.map(|(_, s)| s)
    }

    /// A monomial: the product of its symbols' powers (square and multiply).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn mono(&mut self, m: &Mono) -> Option<u32> {
        let mut acc: Option<u32> = None;
        for &(s, e) in m {
            let x = self.sym(s)?;
            let p = self.power(x, e);
            acc = Some(match acc {
                None => p,
                Some(a) => self.b.bin(MOp::Mul, a, p),
            });
        }
        Some(acc.unwrap_or_else(|| self.b.konst(&BitVec::one(self.w))))
    }

    #[cfg_attr(not(test), allow(dead_code))]
    fn power(&mut self, x: u32, e: u32) -> u32 {
        let mut result: Option<u32> = None;
        let mut base = x;
        let mut e = e.max(1);
        loop {
            if e & 1 == 1 {
                result = Some(match result {
                    None => base,
                    Some(r) => self.b.bin(MOp::Mul, r, base),
                });
            }
            e >>= 1;
            if e == 0 {
                break;
            }
            base = self.b.bin(MOp::Mul, base, base);
        }
        result.unwrap_or(x)
    }
}
