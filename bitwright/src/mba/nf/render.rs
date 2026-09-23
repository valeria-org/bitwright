//! Rendering normal forms as expressions. Candidates are built into one builder with local
//! interning (equal subterms are one node), costed by the nodes reachable from their root, and
//! the cheapest is kept: by node count, then by an operator-weighted size, then by structure.

use std::collections::{BTreeMap, HashMap};

use crate::hash::IdMap;

use super::bits::{self, Bits, anf, mobius, table8};
use super::classes::{Classes, FULL};
use super::poly::{Mono, Poly, Sym};
use super::synth;
use crate::engine::pass::bitwise::{T, min_forms};
use crate::facts::known::{bv_and, bv_not, bv_or, count_ones, trailing_zeros};
use crate::mba::certify;
use crate::mba::expr::{MNode, MOp, MbaExpr};
use crate::mba::solve::Verdict;
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
    memo: IdMap<BNode, u32>,
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
            memo: IdMap::default(),
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
    pub(crate) fn reach(&self, root: u32) -> Vec<u32> {
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

    /// The cost of the candidate rooted at `root`: its nodes, counting a shift's amount as the
    /// constant node it is once lifted (shared with an equal constant), then operator weight.
    pub(crate) fn cost(&self, root: u32) -> Cost {
        let r = self.reach(root);
        let weight: u32 = r.iter().map(|&i| weight(&self.nodes[i as usize].op)).sum();
        let mut consts: Vec<BitVec> = r
            .iter()
            .filter_map(|&i| match self.nodes[i as usize].op {
                MOp::Const(v) => Some(v),
                _ => None,
            })
            .collect();
        let mut amounts = 0u32;
        for &i in &r {
            let n = self.nodes[i as usize];
            if let MOp::Shl(k) | MOp::LShr(k) = n.op {
                let v = BitVec::wrapping_from_u64(n.w, u64::from(k));
                if !consts.contains(&v) {
                    consts.push(v);
                    amounts += 1;
                }
            }
        }
        (r.len() as u32 + amounts, weight)
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
    /// Per product node built from normal forms: the factor and quotient it multiplies.
    products: HashMap<u32, (Poly, Poly)>,
    /// Work spent, in the solver's steps (terms and table entries visited, division term
    /// operations), and the most it may spend: past it, no more candidates are generated.
    pub(crate) work: u64,
    limit: u64,
    /// [`poly`](Self::poly)'s renderings by form and depth, with the work and candidates they
    /// cost, charged again on reuse (so the budget runs out where it would have), and the
    /// factors they were rendered with.
    memo: HashMap<(Poly, u32), (Vec<u32>, u64, u64)>,
    memo_factors: Vec<Poly>,
    /// What synthesis did.
    pub(crate) synth: SynthTally,
}

/// Steps per term operation of exact division (a map update with a monomial key).
const DIVISION_STEP: u64 = 4;

/// A table hit for a normal form (see [`Render::synthesize`]).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Hit {
    /// Proved equal to the normal form, the atoms taken as independent variables.
    Exact(u32),
    /// Neither proved nor refuted (no certificate fits): at most a sampled answer.
    Unproved(u32),
}

/// What synthesis did (telemetry).
#[derive(Copy, Clone, Debug, Default)]
pub(crate) struct SynthTally {
    pub(crate) lookups: u64,
    pub(crate) hits: u64,
    pub(crate) proved: u64,
    pub(crate) refuted: u64,
    pub(crate) unproved: u64,
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
        limit: u64,
    ) -> Render<'a> {
        Render {
            b: Builder::new(vars),
            classes,
            atom_exprs,
            atom_nodes: vec![None; atom_exprs.len()],
            w,
            built: 0,
            products: HashMap::new(),
            work: 0,
            limit,
            memo: HashMap::new(),
            memo_factors: Vec::new(),
            synth: SynthTally::default(),
        }
    }

    /// Spends `n` steps; false once past the limit (then callers stop generating candidates).
    fn spend(&mut self, n: u64) -> bool {
        self.work = self.work.saturating_add(n);
        self.work <= self.limit
    }

    /// Whether candidate generation was cut short by the limit.
    pub(crate) fn exhausted(&self) -> bool {
        self.work > self.limit
    }

    /// `p / f` if exact, charged to the meter; at most `(4·|p| + 16)·|f|` term operations.
    fn divide(&mut self, p: &Poly, f: &Poly) -> Option<Poly> {
        let cap = (4 * p.len() as u64 + 16) * f.len() as u64 + p.len() as u64;
        let room = self.limit.saturating_sub(self.work) / DIVISION_STEP;
        let start = cap.min(room);
        let mut left = start;
        let q = p.div_exact(f, &mut left);
        self.spend((start - left) * DIVISION_STEP + 1);
        match q {
            Ok(q) => q,
            Err(()) => {
                if room < cap {
                    // Stopped by the limit rather than by the division's own bound.
                    self.work = self.limit.saturating_add(1);
                }
                None
            }
        }
    }

    /// The factors and quotients of the products the candidate at `root` uses (to try as
    /// factors in a next round).
    pub(crate) fn factors_of(&self, root: u32) -> Vec<Poly> {
        let mut out: Vec<Poly> = Vec::new();
        for n in self.b.reach(root) {
            if let Some((f, q)) = self.products.get(&n) {
                for x in [f, q] {
                    if x.degree() >= 1 && !out.contains(x) {
                        out.push(x.clone());
                    }
                }
            }
        }
        out
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
        self.spend(4 * s.terms.len() as u64 + 1);
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
        if !self.spend(4u64 << s) {
            return out;
        }
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
        if !self.spend((f.tables.len() as u64) << s) {
            return Vec::new();
        }
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

    /// Renderings of `konst + Σ γ·m` (degree at most 1).
    pub(crate) fn linear(&mut self, p: &Poly) -> Vec<u32> {
        let sums = self.linear_sums(p);
        sums.iter().map(|s| self.sum(s)).collect()
    }

    /// Decompositions of `konst + Σ γ·m` (degree at most 1) into sums: as a bitwise function
    /// when it is one, and as combinations over groups of classes whose coefficients can be
    /// chosen equal (also after taking out, per atom set, the coefficient of its widest class
    /// as an unmasked term).
    pub(crate) fn linear_sums(&mut self, p: &Poly) -> Vec<Sum> {
        let w = self.w;
        let mut out: Vec<Sum> = Vec::new();
        if !self.spend(p.len() as u64 * self.classes.len() as u64) {
            return out;
        }
        if let Some(f) = Bits::from_linear(&p.expand_full(self.classes), self.classes) {
            for n in self.bits(&f) {
                out.push(Sum {
                    terms: vec![(n, BitVec::one(w))],
                    konst: None,
                });
            }
        }
        out.extend(self.grouped(p));
        let n = self.classes.len();
        if n > 1
            && p.terms()
                .keys()
                .any(|m| m.iter().any(|(s, _)| s.class != FULL))
        {
            // Per atom set, the coefficient of its widest class becomes an unmasked term; the
            // other classes keep their differences.
            let mut widest: BTreeMap<u64, (u32, BitVec)> = BTreeMap::new();
            let mut covered: BTreeMap<u64, u32> = BTreeMap::new();
            for (m, c) in p.terms() {
                if let Some(&(s, _)) = m.first()
                    && s.class != FULL
                {
                    let size = count_ones(self.classes.mask(usize::from(s.class)));
                    *covered.entry(s.set).or_default() += size;
                    let e = widest.entry(s.set).or_insert((0, BitVec::zero(w)));
                    if size > e.0 {
                        *e = (size, *c);
                    }
                }
            }
            // Classes a set has no term in have coefficient 0: those count too.
            for (&set, e) in widest.iter_mut() {
                let covered = covered.get(&set).copied().unwrap_or(0);
                let missing = u32::from(w.bits()) - covered.min(u32::from(w.bits()));
                if missing > e.0 {
                    *e = (missing, BitVec::zero(w));
                }
            }
            let mut q = p.clone();
            for (&set, (_, base)) in &widest {
                if base.is_zero() {
                    continue;
                }
                q.add_term(vec![(Sym { set, class: FULL }, 1)], base);
                let nb = BitVec::un_unchecked(UnOp::Neg, base);
                for c in 0..n {
                    q.add_term(
                        vec![(
                            Sym {
                                set,
                                class: c as u16,
                            },
                            1,
                        )],
                        &nb,
                    );
                }
            }
            if q != *p {
                out.extend(self.grouped(&q));
            }
        }
        // `c·~h = −c·h − c`, and back: a complement traded for a constant.
        let variants: Vec<Sum> = out.iter().flat_map(|s| self.complements(s)).collect();
        out.extend(variants);
        self.built += out.len() as u64;
        out
    }

    /// Variants of `s` with complements traded for the constant: every term `c·~h` as
    /// `−c·h` (the constant takes `−c`), and a term `d·h` whose coefficient is the constant as
    /// `−d·~h` (the constant goes).
    fn complements(&mut self, s: &Sum) -> Vec<Sum> {
        let w = self.w;
        let mut out = Vec::new();
        let mut k = s.konst.unwrap_or(BitVec::zero(w));
        let mut changed = false;
        let mut terms = Vec::with_capacity(s.terms.len());
        for &(t, c) in &s.terms {
            let n = self.b.nodes[t as usize];
            if n.op == MOp::Not {
                terms.push((n.args[0], BitVec::un_unchecked(UnOp::Neg, &c)));
                k = BitVec::bin_unchecked(BinOp::Sub, &k, &c);
                changed = true;
            } else {
                terms.push((t, c));
            }
        }
        if changed {
            out.push(Sum {
                terms,
                konst: Some(k),
            });
        }
        if let Some(k) = s.konst
            && !k.is_zero()
            && let Some(i) = s.terms.iter().position(|(_, c)| *c == k)
        {
            let mut terms = s.terms.clone();
            let (t, c) = terms[i];
            let nt = self.b.un(MOp::Not, t);
            terms[i] = (nt, BitVec::un_unchecked(UnOp::Neg, &c));
            out.push(Sum { terms, konst: None });
        }
        out
    }

    /// The decompositions of a degree-≤1 form over groups of classes: unmasked terms are one
    /// group, and classes whose coefficients agree (each modulo its own precision) with the
    /// group's most precise member are another. With one group every rendering of it is
    /// offered; with several, each group's rendering is chosen in turn for the cheapest whole.
    fn grouped(&mut self, p: &Poly) -> Vec<Sum> {
        let w = self.w;
        let n = self.classes.len();
        let mut coef: Vec<BTreeMap<u64, BitVec>> = vec![BTreeMap::new(); n + 1];
        for (m, c) in p.terms() {
            if let Some(&(s, _)) = m.first() {
                let k = if s.class == FULL {
                    n
                } else {
                    usize::from(s.class)
                };
                coef[k].insert(s.set, *c);
            }
        }
        let prec = |c: usize| u32::from(w.bits()) - u32::from(self.classes.low(c));
        let same = |a: &BitVec, b: &BitVec, m: u32| {
            let lm = crate::facts::known::low_mask(w, m);
            bv_and(a, &lm) == bv_and(b, &lm)
        };
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
                let z = BitVec::zero(w);
                let fits = g.iter().chain(core::iter::once(&c)).all(|&x| {
                    coef[x].keys().chain(coef[rep].keys()).all(|k| {
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
        let mut options: Vec<Vec<Sum>> = Vec::new();
        if !coef[n].is_empty() {
            let ones = BitVec::ones(w);
            match self.group(&coef[n], &ones) {
                Some(o) => options.push(o),
                None => return Vec::new(),
            }
        }
        for g in &groups {
            let rep = *g
                .iter()
                .max_by_key(|&&x| (prec(x), core::cmp::Reverse(x)))
                .unwrap_or(&g[0]);
            let mask = g
                .iter()
                .fold(BitVec::zero(w), |m, &c| bv_or(&m, self.classes.mask(c)));
            match self.group(&coef[rep], &mask) {
                Some(o) => options.push(o),
                None => return Vec::new(),
            }
        }
        let konst = p.konst();
        let total = |options: &[Vec<Sum>], choice: &[usize]| -> Sum {
            let mut t = Sum {
                terms: Vec::new(),
                konst: Some(konst),
            };
            for (g, &k) in choice.iter().enumerate() {
                let part = &options[g][k];
                t.terms.extend(part.terms.iter().copied());
                if let Some(c) = part.konst {
                    t.konst = Some(BitVec::bin_unchecked(
                        BinOp::Add,
                        &t.konst.unwrap_or(BitVec::zero(w)),
                        &c,
                    ));
                }
            }
            t
        };
        match options.len() {
            0 => vec![total(&options, &[])],
            1 => (0..options[0].len())
                .map(|k| total(&options, &[k]))
                .collect(),
            _ => {
                let mut choice = vec![0usize; options.len()];
                for g in 0..options.len() {
                    if options[g].len() < 2 {
                        continue;
                    }
                    let mut best: Option<(Cost, usize)> = None;
                    for k in 0..options[g].len() {
                        choice[g] = k;
                        let root = self.sum(&total(&options, &choice));
                        let cost = self.b.cost(root);
                        if best.is_none_or(|(c, _)| cost < c) {
                            best = Some((cost, k));
                        }
                    }
                    choice[g] = best.map_or(0, |(_, k)| k);
                }
                vec![total(&options, &choice)]
            }
        }
    }

    /// The cheapest of `sums`, each costed on its own.
    fn cheapest(&mut self, sums: Vec<Sum>) -> Option<Sum> {
        let mut best: Option<(Cost, Sum)> = None;
        for s in sums {
            let root = self.sum(&s);
            let cost = self.b.cost(root);
            if best.as_ref().is_none_or(|(c, _)| cost < *c) {
                best = Some((cost, s));
            }
        }
        best.map(|(_, s)| s)
    }

    /// Renderings of a normal form of any degree: the linear part's cheapest decomposition plus
    /// the nonlinear part monomial by monomial, or factored by a symbol common to all its
    /// monomials or by a factor of the input's products it is exactly divisible by; and the
    /// whole as a product of such a factor and its quotient.
    pub(crate) fn poly(&mut self, p: &Poly, factors: &[Poly], depth: u32) -> Vec<u32> {
        // Products render their factor for every quotient: each form once per depth. Deeper
        // calls pass the factors they were given.
        if depth == 0 && self.memo_factors.as_slice() != factors {
            self.memo.clear();
            self.memo_factors = factors.to_vec();
        }
        let key = (p.clone(), depth);
        if let Some((out, work, built)) = self.memo.get(&key) {
            let (out, work, built) = (out.clone(), *work, *built);
            self.spend(work);
            self.built += built;
            return out;
        }
        let (work, built) = (self.work, self.built);
        let out = self.render_poly(p, factors, depth);
        if !self.exhausted() {
            let spent = (self.work - work, self.built - built);
            self.memo.insert(key, (out.clone(), spent.0, spent.1));
        }
        out
    }

    fn render_poly(&mut self, p: &Poly, factors: &[Poly], depth: u32) -> Vec<u32> {
        const MAX_DEPTH: u32 = 2;
        if p.degree() <= 1 {
            return self.linear(p);
        }
        let w = self.w;
        let one = BitVec::one(w);
        let lin = p.part(|d| d <= 1);
        let nl = p.part(|d| d >= 2);
        let lin_sum = if lin.is_zero() {
            Sum::default()
        } else {
            let sums = self.linear_sums(&lin);
            match self.cheapest(sums) {
                Some(s) => s,
                None => return Vec::new(),
            }
        };
        let mut parts: Vec<Sum> = Vec::new();
        let mut naive = Sum::default();
        if !self.spend(nl.len() as u64 * u64::from(nl.degree())) {
            return Vec::new();
        }
        for (m, c) in nl.terms() {
            match self.mono(m) {
                Some(t) => naive.terms.push((t, *c)),
                None => return Vec::new(),
            }
        }
        parts.push(naive);
        if depth < MAX_DEPTH {
            let mut fs: Vec<Poly> = if depth == 0 {
                factors.to_vec()
            } else {
                Vec::new()
            };
            fs.extend(common_symbols(&nl).into_iter().map(|s| Poly::sym(w, s)));
            for f in &fs {
                if self.exhausted() {
                    break;
                }
                if let Some(q) = self.divide(&nl, f)
                    && let Some(x) = self.product(f, &q, factors, depth)
                {
                    parts.push(Sum {
                        terms: vec![(x, one)],
                        konst: None,
                    });
                }
            }
        }
        let mut out: Vec<u32> = parts
            .iter()
            .map(|n| {
                let mut s = lin_sum.clone();
                s.terms.extend(n.terms.iter().copied());
                self.sum(&s)
            })
            .collect();
        if depth < MAX_DEPTH {
            for f in factors {
                if self.exhausted() {
                    break;
                }
                if let Some(q) = self.divide(p, f)
                    && let Some(x) = self.product(f, &q, factors, depth)
                {
                    out.push(x);
                }
            }
        }
        self.built += out.len() as u64;
        out
    }

    /// The synthesis table's smallest expression with `nf`'s values at the probes, when `nf`
    /// mentions one to three atoms and that expression costs less than `bar`. It is exact only
    /// once a certificate proves it equal to `nf` with the atoms as independent variables (then
    /// also for their actual values); a refuted one is dropped.
    pub(crate) fn synthesize(&mut self, nf: &Poly, bar: Option<Cost>) -> Option<Hit> {
        let mask = nf.atoms();
        let k = mask.count_ones() as usize;
        if k == 0 || k > 3 {
            return None;
        }
        let ids: Vec<u32> = (0..64u32).filter(|&a| mask >> a & 1 == 1).collect();
        if !self.spend((synth::PROBES * nf.len()) as u64) {
            return None;
        }
        self.synth.lookups += 1;
        let w = self.w;
        // The values at the probes, atom `ids[j]` taking coordinate `j`: truncated at narrower
        // widths, the low 64 bits at wider ones (where the table is read by those too).
        let mask = u64::MAX >> 64u16.saturating_sub(w.bits());
        let mut point = vec![0u64; ids[k - 1] as usize + 1];
        let mut values = [0u64; synth::PROBES];
        for (i, slot) in values.iter_mut().enumerate() {
            let p = synth::probe(i);
            for (j, &a) in ids.iter().enumerate() {
                point[a as usize] = p[j] & mask;
            }
            *slot = nf.eval_low(self.classes, &point)? & mask;
        }
        let table = synth::table();
        let i = table.lookup(w.bits(), &values)?;
        let node = self.table_node(table, i, &ids)?;
        if bar.is_some_and(|b| self.b.cost(node) >= b) {
            return None;
        }
        self.synth.hits += 1;
        let skeleton = self.skeleton(nf, &ids)?;
        let hit = table.expr(i, w, k)?;
        let effort = self
            .limit
            .saturating_sub(self.work)
            .saturating_mul(super::EVALS_PER_STEP);
        let report = certify::check(&skeleton, &hit, effort);
        self.spend(report.work.div_ceil(super::EVALS_PER_STEP).max(1));
        match report.verdict {
            Verdict::Proved => {
                self.synth.proved += 1;
                Some(Hit::Exact(node))
            }
            Verdict::Refuted => {
                self.synth.refuted += 1;
                None
            }
            _ => {
                self.synth.unproved += 1;
                Some(Hit::Unproved(node))
            }
        }
    }

    /// Table entry `i` in this builder, variable `j` being atom `ids[j]`.
    fn table_node(&mut self, t: &synth::Table, i: u32, ids: &[u32]) -> Option<u32> {
        let mut node: HashMap<u32, u32> = HashMap::new();
        for j in t.needed(i) {
            let e = t.entry(j);
            let args: Option<Vec<u32>> = e.args[..e.op.arity()]
                .iter()
                .map(|a| node.get(a).copied())
                .collect();
            let args = args?;
            let x = match e.op {
                synth::Op::Var(v) => self.atom(*ids.get(usize::from(v))?)?,
                synth::Op::One => self.b.konst(&BitVec::one(self.w)),
                op if args.len() == 1 => self.b.un(op.mop()?, args[0]),
                op => self.b.bin(op.mop()?, args[0], *args.get(1)?),
            };
            node.insert(j, x);
        }
        node.get(&i).copied()
    }

    /// `nf` over `ids.len()` fresh variables, variable `j` standing for atom `ids[j]`, as the
    /// sum of its monomials.
    fn skeleton(&self, nf: &Poly, ids: &[u32]) -> Option<MbaExpr> {
        let w = self.w;
        let k = ids.len();
        let mut map: Vec<u32> = (0..64).collect();
        for (j, &a) in ids.iter().enumerate() {
            map[a as usize] = j as u32;
        }
        let nf = nf.rename_atoms(&map);
        let vars: Option<Vec<MbaExpr>> = (0..k as u32)
            .map(|j| {
                let mut m = MbaExpr::new(vec![w; k]);
                m.push(MOp::Var(j), &[]).ok()?;
                Some(m)
            })
            .collect();
        let vars = vars?;
        let mut r = Render::new(vec![w; k], w, self.classes, &vars, u64::MAX);
        let mut sum = Sum {
            terms: Vec::new(),
            konst: Some(nf.konst()),
        };
        for (m, c) in nf.terms() {
            if !m.is_empty() {
                let t = r.mono(m)?;
                sum.terms.push((t, *c));
            }
        }
        let root = r.sum(&sum);
        r.b.finish(root)
    }

    /// `f·q`, each rendered at its cheapest.
    fn product(&mut self, f: &Poly, q: &Poly, factors: &[Poly], depth: u32) -> Option<u32> {
        let a = self.poly(f, factors, depth + 1);
        let a = self.best(&a)?;
        let b = self.poly(q, factors, depth + 1);
        let b = self.best(&b)?;
        let x = self.b.bin(MOp::Mul, a, b);
        self.products
            .entry(x)
            .or_insert_with(|| (f.clone(), q.clone()));
        Some(x)
    }

    /// The renderings of `Σ_S γ_S·(AND_S & mask)` as terms of a sum: the masked conjunctions,
    /// and `b·mask + Σ_{v≠b} (v − b)·(g_v & mask)` over the distinct values `v` of
    /// `Σ_{∅≠S⊆p} γ_S` at the corners `p` (at most three atoms), `g_v` the minimum form of the
    /// corners with value `v`.
    fn group(&mut self, coef: &BTreeMap<u64, BitVec>, mask: &BitVec) -> Option<Vec<Sum>> {
        let w = self.w;
        if !self.spend(coef.len() as u64 * 8) {
            return None;
        }
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
            options.extend(self.affine_plus(coef, mask, &support, &atoms));
        }
        Some(options)
    }

    /// `c·(g & mask)` plus an affine rest, for every bitwise function `g` of the (at most three)
    /// atoms whose conjunction coefficients of two or more atoms, times some `c`, are the
    /// group's: `Σ_S γ_S·(AND_S & M) = c·(g & M) − c·a_∅·M + Σ_i (γ_i − c·a_i)·(x_i & M)` with
    /// `g = Σ_S a_S·AND_S` (Möbius over its table). `c` is solved from the equation with the
    /// fewest factors of two in `a_S`, each solution checked against all of them.
    fn affine_plus(
        &mut self,
        coef: &BTreeMap<u64, BitVec>,
        mask: &BitVec,
        support: &[u32],
        atoms: &[u32],
    ) -> Vec<Sum> {
        let w = self.w;
        let s = support.len();
        if !(2..=3).contains(&s) {
            return Vec::new();
        }
        // The group's coefficients by subset of support positions.
        let mut d = vec![BitVec::zero(w); 1 << s];
        for (&set, k) in coef {
            let q = support
                .iter()
                .enumerate()
                .filter(|&(_, &a)| set >> a & 1 == 1)
                .fold(0usize, |q, (j, _)| q | 1 << j);
            d[q] = *k;
        }
        if (0..1usize << s).all(|q| q.count_ones() < 2 || d[q].is_zero())
            || !self.spend(1u64 << ((1 << s) + s))
        {
            return Vec::new();
        }
        let mut out = Vec::new();
        // Per Möbius coefficient (a small integer): the inverse of its odd part, computed once.
        let mut inverses: Vec<(i64, BitVec)> = Vec::new();
        let wide: Vec<usize> = (0..1usize << s).filter(|q| q.count_ones() >= 2).collect();
        // `c·a_q = d_q` needs `a_q ≠ 0` wherever `d_q ≠ 0`: most tables fail that already.
        let needed = wide
            .iter()
            .filter(|&&q| !d[q].is_zero())
            .fold(0u32, |m, &q| m | 1 << q);
        for tt in 0..1u32 << (1 << s) {
            let table = [u64::from(tt)];
            let a = mobius(&table, s);
            let present = wide
                .iter()
                .filter(|&&q| a[q] != 0)
                .fold(0u32, |m, &q| m | 1 << q);
            if needed & !present != 0 {
                continue;
            }
            let Some(&pivot) = wide
                .iter()
                .filter(|&&q| a[q] != 0)
                .min_by_key(|&&q| (a[q].trailing_zeros(), q))
            else {
                continue;
            };
            let aq = BitVec::wrapping_from_i128(w, i128::from(a[pivot]));
            let v = a[pivot].trailing_zeros();
            if crate::facts::known::trailing_zeros(&d[pivot]) < v {
                continue;
            }
            // c = (d / 2^v)·u⁻¹ mod 2^(W−v), u the odd part of a.
            let inv = match inverses.iter().find(|(k, _)| *k == a[pivot]) {
                Some((_, x)) => *x,
                None => {
                    let u = crate::facts::known::bv_lshr(&aq, v);
                    let x = super::poly::odd_inverse(&u);
                    inverses.push((a[pivot], x));
                    x
                }
            };
            let dv = crate::facts::known::bv_lshr(&d[pivot], v);
            let c0 = BitVec::bin_unchecked(BinOp::Mul, &dv, &inv);
            let step =
                crate::facts::known::bv_shl(&BitVec::one(w), u32::from(w.bits()).saturating_sub(v));
            let mut chosen: Option<BitVec> = None;
            for j in 0..1u64 << v.min(3) {
                let c = BitVec::bin_unchecked(
                    BinOp::Add,
                    &c0,
                    &BitVec::bin_unchecked(BinOp::Mul, &step, &BitVec::wrapping_from_u64(w, j)),
                );
                let fits = wide.iter().all(|&q| {
                    BitVec::bin_unchecked(
                        BinOp::Mul,
                        &c,
                        &BitVec::wrapping_from_i128(w, i128::from(a[q])),
                    ) == d[q]
                });
                if fits {
                    chosen = Some(c);
                    break;
                }
            }
            let Some(c) = chosen else {
                continue;
            };
            let Some(g) = self.min_form(tt as u8 | if s == 2 { (tt as u8) << 4 } else { 0 }, atoms)
            else {
                continue;
            };
            let gm = self.masked(g, mask);
            let a0 = BitVec::wrapping_from_i128(w, i128::from(a[0]));
            let mut sum = Sum {
                terms: vec![(gm, c)],
                konst: Some(BitVec::un_unchecked(
                    UnOp::Neg,
                    &BitVec::bin_unchecked(
                        BinOp::Mul,
                        &BitVec::bin_unchecked(BinOp::Mul, &c, &a0),
                        mask,
                    ),
                )),
            };
            for (j, &x) in atoms.iter().enumerate() {
                let q = 1usize << j;
                let r = BitVec::bin_unchecked(
                    BinOp::Sub,
                    &d[q],
                    &BitVec::bin_unchecked(
                        BinOp::Mul,
                        &c,
                        &BitVec::wrapping_from_i128(w, i128::from(a[q])),
                    ),
                );
                if !r.is_zero() {
                    let xm = self.masked(x, mask);
                    sum.terms.push((xm, r));
                }
            }
            out.push(sum);
        }
        out
    }

    /// A monomial: the product of its symbols' powers (square and multiply).
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

/// The symbols every monomial of `p` contains.
fn common_symbols(p: &Poly) -> Vec<Sym> {
    let mut it = p.terms().keys();
    let Some(first) = it.next() else {
        return Vec::new();
    };
    let mut common: Vec<Sym> = first.iter().map(|&(s, _)| s).collect();
    for m in it {
        common.retain(|s| m.iter().any(|&(t, _)| t == *s));
    }
    common
}
