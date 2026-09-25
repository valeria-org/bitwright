//! Rendering normal forms as expressions. Candidates are built into one builder with local
//! interning (equal subterms are one node), costed by the nodes reachable from their root, and
//! the cheapest is kept: by node count, then by an operator-weighted size, then by structure.

use std::collections::{BTreeMap, HashMap};

use crate::hash::IdMap;

use super::bits::{self, Bits, anf, mobius, table8};
use super::classes::{Classes, FULL};
use super::poly::{Mono, Poly, Sym};
use super::synth;
use crate::engine::pass::bitwise::{T, min_forms, subtables};
use crate::facts::known::{bv_and, bv_not, bv_or, bv_xor, count_ones, trailing_zeros};
use crate::mba::certify;
use crate::mba::expr::{MNode, MOp, MbaExpr};
use crate::mba::solve::Verdict;
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct BNode {
    op: MOp,
    w: Width,
    args: [u32; 2],
}

/// Hashed as two words and a constant's significant limbs (interning hashes every node built).
impl core::hash::Hash for BNode {
    fn hash<H: core::hash::Hasher>(&self, h: &mut H) {
        let (tag, extra) = match self.op {
            MOp::Const(_) => (0u64, 0u64),
            MOp::Var(i) => (1, u64::from(i)),
            MOp::Add => (2, 0),
            MOp::Sub => (3, 0),
            MOp::Mul => (4, 0),
            MOp::Neg => (5, 0),
            MOp::And => (6, 0),
            MOp::Or => (7, 0),
            MOp::Xor => (8, 0),
            MOp::Not => (9, 0),
            MOp::Shl(k) => (10, u64::from(k)),
            MOp::LShr(k) => (11, u64::from(k)),
            MOp::Zext => (12, 0),
            MOp::Sext => (13, 0),
            MOp::Trunc => (14, 0),
        };
        h.write_u64(tag | u64::from(self.w.bits()) << 8 | extra << 24);
        h.write_u64(u64::from(self.args[0]) | u64::from(self.args[1]) << 32);
        if let MOp::Const(v) = &self.op {
            for &l in v.limbs() {
                h.write_u64(l);
            }
        }
    }
}

/// Nodes with local interning.
#[derive(Clone, Debug)]
pub(crate) struct Builder {
    vars: Vec<Width>,
    nodes: Vec<BNode>,
    memo: IdMap<BNode, u32>,
    /// [`Builder::reach`]'s visited marks: a stamp per node, current when equal to the epoch.
    marks: core::cell::RefCell<(Vec<u32>, u32)>,
    /// Costs of candidates already costed (nodes never change once interned).
    costs: core::cell::RefCell<IdMap<u32, Cost>>,
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
            marks: Default::default(),
            costs: Default::default(),
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
            // As the context builds it: `a − c` is `a + (−c)`, whose constant is its own node.
            MOp::Sub if cb.is_some() => {
                let c = cb
                    .map(|c| BitVec::un_unchecked(UnOp::Neg, &c))
                    .unwrap_or(BitVec::zero(w));
                let n = self.konst(&c);
                return self.bin(MOp::Add, a, n);
            }
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
        // `~(−x) ^ y` as `~(−x ^ y)`: the engine's rules rewrite `~(−x)` to `x − 1`, which
        // shares nothing with other uses of `−x`.
        if op == MOp::Xor {
            let neg_under_not = |b: &Builder, i: u32| {
                let n = b.nodes[i as usize];
                (n.op == MOp::Not && b.nodes[n.args[0] as usize].op == MOp::Neg)
                    .then_some(n.args[0])
            };
            if let Some(x) = neg_under_not(self, a) {
                let inner = self.bin(MOp::Xor, x, b);
                return self.un(MOp::Not, inner);
            }
            if let Some(y) = neg_under_not(self, b) {
                let inner = self.bin(MOp::Xor, a, y);
                return self.un(MOp::Not, inner);
            }
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
        let mut marks = self.marks.borrow_mut();
        let (stamp, epoch) = &mut *marks;
        *epoch = epoch.wrapping_add(1);
        if *epoch == 0 {
            stamp.fill(0);
            *epoch = 1;
        }
        if stamp.len() < self.nodes.len() {
            stamp.resize(self.nodes.len(), 0);
        }
        let mut out = Vec::new();
        let mut stack = vec![(root, false)];
        while let Some((i, done)) = stack.pop() {
            if done {
                out.push(i);
                continue;
            }
            let fresh = core::mem::replace(&mut stamp[i as usize], *epoch) != *epoch;
            if !fresh {
                continue;
            }
            stack.push((i, true));
            let n = self.nodes[i as usize];
            for &k in n.args[..n.op.arity()].iter().rev() {
                stack.push((k, false));
            }
        }
        out
    }

    /// The cost of the candidate rooted at `root`: its nodes, counting a shift's amount as the
    /// constant node it is once lifted (shared with an equal constant), one more for each
    /// `a − (a & b)` (the engine's rules read it as `a & ~b`, which shares nothing with other
    /// uses of `a & b`) and one more for the constant 1 where the rules rewrite `~(−x)` to
    /// `x − 1` or `−(~x)` to `x + 1` while the inner node stays for other uses, then operator
    /// weight.
    pub(crate) fn cost(&self, root: u32) -> Cost {
        if let Some(&c) = self.costs.borrow().get(&root) {
            return c;
        }
        let c = self.cost_of(root);
        self.costs.borrow_mut().insert(root, c);
        c
    }

    fn cost_of(&self, root: u32) -> Cost {
        let r = self.reach(root);
        let weight: u32 = r.iter().map(|&i| weight(&self.nodes[i as usize].op)).sum();
        let unstable = r
            .iter()
            .filter(|&&i| {
                let n = self.nodes[i as usize];
                n.op == MOp::Sub && {
                    let m = self.nodes[n.args[1] as usize];
                    m.op == MOp::And && m.args.contains(&n.args[0])
                }
            })
            .count() as u32;
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
        let one = r.first().map(|&i| BitVec::one(self.nodes[i as usize].w));
        let rewritten = one.is_some_and(|one| !consts.contains(&one) && self.rewrites_shared(&r));
        (
            r.len() as u32 + amounts + unstable + u32::from(rewritten),
            weight,
        )
    }

    /// Whether some `~(−x)` or `−(~x)` among `r` (a candidate's nodes) has its inner node used
    /// elsewhere in the candidate too.
    fn rewrites_shared(&self, r: &[u32]) -> bool {
        let inner = |n: &BNode| -> Option<u32> {
            let m = self.nodes[n.args[0] as usize];
            matches!((n.op, m.op), (MOp::Not, MOp::Neg) | (MOp::Neg, MOp::Not)).then_some(n.args[0])
        };
        let sites: Vec<u32> = r
            .iter()
            .filter_map(|&i| inner(&self.nodes[i as usize]))
            .collect();
        if sites.is_empty() {
            return false;
        }
        let mut users = 0usize;
        for &i in r {
            let n = self.nodes[i as usize];
            users += n.args[..n.op.arity()]
                .iter()
                .filter(|a| sites.contains(a))
                .count();
        }
        users > sites.len()
    }

    /// The node that renders `|k|·t` when `|k|` is a power of two above 1 and that node exists
    /// (`t + t`, `t << j`).
    fn multiple(&self, t: u32, k: &BitVec) -> Option<u32> {
        let w = self.width(t);
        let mag = if k.msb() {
            BitVec::un_unchecked(UnOp::Neg, k)
        } else {
            *k
        };
        if count_ones(&mag) != 1 || mag == BitVec::one(w) {
            return None;
        }
        let n = if mag == BitVec::wrapping_from_u64(w, 2) {
            BNode {
                op: MOp::Add,
                w,
                args: [t, t],
            }
        } else {
            BNode {
                op: MOp::Shl(trailing_zeros(&mag) as u16),
                w,
                args: [t, 0],
            }
        };
        self.memo.get(&n).copied()
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
    /// [`poly`](Self::poly)'s renderings by form and depth, and the factors they were rendered
    /// with. A reuse costs the lookup: products render their factors for every quotient, and
    /// charging each reuse the rendering's work spent most of a budget on nothing.
    memo: HashMap<(Poly, u32), Vec<u32>>,
    memo_factors: Vec<Poly>,
    /// What synthesis did.
    pub(crate) synth: SynthTally,
    /// Peels in progress (see [`Render::peel`]); an atom's definition renders as if in one
    /// (see [`Render::for_atom`]).
    peeling: u32,
    /// Whether the linear form being decomposed is a normal form's own linear part (see
    /// [`Render::split_off`]).
    top: bool,
    /// The node count a rendering must stay under to be of use (see [`Render::hopeless`]).
    bar: Option<u32>,
    /// Per atom set, the fewest nodes a rendering over it has.
    floors: HashMap<u64, u32>,
    /// Conjunctions built so far, by atom set (see [`Render::conj`]).
    conjs: HashMap<u64, u32>,
    /// The best forms of tables over four to six atoms (nodes), by table and atoms.
    wide: HashMap<(u64, Vec<u32>), Option<u32>>,
}

/// The most decompositions [`Render::two_terms`] builds over up to three atoms, those whose
/// estimated size is smallest.
const TWO_TERMS_BUILT: usize = 8;

/// The most decompositions of a polynomial's linear part tried beside its nonlinear part.
const LINEAR_JOINED: usize = 8;

/// The best estimated decompositions [`Render::two_terms`] also tries with other forms of
/// their functions, and the most forms of a lone function.
const TWO_TERMS_PAIRED: usize = 3;
const TWO_TERMS_FORMS: usize = 5;

/// The cheapest decompositions [`Render::two_terms`] also weighs with a shared coefficient
/// taken out.
const TWO_TERMS_FACTORED: usize = 8;

/// The most pairs of minimum forms sharing a subterm [`Render::two_terms`] builds per
/// decomposition.
const TWO_TERMS_SHARED: usize = 8;

/// The most splits [`Render::split_off`] decomposes further.
const SPLITS: usize = 2;

/// A split of [`Render::split_off`]: the distinct values left, the operators of `g`, the pair
/// of atoms `g` reads (by position), `g`'s table over them, and `k`.
type Split = (usize, u8, (usize, usize), u8, BitVec);

/// The most symbols a polynomial's nonlinear part is partly factored by, and the most
/// monomials it may have for that.
const PARTIAL_SYMBOLS: usize = 3;
const PARTIAL_TERMS: usize = 12;

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
            peeling: 0,
            top: false,
            bar: None,
            floors: HashMap::new(),
            conjs: HashMap::new(),
            wide: HashMap::new(),
        }
    }

    /// Renders an atom's definition: with the decompositions a peel's rest gets (no groups,
    /// peels, pairings of other forms or splits, which are for a question's own form).
    pub(crate) fn for_atom(mut self) -> Self {
        self.peeling = 1;
        self
    }

    /// Renders only what can come in under `bar` nodes (an answer must be smaller than the
    /// question): forms whose atoms alone reach it are not rendered at all.
    pub(crate) fn with_bar(mut self, bar: u32) -> Self {
        self.bar = Some(bar);
        self
    }

    /// Whether no rendering of a form over the atoms in `set` comes in under the bar. The form
    /// is canonical over independent atoms, so each of its renderings reads every atom in
    /// `set`: it has at least the nodes of their renderings, and a node joining each further
    /// atom that no other contains (nothing inside one reaches another).
    pub(crate) fn hopeless(&mut self, set: u64) -> bool {
        let Some(bar) = self.bar else {
            return false;
        };
        if let Some(&floor) = self.floors.get(&set) {
            return floor >= bar;
        }
        let mut roots: Vec<u32> = Vec::new();
        for a in (0..64u32).filter(|&a| set >> a & 1 == 1) {
            let Some(n) = self.atom(a) else {
                return false;
            };
            if !roots.contains(&n) {
                roots.push(n);
            }
        }
        let reaches: Vec<Vec<u32>> = roots.iter().map(|&n| self.b.reach(n)).collect();
        let mut union: Vec<u32> = reaches.iter().flatten().copied().collect();
        union.sort_unstable();
        union.dedup();
        let tops = roots
            .iter()
            .enumerate()
            .filter(|&(i, n)| {
                !reaches
                    .iter()
                    .enumerate()
                    .any(|(j, r)| j != i && r.contains(n))
            })
            .count();
        let floor = union.len() as u32 + tops.saturating_sub(1) as u32;
        self.floors.insert(set, floor);
        floor >= bar
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

    /// The most work candidate generation may spend.
    pub(crate) fn limit(&self) -> u64 {
        self.limit
    }

    /// Sets the most work candidate generation may spend (from here on).
    pub(crate) fn set_limit(&mut self, limit: u64) {
        self.limit = limit;
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

    /// `p = f·q + r` (see [`Poly::div_rem`]), charged to the meter like [`Render::divide`].
    fn divide_rem(&mut self, p: &Poly, f: &Poly) -> Option<(Poly, Poly)> {
        let cap = (4 * p.len() as u64 + 16) * f.len() as u64 + p.len() as u64;
        let room = self.limit.saturating_sub(self.work) / DIVISION_STEP;
        let start = cap.min(room);
        let mut left = start;
        let q = p.div_rem(f, &mut left);
        self.spend((start - left) * DIVISION_STEP + 1);
        match q {
            Ok(q) => q,
            Err(()) => {
                if room < cap {
                    self.work = self.limit.saturating_add(1);
                }
                None
            }
        }
    }

    /// The factors and quotients of the products the candidate at `root` uses (to try as
    /// factors in a next round), but for single monomials.
    pub(crate) fn factors_of(&self, root: u32) -> Vec<Poly> {
        let mut out: Vec<Poly> = Vec::new();
        for n in self.b.reach(root) {
            if let Some((f, q)) = self.products.get(&n) {
                for x in [f, q] {
                    if x.degree() >= 1 && x.len() >= 2 && !out.contains(x) {
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

    /// `AND_set`: on a conjunction of all atoms but one already built, when there is one (so
    /// `x & (b & z)` shares `b & z`), else in ascending atoms.
    fn conj(&mut self, set: u64) -> Option<u32> {
        if let Some(&n) = self.conjs.get(&set) {
            return Some(n);
        }
        let n = if set.count_ones() >= 3
            && let Some((rest, a)) = (0..64u32)
                .filter(|&a| set >> a & 1 == 1)
                .find_map(|a| self.conjs.get(&(set & !(1 << a))).map(|&r| (r, a)))
        {
            let x = self.atom(a)?;
            self.b.bin(MOp::And, rest, x)
        } else {
            let mut acc: Option<u32> = None;
            let mut sub = 0u64;
            for a in 0..64u32 {
                if set >> a & 1 == 1 {
                    let n = self.atom(a)?;
                    sub |= 1 << a;
                    acc = Some(match acc {
                        None => n,
                        Some(x) => self.b.bin(MOp::And, x, n),
                    });
                    if let Some(x) = acc {
                        self.conjs.entry(sub).or_insert(x);
                    }
                }
            }
            acc?
        };
        self.conjs.insert(set, n);
        Some(n)
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

    /// `k·t` for a coefficient `k` (positive in the signed sense): `t`, `t + t` (one node,
    /// where a shift needs its amount too), a shift, or a product.
    fn scaled(&mut self, t: u32, k: &BitVec) -> u32 {
        if *k == BitVec::one(self.w) {
            return t;
        }
        if *k == BitVec::wrapping_from_u64(self.w, 2) {
            return self.b.bin(MOp::Add, t, t);
        }
        if count_ones(k) == 1 {
            let s = trailing_zeros(k);
            return self.b.un(MOp::Shl(s as u16), t);
        }
        let c = self.b.konst(k);
        self.b.bin(MOp::Mul, t, c)
    }

    /// Emits `Σ kᵢ·tᵢ + c`: terms of one node merged (`(a + b)·t` is never larger than
    /// `a·t + b·t`), positive coefficients first, then the others, subtracted (or added with
    /// their negative coefficient when that constant is needed anyway), powers of two as shifts,
    /// the constant last.
    pub(crate) fn sum(&mut self, s: &Sum) -> u32 {
        let w = self.w;
        self.spend(4 * s.terms.len() as u64 + 1);
        let mut acc: Option<u32> = None;
        type Terms = Vec<(u32, BitVec)>;
        let mut merged: Terms = Vec::with_capacity(s.terms.len());
        // Each node's position in `merged`, for sums too long to search (same order either way).
        let indexed = s.terms.len() > 8;
        let mut at: IdMap<u32, usize> = IdMap::default();
        for &(t, k) in &s.terms {
            let found = if indexed {
                at.get(&t).copied()
            } else {
                merged.iter().position(|(u, _)| *u == t)
            };
            match found {
                Some(j) => merged[j].1 = BitVec::bin_unchecked(BinOp::Add, &merged[j].1, &k),
                None => {
                    if indexed {
                        at.insert(t, merged.len());
                    }
                    merged.push((t, k));
                }
            }
        }
        // A term whose power-of-two multiple is another term's node goes into that term
        // (`−2·a` beside an atom rendered `a + a`).
        let mut i = 0;
        while i < merged.len() {
            let (t, k) = merged[i];
            let into = self.b.multiple(t, &k).and_then(|x| {
                if indexed {
                    at.get(&x).copied()
                } else {
                    merged.iter().position(|&(u, _)| u == x)
                }
            });
            match into {
                Some(j) if j != i => {
                    let one = if k.msb() {
                        BitVec::ones(w)
                    } else {
                        BitVec::one(w)
                    };
                    merged[j].1 = BitVec::bin_unchecked(BinOp::Add, &merged[j].1, &one);
                    merged.remove(i);
                    if indexed {
                        at.clear();
                        at.extend(merged.iter().enumerate().map(|(p, &(u, _))| (u, p)));
                    }
                    i = 0;
                }
                _ => i += 1,
            }
        }
        let (pos, mut neg): (Terms, Terms) = merged
            .into_iter()
            .filter(|(_, k)| !k.is_zero())
            .partition(|(_, k)| !k.msb());
        let mut k = s.konst.unwrap_or(BitVec::zero(w));
        // Only subtracted terms and no constant: a term with a coefficient other than −1 goes
        // first, a product by its negative coefficient, and the others are subtracted from it
        // (`t·−2 − ~y`, not `−~y − (t + t)`, whose `−~y` the rules read as `y + 1`).
        if pos.is_empty()
            && k.is_zero()
            && let Some(i) = neg.iter().position(|(_, c)| *c != BitVec::ones(w))
        {
            neg.swap(0, i);
        }
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
                // coefficient (`t·k` is smaller than `−(t << j)`, whose amount is a constant
                // too), or negate a coefficient of −1.
                None if !k.is_zero() && !reuse => {
                    let a = self.b.konst(&k);
                    k = BitVec::zero(w);
                    let x = self.scaled(t, &nc);
                    self.b.bin(MOp::Sub, a, x)
                }
                None if nc == BitVec::one(w) => self.b.un(MOp::Neg, t),
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
        } else if s <= 6 {
            out.extend(self.wide_forms(t[0], &atoms));
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

    /// Forms of a table of 4 to 6 atoms (one word): a single true entry as the negated or of
    /// literals (`~(x | y | ~z | t)`), a single false one as their or, each split on one atom
    /// `a`, `f = a ? f₁ : f₀`, its halves rendered the same way down to three atoms (`a & f₁`,
    /// `~a & f₀`, `a ^ f₀`, `a | f₀`, `~a | f₁`, or `f₀ ^ (a & (f₀ ^ f₁))`), and each
    /// decomposition `f = g(free, h(bound))` (see [`Render::decompositions`]).
    fn wide_forms(&mut self, t: u64, atoms: &[u32]) -> Vec<u32> {
        let w = self.w;
        let s = atoms.len();
        let entries = 1usize << s;
        let full = if entries == 64 {
            u64::MAX
        } else {
            (1u64 << entries) - 1
        };
        let t = t & full;
        let mut out = Vec::new();
        if !self.spend(entries as u64 * s as u64) {
            return out;
        }
        if t == 0 || t == full {
            let v = if t == 0 {
                BitVec::zero(w)
            } else {
                BitVec::ones(w)
            };
            out.push(self.b.konst(&v));
            return out;
        }
        // A single true (false) entry: the negated or (the or) of literals.
        for (target, negate) in [(t, true), (!t & full, false)] {
            if target.count_ones() != 1 {
                continue;
            }
            let e = target.trailing_zeros() as usize;
            let mut acc: Option<u32> = None;
            for (j, &a) in atoms.iter().enumerate() {
                // In `~(… | l | …)` each literal is false at the entry; in `… | l | …` false too.
                let lit = if e >> j & 1 == 1 {
                    self.b.un(MOp::Not, a)
                } else {
                    a
                };
                acc = Some(match acc {
                    None => lit,
                    Some(x) => self.b.bin(MOp::Or, x, lit),
                });
            }
            if let Some(x) = acc {
                out.push(if negate { self.b.un(MOp::Not, x) } else { x });
            }
        }
        // Splits on one atom.
        for j in 0..s {
            let (mut f0, mut f1) = (0u64, 0u64);
            let mut k = 0;
            for e in 0..entries {
                if e >> j & 1 == 1 {
                    continue;
                }
                f0 |= (t >> e & 1) << k;
                f1 |= (t >> (e | 1 << j) & 1) << k;
                k += 1;
            }
            let rest: Vec<u32> = atoms
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != j)
                .map(|(_, &x)| x)
                .collect();
            let a = atoms[j];
            let half = 1usize << (s - 1);
            let hfull = if half == 64 {
                u64::MAX
            } else {
                (1u64 << half) - 1
            };
            let x = match (f0, f1) {
                _ if f0 == f1 => self.best_of_table(f0, &rest),
                (0, _) => self
                    .best_of_table(f1, &rest)
                    .map(|g| self.b.bin(MOp::And, a, g)),
                (_, 0) => self.best_of_table(f0, &rest).map(|g| {
                    let na = self.b.un(MOp::Not, a);
                    self.b.bin(MOp::And, na, g)
                }),
                _ if f0 == hfull => self.best_of_table(f1, &rest).map(|g| {
                    let na = self.b.un(MOp::Not, a);
                    self.b.bin(MOp::Or, na, g)
                }),
                _ if f1 == hfull => self
                    .best_of_table(f0, &rest)
                    .map(|g| self.b.bin(MOp::Or, a, g)),
                _ if f1 == !f0 & hfull => self
                    .best_of_table(f0, &rest)
                    .map(|g| self.b.bin(MOp::Xor, a, g)),
                _ => match (
                    self.best_of_table(f0, &rest),
                    self.best_of_table(f0 ^ f1, &rest),
                ) {
                    (Some(g0), Some(d)) => {
                        let m = self.b.bin(MOp::And, a, d);
                        Some(self.b.bin(MOp::Xor, g0, m))
                    }
                    _ => None,
                },
            };
            out.extend(x);
            if self.exhausted() {
                break;
            }
        }
        out.extend(self.decompositions(t, atoms));
        out
    }

    /// Decompositions `f = g(free, h(bound))` of a table over 4 or 5 atoms: a set of two or
    /// three atoms `f` reads only through one function `h` of them (its chart has at most two
    /// distinct columns), `h` and `g` (with `h`'s node as an atom) each of at most three inputs,
    /// rendered by their minimum forms (`~((d ^ s) | ((u | v) ^ d))` reads `u` and `v` only
    /// through `u | v`).
    fn decompositions(&mut self, t: u64, atoms: &[u32]) -> Vec<u32> {
        let s = atoms.len();
        let entries = 1usize << s;
        let mut out = Vec::new();
        // `g` reads the free atoms and `h`: at most three.
        for size in s.saturating_sub(2).max(2)..=3usize.min(s - 1) {
            for bound in 0u32..1 << s {
                if bound.count_ones() as usize != size || self.exhausted() {
                    continue;
                }
                if !self.spend(entries as u64 + 16) {
                    return out;
                }
                let bi: Vec<usize> = (0..s).filter(|&j| bound >> j & 1 == 1).collect();
                let fi: Vec<usize> = (0..s).filter(|&j| bound >> j & 1 == 0).collect();
                // Per value of the bound atoms, the function of the free ones.
                let mut cols = vec![0u64; 1 << size];
                for e in 0..entries {
                    if t >> e & 1 == 0 {
                        continue;
                    }
                    let b = bi
                        .iter()
                        .enumerate()
                        .fold(0usize, |q, (k, &j)| q | (e >> j & 1) << k);
                    let f = fi
                        .iter()
                        .enumerate()
                        .fold(0usize, |q, (k, &j)| q | (e >> j & 1) << k);
                    cols[b] |= 1 << f;
                }
                let c0 = cols[0];
                let Some(&c1) = cols.iter().find(|&&c| c != c0) else {
                    continue;
                };
                if cols.iter().any(|&c| c != c0 && c != c1) {
                    continue;
                }
                let h = (0..1usize << size)
                    .filter(|&b| cols[b] == c1)
                    .fold(0u64, |t, b| t | 1 << b);
                let bound_atoms: Vec<u32> = bi.iter().map(|&j| atoms[j]).collect();
                let Some(hn) = self.best_of_table(h, &bound_atoms) else {
                    continue;
                };
                // `g(free, x)`: the column `c1` where `x` is set, `c0` where it is not.
                let half = 1u32 << fi.len();
                let g = c0 | c1 << half;
                let mut g_atoms: Vec<u32> = fi.iter().map(|&j| atoms[j]).collect();
                g_atoms.push(hn);
                out.extend(self.best_of_table(g, &g_atoms));
            }
        }
        out
    }

    /// The best form of a one-word table over `atoms` (nodes), at most six of them.
    fn best_of_table(&mut self, t: u64, atoms: &[u32]) -> Option<u32> {
        let s = atoms.len();
        if s <= 3 {
            let entries = 1usize << s;
            let mut tt = 0u8;
            for e in 0..8usize {
                // An 8-bit table over three inputs, the missing ones not read.
                if t >> (e % entries) & 1 == 1 {
                    tt |= 1 << e;
                }
            }
            let padded: Vec<u32> = match s {
                0 => {
                    let v = if t & 1 == 1 {
                        BitVec::ones(self.w)
                    } else {
                        BitVec::zero(self.w)
                    };
                    return Some(self.b.konst(&v));
                }
                _ => atoms.to_vec(),
            };
            return self.min_form(tt, &padded);
        }
        // Splits and decompositions meet the same tables again: each once.
        let key = (t, atoms.to_vec());
        if let Some(&x) = self.wide.get(&key) {
            self.spend(s as u64);
            return x;
        }
        let c = self.wide_forms(t, atoms);
        let x = self.best(&c);
        if !self.exhausted() {
            self.wide.insert(key, x);
        }
        x
    }

    /// The minimum-size form of an 8-bit table over `atoms` (at most three).
    fn min_form(&mut self, tt: u8, atoms: &[u32]) -> Option<u32> {
        let (tmpl, _) = &min_forms().forms[tt as usize];
        self.template(tmpl, atoms)
    }

    /// A minimum-form template built over `atoms`.
    fn template(&mut self, tmpl: &[T], atoms: &[u32]) -> Option<u32> {
        let w = self.w;
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
        self.bits_with(f, &BitVec::zero(self.w))
    }

    /// Renderings of `f ^ extra` for a constant `extra`: a function whose bits do not all
    /// follow the classes, as `(x & ~3) ^ k` does with `k` when no bitwise operand splits the
    /// classes by `k`. Each class's positions in `extra` have its table complemented.
    fn bits_with(&mut self, f: &Bits, extra: &BitVec) -> Vec<u32> {
        let w = self.w;
        let s = f.support.len();
        if !self.spend((f.tables.len() as u64) << s) {
            return Vec::new();
        }
        if f.uniform() && extra.is_zero() {
            return self.uniform(&f.tables[0], &f.support);
        }
        let n = self.classes.len();
        // Positions grouped by table.
        let mut groups: Vec<(Vec<u64>, BitVec)> = Vec::new();
        for c in 0..n {
            let mask = self.classes.mask(c);
            let t = &f.tables[c];
            let mut nt: Vec<u64> = t.iter().map(|x| !x).collect();
            if s < 6 {
                nt[0] &= (1u64 << (1usize << s)) - 1;
            }
            for (t, m) in [
                (t, bv_and(mask, &bv_not(extra))),
                (&nt, bv_and(mask, extra)),
            ] {
                if m.is_zero() {
                    continue;
                }
                match groups.iter_mut().find(|(g, _)| g == t) {
                    Some((_, gm)) => *gm = bv_or(gm, &m),
                    None => groups.push((t.clone(), m)),
                }
            }
        }
        if let [(t, _)] = groups.as_slice() {
            let t = t.clone();
            return self.uniform(&t, &f.support);
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
        // ((g ^ A) | B) & ~C for a base table g: positions with ¬g in A, all-ones in B, zero in
        // C. With all three, (g & M) ^ K is smaller: M the positions with g or ¬g, K those with
        // ¬g or all-ones.
        let bases: Vec<Vec<u64>> = groups
            .iter()
            .filter(|(t, _)| !full(t) && !empty(t))
            .map(|(t, _)| t.clone())
            .collect();
        for g in &bases {
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
                if t == g {
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
            let Some(base) = self.best_uniform(g, &f.support) else {
                continue;
            };
            let mut r = base;
            if !a.is_zero() {
                let k = self.b.konst(&a);
                r = self.b.bin(MOp::Xor, r, k);
            }
            if !b.is_zero() {
                let k = self.b.konst(&b);
                r = self.b.bin(MOp::Or, r, k);
            }
            if !c.is_zero() {
                r = self.masked(r, &bv_not(&c));
            }
            out.push(r);
            if !a.is_zero() && !b.is_zero() && !c.is_zero() {
                let r = self.masked(base, &bv_not(&bv_or(&b, &c)));
                let k = self.b.konst(&bv_or(&a, &b));
                out.push(self.b.bin(MOp::Xor, r, k));
            }
        }
        // g(x₁ ^ A₁, …) ^ O for a base table g of at most three atoms, when every class's table
        // is g with some inputs complemented, and maybe its output: `Aᵢ` the classes that
        // complement input `i`, `O` those that complement the output.
        if s <= 3 {
            let entries = 1usize << s;
            let all = (1u64 << entries) - 1;
            for g in &bases {
                let g0 = g[0] & all;
                let mut flips = vec![BitVec::zero(w); s];
                let mut o = BitVec::zero(w);
                let mut fits = true;
                for (t, m) in &groups {
                    let t0 = t[0] & all;
                    let hit =
                        (0..entries)
                            .flat_map(|f| [(f, false), (f, true)])
                            .find(|&(f, neg)| {
                                let x = flip_inputs(g0, s, f);
                                (if neg { !x & all } else { x }) == t0
                            });
                    let Some((f, neg)) = hit else {
                        fits = false;
                        break;
                    };
                    for (j, a) in flips.iter_mut().enumerate() {
                        if f >> j & 1 == 1 {
                            *a = bv_or(a, m);
                        }
                    }
                    if neg {
                        o = bv_or(&o, m);
                    }
                }
                // Without complemented inputs this is the form above.
                if !fits || flips.iter().all(BitVec::is_zero) {
                    continue;
                }
                let Some(tt) = table8(g, s) else {
                    continue;
                };
                let mut ins = Vec::with_capacity(s);
                for (&a, k) in f.support.iter().zip(&flips) {
                    let Some(x) = self.atom(a) else {
                        return out;
                    };
                    ins.push(if k.is_zero() {
                        x
                    } else {
                        let k = self.b.konst(k);
                        self.b.bin(MOp::Xor, x, k)
                    });
                }
                let Some(mut x) = self.min_form(tt, &ins) else {
                    continue;
                };
                if !o.is_zero() {
                    let k = self.b.konst(&o);
                    x = self.b.bin(MOp::Xor, x, k);
                }
                out.push(x);
            }
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
        // Only the form's own linear part, not the parts decompositions render.
        let top = core::mem::replace(&mut self.top, false);
        let out = self.linear_sums_at(p, top);
        self.top = top;
        out
    }

    fn linear_sums_at(&mut self, p: &Poly, top: bool) -> Vec<Sum> {
        let w = self.w;
        let mut out: Vec<Sum> = Vec::new();
        if self.hopeless(p.atoms()) || !self.spend(p.len() as u64 * self.classes.len() as u64) {
            return out;
        }
        let plain = Bits::from_linear(&p.expand_full(self.classes), self.classes);
        if let Some(f) = &plain {
            for n in self.bits(f) {
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
        if n > 1
            && let Some(s) = self.affine_bits(p)
        {
            out.push(s);
        }
        out.extend(self.scaled_bits(p, plain.is_some()));
        out.extend(self.two_terms(p));
        if top && self.peeling == 0 {
            out.extend(self.split_off(p));
        }
        // What a peel leaves is rendered without the searches over independent groups and
        // further peels: they would multiply the peel's work.
        if self.peeling == 0 {
            out.extend(self.components(p));
            out.extend(self.peel(p));
        }
        // `c·~h = −c·h − c`, and back: a complement traded for a constant.
        let variants: Vec<Sum> = out.iter().flat_map(|s| self.complements(s)).collect();
        out.extend(variants);
        self.built += out.len() as u64;
        out
    }

    /// The cheapest decomposition `Σ βᵢ·xᵢ ± g (+ k)` of a degree-≤1 form, `g` one bitwise
    /// function (a table per class) and the `xᵢ` unmasked atoms. The coefficient of a single
    /// atom in a bitwise function is −1, 0 or 1 in every class, so `βᵢ` is within one of the
    /// atom's coefficient in each class (modulo that class's precision): a few choices per
    /// atom, for at most three atoms with such terms. Each choice is checked on the tables'
    /// corner sums before anything is built. For example `2·(x & ~4) + (p & ~4) −
    /// (x & p & ~4) + (x & p & 4) + 4` is `x + ((x ^ 4) | p)`.
    fn affine_bits(&mut self, p: &Poly) -> Option<Sum> {
        let w = self.w;
        let n = self.classes.len();
        let single = |m: &Mono| matches!(m.as_slice(), [(s, 1)] if s.set.count_ones() == 1);
        if p.atoms().count_ones() > 5
            || !p.terms().keys().any(single)
            || !self.spend(p.len() as u64 * n as u64)
        {
            return None;
        }
        let q = p.expand_full(self.classes);
        let prec = |c: usize| u32::from(w.bits()) - u32::from(self.classes.low(c));
        let atoms = q.atoms();
        let support: Vec<u32> = (0..64).filter(|&a| atoms >> a & 1 == 1).collect();
        let s = support.len();
        if s == 0 || s > 5 {
            return None;
        }
        let entries = 1usize << s;
        let index = |set: u64| {
            support
                .iter()
                .enumerate()
                .filter(|&(_, &a)| set >> a & 1 == 1)
                .fold(0usize, |q, (j, _)| q | 1 << j)
        };
        // Per class, the coefficient of each conjunction (by subset of the support). One of
        // `k ≥ 2` atoms keeps its coefficient, which in a bitwise function is at most
        // `2^(k−1)` in size (an alternating sum of `2^k` table entries): else none fits.
        let mut gamma = vec![vec![BitVec::zero(w); entries]; n];
        for (m, c) in q.terms() {
            let sym = match m.as_slice() {
                [] => continue,
                [(sym, 1)] => sym,
                _ => return None,
            };
            let class = usize::from(sym.class);
            let k = sym.set.count_ones();
            if k >= 2 {
                let v = super::poly::signed_rep(c, prec(class)).to_i128();
                if v.is_none_or(|v| v.abs() > 1i128 << (k - 1).min(64)) {
                    return None;
                }
            }
            *gamma.get_mut(class)?.get_mut(index(sym.set))? = *c;
        }
        let singles: Vec<usize> = (0..s)
            .filter(|&j| gamma.iter().any(|g| !g[1 << j].is_zero()))
            .collect();
        if singles.is_empty()
            || singles.len() > 3
            || !self.spend(27 * 4 * (n * entries) as u64 + q.len() as u64)
        {
            return None;
        }
        let top = (0..n)
            .max_by_key(|&c| (prec(c), core::cmp::Reverse(c)))
            .unwrap_or(0);
        let sub = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Sub, a, b);
        let add = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Add, a, b);
        let low = |c: usize| crate::facts::known::low_mask(w, prec(c));
        // `v ∈ {−1, 0, 1}`, and `v ∈ {0, 1}`, modulo class `c`'s precision.
        let within_one = |v: &BitVec, c: usize| {
            let v = bv_and(v, &low(c));
            v.is_zero() || v == BitVec::one(w) || v == low(c)
        };
        let bit = |v: &BitVec, c: usize| {
            let v = bv_and(v, &low(c));
            v.is_zero() || v == BitVec::one(w)
        };
        let mut choices: Vec<(usize, Vec<BitVec>)> = Vec::new();
        for &j in &singles {
            let mut betas: Vec<BitVec> = Vec::new();
            for d in [0i128, -1, 1] {
                let b = sub(&gamma[top][1 << j], &BitVec::wrapping_from_i128(w, d));
                let b = super::poly::signed_rep(&b, prec(top));
                if (0..n).all(|c| within_one(&sub(&gamma[c][1 << j], &b), c)) && !betas.contains(&b)
                {
                    betas.push(b);
                }
            }
            if betas.is_empty() {
                return None;
            }
            choices.push((j, betas));
        }
        // Per class and corner: the sum of the coefficients of the conjunctions inside it.
        let mut corner = gamma;
        for t in corner.iter_mut() {
            for b in 0..s {
                for p in 0..entries {
                    if p >> b & 1 == 1 {
                        t[p] = add(&t[p], &t[p ^ 1 << b]);
                    }
                }
            }
        }
        // Per class: the constant's bit there, for the form and for its negation.
        let konst = q.konst();
        let class_bit = |v: &BitVec, c: usize| {
            self.classes
                .bit(v, c)
                .map(|b| if b { BitVec::one(w) } else { BitVec::zero(w) })
        };
        let neg_konst = BitVec::un_unchecked(UnOp::Neg, &konst);
        let kbits: [Vec<Option<BitVec>>; 2] = [
            (0..n).map(|c| class_bit(&konst, c)).collect(),
            (0..n).map(|c| class_bit(&neg_konst, c)).collect(),
        ];
        let combos: usize = choices.iter().map(|(_, b)| b.len()).product();
        let mut out = Vec::new();
        for mut i in 0..combos {
            let mut beta = vec![BitVec::zero(w); s];
            for (j, betas) in &choices {
                beta[*j] = betas[i % betas.len()];
                i /= betas.len();
            }
            if beta.iter().all(BitVec::is_zero) {
                // The whole is a bitwise function: already a decomposition.
                continue;
            }
            let mut bsum = vec![BitVec::zero(w); entries];
            for p in 1..entries {
                bsum[p] = add(&bsum[p & (p - 1)], &beta[p.trailing_zeros() as usize]);
            }
            for with_konst in [true, false] {
                if !with_konst && konst.is_zero() {
                    continue;
                }
                for (sign, kb) in [(BitVec::one(w), &kbits[0]), (BitVec::ones(w), &kbits[1])] {
                    // The table of `±(form − Σ βᵢ·xᵢ)` in each class: its constant's bit plus
                    // the corner sums, each 0 or 1.
                    let fits = (0..n).all(|c| {
                        let k0 = if with_konst {
                            kb[c]
                        } else {
                            Some(BitVec::zero(w))
                        };
                        let Some(k0) = k0 else {
                            return false;
                        };
                        (0..entries).all(|p| {
                            let d = BitVec::bin_unchecked(
                                BinOp::Mul,
                                &sign,
                                &sub(&corner[c][p], &bsum[p]),
                            );
                            bit(&add(&k0, &d), c)
                        })
                    });
                    if !fits {
                        continue;
                    }
                    let mut rest = q.clone();
                    let mut terms = Vec::new();
                    for (j, b) in beta.iter().enumerate() {
                        if b.is_zero() {
                            continue;
                        }
                        let nb = BitVec::un_unchecked(UnOp::Neg, b);
                        let set = 1u64 << support[j];
                        for c in 0..n {
                            rest.add_term(
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
                        terms.push((self.atom(support[j])?, *b));
                    }
                    if !with_konst {
                        rest.add_term(Vec::new(), &neg_konst);
                    }
                    let form = if sign.is_ones() { rest.neg() } else { rest };
                    let Some(f) = Bits::from_linear(&form, self.classes) else {
                        continue;
                    };
                    let renderings = self.bits(&f);
                    let Some(g) = self.best(&renderings) else {
                        continue;
                    };
                    terms.push((g, sign));
                    out.push(Sum {
                        terms,
                        konst: (!with_konst).then_some(konst),
                    });
                }
            }
        }
        self.cheapest(out)
    }

    /// Decompositions `s·g + d` of a degree-≤1 form, `g` a bitwise function (with bits of a
    /// constant the classes do not follow, see [`bits_with`](Self::bits_with)) and `s` odd:
    /// the form times `s⁻¹` is then `g` plus a constant. An atom's coefficient in a bitwise
    /// function is −1, 0 or 1 in every class, so `±s` is an atom's coefficient in the most
    /// precise class that has one. In each class the corner sums force `g`'s value at zero
    /// (to 0 where they reach 1, to 1 where they reach −1) or leave it free, and a free class
    /// takes the constant's bits. For example `1111·x + 1111·k − 2222·(x & k)` is
    /// `(x ^ k)·1111`, and `k + (x & ~3) − 2·(x & k & ~3)` is `(x & ~3) ^ k` even when no
    /// bitwise operand has `k`'s bits. `plain` says the form is itself a bitwise function
    /// (then `s = 1` is not tried again).
    fn scaled_bits(&mut self, p: &Poly, plain: bool) -> Vec<Sum> {
        let w = self.w;
        let n = self.classes.len();
        let q = p.expand_full(self.classes);
        let atoms = q.atoms();
        if atoms == 0 || atoms.count_ones() > 5 || !self.spend(q.len() as u64 + n as u64) {
            return Vec::new();
        }
        let prec = |c: usize| u32::from(w.bits()) - u32::from(self.classes.low(c));
        let mut scales: Vec<BitVec> = Vec::new();
        for a in (0..64u32).filter(|&a| atoms >> a & 1 == 1).take(3) {
            let top = q
                .terms()
                .iter()
                .filter_map(|(m, c)| match m.as_slice() {
                    [(sym, 1)] if sym.set == 1u64 << a => {
                        let class = usize::from(sym.class);
                        let v = super::poly::signed_rep(c, prec(class));
                        (!v.is_zero()).then_some(((prec(class), core::cmp::Reverse(class)), v))
                    }
                    _ => None,
                })
                .max_by(|x, y| x.0.cmp(&y.0))
                .map(|(_, v)| v);
            let Some(v) = top else {
                continue;
            };
            if !v.bit(0).unwrap_or(false) {
                continue;
            }
            for k in [v, BitVec::un_unchecked(UnOp::Neg, &v)] {
                if !scales.contains(&k) && !(plain && k == BitVec::one(w)) {
                    scales.push(k);
                }
            }
        }
        let sub = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Sub, a, b);
        let mut out = Vec::new();
        for k in scales {
            if !self.spend(q.len() as u64 + ((n as u64) << atoms.count_ones())) {
                break;
            }
            let ps = q.scale(&super::poly::odd_inverse(&k));
            let Some(zv) = Bits::zero_values(&ps, self.classes) else {
                continue;
            };
            let kp = ps.konst();
            // The top position: complementing `g` there adds `2^(W−1)`, whatever `g`'s value.
            let top = crate::facts::known::bv_shl(&BitVec::one(w), u32::from(w.bits()) - 1);
            let flipped = bv_xor(&kp, &top);
            let (mut g0, mut extra) = (BitVec::zero(w), BitVec::zero(w));
            for (c, &([zero, one], moved)) in zv.iter().enumerate() {
                let mask = self.classes.mask(c);
                let has_top = !bv_and(mask, &top).is_zero();
                // The constant's bit throughout the class, maybe but for the top position.
                let (bit, flip) = match self.classes.bit(&kp, c) {
                    Some(b) => (Some(b), false),
                    None if has_top => (self.classes.bit(&flipped, c), true),
                    None => (None, false),
                };
                let set = match (zero, one, bit) {
                    (true, false, _) => false,
                    (false, true, _) => true,
                    (_, _, Some(b)) => b,
                    _ => {
                        if !moved {
                            extra = bv_or(&extra, &bv_and(&kp, mask));
                        }
                        false
                    }
                };
                if bit == Some(set) && flip {
                    extra = bv_or(&extra, &top);
                }
                if set {
                    g0 = bv_or(&g0, mask);
                }
            }
            // `g = h ^ extra = h + extra` (`h` is 0 where `extra` has bits, or they are the top
            // position): `ps = h + extra + d'` with `h`'s constant `g0`.
            let dp = sub(&sub(&kp, &g0), &extra);
            let mut h = ps;
            h.add_term(Vec::new(), &sub(&g0, &kp));
            let Some(f) = Bits::from_linear(&h, self.classes) else {
                continue;
            };
            let renderings = self.bits_with(&f, &extra);
            let Some(g) = self.best(&renderings) else {
                continue;
            };
            let d = BitVec::bin_unchecked(BinOp::Mul, &k, &dp);
            out.push(Sum {
                terms: vec![(g, k)],
                konst: (!d.is_zero()).then_some(d),
            });
        }
        out
    }

    /// The cheapest decomposition `c + a·g + b·h` of a degree-≤1 form of two or three atoms
    /// whose symbols are all unmasked, `g` and `h` bitwise functions. Such a form is determined
    /// by its values at the corners where every atom is 0 or all-ones, and a bitwise function is
    /// −1 at the corners where it holds and 0 at the others: for each `g`, the coefficients `a`
    /// that leave two values at the corners, `c` and `c − b`, are read off, and `h` holds where
    /// the second is. For example `−7·x − 4·~(x ^ y) + 4·y + …` is `−7·~y + 4·(x ^ y)`.
    fn two_terms(&mut self, p: &Poly) -> Option<Sum> {
        self.two_terms_by(p, true)
    }

    /// [`Render::two_terms`]; without `enumerate`, the decompositions are read off the
    /// values only (as over more than three atoms), not searched over every table.
    fn two_terms_by(&mut self, p: &Poly, enumerate: bool) -> Option<Sum> {
        let w = self.w;
        let n = self.classes.len();
        let atoms = p.atoms();
        let s = atoms.count_ones() as usize;
        if !(2..=6).contains(&s) {
            return None;
        }
        let support: Vec<u32> = (0..64).filter(|&a| atoms >> a & 1 == 1).collect();
        let corners = 1usize << s;
        let index = |set: u64| {
            support
                .iter()
                .enumerate()
                .filter(|&(_, &a)| set >> a & 1 == 1)
                .fold(0usize, |q, (j, _)| q | 1 << j)
        };
        let add = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Add, a, b);
        let sub = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Sub, a, b);
        let mut d = vec![BitVec::zero(w); corners];
        for (m, c) in p.terms() {
            match m.as_slice() {
                [] => {}
                [(sym, 1)] if sym.class == FULL || n == 1 => {
                    let q = index(sym.set);
                    d[q] = add(&d[q], c);
                }
                _ => return None,
            }
        }
        let tables = if s <= 3 && enumerate {
            1u64 << corners
        } else {
            0
        };
        if !self.spend(tables * corners as u64 * 4 + corners as u64 * 16) {
            return None;
        }
        // The value at corner `P`: the constant minus the coefficients of the conjunctions
        // inside `P` (each −1 there).
        for b in 0..s {
            for q in 0..corners {
                if q >> b & 1 == 1 {
                    d[q] = add(&d[q], &d[q ^ 1 << b]);
                }
            }
        }
        let konst = p.konst();
        let u: Vec<BitVec> = d.iter().map(|x| sub(&konst, x)).collect();
        let distinct = |vals: &mut Vec<BitVec>, v: &BitVec| {
            if !vals.contains(v) {
                vals.push(*v);
            }
        };
        // `c + a·g + b·h` takes at most four values at the corners: `c`, `c − a`, `c − b` and
        // `c − a − b`.
        let mut all: Vec<BitVec> = Vec::with_capacity(5);
        for v in &u {
            distinct(&mut all, v);
            if all.len() > 4 {
                return None;
            }
        }
        // `(g, a, (h, b), c)` for `c + a·g + b·h`.
        type Found = (u64, BitVec, Option<(u64, BitVec)>, BitVec);
        let mut found: Vec<Found> = Vec::new();
        if tables == 0 {
            // Too many functions to try each (or not asked to): the terms are read off the
            // values. With `u = c − a·[g] − b·[h]` every value is `c`, `c − a`, `c − b` or
            // `c − a − b`.
            let mut vals: Vec<BitVec> = Vec::new();
            for v in &u {
                distinct(&mut vals, v);
            }
            let at = |v: &BitVec| {
                (0..corners)
                    .filter(|&q| u[q] == *v)
                    .fold(0u64, |t, q| t | 1 << q)
            };
            match vals.len() {
                2 => {
                    for (c, v) in [(vals[0], vals[1]), (vals[1], vals[0])] {
                        found.push((at(&v), sub(&c, &v), None, c));
                    }
                }
                3 => {
                    for i in 0..3 {
                        let (c, x, y) = (vals[i], vals[(i + 1) % 3], vals[(i + 2) % 3]);
                        // No corner has both: g and h apart.
                        found.push((at(&x), sub(&c, &x), Some((at(&y), sub(&c, &y))), c));
                        // No corner has neither (`y` has both): c = x + y − v₁₁ with v₁₁ = y…
                        for (v10, v11) in [(x, y), (y, x)] {
                            let v01 = vals[i];
                            let c2 = sub(&add(&v10, &v01), &v11);
                            let g = at(&v10) | at(&v11);
                            let h = at(&v01) | at(&v11);
                            found.push((g, sub(&c2, &v10), Some((h, sub(&c2, &v01))), c2));
                        }
                        // One of g, h inside the other (`c`, then `x` for h alone, `y` both).
                        for (v01, v11) in [(x, y), (y, x)] {
                            let g = at(&v11);
                            let h = at(&v01) | at(&v11);
                            found.push((g, sub(&v01, &v11), Some((h, sub(&c, &v01))), c));
                        }
                    }
                }
                4 => {
                    for i in 0..4 {
                        for j in 0..4 {
                            if i == j {
                                continue;
                            }
                            let (c, v11) = (vals[i], vals[j]);
                            let rest: Vec<BitVec> = (0..4)
                                .filter(|&k| k != i && k != j)
                                .map(|k| vals[k])
                                .collect();
                            let (v10, v01) = (rest[0], rest[1]);
                            if add(&v10, &v01) != add(&c, &v11) {
                                continue;
                            }
                            let g = at(&v10) | at(&v11);
                            let h = at(&v01) | at(&v11);
                            found.push((g, sub(&c, &v10), Some((h, sub(&c, &v01))), c));
                        }
                    }
                }
                _ => {}
            }
        }
        // Each corner's value by its index among the (at most four) distinct values: which
        // values a table's corners take is a few bit operations.
        let idx: Vec<u8> = u
            .iter()
            .map(|v| all.iter().position(|x| x == v).unwrap_or(0) as u8)
            .collect();
        for g in 1..tables.max(1) - 1 {
            // The values inside and outside `g`, each in the order the corners first take them.
            let (mut inside_i, mut out_i) = ([0u8; 4], [0u8; 4]);
            let (mut ni, mut no) = (0usize, 0usize);
            let (mut seen_in, mut seen_out) = (0u8, 0u8);
            for (q, &i) in idx.iter().enumerate() {
                let (seen, list, n) = if g >> q & 1 == 1 {
                    (&mut seen_in, &mut inside_i, &mut ni)
                } else {
                    (&mut seen_out, &mut out_i, &mut no)
                };
                if *seen >> i & 1 == 0 {
                    *seen |= 1 << i;
                    list[*n] = i;
                    *n += 1;
                }
            }
            if no > 2 || ni > 2 {
                continue;
            }
            let out: Vec<BitVec> = out_i[..no].iter().map(|&i| all[usize::from(i)]).collect();
            let inside: Vec<BitVec> = inside_i[..ni]
                .iter()
                .map(|&i| all[usize::from(i)])
                .collect();
            // `a` moves a value inside onto one outside.
            let mut coefs: Vec<BitVec> = Vec::new();
            for x in &out {
                for y in &inside {
                    let a = sub(x, y);
                    if !a.is_zero() {
                        distinct(&mut coefs, &a);
                    }
                }
            }
            for a in coefs {
                let r: Vec<BitVec> = (0..corners)
                    .map(|q| {
                        if g >> q & 1 == 1 {
                            add(&u[q], &a)
                        } else {
                            u[q]
                        }
                    })
                    .collect();
                let mut vals = Vec::new();
                for v in &r {
                    distinct(&mut vals, v);
                }
                // `u = c − a·[g] − b·[h]`, so the form is `c + a·g + b·h`.
                match vals.as_slice() {
                    [c] => found.push((g, a, None, *c)),
                    [x, y] => {
                        for (c, other) in [(x, y), (y, x)] {
                            let h = (0..corners)
                                .filter(|&q| r[q] == *other)
                                .fold(0u64, |t, q| t | 1 << q);
                            found.push((g, a, Some((h, sub(c, other))), *c));
                        }
                    }
                    _ => {}
                }
            }
        }
        if found.is_empty() || !self.spend(found.len() as u64 * 8) {
            return None;
        }
        // Up to three atoms the functions' smallest forms have known sizes (the minimum-form
        // table): the decompositions are ranked by estimate (the functions' operators plus a
        // node or two per coefficient, join and constant), and only the cheapest are built.
        if s <= 3 && found.len() > 1 {
            let ops = |t: u64| {
                table8(&[t], s).map_or(u32::MAX / 4, |tt| {
                    u32::from(min_forms().forms[usize::from(tt)].1)
                })
            };
            let scale = |k: &BitVec| {
                let m = if k.msb() {
                    BitVec::un_unchecked(UnOp::Neg, k)
                } else {
                    *k
                };
                if m == BitVec::one(w) {
                    0
                } else if m == BitVec::wrapping_from_u64(w, 2) {
                    1
                } else {
                    2
                }
            };
            let estimate = |(g, a, h, c): &Found| {
                let mut e = ops(*g) + scale(a);
                if let Some((h, b)) = h {
                    e += ops(*h) + scale(b) + 1;
                }
                e + if c.is_zero() { 0 } else { 2 }
            };
            let mut ranked: Vec<(u32, usize)> = found
                .iter()
                .enumerate()
                .map(|(i, f)| (estimate(f), i))
                .collect();
            ranked.sort_unstable();
            ranked.truncate(TWO_TERMS_BUILT);
            found = ranked.iter().map(|&(_, i)| found[i]).collect();
        }
        let mut nodes: HashMap<u64, Option<u32>> = HashMap::new();
        let mut sums = Vec::with_capacity(found.len());
        // The best estimated, also with the other minimum forms of each function: a pair of
        // forms that share a subterm (the majority as `(y & z) | (x & (y | z))` beside
        // `~(x | (y | z))`), and a lone function's other forms. Not for what a peel leaves.
        if s <= 3 && self.peeling == 0 {
            let atoms: Option<Vec<u32>> = support.iter().map(|&a| self.atom(a)).collect();
            let forms = min_forms();
            let templates = |t: u64| -> Vec<&'static [T]> {
                table8(&[t], s).map_or(Vec::new(), |tt| {
                    let tt = usize::from(tt);
                    core::iter::once(forms.forms[tt].0.as_slice())
                        .chain(forms.alts[tt].iter().map(Vec::as_slice))
                        .collect()
                })
            };
            for (g, a, h, c) in found.iter().take(TWO_TERMS_PAIRED) {
                let Some(atoms) = &atoms else {
                    break;
                };
                let konst = (!c.is_zero()).then_some(*c);
                let gt = templates(*g);
                match h {
                    None => {
                        for tmpl in gt.iter().skip(1).take(TWO_TERMS_FORMS - 1) {
                            if let Some(gn) = self.template(tmpl, atoms) {
                                sums.push(Sum {
                                    terms: vec![(gn, *a)],
                                    konst,
                                });
                            }
                        }
                    }
                    Some((h, b)) => {
                        let ht = templates(*h);
                        let hsubs: Vec<Vec<u8>> = ht.iter().map(|t| subtables(t)).collect();
                        let mut shared = 0;
                        for (i, gf) in gt.iter().enumerate() {
                            let gsubs = subtables(gf);
                            for (j, hf) in ht.iter().enumerate() {
                                // The first few forms of each in every pairing, then pairs that
                                // share a subterm.
                                let first = i < TWO_TERMS_FORMS && j < TWO_TERMS_FORMS;
                                if (i, j) == (0, 0) {
                                    continue;
                                }
                                if !first {
                                    if shared == TWO_TERMS_SHARED
                                        || !hsubs[j].iter().any(|t| gsubs.contains(t))
                                    {
                                        continue;
                                    }
                                    shared += 1;
                                }
                                if let (Some(gn), Some(hn)) =
                                    (self.template(gf, atoms), self.template(hf, atoms))
                                {
                                    sums.push(Sum {
                                        terms: vec![(gn, *a), (hn, *b)],
                                        konst,
                                    });
                                }
                            }
                        }
                        // One function read through the other: `y ^ w` beside `~w` as
                        // `~(y ^ n)` with `n` the node of `~w`.
                        for (u, ku, v, kv) in [(*g, *a, *h, *b), (*h, *b, *g, *a)] {
                            let Some(un) = self.best_uniform(&[u], &support) else {
                                continue;
                            };
                            if let Some(vn) = self.through(v, u, un, &support, atoms) {
                                sums.push(Sum {
                                    terms: vec![(un, ku), (vn, kv)],
                                    konst,
                                });
                            }
                        }
                    }
                }
            }
        }
        let mut plain = Vec::with_capacity(found.len());
        for (g, a, h, c) in found {
            let mut terms = Vec::with_capacity(2);
            for (t, k) in core::iter::once((g, a)).chain(h) {
                let node = match nodes.get(&t) {
                    Some(&x) => x,
                    None => {
                        let x = self.best_uniform(&[t], &support);
                        nodes.insert(t, x);
                        x
                    }
                };
                terms.push((node?, k));
            }
            plain.push(Sum {
                terms,
                konst: (!c.is_zero()).then_some(c),
            });
        }
        // A constant traded for a complement can make a decomposition the cheapest (`7·g' +
        // 6·h + 7` as `6·h − 7·~g'`, whose `~g'` shares with `h`): each is weighed so; and a
        // coefficient the terms share taken out, for the cheapest few (`−5·a − 5·b` is
        // `(a + b)·−5`).
        sums.extend(plain);
        let traded: Vec<Sum> = sums
            .iter()
            .filter(|s| s.konst.is_some())
            .cloned()
            .collect::<Vec<Sum>>()
            .iter()
            .flat_map(|s| self.complements(s))
            .collect();
        sums.extend(traded);
        let mut sums = self.ranked(sums);
        let factored: Vec<Sum> = sums
            .iter()
            .take(TWO_TERMS_FACTORED)
            .cloned()
            .collect::<Vec<Sum>>()
            .iter()
            .flat_map(|s| self.factored(s))
            .collect();
        sums.truncate(1);
        sums.extend(factored);
        self.cheapest(sums)
    }

    /// Table `v` (over `support`, at most three atoms) as a function of table `u` (rendered
    /// `un`) and at most two of the atoms, the fewest that determine it: its minimum form over
    /// those atoms' nodes and `un`. `None` when no such set does (or `v` needs none of `u`).
    fn through(&mut self, v: u64, u: u64, un: u32, support: &[u32], atoms: &[u32]) -> Option<u32> {
        let s = support.len();
        let corners = 1usize << s;
        if !self.spend(corners as u64 * 8) {
            return None;
        }
        let mut subsets: Vec<u32> = (0..1u32 << s).filter(|m| m.count_ones() <= 2).collect();
        subsets.sort_by_key(|m| m.count_ones());
        for m in subsets {
            let idx: Vec<usize> = (0..s).filter(|&j| m >> j & 1 == 1).collect();
            let k = idx.len();
            // The table over the chosen atoms and `u` (the last input); `None` where unseen.
            let mut t: Vec<Option<bool>> = vec![None; 1 << (k + 1)];
            let mut alone = true;
            let mut fits = true;
            let mut by_atoms: Vec<Option<bool>> = vec![None; 1 << k];
            for q in 0..corners {
                let a = idx
                    .iter()
                    .enumerate()
                    .fold(0usize, |e, (i, &j)| e | (q >> j & 1) << i);
                let e = a | ((u >> q & 1) as usize) << k;
                let bit = v >> q & 1 == 1;
                match t[e] {
                    Some(b) if b != bit => {
                        fits = false;
                        break;
                    }
                    _ => t[e] = Some(bit),
                }
                match by_atoms[a] {
                    Some(b) if b != bit => alone = false,
                    _ => by_atoms[a] = Some(bit),
                }
            }
            if !fits || alone {
                continue;
            }
            // Unseen entries (the atoms and `u` never meet so) are free: 0.
            let table = t
                .iter()
                .enumerate()
                .fold(0u64, |acc, (e, b)| acc | u64::from(b.unwrap_or(false)) << e);
            let mut ins: Vec<u32> = idx.iter().map(|&j| atoms[j]).collect();
            ins.push(un);
            return self.best_of_table(table, &ins);
        }
        None
    }

    /// A three-atom form (unmasked, degree at most 1) as `k·g + rest`: `g` a function of two
    /// of its atoms and `k` small, where `rest` takes at most three values at the corners (then
    /// decomposed by [`Render::two_terms`]), for the two such splits leaving the fewest values:
    /// a third term beside two when all three are cheaper (`−6·~((x & y) | (x ^ y ^ z)) +
    /// (x & z) − (x & y)`, the rest `−6·~((x & y) | …) − (x & y)` sharing `x & y`).
    fn split_off(&mut self, p: &Poly) -> Vec<Sum> {
        let w = self.w;
        let n = self.classes.len();
        let atoms = p.atoms();
        if atoms.count_ones() != 3 || !self.spend(3 * 10 * 4 * 8 + p.len() as u64) {
            return Vec::new();
        }
        let support: Vec<u32> = (0..64).filter(|&a| atoms >> a & 1 == 1).collect();
        let class = if n == 1 { 0 } else { FULL };
        // The values at the corners (each atom 0 or all ones), as in `two_terms`.
        let mut d = vec![BitVec::zero(w); 8];
        for (m, c) in p.terms() {
            match m.as_slice() {
                [] => {}
                [(sym, 1)] if sym.class == FULL || n == 1 => {
                    let q = support
                        .iter()
                        .enumerate()
                        .filter(|&(_, &a)| sym.set >> a & 1 == 1)
                        .fold(0usize, |q, (j, _)| q | 1 << j);
                    d[q] = BitVec::bin_unchecked(BinOp::Add, &d[q], c);
                }
                _ => return Vec::new(),
            }
        }
        for b in 0..3 {
            for q in 0..8 {
                if q >> b & 1 == 1 {
                    d[q] = BitVec::bin_unchecked(BinOp::Add, &d[q], &d[q ^ 1 << b]);
                }
            }
        }
        let konst = p.konst();
        let u: Vec<BitVec> = d
            .iter()
            .map(|x| BitVec::bin_unchecked(BinOp::Sub, &konst, x))
            .collect();
        let mut splits: Vec<Split> = Vec::new();
        let forms = min_forms();
        for (i, j) in [(0usize, 1usize), (0, 2), (1, 2)] {
            for t in 1u8..15 {
                // Tables that read both atoms of the pair.
                if matches!(t, 0x3 | 0x5 | 0xA | 0xC) {
                    continue;
                }
                let g = |q: usize| t >> ((q >> i & 1) | (q >> j & 1) << 1) & 1 == 1;
                for k in [1i128, -1, 2, -2] {
                    let k = BitVec::wrapping_from_i128(w, k);
                    let mut vals: Vec<BitVec> = Vec::with_capacity(4);
                    for (q, v) in u.iter().enumerate() {
                        // `k·g` is `−k` at a corner where `g` holds: the rest is `u + k·g`.
                        let r = if g(q) {
                            BitVec::bin_unchecked(BinOp::Add, v, &k)
                        } else {
                            *v
                        };
                        if !vals.contains(&r) {
                            vals.push(r);
                        }
                        if vals.len() > 3 {
                            break;
                        }
                    }
                    if vals.len() <= 3 {
                        // The 8-entry table of `g` over atoms (i, j) as inputs 0 and 1.
                        let tt = (0..8usize)
                            .fold(0u8, |acc, e| acc | u8::from(t >> (e & 3) & 1 == 1) << e);
                        splits.push((vals.len(), forms.forms[usize::from(tt)].1, (i, j), t, k));
                    }
                }
            }
        }
        splits.sort_by_key(|&(values, ops, ..)| (values, ops));
        let mut out = Vec::new();
        for (_, _, (i, j), t, k) in splits.into_iter().take(SPLITS) {
            // `g`'s terms (its integer conjunction form) times `k`, taken from the form.
            let m = mobius(&[u64::from(t)], 2);
            let mut rest = p.clone();
            let neg = |c: &BitVec| BitVec::un_unchecked(UnOp::Neg, c);
            let kg = |v: i64| {
                BitVec::bin_unchecked(
                    BinOp::Mul,
                    &k,
                    &BitVec::wrapping_from_i128(w, i128::from(v)),
                )
            };
            // g = −m₀ + Σ m_T·AND_T.
            rest.add_term(Vec::new(), &kg(m[0]));
            for (q, &v) in m.iter().enumerate().skip(1) {
                if v == 0 {
                    continue;
                }
                let set = [(0usize, i), (1, j)]
                    .iter()
                    .filter(|&&(b, _)| q >> b & 1 == 1)
                    .fold(0u64, |s, &(_, a)| s | 1 << support[a]);
                rest.add_term(vec![(Sym { set, class }, 1)], &neg(&kg(v)));
            }
            let Some(r) = self.two_terms_by(&rest, false) else {
                continue;
            };
            let Some(gn) = self.best_uniform(&[u64::from(t)], &[support[i], support[j]]) else {
                continue;
            };
            let mut terms = r.terms.clone();
            terms.push((gn, k));
            out.push(Sum {
                terms,
                konst: r.konst,
            });
        }
        out
    }

    /// A degree-≤1 form whose atoms fall into independent groups (no term mentions atoms of
    /// two), rendered group by group, each by the decompositions above: `2·(~x & (y ^ z)) + a
    /// − 1` from its part over `x, y, z` and `a`. The constant goes with the group whose
    /// rendering it makes cheapest, or stands alone.
    fn components(&mut self, p: &Poly) -> Option<Sum> {
        let w = self.w;
        let mut groups: Vec<u64> = Vec::new();
        for m in p.terms().keys() {
            let mut set = m.iter().fold(0u64, |s, (sym, _)| s | sym.set);
            if set == 0 {
                continue;
            }
            groups.retain(|&g| {
                if g & set != 0 {
                    set |= g;
                    false
                } else {
                    true
                }
            });
            groups.push(set);
        }
        if groups.len() < 2 || !self.spend(p.len() as u64 * groups.len() as u64) {
            return None;
        }
        groups.sort_unstable();
        let parts: Vec<Poly> = groups
            .iter()
            .map(|&g| {
                let mut q = Poly::zero(w);
                for (m, c) in p.terms() {
                    let set = m.iter().fold(0u64, |s, (sym, _)| s | sym.set);
                    if set != 0 && set & !g == 0 {
                        q.add_term(m.clone(), c);
                    }
                }
                q
            })
            .collect();
        let konst = p.konst();
        let mut base: Vec<Sum> = Vec::with_capacity(parts.len());
        for q in &parts {
            let sums = self.linear_sums(q);
            base.push(self.cheapest(sums)?);
        }
        let join = |parts: &[Sum], konst: BitVec| {
            let mut t = Sum {
                terms: Vec::new(),
                konst: None,
            };
            let mut k = konst;
            for s in parts {
                t.terms.extend(s.terms.iter().copied());
                if let Some(c) = s.konst {
                    k = BitVec::bin_unchecked(BinOp::Add, &k, &c);
                }
            }
            t.konst = (!k.is_zero()).then_some(k);
            t
        };
        let mut options = vec![join(&base, konst)];
        if !konst.is_zero() {
            for (i, q) in parts.iter().enumerate() {
                let mut qk = q.clone();
                qk.add_term(Vec::new(), &konst);
                let sums = self.linear_sums(&qk);
                let Some(si) = self.cheapest(sums) else {
                    continue;
                };
                let mut with = base.clone();
                with[i] = si;
                options.push(join(&with, BitVec::zero(w)));
            }
        }
        self.cheapest(options)
    }

    /// A degree-≤1 form (its symbols unmasked) with an atom whose terms, those mentioning it,
    /// are `s` times the terms of a bitwise function of the two or three atoms they mention
    /// (fewer than the form's): that function peeled off and the rest rendered on its own.
    /// The function's terms without the atom are free, chosen so its table is 0 or 1 (where
    /// the atom's terms leave a choice, each way): `(p | (a ^ d)) + (a ^ D)` comes apart at `D`,
    /// whose terms `D − 2·(a & D)` are those of `a ^ D`.
    fn peel(&mut self, p: &Poly) -> Option<Sum> {
        // One peel deep: what is left is rendered by the cheaper decompositions only.
        if self.peeling >= 1 {
            return None;
        }
        self.peeling += 1;
        let r = self.peel_at(p);
        self.peeling -= 1;
        r
    }

    fn peel_at(&mut self, p: &Poly) -> Option<Sum> {
        let w = self.w;
        let n = self.classes.len();
        let all = p.atoms();
        if all.count_ones() < 3 || all.count_ones() > 8 {
            return None;
        }
        // Coefficients by atom set; every symbol unmasked.
        let mut coef: BTreeMap<u64, BitVec> = BTreeMap::new();
        for (m, c) in p.terms() {
            match m.as_slice() {
                [] => {}
                [(sym, 1)] if sym.class == FULL || n == 1 => {
                    coef.insert(sym.set, *c);
                }
                _ => return None,
            }
        }
        if !self.spend(coef.len() as u64 * u64::from(all.count_ones()) * 8) {
            return None;
        }
        let class = if n == 1 { 0 } else { FULL };
        let mut out: Vec<Sum> = Vec::new();
        for x in (0..64u32).rev().filter(|&a| all >> a & 1 == 1) {
            let bit = 1u64 << x;
            let support = coef
                .keys()
                .filter(|&&set| set & bit != 0)
                .fold(0u64, |s, &set| s | set);
            let k = support.count_ones() as usize;
            if !(2..=3).contains(&k) || support == all {
                continue;
            }
            // The scale: from the atom's lone term, or where it has none (`x & d`), from its
            // term with the fewest atoms, whose coefficient in the function is ±1, ±2 or ±4.
            let neg = |c: &BitVec| BitVec::un_unchecked(UnOp::Neg, c);
            let scales: Vec<BitVec> = match coef.get(&bit) {
                Some(&c) => vec![c, neg(&c)],
                None => {
                    let Some(&c) = coef
                        .iter()
                        .filter(|(set, _)| **set & bit != 0)
                        .min_by_key(|(set, _)| (set.count_ones(), **set))
                        .map(|(_, c)| c)
                    else {
                        continue;
                    };
                    let mut v = vec![c, neg(&c)];
                    for sh in 1..=2u32 {
                        if crate::facts::known::trailing_zeros(&c) >= sh {
                            let half = BitVec::bin_unchecked(
                                BinOp::AShr,
                                &c,
                                &BitVec::wrapping_from_u64(w, u64::from(sh)),
                            );
                            v.push(half);
                            v.push(neg(&half));
                        }
                    }
                    v
                }
            };
            let atoms: Vec<u32> = (0..64u32).filter(|&a| support >> a & 1 == 1).collect();
            let xi = atoms.iter().position(|&a| a == x)?;
            let set_of = |q: usize| {
                (0..k)
                    .filter(|&t| q >> t & 1 == 1)
                    .fold(0u64, |s, t| s | 1 << atoms[t])
            };
            for s in scales {
                // The function's coefficients on the sets with the atom: c_T / s, small.
                let mut a = vec![0i64; 1 << k];
                let mut fits = true;
                for (q, slot) in a.iter_mut().enumerate() {
                    if q >> xi & 1 == 0 {
                        continue;
                    }
                    let c = coef.get(&set_of(q)).copied().unwrap_or(BitVec::zero(w));
                    match (-4i64..=4).find(|&v| {
                        BitVec::bin_unchecked(
                            BinOp::Mul,
                            &s,
                            &BitVec::wrapping_from_i128(w, i128::from(v)),
                        ) == c
                    }) {
                        Some(v) => *slot = v,
                        None => {
                            fits = false;
                            break;
                        }
                    }
                }
                if !fits {
                    continue;
                }
                // Per pattern q of the other atoms: the rise when the atom is set.
                let others: Vec<usize> = (0..1usize << k).filter(|q| q >> xi & 1 == 0).collect();
                let rise = |q: usize| -> i64 {
                    (0..1usize << k)
                        .filter(|&t| t >> xi & 1 == 1 && t & !(q | 1 << xi) == 0)
                        .map(|t| a[t])
                        .sum()
                };
                let mut forced: Vec<Option<bool>> = Vec::with_capacity(others.len());
                for &q in &others {
                    forced.push(match rise(q) {
                        0 => None,
                        1 => Some(false),
                        -1 => Some(true),
                        _ => {
                            fits = false;
                            break;
                        }
                    });
                }
                if !fits {
                    continue;
                }
                let free: Vec<usize> = (0..others.len()).filter(|&i| forced[i].is_none()).collect();
                if free.len() > 2 {
                    continue;
                }
                for choice in 0..1usize << free.len() {
                    // The table: f(q) off the atom, f(q) + rise(q) on it.
                    let mut table = 0u64;
                    for (i, &q) in others.iter().enumerate() {
                        let off = match forced[i] {
                            Some(v) => v,
                            None => {
                                let j = free.iter().position(|&f| f == i).unwrap_or(0);
                                choice >> j & 1 == 1
                            }
                        };
                        let on = i64::from(off) + rise(q) == 1;
                        if off {
                            table |= 1 << q;
                        }
                        if on {
                            table |= 1 << (q | 1 << xi);
                        }
                    }
                    // Its expansion, s times, taken from the form.
                    let mut m: Vec<i64> =
                        (0..1usize << k).map(|q| (table >> q & 1) as i64).collect();
                    for b in 0..k {
                        for q in 0..1usize << k {
                            if q >> b & 1 == 1 {
                                m[q] -= m[q ^ 1 << b];
                            }
                        }
                    }
                    let mut rest = p.clone();
                    let sv = |v: i64| {
                        BitVec::bin_unchecked(
                            BinOp::Mul,
                            &s,
                            &BitVec::wrapping_from_i128(w, i128::from(v)),
                        )
                    };
                    // f = −m_∅ + Σ m_T·AND_T.
                    rest.add_term(Vec::new(), &sv(m[0]));
                    for (q, &v) in m.iter().enumerate().skip(1) {
                        if v != 0 {
                            rest.add_term(
                                vec![(
                                    Sym {
                                        set: set_of(q),
                                        class,
                                    },
                                    1,
                                )],
                                &sv(-v),
                            );
                        }
                    }
                    if rest.atoms() >> x & 1 == 1 {
                        continue;
                    }
                    let sums = self.linear_sums(&rest);
                    let Some(r) = self.cheapest(sums) else {
                        continue;
                    };
                    let Some(g) = self.best_uniform(&[table], &atoms) else {
                        continue;
                    };
                    let mut terms = r.terms.clone();
                    terms.push((g, s));
                    out.push(Sum {
                        terms,
                        konst: r.konst,
                    });
                }
            }
            if !out.is_empty() {
                break;
            }
        }
        self.cheapest(out)
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
            let (t, c) = s.terms[i];
            for nt in self.complement(t) {
                let mut terms = s.terms.clone();
                terms[i] = (nt, BitVec::un_unchecked(UnOp::Neg, &c));
                out.push(Sum { terms, konst: None });
            }
        }
        out.extend(self.trades(s));
        out.extend(self.factored(s));
        out
    }

    /// `~t` for a node of the builder: the complement node, and where it is cheaper to push
    /// it through the operator (`~(~a | b)` is `a & ~b`, `~(a ^ ~b)` is `a ^ b`), that too.
    fn complement(&mut self, t: u32) -> Vec<u32> {
        let n = self.b.nodes[t as usize];
        let is_not = |b: &Builder, x: u32| b.nodes[x as usize].op == MOp::Not;
        let arg = |b: &Builder, x: u32| b.nodes[x as usize].args[0];
        let mut out = Vec::with_capacity(2);
        match n.op {
            MOp::Not => return vec![n.args[0]],
            MOp::Xor => {
                let (a, c) = (n.args[0], n.args[1]);
                if is_not(&self.b, a) {
                    let a0 = arg(&self.b, a);
                    return vec![self.b.bin(MOp::Xor, a0, c)];
                }
                if is_not(&self.b, c) {
                    let c0 = arg(&self.b, c);
                    return vec![self.b.bin(MOp::Xor, a, c0)];
                }
            }
            MOp::And | MOp::Or => {
                let (a, c) = (n.args[0], n.args[1]);
                if is_not(&self.b, a) || is_not(&self.b, c) {
                    let flip = if n.op == MOp::And { MOp::Or } else { MOp::And };
                    let na = if is_not(&self.b, a) {
                        arg(&self.b, a)
                    } else {
                        self.b.un(MOp::Not, a)
                    };
                    let nc = if is_not(&self.b, c) {
                        arg(&self.b, c)
                    } else {
                        self.b.un(MOp::Not, c)
                    };
                    out.push(self.b.bin(flip, na, nc));
                }
            }
            _ => {}
        }
        out.push(self.b.un(MOp::Not, t));
        out
    }

    /// Variants of `s` that trade its constant for complements: `−1 + R` as `~(−R)` (`−1 − 2·x`
    /// is `~(x + x)`), and `k + 2k·t` as `k·t − k·~t` (`2·t + 1` is `t − ~t`, `−2·t − 1` is
    /// `~t − t`).
    fn trades(&mut self, s: &Sum) -> Vec<Sum> {
        let w = self.w;
        let mut out = Vec::new();
        let Some(k) = s.konst.filter(|k| !k.is_zero()) else {
            return out;
        };
        let neg = |c: &BitVec| BitVec::un_unchecked(UnOp::Neg, c);
        if k == BitVec::ones(w) && !s.terms.is_empty() {
            let flipped = Sum {
                terms: s.terms.iter().map(|&(t, c)| (t, neg(&c))).collect(),
                konst: None,
            };
            // Its terms' shared coefficients taken out too (`~(3·(x & y) + 3·x)` as
            // `~((x & y) + x)·3`).
            let mut inner_sums = self.factored(&flipped);
            inner_sums.push(flipped);
            let Some(best) = self.cheapest(inner_sums) else {
                return out;
            };
            let inner = self.sum(&best);
            let n = self.b.un(MOp::Not, inner);
            out.push(Sum {
                terms: vec![(n, BitVec::one(w))],
                konst: None,
            });
        }
        let twice = BitVec::bin_unchecked(BinOp::Add, &k, &k);
        if let Some(i) = s.terms.iter().position(|(_, c)| *c == twice) {
            let t = s.terms[i].0;
            for nt in self.complement(t) {
                let mut terms = s.terms.clone();
                terms[i] = (t, k);
                terms.push((nt, neg(&k)));
                out.push(Sum { terms, konst: None });
            }
        }
        out
    }

    /// Variants of `s` with a coefficient several terms share (up to sign) taken out:
    /// `6·a + 6·b` as `(a + b)·6`, one product where there were two.
    fn factored(&mut self, s: &Sum) -> Vec<Sum> {
        let w = self.w;
        let mut out = Vec::new();
        let neg = |c: &BitVec| BitVec::un_unchecked(UnOp::Neg, c);
        let rep = |c: &BitVec| if c.msb() { neg(c) } else { *c };
        let mut seen: Vec<BitVec> = Vec::new();
        for &(_, c) in &s.terms {
            let r = rep(&c);
            if r == BitVec::one(w) || seen.contains(&r) {
                continue;
            }
            seen.push(r);
            // Taken out with the sign most of the group has (`−5·a − 5·b` is `(a + b)·−5`).
            let negative = s.terms.iter().filter(|(_, d)| *d == neg(&r)).count();
            let positive = s.terms.iter().filter(|(_, d)| *d == r).count();
            let r = if negative > positive { neg(&r) } else { r };
            let group: Vec<(u32, BitVec)> = s
                .terms
                .iter()
                .filter(|(_, d)| rep(d) == rep(&r))
                .map(|&(t, d)| {
                    (
                        t,
                        if d == r {
                            BitVec::one(w)
                        } else {
                            BitVec::ones(w)
                        },
                    )
                })
                .collect();
            if group.len() < 2 {
                continue;
            }
            let rest: Vec<(u32, BitVec)> = s
                .terms
                .iter()
                .filter(|(_, d)| rep(d) != rep(&r))
                .copied()
                .collect();
            let inner = self.sum(&Sum {
                terms: group.clone(),
                konst: None,
            });
            let mut terms = rest.clone();
            terms.push((inner, r));
            out.push(Sum {
                terms,
                konst: s.konst,
            });
            // A constant that is a small multiple of `r` goes inside too, where it can become
            // a complement (`6·x − 6·y − 6` is `(x + ~y)·6`: an `x − y − 1` inside).
            let Some(k) = s.konst else {
                continue;
            };
            let Some(m) = [1i128, -1, 2, -2]
                .iter()
                .map(|&m| BitVec::wrapping_from_i128(w, m))
                .find(|m| BitVec::bin_unchecked(BinOp::Mul, &r, m) == k)
            else {
                continue;
            };
            let with = Sum {
                terms: group,
                konst: Some(m),
            };
            let mut variants = vec![with.clone()];
            variants.extend(self.complements(&with));
            let Some(best) = self.cheapest(variants) else {
                continue;
            };
            let inner = self.sum(&best);
            let mut terms = rest;
            terms.push((inner, r));
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
    /// `sums` from cheapest to dearest (ties in their order).
    fn ranked(&mut self, sums: Vec<Sum>) -> Vec<Sum> {
        let mut costed: Vec<(Cost, usize, Sum)> = sums
            .into_iter()
            .enumerate()
            .map(|(i, s)| {
                let root = self.sum(&s);
                (self.b.cost(root), i, s)
            })
            .collect();
        costed.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
        costed.into_iter().map(|(_, _, s)| s).collect()
    }

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
        if let Some(out) = self.memo.get(&key) {
            let out = out.clone();
            self.spend(p.len() as u64 + out.len() as u64);
            return out;
        }
        let out = self.render_poly(p, factors, depth);
        if !self.exhausted() {
            self.memo.insert(key, out.clone());
        }
        out
    }

    fn render_poly(&mut self, p: &Poly, factors: &[Poly], depth: u32) -> Vec<u32> {
        const MAX_DEPTH: u32 = 2;
        if p.degree() <= 1 {
            self.top = depth == 0;
            let out = self.linear(p);
            self.top = false;
            return out;
        }
        if self.hopeless(p.atoms()) {
            return Vec::new();
        }
        let w = self.w;
        let one = BitVec::one(w);
        let lin = p.part(|d| d <= 1);
        let nl = p.part(|d| d >= 2);
        // The linear part's cheapest decompositions: which is best depends on what it joins
        // (`(x | y) + 1` or `−~(x | y)` alone, but `x·y − ~(x | y)` beside a product).
        let lin_sums = if lin.is_zero() {
            vec![Sum::default()]
        } else {
            self.top = depth == 0;
            let sums = self.linear_sums(&lin);
            self.top = false;
            let mut sums = self.ranked(sums);
            sums.truncate(LINEAR_JOINED);
            if sums.is_empty() {
                return Vec::new();
            }
            sums
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
        // A single monomial is best as itself (powers shared): factoring it only splits it.
        if depth < MAX_DEPTH && nl.len() > 1 {
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
                let Some(q) = self.divide(&nl, f) else {
                    continue;
                };
                if let Some(x) = self.product(f, &q, factors, depth) {
                    parts.push(Sum {
                        terms: vec![(x, one)],
                        konst: None,
                    });
                }
                // At the top, a quotient mostly of negative terms, negated and subtracted:
                // `d − f·q` is a negation smaller than `−f·q + d`.
                let negative = q.terms().values().filter(|c| c.msb()).count();
                if depth == 0 && 2 * negative > q.len() {
                    let minus = BitVec::ones(w);
                    if let Some(x) = self.product(f, &q.scale(&minus), factors, depth) {
                        parts.push(Sum {
                            terms: vec![(x, minus)],
                            konst: None,
                        });
                    }
                }
            }
        }
        // Part of it factored: by a symbol most (not all) of its monomials share, the others
        // beside (`2·c·(a & c) − a·c − c² − a²` is `c·(2·(a & c) − a − c) − a²`, `c·−(a ^ c)`
        // less `a²`). At the top only, and for a few monomials: each factor is rendered again.
        if depth == 0 && (3..=PARTIAL_TERMS).contains(&nl.len()) {
            let mut counts: Vec<(usize, Sym)> = Vec::new();
            for m in nl.terms().keys() {
                for &(s, _) in m {
                    match counts.iter_mut().find(|(_, t)| *t == s) {
                        Some(e) => e.0 += 1,
                        None => counts.push((1, s)),
                    }
                }
            }
            counts.retain(|&(k, _)| k >= 2 && k < nl.len());
            counts.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
            for &(_, sym) in counts.iter().take(PARTIAL_SYMBOLS) {
                if self.exhausted() {
                    break;
                }
                let f = Poly::sym(w, sym);
                let Some((q, r)) = self.divide_rem(&nl, &f) else {
                    continue;
                };
                let Some(x) = self.product(&f, &q, factors, depth) else {
                    continue;
                };
                let mut part = Sum {
                    terms: vec![(x, one)],
                    konst: None,
                };
                for (m, c) in r.terms() {
                    match self.mono(m) {
                        Some(t) => part.terms.push((t, *c)),
                        None => return Vec::new(),
                    }
                }
                parts.push(part);
            }
        }
        let mut out: Vec<u32> = Vec::with_capacity(parts.len());
        for n in &parts {
            let joined: Vec<Sum> = lin_sums
                .iter()
                .map(|l| {
                    let mut s = l.clone();
                    s.terms.extend(n.terms.iter().copied());
                    s
                })
                .collect();
            if let Some(s) = self.cheapest(joined) {
                out.push(self.sum(&s));
            }
        }
        if depth == 0
            && let Some(x) = self.shifted_power(p)
        {
            out.push(x);
        }
        if depth < MAX_DEPTH {
            // The whole form as a product: by a factor of the input's products, or by a
            // symbol all its monomials share (`x·y − 3·y` is `(x − 3)·y`).
            let mut fs: Vec<Poly> = factors.to_vec();
            fs.extend(common_symbols(p).into_iter().map(|s| Poly::sym(w, s)));
            for f in &fs {
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

    /// A polynomial in one atom `x`, of degree 4 or more, that is `a·(x + s)^k + b` as a
    /// function: its value built by repeated squaring (`(x − 1)^100`, whose expansion the
    /// normal form reduces at narrow widths, is `(x − 1)^36` at 8 bits). The shift `s` is
    /// tried among small constants; `b` is the value at `x = −s` and `a` the value at
    /// `x = 1 − s` less `b`; the exponent is every one at widths to 12 (where `y^k` repeats
    /// with period `2^(W−2)` from `k = W` on, [`power_class`]) and the degree beyond (where a
    /// polynomial of degree at most `max_degree` is not reduced). A candidate that matches at
    /// the probe points is built with its cheapest equivalent exponent; like every rendering,
    /// it is certified against the question before it is returned.
    fn shifted_power(&mut self, p: &Poly) -> Option<u32> {
        let w = self.w;
        let bits = u32::from(w.bits());
        let atoms = p.atoms();
        if !(3..=64).contains(&bits) || p.degree() < 4 || atoms.count_ones() != 1 {
            return None;
        }
        // Every monomial a power of one symbol: the atom at every position.
        let sym = p.terms().keys().find_map(|m| m.first().map(|&(s, _)| s))?;
        let whole = sym.set == atoms
            && (sym.class == FULL || self.classes.mask(usize::from(sym.class)).is_ones());
        if !whole
            || !p
                .terms()
                .keys()
                .all(|m| m.is_empty() || (m.len() == 1 && m[0].0 == sym))
        {
            return None;
        }
        let atom = atoms.trailing_zeros() as usize;
        let mask = u64::MAX >> (64 - bits);
        let mut point = vec![0u64; atom + 1];
        let classes = self.classes;
        let mut eval = |x: u64| -> Option<u64> {
            point[atom] = x & mask;
            Some(p.eval_low(classes, &point)? & mask)
        };
        let ks: Vec<u32> = if bits <= 12 {
            (2..bits + (1 << (bits - 2))).collect()
        } else {
            vec![p.degree()]
        };
        if !self.spend(ks.len() as u64 * 33 * p.len() as u64) {
            return None;
        }
        // Probe points: small values, both signs, and a spread of others.
        let probes: Vec<u64> = (0..24u64)
            .map(|i| match i {
                0..=9 => i,
                10..=15 => (i - 9).wrapping_neg(),
                _ => i.wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left(i as u32),
            })
            .collect();
        let pow = |y: u64, k: u32| -> u64 {
            let (mut r, mut b, mut e) = (1u64, y, k);
            while e > 0 {
                if e & 1 == 1 {
                    r = r.wrapping_mul(b);
                }
                b = b.wrapping_mul(b);
                e >>= 1;
            }
            r & mask
        };
        let values: Vec<u64> = probes
            .iter()
            .map(|&x| eval(x))
            .collect::<Option<Vec<u64>>>()?;
        for s in (0..=16u64).flat_map(|v| [v, v.wrapping_neg()]).skip(1) {
            let s = s & mask;
            let b = eval(s.wrapping_neg())?;
            let a = eval(1u64.wrapping_sub(s))?.wrapping_sub(b) & mask;
            if a == 0 {
                continue;
            }
            let Some(&k) = ks.iter().find(|&&k| {
                probes.iter().zip(&values).all(|(&x, &v)| {
                    a.wrapping_mul(pow(x.wrapping_add(s), k)).wrapping_add(b) & mask == v
                })
            }) else {
                continue;
            };
            let k = power_class(k, bits);
            let x = self.sym(sym)?;
            let base = if s == 0 {
                x
            } else {
                self.sum(&Sum {
                    terms: vec![(x, BitVec::one(w))],
                    konst: Some(BitVec::wrapping_from_u64(w, s)),
                })
            };
            let y = self.power(base, k);
            let b = BitVec::wrapping_from_u64(w, b);
            return Some(self.sum(&Sum {
                terms: vec![(y, BitVec::wrapping_from_u64(w, a))],
                konst: (!b.is_zero()).then_some(b),
            }));
        }
        None
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

/// The cheapest exponent `k'` with `y^k' = y^k` for every `y` at `bits` (at least 3): `k`
/// itself below `bits`; from `bits` on, where every even `y` gives 0 and the odd ones form a
/// group of exponent `2^(bits−2)`, any `k' >= bits` with `k' ≡ k (mod 2^(bits−2))`, the one
/// with the fewest multiplications by repeated squaring.
fn power_class(k: u32, bits: u32) -> u32 {
    if k < bits || bits > 34 {
        return k;
    }
    let period = 1u64 << (bits - 2);
    let first = u64::from(bits) + (u64::from(k) - u64::from(bits)) % period;
    let cost = |e: u64| (63 - e.leading_zeros()) + e.count_ones();
    (0..4u64)
        .map(|j| first + j * period)
        .filter(|&e| e <= u64::from(u32::MAX))
        .min_by_key(|&e| (cost(e), e))
        .map_or(k, |e| e as u32)
}

/// Table `t` of `s` inputs with the inputs in `f` complemented: entry `p` is `t`'s entry
/// `p ^ f`.
fn flip_inputs(t: u64, s: usize, f: usize) -> u64 {
    (0..1usize << s)
        .filter(|&p| t >> (p ^ f) & 1 == 1)
        .fold(0, |acc, p| acc | 1 << p)
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
