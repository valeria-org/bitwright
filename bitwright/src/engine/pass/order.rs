//! The order part of the compares pass: boolean combinations of comparisons between a few terms
//! of one width, where a term is an atom or a `select` between terms on such a condition (a
//! minimum or maximum written out), decided over the orders the atoms can stand in.
//!
//! Whatever values the atoms take, they stand in one *total preorder* (a ranking with ties):
//! the unsigned one for `<u`, `<=u`, the signed one for `<s`, `<=s`, and either for `==`, `!=`.
//! A comparison of two terms is decided by their ranks, so the whole formula is a function of
//! the preorder (and of the 1-bit leaves that are not comparisons, enumerated too). The pass
//! enumerates every preorder of up to [`MAX_ATOMS`] atoms, drops the ones the atoms cannot
//! stand in, and reads the formula's value in each:
//!
//! - constants stand in their own order, and facts order atoms whose ranges do not overlap;
//! - an operation bounded by an operand stands at most (or at least) there: `x & y <=u x`,
//!   `x <=u x | y`, `x >>u s <=u x`, `urem(x, y) <=u x`, `udiv(x, d) <=u x` for a divisor the
//!   facts show nonzero;
//! - monotone operations keep the order of their operands: `x <=u y` gives
//!   `x >>u s <=u y >>u s` and `udiv(x, d) <=u udiv(y, d)`, and `x <=s y` gives
//!   `x >>s s <=s y >>s s`.
//!
//! Dropping only orders that cannot occur keeps the reading exact: each assignment of values
//! stands in one of the orders read. A formula true in every one is true, false in every one is
//! false, and one that agrees everywhere with a single comparison of two atoms (or a 1-bit
//! leaf) is that comparison; a `select` whose value is always one atom is that atom, and one
//! that is always the lesser (greater) of two is written as that minimum (maximum). This
//! decides transitivity (`x <u y & y <u z & z <=u x` is false), trichotomy, the lattice laws of
//! minimum and maximum however they are spelled (`select(x <u y, x, y) == select(y <u x, y, x)`
//! is true), and monotonicity (`x <=u y` implies `x >>u 2 <=u y >>u 2`). The result replaces
//! the node only when it is smaller.

use super::{Fin, Runner, Stop, facts};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::CmpOp;

/// The most term atoms (541 preorders at 5).
const MAX_ATOMS: usize = 5;

/// The most 1-bit leaves that are not comparisons.
const MAX_BOOLS: usize = 2;

/// The most formula nodes.
const MAX_ITEMS: usize = 48;

/// A formula node.
#[derive(Clone, Copy)]
enum Item {
    /// A term atom (its index).
    Atom(usize),
    /// A 1-bit leaf (its index).
    Bool(usize),
    Const(bool),
    Not(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    /// `a < b` (`strict`) or `a <= b` in the model's order, between term items.
    Less(bool, usize, usize),
    /// `a == b` (or `!=` when negated) between term items.
    Equal(bool, usize, usize),
    /// A 1-bit select between 1-bit items, or a term select between term items.
    Select(usize, usize, usize),
}

/// The formula below a node, compiled.
struct Model {
    items: Vec<Item>,
    index: IdMap<u32, usize>,
    atoms: Vec<u32>,
    bools: Vec<u32>,
    /// The width of the terms.
    width: u16,
    /// The order's kind, once a comparison fixed it: `Some(true)` signed.
    signed: Option<bool>,
    /// Whether an item is a term (else 1-bit).
    term: Vec<bool>,
    comparisons: usize,
    selects: usize,
    /// The node of each item, in order (to undo an attempt).
    nodes: Vec<u32>,
}

/// A model's state, to return to when an attempt does not fit.
struct Mark {
    items: usize,
    atoms: usize,
    bools: usize,
    width: u16,
    signed: Option<bool>,
    comparisons: usize,
    selects: usize,
}

impl Model {
    fn push(&mut self, n: u32, it: Item, term: bool) -> usize {
        self.items.push(it);
        self.term.push(term);
        self.nodes.push(n);
        let i = self.items.len() - 1;
        self.index.insert(n, i);
        i
    }

    fn mark(&self) -> Mark {
        Mark {
            items: self.items.len(),
            atoms: self.atoms.len(),
            bools: self.bools.len(),
            width: self.width,
            signed: self.signed,
            comparisons: self.comparisons,
            selects: self.selects,
        }
    }

    fn undo(&mut self, m: Mark) {
        for n in self.nodes.drain(m.items..) {
            self.index.remove(&n);
        }
        self.items.truncate(m.items);
        self.term.truncate(m.items);
        self.atoms.truncate(m.atoms);
        self.bools.truncate(m.bools);
        self.width = m.width;
        self.signed = m.signed;
        self.comparisons = m.comparisons;
        self.selects = m.selects;
    }

    /// The 1-bit node `n`: `None` when it does not fit.
    fn boolean(&mut self, cx: &Context, n: u32) -> Option<usize> {
        if let Some(&i) = self.index.get(&n) {
            return (!self.term[i]).then_some(i);
        }
        if self.items.len() >= MAX_ITEMS {
            return None;
        }
        let node = cx.node(n);
        let it = match node.op {
            OpCode::Const => Item::Const(cx.const_val(n).is_some_and(|v| !v.is_zero())),
            OpCode::Not => Item::Not(self.boolean(cx, node.a)?),
            OpCode::And | OpCode::Or | OpCode::Xor => {
                let (a, b) = (self.boolean(cx, node.a)?, self.boolean(cx, node.b)?);
                match node.op {
                    OpCode::And => Item::And(a, b),
                    OpCode::Or => Item::Or(a, b),
                    _ => Item::Xor(a, b),
                }
            }
            OpCode::Select => {
                let c = self.boolean(cx, node.a)?;
                let (t, e) = (self.boolean(cx, node.b)?, self.boolean(cx, node.c)?);
                Item::Select(c, t, e)
            }
            op if op.as_cmp().is_some() && cx.wid(node.a) > 1 => {
                let w = cx.wid(node.a);
                if self.width == 0 {
                    self.width = w;
                } else if self.width != w {
                    return None;
                }
                let cmp = op.as_cmp()?;
                let signed = match cmp {
                    CmpOp::Ult | CmpOp::Ule => Some(false),
                    CmpOp::Slt | CmpOp::Sle => Some(true),
                    CmpOp::Eq | CmpOp::Ne => None,
                };
                if let Some(s) = signed {
                    match self.signed {
                        None => self.signed = Some(s),
                        Some(t) if t != s => return None,
                        Some(_) => {}
                    }
                }
                let (a, b) = (self.value(cx, node.a)?, self.value(cx, node.b)?);
                self.comparisons += 1;
                match cmp {
                    CmpOp::Ult | CmpOp::Slt => Item::Less(true, a, b),
                    CmpOp::Ule | CmpOp::Sle => Item::Less(false, a, b),
                    CmpOp::Eq => Item::Equal(false, a, b),
                    CmpOp::Ne => Item::Equal(true, a, b),
                }
            }
            _ => {
                if self.bools.len() >= MAX_BOOLS {
                    return None;
                }
                self.bools.push(n);
                Item::Bool(self.bools.len() - 1)
            }
        };
        Some(self.push(n, it, false))
    }

    /// The term `n` (of the model's width): a select on a condition that fits, or an atom.
    fn value(&mut self, cx: &Context, n: u32) -> Option<usize> {
        if let Some(&i) = self.index.get(&n) {
            return self.term[i].then_some(i);
        }
        if self.items.len() >= MAX_ITEMS {
            return None;
        }
        let node = cx.node(n);
        if node.op == OpCode::Select {
            let mark = self.mark();
            if let Some(c) = self.boolean(cx, node.a)
                && let Some(t) = self.value(cx, node.b)
                && let Some(e) = self.value(cx, node.c)
            {
                self.selects += 1;
                return Some(self.push(n, Item::Select(c, t, e), true));
            }
            // Not a select between terms on an order condition: an atom after all.
            self.undo(mark);
        }
        if self.atoms.len() >= MAX_ATOMS {
            return None;
        }
        self.atoms.push(n);
        let i = self.atoms.len() - 1;
        Some(self.push(n, Item::Atom(i), true))
    }
}

/// What is known about the atoms: `le[i][j]` when atom `i` is always at most atom `j`,
/// `lt[i][j]` when always below, and conditional orders `(c, d, a, b)`: when `c <= d`, also
/// `a <= b`.
struct Known {
    le: Vec<Vec<bool>>,
    lt: Vec<Vec<bool>>,
    mono: Vec<(usize, usize, usize, usize)>,
}

fn cmp_u(a: &BitVec, b: &BitVec, op: CmpOp) -> bool {
    BitVec::apply_cmp(op, a, b).unwrap_or(false)
}

/// The order facts of the model's atoms, and the finality their facts carry.
fn known(r: &mut Runner<'_, '_>, cx: &mut Context, m: &Model) -> Result<(Known, Fin), Stop> {
    let k = m.atoms.len();
    let signed = m.signed == Some(true);
    let (lt_op, le_op) = if signed {
        (CmpOp::Slt, CmpOp::Sle)
    } else {
        (CmpOp::Ult, CmpOp::Ule)
    };
    let mut kn = Known {
        le: vec![vec![false; k]; k],
        lt: vec![vec![false; k]; k],
        mono: Vec::new(),
    };
    let mut fin = Fin::FINAL;
    // Ranges from the facts (a constant's is the constant).
    let mut bounds: Vec<Option<(BitVec, BitVec)>> = Vec::with_capacity(k);
    for &a in &m.atoms {
        let (f, ff) = facts(r, cx, a)?;
        fin = fin.and(ff);
        bounds.push(f.map(|f| {
            if signed {
                (f.srange().lo(), f.srange().hi())
            } else {
                (f.urange().lo(), f.urange().hi())
            }
        }));
    }
    for i in 0..k {
        for j in 0..k {
            if i == j {
                continue;
            }
            if let (Some((_, hi)), Some((lo, _))) = (&bounds[i], &bounds[j]) {
                if cmp_u(hi, lo, lt_op) {
                    kn.lt[i][j] = true;
                }
                if cmp_u(hi, lo, le_op) {
                    kn.le[i][j] = true;
                }
            }
        }
    }
    let pos = |n: u32| m.atoms.iter().position(|&a| a == n);
    for (i, &a) in m.atoms.iter().enumerate() {
        let node = cx.node(a);
        let below = |j: Option<usize>, kn: &mut Known| {
            if let Some(j) = j {
                kn.le[i][j] = true;
            }
        };
        match node.op {
            // Bounded by an operand, unsigned.
            OpCode::And | OpCode::LShr | OpCode::URem if !signed => {
                below(pos(node.a), &mut kn);
                if node.op == OpCode::And {
                    below(pos(node.b), &mut kn);
                }
            }
            OpCode::UDiv if !signed => {
                let (f, ff) = facts(r, cx, node.b)?;
                if f.is_some_and(|f| !f.urange().lo().is_zero()) {
                    fin = fin.and(ff);
                    below(pos(node.a), &mut kn);
                }
            }
            OpCode::Or if !signed => {
                for o in [node.a, node.b] {
                    if let Some(j) = pos(o) {
                        kn.le[j][i] = true;
                    }
                }
            }
            _ => {}
        }
        // Monotone pairs: the same operation with the same second operand.
        let monotone = if signed {
            matches!(node.op, OpCode::AShr)
        } else {
            matches!(node.op, OpCode::LShr | OpCode::UDiv)
        };
        if monotone {
            for (j, &b) in m.atoms.iter().enumerate() {
                let o = cx.node(b);
                if j != i
                    && o.op == node.op
                    && o.b == node.b
                    && let (Some(c), Some(d)) = (pos(node.a), pos(o.a))
                {
                    kn.mono.push((c, d, i, j));
                }
            }
        }
    }
    Ok((kn, fin))
}

/// Every total preorder of `k <= MAX_ATOMS` atoms, computed once per `k`.
fn preorders(k: usize) -> &'static [Vec<u8>] {
    static CACHE: [std::sync::OnceLock<Vec<Vec<u8>>>; MAX_ATOMS + 1] =
        [const { std::sync::OnceLock::new() }; MAX_ATOMS + 1];
    CACHE[k].get_or_init(|| enumerate_preorders(k))
}

/// Every total preorder of `k` atoms, as ranks (ties share a rank; ranks are `0..=max`).
fn enumerate_preorders(k: usize) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut r = vec![0u8; k];
    let total = (k as u32).pow(k as u32).max(1);
    for code in 0..total {
        let mut c = code;
        for x in r.iter_mut() {
            *x = (c % k.max(1) as u32) as u8;
            c /= k.max(1) as u32;
        }
        let max = r.iter().copied().max().unwrap_or(0);
        if (0..=max).all(|v| r.contains(&v)) {
            out.push(r.clone());
        }
    }
    out
}

fn feasible(kn: &Known, rank: &[u8]) -> bool {
    let k = rank.len();
    for i in 0..k {
        for j in 0..k {
            if (kn.le[i][j] && rank[i] > rank[j]) || (kn.lt[i][j] && rank[i] >= rank[j]) {
                return false;
            }
        }
    }
    kn.mono
        .iter()
        .all(|&(c, d, a, b)| rank[c] > rank[d] || rank[a] <= rank[b])
}

/// Every item's value in one state: a term's is the rank of the atom it takes, a 1-bit
/// item's 0 or 1.
fn eval(items: &[Item], rank: &[u8], bools: u32, out: &mut Vec<u8>) {
    out.clear();
    for it in items {
        let v = match *it {
            Item::Atom(i) => rank[i],
            Item::Bool(i) => ((bools >> i) & 1) as u8,
            Item::Const(b) => u8::from(b),
            Item::Not(a) => 1 - out[a],
            Item::And(a, b) => out[a] & out[b],
            Item::Or(a, b) => out[a] | out[b],
            Item::Xor(a, b) => out[a] ^ out[b],
            Item::Less(strict, a, b) => u8::from(if strict {
                out[a] < out[b]
            } else {
                out[a] <= out[b]
            }),
            Item::Equal(neg, a, b) => u8::from((out[a] == out[b]) != neg),
            Item::Select(c, t, e) => {
                if out[c] != 0 {
                    out[t]
                } else {
                    out[e]
                }
            }
        };
        out.push(v);
    }
}

/// What the node is, if simpler.
enum Found {
    Const(bool),
    /// A comparison between atoms: `(op, a, b)`.
    Cmp(CmpOp, u32, u32),
    /// A 1-bit leaf, or its complement.
    Leaf(u32, bool),
    /// A term atom.
    Atom(u32),
    /// The minimum (`false`) or maximum (`true`) of two atoms.
    Extreme(bool, u32, u32),
    /// A part of the formula (a node below it).
    Part(u32),
}

/// Decides the node `n` (1-bit, or a term select): `Some` form it always equals.
pub(super) fn decide(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<(u32, Vec<u32>, Fin)>, Stop> {
    let node = cx.node(n);
    let mut m = Model {
        items: Vec::new(),
        index: IdMap::default(),
        atoms: Vec::new(),
        bools: Vec::new(),
        width: 0,
        signed: None,
        term: Vec::new(),
        comparisons: 0,
        selects: 0,
        nodes: Vec::new(),
    };
    let root = if node.width == 1 {
        m.boolean(cx, n)
    } else if node.op == OpCode::Select {
        m.width = node.width;
        m.value(cx, n)
    } else {
        None
    };
    let Some(root) = root else {
        return Ok(None);
    };
    // Worth deciding: several comparisons, or selects between terms (a lone comparison of two
    // atoms is the compares pass's, unless their order is known).
    if m.atoms.len() < 2 || (m.comparisons < 2 && m.selects == 0 && !related(cx, &m)) {
        return Ok(None);
    }
    let (kn, fin) = known(r, cx, &m)?;
    let orders = preorders(m.atoms.len());
    // With nothing known, every order is possible.
    let anything = kn.mono.is_empty() && kn.le.iter().chain(&kn.lt).all(|row| !row.contains(&true));
    // The states: each possible order with each assignment of the 1-bit leaves.
    let possible: Vec<&[u8]> = orders
        .iter()
        .filter(|rk| anything || feasible(&kn, rk))
        .map(Vec::as_slice)
        .collect();
    let per = 1usize << m.bools.len();
    let count = possible.len() * per;
    r.meter
        .charge(Counter::PassWork, (count * m.items.len()) as u64 / 8 + 1)?;
    if count == 0 {
        // No order is possible: the facts contradict each other (infeasible assumptions).
        return Ok(None);
    }
    let state = |s: usize| (possible[s / per], (s % per) as u32);
    // Whatever the formula turns out to be, it agrees with it on every state: first on a
    // sample of them, which most formulas with no simpler form fail.
    if count > 64 {
        let sample: Vec<(&[u8], u32)> = (0..32).map(|i| state(i * count / 32)).collect();
        if !may_simplify(&m, root, &sample) {
            return Ok(None);
        }
    }
    let states: Vec<(&[u8], u32)> = (0..count).map(state).collect();
    // Every item's value in every state (item-major).
    let mut vals = Vec::with_capacity(m.items.len());
    let mut all = vec![0u8; m.items.len() * states.len()];
    for (s, (rk, b)) in states.iter().enumerate() {
        eval(&m.items, rk, *b, &mut vals);
        for (i, &v) in vals.iter().enumerate() {
            all[i * states.len() + s] = v;
        }
    }
    let row = |i: usize| &all[i * states.len()..(i + 1) * states.len()];
    let table: Vec<u8> = row(root).to_vec();
    // A part of the formula that always agrees with the whole (a redundant conjunct, a
    // disjunct that implies the rest, an arm always taken).
    let part = (0..m.items.len())
        .find(|&i| {
            i != root
                && m.term[i] == m.term[root]
                && !matches!(m.items[i], Item::Const(_))
                && row(i) == &table[..]
        })
        .map(|i| m.nodes[i]);
    let k = m.atoms.len();
    let found = if !m.term[root] {
        if table.iter().all(|&v| v == 1) {
            Some(Found::Const(true))
        } else if table.iter().all(|&v| v == 0) {
            Some(Found::Const(false))
        } else {
            let pick = |f: &dyn Fn(&[u8], u32) -> bool| {
                states
                    .iter()
                    .zip(&table)
                    .all(|((rk, b), &v)| f(rk, *b) == (v == 1))
            };
            let mut found = None;
            'pairs: for i in 0..k {
                for j in 0..k {
                    if i == j {
                        continue;
                    }
                    if pick(&|rk, _| rk[i] < rk[j]) {
                        found = Some((true, i, j, false));
                        break 'pairs;
                    }
                    if pick(&|rk, _| rk[i] <= rk[j]) {
                        found = Some((false, i, j, false));
                        break 'pairs;
                    }
                    if i < j && pick(&|rk, _| rk[i] == rk[j]) {
                        found = Some((false, i, j, true));
                        break 'pairs;
                    }
                    if i < j && pick(&|rk, _| rk[i] != rk[j]) {
                        found = Some((true, i, j, true));
                        break 'pairs;
                    }
                }
            }
            let signed = m.signed == Some(true);
            match found {
                Some((strict, i, j, eq)) => {
                    let op = match (eq, strict, signed) {
                        (true, false, _) => CmpOp::Eq,
                        (true, true, _) => CmpOp::Ne,
                        (false, true, false) => CmpOp::Ult,
                        (false, false, false) => CmpOp::Ule,
                        (false, true, true) => CmpOp::Slt,
                        (false, false, true) => CmpOp::Sle,
                    };
                    Some(Found::Cmp(op, m.atoms[i], m.atoms[j]))
                }
                None => (0..m.bools.len()).find_map(|bi| {
                    [false, true].into_iter().find_map(|neg| {
                        pick(&|_, b| (((b >> bi) & 1) == 1) != neg)
                            .then_some(Found::Leaf(m.bools[bi], neg))
                    })
                }),
            }
        }
    } else {
        // A term: always one atom (by rank), or the lesser or greater of two.
        let pick =
            |f: &dyn Fn(&[u8]) -> u8| states.iter().zip(&table).all(|((rk, _), &v)| f(rk) == v);
        let mut found = (0..k)
            .find(|&i| pick(&|rk| rk[i]))
            .map(|i| Found::Atom(m.atoms[i]));
        if found.is_none() && m.signed.is_some() {
            'two: for i in 0..k {
                for j in i + 1..k {
                    if pick(&|rk| rk[i].min(rk[j])) {
                        found = Some(Found::Extreme(false, m.atoms[i], m.atoms[j]));
                        break 'two;
                    }
                    if pick(&|rk| rk[i].max(rk[j])) {
                        found = Some(Found::Extreme(true, m.atoms[i], m.atoms[j]));
                        break 'two;
                    }
                }
            }
        }
        found
    };
    let found = match (found, part) {
        (Some(f), _) => f,
        (None, Some(p)) => Found::Part(p),
        (None, None) => return Ok(None),
    };
    let signed = m.signed == Some(true);
    let lt = if signed { CmpOp::Slt } else { CmpOp::Ult };
    let e = match found {
        Found::Const(b) => r.build(cx, |cx| cx.mk_const(&BitVec::from_bool(b)))?,
        Found::Cmp(op, a, b) => r.build(cx, |cx| cx.c_cmp(op, a, b))?,
        Found::Leaf(l, false) => l,
        Found::Leaf(l, true) => r.build(cx, |cx| cx.c_un(crate::UnOp::Not, l))?,
        Found::Atom(a) | Found::Part(a) => a,
        Found::Extreme(max, a, b) => {
            let c = r.build(cx, |cx| cx.c_cmp(lt, a, b))?;
            let (t, f) = if max { (b, a) } else { (a, b) };
            r.build(cx, |cx| cx.c_select(c, t, f))?
        }
    };
    let mut atoms = m.atoms.clone();
    atoms.extend(&m.bools);
    Ok(Some((e, atoms, fin)))
}

/// Whether some form [`decide`] looks for agrees with the formula at `root` on `sample` (a
/// necessary condition for agreeing on every state).
fn may_simplify(m: &Model, root: usize, sample: &[(&[u8], u32)]) -> bool {
    let mut vals = Vec::with_capacity(m.items.len());
    let mut rows = vec![vec![0u8; sample.len()]; m.items.len()];
    for (s, (rk, b)) in sample.iter().enumerate() {
        eval(&m.items, rk, *b, &mut vals);
        for (i, &v) in vals.iter().enumerate() {
            rows[i][s] = v;
        }
    }
    let t = &rows[root];
    // A part of the formula.
    if (0..m.items.len()).any(|i| {
        i != root
            && m.term[i] == m.term[root]
            && !matches!(m.items[i], Item::Const(_))
            && rows[i] == *t
    }) {
        return true;
    }
    let agrees =
        |f: &dyn Fn(&[u8], u32) -> u8| sample.iter().zip(t).all(|((rk, b), &v)| f(rk, *b) == v);
    let k = m.atoms.len();
    if !m.term[root] {
        // A constant, a comparison of two atoms, a 1-bit leaf or its complement.
        t.iter().all(|&v| v == t[0])
            || (0..k).any(|i| {
                (0..k).any(|j| {
                    i != j
                        && (agrees(&|rk, _| u8::from(rk[i] < rk[j]))
                            || agrees(&|rk, _| u8::from(rk[i] <= rk[j]))
                            || agrees(&|rk, _| u8::from(rk[i] == rk[j]))
                            || agrees(&|rk, _| u8::from(rk[i] != rk[j])))
                })
            })
            || (0..m.bools.len()).any(|bi| {
                [false, true]
                    .into_iter()
                    .any(|neg| agrees(&|_, b| u8::from(((b >> bi) & 1 == 1) != neg)))
            })
    } else {
        // An atom, or the lesser or greater of two.
        (0..k).any(|i| agrees(&|rk, _| rk[i]))
            || (m.signed.is_some()
                && (0..k).any(|i| {
                    (i + 1..k).any(|j| {
                        agrees(&|rk, _| rk[i].min(rk[j])) || agrees(&|rk, _| rk[i].max(rk[j]))
                    })
                }))
    }
}

/// Whether two atoms of the model are related by structure (so a lone comparison of them may
/// be decided).
fn related(cx: &Context, m: &Model) -> bool {
    let has = |n: u32| m.atoms.contains(&n);
    m.atoms.iter().any(|&a| {
        let node = cx.node(a);
        match node.op {
            OpCode::And | OpCode::Or => has(node.a) || has(node.b),
            OpCode::LShr | OpCode::URem | OpCode::UDiv | OpCode::AShr => {
                has(node.a)
                    || m.atoms.iter().any(|&b| {
                        let o = cx.node(b);
                        b != a && o.op == node.op && o.b == node.b
                    })
            }
            _ => false,
        }
    })
}
