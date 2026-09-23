//! Invertibility: when an expression is an injective or bijective function of one of its
//! subexpressions, and what that function's inverse gives at a constant.
//!
//! An expression is read as a chain of *layers* from a subexpression (the *inner* value) up to
//! its root. A layer is one node that is an injective function of one operand when every other
//! operand (a *parameter*) is fixed:
//!
//! | Layer | Kind | Preimage of `c` |
//! |-|-|-|
//! | `~v`, `-v`, `bswap(v)`, `bitrev(v)` | bijective | the same operator of `c` |
//! | `v + k`, `v - k`, `k - v`, `v ^ k` | bijective | `c - k`, `c + k`, `k - c`, `c ^ k` |
//! | `v * k` with `k` proved odd | bijective | `c * k⁻¹` (`k⁻¹` by Newton's iteration) |
//! | `rotl(v, k)`, `rotr(v, k)`, any `k` | bijective | the opposite rotation of `c` |
//! | `zext(v)`, `sext(v)`, `concat(v, k)`, `concat(k, v)` | injective | the part of `c`, if `c` is an image |
//! | an extension output declared invertible in an argument | as declared | [`ExtOp::invert`] |
//! | `v ^ g(v)`, `v + g(v)`, `v - g(v)`, `g(v) - v`, triangular | bijective | solved bit by bit |
//!
//! Composing layers keeps injectivity (and bijectivity), so a chain of layers is injective in
//! its inner value; nothing else is ever claimed.
//!
//! **Triangular layers.** Combining two values that both depend on the inner one generally
//! destroys invertibility: `f(x) ^ x`, `f_a(x) ^ f_b(x)` and `f_a(x) | f_b(x)` are not injective
//! even for bijective `f`. The one form accepted is `v ⊙ g(v)` with `⊙` one of `^ + -`, where
//! `g` is a function of `v` (and of parameters) whose *bit dependencies* make the whole map
//! triangular. `D_i`, the bits of `v` that bit `i` of `g` can depend on, is computed per
//! operator (bitwise operators bit by bit, arithmetic from the bits below, shifts and rotations
//! re-indexed, by a variable count over the count's range), with every bit the facts pin
//! dropped; the facts of `g` are computed afresh with `v` unknown, so they hold for every value
//! of `v`, not only the values it takes in context. Then:
//!
//! - `v ^ g(v)` is bijective when the graph "bit `i` reads the bits `D_i`" is acyclic: the bits
//!   of `v` are recovered level by level in topological order. This covers the xorshift
//!   involution `h ^ ((h >>u 32) >>u (h >>u 60))` (the low half reads only the high half, whose
//!   bits `g` leaves zero) and xorshift steps `x ^ (x << 13)`.
//! - `v + g(v)`, `v - g(v)` and `g(v) - v` are bijective when every `D_i` lies below `i`: carries
//!   only travel upward, so bit `i` of the result is bit `i` of `v` flipped by lower bits (a
//!   T-function with an invertible diagonal), recovered from bit 0 up. This covers
//!   `u - (((u << 1) | b) & h)`, and refuses `u - ((u | b) & h)`, whose bit `i` reads bit `i`.
//!
//! The analysis looks at no more than [`MAX_REGION`] nodes of `g`, and only at inner values of
//! at most 128 bits (dependencies are 128-bit masks); larger layers are not recognized.
//!
//! [`ExtOp::invert`]: crate::ext::ExtOp::invert

#[cfg(test)]
mod tests;

use crate::error::Error;
use crate::expr::{Context, Expr, OpCode};
use crate::ext::Invertible;
use crate::facts::{Assumptions, Facts, KnownBits, Proof, Reliance, Truth};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// The most nodes of a triangular layer's `g` examined.
pub(crate) const MAX_REGION: usize = 256;
/// The most node pairs examined when matching the `g`s of two triangular layers.
const MAX_MATCH: u32 = 1024;
/// The deepest the matching recursion goes.
const MAX_MATCH_DEPTH: u32 = 256;
/// The widest inner value of a triangular layer.
const MAX_TRI_BITS: u16 = 128;
/// The most leaves of an or-tree split by [`solve_eq`]'s callers.
pub(crate) const MAX_SPLIT: usize = 16;

/// What a layer, or a chain of layers, is known to be.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Kind {
    /// Distinct inputs give distinct outputs.
    Injective,
    /// Injective and onto (input and output have one width).
    Bijective,
}

/// Where the analysis gets facts about parameters, and the account its work is charged to.
pub(crate) trait Oracle {
    /// Why the analysis had to stop (a budget, an error).
    type Err;
    /// Facts about node `i`, valid wherever the result is used; `None` if unavailable.
    fn facts(&mut self, cx: &mut Context, i: u32) -> Result<Option<Facts>, Self::Err>;
    /// Charges `units` of work.
    fn charge(&mut self, units: u64) -> Result<(), Self::Err>;
}

/// How a layer maps its inner value `v`. Parameters are node indices.
#[derive(Clone, Debug)]
pub(crate) enum Map {
    /// `op(v)`: `not`, `neg`, `bswap` or `bitrev`, each its own inverse.
    Un(UnOp),
    /// `v + k`.
    Add(u32),
    /// `v - k`.
    Sub(u32),
    /// `k - v`.
    SubFrom(u32),
    /// `v ^ k`.
    Xor(u32),
    /// `v * k`, `k` odd.
    Mul(u32),
    /// `rotl(v, k)`.
    RotL(u32),
    /// `rotr(v, k)`.
    RotR(u32),
    /// `zext(v)`.
    Zext,
    /// `sext(v)`.
    Sext,
    /// `concat(v, k)`: `v` is the high part.
    ConcatHi(u32),
    /// `concat(k, v)`: `v` is the low part.
    ConcatLo(u32),
    /// Output `output` of an extension call, in argument `arg`.
    Ext {
        /// The output.
        output: u8,
        /// The argument position of `v`.
        arg: u8,
    },
    /// `v ⊙ g(v)`, triangular.
    Tri(Box<Tri>),
}

/// One layer at the top of a node: the node is `map(inner)`.
#[derive(Clone, Debug)]
pub(crate) struct Layer {
    /// The operand the node is a function of.
    pub(crate) inner: u32,
    /// Injective or bijective.
    pub(crate) kind: Kind,
    /// How.
    pub(crate) map: Map,
}

/// The operator joining `v` and `g(v)` in a triangular layer.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum TriOp {
    /// `v ^ g`.
    Xor,
    /// `v + g`.
    Add,
    /// `v - g`.
    Sub,
    /// `g - v`.
    SubFrom,
}

/// A triangular layer `v ⊙ g(v)`, ready to be solved at a constant.
#[derive(Clone, Debug)]
pub(crate) struct Tri {
    op: TriOp,
    /// `g`.
    g: u32,
    /// The nodes of `g` that depend on `v` (`g` among them), ascending: a topological order.
    region: Vec<u32>,
    /// For `^`: the bits of `v` in the order they are recovered, a mask per level.
    levels: Vec<u128>,
}

// ----- primitive layers -------------------------------------------------------------------------

/// The primitive layer of node `n` in its operand at position `pos`, the others fixed: the
/// map, its kind, and the parameter that must be proved odd (a multiplier), if any.
fn primitive(cx: &Context, n: u32, pos: usize) -> Option<(Map, Kind, Option<u32>)> {
    use Kind::{Bijective, Injective};
    let node = cx.node(n);
    let other = if pos == 0 { node.b } else { node.a };
    Some(match (node.op, pos) {
        (OpCode::Not, 0) => (Map::Un(UnOp::Not), Bijective, None),
        (OpCode::Neg, 0) => (Map::Un(UnOp::Neg), Bijective, None),
        (OpCode::Bswap, 0) => (Map::Un(UnOp::Bswap), Bijective, None),
        (OpCode::BitRev, 0) => (Map::Un(UnOp::BitRev), Bijective, None),
        (OpCode::Add, 0 | 1) => (Map::Add(other), Bijective, None),
        (OpCode::Xor, 0 | 1) => (Map::Xor(other), Bijective, None),
        (OpCode::Mul, 0 | 1) => (Map::Mul(other), Bijective, Some(other)),
        (OpCode::Sub, 0) => (Map::Sub(node.b), Bijective, None),
        (OpCode::Sub, 1) => (Map::SubFrom(node.a), Bijective, None),
        (OpCode::RotL, 0) => (Map::RotL(node.b), Bijective, None),
        (OpCode::RotR, 0) => (Map::RotR(node.b), Bijective, None),
        (OpCode::Zext, 0) => (Map::Zext, Injective, None),
        (OpCode::Sext, 0) => (Map::Sext, Injective, None),
        (OpCode::Concat, 0) => (Map::ConcatHi(node.b), Injective, None),
        (OpCode::Concat, 1) => (Map::ConcatLo(node.a), Injective, None),
        _ => return None,
    })
}

/// Whether `k` is proved odd.
fn odd<O: Oracle>(cx: &mut Context, o: &mut O, k: u32) -> Result<bool, O::Err> {
    if let Some(v) = cx.const_val(k) {
        return Ok(v.bit(0) == Some(true));
    }
    Ok(o.facts(cx, k)?.and_then(|f| f.known().bit(0)) == Some(true))
}

/// The declared invertibility of extension node `n` in argument `pos`, given the known bits of
/// the other arguments (its own is always unknown: it is the value that varies).
fn ext_kind<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    n: u32,
    pos: usize,
) -> Result<Option<Kind>, O::Err> {
    let node = cx.node(n);
    let Some((_, output)) = node.op.as_ext() else {
        return Ok(None);
    };
    let args: Vec<u32> = node.children().collect();
    let mut known = Vec::with_capacity(args.len());
    for (k, &c) in args.iter().enumerate() {
        let w = cx.width_of(c);
        known.push(if k == pos {
            KnownBits::unknown(w)
        } else if let Some(v) = cx.const_val(c) {
            KnownBits::constant(&v)
        } else {
            o.facts(cx, c)?.map_or(KnownBits::unknown(w), |f| f.known())
        });
    }
    let Some(op) = cx.registry.as_deref().and_then(|r| r.op_at(node.aux)) else {
        return Ok(None);
    };
    Ok(match op.invertible(output as u8, pos as u8, &known) {
        Invertible::Bijective if cx.width_of(n) == cx.width_of(args[pos]) => Some(Kind::Bijective),
        Invertible::Injective => Some(Kind::Injective),
        _ => None,
    })
}

/// The multiplicative inverse of odd `k` modulo `2^W` (Newton's iteration: each step doubles
/// the number of correct low bits).
pub(crate) fn mul_inverse(k: &BitVec) -> Option<BitVec> {
    if k.bit(0) != Some(true) {
        return None;
    }
    let w = k.width();
    let one = BitVec::one(w);
    let two = BitVec::wrapping_from_u64(w, 2);
    let mul = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Mul, a, b);
    let mut i = one;
    // 2^10 > 512 correct bits.
    for _ in 0..10 {
        i = mul(&i, &BitVec::bin_unchecked(BinOp::Sub, &two, &mul(k, &i)));
    }
    (mul(k, &i) == one).then_some(i)
}

// ----- triangular layers --------------------------------------------------------------------------

/// Per bit of a node, the bits of `v` it can depend on.
type Deps = Vec<u128>;

fn all(d: &[u128]) -> u128 {
    d.iter().fold(0, |a, x| a | x)
}

/// Each bit also depends on everything the bits below it depend on (carries).
fn prefix(mut d: Deps) -> Deps {
    let mut acc = 0;
    for x in &mut d {
        acc |= *x;
        *x = acc;
    }
    d
}

/// A count's range `[lo, hi]` from its facts, saturated to `u64`.
fn count_range(f: &Facts) -> (u64, u64) {
    let sat = |v: BitVec| v.to_u64().unwrap_or(u64::MAX);
    (sat(f.urange().lo()), sat(f.urange().hi()))
}

/// Dependencies of a shift or rotation of `a` by a count whose facts are `cf` and whose own
/// dependencies are `cd` (all zero for a parameter).
fn shift_deps(op: OpCode, a: &[u128], cf: &Facts, cd: u128) -> Deps {
    let w = a.len();
    let wu = w as u64;
    let (lo, hi) = count_range(cf);
    let mut out = vec![cd; w];
    match op {
        OpCode::RotL | OpCode::RotR => {
            if hi - lo >= wu - 1 {
                let x = all(a) | cd;
                out.iter_mut().for_each(|o| *o = x);
                return out;
            }
            for t in lo..=hi {
                let t = (t % wu) as usize;
                for (i, o) in out.iter_mut().enumerate() {
                    let j = if op == OpCode::RotL {
                        (i + w - t) % w
                    } else {
                        (i + t) % w
                    };
                    *o |= a[j];
                }
            }
        }
        _ => {
            // A count of W or more is one case (everything shifted out, or the sign fill).
            for t in lo.min(wu)..=hi.min(wu) {
                let t = t as usize;
                for (i, o) in out.iter_mut().enumerate() {
                    *o |= match op {
                        OpCode::Shl if t <= i && t < w => a[i - t],
                        OpCode::LShr if i + t < w => a[i + t],
                        OpCode::AShr => a[(i + t).min(w - 1)],
                        _ => 0,
                    };
                }
            }
        }
    }
    out
}

/// The dependencies of node `i` from its operands' (`d`) and facts (`f`).
fn node_deps(cx: &Context, i: u32, d: &IdMap<u32, Deps>, f: &IdMap<u32, Facts>) -> Deps {
    let n = cx.node(i);
    let w = usize::from(n.width);
    let full = || {
        let x = n.children().fold(0, |acc, c| acc | all(&d[&c]));
        vec![x; w]
    };
    let zip = |x: u32, y: u32| -> Deps { d[&x].iter().zip(&d[&y]).map(|(p, q)| p | q).collect() };
    match n.op {
        OpCode::Const | OpCode::Sym => vec![0; w],
        OpCode::Not => d[&n.a].clone(),
        OpCode::Neg => prefix(d[&n.a].clone()),
        OpCode::Bswap => {
            let a = &d[&n.a];
            (0..w).map(|b| a[(w / 8 - 1 - b / 8) * 8 + b % 8]).collect()
        }
        OpCode::BitRev => {
            let a = &d[&n.a];
            (0..w).map(|b| a[w - 1 - b]).collect()
        }
        OpCode::Add | OpCode::Sub | OpCode::Mul => prefix(zip(n.a, n.b)),
        OpCode::And | OpCode::Or | OpCode::Xor => zip(n.a, n.b),
        OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR => {
            let cf = match cx.const_val(n.b) {
                Some(v) => Facts::constant(&v),
                None => f[&n.b],
            };
            shift_deps(n.op, &d[&n.a], &cf, all(&d[&n.b]))
        }
        OpCode::Zext => {
            let a = &d[&n.a];
            (0..w).map(|b| a.get(b).copied().unwrap_or(0)).collect()
        }
        OpCode::Sext => {
            let a = &d[&n.a];
            (0..w).map(|b| a[b.min(a.len() - 1)]).collect()
        }
        OpCode::Extract => {
            let a = &d[&n.a];
            let lo = n.b as usize;
            (0..w).map(|b| a[lo + b]).collect()
        }
        OpCode::Concat => {
            let (h, l) = (&d[&n.a], &d[&n.b]);
            (0..w)
                .map(|b| if b < l.len() { l[b] } else { h[b - l.len()] })
                .collect()
        }
        OpCode::Select => {
            let c = all(&d[&n.a]);
            d[&n.b]
                .iter()
                .zip(&d[&n.c])
                .map(|(t, e)| c | t | e)
                .collect()
        }
        // Every bit may read every bit of every operand: high products, divisions, counts,
        // comparisons, deposits and extractions, extension outputs.
        _ => full(),
    }
}

/// Whether `v ⊙ g` is a triangular bijection of `v`, where `region` lists the nodes of `g`
/// that depend on `v` (ascending, `g` among them) and every other operand met below them is a
/// parameter (a constant, or facts from the oracle). For `^`, the level masks in solving order.
fn triangular<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    op: TriOp,
    v: u32,
    g: u32,
    region: &[u32],
) -> Result<Option<Vec<u128>>, O::Err> {
    let wv = cx.wid(v);
    if wv > MAX_TRI_BITS || cx.wid(g) != wv || region.last() != Some(&g) {
        return Ok(None);
    }
    let w = usize::from(wv);
    let mut deps: IdMap<u32, Deps> = IdMap::default();
    let mut facts: IdMap<u32, Facts> = IdMap::default();
    deps.insert(v, (0..w).map(|b| 1u128 << b).collect());
    facts.insert(v, Facts::top(cx.width_of(v)));
    for &i in region {
        let n = cx.node(i);
        // Parameters: constants, or whatever the oracle knows.
        for c in n.children() {
            if deps.contains_key(&c) {
                continue;
            }
            let f = match cx.const_val(c) {
                Some(k) => Facts::constant(&k),
                None => o
                    .facts(cx, c)?
                    .unwrap_or_else(|| Facts::top(cx.width_of(c))),
            };
            deps.insert(c, vec![0; usize::from(cx.wid(c))]);
            facts.insert(c, f);
        }
        // A variable shift reads, for every result bit, the source bit of every count value.
        let span = match n.op {
            OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR
                if cx.const_val(n.b).is_none() =>
            {
                let (lo, hi) = count_range(&facts[&n.b]);
                (hi - lo).min(u64::from(n.width))
            }
            _ => 0,
        };
        o.charge(1 + u64::from(n.width) * (1 + span))?;
        let kids: Vec<Facts> = n.children().map(|c| facts[&c]).collect();
        let refs: Vec<&Facts> = kids.iter().collect();
        let f = cx.transfer_local(i, &refs);
        let mut d = node_deps(cx, i, &deps, &facts);
        // A bit the facts pin depends on nothing.
        let known = f.known().known();
        for (b, x) in d.iter_mut().enumerate() {
            if known.bit(b as u16) == Some(true) {
                *x = 0;
            }
        }
        deps.insert(i, d);
        facts.insert(i, f);
    }
    let d = &deps[&g];
    o.charge(w as u64 * w as u64 / 16 + 1)?;
    Ok(match op {
        TriOp::Xor => levels(d),
        // Strictly below: bit `b` reads only bits `0..b`.
        TriOp::Add | TriOp::Sub | TriOp::SubFrom => d
            .iter()
            .enumerate()
            .all(|(b, x)| x >> b == 0)
            .then(Vec::new),
    })
}

/// The bits in the order they can be recovered: each level's bits read only earlier levels.
/// `None` if the dependencies have a cycle (a bit reading itself included).
fn levels(d: &[u128]) -> Option<Vec<u128>> {
    let w = d.len();
    let full = if w == 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    };
    let mut done = 0u128;
    let mut out = Vec::new();
    while done != full {
        let level = (0..w)
            .filter(|&b| done >> b & 1 == 0 && d[b] & !done == 0)
            .fold(0u128, |acc, b| acc | 1 << b);
        if level == 0 {
            return None;
        }
        done |= level;
        out.push(level);
    }
    Some(out)
}

/// The nodes of `g` down to `v` when every other leaf below `g` is a constant (ascending);
/// `None` if a leaf is not, or there are too many.
fn const_region(cx: &Context, g: u32, v: u32) -> Option<Vec<u32>> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut out = Vec::new();
    let mut stack = vec![g];
    while let Some(i) = stack.pop() {
        if i == v || cx.const_val(i).is_some() || seen.insert(i, ()).is_some() {
            continue;
        }
        let n = cx.node(i);
        if n.op == OpCode::Sym || out.len() >= MAX_REGION {
            return None;
        }
        out.push(i);
        stack.extend(n.children());
    }
    out.sort_unstable();
    Some(out)
}

/// Matches `g1` with `g2` as one function applied to `v1` and to `v2`: equal structure,
/// except that `v1` in `g1` stands where `v2` is in `g2`; subterms both share are parameters.
struct Match<'c> {
    cx: &'c Context,
    v1: u32,
    v2: u32,
    /// Each node of `g1` and its partner in `g2`.
    map: IdMap<u32, u32>,
    trail: Vec<u32>,
    steps: u32,
    depth: u32,
}

impl Match<'_> {
    fn bind(&mut self, x1: u32, x2: u32) {
        self.map.insert(x1, x2);
        self.trail.push(x1);
    }

    fn undo(&mut self, to: usize) {
        while self.trail.len() > to {
            if let Some(x) = self.trail.pop() {
                self.map.remove(&x);
            }
        }
    }

    /// Bounded by [`MAX_MATCH`] steps and [`MAX_MATCH_DEPTH`] levels of recursion.
    fn go(&mut self, x1: u32, x2: u32) -> bool {
        self.steps += 1;
        if self.steps > MAX_MATCH || self.depth >= MAX_MATCH_DEPTH {
            return false;
        }
        if let Some(&p) = self.map.get(&x1) {
            return p == x2;
        }
        if x1 == self.v1 || x2 == self.v2 {
            if x1 == self.v1 && x2 == self.v2 {
                self.bind(x1, x2);
                return true;
            }
            return false;
        }
        if x1 == x2 {
            self.bind(x1, x2);
            return true;
        }
        let (n1, n2) = (self.cx.node(x1), self.cx.node(x2));
        if n1.op != n2.op
            || n1.width != n2.width
            || n1.aux != n2.aux
            || matches!(n1.op, OpCode::Const | OpCode::Sym)
            || (n1.op == OpCode::Extract && n1.b != n2.b)
        {
            return false;
        }
        let mark = self.trail.len();
        self.bind(x1, x2);
        self.depth += 1;
        let (k1, k2): (Vec<u32>, Vec<u32>) = (n1.children().collect(), n2.children().collect());
        let commutative = n1.op.as_bin().is_some_and(BinOp::is_commutative)
            || matches!(n1.op, OpCode::Eq | OpCode::Ne);
        let ok = if commutative {
            (self.go(k1[0], k2[0]) && self.go(k1[1], k2[1])) || {
                self.undo(mark + 1);
                self.go(k1[0], k2[1]) && self.go(k1[1], k2[0])
            }
        } else {
            k1.iter().zip(&k2).all(|(&a, &b)| self.go(a, b))
        };
        self.depth -= 1;
        if !ok {
            self.undo(mark);
        }
        ok
    }
}

/// The region of `g1` (its nodes that depend on `v1`, ascending) if `g1` and `g2` are one
/// function applied to `v1` and to `v2`; and the steps the match took.
fn match_region(cx: &Context, g1: u32, g2: u32, v1: u32, v2: u32) -> (Option<Vec<u32>>, u32) {
    let mut m = Match {
        cx,
        v1,
        v2,
        map: IdMap::default(),
        trail: Vec::new(),
        steps: 0,
        depth: 0,
    };
    let ok = m.go(g1, g2);
    (ok.then(|| m.region(v1)).flatten(), m.steps)
}

impl Match<'_> {
    /// The nodes of `g1` matched through the hole, ascending (`None` if too many).
    fn region(&self, v1: u32) -> Option<Vec<u32>> {
        let mut region: Vec<u32> = self
            .map
            .iter()
            .filter(|&(&x1, &x2)| x1 != x2 && x1 != v1)
            .map(|(&x1, _)| x1)
            .collect();
        if region.len() > MAX_REGION {
            return None;
        }
        region.sort_unstable();
        Some(region)
    }
}

/// The ways node `n` (`^`, `+` or `-`) can read as `v ⊙ g`: `(v, g, op)`.
fn tri_forms(cx: &Context, n: u32) -> Vec<(u32, u32, TriOp)> {
    let node = cx.node(n);
    match node.op {
        OpCode::Xor => vec![(node.a, node.b, TriOp::Xor), (node.b, node.a, TriOp::Xor)],
        OpCode::Add => vec![(node.a, node.b, TriOp::Add), (node.b, node.a, TriOp::Add)],
        OpCode::Sub => vec![
            (node.a, node.b, TriOp::Sub),
            (node.b, node.a, TriOp::SubFrom),
        ],
        _ => Vec::new(),
    }
}

// ----- solving at a constant (R2) -----------------------------------------------------------------

/// The layer at the top of `n` whose parameters are all constants, so that its preimage of a
/// constant is a constant.
pub(crate) fn solve_layer<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    n: u32,
) -> Result<Option<Layer>, O::Err> {
    let node = cx.node(n);
    let kids: Vec<u32> = node.children().collect();
    let open: Vec<usize> = (0..kids.len())
        .filter(|&p| cx.const_val(kids[p]).is_none())
        .collect();
    if let [pos] = open[..] {
        if let Some((map, kind, cond)) = primitive(cx, n, pos) {
            if cond.is_some_and(|k| cx.const_val(k).and_then(|v| v.bit(0)) != Some(true)) {
                return Ok(None);
            }
            return Ok(Some(Layer {
                inner: kids[pos],
                kind,
                map,
            }));
        }
        if let Some((_, output)) = node.op.as_ext()
            && let Some(kind) = ext_kind(cx, o, n, pos)?
        {
            return Ok(Some(Layer {
                inner: kids[pos],
                kind,
                map: Map::Ext {
                    output: output as u8,
                    arg: pos as u8,
                },
            }));
        }
        return Ok(None);
    }
    if open.len() != 2 {
        return Ok(None);
    }
    for (v, g, op) in tri_forms(cx, n) {
        o.charge(1)?;
        let Some(region) = const_region(cx, g, v) else {
            continue;
        };
        o.charge(region.len() as u64)?;
        if let Some(levels) = triangular(cx, o, op, v, g, &region)? {
            return Ok(Some(Layer {
                inner: v,
                kind: Kind::Bijective,
                map: Map::Tri(Box::new(Tri {
                    op,
                    g,
                    region,
                    levels,
                })),
            }));
        }
    }
    Ok(None)
}

/// Evaluates the region of a triangular layer at `v = b`: the value of `g`.
fn eval_g(cx: &Context, t: &Tri, v: u32, b: &BitVec) -> Option<BitVec> {
    let mut vals: IdMap<u32, BitVec> = IdMap::default();
    vals.insert(v, *b);
    for &i in &t.region {
        let r = cx
            .eval_node(
                i,
                |j| {
                    vals.get(&j)
                        .copied()
                        .or_else(|| cx.const_val(j))
                        .unwrap_or(BitVec::zero(Width::W1))
                },
                |_, _| None,
            )
            .ok()?;
        vals.insert(i, r);
    }
    vals.get(&t.g).copied()
}

fn tri_apply(cx: &Context, t: &Tri, v: u32, b: &BitVec) -> Option<BitVec> {
    let g = eval_g(cx, t, v, b)?;
    let bin = |op, x: &BitVec, y: &BitVec| BitVec::bin_unchecked(op, x, y);
    Some(match t.op {
        TriOp::Xor => bin(BinOp::Xor, b, &g),
        TriOp::Add => bin(BinOp::Add, b, &g),
        TriOp::Sub => bin(BinOp::Sub, b, &g),
        TriOp::SubFrom => bin(BinOp::Sub, &g, b),
    })
}

/// The `v` with `v ⊙ g(v) = c`, checked by evaluation.
fn tri_solve<O: Oracle>(
    cx: &Context,
    o: &mut O,
    t: &Tri,
    v: u32,
    c: &BitVec,
) -> Result<Option<BitVec>, O::Err> {
    let w = c.width();
    let region = t.region.len() as u64;
    let mut b = BitVec::zero(w);
    let or = |x: &BitVec, m: &BitVec| BitVec::bin_unchecked(BinOp::Or, x, m);
    if t.op == TriOp::Xor {
        for &level in &t.levels {
            o.charge(region)?;
            let Some(g) = eval_g(cx, t, v, &b) else {
                return Ok(None);
            };
            let m = BitVec::wrapping_from_u128(w, level);
            let bits = BitVec::bin_unchecked(BinOp::Xor, c, &g);
            b = or(&b, &BitVec::bin_unchecked(BinOp::And, &bits, &m));
        }
    } else {
        // Bit `i` of the result is bit `i` of `v` flipped by lower bits only.
        for i in 0..w.bits() {
            o.charge(region)?;
            let Some(r) = tri_apply(cx, t, v, &b) else {
                return Ok(None);
            };
            if r.bit(i) != c.bit(i) {
                let m = BitVec::bin_unchecked(
                    BinOp::Shl,
                    &BitVec::one(w),
                    &BitVec::wrapping_from_u64(w, u64::from(i)),
                );
                b = or(&b, &m);
            }
        }
    }
    o.charge(region)?;
    Ok((tri_apply(cx, t, v, &b).as_ref() == Some(c)).then_some(b))
}

/// The preimage of `c` under layer `l` at the top of `n`: `Some(Some(v))` if exactly `v`
/// maps to `c`, `Some(None)` if nothing does, `None` if it could not be computed.
pub(crate) fn preimage<O: Oracle>(
    cx: &Context,
    o: &mut O,
    n: u32,
    l: &Layer,
    c: &BitVec,
) -> Result<Option<Option<BitVec>>, O::Err> {
    let k = |p: u32| cx.const_val(p);
    let bin = |op, x: &BitVec, y: &BitVec| BitVec::bin_unchecked(op, x, y);
    let wi = cx.width_of(l.inner);
    let exact = |v: BitVec| Some(Some(v));
    Ok(match &l.map {
        Map::Un(op) => exact(BitVec::un_unchecked(*op, c)),
        Map::Add(p) => k(*p).and_then(|p| exact(bin(BinOp::Sub, c, &p))),
        Map::Sub(p) => k(*p).and_then(|p| exact(bin(BinOp::Add, c, &p))),
        Map::SubFrom(p) => k(*p).and_then(|p| exact(bin(BinOp::Sub, &p, c))),
        Map::Xor(p) => k(*p).and_then(|p| exact(bin(BinOp::Xor, c, &p))),
        Map::Mul(p) => k(*p)
            .and_then(|p| mul_inverse(&p))
            .and_then(|i| exact(bin(BinOp::Mul, c, &i))),
        Map::RotL(p) => k(*p).and_then(|p| exact(bin(BinOp::RotR, c, &p))),
        Map::RotR(p) => k(*p).and_then(|p| exact(bin(BinOp::RotL, c, &p))),
        Map::Zext | Map::Sext => (|| {
            let t = c.trunc(wi).ok()?;
            let back = if matches!(l.map, Map::Zext) {
                t.zext(c.width()).ok()?
            } else {
                t.sext(c.width()).ok()?
            };
            Some((back == *c).then_some(t))
        })(),
        Map::ConcatHi(p) => k(*p).and_then(|p| {
            let wl = p.width();
            let (hi, lo) = (c.extract(wl.bits(), wi).ok()?, c.trunc(wl).ok()?);
            Some((lo == p).then_some(hi))
        }),
        Map::ConcatLo(p) => k(*p).and_then(|p| {
            let (hi, lo) = (c.extract(wi.bits(), p.width()).ok()?, c.trunc(wi).ok()?);
            Some((hi == p).then_some(lo))
        }),
        Map::Ext { output, arg } => {
            let node = cx.node(n);
            let Some(op) = cx.registry.as_deref().and_then(|r| r.op_at(node.aux)) else {
                return Ok(None);
            };
            let mut args: Vec<BitVec> = Vec::new();
            for (p, a) in node.children().enumerate() {
                args.push(if p == usize::from(*arg) {
                    BitVec::zero(cx.width_of(a))
                } else {
                    match k(a) {
                        Some(v) => v,
                        None => return Ok(None),
                    }
                });
            }
            match op.invert(*output, *arg, &args, c) {
                // Checked by evaluation: a wrong answer from the operation is never used.
                Some(v) if v.width() == wi => {
                    args[usize::from(*arg)] = v;
                    let out = crate::ext::run_eval(op, &args).ok();
                    let hit = out.and_then(|o| o.get(usize::from(*output)).copied()) == Some(*c);
                    hit.then_some(Some(v))
                }
                Some(_) => None,
                // Nothing maps to `c`: the operation's word for an injection; a bijection
                // that says so breaks its contract, so nothing is concluded.
                None if l.kind == Kind::Injective => Some(None),
                None => None,
            }
        }
        Map::Tri(t) => tri_solve(cx, o, t, l.inner, c)?.map(Some),
    })
}

/// The result of solving `e == c` through `e`'s layers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Solved {
    /// `e == c` holds exactly when `x == v`.
    Eq(u32, BitVec),
    /// `e == c` is this constant.
    Const(bool),
}

/// Solves `e == c` through as many layers of `e` with constant parameters as possible; `None`
/// if not even one could be undone.
pub(crate) fn solve_eq<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    e: u32,
    c: &BitVec,
) -> Result<Option<Solved>, O::Err> {
    let (mut cur, mut val) = (e, *c);
    let mut peeled = false;
    loop {
        o.charge(1)?;
        let Some(l) = solve_layer(cx, o, cur)? else {
            break;
        };
        match preimage(cx, o, cur, &l, &val)? {
            None => break,
            Some(None) => return Ok(Some(Solved::Const(false))),
            Some(Some(v)) => {
                (cur, val) = (l.inner, v);
                peeled = true;
            }
        }
    }
    Ok(peeled.then_some(Solved::Eq(cur, val)))
}

// ----- cancelling on both sides (R1) --------------------------------------------------------------

/// If `n1` and `n2` are one injective layer applied to different operands, those operands:
/// `n1 == n2` holds exactly when they are equal.
pub(crate) fn cancel_layer<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    n1: u32,
    n2: u32,
) -> Result<Option<(u32, u32)>, O::Err> {
    let (a, b) = (cx.node(n1), cx.node(n2));
    if a.op != b.op || a.width != b.width || a.aux != b.aux || n1 == n2 {
        return Ok(None);
    }
    let (ka, kb): (Vec<u32>, Vec<u32>) = (a.children().collect(), b.children().collect());
    if ka.len() != kb.len() || ka.is_empty() {
        return Ok(None);
    }
    // Pairings of positions: the direct one, and for a commutative operator the swapped one.
    let swappable = a.op.as_bin().is_some_and(BinOp::is_commutative)
        || (a.op.as_ext().is_some()
            && ka.len() >= 2
            && cx
                .registry
                .as_deref()
                .and_then(|r| r.op_at(a.aux))
                .is_some_and(|op| op.traits().commutative));
    let mut pairings = vec![(0..ka.len()).collect::<Vec<usize>>()];
    if swappable {
        let mut s: Vec<usize> = (0..ka.len()).collect();
        s.swap(0, 1);
        pairings.push(s);
    }
    for pairing in &pairings {
        // Positions where the operands differ (the rest must be shared parameters).
        let diff: Vec<usize> = (0..ka.len()).filter(|&p| ka[p] != kb[pairing[p]]).collect();
        let [p] = diff[..] else {
            continue;
        };
        let (x, y) = (ka[p], kb[pairing[p]]);
        if cx.wid(x) != cx.wid(y) {
            continue;
        }
        if let Some((_, _, cond)) = primitive(cx, n1, p) {
            if let Some(k) = cond
                && !odd(cx, o, k)?
            {
                continue;
            }
            // A primitive layer's map depends only on the operator and the shared operands;
            // for a swapped pairing the operator is commutative, so the map is the same.
            return Ok(Some((x, y)));
        }
        if a.op.as_ext().is_some() && pairing[p] == p && ext_kind(cx, o, n1, p)?.is_some() {
            return Ok(Some((x, y)));
        }
    }
    // Both operands differ: triangular layers `v1 ⊙ g1` and `v2 ⊙ g2` with `g1`, `g2` one
    // function of `v1`, `v2`.
    let (fa, fb) = (tri_forms(cx, n1), tri_forms(cx, n2));
    for &(v1, g1, op1) in &fa {
        for &(v2, g2, op2) in &fb {
            if op1 != op2 || v1 == v2 || g1 == g2 || cx.const_val(g1).is_some() {
                continue;
            }
            let (region, steps) = match_region(cx, g1, g2, v1, v2);
            o.charge(u64::from(steps))?;
            let Some(region) = region else {
                continue;
            };
            if triangular(cx, o, op1, v1, g1, &region)?.is_some() {
                return Ok(Some((v1, v2)));
            }
        }
    }
    Ok(None)
}

// ----- chains (queries) ---------------------------------------------------------------------------

/// How `e` depends on a subexpression `x`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Chain {
    /// `e` does not depend on `x` at all.
    Independent,
    /// `e` is a chain of layers down to `x`: injective (or bijective) in `x`.
    Proved(Kind),
    /// Not decided.
    Unknown,
}

/// The most nodes of `e` a chain query examines.
const MAX_CHAIN_NODES: usize = 1 << 16;

/// How `e` depends on its subexpression `x`, every value not depending on `x` fixed.
pub(crate) fn chain<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    e: u32,
    x: u32,
) -> Result<Chain, O::Err> {
    if e == x {
        return Ok(Chain::Proved(Kind::Bijective));
    }
    // Which nodes below `e` reach `x`: descending indices list users before operands, so one
    // pass over the ascending order decides every node from its operands.
    let mut below: Vec<u32> = Vec::new();
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack = vec![e];
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        below.push(i);
        if below.len() > MAX_CHAIN_NODES {
            return Ok(Chain::Unknown);
        }
        if i != x {
            stack.extend(cx.node(i).children());
        }
    }
    o.charge(below.len() as u64)?;
    below.sort_unstable();
    let mut reach: IdMap<u32, ()> = IdMap::default();
    for &i in &below {
        if i == x || cx.node(i).children().any(|c| reach.contains_key(&c)) {
            reach.insert(i, ());
        }
    }
    if !reach.contains_key(&e) {
        return Ok(Chain::Independent);
    }
    let mut kind = Kind::Bijective;
    let mut cur = e;
    while cur != x {
        o.charge(1)?;
        let Some((next, k)) = chain_layer(cx, o, cur, x, &reach)? else {
            return Ok(Chain::Unknown);
        };
        kind = kind.min(k);
        cur = next;
    }
    Ok(Chain::Proved(kind))
}

/// The layer at `n` whose inner operand reaches `x` and whose parameters do not.
fn chain_layer<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    n: u32,
    x: u32,
    reach: &IdMap<u32, ()>,
) -> Result<Option<(u32, Kind)>, O::Err> {
    let node = cx.node(n);
    let kids: Vec<u32> = node.children().collect();
    let open: Vec<usize> = (0..kids.len())
        .filter(|&p| reach.contains_key(&kids[p]))
        .collect();
    if let [pos] = open[..] {
        if let Some((_, kind, cond)) = primitive(cx, n, pos) {
            if let Some(k) = cond
                && !odd(cx, o, k)?
            {
                return Ok(None);
            }
            return Ok(Some((kids[pos], kind)));
        }
        if node.op.as_ext().is_some()
            && let Some(kind) = ext_kind(cx, o, n, pos)?
        {
            return Ok(Some((kids[pos], kind)));
        }
        return Ok(None);
    }
    if open.len() != 2 {
        return Ok(None);
    }
    for (v, g, op) in tri_forms(cx, n) {
        // `g` must depend on `x` only through `v`.
        let mut seen: IdMap<u32, ()> = IdMap::default();
        let mut region = Vec::new();
        let mut stack = vec![g];
        let mut ok = true;
        while let Some(i) = stack.pop() {
            if i == v || !reach.contains_key(&i) || seen.insert(i, ()).is_some() {
                continue;
            }
            if i == x || region.len() >= MAX_REGION {
                ok = false;
                break;
            }
            region.push(i);
            stack.extend(cx.node(i).children());
        }
        o.charge(1 + region.len() as u64)?;
        if !ok {
            continue;
        }
        region.sort_unstable();
        if triangular(cx, o, op, v, g, &region)?.is_some() {
            return Ok(Some((v, Kind::Bijective)));
        }
    }
    Ok(None)
}

// ----- queries ------------------------------------------------------------------------------------

/// Facts for a query: the base facts, or facts under assumptions (collecting what they rely
/// on). Queries have no budget; the analysis is bounded by its own caps.
struct Queries<'a> {
    a: Option<&'a Assumptions>,
    rel: Reliance,
}

impl Oracle for Queries<'_> {
    type Err = Error;

    fn facts(&mut self, cx: &mut Context, i: u32) -> Result<Option<Facts>, Error> {
        let e = cx.handle(i);
        let Some(a) = self.a else {
            return Ok(Some(cx.facts(e)?));
        };
        let cap = cx.config().fact_work;
        Ok(match cx.facts_under_cap(e, a, cap)? {
            Ok((f, r)) => {
                self.rel |= r;
                Some(f)
            }
            Err(_) => None,
        })
    }

    fn charge(&mut self, _units: u64) -> Result<(), Error> {
        Ok(())
    }
}

/// Answers [`Query::Injective`] (`onto` false) and [`Query::Bijective`] (`onto` true).
///
/// [`Query::Injective`]: crate::Query::Injective
/// [`Query::Bijective`]: crate::Query::Bijective
pub(crate) fn prove(
    cx: &mut Context,
    e: Expr,
    of: Expr,
    onto: bool,
    a: Option<&Assumptions>,
) -> Result<Proof, Error> {
    let answer = |truth, relies_on| Proof { truth, relies_on };
    let (ei, xi) = (cx.id(e)?, cx.id(of)?);
    if let Some(a) = a {
        a.check_context(cx)?;
        // Infeasible assumptions prove anything.
        let cap = cx.config().fact_work;
        if let Err(r) = cx.facts_under_cap(e, a, cap)? {
            return Ok(answer(Truth::True, r));
        }
    }
    let (we, wx) = (cx.wid(ei), cx.wid(xi));
    if we < wx || (onto && we != wx) {
        return Ok(answer(Truth::False, Reliance::NONE));
    }
    let mut o = Queries {
        a,
        rel: Reliance::NONE,
    };
    Ok(match chain(cx, &mut o, ei, xi)? {
        // A function of nothing it varies: every value of `of` gives the same `e`.
        Chain::Independent => answer(Truth::False, Reliance::NONE),
        // Injective between sets of one size is bijective.
        Chain::Proved(_) => answer(Truth::True, o.rel),
        Chain::Unknown => answer(Truth::Unknown, Reliance::NONE),
    })
}
