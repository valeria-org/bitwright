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
//! | a *region* of nodes whose value fixes the hole bit by bit (below) | injective | recovered bit by bit |
//!
//! Composing layers keeps injectivity (and bijectivity), so a chain of layers is injective in
//! its inner value; nothing else is ever claimed.
//!
//! **Regions.** Combining two values that both depend on the inner one generally destroys
//! invertibility: `f(x) ^ x`, `f_a(x) ^ f_b(x)` and `f_a(x) | f_b(x)` are not injective even for
//! bijective `f`. Such a node is a layer only when a *pivot analysis* proves it. Over the region
//! between the node and its *hole* (a node every varying path goes through), it tracks for every
//! bit `k` of every node `D_k`, the hole bits it can depend on, and its *pivots*: the hole bits
//! `j` with bit `k = hole_j ^ φ(D_k \ {j})`, flipped by `hole_j` whatever the others are (bit `k`
//! of `x ^ (x >> 4)` has two). The hole's bits are their own pivots; `~` keeps them, and `^` keeps
//! the pivots of each operand that the other does not read; `+`, `-` and negation keep those no
//! carry from the bits below reads either; a product with a factor that does not vary, with `t`
//! low bits known zero and the next known one, moves them up by `t`; `&` and `|` pass an
//! operand's bit through where the other's is known to be 1 (resp. 0); shifts and rotations by
//! constants, casts and `concat` re-index; a select by a condition that does not vary keeps the
//! pivots both arms share; a bit the facts pin depends on nothing. The facts are computed afresh
//! with the hole unknown, so all of this holds for every value of the hole, not just the values
//! it takes in context.
//!
//! The region is injective when every hole bit can be *recovered*: it is the one dependency of an
//! output bit not recovered before, and one of that bit's pivots (so, by induction, two values of
//! the hole with one image agree on every bit). A preimage is recovered the same way, level by
//! level, by evaluating the region, and then checked: a value that does not check proves that
//! nothing maps to the constant. This covers the xorshift involution
//! `h ^ ((h >>u 32) >>u (h >>u 60))`, xorshift steps, T-functions such as
//! `u - (((u << 1) | b) & h)` (refusing `u - ((u | b) & h)`, whose bit `i` reads bit `i`), and
//! block-triangular maps, such as a pointer encoding whose low bits are a bijection of the low
//! bits and whose high bits, given those, are one of the high bits.
//!
//! The nearest dominator is tried first, then deeper ones: one big region is not compositional
//! (a multiplication mixes every bit below, so `S((x ^ k) * k)` is proved over `(x ^ k) * k`, not
//! over `x`). For `f(a) == f(b)` the sides are anti-unified first: one function of a pair of
//! different subterms, found as deep as the structure allows. At most [`MAX_REGION`] nodes, and
//! holes of at most 128 bits, are examined.
//!
//! [`ExtOp::invert`]: crate::ext::ExtOp::invert

pub(crate) mod gf2;
#[cfg(test)]
mod tests;

use crate::error::Error;
use crate::expr::{Context, Expr, OpCode, count_mod};
use crate::ext::Invertible;
use crate::facts::{Assumptions, Facts, KnownBits, Proof, Reliance, Truth};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// The most nodes of a region examined.
pub(crate) const MAX_REGION: usize = 256;
/// The most dominators tried as a region's hole.
const MAX_CANDIDATES: usize = 8;
/// The most node pairs examined when anti-unifying two sides.
const MAX_MATCH: u32 = 1024;
/// The deepest the anti-unification recursion goes.
const MAX_MATCH_DEPTH: u32 = 256;
/// The widest hole of a region (dependencies are 128-bit masks).
const MAX_HOLE_BITS: u16 = 128;
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
    /// A region of several nodes, injective by the pivot analysis.
    Region(Box<Region>),
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

/// A recovery plan: per level, the hole bits recovered together, each with the output bit it
/// flips.
type Plan = Vec<Vec<(u8, u16)>>;

/// A layer of several nodes: the node is a function of the hole (the layer's inner value)
/// computed by `nodes`, and injective because every bit of the hole can be recovered from the
/// node's value.
#[derive(Clone, Debug)]
pub(crate) struct Region {
    /// The nodes between the hole and the node, ascending (the node last).
    nodes: Vec<u32>,
    /// How the hole's bits are recovered.
    how: How,
}

/// How a region's hole is recovered from its value.
#[derive(Clone, Debug)]
pub(crate) enum How {
    /// Bit by bit, level by level (the pivot analysis).
    Levels(Plan),
    /// By elimination: the region is affine over GF(2) with a matrix of full column rank,
    /// these its rows (per output bit, the hole bits it is the xor of).
    Linear(gf2::Rows),
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

// ----- regions ----------------------------------------------------------------------------------

/// Per bit of a node: the bits of the hole it can depend on (`dep`), and its *pivots* (`piv`,
/// among them): the hole bits `j` such that the bit is `hole_j ^ φ`, with `φ` a function of its
/// other dependencies only. An output bit can have several (`x_k ^ x_{k+4}` has two), and each
/// one alone satisfies that.
#[derive(Clone, Debug)]
struct Bits {
    dep: Vec<u128>,
    piv: Vec<u128>,
}

impl Bits {
    fn opaque(dep: Vec<u128>) -> Bits {
        let piv = vec![0; dep.len()];
        Bits { dep, piv }
    }

    fn all(&self) -> u128 {
        all(&self.dep)
    }
}

fn all(d: &[u128]) -> u128 {
    d.iter().fold(0, |a, x| a | x)
}

/// The counts a shift or rotation of width `w` by a count with facts `f` acts as: `n` in a row
/// from `first`. A shift acts the same for every count of `w` or more (as `w`), so `n <= w + 1`;
/// a rotation acts as its count modulo `w`, so `first < w` and `n <= w`.
fn count_span(op: OpCode, f: &Facts, w: usize) -> (u64, u64) {
    let (lo, hi) = (f.urange().lo(), f.urange().hi());
    let wu = w as u64;
    if matches!(op, OpCode::RotL | OpCode::RotR) {
        let span = BitVec::bin_unchecked(BinOp::Sub, &hi, &lo).to_u64();
        let n = span.map_or(wu, |s| s.saturating_add(1).min(wu));
        (count_mod(&lo, w as u16), n)
    } else {
        let cap = |v: BitVec| v.to_u64().map_or(wu, |v| v.min(wu));
        let (first, last) = (cap(lo), cap(hi));
        (first, last - first + 1)
    }
}

/// Dependencies of a shift or rotation of `a` by a count whose facts are `cf` and whose own
/// dependencies are `cd` (all zero for a parameter).
fn shift_deps(op: OpCode, a: &[u128], cf: &Facts, cd: u128) -> Vec<u128> {
    let w = a.len();
    let wu = w as u64;
    let (first, n) = count_span(op, cf, w);
    let mut out = vec![cd; w];
    match op {
        OpCode::RotL | OpCode::RotR => {
            if n == wu {
                let x = all(a) | cd;
                out.iter_mut().for_each(|o| *o = x);
                return out;
            }
            for t in first..first + n {
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
            for t in first..first + n {
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

/// An operation whose bit `k` is `a_k ^ c_k` (or `a_k` alone) flipped by a carry from the bits
/// below: `+`, `-` (`a + ~c + 1`), negation (`~a + 1`), and a product with an odd factor `c`
/// that does not vary (`a_k * c_0` plus terms of lower bits).
fn carry_chain(a: &Bits, c: Option<&Bits>) -> Bits {
    let w = a.dep.len();
    let mut out = Bits::opaque(vec![0; w]);
    let mut low = 0u128;
    for k in 0..w {
        let (da, pa) = (a.dep[k], a.piv[k]);
        let (dc, pc) = c.map_or((0, 0), |c| (c.dep[k], c.piv[k]));
        out.dep[k] = low | da | dc;
        // A pivot of one side that neither the other side nor the carry reads.
        out.piv[k] = (pa & !(low | dc)) | (pc & !(low | da));
        low |= da | dc;
    }
    out
}

/// The bits of node `i` from its operands' (`b`) and facts (`f`).
fn node_bits(cx: &Context, i: u32, b: &IdMap<u32, Bits>, f: &IdMap<u32, Facts>) -> Bits {
    let n = cx.node(i);
    let w = usize::from(n.width);
    // Bit `k` is bit `src(k)` of `a` (a constant where there is none).
    let pick = |a: u32, src: &dyn Fn(usize) -> Option<usize>| {
        let ba = &b[&a];
        let mut out = Bits::opaque(vec![0; w]);
        for k in 0..w {
            if let Some(s) = src(k) {
                out.dep[k] = ba.dep[s];
                out.piv[k] = ba.piv[s];
            }
        }
        out
    };
    let known = |c: u32, k: usize| f[&c].known().bit(k as u16);
    match n.op {
        OpCode::Const | OpCode::Sym => Bits::opaque(vec![0; w]),
        OpCode::Not => b[&n.a].clone(),
        OpCode::Neg => carry_chain(&b[&n.a], None),
        OpCode::Add | OpCode::Sub => carry_chain(&b[&n.a], Some(&b[&n.b])),
        OpCode::Mul => {
            // With a factor `m` that does not vary and has `t` low bits known zero, the product
            // is `(y * (m >> t)) << t`: bit `k` reads `y`'s bits up to `k - t`, and when
            // `m >> t` is odd, it is `y_(k-t)` flipped by lower bits.
            let fixed = |m: u32| b[&m].all() == 0;
            let (y, m) = if fixed(n.b) { (n.a, n.b) } else { (n.b, n.a) };
            if !fixed(m) {
                let mut out = carry_chain(&b[&n.a], Some(&b[&n.b]));
                out.piv.iter_mut().for_each(|p| *p = 0);
                return out;
            }
            let t = f[&m].known().trailing_known_zeros() as usize;
            let base = carry_chain(&b[&y], None);
            let mut out = Bits::opaque(vec![0; w]);
            for k in t..w {
                out.dep[k] = base.dep[k - t];
                out.piv[k] = base.piv[k - t];
            }
            if t >= w || known(m, t) != Some(true) {
                out.piv.iter_mut().for_each(|p| *p = 0);
            }
            out
        }
        OpCode::And | OpCode::Or | OpCode::Xor => {
            let (ba, bc) = (&b[&n.a], &b[&n.b]);
            let mut out = Bits::opaque(vec![0; w]);
            for k in 0..w {
                out.dep[k] = ba.dep[k] | bc.dep[k];
                // An operand's bit passes through when the other's is known to let it.
                let through = |x: u32| match n.op {
                    OpCode::And => known(x, k) == Some(true),
                    OpCode::Or => known(x, k) == Some(false),
                    _ => false,
                };
                let (pa, pc) = (ba.piv[k], bc.piv[k]);
                out.piv[k] = if n.op == OpCode::Xor {
                    (pa & !bc.dep[k]) | (pc & !ba.dep[k])
                } else if through(n.b) {
                    pa
                } else if through(n.a) {
                    pc
                } else {
                    0
                };
            }
            out
        }
        OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR => {
            let Some(v) = cx.const_val(n.b) else {
                let d = shift_deps(n.op, &b[&n.a].dep, &f[&n.b], b[&n.b].all());
                return Bits::opaque(d);
            };
            // The one count it acts as: at most `w` for a shift, below `w` for a rotation.
            let c = count_span(n.op, &Facts::constant(&v), w).0 as usize;
            match n.op {
                OpCode::Shl => pick(n.a, &|k| (c <= k).then(|| k - c)),
                OpCode::LShr => pick(n.a, &|k| (k + c < w).then(|| k + c)),
                OpCode::AShr => pick(n.a, &|k| Some((k + c).min(w - 1))),
                OpCode::RotL => pick(n.a, &|k| Some((k + w - c) % w)),
                _ => pick(n.a, &|k| Some((k + c) % w)),
            }
        }
        OpCode::Bswap => pick(n.a, &|k| Some((w / 8 - 1 - k / 8) * 8 + k % 8)),
        OpCode::BitRev => pick(n.a, &|k| Some(w - 1 - k)),
        OpCode::Zext => {
            let wa = usize::from(cx.wid(n.a));
            pick(n.a, &|k| (k < wa).then_some(k))
        }
        OpCode::Sext => {
            let wa = usize::from(cx.wid(n.a));
            pick(n.a, &|k| Some(k.min(wa - 1)))
        }
        OpCode::Extract => {
            let lo = n.b as usize;
            pick(n.a, &|k| Some(lo + k))
        }
        OpCode::Concat => {
            let (h, l) = (&b[&n.a], &b[&n.b]);
            let wl = l.dep.len();
            let mut out = Bits::opaque(vec![0; w]);
            for k in 0..w {
                let (x, s) = if k < wl { (l, k) } else { (h, k - wl) };
                out.dep[k] = x.dep[s];
                out.piv[k] = x.piv[s];
            }
            out
        }
        OpCode::Select => {
            // Either arm's bit, chosen by a condition that does not vary: flipped by the pivots
            // both arms share.
            let (c, t, e) = (&b[&n.a], &b[&n.b], &b[&n.c]);
            let cond = c.all();
            let mut out = Bits::opaque(vec![0; w]);
            for k in 0..w {
                out.dep[k] = cond | t.dep[k] | e.dep[k];
                if cond == 0 {
                    out.piv[k] = t.piv[k] & e.piv[k];
                }
            }
            out
        }
        // Every bit may read every bit of every operand: high products, divisions, counts,
        // comparisons, deposits and extractions, extension outputs.
        _ => Bits::opaque(vec![n.children().fold(0, |acc, c| acc | b[&c].all()); w]),
    }
}

/// Whether node `top` is an injective function of `hole`, computed by `nodes` (the nodes
/// between them, ascending, `top` last), every other operand met below them a parameter (a
/// constant, or facts from the oracle): the recovery plan if so. The facts used are computed
/// afresh over the region with the hole unknown, so the answer holds for every value of the
/// hole, not only the values it takes in context.
fn recover<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    top: u32,
    hole: u32,
    nodes: &[u32],
) -> Result<Option<How>, O::Err> {
    if let Some(plan) = recover_levels(cx, o, top, hole, nodes)? {
        return Ok(Some(How::Levels(plan)));
    }
    // An affine map over GF(2) whose rows span every hole bit.
    o.charge(nodes.len() as u64 * 4 + 1)?;
    let wv = u32::from(cx.wid(hole));
    if let Some(map) = gf2::rows(cx, hole, nodes)
        && let Some(r) = map.get(&top)
        && gf2::full_rank(r, wv)
    {
        return Ok(Some(How::Linear(r.clone())));
    }
    Ok(None)
}

/// [`recover`] by the pivot analysis.
fn recover_levels<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    top: u32,
    hole: u32,
    nodes: &[u32],
) -> Result<Option<Plan>, O::Err> {
    let wv = cx.wid(hole);
    if wv > MAX_HOLE_BITS || nodes.last() != Some(&top) {
        return Ok(None);
    }
    let wv = usize::from(wv);
    let mut bits: IdMap<u32, Bits> = IdMap::default();
    let mut facts: IdMap<u32, Facts> = IdMap::default();
    bits.insert(
        hole,
        Bits {
            dep: (0..wv).map(|k| 1u128 << k).collect(),
            piv: (0..wv).map(|k| 1u128 << k).collect(),
        },
    );
    facts.insert(hole, Facts::top(cx.width_of(hole)));
    for &i in nodes {
        let n = cx.node(i);
        // Parameters: constants, or whatever the oracle knows.
        for c in n.children() {
            if bits.contains_key(&c) {
                continue;
            }
            let f = match cx.const_val(c) {
                Some(k) => Facts::constant(&k),
                None => o
                    .facts(cx, c)?
                    .unwrap_or_else(|| Facts::top(cx.width_of(c))),
            };
            bits.insert(c, Bits::opaque(vec![0; usize::from(cx.wid(c))]));
            facts.insert(c, f);
        }
        // A variable shift reads, for every result bit, the source bit of every count it acts as.
        let counts = match n.op {
            OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR
                if cx.const_val(n.b).is_none() =>
            {
                count_span(n.op, &facts[&n.b], usize::from(n.width)).1
            }
            _ => 1,
        };
        o.charge(1 + u64::from(n.width) * counts)?;
        let kids: Vec<Facts> = n.children().map(|c| facts[&c]).collect();
        let refs: Vec<&Facts> = kids.iter().collect();
        let f = cx.transfer_local(i, &refs);
        let mut nb = node_bits(cx, i, &bits, &facts);
        // A bit the facts pin depends on nothing and flips with nothing.
        let known = f.known().known();
        for k in 0..nb.dep.len() {
            if known.bit(k as u16) == Some(true) {
                nb.dep[k] = 0;
                nb.piv[k] = 0;
            }
        }
        bits.insert(i, nb);
        facts.insert(i, f);
    }
    let t = &bits[&top];
    o.charge(t.dep.len() as u64 * wv as u64 / 16 + 1)?;
    Ok(levels(t, wv))
}

/// The recovery plan: per level, pairs (hole bit, output bit) such that the hole bit is the one
/// dependency of the output bit not recovered at an earlier level, and one of its pivots. `None`
/// if a hole bit is never recovered (injectivity is not proved). Recovering a bit only makes
/// more output bits usable, so this closure finds every bit that can be recovered.
fn levels(top: &Bits, wv: usize) -> Option<Plan> {
    let full = if wv >= 128 {
        u128::MAX
    } else {
        (1u128 << wv) - 1
    };
    let mut done = 0u128;
    let mut out = Vec::new();
    while done != full {
        let mut level = Vec::new();
        let mut got = 0u128;
        for (k, (&d, &p)) in top.dep.iter().zip(&top.piv).enumerate() {
            let open = d & !done;
            if open.count_ones() != 1 || p & open == 0 || got & open != 0 {
                continue;
            }
            level.push((open.trailing_zeros() as u8, k as u16));
            got |= open;
        }
        if level.is_empty() {
            return None;
        }
        done |= got;
        out.push(level);
    }
    Some(out)
}

/// The nodes below `top` that every path from `top` to a varying leaf passes through, nearest
/// first: at most [`MAX_CANDIDATES`], after looking at no more than [`MAX_REGION`] nodes; and
/// how many were looked at. Varying operands are visited in descending index order (every
/// operand has a lower index than its users), so a node alone in the frontier when it is
/// reached dominates everything still below.
fn dominators(cx: &Context, top: u32, varies: &dyn Fn(u32) -> bool) -> (Vec<u32>, u64) {
    let mut heap = std::collections::BinaryHeap::new();
    let mut seen: IdMap<u32, ()> = IdMap::default();
    for c in cx.node(top).children() {
        if varies(c) && seen.insert(c, ()).is_none() {
            heap.push(c);
        }
    }
    let mut out = Vec::new();
    let mut looked = 0u64;
    while let Some(i) = heap.pop() {
        looked += 1;
        if heap.is_empty() {
            out.push(i);
            if out.len() >= MAX_CANDIDATES {
                break;
            }
        }
        if looked as usize > MAX_REGION {
            break;
        }
        for c in cx.node(i).children() {
            if varies(c) && seen.insert(c, ()).is_none() {
                heap.push(c);
            }
        }
    }
    (out, looked)
}

/// The varying nodes reachable from `top` without passing `hole` (the ones a region of `top`
/// over `hole` computes), ascending; `None` if there are more than [`MAX_REGION`] or one of them
/// is a leaf (a varying value that does not go through `hole`).
fn between(cx: &Context, top: u32, hole: u32, varies: &dyn Fn(u32) -> bool) -> Option<Vec<u32>> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut out = Vec::new();
    let mut stack = vec![top];
    while let Some(i) = stack.pop() {
        if i == hole || seen.insert(i, ()).is_some() || (i != top && !varies(i)) {
            continue;
        }
        let n = cx.node(i);
        if n.op.arity() == 0 || out.len() >= MAX_REGION {
            return None;
        }
        out.push(i);
        stack.extend(n.children());
    }
    out.sort_unstable();
    Some(out)
}

/// Candidate regions of `top`: each dominator (nearest first) with the nodes between; and the
/// work spent finding them.
fn candidates(cx: &Context, top: u32, varies: &dyn Fn(u32) -> bool) -> (Vec<(u32, Vec<u32>)>, u64) {
    let (doms, looked) = dominators(cx, top, varies);
    let out: Vec<(u32, Vec<u32>)> = doms
        .into_iter()
        .filter(|&d| cx.wid(d) <= MAX_HOLE_BITS)
        .filter_map(|d| between(cx, top, d, varies).map(|r| (d, r)))
        .collect();
    let work = looked + out.iter().map(|(_, r)| r.len() as u64).sum::<u64>();
    (out, work)
}

/// A step of undoing a partial match.
enum Undo {
    Bind(u32),
    Hole,
}

/// Anti-unification of two expressions: one function `G` with `n1 = G[v1]` and `n2 = G[v2]`,
/// equal structure except at one pair of different subterms `(v1, v2)`, the *hole*, taken as
/// deep as the structure allows; the subterms both sides share are parameters of `G`.
struct AntiUnify<'c> {
    cx: &'c Context,
    hole: Option<(u32, u32)>,
    /// Each node of side one and its partner on side two.
    map: IdMap<u32, u32>,
    trail: Vec<Undo>,
    steps: u32,
    depth: u32,
}

impl AntiUnify<'_> {
    fn bind(&mut self, x1: u32, x2: u32) {
        self.map.insert(x1, x2);
        self.trail.push(Undo::Bind(x1));
    }

    fn undo(&mut self, to: usize) {
        while self.trail.len() > to {
            match self.trail.pop() {
                Some(Undo::Bind(x)) => {
                    self.map.remove(&x);
                }
                Some(Undo::Hole) => self.hole = None,
                None => {}
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
        if x1 == x2 {
            self.bind(x1, x2);
            return true;
        }
        if let Some((_, h2)) = self.hole {
            // The hole's own pair is in the map; its second node pairs with nothing else.
            return x2 != h2 && self.descend(x1, x2);
        }
        // No hole yet: as deep as the structure allows, else this pair.
        let mark = self.trail.len();
        if self.descend(x1, x2) {
            return true;
        }
        self.undo(mark);
        if self.cx.wid(x1) != self.cx.wid(x2) {
            return false;
        }
        self.hole = Some((x1, x2));
        self.trail.push(Undo::Hole);
        self.bind(x1, x2);
        true
    }

    fn descend(&mut self, x1: u32, x2: u32) -> bool {
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

/// Two sides anti-unified: the hole on side one (`v1`, its partner is `map[v1]`) and each node
/// of side one with its partner on side two.
struct Unified {
    v1: u32,
    map: IdMap<u32, u32>,
}

/// `n1` and `n2` anti-unified, if they are one function of two different subterms; and the
/// steps spent.
fn anti_unify(cx: &Context, n1: u32, n2: u32) -> (Option<Unified>, u32) {
    let mut m = AntiUnify {
        cx,
        hole: None,
        map: IdMap::default(),
        trail: Vec::new(),
        steps: 0,
        depth: 0,
    };
    let ok = m.go(n1, n2);
    let steps = m.steps;
    match (ok, m.hole) {
        (true, Some((v1, _))) => (Some(Unified { v1, map: m.map }), steps),
        _ => (None, steps),
    }
}

/// The value of the last of `nodes` with the hole at `x` (every other operand a constant).
pub(crate) fn eval_region(cx: &Context, nodes: &[u32], hole: u32, x: &BitVec) -> Option<BitVec> {
    let mut vals: IdMap<u32, BitVec> = IdMap::default();
    vals.insert(hole, *x);
    for &i in nodes {
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
    nodes.last().and_then(|t| vals.get(t)).copied()
}

/// The preimage of `c` under a region, recovered as its plan says and then checked. A value
/// that does not check proves that nothing maps to `c`: any preimage would be the one recovered.
fn region_solve<O: Oracle>(
    cx: &Context,
    o: &mut O,
    r: &Region,
    hole: u32,
    c: &BitVec,
) -> Result<Option<Option<BitVec>>, O::Err> {
    let w = cx.width_of(hole);
    let cost = r.nodes.len() as u64;
    let levels = match &r.how {
        How::Levels(l) => l,
        How::Linear(rows) => {
            // x = M⁻¹·(c ⊕ f(0)): the map is affine, f(x) = M·x ⊕ f(0).
            o.charge(cost + rows.len() as u64)?;
            let Some(f0) = eval_region(cx, &r.nodes, hole, &BitVec::zero(w)) else {
                return Ok(None);
            };
            let y: Vec<bool> = (0..rows.len() as u16)
                .map(|k| c.bit(k) != f0.bit(k))
                .collect();
            let x = match gf2::solve(rows, &y, u32::from(w.bits())) {
                Some(Some(x)) => BitVec::wrapping_from_limbs(w, &[x as u64, (x >> 64) as u64]),
                Some(None) => return Ok(Some(None)),
                None => return Ok(None),
            };
            let Some(back) = eval_region(cx, &r.nodes, hole, &x) else {
                return Ok(None);
            };
            return Ok(Some((back == *c).then_some(x)));
        }
    };
    let mut x = BitVec::zero(w);
    for level in levels {
        o.charge(cost)?;
        let Some(y) = eval_region(cx, &r.nodes, hole, &x) else {
            return Ok(None);
        };
        for &(j, k) in level {
            if y.bit(k) != c.bit(k) {
                let m = BitVec::bin_unchecked(
                    BinOp::Shl,
                    &BitVec::one(w),
                    &BitVec::wrapping_from_u64(w, u64::from(j)),
                );
                x = BitVec::bin_unchecked(BinOp::Or, &x, &m);
            }
        }
    }
    o.charge(cost)?;
    let Some(y) = eval_region(cx, &r.nodes, hole, &x) else {
        return Ok(None);
    };
    Ok(Some((y == *c).then_some(x)))
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
    }
    if open.is_empty() {
        return Ok(None);
    }
    // A region over the nearest node every varying path goes through, or a deeper one.
    let (cands, work) = candidates(cx, n, &|c| cx.const_val(c).is_none());
    o.charge(work)?;
    for (d, nodes) in cands {
        if let Some(how) = recover(cx, o, n, d, &nodes)? {
            let kind = if cx.wid(n) == cx.wid(d) {
                Kind::Bijective
            } else {
                Kind::Injective
            };
            return Ok(Some(Layer {
                inner: d,
                kind,
                map: Map::Region(Box::new(Region { nodes, how })),
            }));
        }
    }
    Ok(None)
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
        Map::Region(r) => region_solve(cx, o, r, l.inner, c)?,
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
    // Otherwise the deepest pair of different subterms the sides are one function of, and the
    // nearest node above it (on side one) every path to it passes through: a region.
    let (found, steps) = anti_unify(cx, n1, n2);
    o.charge(u64::from(steps))?;
    let Some(Unified { v1, map }) = found else {
        return Ok(None);
    };
    let (cands, work) = candidates(cx, n1, &|c| c == v1 || map.get(&c).is_some_and(|&p| p != c));
    o.charge(work)?;
    for (d1, nodes) in cands {
        let Some(&d2) = map.get(&d1) else {
            continue;
        };
        if cx.wid(d1) == cx.wid(d2) && recover(cx, o, n1, d1, &nodes)?.is_some() {
            return Ok(Some((d1, d2)));
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
        let Some((next, k)) = chain_layer(cx, o, cur, &reach)? else {
            return Ok(Chain::Unknown);
        };
        kind = kind.min(k);
        cur = next;
    }
    Ok(Chain::Proved(kind))
}

/// The layer at `n` whose inner value reaches the chain's end (`reach`) and whose parameters
/// do not.
fn chain_layer<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    n: u32,
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
    }
    let (cands, work) = candidates(cx, n, &|c| reach.contains_key(&c));
    o.charge(work)?;
    for (d, nodes) in cands {
        if recover(cx, o, n, d, &nodes)?.is_some() {
            let kind = if cx.wid(n) == cx.wid(d) {
                Kind::Bijective
            } else {
                Kind::Injective
            };
            return Ok(Some((d, kind)));
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
