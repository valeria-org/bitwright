//! Predicates decided by residues (called by the compares pass and `Context::prove`): the
//! opaque predicates of number theory, `x·x != 7·y·y − 1`, `x·(x + 1)` even, an odd square 1
//! modulo 8, a sum of three squares never 7 modulo 8, `x² + 1` never a multiple of 3, however
//! they are combined, and the tests of low bits they disguise.
//!
//! *Low bits.* The low `k` bits of `+ − · neg ~ & | ^`, of left shifts by constants and of
//! extensions depend only on the low `k` bits of the operands, so a choice of each leaf's value
//! modulo `2^k` (a *class*) fixes the low bits of every such term, and every bit of one a mask
//! or a narrow cast keeps within them; a signed remainder by `2^j` keeps the low `j` bits of its
//! dividend (and is 0 where they are). At a class the predicate is evaluated three-valued: a
//! comparison of two terms whose known low bits differ is false, one of two values known in
//! full is decided, anything else is unknown, and `&`, `|` and `select` decide over an unknown
//! operand when the other one decides alone. A class that decides does so for every value in
//! it; one that does not is split by the next bit of each leaf, as Hensel lifting splits a
//! solution modulo `2^k` into those modulo `2^(k+1)`. The predicate is a constant when no class
//! is left undecided and all decided alike: `x·x != 7·y·y − 1` is true because modulo 4 every
//! square is 0 or 1 and `7·y·y − 1` is 2 or 3. A leaf no wider than `k` is known in full, so a
//! predicate over a few narrow values is decided by exhausting them. And one over a single
//! value that its low bits alone decide is that test of them ([`residue_test`]): `(x·x & 7) ==
//! 1` is `x` odd.
//!
//! *Other moduli.* Where the intervals of the operands (from extensions, masks, remainders,
//! squares and constants) show that a sum, difference, product or left shift does not wrap
//! around, unsigned or signed, it is the integers' arithmetic, so residues modulo any `m` decide
//! the same way, every residue of each leaf at once: `urem(zext(a)·zext(a), 7) != 3`, as no
//! square is 3 modulo 7, and `srem(sext(c)·sext(c) + 1, 3) != 0` (a signed remainder of a
//! value that is never negative, or of a multiple, is the residue). A residue reads its value
//! as unsigned or, from a sign extension on, signed; a value never negative reads the same
//! both ways. The moduli tried are the divisors of the predicate's remainders, and 3, 5 and 7
//! for its equalities.
//!
//! Leaves are taken as independent, every combination of their classes, so a decision holds a
//! fortiori for the values they actually take. Each search is bounded, and is tried only where
//! it can conclude: on a predicate with a product of a value with itself (the source of these
//! laws, found by a look that allocates nothing), under an equality of terms whose low bits only
//! low bits decide, in a predicate a few low bits fix in full, or in a remainder of arithmetic
//! that does not wrap. Before any of it the predicate is evaluated at a few points, and a class
//! that stays undecided is tried as a value of its own: two different values end the search.

use super::{Runner, Stop};
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::value::narrow::{self, mask};

/// The most operations (leaves and constants included) a predicate's cone may have.
const MAX_OPS: usize = 48;

/// The most leaves.
const MAX_LEAVES: usize = 4;

/// The most undecided classes kept from one bit to the next.
const MAX_CLASSES: usize = 1024;

/// The most operations one search evaluates (classes times the program's length).
const MAX_WORK: u64 = 16_384;

/// The most bits of leaves enumerated to fix a predicate in full.
const EXHAUST_BITS: u32 = 12;

/// The most low bits of one value a predicate recovered as a test of them reads.
const RECOVER_BITS: u32 = 8;

/// The points the predicate is evaluated at first.
const SAMPLES: u64 = 8;

/// The largest modulus other than a power of two.
const MAX_MODULUS: u128 = 1024;

/// One operation of a predicate's cone; operands are indices of earlier operations.
#[derive(Clone, Copy, Debug)]
enum Op {
    Leaf(usize),
    Const(u128),
    Un(UnOp, usize),
    Bin(BinOp, usize, usize),
    Cmp(CmpOp, usize, usize),
    Zext(usize),
    Sext(usize),
    /// The operand and the lowest bit taken.
    Extract(usize, u16),
    /// The high and the low part.
    Concat(usize, usize),
    Select(usize, usize, usize),
}

/// A predicate's cone as a program over its leaves (in post-order, the predicate last).
struct Prog {
    ops: Vec<Op>,
    /// The width of each operation's result (at most 128).
    widths: Vec<u16>,
    /// The width of each leaf.
    leaves: Vec<u16>,
    /// The node of each leaf.
    leaf_ids: Vec<u32>,
    /// The leaves each operation depends on (bit `i`: leaf `i`).
    deps: Vec<u8>,
    /// Whether each operation's low bits are a function of the leaves' low bits, at every
    /// number of bits.
    closed: Vec<bool>,
    /// The fewest low bits of every leaf that fix each operation's value in full (at most the
    /// widest leaf's width: every value is fixed by every bit).
    fixed: Vec<u32>,
    /// Whether a product of two values that depend on one leaf is among the operations.
    square: bool,
}

/// What is known of a value at a class (or at a point).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum V {
    /// The value, in full.
    Exact(u128),
    /// Its low bits: `Low(r, b)`, the value is `r` modulo `2^b` (`0 < b <` its width).
    Low(u128, u32),
    /// Its residue modulo the modulus of the search (see [`eval_mod`]).
    Res(u128),
    Unknown,
}

/// Whether node `i` is an operation the programs interpret (its operands at most 128 bits).
fn interpreted(cx: &Context, i: u32) -> bool {
    let node = cx.node(i);
    let op = node.op;
    let ok = match op {
        OpCode::UMulHi | OpCode::SMulHi => node.width <= 64,
        OpCode::Zext | OpCode::Sext | OpCode::Extract | OpCode::Concat | OpCode::Select => true,
        _ => op.as_un().is_some() || op.as_bin().is_some() || op.as_cmp().is_some(),
    };
    ok && node.children().all(|c| cx.wid(c) <= 128)
}

/// A predicate to decide: a 1-bit node, or one `Context::prove` asks about without building it.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Pred {
    /// A 1-bit node.
    Node(u32),
    /// `a op b`.
    Cmp(CmpOp, u32, u32),
    /// `a != 0`.
    NonZero(u32),
    /// Bit `k` of `a`.
    Bit(u32, u16),
}

impl Pred {
    /// The nodes the predicate is built on.
    fn roots(self) -> ([u32; 2], usize) {
        match self {
            Pred::Node(a) | Pred::NonZero(a) | Pred::Bit(a, _) => ([a, a], 1),
            Pred::Cmp(_, a, b) => ([a, b], 2),
        }
    }
}

/// Whether the cones of `roots` (within [`MAX_OPS`] nodes) have a product of two values that
/// are not constants, which every search needs: a look that allocates nothing, before compiling.
fn has_product(cx: &Context, roots: &[u32]) -> bool {
    let mut seen = [0u32; MAX_OPS];
    let mut stack = [0u32; MAX_OPS];
    let (mut n, mut top) = (0, 0);
    for &r in roots {
        if !seen[..n].contains(&r) {
            (seen[n], stack[top]) = (r, r);
            n += 1;
            top += 1;
        }
    }
    while top > 0 {
        top -= 1;
        let i = stack[top];
        if cx.const_val(i).is_some() || !interpreted(cx, i) {
            continue;
        }
        let node = cx.node(i);
        if node.op == OpCode::Mul
            && cx.const_val(node.a).is_none()
            && cx.const_val(node.b).is_none()
        {
            return true;
        }
        for c in node.children() {
            if seen[..n].contains(&c) {
                continue;
            }
            if n == MAX_OPS {
                return false;
            }
            (seen[n], stack[top]) = (c, c);
            n += 1;
            top += 1;
        }
    }
    false
}

/// The number of bits up to the highest set bit of `c`.
fn bit_len(c: u128) -> u32 {
    128 - c.leading_zeros()
}

/// Compiles the cones of the predicate's nodes and the predicate on them, or `None` past the
/// caps.
fn compile(cx: &Context, pred: Pred) -> Option<Prog> {
    let mut p = Prog {
        ops: Vec::new(),
        widths: Vec::new(),
        leaves: Vec::new(),
        leaf_ids: Vec::new(),
        deps: Vec::new(),
        closed: Vec::new(),
        fixed: Vec::new(),
        square: false,
    };
    let mut at: IdMap<u32, usize> = IdMap::default();
    let (roots, len) = pred.roots();
    let mut stack: Vec<(u32, bool)> = roots[..len].iter().rev().map(|&r| (r, false)).collect();
    while let Some((i, done)) = stack.pop() {
        if at.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        let konst = cx.const_val(i);
        let interp = konst.is_none() && interpreted(cx, i);
        if interp && !done {
            stack.push((i, true));
            stack.extend(node.children().map(|c| (c, false)));
            continue;
        }
        let op = if let Some(v) = konst {
            Op::Const(v.to_u128()?)
        } else if interp {
            let a = at[&node.a];
            match node.op {
                OpCode::Zext => Op::Zext(a),
                OpCode::Sext => Op::Sext(a),
                OpCode::Extract => Op::Extract(a, node.b as u16),
                OpCode::Concat => Op::Concat(a, at[&node.b]),
                OpCode::Select => Op::Select(a, at[&node.b], at[&node.c]),
                op => {
                    if let Some(u) = op.as_un() {
                        Op::Un(u, a)
                    } else if let Some(c) = op.as_cmp() {
                        Op::Cmp(c, a, at[&node.b])
                    } else {
                        Op::Bin(op.as_bin()?, a, at[&node.b])
                    }
                }
            }
        } else {
            if p.leaves.len() >= MAX_LEAVES {
                return None;
            }
            p.leaves.push(node.width);
            p.leaf_ids.push(i);
            Op::Leaf(p.leaves.len() - 1)
        };
        p.push(op, node.width);
        at.insert(i, p.ops.len() - 1);
        if p.ops.len() > MAX_OPS {
            return None;
        }
    }
    match pred {
        Pred::Node(n) => {
            if cx.wid(n) != 1 || at[&n] != p.ops.len() - 1 {
                return None;
            }
        }
        Pred::Cmp(op, a, b) => p.push(Op::Cmp(op, at[&a], at[&b]), 1),
        Pred::NonZero(a) => {
            p.push(Op::Const(0), cx.wid(a));
            p.push(Op::Cmp(CmpOp::Ne, at[&a], p.ops.len() - 1), 1);
        }
        Pred::Bit(a, k) => p.push(Op::Extract(at[&a], k), 1),
    }
    Some(p)
}

impl Prog {
    /// Appends `op` (of width `w`) with what is known of it statically.
    fn push(&mut self, op: Op, w: u16) {
        let konst = |j: usize| match self.ops[j] {
            Op::Const(c) => Some(c),
            _ => None,
        };
        let (deps, closed, fixed) = match op {
            Op::Leaf(i) => (1u8 << i, true, u32::from(self.leaves[i])),
            Op::Const(_) => (0, true, 0),
            Op::Un(u, a) => (
                self.deps[a],
                matches!(u, UnOp::Not | UnOp::Neg) && self.closed[a],
                self.fixed[a],
            ),
            Op::Bin(b, x, y) => {
                let (lx, ly) = (self.closed[x], self.closed[y]);
                let both = self.fixed[x].max(self.fixed[y]);
                let closed = match b {
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor => {
                        lx && ly
                    }
                    BinOp::Shl => lx && konst(y).is_some(),
                    BinOp::URem => lx && konst(y).is_some_and(|d| d.is_power_of_two()),
                    _ => false,
                };
                // A mask, or a remainder by a power of two, of low bits keeps the value in them.
                let fixed = match (b, konst(x), konst(y)) {
                    (BinOp::And, _, Some(c)) if lx => both.min(bit_len(c)),
                    (BinOp::And, Some(c), _) if ly => both.min(bit_len(c)),
                    (BinOp::URem, _, Some(d)) if lx && d.is_power_of_two() => {
                        both.min(d.trailing_zeros())
                    }
                    _ => both,
                };
                if b == BinOp::Mul && self.deps[x] & self.deps[y] != 0 {
                    self.square = true;
                }
                (self.deps[x] | self.deps[y], closed, fixed)
            }
            Op::Cmp(_, x, y) => (
                self.deps[x] | self.deps[y],
                false,
                self.fixed[x].max(self.fixed[y]),
            ),
            Op::Zext(a) | Op::Sext(a) => (self.deps[a], self.closed[a], self.fixed[a]),
            Op::Extract(a, lo) => (
                self.deps[a],
                self.closed[a] && lo == 0,
                if self.closed[a] {
                    self.fixed[a].min(u32::from(lo) + u32::from(w))
                } else {
                    self.fixed[a]
                },
            ),
            Op::Concat(h, l) => (
                self.deps[h] | self.deps[l],
                self.closed[h] && self.closed[l],
                self.fixed[h].max(self.fixed[l]),
            ),
            Op::Select(c, a, b) => (
                self.deps[c] | self.deps[a] | self.deps[b],
                false,
                self.fixed[c].max(self.fixed[a]).max(self.fixed[b]),
            ),
        };
        // A value of `w` bits whose low bits the leaves' low bits fix is fixed by `w` of them.
        let fixed = if closed {
            fixed.min(u32::from(w))
        } else {
            fixed
        };
        self.ops.push(op);
        self.widths.push(w);
        self.deps.push(deps);
        self.closed.push(closed || deps == 0);
        self.fixed.push(if deps == 0 { 0 } else { fixed });
    }

    /// Whether the search over the low bits can conclude (with a product of a value with
    /// itself): a predicate a few low bits of each leaf fix in full, or an equality of terms
    /// whose low bits only low bits decide (or a signed remainder of one by a power of two,
    /// which keeps them).
    fn low_bits_decide(&self) -> bool {
        let k = self.fixed[self.ops.len() - 1];
        let bits: u32 = self.leaves.iter().map(|&w| u32::from(w).min(k)).sum();
        let lowish = |j: usize| {
            self.closed[j]
                || matches!(self.ops[j], Op::Bin(BinOp::SRem, a, d)
                    if self.closed[a] && matches!(self.ops[d], Op::Const(c) if c.is_power_of_two()))
        };
        bits <= EXHAUST_BITS
            || self.ops.iter().any(|op| {
                matches!(*op, Op::Cmp(CmpOp::Eq | CmpOp::Ne, a, b)
                    if lowish(a) && lowish(b) && self.deps[a] | self.deps[b] != 0)
            })
    }
}

// ----- low bits ---------------------------------------------------------------------------------

/// A value of width `w` whose low `b` bits are `r`: known in full when they cover it.
#[inline]
fn low(r: u128, b: u32, w: u16) -> V {
    if b >= u32::from(w) {
        V::Exact(r & mask(w))
    } else if b == 0 {
        V::Unknown
    } else {
        V::Low(r & mask(b as u16), b)
    }
}

/// The known low bits of a value and how many there are (every bit of one known in full).
#[inline]
fn bits(v: V) -> Option<(u128, u32)> {
    match v {
        V::Exact(x) => Some((x, 128)),
        V::Low(r, b) => Some((r, b)),
        _ => None,
    }
}

/// The sign extension of `v` from `from` bits to `to`.
fn sext(v: u128, from: u16, to: u16) -> u128 {
    (narrow::signed(v, from) as u128) & mask(to)
}

/// Whether `c` has no bit at `b` or above.
#[inline]
fn below(c: u128, b: u32) -> bool {
    b >= 128 || c >> b == 0
}

/// `op` over `x` and `y` at width `w`, from their low bits.
fn bin_low(op: BinOp, w: u16, x: V, y: V) -> V {
    use V::{Exact, Unknown};
    if let (Exact(u), Exact(v)) = (x, y) {
        return if narrow::bin_supported(op, w) {
            Exact(narrow::bin(op, w, u, v))
        } else {
            Unknown
        };
    }
    let both = bits(x)
        .zip(bits(y))
        .map(|((u, a), (v, b))| (u, v, a.min(b)));
    let ones = mask(w);
    match op {
        BinOp::Add => both.map_or(Unknown, |(u, v, b)| low(u.wrapping_add(v), b, w)),
        BinOp::Sub => both.map_or(Unknown, |(u, v, b)| low(u.wrapping_sub(v), b, w)),
        BinOp::Mul => {
            if x == Exact(0) || y == Exact(0) {
                return Exact(0);
            }
            // A factor with `t` low zero bits lifts the other's known bits by `t`.
            let lift = |c: V, o: V| match c {
                Exact(c) => {
                    let (r, b) = bits(o).unwrap_or((0, 0));
                    Some(low(c.wrapping_mul(r), (b + c.trailing_zeros()).min(128), w))
                }
                _ => None,
            };
            lift(x, y)
                .or_else(|| lift(y, x))
                .unwrap_or_else(|| both.map_or(Unknown, |(u, v, b)| low(u.wrapping_mul(v), b, w)))
        }
        BinOp::And => match (x, y) {
            (Exact(0), _) | (_, Exact(0)) => Exact(0),
            // A mask clears what it does not keep: in full when it keeps only known bits, and its
            // low zero bits whatever the other operand is.
            (Exact(c), o) | (o, Exact(c)) => match bits(o) {
                Some((r, b)) if below(c, b) => Exact(c & r),
                Some((r, b)) => low(c & r, b, w),
                None => low(0, c.trailing_zeros(), w),
            },
            _ => both.map_or(Unknown, |(u, v, b)| low(u & v, b, w)),
        },
        BinOp::Or => match (x, y) {
            (Exact(c), _) | (_, Exact(c)) if c == ones => Exact(ones),
            (Exact(c), o) | (o, Exact(c)) if bits(o).is_none() => low(c, c.trailing_ones(), w),
            _ => both.map_or(Unknown, |(u, v, b)| low(u | v, b, w)),
        },
        BinOp::Xor => both.map_or(Unknown, |(u, v, b)| low(u ^ v, b, w)),
        BinOp::Shl => match y {
            Exact(s) if s >= u128::from(w) => Exact(0),
            Exact(s) => {
                let (r, b) = bits(x).unwrap_or((0, 0));
                low(r << s, (b + s as u32).min(128), w)
            }
            _ if x == Exact(0) => Exact(0),
            _ => Unknown,
        },
        BinOp::LShr if x == Exact(0) => Exact(0),
        // A right shift by a constant moves known bits down.
        BinOp::LShr | BinOp::AShr => match (y, bits(x)) {
            (Exact(s), Some((r, b))) if s < u128::from(b) => low(r >> s, b - s as u32, w),
            _ => Unknown,
        },
        BinOp::URem | BinOp::SRem if x == Exact(0) => Exact(0),
        // Modulo a power of two: the low bits.
        BinOp::URem => match (y, bits(x)) {
            (Exact(d), Some((r, b))) if d.is_power_of_two() => {
                let j = d.trailing_zeros();
                if j <= b {
                    Exact(r & (d - 1))
                } else {
                    low(r, b, w)
                }
            }
            _ => Unknown,
        },
        // The signed remainder by a positive power of two `2^j` is the dividend modulo `2^j`
        // up to its sign: its low `j` bits are the dividend's, and it is 0 where they are.
        BinOp::SRem => match (y, bits(x)) {
            (Exact(d), Some((r, b))) if d.is_power_of_two() && d <= ones >> 1 => {
                let j = d.trailing_zeros();
                if j <= b && r & (d - 1) == 0 {
                    Exact(0)
                } else {
                    low(r, b.min(j), w)
                }
            }
            _ => Unknown,
        },
        _ => Unknown,
    }
}

/// The value of `p` at the class whose leaves have low `k` bits `leaf` (every leaf in full at
/// `k = 128`); `vals` is scratch.
fn eval_low(p: &Prog, k: u32, leaf: &[u128], vals: &mut [V]) -> V {
    use V::{Exact, Low, Unknown};
    for (j, op) in p.ops.iter().enumerate() {
        let w = p.widths[j];
        vals[j] = match *op {
            Op::Leaf(i) => low(leaf[i], k, p.leaves[i]),
            Op::Const(c) => Exact(c),
            Op::Un(u, a) => match vals[a] {
                Exact(v) => Exact(narrow::un(u, w, v)),
                Low(r, b) => match u {
                    UnOp::Not => low(!r, b, w),
                    UnOp::Neg => low(r.wrapping_neg(), b, w),
                    UnOp::Ctz if r != 0 => Exact(u128::from(r.trailing_zeros())),
                    _ => Unknown,
                },
                _ => Unknown,
            },
            Op::Bin(b, x, y) => bin_low(b, w, vals[x], vals[y]),
            Op::Cmp(c, x, y) => match (vals[x], vals[y]) {
                (Exact(u), Exact(v)) => Exact(u128::from(narrow::cmp(c, p.widths[x], u, v))),
                (u, v) if matches!(c, CmpOp::Eq | CmpOp::Ne) => match (bits(u), bits(v)) {
                    // Low bits both know that differ.
                    (Some((a, ba)), Some((b, bb))) if (a ^ b) & mask(ba.min(bb) as u16) != 0 => {
                        Exact(u128::from(c == CmpOp::Ne))
                    }
                    _ => Unknown,
                },
                _ => Unknown,
            },
            // The low bits of a value stay its low bits at any wider width.
            Op::Zext(a) => vals[a],
            Op::Sext(a) => match vals[a] {
                Exact(v) => Exact(sext(v, p.widths[a], w)),
                v => v,
            },
            Op::Extract(a, lo) => match vals[a] {
                Exact(v) => Exact((v >> lo) & mask(w)),
                Low(r, b) if u32::from(lo) < b => low(r >> lo, b - u32::from(lo), w),
                _ => Unknown,
            },
            Op::Concat(h, l) => {
                let wl = p.widths[l];
                match (vals[h], vals[l]) {
                    (Exact(hv), Exact(lv)) => Exact((hv << wl) | lv),
                    (_, Low(r, b)) => Low(r, b),
                    (hv, Exact(lv)) => match bits(hv) {
                        Some((r, b)) => low((r << wl) | lv, (u32::from(wl) + b).min(128), w),
                        None => low(lv, u32::from(wl), w),
                    },
                    _ => Unknown,
                }
            }
            Op::Select(c, a, b) => match vals[c] {
                Exact(0) => vals[b],
                Exact(_) => vals[a],
                _ if vals[a] == vals[b] => vals[a],
                _ => match (bits(vals[a]), bits(vals[b])) {
                    // The low bits the two arms agree on.
                    (Some((u, bu)), Some((v, bv))) => {
                        low(u, bu.min(bv).min((u ^ v).trailing_zeros()), w)
                    }
                    _ => Unknown,
                },
            },
        };
    }
    vals[p.ops.len() - 1]
}

/// A point: leaf `i`'s value at sample `s` (all zeros, all ones, one, then pseudorandom).
fn sample(s: u64, i: usize) -> u128 {
    let mix = |z: u64| {
        let mut z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    match s {
        0 => 0,
        1 => u128::MAX,
        2 => 1,
        _ => {
            let z = s << 8 | i as u64;
            u128::from(mix(z)) << 64 | u128::from(mix(!z))
        }
    }
}

/// The predicate's value at a point (`None` never happens: every operation is evaluated in full
/// on values known in full).
fn at_point(p: &Prog, leaf: &[u128], vals: &mut [V]) -> Option<bool> {
    match eval_low(p, 128, leaf, vals) {
        V::Exact(v) => Some(v != 0),
        _ => None,
    }
}

/// The search over the low bits: `Some(seen)` when every class decides the predicate as the
/// sample points did. `work` counts the classes and points evaluated.
fn search_low(p: &Prog, seen: bool, work: &mut u64) -> Option<bool> {
    let n = p.leaves.len();
    if n == 0 {
        // No leaves: the points decided it.
        return Some(seen);
    }
    let limit = *work + MAX_WORK / p.ops.len() as u64;
    let mut vals = vec![V::Unknown; p.ops.len()];
    // Undecided classes, `n` residues each; at first one class with no bits.
    let mut live: Vec<u128> = vec![0; n];
    let mut next: Vec<u128> = Vec::new();
    let mut class = vec![0u128; n];
    let top = p.leaves.iter().copied().max().unwrap_or(0);
    for k in 1..=u32::from(top) {
        let grow: Vec<usize> = (0..n).filter(|&i| u32::from(p.leaves[i]) >= k).collect();
        let classes = live.len() / n;
        let children = classes << grow.len();
        if children > MAX_CLASSES || *work + children as u64 + 1 > limit {
            return None;
        }
        *work += children as u64 + 1;
        next.clear();
        let bit = 1u128 << (k - 1);
        for c in 0..classes {
            for pick in 0..1usize << grow.len() {
                class.copy_from_slice(&live[c * n..(c + 1) * n]);
                for (j, &i) in grow.iter().enumerate() {
                    if pick >> j & 1 == 1 {
                        class[i] |= bit;
                    }
                }
                match eval_low(p, k, &class, &mut vals) {
                    V::Exact(v) if (v != 0) == seen => {}
                    V::Exact(_) => return None,
                    _ => next.extend_from_slice(&class),
                }
            }
        }
        if next.is_empty() {
            return Some(seen);
        }
        // An undecided class as a value of its own (its residues, the higher bits zero): a
        // point where the predicate has the other value ends the search.
        class.copy_from_slice(&next[..n]);
        if at_point(p, &class, &mut vals) != Some(seen) {
            return None;
        }
        core::mem::swap(&mut live, &mut next);
    }
    None
}

// ----- other moduli -----------------------------------------------------------------------------

/// Every bit up to the highest of `x`: the largest value with no bit above it.
#[inline]
fn smear(x: u128) -> u128 {
    if x == 0 {
        0
    } else {
        u128::MAX >> x.leading_zeros()
    }
}

/// How a residue modulo `m` reads a value's bits: as an unsigned or a signed integer (the
/// same integer for a value never negative).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Read {
    U,
    S,
}

/// What the search modulo `m` knows of each operation statically: the unsigned and the signed
/// interval of its value, and the reading in which its value is an integer its operands'
/// determine, if there is one (a sum, difference, product or left shift that cannot wrap in
/// that reading, an extension, a mask that keeps the value, a leaf).
struct Ranges {
    u: Vec<(u128, u128)>,
    s: Vec<(i128, i128)>,
    read: Vec<Option<Read>>,
    /// Whether it is a sum, difference, product or left shift that does not wrap in its reading.
    exact: Vec<bool>,
    /// Whether the operation is a constant (whose residue is known in either reading).
    konst: Vec<bool>,
}

impl Ranges {
    /// Whether operation `j` is never negative: both readings are one integer.
    fn nonneg(&self, j: usize) -> bool {
        self.s[j].0 >= 0
    }

    /// Whether operation `j` has a residue in reading `r`.
    fn reads(&self, j: usize, r: Read) -> bool {
        self.konst[j] || self.read[j] == Some(r) || (self.read[j].is_some() && self.nonneg(j))
    }
}

/// The signed bounds of width `w`.
fn signed_bounds(w: u16) -> (i128, i128) {
    let smax = (mask(w) >> 1) as i128;
    (-smax - 1, smax)
}

/// The intervals and readings of [`Ranges`].
fn ranges(p: &Prog) -> Ranges {
    let n = p.ops.len();
    let mut r = Ranges {
        u: Vec::with_capacity(n),
        s: Vec::with_capacity(n),
        read: Vec::with_capacity(n),
        exact: vec![false; n],
        konst: p.ops.iter().map(|op| matches!(op, Op::Const(_))).collect(),
    };
    // A leaf only sign-extended reads as signed.
    let mut uses = vec![(false, false); p.leaves.len()];
    for op in &p.ops {
        let mut note = |j: usize, signed: bool| {
            if let Op::Leaf(i) = p.ops[j] {
                if signed {
                    uses[i].1 = true;
                } else {
                    uses[i].0 = true;
                }
            }
        };
        match *op {
            Op::Sext(a) => note(a, true),
            Op::Leaf(_) | Op::Const(_) => {}
            Op::Un(_, a) | Op::Zext(a) | Op::Extract(a, _) => note(a, false),
            Op::Bin(_, a, b) | Op::Cmp(_, a, b) | Op::Concat(a, b) => {
                note(a, false);
                note(b, false);
            }
            Op::Select(c, a, b) => {
                note(c, false);
                note(a, false);
                note(b, false);
            }
        }
    }
    for (j, op) in p.ops.iter().enumerate() {
        let w = p.widths[j];
        let (smin, smax) = signed_bounds(w);
        let full = (0, mask(w));
        // The signed interval of a value whose unsigned one is `u`.
        let from_u = |u: (u128, u128)| {
            if u.1 <= smax as u128 {
                (u.0 as i128, u.1 as i128)
            } else {
                (smin, smax)
            }
        };
        let (u, s, read) = match *op {
            Op::Leaf(i) => {
                let read = if uses[i] == (false, true) {
                    Read::S
                } else {
                    Read::U
                };
                (full, (smin, smax), Some(read))
            }
            Op::Const(c) => (
                (c, c),
                {
                    let v = narrow::signed(c, w);
                    (v, v)
                },
                None,
            ),
            Op::Un(UnOp::Not, a) => {
                let u = (!r.u[a].1 & mask(w), !r.u[a].0 & mask(w));
                (u, (-1 - r.s[a].1, -1 - r.s[a].0), None)
            }
            Op::Un(UnOp::Popcnt | UnOp::Clz | UnOp::Ctz, _) => {
                let u = (0, u128::from(w));
                (u, from_u(u), None)
            }
            Op::Un(..) => (full, (smin, smax), None),
            Op::Cmp(..) => ((0, 1), (0, 1), None),
            Op::Bin(b, x, y) => {
                let ((xl, xh), (yl, yh)) = (r.u[x], r.u[y]);
                let ((sxl, sxh), (syl, syh)) = (r.s[x], r.s[y]);
                let square = x == y;
                // Without wraparound, unsigned: the operands' unsigned integers.
                let fits = |v: Option<u128>| v.filter(|&v| v <= mask(w));
                let unsigned = match b {
                    BinOp::Add => fits(xh.checked_add(yh)).map(|h| (xl + yl, h)),
                    BinOp::Sub => (xl >= yh).then(|| (xl - yh, xh - yl)),
                    BinOp::Mul => fits(xh.checked_mul(yh)).map(|h| (xl * yl, h)),
                    BinOp::Shl if yl == yh && yl < u128::from(w) => {
                        let sh = yl as u32;
                        (xh.leading_zeros() >= sh + (128 - u32::from(w)))
                            .then(|| (xl << sh, xh << sh))
                    }
                    _ => None,
                };
                // And signed: the operands' signed integers.
                let sfits = |l: Option<i128>, h: Option<i128>| {
                    l.zip(h).filter(|&(l, h)| smin <= l && h <= smax)
                };
                let signed = match b {
                    BinOp::Add => sfits(sxl.checked_add(syl), sxh.checked_add(syh)),
                    BinOp::Sub => sfits(sxl.checked_sub(syh), sxh.checked_sub(syl)),
                    BinOp::Mul if square => {
                        let (a, c) = (sxl.unsigned_abs(), sxh.unsigned_abs());
                        let lo = if sxl <= 0 && 0 <= sxh { 0 } else { a.min(c) };
                        let sq = |v: u128| v.checked_mul(v).and_then(|v| i128::try_from(v).ok());
                        sfits(sq(lo), sq(a.max(c)))
                    }
                    BinOp::Mul => {
                        let ends = [
                            sxl.checked_mul(syl),
                            sxl.checked_mul(syh),
                            sxh.checked_mul(syl),
                            sxh.checked_mul(syh),
                        ];
                        if ends.iter().all(Option::is_some) {
                            let ends = ends.map(|e| e.unwrap_or(0));
                            sfits(ends.iter().min().copied(), ends.iter().max().copied())
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                // The reading in which it does not wrap, the one its operands' residues are in
                // first (a factor that is a multiple of the modulus needs no residue of the
                // other).
                let provides_u = r.reads(x, Read::U) && r.reads(y, Read::U);
                let provides_s = r.reads(x, Read::S) && r.reads(y, Read::S);
                let pick = [
                    (Read::U, unsigned.is_some() && provides_u),
                    (Read::S, signed.is_some() && provides_s),
                    (Read::U, unsigned.is_some()),
                    (Read::S, signed.is_some()),
                ]
                .into_iter()
                .find_map(|(rd, ok)| ok.then_some(rd));
                if let (Some(Read::U), Some(u)) = (pick, unsigned) {
                    r.exact[j] = true;
                    (u, from_u(u), Some(Read::U))
                } else if let (Some(Read::S), Some(sv)) = (pick, signed) {
                    r.exact[j] = true;
                    let u = if sv.0 >= 0 {
                        (sv.0 as u128, sv.1 as u128)
                    } else {
                        full
                    };
                    (u, sv, Some(Read::S))
                } else {
                    let u = match b {
                        BinOp::And => (0, xh.min(yh)),
                        BinOp::Or => (xl.max(yl), smear(xh | yh)),
                        BinOp::Xor => (0, smear(xh | yh)),
                        BinOp::LShr if yl == yh && yl < u128::from(w) => (xl >> yl, xh >> yl),
                        BinOp::LShr => (0, xh),
                        BinOp::UDiv if yl > 0 => (xl / yh, xh / yl),
                        BinOp::URem if yl > 0 => (0, xh.min(yh - 1)),
                        BinOp::URem => (0, xh),
                        _ => unsigned.unwrap_or(full),
                    };
                    let s = match b {
                        // A remainder by a positive divisor has the dividend's sign, and is
                        // smaller in magnitude than the divisor.
                        BinOp::SRem if syl > 0 => (
                            if sxl < 0 { sxl.max(1 - syh) } else { 0 },
                            if sxh > 0 { sxh.min(syh - 1) } else { 0 },
                        ),
                        _ => signed.unwrap_or_else(|| from_u(u)),
                    };
                    // A mask that keeps every bit the value may have keeps the value.
                    let read = match (b, p.ops[x], p.ops[y]) {
                        (BinOp::And, _, Op::Const(c)) if smear(xh) & !c == 0 => r.read[x],
                        (BinOp::And, Op::Const(c), _) if smear(yh) & !c == 0 => r.read[y],
                        _ => None,
                    };
                    (u, s, read)
                }
            }
            Op::Zext(a) => {
                let read = r.reads(a, Read::U).then_some(Read::U);
                (r.u[a], from_u(r.u[a]), read)
            }
            Op::Sext(a) => {
                let wa = p.widths[a];
                let u = if r.u[a].1 <= mask(wa) >> 1 {
                    r.u[a]
                } else {
                    full
                };
                (u, r.s[a], r.reads(a, Read::S).then_some(Read::S))
            }
            Op::Extract(a, lo) => {
                if lo == 0 && r.u[a].1 <= mask(w) {
                    let read = r.reads(a, Read::U).then_some(Read::U);
                    (r.u[a], from_u(r.u[a]), read)
                } else {
                    let u = (0, (r.u[a].1 >> lo).min(mask(w)));
                    (u, from_u(u), None)
                }
            }
            Op::Concat(h, l) => {
                let wl = p.widths[l];
                let u = (r.u[h].0 << wl | r.u[l].0, r.u[h].1 << wl | r.u[l].1);
                let read = (r.u[h].1 == 0 && r.reads(l, Read::U)).then_some(Read::U);
                (u, from_u(u), read)
            }
            Op::Select(_, a, b) => {
                let u = (r.u[a].0.min(r.u[b].0), r.u[a].1.max(r.u[b].1));
                let s = (r.s[a].0.min(r.s[b].0), r.s[a].1.max(r.s[b].1));
                let read = [Read::U, Read::S]
                    .into_iter()
                    .find(|&x| r.reads(a, x) && r.reads(b, x));
                (u, s, read)
            }
        };
        r.u.push(u);
        r.s.push(s);
        r.read.push(read);
    }
    r
}

/// The residue modulo `m` of operation `j`'s value in reading `want`, if known.
#[inline]
fn residue(p: &Prog, r: &Ranges, vals: &[V], j: usize, want: Read, m: u128) -> Option<u128> {
    match vals[j] {
        V::Exact(x) => Some(match want {
            Read::U => x % m,
            Read::S => narrow::signed(x, p.widths[j]).rem_euclid(m as i128) as u128,
        }),
        V::Res(v) if r.reads(j, want) => Some(v),
        _ => None,
    }
}

/// The value of `p` modulo `m` where each leaf has residue (or, if narrower than `m`, value)
/// `leaf`: an operation's residue is that of its integer in its reading.
fn eval_mod(p: &Prog, m: u128, r: &Ranges, leaf: &[u128], vals: &mut [V]) -> V {
    use V::{Exact, Res, Unknown};
    for (j, op) in p.ops.iter().enumerate() {
        let w = p.widths[j];
        let read = r.read[j];
        // The residue of the operand `a` in this operation's reading, if it has one.
        let res = |vals: &[V], a: usize| read.and_then(|rd| residue(p, r, vals, a, rd, m));
        vals[j] = match *op {
            Op::Leaf(i) => {
                if mask(p.leaves[i]) < m {
                    Exact(leaf[i])
                } else {
                    Res(leaf[i])
                }
            }
            Op::Const(c) => Exact(c),
            Op::Un(u, a) => match vals[a] {
                Exact(v) => Exact(narrow::un(u, w, v)),
                _ => Unknown,
            },
            Op::Bin(b, x, y) => match (b, vals[x], vals[y]) {
                (_, Exact(a), Exact(c)) if narrow::bin_supported(b, w) => {
                    Exact(narrow::bin(b, w, a, c))
                }
                // A multiple of `m` that does not wrap, whatever the other factor (a quotient
                // `udiv(p, d) · d`, say).
                (BinOp::Mul, ..)
                    if r.exact[j]
                        && [x, y]
                            .into_iter()
                            .any(|f| matches!(vals[f], Exact(_)) && res(vals, f) == Some(0)) =>
                {
                    Res(0)
                }
                (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl, ..) if r.exact[j] => {
                    match (b, res(vals, x), vals[y]) {
                        // A wrapless shift is by a constant below the width.
                        (BinOp::Shl, Some(a), Exact(s)) => Res((0..s).fold(a, |v, _| v * 2 % m)),
                        (BinOp::Shl, ..) | (_, None, _) => Unknown,
                        (_, Some(a), _) => match res(vals, y) {
                            Some(c) if b == BinOp::Add => Res((a + c) % m),
                            Some(c) if b == BinOp::Sub => Res((a + m - c) % m),
                            Some(c) => Res(a * c % m),
                            None => Unknown,
                        },
                    }
                }
                // The remainder by a divisor of `m`: of the unsigned integer, or of a signed one
                // by a positive divisor, which is that residue when the dividend is not
                // negative, and 0 when the residue is.
                (BinOp::URem, _, Exact(d)) if d > 0 && m.is_multiple_of(d) => {
                    residue(p, r, vals, x, Read::U, m).map_or(Unknown, |a| Exact(a % d))
                }
                (BinOp::SRem, _, Exact(d)) if d > 0 && d <= mask(w) >> 1 && m.is_multiple_of(d) => {
                    match residue(p, r, vals, x, Read::S, m).map(|a| a % d) {
                        Some(a) if a == 0 || r.nonneg(x) => Exact(a),
                        _ => Unknown,
                    }
                }
                // A mask that keeps every bit the value may have.
                (BinOp::And, u, Exact(c)) if smear(r.u[x].1) & !c == 0 => u,
                (BinOp::And, Exact(c), v) if smear(r.u[y].1) & !c == 0 => v,
                (BinOp::And, Exact(0), _) | (BinOp::And, _, Exact(0)) => Exact(0),
                (BinOp::Or, Exact(c), _) | (BinOp::Or, _, Exact(c)) if c == mask(w) => {
                    Exact(mask(w))
                }
                _ => Unknown,
            },
            Op::Cmp(c, x, y) => match (vals[x], vals[y]) {
                (Exact(u), Exact(v)) => Exact(u128::from(narrow::cmp(c, p.widths[x], u, v))),
                _ if matches!(c, CmpOp::Eq | CmpOp::Ne) => {
                    // Equal bits are equal integers in either reading.
                    let differ = [Read::U, Read::S].into_iter().any(|rd| {
                        matches!((residue(p, r, vals, x, rd, m), residue(p, r, vals, y, rd, m)),
                            (Some(a), Some(b)) if a != b)
                    });
                    if differ {
                        Exact(u128::from(c == CmpOp::Ne))
                    } else {
                        Unknown
                    }
                }
                _ => Unknown,
            },
            Op::Zext(a) => match vals[a] {
                Exact(v) => Exact(v),
                _ => res(vals, a).map_or(Unknown, Res),
            },
            Op::Sext(a) => match vals[a] {
                Exact(v) => Exact(sext(v, p.widths[a], w)),
                _ => res(vals, a).map_or(Unknown, Res),
            },
            Op::Extract(a, lo) => match vals[a] {
                Exact(v) => Exact((v >> lo) & mask(w)),
                _ => res(vals, a).map_or(Unknown, Res),
            },
            Op::Concat(h, l) => match (vals[h], vals[l]) {
                (Exact(hv), Exact(lv)) => Exact((hv << p.widths[l]) | lv),
                _ => res(vals, l).map_or(Unknown, Res),
            },
            Op::Select(c, a, b) => match vals[c] {
                Exact(0) => vals[b],
                Exact(_) => vals[a],
                _ if vals[a] == vals[b] => vals[a],
                _ => match (res(vals, a), res(vals, b)) {
                    (Some(u), Some(v)) if u == v => Res(u),
                    _ => Unknown,
                },
            },
        };
    }
    vals[p.ops.len() - 1]
}

/// The moduli worth a search: the divisors of the remainders and quotients that are not powers
/// of two, and 3, 5 and 7 when an equality has a side the integers' arithmetic computes.
fn moduli(p: &Prog, r: &Ranges) -> Vec<u128> {
    let mut out: Vec<u128> = Vec::new();
    let mut small = false;
    for op in &p.ops {
        match *op {
            Op::Bin(BinOp::URem | BinOp::SRem | BinOp::UDiv | BinOp::SDiv, _, d) => {
                if let Op::Const(d) = p.ops[d]
                    && d > 2
                    && !d.is_power_of_two()
                    && d <= MAX_MODULUS
                    && !out.contains(&d)
                {
                    out.push(d);
                }
            }
            Op::Cmp(CmpOp::Eq | CmpOp::Ne, a, b) => small |= r.exact[a] || r.exact[b],
            _ => {}
        }
    }
    if small {
        for m in [3, 5, 7] {
            if !out.contains(&m) {
                out.push(m);
            }
        }
    }
    out
}

/// The search modulo `m`: every combination of the leaves' residues (or values) at once.
/// `work` counts the combinations evaluated.
fn search_mod(p: &Prog, m: u128, r: &Ranges, seen: bool, work: &mut u64) -> Option<bool> {
    let n = p.leaves.len();
    let counts: Vec<u128> = p
        .leaves
        .iter()
        .map(|&w| if mask(w) < m { mask(w) + 1 } else { m })
        .collect();
    let total = counts
        .iter()
        .try_fold(1u128, |t, &c| t.checked_mul(c))
        .filter(|&t| t <= u128::from(MAX_WORK / p.ops.len() as u64))?;
    let mut vals = vec![V::Unknown; p.ops.len()];
    let mut leaf = vec![0u128; n];
    for _ in 0..total {
        *work += 1;
        match eval_mod(p, m, r, &leaf, &mut vals) {
            V::Exact(v) if (v != 0) == seen => {}
            _ => return None,
        }
        // The next combination, the first leaf fastest.
        for i in 0..n {
            leaf[i] += 1;
            if leaf[i] < counts[i] {
                break;
            }
            leaf[i] = 0;
        }
    }
    Some(seen)
}

/// The value of the predicate if residues show it constant (see the module comment), and the
/// work it took: operations evaluated.
pub(crate) fn constant(cx: &Context, pred: Pred) -> (Option<bool>, u64) {
    let (roots, len) = pred.roots();
    if !has_product(cx, &roots[..len]) {
        return (None, MAX_OPS as u64);
    }
    let Some(p) = compile(cx, pred).filter(|p| p.square) else {
        return (None, 2 * MAX_OPS as u64);
    };
    let len = p.ops.len() as u64;
    let low = p.low_bits_decide();
    let ranges = ranges(&p);
    let moduli = moduli(&p, &ranges);
    if !low && moduli.is_empty() {
        return (None, 3 * len);
    }
    // A few points first: two values there and it is not a constant.
    let mut vals = vec![V::Unknown; p.ops.len()];
    let mut seen = None;
    let mut leaf = vec![0u128; p.leaves.len()];
    for s in 0..SAMPLES {
        for (i, l) in leaf.iter_mut().enumerate() {
            *l = sample(s, i);
        }
        let v = at_point(&p, &leaf, &mut vals);
        if v.is_none() || (seen.is_some() && v != seen) {
            return (None, (s + 3) * len);
        }
        seen = v;
    }
    let Some(seen) = seen else {
        return (None, (SAMPLES + 2) * len);
    };
    let mut work = SAMPLES + 2;
    let mut out = if low {
        search_low(&p, seen, &mut work)
    } else {
        None
    };
    for &m in &moduli {
        if out.is_some() {
            break;
        }
        out = search_mod(&p, m, &ranges, seen, &mut work);
    }
    (out, work * len)
}

/// A predicate over one value that only its low bits decide, as a test of the fewest of them:
/// `(x, j, t)` when it holds exactly where `t[trunc<j>(x)]`, and the work it took. So
/// `(x·x & 7) == 1` is `x` odd, `(x·x & 15) == 0` is `trunc<2>(x) == 0`, and `x·(x + 1) & 3`
/// is 2 where `x` is 1 or 2 modulo 4: the disguise of a parity or alignment test comes off.
pub(crate) fn residue_test(cx: &Context, n: u32) -> (Option<(u32, u16, Vec<bool>)>, u64) {
    if !has_product(cx, &[n]) {
        return (None, MAX_OPS as u64);
    }
    let Some(p) = compile(cx, Pred::Node(n)) else {
        return (None, 2 * MAX_OPS as u64);
    };
    let k = p.fixed[p.ops.len() - 1];
    let len = p.ops.len() as u64;
    if p.leaves.len() != 1 || k == 0 || k > RECOVER_BITS || k >= u32::from(p.leaves[0]) {
        return (None, 3 * len);
    }
    // The truth table over the value's low `k` bits.
    let size = 1usize << k;
    let mut vals = vec![V::Unknown; p.ops.len()];
    let mut table = vec![false; size];
    for (r, t) in table.iter_mut().enumerate() {
        match eval_low(&p, k, &[r as u128], &mut vals) {
            V::Exact(v) => *t = v != 0,
            _ => return (None, (r as u64 + 4) * len),
        }
    }
    let work = (size as u64 + 3) * len;
    // The fewest low bits it depends on.
    let j = (1..=k)
        .find(|&j| (0..size).all(|r| table[r] == table[r & ((1 << j) - 1)]))
        .unwrap_or(k);
    table.truncate(1 << j);
    if table.iter().all(|&t| t) || !table.iter().any(|&t| t) {
        return (None, work);
    }
    (Some((p.leaf_ids[0], j as u16, table)), work)
}

/// [`constant`] of a 1-bit node for the compares pass, charged to the call's pass work.
pub(super) fn decide(r: &mut Runner<'_, '_>, cx: &Context, n: u32) -> Result<Option<bool>, Stop> {
    if cx.wid(n) != 1 || cx.const_val(n).is_some() {
        return Ok(None);
    }
    let (out, work) = constant(cx, Pred::Node(n));
    r.meter.charge(Counter::PassWork, work / 64 + 1)?;
    Ok(out)
}

/// [`residue_test`] for the compares pass, charged to the call's pass work.
pub(super) fn recover(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
) -> Result<Option<(u32, u16, Vec<bool>)>, Stop> {
    if cx.wid(n) != 1 || cx.const_val(n).is_some() {
        return Ok(None);
    }
    let (out, work) = residue_test(cx, n);
    r.meter.charge(Counter::PassWork, work / 64 + 1)?;
    Ok(out)
}
