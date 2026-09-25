//! Low bits by residues: the low `k` bits of `+ − * neg ~ & | ^` and left shifts by constants
//! depend only on the low `k` bits of their operands, so an expression built from them is,
//! modulo `2^k`, a function of its leaves modulo `2^k`. With few leaves and a small `k` that
//! function is a small table, computed by evaluating every combination of the leaves'
//! residues. It decides what the operations' transfer functions cannot: `x·x` is `x` modulo 2
//! and never `2` or `3` modulo 4, an odd square is 1 modulo 8, `x·(x + 1)` is even, a product of
//! four consecutive values is a multiple of 8.

use super::{Runner, Stop};
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};

/// The most leaves a table is built over.
const MAX_LEAVES: usize = 3;

/// The most nodes the expression may have.
const MAX_NODES: usize = 32;

/// The most combinations of the leaves' residues evaluated.
const MAX_COMBOS: u64 = 4096;

/// One operation over residues.
#[derive(Clone, Copy)]
enum Op {
    Leaf(usize),
    Const(u64),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Neg(usize),
    Not(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    Shl(usize, u32),
}

/// The values of an expression modulo `2^k`, for every combination of its leaves' residues.
pub(crate) struct Residues {
    /// The leaves (atoms), in the order their residues are enumerated.
    pub(super) leaves: Vec<u32>,
    /// `2^k - 1`.
    pub(super) mask: u64,
    /// The expression's value per combination: combination `c` gives leaf `i` the residue
    /// `(c >> (k·i)) & mask`.
    pub(super) values: Vec<u64>,
    k: u32,
}

impl Residues {
    /// Leaf `i`'s residue in combination `c`.
    pub(super) fn leaf(&self, c: usize, i: usize) -> u64 {
        (c as u64 >> (self.k * i as u32)) & self.mask
    }
}

/// Compiles the expression at `x` (post-order), or `None` when it has other operations at the
/// top, more leaves or nodes than the caps, or no product (products are what the other passes
/// do not see through modulo a power of two).
fn compile(cx: &Context, x: u32) -> Option<(Vec<Op>, Vec<u32>)> {
    let mut ops: Vec<Op> = Vec::new();
    let mut at: crate::hash::IdMap<u32, usize> = crate::hash::IdMap::default();
    let mut leaves: Vec<u32> = Vec::new();
    let mut product = false;
    let w = cx.wid(x);
    // Iterative post-order.
    let mut stack: Vec<(u32, bool)> = vec![(x, false)];
    while let Some((i, done)) = stack.pop() {
        if at.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        let arith = cx.wid(i) == w
            && matches!(
                node.op,
                OpCode::Add
                    | OpCode::Sub
                    | OpCode::Mul
                    | OpCode::Neg
                    | OpCode::Not
                    | OpCode::And
                    | OpCode::Or
                    | OpCode::Xor
            );
        let shift = node.op == OpCode::Shl && cx.const_val(node.b).is_some();
        if !done && (arith || shift) {
            stack.push((i, true));
            for c in node.children() {
                if !(shift && c == node.b) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        let op = if let Some(v) = cx.const_val(i) {
            Op::Const(v.limbs()[0])
        } else if shift {
            let s = cx.const_val(node.b)?.to_u64().unwrap_or(u64::MAX);
            Op::Shl(at[&node.a], s.min(64) as u32)
        } else if arith {
            let (a, b) = (at[&node.a], node.children().nth(1).map(|c| at[&c]));
            match node.op {
                OpCode::Add => Op::Add(a, b?),
                OpCode::Sub => Op::Sub(a, b?),
                OpCode::Mul => {
                    product = true;
                    Op::Mul(a, b?)
                }
                OpCode::Neg => Op::Neg(a),
                OpCode::Not => Op::Not(a),
                OpCode::And => Op::And(a, b?),
                OpCode::Or => Op::Or(a, b?),
                _ => Op::Xor(a, b?),
            }
        } else {
            if leaves.len() >= MAX_LEAVES {
                return None;
            }
            leaves.push(i);
            Op::Leaf(leaves.len() - 1)
        };
        ops.push(op);
        at.insert(i, ops.len() - 1);
        if ops.len() > MAX_NODES {
            return None;
        }
    }
    product.then_some((ops, leaves))
}

/// The value modulo `2^k` of the compiled expression at combination `c`.
fn eval(ops: &[Op], k: u32, mask: u64, c: u64, vals: &mut [u64]) -> u64 {
    for (j, op) in ops.iter().enumerate() {
        vals[j] = match *op {
            Op::Leaf(i) => c >> (k * i as u32),
            Op::Const(v) => v,
            Op::Add(a, b) => vals[a].wrapping_add(vals[b]),
            Op::Sub(a, b) => vals[a].wrapping_sub(vals[b]),
            Op::Mul(a, b) => vals[a].wrapping_mul(vals[b]),
            Op::Neg(a) => vals[a].wrapping_neg(),
            Op::Not(a) => !vals[a],
            Op::And(a, b) => vals[a] & vals[b],
            Op::Or(a, b) => vals[a] | vals[b],
            Op::Xor(a, b) => vals[a] ^ vals[b],
            Op::Shl(a, s) => {
                if s >= 64 {
                    0
                } else {
                    vals[a] << s
                }
            }
        } & mask;
    }
    vals[ops.len() - 1]
}

/// Whether the bits of `m` (among the low `k`) of `x` may be constant, or equal to one leaf's,
/// at every combination: false when a few combinations already show neither, which saves the
/// full table (a table seen before answers exactly).
pub(super) fn may_fold(r: &Runner<'_, '_>, cx: &Context, x: u32, k: u32, m: u64) -> bool {
    if let Some(t) = r.residues.get(&(x, k)) {
        return t.is_some();
    }
    if k == 0 || k > u32::from(cx.wid(x)) {
        return false;
    }
    let Some((ops, leaves)) = compile(cx, x) else {
        return false;
    };
    let combos = 1u64 << (k as usize * leaves.len());
    if leaves.len() * k as usize > 16 || combos > MAX_COMBOS {
        return false;
    }
    let mask = (1u64 << k) - 1;
    let mut vals = vec![0u64; ops.len()];
    // Combinations spread over the table (a fixed sequence: the answer is deterministic).
    let picks: Vec<u64> = (0..8u64)
        .map(|j| j.wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left(17) % combos)
        .chain([0, combos - 1])
        .collect();
    let values: Vec<(u64, u64)> = picks
        .iter()
        .map(|&c| (c, eval(&ops, k, mask, c, &mut vals)))
        .collect();
    let first = values[0].1 & m;
    if values.iter().all(|&(_, v)| v & m == first) {
        return true;
    }
    (0..leaves.len()).any(|i| {
        values
            .iter()
            .all(|&(c, v)| v & m == (c >> (k * i as u32)) & mask & m)
    })
}

/// The table of `x` modulo `2^k` (`1 <= k <= 16`), if it fits the caps; remembered for the
/// call (a node's table never changes).
pub(super) fn residues(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    x: u32,
    k: u32,
) -> Result<Option<std::rc::Rc<Residues>>, Stop> {
    if let Some(t) = r.residues.get(&(x, k)) {
        return Ok(t.clone());
    }
    let t = table(r, cx, x, k)?.map(std::rc::Rc::new);
    r.residues.insert((x, k), t.clone());
    Ok(t)
}

fn table(r: &mut Runner<'_, '_>, cx: &Context, x: u32, k: u32) -> Result<Option<Residues>, Stop> {
    if k == 0 || k > u32::from(cx.wid(x)) {
        return Ok(None);
    }
    let Some((ops, leaves)) = compile(cx, x) else {
        return Ok(None);
    };
    let combos = 1u64 << (k as usize * leaves.len());
    if leaves.len() * k as usize > 16 || combos > MAX_COMBOS {
        return Ok(None);
    }
    r.meter
        .charge(Counter::PassWork, combos * ops.len() as u64 / 64 + 1)?;
    let mask = (1u64 << k) - 1;
    let mut vals = vec![0u64; ops.len()];
    let values = (0..combos)
        .map(|c| eval(&ops, k, mask, c, &mut vals))
        .collect();
    Ok(Some(Residues {
        leaves,
        mask,
        values,
        k,
    }))
}
