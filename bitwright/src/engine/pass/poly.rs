//! Polynomial equality (called by the compares pass): two sides built from `+ − * neg`, left
//! shifts by constants and constants over a few leaves are expanded into sums of monomials
//! with coefficients modulo `2^W`; equal polynomials are equal functions, so `a == b` is true
//! (and `a != b` false). `(x + y)·(x − y) == x·x − y·y` and the sum of cubes are decided this
//! way. Different polynomials may still be equal functions (`2^(W−1)·(x² + x)` is 0), which
//! this leaves undecided.

use super::{Runner, Stop};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::BinOp;

/// The most leaves.
const MAX_LEAVES: usize = 4;

/// The most monomials a polynomial keeps.
const MAX_TERMS: usize = 64;

/// The most degree per leaf.
const MAX_DEGREE: u8 = 6;

/// A monomial: the exponent of each leaf.
type Mono = [u8; MAX_LEAVES];

/// A polynomial: monomials with nonzero coefficients, sorted.
type Poly = Vec<(Mono, BitVec)>;

fn add(a: &Poly, b: &Poly, sub: bool) -> Poly {
    let mut out: Poly = a.clone();
    for (m, c) in b {
        let c = if sub {
            BitVec::apply_un(crate::UnOp::Neg, c).unwrap_or(*c)
        } else {
            *c
        };
        match out.binary_search_by(|(k, _)| k.cmp(m)) {
            Ok(i) => {
                out[i].1 = BitVec::apply_bin(BinOp::Add, &out[i].1, &c).unwrap_or(c);
            }
            Err(i) => out.insert(i, (*m, c)),
        }
    }
    out.retain(|(_, c)| !c.is_zero());
    out
}

fn mul(a: &Poly, b: &Poly) -> Option<Poly> {
    let mut out: Poly = Vec::new();
    for (ma, ca) in a {
        for (mb, cb) in b {
            let mut m = [0u8; MAX_LEAVES];
            for i in 0..MAX_LEAVES {
                m[i] = ma[i].checked_add(mb[i]).filter(|&d| d <= MAX_DEGREE)?;
            }
            let c = BitVec::apply_bin(BinOp::Mul, ca, cb).ok()?;
            out = add(&out, &vec![(m, c)], false);
            if out.len() > MAX_TERMS {
                return None;
            }
        }
    }
    Some(out)
}

/// The polynomial of `x` over `leaves` (added as met), if it is one within the caps.
fn poly_of(
    cx: &Context,
    x: u32,
    leaves: &mut Vec<u32>,
    memo: &mut IdMap<u32, Poly>,
    steps: &mut u32,
) -> Option<Poly> {
    if let Some(p) = memo.get(&x) {
        return Some(p.clone());
    }
    *steps += 1;
    if *steps > 256 {
        return None;
    }
    let node = cx.node(x);
    let w = cx.width_of(x);
    let p = if let Some(v) = cx.const_val(x) {
        if v.is_zero() {
            Vec::new()
        } else {
            vec![([0u8; MAX_LEAVES], v)]
        }
    } else {
        match node.op {
            OpCode::Add | OpCode::Sub => {
                let a = poly_of(cx, node.a, leaves, memo, steps)?;
                let b = poly_of(cx, node.b, leaves, memo, steps)?;
                let p = add(&a, &b, node.op == OpCode::Sub);
                (p.len() <= MAX_TERMS).then_some(p)?
            }
            OpCode::Neg => {
                let a = poly_of(cx, node.a, leaves, memo, steps)?;
                add(&Vec::new(), &a, true)
            }
            OpCode::Mul => {
                let a = poly_of(cx, node.a, leaves, memo, steps)?;
                let b = poly_of(cx, node.b, leaves, memo, steps)?;
                mul(&a, &b)?
            }
            OpCode::Shl if cx.const_val(node.b).is_some() => {
                let a = poly_of(cx, node.a, leaves, memo, steps)?;
                let s = cx.const_val(node.b)?;
                let k = BitVec::apply_bin(BinOp::Shl, &BitVec::one(w), &s).ok()?;
                mul(&a, &vec![([0u8; MAX_LEAVES], k)])?
            }
            _ => {
                let i = match leaves.iter().position(|&l| l == x) {
                    Some(i) => i,
                    None => {
                        if leaves.len() >= MAX_LEAVES {
                            return None;
                        }
                        leaves.push(x);
                        leaves.len() - 1
                    }
                };
                let mut m = [0u8; MAX_LEAVES];
                m[i] = 1;
                vec![(m, BitVec::one(w))]
            }
        }
    };
    memo.insert(x, p.clone());
    Some(p)
}

/// Whether `a` and `b` expand to the same polynomial (and at least one has a product, which is
/// what the linear forms do not expand).
pub(super) fn equal(r: &mut Runner<'_, '_>, cx: &Context, a: u32, b: u32) -> Result<bool, Stop> {
    let has_mul = |x: u32| {
        let mut stack = vec![x];
        let mut seen = 0;
        while let Some(i) = stack.pop() {
            seen += 1;
            if seen > 64 {
                return false;
            }
            let n = cx.node(i);
            if n.op == OpCode::Mul {
                return true;
            }
            if matches!(n.op, OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Shl) {
                stack.extend(n.children());
            }
        }
        false
    };
    if !has_mul(a) && !has_mul(b) {
        return Ok(false);
    }
    let mut leaves = Vec::new();
    let mut memo = IdMap::default();
    let mut steps = 0u32;
    let pa = poly_of(cx, a, &mut leaves, &mut memo, &mut steps);
    let pb = poly_of(cx, b, &mut leaves, &mut memo, &mut steps);
    r.meter.charge(Counter::PassWork, u64::from(steps))?;
    Ok(matches!((pa, pb), (Some(pa), Some(pb)) if pa == pb))
}
