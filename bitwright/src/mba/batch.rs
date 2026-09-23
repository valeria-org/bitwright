//! Batched evaluation: an [`MbaExpr`] compiled once into a straight-line program over lanes and
//! evaluated a block of points at a time. Lanes are `u64` for widths up to 64, `u128` up to 128,
//! and [`BitVec`] above; the loops are plain element-wise loops the compiler can vectorize, with
//! no `unsafe`. Used by the certificates, the solver and the evidence gate. It equals
//! [`MbaExpr::eval`] point for point (tested exhaustively at small widths).

use super::expr::{MOp, MbaExpr};
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// Points per block.
pub(crate) const BLOCK: usize = 256;

/// A value lane: one point's value of one node.
pub(crate) trait Lane: Copy + PartialEq + Default {
    /// What an operation needs to know about its width (a mask, or the width).
    type M: Copy;
    /// The width data for `w`.
    fn mask(w: Width) -> Self::M;
    /// `v` as a lane (its width fits the lane).
    fn from_bv(v: &BitVec) -> Self;
    /// The lane as a value of width `w`.
    fn to_bv(self, w: Width) -> BitVec;
    /// `v` mod 2^w.
    fn small(v: u64, m: Self::M) -> Self;
    /// `2^j` (zero when `j` is not below the width).
    fn pow2(j: u16, m: Self::M) -> Self;
    fn add(a: Self, b: Self, m: Self::M) -> Self;
    fn sub(a: Self, b: Self, m: Self::M) -> Self;
    fn mul(a: Self, b: Self, m: Self::M) -> Self;
    fn neg(a: Self, m: Self::M) -> Self;
    fn not(a: Self, m: Self::M) -> Self;
    fn and(a: Self, b: Self) -> Self;
    fn or(a: Self, b: Self) -> Self;
    fn xor(a: Self, b: Self) -> Self;
    fn shl(a: Self, k: u16, m: Self::M) -> Self;
    fn lshr(a: Self, k: u16) -> Self;
    fn zext(a: Self, to: Self::M) -> Self;
    fn sext(a: Self, from: Self::M, to: Self::M) -> Self;
    fn trunc(a: Self, to: Self::M) -> Self;
}

impl Lane for u64 {
    type M = u64;
    #[inline]
    fn mask(w: Width) -> u64 {
        if w.bits() >= 64 {
            u64::MAX
        } else {
            (1u64 << w.bits()) - 1
        }
    }
    #[inline]
    fn from_bv(v: &BitVec) -> u64 {
        v.limbs().first().copied().unwrap_or(0)
    }
    #[inline]
    fn to_bv(self, w: Width) -> BitVec {
        BitVec::wrapping_from_u64(w, self)
    }
    #[inline]
    fn small(v: u64, m: u64) -> u64 {
        v & m
    }
    #[inline]
    fn pow2(j: u16, m: u64) -> u64 {
        1u64.checked_shl(u32::from(j)).unwrap_or(0) & m
    }
    #[inline]
    fn add(a: u64, b: u64, m: u64) -> u64 {
        a.wrapping_add(b) & m
    }
    #[inline]
    fn sub(a: u64, b: u64, m: u64) -> u64 {
        a.wrapping_sub(b) & m
    }
    #[inline]
    fn mul(a: u64, b: u64, m: u64) -> u64 {
        a.wrapping_mul(b) & m
    }
    #[inline]
    fn neg(a: u64, m: u64) -> u64 {
        a.wrapping_neg() & m
    }
    #[inline]
    fn not(a: u64, m: u64) -> u64 {
        !a & m
    }
    #[inline]
    fn and(a: u64, b: u64) -> u64 {
        a & b
    }
    #[inline]
    fn or(a: u64, b: u64) -> u64 {
        a | b
    }
    #[inline]
    fn xor(a: u64, b: u64) -> u64 {
        a ^ b
    }
    #[inline]
    fn shl(a: u64, k: u16, m: u64) -> u64 {
        a.checked_shl(u32::from(k)).unwrap_or(0) & m
    }
    #[inline]
    fn lshr(a: u64, k: u16) -> u64 {
        a.checked_shr(u32::from(k)).unwrap_or(0)
    }
    #[inline]
    fn zext(a: u64, _: u64) -> u64 {
        a
    }
    #[inline]
    fn sext(a: u64, from: u64, to: u64) -> u64 {
        let sign = (from >> 1).wrapping_add(1);
        if a & sign != 0 { (a | !from) & to } else { a }
    }
    #[inline]
    fn trunc(a: u64, to: u64) -> u64 {
        a & to
    }
}

impl Lane for u128 {
    type M = u128;
    #[inline]
    fn mask(w: Width) -> u128 {
        if w.bits() >= 128 {
            u128::MAX
        } else {
            (1u128 << w.bits()) - 1
        }
    }
    #[inline]
    fn from_bv(v: &BitVec) -> u128 {
        let l = v.limbs();
        u128::from(l.first().copied().unwrap_or(0))
            | u128::from(l.get(1).copied().unwrap_or(0)) << 64
    }
    #[inline]
    fn to_bv(self, w: Width) -> BitVec {
        BitVec::wrapping_from_u128(w, self)
    }
    #[inline]
    fn small(v: u64, m: u128) -> u128 {
        u128::from(v) & m
    }
    #[inline]
    fn pow2(j: u16, m: u128) -> u128 {
        1u128.checked_shl(u32::from(j)).unwrap_or(0) & m
    }
    #[inline]
    fn add(a: u128, b: u128, m: u128) -> u128 {
        a.wrapping_add(b) & m
    }
    #[inline]
    fn sub(a: u128, b: u128, m: u128) -> u128 {
        a.wrapping_sub(b) & m
    }
    #[inline]
    fn mul(a: u128, b: u128, m: u128) -> u128 {
        a.wrapping_mul(b) & m
    }
    #[inline]
    fn neg(a: u128, m: u128) -> u128 {
        a.wrapping_neg() & m
    }
    #[inline]
    fn not(a: u128, m: u128) -> u128 {
        !a & m
    }
    #[inline]
    fn and(a: u128, b: u128) -> u128 {
        a & b
    }
    #[inline]
    fn or(a: u128, b: u128) -> u128 {
        a | b
    }
    #[inline]
    fn xor(a: u128, b: u128) -> u128 {
        a ^ b
    }
    #[inline]
    fn shl(a: u128, k: u16, m: u128) -> u128 {
        a.checked_shl(u32::from(k)).unwrap_or(0) & m
    }
    #[inline]
    fn lshr(a: u128, k: u16) -> u128 {
        a.checked_shr(u32::from(k)).unwrap_or(0)
    }
    #[inline]
    fn zext(a: u128, _: u128) -> u128 {
        a
    }
    #[inline]
    fn sext(a: u128, from: u128, to: u128) -> u128 {
        let sign = (from >> 1).wrapping_add(1);
        if a & sign != 0 { (a | !from) & to } else { a }
    }
    #[inline]
    fn trunc(a: u128, to: u128) -> u128 {
        a & to
    }
}

/// A lane of any width up to 512 bits: the value's limbs, always canonical (zero above the
/// width); every operation takes its width from the instruction, never from the lane, so a
/// lane can never carry a wrong width.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Wide(pub(crate) [u64; 8]);

impl Wide {
    fn bv(self, w: Width) -> BitVec {
        BitVec::wrapping_from_limbs(w, &self.0)
    }

    fn of(v: &BitVec) -> Wide {
        let mut l = [0u64; 8];
        for (d, s) in l.iter_mut().zip(v.limbs()) {
            *d = *s;
        }
        Wide(l)
    }
}

impl Lane for Wide {
    type M = Width;
    fn mask(w: Width) -> Width {
        w
    }
    fn from_bv(v: &BitVec) -> Wide {
        Wide::of(v)
    }
    fn to_bv(self, w: Width) -> BitVec {
        self.bv(w)
    }
    fn small(v: u64, w: Width) -> Wide {
        Wide::of(&BitVec::wrapping_from_u64(w, v))
    }
    fn pow2(j: u16, w: Width) -> Wide {
        let mut limbs = [0u64; 8];
        if j < w.bits()
            && let Some(l) = limbs.get_mut(usize::from(j / 64))
        {
            *l = 1u64 << (j % 64);
        }
        Wide(limbs)
    }
    fn add(a: Wide, b: Wide, w: Width) -> Wide {
        Wide::of(&BitVec::bin_unchecked(BinOp::Add, &a.bv(w), &b.bv(w)))
    }
    fn sub(a: Wide, b: Wide, w: Width) -> Wide {
        Wide::of(&BitVec::bin_unchecked(BinOp::Sub, &a.bv(w), &b.bv(w)))
    }
    fn mul(a: Wide, b: Wide, w: Width) -> Wide {
        Wide::of(&BitVec::bin_unchecked(BinOp::Mul, &a.bv(w), &b.bv(w)))
    }
    fn neg(a: Wide, w: Width) -> Wide {
        Wide::of(&BitVec::un_unchecked(UnOp::Neg, &a.bv(w)))
    }
    fn not(a: Wide, w: Width) -> Wide {
        Wide::of(&BitVec::un_unchecked(UnOp::Not, &a.bv(w)))
    }
    fn and(a: Wide, b: Wide) -> Wide {
        Wide(core::array::from_fn(|i| a.0[i] & b.0[i]))
    }
    fn or(a: Wide, b: Wide) -> Wide {
        Wide(core::array::from_fn(|i| a.0[i] | b.0[i]))
    }
    fn xor(a: Wide, b: Wide) -> Wide {
        Wide(core::array::from_fn(|i| a.0[i] ^ b.0[i]))
    }
    fn shl(a: Wide, k: u16, w: Width) -> Wide {
        let k = BitVec::wrapping_from_u64(w, u64::from(k));
        Wide::of(&BitVec::bin_unchecked(BinOp::Shl, &a.bv(w), &k))
    }
    fn lshr(a: Wide, k: u16) -> Wide {
        // The value is canonical, so shifting all 512 bits is shifting it at its width.
        let k = BitVec::wrapping_from_u64(Width::W512, u64::from(k));
        Wide::of(&BitVec::bin_unchecked(BinOp::LShr, &a.bv(Width::W512), &k))
    }
    fn zext(a: Wide, _: Width) -> Wide {
        a
    }
    fn sext(a: Wide, from: Width, to: Width) -> Wide {
        let v = a.bv(from);
        Wide::of(&v.sext(to).unwrap_or(v))
    }
    fn trunc(a: Wide, to: Width) -> Wide {
        Wide::of(&a.bv(to))
    }
}

/// Which lane type a program runs on.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    N64,
    N128,
    Wide,
}

impl Kind {
    /// The narrowest lane type holding `bits`.
    pub(crate) fn of(bits: u16) -> Kind {
        if bits <= 64 {
            Kind::N64
        } else if bits <= 128 {
            Kind::N128
        } else {
            Kind::Wide
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Op {
    Const(u32),
    Var(u32),
    Add,
    Sub,
    Mul,
    Neg,
    And,
    Or,
    Xor,
    Not,
    Shl(u16),
    LShr(u16),
    Zext,
    Sext(Width),
    Trunc,
}

#[derive(Copy, Clone, Debug)]
struct Ins {
    op: Op,
    w: Width,
    a: u32,
    b: u32,
}

/// An [`MbaExpr`] compiled for batched evaluation.
#[derive(Clone, Debug)]
pub(crate) struct Program {
    vars: Vec<Width>,
    ins: Vec<Ins>,
    consts: Vec<BitVec>,
    /// Each node's register (`u32::MAX` for a node the root does not use, unless every node
    /// was kept).
    reg: Vec<u32>,
    widest: u16,
}

impl Program {
    /// Compiles `m`: only the nodes the root uses, or every node with `all`. `None` for an
    /// expression with no nodes.
    pub(crate) fn new(m: &MbaExpr, all: bool) -> Option<Program> {
        let nodes = m.nodes();
        let root = nodes.len().checked_sub(1)?;
        let mut live = vec![all; nodes.len()];
        live[root] = true;
        for i in (0..nodes.len()).rev() {
            if live[i] {
                let n = &nodes[i];
                for &k in &n.args[..n.op.arity()] {
                    live[k as usize] = true;
                }
            }
        }
        let mut reg = vec![u32::MAX; nodes.len()];
        let mut ins = Vec::new();
        let mut consts = Vec::new();
        let mut widest = 1u16;
        for (i, n) in nodes.iter().enumerate() {
            if !live[i] {
                continue;
            }
            widest = widest.max(n.width.bits());
            let arg = |k: usize| reg[n.args[k] as usize];
            let (op, a, b) = match n.op {
                MOp::Const(v) => {
                    consts.push(v);
                    (Op::Const(consts.len() as u32 - 1), 0, 0)
                }
                MOp::Var(v) => (Op::Var(v), 0, 0),
                MOp::Add => (Op::Add, arg(0), arg(1)),
                MOp::Sub => (Op::Sub, arg(0), arg(1)),
                MOp::Mul => (Op::Mul, arg(0), arg(1)),
                MOp::And => (Op::And, arg(0), arg(1)),
                MOp::Or => (Op::Or, arg(0), arg(1)),
                MOp::Xor => (Op::Xor, arg(0), arg(1)),
                MOp::Neg => (Op::Neg, arg(0), 0),
                MOp::Not => (Op::Not, arg(0), 0),
                MOp::Shl(k) => (Op::Shl(k), arg(0), 0),
                MOp::LShr(k) => (Op::LShr(k), arg(0), 0),
                MOp::Zext => (Op::Zext, arg(0), 0),
                MOp::Sext => (Op::Sext(nodes[n.args[0] as usize].width), arg(0), 0),
                MOp::Trunc => (Op::Trunc, arg(0), 0),
            };
            reg[i] = ins.len() as u32;
            ins.push(Ins {
                op,
                w: n.width,
                a,
                b,
            });
        }
        for &w in m.vars() {
            widest = widest.max(w.bits());
        }
        Some(Program {
            vars: m.vars().to_vec(),
            ins,
            consts,
            reg,
            widest,
        })
    }

    /// The instructions (the nodes evaluated per point).
    pub(crate) fn len(&self) -> usize {
        self.ins.len()
    }

    /// The widest node or variable.
    pub(crate) fn widest(&self) -> u16 {
        self.widest
    }

    /// The register of node `i` (`None` if it was not kept).
    pub(crate) fn reg_of(&self, i: usize) -> Option<usize> {
        self.reg
            .get(i)
            .copied()
            .filter(|&r| r != u32::MAX)
            .map(|r| r as usize)
    }

    /// The root's register.
    pub(crate) fn root(&self) -> usize {
        self.ins.len().saturating_sub(1)
    }

    /// Evaluates `n` points: `inputs[v][p]` is variable `v` at point `p`; afterwards
    /// `regs[r][p]` is register `r` at point `p`. `regs` is resized as needed.
    pub(crate) fn run<L: Lane>(&self, regs: &mut Vec<Vec<L>>, inputs: &[Vec<L>], n: usize) {
        if regs.len() < self.ins.len() {
            regs.resize_with(self.ins.len(), Vec::new);
        }
        for (r, ins) in self.ins.iter().enumerate() {
            let (lo, hi) = regs.split_at_mut(r);
            let out = &mut hi[0];
            if out.len() < n {
                out.resize(n, L::default());
            }
            let out = &mut out[..n];
            let m = L::mask(ins.w);
            let a = || &lo[ins.a as usize][..n];
            let b = || &lo[ins.b as usize][..n];
            match ins.op {
                Op::Const(c) => out.fill(L::from_bv(&self.consts[c as usize])),
                Op::Var(v) => match inputs.get(v as usize) {
                    Some(col) if col.len() >= n => out.copy_from_slice(&col[..n]),
                    _ => out.fill(L::default()),
                },
                Op::Add => zip2(out, a(), b(), |x, y| L::add(x, y, m)),
                Op::Sub => zip2(out, a(), b(), |x, y| L::sub(x, y, m)),
                Op::Mul => zip2(out, a(), b(), |x, y| L::mul(x, y, m)),
                Op::And => zip2(out, a(), b(), L::and),
                Op::Or => zip2(out, a(), b(), L::or),
                Op::Xor => zip2(out, a(), b(), L::xor),
                Op::Neg => zip1(out, a(), |x| L::neg(x, m)),
                Op::Not => zip1(out, a(), |x| L::not(x, m)),
                Op::Shl(k) => zip1(out, a(), |x| L::shl(x, k, m)),
                Op::LShr(k) => zip1(out, a(), |x| L::lshr(x, k)),
                Op::Zext => zip1(out, a(), |x| L::zext(x, m)),
                Op::Sext(from) => {
                    let f = L::mask(from);
                    zip1(out, a(), |x| L::sext(x, f, m))
                }
                Op::Trunc => zip1(out, a(), |x| L::trunc(x, m)),
            }
        }
    }

    /// The root's value at each of the given points (`points[p][v]`: variable `v` at point
    /// `p`, of the variable's width). For tests and small uses; the certificates fill lanes
    /// directly.
    pub(crate) fn eval_points(&self, points: &[Vec<BitVec>]) -> Vec<BitVec> {
        match Kind::of(self.widest) {
            Kind::N64 => self.eval_points_in::<u64>(points),
            Kind::N128 => self.eval_points_in::<u128>(points),
            Kind::Wide => self.eval_points_in::<Wide>(points),
        }
    }

    fn eval_points_in<L: Lane>(&self, points: &[Vec<BitVec>]) -> Vec<BitVec> {
        let mut out = Vec::with_capacity(points.len());
        let mut regs: Vec<Vec<L>> = Vec::new();
        let w = self.ins.last().map_or(Width::W1, |i| i.w);
        for chunk in points.chunks(BLOCK) {
            let inputs: Vec<Vec<L>> = (0..self.vars.len())
                .map(|v| {
                    chunk
                        .iter()
                        .map(|p| p.get(v).map_or(L::default(), L::from_bv))
                        .collect()
                })
                .collect();
            self.run(&mut regs, &inputs, chunk.len());
            if let Some(root) = regs.get(self.root()) {
                out.extend(root[..chunk.len()].iter().map(|x| x.to_bv(w)));
            }
        }
        out
    }
}

#[inline]
fn zip1<L: Copy>(out: &mut [L], a: &[L], f: impl Fn(L) -> L) {
    for (o, &x) in out.iter_mut().zip(a) {
        *o = f(x);
    }
}

#[inline]
fn zip2<L: Copy>(out: &mut [L], a: &[L], b: &[L], f: impl Fn(L, L) -> L) {
    for ((o, &x), &y) in out.iter_mut().zip(a).zip(b) {
        *o = f(x, y);
    }
}
