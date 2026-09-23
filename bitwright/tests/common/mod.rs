//! Shared by the `heavy_*` suites: a seeded RNG, boundary values, a random DAG generator
//! paired with a reference DAG that `bitwright-ref` evaluates, environments, and honest
//! extension operations with independent reference definitions.
//!
//! Every suite has a `smoke` entry point (runs by default, fast in debug) and a `heavy` one
//! (`#[ignore]`, run nightly in release) sharing one body parameterized by [`Size`]. Seeds are
//! fixed; every failure message names the seed and the input so it can be replayed.

// Each test binary uses a different part of this module.
#![allow(dead_code)]

use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::sync::Arc;

use bitwright::ext::{ExtId, ExtOp, ExtSig, ExtTraits, Registry};
use bitwright::{
    BinOp, BitVec, CmpOpExt, Context, ContextConfig, Error, Expr, KnownBits, SymbolKey, UnOp, View,
    Width,
};
use bitwright_ref as r;

// ----- sizes ---------------------------------------------------------------------------------

/// How much work a property runs: `Smoke` by default, `Heavy` nightly (`--ignored`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Size {
    Smoke,
    Heavy,
}

impl Size {
    pub fn pick<T>(self, smoke: T, heavy: T) -> T {
        match self {
            Size::Smoke => smoke,
            Size::Heavy => heavy,
        }
    }
}

// ----- random numbers ------------------------------------------------------------------------

/// SplitMix64 with an explicit seed: no clock, no OS randomness.
#[derive(Clone, Debug)]
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// Uniform in `0..n` (`n > 0`).
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    pub fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }

    pub fn pick<T: Clone>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len() as u64) as usize].clone()
    }

    /// A value with every limb random.
    pub fn bitvec(&mut self, width: Width) -> BitVec {
        let limbs: Vec<u64> = (0..8).map(|_| self.next()).collect();
        BitVec::wrapping_from_limbs(width, &limbs)
    }

    /// A boundary value half the time, a random one otherwise.
    pub fn biased(&mut self, width: Width) -> BitVec {
        if self.chance(1, 2) {
            let b = boundary_values(width);
            self.pick(&b)
        } else {
            self.bitvec(width)
        }
    }
}

// ----- widths, conversions and operator maps -------------------------------------------------

/// Widths around every representation boundary: tiny, byte, word, the u64/u128 native paths
/// and the limb kernels up to the maximum.
pub const WIDTHS: [u16; 23] = [
    1, 2, 3, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257, 511, 512,
];

/// A subset of [`WIDTHS`] for debug-build smoke runs.
pub const SMOKE_WIDTHS: [u16; 9] = [1, 7, 8, 33, 64, 65, 128, 129, 512];

pub fn w(bits: u16) -> Width {
    Width::new(bits).unwrap_or_else(|e| panic!("width {bits}: {e}"))
}

pub fn to_ref(v: &BitVec) -> r::Bits {
    r::Bits::from_limbs(v.width().bits(), v.limbs())
}

pub fn from_ref(b: &r::Bits) -> BitVec {
    BitVec::wrapping_from_limbs(w(b.width()), &b.to_limbs())
}

pub fn ref_bool(b: bool) -> r::Bits {
    r::Bits::from_bools(vec![b])
}

pub fn ref_un(op: UnOp) -> r::UnOp {
    match op {
        UnOp::Not => r::UnOp::Not,
        UnOp::Neg => r::UnOp::Neg,
        UnOp::Popcnt => r::UnOp::Popcnt,
        UnOp::Clz => r::UnOp::Clz,
        UnOp::Ctz => r::UnOp::Ctz,
        UnOp::Bswap => r::UnOp::Bswap,
        UnOp::BitRev => r::UnOp::BitRev,
        other => panic!("unmapped unary operator {other:?}"),
    }
}

pub fn ref_bin(op: BinOp) -> r::BinOp {
    match op {
        BinOp::Add => r::BinOp::Add,
        BinOp::Sub => r::BinOp::Sub,
        BinOp::Mul => r::BinOp::Mul,
        BinOp::UMulHi => r::BinOp::UMulHi,
        BinOp::SMulHi => r::BinOp::SMulHi,
        BinOp::UDiv => r::BinOp::UDiv,
        BinOp::URem => r::BinOp::URem,
        BinOp::SDiv => r::BinOp::SDiv,
        BinOp::SRem => r::BinOp::SRem,
        BinOp::And => r::BinOp::And,
        BinOp::Or => r::BinOp::Or,
        BinOp::Xor => r::BinOp::Xor,
        BinOp::Shl => r::BinOp::Shl,
        BinOp::LShr => r::BinOp::LShr,
        BinOp::AShr => r::BinOp::AShr,
        BinOp::RotL => r::BinOp::RotL,
        BinOp::RotR => r::BinOp::RotR,
        BinOp::Pdep => r::BinOp::Pdep,
        BinOp::Pext => r::BinOp::Pext,
        other => panic!("unmapped binary operator {other:?}"),
    }
}

pub fn ref_cmp(op: CmpOpExt) -> r::CmpOp {
    match op {
        CmpOpExt::Eq => r::CmpOp::Eq,
        CmpOpExt::Ne => r::CmpOp::Ne,
        CmpOpExt::Ult => r::CmpOp::Ult,
        CmpOpExt::Ule => r::CmpOp::Ule,
        CmpOpExt::Ugt => r::CmpOp::Ugt,
        CmpOpExt::Uge => r::CmpOp::Uge,
        CmpOpExt::Slt => r::CmpOp::Slt,
        CmpOpExt::Sle => r::CmpOp::Sle,
        CmpOpExt::Sgt => r::CmpOp::Sgt,
        CmpOpExt::Sge => r::CmpOp::Sge,
        other => panic!("unmapped comparison {other:?}"),
    }
}

// ----- boundary values -----------------------------------------------------------------------

/// `2^k` at `width` (`k < width`).
pub fn pow2(width: Width, k: u16) -> BitVec {
    let mut l = [0u64; 8];
    l[usize::from(k / 64)] = 1 << (k % 64);
    BitVec::wrapping_from_limbs(width, &l)
}

/// Ones in bits `[lo, lo + n)` (clipped to the width).
pub fn ones_range(width: Width, lo: u16, n: u16) -> BitVec {
    let mut l = [0u64; 8];
    for i in lo..(lo + n).min(width.bits()) {
        l[usize::from(i / 64)] |= 1 << (i % 64);
    }
    BitVec::wrapping_from_limbs(width, &l)
}

fn add1(v: &BitVec) -> BitVec {
    BitVec::apply_bin(BinOp::Add, v, &BitVec::one(v.width())).unwrap()
}

fn sub1(v: &BitVec) -> BitVec {
    BitVec::apply_bin(BinOp::Sub, v, &BitVec::one(v.width())).unwrap()
}

/// The boundary values of a width, deduplicated and sorted: 0, 1, 2, all ones, all ones − 1,
/// the signed minimum and maximum and their neighbours, powers of two and their neighbours at
/// the interesting positions (1, the middle, the top, every limb boundary), alternating bit
/// patterns, values with only the bottom or only the top limb set, shift counts around the
/// width (W − 1, W, W + 1, 2W, 2W + 1), and a huge count (2^64 + 1).
pub fn boundary_values(width: Width) -> Vec<BitVec> {
    let n = width.bits();
    let mut v = vec![
        BitVec::zero(width),
        BitVec::one(width),
        BitVec::wrapping_from_u64(width, 2),
        BitVec::ones(width),
        sub1(&BitVec::ones(width)),
        BitVec::smin(width),
        add1(&BitVec::smin(width)),
        BitVec::smax(width),
        sub1(&BitVec::smax(width)),
    ];
    for k in [
        1,
        n / 2,
        n - 1,
        31,
        32,
        63,
        64,
        65,
        127,
        128,
        129,
        255,
        256,
        257,
        511,
    ] {
        if k < n {
            let p = pow2(width, k);
            v.push(sub1(&p));
            v.push(p);
            v.push(add1(&p));
        }
    }
    v.push(BitVec::wrapping_from_limbs(
        width,
        &[0x5555_5555_5555_5555; 8],
    ));
    v.push(BitVec::wrapping_from_limbs(
        width,
        &[0xaaaa_aaaa_aaaa_aaaa; 8],
    ));
    if n > 64 {
        // Only the bottom limb, and only the top limb.
        v.push(ones_range(width, 0, 64));
        let top = (n - 1) / 64 * 64;
        v.push(ones_range(width, top, n - top));
        v.push(BitVec::wrapping_from_limbs(width, &[1, 1])); // 2^64 + 1: a huge count
    }
    for c in [
        u64::from(n) - 1,
        u64::from(n),
        u64::from(n) + 1,
        2 * u64::from(n),
        2 * u64::from(n) + 1,
    ] {
        v.push(BitVec::wrapping_from_u64(width, c));
    }
    v.sort();
    v.dedup();
    v
}

/// A shorter list of boundary values (for cross products at the widest widths).
pub fn core_values(width: Width) -> Vec<BitVec> {
    let n = width.bits();
    let mut v = vec![
        BitVec::zero(width),
        BitVec::one(width),
        BitVec::wrapping_from_u64(width, 2),
        BitVec::ones(width),
        BitVec::smin(width),
        add1(&BitVec::smin(width)),
        BitVec::smax(width),
        BitVec::wrapping_from_limbs(width, &[0x5555_5555_5555_5555; 8]),
        BitVec::wrapping_from_u64(width, u64::from(n) - 1),
        BitVec::wrapping_from_u64(width, u64::from(n)),
        BitVec::wrapping_from_u64(width, u64::from(n) + 1),
    ];
    if n > 64 {
        v.push(ones_range(width, 0, 64));
        let top = (n - 1) / 64 * 64;
        v.push(ones_range(width, top, n - top));
        v.push(pow2(width, 64));
    }
    v.sort();
    v.dedup();
    v
}

// ----- the reference DAG and its generator ---------------------------------------------------

/// One node of the reference DAG: operands are indices of earlier nodes.
#[derive(Clone, Debug)]
pub enum RNode {
    Const(r::Bits),
    /// Symbol `k` of the generator's fixed list.
    Sym(usize),
    Un(UnOp, usize),
    Bin(BinOp, usize, usize),
    Cmp(CmpOpExt, usize, usize),
    Zext(usize, u16),
    Sext(usize, u16),
    /// `Extract(a, lo, len)`.
    Extract(usize, u16, u16),
    /// `Concat(hi, lo)`.
    Concat(usize, usize),
    Select(usize, usize, usize),
    /// Output `k` of an extension operation.
    Ext(ExtKind, usize, Vec<usize>),
}

/// What the generator may build.
#[derive(Clone, Debug)]
pub struct GenConfig {
    /// Widths of the fixed symbols `s0, s1, …`.
    pub syms: Vec<u16>,
    /// Widths intermediate nodes may take (cast targets, comparison operand widths).
    pub widths: Vec<u16>,
    /// Depth of a fresh subexpression.
    pub depth: u32,
    /// One in `share` subexpressions reuses an existing node of the width (0: never).
    pub share: u64,
    /// Build extension calls (the context must use [`registry`]).
    pub ext: bool,
    /// Only these binary operators (empty: all).
    pub bin_ops: Vec<BinOp>,
    /// Leaves are symbols (never constants) with this chance out of 8.
    pub sym_leaf: u64,
}

impl GenConfig {
    /// Small widths, suited to exhaustive checks: 2–3 symbols of at most `max_w` bits.
    pub fn small(rng: &mut Rng, max_w: u16, depth: u32) -> GenConfig {
        let n = 2 + rng.below(2) as usize;
        let syms = (0..n)
            .map(|_| 1 + rng.below(u64::from(max_w)) as u16)
            .collect();
        GenConfig {
            syms,
            widths: (1..=max_w).collect(),
            depth,
            share: 6,
            ext: false,
            bin_ops: Vec::new(),
            sym_leaf: 5,
        }
    }

    /// Mixed wide widths from [`WIDTHS`] (and the given ones).
    pub fn wide(rng: &mut Rng, widths: &[u16], depth: u32) -> GenConfig {
        let n = 1 + rng.below(3) as usize;
        let syms = (0..n).map(|_| rng.pick(widths)).collect();
        GenConfig {
            syms,
            widths: widths.to_vec(),
            depth,
            share: 6,
            ext: false,
            bin_ops: Vec::new(),
            sym_leaf: 5,
        }
    }

    /// Extension calls on or off (the context must use [`registry`] when on).
    pub fn with_ext(mut self, ext: bool) -> GenConfig {
        self.ext = ext;
        self
    }

    /// Total bits of the symbols (the size of an exhaustive enumeration).
    pub fn sym_bits(&self) -> u32 {
        self.syms.iter().map(|&b| u32::from(b)).sum()
    }
}

/// A DAG built in a context together with its reference twin.
#[derive(Debug)]
pub struct Dag {
    pub cfg: GenConfig,
    /// Symbol names (`s0`, `s1`, …) and widths.
    pub syms: Vec<(SymbolKey, Width)>,
    pub nodes: Vec<RNode>,
    /// The context expression built for each reference node (the canonical form may differ).
    pub exprs: Vec<Expr>,
    pub widths: Vec<u16>,
    by_width: BTreeMap<u16, Vec<usize>>,
    ext_ids: Vec<ExtId>,
}

impl Dag {
    /// A fresh generator over `cx`, which must have [`registry`] when `cfg.ext` is set.
    pub fn new(cx: &mut Context, cfg: GenConfig) -> Dag {
        let syms: Vec<(SymbolKey, Width)> = cfg
            .syms
            .iter()
            .enumerate()
            .map(|(k, &b)| (SymbolKey::from(format!("s{k}")), w(b)))
            .collect();
        let ext_ids = if cfg.ext {
            let reg = cx.registry().expect("ext DAGs need the test registry");
            ExtKind::ALL
                .iter()
                .map(|k| reg.id(k.name()).expect("registered"))
                .collect()
        } else {
            Vec::new()
        };
        let mut dag = Dag {
            cfg,
            syms,
            nodes: Vec::new(),
            exprs: Vec::new(),
            widths: Vec::new(),
            by_width: BTreeMap::new(),
            ext_ids,
        };
        for k in 0..dag.syms.len() {
            let (key, width) = dag.syms[k].clone();
            let e = cx.symbol(key, width).unwrap();
            dag.push(RNode::Sym(k), e, width.bits());
        }
        dag
    }

    fn push(&mut self, n: RNode, e: Expr, width: u16) -> usize {
        self.nodes.push(n);
        self.exprs.push(e);
        self.widths.push(width);
        let i = self.nodes.len() - 1;
        self.by_width.entry(width).or_default().push(i);
        i
    }

    /// A random expression of width `width`; returns its reference node index.
    pub fn random(&mut self, cx: &mut Context, rng: &mut Rng, width: u16) -> usize {
        let d = self.cfg.depth;
        self.node(cx, rng, width, d)
    }

    pub fn expr(&self, i: usize) -> Expr {
        self.exprs[i]
    }

    fn leaf(&mut self, cx: &mut Context, rng: &mut Rng, width: u16) -> usize {
        if !self.syms.is_empty() && rng.chance(self.cfg.sym_leaf, 8) {
            let k = rng.below(self.syms.len() as u64) as usize;
            return self.fit(cx, rng, k, width);
        }
        let v = rng.biased(w(width));
        let e = cx.constant(&v).unwrap();
        self.push(RNode::Const(to_ref(&v)), e, width)
    }

    /// Node `i` at `width`: itself, an extract of it, or an extension of it.
    fn fit(&mut self, cx: &mut Context, rng: &mut Rng, i: usize, width: u16) -> usize {
        let from = self.widths[i];
        let a = self.exprs[i];
        if from == width {
            i
        } else if from > width {
            let lo = rng.below(u64::from(from - width) + 1) as u16;
            let e = cx.extract(a, lo, w(width)).unwrap();
            self.push(RNode::Extract(i, lo, width), e, width)
        } else if rng.chance(1, 2) {
            let e = cx.zext(a, w(width)).unwrap();
            self.push(RNode::Zext(i, width), e, width)
        } else {
            let e = cx.sext(a, w(width)).unwrap();
            self.push(RNode::Sext(i, width), e, width)
        }
    }

    fn narrower(&self, rng: &mut Rng, width: u16) -> u16 {
        let c: Vec<u16> = self
            .cfg
            .widths
            .iter()
            .copied()
            .filter(|&x| x < width)
            .collect();
        if c.is_empty() || rng.chance(1, 4) {
            1 + rng.below(u64::from(width - 1)) as u16
        } else {
            rng.pick(&c)
        }
    }

    fn wider(&self, rng: &mut Rng, width: u16) -> Option<u16> {
        let c: Vec<u16> = self
            .cfg
            .widths
            .iter()
            .copied()
            .filter(|&x| x > width)
            .collect();
        (!c.is_empty()).then(|| rng.pick(&c))
    }

    fn node(&mut self, cx: &mut Context, rng: &mut Rng, width: u16, depth: u32) -> usize {
        if self.cfg.share > 0
            && rng.chance(1, self.cfg.share)
            && let Some(pool) = self.by_width.get(&width)
        {
            let pool = pool.clone();
            return rng.pick(&pool);
        }
        if depth == 0 || rng.chance(1, 8) {
            return self.leaf(cx, rng, width);
        }
        let d = depth - 1;
        loop {
            match rng.below(13) {
                0 | 1 => {
                    let op = rng.pick(&UnOp::ALL);
                    if op == UnOp::Bswap && !width.is_multiple_of(8) {
                        continue;
                    }
                    let a = self.node(cx, rng, width, d);
                    let e = cx.un(op, self.exprs[a]).unwrap();
                    return self.push(RNode::Un(op, a), e, width);
                }
                2..=6 => {
                    let op = if self.cfg.bin_ops.is_empty() {
                        rng.pick(&BinOp::ALL)
                    } else {
                        rng.pick(&self.cfg.bin_ops)
                    };
                    let a = self.node(cx, rng, width, d);
                    let b = if rng.chance(1, 8) {
                        a
                    } else {
                        self.node(cx, rng, width, d)
                    };
                    let e = cx.bin(op, self.exprs[a], self.exprs[b]).unwrap();
                    return self.push(RNode::Bin(op, a, b), e, width);
                }
                7 if width == 1 => {
                    let op = rng.pick(&CmpOpExt::ALL);
                    let ow = rng.pick(&self.cfg.widths);
                    let a = self.node(cx, rng, ow, d);
                    let b = if rng.chance(1, 8) {
                        a
                    } else {
                        self.node(cx, rng, ow, d)
                    };
                    let e = cx.cmp(op, self.exprs[a], self.exprs[b]).unwrap();
                    return self.push(RNode::Cmp(op, a, b), e, 1);
                }
                8 if width > 1 => {
                    let from = self.narrower(rng, width);
                    let a = self.node(cx, rng, from, d);
                    let ea = self.exprs[a];
                    return if rng.chance(1, 2) {
                        let e = cx.zext(ea, w(width)).unwrap();
                        self.push(RNode::Zext(a, width), e, width)
                    } else {
                        let e = cx.sext(ea, w(width)).unwrap();
                        self.push(RNode::Sext(a, width), e, width)
                    };
                }
                9 => {
                    let Some(from) = self.wider(rng, width) else {
                        continue;
                    };
                    // Low bits, high bits, a limb boundary, or anywhere.
                    let span = from - width;
                    let lo = match rng.below(4) {
                        0 => 0,
                        1 => span,
                        2 => [63u16, 64, 65, 127, 128, 129, 255, 256]
                            .into_iter()
                            .rfind(|&l| l <= span)
                            .unwrap_or(0),
                        _ => rng.below(u64::from(span) + 1) as u16,
                    };
                    let a = self.node(cx, rng, from, d);
                    let e = cx.extract(self.exprs[a], lo, w(width)).unwrap();
                    return self.push(RNode::Extract(a, lo, width), e, width);
                }
                10 if width > 1 => {
                    let hw = self.narrower(rng, width);
                    let h = self.node(cx, rng, hw, d);
                    let l = self.node(cx, rng, width - hw, d);
                    let e = cx.concat(self.exprs[h], self.exprs[l]).unwrap();
                    return self.push(RNode::Concat(h, l), e, width);
                }
                11 => {
                    let c = self.node(cx, rng, 1, d);
                    let t = self.node(cx, rng, width, d);
                    let f = if rng.chance(1, 8) {
                        t
                    } else {
                        self.node(cx, rng, width, d)
                    };
                    let e = cx
                        .select(self.exprs[c], self.exprs[t], self.exprs[f])
                        .unwrap();
                    return self.push(RNode::Select(c, t, f), e, width);
                }
                12 if self.cfg.ext => {
                    if let Some(i) = self.ext_node(cx, rng, width, d) {
                        return i;
                    }
                }
                _ => {}
            }
        }
    }

    /// A call of a random extension operation with an output of `width`; every output is
    /// recorded (so later nodes share them).
    fn ext_node(&mut self, cx: &mut Context, rng: &mut Rng, width: u16, d: u32) -> Option<usize> {
        let mut choices: Vec<(ExtKind, usize)> = vec![
            (ExtKind::AddC, 0),
            (ExtKind::DivMod, rng.below(4) as usize),
            (ExtKind::Flags, 0),
            (ExtKind::Flags, 7),
            (ExtKind::Mix, 0),
        ];
        if width <= 256 {
            choices.push((ExtKind::Fsh, rng.below(2) as usize));
        }
        if width == 1 {
            choices.push((ExtKind::AddC, 1 + rng.below(2) as usize));
            choices.push((ExtKind::Flags, 1 + rng.below(6) as usize));
        }
        let (kind, k) = rng.pick(&choices);
        // Argument widths: the operand width `aw` is `width` unless the output is a 1-bit flag,
        // whose operands may have any width.
        let aw = if kind.output_width(k, 2) == 2 {
            width
        } else {
            rng.pick(&self.cfg.widths)
        };
        let arg_widths: Vec<u16> = match kind {
            ExtKind::AddC => vec![aw, aw, 1],
            ExtKind::DivMod | ExtKind::Flags => vec![aw, aw],
            ExtKind::Fsh => vec![aw, aw, rng.pick(&self.cfg.widths)],
            ExtKind::Mix => vec![aw],
        };
        if kind == ExtKind::Fsh && aw > 256 {
            return None;
        }
        let args: Vec<usize> = arg_widths
            .iter()
            .map(|&aw| self.node(cx, rng, aw, d))
            .collect();
        let exprs: Vec<Expr> = args.iter().map(|&a| self.exprs[a]).collect();
        let id = self.ext_ids[kind as usize];
        let outs = cx.ext(id, &exprs).unwrap();
        let mut chosen = None;
        for (j, &e) in outs.iter().enumerate() {
            let ow = kind.output_width(j, aw);
            let i = self.push(RNode::Ext(kind, j, args.clone()), e, ow);
            if j == k {
                chosen = Some(i);
            }
        }
        let i = chosen.expect("output exists");
        assert_eq!(self.widths[i], width, "{kind:?}[{k}] at {aw}");
        Some(i)
    }

    /// The reference value of every node under `env` (one value per symbol).
    pub fn eval_ref(&self, env: &[BitVec]) -> Vec<r::Bits> {
        let mut v: Vec<r::Bits> = Vec::with_capacity(self.nodes.len());
        for n in &self.nodes {
            let x = match n {
                RNode::Const(b) => b.clone(),
                RNode::Sym(k) => to_ref(&env[*k]),
                RNode::Un(op, a) => r::un(ref_un(*op), &v[*a]).expect("bswap at byte widths"),
                RNode::Bin(op, a, b) => r::bin(ref_bin(*op), &v[*a], &v[*b]),
                RNode::Cmp(op, a, b) => ref_bool(r::cmp(ref_cmp(*op), &v[*a], &v[*b])),
                RNode::Zext(a, to) => r::zext(&v[*a], *to),
                RNode::Sext(a, to) => r::sext(&v[*a], *to),
                RNode::Extract(a, lo, n) => r::extract(&v[*a], *lo, *n),
                RNode::Concat(h, l) => r::concat(&v[*h], &v[*l]),
                RNode::Select(c, t, f) => r::select(&v[*c], &v[*t], &v[*f]),
                RNode::Ext(kind, k, args) => {
                    let a: Vec<&r::Bits> = args.iter().map(|&i| &v[i]).collect();
                    kind.eval_ref(&a)[*k].clone()
                }
            };
            v.push(x);
        }
        v
    }

    /// `env` as a symbol binding for [`Context::eval`].
    pub fn binding(&self, env: &[BitVec]) -> Vec<(SymbolKey, BitVec)> {
        self.syms
            .iter()
            .zip(env)
            .map(|((k, _), v)| (k.clone(), *v))
            .collect()
    }

    /// Every assignment of the symbols, if there are at most `2^max_bits`.
    pub fn every_env(&self, max_bits: u32) -> Option<Vec<Vec<BitVec>>> {
        every_env(&self.syms, max_bits)
    }

    /// One environment: boundary values or random ones.
    pub fn boundary_env(&self, rng: &mut Rng) -> Vec<BitVec> {
        self.syms.iter().map(|(_, sw)| rng.biased(*sw)).collect()
    }

    /// Describes an environment for failure messages.
    pub fn show_env(&self, env: &[BitVec]) -> String {
        let mut s = String::new();
        for ((k, _), v) in self.syms.iter().zip(env) {
            let _ = write!(s, "{k:?} = {v}; ");
        }
        s
    }
}

/// Every assignment of symbols of the given widths, if there are at most `2^max_bits`.
pub fn every_env(syms: &[(SymbolKey, Width)], max_bits: u32) -> Option<Vec<Vec<BitVec>>> {
    let bits: u32 = syms.iter().map(|(_, sw)| u32::from(sw.bits())).sum();
    if bits > max_bits || bits > 24 {
        return None;
    }
    Some(
        (0..(1u64 << bits))
            .map(|code| {
                let mut c = code;
                syms.iter()
                    .map(|(_, sw)| {
                        let v = BitVec::wrapping_from_u64(*sw, c);
                        c >>= sw.bits();
                        v
                    })
                    .collect()
            })
            .collect(),
    )
}

/// Checks that the context evaluates every node of `dag` to its reference value under `env`.
pub fn assert_matches_reference(cx: &mut Context, dag: &Dag, env: &[BitVec], what: &str) {
    let got = cx.eval(&dag.exprs, &dag.binding(env)[..]).unwrap();
    let want = dag.eval_ref(env);
    for (i, (g, r)) in got.iter().zip(&want).enumerate() {
        if g.limbs() != &r.to_limbs()[..] {
            panic!(
                "{what}: node {i} ({:?}) evaluates to {g}, the reference says {}\n  expr: {}\n  env: {}",
                dag.nodes[i],
                from_ref(r),
                cx.display(dag.exprs[i]),
                dag.show_env(env)
            );
        }
    }
}

/// Whether `a` and `b` agree at every environment in `envs` (the symbols of `dag`); the first
/// disagreeing environment otherwise.
pub fn first_difference(
    cx: &mut Context,
    dag: &Dag,
    a: Expr,
    b: Expr,
    envs: &[Vec<BitVec>],
) -> Option<Vec<BitVec>> {
    for env in envs {
        let v = cx.eval(&[a, b], &dag.binding(env)[..]).unwrap();
        if v[0] != v[1] {
            return Some(env.clone());
        }
    }
    None
}

/// Exhaustive environments when small, else `samples` boundary-biased ones.
pub fn envs_for(dag: &Dag, rng: &mut Rng, max_bits: u32, samples: usize) -> Vec<Vec<BitVec>> {
    dag.every_env(max_bits)
        .unwrap_or_else(|| (0..samples).map(|_| dag.boundary_env(rng)).collect())
}

// ----- the reference over a context's own DAG ------------------------------------------------

/// A context's canonical DAG under some roots, evaluated node by node with `bitwright-ref`
/// (never with the context's evaluator). Used as the oracle for results the generator did not
/// build itself: simplified expressions, substitutions, imported scripts.
#[derive(Debug)]
pub struct Canonical {
    nodes: Vec<(Expr, View, u16)>,
    index: HashMap<Expr, usize>,
    keys: Vec<Option<SymbolKey>>,
    ext: Vec<Option<ExtKind>>,
    roots: Vec<Expr>,
}

impl Canonical {
    pub fn new(cx: &mut Context, roots: &[Expr]) -> Canonical {
        let order = cx.post_order(roots).unwrap();
        let mut nodes = Vec::with_capacity(order.len());
        let mut index = HashMap::new();
        let mut keys = Vec::with_capacity(order.len());
        let mut ext = Vec::with_capacity(order.len());
        for e in order {
            let view = cx.view(e).unwrap();
            keys.push(match view {
                View::Sym(id) => Some(cx.symbol_key(id).unwrap().clone()),
                _ => None,
            });
            ext.push(match view {
                View::Ext { op, .. } => {
                    let name = cx.registry().unwrap().op(op).unwrap().name().to_string();
                    Some(ExtKind::from_name(&name).expect("a test operation"))
                }
                _ => None,
            });
            index.insert(e, nodes.len());
            nodes.push((e, view, cx.width(e).unwrap().bits()));
        }
        Canonical {
            nodes,
            index,
            keys,
            ext,
            roots: roots.to_vec(),
        }
    }

    /// The number of distinct nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// The roots' values under `env` (symbols by key), with the nodes in `overrides` taking the
    /// given values instead of their own.
    pub fn eval(&self, env: &[(SymbolKey, BitVec)], overrides: &[(Expr, r::Bits)]) -> Vec<r::Bits> {
        let mut v: Vec<r::Bits> = Vec::with_capacity(self.nodes.len());
        let at = |v: &Vec<r::Bits>, e: &Expr| v[self.index[e]].clone();
        for (k, (e, view, width)) in self.nodes.iter().enumerate() {
            if let Some((_, o)) = overrides.iter().find(|(t, _)| t == e) {
                v.push(o.clone());
                continue;
            }
            let x = match view {
                View::Const(c) => to_ref(c),
                View::Sym(_) => {
                    let key = self.keys[k].as_ref().unwrap();
                    let (_, val) = env
                        .iter()
                        .find(|(kk, _)| kk == key)
                        .unwrap_or_else(|| panic!("no value for {key:?}"));
                    to_ref(val)
                }
                View::Un(op, a) => r::un(ref_un(*op), &at(&v, a)).unwrap(),
                View::Bin(op, a, b) => r::bin(ref_bin(*op), &at(&v, a), &at(&v, b)),
                View::Cmp(op, a, b) => {
                    ref_bool(r::cmp(ref_cmp((*op).into()), &at(&v, a), &at(&v, b)))
                }
                View::Zext(a) => r::zext(&at(&v, a), *width),
                View::Sext(a) => r::sext(&at(&v, a), *width),
                View::Extract { lo, src } => r::extract(&at(&v, src), *lo, *width),
                View::Concat { hi, lo } => r::concat(&at(&v, hi), &at(&v, lo)),
                View::Select { cond, then, els } => {
                    r::select(&at(&v, cond), &at(&v, then), &at(&v, els))
                }
                View::Ext { output, args, .. } => {
                    let a: Vec<r::Bits> = args.as_slice().iter().map(|x| at(&v, x)).collect();
                    let a: Vec<&r::Bits> = a.iter().collect();
                    self.ext[k].unwrap().eval_ref(&a)[usize::from(*output)].clone()
                }
                other => panic!("unexpected node {other:?}"),
            };
            v.push(x);
        }
        self.roots.iter().map(|e| at(&v, e)).collect()
    }
}

/// Whether the reference values of `a` and `b` differ anywhere in `envs`; the first
/// environment where they do.
pub fn reference_difference(
    cx: &mut Context,
    a: Expr,
    b: Expr,
    envs: &[Vec<(SymbolKey, BitVec)>],
) -> Option<usize> {
    let dag = Canonical::new(cx, &[a, b]);
    envs.iter().position(|env| {
        let v = dag.eval(env, &[]);
        v[0] != v[1]
    })
}

// ----- honest extension operations -------------------------------------------------------------

/// The test registry's operations. Each has a host implementation (over `BitVec`, as a user
/// would write it) and an independent reference definition over `bitwright-ref` bits.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ExtKind {
    /// `(a: W, b: W, cin: 1) -> (sum: W, carry: 1, overflow: 1)`; commutative in `a`, `b`.
    AddC = 0,
    /// `(a: W, b: W) -> (udiv, urem, sdiv, srem)`, with an SMT-LIB term per output.
    DivMod = 1,
    /// `(hi: W, lo: W, count: C) -> (shld, shrd)` by `count mod W`, `W <= 256`.
    Fsh = 2,
    /// `(a: W, b: W) -> (diff, cf, zf, sf, of, pf, af, popcnt(diff))` of `a - b`: 8 outputs.
    Flags = 3,
    /// `(a: W) -> (a * K) ^ rotl(a, 1)`, opaque to the simplifier.
    Mix = 4,
}

impl ExtKind {
    pub const ALL: [ExtKind; 5] = [
        ExtKind::AddC,
        ExtKind::DivMod,
        ExtKind::Fsh,
        ExtKind::Flags,
        ExtKind::Mix,
    ];

    pub fn from_name(name: &str) -> Option<ExtKind> {
        ExtKind::ALL.into_iter().find(|k| k.name() == name)
    }

    pub fn name(self) -> &'static str {
        match self {
            ExtKind::AddC => "hv.addc",
            ExtKind::DivMod => "hv.divmod",
            ExtKind::Fsh => "hv.fsh",
            ExtKind::Flags => "hv.flags",
            ExtKind::Mix => "hv.mix",
        }
    }

    /// The width of output `k` when the value operands are `aw` bits.
    pub fn output_width(self, k: usize, aw: u16) -> u16 {
        match (self, k) {
            (ExtKind::AddC, 0) | (ExtKind::DivMod, _) | (ExtKind::Fsh, _) | (ExtKind::Mix, _) => aw,
            (ExtKind::Flags, 0 | 7) => aw,
            _ => 1,
        }
    }

    /// The reference definition, over bits.
    pub fn eval_ref(self, a: &[&r::Bits]) -> Vec<r::Bits> {
        let n = a[0].width();
        let msb = |x: &r::Bits| x.bit(x.width() - 1);
        match self {
            ExtKind::AddC => {
                let cin = r::zext(a[2], n);
                let s1 = r::bin(r::BinOp::Add, a[0], a[1]);
                let s = r::bin(r::BinOp::Add, &s1, &cin);
                let carry = r::cmp(r::CmpOp::Ult, &s1, a[0]) || r::cmp(r::CmpOp::Ult, &s, &s1);
                let overflow = msb(a[0]) == msb(a[1]) && msb(&s) != msb(a[0]);
                vec![s, ref_bool(carry), ref_bool(overflow)]
            }
            ExtKind::DivMod => [
                r::BinOp::UDiv,
                r::BinOp::URem,
                r::BinOp::SDiv,
                r::BinOp::SRem,
            ]
            .iter()
            .map(|&op| r::bin(op, a[0], a[1]))
            .collect(),
            ExtKind::Fsh => {
                // count mod W by Horner over the count's bits.
                let m = (0..a[2].width()).rev().fold(0u32, |acc, i| {
                    (2 * acc + u32::from(a[2].bit(i))) % u32::from(n)
                });
                let cat = r::concat(a[0], a[1]);
                let sh = r::Bits::from_u128(2 * n, u128::from(m));
                let left = r::extract(&r::bin(r::BinOp::Shl, &cat, &sh), n, n);
                let right = r::extract(&r::bin(r::BinOp::LShr, &cat, &sh), 0, n);
                vec![left, right]
            }
            ExtKind::Flags => {
                let d = r::bin(r::BinOp::Sub, a[0], a[1]);
                let cf = r::cmp(r::CmpOp::Ult, a[0], a[1]);
                let zf = d == r::Bits::zero(n);
                let sf = msb(&d);
                let of = msb(a[0]) != msb(a[1]) && msb(&d) != msb(a[0]);
                let low = n.min(8);
                let pf = (0..low).filter(|&i| d.bit(i)).count() % 2 == 0;
                let k = n.min(4);
                let af = r::cmp(
                    r::CmpOp::Ult,
                    &r::extract(a[0], 0, k),
                    &r::extract(a[1], 0, k),
                );
                let pop = r::un(r::UnOp::Popcnt, &d).unwrap();
                vec![
                    d,
                    ref_bool(cf),
                    ref_bool(zf),
                    ref_bool(sf),
                    ref_bool(of),
                    ref_bool(pf),
                    ref_bool(af),
                    pop,
                ]
            }
            ExtKind::Mix => {
                let k = r::Bits::from_u128(n, MIX_K);
                let m = r::bin(r::BinOp::Mul, a[0], &k);
                let rot = r::bin(r::BinOp::RotL, a[0], &r::Bits::from_u128(n, 1));
                vec![r::bin(r::BinOp::Xor, &m, &rot)]
            }
        }
    }
}

const MIX_K: u128 = 0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c834;

fn bin(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::apply_bin(op, a, b).unwrap()
}

fn lt(a: &BitVec, b: &BitVec) -> bool {
    BitVec::apply_cmp(CmpOpExt::Ult, a, b).unwrap()
}

struct AddC;

impl ExtOp for AddC {
    fn name(&self) -> &str {
        ExtKind::AddC.name()
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b, c] if a == b && c.bits() == 1 => Ok(ExtSig::new(&[
                ("sum", *a),
                ("carry", Width::W1),
                ("overflow", Width::W1),
            ])),
            _ => Err("a, b of one width and a 1-bit carry in".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let wd = args[0].width();
        let cin = args[2].zext(wd).unwrap();
        let s1 = bin(BinOp::Add, &args[0], &args[1]);
        let s = bin(BinOp::Add, &s1, &cin);
        out[1] = BitVec::from_bool(lt(&s1, &args[0]) || lt(&s, &s1));
        out[2] = BitVec::from_bool(args[0].msb() == args[1].msb() && s.msb() != args[0].msb());
        out[0] = s;
    }
    fn known_bits(&self, args: &[KnownBits], out: &mut [KnownBits]) {
        // The sum's low bit is the parity of the three low bits, when all are known.
        let bits: Option<Vec<bool>> = args.iter().map(|k| k.bit(0)).collect();
        if let Some(b) = bits {
            let wd = args[0].width();
            let odd = b.iter().filter(|x| **x).count() % 2 == 1;
            let low = BitVec::one(wd);
            let (zero, one) = if odd {
                (BitVec::zero(wd), low)
            } else {
                (low, BitVec::zero(wd))
            };
            out[0] = KnownBits::new(zero, one).unwrap();
        }
    }
    fn expand(&self, cx: &mut Context, args: &[Expr]) -> Option<Result<Vec<Expr>, Error>> {
        Some((|| {
            let wd = cx.width(args[0])?;
            let cin = cx.zext(args[2], wd)?;
            let s1 = cx.add(args[0], args[1])?;
            let s = cx.add(s1, cin)?;
            let c1 = cx.add_carry(args[0], args[1])?;
            let c2 = cx.add_carry(s1, cin)?;
            let carry = cx.or(c1, c2)?;
            let top = wd.bits() - 1;
            let (sa, sb, ss) = (
                cx.bit(args[0], top)?,
                cx.bit(args[1], top)?,
                cx.bit(s, top)?,
            );
            let same = cx.xnor(sa, sb)?;
            let flipped = cx.xor(ss, sa)?;
            let overflow = cx.and(same, flipped)?;
            Ok(vec![s, carry, overflow])
        })())
    }
    fn traits(&self) -> ExtTraits {
        ExtTraits::default().with_commutative(true)
    }
}

struct DivMod;

impl ExtOp for DivMod {
    fn name(&self) -> &str {
        ExtKind::DivMod.name()
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b] if a == b => Ok(ExtSig::new(&[
                ("udiv", *a),
                ("urem", *a),
                ("sdiv", *a),
                ("srem", *a),
            ])),
            _ => Err("two operands of one width".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        for (o, op) in out
            .iter_mut()
            .zip([BinOp::UDiv, BinOp::URem, BinOp::SDiv, BinOp::SRem])
        {
            *o = bin(op, &args[0], &args[1]);
        }
    }
    fn smtlib(&self, output: u8, args: &[&str], _widths: &[Width]) -> Option<String> {
        let f = ["bvudiv", "bvurem", "bvsdiv", "bvsrem"][usize::from(output)];
        Some(format!("({f} {} {})", args[0], args[1]))
    }
}

struct Fsh;

impl ExtOp for Fsh {
    fn name(&self) -> &str {
        ExtKind::Fsh.name()
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [h, l, _] if h == l && h.bits() <= 256 => {
                Ok(ExtSig::new(&[("shld", *h), ("shrd", *h)]))
            }
            _ => Err("hi, lo of one width up to 256 bits, and a count".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let n = args[0].width();
        let c = &args[2];
        let cw = w(c.width().bits().max(16));
        let m = bin(
            BinOp::URem,
            &c.zext(cw).unwrap(),
            &BitVec::from_u64(cw, u64::from(n.bits())).unwrap(),
        )
        .to_u64()
        .unwrap();
        let cat = BitVec::concat(&args[0], &args[1]).unwrap();
        let sh = BitVec::from_u64(cat.width(), m).unwrap();
        out[0] = bin(BinOp::Shl, &cat, &sh).extract(n.bits(), n).unwrap();
        out[1] = bin(BinOp::LShr, &cat, &sh).trunc(n).unwrap();
    }
}

struct Flags;

impl ExtOp for Flags {
    fn name(&self) -> &str {
        ExtKind::Flags.name()
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b] if a == b => {
                let one = Width::W1;
                Ok(ExtSig::new(&[
                    ("diff", *a),
                    ("cf", one),
                    ("zf", one),
                    ("sf", one),
                    ("of", one),
                    ("pf", one),
                    ("af", one),
                    ("pop", *a),
                ]))
            }
            _ => Err("two operands of one width".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let (a, b) = (&args[0], &args[1]);
        let n = a.width().bits();
        let d = bin(BinOp::Sub, a, b);
        let low = d.trunc(w(n.min(8))).unwrap();
        let pop_low = BitVec::apply_un(UnOp::Popcnt, &low).unwrap();
        let k = w(n.min(4));
        out[1] = BitVec::from_bool(lt(a, b));
        out[2] = BitVec::from_bool(d.is_zero());
        out[3] = BitVec::from_bool(d.msb());
        out[4] = BitVec::from_bool(a.msb() != b.msb() && d.msb() != a.msb());
        out[5] = BitVec::from_bool(pop_low.bit(0) == Some(false));
        out[6] = BitVec::from_bool(lt(&a.trunc(k).unwrap(), &b.trunc(k).unwrap()));
        out[7] = BitVec::apply_un(UnOp::Popcnt, &d).unwrap();
        out[0] = d;
    }
    fn known_bits(&self, args: &[KnownBits], out: &mut [KnownBits]) {
        // popcnt(diff) <= W: the bits above W's bit length are zero.
        let wd = args[0].width();
        let n = wd.bits();
        let len = 16 - n.leading_zeros() as u16;
        if len < n {
            let zero = BitVec::apply_un(UnOp::Not, &ones_range(wd, 0, len)).unwrap();
            out[7] = KnownBits::new(zero, BitVec::zero(wd)).unwrap();
        }
    }
}

struct Mix;

impl ExtOp for Mix {
    fn name(&self) -> &str {
        ExtKind::Mix.name()
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a] => Ok(ExtSig::new(&[("h", *a)])),
            _ => Err("one operand".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let wd = args[0].width();
        let k = BitVec::wrapping_from_u128(wd, MIX_K);
        let rot = bin(BinOp::RotL, &args[0], &BitVec::one(wd));
        out[0] = bin(BinOp::Xor, &bin(BinOp::Mul, &args[0], &k), &rot);
    }
    fn traits(&self) -> ExtTraits {
        ExtTraits::default().with_opaque(true)
    }
}

/// The registry of the test operations, registered (with the contract self-test) once per test
/// binary.
pub fn registry() -> Arc<Registry> {
    static REGISTRY: std::sync::OnceLock<Arc<Registry>> = std::sync::OnceLock::new();
    REGISTRY
        .get_or_init(|| {
            Arc::new(
                Registry::builder()
                    .register(AddC)
                    .unwrap()
                    .register(DivMod)
                    .unwrap()
                    .register(Fsh)
                    .unwrap()
                    .register(Flags)
                    .unwrap()
                    .register(Mix)
                    .unwrap()
                    .build(),
            )
        })
        .clone()
}

/// A context with the test registry.
pub fn ext_context(registry: &Arc<Registry>) -> Context {
    Context::with_registry(ContextConfig::default(), registry.clone())
}

/// A context with `config` and the test registry.
pub fn test_context(config: ContextConfig) -> Context {
    Context::with_registry(config, registry())
}
