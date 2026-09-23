//! Deterministic workloads: values, random expression DAGs, and MBA-shaped expressions.

use bitwright::{BinOp, BitVec, CmpOp, Context, Expr, SymbolKey, UnOp, Width};

/// SplitMix64: a small deterministic generator (no seeds from the OS or the clock).
#[derive(Clone, Debug)]
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed)
    }

    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n.max(1)
    }

    pub fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize]
    }
}

pub fn width(bits: u16) -> Width {
    Width::new(bits).expect("benchmark widths are valid")
}

/// A value of `w` bits: mostly random, a quarter boundary values (0, 1, all ones, sign bit).
pub fn value(rng: &mut Rng, w: Width) -> BitVec {
    let n = usize::from(w.bits()).div_ceil(64);
    match rng.below(8) {
        0 => BitVec::zero(w),
        1 => BitVec::one(w),
        _ => {
            let limbs: Vec<u64> = (0..n).map(|_| rng.next()).collect();
            BitVec::wrapping_from_limbs(w, &limbs)
        }
    }
}

/// `n` pairs of values of `w` bits.
pub fn value_pairs(seed: u64, w: Width, n: usize) -> Vec<(BitVec, BitVec)> {
    let mut rng = Rng::new(seed);
    (0..n)
        .map(|_| (value(&mut rng, w), value(&mut rng, w)))
        .collect()
}

/// Shape of a random DAG.
#[derive(Clone, Copy, Debug)]
pub struct Dag {
    pub width: Width,
    pub symbols: usize,
    /// Operator nodes to create (hash-consing may merge some).
    pub nodes: usize,
    /// Whether to use division, remainder and multiplication-high (slow, partial-looking
    /// operators) and data-dependent shifts.
    pub heavy_ops: bool,
}

/// Builds a random DAG in `cx` and returns one root that depends on most of it: operands come
/// mostly from recent nodes (depth) and sometimes from anywhere (sharing).
pub fn dag(cx: &mut Context, seed: u64, shape: Dag) -> Expr {
    let mut rng = Rng::new(seed);
    let w = shape.width;
    let mut pool: Vec<Expr> = (0..shape.symbols)
        .map(|i| {
            cx.symbol(SymbolKey::U64(i as u64), w)
                .expect("symbol of a valid width")
        })
        .collect();
    let light = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
    ];
    let heavy = [
        BinOp::UDiv,
        BinOp::URem,
        BinOp::SDiv,
        BinOp::UMulHi,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
        BinOp::RotL,
    ];
    let unary = [UnOp::Not, UnOp::Neg, UnOp::Popcnt, UnOp::Bswap];
    let operand = |rng: &mut Rng, pool: &[Expr]| -> Expr {
        let n = pool.len() as u64;
        if rng.below(4) == 0 {
            pool[rng.below(n) as usize]
        } else {
            pool[(n - 1 - rng.below(n.min(8))) as usize]
        }
    };
    for _ in 0..shape.nodes {
        let a = operand(&mut rng, &pool);
        let b = operand(&mut rng, &pool);
        let e = match rng.below(16) {
            0..=8 => cx.bin(rng.pick(&light), a, b),
            9 if shape.heavy_ops => cx.bin(rng.pick(&heavy), a, b),
            9 | 10 => {
                let k = value(&mut rng, w);
                let k = cx.constant(&k).expect("constant");
                cx.bin(rng.pick(&light), a, k)
            }
            11 => {
                let k = cx
                    .constant_u64(w, rng.below(u64::from(w.bits())))
                    .expect("shift count");
                cx.bin(rng.pick(&[BinOp::Shl, BinOp::LShr, BinOp::RotL]), a, k)
            }
            12 => cx.un(rng.pick(&unary), a),
            13 => {
                let c = cx
                    .cmp(rng.pick(&[CmpOp::Eq, CmpOp::Ult, CmpOp::Slt]), a, b)
                    .expect("comparison");
                let d = operand(&mut rng, &pool);
                cx.select(c, b, d)
            }
            14 if w.bits() > 1 => {
                let half = width(w.bits() / 2);
                let t = cx.trunc(a, half).expect("trunc");
                if rng.below(2) == 0 {
                    cx.zext(t, w)
                } else {
                    cx.sext(t, w)
                }
            }
            _ => cx.bin(BinOp::Xor, a, b),
        }
        .expect("benchmark DAG node");
        pool.push(e);
    }
    // Fold the most recent nodes into one root.
    let tail = pool.len().saturating_sub(16);
    let mut root = pool[tail];
    for &e in &pool[tail + 1..] {
        root = cx.bin(BinOp::Xor, root, e).expect("xor");
    }
    root
}

/// Linear mixed boolean-arithmetic expressions over `x` and `y` in the text syntax, each equal
/// to a simple target (as an obfuscator writes them), and the target.
pub fn mba_corpus(seed: u64, count: usize) -> Vec<String> {
    // Eight Boolean functions of (x, y) and their truth tables over (x, y) in 00, 01, 10, 11.
    const BASIS: [(&str, [i64; 4]); 8] = [
        ("(x & y)", [0, 0, 0, 1]),
        ("(x | y)", [0, 1, 1, 1]),
        ("(x ^ y)", [0, 1, 1, 0]),
        ("(x & ~y)", [0, 0, 1, 0]),
        ("(~x & y)", [0, 1, 0, 0]),
        ("~(x | y)", [1, 0, 0, 0]),
        ("x", [0, 0, 1, 1]),
        ("y", [0, 1, 0, 1]),
    ];
    let mut rng = Rng::new(seed);
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        // Random coefficients on a random subset; the sum is some linear MBA. Add a random
        // multiple of an identity that is zero (x ^ y) - (x | y) + (x & y) to hide it.
        let terms = 3 + rng.below(4) as usize;
        let mut parts = Vec::new();
        for _ in 0..terms {
            let (f, _) = BASIS[rng.below(8) as usize];
            let c = rng.below(9) as i64 - 4;
            if c != 0 {
                parts.push(format!("{c} * {f}"));
            }
        }
        let k = 1 + rng.below(5);
        parts.push(format!("{k} * ((x ^ y) - (x | y) + (x & y))"));
        out.push(parts.join(" + ").replace("+ -", "- "));
    }
    out
}
