//! Shared test utilities: a seeded RNG and a generator of random expressions paired with
//! reference terms.

use crate::{BinOp, BitVec, CmpOpExt, Context, Expr, UnOp, Width};
use bitwright_ref as r;

pub(crate) struct Rng(pub(crate) u64);

impl Rng {
    pub(crate) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    pub(crate) fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    pub(crate) fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }
}

pub(crate) fn ref_un(op: UnOp) -> r::UnOp {
    match op {
        UnOp::Not => r::UnOp::Not,
        UnOp::Neg => r::UnOp::Neg,
        UnOp::Popcnt => r::UnOp::Popcnt,
        UnOp::Clz => r::UnOp::Clz,
        UnOp::Ctz => r::UnOp::Ctz,
        UnOp::Bswap => r::UnOp::Bswap,
        UnOp::BitRev => r::UnOp::BitRev,
    }
}

pub(crate) fn ref_bin(op: BinOp) -> r::BinOp {
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
    }
}

pub(crate) fn ref_cmp(op: CmpOpExt) -> r::CmpOp {
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
    }
}

pub(crate) fn width(w: u16) -> Width {
    Width::new(w).unwrap()
}

/// Symbols: `v{k}_{w}` for k in 0..3, at any width. The reference environment index is
/// assigned on first use.
pub(crate) struct Gen {
    pub(crate) rng: Rng,
    pub(crate) max_w: u16,
    pub(crate) vars: Vec<(String, u16)>,
}

impl Gen {
    pub(crate) fn var_index(&mut self, name: &str, w: u16) -> usize {
        if let Some(i) = self.vars.iter().position(|(n, _)| n == name) {
            return i;
        }
        self.vars.push((name.to_string(), w));
        self.vars.len() - 1
    }

    pub(crate) fn constant(&mut self, w: u16) -> BitVec {
        let width = width(w);
        match self.rng.below(6) {
            0 => BitVec::zero(width),
            1 => BitVec::one(width),
            2 => BitVec::ones(width),
            3 => BitVec::smin(width),
            _ => {
                // Random in every limb, so wide widths get random high bits too.
                let limbs: Vec<u64> = (0..8).map(|_| self.rng.next()).collect();
                BitVec::wrapping_from_limbs(width, &limbs)
            }
        }
    }

    /// Builds a random expression of width `w` in `cx` and the same expression as a
    /// reference term (with no canonicalization).
    pub(crate) fn expr(&mut self, cx: &mut Context, w: u16, depth: u32) -> (Expr, r::Term) {
        if depth == 0 || self.rng.chance(1, 5) {
            if self.rng.chance(1, 3) {
                let v = self.constant(w);
                let e = cx.constant(&v).unwrap();
                let t = r::Term::Const(r::Bits::from_limbs(w, v.limbs()));
                return (e, t);
            }
            let name = format!("v{}_{}", self.rng.below(3), w);
            let e = cx.symbol(name.as_str(), width(w)).unwrap();
            let idx = self.var_index(&name, w);
            return (e, r::Term::Var(idx, w));
        }
        let d = depth - 1;
        loop {
            match self.rng.below(10) {
                0 => {
                    let op = UnOp::ALL[self.rng.below(7) as usize];
                    if op == UnOp::Bswap && !w.is_multiple_of(8) {
                        continue;
                    }
                    let (a, ta) = self.expr(cx, w, d);
                    let e = cx.un(op, a).unwrap();
                    return (e, r::Term::Un(ref_un(op), Box::new(ta)));
                }
                1..=4 => {
                    let op = BinOp::ALL[self.rng.below(19) as usize];
                    let (a, ta) = self.expr(cx, w, d);
                    let (b, tb) = if self.rng.chance(1, 6) {
                        (a, ta.clone()) // exercise x op x
                    } else {
                        self.expr(cx, w, d)
                    };
                    let e = cx.bin(op, a, b).unwrap();
                    return (e, r::Term::Bin(ref_bin(op), Box::new(ta), Box::new(tb)));
                }
                5 if w == 1 => {
                    let op = CmpOpExt::ALL[self.rng.below(10) as usize];
                    let ow = 1 + self.rng.below(u64::from(self.max_w)) as u16;
                    let (a, ta) = self.expr(cx, ow, d);
                    let (b, tb) = if self.rng.chance(1, 6) {
                        (a, ta.clone())
                    } else {
                        self.expr(cx, ow, d)
                    };
                    let e = cx.cmp(op, a, b).unwrap();
                    return (e, r::Term::Cmp(ref_cmp(op), Box::new(ta), Box::new(tb)));
                }
                6 if w > 1 => {
                    let from = 1 + self.rng.below(u64::from(w - 1)) as u16;
                    let (a, ta) = self.expr(cx, from, d);
                    return if self.rng.chance(1, 2) {
                        (
                            cx.zext(a, width(w)).unwrap(),
                            r::Term::Zext(Box::new(ta), w),
                        )
                    } else {
                        (
                            cx.sext(a, width(w)).unwrap(),
                            r::Term::Sext(Box::new(ta), w),
                        )
                    };
                }
                7 if w < self.max_w => {
                    let from = w + 1 + self.rng.below(u64::from(self.max_w - w)) as u16;
                    let lo = self.rng.below(u64::from(from - w + 1)) as u16;
                    let (a, ta) = self.expr(cx, from, d);
                    let e = cx.extract(a, lo, width(w)).unwrap();
                    return (e, r::Term::Extract(Box::new(ta), lo, w));
                }
                8 if w > 1 => {
                    let hw = 1 + self.rng.below(u64::from(w - 1)) as u16;
                    let (h, th) = self.expr(cx, hw, d);
                    let (l, tl) = self.expr(cx, w - hw, d);
                    let e = cx.concat(h, l).unwrap();
                    return (e, r::Term::Concat(Box::new(th), Box::new(tl)));
                }
                9 => {
                    let (c, tc) = self.expr(cx, 1, d);
                    let (a, ta) = self.expr(cx, w, d);
                    let (b, tb) = if self.rng.chance(1, 6) {
                        (a, ta.clone())
                    } else {
                        self.expr(cx, w, d)
                    };
                    let e = cx.select(c, a, b).unwrap();
                    return (e, r::Term::Select(Box::new(tc), Box::new(ta), Box::new(tb)));
                }
                _ => {}
            }
        }
    }
}
