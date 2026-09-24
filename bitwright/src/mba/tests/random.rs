//! Random MBA expressions for the tests: trees over a few variables, emitted into
//! [`MbaExpr`]s, rewritten by MBA identities (equal pairs), perturbed (unequal pairs), converted
//! to reference terms, and compared by exhaustive evaluation.

use super::super::batch::{BLOCK, Program};
use super::super::*;
use crate::testutil::{Rng, ref_bin, ref_un};
use crate::{BinOp, BitVec, UnOp, Width};
use bitwright_ref as r;

/// An expression tree.
#[derive(Clone, Debug)]
pub(crate) enum T {
    C(BitVec),
    V(u32),
    /// `Neg`, `Not`, `Shl(k)`, `LShr(k)`.
    Un(MOp, Box<T>),
    /// `Add`, `Sub`, `Mul`, `And`, `Or`, `Xor`.
    Bin(MOp, Box<T>, Box<T>),
    /// `Zext`, `Sext` or `Trunc` to a width.
    Cast(MOp, Width, Box<T>),
}

pub(crate) use T::{Bin, C, Un, V};

pub(crate) fn bin(op: MOp, a: T, b: T) -> T {
    Bin(op, Box::new(a), Box::new(b))
}

pub(crate) fn un(op: MOp, a: T) -> T {
    Un(op, Box::new(a))
}

pub(crate) fn add(a: T, b: T) -> T {
    bin(MOp::Add, a, b)
}
pub(crate) fn sub(a: T, b: T) -> T {
    bin(MOp::Sub, a, b)
}
pub(crate) fn mul(a: T, b: T) -> T {
    bin(MOp::Mul, a, b)
}
pub(crate) fn and(a: T, b: T) -> T {
    bin(MOp::And, a, b)
}
pub(crate) fn or(a: T, b: T) -> T {
    bin(MOp::Or, a, b)
}
pub(crate) fn xor(a: T, b: T) -> T {
    bin(MOp::Xor, a, b)
}
pub(crate) fn not(a: T) -> T {
    un(MOp::Not, a)
}
pub(crate) fn neg(a: T) -> T {
    un(MOp::Neg, a)
}
pub(crate) fn k(w: Width, v: i128) -> T {
    C(BitVec::wrapping_from_i128(w, v))
}

impl T {
    /// The width, given the variables' widths.
    pub(crate) fn width(&self, vars: &[Width]) -> Width {
        match self {
            C(v) => v.width(),
            V(i) => vars[*i as usize],
            Un(_, a) | Bin(_, a, _) => a.width(vars),
            T::Cast(_, w, _) => *w,
        }
    }

    /// Emits into `m` (operands first); returns the node.
    pub(crate) fn emit(&self, m: &mut MbaExpr) -> u32 {
        match self {
            C(v) => m.push(MOp::Const(*v), &[]).unwrap(),
            V(i) => m.push(MOp::Var(*i), &[]).unwrap(),
            Un(op, a) => {
                let a = a.emit(m);
                m.push(*op, &[a]).unwrap()
            }
            Bin(op, a, b) => {
                let a = a.emit(m);
                let b = b.emit(m);
                m.push(*op, &[a, b]).unwrap()
            }
            T::Cast(op, w, a) => {
                let a = a.emit(m);
                m.push_cast(*op, a, *w).unwrap()
            }
        }
    }

    /// As an expression over variables of the given widths.
    pub(crate) fn expr(&self, vars: &[Width]) -> MbaExpr {
        let mut m = MbaExpr::new(vars.to_vec());
        self.emit(&mut m);
        m
    }

    /// As a reference term.
    pub(crate) fn to_ref(&self, vars: &[Width]) -> r::Term {
        let bits = |v: &BitVec| r::Bits::from_limbs(v.width().bits(), v.limbs());
        match self {
            C(v) => r::Term::Const(bits(v)),
            V(i) => r::Term::Var(*i as usize, vars[*i as usize].bits()),
            Un(op, a) => {
                let ta = a.to_ref(vars);
                let w = a.width(vars);
                match op {
                    MOp::Neg => r::Term::Un(ref_un(UnOp::Neg), Box::new(ta)),
                    MOp::Not => r::Term::Un(ref_un(UnOp::Not), Box::new(ta)),
                    MOp::Shl(s) | MOp::LShr(s) => {
                        let k = BitVec::wrapping_from_u64(w, u64::from(*s));
                        let op = if matches!(op, MOp::Shl(_)) {
                            BinOp::Shl
                        } else {
                            BinOp::LShr
                        };
                        r::Term::Bin(
                            ref_bin(op),
                            Box::new(ta),
                            Box::new(r::Term::Const(bits(&k))),
                        )
                    }
                    _ => unreachable!(),
                }
            }
            Bin(op, a, b) => {
                let op = match op {
                    MOp::Add => BinOp::Add,
                    MOp::Sub => BinOp::Sub,
                    MOp::Mul => BinOp::Mul,
                    MOp::And => BinOp::And,
                    MOp::Or => BinOp::Or,
                    _ => BinOp::Xor,
                };
                r::Term::Bin(
                    ref_bin(op),
                    Box::new(a.to_ref(vars)),
                    Box::new(b.to_ref(vars)),
                )
            }
            T::Cast(op, w, a) => {
                let ta = Box::new(a.to_ref(vars));
                match op {
                    MOp::Zext => r::Term::Zext(ta, w.bits()),
                    MOp::Sext => r::Term::Sext(ta, w.bits()),
                    _ => r::Term::Extract(ta, 0, w.bits()),
                }
            }
        }
    }

    /// A bitwise function of variables and constants.
    pub(crate) fn local(&self) -> bool {
        match self {
            C(_) | V(_) => true,
            Un(MOp::Not, a) => a.local(),
            Bin(MOp::And | MOp::Or | MOp::Xor, a, b) => a.local() && b.local(),
            _ => false,
        }
    }
}

/// Which expressions a generator makes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Frag {
    /// Linear MBA with 0/all-ones constants in bitwise parts.
    Linear,
    /// Linear combinations of bitwise functions with any constants.
    SemiLinear,
    /// Polynomial MBA: `+ − · neg ~ <<` over bitwise functions of variables and constants.
    Poly,
    /// No `& | ^`.
    PurePoly,
    /// Anything: right shifts, casts, arithmetic under bitwise operators.
    Any,
}

pub(crate) struct Gen {
    pub(crate) rng: Rng,
    pub(crate) w: Width,
    pub(crate) t: u32,
}

impl Gen {
    pub(crate) fn new(seed: u64, w: Width, t: u32) -> Gen {
        Gen {
            rng: Rng(seed),
            w,
            t,
        }
    }

    fn pick<X: Copy>(&mut self, xs: &[X]) -> X {
        xs[self.rng.below(xs.len() as u64) as usize]
    }

    pub(crate) fn var(&mut self) -> T {
        V(self.rng.below(u64::from(self.t)) as u32)
    }

    /// A constant: uniform (0 or all-ones) or any.
    pub(crate) fn konst(&mut self, uniform: bool) -> T {
        let w = self.w;
        if uniform {
            return C(if self.rng.chance(1, 2) {
                BitVec::zero(w)
            } else {
                BitVec::ones(w)
            });
        }
        C(match self.rng.below(6) {
            0 => BitVec::one(w),
            1 => BitVec::smin(w),
            2 => BitVec::wrapping_from_u64(w, self.rng.below(16)),
            _ => BitVec::wrapping_from_limbs(w, &[self.rng.next(), self.rng.next()]),
        })
    }

    /// A small coefficient.
    pub(crate) fn coeff(&mut self) -> T {
        let w = self.w;
        C(match self.rng.below(5) {
            0 => BitVec::ones(w),
            1 => BitVec::smin(w),
            2 => BitVec::wrapping_from_i128(w, self.rng.below(9) as i128 - 4),
            _ => BitVec::wrapping_from_limbs(w, &[self.rng.next()]),
        })
    }

    /// A bitwise function of the variables (constants uniform when `uniform`).
    pub(crate) fn bitwise(&mut self, depth: u32, uniform: bool) -> T {
        if depth == 0 || self.rng.chance(1, 4) {
            return if self.rng.chance(1, 6) {
                self.konst(uniform)
            } else {
                self.var()
            };
        }
        match self.rng.below(5) {
            0 => not(self.bitwise(depth - 1, uniform)),
            _ => {
                let op = self.pick(&[MOp::And, MOp::Or, MOp::Xor]);
                let a = self.bitwise(depth - 1, uniform);
                let b = self.bitwise(depth - 1, uniform);
                bin(op, a, b)
            }
        }
    }

    /// An expression of the fragment.
    pub(crate) fn expr(&mut self, frag: Frag, depth: u32) -> T {
        match frag {
            Frag::Linear | Frag::SemiLinear => {
                let uniform = frag == Frag::Linear;
                let mut e = self.bitwise(2, uniform);
                for _ in 0..depth {
                    let f = self.bitwise(2, uniform);
                    let c = self.coeff();
                    let term = mul(c, f);
                    e = match self.rng.below(3) {
                        0 => sub(e, term),
                        _ => add(e, term),
                    };
                }
                e
            }
            Frag::Poly | Frag::PurePoly | Frag::Any => self.term(frag, depth),
        }
    }

    fn term(&mut self, frag: Frag, depth: u32) -> T {
        if depth == 0 || self.rng.chance(1, 5) {
            return match (frag, self.rng.below(4)) {
                (_, 0) => self.coeff(),
                (Frag::PurePoly, _) => self.var(),
                (_, 1) => self.var(),
                _ => self.bitwise(2, false),
            };
        }
        let d = depth - 1;
        let top = if frag == Frag::Any { 12 } else { 8 };
        match self.rng.below(top) {
            0 | 1 => {
                let (a, b) = (self.term(frag, d), self.term(frag, d));
                add(a, b)
            }
            2 => {
                let (a, b) = (self.term(frag, d), self.term(frag, d));
                sub(a, b)
            }
            3 | 4 => {
                let (a, b) = (self.term(frag, d), self.term(frag, d));
                mul(a, b)
            }
            5 => neg(self.term(frag, d)),
            6 => not(self.term(frag, d)),
            7 => {
                let s = self.rng.below(u64::from(self.w.bits())) as u16;
                un(MOp::Shl(s), self.term(frag, d))
            }
            8 => {
                let s = self.rng.below(u64::from(self.w.bits())) as u16;
                un(MOp::LShr(s), self.term(frag, d))
            }
            9 | 10 => {
                // Arithmetic under a bitwise operator.
                let op = self.pick(&[MOp::And, MOp::Or, MOp::Xor]);
                let a = self.term(frag, d);
                let b = if self.rng.chance(1, 2) {
                    self.bitwise(1, false)
                } else {
                    self.term(frag, d)
                };
                bin(op, a, b)
            }
            _ => {
                // A cast round trip through another width.
                let w = self.w.bits();
                let a = self.term(frag, d);
                if w > 1 && self.rng.chance(1, 2) {
                    let n = Width::new(1 + self.rng.below(u64::from(w) - 1) as u16).unwrap();
                    let op = self.pick(&[MOp::Zext, MOp::Sext]);
                    T::Cast(op, self.w, Box::new(T::Cast(MOp::Trunc, n, Box::new(a))))
                } else if w < 512 {
                    let n = Width::new(w + 1 + self.rng.below(3) as u16).unwrap();
                    let op = self.pick(&[MOp::Zext, MOp::Sext]);
                    T::Cast(MOp::Trunc, self.w, Box::new(T::Cast(op, n, Box::new(a))))
                } else {
                    a
                }
            }
        }
    }

    /// Arithmetic whose low bits are known under a bitwise operator with a constant (such as
    /// `−2·(x & 1) | 1`), and polynomials that appear both inside and outside a bitwise
    /// operator (such as `p + x − (x & p)`, which is `x | p`).
    pub(crate) fn known_bits(&mut self) -> T {
        let w = self.w;
        let bits = u32::from(w.bits());
        // `c·2^j·e + k`: its low j bits are k's.
        let j = (1 + self.rng.below(3) as u32).min(bits);
        let e = match self.rng.below(3) {
            0 => self.var(),
            1 => self.bitwise(1, false),
            _ => mul(self.var(), self.var()),
        };
        let scale = BitVec::wrapping_from_u64(w, (self.rng.next() | 1) << j);
        let p = add(mul(C(scale), e), self.konst(false));
        let low = crate::facts::known::low_mask(w, j);
        let r = BitVec::wrapping_from_limbs(w, &[self.rng.next(), self.rng.next()]);
        let k = match self.rng.below(3) {
            0 => crate::facts::known::bv_and(&r, &low),
            1 => crate::facts::known::bv_or(&r, &crate::facts::known::bv_not(&low)),
            _ => r,
        };
        let op = self.pick(&[MOp::And, MOp::Or, MOp::Xor]);
        let a = bin(op, p.clone(), C(k));
        match self.rng.below(5) {
            0 => a,
            1 => mul(a.clone(), a),
            2 => {
                // `p + x − (x & p) = x | p`, `p + x − 2(x & p) = x ^ p`.
                let x = self.bitwise(1, false);
                let c = C(BitVec::wrapping_from_u64(w, 1 + self.rng.below(2)));
                sub(add(p.clone(), x.clone()), mul(c, and(x, p)))
            }
            3 => {
                let x = self.var();
                let op = self.pick(&[MOp::And, MOp::Or, MOp::Xor]);
                add(add(p.clone(), bin(op, x, p)), self.var())
            }
            _ => add(a, self.expr(Frag::SemiLinear, 1)),
        }
    }

    /// An equal expression: MBA identities applied at random nodes. Identities that would put
    /// arithmetic under a bitwise operator are used only on bitwise operands unless `any`.
    pub(crate) fn rewrite(&mut self, e: &T, any: bool) -> T {
        self.rw(e, false, any, 0)
    }

    fn rw(&mut self, e: &T, bitwise_ctx: bool, any: bool, depth: u32) -> T {
        let w = self.w;
        match e {
            C(_) | V(_) => e.clone(),
            T::Cast(op, cw, a) => T::Cast(*op, *cw, Box::new(self.rw(a, false, any, depth + 1))),
            Un(op, a) => {
                let sub_ctx = matches!(op, MOp::Not) && bitwise_ctx;
                let ra = self.rw(a, sub_ctx, any, depth + 1);
                if depth > 6 || !self.rng.chance(1, 3) {
                    return un(*op, ra);
                }
                match op {
                    MOp::Not if !bitwise_ctx => sub(neg(ra), k(w, 1)),
                    MOp::Not => xor(ra, k(w, -1)),
                    MOp::Neg => add(not(ra), k(w, 1)),
                    _ => un(*op, ra),
                }
            }
            Bin(op, a, b) => {
                let sub_ctx = matches!(op, MOp::And | MOp::Or | MOp::Xor);
                let (ra, rb) = (
                    self.rw(a, sub_ctx, any, depth + 1),
                    self.rw(b, sub_ctx, any, depth + 1),
                );
                if depth > 6 || !self.rng.chance(1, 2) {
                    return bin(*op, ra, rb);
                }
                // Bitwise results may be spelled with arithmetic only where they are read
                // arithmetically; arithmetic may read bitwise operators of operands only when
                // the operands are bitwise (or anything goes).
                let loc = any || (ra.local() && rb.local());
                let (x, y) = (ra.clone(), rb.clone());
                match (op, bitwise_ctx) {
                    (MOp::Add, _) if loc => match self.rng.below(3) {
                        0 => add(xor(x.clone(), y.clone()), mul(k(w, 2), and(x, y))),
                        1 => add(or(x.clone(), y.clone()), and(x, y)),
                        _ => sub(mul(k(w, 2), or(x.clone(), y.clone())), xor(x, y)),
                    },
                    (MOp::Add, _) => add(y, x),
                    (MOp::Sub, _) if loc && self.rng.chance(1, 2) => {
                        sub(xor(x.clone(), y.clone()), mul(k(w, 2), and(not(x), y)))
                    }
                    (MOp::Sub, _) => add(add(x, not(y)), k(w, 1)),
                    (MOp::Mul, _) if loc => add(
                        mul(and(x.clone(), y.clone()), or(x.clone(), y.clone())),
                        mul(and(x.clone(), not(y.clone())), and(not(x), y)),
                    ),
                    (MOp::Mul, _) => mul(y, x),
                    (MOp::Xor, false) if loc || any => match self.rng.below(2) {
                        0 => sub(or(x.clone(), y.clone()), and(x, y)),
                        _ => sub(add(x.clone(), y.clone()), mul(k(w, 2), and(x, y))),
                    },
                    (MOp::Xor, _) => and(or(x.clone(), y.clone()), not(and(x, y))),
                    (MOp::Or, false) if loc || any => match self.rng.below(2) {
                        0 => add(xor(x.clone(), y.clone()), and(x, y)),
                        _ => sub(add(x.clone(), y.clone()), and(x, y)),
                    },
                    (MOp::Or, _) => not(and(not(x), not(y))),
                    (MOp::And, false) if loc || any => match self.rng.below(2) {
                        0 => sub(or(x.clone(), y.clone()), xor(x, y)),
                        _ => sub(add(x.clone(), y.clone()), or(x, y)),
                    },
                    (MOp::And, _) => not(or(not(x), not(y))),
                    _ => bin(*op, x, y),
                }
            }
        }
    }

    /// A term equal to zero at every input, of the given fragment.
    pub(crate) fn zero(&mut self, frag: Frag) -> T {
        let w = self.w;
        let half = C(BitVec::smin(w));
        match (frag, self.rng.below(4)) {
            (Frag::PurePoly, 0) | (Frag::Poly | Frag::Any, 0) => {
                // 2^(W-1)·(u² + u): u(u + 1) is even.
                let u = if frag == Frag::PurePoly {
                    self.term(Frag::PurePoly, 1)
                } else {
                    self.bitwise(1, false)
                };
                mul(half, add(mul(u.clone(), u.clone()), u))
            }
            (Frag::PurePoly, _) => {
                // 2^(W-1)·(u² − u) and (u + 1)² − u² − 2u − 1.
                let u = self.term(Frag::PurePoly, 1);
                if self.rng.chance(1, 2) {
                    mul(half, sub(mul(u.clone(), u.clone()), u))
                } else {
                    let one = k(w, 1);
                    let s = add(u.clone(), one.clone());
                    sub(
                        sub(
                            sub(mul(s.clone(), s), mul(u.clone(), u.clone())),
                            mul(k(w, 2), u),
                        ),
                        one,
                    )
                }
            }
            (Frag::Poly | Frag::Any, 1) => {
                // x·y − (x & y)(x | y) − (x & ~y)(~x & y).
                let (x, y) = (self.bitwise(1, false), self.bitwise(1, false));
                sub(
                    sub(
                        mul(x.clone(), y.clone()),
                        mul(and(x.clone(), y.clone()), or(x.clone(), y.clone())),
                    ),
                    mul(and(x.clone(), not(y.clone())), and(not(x), y)),
                )
            }
            (Frag::Poly | Frag::Any, 2) => {
                // 2^(W-1)·((a & b)·(b & c) − (a & b & c)): the low bit of a product of
                // conjunctions is the conjunction of the low bits.
                let (a, b, c) = (self.var(), self.var(), self.var());
                mul(
                    half,
                    sub(
                        mul(and(a.clone(), b.clone()), and(b.clone(), c.clone())),
                        and(and(a, b), c),
                    ),
                )
            }
            (Frag::Linear | Frag::SemiLinear, _) | (_, _) => {
                // (a | b) − (a & b) − (a ^ b).
                let uniform = frag == Frag::Linear;
                let (a, b) = (self.bitwise(1, uniform), self.bitwise(1, uniform));
                sub(
                    sub(or(a.clone(), b.clone()), and(a.clone(), b.clone())),
                    xor(a, b),
                )
            }
        }
    }

    /// A term that is usually not zero (sometimes only at a few inputs), of the fragment.
    pub(crate) fn nonzero(&mut self, frag: Frag) -> T {
        let w = self.w;
        let t = self.t;
        let pure = frag == Frag::PurePoly;
        match self.rng.below(7) {
            0 => k(w, 1),
            1 => C(BitVec::smin(w)),
            2 if !pure => {
                // Corner-invisible: x·y − (x & y).
                let (x, y) = (self.var(), self.var());
                sub(mul(x.clone(), y.clone()), and(x, y))
            }
            3 if !pure && t >= 2 => {
                // (x & ~y)·(~x & y): zero at every corner.
                mul(and(V(0), not(V(1))), and(not(V(0)), V(1)))
            }
            4 if !pure && t >= 3 && w.bits() >= 3 => {
                // Nonzero only when three different positions are set.
                mul(
                    mul(and(V(0), k(w, 1)), and(V(1), k(w, 2))),
                    and(V(2), k(w, 4)),
                )
            }
            5 if !pure => mul(C(BitVec::smin(w)), and(self.var(), self.var())),
            _ => {
                // 2^(W-1)·u·v·z: nonzero only when all three are odd.
                let (a, b, c) = (self.var(), self.var(), self.var());
                mul(mul(C(BitVec::smin(w)), mul(a, b)), c)
            }
        }
    }
}

/// Every assignment of the variables (at most 20 bits), point-major.
pub(crate) fn every_point(vars: &[Width]) -> Vec<Vec<BitVec>> {
    let bits: u32 = vars.iter().map(|w| u32::from(w.bits())).sum();
    assert!(bits <= 20, "{bits} bits");
    (0..1u64 << bits)
        .map(|mut c| {
            vars.iter()
                .map(|&w| {
                    let x = BitVec::wrapping_from_u64(w, c);
                    c >>= w.bits();
                    x
                })
                .collect()
        })
        .collect()
}

/// Whether `a` and `b` agree at every input (by the batched evaluator, itself checked against
/// the reference).
pub(crate) fn equal_everywhere(a: &MbaExpr, b: &MbaExpr) -> bool {
    let (pa, pb) = (
        Program::new(a, false).unwrap(),
        Program::new(b, false).unwrap(),
    );
    if pa.widest().max(pb.widest()) > 64 {
        let pts = every_point(a.vars());
        return pa.eval_points(&pts) == pb.eval_points(&pts);
    }
    let vars = a.vars();
    let bits: u32 = vars.iter().map(|w| u32::from(w.bits())).sum();
    assert!(bits <= 20, "{bits} bits");
    let total = 1u64 << bits;
    let (mut ra, mut rb): (Vec<Vec<u64>>, Vec<Vec<u64>>) = (Vec::new(), Vec::new());
    let mut start = 0;
    while start < total {
        let n = (total - start).min(BLOCK as u64) as usize;
        let mut shift = 0;
        let cols: Vec<Vec<u64>> = vars
            .iter()
            .map(|w| {
                let s = shift;
                shift += u32::from(w.bits());
                let mask = (1u64 << w.bits()) - 1;
                (start..start + n as u64).map(|c| (c >> s) & mask).collect()
            })
            .collect();
        pa.run(&mut ra, &cols, n);
        pb.run(&mut rb, &cols, n);
        if ra[pa.root()][..n] != rb[pb.root()][..n] {
            return false;
        }
        start += n as u64;
    }
    true
}
