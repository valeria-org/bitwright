//! The division pass: multiply-high sequences that divide by a constant, and the remainders
//! computed from such quotients.
//!
//! A compiler divides by a constant `d` by multiplying with a *magic* constant `M ≈ 2^k / d` and
//! shifting (Granlund and Montgomery): `umulhi(x, M) >>u s`; an add-and-halve step when `M`
//! needs `W + 1` bits, `(t + ((x − t) >>u 1)) >>u s` with `t = umulhi(x, M − 2^W)`; the product
//! in a register twice as wide, `trunc((zext(x) · M) >>u k)`; for signed division `smulhi`, an
//! arithmetic shift and a correction by the quotient's sign bit, `q + (q >>u (W − 1))` with
//! `q = (smulhi(x, M) ± x) >>s s`, or by the dividend's, `q − (x >>s (W − 1))`.
//!
//! The pass reads such a node as an exact function of its input `n` (the multiplicand): on each
//! interval (*piece*) of `n` it is an *affine floor* `floor((a·n + b) / c)` ([`Aff`]), carried
//! through `+ − neg ~`, products and left shifts by constants, right shifts, `umulhi`/`smulhi`
//! and `udiv`/`sdiv` by constants, extensions, extracts, the add-and-halve step, and bitwise
//! operations of values constant on the piece. Where a node's bits wrap (an unsigned reading of
//! a value that is negative on part of the piece), a signed dividend changes sign, or an operand
//! that must be exact takes a few values (a sign bit), the piece is split there. The node
//! divides by `d` exactly when, on every piece, its affine floor equals the quotient, which
//! [`agrees`] decides at no more than eight points per piece, with integers wide enough that
//! nothing wraps: every input is covered, none sampled. The node then becomes `udiv(x, d)` or
//! `sdiv(x, d)` (a dividend `x >>u j` merging into the divisor).
//!
//! In a linear sum, `c·x − c·d·q` with `q = udiv(x, d)` (or `sdiv`) is `c·urem(x, d)` (or
//! `srem`), and `c·x − c·(q·z)` with `q = udiv(x, z)` is `c·urem(x, z)`: the remainder a compiler
//! computes from the quotient.
//!
//! It undoes a compiler's strength reduction, so only `Strategy::deobfuscate()` runs it.

use super::linear::{self, Form};
use super::{Fin, PassKind, Runner, Step, Stop, facts, finish_with};
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::ops::{BinOp, CmpOp};
use crate::{BitVec, Width};

/// The widest input and result.
const MAX_WIDTH: u16 = 64;

/// The widest node inside a sequence (a 64-bit division multiplies in 128 bits).
const MAX_INNER: u16 = 128;

/// The most nodes of a sequence (constants included).
const MAX_NODES: u32 = 32;

/// How deep below the node the multiply-high is looked for.
const MAX_DEPTH: u32 = 8;

/// The most pieces the input's range is split into, and the most evaluations over them.
const MAX_PIECES: usize = 8;
const MAX_EVALS: u32 = 16;

/// The most values an operand that must be exact may take on a piece: it is split at each.
const SPLIT_VALUES: i128 = 4;

/// The most bits of an affine floor's denominator.
const MAX_DEN: u32 = 300;

/// The most significant bits of a coefficient: with an input below `2^64`, `a·n + b` stays
/// below `2^506`, inside [`Int`]'s 511 bits (reduced, coefficients are below `2^128·2^300`).
const MAX_BITS: u32 = 440;

// ----- exact integers --------------------------------------------------------------------------

fn int_width() -> Width {
    Width::new(Width::MAX_BITS).unwrap_or(Width::W64)
}

/// A signed integer of up to 511 bits (two's complement at 512): wide enough that the products
/// of a 128-bit sequence's coefficients and a 64-bit input never wrap.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Int(BitVec);

impl Int {
    fn of(v: i128) -> Int {
        Int(BitVec::wrapping_from_i128(int_width(), v))
    }

    fn zero() -> Int {
        Int::of(0)
    }

    fn one() -> Int {
        Int::of(1)
    }

    /// `2^k`, for `k` below 511.
    fn pow2(k: u32) -> Int {
        Int::one().shl(k)
    }

    /// The unsigned reading of `v`.
    fn unsigned(v: &BitVec) -> Int {
        Int(v
            .zext(int_width())
            .unwrap_or_else(|_| BitVec::zero(int_width())))
    }

    /// The signed reading of `v`.
    fn signed(v: &BitVec) -> Int {
        Int(v
            .sext(int_width())
            .unwrap_or_else(|_| BitVec::zero(int_width())))
    }

    fn bin(&self, op: BinOp, o: &Int) -> Int {
        Int(BitVec::bin_unchecked(op, &self.0, &o.0))
    }

    fn add(&self, o: &Int) -> Int {
        self.bin(BinOp::Add, o)
    }

    fn sub(&self, o: &Int) -> Int {
        self.bin(BinOp::Sub, o)
    }

    fn mul(&self, o: &Int) -> Int {
        self.bin(BinOp::Mul, o)
    }

    fn neg(&self) -> Int {
        Int::zero().sub(self)
    }

    fn shl(&self, k: u32) -> Int {
        self.bin(BinOp::Shl, &Int::of(i128::from(k)))
    }

    /// `floor(self / 2^k)`.
    fn shr(&self, k: u32) -> Int {
        self.bin(BinOp::AShr, &Int::of(i128::from(k)))
    }

    fn lt(&self, o: &Int) -> bool {
        BitVec::cmp_unchecked(CmpOp::Slt, &self.0, &o.0)
    }

    fn is_neg(&self) -> bool {
        self.0.msb()
    }

    fn min(self, o: Int) -> Int {
        if o.lt(&self) { o } else { self }
    }

    fn max(self, o: Int) -> Int {
        if self.lt(&o) { o } else { self }
    }

    /// `k` when `self` is `2^k`.
    fn log2(&self) -> Option<u32> {
        (crate::facts::known::count_ones(&self.0) == 1).then(|| {
            BitVec::un_unchecked(crate::ops::UnOp::Ctz, &self.0)
                .to_u64()
                .unwrap_or(0) as u32
        })
    }

    /// `floor(self / d)` for `d > 0`.
    fn div_floor(&self, d: &Int) -> Int {
        if let Some(k) = d.log2() {
            return self.shr(k);
        }
        // Truncation rounds toward zero: one less where a negative quotient is inexact.
        let q = self.bin(BinOp::SDiv, d);
        if self.is_neg() && q.mul(d) != *self {
            q.sub(&Int::one())
        } else {
            q
        }
    }

    /// `ceil(self / d)` for `d > 0`.
    fn div_ceil(&self, d: &Int) -> Int {
        self.neg().div_floor(d).neg()
    }

    /// The bits of `|self|` (of `-self - 1` when negative).
    fn bits(&self) -> u32 {
        let v = if self.is_neg() {
            crate::facts::known::bv_not(&self.0)
        } else {
            self.0
        };
        let lz = BitVec::un_unchecked(crate::ops::UnOp::Clz, &v)
            .to_u64()
            .unwrap_or(0) as u32;
        u32::from(Width::MAX_BITS) - lz
    }

    /// The representative of `self` modulo `m` (even, at least 2) in `[−m/2, m/2)`.
    fn centered(&self, m: &Int) -> Int {
        // Modulo 2^j: the low j bits, sign-extended.
        if let Some(j) = m.log2()
            && let Ok(w) = Width::new(j as u16)
            && let Ok(low) = self.0.trunc(w)
        {
            return Int::signed(&low);
        }
        let r = self.sub(&m.mul(&self.div_floor(m)));
        if r.lt(&m.shr(1)) { r } else { r.sub(m) }
    }

    /// The low bits of `self` as a value of width `w`.
    fn to_bits(&self, w: Width) -> BitVec {
        self.0.trunc(w).unwrap_or_else(|_| BitVec::zero(w))
    }

    #[cfg(test)]
    fn as_i128(&self) -> Option<i128> {
        self.0.to_i128()
    }
}

// ----- affine floors ---------------------------------------------------------------------------

/// `floor((a·n + b) / c)` (`c >= 1`): the value a node takes as a function of the input `n` on
/// a piece, congruent to the node's bits modulo `2^W` (`W` the node's width). With `c = 1` it
/// is *exact*: an integer affine function.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Aff {
    a: Int,
    b: Int,
    c: Int,
}

impl Aff {
    fn exact(b: Int) -> Aff {
        Aff {
            a: Int::zero(),
            b,
            c: Int::one(),
        }
    }

    fn is_exact(&self) -> bool {
        self.c == Int::one()
    }

    fn at(&self, n: &Int) -> Int {
        self.a.mul(n).add(&self.b).div_floor(&self.c)
    }

    /// The same bits at width `w` with the smallest coefficients: `a` and `b` matter only
    /// modulo `2^w·c` (adding `2^w·c·(i·n + j)` to `a·n + b` adds a multiple of `2^w` to the
    /// floor).
    fn reduced(&self, w: u16) -> Aff {
        let m = self.c.shl(u32::from(w));
        Aff {
            a: self.a.centered(&m),
            b: self.b.centered(&m),
            c: self.c.clone(),
        }
    }

    /// Whether the coefficients are small enough for [`Int`] (see [`MAX_BITS`]).
    fn fits(&self) -> bool {
        self.c.bits() <= MAX_DEN && self.a.bits() <= MAX_BITS && self.b.bits() <= MAX_BITS
    }

    /// `floor(self / d)` (`d >= 1`), of a value read exactly: `floor(floor(z) / d)` is
    /// `floor(z / d)`.
    fn over(&self, d: &Int) -> Aff {
        Aff {
            c: self.c.mul(d),
            ..self.clone()
        }
    }

    /// `self + e` for an exact `e = f·n + g`: `floor((a·n + b) / c) + f·n + g` is
    /// `floor(((a + f·c)·n + b + g·c) / c)`.
    fn plus_exact(&self, e: &Aff) -> Aff {
        Aff {
            a: self.a.add(&e.a.mul(&self.c)),
            b: self.b.add(&e.b.mul(&self.c)),
            c: self.c.clone(),
        }
    }

    /// `e − self` for an exact `e`: `−floor(Z / c) = floor((−Z + c − 1) / c)`.
    fn subtracted_from(&self, e: &Aff) -> Aff {
        let c = &self.c;
        Aff {
            a: e.a.mul(c).sub(&self.a),
            b: e.b.mul(c).sub(&self.b).add(c).sub(&Int::one()),
            c: c.clone(),
        }
    }

    /// `self · k`, of an exact value.
    fn scaled(&self, k: &Int) -> Aff {
        Aff {
            a: self.a.mul(k),
            b: self.b.mul(k),
            c: self.c.clone(),
        }
    }
}

/// Why a piece has no affine floor.
enum Why {
    /// Split the piece before this input, and evaluate each part on its own.
    Split(Int),
    /// The node is not read: another leaf, an operator outside the model, a coefficient too
    /// large for [`Int`].
    Fail,
}

/// The first input of `[lo, hi]` at which `m` is at least `bound` (`m` monotone, below `bound`
/// at one end and not at the other): the split between the two.
fn crossing(m: &Aff, bound: &Int, lo: &Int, hi: &Int) -> Result<Int, Why> {
    // m(n) >= B iff a·n + b >= B·c.
    let t = bound.mul(&m.c).sub(&m.b);
    let s = if m.a.is_neg() {
        // Decreasing: m(n) >= B iff n <= floor((b − B·c) / −a).
        t.neg().div_floor(&m.a.neg()).add(&Int::one())
    } else if m.a == Int::zero() {
        return Err(Why::Fail);
    } else {
        t.div_ceil(&m.a)
    };
    if lo.lt(&s) && !hi.lt(&s) {
        Ok(s)
    } else {
        Err(Why::Fail)
    }
}

/// Whether `floor((a·m + b) / c) == floor(m / d)` for every integer `m` of `[lo, hi]`
/// (`0 <= lo <= hi`, `d >= 1`).
///
/// With `m = q·d + r`, `0 <= r < d`, the two agree at `m` iff `0 <= E(q, r) < c` for
/// `E(q, r) = a·m + b − q·c = q·(a·d − c) + a·r + b`, affine in `(q, r)`. The pairs the
/// interval covers are rows `q_lo..=q_hi` of `r`, full except the first and the last, and an
/// affine function takes its least and greatest values over them at the ends of the first and
/// last rows or at the corners of the full rows between. So they agree everywhere iff they
/// agree at those (at most eight) points.
fn agrees(f: &Aff, d: &Int, lo: &Int, hi: &Int) -> bool {
    let (qlo, qhi) = (lo.div_floor(d), hi.div_floor(d));
    let last = d.sub(&Int::one());
    let at = |q: &Int, r: &Int| q.mul(d).add(r);
    let mut points = vec![lo.clone(), hi.clone()];
    if qlo.lt(&qhi) {
        points.push(at(&qlo, &last));
        points.push(at(&qhi, &Int::zero()));
        let (q1, q2) = (qlo.add(&Int::one()), qhi.sub(&Int::one()));
        if !q2.lt(&q1) {
            for q in [&q1, &q2] {
                points.push(at(q, &Int::zero()));
                points.push(at(q, &last));
            }
        }
    }
    points.iter().all(|m| f.at(m) == m.div_floor(d))
}

// ----- reading a sequence ----------------------------------------------------------------------

/// The operators the multiply-high is looked for through (the model also reads bitwise
/// operations of values it shows constant).
fn read_op(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Add
            | OpCode::Sub
            | OpCode::Neg
            | OpCode::Not
            | OpCode::Mul
            | OpCode::Shl
            | OpCode::LShr
            | OpCode::AShr
            | OpCode::UMulHi
            | OpCode::SMulHi
            | OpCode::UDiv
            | OpCode::SDiv
            | OpCode::Zext
            | OpCode::Sext
            | OpCode::Extract
    )
}

/// The multiplicand of the multiply-high below `n`, and whether it is signed: the first
/// `umulhi`/`smulhi` by a constant, product of an extension by a constant, or division by a
/// constant (whose dividend is the input then: a quotient divided further), reached through
/// the operators the model reads (at most [`MAX_NODES`] nodes, [`MAX_DEPTH`] deep).
fn core(r: &mut Runner<'_, '_>, cx: &Context, n: u32) -> Result<Option<(u32, bool)>, Stop> {
    let mut stack = vec![(n, 0u32)];
    let mut seen = 0u32;
    while let Some((i, depth)) = stack.pop() {
        seen += 1;
        if seen > MAX_NODES {
            break;
        }
        let node = cx.node(i);
        if !read_op(node.op) || node.width > MAX_INNER {
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        let konst = |j: u32| cx.is_const(j);
        match node.op {
            OpCode::UMulHi | OpCode::SMulHi => {
                let signed = node.op == OpCode::SMulHi;
                if konst(node.b) && !konst(node.a) {
                    return Ok(Some((node.a, signed)));
                }
                if konst(node.a) && !konst(node.b) {
                    return Ok(Some((node.b, signed)));
                }
            }
            OpCode::UDiv | OpCode::SDiv if konst(node.b) && !konst(node.a) => {
                return Ok(Some((node.a, node.op == OpCode::SDiv)));
            }
            OpCode::Mul => {
                let x = if konst(node.b) { node.a } else { node.b };
                if konst(node.a) != konst(node.b) {
                    let e = cx.node(x);
                    if matches!(e.op, OpCode::Zext | OpCode::Sext) && !konst(e.a) {
                        return Ok(Some((e.a, e.op == OpCode::Sext)));
                    }
                }
            }
            _ => {}
        }
        if depth < MAX_DEPTH {
            for c in node.children() {
                // A shift's count is no part of the value.
                if !konst(c) {
                    stack.push((c, depth + 1));
                }
            }
        }
    }
    Ok(None)
}

/// The affine floors of one sequence over one piece of its input.
struct Eval<'c> {
    cx: &'c Context,
    input: u32,
    lo: Int,
    hi: Int,
    memo: Vec<(u32, Aff)>,
    /// Nodes evaluated (charged to the pass's work).
    work: u32,
}

impl Eval<'_> {
    /// The node's affine floor on the piece.
    fn model(&mut self, i: u32, depth: u32) -> Result<Aff, Why> {
        if let Some((_, m)) = self.memo.iter().find(|(j, _)| *j == i) {
            return Ok(m.clone());
        }
        self.work += 1;
        if self.work > MAX_NODES || depth > MAX_DEPTH + 4 {
            return Err(Why::Fail);
        }
        let m = self.compute(i, depth)?;
        // (Bounded before reducing: the modulus is c·2^W.)
        if m.c.bits() > MAX_DEN {
            return Err(Why::Fail);
        }
        let m = m.reduced(self.cx.wid(i));
        if !m.fits() {
            return Err(Why::Fail);
        }
        self.memo.push((i, m.clone()));
        Ok(m)
    }

    fn compute(&mut self, i: u32, depth: u32) -> Result<Aff, Why> {
        let cx = self.cx;
        if i == self.input {
            return Ok(Aff {
                a: Int::one(),
                b: Int::zero(),
                c: Int::one(),
            });
        }
        let node = cx.node(i);
        let w = node.width;
        if let Some(v) = cx.const_val(i) {
            return Ok(Aff::exact(Int::signed(&v)));
        }
        if w > MAX_INNER {
            return Err(Why::Fail);
        }
        let shift = |j: u32| -> Option<u32> {
            let v = cx.const_val(j)?;
            Some(
                v.to_u64()
                    .map_or(u32::MAX, |s| s.min(u64::from(u32::MAX)) as u32),
            )
        };
        let d = depth + 1;
        match node.op {
            OpCode::Add => {
                if let Some(m) = self.average(node.a, node.b, w, d)? {
                    return Ok(m);
                }
                if let Some(m) = self.average(node.b, node.a, w, d)? {
                    return Ok(m);
                }
                let (p, q) = (self.model(node.a, d)?, self.model(node.b, d)?);
                self.sum(p, q, false)
            }
            OpCode::Sub => {
                let (p, q) = (self.model(node.a, d)?, self.model(node.b, d)?);
                self.sum(p, q, true)
            }
            OpCode::Neg => {
                let p = self.model(node.a, d)?;
                self.sum(Aff::exact(Int::zero()), p, true)
            }
            // `~p = −1 − p`.
            OpCode::Not => {
                let p = self.model(node.a, d)?;
                self.sum(Aff::exact(Int::of(-1)), p, true)
            }
            OpCode::Mul => {
                let (x, c) = match (cx.const_val(node.a), cx.const_val(node.b)) {
                    (None, Some(c)) => (node.a, c),
                    (Some(c), None) => (node.b, c),
                    _ => return Err(Why::Fail),
                };
                let p = self.model(x, d)?;
                let p = self.exactify(p)?;
                Ok(p.scaled(&Int::signed(&c)))
            }
            OpCode::Shl => {
                let s = shift(node.b).ok_or(Why::Fail)?;
                if s >= u32::from(w) {
                    return Ok(Aff::exact(Int::zero()));
                }
                let p = self.model(node.a, d)?;
                let p = self.exactify(p)?;
                Ok(p.scaled(&Int::pow2(s)))
            }
            OpCode::LShr | OpCode::AShr => {
                let signed = node.op == OpCode::AShr;
                let s = shift(node.b).ok_or(Why::Fail)?;
                if s >= u32::from(w) && !signed {
                    return Ok(Aff::exact(Int::zero()));
                }
                let s = s.min(u32::from(w) - 1);
                let p = self.model(node.a, d)?;
                Ok(self.read(&p, w, signed)?.over(&Int::pow2(s)))
            }
            OpCode::UMulHi | OpCode::SMulHi => {
                let signed = node.op == OpCode::SMulHi;
                let (x, c) = match (cx.const_val(node.a), cx.const_val(node.b)) {
                    (None, Some(c)) => (node.a, c),
                    (Some(c), None) => (node.b, c),
                    _ => return Err(Why::Fail),
                };
                let p = self.model(x, d)?;
                let p = self.read(&p, w, signed)?;
                let p = self.exactify(p)?;
                let c = if signed {
                    Int::signed(&c)
                } else {
                    Int::unsigned(&c)
                };
                // The high half of the double-width product: floor(p·c / 2^W).
                Ok(p.scaled(&c).over(&Int::pow2(u32::from(w))))
            }
            OpCode::UDiv | OpCode::SDiv => {
                let signed = node.op == OpCode::SDiv;
                let c = cx.const_val(node.b).ok_or(Why::Fail)?;
                let c = if signed {
                    Int::signed(&c)
                } else {
                    Int::unsigned(&c)
                };
                if c == Int::zero() {
                    return Err(Why::Fail);
                }
                let p = self.model(node.a, d)?;
                let p = self.read(&p, w, signed)?;
                if !signed {
                    return Ok(p.over(&c));
                }
                // trunc(p / c): floor(p / |c|) where p >= 0, ceil(p / |c|) where p < 0 (so
                // split where p's sign changes), negated for c < 0. INT_MIN / −1 is 2^(W−1),
                // congruent to the bits it wraps to.
                let (vlo, vhi) = (p.at(&self.lo), p.at(&self.hi));
                if vlo.is_neg() != vhi.is_neg() {
                    return Err(Why::Split(crossing(&p, &Int::zero(), &self.lo, &self.hi)?));
                }
                let ac = if c.is_neg() { c.neg() } else { c.clone() };
                let q = if vlo.is_neg() {
                    p.plus_exact(&Aff::exact(ac.sub(&Int::one()))).over(&ac)
                } else {
                    p.over(&ac)
                };
                Ok(if c.is_neg() {
                    q.subtracted_from(&Aff::exact(Int::zero()))
                } else {
                    q
                })
            }
            OpCode::Zext | OpCode::Sext => {
                let p = self.model(node.a, d)?;
                self.read(&p, cx.wid(node.a), node.op == OpCode::Sext)
            }
            OpCode::Extract => {
                let p = self.model(node.a, d)?;
                if node.b == 0 {
                    // The low bits: congruent modulo the narrower width too.
                    return Ok(p);
                }
                Ok(self
                    .read(&p, cx.wid(node.a), false)?
                    .over(&Int::pow2(node.b)))
            }
            // A bitwise operation of values constant on the piece (a sign bit masked, `& 1`).
            OpCode::And | OpCode::Or | OpCode::Xor => {
                let p = self.model(node.a, d)?;
                let p = self.exactify(p)?;
                let q = self.model(node.b, d)?;
                let q = self.exactify(q)?;
                if p.a != Int::zero() || q.a != Int::zero() {
                    return Err(Why::Fail);
                }
                let width = cx.width_of(i);
                let op = node.op.as_bin().ok_or(Why::Fail)?;
                let v = BitVec::bin_unchecked(op, &p.b.to_bits(width), &q.b.to_bits(width));
                Ok(Aff::exact(Int::signed(&v)))
            }
            _ => Err(Why::Fail),
        }
    }

    /// `t + ((u − t) >>u 1)`, when `s` is `(u − t) >>u 1`: `floor((u + t) / 2)` where `u >= t`,
    /// `floor((u + t + 2^W) / 2)` where `u − t` wraps (the add-and-halve step of a multiplier of
    /// `W + 1` bits, which never wraps).
    fn average(&mut self, t: u32, s: u32, w: u16, d: u32) -> Result<Option<Aff>, Why> {
        let cx = self.cx;
        let sn = cx.node(s);
        if sn.op != OpCode::LShr || cx.const_val(sn.b).and_then(|v| v.to_u64()) != Some(1) {
            return Ok(None);
        }
        let sub = cx.node(sn.a);
        if sub.op != OpCode::Sub || sub.b != t {
            return Ok(None);
        }
        let mt = self.model(t, d)?;
        let mt = self.read(&mt, w, false)?;
        let mu = self.model(sub.a, d)?;
        let mu = self.read(&mu, w, false)?;
        // The bits of u − t are u − t, or u − t + 2^W where u < t (split where that changes),
        // and t + floor(bits / 2) = floor((u + t + [u < t]·2^W) / 2).
        let diff = self.sum(mu.clone(), mt.clone(), true)?;
        let below = diff.at(&self.lo).is_neg();
        if below != diff.at(&self.hi).is_neg() {
            return Err(Why::Split(crossing(
                &diff,
                &Int::zero(),
                &self.lo,
                &self.hi,
            )?));
        }
        let sum = self.sum(mu, mt, false)?;
        let sum = if below {
            sum.plus_exact(&Aff::exact(Int::pow2(u32::from(w))))
        } else {
            sum
        };
        Ok(Some(sum.over(&Int::of(2))))
    }

    /// `p + q` (or `p − q`), when one of them is exact on the piece, or is made so by a split
    /// where it takes a few values.
    fn sum(&self, p: Aff, q: Aff, sub: bool) -> Result<Aff, Why> {
        let (p, q) = if p.is_exact() || q.is_exact() {
            (p, q)
        } else if let Some(c) = self.constant(&q) {
            (p, c)
        } else if let Some(c) = self.constant(&p) {
            (c, q)
        } else {
            // Neither is constant: split where one of them steps, if one takes a few values.
            return Err(match (self.exactify(q), self.exactify(p)) {
                (Err(Why::Split(s)), _) | (_, Err(Why::Split(s))) => Why::Split(s),
                _ => Why::Fail,
            });
        };
        if q.is_exact() {
            let q = if sub { q.scaled(&Int::of(-1)) } else { q };
            return Ok(p.plus_exact(&q));
        }
        // p exact, q not.
        if sub {
            Ok(q.subtracted_from(&p))
        } else {
            Ok(q.plus_exact(&p))
        }
    }

    /// The constant `m` is on the piece (monotone, it is one when its ends agree), if it is one.
    fn constant(&self, m: &Aff) -> Option<Aff> {
        let v = m.at(&self.lo);
        (v == m.at(&self.hi)).then(|| Aff::exact(v))
    }

    /// `m` as an exact value: itself, the constant it is on the piece, or (when it takes a few
    /// values, a sign bit's two) a split where it first changes.
    fn exactify(&self, m: Aff) -> Result<Aff, Why> {
        if m.is_exact() {
            return Ok(m);
        }
        if let Some(c) = self.constant(&m) {
            return Ok(c);
        }
        let (vlo, vhi) = (m.at(&self.lo), m.at(&self.hi));
        let gap = vhi.sub(&vlo);
        let few = Int::of(SPLIT_VALUES);
        if gap.lt(&few) && few.neg().lt(&gap) {
            // Where it first leaves its value at lo.
            let bound = if vlo.lt(&vhi) {
                vlo.add(&Int::one())
            } else {
                vlo
            };
            return Err(Why::Split(crossing(&m, &bound, &self.lo, &self.hi)?));
        }
        Err(Why::Fail)
    }

    /// `m` (of a node of width `w`) as the exact unsigned or signed value of the node's bits on
    /// the piece: the multiple of `2^w` that brings it into the reading's range removed. Where
    /// the bits wrap inside the piece, the piece is split where they first do.
    fn read(&self, m: &Aff, w: u16, signed: bool) -> Result<Aff, Why> {
        let m = m.reduced(w);
        let (vlo, vhi) = (m.at(&self.lo), m.at(&self.hi));
        let base = if signed {
            Int::pow2(u32::from(w) - 1).neg()
        } else {
            Int::zero()
        };
        let window = |v: &Int| v.sub(&base).shr(u32::from(w));
        let (jlo, jhi) = (window(&vlo), window(&vhi));
        if jlo == jhi {
            let off = jlo.shl(u32::from(w)).mul(&m.c);
            return Ok(Aff {
                b: m.b.sub(&off),
                ..m
            });
        }
        // The edge of lo's window that the values cross.
        let j = if jlo.lt(&jhi) {
            jlo.add(&Int::one())
        } else {
            jlo
        };
        let bound = base.add(&j.shl(u32::from(w)));
        Err(Why::Split(crossing(&m, &bound, &self.lo, &self.hi)?))
    }
}

/// A piece of the input and the node's affine floor on it, exact in the result's reading.
type Piece = (Int, Int, Aff);

/// The affine floors of `n` over `[lo, hi]` of `input`, piece by piece in order, each read
/// exactly as a `w`-bit unsigned (or signed) result; `None` when some piece has none.
fn pieces(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    input: u32,
    signed: bool,
    (lo, hi): (Int, Int),
) -> Result<Option<Vec<Piece>>, Stop> {
    let w = cx.wid(n);
    let mut todo = vec![(lo, hi)];
    let mut out: Vec<Piece> = Vec::new();
    let mut evals = 0u32;
    while let Some((lo, hi)) = todo.pop() {
        evals += 1;
        if evals > MAX_EVALS {
            return Ok(None);
        }
        let mut e = Eval {
            cx,
            input,
            lo: lo.clone(),
            hi: hi.clone(),
            memo: Vec::new(),
            work: 0,
        };
        let m = e.model(n, 0).and_then(|m| e.read(&m, w, signed));
        r.meter.charge(Counter::PassWork, u64::from(e.work))?;
        match m {
            Ok(m) => out.push((lo, hi, m)),
            Err(Why::Split(s)) => {
                if out.len() + todo.len() + 2 > MAX_PIECES {
                    return Ok(None);
                }
                todo.push((s.clone(), hi));
                todo.push((lo, s.sub(&Int::one())));
            }
            Err(Why::Fail) => return Ok(None),
        }
    }
    out.sort_by(|x, y| {
        if x.0.lt(&y.0) {
            core::cmp::Ordering::Less
        } else if y.0.lt(&x.0) {
            core::cmp::Ordering::Greater
        } else {
            core::cmp::Ordering::Equal
        }
    });
    Ok(Some(out))
}

/// The divisor the pieces suggest: their value is 0 at 0 and first changes, to 1 (or −1 for a
/// signed quotient), at `|d|`. Only a candidate: [`divides`] proves it.
fn candidate(pieces: &[Piece], signed: bool) -> Option<Int> {
    let zero = Int::zero();
    // The piece holding 0, or else the nearest one (its formula carried to 0).
    let near = |n: &Int| {
        pieces
            .iter()
            .find(|(lo, hi, _)| !n.lt(lo) && !hi.lt(n))
            .or_else(|| pieces.iter().find(|(lo, _, _)| n.lt(lo)))
            .or(pieces.last())
    };
    if near(&zero)?.2.at(&zero) != zero {
        return None;
    }
    let one = Int::one();
    let mut first = None;
    for (lo, hi, m) in pieces {
        if hi.lt(&one) {
            continue;
        }
        let s = lo.clone().max(one.clone());
        if m.at(&s) != zero {
            first = Some((s.clone(), m.at(&s)));
            break;
        }
        if m.at(hi) == zero {
            continue;
        }
        // Monotone on the piece: the first input past s where it leaves 0.
        let t = if m.a.is_neg() {
            // m(n) <= −1 iff a·n + b < 0 iff n > b / −a.
            m.b.div_floor(&m.a.neg()).add(&one)
        } else {
            // m(n) >= 1 iff a·n + b >= c.
            m.c.sub(&m.b).div_ceil(&m.a)
        };
        first = Some((t.clone(), m.at(&t)));
        break;
    }
    let (t, v) = first?;
    if v == one {
        Some(t)
    } else if signed && v == Int::of(-1) {
        Some(t.neg())
    } else {
        None
    }
}

/// Whether the pieces equal `udiv(n, d)` (`sdiv(n, d)` when signed) on every input they cover.
fn divides(pieces: &[Piece], d: &Int, signed: bool) -> bool {
    let zero = Int::zero();
    let one = Int::one();
    pieces.iter().all(|(lo, hi, m)| {
        if !signed {
            return !lo.is_neg() && agrees(m, d, lo, hi);
        }
        // trunc(n / d) = σ·floor(τ·n / |d|), with σ and τ the signs that make it so on each
        // side of 0; compare σ·m(τ·n) with floor(m / |d|) over τ·[lo, hi].
        let ad = if d.is_neg() { d.neg() } else { d.clone() };
        let side = |lo: &Int, hi: &Int, negative: bool| {
            let tau = negative;
            let sigma = negative != d.is_neg();
            let (lo, hi) = if tau {
                (hi.neg(), lo.neg())
            } else {
                (lo.clone(), hi.clone())
            };
            let a = if tau != sigma { m.a.neg() } else { m.a.clone() };
            let b = if sigma {
                m.c.sub(&one).sub(&m.b)
            } else {
                m.b.clone()
            };
            let c = m.c.clone();
            agrees(&Aff { a, b, c }, &ad, &lo, &hi)
        };
        let neg_ok = !lo.is_neg() || side(lo, &hi.clone().min(Int::of(-1)), true);
        let pos_ok = hi.is_neg() || side(&lo.clone().max(zero.clone()), hi, false);
        neg_ok && pos_ok
    })
}

/// Every value of a `w`-bit input in a reading.
fn full(w: u16, signed: bool) -> (Int, Int) {
    let width = Width::new(w).unwrap_or(Width::W64);
    if signed {
        (
            Int::signed(&BitVec::smin(width)),
            Int::signed(&BitVec::smax(width)),
        )
    } else {
        (Int::zero(), Int::unsigned(&BitVec::ones(width)))
    }
}

/// The divisor that `n` (of width `w`) divides `input` by over `range`, if it does.
fn quotient_by(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    n: u32,
    input: u32,
    signed: bool,
    range: (Int, Int),
) -> Result<Option<Int>, Stop> {
    let Some(ps) = pieces(r, cx, n, input, signed, range)? else {
        return Ok(None);
    };
    let Some(d) = candidate(&ps, signed) else {
        return Ok(None);
    };
    let w = u32::from(cx.wid(n));
    let two = Int::of(2);
    let ad = if d.is_neg() { d.neg() } else { d.clone() };
    let limit = Int::pow2(if signed { w - 1 } else { w });
    if ad.lt(&two) || !ad.lt(&limit) {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, 8 * ps.len() as u64)?;
    Ok(divides(&ps, &d, signed).then_some(d))
}

/// Whether `n` can be the last step of a quotient: a right shift or multiply-high by a
/// constant, an extract or extension (of a wider product), a negation, or a sum with a sign
/// correction or the add-and-halve step. Other sums, most of the nodes there are, are not.
fn quotient_top(cx: &Context, n: u32) -> bool {
    let node = cx.node(n);
    let by = |i: u32, s: u64| cx.const_val(i).and_then(|v| v.to_u64()) == Some(s);
    match node.op {
        OpCode::LShr | OpCode::AShr => cx.is_const(node.b),
        OpCode::Add | OpCode::Sub => {
            let top = u64::from(node.width) - 1;
            let sign = |i: u32| {
                let m = cx.node(i);
                let m = if m.op == OpCode::And && by(m.b, 1) {
                    cx.node(m.a)
                } else {
                    m
                };
                matches!(m.op, OpCode::LShr | OpCode::AShr) && by(m.b, top)
            };
            let half = |h: u32, t: u32| {
                let m = cx.node(h);
                m.op == OpCode::LShr && by(m.b, 1) && {
                    let s = cx.node(m.a);
                    s.op == OpCode::Sub && s.b == t
                }
            };
            sign(node.a) || sign(node.b) || half(node.a, node.b) || half(node.b, node.a)
        }
        _ => true,
    }
}

/// The quotient at `n`: `udiv`/`sdiv` of the multiply-high's input by the divisor it proves.
fn quotient(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let w = cx.wid(n);
    if !(2..=MAX_WIDTH).contains(&w) || !quotient_top(cx, n) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let Some((input, signed)) = core(r, cx, n)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    if cx.wid(input) != w {
        return Ok(Step::Normal(Fin::FINAL));
    }
    // Over every input first: a quotient proved there relies on no facts. Then over the
    // interval the facts bound the input to.
    let mut fin = Fin::FINAL;
    let mut d = quotient_by(r, cx, n, input, signed, full(w, signed))?;
    if d.is_none() {
        let (f, ff) = facts(r, cx, input)?;
        fin = ff;
        if let Some(f) = f {
            let bounds = if signed {
                let s = f.srange();
                (Int::signed(&s.lo()), Int::signed(&s.hi()))
            } else {
                let u = f.urange();
                (Int::unsigned(&u.lo()), Int::unsigned(&u.hi()))
            };
            if bounds != full(w, signed) {
                d = quotient_by(r, cx, n, input, signed, bounds)?;
            }
        }
    }
    let Some(d) = d else {
        r.stats
            .passes
            .entry(PassKind::Division.name())
            .or_default()
            .noop += 1;
        return Ok(Step::Normal(fin.unchanged()));
    };
    let width = cx.width_of(n);
    // `udiv(x >>u j, d)` is `udiv(x, d·2^j)` (floor(floor(x / 2^j) / d) = floor(x / (2^j·d))).
    let (x, dv) = {
        let i = cx.node(input);
        let j = (i.op == OpCode::LShr && !signed)
            .then(|| cx.const_val(i.b).and_then(|v| v.to_u64()))
            .flatten()
            .filter(|&j| j < u64::from(w));
        match j {
            Some(j) if d.shl(j as u32).lt(&Int::pow2(u32::from(w))) => (i.a, d.shl(j as u32)),
            _ => (input, d),
        }
    };
    let op = if signed { BinOp::SDiv } else { BinOp::UDiv };
    let dv = dv.to_bits(width);
    let before = cx.len() as u32;
    let e = r.build(cx, |cx| {
        let c = cx.mk_const(&dv)?;
        cx.c_bin(op, x, c)
    })?;
    // A bare multiply-high is the size of its division: the division is the normal form.
    let tie = matches!(cx.node(n).op, OpCode::UMulHi | OpCode::SMulHi);
    finish_with(r, cx, PassKind::Division, n, e, before, &[x], fin, tie)
}

// ----- remainders ------------------------------------------------------------------------------

/// Whether a quotient (a `udiv`/`sdiv`, or a product with one) is among the first nodes of the
/// linear region at `n`: what makes computing its form worthwhile.
fn has_quotient(r: &mut Runner<'_, '_>, cx: &Context, n: u32) -> Result<bool, Stop> {
    let mut stack = vec![n];
    let mut seen = 0u32;
    let quot = |i: u32| matches!(cx.node(i).op, OpCode::UDiv | OpCode::SDiv);
    while let Some(i) = stack.pop() {
        seen += 1;
        if seen > MAX_NODES {
            return Ok(false);
        }
        r.meter.charge(Counter::PassWork, 1)?;
        let node = cx.node(i);
        match node.op {
            OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Not | OpCode::Shl => {
                stack.extend(node.children().filter(|&c| !cx.is_const(c)));
            }
            OpCode::Mul => {
                if quot(node.a) || quot(node.b) {
                    return Ok(true);
                }
                stack.extend(node.children().filter(|&c| !cx.is_const(c)));
            }
            OpCode::UDiv | OpCode::SDiv => return Ok(i != n),
            _ => {}
        }
    }
    Ok(false)
}

/// For a term `t` of a linear sum: the dividend, divisor and remainder operator of the quotient
/// it is, with the factor `f` such that `c·x − c·f·t` is `c·rem(x, d)`.
fn quotient_term(cx: &Context, t: u32) -> Option<(u32, u32, BinOp, BitVec)> {
    let node = cx.node(t);
    let rem = |op: OpCode| match op {
        OpCode::UDiv => Some(BinOp::URem),
        OpCode::SDiv => Some(BinOp::SRem),
        _ => None,
    };
    match node.op {
        OpCode::UDiv | OpCode::SDiv => {
            let d = cx.const_val(node.b)?;
            Some((node.a, node.b, rem(node.op)?, d))
        }
        OpCode::Mul => {
            let one = BitVec::one(cx.width_of(t));
            [(node.a, node.b), (node.b, node.a)]
                .into_iter()
                .find_map(|(q, z)| {
                    let qn = cx.node(q);
                    (qn.b == z).then_some(())?;
                    Some((qn.a, z, rem(qn.op)?, one))
                })
        }
        _ => None,
    }
}

/// The remainder at `n`: a linear sum with `c·x` and `−c·f·q` for a quotient `q` of `x` (see
/// [`quotient_term`]) takes `c·rem(x, d)` for the two.
fn remainder(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    use super::forms::Parts;
    if !has_quotient(r, cx, n)? {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let form = linear::form_of(r, cx, n)?;
    let (konst, terms, mut fin) = {
        let (k, t, f) = form.parts();
        (*k, t.to_vec(), f)
    };
    let coeff = |t: u32| terms.iter().find(|(a, _)| *a == t).map(|(_, k)| *k);
    let mul = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Mul, a, b);
    for (t, kt) in &terms {
        let Some((x, dnode, rem, f)) = quotient_term(cx, *t) else {
            continue;
        };
        let fx = linear::form_of(r, cx, x)?;
        let (kx, tx) = {
            let (k, t, f) = fx.parts();
            fin = fin.and(f);
            (*k, t.to_vec())
        };
        // The multiple `c` of x in the sum, from x's first term.
        let Some((t1, k1)) = tx.first() else {
            continue;
        };
        let (Some(inv), Some(have)) = (crate::invert::mul_inverse(k1), coeff(*t1)) else {
            continue;
        };
        let c = mul(&have, &inv);
        // −c·f·q, and every term of c·x, are in the sum.
        let cancels = BitVec::bin_unchecked(BinOp::Add, kt, &mul(&c, &f)).is_zero()
            && tx
                .iter()
                .all(|(a, k)| a != t && coeff(*a) == Some(mul(&c, k)));
        if !cancels {
            continue;
        }
        let before = cx.len() as u32;
        let rnode = r.build(cx, |cx| cx.c_bin(rem, x, dnode))?;
        let mut rest: Vec<(u32, BitVec)> = terms
            .iter()
            .filter(|(a, _)| a != t && !tx.iter().any(|(b, _)| b == a))
            .cloned()
            .collect();
        rest.push((rnode, c));
        let k = BitVec::bin_unchecked(BinOp::Sub, &konst, &mul(&c, &kx));
        let e = linear::emit(r, cx, &Form::of(k, &rest))?;
        let mut atoms: Vec<u32> = terms
            .iter()
            .map(|(a, _)| *a)
            .filter(|a| a != t)
            .chain([x, dnode])
            .collect();
        atoms.sort_unstable();
        atoms.dedup();
        match finish_with(r, cx, PassKind::Division, n, e, before, &atoms, fin, false)? {
            Step::To(e, f) => return Ok(Step::To(e, f)),
            Step::Normal(f) => fin = fin.and(f),
        }
    }
    Ok(Step::Normal(fin.unchanged()))
}

// ----- the pass --------------------------------------------------------------------------------

/// The division pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    match cx.node(n).op {
        // A signed quotient ends in a sum (its sign correction); a remainder is one.
        OpCode::Add | OpCode::Sub => match quotient(r, cx, n)? {
            Step::Normal(f) => Ok(match remainder(r, cx, n)? {
                Step::Normal(g) => Step::Normal(f.and(g)),
                to => to,
            }),
            to => Ok(to),
        },
        OpCode::LShr
        | OpCode::AShr
        | OpCode::UMulHi
        | OpCode::SMulHi
        | OpCode::Zext
        | OpCode::Sext
        | OpCode::Extract
        | OpCode::Neg => quotient(r, cx, n),
        _ => Ok(Step::Normal(Fin::FINAL)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::tests::equivalent;
    use crate::engine::{Engine, Phase, Run, Strategy, Verify};
    use crate::testutil::Rng;
    use crate::{Context, Expr, ParseOptions, UnOp, View};

    fn aff(a: i128, b: i128, c: i128) -> Aff {
        Aff {
            a: Int::of(a),
            b: Int::of(b),
            c: Int::of(c),
        }
    }

    #[test]
    fn agrees_matches_brute_force() {
        let mut rng = Rng(0xd1f1);
        for i in 0..30_000 {
            // Powers of two (shifts), and other denominators (divisions).
            let c = if i % 2 == 0 {
                1 << rng.below(9)
            } else {
                1 + rng.below(40) as i128
            };
            let a = rng.below(80) as i128 - 20;
            let b = rng.below(300) as i128 - 150;
            let d = 1 + rng.below(12) as i128;
            let lo = rng.below(60) as i128;
            let hi = lo + rng.below(80) as i128;
            let f = aff(a, b, c);
            let want = (lo..=hi).all(|m| (a * m + b).div_euclid(c) == m.div_euclid(d));
            assert_eq!(
                agrees(&f, &Int::of(d), &Int::of(lo), &Int::of(hi)),
                want,
                "a={a} b={b} c={c} d={d} [{lo}, {hi}]"
            );
        }
    }

    #[test]
    fn integers_round_and_reduce() {
        for p in -40i128..40 {
            for d in 1i128..9 {
                assert_eq!(Int::of(p).div_floor(&Int::of(d)), Int::of(p.div_euclid(d)));
                let c = -((-p).div_euclid(d));
                assert_eq!(Int::of(p).div_ceil(&Int::of(d)), Int::of(c));
            }
            for k in 0..6u32 {
                assert_eq!(Int::of(p).shr(k), Int::of(p >> k));
            }
            for m in (2..20i128).step_by(2) {
                let r = Int::of(p).centered(&Int::of(m)).as_i128().unwrap();
                assert_eq!((r - p).rem_euclid(m), 0);
                assert!(-(m / 2) <= r && r < m / 2);
            }
        }
        assert_eq!(Int::of(5).bits(), 3);
        assert_eq!(Int::of(-5).bits(), 3);
        assert_eq!(Int::zero().bits(), 0);
    }

    // ----- through the engine ---------------------------------------------------------------

    fn alone() -> Engine {
        Engine::builder()
            .builtin()
            .strategy(Strategy::new("t", vec![Phase::Division]))
            .build()
            .unwrap()
    }

    fn deobfuscate() -> Engine {
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .verify(Verify::strict())
            .build()
            .unwrap()
    }

    fn mask(w: u32) -> u64 {
        u64::MAX >> (64 - w)
    }

    /// `v` (of `w` bits) read signed.
    fn sx(v: u64, w: u32) -> i64 {
        ((v << (64 - w)) as i64) >> (64 - w)
    }

    /// The divisor `f` (a function of `w`-bit inputs) divides by: `Some(d)` when it is
    /// `udiv(x, d)` (`sdiv(x, d)` if `signed`) at every input, `2 <= |d| < 2^w` (`2^(w−1)`
    /// signed).
    fn divisor(f: &dyn Fn(u64) -> u64, w: u32, signed: bool) -> Option<i64> {
        let m = mask(w);
        if f(0) != 0 {
            return None;
        }
        let top = if signed { m >> 1 } else { m };
        let (x, v) = (1..=top).map(|x| (x, f(x))).find(|&(_, v)| v != 0)?;
        let d = match v {
            1 if x >= 2 => x as i64,
            v if signed && v == m && x >= 2 => -(x as i64),
            _ => return None,
        };
        let want = |x: u64| {
            if signed {
                ((sx(x, w) / d) as u64) & m
            } else {
                x / d as u64
            }
        };
        (0..=m).all(|x| f(x) == want(x)).then_some(d)
    }

    /// `e` (over the symbol `x`) after `eng`: the divisor when it became `udiv(x, d)` (`sdiv`
    /// if `signed`), `None` otherwise; then it must agree with `e` at every input (a part of
    /// it may have become a division: `umulhi(x, 2) >>u 1` is `udiv(x, 2^(W−1)) >>u 1`).
    fn recovered(eng: &Engine, cx: &mut Context, e: Expr, x: Expr, signed: bool) -> Option<i64> {
        let out = eng.run(cx, &[e], Run::default()).unwrap().roots[0].expr;
        let op = if signed { BinOp::SDiv } else { BinOp::UDiv };
        match cx.view(out).unwrap() {
            View::Bin(o, a, c) if o == op && a == x => {
                let c = cx.as_const(c).unwrap().unwrap();
                Some(if signed {
                    c.to_i128().unwrap() as i64
                } else {
                    c.to_u64().unwrap() as i64
                })
            }
            _ => {
                assert!(
                    out == e || equivalent(cx, e, out, &mut Rng(1)),
                    "{} became {}",
                    cx.display(e),
                    cx.display(out)
                );
                None
            }
        }
    }

    /// A sequence over `x` at `w` bits, built with the multiplier and shift given, and the same
    /// computed natively (with the multiplier and the input as `w`-bit values).
    struct Form {
        name: &'static str,
        signed: bool,
        /// Multipliers `0..2^(w + extra)`.
        extra: u32,
        build: fn(&mut Context, Expr, u64, u32, u32) -> Expr,
        eval: fn(u64, u64, u32, u32) -> u64,
    }

    fn k(cx: &mut Context, w: u32, v: u64) -> Expr {
        cx.constant_u64(Width::new(w as u16).unwrap(), v).unwrap()
    }

    fn b2(cx: &mut Context, op: BinOp, a: Expr, b: Expr) -> Expr {
        cx.bin(op, a, b).unwrap()
    }

    fn sh(cx: &mut Context, op: BinOp, a: Expr, s: u32, w: u32) -> Expr {
        if s == 0 {
            return a;
        }
        let c = k(cx, w, u64::from(s));
        b2(cx, op, a, c)
    }

    fn umulhi(a: u64, b: u64, w: u32) -> u64 {
        ((u128::from(a) * u128::from(b)) >> w) as u64
    }

    fn smulhi(a: u64, b: u64, w: u32) -> u64 {
        ((i128::from(sx(a, w)) * i128::from(sx(b, w))) >> w) as u64 & mask(w)
    }

    fn ashr(a: u64, s: u32, w: u32) -> u64 {
        (sx(a, w) >> s) as u64 & mask(w)
    }

    /// `q0 + (q0 >>u (w − 1))`: the correction by the quotient's sign (LLVM).
    fn by_quotient_sign(cx: &mut Context, q: Expr, w: u32) -> Expr {
        let t = sh(cx, BinOp::LShr, q, w - 1, w);
        b2(cx, BinOp::Add, q, t)
    }

    fn forms() -> Vec<Form> {
        vec![
            Form {
                name: "umulhi(x, M) >>u s",
                signed: false,
                extra: 0,
                build: |cx, x, m, s, w| {
                    let c = k(cx, w, m);
                    let t = b2(cx, BinOp::UMulHi, x, c);
                    sh(cx, BinOp::LShr, t, s, w)
                },
                eval: |x, m, s, w| umulhi(x, m, w) >> s,
            },
            Form {
                name: "(t + ((x - t) >>u 1)) >>u s, t = umulhi(x, M)",
                signed: false,
                extra: 0,
                build: |cx, x, m, s, w| {
                    let c = k(cx, w, m);
                    let t = b2(cx, BinOp::UMulHi, x, c);
                    let d = b2(cx, BinOp::Sub, x, t);
                    let h = sh(cx, BinOp::LShr, d, 1, w);
                    let a = b2(cx, BinOp::Add, t, h);
                    sh(cx, BinOp::LShr, a, s, w)
                },
                eval: |x, m, s, w| {
                    let t = umulhi(x, m, w);
                    ((t + ((x.wrapping_sub(t) & mask(w)) >> 1)) & mask(w)) >> s
                },
            },
            Form {
                name: "trunc((zext(x) * M) >>u (w + s))",
                signed: false,
                extra: 1,
                build: |cx, x, m, s, w| {
                    let ww = Width::new(2 * w as u16).unwrap();
                    let z = cx.zext(x, ww).unwrap();
                    let c = k(cx, 2 * w, m);
                    let p = b2(cx, BinOp::Mul, z, c);
                    let q = sh(cx, BinOp::LShr, p, w + s, 2 * w);
                    cx.trunc(q, Width::new(w as u16).unwrap()).unwrap()
                },
                eval: |x, m, s, w| ((x * m) & mask(2 * w)) >> (w + s) & mask(w),
            },
            Form {
                name: "(smulhi(x, M) >>s s) + (x >>u (w - 1))",
                signed: true,
                extra: 0,
                build: |cx, x, m, s, w| {
                    let c = k(cx, w, m);
                    let t = b2(cx, BinOp::SMulHi, x, c);
                    let q = sh(cx, BinOp::AShr, t, s, w);
                    let sign = sh(cx, BinOp::LShr, x, w - 1, w);
                    b2(cx, BinOp::Add, q, sign)
                },
                eval: |x, m, s, w| (ashr(smulhi(x, m, w), s, w) + (x >> (w - 1))) & mask(w),
            },
            Form {
                name: "q + (q >>u (w - 1)), q = smulhi(x, M) >>s s",
                signed: true,
                extra: 0,
                build: |cx, x, m, s, w| {
                    let c = k(cx, w, m);
                    let t = b2(cx, BinOp::SMulHi, x, c);
                    let q = sh(cx, BinOp::AShr, t, s, w);
                    by_quotient_sign(cx, q, w)
                },
                eval: |x, m, s, w| {
                    let q = ashr(smulhi(x, m, w), s, w);
                    (q + (q >> (w - 1))) & mask(w)
                },
            },
            Form {
                name: "q + (q >>u (w - 1)), q = (smulhi(x, M) + x) >>s s",
                signed: true,
                extra: 0,
                build: |cx, x, m, s, w| {
                    let c = k(cx, w, m);
                    let t = b2(cx, BinOp::SMulHi, x, c);
                    let t = b2(cx, BinOp::Add, t, x);
                    let q = sh(cx, BinOp::AShr, t, s, w);
                    by_quotient_sign(cx, q, w)
                },
                eval: |x, m, s, w| {
                    let q = ashr((smulhi(x, m, w) + x) & mask(w), s, w);
                    (q + (q >> (w - 1))) & mask(w)
                },
            },
            Form {
                name: "q + (q >>u (w - 1)), q = (smulhi(x, M) - x) >>s s",
                signed: true,
                extra: 0,
                build: |cx, x, m, s, w| {
                    let c = k(cx, w, m);
                    let t = b2(cx, BinOp::SMulHi, x, c);
                    let t = b2(cx, BinOp::Sub, t, x);
                    let q = sh(cx, BinOp::AShr, t, s, w);
                    by_quotient_sign(cx, q, w)
                },
                eval: |x, m, s, w| {
                    let q = ashr(smulhi(x, m, w).wrapping_sub(x) & mask(w), s, w);
                    (q + (q >> (w - 1))) & mask(w)
                },
            },
            Form {
                name: "((smulhi(x, M) + x) >>s s) - (x >>s (w - 1))",
                signed: true,
                extra: 0,
                build: |cx, x, m, s, w| {
                    let c = k(cx, w, m);
                    let t = b2(cx, BinOp::SMulHi, x, c);
                    let t = b2(cx, BinOp::Add, t, x);
                    let q = sh(cx, BinOp::AShr, t, s, w);
                    let sign = sh(cx, BinOp::AShr, x, w - 1, w);
                    b2(cx, BinOp::Sub, q, sign)
                },
                eval: |x, m, s, w| {
                    let q = ashr((smulhi(x, m, w) + x) & mask(w), s, w);
                    q.wrapping_sub(ashr(x, w - 1, w)) & mask(w)
                },
            },
            Form {
                name: "trunc((sext(x) * M) >>s (w + s)) - (x >>s (w - 1))",
                signed: true,
                extra: 1,
                build: |cx, x, m, s, w| {
                    let ww = Width::new(2 * w as u16).unwrap();
                    let e = cx.sext(x, ww).unwrap();
                    // M − 2^w: multipliers of either sign.
                    let c = k(cx, 2 * w, m.wrapping_sub(1 << w) & mask(2 * w));
                    let p = b2(cx, BinOp::Mul, e, c);
                    let q = sh(cx, BinOp::AShr, p, w + s, 2 * w);
                    let q = cx.trunc(q, Width::new(w as u16).unwrap()).unwrap();
                    let sign = sh(cx, BinOp::AShr, x, w - 1, w);
                    b2(cx, BinOp::Sub, q, sign)
                },
                eval: |x, m, s, w| {
                    let c = m as i64 - (1 << w);
                    // The product wraps at 2w bits like the register's.
                    let p = sx((sx(x, w) * c) as u64 & mask(2 * w), 2 * w) >> (w + s);
                    (p as u64).wrapping_sub(ashr(x, w - 1, w)) & mask(w)
                },
            },
        ]
    }

    /// Whether a product is left in `e` after the builder's folding.
    fn multiplies(cx: &mut Context, e: Expr) -> bool {
        cx.post_order(&[e]).unwrap().into_iter().any(|n| {
            matches!(
                cx.view(n).unwrap(),
                View::Bin(BinOp::UMulHi | BinOp::SMulHi | BinOp::Mul, ..)
            )
        })
    }

    /// Every multiplier and shift of every form at the widths given: the pass rewrites a
    /// sequence exactly when it is a division, and into that division.
    fn sweep(widths: core::ops::RangeInclusive<u32>, which: &[&str]) -> u32 {
        let eng = alone();
        let mut found = 0;
        for f in forms()
            .iter()
            .filter(|f| which.is_empty() || which.contains(&f.name))
        {
            for w in widths.clone() {
                for m in 0..1u64 << (w + f.extra) {
                    for s in 0..w {
                        let want = divisor(&|x| (f.eval)(x, m, s, w), w, f.signed);
                        let mut cx = Context::new();
                        let x = cx.symbol("x", Width::new(w as u16).unwrap()).unwrap();
                        let e = (f.build)(&mut cx, x, m, s, w);
                        let got = recovered(&eng, &mut cx, e, x, f.signed);
                        // (A multiplier of 0 or 1 leaves shifts, which are no business of the
                        // pass's even where they divide.)
                        if multiplies(&mut cx, e) {
                            assert_eq!(got, want, "w={w} M={m} s={s}: {}", f.name);
                        }
                        found += u32::from(got.is_some());
                    }
                }
            }
        }
        found
    }

    /// Every multiplier and shift at up to 8 bits, of every form: exhaustively sound and
    /// complete.
    #[test]
    fn every_multiplier_of_every_form() {
        assert!(sweep(2..=8, &[]) > 2000);
    }

    /// The unsigned forms at 9 and 10 bits too.
    #[test]
    fn every_unsigned_multiplier_to_ten_bits() {
        let forms = [
            "umulhi(x, M) >>u s",
            "(t + ((x - t) >>u 1)) >>u s, t = umulhi(x, M)",
        ];
        assert!(sweep(9..=10, &forms) > 1000);
    }

    /// The unsigned magic of Hacker's Delight (§10-8, as LLVM computes it) for inputs below
    /// `2^bits` and a `w`-bit multiply: the least `p >= w` with
    /// `2^p > nc·(d − 1 − (2^p − 1) mod d)`, `nc` the greatest input that is `d − 1` modulo `d`;
    /// the multiplier `(2^p + d − 1 − (2^p − 1) mod d) / d` (up to `w + 1` bits) and `p − w`.
    fn magic_u(d: u128, w: u32, bits: u32) -> (u128, u32) {
        let top = 1u128 << bits;
        let nc = top - 1 - (top - d) % d;
        let mut p = w;
        loop {
            let tp = 1u128 << p;
            let r = (tp - 1) % d;
            if tp > nc * (d - 1 - r) {
                return ((tp + d - 1 - r) / d, p - w);
            }
            p += 1;
        }
    }

    /// The signed magic of Hacker's Delight (fig. 10-1) at `w` bits, `2 <= |d| < 2^(w−1)`: the
    /// multiplier (read signed) and the shift.
    fn magic_s(d: i128, w: u32) -> (i128, u32) {
        let two = 1u128 << (w - 1);
        let ad = d.unsigned_abs();
        let t = two + u128::from(d < 0);
        let anc = t - 1 - t % ad;
        let mut p = w - 1;
        let (mut q1, mut r1) = (two / anc, two % anc);
        let (mut q2, mut r2) = (two / ad, two % ad);
        loop {
            p += 1;
            q1 *= 2;
            r1 *= 2;
            if r1 >= anc {
                q1 += 1;
                r1 -= anc;
            }
            q2 *= 2;
            r2 *= 2;
            if r2 >= ad {
                q2 += 1;
                r2 -= ad;
            }
            let delta = ad - r2;
            if !(q1 < delta || (q1 == delta && r1 == 0)) {
                break;
            }
        }
        let m = (q2 + 1) as i128;
        let m = if m >= 1 << (w - 1) { m - (1 << w) } else { m };
        (if d < 0 { -m } else { m }, p - w)
    }

    /// The compiler sequences for one divisor at `w` bits (at most 64), as source text over
    /// `x`, each with the operation it computes: the unsigned quotient (LLVM's, with the add
    /// step or the pre-shift where the multiplier needs it, and in a register twice as wide at
    /// 32 bits, GCC's), the signed one (LLVM's correction by the quotient's sign, GCC's by the
    /// input's), and the remainders from them.
    fn sequences(d: i128, w: u32) -> Vec<(String, String)> {
        let mut out = Vec::new();
        let hex = |v: u128| format!("{v:#x}");
        let wm = |v: i128| (v as u128) & (u128::MAX >> (128 - w));
        if d > 0 && !(d as u128).is_power_of_two() {
            let du = d as u128;
            let (m, s) = magic_u(du, w, w);
            let q = if m < 1 << w {
                if s == 0 {
                    format!("umulhi(x, {})", hex(m))
                } else {
                    format!("(umulhi(x, {}) >>u {s})", hex(m))
                }
            } else {
                let m0 = hex(m - (1 << w));
                format!(
                    "((umulhi(x, {m0}) + ((x - umulhi(x, {m0})) >>u 1)) >>u {})",
                    s - 1
                )
            };
            out.push((q.clone(), format!("udiv(x, {d})")));
            out.push((format!("x - {d} * {q}"), format!("urem(x, {d})")));
            let j = du.trailing_zeros();
            if j > 0 && m >= 1 << w {
                let (m, s) = magic_u(du >> j, w, w - j);
                assert!(m < 1 << w);
                let q = format!("(umulhi(x >>u {j}, {}) >>u {s})", hex(m));
                out.push((q, format!("udiv(x, {d})")));
            }
            if w == 32 {
                let q = if m < 1 << 32 {
                    format!("trunc<32>((zext<64>(x) * {}) >>u {})", hex(m), 32 + s)
                } else {
                    let m0 = hex(m - (1 << 32));
                    let t = format!("trunc<32>((zext<64>(x) * {m0}) >>u 32)");
                    format!("(({t} + ((x - {t}) >>u 1)) >>u {})", s - 1)
                };
                out.push((q.clone(), format!("udiv(x, {d})")));
                out.push((format!("x - {q} * {d}"), format!("urem(x, {d})")));
            }
            if w == 64 && m < 1 << 64 {
                let q = format!("(extract<64, 64>(zext<128>(x) * {}) >>u {s})", hex(m));
                out.push((q, format!("udiv(x, {d})")));
            }
        }
        let ad = d.unsigned_abs();
        if (2..1 << (w - 1)).contains(&ad) && !ad.is_power_of_two() {
            let (m, s) = magic_s(d, w);
            let mut t = format!("smulhi(x, {})", hex(wm(m)));
            if d > 0 && m < 0 {
                t = format!("({t} + x)");
            } else if d < 0 && m > 0 {
                t = format!("({t} - x)");
            }
            let q = format!("({t} >>s {s})");
            let llvm = format!("({q} + ({q} >>u {}))", w - 1);
            out.push((llvm.clone(), format!("sdiv(x, {d})")));
            out.push((format!("x - {llvm} * {d}"), format!("srem(x, {d})")));
            // GCC: the input's sign, and the quotient by |d| negated for a negative divisor.
            let (m, s) = magic_s(ad as i128, w);
            let t = if m < 0 {
                format!("(smulhi(x, {}) + x)", hex(wm(m)))
            } else {
                format!("smulhi(x, {})", hex(wm(m)))
            };
            let sign = format!("(x >>s {})", w - 1);
            let gcc = if d > 0 {
                format!("(({t} >>s {s}) - {sign})")
            } else {
                format!("({sign} - ({t} >>s {s}))")
            };
            out.push((gcc.clone(), format!("sdiv(x, {d})")));
            out.push((format!("x - {d} * {gcc}"), format!("srem(x, {d})")));
            if w == 32 && d > 0 && m > 0 {
                let q = format!(
                    "(trunc<32>((sext<64>(x) * {}) >>s {}) - {sign})",
                    hex(m as u128),
                    32 + s
                );
                out.push((q.clone(), format!("sdiv(x, {d})")));
                out.push((format!("x - {d} * {q}"), format!("srem(x, {d})")));
            }
        }
        out
    }

    fn fixtures(eng: &Engine, w: u32, divisors: &[i128]) -> usize {
        let o = ParseOptions::width(Width::new(w as u16).unwrap());
        let mut rng = Rng(u64::from(w));
        let mut n = 0;
        for &d in divisors {
            for (src, want) in sequences(d, w) {
                let mut cx = Context::new();
                let e = cx.parse(&src, &o).unwrap();
                let want = cx.parse(&want, &o).unwrap();
                let out = eng.simplify(&mut cx, e).unwrap();
                assert_eq!(
                    out.expr,
                    want,
                    "w={w} d={d}: {src} gave {}",
                    cx.display(out.expr)
                );
                if w > 32 {
                    assert!(equivalent(&mut cx, e, want, &mut rng), "{src}");
                }
                n += 1;
            }
        }
        n
    }

    /// Every divisor at up to 10 bits, every sequence a compiler emits for it.
    #[test]
    fn every_divisor_to_ten_bits() {
        let eng = alone();
        let mut rng = Rng(7);
        for w in 3..=10u32 {
            let o = ParseOptions::width(Width::new(w as u16).unwrap());
            let top = 1i128 << w;
            for d in (-(top / 2) + 1)..top {
                for (src, want) in sequences(d, w) {
                    let mut cx = Context::new();
                    let e = cx.parse(&src, &o).unwrap();
                    let want = cx.parse(&want, &o).unwrap();
                    let out = eng.simplify(&mut cx, e).unwrap();
                    assert_eq!(
                        out.expr,
                        want,
                        "w={w} d={d}: {src} gave {}",
                        cx.display(out.expr)
                    );
                    assert!(equivalent(&mut cx, e, want, &mut rng), "{src}");
                }
            }
        }
    }

    /// Divisors at 32 and 64 bits through the deobfuscation strategy, remainders included.
    #[test]
    fn compiler_sequences_at_32_and_64_bits() {
        let eng = deobfuscate();
        let mut ds: Vec<i128> = (2..=64).collect();
        ds.extend([
            100,
            641,
            1000,
            6700417,
            1_000_000_007,
            0x7fff_ffff,
            0x3fff_ffff,
            274_177,
            67_280_421_310_721,
            1_000_000_000_000_000_007,
        ]);
        let mut rng = Rng(0xd1c);
        for _ in 0..40 {
            let bits = 2 + rng.below(60) as u32;
            ds.push(i128::from(rng.next() >> (64 - bits)) | 1);
        }
        let neg: Vec<i128> = ds.iter().map(|d| -d).collect();
        ds.extend(neg);
        let d32: Vec<i128> = ds
            .iter()
            .copied()
            .filter(|d| d.unsigned_abs() < 1 << 32)
            .chain([0xffff_fffb, 0xffff_ffff, 0x8000_0001])
            .collect();
        let d64: Vec<i128> = ds
            .iter()
            .copied()
            .filter(|d| d.unsigned_abs() < 1 << 62)
            .collect();
        assert!(fixtures(&eng, 32, &d32) > 1000);
        assert!(fixtures(&eng, 64, &d64) > 1000);
    }

    /// Near misses stay: a multiplier one off, a shift one short, a product that overflows its
    /// register, a sign correction by the wrong sign.
    #[test]
    fn near_misses_stay() {
        let eng = deobfuscate();
        let o = ParseOptions::width(Width::W32);
        let mut rng = Rng(5);
        for src in [
            "umulhi(x, 0xaaaaaaaa) >>u 1",
            "umulhi(x, 0xaaaaaaab)",
            "umulhi(x, 0x24924925) >>u 2",
            "(umulhi(x, 0x24924924) + ((x - umulhi(x, 0x24924924)) >>u 1)) >>u 2",
            "trunc<32>((zext<64>(x) * 0x124924925) >>u 35)",
            "smulhi(x, 0x55555556) - (x >>u 31)",
            "(smulhi(x, 0x92492493) >>s 2) + (x >>u 31)",
            "smulhi(x, 0x55555555) + (x >>u 31)",
        ] {
            let mut cx = Context::new();
            let e = cx.parse(src, &o).unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            let shown = cx.display(out.expr).to_string();
            assert!(!shown.contains("div"), "{src} became {shown}");
            assert!(equivalent(&mut cx, e, out.expr, &mut rng), "{src}");
        }
    }

    /// The facts' bounds on the input admit a multiplier valid only below them.
    #[test]
    fn bounded_inputs_admit_smaller_multipliers() {
        let eng = deobfuscate();
        let o = ParseOptions::width(Width::W32);
        let mut rng = Rng(11);
        // ceil(2^34 / 7) = 0x92492493 is exact for inputs below 2^31 only (LLVM uses it when
        // the dividend has a leading zero).
        for (src, want) in [
            (
                "umulhi(x & 0x7fffffff, 0x92492493) >>u 2",
                "udiv(x & 0x7fffffff, 7)",
            ),
            ("umulhi(x, 0x92492493) >>u 2", ""),
            (
                "umulhi(zext<32>(y:8), 0xcccccccd) >>u 3",
                "udiv(zext<32>(y:8), 10)",
            ),
        ] {
            let mut cx = Context::new();
            let e = cx.parse(src, &o).unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            if want.is_empty() {
                assert!(!cx.display(out.expr).to_string().contains("div"), "{src}");
            } else {
                let want = cx.parse(want, &o).unwrap();
                assert_eq!(out.expr, want, "{src}: {}", cx.display(out.expr));
            }
            assert!(equivalent(&mut cx, e, out.expr, &mut rng), "{src}");
        }
    }

    /// A bound the run assumes admits a multiplier too, and the result relies on that
    /// assumption only; one proved over every input relies on none.
    #[test]
    fn assumed_bounds_are_relied_on() {
        let eng = deobfuscate();
        let o = ParseOptions::width(Width::W32);
        let mut cx = Context::new();
        let small = cx.parse("umulhi(x, 0x92492493) >>u 2", &o).unwrap();
        let plain = cx.parse("umulhi(x, 0xaaaaaaab) >>u 1", &o).unwrap();
        let below = cx.parse("x <u 1000", &o).unwrap();
        let other = cx.parse("y <u 5", &o).unwrap();
        let mut a = crate::Assumptions::new();
        let u = a.assume_true(&mut cx, other).unwrap();
        let id = a.assume_true(&mut cx, below).unwrap();
        let run = |cx: &mut Context, e| eng.run(cx, &[e], Run::default().with_assumptions(&a));
        let out = run(&mut cx, small).unwrap().roots[0];
        assert_eq!(cx.display(out.expr).to_string(), "udiv(x, 7)");
        assert!(out.relies_on.may_use(id) && !out.relies_on.may_use(u));
        let out = run(&mut cx, plain).unwrap().roots[0];
        assert_eq!(cx.display(out.expr).to_string(), "udiv(x, 3)");
        assert!(!out.relies_on.may_use(id) && !out.relies_on.may_use(u));
        // Without the assumption the first is no division.
        let out = eng.simplify(&mut cx, small).unwrap();
        assert!(!cx.display(out.expr).to_string().contains("div"));
    }

    /// Remainders from quotients however the sum spells the product, and by a divisor that is
    /// not a constant.
    #[test]
    fn remainders_from_quotients() {
        let eng = deobfuscate();
        let o = ParseOptions::width(Width::W32);
        for (src, want) in [
            ("x - udiv(x, 7) * 7", "urem(x, 7)"),
            ("udiv(x, 7) * 0xfffffff9 + x", "urem(x, 7)"),
            ("x - (udiv(x, 3) + (udiv(x, 3) << 1))", "urem(x, 3)"),
            ("3 * x - 21 * udiv(x, 7) + y", "3 * urem(x, 7) + y"),
            ("x - sdiv(x, -5) * -5", "srem(x, -5)"),
            ("x - udiv(x, y) * y", "urem(x, y)"),
            ("x - y * sdiv(x, y)", "srem(x, y)"),
            ("(x + z) - udiv(x + z, 10) * 10", "urem(x + z, 10)"),
            // Not a remainder: the quotient of another dividend, or another multiple.
            ("x - udiv(y, 7) * 7", "x - udiv(y, 7) * 7"),
            ("x - udiv(x, 7) * 6", "x - udiv(x, 7) * 6"),
        ] {
            let mut cx = Context::new();
            let e = cx.parse(src, &o).unwrap();
            let want = cx.parse(want, &o).unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            assert_eq!(out.expr, want, "{src}: {}", cx.display(out.expr));
        }
    }

    /// A quotient divided, shifted or negated further is one division; one that is not a
    /// division of the input stays.
    #[test]
    fn quotients_compose() {
        let eng = deobfuscate();
        let o = ParseOptions::width(Width::W32);
        let mut rng = Rng(13);
        for (src, want) in [
            ("udiv(x, 3) >>u 2", "udiv(x, 12)"),
            ("-sdiv(x, 7)", "sdiv(x, -7)"),
            ("-sdiv(x, -9)", "sdiv(x, 9)"),
            // The inner multiply-high is x / 641 already.
            ("umulhi(x, 6700417) >>u 1", "udiv(x, 1282)"),
            // floor(trunc(x / 3) / 2) is no truncating division.
            ("sdiv(x, 3) >>s 1", "sdiv(x, 3) >>s 1"),
            (
                "sdiv(x, 6) + (sdiv(x, 6) >>u 31)",
                "sdiv(x, 6) + (sdiv(x, 6) >>u 31)",
            ),
        ] {
            let mut cx = Context::new();
            let e = cx.parse(src, &o).unwrap();
            let want = cx.parse(want, &o).unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            assert_eq!(out.expr, want, "{src}: {}", cx.display(out.expr));
            assert!(equivalent(&mut cx, e, out.expr, &mut rng), "{src}");
        }
    }

    /// A sign bit taken with a mask, as a lifter may write it, is a sign bit (with the division
    /// pass alone, which no rule tidies first).
    #[test]
    fn masked_sign_bits() {
        let eng = alone();
        let o = ParseOptions::width(Width::W32);
        for (src, want) in [
            ("smulhi(x, 0x55555556) + ((x >>u 31) & 1)", "sdiv(x, 3)"),
            (
                "((smulhi(x, 0x92492493) + x) >>s 2) + ((((smulhi(x, 0x92492493) + x) >>s 2) >>u 31) & 1)",
                "sdiv(x, 7)",
            ),
            // Not the sign: no quotient.
            ("smulhi(x, 0x55555556) + (x >>u 30)", ""),
        ] {
            let mut cx = Context::new();
            let e = cx.parse(src, &o).unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            if want.is_empty() {
                assert_eq!(out.expr, e, "{src}: {}", cx.display(out.expr));
            } else {
                let want = cx.parse(want, &o).unwrap();
                assert_eq!(out.expr, want, "{src}: {}", cx.display(out.expr));
            }
        }
    }

    /// A shift of the dividend merges into the divisor only when their product fits: a
    /// quotient by 20 of `y >>u 4` (at most 15) is 0, never `udiv(y, 320 mod 256)`.
    #[test]
    fn pre_shifts_merge_when_the_divisor_fits() {
        let eng = alone();
        let mut rng = Rng(17);
        for (d, j, merged) in [
            (20u128, 4u32, false),
            (3, 2, true),
            (15, 4, true),
            (17, 4, false),
        ] {
            let (m, s) = magic_u(d, 8, 8);
            if m >= 1 << 8 {
                continue;
            }
            let src = format!("umulhi(y >>u {j}, {m}) >>u {s}");
            let mut cx = Context::new();
            let e = cx.parse(&src, &ParseOptions::width(Width::W8)).unwrap();
            let out = eng.simplify(&mut cx, e).unwrap();
            let shown = cx.display(out.expr).to_string();
            assert_eq!(!shown.contains(">>u"), merged, "{src}: {shown}");
            assert!(equivalent(&mut cx, e, out.expr, &mut rng), "{src}: {shown}");
        }
    }

    /// The other built-in strategies keep a compiler's strength reduction.
    #[test]
    fn only_deobfuscation_divides() {
        let o = ParseOptions::width(Width::W32);
        for strategy in [Strategy::standard(), Strategy::compile()] {
            let eng = Engine::builder()
                .builtin()
                .strategy(strategy)
                .build()
                .unwrap();
            for src in [
                "umulhi(x, 0xaaaaaaab) >>u 1",
                "((smulhi(x, 0x92492493) + x) >>s 2) + (x >>u 31)",
            ] {
                let mut cx = Context::new();
                let e = cx.parse(src, &o).unwrap();
                let out = eng.simplify(&mut cx, e).unwrap();
                assert!(!cx.display(out.expr).to_string().contains("div"), "{src}");
            }
        }
    }

    /// A random expression over one input built from the operators the pass reads, around
    /// a multiply-high by a constant.
    fn random_sequence(rng: &mut Rng, cx: &mut Context, x: Expr, w: u32, depth: u32) -> Expr {
        let width = Width::new(w as u16).unwrap();
        let konst = |rng: &mut Rng, cx: &mut Context| {
            let v = rng.next() & mask(w);
            cx.constant_u64(width, v).unwrap()
        };
        if depth == 0 || rng.chance(1, 5) {
            return if rng.chance(3, 4) { x } else { konst(rng, cx) };
        }
        let d = depth - 1;
        let shift = |rng: &mut Rng, cx: &mut Context| {
            cx.constant_u64(width, rng.below(u64::from(w) + 1)).unwrap()
        };
        match rng.below(12) {
            0 | 1 => {
                let a = random_sequence(rng, cx, x, w, d);
                let c = konst(rng, cx);
                let op = if rng.chance(1, 2) {
                    BinOp::UMulHi
                } else {
                    BinOp::SMulHi
                };
                cx.bin(op, a, c).unwrap()
            }
            2 | 3 => {
                let a = random_sequence(rng, cx, x, w, d);
                let s = shift(rng, cx);
                let op = [BinOp::LShr, BinOp::AShr, BinOp::Shl][rng.below(3) as usize];
                cx.bin(op, a, s).unwrap()
            }
            4 | 5 => {
                let a = random_sequence(rng, cx, x, w, d);
                let b = random_sequence(rng, cx, x, w, d);
                let op = if rng.chance(1, 2) {
                    BinOp::Add
                } else {
                    BinOp::Sub
                };
                cx.bin(op, a, b).unwrap()
            }
            6 => {
                let a = random_sequence(rng, cx, x, w, d);
                let op = if rng.chance(1, 2) {
                    UnOp::Neg
                } else {
                    UnOp::Not
                };
                cx.un(op, a).unwrap()
            }
            7 => {
                let a = random_sequence(rng, cx, x, w, d);
                let c = konst(rng, cx);
                let op = [BinOp::Mul, BinOp::UDiv, BinOp::SDiv][rng.below(3) as usize];
                cx.bin(op, a, c).unwrap()
            }
            8 => {
                // The add-and-halve step over a multiply-high.
                let c = konst(rng, cx);
                let t = cx.bin(BinOp::UMulHi, x, c).unwrap();
                let u = random_sequence(rng, cx, x, w, d);
                let s = cx.bin(BinOp::Sub, u, t).unwrap();
                let one = cx.constant_u64(width, 1).unwrap();
                let h = cx.bin(BinOp::LShr, s, one).unwrap();
                cx.bin(BinOp::Add, t, h).unwrap()
            }
            9 => {
                // A sign correction.
                let q = random_sequence(rng, cx, x, w, d);
                let top = cx.constant_u64(width, u64::from(w - 1)).unwrap();
                let sign = cx.bin(BinOp::LShr, q, top).unwrap();
                cx.bin(BinOp::Add, q, sign).unwrap()
            }
            _ => {
                // The same in a register twice as wide.
                let ww = Width::new(2 * w as u16).unwrap();
                let a = random_sequence(rng, cx, x, w, d);
                let e = if rng.chance(1, 2) {
                    cx.zext(a, ww).unwrap()
                } else {
                    cx.sext(a, ww).unwrap()
                };
                let c = cx.constant_u64(ww, rng.next() & mask(2 * w)).unwrap();
                let p = cx.bin(BinOp::Mul, e, c).unwrap();
                let s = cx
                    .constant_u64(ww, u64::from(w) + rng.below(u64::from(w)))
                    .unwrap();
                let op = if rng.chance(1, 2) {
                    BinOp::LShr
                } else {
                    BinOp::AShr
                };
                let q = cx.bin(op, p, s).unwrap();
                if rng.chance(1, 2) {
                    cx.trunc(q, width).unwrap()
                } else {
                    let lo = rng.below(u64::from(w) + 1) as u16;
                    cx.extract(q, lo, width).unwrap()
                }
            }
        }
    }

    /// Whatever the pass makes of random sequences agrees with them at every input, and is
    /// left as it is when simplified again.
    #[test]
    fn random_sequences_are_sound_and_idempotent() {
        let eng = alone();
        let full = deobfuscate();
        let mut rng = Rng(0xd1d1);
        let mut check = Rng(3);
        let mut changed = 0;
        for i in 0..6000 {
            let w = 2 + (i % 6) as u32;
            let mut cx = Context::new();
            let x = cx.symbol("x", Width::new(w as u16).unwrap()).unwrap();
            let e = random_sequence(&mut rng, &mut cx, x, w, 4);
            let eng = if i % 7 == 0 { &full } else { &eng };
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            let r = out.roots[0];
            assert_eq!(out.stats.rejected, 0, "{}", cx.display(e));
            assert!(
                equivalent(&mut cx, e, r.expr, &mut check),
                "W={w}: {} vs {}",
                cx.display(e),
                cx.display(r.expr)
            );
            if cx.display(r.expr).to_string().contains("div") {
                changed += 1;
            }
            cx.memo.clear();
            let again = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
            assert_eq!(
                again.roots[0].expr,
                r.expr,
                "not idempotent: {} -> {}",
                cx.display(r.expr),
                cx.display(again.roots[0].expr)
            );
        }
        assert!(changed > 100, "{changed}");
    }
}
