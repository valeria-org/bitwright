//! The semantics of a program as bitwright expressions (LLVM's language reference, read as
//! mathematics): each value is a pair of its bits and a 1-bit poison flag; a program has a
//! 1-bit undefined-behavior condition; and each nondeterministic choice (an `undef` use, a
//! `freeze` of poison, the sign and payload of a NaN a floating-point operation returns, a
//! zero's sign under `nsz`, `llvm.fmuladd` fusing or not) is a fresh leaf whose allowed values
//! are stated by a validity condition.

use std::collections::{BTreeMap, HashMap};

use super::ir::{
    Body, CFun, FPred, IPred, Intrinsic, Lit, Node, NodeId, Op, PFun, Term, Transform, Ty, flags,
};
use super::llvm::fpclass;
use crate::fp::FpOp;
use crate::fp::{FpCmpOp, FpFormat, FpTest, RoundingMode};
use crate::{BinOp, BitVec, CmpOpExt, Context, Error, Expr, SymbolKey, UnOp, Width};

/// Symbol keys: inputs (value, poison), symbolic constants, and each side's choices.
pub(crate) const INPUT_KEY: u64 = 1 << 32;
pub(crate) const CONST_KEY: u64 = 2 << 32;
pub(crate) const TGT_CHOICE_KEY: u64 = 3 << 32;
pub(crate) const SRC_CHOICE_KEY: u64 = 4 << 32;

/// The inputs and constants of an encoding.
pub(crate) struct Leaves {
    /// Per input (in [`Transform::inputs`] order): value and poison flag.
    pub(crate) inputs: Vec<(Expr, Expr)>,
    /// Per symbolic constant.
    pub(crate) consts: Vec<Expr>,
}

/// Where a side's choices come from.
#[derive(Clone, Copy)]
pub(crate) enum Choices<'a> {
    /// Fresh symbols, keyed from this base.
    Symbols(u64),
    /// These values, in allocation order (missing ones are 0).
    Fixed(&'a [BitVec]),
    /// Another encoding's choices, where this one makes a choice of the same purpose about
    /// the same expression (else 0): the source copying the target where they compute alike.
    Mirror(&'a HashMap<ChoiceKey, Expr>),
}

/// What a choice is about: its purpose and the expression it decides something of. Two
/// encodings that compute one expression make their choices about it under one key.
pub(crate) type ChoiceKey = (Purpose, Expr);

/// The purpose of a choice.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Purpose {
    NanSign,
    NanPayload,
    ZeroSign,
    Freeze,
    Fuse,
    SignalingNan,
    InputZero,
}

/// A program, encoded.
pub(crate) struct Side {
    /// Its result: value and poison flag (`None` for a function returning `void`).
    pub(crate) result: Option<(Expr, Expr)>,
    /// Its undefined behavior.
    pub(crate) ub: Expr,
    /// Whether the choices are allowed ones.
    pub(crate) valid: Expr,
    /// The width of each choice, in allocation order.
    pub(crate) choices: Vec<Width>,
    /// Each choice's key (none for an `undef`) and the expression it is.
    pub(crate) keyed: Vec<(Option<ChoiceKey>, Expr)>,
    /// Each instruction's value and poison flag, for reports.
    pub(crate) values: Vec<(NodeId, Expr, Expr)>,
    /// The precondition (true without one).
    pub(crate) pre: Expr,
}

/// An error that makes a type assignment meaningless (`bswap` of an odd number of bytes):
/// the verifier skips the assignment.
pub(crate) const SKIP: &str = "skip:";

fn unsupported(m: impl Into<String>) -> Error {
    Error::Unsupported(m.into())
}

pub(crate) struct Enc<'a> {
    pub(crate) cx: &'a mut Context,
    t: &'a Transform,
    ty: &'a [Ty],
    leaves: &'a Leaves,
    choices: Choices<'a>,
    widths: Vec<Width>,
    keyed: Vec<(Option<ChoiceKey>, Expr)>,
    valid: Expr,
    ub: Expr,
    reach: Expr,
    memo: HashMap<NodeId, (Expr, Expr)>,
    input_index: HashMap<NodeId, usize>,
    const_index: HashMap<NodeId, usize>,
    values: Vec<(NodeId, Expr, Expr)>,
    tru: Expr,
    fls: Expr,
}

fn w(bits: u16) -> Result<Width, Error> {
    Ok(Width::new(bits)?)
}

impl<'a> Enc<'a> {
    pub(crate) fn new(
        cx: &'a mut Context,
        t: &'a Transform,
        ty: &'a [Ty],
        leaves: &'a Leaves,
        choices: Choices<'a>,
    ) -> Result<Self, Error> {
        let tru = cx.bool(true)?;
        let fls = cx.bool(false)?;
        Ok(Enc {
            cx,
            t,
            ty,
            leaves,
            choices,
            widths: Vec::new(),
            keyed: Vec::new(),
            valid: tru,
            ub: fls,
            reach: tru,
            memo: HashMap::new(),
            input_index: t.inputs.iter().enumerate().map(|(i, &n)| (n, i)).collect(),
            const_index: t.consts.iter().enumerate().map(|(i, &n)| (n, i)).collect(),
            values: Vec::new(),
            tru,
            fls,
        })
    }

    // Boolean helpers (1-bit values).
    fn and(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        self.cx.bin(BinOp::And, a, b)
    }
    fn or(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        self.cx.bin(BinOp::Or, a, b)
    }
    fn not(&mut self, a: Expr) -> Result<Expr, Error> {
        self.cx.un(UnOp::Not, a)
    }
    fn eq(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        self.cx.cmp(CmpOpExt::Eq, a, b)
    }
    fn ne(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        self.cx.cmp(CmpOpExt::Ne, a, b)
    }
    fn konst(&mut self, bits: u16, v: u64) -> Result<Expr, Error> {
        self.cx.constant(&BitVec::wrapping_from_u64(w(bits)?, v))
    }
    fn is_zero(&mut self, a: Expr) -> Result<Expr, Error> {
        let bits = self.cx.width(a)?.bits();
        let z = self.konst(bits, 0)?;
        self.eq(a, z)
    }
    fn msb(&mut self, a: Expr) -> Result<Expr, Error> {
        let bits = self.cx.width(a)?.bits();
        self.cx.bit(a, bits - 1)
    }
    fn add_ub(&mut self, cond: Expr) -> Result<(), Error> {
        let c = self.and(self.reach, cond)?;
        self.ub = self.or(self.ub, c)?;
        Ok(())
    }

    /// A fresh choice of `bits` bits, about `key` (see [`ChoiceKey`]).
    fn choice(&mut self, bits: u16, key: Option<ChoiceKey>) -> Result<Expr, Error> {
        let k = self.widths.len();
        let width = w(bits)?;
        self.widths.push(width);
        let e = match self.choices {
            Choices::Symbols(base) => self.cx.symbol(SymbolKey::U64(base + k as u64), width)?,
            Choices::Fixed(vals) => match vals.get(k) {
                Some(v) if v.width() == width => self.cx.constant(v)?,
                _ => self.cx.zero(width)?,
            },
            Choices::Mirror(map) => match key.and_then(|k| map.get(&k)) {
                Some(&e) if self.cx.width(e)? == width => e,
                _ => self.cx.zero(width)?,
            },
        };
        self.keyed.push((key, e));
        Ok(e)
    }

    fn allow(&mut self, cond: Expr) -> Result<(), Error> {
        self.valid = self.and(self.valid, cond)?;
        Ok(())
    }

    fn ty(&self, n: NodeId) -> Ty {
        self.ty[n as usize]
    }

    fn int_bits(&self, n: NodeId) -> Result<u16, Error> {
        match self.ty(n) {
            Ty::Int(b) => Ok(b),
            t => Err(unsupported(format!(
                "{} is {t}, not an integer",
                self.t.label(n)
            ))),
        }
    }

    fn format(&self, n: NodeId) -> Result<FpFormat, Error> {
        match self.ty(n) {
            Ty::Float(f) => Ok(f),
            t => Err(unsupported(format!(
                "{} is {t}, not floating point",
                self.t.label(n)
            ))),
        }
    }

    // Floating-point helpers.
    fn test(&mut self, f: FpFormat, t: FpTest, x: Expr) -> Result<Expr, Error> {
        self.cx.fp_test(f, t, x)
    }

    fn snan(&mut self, f: FpFormat, x: Expr) -> Result<Expr, Error> {
        let nan = self.test(f, FpTest::Nan, x)?;
        let q = self.cx.bit(x, (f.sb() - 2) as u16)?;
        let nq = self.not(q)?;
        self.and(nan, nq)
    }

    fn fconst(&mut self, v: &BitVec) -> Result<Expr, Error> {
        self.cx.constant(v)
    }

    /// The result `r` of a floating-point math operation, with LLVM's NaN results: when `r` is
    /// a NaN, any sign, and a quiet bit and payload that are preferred (quiet, zero payload),
    /// or copied from a NaN operand, quieted or unchanged (a payload between formats keeps its
    /// high bits, as `fpext` and `fptrunc` do).
    ///
    /// The choices and their conditions are made whatever the operands (even where the
    /// result cannot be a NaN): an encoding's choices must line up with every other encoding
    /// of the same program.
    fn nan_result(
        &mut self,
        f: FpFormat,
        r: Expr,
        ins: &[(Expr, FpFormat)],
    ) -> Result<Expr, Error> {
        let nan = self.test(f, FpTest::Nan, r)?;
        self.nan_result_when(f, r, nan, ins)
    }

    /// [`Self::nan_result`] with the result's NaN-ness given (see [`Self::nan_spec`]).
    fn nan_result_when(
        &mut self,
        f: FpFormat,
        r: Expr,
        nan: Expr,
        ins: &[(Expr, FpFormat)],
    ) -> Result<Expr, Error> {
        let (eb, sb) = (f.eb() as u16, f.sb() as u16);
        let mw = sb - 1;
        let q = self.konst(mw, 1 << (sb - 2))?;
        let sign = self.choice(1, Some((Purpose::NanSign, r)))?;
        let mut mant = q;
        let options = 1 + 2 * ins.len();
        if options > 1 {
            let kbits = (usize::BITS - (options - 1).leading_zeros()) as u16;
            let k = self.choice(kbits, Some((Purpose::NanPayload, r)))?;
            let last = self.konst(kbits, (options - 1) as u64)?;
            let in_range = self.cx.cmp(CmpOpExt::Ule, k, last)?;
            self.allow(in_range)?;
            for (i, &(x, fx)) in ins.iter().enumerate() {
                let xw = fx.sb() as u16 - 1;
                let xm = self.cx.trunc(x, w(xw)?)?;
                let m = if xw == mw {
                    xm
                } else if xw < mw {
                    let z = self.cx.zext(xm, w(mw)?)?;
                    let sh = self.konst(mw, u64::from(mw - xw))?;
                    self.cx.bin(BinOp::Shl, z, sh)?
                } else {
                    let sh = self.konst(xw, u64::from(xw - mw))?;
                    let s = self.cx.bin(BinOp::LShr, xm, sh)?;
                    self.cx.trunc(s, w(mw)?)?
                };
                let quieted = self.cx.bin(BinOp::Or, m, q)?;
                let xnan = self.test(fx, FpTest::Nan, x)?;
                let kq = self.konst(kbits, (1 + 2 * i) as u64)?;
                let ku = self.konst(kbits, (2 + 2 * i) as u64)?;
                let is_q = self.eq(k, kq)?;
                let is_u = self.eq(k, ku)?;
                // A copied payload needs a NaN operand; an unchanged one a nonzero payload (so
                // it stays a NaN).
                let copied = self.or(is_q, is_u)?;
                let ncopied = self.not(copied)?;
                let ok = self.or(ncopied, xnan)?;
                self.allow(ok)?;
                let mz = self.is_zero(m)?;
                let bad = self.and(is_u, mz)?;
                let good = self.not(bad)?;
                self.allow(good)?;
                mant = self.cx.select(is_q, quieted, mant)?;
                mant = self.cx.select(is_u, m, mant)?;
            }
        }
        let ones = self.cx.ones(w(eb)?)?;
        let tail = self.cx.concat(ones, mant)?;
        let nanval = self.cx.concat(sign, tail)?;
        self.cx.select(nan, nanval, r)
    }

    /// When IEEE 754 makes an operation's result a NaN, from its operands' classes alone (so
    /// a proof need not look inside the arithmetic): the invalid operations and NaN operands.
    pub(crate) fn nan_spec(&mut self, op: NanOp, f: FpFormat, a: &[Expr]) -> Result<Expr, Error> {
        let mut any_nan = self.fls;
        for &x in a {
            let n = self.test(f, FpTest::Nan, x)?;
            any_nan = self.or(any_nan, n)?;
        }
        let inf = |e: &mut Self, x| e.test(f, FpTest::Infinite, x);
        let zero = |e: &mut Self, x| e.test(f, FpTest::Zero, x);
        let invalid = match op {
            NanOp::Add | NanOp::Sub => {
                // ∞ − ∞.
                let (ia, ib) = (inf(self, a[0])?, inf(self, a[1])?);
                let both = self.and(ia, ib)?;
                let (sa, sb) = (self.msb(a[0])?, self.msb(a[1])?);
                let opposite = if op == NanOp::Add {
                    self.ne(sa, sb)?
                } else {
                    self.eq(sa, sb)?
                };
                self.and(both, opposite)?
            }
            NanOp::Mul => {
                // 0 · ∞.
                let (za, zb) = (zero(self, a[0])?, zero(self, a[1])?);
                let (ia, ib) = (inf(self, a[0])?, inf(self, a[1])?);
                let x = self.and(za, ib)?;
                let y = self.and(ia, zb)?;
                self.or(x, y)?
            }
            NanOp::Div => {
                // 0 / 0, ∞ / ∞.
                let (za, zb) = (zero(self, a[0])?, zero(self, a[1])?);
                let (ia, ib) = (inf(self, a[0])?, inf(self, a[1])?);
                let x = self.and(za, zb)?;
                let y = self.and(ia, ib)?;
                self.or(x, y)?
            }
            NanOp::Rem => {
                // ∞ rem y, x rem 0.
                let ia = inf(self, a[0])?;
                let zb = zero(self, a[1])?;
                self.or(ia, zb)?
            }
            NanOp::Sqrt => {
                // Below zero (−0 is fine).
                let neg = self.msb(a[0])?;
                let z = zero(self, a[0])?;
                let nz = self.not(z)?;
                self.and(neg, nz)?
            }
            NanOp::Fma => {
                // 0 · ∞, or an infinite product (exact: only from an infinite factor) plus
                // an infinity of the other sign.
                let (za, zb) = (zero(self, a[0])?, zero(self, a[1])?);
                let (ia, ib, ic) = (inf(self, a[0])?, inf(self, a[1])?, inf(self, a[2])?);
                let x = self.and(za, ib)?;
                let y = self.and(ia, zb)?;
                let zero_inf = self.or(x, y)?;
                let some_inf = self.or(ia, ib)?;
                let nza = self.not(za)?;
                let nzb = self.not(zb)?;
                let nonzero = self.and(nza, nzb)?;
                let prod_inf = self.and(some_inf, nonzero)?;
                let (sa, sb, sc) = (self.msb(a[0])?, self.msb(a[1])?, self.msb(a[2])?);
                let sp = self.cx.bin(BinOp::Xor, sa, sb)?;
                let opposite = self.ne(sp, sc)?;
                let t = self.and(prod_inf, ic)?;
                let cancel = self.and(t, opposite)?;
                self.or(zero_inf, cancel)?
            }
            NanOp::Exact => self.fls,
        };
        self.or(any_nan, invalid)
    }

    /// Operand `x` of an `nsz` operation: a zero's sign may flip.
    fn nsz(&mut self, f: FpFormat, x: Expr) -> Result<Expr, Error> {
        let z = self.test(f, FpTest::Zero, x)?;
        let flip = self.choice(1, Some((Purpose::InputZero, x)))?;
        let c = self.and(z, flip)?;
        let n = self.cx.fp_neg(f, x)?;
        self.cx.select(c, n, x)
    }

    /// The result `r` of an `nsz` operation whose zero operands (`when`) flipping would only
    /// flip the result's sign: flipped, by one choice about `r`. For `a ± b` that is when
    /// both are zeros; for `a · b`, `a / b`, when either is (a zero or an infinite result);
    /// for one-operand operations and `fmod`, when the (first) operand is.
    fn nsz_out(&mut self, f: FpFormat, r: Expr, when: Expr) -> Result<Expr, Error> {
        let flip = self.choice(1, Some((Purpose::ZeroSign, r)))?;
        let c = self.and(when, flip)?;
        let n = self.cx.fp_neg(f, r)?;
        self.cx.select(c, n, r)
    }

    /// Poison from `nnan` and `ninf`: an operand or the result that is a NaN or an infinity.
    fn fmf_poison(&mut self, fl: u16, f: FpFormat, vals: &[Expr]) -> Result<Expr, Error> {
        let mut p = self.fls;
        for &x in vals {
            if fl & flags::NNAN != 0 {
                let n = self.test(f, FpTest::Nan, x)?;
                p = self.or(p, n)?;
            }
            if fl & flags::NINF != 0 {
                let n = self.test(f, FpTest::Infinite, x)?;
                p = self.or(p, n)?;
            }
        }
        Ok(p)
    }

    /// The value and poison flag of node `n`.
    pub(crate) fn val(&mut self, n: NodeId) -> Result<(Expr, Expr), Error> {
        if let Some(&v) = self.memo.get(&n) {
            return Ok(v);
        }
        let t = self.t;
        let out = match t.node(n) {
            Node::Input { .. } => self.leaves.inputs[self.input_index[&n]],
            Node::Sym(_) => (self.leaves.consts[self.const_index[&n]], self.fls),
            Node::Lit(l) => {
                let ty = self.ty(n);
                match l {
                    Lit::Num(s) => {
                        let v = match ty {
                            Ty::Int(b) => super::value::int_literal(s, b),
                            Ty::Float(f) => super::value::float_literal(s, f),
                        };
                        let Some(v) = v else {
                            return Err(unsupported(format!("{SKIP} {s} is not a {ty}")));
                        };
                        (self.cx.constant(&v)?, self.fls)
                    }
                    Lit::Bool(b) => (self.cx.bool(*b)?, self.fls),
                    Lit::Poison => (self.cx.zero(w(ty.bits())?)?, self.tru),
                    Lit::Undef => (self.choice(ty.bits(), None)?, self.fls),
                    Lit::Inf(neg) => {
                        let f = self.format(n)?;
                        (self.fconst(&f.inf(*neg))?, self.fls)
                    }
                    Lit::Nan => {
                        let f = self.format(n)?;
                        (self.fconst(&f.nan())?, self.fls)
                    }
                }
            }
            Node::CExpr(f, args) => (self.cexpr(n, *f, args)?, self.fls),
            Node::Pred(p, args) => (self.pred(*p, args)?, self.fls),
            Node::Inst(inst) => {
                if inst.op == Op::Phi {
                    return Err(unsupported(format!(
                        "{} is used before its block",
                        t.label(n)
                    )));
                }
                let v = self.inst(n)?;
                self.values.push((n, v.0, v.1));
                v
            }
        };
        self.memo.insert(n, out);
        Ok(out)
    }

    fn cexpr(&mut self, n: NodeId, f: CFun, args: &[NodeId]) -> Result<Expr, Error> {
        let bits = self.int_bits(n)?;
        let mut a = Vec::with_capacity(args.len());
        for &x in args {
            a.push(self.val(x)?.0);
        }
        let bin = |e: &mut Self, op: BinOp| e.cx.bin(op, a[0], a[1]);
        Ok(match f {
            CFun::Neg => self.cx.un(UnOp::Neg, a[0])?,
            CFun::Not => self.cx.un(UnOp::Not, a[0])?,
            CFun::Add => bin(self, BinOp::Add)?,
            CFun::Sub => bin(self, BinOp::Sub)?,
            CFun::Mul => bin(self, BinOp::Mul)?,
            CFun::SDiv => bin(self, BinOp::SDiv)?,
            CFun::UDiv => bin(self, BinOp::UDiv)?,
            CFun::SRem => bin(self, BinOp::SRem)?,
            CFun::URem => bin(self, BinOp::URem)?,
            CFun::Shl => bin(self, BinOp::Shl)?,
            CFun::AShr => bin(self, BinOp::AShr)?,
            CFun::LShr => bin(self, BinOp::LShr)?,
            CFun::And => bin(self, BinOp::And)?,
            CFun::Or => bin(self, BinOp::Or)?,
            CFun::Xor => bin(self, BinOp::Xor)?,
            CFun::Abs => self.cx.abs(a[0])?,
            CFun::Log2 => {
                // ⌊log2 x⌋ = W − 1 − clz(x) (and W − 1 − W = −1 for 0).
                let clz = self.cx.un(UnOp::Clz, a[0])?;
                let top = self.konst(bits, u64::from(bits) - 1)?;
                self.cx.bin(BinOp::Sub, top, clz)?
            }
            CFun::Width => {
                let of = self.ty(args[0]).bits();
                self.konst(bits, u64::from(of))?
            }
            CFun::Trunc => self.cx.trunc(a[0], w(bits)?)?,
            CFun::ZExt => self.cx.zext(a[0], w(bits)?)?,
            CFun::SExt => self.cx.sext(a[0], w(bits)?)?,
            CFun::UMax => self.cx.umax(a[0], a[1])?,
            CFun::UMin => self.cx.umin(a[0], a[1])?,
            CFun::SMax => self.cx.smax(a[0], a[1])?,
            CFun::SMin => self.cx.smin(a[0], a[1])?,
            CFun::Clz => self.cx.un(UnOp::Clz, a[0])?,
            CFun::Ctz => self.cx.un(UnOp::Ctz, a[0])?,
            CFun::Popcount => self.cx.un(UnOp::Popcnt, a[0])?,
        })
    }

    fn pred(&mut self, p: PFun, args: &[NodeId]) -> Result<Expr, Error> {
        let mut a = Vec::with_capacity(args.len());
        for &x in args {
            a.push(self.val(x)?.0);
        }
        Ok(match p {
            PFun::True => self.tru,
            PFun::And => self.and(a[0], a[1])?,
            PFun::Or => self.or(a[0], a[1])?,
            PFun::Not => self.not(a[0])?,
            PFun::Cmp(c) => self.cx.cmp(icmp(c), a[0], a[1])?,
            PFun::IsPowerOf2 | PFun::IsPowerOf2OrZero => {
                let bits = self.cx.width(a[0])?.bits();
                let one = self.konst(bits, 1)?;
                let m1 = self.cx.bin(BinOp::Sub, a[0], one)?;
                let and = self.cx.bin(BinOp::And, a[0], m1)?;
                let single = self.is_zero(and)?;
                if p == PFun::IsPowerOf2 {
                    let z = self.is_zero(a[0])?;
                    let nz = self.not(z)?;
                    self.and(single, nz)?
                } else {
                    single
                }
            }
            PFun::IsSignBit => {
                let bits = self.cx.width(a[0])?.bits();
                let smin = self.cx.constant(&BitVec::smin(w(bits)?))?;
                self.eq(a[0], smin)?
            }
            PFun::IsMask => {
                // 2^k − 1 for some k ≥ 1.
                let bits = self.cx.width(a[0])?.bits();
                let one = self.konst(bits, 1)?;
                let p1 = self.cx.bin(BinOp::Add, a[0], one)?;
                let and = self.cx.bin(BinOp::And, a[0], p1)?;
                let low = self.is_zero(and)?;
                let z = self.is_zero(a[0])?;
                let nz = self.not(z)?;
                self.and(low, nz)?
            }
            PFun::IsShiftedMask => {
                // One run of ones: x ≠ 0 and (x | (x − 1)) + 1 is a power of two or 0.
                let bits = self.cx.width(a[0])?.bits();
                let one = self.konst(bits, 1)?;
                let m1 = self.cx.bin(BinOp::Sub, a[0], one)?;
                let fill = self.cx.bin(BinOp::Or, a[0], m1)?;
                let p1 = self.cx.bin(BinOp::Add, fill, one)?;
                let and = self.cx.bin(BinOp::And, fill, p1)?;
                let run = self.is_zero(and)?;
                let z = self.is_zero(a[0])?;
                let nz = self.not(z)?;
                self.and(run, nz)?
            }
            PFun::MaskedValueIsZero => {
                let and = self.cx.bin(BinOp::And, a[0], a[1])?;
                self.is_zero(and)?
            }
            PFun::WillNotOverflowSignedAdd => {
                let o = self.cx.sadd_overflow(a[0], a[1])?;
                self.not(o)?
            }
            PFun::WillNotOverflowUnsignedAdd => {
                let o = self.cx.add_carry(a[0], a[1])?;
                self.not(o)?
            }
            PFun::WillNotOverflowSignedSub => {
                let o = self.cx.ssub_overflow(a[0], a[1])?;
                self.not(o)?
            }
            PFun::WillNotOverflowUnsignedSub => {
                let o = self.cx.sub_borrow(a[0], a[1])?;
                self.not(o)?
            }
            PFun::WillNotOverflowSignedMul => {
                let o = self.smul_overflow(a[0], a[1])?;
                self.not(o)?
            }
            PFun::WillNotOverflowUnsignedMul => {
                let hi = self.cx.bin(BinOp::UMulHi, a[0], a[1])?;
                self.is_zero(hi)?
            }
            PFun::WillNotOverflowUnsignedShl => {
                let (sh, ok) = self.shl_checks(a[0], a[1])?;
                let back = self.cx.bin(BinOp::LShr, sh, a[1])?;
                let same = self.eq(back, a[0])?;
                self.and(ok, same)?
            }
            PFun::WillNotOverflowSignedShl => {
                let (sh, ok) = self.shl_checks(a[0], a[1])?;
                let back = self.cx.bin(BinOp::AShr, sh, a[1])?;
                let same = self.eq(back, a[0])?;
                self.and(ok, same)?
            }
        })
    }

    /// `a << b` and whether `b` is in range.
    fn shl_checks(&mut self, a: Expr, b: Expr) -> Result<(Expr, Expr), Error> {
        let bits = self.cx.width(a)?.bits();
        let sh = self.cx.bin(BinOp::Shl, a, b)?;
        let wc = self.konst(bits, u64::from(bits))?;
        let ok = self.cx.cmp(CmpOpExt::Ult, b, wc)?;
        Ok((sh, ok))
    }

    fn smul_overflow(&mut self, a: Expr, b: Expr) -> Result<Expr, Error> {
        // The high half of the signed product is not the sign extension of the low half.
        let lo = self.cx.bin(BinOp::Mul, a, b)?;
        let hi = self.cx.bin(BinOp::SMulHi, a, b)?;
        let bits = self.cx.width(a)?.bits();
        let sh = self.konst(bits, u64::from(bits) - 1)?;
        let sign = self.cx.bin(BinOp::AShr, lo, sh)?;
        self.ne(hi, sign)
    }

    /// Instruction `n` (not a `phi`).
    fn inst(&mut self, n: NodeId) -> Result<(Expr, Expr), Error> {
        let Node::Inst(inst) = self.t.node(n) else {
            unreachable!("an instruction")
        };
        let fl = inst.flags;
        let mut vs = Vec::with_capacity(inst.args.len());
        let mut ps = Vec::with_capacity(inst.args.len());
        for &a in &inst.args {
            let (v, p) = self.val(a)?;
            vs.push(v);
            ps.push(p);
        }
        let any_poison = |e: &mut Self, ps: &[Expr]| -> Result<Expr, Error> {
            let mut p = e.fls;
            for &x in ps {
                p = e.or(p, x)?;
            }
            Ok(p)
        };
        let has = |f: u16| fl & f != 0;
        match inst.op {
            Op::Add | Op::Sub | Op::Mul => {
                let op = match inst.op {
                    Op::Add => BinOp::Add,
                    Op::Sub => BinOp::Sub,
                    _ => BinOp::Mul,
                };
                let v = self.cx.bin(op, vs[0], vs[1])?;
                let mut p = any_poison(self, &ps)?;
                if has(flags::NUW) {
                    let o = match inst.op {
                        Op::Add => self.cx.add_carry(vs[0], vs[1])?,
                        Op::Sub => self.cx.sub_borrow(vs[0], vs[1])?,
                        _ => {
                            let hi = self.cx.bin(BinOp::UMulHi, vs[0], vs[1])?;
                            let z = self.is_zero(hi)?;
                            self.not(z)?
                        }
                    };
                    p = self.or(p, o)?;
                }
                if has(flags::NSW) {
                    let o = match inst.op {
                        Op::Add => self.cx.sadd_overflow(vs[0], vs[1])?,
                        Op::Sub => self.cx.ssub_overflow(vs[0], vs[1])?,
                        _ => self.smul_overflow(vs[0], vs[1])?,
                    };
                    p = self.or(p, o)?;
                }
                Ok((v, p))
            }
            Op::UDiv | Op::SDiv | Op::URem | Op::SRem => {
                let bits = self.int_bits(n)?;
                let signed = matches!(inst.op, Op::SDiv | Op::SRem);
                // Division by zero or by poison, and signed overflow, are undefined behavior.
                let z = self.is_zero(vs[1])?;
                let mut ub = self.or(z, ps[1])?;
                if signed {
                    // INT_MIN / −1 overflows; a poison dividend may be INT_MIN, so it is
                    // undefined too.
                    let smin = self.cx.constant(&BitVec::smin(w(bits)?))?;
                    let ones = self.cx.ones(w(bits)?)?;
                    let a_min = self.eq(vs[0], smin)?;
                    let a_min = self.or(a_min, ps[0])?;
                    let b_m1 = self.eq(vs[1], ones)?;
                    let o = self.and(a_min, b_m1)?;
                    ub = self.or(ub, o)?;
                }
                self.add_ub(ub)?;
                let op = match inst.op {
                    Op::UDiv => BinOp::UDiv,
                    Op::SDiv => BinOp::SDiv,
                    Op::URem => BinOp::URem,
                    _ => BinOp::SRem,
                };
                let v = self.cx.bin(op, vs[0], vs[1])?;
                let mut p = ps[0];
                if has(flags::EXACT) && matches!(inst.op, Op::UDiv | Op::SDiv) {
                    let rop = if signed { BinOp::SRem } else { BinOp::URem };
                    let r = self.cx.bin(rop, vs[0], vs[1])?;
                    let rz = self.is_zero(r)?;
                    let inexact = self.not(rz)?;
                    p = self.or(p, inexact)?;
                }
                Ok((v, p))
            }
            Op::Shl | Op::LShr | Op::AShr => {
                let bits = self.int_bits(n)?;
                let op = match inst.op {
                    Op::Shl => BinOp::Shl,
                    Op::LShr => BinOp::LShr,
                    _ => BinOp::AShr,
                };
                let v = self.cx.bin(op, vs[0], vs[1])?;
                let wc = self.konst(bits, u64::from(bits))?;
                let big = self.cx.cmp(CmpOpExt::Uge, vs[1], wc)?;
                let mut p = any_poison(self, &ps)?;
                p = self.or(p, big)?;
                if inst.op == Op::Shl {
                    if has(flags::NUW) {
                        let back = self.cx.bin(BinOp::LShr, v, vs[1])?;
                        let lost = self.ne(back, vs[0])?;
                        p = self.or(p, lost)?;
                    }
                    if has(flags::NSW) {
                        let back = self.cx.bin(BinOp::AShr, v, vs[1])?;
                        let lost = self.ne(back, vs[0])?;
                        p = self.or(p, lost)?;
                    }
                } else if has(flags::EXACT) {
                    let back = self.cx.bin(BinOp::Shl, v, vs[1])?;
                    let lost = self.ne(back, vs[0])?;
                    p = self.or(p, lost)?;
                }
                Ok((v, p))
            }
            Op::And | Op::Or | Op::Xor => {
                let op = match inst.op {
                    Op::And => BinOp::And,
                    Op::Or => BinOp::Or,
                    _ => BinOp::Xor,
                };
                let v = self.cx.bin(op, vs[0], vs[1])?;
                let mut p = any_poison(self, &ps)?;
                if inst.op == Op::Or && has(flags::DISJOINT) {
                    let both = self.cx.bin(BinOp::And, vs[0], vs[1])?;
                    let z = self.is_zero(both)?;
                    let overlap = self.not(z)?;
                    p = self.or(p, overlap)?;
                }
                Ok((v, p))
            }
            Op::ICmp(pred) => {
                let v = self.cx.cmp(icmp(pred), vs[0], vs[1])?;
                let mut p = any_poison(self, &ps)?;
                if has(flags::SAMESIGN) {
                    let (sa, sb) = (self.msb(vs[0])?, self.msb(vs[1])?);
                    let differ = self.ne(sa, sb)?;
                    p = self.or(p, differ)?;
                }
                Ok((v, p))
            }
            Op::Select => {
                let v = self.cx.select(vs[0], vs[1], vs[2])?;
                let arm = self.cx.select(vs[0], ps[1], ps[2])?;
                let mut p = self.or(ps[0], arm)?;
                let mut v = v;
                if let Ty::Float(f) = self.ty(n) {
                    if has(flags::NSZ) {
                        let z = self.test(f, FpTest::Zero, v)?;
                        v = self.nsz_out(f, v, z)?;
                    }
                    let fp = self.fmf_poison(fl, f, &[v])?;
                    p = self.or(p, fp)?;
                }
                Ok((v, p))
            }
            Op::Freeze => {
                let bits = self.ty(n).bits();
                let c = self.choice(bits, Some((Purpose::Freeze, vs[0])))?;
                let v = self.cx.select(ps[0], c, vs[0])?;
                Ok((v, self.fls))
            }
            Op::Trunc => {
                let bits = self.int_bits(n)?;
                let v = self.cx.trunc(vs[0], w(bits)?)?;
                let mut p = ps[0];
                let from = self.cx.width(vs[0])?;
                if has(flags::NUW) {
                    let back = self.cx.zext(v, from)?;
                    let lost = self.ne(back, vs[0])?;
                    p = self.or(p, lost)?;
                }
                if has(flags::NSW) {
                    let back = self.cx.sext(v, from)?;
                    let lost = self.ne(back, vs[0])?;
                    p = self.or(p, lost)?;
                }
                Ok((v, p))
            }
            Op::ZExt | Op::SExt => {
                let bits = self.int_bits(n)?;
                let v = if inst.op == Op::ZExt {
                    self.cx.zext(vs[0], w(bits)?)?
                } else {
                    self.cx.sext(vs[0], w(bits)?)?
                };
                let mut p = ps[0];
                if inst.op == Op::ZExt && has(flags::NNEG) {
                    let neg = self.msb(vs[0])?;
                    p = self.or(p, neg)?;
                }
                Ok((v, p))
            }
            Op::BitCast | Op::Copy => Ok((vs[0], ps[0])),
            Op::FAdd | Op::FSub | Op::FMul | Op::FDiv | Op::FRem => {
                let f = self.format(n)?;
                let (a, b) = (vs[0], vs[1]);
                let rne = RoundingMode::Rne;
                let (r, spec) = match inst.op {
                    Op::FAdd => (self.cx.fp(FpOp::Add(rne), f, &[a, b])?, NanOp::Add),
                    Op::FSub => (self.cx.fp_sub(f, rne, a, b)?, NanOp::Sub),
                    Op::FMul => (self.cx.fp(FpOp::Mul(rne), f, &[a, b])?, NanOp::Mul),
                    Op::FDiv => (self.cx.fp(FpOp::Div(rne), f, &[a, b])?, NanOp::Div),
                    _ => (self.fmod(f, a, b)?, NanOp::Rem),
                };
                let nan = self.nan_spec(spec, f, &[a, b])?;
                let mut r = self.nan_result_when(f, r, nan, &[(a, f), (b, f)])?;
                if has(flags::NSZ) {
                    let (za, zb) = (
                        self.test(f, FpTest::Zero, a)?,
                        self.test(f, FpTest::Zero, b)?,
                    );
                    let when = match inst.op {
                        Op::FAdd | Op::FSub => self.and(za, zb)?,
                        Op::FMul | Op::FDiv => self.or(za, zb)?,
                        _ => za,
                    };
                    r = self.nsz_out(f, r, when)?;
                }
                let mut p = any_poison(self, &ps)?;
                let fp = self.fmf_poison(fl, f, &[a, b, r])?;
                p = self.or(p, fp)?;
                Ok((r, p))
            }
            Op::FNeg => {
                let f = self.format(n)?;
                let a = vs[0];
                let mut r = self.cx.fp_neg(f, a)?;
                if has(flags::NSZ) {
                    let z = self.test(f, FpTest::Zero, a)?;
                    r = self.nsz_out(f, r, z)?;
                }
                let fp = self.fmf_poison(fl, f, &[a, r])?;
                let p = self.or(ps[0], fp)?;
                Ok((r, p))
            }
            Op::FCmp(pred) => {
                let f = self.format(inst.args[0])?;
                let (a, b) = (vs[0], vs[1]);
                let v = self.fcmp(f, pred, a, b)?;
                let mut p = any_poison(self, &ps)?;
                let fp = self.fmf_poison(fl, f, &[a, b])?;
                p = self.or(p, fp)?;
                Ok((v, p))
            }
            Op::FPTrunc | Op::FPExt => {
                let from = self.format(inst.args[0])?;
                let to = self.format(n)?;
                let a = vs[0];
                let r = self.cx.fp(
                    FpOp::Convert {
                        to,
                        rm: RoundingMode::Rne,
                    },
                    from,
                    &[a],
                )?;
                let nan = self.nan_spec(NanOp::Exact, from, &[a])?;
                let mut r = self.nan_result_when(to, r, nan, &[(a, from)])?;
                if has(flags::NSZ) {
                    let z = self.test(from, FpTest::Zero, a)?;
                    r = self.nsz_out(to, r, z)?;
                }
                let fa = self.fmf_poison(fl, from, &[a])?;
                let fr = self.fmf_poison(fl, to, &[r])?;
                let p = self.or(ps[0], fa)?;
                let p = self.or(p, fr)?;
                Ok((r, p))
            }
            Op::FPToUI | Op::FPToSI => {
                let f = self.format(inst.args[0])?;
                let bits = self.int_bits(n)?;
                let signed = inst.op == Op::FPToSI;
                let rtz = RoundingMode::Rtz;
                let a = vs[0];
                let v = if signed {
                    self.cx.fp(FpOp::ToSInt(rtz, w(bits)?), f, &[a])?
                } else {
                    self.cx.fp(FpOp::ToUInt(rtz, w(bits)?), f, &[a])?
                };
                // Poison unless the value rounded toward zero fits.
                let y = self.cx.fp(FpOp::RoundToIntegral(rtz), f, &[a])?;
                let nan = self.test(f, FpTest::Nan, a)?;
                let inf = self.test(f, FpTest::Infinite, a)?;
                let special = self.or(nan, inf)?;
                let (lo, hi) = if signed {
                    let lo = f.from_sint(RoundingMode::Rne, &BitVec::smin(w(bits)?));
                    let top = pow2(&BitVec::zero(w(bits + 1)?), bits - 1)?;
                    (lo, f.from_uint(RoundingMode::Rne, &top))
                } else {
                    let top = pow2(&BitVec::zero(w(bits + 1)?), bits)?;
                    (f.zero(false), f.from_uint(RoundingMode::Rne, &top))
                };
                let (lo, hi) = (self.fconst(&lo)?, self.fconst(&hi)?);
                let ge = self.cx.fp_cmp(f, FpCmpOp::Ge, y, lo)?;
                let lt = self.cx.fp_cmp(f, FpCmpOp::Lt, y, hi)?;
                let fits = self.and(ge, lt)?;
                let nf = self.not(fits)?;
                let bad = self.or(special, nf)?;
                let p = self.or(ps[0], bad)?;
                Ok((v, p))
            }
            Op::UIToFP | Op::SIToFP => {
                let f = self.format(n)?;
                let a = vs[0];
                let rne = RoundingMode::Rne;
                let mut r = if inst.op == Op::SIToFP {
                    self.cx.fp(FpOp::FromSInt(rne), f, &[a])?
                } else {
                    self.cx.fp(FpOp::FromUInt(rne), f, &[a])?
                };
                let mut p = ps[0];
                if inst.op == Op::UIToFP && has(flags::NNEG) {
                    let neg = self.msb(a)?;
                    p = self.or(p, neg)?;
                }
                if has(flags::NSZ) {
                    let z = self.is_zero(a)?;
                    r = self.nsz_out(f, r, z)?;
                }
                let fp = self.fmf_poison(fl, f, &[r])?;
                p = self.or(p, fp)?;
                Ok((r, p))
            }
            Op::Call(i) => self.intrinsic(n, i, fl, &vs, &ps),
            Op::Phi => unreachable!("phis are encoded with their block"),
        }
    }

    /// `fmod(a, b)` (LLVM's `frem`), from the IEEE remainder: when the remainder's sign differs
    /// from `a`'s, the quotient was rounded away from `trunc(a / b)`, and adding `|b|` with
    /// `a`'s sign (exact: the result is representable) corrects it.
    fn fmod(&mut self, f: FpFormat, a: Expr, b: Expr) -> Result<Expr, Error> {
        let r = self.cx.fp(FpOp::Rem, f, &[a, b])?;
        let rz = self.test(f, FpTest::Zero, r)?;
        let nz = self.not(rz)?;
        let (sr, sa) = (self.msb(r)?, self.msb(a)?);
        let differ = self.ne(sr, sa)?;
        let fix = self.and(nz, differ)?;
        let step = self.cx.fp_copysign(f, b, a)?;
        let fixed = self.cx.fp(FpOp::Add(RoundingMode::Rne), f, &[r, step])?;
        self.cx.select(fix, fixed, r)
    }

    fn fcmp(&mut self, f: FpFormat, pred: FPred, a: Expr, b: Expr) -> Result<Expr, Error> {
        let na = self.test(f, FpTest::Nan, a)?;
        let nb = self.test(f, FpTest::Nan, b)?;
        let uno = self.or(na, nb)?;
        let cmp = |e: &mut Self, op| e.cx.fp_cmp(f, op, a, b);
        Ok(match pred {
            FPred::False => self.fls,
            FPred::True => self.tru,
            FPred::Oeq => cmp(self, FpCmpOp::Eq)?,
            FPred::Ogt => cmp(self, FpCmpOp::Gt)?,
            FPred::Oge => cmp(self, FpCmpOp::Ge)?,
            FPred::Olt => cmp(self, FpCmpOp::Lt)?,
            FPred::Ole => cmp(self, FpCmpOp::Le)?,
            FPred::One => {
                let eq = cmp(self, FpCmpOp::Eq)?;
                let ne = self.not(eq)?;
                let ord = self.not(uno)?;
                self.and(ord, ne)?
            }
            FPred::Ord => self.not(uno)?,
            FPred::Uno => uno,
            FPred::Ueq => {
                let c = cmp(self, FpCmpOp::Eq)?;
                self.or(uno, c)?
            }
            FPred::Ugt => {
                let c = cmp(self, FpCmpOp::Gt)?;
                self.or(uno, c)?
            }
            FPred::Uge => {
                let c = cmp(self, FpCmpOp::Ge)?;
                self.or(uno, c)?
            }
            FPred::Ult => {
                let c = cmp(self, FpCmpOp::Lt)?;
                self.or(uno, c)?
            }
            FPred::Ule => {
                let c = cmp(self, FpCmpOp::Le)?;
                self.or(uno, c)?
            }
            FPred::Une => {
                let c = cmp(self, FpCmpOp::Eq)?;
                self.not(c)?
            }
        })
    }

    fn intrinsic(
        &mut self,
        n: NodeId,
        i: Intrinsic,
        fl: u16,
        vs: &[Expr],
        ps: &[Expr],
    ) -> Result<(Expr, Expr), Error> {
        let mut p = self.fls;
        let data = match i {
            Intrinsic::Abs | Intrinsic::Ctlz | Intrinsic::Cttz => &ps[..1],
            _ => ps,
        };
        for &x in data {
            p = self.or(p, x)?;
        }
        if i == Intrinsic::Assume {
            let nc = self.not(vs[0])?;
            let bad = self.or(ps[0], nc)?;
            self.add_ub(bad)?;
            return Ok((self.tru, self.fls));
        }
        if !i.is_float() {
            let bits = self.int_bits(n)?;
            let v = match i {
                Intrinsic::UMin => self.cx.umin(vs[0], vs[1])?,
                Intrinsic::UMax => self.cx.umax(vs[0], vs[1])?,
                Intrinsic::SMin => self.cx.smin(vs[0], vs[1])?,
                Intrinsic::SMax => self.cx.smax(vs[0], vs[1])?,
                Intrinsic::Abs => {
                    let smin = self.cx.constant(&BitVec::smin(w(bits)?))?;
                    let is_min = self.eq(vs[0], smin)?;
                    // The flag operand: poison at INT_MIN when it is true (a poison flag,
                    // poison).
                    let flagged = self.and(vs[1], is_min)?;
                    p = self.or(p, flagged)?;
                    p = self.or(p, ps[1])?;
                    self.cx.abs(vs[0])?
                }
                Intrinsic::Ctpop => self.cx.un(UnOp::Popcnt, vs[0])?,
                Intrinsic::Ctlz | Intrinsic::Cttz => {
                    let z = self.is_zero(vs[0])?;
                    let flagged = self.and(vs[1], z)?;
                    p = self.or(p, flagged)?;
                    p = self.or(p, ps[1])?;
                    let op = if i == Intrinsic::Ctlz {
                        UnOp::Clz
                    } else {
                        UnOp::Ctz
                    };
                    self.cx.un(op, vs[0])?
                }
                Intrinsic::Bswap => {
                    if bits % 16 != 0 {
                        return Err(unsupported(format!("{SKIP} bswap of i{bits}")));
                    }
                    self.cx.un(UnOp::Bswap, vs[0])?
                }
                Intrinsic::BitReverse => self.cx.un(UnOp::BitRev, vs[0])?,
                Intrinsic::Fshl | Intrinsic::Fshr => {
                    // Shift amounts modulo the width; a shift by W is 0, so no select for 0.
                    let wc = self.konst(bits, u64::from(bits))?;
                    let s = self.cx.bin(BinOp::URem, vs[2], wc)?;
                    let rest = self.cx.bin(BinOp::Sub, wc, s)?;
                    if i == Intrinsic::Fshl {
                        let hi = self.cx.bin(BinOp::Shl, vs[0], s)?;
                        let lo = self.cx.bin(BinOp::LShr, vs[1], rest)?;
                        self.cx.bin(BinOp::Or, hi, lo)?
                    } else {
                        let lo = self.cx.bin(BinOp::LShr, vs[1], s)?;
                        let hi = self.cx.bin(BinOp::Shl, vs[0], rest)?;
                        self.cx.bin(BinOp::Or, hi, lo)?
                    }
                }
                Intrinsic::UAddSat => self.cx.add_sat_u(vs[0], vs[1])?,
                Intrinsic::USubSat => self.cx.sub_sat_u(vs[0], vs[1])?,
                Intrinsic::SAddSat => self.cx.add_sat_s(vs[0], vs[1])?,
                Intrinsic::SSubSat => self.cx.sub_sat_s(vs[0], vs[1])?,
                _ => unreachable!("an integer intrinsic"),
            };
            return Ok((v, p));
        }
        let f = self.format(n)?;
        let mut a: Vec<Expr> = vs.to_vec();
        let fused = matches!(i, Intrinsic::Fma | Intrinsic::FMulAdd);
        if fl & flags::NSZ != 0 && fused {
            for x in a.iter_mut() {
                *x = self.nsz(f, *x)?;
            }
        }
        let ins: Vec<(Expr, FpFormat)> = a.iter().map(|&x| (x, f)).collect();
        let rne = RoundingMode::Rne;
        let r = match i {
            Intrinsic::FAbs => self.cx.fp_abs(f, a[0])?,
            Intrinsic::CopySign => self.cx.fp_copysign(f, a[0], a[1])?,
            Intrinsic::Sqrt => {
                let r = self.cx.fp(FpOp::Sqrt(rne), f, &[a[0]])?;
                let nan = self.nan_spec(NanOp::Sqrt, f, &a)?;
                self.nan_result_when(f, r, nan, &ins)?
            }
            Intrinsic::Fma => {
                let r = self.cx.fp(FpOp::Fma(rne), f, &a)?;
                let nan = self.nan_spec(NanOp::Fma, f, &a)?;
                self.nan_result_when(f, r, nan, &ins)?
            }
            Intrinsic::FMulAdd => {
                // Fused or not, as the implementation likes.
                let fused = self.cx.fp(FpOp::Fma(rne), f, &a)?;
                let m = self.cx.fp(FpOp::Mul(rne), f, &[a[0], a[1]])?;
                let sep = self.cx.fp(FpOp::Add(rne), f, &[m, a[2]])?;
                let c = self.choice(1, Some((Purpose::Fuse, fused)))?;
                let r = self.cx.select(c, fused, sep)?;
                self.nan_result(f, r, &ins)?
            }
            Intrinsic::MinNum
            | Intrinsic::MaxNum
            | Intrinsic::MinimumNum
            | Intrinsic::MaximumNum
            | Intrinsic::Minimum
            | Intrinsic::Maximum => {
                let is_min = matches!(
                    i,
                    Intrinsic::MinNum | Intrinsic::MinimumNum | Intrinsic::Minimum
                );
                let op = if is_min { FpOp::Min } else { FpOp::Max };
                // minimumNumber / maximumNumber: a NaN loses to a number, −0 < +0.
                let mut r = self.cx.fp(op, f, &[a[0], a[1]])?;
                let nanc = self.fconst(&f.nan())?;
                match i {
                    Intrinsic::Minimum | Intrinsic::Maximum => {
                        let na = self.test(f, FpTest::Nan, a[0])?;
                        let nb = self.test(f, FpTest::Nan, a[1])?;
                        let either = self.or(na, nb)?;
                        r = self.cx.select(either, nanc, r)?;
                    }
                    Intrinsic::MinNum | Intrinsic::MaxNum => {
                        // A signaling NaN may give a NaN instead of the other operand.
                        let sa = self.snan(f, a[0])?;
                        let sb = self.snan(f, a[1])?;
                        let s = self.or(sa, sb)?;
                        let c = self.choice(1, Some((Purpose::SignalingNan, r)))?;
                        let take = self.and(s, c)?;
                        r = self.cx.select(take, nanc, r)?;
                    }
                    _ => {}
                }
                if fl & flags::NSZ != 0 {
                    // Zeros of different signs: either one.
                    let za = self.test(f, FpTest::Zero, a[0])?;
                    let zb = self.test(f, FpTest::Zero, a[1])?;
                    let (sa, sb) = (self.msb(a[0])?, self.msb(a[1])?);
                    let both = self.and(za, zb)?;
                    let differ = self.ne(sa, sb)?;
                    let mixed = self.and(both, differ)?;
                    let c = self.choice(1, Some((Purpose::ZeroSign, r)))?;
                    let flip = self.and(mixed, c)?;
                    let nr = self.cx.fp_neg(f, r)?;
                    r = self.cx.select(flip, nr, r)?;
                }
                self.nan_result(f, r, &ins)?
            }
            Intrinsic::Floor
            | Intrinsic::Ceil
            | Intrinsic::Trunc
            | Intrinsic::Round
            | Intrinsic::RoundEven
            | Intrinsic::Rint
            | Intrinsic::NearbyInt => {
                let rm = match i {
                    Intrinsic::Floor => RoundingMode::Rtn,
                    Intrinsic::Ceil => RoundingMode::Rtp,
                    Intrinsic::Trunc => RoundingMode::Rtz,
                    Intrinsic::Round => RoundingMode::Rna,
                    _ => RoundingMode::Rne,
                };
                let r = self.cx.fp(FpOp::RoundToIntegral(rm), f, &[a[0]])?;
                let nan = self.nan_spec(NanOp::Exact, f, &a)?;
                self.nan_result_when(f, r, nan, &ins)?
            }
            _ => unreachable!("a floating-point intrinsic"),
        };
        let mut r = r;
        if fl & flags::NSZ != 0 {
            let when = match i {
                Intrinsic::Sqrt
                | Intrinsic::Floor
                | Intrinsic::Ceil
                | Intrinsic::Trunc
                | Intrinsic::Round
                | Intrinsic::RoundEven
                | Intrinsic::Rint
                | Intrinsic::NearbyInt => Some(self.test(f, FpTest::Zero, a[0])?),
                Intrinsic::CopySign => Some(self.test(f, FpTest::Zero, a[1])?),
                _ => None,
            };
            if let Some(when) = when {
                r = self.nsz_out(f, r, when)?;
            }
        }
        let mut all = a.clone();
        all.push(r);
        let fp = self.fmf_poison(fl, f, &all)?;
        p = self.or(p, fp)?;
        Ok((r, p))
    }

    /// Poison of a value with `range` or `nofpclass` constraints: an input, or a return value.
    pub(crate) fn constrained(
        &mut self,
        ty: Ty,
        v: Expr,
        range: Option<&(String, String)>,
        classes: u16,
    ) -> Result<Expr, Error> {
        let mut p = self.fls;
        if let (Some((lo, hi)), Ty::Int(bits)) = (range, ty) {
            let lo = super::value::int_literal(lo, bits);
            let hi = super::value::int_literal(hi, bits);
            if let (Some(lo), Some(hi)) = (lo, hi) {
                // v in [lo, hi), wrapping: v − lo <u hi − lo ([0, 0) is empty).
                let (l, h) = (self.cx.constant(&lo)?, self.cx.constant(&hi)?);
                let off = self.cx.bin(BinOp::Sub, v, l)?;
                let span = self.cx.bin(BinOp::Sub, h, l)?;
                let inside = self.cx.cmp(CmpOpExt::Ult, off, span)?;
                let out = self.not(inside)?;
                p = self.or(p, out)?;
            }
        }
        if let (Ty::Float(f), true) = (ty, classes != 0) {
            let neg = self.msb(v)?;
            let pos = self.not(neg)?;
            let tests = [
                (fpclass::SNAN, FpTest::Nan, None),
                (fpclass::QNAN, FpTest::Nan, None),
                (fpclass::NINF, FpTest::Infinite, Some(true)),
                (fpclass::PINF, FpTest::Infinite, Some(false)),
                (fpclass::NNORM, FpTest::Normal, Some(true)),
                (fpclass::PNORM, FpTest::Normal, Some(false)),
                (fpclass::NSUB, FpTest::Subnormal, Some(true)),
                (fpclass::PSUB, FpTest::Subnormal, Some(false)),
                (fpclass::NZERO, FpTest::Zero, Some(true)),
                (fpclass::PZERO, FpTest::Zero, Some(false)),
            ];
            for (bit, test, sign) in tests {
                if classes & bit == 0 {
                    continue;
                }
                let mut c = self.test(f, test, v)?;
                if bit == fpclass::SNAN || bit == fpclass::QNAN {
                    let q = self.cx.bit(v, (f.sb() - 2) as u16)?;
                    let want = if bit == fpclass::QNAN {
                        q
                    } else {
                        self.not(q)?
                    };
                    c = self.and(c, want)?;
                }
                match sign {
                    Some(true) => c = self.and(c, neg)?,
                    Some(false) => c = self.and(c, pos)?,
                    None => {}
                }
                p = self.or(p, c)?;
            }
        }
        Ok(p)
    }

    /// Encodes a program (with the precondition, for the source).
    pub(crate) fn body(mut self, body: &Body, with_pre: bool) -> Result<Side, Error> {
        let pre = match self.t.pre {
            Some(p) if with_pre => self.val(p)?.0,
            _ => self.tru,
        };
        let nb = body.blocks.len();
        let order = topological(body)?;
        let mut reach: Vec<Expr> = vec![self.fls; nb];
        reach[0] = self.tru;
        // Taken edges: (from, to) → condition (with `from` reached).
        let mut taken: BTreeMap<(usize, usize), Expr> = BTreeMap::new();
        let reachable: Vec<bool> = {
            let mut r = vec![false; nb];
            for &b in &order {
                r[b] = true;
            }
            r
        };
        let mut result: Option<(Expr, Expr)> = None;
        for &b in &order {
            if b != 0 {
                let mut r = self.fls;
                for (&(_, to), &c) in &taken {
                    if to == b {
                        r = self.or(r, c)?;
                    }
                }
                reach[b] = r;
            }
            self.reach = reach[b];
            let block = &body.blocks[b];
            for &i in &block.insts {
                let Node::Inst(inst) = self.t.node(i) else {
                    continue;
                };
                if inst.op == Op::Phi {
                    let v = self.phi(i, b, &taken, &reachable)?;
                    self.memo.insert(i, v);
                    self.values.push((i, v.0, v.1));
                } else {
                    self.val(i)?;
                }
            }
            match &block.term {
                Term::None => {}
                Term::Ret(v) => {
                    if let Some(v) = v {
                        let (x, mut px) = self.val(*v)?;
                        let ty = self.ty(*v);
                        let extra =
                            self.constrained(ty, x, body.ret_range.as_ref(), body.ret_nofpclass)?;
                        px = self.or(px, extra)?;
                        if body.ret_noundef {
                            self.add_ub(px)?;
                        }
                        result = Some(match result {
                            None => (x, px),
                            Some((rx, rp)) => (
                                self.cx.select(self.reach, x, rx)?,
                                self.cx.select(self.reach, px, rp)?,
                            ),
                        });
                    }
                }
                Term::Jmp(t) => {
                    let e = taken.entry((b, *t)).or_insert(self.fls);
                    *e = self.cx.bin(BinOp::Or, *e, self.reach)?;
                }
                Term::Br(c, t, f) => {
                    let (cv, cp) = self.val(*c)?;
                    self.add_ub(cp)?;
                    let yes = self.and(self.reach, cv)?;
                    let ncv = self.not(cv)?;
                    let no = self.and(self.reach, ncv)?;
                    for (to, cond) in [(*t, yes), (*f, no)] {
                        let old = taken.get(&(b, to)).copied().unwrap_or(self.fls);
                        let new = self.or(old, cond)?;
                        taken.insert((b, to), new);
                    }
                }
                Term::Switch(c, dflt, cases) => {
                    let (cv, cp) = self.val(*c)?;
                    self.add_ub(cp)?;
                    let mut any = self.fls;
                    for &(lit, to) in cases {
                        let (lv, _) = self.val(lit)?;
                        let hit = self.eq(cv, lv)?;
                        any = self.or(any, hit)?;
                        let cond = self.and(self.reach, hit)?;
                        let old = taken.get(&(b, to)).copied().unwrap_or(self.fls);
                        let new = self.or(old, cond)?;
                        taken.insert((b, to), new);
                    }
                    let none = self.not(any)?;
                    let cond = self.and(self.reach, none)?;
                    let old = taken.get(&(b, *dflt)).copied().unwrap_or(self.fls);
                    let new = self.or(old, cond)?;
                    taken.insert((b, *dflt), new);
                }
                Term::Unreachable => self.add_ub(self.tru)?,
            }
        }
        if let Some(root) = body.root {
            self.reach = self.tru;
            result = Some(self.val(root)?);
        }
        Ok(Side {
            result,
            ub: self.ub,
            valid: self.valid,
            choices: self.widths,
            keyed: self.keyed,
            values: self.values,
            pre,
        })
    }

    fn phi(
        &mut self,
        n: NodeId,
        b: usize,
        taken: &BTreeMap<(usize, usize), Expr>,
        reachable: &[bool],
    ) -> Result<(Expr, Expr), Error> {
        let Node::Inst(inst) = self.t.node(n) else {
            unreachable!("a phi")
        };
        let mut v: Option<(Expr, Expr)> = None;
        for (&a, &from) in inst.args.iter().zip(&inst.incoming) {
            // Values from blocks never reached never flow in.
            if !reachable[from] {
                continue;
            }
            let (x, px) = self.val(a)?;
            let cond = taken.get(&(from, b)).copied().unwrap_or(self.fls);
            v = Some(match v {
                None => (x, px),
                Some((y, py)) => (self.cx.select(cond, x, y)?, self.cx.select(cond, px, py)?),
            });
        }
        let Some((mut x, mut p)) = v else {
            return Err(unsupported("a phi without operands"));
        };
        if let Ty::Float(f) = self.ty(n) {
            if inst.flags & flags::NSZ != 0 {
                x = self.nsz(f, x)?;
            }
            let fp = self.fmf_poison(inst.flags, f, &[x])?;
            p = self.or(p, fp)?;
        }
        Ok((x, p))
    }
}

/// The operations [`Enc::nan_spec`] knows.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum NanOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Sqrt,
    Fma,
    /// Conversions and rounding to an integral value: a NaN only from a NaN.
    Exact,
}

/// `2^k` at the width of `z` (which must be wider than `k`).
fn pow2(z: &BitVec, k: u16) -> Result<BitVec, Error> {
    let one = BitVec::one(z.width());
    let sh = BitVec::wrapping_from_u64(z.width(), u64::from(k));
    Ok(BitVec::apply_bin(BinOp::Shl, &one, &sh)?)
}

fn icmp(p: IPred) -> CmpOpExt {
    match p {
        IPred::Eq => CmpOpExt::Eq,
        IPred::Ne => CmpOpExt::Ne,
        IPred::Ugt => CmpOpExt::Ugt,
        IPred::Uge => CmpOpExt::Uge,
        IPred::Ult => CmpOpExt::Ult,
        IPred::Ule => CmpOpExt::Ule,
        IPred::Sgt => CmpOpExt::Sgt,
        IPred::Sge => CmpOpExt::Sge,
        IPred::Slt => CmpOpExt::Slt,
        IPred::Sle => CmpOpExt::Sle,
    }
}

/// The blocks in an order where every edge goes forward; an error on a cycle.
fn topological(body: &Body) -> Result<Vec<usize>, Error> {
    let n = body.blocks.len();
    let succ = |b: usize| -> Vec<usize> {
        match &body.blocks[b].term {
            Term::Jmp(t) => vec![*t],
            Term::Br(_, t, f) => vec![*t, *f],
            Term::Switch(_, d, cases) => {
                let mut v: Vec<usize> = cases.iter().map(|&(_, t)| t).collect();
                v.push(*d);
                v
            }
            _ => Vec::new(),
        }
    };
    // Depth-first from the entry: post-order reversed; a back edge is a loop.
    let mut state = vec![0u8; n]; // 0 new, 1 on the stack, 2 done
    let mut post = Vec::with_capacity(n);
    let mut stack: Vec<(usize, usize)> = vec![(0, 0)];
    state[0] = 1;
    while let Some(&mut (b, ref mut k)) = stack.last_mut() {
        let s = succ(b);
        if *k < s.len() {
            let t = s[*k];
            *k += 1;
            match state[t] {
                0 => {
                    state[t] = 1;
                    stack.push((t, 0));
                }
                1 => {
                    return Err(unsupported(format!(
                        "a loop (block %{} branches back to %{})",
                        body.blocks[b].name, body.blocks[t].name
                    )));
                }
                _ => {}
            }
        } else {
            state[b] = 2;
            post.push(b);
            stack.pop();
        }
    }
    post.reverse();
    Ok(post)
}
