//! Building floating-point nodes.
//!
//! The operations that round (and the comparisons, `min`, `max`, `rem` and the conversions) are
//! nodes of their own. The ones that only look at or change the sign and exponent bits are
//! built from bit-vector operators, so every pass sees through them: `neg` is `x ^ sign`, `abs`
//! is `x & ~sign`, `copysign` combines the two, each classification is one unsigned comparison
//! of the encoding (`isNaN(x)` is `|x| >u ∞`), `sub` is `add` of the negation, `gt` and `ge`
//! are `lt` and `le` with the operands swapped, and x87's load and store are extracts,
//! concatenations and selects.
//!
//! Construction applies exact identities (`fp_identity`): bit for bit on every encoding, and
//! never adding a node.

use super::{Context, Expr, Node};
use crate::error::{Error, WidthError};
use crate::fp::node::{Desc, Kind};
use crate::fp::{FpCmpOp, FpFormat, FpOp, FpTest, RoundingMode};
use crate::ops::{BinOp, CmpOp};
use crate::{BitVec, Width};

/// The sign bit of `f`.
fn sign_mask(f: FpFormat) -> BitVec {
    BitVec::smin(f.width())
}

/// The smallest positive normal encoding: exponent field 1, significand 0.
fn min_normal(f: FpFormat) -> BitVec {
    let one = BitVec::one(f.width());
    let shift = BitVec::wrapping_from_u64(f.width(), u64::from(f.sb() - 1));
    BitVec::bin_unchecked(BinOp::Shl, &one, &shift)
}

impl Context {
    /// The floating-point node `d` on `args`: widths checked, folded when every operand is a
    /// constant, commutative operands in canonical order.
    pub(crate) fn c_fp(&mut self, d: Desc, args: &[u32]) -> Result<u32, Error> {
        let kind = d.kind();
        if args.len() != kind.arity() {
            return Err(Error::Unsupported(format!(
                "{:?} takes {} operands, got {}",
                d.op,
                kind.arity(),
                args.len()
            )));
        }
        let fw = d.format.width().bits();
        if !matches!(kind, Kind::FromSInt | Kind::FromUInt) {
            for &a in args {
                let w = self.wid(a);
                if w != fw {
                    return Err(WidthError::Mismatch { left: fw, right: w }.into());
                }
            }
        }
        let mut kids = [0u32; 3];
        kids[..args.len()].copy_from_slice(args);
        if kind.commutative() && self.order(kids[0], kids[1]).is_gt() {
            kids.swap(0, 1);
        }
        let consts: Option<Vec<BitVec>> = kids[..args.len()]
            .iter()
            .map(|&a| self.const_val(a))
            .collect();
        if let Some(vals) = consts {
            return self.mk_const(&crate::fp::eval(&d, &vals));
        }
        if let Some(i) = self.fp_identity(d, &kids[..args.len()])? {
            return Ok(i);
        }
        let (aux, attr) = d.encode();
        let mut n = Node::new(kind.opcode(), d.width(), kids[0], kids[1], kids[2]);
        n.aux = aux;
        if kind == Kind::Convert {
            n.b = attr;
        }
        self.mk(n)
    }

    /// The operand of a floating-point negation (`x ^ sign`) of format `f`.
    fn fneg_of(&self, f: FpFormat, i: u32) -> Option<u32> {
        let n = self.node(i);
        (n.op == super::OpCode::Xor && self.const_val(n.b) == Some(sign_mask(f))).then_some(n.a)
    }

    /// Whether node `i` is the constant `v` of format `f`.
    fn fp_is(&self, i: u32, v: &BitVec) -> bool {
        self.const_val(i).as_ref() == Some(v)
    }

    /// Exact identities, bit for bit on every encoding (so a NaN operand gives the canonical NaN
    /// on both sides, and zeros keep their signs), none of which adds a node:
    /// `fma(x, 1, y) = x + y`; `fma(x, y, −0) = x · y` except toward −∞ (where `+0 + −0` is
    /// `−0`); `x · 2 = x + x`; `(−a) · (−b) = a · b` and likewise for `/`; negation reverses
    /// the order (`−a < −b` is `b < a`, `−a = −b` is `a = b`); `x < x` is false; rounding to
    /// an integral value a rounded value or a converted integer changes nothing; a signed
    /// conversion of a zero or sign extension converts the operand itself; and an integer that
    /// converts exactly converts back to itself, extended.
    fn fp_identity(&mut self, d: Desc, k: &[u32]) -> Result<Option<u32>, Error> {
        let f = d.format;
        if !matches!(
            d.op,
            FpOp::Fma(_)
                | FpOp::Mul(_)
                | FpOp::Div(_)
                | FpOp::Lt
                | FpOp::Le
                | FpOp::Eq
                | FpOp::RoundToIntegral(_)
                | FpOp::FromSInt(_)
                | FpOp::FromUInt(_)
                | FpOp::ToSInt(..)
                | FpOp::ToUInt(..)
        ) {
            return Ok(None);
        }
        // 1 and 2: the exponent field at the bias (and one above), the significand 0.
        let power = |k: u64| {
            let w = f.width();
            let e = BitVec::wrapping_from_u64(w, (1u64 << (f.eb() - 1)) - 1 + k);
            let shift = BitVec::wrapping_from_u64(w, u64::from(f.sb() - 1));
            BitVec::bin_unchecked(BinOp::Shl, &e, &shift)
        };
        let (one, two) = (power(0), power(1));
        let with = |op| Desc { op, format: f };
        let r = match d.op {
            FpOp::Fma(rm) if self.fp_is(k[1], &one) => {
                Some(self.c_fp(with(FpOp::Add(rm)), &[k[0], k[2]])?)
            }
            FpOp::Fma(rm) if rm != RoundingMode::Rtn && self.fp_is(k[2], &f.zero(true)) => {
                Some(self.c_fp(with(FpOp::Mul(rm)), &[k[0], k[1]])?)
            }
            FpOp::Mul(rm) if self.fp_is(k[1], &two) => {
                Some(self.c_fp(with(FpOp::Add(rm)), &[k[0], k[0]])?)
            }
            FpOp::Mul(_) | FpOp::Div(_) => match (self.fneg_of(f, k[0]), self.fneg_of(f, k[1])) {
                (Some(a), Some(b)) => Some(self.c_fp(d, &[a, b])?),
                _ => None,
            },
            FpOp::Lt if k[0] == k[1] => Some(self.mk_const(&BitVec::from_bool(false))?),
            FpOp::Lt | FpOp::Le | FpOp::Eq => {
                match (self.fneg_of(f, k[0]), self.fneg_of(f, k[1])) {
                    (Some(a), Some(b)) if d.op == FpOp::Eq => Some(self.c_fp(d, &[a, b])?),
                    (Some(a), Some(b)) => Some(self.c_fp(d, &[b, a])?),
                    _ => None,
                }
            }
            // Already integral: a rounded value; or a converted integer (exact, or rounded to a
            // float of at least 2^(p−1), which is an integer), when an overflow's ±Ω is an
            // integer too (`emax ≥ p − 1`: not so in tiny formats, where −4 toward +∞ in (2, 3)
            // is −3.5). In one format only: binary16 and bfloat16 are both 16 bits.
            FpOp::RoundToIntegral(_)
                if self.fp_desc(k[0]).is_some_and(|inner| inner.format == f)
                    && match self.node(k[0]).op {
                        super::OpCode::FRound => true,
                        // emax + 1 = 2^(eb−1) ≥ p.
                        super::OpCode::FFromS | super::OpCode::FFromU => {
                            1u32 << (f.eb() - 1) >= f.sb()
                        }
                        _ => false,
                    } =>
            {
                Some(k[0])
            }
            // An integer that converts exactly converts back to itself, extended.
            FpOp::ToSInt(_, w) | FpOp::ToUInt(_, w) => self.int_round_trip(d, f, k[0], w)?,
            FpOp::FromSInt(rm) | FpOp::FromUInt(rm) => {
                let n = self.node(k[0]);
                match (d.op, n.op) {
                    (_, super::OpCode::Zext) => Some(self.c_fp(with(FpOp::FromUInt(rm)), &[n.a])?),
                    (FpOp::FromSInt(_), super::OpCode::Sext) => Some(self.c_fp(d, &[n.a])?),
                    _ => None,
                }
            }
            _ => None,
        };
        Ok(r)
    }

    /// `to_int(from_int(i))` when every value of `i` converts exactly and fits the result:
    /// `i` extended. Exact means at most `p` significant bits and within the format's range: `m`
    /// bits unsigned, `m − 1` signed (whose `−2^(m−1)` is a power of two).
    fn int_round_trip(
        &mut self,
        d: Desc,
        f: FpFormat,
        a: u32,
        w: Width,
    ) -> Result<Option<u32>, Error> {
        let n = self.node(a);
        let signed_out = matches!(d.op, FpOp::ToSInt(..));
        let (signed_in, i) = match n.op {
            super::OpCode::FFromS => (true, n.a),
            super::OpCode::FFromU => (false, n.a),
            _ => return Ok(None),
        };
        if self.fp_desc(a).is_none_or(|inner| inner.format != f) {
            return Ok(None);
        }
        let m = u32::from(self.wid(i));
        let emax = (1u32 << (f.eb() - 1)) - 1;
        let exact = if signed_in {
            m - 1 <= f.sb() && m - 1 <= emax
        } else {
            m <= f.sb() && m <= emax + 1
        };
        let out = u32::from(w.bits());
        // The result's range must hold every value: signed into signed needs n ≥ m, unsigned
        // into unsigned n ≥ m, unsigned into signed n > m; a negative value into unsigned
        // saturates, so not that.
        let fits = match (signed_in, signed_out) {
            (true, true) | (false, false) => out >= m,
            (false, true) => out > m,
            (true, false) => false,
        };
        if !exact || !fits {
            return Ok(None);
        }
        if out == m {
            return Ok(Some(i));
        }
        let e = if signed_in {
            self.c_sext(i, w.bits())?
        } else {
            self.c_zext(i, w.bits())?
        };
        Ok(Some(e))
    }

    fn c_fneg(&mut self, f: FpFormat, a: u32) -> Result<u32, Error> {
        let s = self.mk_const(&sign_mask(f))?;
        self.c_bin(BinOp::Xor, a, s)
    }

    fn c_fabs(&mut self, f: FpFormat, a: u32) -> Result<u32, Error> {
        let m = self.mk_const(&BitVec::smax(f.width()))?;
        self.c_bin(BinOp::And, a, m)
    }

    fn c_fcmp(&mut self, f: FpFormat, op: FpCmpOp, a: u32, b: u32) -> Result<u32, Error> {
        let (op, a, b) = match op {
            FpCmpOp::Eq => (FpOp::Eq, a, b),
            FpCmpOp::Lt => (FpOp::Lt, a, b),
            FpCmpOp::Le => (FpOp::Le, a, b),
            FpCmpOp::Gt => (FpOp::Lt, b, a),
            FpCmpOp::Ge => (FpOp::Le, b, a),
        };
        self.c_fp(Desc { op, format: f }, &[a, b])
    }

    fn c_ftest(&mut self, f: FpFormat, t: FpTest, a: u32) -> Result<u32, Error> {
        let w = f.width();
        if self.wid(a) != w.bits() {
            return Err(WidthError::Mismatch {
                left: w.bits(),
                right: self.wid(a),
            }
            .into());
        }
        let inf = f.inf(false);
        let c = |cx: &mut Context, v: &BitVec| cx.mk_const(v);
        match t {
            FpTest::Nan => {
                let mag = self.c_fabs(f, a)?;
                let i = c(self, &inf)?;
                self.c_cmp(CmpOp::Ult, i, mag)
            }
            FpTest::Infinite => {
                let mag = self.c_fabs(f, a)?;
                let i = c(self, &inf)?;
                self.c_cmp(CmpOp::Eq, mag, i)
            }
            FpTest::Zero => {
                let mag = self.c_fabs(f, a)?;
                let z = c(self, &BitVec::zero(w))?;
                self.c_cmp(CmpOp::Eq, mag, z)
            }
            FpTest::Subnormal => {
                // 0 < |a| < min_normal, as (|a| − 1) <u (min_normal − 1).
                let mag = self.c_fabs(f, a)?;
                let m1 = c(self, &BitVec::ones(w))?;
                let shifted = self.c_bin(BinOp::Add, mag, m1)?;
                let bound = BitVec::bin_unchecked(BinOp::Sub, &min_normal(f), &BitVec::one(w));
                let b = c(self, &bound)?;
                self.c_cmp(CmpOp::Ult, shifted, b)
            }
            FpTest::Normal => {
                // min_normal ≤ |a| < ∞, as (|a| − min_normal) <u (∞ − min_normal).
                let mag = self.c_fabs(f, a)?;
                let neg_min = BitVec::un_unchecked(crate::UnOp::Neg, &min_normal(f));
                let k = c(self, &neg_min)?;
                let shifted = self.c_bin(BinOp::Add, mag, k)?;
                let bound = BitVec::bin_unchecked(BinOp::Sub, &inf, &min_normal(f));
                let b = c(self, &bound)?;
                self.c_cmp(CmpOp::Ult, shifted, b)
            }
            FpTest::Negative => {
                // The sign set and |a| ≤ ∞: (a ^ sign) ≤u ∞.
                let flipped = self.c_fneg(f, a)?;
                let i = c(self, &inf)?;
                self.c_cmp(CmpOp::Ule, flipped, i)
            }
            FpTest::Positive => {
                let i = c(self, &inf)?;
                self.c_cmp(CmpOp::Ule, a, i)
            }
        }
    }

    fn c_x87_load(&mut self, x: u32) -> Result<u32, Error> {
        if self.wid(x) != 80 {
            return Err(WidthError::Mismatch {
                left: 80,
                right: self.wid(x),
            }
            .into());
        }
        let sign = self.c_extract(x, 79, 1)?;
        let e = self.c_extract(x, 64, 15)?;
        let i = self.c_extract(x, 63, 1)?;
        let frac = self.c_extract(x, 0, 63)?;
        let zero15 = self.c_uint15(0)?;
        let one15 = self.c_uint15(1)?;
        let e_zero = self.c_cmp(CmpOp::Eq, e, zero15)?;
        let one1 = self.c_uint1(1)?;
        let i_set = self.c_cmp(CmpOp::Eq, i, one1)?;
        // A pseudo-denormal (e = 0, i = 1) stands for the normal value with exponent field 1.
        let pseudo_denormal = self.c_bin(BinOp::And, e_zero, i_set)?;
        let e_fixed = self.c_select(pseudo_denormal, one15, e)?;
        let se = self.c_concat(sign, e_fixed)?;
        let value = self.c_concat(se, frac)?;
        // e ≠ 0 with i = 0 (unnormal, pseudo-infinity, pseudo-NaN) is invalid: the NaN.
        let e_nonzero = self.c_cmp(CmpOp::Ne, e, zero15)?;
        let i_clear = self.c_cmp(CmpOp::Ne, i, one1)?;
        let invalid = self.c_bin(BinOp::And, e_nonzero, i_clear)?;
        let nan = self.mk_const(&FpFormat::X87.nan())?;
        self.c_select(invalid, nan, value)
    }

    fn c_x87_store(&mut self, a: u32) -> Result<u32, Error> {
        let w = FpFormat::X87.width().bits();
        if self.wid(a) != w {
            return Err(WidthError::Mismatch {
                left: w,
                right: self.wid(a),
            }
            .into());
        }
        let se = self.c_extract(a, 63, 16)?;
        let e = self.c_extract(a, 63, 15)?;
        let frac = self.c_extract(a, 0, 63)?;
        let zero15 = self.c_uint15(0)?;
        let i = self.c_cmp(CmpOp::Ne, e, zero15)?;
        let sei = self.c_concat(se, i)?;
        self.c_concat(sei, frac)
    }

    fn c_uint15(&mut self, v: u64) -> Result<u32, Error> {
        self.mk_const(&BitVec::wrapping_from_u64(Width::new(15)?, v))
    }

    fn c_uint1(&mut self, v: u64) -> Result<u32, Error> {
        self.mk_const(&BitVec::wrapping_from_u64(Width::W1, v))
    }

    /// Builds a parsed `fp.` call.
    pub(crate) fn build_fp_call(
        &mut self,
        call: &crate::fp::syntax::Call,
        args: &[Expr],
    ) -> Result<Expr, Error> {
        use crate::fp::syntax::Base;
        let f = call.format();
        match call.base {
            Base::Op(_) => {
                let d = call
                    .desc()
                    .ok_or_else(|| Error::Unsupported("an incomplete fp call".into()))?;
                self.fp(d.op, d.format, args)
            }
            Base::Sub => self.fp_sub(f, call.rm, args[0], args[1]),
            Base::Neg => self.fp_neg(f, args[0]),
            Base::Abs => self.fp_abs(f, args[0]),
            Base::CopySign => self.fp_copysign(f, args[0], args[1]),
            Base::Gt => self.fp_cmp(f, FpCmpOp::Gt, args[0], args[1]),
            Base::Ge => self.fp_cmp(f, FpCmpOp::Ge, args[0], args[1]),
            Base::Test(t) => self.fp_test(f, t, args[0]),
            Base::X87Load => self.x87_load(args[0]),
            Base::X87Store => self.x87_store(args[0]),
        }
    }

    // ----- public builder -------------------------------------------------------------------

    /// The floating-point operation `op` of `format` on `args` (1 to 3 operands, as
    /// [`FpOp::arity`] says). The floating-point operands must be `format`'s width; the
    /// operand of [`FpOp::FromSInt`] and [`FpOp::FromUInt`] may be any width (`format` is
    /// then the result's). Operations on constants are folded.
    ///
    /// ```
    /// use bitwright::fp::{FpFormat, FpOp, RoundingMode};
    /// use bitwright::{BitVec, Context, Width};
    ///
    /// let mut cx = Context::new();
    /// let x = cx.symbol("x", Width::W64)?;
    /// let three = cx.constant(&BitVec::from_f64(3.0))?;
    /// let e = cx.fp(FpOp::Mul(RoundingMode::Rne), FpFormat::F64, &[x, three])?;
    /// assert_eq!(cx.display(e).to_string(), "fp.mul.rne.f64(x, 0x4008000000000000)");
    /// # Ok::<(), bitwright::Error>(())
    /// ```
    pub fn fp(&mut self, op: FpOp, format: FpFormat, args: &[Expr]) -> Result<Expr, Error> {
        let ids = self.ids(args)?;
        let i = self.c_fp(Desc { op, format }, &ids)?;
        Ok(self.handle(i))
    }

    /// `a − b`, built as `a + neg(b)` (the same function, bit for bit).
    pub fn fp_sub(
        &mut self,
        format: FpFormat,
        rm: RoundingMode,
        a: Expr,
        b: Expr,
    ) -> Result<Expr, Error> {
        let (a, b) = (self.id(a)?, self.id(b)?);
        if self.wid(b) != format.width().bits() {
            return Err(WidthError::Mismatch {
                left: format.width().bits(),
                right: self.wid(b),
            }
            .into());
        }
        let nb = self.c_fneg(format, b)?;
        let i = self.c_fp(
            Desc {
                op: FpOp::Add(rm),
                format,
            },
            &[a, nb],
        )?;
        Ok(self.handle(i))
    }

    /// `a` with its sign bit flipped (a NaN too): `a ^ sign`.
    pub fn fp_neg(&mut self, format: FpFormat, a: Expr) -> Result<Expr, Error> {
        let a = self.id(a)?;
        let i = self.c_fneg(format, a)?;
        Ok(self.handle(i))
    }

    /// `a` with its sign bit cleared (a NaN too): `a & ~sign`.
    pub fn fp_abs(&mut self, format: FpFormat, a: Expr) -> Result<Expr, Error> {
        let a = self.id(a)?;
        let i = self.c_fabs(format, a)?;
        Ok(self.handle(i))
    }

    /// `a` with the sign bit of `b`.
    pub fn fp_copysign(&mut self, format: FpFormat, a: Expr, b: Expr) -> Result<Expr, Error> {
        let (a, b) = (self.id(a)?, self.id(b)?);
        let mag = self.c_fabs(format, a)?;
        let s = self.mk_const(&sign_mask(format))?;
        let sign = self.c_bin(BinOp::And, b, s)?;
        let i = self.c_bin(BinOp::Or, mag, sign)?;
        Ok(self.handle(i))
    }

    /// A comparison (1 bit; false when either operand is a NaN).
    pub fn fp_cmp(
        &mut self,
        format: FpFormat,
        op: FpCmpOp,
        a: Expr,
        b: Expr,
    ) -> Result<Expr, Error> {
        let (a, b) = (self.id(a)?, self.id(b)?);
        let i = self.c_fcmp(format, op, a, b)?;
        Ok(self.handle(i))
    }

    /// A classification test (1 bit).
    pub fn fp_test(&mut self, format: FpFormat, t: FpTest, a: Expr) -> Result<Expr, Error> {
        let a = self.id(a)?;
        let i = self.c_ftest(format, t, a)?;
        Ok(self.handle(i))
    }

    /// The x87 load of an 80-bit extended-precision encoding, as a value of
    /// [`FpFormat::X87`]; see [`crate::fp::x87_load`].
    pub fn x87_load(&mut self, a: Expr) -> Result<Expr, Error> {
        let a = self.id(a)?;
        let i = self.c_x87_load(a)?;
        Ok(self.handle(i))
    }

    /// The x87 store of a value of [`FpFormat::X87`] as its 80-bit encoding; see
    /// [`crate::fp::x87_store`].
    pub fn x87_store(&mut self, a: Expr) -> Result<Expr, Error> {
        let a = self.id(a)?;
        let i = self.c_x87_store(a)?;
        Ok(self.handle(i))
    }
}
