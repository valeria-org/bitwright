//! IEEE 754 floating point on bit-vectors.
//!
//! A floating-point value is a [`BitVec`] holding an IEEE 754 interchange encoding of a format
//! [`FpFormat`] `(eb, sb)`: a sign bit, `eb` exponent bits and `sb − 1` trailing significand bits
//! (SMT-LIB's convention: `sb` counts the hidden bit). Every operation is total and exact: it
//! is defined for every input pattern and gives exactly one result pattern, as the book's
//! chapter on floating point specifies. In short:
//!
//! - results are correctly rounded in the operation's [`RoundingMode`];
//! - every operation that produces a NaN produces the format's canonical quiet NaN (sign 0,
//!   exponent all ones, only the top significand bit set); `neg`, `abs` and `copysign` change the
//!   sign bit only, of a NaN too;
//! - `min` and `max` are IEEE 754-2019's minimumNumber and maximumNumber (a NaN operand is
//!   ignored, `−0 < +0`);
//! - conversions to integers saturate, and a NaN converts to 0.
//!
//! ```
//! use bitwright::fp::{FpFormat, RoundingMode};
//! use bitwright::BitVec;
//!
//! let f = FpFormat::F32;
//! let (a, b) = (BitVec::from_f32(0.1), BitVec::from_f32(0.2));
//! let sum = f.add(RoundingMode::Rne, &a, &b)?;
//! assert_eq!(sum.to_f32(), Some(0.1f32 + 0.2f32));
//! // The exact sum lies 3/4 of the way to the next value up: to nearest (and toward +∞) it
//! // rounds up, toward zero one unit in the last place lower.
//! let down = f.add(RoundingMode::Rtz, &a, &b)?;
//! assert_eq!(down.to_f32(), Some(f32::from_bits((0.1f32 + 0.2f32).to_bits() - 1)));
//! # Ok::<(), bitwright::WidthError>(())
//! ```

#[cfg(test)]
mod expr_tests;
mod frame;
pub(crate) mod node;
#[cfg(test)]
mod reference;
mod soft;
pub(crate) mod syntax;
#[cfg(test)]
pub(crate) mod tests;

use core::cmp::Ordering;
use core::fmt;

use crate::{BitVec, Width, WidthError};
use frame::{Frame, MID_PRECISION, Mid, NARROW_PRECISION, SMALL_PRECISION, Wide};
use soft::Fmt;

/// Runs `$body` with `$S` the frame type a format of precision `$p` computes in.
macro_rules! frames_for {
    ($p:expr, $S:ident => $body:expr) => {{
        let p: u32 = $p;
        if p <= SMALL_PRECISION {
            #[allow(dead_code)]
            type $S = u64;
            $body
        } else if p <= NARROW_PRECISION {
            #[allow(dead_code)]
            type $S = u128;
            $body
        } else if p <= MID_PRECISION {
            #[allow(dead_code)]
            type $S = Mid;
            $body
        } else {
            #[allow(dead_code)]
            type $S = Wide;
            $body
        }
    }};
}

/// Runs `$body` with `$S` the frame type the format `$fmt` computes in.
macro_rules! frames {
    ($fmt:expr, $S:ident => $body:expr) => {
        frames_for!($fmt.sb(), $S => $body)
    };
}

/// A binary floating-point format: `eb` exponent bits and `sb` significand bits, the hidden bit
/// included, so a value is `eb + sb` bits wide. `2 ≤ eb ≤ 31`, `sb ≥ 2`, `eb + sb ≤ 512`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FpFormat {
    eb: u8,
    sb: u16,
}

impl FpFormat {
    /// IEEE binary16 (half precision): `(5, 11)`.
    pub const F16: FpFormat = FpFormat { eb: 5, sb: 11 };
    /// bfloat16: `(8, 8)`.
    pub const BF16: FpFormat = FpFormat { eb: 8, sb: 8 };
    /// IEEE binary32 (single precision): `(8, 24)`.
    pub const F32: FpFormat = FpFormat { eb: 8, sb: 24 };
    /// IEEE binary64 (double precision): `(11, 53)`.
    pub const F64: FpFormat = FpFormat { eb: 11, sb: 53 };
    /// IEEE binary128 (quadruple precision): `(15, 113)`.
    pub const F128: FpFormat = FpFormat { eb: 15, sb: 113 };
    /// IEEE binary256 (octuple precision): `(19, 237)`.
    pub const F256: FpFormat = FpFormat { eb: 19, sb: 237 };
    /// The values of x87 extended precision, `(15, 64)`, 79 bits wide; see [`x87_load`] and
    /// [`x87_store`] for its 80-bit memory encoding.
    pub const X87: FpFormat = FpFormat { eb: 15, sb: 64 };

    /// The named formats, with the names the text syntax uses for them.
    pub const NAMED: [(FpFormat, &'static str); 6] = [
        (FpFormat::F16, "f16"),
        (FpFormat::BF16, "bf16"),
        (FpFormat::F32, "f32"),
        (FpFormat::F64, "f64"),
        (FpFormat::F128, "f128"),
        (FpFormat::F256, "f256"),
    ];

    /// The format `(eb, sb)`, if `2 ≤ eb ≤ 31`, `sb ≥ 2` and `eb + sb ≤ 512`.
    pub const fn new(eb: u32, sb: u32) -> Result<FpFormat, WidthError> {
        if eb < 2 || eb > 31 || sb < 2 || eb + sb > Width::MAX_BITS as u32 {
            return Err(WidthError::FpFormat { eb, sb });
        }
        Ok(FpFormat {
            eb: eb as u8,
            sb: sb as u16,
        })
    }

    /// Exponent bits.
    pub const fn eb(self) -> u32 {
        self.eb as u32
    }

    /// Significand bits, the hidden bit included (the precision).
    pub const fn sb(self) -> u32 {
        self.sb as u32
    }

    /// The width of an encoding: `eb + sb`.
    pub fn width(self) -> Width {
        Width::new(self.eb as u16 + self.sb).expect("a valid format fits in 512 bits")
    }

    /// The name of a standard format (`"f32"`, …), if it has one.
    pub fn name(self) -> Option<&'static str> {
        Self::NAMED
            .iter()
            .find(|(f, _)| *f == self)
            .map(|&(_, n)| n)
    }

    /// The format a name of [`NAMED`](Self::NAMED) stands for.
    pub fn from_name(name: &str) -> Option<FpFormat> {
        Self::NAMED
            .iter()
            .find(|&&(_, n)| n == name)
            .map(|&(f, _)| f)
    }

    fn fmt(self) -> Fmt {
        Fmt::new(self.eb(), self.sb())
    }

    fn check(self, v: &BitVec) -> Result<(), WidthError> {
        let (left, right) = (self.width().bits(), v.width().bits());
        if left == right {
            Ok(())
        } else {
            Err(WidthError::Mismatch { left, right })
        }
    }

    /// The canonical quiet NaN.
    pub fn nan(self) -> BitVec {
        frames!(self, S => store::<S>(self.width(), soft::nan::<S>(&self.fmt())))
    }

    /// An infinity.
    pub fn inf(self, negative: bool) -> BitVec {
        frames!(self, S => store::<S>(self.width(), soft::inf::<S>(&self.fmt(), negative)))
    }

    /// A zero.
    pub fn zero(self, negative: bool) -> BitVec {
        frames!(self, S => store::<S>(self.width(), soft::zero::<S>(&self.fmt(), negative)))
    }

    /// `a + b`.
    pub fn add(self, rm: RoundingMode, a: &BitVec, b: &BitVec) -> Result<BitVec, WidthError> {
        self.bin(a, b, |f, x, y| {
            frames!(f, S => {
                let r = soft::add::<S>(&f.fmt(), rm, load(x), load(y));
                store(f.width(), r)
            })
        })
    }

    /// `a − b`, which is `a + neg(b)`.
    pub fn sub(self, rm: RoundingMode, a: &BitVec, b: &BitVec) -> Result<BitVec, WidthError> {
        self.bin(a, b, |f, x, y| {
            frames!(f, S => {
                let r = soft::sub::<S>(&f.fmt(), rm, load(x), load(y));
                store(f.width(), r)
            })
        })
    }

    /// `a · b`.
    pub fn mul(self, rm: RoundingMode, a: &BitVec, b: &BitVec) -> Result<BitVec, WidthError> {
        self.bin(a, b, |f, x, y| {
            frames!(f, S => {
                let r = soft::mul::<S>(&f.fmt(), rm, load(x), load(y));
                store(f.width(), r)
            })
        })
    }

    /// `a / b`.
    pub fn div(self, rm: RoundingMode, a: &BitVec, b: &BitVec) -> Result<BitVec, WidthError> {
        self.bin(a, b, |f, x, y| {
            frames!(f, S => {
                let r = soft::div::<S>(&f.fmt(), rm, load(x), load(y));
                store(f.width(), r)
            })
        })
    }

    /// `a · b + c`, rounded once.
    pub fn fma(
        self,
        rm: RoundingMode,
        a: &BitVec,
        b: &BitVec,
        c: &BitVec,
    ) -> Result<BitVec, WidthError> {
        self.check(a)?;
        self.check(b)?;
        self.check(c)?;
        Ok(frames!(self, S => {
            let r = soft::fma::<S>(&self.fmt(), rm, load(a), load(b), load(c));
            store(self.width(), r)
        }))
    }

    /// `√a`.
    pub fn sqrt(self, rm: RoundingMode, a: &BitVec) -> Result<BitVec, WidthError> {
        self.check(a)?;
        Ok(frames!(self, S => store(self.width(), soft::sqrt::<S>(&self.fmt(), rm, load(a)))))
    }

    /// The IEEE remainder `a − n·b`, `n` the integer nearest `a / b` (ties to even). Exact, so
    /// it takes no rounding mode.
    pub fn rem(self, a: &BitVec, b: &BitVec) -> Result<BitVec, WidthError> {
        self.bin(a, b, |f, x, y| {
            frames!(f, S => {
                store(f.width(), soft::rem::<S>(&f.fmt(), load(x), load(y)))
            })
        })
    }

    /// `a` rounded to an integral value by `rm`.
    pub fn round_to_integral(self, rm: RoundingMode, a: &BitVec) -> Result<BitVec, WidthError> {
        self.check(a)?;
        Ok(frames!(self, S => {
            store(self.width(), soft::round_to_integral::<S>(&self.fmt(), rm, load(a)))
        }))
    }

    /// IEEE 754-2019 minimumNumber: the smaller operand (`−0 < +0`), a NaN operand ignored.
    pub fn min(self, a: &BitVec, b: &BitVec) -> Result<BitVec, WidthError> {
        self.bin(a, b, |f, x, y| {
            frames!(f, S => {
                store(f.width(), soft::min::<S>(&f.fmt(), load(x), load(y)))
            })
        })
    }

    /// IEEE 754-2019 maximumNumber: the larger operand (`−0 < +0`), a NaN operand ignored.
    pub fn max(self, a: &BitVec, b: &BitVec) -> Result<BitVec, WidthError> {
        self.bin(a, b, |f, x, y| {
            frames!(f, S => {
                store(f.width(), soft::max::<S>(&f.fmt(), load(x), load(y)))
            })
        })
    }

    /// `a` with its sign bit flipped (a NaN too).
    pub fn neg(self, a: &BitVec) -> Result<BitVec, WidthError> {
        self.check(a)?;
        Ok(frames!(self, S => store(self.width(), soft::neg::<S>(&self.fmt(), load(a)))))
    }

    /// `a` with its sign bit cleared (a NaN too).
    pub fn abs(self, a: &BitVec) -> Result<BitVec, WidthError> {
        self.check(a)?;
        let top = self.width().bits() - 1;
        Ok(frames!(self, S => store(self.width(), load::<S>(a).low(u32::from(top)))))
    }

    /// `a` with the sign bit of `b`.
    pub fn copysign(self, a: &BitVec, b: &BitVec) -> Result<BitVec, WidthError> {
        let abs = self.abs(a)?;
        self.check(b)?;
        if b.msb() { self.neg(&abs) } else { Ok(abs) }
    }

    /// IEEE comparison: `None` when either operand is a NaN (unordered), else how `v(a)`
    /// compares with `v(b)` (so `+0` and `−0` are equal).
    pub fn compare(self, a: &BitVec, b: &BitVec) -> Result<Option<Ordering>, WidthError> {
        self.check(a)?;
        self.check(b)?;
        Ok(frames!(self, S => soft::compare::<S>(&self.fmt(), load(a), load(b))))
    }

    /// Whether the comparison `op` holds (false when either operand is a NaN).
    pub fn cmp(self, op: FpCmpOp, a: &BitVec, b: &BitVec) -> Result<bool, WidthError> {
        let o = self.compare(a, b)?;
        Ok(match (op, o) {
            (_, None) => false,
            (FpCmpOp::Eq, Some(o)) => o == Ordering::Equal,
            (FpCmpOp::Lt, Some(o)) => o == Ordering::Less,
            (FpCmpOp::Le, Some(o)) => o != Ordering::Greater,
            (FpCmpOp::Gt, Some(o)) => o == Ordering::Greater,
            (FpCmpOp::Ge, Some(o)) => o != Ordering::Less,
        })
    }

    /// Whether `a` passes the test.
    pub fn test(self, t: FpTest, a: &BitVec) -> Result<bool, WidthError> {
        self.check(a)?;
        let (eb, sb) = (self.eb(), self.sb());
        let e_bits = frames!(self, S => {
            let mut l = [0u64; 1];
            load::<S>(a).shr(sb - 1).low(eb).write_limbs(&mut l);
            l[0]
        });
        let t_zero = frames!(self, S => load::<S>(a).low(sb - 1).is_zero());
        let e_max = (1u64 << eb) - 1;
        let nan = e_bits == e_max && !t_zero;
        Ok(match t {
            FpTest::Nan => nan,
            FpTest::Infinite => e_bits == e_max && t_zero,
            FpTest::Zero => e_bits == 0 && t_zero,
            FpTest::Subnormal => e_bits == 0 && !t_zero,
            FpTest::Normal => e_bits != 0 && e_bits != e_max,
            FpTest::Negative => a.msb() && !nan,
            FpTest::Positive => !a.msb() && !nan,
        })
    }

    /// Converts `a` from this format to `to`.
    pub fn convert(self, to: FpFormat, rm: RoundingMode, a: &BitVec) -> Result<BitVec, WidthError> {
        self.check(a)?;
        let (from_f, to_f) = (self.fmt(), to.fmt());
        Ok(frames_for!(self.sb().max(to.sb()), S => {
            store(to.width(), soft::convert::<S>(&from_f, &to_f, rm, load(a)))
        }))
    }

    /// The signed (two's complement) integer `x`, of any width, rounded to this format.
    pub fn from_sint(self, rm: RoundingMode, x: &BitVec) -> BitVec {
        let negative = x.msb();
        let mag = if negative {
            BitVec::un_unchecked(crate::UnOp::Neg, x)
        } else {
            *x
        };
        // The magnitude of the most negative value is 2^(n−1), which its unsigned reading is.
        self.round_magnitude(rm, negative, &mag)
    }

    /// The unsigned integer `x`, of any width, rounded to this format.
    pub fn from_uint(self, rm: RoundingMode, x: &BitVec) -> BitVec {
        self.round_magnitude(rm, false, x)
    }

    fn round_magnitude(self, rm: RoundingMode, negative: bool, mag: &BitVec) -> BitVec {
        let f = self.fmt();
        // Keep p + 3 bits, the rest jammed, so the format's own frame can round it.
        let wide = Wide::from_limbs(mag.limbs());
        if wide.is_zero() {
            return self.zero(false);
        }
        let keep = self.sb() + 3;
        let (m, e) = match wide.bits().checked_sub(keep) {
            Some(extra) if extra > 0 => (wide.shr_jam(extra), extra),
            _ => (wide, 0),
        };
        let mut l = [0u64; 9];
        m.write_limbs(&mut l);
        frames!(self, S => {
            let r = soft::round::<S>(&f, rm, negative, S::from_limbs(&l), i64::from(e), false);
            store(self.width(), r)
        })
    }

    /// `a` rounded to an integer by `rm` and saturated to a signed `width`-bit integer; a NaN
    /// converts to 0.
    pub fn to_sint(self, rm: RoundingMode, a: &BitVec, width: Width) -> Result<BitVec, WidthError> {
        self.to_integer(rm, a, width, true)
    }

    /// `a` rounded to an integer by `rm` and saturated to an unsigned `width`-bit integer (a
    /// negative value converts to 0); a NaN converts to 0.
    pub fn to_uint(self, rm: RoundingMode, a: &BitVec, width: Width) -> Result<BitVec, WidthError> {
        self.to_integer(rm, a, width, false)
    }

    fn to_integer(
        self,
        rm: RoundingMode,
        a: &BitVec,
        width: Width,
        signed: bool,
    ) -> Result<BitVec, WidthError> {
        self.check(a)?;
        let n = u32::from(width.bits());
        let (max, min) = if signed {
            (BitVec::smax(width), BitVec::smin(width))
        } else {
            (BitVec::ones(width), BitVec::zero(width))
        };
        // Magnitudes up to 2^n fit the wide frame; anything larger saturates anyway.
        let v = soft::to_integer::<Wide>(&self.fmt(), rm, load(a), n + 1);
        Ok(match v {
            soft::IntVal::Nan => BitVec::zero(width),
            soft::IntVal::PosInf | soft::IntVal::Huge { sign: false } => max,
            soft::IntVal::NegInf | soft::IntVal::Huge { sign: true } => min,
            soft::IntVal::Int { sign, mag } => {
                let mut l = [0u64; 9];
                mag.write_limbs(&mut l);
                if !sign {
                    let limit = if signed { n - 1 } else { n };
                    if mag.bits() > limit {
                        max
                    } else {
                        BitVec::wrapping_from_limbs(width, &l)
                    }
                } else if mag.is_zero() {
                    BitVec::zero(width)
                } else if !signed || mag > Wide::pow2(n - 1) {
                    min
                } else {
                    // −mag, two's complement (mag = 2^(n−1) gives the minimum).
                    let m = BitVec::wrapping_from_limbs(width, &l);
                    BitVec::un_unchecked(crate::UnOp::Neg, &m)
                }
            }
        })
    }

    fn bin(
        self,
        a: &BitVec,
        b: &BitVec,
        k: impl FnOnce(FpFormat, &BitVec, &BitVec) -> BitVec,
    ) -> Result<BitVec, WidthError> {
        self.check(a)?;
        self.check(b)?;
        Ok(k(self, a, b))
    }
}

impl fmt::Debug for FpFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.name() {
            Some(n) => write!(f, "{n}"),
            None => write!(f, "fp<{}, {}>", self.eb, self.sb),
        }
    }
}

impl fmt::Display for FpFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

fn load<S: Frame>(v: &BitVec) -> S {
    S::from_limbs(v.limbs())
}

fn store<S: Frame>(w: Width, x: S) -> BitVec {
    let mut l = [0u64; 8];
    x.write_limbs(&mut l);
    BitVec::wrapping_from_limbs(w, &l)
}

/// A floating-point operator, as an expression node holds it (see [`View::Fp`](crate::View)).
/// Its [`FpFormat`] is given separately: the format of the floating-point operands, or of the
/// result for the conversions from integers.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum FpOp {
    /// `a + b`.
    Add(RoundingMode),
    /// `a · b`.
    Mul(RoundingMode),
    /// `a / b`.
    Div(RoundingMode),
    /// `a · b + c`, rounded once.
    Fma(RoundingMode),
    /// `√a`.
    Sqrt(RoundingMode),
    /// The IEEE remainder.
    Rem,
    /// Rounding to an integral value.
    RoundToIntegral(RoundingMode),
    /// minimumNumber.
    Min,
    /// maximumNumber.
    Max,
    /// `a = b` (1 bit).
    Eq,
    /// `a < b` (1 bit).
    Lt,
    /// `a ≤ b` (1 bit).
    Le,
    /// To another format.
    Convert {
        /// The result's format.
        to: FpFormat,
        /// The rounding mode.
        rm: RoundingMode,
    },
    /// From a signed integer of any width.
    FromSInt(RoundingMode),
    /// From an unsigned integer of any width.
    FromUInt(RoundingMode),
    /// To a signed integer of the given width, saturating (a NaN gives 0).
    ToSInt(RoundingMode, Width),
    /// To an unsigned integer of the given width, saturating (a NaN gives 0).
    ToUInt(RoundingMode, Width),
}

impl FpOp {
    /// The rounding mode, if the operation rounds.
    pub fn rounding_mode(self) -> Option<RoundingMode> {
        match self {
            FpOp::Add(rm)
            | FpOp::Mul(rm)
            | FpOp::Div(rm)
            | FpOp::Fma(rm)
            | FpOp::Sqrt(rm)
            | FpOp::RoundToIntegral(rm)
            | FpOp::Convert { rm, .. }
            | FpOp::FromSInt(rm)
            | FpOp::FromUInt(rm)
            | FpOp::ToSInt(rm, _)
            | FpOp::ToUInt(rm, _) => Some(rm),
            FpOp::Rem | FpOp::Min | FpOp::Max | FpOp::Eq | FpOp::Lt | FpOp::Le => None,
        }
    }

    /// The number of operands: 3 for `Fma`, 2 for the binary operations and comparisons, 1
    /// otherwise.
    pub fn arity(self) -> usize {
        node::Kind::of_op(self).arity()
    }
}

/// The operands of a floating-point node (1 to 3).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct FpArgs {
    args: [crate::Expr; 3],
    len: u8,
}

impl FpArgs {
    /// `args` must hold 1 to 3 handles.
    pub(crate) fn new(args: &[crate::Expr]) -> FpArgs {
        let mut a = [args[0]; 3];
        a[..args.len()].copy_from_slice(args);
        FpArgs {
            args: a,
            len: args.len() as u8,
        }
    }

    /// The operands in order.
    pub fn as_slice(&self) -> &[crate::Expr] {
        &self.args[..usize::from(self.len)]
    }
}

/// Evaluates a floating-point operation on operand values of the right widths.
pub(crate) fn eval(d: &node::Desc, args: &[BitVec]) -> BitVec {
    let f = d.format;
    let a = &args[0];
    let r = match d.op {
        FpOp::Add(rm) => f.add(rm, a, &args[1]),
        FpOp::Mul(rm) => f.mul(rm, a, &args[1]),
        FpOp::Div(rm) => f.div(rm, a, &args[1]),
        FpOp::Fma(rm) => f.fma(rm, a, &args[1], &args[2]),
        FpOp::Sqrt(rm) => f.sqrt(rm, a),
        FpOp::Rem => f.rem(a, &args[1]),
        FpOp::RoundToIntegral(rm) => f.round_to_integral(rm, a),
        FpOp::Min => f.min(a, &args[1]),
        FpOp::Max => f.max(a, &args[1]),
        FpOp::Eq => f.cmp(FpCmpOp::Eq, a, &args[1]).map(BitVec::from_bool),
        FpOp::Lt => f.cmp(FpCmpOp::Lt, a, &args[1]).map(BitVec::from_bool),
        FpOp::Le => f.cmp(FpCmpOp::Le, a, &args[1]).map(BitVec::from_bool),
        FpOp::Convert { to, rm } => f.convert(to, rm, a),
        FpOp::FromSInt(rm) => Ok(f.from_sint(rm, a)),
        FpOp::FromUInt(rm) => Ok(f.from_uint(rm, a)),
        FpOp::ToSInt(rm, w) => f.to_sint(rm, a, w),
        FpOp::ToUInt(rm, w) => f.to_uint(rm, a, w),
    };
    r.expect("operand widths are checked when the node is built")
}

/// A rounding direction (IEEE 754 §4.3), named as in SMT-LIB.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
#[non_exhaustive]
pub enum RoundingMode {
    /// To nearest, ties to even (the default everywhere).
    Rne,
    /// To nearest, ties away from zero.
    Rna,
    /// Toward +∞.
    Rtp,
    /// Toward −∞.
    Rtn,
    /// Toward zero.
    Rtz,
}

impl RoundingMode {
    /// Every mode.
    pub const ALL: [RoundingMode; 5] = [
        RoundingMode::Rne,
        RoundingMode::Rna,
        RoundingMode::Rtp,
        RoundingMode::Rtn,
        RoundingMode::Rtz,
    ];

    /// The name in the text syntax: `"rne"`, `"rna"`, `"rtp"`, `"rtn"`, `"rtz"`.
    pub const fn name(self) -> &'static str {
        match self {
            RoundingMode::Rne => "rne",
            RoundingMode::Rna => "rna",
            RoundingMode::Rtp => "rtp",
            RoundingMode::Rtn => "rtn",
            RoundingMode::Rtz => "rtz",
        }
    }

    /// The mode with this name.
    pub fn from_name(name: &str) -> Option<RoundingMode> {
        Self::ALL.into_iter().find(|m| m.name() == name)
    }
}

/// A floating-point comparison; each is false when either operand is a NaN.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
#[non_exhaustive]
pub enum FpCmpOp {
    /// `v(a) = v(b)` (`+0 = −0`).
    Eq,
    /// `v(a) < v(b)`.
    Lt,
    /// `v(a) ≤ v(b)`.
    Le,
    /// `v(a) > v(b)`.
    Gt,
    /// `v(a) ≥ v(b)`.
    Ge,
}

/// A classification test (SMT-LIB's `fp.isNaN`, …).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
#[non_exhaustive]
pub enum FpTest {
    /// Any NaN.
    Nan,
    /// `±∞`.
    Infinite,
    /// `±0`.
    Zero,
    /// A nonzero value with the minimum exponent field.
    Subnormal,
    /// A finite nonzero value that is not subnormal.
    Normal,
    /// The sign bit set, and not a NaN.
    Negative,
    /// The sign bit clear, and not a NaN.
    Positive,
}

/// Loads an 80-bit x87 extended-precision encoding as a value of [`FpFormat::X87`] (79 bits):
/// the explicit integer bit is dropped; a pseudo-denormal becomes the normal value it stands
/// for; an unnormal, a pseudo-infinity and a pseudo-NaN (which x87 rejects as invalid) become
/// the canonical NaN; other NaNs keep their payload.
pub fn x87_load(x: &BitVec) -> Result<BitVec, WidthError> {
    if x.width().bits() != 80 {
        return Err(WidthError::Mismatch {
            left: 80,
            right: x.width().bits(),
        });
    }
    let bits = x.to_u128().expect("80 bits");
    let sign = bits >> 79 & 1;
    let e = (bits >> 64) & 0x7fff;
    let i = (bits >> 63) & 1;
    let frac = bits & ((1u128 << 63) - 1);
    let w79 = FpFormat::X87.width();
    let out = |s: u128, e: u128, f: u128| BitVec::wrapping_from_u128(w79, s << 78 | e << 63 | f);
    Ok(match (e, i) {
        (0, 0) => out(sign, 0, frac),
        (0, _) => out(sign, 1, frac),
        (_, 1) => out(sign, e, frac),
        _ => FpFormat::X87.nan(),
    })
}

/// Stores a value of [`FpFormat::X87`] (79 bits) as its 80-bit x87 encoding: the explicit
/// integer bit is 1 exactly when the exponent field is nonzero. NaN payloads are kept.
pub fn x87_store(a: &BitVec) -> Result<BitVec, WidthError> {
    FpFormat::X87.check(a)?;
    let bits = a.to_u128().expect("79 bits");
    let sign = bits >> 78 & 1;
    let e = (bits >> 63) & 0x7fff;
    let frac = bits & ((1u128 << 63) - 1);
    let i = u128::from(e != 0);
    Ok(BitVec::wrapping_from_u128(
        Width::new(80).expect("80 bits"),
        sign << 79 | e << 64 | i << 63 | frac,
    ))
}

impl BitVec {
    /// The binary32 encoding of `v` (NaN payloads as they are).
    pub fn from_f32(v: f32) -> BitVec {
        BitVec::wrapping_from_u64(Width::W32, u64::from(v.to_bits()))
    }

    /// The binary64 encoding of `v` (NaN payloads as they are).
    pub fn from_f64(v: f64) -> BitVec {
        BitVec::wrapping_from_u64(Width::W64, v.to_bits())
    }

    /// The `f32` this 32-bit value encodes, `None` at another width.
    pub fn to_f32(&self) -> Option<f32> {
        (self.width() == Width::W32).then(|| f32::from_bits(self.limbs()[0] as u32))
    }

    /// The `f64` this 64-bit value encodes, `None` at another width.
    pub fn to_f64(&self) -> Option<f64> {
        (self.width() == Width::W64).then(|| f64::from_bits(self.limbs()[0]))
    }
}
