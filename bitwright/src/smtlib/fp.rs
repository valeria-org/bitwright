//! Floating-point nodes in SMT-LIB's FloatingPoint theory.
//!
//! An operand, a bit-vector, is read as a float with `((_ to_fp eb sb) x)`. A float result is
//! turned back into bits without `fp.to_ieee_bv`, which is not standard (a NaN has many
//! encodings): the exporter declares the bits and asserts what they are,
//!
//! ```text
//! (declare-const n7_bits (_ BitVec 32))
//! (assert (ite (fp.isNaN T) (= n7_bits NAN) (= ((_ to_fp 8 24) n7_bits) T)))
//! ```
//!
//! which pins exactly one pattern for every input: the canonical NaN, or the one encoding of a
//! non-NaN value (SMT-LIB's `=` tells `+0` and `−0` apart). What the standard leaves open is
//! spelled out as bitwright defines it: `min` and `max` return an operand's own pattern with
//! `−0 < +0`, and conversions to integers saturate, a NaN converting to 0.

use core::fmt::Write as _;

use super::export::{App, literal, sort};
use crate::error::Error;
use crate::fp::node::Desc;
use crate::fp::{FpFormat, FpOp, RoundingMode};
use crate::{BitVec, Width};

/// SMT-LIB's name of a rounding mode.
pub(crate) fn rm_name(rm: RoundingMode) -> &'static str {
    match rm {
        RoundingMode::Rne => "RNE",
        RoundingMode::Rna => "RNA",
        RoundingMode::Rtp => "RTP",
        RoundingMode::Rtn => "RTN",
        RoundingMode::Rtz => "RTZ",
    }
}

fn to_fp(f: FpFormat, bits: &str) -> String {
    format!("((_ to_fp {} {}) {bits})", f.eb(), f.sb())
}

/// A float literal of `f` from its encoding.
fn fp_lit(f: FpFormat, v: &BitVec) -> String {
    to_fp(f, &literal(v))
}

/// Declares the bits of the float term `t` of format `f` and asserts them; returns their name.
fn bits_of(out: &mut String, tag: &str, f: FpFormat, t: &str) -> String {
    let name = format!("{tag}_bits");
    let w = f.width().bits();
    writeln!(out, "(declare-const {name} {})", sort(w)).ok();
    writeln!(
        out,
        "(assert (ite (fp.isNaN {t}) (= {name} {}) (= {} {t})))",
        literal(&f.nan()),
        to_fp(f, &name)
    )
    .ok();
    name
}

/// `2^k` as a float of `f`, if it is finite there.
fn power_of_two(f: FpFormat, k: u32) -> Option<String> {
    let bias = (1u64 << (f.eb() - 1)) - 1;
    if u64::from(k) > bias {
        return None;
    }
    let w = f.width();
    let e = BitVec::wrapping_from_u64(w, u64::from(k) + bias);
    let shift = BitVec::wrapping_from_u64(w, u64::from(f.sb() - 1));
    let v = BitVec::bin_unchecked(crate::BinOp::Shl, &e, &shift);
    Some(fp_lit(f, &v))
}

/// The SMT-LIB term of a floating-point node.
pub(crate) fn term(out: &mut String, d: &Desc, app: &App<'_>) -> Result<String, Error> {
    let f = d.format;
    let arg = |k: usize| -> Result<&str, Error> {
        app.args
            .get(k)
            .map(String::as_str)
            .ok_or_else(|| Error::Contract(format!("{:?} is missing an operand", d.op)))
    };
    let x = |k: usize| arg(k).map(|a| to_fp(f, a));
    let rm = rm_name(d.op.rounding_mode().unwrap_or(RoundingMode::Rne));
    let tag = app.tag;
    let one_bit = |c: &str| format!("(ite {c} #b1 #b0)");
    let nan = literal(&f.nan());
    Ok(match d.op {
        FpOp::Add(_) => bits_of(out, tag, f, &format!("(fp.add {rm} {} {})", x(0)?, x(1)?)),
        FpOp::Mul(_) => bits_of(out, tag, f, &format!("(fp.mul {rm} {} {})", x(0)?, x(1)?)),
        FpOp::Div(_) => bits_of(out, tag, f, &format!("(fp.div {rm} {} {})", x(0)?, x(1)?)),
        FpOp::Fma(_) => bits_of(
            out,
            tag,
            f,
            &format!("(fp.fma {rm} {} {} {})", x(0)?, x(1)?, x(2)?),
        ),
        FpOp::Sqrt(_) => bits_of(out, tag, f, &format!("(fp.sqrt {rm} {})", x(0)?)),
        FpOp::Rem => bits_of(out, tag, f, &format!("(fp.rem {} {})", x(0)?, x(1)?)),
        FpOp::RoundToIntegral(_) => {
            bits_of(out, tag, f, &format!("(fp.roundToIntegral {rm} {})", x(0)?))
        }
        FpOp::Min | FpOp::Max => {
            // An operand's own pattern: a NaN one is skipped, −0 is below +0.
            let (a, b) = (arg(0)?, arg(1)?);
            let (fa, fb) = (x(0)?, x(1)?);
            let (order, zero_sign) = if d.op == FpOp::Min {
                ("fp.lt", "fp.isNegative")
            } else {
                ("fp.gt", "fp.isPositive")
            };
            format!(
                "(ite (and (fp.isNaN {fa}) (fp.isNaN {fb})) {nan} (ite (fp.isNaN {fa}) {b} \
                 (ite (fp.isNaN {fb}) {a} (ite (or ({order} {fa} {fb}) (and (fp.isZero {fa}) \
                 (fp.isZero {fb}) ({zero_sign} {fa}))) {a} {b}))))"
            )
        }
        FpOp::Eq => one_bit(&format!("(fp.eq {} {})", x(0)?, x(1)?)),
        FpOp::Lt => one_bit(&format!("(fp.lt {} {})", x(0)?, x(1)?)),
        FpOp::Le => one_bit(&format!("(fp.leq {} {})", x(0)?, x(1)?)),
        FpOp::Convert { to, .. } => bits_of(
            out,
            tag,
            to,
            &format!("((_ to_fp {} {}) {rm} {})", to.eb(), to.sb(), x(0)?),
        ),
        FpOp::FromSInt(_) => bits_of(
            out,
            tag,
            f,
            &format!("((_ to_fp {} {}) {rm} {})", f.eb(), f.sb(), arg(0)?),
        ),
        FpOp::FromUInt(_) => bits_of(
            out,
            tag,
            f,
            &format!(
                "((_ to_fp_unsigned {} {}) {rm} {})",
                f.eb(),
                f.sb(),
                arg(0)?
            ),
        ),
        FpOp::ToSInt(_, w) | FpOp::ToUInt(_, w) => {
            let signed = matches!(d.op, FpOp::ToSInt(..));
            to_integer(out, f, rm, &x(0)?, w, signed, tag)
        }
    })
}

/// A saturating conversion to an integer: `NaN` gives 0; the integer `k` a value rounds to by
/// `rm` gives its nearest end when outside the range; otherwise `fp.to_sbv` / `fp.to_ubv`
/// (which take `k` itself, however large). `k` is tested through `R = fp.roundToIntegral(a)`,
/// which equals `k` except that it overflows to an infinity when `k` exceeds the format's
/// largest value (possible only in formats too small for their own integers).
fn to_integer(
    out: &mut String,
    f: FpFormat,
    rm: &str,
    a: &str,
    w: Width,
    signed: bool,
    tag: &str,
) -> String {
    let n = u32::from(w.bits());
    let r = format!("{tag}_r");
    writeln!(
        out,
        "(define-fun {r} () (_ FloatingPoint {} {}) (fp.roundToIntegral {rm} {a}))",
        f.eb(),
        f.sb()
    )
    .ok();
    let emax = (1u32 << (f.eb() - 1)) - 1;
    // `k ≥ 2^m` (or `k ≤ −2^m`): against the float `2^m` when it is finite; when `2^m` is the
    // first power past the largest value, `R` overflows exactly when `|k|` reaches it; beyond
    // that no finite value reaches it, so only an infinite operand does.
    let reaches = |m: u32, negative: bool| {
        let (cmp, sign) = if negative {
            ("fp.leq", "fp.isNegative")
        } else {
            ("fp.geq", "fp.isPositive")
        };
        match power_of_two(f, m) {
            Some(t) => {
                let t = if negative { format!("(fp.neg {t})") } else { t };
                format!("({cmp} {r} {t})")
            }
            None if m == emax + 1 => format!("(and (fp.isInfinite {r}) ({sign} {r}))"),
            None => format!("(and (fp.isInfinite {a}) ({sign} {a}))"),
        }
    };
    let (max, min, hi, lo) = if signed {
        // Above 2^(n−1) − 1 means reaching 2^(n−1); below −2^(n−1) means reaching
        // −2^(n−1) − 1, but −2^(n−1) itself saturates to the same value, so reaching it will do.
        (
            BitVec::smax(w),
            BitVec::smin(w),
            reaches(n - 1, false),
            reaches(n - 1, true),
        )
    } else {
        let lo = format!("(fp.lt {r} (_ +zero {} {}))", f.eb(), f.sb());
        (BitVec::ones(w), BitVec::zero(w), reaches(n, false), lo)
    };
    let conv = if signed { "fp.to_sbv" } else { "fp.to_ubv" };
    format!(
        "(ite (fp.isNaN {a}) {} (ite {hi} {} (ite {lo} {} ((_ {conv} {n}) {rm} {a}))))",
        literal(&BitVec::zero(w)),
        literal(&max),
        literal(&min)
    )
}
