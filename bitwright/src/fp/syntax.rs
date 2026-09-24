//! The text syntax of floating-point operations: `fp.<op>[.<mode>]<format>(operands)`.
//!
//! A format is written `.f32` when it has a name ([`FpFormat::NAMED`]), else as the generics
//! `<eb, sb>`; a conversion between formats names both (`fp.convert.rne.f32.f64`, or
//! `<eb, sb, eb', sb'>`), and a conversion to an integer ends with the integer's width
//! (`fp.to_sbv.rtz.f64<32>`, or `<eb, sb, n>`). Every identifier that starts with `fp.` is
//! reserved.

use super::node::{Desc, Kind};
use super::{FpFormat, FpOp, FpTest, RoundingMode};
use crate::Width;

/// What an `fp.` name calls: a node kind, or an operation built from other operators.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Base {
    Op(Kind),
    Sub,
    Neg,
    Abs,
    CopySign,
    Gt,
    Ge,
    Test(FpTest),
    X87Load,
    X87Store,
}

const NAMES: &[(&str, Base)] = &[
    ("add", Base::Op(Kind::Add)),
    ("sub", Base::Sub),
    ("mul", Base::Op(Kind::Mul)),
    ("div", Base::Op(Kind::Div)),
    ("fma", Base::Op(Kind::Fma)),
    ("sqrt", Base::Op(Kind::Sqrt)),
    ("rem", Base::Op(Kind::Rem)),
    ("round", Base::Op(Kind::RoundToIntegral)),
    ("min", Base::Op(Kind::Min)),
    ("max", Base::Op(Kind::Max)),
    ("eq", Base::Op(Kind::Eq)),
    ("lt", Base::Op(Kind::Lt)),
    ("le", Base::Op(Kind::Le)),
    ("gt", Base::Gt),
    ("ge", Base::Ge),
    ("neg", Base::Neg),
    ("abs", Base::Abs),
    ("copysign", Base::CopySign),
    ("isnan", Base::Test(FpTest::Nan)),
    ("isinf", Base::Test(FpTest::Infinite)),
    ("iszero", Base::Test(FpTest::Zero)),
    ("isnormal", Base::Test(FpTest::Normal)),
    ("issubnormal", Base::Test(FpTest::Subnormal)),
    ("isneg", Base::Test(FpTest::Negative)),
    ("ispos", Base::Test(FpTest::Positive)),
    ("convert", Base::Op(Kind::Convert)),
    ("from_sbv", Base::Op(Kind::FromSInt)),
    ("from_ubv", Base::Op(Kind::FromUInt)),
    ("to_sbv", Base::Op(Kind::ToSInt)),
    ("to_ubv", Base::Op(Kind::ToUInt)),
    ("x87_load", Base::X87Load),
    ("x87_store", Base::X87Store),
];

impl Base {
    pub(crate) fn rounds(self) -> bool {
        match self {
            Base::Op(k) => matches!(
                k,
                Kind::Add
                    | Kind::Mul
                    | Kind::Div
                    | Kind::Fma
                    | Kind::Sqrt
                    | Kind::RoundToIntegral
                    | Kind::Convert
                    | Kind::FromSInt
                    | Kind::FromUInt
                    | Kind::ToSInt
                    | Kind::ToUInt
            ),
            Base::Sub => true,
            _ => false,
        }
    }

    /// How many formats the name gives.
    pub(crate) fn formats(self) -> usize {
        match self {
            Base::Op(Kind::Convert) => 2,
            Base::X87Load | Base::X87Store => 0,
            _ => 1,
        }
    }

    pub(crate) fn int_width(self) -> bool {
        matches!(self, Base::Op(Kind::ToSInt | Kind::ToUInt))
    }

    pub(crate) fn arity(self) -> usize {
        match self {
            Base::Op(k) => k.arity(),
            Base::Sub | Base::CopySign | Base::Gt | Base::Ge => 2,
            _ => 1,
        }
    }
}

fn op_name(k: Kind) -> &'static str {
    NAMES
        .iter()
        .find(|(_, b)| *b == Base::Op(k))
        .map_or("?", |&(n, _)| n)
}

/// The call name of a floating-point node, generics included.
pub(crate) fn call_name(d: &Desc) -> String {
    let mut s = format!("fp.{}", op_name(d.kind()));
    if let Some(rm) = d.op.rounding_mode() {
        s.push('.');
        s.push_str(rm.name());
    }
    let mut generics: Vec<u32> = Vec::new();
    let mut formats = vec![d.format];
    if let FpOp::Convert { to, .. } = d.op {
        formats.push(to);
    }
    if formats.iter().all(|f| f.name().is_some()) {
        for f in &formats {
            s.push('.');
            s.push_str(f.name().unwrap_or("?"));
        }
    } else {
        for f in &formats {
            generics.extend([f.eb(), f.sb()]);
        }
    }
    if let FpOp::ToSInt(_, w) | FpOp::ToUInt(_, w) = d.op {
        generics.push(u32::from(w.bits()));
    }
    if !generics.is_empty() {
        let g: Vec<String> = generics.iter().map(u32::to_string).collect();
        s.push('<');
        s.push_str(&g.join(", "));
        s.push('>');
    }
    s
}

/// A parsed `fp.` name, before its generics.
#[derive(Clone, Debug)]
pub(crate) struct Name {
    pub(crate) base: Base,
    pub(crate) rm: RoundingMode,
    /// The formats the name spells (`.f32`); the rest come from the generics.
    pub(crate) named: Vec<FpFormat>,
}

impl Name {
    /// How many generic numbers must follow: `(eb, sb)` for each format the name does not
    /// spell, and the integer width of a conversion to an integer.
    pub(crate) fn generics(&self) -> usize {
        let unnamed = self.base.formats() - self.named.len();
        2 * unnamed + usize::from(self.base.int_width())
    }

    /// The call, completed by its generics.
    pub(crate) fn finish(&self, generics: &[u16]) -> Result<Call, String> {
        let mut formats = self.named.clone();
        let mut g = generics.iter().map(|&v| u32::from(v));
        while formats.len() < self.base.formats() {
            let (eb, sb) = (g.next().unwrap_or(0), g.next().unwrap_or(0));
            formats.push(FpFormat::new(eb, sb).map_err(|e| e.to_string())?);
        }
        let int_width = if self.base.int_width() {
            let n = g.next().unwrap_or(0);
            Some(Width::new(n as u16).map_err(|e| e.to_string())?)
        } else {
            None
        };
        Ok(Call {
            base: self.base,
            rm: self.rm,
            formats,
            int_width,
        })
    }
}

/// A complete `fp.` call.
#[derive(Clone, Debug)]
pub(crate) struct Call {
    pub(crate) base: Base,
    pub(crate) rm: RoundingMode,
    pub(crate) formats: Vec<FpFormat>,
    pub(crate) int_width: Option<Width>,
}

impl Call {
    /// The format of the floating-point operands (or of the result, from an integer).
    pub(crate) fn format(&self) -> FpFormat {
        self.formats.first().copied().unwrap_or(FpFormat::X87)
    }

    /// The node this call builds, when it is one.
    pub(crate) fn desc(&self) -> Option<Desc> {
        let Base::Op(k) = self.base else {
            return None;
        };
        let rm = self.rm;
        let op = match k {
            Kind::Add => FpOp::Add(rm),
            Kind::Mul => FpOp::Mul(rm),
            Kind::Div => FpOp::Div(rm),
            Kind::Fma => FpOp::Fma(rm),
            Kind::Sqrt => FpOp::Sqrt(rm),
            Kind::Rem => FpOp::Rem,
            Kind::RoundToIntegral => FpOp::RoundToIntegral(rm),
            Kind::Min => FpOp::Min,
            Kind::Max => FpOp::Max,
            Kind::Eq => FpOp::Eq,
            Kind::Lt => FpOp::Lt,
            Kind::Le => FpOp::Le,
            Kind::Convert => FpOp::Convert {
                to: *self.formats.get(1)?,
                rm,
            },
            Kind::FromSInt => FpOp::FromSInt(rm),
            Kind::FromUInt => FpOp::FromUInt(rm),
            Kind::ToSInt => FpOp::ToSInt(rm, self.int_width?),
            Kind::ToUInt => FpOp::ToUInt(rm, self.int_width?),
        };
        Some(Desc {
            op,
            format: self.format(),
        })
    }

    /// The width of each operand, when the call fixes it (the integer operand of a conversion
    /// from an integer takes any width).
    pub(crate) fn operand_width(&self) -> Option<u16> {
        match self.base {
            Base::Op(Kind::FromSInt | Kind::FromUInt) => None,
            Base::X87Load => Some(80),
            Base::X87Store => Some(FpFormat::X87.width().bits()),
            _ => Some(self.format().width().bits()),
        }
    }

    /// The width of the result.
    pub(crate) fn result_width(&self) -> u16 {
        match self.base {
            Base::Gt | Base::Ge | Base::Test(_) => 1,
            Base::X87Load => FpFormat::X87.width().bits(),
            Base::X87Store => 80,
            Base::Sub | Base::Neg | Base::Abs | Base::CopySign => self.format().width().bits(),
            Base::Op(_) => self.desc().map_or(1, |d| d.width()),
        }
    }
}

/// Parses an identifier that starts with `fp.`.
pub(crate) fn parse_name(ident: &str) -> Result<Name, String> {
    let (base, rm, named) = split_name(ident)?;
    let rm = match rm {
        Some(m) => RoundingMode::from_name(m)
            .ok_or_else(|| format!("`{m}` is not a rounding mode (rne, rna, rtp, rtn, rtz)"))?,
        None => RoundingMode::Rne,
    };
    Ok(Name { base, rm, named })
}

/// An `fp.` identifier's parts: what it calls, the word in the rounding mode's place (for the
/// operations that round; a rule may name a rounding-mode variable there), and the formats it
/// names.
pub(crate) fn split_name(ident: &str) -> Result<(Base, Option<&str>, Vec<FpFormat>), String> {
    let mut parts = ident.split('.');
    parts.next(); // "fp"
    let op = parts.next().unwrap_or("");
    let base = NAMES
        .iter()
        .find(|(n, _)| *n == op)
        .map(|&(_, b)| b)
        .ok_or_else(|| format!("unknown floating-point operation `fp.{op}`"))?;
    let rm = if base.rounds() {
        Some(
            parts
                .next()
                .ok_or_else(|| format!("`fp.{op}` needs a rounding mode (`fp.{op}.rne`, …)"))?,
        )
    } else {
        None
    };
    let mut named = Vec::new();
    for p in parts {
        let f = FpFormat::from_name(p).ok_or_else(|| {
            format!("`{p}` is not a format name (f16, bf16, f32, f64, f128, f256)")
        })?;
        named.push(f);
    }
    if named.len() > base.formats() || (!named.is_empty() && named.len() < base.formats()) {
        return Err(format!(
            "`fp.{op}` names {} format(s): all by name, or all as `<eb, sb>`",
            base.formats()
        ));
    }
    Ok((base, rm, named))
}
