//! How a floating-point node stores its operation: the opcode names the operation, `aux` holds
//! the rounding mode (bits 5–7) and the exponent width `eb` of the operation's format
//! (bits 0–4), and a conversion between formats keeps the target's `eb` in `b`. The
//! significand width follows from the operand's width (or, for a conversion from an integer,
//! the node's own width).

use super::{FpFormat, FpOp, RoundingMode};
use crate::expr::{Node, OpCode};

/// The operation a floating-point opcode performs, without its attributes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Kind {
    Add,
    Mul,
    Div,
    Fma,
    Sqrt,
    Rem,
    Round,
    Min,
    Max,
    Eq,
    Lt,
    Le,
    Convert,
    FromS,
    FromU,
    ToS,
    ToU,
}

impl Kind {
    pub(crate) const fn opcode(self) -> OpCode {
        match self {
            Kind::Add => OpCode::FAdd,
            Kind::Mul => OpCode::FMul,
            Kind::Div => OpCode::FDiv,
            Kind::Fma => OpCode::FFma,
            Kind::Sqrt => OpCode::FSqrt,
            Kind::Rem => OpCode::FRem,
            Kind::Round => OpCode::FRound,
            Kind::Min => OpCode::FMin,
            Kind::Max => OpCode::FMax,
            Kind::Eq => OpCode::FEq,
            Kind::Lt => OpCode::FLt,
            Kind::Le => OpCode::FLe,
            Kind::Convert => OpCode::FConvert,
            Kind::FromS => OpCode::FFromS,
            Kind::FromU => OpCode::FFromU,
            Kind::ToS => OpCode::FToS,
            Kind::ToU => OpCode::FToU,
        }
    }

    pub(crate) const fn of(op: OpCode) -> Option<Kind> {
        Some(match op {
            OpCode::FAdd => Kind::Add,
            OpCode::FMul => Kind::Mul,
            OpCode::FDiv => Kind::Div,
            OpCode::FFma => Kind::Fma,
            OpCode::FSqrt => Kind::Sqrt,
            OpCode::FRem => Kind::Rem,
            OpCode::FRound => Kind::Round,
            OpCode::FMin => Kind::Min,
            OpCode::FMax => Kind::Max,
            OpCode::FEq => Kind::Eq,
            OpCode::FLt => Kind::Lt,
            OpCode::FLe => Kind::Le,
            OpCode::FConvert => Kind::Convert,
            OpCode::FFromS => Kind::FromS,
            OpCode::FFromU => Kind::FromU,
            OpCode::FToS => Kind::ToS,
            OpCode::FToU => Kind::ToU,
            _ => return None,
        })
    }

    pub(crate) const fn arity(self) -> usize {
        match self {
            Kind::Fma => 3,
            Kind::Add
            | Kind::Mul
            | Kind::Div
            | Kind::Rem
            | Kind::Min
            | Kind::Max
            | Kind::Eq
            | Kind::Lt
            | Kind::Le => 2,
            _ => 1,
        }
    }

    pub(crate) const fn of_op(op: FpOp) -> Kind {
        match op {
            FpOp::Add(_) => Kind::Add,
            FpOp::Mul(_) => Kind::Mul,
            FpOp::Div(_) => Kind::Div,
            FpOp::Fma(_) => Kind::Fma,
            FpOp::Sqrt(_) => Kind::Sqrt,
            FpOp::Rem => Kind::Rem,
            FpOp::RoundToIntegral(_) => Kind::Round,
            FpOp::Min => Kind::Min,
            FpOp::Max => Kind::Max,
            FpOp::Eq => Kind::Eq,
            FpOp::Lt => Kind::Lt,
            FpOp::Le => Kind::Le,
            FpOp::Convert { .. } => Kind::Convert,
            FpOp::FromSInt(_) => Kind::FromS,
            FpOp::FromUInt(_) => Kind::FromU,
            FpOp::ToSInt(..) => Kind::ToS,
            FpOp::ToUInt(..) => Kind::ToU,
        }
    }

    /// Whether the first two operands commute (bit for bit, NaNs being canonical).
    pub(crate) const fn commutative(self) -> bool {
        matches!(
            self,
            Kind::Add | Kind::Mul | Kind::Fma | Kind::Min | Kind::Max | Kind::Eq
        )
    }
}

/// A floating-point node's operation, decoded.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Desc {
    pub(crate) op: FpOp,
    /// The format of the floating-point operands (for a conversion from an integer, of the
    /// result).
    pub(crate) format: FpFormat,
}

fn rm_code(rm: RoundingMode) -> u8 {
    match rm {
        RoundingMode::Rne => 0,
        RoundingMode::Rna => 1,
        RoundingMode::Rtp => 2,
        RoundingMode::Rtn => 3,
        RoundingMode::Rtz => 4,
    }
}

fn rm_of(aux: u8) -> RoundingMode {
    match aux >> 5 {
        1 => RoundingMode::Rna,
        2 => RoundingMode::Rtp,
        3 => RoundingMode::Rtn,
        4 => RoundingMode::Rtz,
        _ => RoundingMode::Rne,
    }
}

impl Desc {
    pub(crate) fn kind(&self) -> Kind {
        Kind::of_op(self.op)
    }

    /// The width of the result.
    pub(crate) fn width(&self) -> u16 {
        match self.op {
            FpOp::Eq | FpOp::Lt | FpOp::Le => 1,
            FpOp::Convert { to, .. } => to.width().bits(),
            FpOp::ToSInt(_, w) | FpOp::ToUInt(_, w) => w.bits(),
            _ => self.format.width().bits(),
        }
    }

    /// `aux` and the attribute kept in `b` (0 unless a conversion between formats).
    pub(crate) fn encode(&self) -> (u8, u32) {
        let rm = self.op.rounding_mode().unwrap_or(RoundingMode::Rne);
        let aux = (rm_code(rm) << 5) | self.format.eb() as u8;
        let b = match self.op {
            FpOp::Convert { to, .. } => to.eb(),
            _ => 0,
        };
        (aux, b)
    }

    /// The operation of an FP node, given the width of its first operand.
    pub(crate) fn decode(n: &Node, operand_width: u16) -> Option<Desc> {
        let kind = Kind::of(n.op)?;
        let rm = rm_of(n.aux);
        let eb = u32::from(n.aux & 0x1f);
        let fp_width = match kind {
            Kind::FromS | Kind::FromU => n.width,
            _ => operand_width,
        };
        let format = FpFormat::new(eb, u32::from(fp_width) - eb).ok()?;
        let op = match kind {
            Kind::Add => FpOp::Add(rm),
            Kind::Mul => FpOp::Mul(rm),
            Kind::Div => FpOp::Div(rm),
            Kind::Fma => FpOp::Fma(rm),
            Kind::Sqrt => FpOp::Sqrt(rm),
            Kind::Rem => FpOp::Rem,
            Kind::Round => FpOp::RoundToIntegral(rm),
            Kind::Min => FpOp::Min,
            Kind::Max => FpOp::Max,
            Kind::Eq => FpOp::Eq,
            Kind::Lt => FpOp::Lt,
            Kind::Le => FpOp::Le,
            Kind::Convert => {
                let to_eb = n.b;
                FpOp::Convert {
                    to: FpFormat::new(to_eb, u32::from(n.width) - to_eb).ok()?,
                    rm,
                }
            }
            Kind::FromS => FpOp::FromSInt(rm),
            Kind::FromU => FpOp::FromUInt(rm),
            Kind::ToS => FpOp::ToSInt(rm, crate::Width::new(n.width).ok()?),
            Kind::ToU => FpOp::ToUInt(rm, crate::Width::new(n.width).ok()?),
        };
        Some(Desc { op, format })
    }
}
