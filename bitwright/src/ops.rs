//! Operator kinds.
//!
//! The semantics of every operator are total and follow SMT-LIB QF_BV; see
//! `docs/design.md` §3.2. Shift and rotate counts have the width of the shifted value and are
//! read as unsigned.

/// Unary operators. All map a `W`-bit operand to a `W`-bit result.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[non_exhaustive]
pub enum UnOp {
    /// Bitwise complement.
    Not,
    /// Two's-complement negation.
    Neg,
    /// Number of set bits.
    Popcnt,
    /// Number of leading zero bits; `clz(0) = W`.
    Clz,
    /// Number of trailing zero bits; `ctz(0) = W`.
    Ctz,
    /// Byte reversal. Only defined when `W % 8 == 0` (a typing rule, not partiality).
    Bswap,
    /// Bit reversal.
    BitRev,
}

impl UnOp {
    /// Every unary operator.
    pub const ALL: [UnOp; 7] = [
        UnOp::Not,
        UnOp::Neg,
        UnOp::Popcnt,
        UnOp::Clz,
        UnOp::Ctz,
        UnOp::Bswap,
        UnOp::BitRev,
    ];

    /// The operator's name in the expression syntax.
    pub const fn name(self) -> &'static str {
        match self {
            UnOp::Not => "not",
            UnOp::Neg => "neg",
            UnOp::Popcnt => "popcnt",
            UnOp::Clz => "clz",
            UnOp::Ctz => "ctz",
            UnOp::Bswap => "bswap",
            UnOp::BitRev => "bitrev",
        }
    }
}

/// Binary operators. All map two `W`-bit operands to a `W`-bit result.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[non_exhaustive]
pub enum BinOp {
    /// Addition modulo `2^W`.
    Add,
    /// Subtraction modulo `2^W`.
    Sub,
    /// Multiplication modulo `2^W`.
    Mul,
    /// High `W` bits of the `2W`-bit unsigned product.
    UMulHi,
    /// High `W` bits of the `2W`-bit signed product.
    SMulHi,
    /// Unsigned division; `udiv(x, 0) = ones`.
    UDiv,
    /// Unsigned remainder; `urem(x, 0) = x`.
    URem,
    /// Signed truncating division (`bvsdiv`); `sdiv(x, 0) = (x <s 0 ? 1 : -1)`.
    SDiv,
    /// Signed remainder (`bvsrem`), sign follows the dividend; `srem(x, 0) = x`.
    SRem,
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise exclusive or.
    Xor,
    /// Left shift; a count `>= W` gives 0.
    Shl,
    /// Logical right shift; a count `>= W` gives 0.
    LShr,
    /// Arithmetic right shift; a count `>= W` gives the sign fill.
    AShr,
    /// Rotate left by `count mod W`.
    RotL,
    /// Rotate right by `count mod W`.
    RotR,
    /// Parallel bit deposit of the first operand under the mask in the second.
    Pdep,
    /// Parallel bit extract of the first operand under the mask in the second.
    Pext,
}

impl BinOp {
    /// Every binary operator.
    pub const ALL: [BinOp; 19] = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::UMulHi,
        BinOp::SMulHi,
        BinOp::UDiv,
        BinOp::URem,
        BinOp::SDiv,
        BinOp::SRem,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
        BinOp::RotL,
        BinOp::RotR,
        BinOp::Pdep,
        BinOp::Pext,
    ];

    /// The operator's name in the expression syntax.
    pub const fn name(self) -> &'static str {
        match self {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::UMulHi => "umulhi",
            BinOp::SMulHi => "smulhi",
            BinOp::UDiv => "udiv",
            BinOp::URem => "urem",
            BinOp::SDiv => "sdiv",
            BinOp::SRem => "srem",
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::Xor => "xor",
            BinOp::Shl => "shl",
            BinOp::LShr => "lshr",
            BinOp::AShr => "ashr",
            BinOp::RotL => "rotl",
            BinOp::RotR => "rotr",
            BinOp::Pdep => "pdep",
            BinOp::Pext => "pext",
        }
    }

    /// Whether the operands may be swapped without changing the result.
    pub const fn is_commutative(self) -> bool {
        matches!(
            self,
            BinOp::Add
                | BinOp::Mul
                | BinOp::UMulHi
                | BinOp::SMulHi
                | BinOp::And
                | BinOp::Or
                | BinOp::Xor
        )
    }
}

/// The comparison predicates stored in expressions. Each maps two `W`-bit operands to a 1-bit
/// result. `ugt`, `uge`, `sgt` and `sge` are spelled by swapping operands; see [`CmpOpExt`].
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[non_exhaustive]
pub enum CmpOp {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Unsigned less than.
    Ult,
    /// Unsigned less than or equal.
    Ule,
    /// Signed less than.
    Slt,
    /// Signed less than or equal.
    Sle,
}

impl CmpOp {
    /// Every stored predicate.
    pub const ALL: [CmpOp; 6] = [
        CmpOp::Eq,
        CmpOp::Ne,
        CmpOp::Ult,
        CmpOp::Ule,
        CmpOp::Slt,
        CmpOp::Sle,
    ];

    /// Whether the operands may be swapped without changing the result.
    pub const fn is_commutative(self) -> bool {
        matches!(self, CmpOp::Eq | CmpOp::Ne)
    }

    /// The logical negation of this predicate over the same operand order, as an extended
    /// predicate (for example `!(a <u b)` is `a >=u b`).
    pub const fn negated(self) -> CmpOpExt {
        match self {
            CmpOp::Eq => CmpOpExt::Ne,
            CmpOp::Ne => CmpOpExt::Eq,
            CmpOp::Ult => CmpOpExt::Uge,
            CmpOp::Ule => CmpOpExt::Ugt,
            CmpOp::Slt => CmpOpExt::Sge,
            CmpOp::Sle => CmpOpExt::Sgt,
        }
    }
}

/// Every comparison predicate, including the operand-swapped forms.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[non_exhaustive]
pub enum CmpOpExt {
    /// Equal.
    Eq,
    /// Not equal.
    Ne,
    /// Unsigned less than.
    Ult,
    /// Unsigned less than or equal.
    Ule,
    /// Unsigned greater than.
    Ugt,
    /// Unsigned greater than or equal.
    Uge,
    /// Signed less than.
    Slt,
    /// Signed less than or equal.
    Sle,
    /// Signed greater than.
    Sgt,
    /// Signed greater than or equal.
    Sge,
}

impl CmpOpExt {
    /// Every predicate.
    pub const ALL: [CmpOpExt; 10] = [
        CmpOpExt::Eq,
        CmpOpExt::Ne,
        CmpOpExt::Ult,
        CmpOpExt::Ule,
        CmpOpExt::Ugt,
        CmpOpExt::Uge,
        CmpOpExt::Slt,
        CmpOpExt::Sle,
        CmpOpExt::Sgt,
        CmpOpExt::Sge,
    ];

    /// The stored predicate and whether the operands must be swapped to express `self`.
    pub const fn canonical(self) -> (CmpOp, bool) {
        match self {
            CmpOpExt::Eq => (CmpOp::Eq, false),
            CmpOpExt::Ne => (CmpOp::Ne, false),
            CmpOpExt::Ult => (CmpOp::Ult, false),
            CmpOpExt::Ule => (CmpOp::Ule, false),
            CmpOpExt::Ugt => (CmpOp::Ult, true),
            CmpOpExt::Uge => (CmpOp::Ule, true),
            CmpOpExt::Slt => (CmpOp::Slt, false),
            CmpOpExt::Sle => (CmpOp::Sle, false),
            CmpOpExt::Sgt => (CmpOp::Slt, true),
            CmpOpExt::Sge => (CmpOp::Sle, true),
        }
    }

    /// The predicate's spelling in the expression syntax.
    pub const fn symbol(self) -> &'static str {
        match self {
            CmpOpExt::Eq => "==",
            CmpOpExt::Ne => "!=",
            CmpOpExt::Ult => "<u",
            CmpOpExt::Ule => "<=u",
            CmpOpExt::Ugt => ">u",
            CmpOpExt::Uge => ">=u",
            CmpOpExt::Slt => "<s",
            CmpOpExt::Sle => "<=s",
            CmpOpExt::Sgt => ">s",
            CmpOpExt::Sge => ">=s",
        }
    }
}

impl From<CmpOp> for CmpOpExt {
    fn from(op: CmpOp) -> Self {
        match op {
            CmpOp::Eq => CmpOpExt::Eq,
            CmpOp::Ne => CmpOpExt::Ne,
            CmpOp::Ult => CmpOpExt::Ult,
            CmpOp::Ule => CmpOpExt::Ule,
            CmpOp::Slt => CmpOpExt::Slt,
            CmpOp::Sle => CmpOpExt::Sle,
        }
    }
}
