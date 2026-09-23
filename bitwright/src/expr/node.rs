//! The stored node representation.

use crate::ops::{BinOp, CmpOp, UnOp};

/// Every node kind. The discriminant is the operator rank used by the canonical operand order
/// (`OrderKey`), so the order of variants is part of the output-stability contract.
#[repr(u8)]
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) enum OpCode {
    Const = 0,
    Sym,
    Not,
    Neg,
    Popcnt,
    Clz,
    Ctz,
    Bswap,
    BitRev,
    Add,
    Sub,
    Mul,
    UMulHi,
    SMulHi,
    UDiv,
    URem,
    SDiv,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
    RotL,
    RotR,
    Pdep,
    Pext,
    Eq,
    Ne,
    Ult,
    Ule,
    Slt,
    Sle,
    Zext,
    Sext,
    Extract,
    Concat,
    Select,
    // Output `k` of an extension call on `n` arguments (`a`, `b`, `c`); `aux` is the operation's
    // index in the context's registry.
    Ext1o0,
    Ext1o1,
    Ext1o2,
    Ext1o3,
    Ext1o4,
    Ext1o5,
    Ext1o6,
    Ext1o7,
    Ext2o0,
    Ext2o1,
    Ext2o2,
    Ext2o3,
    Ext2o4,
    Ext2o5,
    Ext2o6,
    Ext2o7,
    Ext3o0,
    Ext3o1,
    Ext3o2,
    Ext3o3,
    Ext3o4,
    Ext3o5,
    Ext3o6,
    Ext3o7,
}

/// The extension opcodes, by `(arity - 1) * 8 + output`.
const EXT: [OpCode; 24] = [
    OpCode::Ext1o0,
    OpCode::Ext1o1,
    OpCode::Ext1o2,
    OpCode::Ext1o3,
    OpCode::Ext1o4,
    OpCode::Ext1o5,
    OpCode::Ext1o6,
    OpCode::Ext1o7,
    OpCode::Ext2o0,
    OpCode::Ext2o1,
    OpCode::Ext2o2,
    OpCode::Ext2o3,
    OpCode::Ext2o4,
    OpCode::Ext2o5,
    OpCode::Ext2o6,
    OpCode::Ext2o7,
    OpCode::Ext3o0,
    OpCode::Ext3o1,
    OpCode::Ext3o2,
    OpCode::Ext3o3,
    OpCode::Ext3o4,
    OpCode::Ext3o5,
    OpCode::Ext3o6,
    OpCode::Ext3o7,
];

impl OpCode {
    /// The opcode of output `output` (below 8) of an extension call on `arity` (1 to 3)
    /// arguments.
    pub(crate) const fn ext(arity: usize, output: usize) -> Option<OpCode> {
        if arity == 0 || arity > 3 || output >= 8 {
            return None;
        }
        Some(EXT[(arity - 1) * 8 + output])
    }

    /// The arity and output of an extension opcode.
    pub(crate) const fn as_ext(self) -> Option<(usize, usize)> {
        let (first, code) = (OpCode::Ext1o0 as u8, self as u8);
        if code < first {
            return None;
        }
        let i = (code - first) as usize;
        Some((i / 8 + 1, i % 8))
    }

    pub(crate) const fn from_un(op: UnOp) -> OpCode {
        match op {
            UnOp::Not => OpCode::Not,
            UnOp::Neg => OpCode::Neg,
            UnOp::Popcnt => OpCode::Popcnt,
            UnOp::Clz => OpCode::Clz,
            UnOp::Ctz => OpCode::Ctz,
            UnOp::Bswap => OpCode::Bswap,
            UnOp::BitRev => OpCode::BitRev,
        }
    }

    pub(crate) const fn from_bin(op: BinOp) -> OpCode {
        match op {
            BinOp::Add => OpCode::Add,
            BinOp::Sub => OpCode::Sub,
            BinOp::Mul => OpCode::Mul,
            BinOp::UMulHi => OpCode::UMulHi,
            BinOp::SMulHi => OpCode::SMulHi,
            BinOp::UDiv => OpCode::UDiv,
            BinOp::URem => OpCode::URem,
            BinOp::SDiv => OpCode::SDiv,
            BinOp::SRem => OpCode::SRem,
            BinOp::And => OpCode::And,
            BinOp::Or => OpCode::Or,
            BinOp::Xor => OpCode::Xor,
            BinOp::Shl => OpCode::Shl,
            BinOp::LShr => OpCode::LShr,
            BinOp::AShr => OpCode::AShr,
            BinOp::RotL => OpCode::RotL,
            BinOp::RotR => OpCode::RotR,
            BinOp::Pdep => OpCode::Pdep,
            BinOp::Pext => OpCode::Pext,
        }
    }

    pub(crate) const fn from_cmp(op: CmpOp) -> OpCode {
        match op {
            CmpOp::Eq => OpCode::Eq,
            CmpOp::Ne => OpCode::Ne,
            CmpOp::Ult => OpCode::Ult,
            CmpOp::Ule => OpCode::Ule,
            CmpOp::Slt => OpCode::Slt,
            CmpOp::Sle => OpCode::Sle,
        }
    }

    pub(crate) const fn as_un(self) -> Option<UnOp> {
        Some(match self {
            OpCode::Not => UnOp::Not,
            OpCode::Neg => UnOp::Neg,
            OpCode::Popcnt => UnOp::Popcnt,
            OpCode::Clz => UnOp::Clz,
            OpCode::Ctz => UnOp::Ctz,
            OpCode::Bswap => UnOp::Bswap,
            OpCode::BitRev => UnOp::BitRev,
            _ => return None,
        })
    }

    pub(crate) const fn as_bin(self) -> Option<BinOp> {
        Some(match self {
            OpCode::Add => BinOp::Add,
            OpCode::Sub => BinOp::Sub,
            OpCode::Mul => BinOp::Mul,
            OpCode::UMulHi => BinOp::UMulHi,
            OpCode::SMulHi => BinOp::SMulHi,
            OpCode::UDiv => BinOp::UDiv,
            OpCode::URem => BinOp::URem,
            OpCode::SDiv => BinOp::SDiv,
            OpCode::SRem => BinOp::SRem,
            OpCode::And => BinOp::And,
            OpCode::Or => BinOp::Or,
            OpCode::Xor => BinOp::Xor,
            OpCode::Shl => BinOp::Shl,
            OpCode::LShr => BinOp::LShr,
            OpCode::AShr => BinOp::AShr,
            OpCode::RotL => BinOp::RotL,
            OpCode::RotR => BinOp::RotR,
            OpCode::Pdep => BinOp::Pdep,
            OpCode::Pext => BinOp::Pext,
            _ => return None,
        })
    }

    pub(crate) const fn as_cmp(self) -> Option<CmpOp> {
        Some(match self {
            OpCode::Eq => CmpOp::Eq,
            OpCode::Ne => CmpOp::Ne,
            OpCode::Ult => CmpOp::Ult,
            OpCode::Ule => CmpOp::Ule,
            OpCode::Slt => CmpOp::Slt,
            OpCode::Sle => CmpOp::Sle,
            _ => return None,
        })
    }

    /// Number of child nodes.
    pub(crate) const fn arity(self) -> usize {
        match self {
            OpCode::Const | OpCode::Sym => 0,
            OpCode::Not
            | OpCode::Neg
            | OpCode::Popcnt
            | OpCode::Clz
            | OpCode::Ctz
            | OpCode::Bswap
            | OpCode::BitRev
            | OpCode::Zext
            | OpCode::Sext
            | OpCode::Extract => 1,
            OpCode::Select => 3,
            op => match op.as_ext() {
                Some((arity, _)) => arity,
                None => 2,
            },
        }
    }
}

/// One stored node: 16 bytes.
///
/// Field use by kind:
/// - `Const`: width <= 64: `a` = low 32 bits, `b` = high 32 bits; wider (`aux & AUX_POOLED`):
///   `a` = offset into the wide-constant pool.
/// - `Sym`: `a` = symbol index.
/// - unary, `Zext`, `Sext`: `a` = child (the node width is the target width).
/// - `Extract`: `a` = child, `b` = lo.
/// - binary, compare, `Concat`: `a`, `b` (`Concat`: `a` = high part).
/// - `Select`: `a` = condition, `b` = then, `c` = else.
/// - extension output: `a`, `b`, `c` = the arguments; `aux` = the operation's registry index.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) struct Node {
    pub(crate) op: OpCode,
    pub(crate) aux: u8,
    pub(crate) width: u16,
    pub(crate) a: u32,
    pub(crate) b: u32,
    pub(crate) c: u32,
}

pub(crate) const AUX_POOLED: u8 = 1;

const _: () = assert!(core::mem::size_of::<Node>() == 16);

impl Node {
    pub(crate) const fn new(op: OpCode, width: u16, a: u32, b: u32, c: u32) -> Node {
        Node {
            op,
            aux: 0,
            width,
            a,
            b,
            c,
        }
    }

    /// The child indices, in order.
    #[inline]
    pub(crate) fn children(&self) -> Children {
        let all = [self.a, self.b, self.c];
        Children {
            ids: all,
            len: self.op.arity() as u8,
            pos: 0,
        }
    }
}

/// Iterator over a node's child indices.
#[derive(Clone, Debug)]
pub(crate) struct Children {
    ids: [u32; 3],
    len: u8,
    pos: u8,
}

impl Iterator for Children {
    type Item = u32;
    #[inline]
    fn next(&mut self) -> Option<u32> {
        if self.pos < self.len {
            self.pos += 1;
            Some(self.ids[self.pos as usize - 1])
        } else {
            None
        }
    }
}
