//! The form both front ends parse into: the values of a source and a target program in one
//! arena, so the inputs and symbolic constants they share are the same nodes.

use crate::fp::FpFormat;

/// Index of a node in a transformation's arena.
pub type NodeId = u32;

/// A concrete type.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    /// An integer of this many bits (`i1` is a boolean).
    Int(u16),
    /// A floating-point format.
    Float(FpFormat),
}

impl Ty {
    /// The width of a value of the type.
    pub fn bits(self) -> u16 {
        match self {
            Ty::Int(w) => w,
            Ty::Float(f) => f.width().bits(),
        }
    }
}

impl core::fmt::Display for Ty {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Ty::Int(w) => write!(f, "i{w}"),
            Ty::Float(x) => f.write_str(float_name(x).unwrap_or("float?")),
        }
    }
}

/// The LLVM name of a floating-point format.
pub(crate) fn float_name(f: FpFormat) -> Option<&'static str> {
    Some(match (f.eb(), f.sb()) {
        (5, 11) => "half",
        (8, 8) => "bfloat",
        (8, 24) => "float",
        (11, 53) => "double",
        (15, 113) => "fp128",
        _ => return None,
    })
}

/// The format an LLVM floating-point type name stands for.
pub(crate) fn float_type(name: &str) -> Option<FpFormat> {
    Some(match name {
        "half" => FpFormat::F16,
        "bfloat" => FpFormat::BF16,
        "float" => FpFormat::F32,
        "double" => FpFormat::F64,
        "fp128" => FpFormat::F128,
        _ => return None,
    })
}

/// A literal, read against its type once types are known.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lit {
    /// A number as written: decimal or hexadecimal, with an optional `-`.
    Num(String),
    /// `true` or `false`.
    Bool(bool),
    /// `poison`.
    Poison,
    /// `undef`: a fresh arbitrary value at each use.
    Undef,
    /// `inf`, `-inf`.
    Inf(bool),
    /// `nan`: the preferred quiet NaN.
    Nan,
}

/// An integer comparison.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum IPred {
    Eq,
    Ne,
    Ugt,
    Uge,
    Ult,
    Ule,
    Sgt,
    Sge,
    Slt,
    Sle,
}

impl IPred {
    pub(crate) fn parse(s: &str) -> Option<IPred> {
        Some(match s {
            "eq" => IPred::Eq,
            "ne" => IPred::Ne,
            "ugt" => IPred::Ugt,
            "uge" => IPred::Uge,
            "ult" => IPred::Ult,
            "ule" => IPred::Ule,
            "sgt" => IPred::Sgt,
            "sge" => IPred::Sge,
            "slt" => IPred::Slt,
            "sle" => IPred::Sle,
            _ => return None,
        })
    }
}

/// A floating-point comparison.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum FPred {
    False,
    Oeq,
    Ogt,
    Oge,
    Olt,
    Ole,
    One,
    Ord,
    Ueq,
    Ugt,
    Uge,
    Ult,
    Ule,
    Une,
    Uno,
    True,
}

impl FPred {
    pub(crate) fn parse(s: &str) -> Option<FPred> {
        Some(match s {
            "false" => FPred::False,
            "oeq" => FPred::Oeq,
            "ogt" => FPred::Ogt,
            "oge" => FPred::Oge,
            "olt" => FPred::Olt,
            "ole" => FPred::Ole,
            "one" => FPred::One,
            "ord" => FPred::Ord,
            "ueq" => FPred::Ueq,
            "ugt" => FPred::Ugt,
            "uge" => FPred::Uge,
            "ult" => FPred::Ult,
            "ule" => FPred::Ule,
            "une" => FPred::Une,
            "uno" => FPred::Uno,
            "true" => FPred::True,
            _ => return None,
        })
    }
}

/// An intrinsic function (`call @llvm.<name>`).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Intrinsic {
    UMin,
    UMax,
    SMin,
    SMax,
    /// `abs(x, is_int_min_poison)`.
    Abs,
    Ctpop,
    /// `ctlz(x, is_zero_poison)`.
    Ctlz,
    /// `cttz(x, is_zero_poison)`.
    Cttz,
    Bswap,
    BitReverse,
    Fshl,
    Fshr,
    UAddSat,
    USubSat,
    SAddSat,
    SSubSat,
    Assume,
    FAbs,
    CopySign,
    Sqrt,
    Fma,
    FMulAdd,
    MinNum,
    MaxNum,
    Minimum,
    Maximum,
    MinimumNum,
    MaximumNum,
    Floor,
    Ceil,
    Trunc,
    Round,
    RoundEven,
    Rint,
    NearbyInt,
}

impl Intrinsic {
    /// The intrinsic of an `llvm.` name (its type suffixes ignored).
    pub(crate) fn parse(name: &str) -> Option<Intrinsic> {
        let base = name.strip_prefix("llvm.")?;
        // The longest known name that the base starts with, up to a `.` or the end.
        let known: &[(&str, Intrinsic)] = &[
            ("umin", Intrinsic::UMin),
            ("umax", Intrinsic::UMax),
            ("smin", Intrinsic::SMin),
            ("smax", Intrinsic::SMax),
            ("abs", Intrinsic::Abs),
            ("ctpop", Intrinsic::Ctpop),
            ("ctlz", Intrinsic::Ctlz),
            ("cttz", Intrinsic::Cttz),
            ("bswap", Intrinsic::Bswap),
            ("bitreverse", Intrinsic::BitReverse),
            ("fshl", Intrinsic::Fshl),
            ("fshr", Intrinsic::Fshr),
            ("uadd.sat", Intrinsic::UAddSat),
            ("usub.sat", Intrinsic::USubSat),
            ("sadd.sat", Intrinsic::SAddSat),
            ("ssub.sat", Intrinsic::SSubSat),
            ("assume", Intrinsic::Assume),
            ("fabs", Intrinsic::FAbs),
            ("copysign", Intrinsic::CopySign),
            ("sqrt", Intrinsic::Sqrt),
            ("fma", Intrinsic::Fma),
            ("fmuladd", Intrinsic::FMulAdd),
            ("minnum", Intrinsic::MinNum),
            ("maxnum", Intrinsic::MaxNum),
            ("minimum", Intrinsic::Minimum),
            ("maximum", Intrinsic::Maximum),
            ("minimumnum", Intrinsic::MinimumNum),
            ("maximumnum", Intrinsic::MaximumNum),
            ("floor", Intrinsic::Floor),
            ("ceil", Intrinsic::Ceil),
            ("trunc", Intrinsic::Trunc),
            ("round", Intrinsic::Round),
            ("roundeven", Intrinsic::RoundEven),
            ("rint", Intrinsic::Rint),
            ("nearbyint", Intrinsic::NearbyInt),
        ];
        known
            .iter()
            .filter(|(k, _)| {
                base == *k
                    || base
                        .strip_prefix(k)
                        .is_some_and(|rest| rest.starts_with('.'))
            })
            .max_by_key(|(k, _)| k.len())
            .map(|&(_, i)| i)
    }

    /// Whether it takes and returns floating-point values.
    pub(crate) fn is_float(self) -> bool {
        matches!(
            self,
            Intrinsic::FAbs
                | Intrinsic::CopySign
                | Intrinsic::Sqrt
                | Intrinsic::Fma
                | Intrinsic::FMulAdd
                | Intrinsic::MinNum
                | Intrinsic::MaxNum
                | Intrinsic::Minimum
                | Intrinsic::Maximum
                | Intrinsic::MinimumNum
                | Intrinsic::MaximumNum
                | Intrinsic::Floor
                | Intrinsic::Ceil
                | Intrinsic::Trunc
                | Intrinsic::Round
                | Intrinsic::RoundEven
                | Intrinsic::Rint
                | Intrinsic::NearbyInt
        )
    }

    /// Its number of operands, the flag operands of `abs`, `ctlz` and `cttz` included.
    pub(crate) fn arity(self) -> usize {
        match self {
            Intrinsic::Ctpop
            | Intrinsic::Bswap
            | Intrinsic::BitReverse
            | Intrinsic::Assume
            | Intrinsic::FAbs
            | Intrinsic::Sqrt
            | Intrinsic::Floor
            | Intrinsic::Ceil
            | Intrinsic::Trunc
            | Intrinsic::Round
            | Intrinsic::RoundEven
            | Intrinsic::Rint
            | Intrinsic::NearbyInt => 1,
            Intrinsic::Fshl | Intrinsic::Fshr | Intrinsic::Fma | Intrinsic::FMulAdd => 3,
            _ => 2,
        }
    }
}

/// An instruction's operation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum Op {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    Shl,
    LShr,
    AShr,
    And,
    Or,
    Xor,
    FAdd,
    FSub,
    FMul,
    FDiv,
    FRem,
    FNeg,
    ICmp(IPred),
    FCmp(FPred),
    Select,
    Freeze,
    Trunc,
    ZExt,
    SExt,
    FPTrunc,
    FPExt,
    FPToUI,
    FPToSI,
    UIToFP,
    SIToFP,
    BitCast,
    Phi,
    Call(Intrinsic),
    /// `%r = <operand>`: the operand itself (the transformation syntax).
    Copy,
    /// `load <ty>, ptr %p` (lifting only: the verifier refuses memory).
    Load,
    /// `store <ty> %v, ptr %p`.
    Store,
    /// `getelementptr <elem>, ptr %p, <ty> %i`: `p + i · size`, the element's size in bytes.
    Gep(u16),
    /// `alloca <ty>`: a fresh address.
    Alloca,
    /// `ptrtoint` and `inttoptr`: an address resized (zero extension or truncation).
    Resize,
}

impl Op {
    /// The binary operation named `s`.
    pub(crate) fn binary(s: &str) -> Option<Op> {
        Some(match s {
            "add" => Op::Add,
            "sub" => Op::Sub,
            "mul" => Op::Mul,
            "udiv" => Op::UDiv,
            "sdiv" => Op::SDiv,
            "urem" => Op::URem,
            "srem" => Op::SRem,
            "shl" => Op::Shl,
            "lshr" => Op::LShr,
            "ashr" => Op::AShr,
            "and" => Op::And,
            "or" => Op::Or,
            "xor" => Op::Xor,
            "fadd" => Op::FAdd,
            "fsub" => Op::FSub,
            "fmul" => Op::FMul,
            "fdiv" => Op::FDiv,
            "frem" => Op::FRem,
            _ => return None,
        })
    }

    /// The conversion named `s`.
    pub(crate) fn cast(s: &str) -> Option<Op> {
        Some(match s {
            "trunc" => Op::Trunc,
            "zext" => Op::ZExt,
            "sext" => Op::SExt,
            "fptrunc" => Op::FPTrunc,
            "fpext" => Op::FPExt,
            "fptoui" => Op::FPToUI,
            "fptosi" => Op::FPToSI,
            "uitofp" => Op::UIToFP,
            "sitofp" => Op::SIToFP,
            "bitcast" => Op::BitCast,
            _ => return None,
        })
    }
}

/// Instruction flags (poison-generating and fast-math).
pub mod flags {
    /// `nsw`
    pub const NSW: u16 = 1;
    /// `nuw`
    pub const NUW: u16 = 1 << 1;
    /// `exact`
    pub const EXACT: u16 = 1 << 2;
    /// `disjoint`
    pub const DISJOINT: u16 = 1 << 3;
    /// `nneg`
    pub const NNEG: u16 = 1 << 4;
    /// `samesign`
    pub const SAMESIGN: u16 = 1 << 5;
    /// `nnan`
    pub const NNAN: u16 = 1 << 6;
    /// `ninf`
    pub const NINF: u16 = 1 << 7;
    /// `nsz`
    pub const NSZ: u16 = 1 << 8;
    /// `arcp`
    pub const ARCP: u16 = 1 << 9;
    /// `contract`
    pub const CONTRACT: u16 = 1 << 10;
    /// `afn`
    pub const AFN: u16 = 1 << 11;
    /// `reassoc`
    pub const REASSOC: u16 = 1 << 12;
    /// The rewrite-based fast-math flags, which change which rewrites are allowed rather than
    /// what an instruction computes.
    pub const REWRITE: u16 = ARCP | CONTRACT | AFN | REASSOC;

    /// The flag a keyword names (`fast` is every fast-math flag).
    pub fn parse(s: &str) -> Option<u16> {
        Some(match s {
            "nsw" => NSW,
            "nuw" => NUW,
            "exact" => EXACT,
            "disjoint" => DISJOINT,
            "nneg" => NNEG,
            "samesign" => SAMESIGN,
            "nnan" => NNAN,
            "ninf" => NINF,
            "nsz" => NSZ,
            "arcp" => ARCP,
            "contract" => CONTRACT,
            "afn" => AFN,
            "reassoc" => REASSOC,
            "fast" => NNAN | NINF | NSZ | ARCP | CONTRACT | AFN | REASSOC,
            _ => return None,
        })
    }
}

/// An instruction.
#[derive(Clone, Debug)]
pub struct Inst {
    /// Its register name (without `%`), empty for an unnamed one (a void call).
    pub name: String,
    /// The operation.
    pub op: Op,
    /// Flags ([`flags`]).
    pub flags: u16,
    /// Operands.
    pub args: Vec<NodeId>,
    /// For a `phi`, the block each operand comes from (indices in the body).
    pub incoming: Vec<usize>,
}

/// A function in a constant expression or a precondition, or an operator of either.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum CFun {
    // Operators.
    Neg,
    Not,
    Add,
    Sub,
    Mul,
    SDiv,
    UDiv,
    SRem,
    URem,
    Shl,
    AShr,
    LShr,
    And,
    Or,
    Xor,
    // Functions.
    Abs,
    Log2,
    Width,
    Trunc,
    ZExt,
    SExt,
    UMax,
    UMin,
    SMax,
    SMin,
    Clz,
    Ctz,
    Popcount,
}

/// A predicate of a precondition.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[allow(missing_docs)]
pub enum PFun {
    And,
    Or,
    Not,
    Cmp(IPred),
    True,
    IsPowerOf2,
    IsPowerOf2OrZero,
    IsSignBit,
    IsShiftedMask,
    IsMask,
    MaskedValueIsZero,
    WillNotOverflowSignedAdd,
    WillNotOverflowUnsignedAdd,
    WillNotOverflowSignedSub,
    WillNotOverflowUnsignedSub,
    WillNotOverflowSignedMul,
    WillNotOverflowUnsignedMul,
    WillNotOverflowUnsignedShl,
    WillNotOverflowSignedShl,
}

impl PFun {
    /// The predicate function `s` names, with its arity.
    pub(crate) fn function(s: &str) -> Option<(PFun, usize)> {
        Some(match s {
            "isPowerOf2" => (PFun::IsPowerOf2, 1),
            "isPowerOf2OrZero" => (PFun::IsPowerOf2OrZero, 1),
            "isSignBit" => (PFun::IsSignBit, 1),
            "isShiftedMask" => (PFun::IsShiftedMask, 1),
            "isMask" => (PFun::IsMask, 1),
            "MaskedValueIsZero" => (PFun::MaskedValueIsZero, 2),
            "WillNotOverflowSignedAdd" => (PFun::WillNotOverflowSignedAdd, 2),
            "WillNotOverflowUnsignedAdd" => (PFun::WillNotOverflowUnsignedAdd, 2),
            "WillNotOverflowSignedSub" => (PFun::WillNotOverflowSignedSub, 2),
            "WillNotOverflowUnsignedSub" => (PFun::WillNotOverflowUnsignedSub, 2),
            "WillNotOverflowSignedMul" => (PFun::WillNotOverflowSignedMul, 2),
            "WillNotOverflowUnsignedMul" => (PFun::WillNotOverflowUnsignedMul, 2),
            "WillNotOverflowUnsignedShl" => (PFun::WillNotOverflowUnsignedShl, 2),
            "WillNotOverflowSignedShl" => (PFun::WillNotOverflowSignedShl, 2),
            // Facts about uses, which every value satisfies for correctness.
            "hasOneUse" | "isConstant" => (PFun::True, 1),
            _ => return None,
        })
    }
}

/// One node of the arena.
#[derive(Clone, Debug)]
pub enum Node {
    /// An input (a register the source reads without defining it, or a function parameter).
    Input {
        /// Its name (without `%`).
        name: String,
        /// `noundef`: it is never poison (passing poison is the caller's undefined behavior).
        noundef: bool,
        /// A `range(ty lo, hi)` attribute: outside `[lo, hi)`, wrapping, it is poison.
        range: Option<(String, String)>,
    },
    /// A symbolic constant (`C`, `C1`): some value, the same in source and target, never
    /// poison.
    Sym(String),
    /// A literal.
    Lit(Lit),
    /// A constant expression.
    CExpr(CFun, Vec<NodeId>),
    /// A predicate of the precondition (a boolean, not a value).
    Pred(PFun, Vec<NodeId>),
    /// An instruction.
    Inst(Inst),
}

/// A basic block's terminator.
#[derive(Clone, Debug)]
pub enum Term {
    /// None: a transformation's single block, whose result is its root.
    None,
    /// `ret` (a value, or `void`).
    Ret(Option<NodeId>),
    /// A conditional branch: condition, then, else.
    Br(NodeId, usize, usize),
    /// An unconditional branch.
    Jmp(usize),
    /// `switch`: condition, default, cases (a literal node and a block).
    Switch(NodeId, usize, Vec<(NodeId, usize)>),
    /// `unreachable`.
    Unreachable,
}

/// A basic block.
#[derive(Clone, Debug)]
pub struct Block {
    /// Its label.
    pub name: String,
    /// Its instructions, in order.
    pub insts: Vec<NodeId>,
    /// Its terminator.
    pub term: Term,
}

/// A program: the source or the target.
#[derive(Clone, Debug, Default)]
pub struct Body {
    /// Its blocks; the first is the entry.
    pub blocks: Vec<Block>,
    /// A transformation's root: the instruction whose value the target must refine.
    pub root: Option<NodeId>,
    /// `noundef` on the return value: returning poison is undefined behavior.
    pub ret_noundef: bool,
    /// `range(ty lo, hi)` on the return value: outside it, the value is poison.
    pub ret_range: Option<(String, String)>,
    /// `nofpclass(…)` on the return value: in those classes, the value is poison.
    pub ret_nofpclass: u16,
    /// Whether the program returns a value (a function returning `void` does not).
    pub returns_value: bool,
}

/// A transformation to verify: a source, a target that should refine it, a precondition.
#[derive(Clone, Debug)]
pub struct Transform {
    /// Its name (`Name:`, or the function's).
    pub name: String,
    /// The node arena.
    pub nodes: Vec<Node>,
    /// A type annotation per node.
    pub types: Vec<Option<Ty>>,
    /// The inputs, in order.
    pub inputs: Vec<NodeId>,
    /// The symbolic constants, in order.
    pub consts: Vec<NodeId>,
    /// The precondition (`Pre:`).
    pub pre: Option<NodeId>,
    /// The source.
    pub src: Body,
    /// The target.
    pub tgt: Body,
    /// `nofpclass(…)` of inputs: in those classes, the input is poison.
    pub nofpclass: Vec<(NodeId, u16)>,
}

impl Transform {
    pub(crate) fn new(name: String) -> Self {
        Transform {
            name,
            nodes: Vec::new(),
            types: Vec::new(),
            inputs: Vec::new(),
            consts: Vec::new(),
            pre: None,
            src: Body::default(),
            tgt: Body::default(),
            nofpclass: Vec::new(),
        }
    }

    pub(crate) fn push(&mut self, n: Node, ty: Option<Ty>) -> NodeId {
        self.nodes.push(n);
        self.types.push(ty);
        (self.nodes.len() - 1) as NodeId
    }

    /// A node.
    pub fn node(&self, n: NodeId) -> &Node {
        &self.nodes[n as usize]
    }

    /// The display name of a node: `%name` for registers and inputs, the constant's name.
    pub fn label(&self, n: NodeId) -> String {
        match self.node(n) {
            Node::Input { name, .. } => format!("%{name}"),
            Node::Sym(s) => s.clone(),
            Node::Inst(i) if !i.name.is_empty() => format!("%{}", i.name),
            _ => format!("#{n}"),
        }
    }
}
