//! `MbaExpr`: a small, self-contained DAG in the MBA fragment, the unit a solver sees.

use core::hash::{Hash, Hasher};

use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// An operator of the MBA fragment.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MOp {
    /// A constant.
    Const(BitVec),
    /// Variable `i` (an atom of the original expression).
    Var(u32),
    /// `a + b`.
    Add,
    /// `a - b`.
    Sub,
    /// `a * b`.
    Mul,
    /// `-a`.
    Neg,
    /// `a & b`.
    And,
    /// `a | b`.
    Or,
    /// `a ^ b`.
    Xor,
    /// `~a`.
    Not,
    /// `a << k` for a constant `k` below the width.
    Shl(u16),
    /// `a >>u k` for a constant `k` below the width.
    LShr(u16),
    /// Zero extension to the node's width.
    Zext,
    /// Sign extension to the node's width.
    Sext,
    /// The low bits of `a`, at the node's width.
    Trunc,
}

impl MOp {
    /// The number of operands.
    pub fn arity(&self) -> usize {
        match self {
            MOp::Const(_) | MOp::Var(_) => 0,
            MOp::Neg
            | MOp::Not
            | MOp::Shl(_)
            | MOp::LShr(_)
            | MOp::Zext
            | MOp::Sext
            | MOp::Trunc => 1,
            _ => 2,
        }
    }

    fn arith(&self) -> bool {
        matches!(self, MOp::Add | MOp::Sub | MOp::Mul | MOp::Neg)
    }

    fn bitwise(&self) -> bool {
        matches!(self, MOp::And | MOp::Or | MOp::Xor)
    }
}

/// A node: operator, result width, operand indices (earlier nodes).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct MNode {
    /// The operator.
    pub op: MOp,
    /// The result width.
    pub width: Width,
    /// Operand node indices (unused ones are 0).
    pub args: [u32; 2],
}

/// Why a node could not be added.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum MbaError {
    /// An operand index is not an earlier node.
    BadOperand,
    /// Operand widths do not fit the operator.
    Width,
    /// A variable index is not declared.
    UnknownVar,
}

impl core::fmt::Display for MbaError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            MbaError::BadOperand => "an operand is not an earlier node",
            MbaError::Width => "operand widths do not fit the operator",
            MbaError::UnknownVar => "unknown variable",
        })
    }
}

impl std::error::Error for MbaError {}

/// A DAG in the MBA fragment over declared variables. The last node is the root. Nodes refer
/// only to earlier nodes, so evaluation and every traversal are single forward passes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MbaExpr {
    vars: Vec<Width>,
    nodes: Vec<MNode>,
}

/// Structural properties used to decide whether a solver is worth asking.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Shape {
    /// Variables used.
    pub vars: u32,
    /// Nodes.
    pub nodes: u32,
    /// Longest operand chain.
    pub height: u32,
    /// Both arithmetic and bitwise operators occur.
    pub mixed: bool,
    /// The largest number of variables multiplied together in one product (1 for linear).
    pub degree: u32,
}

impl MbaExpr {
    /// An expression over variables of the given widths, with no nodes yet.
    pub fn new(vars: Vec<Width>) -> MbaExpr {
        MbaExpr {
            vars,
            nodes: Vec::new(),
        }
    }

    /// The variables' widths.
    pub fn vars(&self) -> &[Width] {
        &self.vars
    }

    /// The nodes, operands before users; the last is the root.
    pub fn nodes(&self) -> &[MNode] {
        &self.nodes
    }

    /// The root's index, if there are nodes.
    pub fn root(&self) -> Option<u32> {
        self.nodes.len().checked_sub(1).map(|r| r as u32)
    }

    /// The root's width.
    pub fn width(&self) -> Option<Width> {
        self.nodes.last().map(|n| n.width)
    }

    /// Adds a node whose width follows from its operands (every operator but the casts).
    pub fn push(&mut self, op: MOp, args: &[u32]) -> Result<u32, MbaError> {
        let w = match op {
            MOp::Const(v) => v.width(),
            MOp::Var(i) => *self.vars.get(i as usize).ok_or(MbaError::UnknownVar)?,
            MOp::Zext | MOp::Sext | MOp::Trunc => return Err(MbaError::Width),
            _ => {
                let a = self.arg(args, 0)?;
                if op.arity() == 2 && self.arg(args, 1)? != a {
                    return Err(MbaError::Width);
                }
                if let MOp::Shl(k) | MOp::LShr(k) = op
                    && k >= a.bits()
                {
                    return Err(MbaError::Width);
                }
                a
            }
        };
        self.add(op, w, args)
    }

    /// Adds a cast (`Zext`, `Sext`, `Trunc`) to `width`.
    pub fn push_cast(&mut self, op: MOp, a: u32, width: Width) -> Result<u32, MbaError> {
        let wa = self.arg(&[a], 0)?;
        let ok = match op {
            MOp::Zext | MOp::Sext => width > wa,
            MOp::Trunc => width < wa,
            _ => false,
        };
        if !ok {
            return Err(MbaError::Width);
        }
        self.add(op, width, &[a])
    }

    fn arg(&self, args: &[u32], k: usize) -> Result<Width, MbaError> {
        let i = *args.get(k).ok_or(MbaError::BadOperand)?;
        self.nodes
            .get(i as usize)
            .map(|n| n.width)
            .ok_or(MbaError::BadOperand)
    }

    fn add(&mut self, op: MOp, width: Width, args: &[u32]) -> Result<u32, MbaError> {
        let mut a = [0u32; 2];
        for (k, &x) in args.iter().take(op.arity()).enumerate() {
            if x as usize >= self.nodes.len() {
                return Err(MbaError::BadOperand);
            }
            a[k] = x;
        }
        self.nodes.push(MNode { op, width, args: a });
        Ok(self.nodes.len() as u32 - 1)
    }

    /// The root's value for the given variable values (`None` on a width mismatch).
    pub fn eval(&self, vals: &[BitVec]) -> Option<BitVec> {
        let mut v: Vec<BitVec> = Vec::with_capacity(self.nodes.len());
        for n in &self.nodes {
            let a = |k: usize| v[n.args[k] as usize];
            let r = match n.op {
                MOp::Const(c) => c,
                MOp::Var(i) => {
                    let x = *vals.get(i as usize)?;
                    if x.width() != n.width {
                        return None;
                    }
                    x
                }
                MOp::Add => BitVec::bin_unchecked(BinOp::Add, &a(0), &a(1)),
                MOp::Sub => BitVec::bin_unchecked(BinOp::Sub, &a(0), &a(1)),
                MOp::Mul => BitVec::bin_unchecked(BinOp::Mul, &a(0), &a(1)),
                MOp::And => BitVec::bin_unchecked(BinOp::And, &a(0), &a(1)),
                MOp::Or => BitVec::bin_unchecked(BinOp::Or, &a(0), &a(1)),
                MOp::Xor => BitVec::bin_unchecked(BinOp::Xor, &a(0), &a(1)),
                MOp::Neg => BitVec::un_unchecked(UnOp::Neg, &a(0)),
                MOp::Not => BitVec::un_unchecked(UnOp::Not, &a(0)),
                MOp::Shl(k) | MOp::LShr(k) => {
                    let kv = BitVec::wrapping_from_u64(n.width, u64::from(k));
                    let op = if matches!(n.op, MOp::Shl(_)) {
                        BinOp::Shl
                    } else {
                        BinOp::LShr
                    };
                    BitVec::bin_unchecked(op, &a(0), &kv)
                }
                MOp::Zext => a(0).zext(n.width).ok()?,
                MOp::Sext => a(0).sext(n.width).ok()?,
                MOp::Trunc => a(0).trunc(n.width).ok()?,
            };
            v.push(r);
        }
        v.last().copied()
    }

    /// A 128-bit content hash (variables, nodes), stable across processes.
    pub fn key(&self) -> [u64; 2] {
        struct H(u64, u64);
        impl Hasher for H {
            fn finish(&self) -> u64 {
                self.0
            }
            fn write(&mut self, bytes: &[u8]) {
                for &b in bytes {
                    self.0 = crate::hash::combine(self.0, u64::from(b));
                    self.1 = crate::hash::combine(self.1 ^ 0x5555, u64::from(b).rotate_left(29));
                }
            }
        }
        let mut h = H(0x6d62_615f_6578_7072, 0x6269_7477_7269_6768);
        self.hash(&mut h);
        [h.0, h.1]
    }

    /// Structural properties.
    pub fn shape(&self) -> Shape {
        let mut height = vec![0u32; self.nodes.len()];
        // Per node: the most variables multiplied together below it.
        let mut degree = vec![0u32; self.nodes.len()];
        let mut vars_used = vec![false; self.vars.len()];
        let (mut arith, mut bit) = (false, false);
        for (i, n) in self.nodes.iter().enumerate() {
            let kids = &n.args[..n.op.arity()];
            height[i] = kids
                .iter()
                .map(|&k| height[k as usize] + 1)
                .max()
                .unwrap_or(0);
            arith |= n.op.arith();
            bit |= n.op.bitwise();
            degree[i] = match n.op {
                MOp::Const(_) => 0,
                MOp::Var(v) => {
                    if let Some(u) = vars_used.get_mut(v as usize) {
                        *u = true;
                    }
                    1
                }
                MOp::Mul => degree[n.args[0] as usize] + degree[n.args[1] as usize],
                _ => kids.iter().map(|&k| degree[k as usize]).max().unwrap_or(0),
            };
        }
        Shape {
            vars: vars_used.iter().filter(|&&u| u).count() as u32,
            nodes: self.nodes.len() as u32,
            height: height.last().copied().unwrap_or(0),
            mixed: arith && bit,
            degree: degree.last().copied().unwrap_or(0),
        }
    }

    /// Whether this is a linear MBA: arithmetic over bitwise functions of the variables, with
    /// no multiplication of two non-constants, no shift or cast, and only 0 and all-ones
    /// constants inside bitwise parts. Such an expression is determined by its values at the
    /// corners where every variable is 0 or all-ones.
    pub fn is_linear(&self) -> bool {
        // Per node: 0 = constant, 1 = uniform (bitwise over variables, or 0/all-ones), 2 = linear.
        let mut class = vec![0u8; self.nodes.len()];
        let mut uniform_const = vec![false; self.nodes.len()];
        for (i, n) in self.nodes.iter().enumerate() {
            let c = |k: usize| class[n.args[k] as usize];
            let u = |k: usize| uniform_const[n.args[k] as usize];
            class[i] = match n.op {
                MOp::Const(v) => {
                    uniform_const[i] = v.is_zero() || v.is_ones();
                    0
                }
                MOp::Var(_) => 1,
                MOp::And | MOp::Or | MOp::Xor => {
                    // Bitwise of uniform parts (constants must be 0 or all-ones).
                    let ok = (0..2).all(|k| c(k) == 1 || (c(k) == 0 && u(k)));
                    if !ok {
                        return false;
                    }
                    1
                }
                MOp::Not => {
                    // `~c` of a constant is a constant (uniform only when `c` is); `~` of a
                    // bitwise function is one; `~` of a linear term is linear (`−t − 1`).
                    if c(0) == 0 {
                        uniform_const[i] = u(0);
                    }
                    c(0)
                }
                MOp::Add | MOp::Sub => {
                    if c(0) == 0 && c(1) == 0 {
                        0
                    } else {
                        2
                    }
                }
                MOp::Neg => c(0).max(if c(0) == 0 { 0 } else { 2 }),
                MOp::Mul => {
                    if c(0) != 0 && c(1) != 0 {
                        return false;
                    }
                    if c(0) == 0 && c(1) == 0 { 0 } else { 2 }
                }
                _ => return false,
            };
        }
        true
    }

    /// The values at the 2^t corners (variable `j` all-ones when bit `j` of the corner is set),
    /// or `None` over 16 variables or on a width mismatch between variables.
    pub(crate) fn corners(&self) -> Option<Vec<BitVec>> {
        let t = self.vars.len();
        if t > 16 {
            return None;
        }
        (0..1usize << t)
            .map(|p| {
                let vals: Vec<BitVec> = self
                    .vars
                    .iter()
                    .enumerate()
                    .map(|(j, &w)| {
                        if p >> j & 1 == 1 {
                            BitVec::ones(w)
                        } else {
                            BitVec::zero(w)
                        }
                    })
                    .collect();
                self.eval(&vals)
            })
            .collect()
    }
}
