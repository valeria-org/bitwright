//! The rule IR: the one representation shared by the compiler, the checker, the lints and the
//! engine. It is public and read-only; construct it with [`RuleProgram::compile`](super::RuleProgram::compile).

use core::fmt;

use crate::fp::{FpKind, RoundingMode};
use crate::ops::{BinOp, CmpOpExt, UnOp};

/// A linear expression over a rule's width variables: `konst + Σ coeff·var`.
#[derive(Clone, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub struct WExpr {
    /// The constant term.
    pub konst: i64,
    /// `(variable index, coefficient)`, sorted by variable, no zero coefficients.
    pub terms: Vec<(u8, i64)>,
}

impl WExpr {
    /// A constant.
    pub fn konst(k: i64) -> Self {
        WExpr {
            konst: k,
            terms: Vec::new(),
        }
    }

    /// One variable.
    pub fn var(v: u8) -> Self {
        WExpr {
            konst: 0,
            terms: vec![(v, 1)],
        }
    }

    /// Whether it has no variables.
    pub fn as_konst(&self) -> Option<i64> {
        self.terms.is_empty().then_some(self.konst)
    }

    /// The value under an assignment of the variables.
    pub fn eval(&self, vals: &[u16]) -> i64 {
        self.terms.iter().fold(self.konst, |acc, &(v, c)| {
            acc.saturating_add(c.saturating_mul(i64::from(vals[v as usize])))
        })
    }

    /// The largest magnitude of a constant or coefficient in a width expression. Bounded so
    /// that sums and products of the few terms a rule has never overflow.
    pub(crate) const LIMIT: i64 = 1 << 24;

    fn bounded(self) -> Option<WExpr> {
        let ok = |v: i64| (-Self::LIMIT..=Self::LIMIT).contains(&v);
        (ok(self.konst) && self.terms.iter().all(|&(_, c)| ok(c))).then_some(self)
    }

    /// `self + sign·o`, or `None` past [`WExpr::LIMIT`].
    pub(crate) fn add(&self, o: &WExpr, sign: i64) -> Option<WExpr> {
        let mut terms = self.terms.clone();
        for &(v, c) in &o.terms {
            let c = sign.checked_mul(c)?;
            match terms.iter_mut().find(|(x, _)| *x == v) {
                Some((_, k)) => *k = k.checked_add(c)?,
                None => terms.push((v, c)),
            }
        }
        terms.retain(|&(_, c)| c != 0);
        terms.sort_unstable();
        WExpr {
            konst: self.konst.checked_add(sign.checked_mul(o.konst)?)?,
            terms,
        }
        .bounded()
    }

    /// `k·self`, or `None` past [`WExpr::LIMIT`].
    pub(crate) fn scale(&self, k: i64) -> Option<WExpr> {
        let mut terms = Vec::with_capacity(self.terms.len());
        for &(v, c) in &self.terms {
            let c = c.checked_mul(k)?;
            if c != 0 {
                terms.push((v, c));
            }
        }
        WExpr {
            konst: self.konst.checked_mul(k)?,
            terms,
        }
        .bounded()
    }

    /// Renders with the given variable names.
    pub fn display<'a>(&'a self, names: &'a [String]) -> impl fmt::Display + 'a {
        WDisplay { e: self, names }
    }
}

struct WDisplay<'a> {
    e: &'a WExpr,
    names: &'a [String],
}

impl fmt::Display for WDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for &(v, c) in &self.e.terms {
            let name = self.names.get(v as usize).map_or("?", String::as_str);
            let sep = if first {
                if c < 0 { "-" } else { "" }
            } else if c < 0 {
                " - "
            } else {
                " + "
            };
            first = false;
            match c.abs() {
                1 => write!(f, "{sep}{name}")?,
                k => write!(f, "{sep}{k} * {name}")?,
            }
        }
        match (first, self.e.konst) {
            (true, k) => write!(f, "{k}"),
            (false, 0) => Ok(()),
            (false, k) if k < 0 => write!(f, " - {}", -k),
            (false, k) => write!(f, " + {k}"),
        }
    }
}

impl fmt::Debug for WExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names: Vec<String> = (0..8).map(|i| format!("w{i}")).collect();
        write!(f, "{}", self.display(&names))
    }
}

/// A comparison in a width constraint.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum WCmp {
    /// `==`
    Eq,
    /// `!=`
    Ne,
    /// `<`
    Lt,
    /// `<=`
    Le,
    /// `>`
    Gt,
    /// `>=`
    Ge,
}

/// A constraint on width variables (`where` clause).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum WCons {
    /// `a op b`
    Cmp(WExpr, WCmp, WExpr),
    /// `a % m == r`
    Mod(WExpr, u16, u16),
}

impl WCons {
    /// Whether the constraint holds under an assignment.
    pub fn holds(&self, vals: &[u16]) -> bool {
        match self {
            WCons::Cmp(a, op, b) => {
                let (x, y) = (a.eval(vals), b.eval(vals));
                match op {
                    WCmp::Eq => x == y,
                    WCmp::Ne => x != y,
                    WCmp::Lt => x < y,
                    WCmp::Le => x <= y,
                    WCmp::Gt => x > y,
                    WCmp::Ge => x >= y,
                }
            }
            WCons::Mod(a, m, r) => a.eval(vals).rem_euclid(i64::from(*m)) == i64::from(*r),
        }
    }
}

/// What a parameter may bind.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum ParamKind {
    /// Any expression.
    Any,
    /// Only a constant node.
    Const,
    /// Only a symbol node.
    Sym,
    /// Anything but a constant node.
    NonConst,
}

/// A rule parameter (a pattern variable).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub struct Param {
    /// Its name.
    pub name: String,
    /// What it may bind.
    pub kind: ParamKind,
    /// Its width.
    pub width: WExpr,
}

/// A literal in a pattern, template or guard. Its width comes from the node's sort.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum Literal {
    /// An unsigned magnitude (little-endian limbs), optionally negated.
    Int {
        /// Magnitude.
        limbs: Vec<u64>,
        /// Whether the literal is negated.
        negative: bool,
    },
    /// `ones`
    Ones,
    /// `smin_lit`: only the top bit set.
    SMin,
    /// `smax_lit`: every bit but the top set.
    SMax,
    /// `lowmask(N)`: the low `N` bits set.
    LowMask(WExpr),
    /// `bit(K)`: only bit `K` set.
    Bit(WExpr),
    /// A width expression used as a value (for example `W - 1`).
    Width(WExpr),
    /// A floating-point constant of the format with exponent width `eb` (and the literal's
    /// width), for example `fp.one<E, S>`.
    Float {
        /// Which constant.
        value: FloatLit,
        /// The format's exponent width.
        eb: WExpr,
    },
}

/// A floating-point constant a rule can name, in any format.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum FloatLit {
    /// `fp.zero`: +0.
    Zero,
    /// `fp.nzero`: −0.
    NegZero,
    /// `fp.inf`: +∞.
    Inf,
    /// `fp.ninf`: −∞.
    NegInf,
    /// `fp.nan`: the canonical NaN.
    Nan,
    /// `fp.one`: 1.
    One,
    /// `fp.none`: −1.
    NegOne,
    /// `fp.two`: 2.
    Two,
    /// `fp.half`: 1/2.
    Half,
    /// `fp.min_normal`: the smallest positive normal value.
    MinNormal,
    /// `fp.min_subnormal`: the smallest positive value.
    MinSubnormal,
    /// `fp.max_finite`: the largest finite value.
    MaxFinite,
}

/// The rounding mode of a floating-point node in a rule: a fixed one, or one of the rule's
/// rounding-mode variables ([`Rule::modes`]).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum Rounding {
    /// A fixed mode (`fp.add.rne`).
    Mode(RoundingMode),
    /// Rounding-mode variable `i` (`fp.add.r` with `r: rm`).
    Var(u8),
}

/// A floating-point operation in a rule: the node [`crate::Context::fp`] builds, with its
/// format as width expressions. Its result is the format's width (1 bit for a comparison, the
/// node's width for a conversion to an integer).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub struct FpNode {
    /// The operation.
    pub kind: FpKind,
    /// Its rounding mode, for the operations that round.
    pub rounding: Option<Rounding>,
    /// The exponent width of the floating-point operands' format (the result's, from an
    /// integer).
    pub eb: WExpr,
    /// Its significand width, the hidden bit included.
    pub sb: WExpr,
    /// A conversion's target format.
    pub to: Option<(WExpr, WExpr)>,
    /// The operands.
    pub args: Vec<NodeId>,
}

/// Guard predicates about facts. Each is true only when provable, so a guard that uses them
/// positively is monotone in fact precision.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum FactPred {
    /// `zero_bits(x, m)`: every bit of `m` is 0 in `x`.
    ZeroBits,
    /// `one_bits(x, m)`: every bit of `m` is 1 in `x`.
    OneBits,
    /// `nonzero(x)`
    NonZero,
    /// `disjoint(x, y)`: no bit is 1 in both.
    Disjoint,
    /// `proves(a op b)`: the comparison holds.
    Proves,
    /// `fp.not_nan(x)`: the float `x` is not a NaN. The second operand is the format's +∞
    /// (a [`Literal::Float`]), which names the format: `x & smax <=u ∞`.
    FpNotNan,
    /// `fp.finite(x)`: `x` is neither a NaN nor an infinity: `x & smax <u ∞`.
    FpFinite,
    /// `fp.nonzero(x)`: `x` is not a zero of either sign: `x & smax != 0`.
    FpNonZero,
}

/// Predicates on constants, decided exactly.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum ConstPred {
    /// A power of two.
    IsPow2,
    /// `2^k - 1` for some `k >= 1`.
    IsLowMask,
    /// One contiguous run of ones.
    IsShiftedMask,
}

/// Index of a node in a rule's arena.
pub type NodeId = u16;

/// One node of a rule's pattern, template, guard or `let` expression.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum RNode {
    /// A parameter.
    Param(u16),
    /// A `let` value.
    Let(u16),
    /// A literal.
    Lit(Literal),
    /// A unary operator.
    Un(UnOp, NodeId),
    /// A binary operator.
    Bin(BinOp, NodeId, NodeId),
    /// A comparison (1 bit).
    Cmp(CmpOpExt, NodeId, NodeId),
    /// Zero extension to the node's width.
    Zext(NodeId),
    /// Sign extension to the node's width.
    Sext(NodeId),
    /// Bits `[lo, lo + W)` of the operand.
    Extract(WExpr, NodeId),
    /// Concatenation (high, low).
    Concat(NodeId, NodeId),
    /// Selection (1-bit condition).
    Select(NodeId, NodeId, NodeId),
    /// Guard conjunction.
    And(NodeId, NodeId),
    /// Guard disjunction.
    Or(NodeId, NodeId),
    /// Guard negation (never over a fact predicate).
    Not(NodeId),
    /// A fact predicate (first argument is a parameter).
    Fact(FactPred, NodeId, Option<NodeId>),
    /// A constant predicate.
    ConstP(ConstPred, NodeId),
    /// A floating-point operation.
    Fp(FpNode),
}

/// The sort of a node: a bit-vector of a (symbolic) width, or a guard boolean.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum Sort {
    /// A bit-vector.
    Bv(WExpr),
    /// A guard boolean.
    Bool,
}

/// `rule` (directed, possibly conditional) or `identity` (unconditional equation).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub enum RuleKind {
    /// `rule … { lhs => rhs … }`
    Rewrite,
    /// `identity … { lhs <=> rhs }`
    Identity,
}

/// A content hash of a normalized rule (independent of names, positions and docs).
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RuleId(pub [u64; 2]);

impl fmt::Debug for RuleId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl fmt::Display for RuleId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}{:016x}", self.0[0], self.0[1])
    }
}

/// A `let` binding: a constant computed from constant parameters.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
#[non_exhaustive]
pub struct LetDef {
    /// Its name.
    pub name: String,
    /// Its value.
    pub value: NodeId,
}

/// A compiled rule.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct Rule {
    /// `group::name`.
    pub name: String,
    /// The group index in the program.
    pub group: usize,
    /// Rewrite or identity.
    pub kind: RuleKind,
    /// Content hash.
    pub id: RuleId,
    /// Width variable names.
    pub width_vars: Vec<String>,
    /// Rounding-mode variable names (parameters declared `r: rm`). An assignment of a rule's
    /// variables lists the widths, then each mode as its index in [`RoundingMode::ALL`].
    pub modes: Vec<String>,
    /// `where` constraints.
    pub constraints: Vec<WCons>,
    /// Parameters.
    pub params: Vec<Param>,
    /// `let` bindings, in evaluation order.
    pub lets: Vec<LetDef>,
    /// Node arena.
    pub nodes: Vec<RNode>,
    /// Sort of each node.
    pub sorts: Vec<Sort>,
    /// The pattern.
    pub lhs: NodeId,
    /// The template (identities: the right side).
    pub rhs: NodeId,
    /// The guard, if any.
    pub guard: Option<NodeId>,
    /// Whether the left-to-right direction strictly decreases the termination order.
    pub decreasing: bool,
    /// `#[example("input" => "output")]` attributes.
    pub examples: Vec<(String, String)>,
    /// Doc comment.
    pub doc: String,
    /// Byte span of the rule in its source.
    pub span: (usize, usize),
    /// [`Rule::admits`] at every width, for a rule with at most one width variable and no
    /// rounding-mode variable (bit `w`, bit 0 for no variable): computed with the compiler's
    /// validation, so the matcher answers it with one load.
    pub(crate) admitted_widths: Option<Box<[u64; 9]>>,
}

impl Rule {
    /// Whether the directed engine may use this rule (left to right).
    pub fn is_directed(&self) -> bool {
        self.decreasing
    }
    /// Whether the rule applies at this assignment of its width variables (in
    /// [`width_vars`](Rule::width_vars) order, then its [`modes`](Rule::modes), each as an
    /// index in [`RoundingMode::ALL`]): its `where` constraints hold and its pattern,
    /// template, guard and lets are well formed there (floating-point formats valid). The matcher, the checker and the SMT
    /// obligations all use this one test.
    pub fn admits(&self, widths: &[u16]) -> bool {
        super::eval::admitted(self, widths)
    }
}

/// A named group of rules; source order within a group is priority order.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct Group {
    /// The group's path, e.g. `core.bitwise`.
    pub name: String,
    /// Indices of its rules in the program.
    pub rules: Vec<usize>,
}
