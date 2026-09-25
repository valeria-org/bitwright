//! Refinement: the target may only do what the source may. For every input (a value or
//! poison) and every choice the target makes, some choice of the source must be undefined, or
//! the target defined and either the source poison or both equal and the target not poison:
//!
//! ```text
//! ∀ I, T.  valid_T → ∃ S.  valid_S ∧ (¬pre ∨ ub_S ∨ (¬ub_T ∧ (p_S ∨ (¬p_T ∧ v_T = v_S))))
//! ```
//!
//! decided by counterexample-guided search over the native prover: a candidate `(I, T)` that
//! defeats every source choice found so far, then a source choice that answers it (added to
//! the set) or a proof that none does (a counterexample).

use core::fmt;

use std::collections::HashMap;

use super::encode::{
    CONST_KEY, ChoiceKey, Choices, Enc, INPUT_KEY, Leaves, SKIP, SRC_CHOICE_KEY, Side,
    TGT_CHOICE_KEY,
};
use super::ir::{Lit, Node, NodeId, Op, Term, Transform, Ty};
use super::types::{Assignment, typing};
use super::value::ir_constant;
use crate::prove::{self, Model};
use crate::{BinOp, BitVec, CmpOpExt, Context, Error, Expr, FnEnv, SymbolKey, UnOp, Width};

/// How to verify.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct Config {
    /// The widths an open integer type takes.
    pub widths: Vec<u16>,
    /// The most type assignments checked.
    pub max_types: usize,
    /// The SAT solver's conflict budget per question.
    pub conflicts: u64,
    /// The most rounds of the search for source choices.
    pub rounds: usize,
    /// Simplify a counterexample (small values, no poison where possible).
    pub minimize: bool,
    /// The conflict budget of each question that simplifies a counterexample (an undecided
    /// one keeps the counterexample as it is).
    pub minimize_conflicts: u64,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            widths: vec![1, 2, 3, 4, 5, 6, 7, 8, 16, 32, 64],
            max_types: 32,
            conflicts: 200_000,
            rounds: 64,
            minimize: true,
            minimize_conflicts: 5_000,
        }
    }
}

setters!(Config {
    with_widths: widths: Vec<u16>,
    with_max_types: max_types: usize,
    with_conflicts: conflicts: u64,
    with_rounds: rounds: usize,
    with_minimize: minimize: bool,
    with_minimize_conflicts: minimize_conflicts: u64,
});

/// A value in a counterexample.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Shown {
    /// A value.
    Value(BitVec),
    /// Poison.
    Poison,
}

/// How the target fails to refine the source.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Mismatch {
    /// The target has undefined behavior where the source has none.
    TargetUb,
    /// The target is poison where the source is not.
    TargetPoison,
    /// The two values differ.
    Value,
}

/// Inputs where the target does something the source cannot.
#[derive(Clone, Debug)]
pub struct Counterexample {
    /// The types checked (`i8`, or each open type).
    pub types: String,
    /// The inputs.
    pub inputs: Vec<(String, Ty, Shown)>,
    /// The symbolic constants.
    pub consts: Vec<(String, Ty, BitVec)>,
    /// The source's named values (under its first choices).
    pub source: Vec<(String, Ty, Shown)>,
    /// The target's named values.
    pub target: Vec<(String, Ty, Shown)>,
    /// The source's result.
    pub source_result: Option<(Ty, Shown)>,
    /// The target's result.
    pub target_result: Option<(Ty, Shown)>,
    /// What goes wrong.
    pub mismatch: Mismatch,
    /// Whether the source makes choices (then the values shown are one execution of many,
    /// and none of them matches the target).
    pub nondeterministic: bool,
}

fn shown(ty: Ty, v: &Shown) -> String {
    match v {
        Shown::Value(b) => ir_constant(ty, b),
        Shown::Poison => format!("{ty} poison"),
    }
}

impl fmt::Display for Counterexample {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let what = match self.mismatch {
            Mismatch::TargetUb => "the target has undefined behavior where the source has none",
            Mismatch::TargetPoison => "the target is poison where the source is not",
            Mismatch::Value => "the values differ",
        };
        write!(f, "{what}")?;
        if !self.types.is_empty() {
            write!(f, " ({})", self.types)?;
        }
        writeln!(f)?;
        for (n, ty, v) in &self.inputs {
            writeln!(f, "  {n} = {}", shown(*ty, v))?;
        }
        for (n, ty, v) in &self.consts {
            writeln!(f, "  {n} = {}", ir_constant(*ty, v))?;
        }
        if !self.source.is_empty() {
            writeln!(f, "source:")?;
            for (n, ty, v) in &self.source {
                writeln!(f, "  {n} = {}", shown(*ty, v))?;
            }
        }
        if !self.target.is_empty() {
            writeln!(f, "target:")?;
            for (n, ty, v) in &self.target {
                writeln!(f, "  {n} = {}", shown(*ty, v))?;
            }
        }
        match (&self.source_result, &self.target_result, self.mismatch) {
            (_, _, Mismatch::TargetUb) => writeln!(f, "the target's undefined behavior")?,
            (Some((ts, s)), Some((tt, t)), _) => {
                writeln!(f, "source result: {}", shown(*ts, s))?;
                writeln!(f, "target result: {}", shown(*tt, t))?;
            }
            _ => {}
        }
        if self.nondeterministic {
            writeln!(
                f,
                "(the source's choices shown are one of its executions; none matches)"
            )?;
        }
        Ok(())
    }
}

/// The verdict at one type assignment, or overall.
#[derive(Clone, Debug)]
pub enum Verdict {
    /// The target refines the source.
    Valid,
    /// It does not.
    Invalid(Box<Counterexample>),
    /// Not decided within the budget: why.
    Unknown(String),
    /// Outside what bitwright models: why.
    Unsupported(String),
}

/// The checks of one transformation.
#[derive(Clone, Debug)]
pub struct Report {
    /// Its name.
    pub name: String,
    /// Per type assignment checked: its label and verdict.
    pub checks: Vec<(String, Verdict)>,
}

impl Report {
    /// The overall verdict: a counterexample if any assignment has one; else unsupported or
    /// unknown if any is; else valid (at every assignment checked).
    pub fn verdict(&self) -> Verdict {
        if let Some((_, v)) = self
            .checks
            .iter()
            .find(|(_, v)| matches!(v, Verdict::Invalid(_)))
        {
            return v.clone();
        }
        if let Some((_, v)) = self
            .checks
            .iter()
            .find(|(_, v)| matches!(v, Verdict::Unsupported(_)))
        {
            return v.clone();
        }
        if let Some((t, Verdict::Unknown(why))) = self
            .checks
            .iter()
            .find(|(_, v)| matches!(v, Verdict::Unknown(_)))
        {
            return Verdict::Unknown(if t.is_empty() {
                why.clone()
            } else {
                format!("{t}: {why}")
            });
        }
        if self.checks.is_empty() {
            return Verdict::Unsupported("no type assignment to check".into());
        }
        Verdict::Valid
    }
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let valid: Vec<&str> = self
            .checks
            .iter()
            .filter(|(_, v)| matches!(v, Verdict::Valid))
            .map(|(t, _)| t.as_str())
            .collect();
        match self.verdict() {
            Verdict::Valid => {
                write!(f, "valid        {}", self.name)?;
                if valid.iter().any(|t| !t.is_empty()) {
                    write!(f, "  ({})", valid.join("; "))?;
                }
                writeln!(f)
            }
            Verdict::Invalid(cx) => write!(f, "INVALID      {}\n{cx}", self.name),
            Verdict::Unknown(why) => writeln!(f, "unknown      {}  ({why})", self.name),
            Verdict::Unsupported(why) => writeln!(f, "unsupported  {}  ({why})", self.name),
        }
    }
}

/// Verifies that the target of `t` refines its source, at each type assignment in turn
/// (smallest first), stopping at the first counterexample.
pub fn verify(t: &Transform, cfg: &Config) -> Report {
    let mut report = Report {
        name: t.name.clone(),
        checks: Vec::new(),
    };
    if let Some(why) = undef_reuse(t) {
        report
            .checks
            .push((String::new(), Verdict::Unsupported(why)));
        return report;
    }
    let assignments = match typing(t).and_then(|ty| ty.assignments(t, &cfg.widths, cfg.max_types)) {
        Ok(a) => a,
        Err(e) => {
            report.checks.push((String::new(), Verdict::Unsupported(e)));
            return report;
        }
    };
    for a in &assignments {
        let v = match check(t, a, cfg) {
            Ok(v) => v,
            Err(Error::Unsupported(m)) if m.starts_with(SKIP) => continue,
            Err(Error::Unsupported(m)) => Verdict::Unsupported(m),
            Err(e) => Verdict::Unsupported(e.to_string()),
        };
        let stop = matches!(v, Verdict::Invalid(_) | Verdict::Unsupported(_));
        report.checks.push((a.label.clone(), v));
        if stop {
            break;
        }
    }
    report
}

/// A target value that depends on an `undef` without a `freeze` between may differ at each of
/// its uses in LLVM; bitwright gives it one value, so it refuses such a value used twice (or
/// branched on) in the target, where fewer behaviors would miss a bug.
fn undef_reuse(t: &Transform) -> Option<String> {
    let n = t.nodes.len();
    // The nodes the target evaluates: its instructions and what they read.
    let mut used = vec![0u32; n];
    let mut seen = vec![false; n];
    let mut stack: Vec<NodeId> = Vec::new();
    let mut branch_conds: Vec<NodeId> = Vec::new();
    for b in &t.tgt.blocks {
        stack.extend(b.insts.iter().copied());
        match &b.term {
            Term::Ret(Some(v)) => stack.push(*v),
            Term::Br(c, ..) | Term::Switch(c, ..) => {
                stack.push(*c);
                branch_conds.push(*c);
            }
            _ => {}
        }
    }
    if let Some(r) = t.tgt.root {
        stack.push(r);
    }
    while let Some(x) = stack.pop() {
        if std::mem::replace(&mut seen[x as usize], true) {
            continue;
        }
        let args: &[NodeId] = match t.node(x) {
            Node::Inst(i) => &i.args,
            Node::CExpr(_, a) | Node::Pred(_, a) => a,
            _ => &[],
        };
        for &a in args {
            used[a as usize] += 1;
            stack.push(a);
        }
    }
    let mut tainted = vec![false; n];
    for i in 0..n {
        // Arguments precede their users in the arena, except phis (which LLVM orders freely).
        tainted[i] = match t.node(i as NodeId) {
            Node::Lit(Lit::Undef) => true,
            Node::Inst(inst) if inst.op != Op::Freeze => inst
                .args
                .iter()
                .any(|&a| (a as usize) < i && tainted[a as usize]),
            _ => false,
        };
    }
    for i in 0..n {
        if seen[i] && tainted[i] && matches!(t.node(i as NodeId), Node::Inst(_)) && used[i] > 1 {
            return Some(format!(
                "{} depends on undef and is used more than once in the target (freeze it)",
                t.label(i as NodeId)
            ));
        }
    }
    for c in branch_conds {
        if tainted[c as usize] {
            return Some("a branch on a value that depends on undef".into());
        }
    }
    None
}

/// Symbolic inputs and constants.
fn symbolic_leaves(cx: &mut Context, t: &Transform, ty: &[Ty]) -> Result<Leaves, Error> {
    let mut inputs = Vec::new();
    for (i, &n) in t.inputs.iter().enumerate() {
        let width = Width::new(ty[n as usize].bits())?;
        let v = cx.symbol(SymbolKey::U64(INPUT_KEY + 2 * i as u64), width)?;
        let noundef = matches!(t.node(n), Node::Input { noundef: true, .. });
        let p = if noundef {
            cx.bool(false)?
        } else {
            cx.symbol(SymbolKey::U64(INPUT_KEY + 2 * i as u64 + 1), Width::W1)?
        };
        inputs.push((v, p));
    }
    let mut consts = Vec::new();
    for (i, &n) in t.consts.iter().enumerate() {
        let width = Width::new(ty[n as usize].bits())?;
        consts.push(cx.symbol(SymbolKey::U64(CONST_KEY + i as u64), width)?);
    }
    constrain_inputs(cx, t, ty, Leaves { inputs, consts })
}

/// Inputs with `range` and `nofpclass` attributes are poison outside them.
fn constrain_inputs(
    cx: &mut Context,
    t: &Transform,
    ty: &[Ty],
    mut leaves: Leaves,
) -> Result<Leaves, Error> {
    let empty = Leaves {
        inputs: Vec::new(),
        consts: Vec::new(),
    };
    for (i, &n) in t.inputs.iter().enumerate() {
        let range = match t.node(n) {
            Node::Input { range, .. } => range.clone(),
            _ => None,
        };
        let classes = t
            .nofpclass
            .iter()
            .filter(|(m, _)| *m == n)
            .fold(0u16, |a, (_, c)| a | c);
        if range.is_none() && classes == 0 {
            continue;
        }
        let (v, p) = leaves.inputs[i];
        let mut e = Enc::new(cx, t, ty, &empty, Choices::Fixed(&[]))?;
        let extra = e.constrained(ty[n as usize], v, range.as_ref(), classes)?;
        let p = cx.bin(BinOp::Or, p, extra)?;
        leaves.inputs[i] = (v, p);
    }
    Ok(leaves)
}

/// Concrete inputs and constants.
fn concrete_leaves(
    cx: &mut Context,
    t: &Transform,
    ty: &[Ty],
    pt: &Point,
) -> Result<Leaves, Error> {
    let mut inputs = Vec::new();
    for (v, p) in &pt.inputs {
        inputs.push((cx.constant(v)?, cx.bool(*p)?));
    }
    let mut consts = Vec::new();
    for v in &pt.consts {
        consts.push(cx.constant(v)?);
    }
    constrain_inputs(cx, t, ty, Leaves { inputs, consts })
}

/// A point of the input space with the target's choices.
#[derive(Clone, Debug)]
struct Point {
    inputs: Vec<(BitVec, bool)>,
    consts: Vec<BitVec>,
    tgt: Vec<BitVec>,
}

fn read(m: &Model, key: u64, width: Width) -> BitVec {
    m.iter()
        .find(|(k, _)| *k == SymbolKey::U64(key))
        .map_or_else(|| BitVec::zero(width), |(_, v)| *v)
}

fn point(m: &Model, t: &Transform, ty: &[Ty], tgt_choices: &[Width]) -> Result<Point, Error> {
    let mut inputs = Vec::new();
    for (i, &n) in t.inputs.iter().enumerate() {
        let width = Width::new(ty[n as usize].bits())?;
        let v = read(m, INPUT_KEY + 2 * i as u64, width);
        let p = !read(m, INPUT_KEY + 2 * i as u64 + 1, Width::W1).is_zero();
        let noundef = matches!(t.node(n), Node::Input { noundef: true, .. });
        inputs.push((v, p && !noundef));
    }
    let mut consts = Vec::new();
    for (i, &n) in t.consts.iter().enumerate() {
        let width = Width::new(ty[n as usize].bits())?;
        consts.push(read(m, CONST_KEY + i as u64, width));
    }
    let tgt = tgt_choices
        .iter()
        .enumerate()
        .map(|(k, &w)| read(m, TGT_CHOICE_KEY + k as u64, w))
        .collect();
    Ok(Point {
        inputs,
        consts,
        tgt,
    })
}

/// `φ`: the source (with its choices) answers the target at this point.
fn refines(cx: &mut Context, src: &Side, tgt: &Side) -> Result<Expr, Error> {
    let r = match (src.result, tgt.result) {
        (Some((vs, ps)), Some((vt, pt))) => {
            let eq = cx.cmp(CmpOpExt::Eq, vt, vs)?;
            let npt = cx.un(UnOp::Not, pt)?;
            let same = cx.bin(BinOp::And, npt, eq)?;
            cx.bin(BinOp::Or, ps, same)?
        }
        (None, None) => cx.bool(true)?,
        _ => {
            return Err(Error::Unsupported(
                "one side returns a value, the other not".into(),
            ));
        }
    };
    let nub = cx.un(UnOp::Not, tgt.ub)?;
    let defined = cx.bin(BinOp::And, nub, r)?;
    let ok = cx.bin(BinOp::Or, src.ub, defined)?;
    let npre = cx.un(UnOp::Not, src.pre)?;
    let ok = cx.bin(BinOp::Or, npre, ok)?;
    cx.bin(BinOp::And, src.valid, ok)
}

struct Search<'a> {
    cx: Context,
    t: &'a Transform,
    ty: &'a [Ty],
    leaves: Leaves,
    tgt: Side,
    base: Expr,
    src_choices: bool,
    rounds: usize,
    pcfg: prove::Config,
}

enum Found {
    None,
    Point(Point),
}

impl Search<'_> {
    fn new<'a>(t: &'a Transform, a: &'a Assignment, cfg: &Config) -> Result<Search<'a>, Error> {
        let mut cx = Context::new();
        let ty = &a.types[..];
        let leaves = symbolic_leaves(&mut cx, t, ty)?;
        let tgt = Enc::new(&mut cx, t, ty, &leaves, Choices::Symbols(TGT_CHOICE_KEY))?
            .body(&t.tgt, false)?;
        let src0 = Enc::new(&mut cx, t, ty, &leaves, Choices::Fixed(&[]))?.body(&t.src, true)?;
        let phi0 = refines(&mut cx, &src0, &tgt)?;
        let nphi = cx.un(UnOp::Not, phi0)?;
        let mut base = cx.bin(BinOp::And, tgt.valid, nphi)?;
        // The source copying the target's choices where both compute alike: where the programs
        // share code, the two sides become one expression.
        let mut mirror: HashMap<ChoiceKey, Expr> = HashMap::new();
        for &(k, e) in &tgt.keyed {
            if let Some(k) = k {
                mirror.entry(k).or_insert(e);
            }
        }
        if !src0.choices.is_empty() && !mirror.is_empty() {
            let src_m =
                Enc::new(&mut cx, t, ty, &leaves, Choices::Mirror(&mirror))?.body(&t.src, true)?;
            let phi_m = refines(&mut cx, &src_m, &tgt)?;
            let n = cx.un(UnOp::Not, phi_m)?;
            base = cx.bin(BinOp::And, base, n)?;
        }
        Ok(Search {
            cx,
            t,
            ty,
            leaves,
            tgt,
            base,
            src_choices: !src0.choices.is_empty(),
            rounds: cfg.rounds,
            pcfg: prove::Config::default().with_max_conflicts(cfg.conflicts),
        })
    }

    /// A point where no source choice answers the target, under `extra`.
    fn find(&mut self, extra: Expr) -> Result<Found, Error> {
        for _ in 0..=self.rounds {
            let q = self.cx.bin(BinOp::And, self.base, extra)?;
            let model = match prove::satisfy(&mut self.cx, q, &self.pcfg)? {
                Ok(None) => return Ok(Found::None),
                Ok(Some(m)) => m,
                Err(why) => return Err(Error::Unsupported(format!("unknown: {why}"))),
            };
            let pt = point(&model, self.t, self.ty, &self.tgt.choices)?;
            if !self.src_choices {
                return Ok(Found::Point(pt));
            }
            // A source choice that answers this point?
            let cl = concrete_leaves(&mut self.cx, self.t, self.ty, &pt)?;
            let tgt_c = Enc::new(&mut self.cx, self.t, self.ty, &cl, Choices::Fixed(&pt.tgt))?
                .body(&self.t.tgt, false)?;
            let src_s = Enc::new(
                &mut self.cx,
                self.t,
                self.ty,
                &cl,
                Choices::Symbols(SRC_CHOICE_KEY),
            )?
            .body(&self.t.src, true)?;
            let phi = refines(&mut self.cx, &src_s, &tgt_c)?;
            let answer = match prove::satisfy(&mut self.cx, phi, &self.pcfg)? {
                Ok(None) => return Ok(Found::Point(pt)),
                Ok(Some(m)) => m,
                Err(why) => return Err(Error::Unsupported(format!("unknown: {why}"))),
            };
            let s: Vec<BitVec> = src_s
                .choices
                .iter()
                .enumerate()
                .map(|(k, &w)| read(&answer, SRC_CHOICE_KEY + k as u64, w))
                .collect();
            let src_fixed = Enc::new(
                &mut self.cx,
                self.t,
                self.ty,
                &self.leaves,
                Choices::Fixed(&s),
            )?
            .body(&self.t.src, true)?;
            let phi_s = refines(&mut self.cx, &src_fixed, &self.tgt)?;
            let n = self.cx.un(UnOp::Not, phi_s)?;
            self.base = self.cx.bin(BinOp::And, self.base, n)?;
        }
        Err(Error::Unsupported(format!(
            "unknown: the source's choices needed more than {} rounds",
            self.rounds
        )))
    }

    fn input(&mut self, i: usize) -> Result<(Expr, Expr), Error> {
        Ok(self.leaves.inputs[i])
    }
}

/// Checks one type assignment.
fn check(t: &Transform, a: &Assignment, cfg: &Config) -> Result<Verdict, Error> {
    let mut s = Search::new(t, a, cfg)?;
    let tru = s.cx.bool(true)?;
    let mut pt = match s.find(tru) {
        Ok(Found::None) => return Ok(Verdict::Valid),
        Ok(Found::Point(p)) => p,
        Err(Error::Unsupported(m)) if m.starts_with("unknown: ") => {
            return Ok(Verdict::Unknown(m["unknown: ".len()..].to_string()));
        }
        Err(e) => return Err(e),
    };
    if cfg.minimize {
        s.pcfg = prove::Config::default().with_max_conflicts(cfg.minimize_conflicts);
        pt = minimize(&mut s, pt)?;
    }
    Ok(Verdict::Invalid(Box::new(describe(&mut s, a, &pt)?)))
}

/// Simpler counterexamples: inputs not poison where possible, then small values.
fn minimize(s: &mut Search<'_>, mut pt: Point) -> Result<Point, Error> {
    let mut extra = s.cx.bool(true)?;
    let mut budget = 48usize;
    let attempt =
        |s: &mut Search<'_>, extra: &mut Expr, c: Expr, pt: &mut Point| -> Result<bool, Error> {
            let q = s.cx.bin(BinOp::And, *extra, c)?;
            match s.find(q) {
                Ok(Found::Point(p)) => {
                    *extra = q;
                    *pt = p;
                    Ok(true)
                }
                Ok(Found::None) | Err(Error::Unsupported(_)) => Ok(false),
                Err(e) => Err(e),
            }
        };
    let n_inputs = s.t.inputs.len();
    // No poison inputs.
    for i in 0..n_inputs {
        if budget == 0 {
            break;
        }
        if pt.inputs[i].1 {
            budget -= 1;
            let (_, p) = s.input(i)?;
            let np = s.cx.un(UnOp::Not, p)?;
            attempt(s, &mut extra, np, &mut pt)?;
        }
    }
    // Small values: 0, 1, −1, then as few significant bits as possible.
    let targets: Vec<(Expr, Ty)> = (0..n_inputs)
        .map(|i| (s.leaves.inputs[i].0, s.ty[s.t.inputs[i] as usize]))
        .chain((0..s.t.consts.len()).map(|i| (s.leaves.consts[i], s.ty[s.t.consts[i] as usize])))
        .collect();
    for (k, &(v, ty)) in targets.iter().enumerate() {
        let current = if k < n_inputs {
            pt.inputs[k].0
        } else {
            pt.consts[k - n_inputs]
        };
        let width = Width::new(ty.bits())?;
        let mut candidates = vec![BitVec::zero(width), BitVec::one(width), BitVec::ones(width)];
        if let Ty::Float(f) = ty {
            let one = f.from_uint(crate::RoundingMode::Rne, &BitVec::one(Width::W8));
            let neg_one = crate::fp::FpFormat::neg(f, &one).unwrap_or(one);
            candidates = vec![f.zero(false), one, neg_one, f.inf(false), f.nan()];
        }
        let mut settled = false;
        for c in candidates {
            if budget == 0 || c == current {
                settled = c == current;
                if settled {
                    break;
                }
                continue;
            }
            budget -= 1;
            let cc = s.cx.constant(&c)?;
            let eq = s.cx.cmp(CmpOpExt::Eq, v, cc)?;
            if attempt(s, &mut extra, eq, &mut pt)? {
                settled = true;
                break;
            }
        }
        if settled || matches!(ty, Ty::Float(_)) || width.bits() <= 2 {
            continue;
        }
        // Binary search on the significant bits (a sign extension of the low k bits).
        let (mut lo, mut hi) = (1u16, width.bits());
        while lo < hi && budget > 0 {
            budget -= 1;
            let mid = (lo + hi) / 2;
            let low = s.cx.trunc(v, Width::new(mid)?)?;
            let ext = s.cx.sext(low, width)?;
            let eq = s.cx.cmp(CmpOpExt::Eq, v, ext)?;
            if attempt(s, &mut extra, eq, &mut pt)? {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
    }
    Ok(pt)
}

fn eval_one(cx: &mut Context, e: Expr) -> Result<BitVec, Error> {
    let env = FnEnv(|_: &SymbolKey, _| None);
    Ok(cx.eval(&[e], &env)?.remove(0))
}

fn shown_of(cx: &mut Context, v: Expr, p: Expr) -> Result<Shown, Error> {
    Ok(if eval_one(cx, p)?.is_zero() {
        Shown::Value(eval_one(cx, v)?)
    } else {
        Shown::Poison
    })
}

fn named_values(
    cx: &mut Context,
    t: &Transform,
    ty: &[Ty],
    side: &Side,
) -> Result<Vec<(String, Ty, Shown)>, Error> {
    let mut out = Vec::new();
    for &(n, v, p) in &side.values {
        let Node::Inst(inst) = t.node(n) else {
            continue;
        };
        if inst.name.is_empty() {
            continue;
        }
        out.push((
            format!("%{}", inst.name),
            ty[n as usize],
            shown_of(cx, v, p)?,
        ));
    }
    Ok(out)
}

fn result_type(body: &super::ir::Body, ty: &[Ty]) -> Option<Ty> {
    body.root.map(|r| ty[r as usize]).or_else(|| {
        body.blocks.iter().find_map(|b| match b.term {
            Term::Ret(Some(v)) => Some(ty[v as usize]),
            _ => None,
        })
    })
}

/// The values of each side at a point, for the report.
fn describe(s: &mut Search<'_>, a: &Assignment, pt: &Point) -> Result<Counterexample, Error> {
    let (t, ty) = (s.t, s.ty);
    let cx = &mut s.cx;
    let leaves = concrete_leaves(cx, t, ty, pt)?;
    let src = Enc::new(cx, t, ty, &leaves, Choices::Fixed(&[]))?.body(&t.src, true)?;
    let tgt = Enc::new(cx, t, ty, &leaves, Choices::Fixed(&pt.tgt))?.body(&t.tgt, false)?;
    let source = named_values(cx, t, ty, &src)?;
    let target = named_values(cx, t, ty, &tgt)?;
    let source_result = match (src.result, result_type(&t.src, ty)) {
        (Some((v, p)), Some(rt)) => Some((rt, shown_of(cx, v, p)?)),
        _ => None,
    };
    let target_result = match (tgt.result, result_type(&t.tgt, ty)) {
        (Some((v, p)), Some(rt)) => Some((rt, shown_of(cx, v, p)?)),
        _ => None,
    };
    let mismatch = if !eval_one(cx, tgt.ub)?.is_zero() {
        Mismatch::TargetUb
    } else if matches!(target_result, Some((_, Shown::Poison))) {
        Mismatch::TargetPoison
    } else {
        Mismatch::Value
    };
    let inputs = t
        .inputs
        .iter()
        .zip(&pt.inputs)
        .map(|(&n, (v, p))| {
            (
                t.label(n),
                ty[n as usize],
                if *p { Shown::Poison } else { Shown::Value(*v) },
            )
        })
        .collect();
    let consts = t
        .consts
        .iter()
        .zip(&pt.consts)
        .map(|(&n, v)| (t.label(n), ty[n as usize], *v))
        .collect();
    Ok(Counterexample {
        types: a.label.clone(),
        inputs,
        consts,
        source,
        target,
        source_result,
        target_result,
        mismatch,
        nondeterministic: s.src_choices,
    })
}

/// Whether a transformation is valid at fixed values of its symbolic constants, one type
/// assignment, many questions (sharing the search's source choices).
pub(crate) struct Probe<'a> {
    search: Search<'a>,
}

impl<'a> Probe<'a> {
    pub(crate) fn new(t: &'a Transform, a: &'a Assignment, cfg: &Config) -> Result<Self, Error> {
        Ok(Probe {
            search: Search::new(t, a, cfg)?,
        })
    }

    /// `Some(true)` when valid at these constants, `Some(false)` when not, `None` when not
    /// decided.
    pub(crate) fn valid_at(&mut self, consts: &[BitVec]) -> Result<Option<bool>, Error> {
        let s = &mut self.search;
        let mut extra = s.cx.bool(true)?;
        for (i, v) in consts.iter().enumerate() {
            let c = s.cx.constant(v)?;
            let eq = s.cx.cmp(CmpOpExt::Eq, s.leaves.consts[i], c)?;
            extra = s.cx.bin(BinOp::And, extra, eq)?;
        }
        match s.find(extra) {
            Ok(Found::None) => Ok(Some(true)),
            Ok(Found::Point(_)) => Ok(Some(false)),
            Err(Error::Unsupported(m)) if m.starts_with("unknown: ") => Ok(None),
            Err(e) => Err(e),
        }
    }
}
