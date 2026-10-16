//! Refinement: the target may only do what the source may. For every input (a value or
//! poison) and every choice the target makes, some choice of the source must be undefined, or
//! the target defined and either the source poison or both equal and the target not poison:
//!
//! ```text
//! ∀ I, T.  valid_T → ∃ S.  valid_S ∧ (¬pre ∨ ub_S ∨ (¬ub_T ∧ (p_S ∨ (¬p_T ∧ v_T = v_S))))
//! ```
//!
//! (with every register the target defines again refined as the result is), decided by
//! counterexample-guided search over the native prover: a candidate `(I, T)` that defeats
//! every source choice found so far, then a source choice that answers it (added to the set)
//! or a proof that none does (a counterexample). Each program reads the inputs through its own
//! attributes; the inputs themselves are what a caller passes.

use core::fmt;

use std::borrow::Cow;
use std::collections::HashMap;

use super::encode::{
    CONST_KEY, ChoiceKey, Choices, Enc, INPUT_KEY, Leaves, SKIP, SRC_CHOICE_KEY, Side,
    TGT_CHOICE_KEY,
};
use super::ir::{Lit, Node, NodeId, Op, Term, Transform, Ty};
use super::lex::SyntaxError;
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
    /// The most type assignments checked. A transformation with more is not decided (it is
    /// never valid on the ones checked alone): give some types, or raise this.
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
    /// Accept each proof only with a DRUP certificate that the independent checker verifies,
    /// every question blasted as it is (without bitwright's simplifier). The encoding of
    /// LLVM's semantics and the bit-blaster stay trusted; the SAT solver and the simplifier no
    /// longer are. Slower, and a check that fails is an unknown verdict.
    pub certify: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            widths: vec![1, 2, 3, 4, 5, 6, 7, 8, 16, 32, 64],
            max_types: 128,
            conflicts: 200_000,
            rounds: 64,
            minimize: true,
            minimize_conflicts: 5_000,
            certify: false,
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
    with_certify: certify: bool,
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
    /// The inputs, as a caller passes them.
    pub inputs: Vec<(String, Ty, Shown)>,
    /// The symbolic constants.
    pub consts: Vec<(String, Ty, BitVec)>,
    /// The source's named values (under its first choices).
    pub source: Vec<(String, Ty, Shown)>,
    /// The target's named values.
    pub target: Vec<(String, Ty, Shown)>,
    /// The source's result (or the register of [`output`](Self::output)).
    pub source_result: Option<(Ty, Shown)>,
    /// The target's result (or the register of [`output`](Self::output)).
    pub target_result: Option<(Ty, Shown)>,
    /// What goes wrong.
    pub mismatch: Mismatch,
    /// The register the target defines again whose value fails, when it is not the result.
    pub output: Option<String>,
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
        let what = match (self.mismatch, &self.output) {
            (Mismatch::TargetUb, _) => {
                "the target has undefined behavior where the source has none".to_string()
            }
            (Mismatch::TargetPoison, None) => "the target is poison where the source is not".into(),
            (Mismatch::Value, None) => "the values differ".into(),
            (Mismatch::TargetPoison, Some(r)) => {
                format!("the target's {r} is poison where the source's is not")
            }
            (Mismatch::Value, Some(r)) => format!("the values of {r} differ"),
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
        let which = self.output.as_deref().unwrap_or("result");
        match (&self.source_result, &self.target_result, self.mismatch) {
            (_, _, Mismatch::TargetUb) => writeln!(f, "the target's undefined behavior")?,
            (Some((ts, s)), Some((tt, t)), _) => {
                writeln!(f, "source {which}: {}", shown(*ts, s))?;
                writeln!(f, "target {which}: {}", shown(*tt, t))?;
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
    /// Type assignments left unchecked because there were more than
    /// [`Config::max_types`]: then the transformation is not valid, only not refuted.
    pub unchecked: usize,
}

impl Report {
    /// The overall verdict: a counterexample if any assignment has one; else unsupported or
    /// unknown if any is, or if assignments were left unchecked; else valid (at every
    /// assignment of the widths configured).
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
        if self.unchecked > 0 {
            let done = self.checks.len();
            return Verdict::Unknown(format!(
                "valid at the {done} type assignments checked of {}; give some types, or raise \
                 the most checked (max_types, --max-types)",
                done + self.unchecked
            ));
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
        unchecked: 0,
    };
    let (t, assignments, total) = match prepare(t, cfg) {
        Ok(p) => p,
        Err(why) => {
            report
                .checks
                .push((String::new(), Verdict::Unsupported(why)));
            return report;
        }
    };
    for a in &assignments {
        let v = match check(&t, a, cfg) {
            Ok(v) => v,
            // A meaningless assignment (`bswap` of an odd number of bytes) is passed over.
            Err(Error::Unsupported(m)) if m.starts_with(SKIP) => continue,
            Err(Error::Unsupported(m)) => Verdict::Unsupported(m),
            Err(e) => Verdict::Unsupported(e.to_string()),
        };
        let stop = matches!(v, Verdict::Invalid(_) | Verdict::Unsupported(_));
        report.checks.push((a.label.clone(), v));
        if stop {
            return report;
        }
    }
    report.unchecked = total.saturating_sub(assignments.len());
    report
}

/// Translation validation of two modules (see [`pairs_each`](super::pairs_each)): a report
/// per function pair, one the subset cannot read reported unsupported with its error, so
/// that the others are still checked. The error is the module's.
pub fn validate(
    first: &str,
    second: Option<&str>,
    cfg: &Config,
) -> Result<Vec<Report>, SyntaxError> {
    Ok(super::pairs_each(first, second)?
        .into_iter()
        .map(|(name, t)| match t {
            Ok(t) => verify(&t, cfg),
            Err(e) => Report {
                name,
                checks: vec![(String::new(), Verdict::Unsupported(e.to_string()))],
                unchecked: 0,
            },
        })
        .collect())
}

/// What the verifier checks: the transformation with the source's attributes on its body,
/// and its type assignments (at most [`Config::max_types`], with how many there are); or why
/// it cannot be verified.
fn prepare<'t>(
    t: &'t Transform,
    cfg: &Config,
) -> Result<(Cow<'t, Transform>, Vec<Assignment>, usize), String> {
    if let Some(why) = refusal(t) {
        return Err(why);
    }
    if let Some(why) = undef_reuse(t) {
        return Err(why);
    }
    // A transformation built with the source's attributes on its inputs only: on the body.
    let t = if t.src.params.len() != t.inputs.len()
        && (0..t.inputs.len()).any(|i| !t.source_attrs(i).is_empty())
    {
        let mut owned = t.clone();
        owned.src.params = (0..t.inputs.len()).map(|i| t.source_attrs(i)).collect();
        Cow::Owned(owned)
    } else {
        Cow::Borrowed(t)
    };
    let (assignments, total) = typing(&t)?.assignments(&t, &cfg.widths, cfg.max_types)?;
    if let Some(why) = &t.float_env
        && assignments
            .iter()
            .any(|a| a.types.iter().any(|ty| matches!(ty, Ty::Float(_))))
    {
        return Err(why.clone());
    }
    Ok((t, assignments, total))
}

/// Why the verifier cannot check `t` at all: pointers, or something it reads without modeling
/// (the source may declare more than is modeled, which only makes it more defined; the target
/// may not).
fn refusal(t: &Transform) -> Option<String> {
    if t.pointers {
        return Some(
            "pointers and memory (`ptr`, `getelementptr`, `alloca`, `load`, …) are outside the \
             subset the verifier reads"
                .into(),
        );
    }
    if let Some(why) = t.unsupported.first() {
        return Some(why.clone());
    }
    let reach = target_reach(t);
    for (i, &seen) in reach.seen.iter().enumerate() {
        if !seen {
            continue;
        }
        if let Node::Inst(inst) = t.node(i as NodeId)
            && let Some(a) = &inst.attrs
            && let Some(u) = a.unmodeled.first()
        {
            let what = if inst.name.is_empty() {
                format!("a call to {:?}", inst.op)
            } else {
                t.label(i as NodeId)
            };
            return Some(format!(
                "{what} in the target has {u}, which bitwright does not model"
            ));
        }
    }
    None
}

/// The nodes the target evaluates (its instructions, what they read, its branch conditions
/// and results), how many times each is read, and its branch conditions.
struct Reach {
    seen: Vec<bool>,
    used: Vec<u32>,
    branch_conds: Vec<NodeId>,
}

fn target_reach(t: &Transform) -> Reach {
    let n = t.nodes.len();
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
    stack.extend(t.tgt.root);
    stack.extend(t.tgt.matched.iter().map(|&(_, n)| n));
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
    Reach {
        seen,
        used,
        branch_conds,
    }
}

/// A target value that depends on an `undef` without a `freeze` between may differ at each of
/// its uses in LLVM; bitwright gives it one value, so it refuses such a value used twice (or
/// branched on) in the target, where fewer behaviors would miss a bug.
fn undef_reuse(t: &Transform) -> Option<String> {
    let n = t.nodes.len();
    let reach = target_reach(t);
    // What depends on an undef, to a fixed point: operands may come after their users in
    // the arena (the function syntax names every register before reading any instruction).
    let mut tainted = vec![false; n];
    loop {
        let mut changed = false;
        for i in 0..n {
            if tainted[i] {
                continue;
            }
            let depends = match t.node(i as NodeId) {
                Node::Lit(Lit::Undef) => true,
                Node::Inst(inst) if inst.op != Op::Freeze => {
                    inst.args.iter().any(|&a| tainted[a as usize])
                }
                Node::CExpr(_, args) => args.iter().any(|&a| tainted[a as usize]),
                _ => false,
            };
            if depends {
                tainted[i] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let reused = (0..n as NodeId).find(|&i| {
        let k = i as usize;
        reach.seen[k] && tainted[k] && matches!(t.node(i), Node::Inst(_)) && reach.used[k] > 1
    });
    if let Some(i) = reused {
        return Some(format!(
            "{} depends on undef and is used more than once in the target (freeze it)",
            t.label(i)
        ));
    }
    for c in reach.branch_conds {
        if tainted[c as usize] {
            return Some("a branch on a value that depends on undef".into());
        }
    }
    None
}

/// Symbolic inputs (as a caller passes them: never poison where the source declares
/// `noundef`, since passing poison there is the source's undefined behavior) and constants.
fn symbolic_leaves(cx: &mut Context, t: &Transform, ty: &[Ty]) -> Result<Leaves, Error> {
    let mut inputs = Vec::new();
    for (i, &n) in t.inputs.iter().enumerate() {
        let width = Width::new(ty[n as usize].bits())?;
        let v = cx.symbol(SymbolKey::U64(INPUT_KEY + 2 * i as u64), width)?;
        let p = if t.source_attrs(i).noundef {
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
    Ok(Leaves { inputs, consts })
}

/// Concrete inputs and constants.
fn concrete_leaves(cx: &mut Context, pt: &Point) -> Result<Leaves, Error> {
    let mut inputs = Vec::new();
    for (v, p) in &pt.inputs {
        inputs.push((cx.constant(v)?, cx.bool(*p)?));
    }
    let mut consts = Vec::new();
    for v in &pt.consts {
        consts.push(cx.constant(v)?);
    }
    Ok(Leaves { inputs, consts })
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
        inputs.push((v, p && !t.source_attrs(i).noundef));
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

/// Whether the target's value `(vt, pt)` refines the source's `(vs, ps)`.
fn value_refines(
    cx: &mut Context,
    (vs, ps): (Expr, Expr),
    (vt, pt): (Expr, Expr),
) -> Result<Expr, Error> {
    let eq = cx.cmp(CmpOpExt::Eq, vt, vs)?;
    let npt = cx.un(UnOp::Not, pt)?;
    let same = cx.bin(BinOp::And, npt, eq)?;
    cx.bin(BinOp::Or, ps, same)
}

/// `φ`: the source (with its choices) answers the target at this point.
fn refines(cx: &mut Context, src: &Side, tgt: &Side) -> Result<Expr, Error> {
    let mut r = match (src.result, tgt.result) {
        (Some(s), Some(t)) => value_refines(cx, s, t)?,
        (None, None) => cx.bool(true)?,
        _ => {
            return Err(Error::Unsupported(
                "one side returns a value, the other not".into(),
            ));
        }
    };
    if src.matched.len() != tgt.matched.len() {
        return Err(Error::Contract(
            "the source and the target match different registers".into(),
        ));
    }
    for (&s, &t) in src.matched.iter().zip(&tgt.matched) {
        let m = value_refines(cx, s, t)?;
        r = cx.bin(BinOp::And, r, m)?;
    }
    let nub = cx.un(UnOp::Not, tgt.ub)?;
    let defined = cx.bin(BinOp::And, nub, r)?;
    let ok = cx.bin(BinOp::Or, src.ub, defined)?;
    let npre = cx.un(UnOp::Not, src.pre)?;
    let ok = cx.bin(BinOp::Or, npre, ok)?;
    cx.bin(BinOp::And, src.valid, ok)
}

/// A model of `q`, or `None` when there is none, or why it is not decided. With a
/// certificate asked for, an unsatisfiable `q` is accepted only with a DRUP proof that the
/// independent checker verifies.
fn satisfy(
    cx: &mut Context,
    q: Expr,
    pcfg: &prove::Config,
) -> Result<Result<Option<Model>, String>, Error> {
    let nq = cx.un(UnOp::Not, q)?;
    Ok(match prove::valid(cx, nq, pcfg)? {
        prove::Outcome::Proved(cert) => {
            if pcfg.certificate {
                match cert {
                    Some(c) => {
                        if let Err(e) = c.check() {
                            return Ok(Err(format!("a certificate does not check: {e}")));
                        }
                    }
                    None => return Ok(Err("a proof without its certificate".into())),
                }
            }
            Ok(None)
        }
        prove::Outcome::Refuted(m) => Ok(Some(m)),
        prove::Outcome::Unknown(why) => Err(why.to_string()),
    })
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
            pcfg: prove::Config::default()
                .with_max_conflicts(cfg.conflicts)
                .with_certificate(cfg.certify),
        })
    }

    /// A point where no source choice answers the target, under `extra`.
    fn find(&mut self, extra: Expr) -> Result<Found, Error> {
        for _ in 0..=self.rounds {
            let q = self.cx.bin(BinOp::And, self.base, extra)?;
            let model = match satisfy(&mut self.cx, q, &self.pcfg)? {
                Ok(None) => return Ok(Found::None),
                Ok(Some(m)) => m,
                Err(why) => return Err(Error::Unsupported(format!("unknown: {why}"))),
            };
            let pt = point(&model, self.t, self.ty, &self.tgt.choices)?;
            if !self.src_choices {
                return Ok(Found::Point(pt));
            }
            // A source choice that answers this point?
            let cl = concrete_leaves(&mut self.cx, &pt)?;
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
            let answer = match satisfy(&mut self.cx, phi, &self.pcfg)? {
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
        s.pcfg = prove::Config::default()
            .with_max_conflicts(cfg.minimize_conflicts)
            .with_certificate(cfg.certify);
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
    let leaves = concrete_leaves(cx, pt)?;
    let src = Enc::new(cx, t, ty, &leaves, Choices::Fixed(&[]))?.body(&t.src, true)?;
    let tgt = Enc::new(cx, t, ty, &leaves, Choices::Fixed(&pt.tgt))?.body(&t.tgt, false)?;
    let source = named_values(cx, t, ty, &src)?;
    let target = named_values(cx, t, ty, &tgt)?;
    let mut source_result = match (src.result, result_type(&t.src, ty)) {
        (Some((v, p)), Some(rt)) => Some((rt, shown_of(cx, v, p)?)),
        _ => None,
    };
    let mut target_result = match (tgt.result, result_type(&t.tgt, ty)) {
        (Some((v, p)), Some(rt)) => Some((rt, shown_of(cx, v, p)?)),
        _ => None,
    };
    let fails = |cx: &mut Context, s: (Expr, Expr), t: (Expr, Expr)| -> Result<bool, Error> {
        let ok = value_refines(cx, s, t)?;
        Ok(eval_one(cx, ok)?.is_zero())
    };
    let mut output = None;
    let mismatch = if !eval_one(cx, tgt.ub)?.is_zero() {
        Mismatch::TargetUb
    } else {
        // The first value that fails: the result, else a register defined again.
        let result_fails = match (src.result, tgt.result) {
            (Some(sr), Some(tr)) => fails(cx, sr, tr)?,
            _ => false,
        };
        if !result_fails {
            for (k, (&sv, &tv)) in src.matched.iter().zip(&tgt.matched).enumerate() {
                if fails(cx, sv, tv)? {
                    let (name, n) = &t.src.matched[k];
                    output = Some(format!("%{name}"));
                    source_result = Some((ty[*n as usize], shown_of(cx, sv.0, sv.1)?));
                    let tn = t.tgt.matched[k].1;
                    target_result = Some((ty[tn as usize], shown_of(cx, tv.0, tv.1)?));
                    break;
                }
            }
        }
        if matches!(target_result, Some((_, Shown::Poison))) {
            Mismatch::TargetPoison
        } else {
            Mismatch::Value
        }
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
        output,
        nondeterministic: s.src_choices,
    })
}

/// A type assignment's label and its SMT-LIB question, or why it has none (see [`smt`]).
#[cfg(feature = "smtlib")]
pub type Question = (String, Result<String, String>);

/// Each type assignment's question as an SMT-LIB 2.6 script, for another solver to check what
/// a verdict rests on: whether, at some input and with some choices of the target, the target
/// does what none of the source's executions found by the search does. For a valid
/// transformation every script is unsatisfiable, which a solver confirms independently of
/// bitwright's SAT solver and simplifier (the encoding of LLVM's semantics is bitwright's);
/// for an invalid one whose source makes no choices, the script of the failing assignment is
/// satisfiable. One per type assignment, with its label (the transformation's name and
/// types): the script, or why there is none (the search did not decide, or the source makes
/// choices and the counterexample is the verifier's). The error is the transformation's.
#[cfg(feature = "smtlib")]
pub fn smt(t: &Transform, cfg: &Config) -> Result<Vec<Question>, String> {
    let (t, assignments, total) = prepare(t, cfg)?;
    if total > assignments.len() {
        return Err(format!(
            "{total} type assignments, more than the most checked ({}); give some types",
            cfg.max_types
        ));
    }
    let mut out = Vec::new();
    for a in &assignments {
        let label = if a.label.is_empty() {
            t.name.clone()
        } else {
            format!("{} ({})", t.name, a.label)
        };
        let mut s = match Search::new(&t, a, cfg) {
            Ok(s) => s,
            Err(Error::Unsupported(m)) if m.starts_with(SKIP) => continue,
            Err(e) => {
                out.push((label, Err(e.to_string())));
                continue;
            }
        };
        let script = (|| -> Result<String, String> {
            let tru = s.cx.bool(true).map_err(|e| e.to_string())?;
            let expect = match s.find(tru) {
                Ok(Found::None) => "unsat",
                Ok(Found::Point(_)) if !s.src_choices => "sat",
                Ok(Found::Point(_)) => {
                    return Err(
                        "invalid (the source makes choices: the counterexample is the \
                                verifier's)"
                            .into(),
                    );
                }
                Err(Error::Unsupported(m)) => {
                    return Err(m.trim_start_matches("unknown: ").to_string());
                }
                Err(e) => return Err(e.to_string()),
            };
            let base = s.base;
            let script =
                crate::smtlib::satisfiability_query(&mut s.cx, base).map_err(|e| e.to_string())?;
            Ok(format!("; {label}: expect {expect}\n{script}"))
        })();
        out.push((label, script));
    }
    Ok(out)
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
