//! The reference pattern matcher: a direct, backtracking matcher of a rule's pattern against
//! a node of a context. It is the specification the engine's fast matcher is tested against,
//! and it drives the unreachable-pattern lint.
//!
//! Matching is complete: every operand order of every commutative node is tried, width
//! variables are bound in whatever order the node widths determine them, and a candidate is
//! accepted only after every deferred check (widths, closed subterms, the rule's constraints
//! and well-formedness at the bound widths) has passed. A step budget bounds the search; a
//! search over budget is no match, which is always sound.

use super::eval::{admitted, literal};
use super::ir::{NodeId, ParamKind, RNode, Rounding, Rule, Sort, WExpr};
use crate::Width;
use crate::expr::{Context, OpCode};
use crate::ops::CmpOp;

/// Pattern/node pairs the matcher may visit per match attempt.
pub(crate) const MATCH_STEPS: u32 = 1 << 14;

/// The result of a match attempt.
pub(crate) enum Match {
    Yes(Bindings),
    No,
    /// The step budget ran out first: the node may or may not match.
    OutOfSteps,
}

/// The result of a match: node indices bound to parameters, widths bound to width variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Bindings {
    pub(crate) params: Vec<Option<u32>>,
    pub(crate) widths: Vec<Option<u16>>,
}

/// The outcome of binding a width expression to a value.
enum Bind {
    Ok,
    Fail,
    /// Two or more of its variables are unbound: try again later.
    Later,
}

impl Bindings {
    pub(crate) fn new(rule: &Rule) -> Self {
        Bindings {
            params: vec![None; rule.params.len()],
            // The width variables, then the rounding-mode variables.
            widths: vec![None; rule.width_vars.len() + rule.modes.len()],
        }
    }

    /// Binds rounding-mode variable slot `k` (after the width variables) to `mode`, or checks
    /// it.
    fn bind_mode(&mut self, k: usize, mode: u16) -> bool {
        match self.widths[k] {
            Some(m) => m == mode,
            None => {
                self.widths[k] = Some(mode);
                true
            }
        }
    }

    /// Binds the width variables of `e` so that `e == actual`: checks it when every variable
    /// is bound, solves for the one unbound variable, or defers when there are more.
    fn bind(&mut self, e: &WExpr, actual: i64) -> Bind {
        let mut rest = actual - e.konst;
        let mut free: Option<(u8, i64)> = None;
        for &(v, c) in &e.terms {
            match self.widths[v as usize] {
                Some(w) => rest -= c * i64::from(w),
                None if free.is_none() => free = Some((v, c)),
                None => return Bind::Later,
            }
        }
        match free {
            None if rest == 0 => Bind::Ok,
            None => Bind::Fail,
            Some((v, c)) => {
                if c == 0 || rest % c != 0 {
                    return Bind::Fail;
                }
                let val = rest / c;
                if !(1..=i64::from(Width::MAX_BITS)).contains(&val) {
                    return Bind::Fail;
                }
                self.widths[v as usize] = Some(val as u16);
                Bind::Ok
            }
        }
    }

    pub(crate) fn width_values(&self) -> Option<Vec<u16>> {
        self.widths.iter().copied().collect()
    }
}

/// Which width expression of a pattern node.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Which {
    /// Its sort's width.
    Sort,
    /// An extract's offset.
    Offset,
    /// A floating-point node's exponent width.
    Eb,
    /// A conversion's target exponent width.
    ToEb,
}

/// A partial match: bindings plus the pairs still to visit and the checks still to make.
#[derive(Clone)]
struct State {
    b: Bindings,
    todo: Vec<(NodeId, u32)>,
    /// `(width expression's owner, which one, actual)` not yet determined.
    widths: Vec<(NodeId, Which, i64)>,
    /// Literals and closed subterms, compared by value once every width is bound.
    values: Vec<(NodeId, u32)>,
}

struct M<'a> {
    cx: &'a Context,
    rule: &'a Rule,
    steps: u32,
}

fn width_expr(rule: &Rule, pat: NodeId, which: Which) -> Option<&WExpr> {
    match (which, &rule.nodes[pat as usize]) {
        (Which::Sort, _) => match &rule.sorts[pat as usize] {
            Sort::Bv(w) => Some(w),
            Sort::Bool => None,
        },
        (Which::Offset, RNode::Extract(lo, _)) => Some(lo),
        (Which::Eb, RNode::Fp(f)) => Some(&f.eb),
        (Which::ToEb, RNode::Fp(f)) => f.to.as_ref().map(|(e, _)| e),
        _ => None,
    }
}

/// Binds (or defers) one width expression of the pattern.
fn bind_or_defer(m: &M<'_>, st: &mut State, pat: NodeId, which: Which, actual: i64) -> bool {
    let Some(e) = width_expr(m.rule, pat, which) else {
        return true;
    };
    match st.b.bind(e, actual) {
        Bind::Ok => true,
        Bind::Fail => false,
        Bind::Later => {
            st.widths.push((pat, which, actual));
            true
        }
    }
}

/// Visits one pattern/node pair, pushing the children to visit. `false` on a mismatch.
fn step(m: &mut M<'_>, st: &mut State, pat: NodeId, node: u32) -> Step {
    let (rule, cx) = (m.rule, m.cx);
    let n = cx.node(node);
    if !bind_or_defer(m, st, pat, Which::Sort, i64::from(n.width)) {
        return Step::Fail;
    }
    // A closed subterm (no parameters) denotes one constant, which the builder has folded.
    if matches!(rule.nodes[pat as usize], RNode::Lit(_)) || is_closed(rule, pat) {
        if n.op != OpCode::Const {
            return Step::Fail;
        }
        st.values.push((pat, node));
        return Step::Ok;
    }
    match &rule.nodes[pat as usize] {
        RNode::Param(i) => {
            let kind_ok = match rule.params[*i as usize].kind {
                ParamKind::Any => true,
                ParamKind::Const => n.op == OpCode::Const,
                ParamKind::Sym => n.op == OpCode::Sym,
                ParamKind::NonConst => n.op != OpCode::Const,
            };
            if !kind_ok {
                return Step::Fail;
            }
            match st.b.params[*i as usize] {
                Some(prev) if prev != node => return Step::Fail,
                Some(_) => {}
                None => st.b.params[*i as usize] = Some(node),
            }
            Step::Ok
        }
        RNode::Un(op, a) if n.op == OpCode::from_un(*op) => {
            st.todo.push((*a, n.a));
            Step::Ok
        }
        RNode::Bin(op, x, y) if n.op == OpCode::from_bin(*op) => {
            if op.is_commutative() {
                Step::Either((*x, *y), (n.a, n.b))
            } else {
                st.todo.push((*y, n.b));
                st.todo.push((*x, n.a));
                Step::Ok
            }
        }
        RNode::Cmp(op, x, y) => {
            let (stored, swap) = op.canonical();
            if n.op != OpCode::from_cmp(stored) {
                return Step::Fail;
            }
            let (px, py) = if swap { (*y, *x) } else { (*x, *y) };
            if matches!(stored, CmpOp::Eq | CmpOp::Ne) {
                Step::Either((px, py), (n.a, n.b))
            } else {
                st.todo.push((py, n.b));
                st.todo.push((px, n.a));
                Step::Ok
            }
        }
        RNode::Zext(a) if n.op == OpCode::Zext => {
            st.todo.push((*a, n.a));
            Step::Ok
        }
        RNode::Sext(a) if n.op == OpCode::Sext => {
            st.todo.push((*a, n.a));
            Step::Ok
        }
        RNode::Extract(_, a) if n.op == OpCode::Extract => {
            if !bind_or_defer(m, st, pat, Which::Offset, i64::from(n.b)) {
                return Step::Fail;
            }
            st.todo.push((*a, n.a));
            Step::Ok
        }
        RNode::Concat(h, l) if n.op == OpCode::Concat => {
            st.todo.push((*l, n.b));
            st.todo.push((*h, n.a));
            Step::Ok
        }
        RNode::Select(c, t, f) if n.op == OpCode::Select => {
            st.todo.push((*f, n.c));
            st.todo.push((*t, n.b));
            st.todo.push((*c, n.a));
            Step::Ok
        }
        RNode::Fp(f) if n.op == f.kind.opcode() => {
            // The node's attributes: the format's exponent width, a conversion's target's,
            // and the rounding mode (fixed, or bound to a variable).
            let aux = n.aux;
            if !bind_or_defer(m, st, pat, Which::Eb, i64::from(aux & 31)) {
                return Step::Fail;
            }
            if f.to.is_some() && !bind_or_defer(m, st, pat, Which::ToEb, i64::from(n.b)) {
                return Step::Fail;
            }
            let mode = u16::from(aux >> 5);
            match f.rounding {
                Some(Rounding::Mode(r)) if u16::from(crate::fp::node::rm_code(r)) != mode => {
                    return Step::Fail;
                }
                Some(Rounding::Var(i))
                    if !st.b.bind_mode(rule.width_vars.len() + usize::from(i), mode) =>
                {
                    return Step::Fail;
                }
                _ => {}
            }
            let kids = [n.a, n.b, n.c];
            if f.kind.commutative() {
                // The first two operands in either order (the third, fma's addend, fixed).
                if let Some(&c) = f.args.get(2) {
                    st.todo.push((c, kids[2]));
                }
                Step::Either((f.args[0], f.args[1]), (n.a, n.b))
            } else {
                for (k, &a) in f.args.iter().enumerate().rev() {
                    st.todo.push((a, kids[k]));
                }
                Step::Ok
            }
        }
        _ => Step::Fail,
    }
}

enum Step {
    Ok,
    Fail,
    /// A commutative pair: patterns and nodes, to be tried in both orders.
    Either((NodeId, NodeId), (u32, u32)),
}

/// Runs the search from a state; the first complete match.
fn solve(m: &mut M<'_>, mut st: State) -> Option<Bindings> {
    while let Some((pat, node)) = st.todo.pop() {
        if m.steps == 0 {
            return None;
        }
        m.steps -= 1;
        match step(m, &mut st, pat, node) {
            Step::Ok => {}
            Step::Fail => return None,
            Step::Either((px, py), (na, nb)) => {
                let mut swapped = st.clone();
                st.todo.push((py, nb));
                st.todo.push((px, na));
                if let Some(b) = solve(m, st) {
                    return Some(b);
                }
                if na == nb {
                    return None; // the swapped order is the same search
                }
                swapped.todo.push((py, na));
                swapped.todo.push((px, nb));
                return solve(m, swapped);
            }
        }
    }
    finish(m, st)
}

/// The deferred checks of a complete structural match.
fn finish(m: &M<'_>, mut st: State) -> Option<Bindings> {
    let rule = m.rule;
    // Width expressions with several unbound variables, until nothing changes.
    loop {
        let before = st.widths.len();
        let pending = std::mem::take(&mut st.widths);
        for (pat, which, actual) in pending {
            let e = width_expr(rule, pat, which)?;
            match st.b.bind(e, actual) {
                Bind::Ok => {}
                Bind::Fail => return None,
                Bind::Later => st.widths.push((pat, which, actual)),
            }
        }
        if st.widths.is_empty() {
            break;
        }
        if st.widths.len() == before {
            return None;
        }
    }
    let widths = st.b.width_values()?;
    if !admitted(rule, &widths) {
        return None;
    }
    for (pat, n) in st.values {
        let want = match &rule.nodes[pat as usize] {
            RNode::Lit(l) => literal(l, m.cx.width_of(n), &widths)?,
            _ => super::eval::eval(rule, pat, &widths, &[], &[])?.bv()?,
        };
        if m.cx.const_val(n)? != want {
            return None;
        }
    }
    Some(st.b)
}

/// Whether the subterm mentions no parameter (and no `let`).
pub(crate) fn is_closed(rule: &Rule, n: NodeId) -> bool {
    let mut stack = vec![n];
    while let Some(k) = stack.pop() {
        match &rule.nodes[k as usize] {
            RNode::Param(_) | RNode::Let(_) => return false,
            other => stack.extend(super::compile::children(other)),
        }
    }
    true
}

/// Matches the pattern of `rule` against node `node`; the bindings on success. The rule's
/// constraints hold and the rule is well formed at the bound widths.
pub(crate) fn match_rule(cx: &Context, rule: &Rule, node: u32) -> Option<Bindings> {
    let mut steps = MATCH_STEPS;
    match match_rule_steps(cx, rule, node, &mut steps) {
        Match::Yes(b) => Some(b),
        Match::No | Match::OutOfSteps => None,
    }
}

/// [`match_rule`] with an explicit step budget, which is decremented by the steps taken.
pub(crate) fn match_rule_steps(cx: &Context, rule: &Rule, node: u32, steps: &mut u32) -> Match {
    let mut m = M {
        cx,
        rule,
        steps: *steps,
    };
    let st = State {
        b: Bindings::new(rule),
        todo: vec![(rule.lhs, node)],
        widths: Vec::new(),
        values: Vec::new(),
    };
    let r = solve(&mut m, st);
    let exhausted = m.steps == 0;
    *steps = m.steps;
    match r {
        Some(b) => Match::Yes(b),
        None if exhausted => Match::OutOfSteps,
        None => Match::No,
    }
}

/// Builds an instance of the pattern at the given widths, with symbols for non-constant
/// parameters and the given values for constant ones. `None` if some node cannot be built.
pub(crate) fn build_pattern(
    cx: &mut Context,
    rule: &Rule,
    widths: &[u16],
    consts: &[crate::BitVec],
) -> Option<u32> {
    fn build(
        cx: &mut Context,
        rule: &Rule,
        n: NodeId,
        widths: &[u16],
        consts: &[crate::BitVec],
    ) -> Option<u32> {
        let w = super::eval::width_of(rule, n, widths);
        let rec = |cx: &mut Context, m: NodeId| build(cx, rule, m, widths, consts);
        Some(match &rule.nodes[n as usize] {
            RNode::Param(i) => {
                let p = &rule.params[*i as usize];
                if p.kind == ParamKind::Const {
                    let v = consts.get(*i as usize)?;
                    cx.mk_const(v).ok()?
                } else {
                    let e = cx.symbol(format!("${}", p.name).as_str(), w?).ok()?;
                    cx.id(e).ok()?
                }
            }
            RNode::Lit(l) => cx.mk_const(&literal(l, w?, widths)?).ok()?,
            RNode::Un(op, a) => {
                let a = rec(cx, *a)?;
                cx.c_un(*op, a).ok()?
            }
            RNode::Bin(op, a, b) => {
                let (a, b) = (rec(cx, *a)?, rec(cx, *b)?);
                cx.c_bin(*op, a, b).ok()?
            }
            RNode::Cmp(op, a, b) => {
                let (a, b) = (rec(cx, *a)?, rec(cx, *b)?);
                let (stored, swap) = op.canonical();
                let (a, b) = if swap { (b, a) } else { (a, b) };
                cx.c_cmp(stored, a, b).ok()?
            }
            RNode::Zext(a) => {
                let a = rec(cx, *a)?;
                cx.c_zext(a, w?.bits()).ok()?
            }
            RNode::Sext(a) => {
                let a = rec(cx, *a)?;
                cx.c_sext(a, w?.bits()).ok()?
            }
            RNode::Extract(lo, a) => {
                let a = rec(cx, *a)?;
                let lo = u16::try_from(lo.eval(widths)).ok()?;
                cx.c_extract(a, lo, w?.bits()).ok()?
            }
            RNode::Concat(h, l) => {
                let (h, l) = (rec(cx, *h)?, rec(cx, *l)?);
                cx.c_concat(h, l).ok()?
            }
            RNode::Select(c, t, f) => {
                let (c, t, f) = (rec(cx, *c)?, rec(cx, *t)?, rec(cx, *f)?);
                cx.c_select(c, t, f).ok()?
            }
            RNode::Fp(f) => {
                let d = super::eval::fp_desc(rule, n, f, widths)?;
                let args: Vec<u32> = f.args.iter().map(|&a| rec(cx, a)).collect::<Option<_>>()?;
                cx.c_fp(d, &args).ok()?
            }
            _ => return None,
        })
    }
    build(cx, rule, rule.lhs, widths, consts)
}

/// Whether the pattern can match anything the builder produces: some instance of it, built
/// through the canonicalizing constructors, is matched by the pattern itself. A pattern the
/// builder always rewrites (a constant on the left of `+`, `x - c`, `ugt`, …) never fires.
pub(crate) fn pattern_reachable(rule: &Rule) -> bool {
    use crate::BitVec;
    let assignments = super::compile::width_assignments(rule);
    let matchable: Vec<&Vec<u16>> = assignments.iter().filter(|ws| admitted(rule, ws)).collect();
    // Prefer small-but-not-tiny widths, then a few others.
    let mut picks: Vec<&Vec<u16>> = matchable
        .iter()
        .copied()
        .filter(|ws| ws.iter().all(|&w| (4..=16).contains(&w)))
        .take(3)
        .collect();
    picks.extend(matchable.iter().copied().take(2));
    let mut seed = 0x51ed_u64;
    for ws in picks {
        let Some(pw): Option<Vec<Width>> = rule
            .params
            .iter()
            .map(|p| {
                u16::try_from(p.width.eval(ws))
                    .ok()
                    .and_then(|w| Width::new(w).ok())
            })
            .collect()
        else {
            continue;
        };
        for attempt in 0..12u64 {
            let consts: Vec<BitVec> = pw
                .iter()
                .map(|&w| {
                    seed = seed
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    match attempt {
                        0 => BitVec::wrapping_from_u64(w, 3),
                        1 => BitVec::one(w),
                        2 => BitVec::ones(w),
                        3 => BitVec::smin(w),
                        4 => BitVec::wrapping_from_u64(w, 2),
                        5 => BitVec::wrapping_from_u64(w, 4),
                        _ => BitVec::wrapping_from_u64(w, seed >> 7),
                    }
                })
                .collect();
            let mut cx = Context::new();
            if let Some(root) = build_pattern(&mut cx, rule, ws, &consts)
                && match_rule(&cx, rule, root).is_some()
            {
                return true;
            }
        }
    }
    false
}
