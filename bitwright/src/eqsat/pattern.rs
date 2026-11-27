//! Admitted identities and guarded/multi-width rules as e-patterns, e-matching, guard evaluation
//! over e-class [`Facts`], and instantiation.

use super::egraph::{ClassId, EGraph, ENode, EOp, Halt};
use crate::engine::budget::{Counter, Meter};
use crate::facts::Facts;
use crate::facts::known::bv_and;
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::rules::{FactPred, Literal, NodeId, ParamKind, RNode, Rule, RuleKind, Sort, WExpr};
use crate::{BitVec, Width};

/// A pattern node's operator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum POp {
    Var(u16),
    Let(u16),
    Lit(Literal),
    Un(UnOp, u16),
    Bin(BinOp, u16, u16),
    Cmp(CmpOp, u16, u16),
    Zext(u16),
    Sext(u16),
    Extract { lo: WExpr, src: u16 },
    Concat(u16, u16),
    Select(u16, u16, u16),
}

/// One node of an e-pattern, with its symbolic bit-width expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PNode {
    pub(crate) op: POp,
    pub(crate) width: WExpr,
}

/// One side of an equation, width-polymorphic over the rule's width variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Pattern {
    pub(crate) nodes: Vec<PNode>,
    pub(crate) root: u16,
}

/// A match of a pattern at a class: bound width variables and bound parameter e-classes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct MatchOut {
    pub(crate) widths: Vec<u16>,
    pub(crate) vars: Vec<ClassId>,
}

/// An admitted equation or rule.
#[derive(Clone, Debug)]
pub(crate) struct Identity {
    pub(crate) rule: Rule,
    pub(crate) sides: [Pattern; 2],
    pub(crate) vars: usize,
    pub(crate) bidirectional: bool,
}

/// The operators the conservative fragment admits.
pub(crate) fn admitted_bin_conservative(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor
    )
}

pub(crate) fn admitted_un_conservative(op: UnOp) -> bool {
    matches!(op, UnOp::Neg | UnOp::Not)
}

fn guard_supported(rule: &Rule, n: NodeId) -> Result<(), String> {
    match &rule.nodes[n as usize] {
        RNode::And(a, b) | RNode::Or(a, b) => {
            guard_supported(rule, *a)?;
            guard_supported(rule, *b)
        }
        RNode::Not(a) => guard_supported(rule, *a),
        RNode::Fact(p, x, m) => match p {
            FactPred::OneUse => Err("one_use is a sharing predicate, not an equation guard".into()),
            FactPred::FpNotNan | FactPred::FpFinite | FactPred::FpNonZero => {
                Err("floating-point predicates are outside the integer e-graph".into())
            }
            FactPred::Proves => match &rule.nodes[*x as usize] {
                RNode::Cmp(_, l, r) => {
                    pure_or_param(rule, *l)?;
                    pure_or_param(rule, *r)
                }
                _ => Err("unsupported proves guard".into()),
            },
            FactPred::NonZero => pure_or_param(rule, *x),
            FactPred::Disjoint | FactPred::ZeroBits | FactPred::OneBits => {
                pure_or_param(rule, *x)?;
                match m {
                    Some(m) => pure_or_param(rule, *m),
                    None => Err("missing second argument to fact predicate".into()),
                }
            }
        },
        RNode::ConstP(_, a) => pure_or_param(rule, *a),
        _ => pure_or_param(rule, n),
    }
}

fn pure_or_param(rule: &Rule, n: NodeId) -> Result<(), String> {
    match &rule.nodes[n as usize] {
        RNode::Param(_) | RNode::Let(_) | RNode::Lit(_) => Ok(()),
        RNode::Un(_, a) | RNode::Zext(a) | RNode::Sext(a) | RNode::Extract(_, a) => {
            pure_or_param(rule, *a)
        }
        RNode::Bin(_, a, b) | RNode::Cmp(_, a, b) | RNode::Concat(a, b) => {
            pure_or_param(rule, *a)?;
            pure_or_param(rule, *b)
        }
        RNode::Select(c, t, f) => {
            pure_or_param(rule, *c)?;
            pure_or_param(rule, *t)?;
            pure_or_param(rule, *f)
        }
        other => Err(format!("guard subterm outside the fragment: {other:?}")),
    }
}

fn side(rule: &Rule, root: NodeId, extended: bool) -> Result<Pattern, String> {
    let mut nodes: Vec<PNode> = Vec::new();
    let mut map: Vec<Option<u16>> = vec![None; rule.nodes.len()];
    let mut stack: Vec<(NodeId, bool)> = vec![(root, false)];
    while let Some((n, expanded)) = stack.pop() {
        if map[n as usize].is_some() {
            continue;
        }
        let node = &rule.nodes[n as usize];
        let kids: Vec<NodeId> = match node {
            RNode::Un(_, a) | RNode::Zext(a) | RNode::Sext(a) | RNode::Extract(_, a) => vec![*a],
            RNode::Bin(_, a, b) | RNode::Cmp(_, a, b) | RNode::Concat(a, b) => vec![*a, *b],
            RNode::Select(c, t, f) => vec![*c, *t, *f],
            _ => vec![],
        };
        if !expanded && !kids.is_empty() {
            stack.push((n, true));
            for k in kids {
                stack.push((k, false));
            }
            continue;
        }
        let Sort::Bv(width) = &rule.sorts[n as usize] else {
            return Err("non-bitvector sort in term".into());
        };
        let at = |k: NodeId| map[k as usize].ok_or_else(|| "unexpected order".to_string());
        let op = match node {
            RNode::Param(i) => POp::Var(*i),
            RNode::Lit(l) => POp::Lit(l.clone()),
            RNode::Let(i) if extended => POp::Let(*i),
            RNode::Un(op, a) if extended || admitted_un_conservative(*op) => POp::Un(*op, at(*a)?),
            RNode::Bin(op, a, b) if extended || admitted_bin_conservative(*op) => {
                POp::Bin(*op, at(*a)?, at(*b)?)
            }
            RNode::Cmp(op, a, b) if extended => {
                let (cop, swap) = op.canonical();
                let (l, r) = if swap { (*b, *a) } else { (*a, *b) };
                POp::Cmp(cop, at(l)?, at(r)?)
            }
            RNode::Zext(a) if extended => POp::Zext(at(*a)?),
            RNode::Sext(a) if extended => POp::Sext(at(*a)?),
            RNode::Extract(lo, a) if extended => POp::Extract {
                lo: lo.clone(),
                src: at(*a)?,
            },
            RNode::Concat(h, l) if extended => POp::Concat(at(*h)?, at(*l)?),
            RNode::Select(c, t, f) if extended => POp::Select(at(*c)?, at(*t)?, at(*f)?),
            other => return Err(format!("operator outside the fragment: {other:?}")),
        };
        map[n as usize] = Some(nodes.len() as u16);
        nodes.push(PNode {
            op,
            width: width.clone(),
        });
    }
    let root = map[root as usize].ok_or_else(|| "empty side".to_string())?;
    Ok(Pattern { nodes, root })
}

/// Whether pattern `p` mentions every parameter `0..n_vars` and every width variable `0..n_wvars`.
fn binds_all(p: &Pattern, n_vars: usize, n_wvars: usize) -> bool {
    let mut seen_v = vec![false; n_vars];
    let mut seen_w = vec![false; n_wvars];
    let mut mark_w = |w: &WExpr| {
        for &(v, c) in &w.terms {
            if c != 0 && (v as usize) < n_wvars {
                seen_w[v as usize] = true;
            }
        }
    };
    for n in &p.nodes {
        mark_w(&n.width);
        match &n.op {
            POp::Var(v) => {
                if (*v as usize) < n_vars {
                    seen_v[*v as usize] = true;
                }
            }
            POp::Extract { lo, .. } => mark_w(lo),
            POp::Lit(Literal::LowMask(w) | Literal::Bit(w) | Literal::Width(w)) => mark_w(w),
            _ => {}
        }
    }
    seen_v.into_iter().all(|x| x) && seen_w.into_iter().all(|x| x)
}

/// Compiles a rule into an identity, or says why it is not admitted.
pub(crate) fn admit(rule: &Rule, proven: bool, extended: bool) -> Result<Identity, String> {
    if !extended {
        if rule.kind == RuleKind::Rewrite && rule.params.iter().any(|p| p.kind != ParamKind::Any) {
            return Err(
                "a rule with capture kinds (const, sym, nonconst) is not an equation".into(),
            );
        }
        if !proven {
            return Err("not vouched for by its ledger".into());
        }
        if rule.width_vars.len() != 1 || !rule.constraints.is_empty() {
            return Err("needs exactly one width variable and no width constraints".into());
        }
        if rule.guard.is_some() || !rule.lets.is_empty() {
            return Err("has a guard or lets".into());
        }
        let w = WExpr::var(0);
        if rule
            .sorts
            .iter()
            .any(|s| !matches!(s, Sort::Bv(e) if *e == w))
        {
            return Err("not homogeneous in its width".into());
        }
        return Ok(Identity {
            sides: [side(rule, rule.lhs, false)?, side(rule, rule.rhs, false)?],
            vars: rule.params.len(),
            bidirectional: rule.kind == RuleKind::Identity,
            rule: rule.clone(),
        });
    }

    // Extended fragment admission (`1..=512`, mixed widths, casts/shifts/select/cmp, Facts guards).
    if rule.float_values || !rule.modes.is_empty() {
        return Err("floating-point rules are outside the integer e-graph".into());
    }
    if rule
        .params
        .iter()
        .any(|p| !matches!(p.kind, ParamKind::Any | ParamKind::Const))
    {
        return Err("capture kinds sym and nonconst are not congruence-invariant".into());
    }
    if !proven {
        return Err("not vouched for by its ledger".into());
    }
    if rule.width_vars.len() > 4 {
        return Err("too many width variables".into());
    }
    for l in &rule.lets {
        pure_or_param(rule, l.value)?;
    }
    if let Some(g) = rule.guard {
        guard_supported(rule, g)?;
    }
    let lhs = side(rule, rule.lhs, true)?;
    let rhs = side(rule, rule.rhs, true)?;
    let n_vars = rule.params.len();
    let n_wvars = rule.width_vars.len();
    if !binds_all(&lhs, n_vars, n_wvars) {
        return Err("left-hand side does not bind all parameters and width variables".into());
    }
    // Bidirectional for identities and for guarded variable/width-preserving equations without lets
    // (e.g. `x + y => x | y if disjoint(x, y)` holds in both directions wherever `disjoint` holds).
    let bidirectional = match rule.kind {
        RuleKind::Identity => binds_all(&rhs, n_vars, n_wvars),
        RuleKind::Rewrite => {
            rule.guard.is_some()
                && rule.lets.is_empty()
                && rule.params.iter().all(|p| p.kind == ParamKind::Any)
                && binds_all(&rhs, n_vars, n_wvars)
        }
    };
    Ok(Identity {
        rule: rule.clone(),
        sides: [lhs, rhs],
        vars: n_vars,
        bidirectional,
    })
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum BindStep {
    Ok,
    Fail,
    Later,
}

fn try_bind_one(widths: &mut [Option<u16>], e: &WExpr, actual: i64, max_width: u16) -> BindStep {
    let mut rest = actual - e.konst;
    let mut free: Option<(u8, i64)> = None;
    for &(v, c) in &e.terms {
        match widths.get(v as usize).copied().flatten() {
            Some(w) => rest -= c * i64::from(w),
            None if free.is_none() => free = Some((v, c)),
            None => return BindStep::Later,
        }
    }
    match free {
        None if rest == 0 => BindStep::Ok,
        None => BindStep::Fail,
        Some((v, c)) => {
            if c == 0 || rest % c != 0 {
                return BindStep::Fail;
            }
            let val = rest / c;
            if !(1..=i64::from(max_width)).contains(&val) {
                return BindStep::Fail;
            }
            widths[v as usize] = Some(val as u16);
            BindStep::Ok
        }
    }
}

fn bind_width(
    widths: &mut [Option<u16>],
    deferred: &mut Vec<(WExpr, i64)>,
    e: &WExpr,
    actual: i64,
    max_width: u16,
) -> bool {
    match try_bind_one(widths, e, actual, max_width) {
        BindStep::Fail => return false,
        BindStep::Later => {
            deferred.push((e.clone(), actual));
            return true;
        }
        BindStep::Ok => {}
    }
    // Propagate newly bound variables into any deferred width equations.
    loop {
        let mut progress = false;
        let mut i = 0;
        while i < deferred.len() {
            let (de, da) = &deferred[i];
            match try_bind_one(widths, de, *da, max_width) {
                BindStep::Fail => return false,
                BindStep::Later => i += 1,
                BindStep::Ok => {
                    deferred.swap_remove(i);
                    progress = true;
                }
            }
        }
        if !progress {
            return true;
        }
    }
}

/// Structural disjointness in the e-graph: `cx` and `cy` are guaranteed bit-disjoint if some
/// `a & p` node in `cx` (or `cx` itself) and some `b & q` node in `cy` (or `cy` itself) use
/// complement classes `q == ~p`.
fn structural_disjoint(eg: &mut EGraph, cx: ClassId, cy: ClassId) -> bool {
    let cx = eg.find(cx);
    let cy = eg.find(cy);
    let factors = |eg: &mut EGraph, c: ClassId| -> Vec<ClassId> {
        let mut out = vec![c];
        let nodes = eg.classes[c as usize].nodes.clone();
        for ni in nodes {
            let n = eg.nodes[ni as usize];
            if n.op == EOp::Bin(BinOp::And) {
                let k0 = eg.find(n.kids[0]);
                let k1 = eg.find(n.kids[1]);
                if !out.contains(&k0) {
                    out.push(k0);
                }
                if !out.contains(&k1) {
                    out.push(k1);
                }
            }
        }
        out
    };
    let is_not_pair = |eg: &mut EGraph, a: ClassId, b: ClassId| -> bool {
        let check_dir = |eg: &mut EGraph, u: ClassId, v: ClassId| -> bool {
            let nodes = eg.classes[u as usize].nodes.clone();
            nodes.into_iter().any(|ni| {
                let n = eg.nodes[ni as usize];
                n.op == EOp::Un(UnOp::Not) && eg.find(n.kids[0]) == v
            })
        };
        check_dir(eg, a, b) || check_dir(eg, b, a)
    };
    let fx = factors(eg, cx);
    let fy = factors(eg, cy);
    for &a in &fx {
        for &b in &fy {
            if is_not_pair(eg, a, b) {
                return true;
            }
        }
    }
    false
}

fn const_params_for_egraph(
    eg: &mut EGraph,
    rule: &Rule,
    widths: &[u16],
    vars: &[ClassId],
) -> Option<Vec<BitVec>> {
    rule.params
        .iter()
        .zip(vars)
        .map(|(p, &cid)| {
            let cid = eg.find(cid);
            if p.kind == ParamKind::Const {
                eg.classes[cid as usize].konst
            } else {
                let w = u16::try_from(p.width.eval(widths)).ok()?;
                Some(BitVec::zero(Width::new(w).ok()?))
            }
        })
        .collect()
}

fn operand_facts_egraph(
    eg: &mut EGraph,
    rule: &Rule,
    n: NodeId,
    widths: &[u16],
    vars: &[ClassId],
    consts: &[BitVec],
    lets: &[Option<BitVec>],
) -> Option<Facts> {
    match &rule.nodes[n as usize] {
        RNode::Param(i) => {
            let cid = eg.find(vars[*i as usize]);
            Some(eg.classes[cid as usize].facts)
        }
        _ => {
            let v = crate::rules::eval::eval(rule, n, widths, consts, lets)?.bv()?;
            Some(Facts::constant(&v))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn guard_node_holds(
    eg: &mut EGraph,
    rule: &Rule,
    n: NodeId,
    widths: &[u16],
    vars: &[ClassId],
    consts: &[BitVec],
    lets: &[Option<BitVec>],
) -> Option<bool> {
    match &rule.nodes[n as usize] {
        RNode::And(x, y) => Some(
            guard_node_holds(eg, rule, *x, widths, vars, consts, lets)?
                && guard_node_holds(eg, rule, *y, widths, vars, consts, lets)?,
        ),
        RNode::Or(x, y) => Some(
            guard_node_holds(eg, rule, *x, widths, vars, consts, lets)?
                || guard_node_holds(eg, rule, *y, widths, vars, consts, lets)?,
        ),
        RNode::Not(x) => Some(!guard_node_holds(eg, rule, *x, widths, vars, consts, lets)?),
        RNode::Fact(p, x, m) => {
            let fx = operand_facts_egraph(eg, rule, *x, widths, vars, consts, lets)?;
            Some(match p {
                FactPred::OneUse
                | FactPred::FpNotNan
                | FactPred::FpFinite
                | FactPred::FpNonZero => return None,
                FactPred::NonZero => {
                    let z = Facts::constant(&BitVec::zero(fx.width()));
                    crate::facts::decide_cmp(CmpOp::Eq, &fx, &z) == Some(false)
                }
                FactPred::ZeroBits => {
                    let mv = crate::rules::eval::eval(rule, (*m)?, widths, consts, lets)?.bv()?;
                    bv_and(&fx.known().maybe_one(), &mv).is_zero()
                }
                FactPred::OneBits => {
                    let mv = crate::rules::eval::eval(rule, (*m)?, widths, consts, lets)?.bv()?;
                    bv_and(&fx.known().known_one(), &mv) == mv
                }
                FactPred::Disjoint => {
                    let my = (*m)?;
                    let fy = operand_facts_egraph(eg, rule, my, widths, vars, consts, lets)?;
                    if bv_and(&fx.known().maybe_one(), &fy.known().maybe_one()).is_zero() {
                        true
                    } else if let (RNode::Param(ix), RNode::Param(iy)) =
                        (&rule.nodes[*x as usize], &rule.nodes[my as usize])
                    {
                        structural_disjoint(eg, vars[*ix as usize], vars[*iy as usize])
                    } else {
                        false
                    }
                }
                FactPred::Proves => {
                    let RNode::Cmp(op, l, r) = &rule.nodes[*x as usize] else {
                        return None;
                    };
                    let (stored, swap) = op.canonical();
                    let (l, r) = if swap { (*r, *l) } else { (*l, *r) };
                    if let (RNode::Param(i), RNode::Param(j)) =
                        (&rule.nodes[l as usize], &rule.nodes[r as usize])
                        && eg.find(vars[*i as usize]) == eg.find(vars[*j as usize])
                    {
                        return Some(matches!(stored, CmpOp::Eq | CmpOp::Ule | CmpOp::Sle));
                    }
                    let fl = operand_facts_egraph(eg, rule, l, widths, vars, consts, lets)?;
                    let fr = operand_facts_egraph(eg, rule, r, widths, vars, consts, lets)?;
                    crate::facts::decide_cmp(stored, &fl, &fr) == Some(true)
                }
            })
        }
        _ => crate::rules::eval::eval(rule, n, widths, consts, lets).map(|v| v.truthy()),
    }
}

fn guard_holds_egraph(eg: &mut EGraph, rule: &Rule, widths: &[u16], vars: &[ClassId]) -> bool {
    let Some(g) = rule.guard else {
        return true;
    };
    let Some(consts) = const_params_for_egraph(eg, rule, widths, vars) else {
        return false;
    };
    let lets = if rule.lets.is_empty() {
        Vec::new()
    } else {
        let ls = crate::rules::eval::eval_lets(rule, widths, &consts);
        if ls.iter().any(Option::is_none) {
            return false;
        }
        ls
    };
    guard_node_holds(eg, rule, g, widths, vars, &consts, &lets) == Some(true)
}

#[derive(Clone)]
struct MatchState {
    todo: Vec<(u16, ClassId)>,
    vars: Vec<Option<ClassId>>,
    widths: Vec<Option<u16>>,
    deferred_widths: Vec<(WExpr, i64)>,
    deferred_lits: Vec<(u16, ClassId)>,
}

pub(crate) type MatchFn<'a> = &'a mut dyn FnMut(&mut EGraph, &[u16], &[ClassId]) -> bool;

/// Every match of side `dir` of `id` at class `c`, except those `skip` names; at most `limit`
/// more are appended, and the search stops as soon as it has them.
#[allow(clippy::too_many_arguments)]
pub(crate) fn ematch_identity(
    eg: &mut EGraph,
    id: &Identity,
    dir: usize,
    c: ClassId,
    max_width: u16,
    out: &mut Vec<MatchOut>,
    limit: usize,
    skip: MatchFn<'_>,
    m: &mut Meter<'_>,
) -> Result<(), Halt> {
    let p = &id.sides[dir];
    let st = MatchState {
        todo: vec![(p.root, c)],
        vars: vec![None; id.vars],
        widths: vec![None; id.rule.width_vars.len()],
        deferred_widths: Vec::new(),
        deferred_lits: Vec::new(),
    };
    seq(
        eg,
        Some(&id.rule),
        p,
        st,
        max_width,
        &mut |eg, ws, b| {
            if skip(eg, ws, b) {
                return true;
            }
            if out.len() < limit {
                out.push(MatchOut {
                    widths: ws.to_vec(),
                    vars: b.to_vec(),
                });
            }
            out.len() < limit
        },
        m,
    )
    .map(|_| ())
}

/// Standalone single-width pattern matcher (for unit tests without a `Rule`).
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn ematch(
    eg: &mut EGraph,
    p: &Pattern,
    vars: usize,
    c: ClassId,
    w: Width,
    out: &mut Vec<Vec<ClassId>>,
    limit: usize,
    skip: &mut dyn FnMut(&mut EGraph, &[ClassId]) -> bool,
    m: &mut Meter<'_>,
) -> Result<(), Halt> {
    let st = MatchState {
        todo: vec![(p.root, c)],
        vars: vec![None; vars],
        widths: vec![Some(w.bits())],
        deferred_widths: Vec::new(),
        deferred_lits: Vec::new(),
    };
    seq(
        eg,
        None,
        p,
        st,
        Width::MAX_BITS,
        &mut |eg, _, b| {
            if skip(eg, b) {
                return true;
            }
            if out.len() < limit {
                out.push(b.to_vec());
            }
            out.len() < limit
        },
        m,
    )
    .map(|_| ())
}

fn seq(
    eg: &mut EGraph,
    rule: Option<&Rule>,
    p: &Pattern,
    mut st: MatchState,
    max_width: u16,
    k: MatchFn<'_>,
    m: &mut Meter<'_>,
) -> Result<bool, Halt> {
    let Some((pn, c)) = st.todo.pop() else {
        if !st.deferred_widths.is_empty() {
            return Ok(true);
        }
        let mut ws = Vec::with_capacity(st.widths.len());
        for w in &st.widths {
            let Some(w) = *w else { return Ok(true) };
            if w == 0 || w > max_width {
                return Ok(true);
            }
            ws.push(w);
        }
        if let Some(r) = rule
            && !crate::rules::eval::admitted(r, &ws)
        {
            return Ok(true);
        }
        for &(lpn, lc) in &st.deferred_lits {
            let POp::Lit(l) = &p.nodes[lpn as usize].op else {
                return Ok(true);
            };
            let cw = eg.classes[lc as usize].width;
            let Some(v) = crate::rules::eval::literal(l, cw, &ws) else {
                return Ok(true);
            };
            if eg.classes[lc as usize].konst != Some(v) {
                return Ok(true);
            }
        }
        let binding: Vec<ClassId> = st.vars.iter().map(|x| x.unwrap_or(0)).collect();
        if let Some(r) = rule
            && !guard_holds_egraph(eg, r, &ws, &binding)
        {
            return Ok(true);
        }
        return Ok(k(eg, &ws, &binding));
    };
    m.charge(Counter::EqsatWork, 1)?;
    let c = eg.find(c);
    let cw = eg.classes[c as usize].width.bits();
    let pnode = &p.nodes[pn as usize];
    if !bind_width(
        &mut st.widths,
        &mut st.deferred_widths,
        &pnode.width,
        i64::from(cw),
        max_width,
    ) {
        return Ok(true);
    }
    match &pnode.op {
        POp::Var(v) => {
            let v = *v as usize;
            if let Some(r) = rule
                && r.params[v].kind == ParamKind::Const
                && eg.classes[c as usize].konst.is_none()
            {
                return Ok(true);
            }
            match st.vars[v] {
                Some(x) => {
                    if eg.find(x) == c {
                        return seq(eg, rule, p, st, max_width, k, m);
                    }
                }
                None => {
                    st.vars[v] = Some(c);
                    return seq(eg, rule, p, st, max_width, k, m);
                }
            }
        }
        POp::Let(_) => {}
        POp::Lit(_) => {
            if eg.classes[c as usize].konst.is_some() {
                st.deferred_lits.push((pn, c));
                return seq(eg, rule, p, st, max_width, k, m);
            }
        }
        POp::Un(op, a) => {
            let (op, a) = (*op, *a);
            let candidates: Vec<ENode> = eg.classes[c as usize]
                .nodes
                .iter()
                .map(|&i| eg.nodes[i as usize])
                .filter(|n| n.op == EOp::Un(op))
                .collect();
            for n in candidates {
                let mut next = st.clone();
                next.todo.push((a, n.kids[0]));
                if !seq(eg, rule, p, next, max_width, k, m)? {
                    return Ok(false);
                }
            }
        }
        POp::Bin(op, x, y) => {
            let (op, x, y) = (*op, *x, *y);
            let candidates: Vec<ENode> = eg.classes[c as usize]
                .nodes
                .iter()
                .map(|&i| eg.nodes[i as usize])
                .filter(|n| n.op == EOp::Bin(op))
                .collect();
            let comm = matches!(
                op,
                BinOp::Add | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor
            );
            for n in candidates {
                let orders = [(n.kids[0], n.kids[1]), (n.kids[1], n.kids[0])];
                let tries = if comm && n.kids[0] != n.kids[1] { 2 } else { 1 };
                for &(l, r) in &orders[..tries] {
                    let mut next = st.clone();
                    next.todo.push((y, r));
                    next.todo.push((x, l));
                    if !seq(eg, rule, p, next, max_width, k, m)? {
                        return Ok(false);
                    }
                }
            }
        }
        POp::Cmp(op, x, y) => {
            let (op, x, y) = (*op, *x, *y);
            let candidates: Vec<ENode> = eg.classes[c as usize]
                .nodes
                .iter()
                .map(|&i| eg.nodes[i as usize])
                .filter(|n| n.op == EOp::Cmp(op))
                .collect();
            let comm = matches!(op, CmpOp::Eq | CmpOp::Ne);
            for n in candidates {
                let orders = [(n.kids[0], n.kids[1]), (n.kids[1], n.kids[0])];
                let tries = if comm && n.kids[0] != n.kids[1] { 2 } else { 1 };
                for &(l, r) in &orders[..tries] {
                    let mut next = st.clone();
                    next.todo.push((y, r));
                    next.todo.push((x, l));
                    if !seq(eg, rule, p, next, max_width, k, m)? {
                        return Ok(false);
                    }
                }
            }
        }
        POp::Zext(a) => {
            let a = *a;
            let candidates: Vec<ENode> = eg.classes[c as usize]
                .nodes
                .iter()
                .map(|&i| eg.nodes[i as usize])
                .filter(|n| n.op == EOp::Zext(cw))
                .collect();
            for n in candidates {
                let mut next = st.clone();
                next.todo.push((a, n.kids[0]));
                if !seq(eg, rule, p, next, max_width, k, m)? {
                    return Ok(false);
                }
            }
        }
        POp::Sext(a) => {
            let a = *a;
            let candidates: Vec<ENode> = eg.classes[c as usize]
                .nodes
                .iter()
                .map(|&i| eg.nodes[i as usize])
                .filter(|n| n.op == EOp::Sext(cw))
                .collect();
            for n in candidates {
                let mut next = st.clone();
                next.todo.push((a, n.kids[0]));
                if !seq(eg, rule, p, next, max_width, k, m)? {
                    return Ok(false);
                }
            }
        }
        POp::Extract { lo, src } => {
            let (lo, src) = (lo.clone(), *src);
            let candidates: Vec<(ENode, u16)> = eg.classes[c as usize]
                .nodes
                .iter()
                .map(|&i| eg.nodes[i as usize])
                .filter_map(|n| match n.op {
                    EOp::Extract { lo: nlo, width } if width == cw => Some((n, nlo)),
                    _ => None,
                })
                .collect();
            for (n, nlo) in candidates {
                let mut next = st.clone();
                if !bind_width(
                    &mut next.widths,
                    &mut next.deferred_widths,
                    &lo,
                    i64::from(nlo),
                    max_width,
                ) {
                    continue;
                }
                next.todo.push((src, n.kids[0]));
                if !seq(eg, rule, p, next, max_width, k, m)? {
                    return Ok(false);
                }
            }
        }
        POp::Concat(h, l) => {
            let (h, l) = (*h, *l);
            let candidates: Vec<ENode> = eg.classes[c as usize]
                .nodes
                .iter()
                .map(|&i| eg.nodes[i as usize])
                .filter(|n| n.op == EOp::Concat)
                .collect();
            for n in candidates {
                let mut next = st.clone();
                next.todo.push((l, n.kids[1]));
                next.todo.push((h, n.kids[0]));
                if !seq(eg, rule, p, next, max_width, k, m)? {
                    return Ok(false);
                }
            }
        }
        POp::Select(cond, t, f) => {
            let (cond, t, f) = (*cond, *t, *f);
            let candidates: Vec<ENode> = eg.classes[c as usize]
                .nodes
                .iter()
                .map(|&i| eg.nodes[i as usize])
                .filter(|n| n.op == EOp::Select)
                .collect();
            for n in candidates {
                let mut next = st.clone();
                next.todo.push((f, n.kids[2]));
                next.todo.push((t, n.kids[1]));
                next.todo.push((cond, n.kids[0]));
                if !seq(eg, rule, p, next, max_width, k, m)? {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}

/// Builds side `dir` of `id` under `(widths, b)`; its class.
pub(crate) fn instantiate(
    eg: &mut EGraph,
    id: &Identity,
    dir: usize,
    widths: &[u16],
    b: &[ClassId],
    max_width: u16,
    m: &mut Meter<'_>,
) -> Result<Option<ClassId>, Halt> {
    let p = &id.sides[dir];
    let lets = if id.rule.lets.is_empty() {
        Vec::new()
    } else {
        let Some(consts) = const_params_for_egraph(eg, &id.rule, widths, b) else {
            return Ok(None);
        };
        let ls = crate::rules::eval::eval_lets(&id.rule, widths, &consts);
        if ls.iter().any(Option::is_none) {
            return Ok(None);
        }
        ls
    };
    let mut at: Vec<ClassId> = Vec::with_capacity(p.nodes.len());
    for pn in &p.nodes {
        let w_val = pn.width.eval(widths);
        if !(1..=i64::from(max_width)).contains(&w_val) {
            return Ok(None);
        }
        let Ok(nw) = Width::new(w_val as u16) else {
            return Ok(None);
        };
        let c = match &pn.op {
            POp::Var(v) => b[*v as usize],
            POp::Let(i) => {
                let Some(v) = lets.get(*i as usize).copied().flatten() else {
                    return Ok(None);
                };
                let node = eg.const_node(v);
                eg.add(node, false, m)?
            }
            POp::Lit(l) => {
                let Some(v) = crate::rules::eval::literal(l, nw, widths) else {
                    return Ok(None);
                };
                let node = eg.const_node(v);
                eg.add(node, false, m)?
            }
            POp::Un(op, a) => {
                if *op == UnOp::Bswap && !nw.bits().is_multiple_of(8) {
                    return Ok(None);
                }
                eg.add(
                    ENode {
                        op: EOp::Un(*op),
                        kids: [at[*a as usize], 0, 0],
                    },
                    false,
                    m,
                )?
            }
            POp::Bin(op, x, y) => eg.add(
                ENode {
                    op: EOp::Bin(*op),
                    kids: [at[*x as usize], at[*y as usize], 0],
                },
                false,
                m,
            )?,
            POp::Cmp(op, x, y) => eg.add(
                ENode {
                    op: EOp::Cmp(*op),
                    kids: [at[*x as usize], at[*y as usize], 0],
                },
                false,
                m,
            )?,
            POp::Zext(a) => {
                let ka = at[*a as usize];
                let rka = eg.find(ka);
                let aw = eg.classes[rka as usize].width.bits();
                if nw.bits() == aw {
                    ka
                } else if nw.bits() < aw {
                    return Ok(None);
                } else {
                    eg.add(
                        ENode {
                            op: EOp::Zext(nw.bits()),
                            kids: [ka, 0, 0],
                        },
                        false,
                        m,
                    )?
                }
            }
            POp::Sext(a) => {
                let ka = at[*a as usize];
                let rka = eg.find(ka);
                let aw = eg.classes[rka as usize].width.bits();
                if nw.bits() == aw {
                    ka
                } else if nw.bits() < aw {
                    return Ok(None);
                } else {
                    eg.add(
                        ENode {
                            op: EOp::Sext(nw.bits()),
                            kids: [ka, 0, 0],
                        },
                        false,
                        m,
                    )?
                }
            }
            POp::Extract { lo, src } => {
                let ka = at[*src as usize];
                let rka = eg.find(ka);
                let aw = eg.classes[rka as usize].width.bits();
                let Ok(lo_val) = u16::try_from(lo.eval(widths)) else {
                    return Ok(None);
                };
                if u32::from(lo_val) + u32::from(nw.bits()) > u32::from(aw) {
                    return Ok(None);
                }
                if lo_val == 0 && nw.bits() == aw {
                    ka
                } else {
                    eg.add(
                        ENode {
                            op: EOp::Extract {
                                lo: lo_val,
                                width: nw.bits(),
                            },
                            kids: [ka, 0, 0],
                        },
                        false,
                        m,
                    )?
                }
            }
            POp::Concat(h, l) => {
                let kh = at[*h as usize];
                let kl = at[*l as usize];
                let rkh = eg.find(kh);
                let rkl = eg.find(kl);
                let sum = u32::from(eg.classes[rkh as usize].width.bits())
                    + u32::from(eg.classes[rkl as usize].width.bits());
                if sum != u32::from(nw.bits()) || sum > u32::from(max_width) {
                    return Ok(None);
                }
                eg.add(
                    ENode {
                        op: EOp::Concat,
                        kids: [kh, kl, 0],
                    },
                    false,
                    m,
                )?
            }
            POp::Select(cond, t, f) => eg.add(
                ENode {
                    op: EOp::Select,
                    kids: [at[*cond as usize], at[*t as usize], at[*f as usize]],
                },
                false,
                m,
            )?,
        };
        at.push(c);
    }
    Ok(at.get(p.root as usize).copied())
}
