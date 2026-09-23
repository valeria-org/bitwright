//! Admitted identities as e-patterns, e-matching, and instantiation.

use super::egraph::{ClassId, EGraph, ENode, EOp, Halt};
use crate::BitVec;
use crate::engine::budget::{Counter, Meter};
use crate::ops::{BinOp, UnOp};
use crate::rules::{Literal, NodeId, RNode, Rule, RuleKind, Sort};

/// A pattern node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum PNode {
    Var(u16),
    Lit(Literal),
    Un(UnOp, u16),
    Bin(BinOp, u16, u16),
}

/// One side of an identity, width-generic (literals are resolved at the graph's width).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Pattern {
    pub(crate) nodes: Vec<PNode>,
    pub(crate) root: u16,
}

/// An admitted equation: an identity (used in both directions), or a guard-free rule (used in
/// its authored direction only, since its right side may drop variables).
#[derive(Clone, Debug)]
pub(crate) struct Identity {
    pub(crate) sides: [Pattern; 2],
    pub(crate) vars: usize,
    pub(crate) bidirectional: bool,
}

/// The operators the conservative fragment admits.
pub(crate) fn admitted_bin(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor
    )
}

pub(crate) fn admitted_un(op: UnOp) -> bool {
    matches!(op, UnOp::Neg | UnOp::Not)
}

fn side(rule: &Rule, root: NodeId) -> Result<Pattern, String> {
    let mut nodes: Vec<PNode> = Vec::new();
    let mut map: Vec<Option<u16>> = vec![None; rule.nodes.len()];
    let mut stack: Vec<(NodeId, bool)> = vec![(root, false)];
    while let Some((n, expanded)) = stack.pop() {
        if map[n as usize].is_some() {
            continue;
        }
        let node = &rule.nodes[n as usize];
        let kids: Vec<NodeId> = match node {
            RNode::Un(_, a) => vec![*a],
            RNode::Bin(_, a, b) => vec![*a, *b],
            _ => vec![],
        };
        if !expanded && !kids.is_empty() {
            stack.push((n, true));
            for k in kids {
                stack.push((k, false));
            }
            continue;
        }
        let at = |k: NodeId| map[k as usize].ok_or_else(|| "unexpected order".to_string());
        let p = match node {
            RNode::Param(i) => PNode::Var(*i),
            RNode::Lit(l) => PNode::Lit(l.clone()),
            RNode::Un(op, a) if admitted_un(*op) => PNode::Un(*op, at(*a)?),
            RNode::Bin(op, a, b) if admitted_bin(*op) => PNode::Bin(*op, at(*a)?, at(*b)?),
            other => return Err(format!("operator outside the fragment: {other:?}")),
        };
        map[n as usize] = Some(nodes.len() as u16);
        nodes.push(p);
    }
    let root = map[root as usize].ok_or_else(|| "empty side".to_string())?;
    Ok(Pattern { nodes, root })
}

/// Compiles a rule into an identity, or says why it is not admitted.
pub(crate) fn admit(rule: &Rule, proven: bool) -> Result<Identity, String> {
    if rule.kind == RuleKind::Rewrite
        && rule
            .params
            .iter()
            .any(|p| p.kind != crate::rules::ParamKind::Any)
    {
        return Err("a rule with capture kinds (const, sym, nonconst) is not an equation".into());
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
    // Homogeneous: every node has the one width.
    let w = crate::rules::WExpr::var(0);
    if rule
        .sorts
        .iter()
        .any(|s| !matches!(s, Sort::Bv(e) if *e == w))
    {
        return Err("not homogeneous in its width".into());
    }
    Ok(Identity {
        sides: [side(rule, rule.lhs)?, side(rule, rule.rhs)?],
        vars: rule.params.len(),
        bidirectional: rule.kind == RuleKind::Identity,
    })
}

/// The value of a literal at the graph's width, if it is representable there.
fn lit(l: &Literal, w: crate::Width) -> Option<BitVec> {
    crate::rules::eval::literal(l, w, &[w.bits()])
}

/// Every match of `p` at class `c`, as variable bindings, except those `skip` names; at most
/// `limit` more are appended, and the search stops as soon as it has them.
#[allow(clippy::too_many_arguments)]
pub(crate) fn ematch(
    eg: &mut EGraph,
    p: &Pattern,
    vars: usize,
    c: ClassId,
    w: crate::Width,
    out: &mut Vec<Vec<ClassId>>,
    limit: usize,
    skip: &mut dyn FnMut(&mut EGraph, &[ClassId]) -> bool,
    m: &mut Meter<'_>,
) -> Result<(), Halt> {
    let mut b: Vec<Option<ClassId>> = vec![None; vars];
    go(
        eg,
        p,
        p.root,
        c,
        w,
        &mut b,
        &mut |eg, b| {
            let binding: Vec<ClassId> = b.iter().map(|x| x.unwrap_or(0)).collect();
            if skip(eg, &binding) {
                return true;
            }
            if out.len() < limit {
                out.push(binding);
            }
            out.len() < limit
        },
        m,
    )
    .map(|_| ())
}

/// Matches node `pn` of `p` at class `c` under bindings `b`; calls `k` for every completion
/// until it returns `false`. Whether to go on.
#[allow(clippy::too_many_arguments)]
fn go(
    eg: &mut EGraph,
    p: &Pattern,
    pn: u16,
    c: ClassId,
    w: crate::Width,
    b: &mut Vec<Option<ClassId>>,
    k: &mut dyn FnMut(&mut EGraph, &[Option<ClassId>]) -> bool,
    m: &mut Meter<'_>,
) -> Result<bool, Halt> {
    // Matching whole patterns is done by `seq`, which threads the remaining pairs.
    seq(eg, p, &mut vec![(pn, c)], w, b, k, m)
}

#[allow(clippy::too_many_arguments)]
fn seq(
    eg: &mut EGraph,
    p: &Pattern,
    todo: &mut Vec<(u16, ClassId)>,
    w: crate::Width,
    b: &mut Vec<Option<ClassId>>,
    k: &mut dyn FnMut(&mut EGraph, &[Option<ClassId>]) -> bool,
    m: &mut Meter<'_>,
) -> Result<bool, Halt> {
    let Some((pn, c)) = todo.pop() else {
        return Ok(k(eg, b));
    };
    m.charge(Counter::EqsatWork, 1)?;
    let c = eg.find(c);
    match &p.nodes[pn as usize] {
        PNode::Var(v) => {
            let v = *v as usize;
            match b[v] {
                Some(x) => {
                    if eg.find(x) == c {
                        return seq(eg, p, todo, w, b, k, m);
                    }
                }
                None => {
                    b[v] = Some(c);
                    let go_on = seq(eg, p, todo, w, b, k, m);
                    b[v] = None;
                    return go_on;
                }
            }
        }
        PNode::Lit(l) => {
            if let Some(v) = lit(l, w)
                && eg.classes[c as usize].konst == Some(v)
            {
                return seq(eg, p, todo, w, b, k, m);
            }
        }
        PNode::Un(op, a) => {
            let (op, a) = (*op, *a);
            let candidates: Vec<ENode> = eg.classes[c as usize]
                .nodes
                .iter()
                .map(|&i| eg.nodes[i as usize])
                .filter(|n| n.op == EOp::Un(op))
                .collect();
            for n in candidates {
                let mut t = todo.clone();
                t.push((a, n.kids[0]));
                if !seq(eg, p, &mut t, w, b, k, m)? {
                    return Ok(false);
                }
            }
        }
        PNode::Bin(op, x, y) => {
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
                let orders: &[(ClassId, ClassId)] =
                    &[(n.kids[0], n.kids[1]), (n.kids[1], n.kids[0])];
                let tries = if comm && n.kids[0] != n.kids[1] { 2 } else { 1 };
                for &(l, r) in &orders[..tries] {
                    let mut t = todo.clone();
                    t.push((y, r));
                    t.push((x, l));
                    if !seq(eg, p, &mut t, w, b, k, m)? {
                        return Ok(false);
                    }
                }
            }
        }
    }
    Ok(true)
}

/// Builds side `p` under bindings `b`; its class.
pub(crate) fn instantiate(
    eg: &mut EGraph,
    p: &Pattern,
    b: &[ClassId],
    w: crate::Width,
    m: &mut Meter<'_>,
) -> Result<Option<ClassId>, Halt> {
    let mut at: Vec<ClassId> = Vec::with_capacity(p.nodes.len());
    for pn in &p.nodes {
        let c = match pn {
            PNode::Var(v) => b[*v as usize],
            PNode::Lit(l) => {
                let Some(v) = lit(l, w) else {
                    return Ok(None);
                };
                eg.add(
                    ENode {
                        op: EOp::Const(v),
                        kids: [0, 0],
                    },
                    false,
                    m,
                )?
            }
            PNode::Un(op, a) => eg.add(
                ENode {
                    op: EOp::Un(*op),
                    kids: [at[*a as usize], 0],
                },
                false,
                m,
            )?,
            PNode::Bin(op, x, y) => eg.add(
                ENode {
                    op: EOp::Bin(*op),
                    kids: [at[*x as usize], at[*y as usize]],
                },
                false,
                m,
            )?,
        };
        at.push(c);
    }
    Ok(at.get(p.root as usize).copied())
}
