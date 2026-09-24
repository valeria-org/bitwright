//! Applying a matched rule: guard evaluation from facts, and template instantiation through
//! the canonicalizing builder. The reference implementation the engine uses and is tested
//! against.

use super::eval::{eval, literal, width_of};
use super::ir::{FactPred, NodeId, ParamKind, RNode, Rule};
use super::matcher::{Bindings, Match};
use crate::expr::Context;
use crate::facts::known::bv_and;
use crate::facts::{Assumptions, Facts, Reliance};
use crate::ops::CmpOp;
use crate::{BitVec, Width};

/// Values of the constant parameters (zero for the others, which pure computations never
/// read).
pub(crate) fn const_params(cx: &Context, rule: &Rule, b: &Bindings) -> Option<Vec<BitVec>> {
    let widths = b.width_values()?;
    rule.params
        .iter()
        .zip(&b.params)
        .map(|(p, node)| {
            let node = (*node)?;
            if p.kind == ParamKind::Const {
                cx.const_val(node)
            } else {
                let w = u16::try_from(p.width.eval(&widths)).ok()?;
                Some(BitVec::zero(Width::new(w).ok()?))
            }
        })
        .collect()
}

/// What an application may use, and what it reports back.
#[derive(Default)]
pub(crate) struct ApplyEnv<'a> {
    /// Facts are read under these assumptions.
    pub(crate) assumptions: Option<&'a Assumptions>,
    /// Transfers the application's fact queries may still run together (the caller's remaining
    /// fact budget, decremented as queries run); `None` for the context's own cap per query.
    pub(crate) fact_cap: Option<u32>,
    /// Set when a fact query was needed but `fact_cap` was 0.
    pub(crate) out_of_facts: bool,
    /// Set when an answer was "no" only for lack of work or facts (a capped fact query, a
    /// refused query, the matcher's step budget), so the node may not be normal.
    pub(crate) degraded: bool,
    /// Matcher steps left for this application; decremented as they are used.
    pub(crate) steps: u32,
    /// Set when the pattern matched (so a "no" came from the guard or the template).
    pub(crate) matched: bool,
    /// Set when the guard held (so a "no" came from building the template).
    pub(crate) instantiating: bool,
    /// The constraints the facts read so far relied on.
    pub(crate) rel: Reliance,
}

impl ApplyEnv<'_> {
    pub(crate) fn new() -> Self {
        ApplyEnv {
            steps: super::matcher::MATCH_STEPS,
            ..ApplyEnv::default()
        }
    }
}

/// The facts of an operand of a fact predicate: a bound parameter's facts, or the exact value
/// of a literal or `let`.
#[allow(clippy::too_many_arguments)]
fn operand_facts(
    env: &mut ApplyEnv<'_>,
    cx: &mut Context,
    rule: &Rule,
    b: &Bindings,
    n: NodeId,
    widths: &[u16],
    consts: &[BitVec],
    lets: &[Option<BitVec>],
) -> Option<Facts> {
    match &rule.nodes[n as usize] {
        RNode::Param(i) => {
            let node = b.params[*i as usize]?;
            if let Some(v) = cx.const_val(node) {
                return Some(Facts::constant(&v));
            }
            let cap = env.fact_cap.unwrap_or(u32::MAX);
            if cap == 0 {
                env.degraded = true;
                env.out_of_facts = true;
                return None;
            }
            let e = cx.handle(node);
            let work0 = cx.facts.work;
            let f = operand_query(env, cx, e, cap);
            if let Some(c) = &mut env.fact_cap {
                let used = u32::try_from(cx.facts.work - work0).unwrap_or(u32::MAX);
                *c = c.saturating_sub(used);
            }
            f
        }
        _ => {
            let v = eval(rule, n, widths, consts, lets)?.bv()?;
            Some(Facts::constant(&v))
        }
    }
}

/// One fact query of [`operand_facts`], with at most `cap` transfers.
fn operand_query(
    env: &mut ApplyEnv<'_>,
    cx: &mut Context,
    e: crate::Expr,
    cap: u32,
) -> Option<Facts> {
    match env.assumptions {
        Some(a) => match cx.facts_under_cap(e, a, cap) {
            Ok(Ok((f, r))) => {
                env.rel |= r;
                Some(f)
            }
            // Infeasible assumptions prove anything; the engine proves nothing from them (a
            // final "no", not a lack of work).
            Ok(Err(_)) => None,
            Err(_) => {
                env.degraded = true;
                None
            }
        },
        None => {
            let f = cx.try_facts_cap(e, cap).ok().flatten();
            if f.is_none() {
                env.degraded = true;
            }
            f
        }
    }
}

/// Evaluates the rule's guard. Fact predicates are answered from facts and are true only
/// when provable; pure parts are computed from constant parameters.
pub(crate) fn guard_holds(
    env: &mut ApplyEnv<'_>,
    cx: &mut Context,
    rule: &Rule,
    b: &Bindings,
    consts: &[BitVec],
    lets: &[Option<BitVec>],
) -> bool {
    let Some(g) = rule.guard else {
        return true;
    };
    let Some(widths) = b.width_values() else {
        return false;
    };
    holds(env, cx, rule, b, g, &widths, consts, lets) == Some(true)
}

#[allow(clippy::too_many_arguments)]
fn holds(
    env: &mut ApplyEnv<'_>,
    cx: &mut Context,
    rule: &Rule,
    b: &Bindings,
    n: NodeId,
    widths: &[u16],
    consts: &[BitVec],
    lets: &[Option<BitVec>],
) -> Option<bool> {
    match &rule.nodes[n as usize] {
        RNode::And(x, y) => Some(
            holds(env, cx, rule, b, *x, widths, consts, lets)?
                && holds(env, cx, rule, b, *y, widths, consts, lets)?,
        ),
        RNode::Or(x, y) => Some(
            holds(env, cx, rule, b, *x, widths, consts, lets)?
                || holds(env, cx, rule, b, *y, widths, consts, lets)?,
        ),
        // Only pure conditions can be negated (checked by the compiler).
        RNode::Not(x) => Some(!holds(env, cx, rule, b, *x, widths, consts, lets)?),
        RNode::Fact(p, x, m) => {
            let fx = operand_facts(env, cx, rule, b, *x, widths, consts, lets)?;
            Some(match p {
                FactPred::NonZero => {
                    let z = Facts::constant(&BitVec::zero(fx.width()));
                    crate::facts::decide_cmp(CmpOp::Eq, &fx, &z) == Some(false)
                }
                FactPred::ZeroBits => {
                    let mv = eval(rule, (*m)?, widths, consts, lets)?.bv()?;
                    bv_and(&fx.known().maybe_one(), &mv).is_zero()
                }
                FactPred::OneBits => {
                    let mv = eval(rule, (*m)?, widths, consts, lets)?.bv()?;
                    bv_and(&fx.known().known_one(), &mv) == mv
                }
                FactPred::Disjoint => {
                    let fy = operand_facts(env, cx, rule, b, (*m)?, widths, consts, lets)?;
                    bv_and(&fx.known().maybe_one(), &fy.known().maybe_one()).is_zero()
                }
                FactPred::Proves => {
                    let RNode::Cmp(op, l, r) = &rule.nodes[*x as usize] else {
                        return None;
                    };
                    let (stored, swap) = op.canonical();
                    let (l, r) = if swap { (*r, *l) } else { (*l, *r) };
                    if let (RNode::Param(i), RNode::Param(j)) =
                        (&rule.nodes[l as usize], &rule.nodes[r as usize])
                    {
                        let (x, y) = (b.params[*i as usize]?, b.params[*j as usize]?);
                        // The same bound node on both sides is decided by identity.
                        if x == y {
                            return Some(matches!(stored, CmpOp::Eq | CmpOp::Ule | CmpOp::Sle));
                        }
                        // An assumed ordering of the two decides it too.
                        if let Some(a) = env.assumptions
                            && let Some((v, rel)) = cx.assumed_order(a, stored, x, y)
                        {
                            if v {
                                env.rel |= rel;
                            }
                            return Some(v);
                        }
                    }
                    let fl = operand_facts(env, cx, rule, b, l, widths, consts, lets)?;
                    let fr = operand_facts(env, cx, rule, b, r, widths, consts, lets)?;
                    crate::facts::decide_cmp(stored, &fl, &fr) == Some(true)
                }
            })
        }
        // Pure: constant predicates, comparisons of constants, 1-bit constant values.
        _ => Some(eval(rule, n, widths, consts, lets)?.truthy()),
    }
}

/// Builds the template through the canonicalizing constructors.
pub(crate) fn instantiate(
    cx: &mut Context,
    rule: &Rule,
    b: &Bindings,
    lets: &[Option<BitVec>],
) -> Option<u32> {
    let widths = b.width_values()?;
    build(cx, rule, rule.rhs, &widths, b, lets)
}

fn build(
    cx: &mut Context,
    rule: &Rule,
    n: NodeId,
    widths: &[u16],
    b: &Bindings,
    lets: &[Option<BitVec>],
) -> Option<u32> {
    let w = width_of(rule, n, widths);
    let rec = |cx: &mut Context, m: NodeId| build(cx, rule, m, widths, b, lets);
    Some(match &rule.nodes[n as usize] {
        RNode::Param(i) => b.params[*i as usize]?,
        RNode::Let(i) => cx
            .mk_const(&lets.get(*i as usize).copied().flatten()?)
            .ok()?,
        RNode::Lit(l) => cx.mk_const(&literal(l, w?, widths)?).ok()?,
        RNode::Un(op, a) => {
            let a = rec(cx, *a)?;
            cx.c_un(*op, a).ok()?
        }
        RNode::Bin(op, x, y) => {
            let (x, y) = (rec(cx, *x)?, rec(cx, *y)?);
            cx.c_bin(*op, x, y).ok()?
        }
        RNode::Cmp(op, x, y) => {
            let (x, y) = (rec(cx, *x)?, rec(cx, *y)?);
            let (stored, swap) = op.canonical();
            let (x, y) = if swap { (y, x) } else { (x, y) };
            cx.c_cmp(stored, x, y).ok()?
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

/// Tries `rule` at node `node`: match, guard, template. The replacement node, if it applies.
pub(crate) fn try_apply(cx: &mut Context, rule: &Rule, node: u32) -> Option<u32> {
    try_apply_with(&mut ApplyEnv::new(), cx, rule, node)
}

/// [`try_apply`] under an environment (assumptions, budgets), which records whether a "no"
/// was only for lack of work.
pub(crate) fn try_apply_with(
    env: &mut ApplyEnv<'_>,
    cx: &mut Context,
    rule: &Rule,
    node: u32,
) -> Option<u32> {
    let b = match super::matcher::match_rule_steps(cx, rule, node, &mut env.steps) {
        Match::Yes(b) => {
            env.matched = true;
            b
        }
        Match::No => return None,
        Match::OutOfSteps => {
            env.degraded = true;
            return None;
        }
    };
    let consts = const_params(cx, rule, &b)?;
    let widths = b.width_values()?;
    let lets = super::eval::eval_lets(rule, &widths, &consts);
    if lets.iter().any(Option::is_none) && !rule.lets.is_empty() {
        return None;
    }
    if !guard_holds(env, cx, rule, &b, &consts, &lets) {
        return None;
    }
    env.instantiating = true;
    instantiate(cx, rule, &b, &lets)
}
