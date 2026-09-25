//! A rule's soundness obligation as an SMT-LIB script, translated from the rule itself (not
//! from expressions built through the canonicalizing constructors, which would put the builder
//! between the rule and the proof).

use core::fmt::Write as _;

use super::export::{App, literal, quotable, sort, term};
use crate::error::Error;
use crate::expr::OpCode;
use crate::rules::eval::{literal as lit_value, width_of};
use crate::rules::ir::{ConstPred, FactPred, NodeId, RNode, Rule, Sort};

/// The obligation of `rule` at `widths` (one per [`Rule::width_vars`], in order, then each of
/// [`Rule::modes`] as its index in [`RoundingMode::ALL`](crate::fp::RoundingMode::ALL)) as a
/// complete QF_BV script (QF_BVFP for a rule with floating-point operations): every parameter
/// is a free constant, and the script asserts the guard (true without one) and that the two
/// sides differ. `unsat` from a solver proves the rule at those
/// widths; with `sat`, the model is a counterexample. Fact predicates read as what they state
/// about values (`zero_bits(x, m)` is `x & m = 0`, `proves(c)` is `c`), which is exactly what
/// makes a guard sound to act on.
///
/// Errors when the rule does not apply at `widths` ([`Rule::admits`]).
pub fn rule_obligation(rule: &Rule, widths: &[u16]) -> Result<String, Error> {
    if !rule.admits(widths) {
        return Err(Error::Unsupported(format!(
            "{} does not apply at these widths",
            rule.name
        )));
    }
    let mut out = String::new();
    let modes = widths[rule.width_vars.len()..]
        .iter()
        .filter_map(|&m| crate::fp::RoundingMode::ALL.get(usize::from(m)));
    let assignment: Vec<String> = rule
        .width_vars
        .iter()
        .zip(widths)
        .map(|(v, w)| format!("{v} = {w}"))
        .chain(
            rule.modes
                .iter()
                .zip(modes)
                .map(|(v, m)| format!("{v} = {}", m.name())),
        )
        .collect();
    let header = format!("; {} at {}\n", rule.name, assignment.join(", "));
    for (k, p) in rule.params.iter().enumerate() {
        let w = u16::try_from(p.width.eval(widths))
            .map_err(|_| Error::Contract("parameter width".into()))?;
        writeln!(out, "(declare-const {} {})", param_name(rule, k), sort(w)).ok();
    }
    let mut roots = vec![rule.lhs, rule.rhs];
    roots.extend(rule.guard);
    for n in post_order(rule, &roots) {
        let body = node(&mut out, rule, n, widths)?;
        let s = match rule.sorts[n as usize] {
            Sort::Bool => "Bool".to_string(),
            Sort::Bv(_) => sort(bv_width(rule, n, widths)?),
        };
        writeln!(out, "(define-fun {} () {s} {body})", name(n)).ok();
    }
    let guard = match rule.guard {
        Some(g) => truthy(rule, g, widths)?,
        None => "true".to_string(),
    };
    writeln!(out, "(assert {guard})").ok();
    let (l, r) = (name(rule.lhs), name(rule.rhs));
    let equal = match rule
        .float_values
        .then(|| rule.values_format(widths))
        .flatten()
    {
        // Equal as floats: equal, or both NaNs (`|x| > ∞` on the encodings).
        Some(f) => {
            let smax = literal(&crate::BitVec::smax(f.width()));
            let inf = literal(&f.inf(false));
            format!(
                "(or (= {l} {r}) (and (bvugt (bvand {l} {smax}) {inf}) (bvugt (bvand {r} {smax}) {inf})))"
            )
        }
        None => format!("(= {l} {r})"),
    };
    writeln!(out, "(assert (not {equal}))\n(check-sat)").ok();
    // QF_BV, or QF_BVFP when the rule has floating-point operations.
    Ok(format!("{header}{}{out}", super::logic(&out)))
}

fn name(n: NodeId) -> String {
    format!("bw!{n}")
}

/// A parameter's name: its own where SMT-LIB can spell it (rule identifiers never contain `!`,
/// so they cannot collide with the node names), else `param!k`.
fn param_name(rule: &Rule, k: usize) -> String {
    let n = &rule.params[k].name;
    if quotable(n) && !n.contains('!') {
        format!("|{n}|")
    } else {
        format!("|param!{k}|")
    }
}

fn bv_width(rule: &Rule, n: NodeId, widths: &[u16]) -> Result<u16, Error> {
    width_of(rule, n, widths)
        .map(|w| w.bits())
        .ok_or_else(|| Error::Contract(format!("node {n} of {} has no width", rule.name)))
}

/// The operands of `n`, with a `let` read through to its value.
fn operands(rule: &Rule, n: NodeId) -> Vec<NodeId> {
    match rule.nodes[n as usize] {
        RNode::Let(i) => rule
            .lets
            .get(usize::from(i))
            .map(|l| l.value)
            .into_iter()
            .collect(),
        ref other => crate::rules::compile::children(other),
    }
}

/// Every node under `roots`, operands first, each once (iterative).
fn post_order(rule: &Rule, roots: &[NodeId]) -> Vec<NodeId> {
    let mut seen = vec![false; rule.nodes.len()];
    let mut out = Vec::new();
    let mut stack: Vec<(NodeId, bool)> = roots.iter().rev().map(|&r| (r, false)).collect();
    while let Some((n, expanded)) = stack.pop() {
        if expanded {
            out.push(n);
            continue;
        }
        if seen[n as usize] {
            continue;
        }
        seen[n as usize] = true;
        stack.push((n, true));
        for c in operands(rule, n).into_iter().rev() {
            if !seen[c as usize] {
                stack.push((c, false));
            }
        }
    }
    out
}

/// `n` as a Boolean: itself if it is one, else "not zero".
fn truthy(rule: &Rule, n: NodeId, widths: &[u16]) -> Result<String, Error> {
    Ok(match rule.sorts[n as usize] {
        Sort::Bool => name(n),
        Sort::Bv(_) => {
            let w = bv_width(rule, n, widths)?;
            format!("(not (= {} {}))", name(n), zero(w))
        }
    })
}

fn zero(w: u16) -> String {
    format!("(_ bv0 {w})")
}

fn one(w: u16) -> String {
    format!("(_ bv1 {w})")
}

fn node(out: &mut String, rule: &Rule, n: NodeId, widths: &[u16]) -> Result<String, Error> {
    let bvw = |m: NodeId| bv_width(rule, m, widths);
    let app = |out: &mut String,
               op: OpCode,
               kids: &[NodeId],
               lo: u32,
               fp: Option<crate::fp::node::Desc>|
     -> Result<String, Error> {
        let args: Vec<String> = kids.iter().map(|&k| name(k)).collect();
        let arg_w: Vec<u16> = kids.iter().map(|&k| bvw(k)).collect::<Result<_, _>>()?;
        let tag = name(n);
        term(
            out,
            op,
            &App {
                tag: &tag,
                w: bvw(n)?,
                args: &args,
                arg_w: &arg_w,
                lo,
                fp,
            },
        )
    };
    Ok(match &rule.nodes[n as usize] {
        RNode::Param(i) => param_name(rule, usize::from(*i)),
        RNode::Let(i) => {
            let v = rule
                .lets
                .get(usize::from(*i))
                .ok_or_else(|| Error::Contract("dangling let".into()))?;
            name(v.value)
        }
        RNode::Lit(l) => {
            let w =
                width_of(rule, n, widths).ok_or_else(|| Error::Contract("literal width".into()))?;
            let v = lit_value(l, w, widths)
                .ok_or_else(|| Error::Contract("literal does not fit".into()))?;
            literal(&v)
        }
        RNode::Un(op, a) => app(out, OpCode::from_un(*op), &[*a], 0, None)?,
        RNode::Bin(op, a, b) => app(out, OpCode::from_bin(*op), &[*a, *b], 0, None)?,
        RNode::Cmp(op, a, b) => {
            let (stored, swap) = op.canonical();
            let kids = if swap { [*b, *a] } else { [*a, *b] };
            app(out, OpCode::from_cmp(stored), &kids, 0, None)?
        }
        RNode::Zext(a) => app(out, OpCode::Zext, &[*a], 0, None)?,
        RNode::Sext(a) => app(out, OpCode::Sext, &[*a], 0, None)?,
        RNode::Extract(lo, a) => {
            let lo = u32::try_from(lo.eval(widths))
                .map_err(|_| Error::Contract("extract offset".into()))?;
            app(out, OpCode::Extract, &[*a], lo, None)?
        }
        RNode::Concat(h, l) => app(out, OpCode::Concat, &[*h, *l], 0, None)?,
        RNode::Select(c, t, f) => app(out, OpCode::Select, &[*c, *t, *f], 0, None)?,
        RNode::Fp(f) => {
            let d = crate::rules::eval::fp_desc(rule, n, f, widths)
                .ok_or_else(|| Error::Contract("floating-point format".into()))?;
            app(out, f.kind.opcode(), &f.args, 0, Some(d))?
        }
        RNode::And(a, b) => format!(
            "(and {} {})",
            truthy(rule, *a, widths)?,
            truthy(rule, *b, widths)?
        ),
        RNode::Or(a, b) => format!(
            "(or {} {})",
            truthy(rule, *a, widths)?,
            truthy(rule, *b, widths)?
        ),
        RNode::Not(a) => format!("(not {})", truthy(rule, *a, widths)?),
        RNode::Fact(p, x, m) => {
            let arg = |k: Option<NodeId>| {
                k.map(name)
                    .ok_or_else(|| Error::Contract("fact predicate operand".into()))
            };
            match p {
                FactPred::Proves => truthy(rule, *x, widths)?,
                FactPred::NonZero => format!("(not (= {} {}))", name(*x), zero(bvw(*x)?)),
                FactPred::ZeroBits | FactPred::Disjoint => {
                    format!("(= (bvand {} {}) {})", name(*x), arg(*m)?, zero(bvw(*x)?))
                }
                FactPred::OneBits => {
                    let m = arg(*m)?;
                    format!("(= (bvand {} {m}) {m})", name(*x))
                }
                FactPred::FpNotNan | FactPred::FpFinite | FactPred::FpNonZero => {
                    let w = bvw(*x)?;
                    let smax = literal(&crate::BitVec::smax(
                        crate::Width::new(w).map_err(|e| Error::Contract(e.to_string()))?,
                    ));
                    let mag = format!("(bvand {} {smax})", name(*x));
                    match p {
                        FactPred::FpNotNan => format!("(bvule {mag} {})", arg(*m)?),
                        FactPred::FpFinite => format!("(bvult {mag} {})", arg(*m)?),
                        _ => format!("(not (= {mag} {}))", zero(w)),
                    }
                }
            }
        }
        RNode::ConstP(p, a) => {
            let (c, w) = (name(*a), bvw(*a)?);
            let nonzero = format!("(not (= {c} {}))", zero(w));
            // A low mask after filling the trailing zeros (for a shifted mask).
            let low_mask = |v: &str| format!("(= (bvand {v} (bvadd {v} {})) {})", one(w), zero(w));
            match p {
                ConstPred::IsPow2 => format!(
                    "(and {nonzero} (= (bvand {c} (bvsub {c} {})) {}))",
                    one(w),
                    zero(w)
                ),
                ConstPred::IsLowMask => format!("(and {nonzero} {})", low_mask(&c)),
                ConstPred::IsShiftedMask => {
                    let filled = format!("(bvor {c} (bvsub {c} {}))", one(w));
                    format!("(and {nonzero} {})", low_mask(&filled))
                }
            }
        }
    })
}
