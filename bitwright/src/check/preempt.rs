//! Preempted rules: instances of a rule's pattern that the engine never lets the rule see.
//!
//! The engine rewrites bottom up, so a rule whose pattern contains a subterm that another rule
//! or a normal-form pass rewrites first (a mask moved below a shift, `2·x` spelled `x << 1`,
//! …) does not fire on that instance: its pattern is written against a spelling the
//! engine does not keep. Each such rule is a critical pair that does not join, and the fix is
//! to write the pattern in the form the engine produces.
//!
//! [`preempted`] finds them by instantiating each pattern (symbols for its parameters, then
//! each non-constant parameter in turn a constant, over a few constant values and widths) and
//! simplifying both the instance and the rule's result at it: when the rule's result
//! simplifies to something strictly smaller than the instance does, the engine lost the rule
//! there ([`PreemptionKind::Lost`]). A rule the engine never applies on any instance it
//! applies to, with nothing lost, is dead weight: another rule or a pass always gets there
//! first ([`PreemptionKind::Shadowed`]).

use core::fmt;

use super::{Rng, biased, steer};
use crate::engine::{By, Engine, Event, Observer, Run};
use crate::ops::CmpOpExt;
use crate::rules::eval::{Val, admitted, eval, eval_lets};
use crate::rules::{NodeId, ParamKind, RNode, Rule, RuleKind, RuleProgram};
use crate::{BitVec, Width};
use crate::{Bounded, Context};

/// What the engine does instead of a rule.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PreemptionKind {
    /// At some instance, something else rewrites first and the result is larger than the
    /// rule's: the pattern is written in a spelling the engine does not keep.
    Lost,
    /// At every instance tried, something else rewrites first and reaches what the rule would:
    /// the rule never fires, and can go (or be written for what the engine misses).
    Shadowed,
}

/// An instance of a rule's pattern the engine takes elsewhere.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Preemption {
    /// `group::rule`.
    pub rule: String,
    /// Whether the rule's result is lost there, or only reached another way.
    pub kind: PreemptionKind,
    /// The instance (parameters are `$name` symbols or constants).
    pub input: String,
    /// What the engine makes of the rule's result at the instance.
    pub expected: String,
    /// What the engine makes of the instance.
    pub got: String,
    /// The first rewrite the engine made of the instance: what made it (`group::rule` or a
    /// pass), the node and its replacement.
    pub first: Option<(String, String, String)>,
}

impl fmt::Display for Preemption {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            PreemptionKind::Lost => write!(
                f,
                "{}: `{}` simplifies to `{}`, but the rule would give `{}`",
                self.rule, self.input, self.got, self.expected
            )?,
            PreemptionKind::Shadowed => write!(
                f,
                "{}: never fires; the engine takes every instance tried elsewhere (`{}` \
                 simplifies to `{}` without it)",
                self.rule, self.input, self.got
            )?,
        }
        if let Some((by, before, after)) = &self.first {
            write!(f, " (`{by}` rewrites `{before}` to `{after}` first)")?;
        }
        Ok(())
    }
}

/// The rewrites of one run, in order.
#[derive(Default)]
struct Rewrites(Vec<(String, crate::Expr, crate::Expr)>);

impl Observer for Rewrites {
    fn event(&mut self, event: Event<'_>) {
        if let Event::Applied { by, before, after } = event {
            let name = match by {
                By::Rule(r) => r.name.clone(),
                other => other.name().to_string(),
            };
            self.0.push((name, before, after));
        }
    }
}

/// The widths assignments tried per rule: up to two with every width in 4..=16, else the
/// first admitted one.
fn assignments(rule: &Rule) -> Vec<Vec<u16>> {
    let (mut small, mut first): (Vec<Vec<u16>>, Vec<Vec<u16>>) = (Vec::new(), Vec::new());
    crate::rules::compile::for_each_assignment(rule, |ws| {
        if admitted(rule, ws) {
            let widths = &ws[..rule.width_vars.len()];
            if small.len() < 2 && widths.iter().all(|&w| (4..=16).contains(&w)) {
                small.push(ws.to_vec());
            }
            if first.is_empty() {
                first.push(ws.to_vec());
            }
        }
        small.len() < 2
    });
    if small.is_empty() { first } else { small }
}

/// Constant values tried for a parameter of width `w`.
fn values(w: Width) -> Vec<BitVec> {
    let mut v = vec![
        BitVec::wrapping_from_u64(w, 3),
        BitVec::one(w),
        BitVec::ones(w),
        BitVec::smin(w),
        BitVec::wrapping_from_u64(w, 2),
        BitVec::wrapping_from_u64(w, 0x5a),
    ];
    v.dedup();
    v
}

/// Sets each parameter a guard conjunct `p == e` names to the value of `e`, so that guards
/// relating constants (`m == c << 1`) hold. Best effort, after [`steer`](super::steer).
fn solve_equalities(rule: &Rule, widths: &[u16], params: &mut [BitVec]) {
    let Some(g) = rule.guard else {
        return;
    };
    let mut eqs = Vec::new();
    let mut stack = vec![g];
    while let Some(n) = stack.pop() {
        match &rule.nodes[n as usize] {
            RNode::And(a, b) => stack.extend([*a, *b]),
            RNode::Cmp(CmpOpExt::Eq, a, b) => eqs.push((*a, *b)),
            _ => {}
        }
    }
    let param = |n: NodeId| match rule.nodes[n as usize] {
        RNode::Param(i) => Some(usize::from(i)),
        _ => None,
    };
    for _ in 0..2 {
        for &(a, b) in &eqs {
            let (i, e) = match (param(a), param(b)) {
                (Some(i), _) => (i, b),
                (_, Some(i)) => (i, a),
                _ => continue,
            };
            let lets = eval_lets(rule, widths, params);
            if let Some(v) = eval(rule, e, widths, params, &lets).and_then(Val::bv)
                && v.width() == params[i].width()
            {
                params[i] = v;
            }
        }
    }
}

/// The instances of `rule` tried at `widths`: parameter values, `None` for a symbol. Constant
/// parameters take values steered toward the guard; then each parameter that may be anything
/// is in turn a constant too.
fn instances(rule: &Rule, widths: &[u16]) -> Option<Vec<Vec<Option<BitVec>>>> {
    let pw: Vec<Width> = rule
        .params
        .iter()
        .map(|p| {
            u16::try_from(p.width.eval(widths))
                .ok()
                .and_then(|w| Width::new(w).ok())
        })
        .collect::<Option<_>>()?;
    let mut rng = Rng(0x7072_6565_6d70);
    let mut out = Vec::new();
    for k in 0..12usize {
        // Fixed values first (shifted per constant parameter, so those differ), then random
        // ones; each as drawn and steered toward the guard.
        let drawn: Vec<BitVec> = pw
            .iter()
            .zip(&rule.params)
            .enumerate()
            .map(|(i, (&w, p))| {
                let vs = values(w);
                let shift = if p.kind == ParamKind::Const { i } else { 0 };
                if k < vs.len() {
                    vs[(k + shift) % vs.len()]
                } else {
                    biased(&mut rng, w)
                }
            })
            .collect();
        let mut steered = drawn.clone();
        steer(rule, widths, &mut steered, &mut rng);
        solve_equalities(rule, widths, &mut steered);
        for full in [drawn, steered] {
            let base: Vec<Option<BitVec>> = rule
                .params
                .iter()
                .zip(&full)
                .map(|(p, v)| (p.kind == ParamKind::Const).then_some(*v))
                .collect();
            out.push(base.clone());
            for (j, p) in rule.params.iter().enumerate() {
                if p.kind == ParamKind::Any {
                    let mut v = base.clone();
                    v[j] = Some(full[j]);
                    out.push(v);
                }
            }
        }
    }
    Some(out)
}

/// `e` on one line (a `let` prints one binding per line).
fn show(cx: &Context, e: crate::Expr) -> String {
    cx.display(e).to_string().replace('\n', " ")
}

fn size(cx: &mut Context, e: crate::Expr) -> u32 {
    match cx.dag_size(&[e], 10_000) {
        Ok(Bounded::Exact(n)) | Ok(Bounded::AtLeast(n)) => n,
        Err(_) => u32::MAX,
    }
}

/// The rules of `program` that `engine` preempts: at most one finding per rule, an instance it
/// simplifies to something larger than the rule's own result would simplify to
/// ([`PreemptionKind::Lost`], the first found), or else, when the engine applies the rule to
/// none of the instances the rule applies to, the first of those
/// ([`PreemptionKind::Shadowed`]). `engine` must link the program's groups. Rules for floats
/// as values and identities the directed engine does not use are skipped.
pub fn preempted(engine: &Engine, program: &RuleProgram) -> Vec<Preemption> {
    let rules = program.rules();
    let threads = std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .min(rules.len().max(1));
    let chunk = rules.len().div_ceil(threads.max(1)).max(1);
    let mut out = Vec::new();
    std::thread::scope(|s| {
        let mut handles = Vec::new();
        for part in rules.chunks(chunk) {
            let work = move || {
                part.iter()
                    .filter_map(|r| preempted_rule(engine, r))
                    .collect::<Vec<_>>()
            };
            match crate::threads::builder().spawn_scoped(s, work) {
                Ok(h) => handles.push(h),
                Err(_) => out.extend(part.iter().filter_map(|r| preempted_rule(engine, r))),
            }
        }
        for h in handles {
            match h.join() {
                Ok(v) => out.extend(v),
                Err(p) => std::panic::resume_unwind(p),
            }
        }
    });
    out
}

/// [`preempted`] for one rule.
pub fn preempted_rule(engine: &Engine, rule: &Rule) -> Option<Preemption> {
    if rule.float_values || (rule.kind == RuleKind::Identity && !rule.decreasing) {
        return None;
    }
    // The first instance the rule applies to, while the engine has applied it to none.
    let mut shadowed: Option<Preemption> = None;
    let mut fired = false;
    for ws in assignments(rule) {
        for values in instances(rule, &ws)? {
            let mut cx = Context::new();
            let Some(t) = crate::rules::matcher::build_instance(&mut cx, rule, &ws, &values) else {
                continue;
            };
            let Some(r) = crate::rules::apply::try_apply(&mut cx, rule, t) else {
                continue;
            };
            if r == t {
                continue;
            }
            let (t, r) = (cx.handle(t), cx.handle(r));
            let mut seen = Rewrites::default();
            let Ok(got) = engine.run(&mut cx, &[t], Run::default().with_observer(&mut seen)) else {
                continue;
            };
            let Ok(expected) = engine.simplify(&mut cx, r) else {
                continue;
            };
            let (got, expected) = (got.roots[0].expr, expected.expr);
            let lost = got != expected && size(&mut cx, expected) < size(&mut cx, got);
            fired |= seen.0.iter().any(|(by, ..)| *by == rule.name);
            if !lost && (fired || shadowed.is_some()) {
                continue;
            }
            let first = seen
                .0
                .first()
                .map(|(by, before, after)| (by.clone(), show(&cx, *before), show(&cx, *after)));
            let finding = Preemption {
                rule: rule.name.clone(),
                kind: if lost {
                    PreemptionKind::Lost
                } else {
                    PreemptionKind::Shadowed
                },
                input: show(&cx, t),
                expected: show(&cx, expected),
                got: show(&cx, got),
                first,
            };
            if lost {
                return Some(finding);
            }
            shadowed = Some(finding);
        }
    }
    shadowed.filter(|_| !fired)
}
