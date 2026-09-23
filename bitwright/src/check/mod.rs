//! The soundness checker: evidence that every rule is a valid rewrite, and the proof ledger.
//!
//! **Obligation.** For every width assignment satisfying the rule's constraints at which the
//! pattern can match, and every value of the parameters: if the guard holds, the pattern and
//! the template evaluate to the same value. Guards may only talk about facts through positive
//! proof predicates (`proves`, `zero_bits`, `one_bits`, `nonzero`, `disjoint`), which are
//! monotone in fact precision; so evaluating them on the concrete values (the most precise
//! facts possible) proves the rule sound for every sound fact engine.
//!
//! **Evidence** is derived, never declared: exhaustive enumeration over every width
//! assignment up to `max_exhaustive_width` whose parameter space fits in
//! `max_exhaustive_bits`, plus boundary-biased random sampling at wide widths, half of it
//! steered toward values that satisfy the guard.
//!
//! This is testing, not proof: above the exhaustive widths a rule is only sampled. A verdict
//! of [`Verdict::Sound`] therefore requires the guard to have held in *both* tiers (unless
//! every width at which the rule applies was covered exhaustively), so a rule whose guard only
//! holds at unsampled values cannot pass. Proof at wide widths is the SMT export's job.

use core::fmt;
use std::collections::BTreeMap;

use crate::ops::{BinOp, CmpOp};
use crate::rules::eval::{Val, admitted, eval, eval_lets, width_of};
use crate::rules::{ConstPred, FactPred, NodeId, RNode};
use crate::rules::{Ledger, Rule, RuleId, RuleKind, RuleProgram};
use crate::{BitVec, Width};

/// How thoroughly to check.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct CheckConfig {
    /// Enumerate every width assignment with all widths up to this.
    pub max_exhaustive_width: u16,
    /// ... when the parameters have at most this many bits in total (at most 40 is used).
    pub max_exhaustive_bits: u32,
    /// Widths used for sampling (each width variable ranges over these).
    pub sample_widths: Vec<u16>,
    /// Random parameter tuples per sampled width assignment.
    pub samples: u32,
    /// Seed for sampling.
    pub seed: u64,
}

impl Default for CheckConfig {
    fn default() -> Self {
        CheckConfig {
            max_exhaustive_width: 6,
            max_exhaustive_bits: 16,
            sample_widths: vec![
                7, 8, 9, 12, 16, 31, 32, 33, 63, 64, 65, 96, 127, 128, 129, 192, 255, 256, 257,
                384, 511, 512,
            ],
            samples: 64,
            seed: 0x5eed_cafe,
        }
    }
}

setters!(CheckConfig {
    with_max_exhaustive_width: max_exhaustive_width: u16,
    with_max_exhaustive_bits: max_exhaustive_bits: u32,
    with_sample_widths: sample_widths: Vec<u16>,
    with_samples: samples: u32,
    with_seed: seed: u64,
});

impl CheckConfig {
    /// The deeper configuration used nightly.
    pub fn thorough() -> Self {
        CheckConfig {
            max_exhaustive_width: 8,
            max_exhaustive_bits: 24,
            samples: 2048,
            ..CheckConfig::default()
        }
    }
}

/// What the checker established about one rule.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Evidence {
    /// Width assignments checked exhaustively.
    pub exhaustive_instances: u32,
    /// The largest width in an exhaustively checked assignment.
    pub exhaustive_max_width: u16,
    /// Parameter tuples checked exhaustively.
    pub exhaustive_cases: u64,
    /// Width assignments sampled.
    pub sampled_instances: u32,
    /// Parameter tuples sampled.
    pub sampled_cases: u64,
    /// Exhaustively checked tuples for which the guard held (the equation was tested).
    pub exhaustive_fired: u64,
    /// Sampled tuples for which the guard held.
    pub sampled_fired: u64,
    /// Whether every admitted width assignment of the rule was checked exhaustively (so
    /// sampling adds nothing).
    pub complete: bool,
}

impl Evidence {
    /// Tuples for which the guard held, in either tier.
    pub fn guard_true_cases(&self) -> u64 {
        self.exhaustive_fired + self.sampled_fired
    }
}

impl fmt::Display for Evidence {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "exhaustive(inst={},maxw={},cases={},fired={}{}) sampled(inst={},cases={},fired={})",
            self.exhaustive_instances,
            self.exhaustive_max_width,
            self.exhaustive_cases,
            self.exhaustive_fired,
            if self.complete { ",complete" } else { "" },
            self.sampled_instances,
            self.sampled_cases,
            self.sampled_fired
        )
    }
}

/// Inputs on which the two sides of a rule differ.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Counterexample {
    /// Width variable values.
    pub widths: Vec<(String, u16)>,
    /// Parameter values.
    pub params: Vec<(String, BitVec)>,
    /// The pattern's value.
    pub lhs: BitVec,
    /// The template's value.
    pub rhs: BitVec,
}

impl fmt::Display for Counterexample {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ws: Vec<String> = self
            .widths
            .iter()
            .map(|(n, w)| format!("{n} = {w}"))
            .collect();
        let ps: Vec<String> = self
            .params
            .iter()
            .map(|(n, v)| format!("{n} = {v}"))
            .collect();
        if !ws.is_empty() {
            write!(f, "{}; ", ws.join(", "))?;
        }
        write!(
            f,
            "{}: lhs = {}, rhs = {}",
            ps.join(", "),
            self.lhs,
            self.rhs
        )
    }
}

/// The verdict for one rule.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Verdict {
    /// No counterexample, the guard held in the exhaustive tier, and either the exhaustive
    /// tier covered every admitted width assignment or the guard also held in the sampled
    /// tier. The evidence says how much was checked.
    Sound,
    /// A counterexample.
    Unsound(Counterexample),
    /// No counterexample, but not enough evidence for [`Verdict::Sound`]; the reason says
    /// which tier is missing.
    Inconclusive(&'static str),
}

/// The result of checking one rule.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct RuleCheck {
    /// The rule's name.
    pub name: String,
    /// The rule's content hash.
    pub id: RuleId,
    /// Rewrite or identity.
    pub kind: RuleKind,
    /// The verdict.
    pub verdict: Verdict,
    /// What was checked.
    pub evidence: Evidence,
    /// The `#[example]`s that did not hold (see [`check_examples`]).
    pub examples: Vec<ExampleFailure>,
}

impl RuleCheck {
    /// Whether the rule passed with exhaustive evidence.
    pub fn is_sound(&self) -> bool {
        self.verdict == Verdict::Sound
    }
}

/// An `#[example("input" => "output")]` that does not hold.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExampleFailure {
    /// The input or the output does not parse.
    Parse {
        /// The text.
        text: String,
        /// The parser's message.
        error: String,
    },
    /// The rule does not apply to the input (its pattern does not match, or its guard is not
    /// proven).
    DoesNotFire {
        /// The input.
        input: String,
    },
    /// The rule applies but gives something else.
    Differs {
        /// The input.
        input: String,
        /// The expected output.
        expected: String,
        /// What the rule gave.
        got: String,
    },
}

impl fmt::Display for ExampleFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExampleFailure::Parse { text, error } => write!(f, "`{text}` does not parse: {error}"),
            ExampleFailure::DoesNotFire { input } => write!(f, "does not apply to `{input}`"),
            ExampleFailure::Differs {
                input,
                expected,
                got,
            } => write!(f, "`{input}` gave `{got}`, expected `{expected}`"),
        }
    }
}

/// Applies `rule` once, at the root, to each of its `#[example]` inputs and compares the result
/// with the expected output, both parsed with a default width of 8 bits (ascribe widths, as in
/// `p:32`, for others). Guards are answered by the facts of the example's own input. The
/// failures, in example order.
pub fn check_examples(rule: &Rule) -> Vec<ExampleFailure> {
    let mut out = Vec::new();
    for (input, output) in &rule.examples {
        let mut cx = crate::Context::new();
        let o = crate::ParseOptions::width(Width::W8);
        let parse = |cx: &mut crate::Context, text: &str| {
            cx.parse(text, &o).map_err(|e| ExampleFailure::Parse {
                text: text.to_string(),
                error: e.to_string(),
            })
        };
        let (e, want) = match (parse(&mut cx, input), parse(&mut cx, output)) {
            (Ok(e), Ok(w)) => (e, w),
            (Err(f), _) | (_, Err(f)) => {
                out.push(f);
                continue;
            }
        };
        let Ok(root) = cx.id(e) else { continue };
        match crate::rules::apply::try_apply(&mut cx, rule, root) {
            None => out.push(ExampleFailure::DoesNotFire {
                input: input.clone(),
            }),
            Some(got) if cx.handle(got) != want => out.push(ExampleFailure::Differs {
                input: input.clone(),
                expected: output.clone(),
                got: cx.display(cx.handle(got)).to_string(),
            }),
            Some(_) => {}
        }
    }
    out
}

/// SplitMix64.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

/// A boundary-biased value.
fn biased(rng: &mut Rng, w: Width) -> BitVec {
    let wb = w.bits();
    let random = |rng: &mut Rng| {
        let limbs: Vec<u64> = (0..8).map(|_| rng.next()).collect();
        BitVec::wrapping_from_limbs(w, &limbs)
    };
    match rng.next() % 12 {
        0 => BitVec::zero(w),
        1 => BitVec::one(w),
        2 => BitVec::ones(w),
        3 => BitVec::smin(w),
        4 => BitVec::smax(w),
        5 => BitVec::wrapping_from_u64(w, rng.next() % (u64::from(wb) + 2)),
        6 => {
            let k = (rng.next() % u64::from(wb)) as u16;
            BitVec::wrapping_from_limbs(w, &{
                let mut l = [0u64; 8];
                l[k as usize / 64] = 1 << (k % 64);
                l
            })
        }
        7 => {
            // Random significant length.
            let len = 1 + (rng.next() % u64::from(wb)) as u16;
            let v = random(rng);
            v.trunc(Width::new(len).unwrap_or(w))
                .and_then(|t| t.zext(w))
                .unwrap_or(v)
        }
        _ => random(rng),
    }
}

enum Outcome {
    Ok { fired: bool },
    Skip,
    Mismatch(BitVec, BitVec),
}

fn check_case(rule: &Rule, widths: &[u16], params: &[BitVec]) -> Outcome {
    let lets = eval_lets(rule, widths, params);
    if let Some(g) = rule.guard {
        match eval(rule, g, widths, params, &lets) {
            Some(v) if v.truthy() => {}
            Some(_) => return Outcome::Ok { fired: false },
            None => return Outcome::Skip,
        }
    }
    let (l, r) = (
        eval(rule, rule.lhs, widths, params, &lets).and_then(Val::bv),
        eval(rule, rule.rhs, widths, params, &lets).and_then(Val::bv),
    );
    match (l, r) {
        (Some(l), Some(r)) if l == r => Outcome::Ok { fired: true },
        (Some(l), Some(r)) => Outcome::Mismatch(l, r),
        _ => Outcome::Skip,
    }
}

fn counterexample(
    rule: &Rule,
    widths: &[u16],
    params: &[BitVec],
    l: BitVec,
    r: BitVec,
) -> Counterexample {
    Counterexample {
        widths: rule
            .width_vars
            .iter()
            .cloned()
            .zip(widths.iter().copied())
            .collect(),
        params: rule
            .params
            .iter()
            .map(|p| p.name.clone())
            .zip(params.iter().copied())
            .collect(),
        lhs: l,
        rhs: r,
    }
}

fn param_widths(rule: &Rule, widths: &[u16]) -> Option<Vec<Width>> {
    rule.params
        .iter()
        .map(|p| {
            let v = p.width.eval(widths);
            u16::try_from(v).ok().and_then(|v| Width::new(v).ok())
        })
        .collect()
}

/// Steers `params` toward satisfying the guard's positive fact and constant predicates (so
/// sampling tests the equation where it matters), best effort.
fn steer(rule: &Rule, widths: &[u16], params: &mut [BitVec], rng: &mut Rng) {
    let Some(g) = rule.guard else {
        return;
    };
    let mut positive = Vec::new();
    let mut stack = vec![g];
    while let Some(n) = stack.pop() {
        match &rule.nodes[n as usize] {
            RNode::And(a, b) | RNode::Or(a, b) => stack.extend([*a, *b]),
            RNode::Fact(..) | RNode::ConstP(..) => positive.push(n),
            _ => {}
        }
    }
    let param = |n: NodeId| match rule.nodes[n as usize] {
        RNode::Param(i) => Some(usize::from(i)),
        _ => None,
    };
    for _ in 0..2 {
        for &n in &positive {
            let lets = eval_lets(rule, widths, params);
            let value = |m: NodeId, params: &[BitVec]| {
                eval(rule, m, widths, params, &lets).and_then(Val::bv)
            };
            match &rule.nodes[n as usize] {
                RNode::Fact(FactPred::Proves, c, _) => {
                    let RNode::Cmp(op, l, r) = &rule.nodes[*c as usize] else {
                        continue;
                    };
                    let (stored, swap) = op.canonical();
                    let (l, r) = if swap { (*r, *l) } else { (*l, *r) };
                    // Set one side from the other, at the boundary of the predicate.
                    let (target, other, on_left) = match (param(l), param(r)) {
                        (Some(i), _) if rng.next().is_multiple_of(2) || param(r).is_none() => {
                            (i, r, true)
                        }
                        (_, Some(j)) => (j, l, false),
                        _ => continue,
                    };
                    let Some(v) = value(other, params) else {
                        continue;
                    };
                    if v.width() != params[target].width() {
                        continue;
                    }
                    let one = BitVec::one(v.width());
                    let add = |d: BinOp| BitVec::bin_unchecked(d, &v, &one);
                    params[target] = match (stored, on_left) {
                        (CmpOp::Eq | CmpOp::Ule | CmpOp::Sle, _) => v,
                        (CmpOp::Ne, _) => add(BinOp::Add),
                        (CmpOp::Ult | CmpOp::Slt, true) => add(BinOp::Sub),
                        (CmpOp::Ult | CmpOp::Slt, false) => add(BinOp::Add),
                    };
                }
                RNode::Fact(p, x, m) => {
                    let Some(i) = param(*x) else {
                        continue;
                    };
                    let mask = m.and_then(|m| value(m, params));
                    let w = params[i].width();
                    params[i] = match (p, mask) {
                        (FactPred::NonZero, _) if params[i].is_zero() => BitVec::one(w),
                        (FactPred::ZeroBits, Some(m)) if m.width() == w => BitVec::bin_unchecked(
                            BinOp::And,
                            &params[i],
                            &BitVec::un_unchecked(crate::ops::UnOp::Not, &m),
                        ),
                        (FactPred::OneBits, Some(m)) if m.width() == w => {
                            BitVec::bin_unchecked(BinOp::Or, &params[i], &m)
                        }
                        (FactPred::Disjoint, _) => {
                            let Some(j) = m.and_then(param) else {
                                continue;
                            };
                            if params[j].width() == w {
                                params[j] = BitVec::bin_unchecked(
                                    BinOp::And,
                                    &params[j],
                                    &BitVec::un_unchecked(crate::ops::UnOp::Not, &params[i]),
                                );
                            }
                            continue;
                        }
                        _ => continue,
                    };
                }
                RNode::ConstP(p, x) => {
                    let Some(i) = param(*x) else {
                        continue;
                    };
                    let w = params[i].width();
                    let wb = u64::from(w.bits());
                    let k = BitVec::wrapping_from_u64(w, rng.next() % wb);
                    let low = |k: &BitVec| {
                        // (1 << (k + 1)) - 1, i.e. a low mask of k + 1 ones.
                        let top = BitVec::bin_unchecked(BinOp::Shl, &BitVec::one(w), k);
                        let top2 = BitVec::bin_unchecked(BinOp::Add, &top, &top);
                        BitVec::bin_unchecked(BinOp::Sub, &top2, &BitVec::one(w))
                    };
                    params[i] = match p {
                        ConstPred::IsPow2 => BitVec::bin_unchecked(BinOp::Shl, &BitVec::one(w), &k),
                        ConstPred::IsLowMask => low(&k),
                        ConstPred::IsShiftedMask => {
                            let s = BitVec::wrapping_from_u64(w, rng.next() % wb);
                            BitVec::bin_unchecked(BinOp::Shl, &low(&k), &s)
                        }
                    };
                }
                _ => {}
            }
        }
    }
}

/// Checks one rule.
pub fn check_rule(rule: &Rule, cfg: &CheckConfig) -> RuleCheck {
    let mut ev = Evidence::default();
    let mut verdict = None;
    let admitted_all: Vec<Vec<u16>> = crate::rules::width_assignments(rule)
        .into_iter()
        .filter(|ws| admitted(rule, ws))
        .collect();
    let max_bits = cfg.max_exhaustive_bits.min(40);
    let mut complete = true;
    // Exhaustive.
    'exhaustive: for ws in &admitted_all {
        if ws.iter().any(|&w| w > cfg.max_exhaustive_width) {
            complete = false;
            continue;
        }
        let Some(pw) = param_widths(rule, ws) else {
            complete = false;
            continue;
        };
        let bits: u32 = pw.iter().map(|w| u32::from(w.bits())).sum();
        if bits > max_bits {
            complete = false;
            continue;
        }
        ev.exhaustive_instances += 1;
        let maxw = ws
            .iter()
            .copied()
            .chain(Some(width_of(rule, rule.lhs, ws).map_or(0, |w| w.bits())))
            .max()
            .unwrap_or(0);
        ev.exhaustive_max_width = ev.exhaustive_max_width.max(maxw);
        let mut params: Vec<BitVec> = pw.iter().map(|&w| BitVec::zero(w)).collect();
        for k in 0u64..(1u64 << bits) {
            let mut rest = k;
            for (p, w) in params.iter_mut().zip(&pw) {
                let wb = w.bits();
                *p = BitVec::wrapping_from_u64(*w, rest & ((1u64 << wb) - 1));
                rest >>= wb;
            }
            ev.exhaustive_cases += 1;
            match check_case(rule, ws, &params) {
                Outcome::Ok { fired } => ev.exhaustive_fired += u64::from(fired),
                Outcome::Skip => {}
                Outcome::Mismatch(l, r) => {
                    verdict = Some(Verdict::Unsound(counterexample(rule, ws, &params, l, r)));
                    break 'exhaustive;
                }
            }
        }
    }
    // A rule over fixed widths wider than the exhaustive tier, or with no width variables
    // and no admitted assignment in the domain, is not complete.
    ev.complete = complete && ev.exhaustive_instances > 0;
    // Sampled.
    if verdict.is_none() {
        let mut rng = Rng(cfg.seed ^ rule.id.0[0]);
        let n = rule.width_vars.len();
        let mut picks: Vec<Vec<u16>> = Vec::new();
        if n == 0 {
            picks.push(Vec::new());
        } else {
            // Each list width for the first variable; the others at random list widths.
            for &w0 in &cfg.sample_widths {
                for _ in 0..3 {
                    let mut ws = vec![w0];
                    for _ in 1..n {
                        let i = (rng.next() % cfg.sample_widths.len() as u64) as usize;
                        ws.push(cfg.sample_widths[i]);
                    }
                    picks.push(ws);
                }
            }
            // Also the admitted assignments nearest to the constraints' boundaries: those
            // whose first width is in the list.
            for ws in &admitted_all {
                if cfg.sample_widths.contains(&ws[0]) && picks.len() < 400 {
                    picks.push(ws.clone());
                }
            }
        }
        picks.sort();
        picks.dedup();
        'sampled: for ws in picks {
            if !admitted(rule, &ws) {
                continue;
            }
            let Some(pw) = param_widths(rule, &ws) else {
                continue;
            };
            ev.sampled_instances += 1;
            for k in 0..cfg.samples {
                let mut params: Vec<BitVec> = pw.iter().map(|&w| biased(&mut rng, w)).collect();
                if !k.is_multiple_of(2) {
                    steer(rule, &ws, &mut params, &mut rng);
                }
                ev.sampled_cases += 1;
                match check_case(rule, &ws, &params) {
                    Outcome::Ok { fired } => ev.sampled_fired += u64::from(fired),
                    Outcome::Skip => {}
                    Outcome::Mismatch(l, r) => {
                        verdict = Some(Verdict::Unsound(counterexample(rule, &ws, &params, l, r)));
                        break 'sampled;
                    }
                }
            }
        }
    }
    let verdict = verdict.unwrap_or(if ev.exhaustive_instances == 0 {
        Verdict::Inconclusive("no admitted width assignment is small enough to check exhaustively")
    } else if ev.exhaustive_fired == 0 {
        Verdict::Inconclusive("the guard never held in the exhaustive tier")
    } else if !ev.complete && ev.sampled_fired == 0 {
        Verdict::Inconclusive("the guard never held in the sampled tier")
    } else {
        Verdict::Sound
    });
    RuleCheck {
        name: rule.name.clone(),
        id: rule.id,
        kind: rule.kind,
        verdict,
        evidence: ev,
        examples: check_examples(rule),
    }
}

/// Checks every rule of a program, in parallel across threads.
pub fn check_program(program: &RuleProgram, cfg: &CheckConfig) -> Vec<RuleCheck> {
    let rules = program.rules();
    let threads = std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .min(rules.len().max(1));
    let chunk = rules.len().div_ceil(threads.max(1)).max(1);
    let mut out: Vec<RuleCheck> = Vec::with_capacity(rules.len());
    std::thread::scope(|s| {
        let handles: Vec<_> = rules
            .chunks(chunk)
            .map(|part| {
                s.spawn(move || part.iter().map(|r| check_rule(r, cfg)).collect::<Vec<_>>())
            })
            .collect();
        for h in handles {
            // A panicking check is a bug in the checker; surface it.
            match h.join() {
                Ok(v) => out.extend(v),
                Err(p) => std::panic::resume_unwind(p),
            }
        }
    });
    out
}

impl Ledger {
    /// The ledger of a set of checks. Only [`Verdict::Sound`] rules are entered, so the ledger
    /// vouches for nothing that was refuted or checked inconclusively.
    pub fn from_checks(checks: &[RuleCheck]) -> Ledger {
        let mut entries = BTreeMap::new();
        for c in checks {
            if c.verdict != Verdict::Sound {
                continue;
            }
            let kind = match c.kind {
                RuleKind::Rewrite => "rule",
                RuleKind::Identity => "identity",
            };
            entries.insert(
                c.name.clone(),
                (c.id.to_string(), kind.to_string(), c.evidence.to_string()),
            );
        }
        Ledger::from_entries(entries)
    }
}

#[cfg(test)]
mod tests;
