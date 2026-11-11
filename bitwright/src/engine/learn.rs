//! Rules learned from derivations: what a pass worked out once, as a rule the engine matches
//! the next time.

use std::collections::{BTreeMap, HashSet};
use std::fmt::Write;

use super::Derivation;
use crate::Width;
use crate::check::{CheckConfig, Verdict, check_rule};
use crate::error::Error;
use crate::expr::{Context, Expr, View};
use crate::rules::{Ledger, RuleProgram};
use crate::text::{ParseOptions, PrintOptions};

/// How [`learn`] chooses what to keep.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct LearnConfig {
    /// The largest pattern (in nodes, as a tree) a learned rule may have: a larger one is of
    /// its instance, and costs every match attempt.
    pub max_pattern: u32,
    /// The most parameters a learned rule may have.
    pub max_parameters: usize,
    /// The conflicts the native prover may spend on each width of a candidate. A candidate
    /// it does not prove at every width it is asked about is not kept.
    pub proof_conflicts: u64,
    /// The passes whose steps are learned from, by name; empty for every pass. The steps
    /// worth a rule are those of the passes that search (`mba`, `linear_mba`, `sweep`): a
    /// rule for what a cheap pass does anyway saves nothing and reorders its work.
    pub passes: Vec<String>,
}

impl Default for LearnConfig {
    fn default() -> Self {
        LearnConfig {
            max_pattern: 40,
            max_parameters: 6,
            proof_conflicts: 20_000,
            passes: ["mba", "linear_mba", "sweep"].map(String::from).to_vec(),
        }
    }
}

setters!(LearnConfig {
    with_max_pattern: max_pattern: u32,
    with_max_parameters: max_parameters: usize,
    with_proof_conflicts: proof_conflicts: u64,
    with_passes: passes: Vec<String>,
});

/// What [`learn`] made of some derivations.
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct Learned {
    /// The rules kept, as a rule file (group `learned`): every one checked sound and proved
    /// by the native prover at the widths it was asked about. Empty when none was kept.
    pub rules: String,
    /// The checks that admitted them, as the ledger an engine asks for with the rules
    /// ([`EngineBuilder::program`](super::EngineBuilder::program)).
    pub ledger: Ledger,
    /// The steps looked at: those made by passes, not by rules.
    pub steps: usize,
    /// How many rules were kept (distinct ones).
    pub kept: usize,
    /// Of those, the rules that hold at every width (the others are of one width).
    pub generic: usize,
    /// Why the other steps gave no rule, with how many each.
    pub dropped: BTreeMap<&'static str, usize>,
}

/// Turns the steps of `derivations` that passes made into rules: each step with the
/// subexpressions its two sides share taken as parameters, kept if it is a rule the checker
/// finds sound and the native prover proves.
///
/// A pass that rewrote `(s ^ t) + 2 * (s & t)` to `s + t` for two large `s` and `t` did the
/// work of a decision procedure; the step it left says `(x ^ y) + 2 * (x & y) => x + y`, which
/// is a rule, at every width, matched in passing from then on. What a derivation teaches this
/// way is exactly what it shows: the shape of the step, with its constants as they were. A
/// rule is tried at every width first and kept at the step's own width when it only holds or
/// only reads there.
///
/// Nothing is kept on trust. A candidate must be a terminating rule that the checker finds
/// sound (every value at small widths, samples at wide ones), and at the wide widths the
/// checker asks about (8, 32 and 64 bits) it must be proved: by the native prover, or at the
/// step's own width by the arithmetic of [`Derivation::check`], which a narrower width
/// inherits. What is not is dropped and counted in [`Learned::dropped`]. Above the step's
/// width a rule kept at every width rests on the checker's samples, as the built-in rules do.
pub fn learn(derivations: &[&Derivation], cfg: &LearnConfig) -> Result<Learned, Error> {
    let mut out = Learned::default();
    let mut seen: HashSet<crate::rules::RuleId> = HashSet::new();
    let mut texts: Vec<String> = Vec::new();
    let mut checks = Vec::new();
    let check = CheckConfig::default()
        .with_proofs(3)
        .with_proof_conflicts(cfg.proof_conflicts);
    let drop = |out: &mut Learned, why: &'static str| {
        *out.dropped.entry(why).or_default() += 1;
    };
    for d in derivations {
        for step in &d.steps {
            // A rule's own steps teach nothing new.
            if step.by.contains("::") {
                continue;
            }
            if !cfg.passes.is_empty() && !cfg.passes.contains(&step.by) {
                continue;
            }
            out.steps += 1;
            let candidate = match candidate(step.width, &step.before, &step.after, cfg)? {
                Ok(c) => c,
                Err(why) => {
                    drop(&mut out, why);
                    continue;
                }
            };
            // At every width if it holds there, else at its own.
            let mut kept = None;
            let mut why = "it does not compile as a rule (not smaller, or not in the rule syntax)";
            for (generic, text) in [(true, &candidate.generic), (false, &candidate.fixed)] {
                let Some(text) = text else { continue };
                let name = format!("l{}", texts.len());
                let file = format!(
                    "bitwright 1;\n\ngroup learned {{\n    #[allow(BW0407)]\n    rule {name}{text}\n}}\n"
                );
                let program = match RuleProgram::compile(&file) {
                    Ok(p) => p,
                    Err(_) => continue,
                };
                let Some(rule) = program.rules().first() else {
                    continue;
                };
                let checked = check_rule(rule, &check);
                // Sound by the checker (every value at small widths, samples at wide
                // ones), and proved at the wide widths asked about: by the search, or, at
                // the step's own width and so below it, by arithmetic.
                if matches!(checked.verdict, Verdict::Sound)
                    && (checked.evidence.unproved_instances == 0 || candidate.by_arithmetic)
                {
                    kept = Some((generic, rule.id, name, text.clone(), checked));
                    break;
                }
                why = "the checker or the prover does not vouch for it";
            }
            match kept {
                Some((generic, id, name, text, checked)) => {
                    if seen.insert(id) {
                        checks.push(checked);
                        out.kept += 1;
                        out.generic += usize::from(generic);
                        texts.push(format!(
                            "    /// Learned from a step of `{}`.\n    #[allow(BW0407)]\n    rule {name}{text}\n",
                            step.by
                        ));
                    } else {
                        drop(&mut out, "the same rule as another step's");
                    }
                }
                None => drop(&mut out, why),
            }
        }
    }
    out.ledger = Ledger::from_checks(&checks);
    if !texts.is_empty() {
        let _ = write!(
            out.rules,
            "bitwright 1;\n\ngroup learned {{\n{}}}\n",
            texts.concat()
        );
    }
    Ok(out)
}

/// A step as rule text after the rule's name, at every width (when the step has nothing of
/// one width in it) and at its own.
struct Candidate {
    generic: Option<String>,
    fixed: Option<String>,
    /// Whether the two sides are equal at the step's width by the ring laws or as linear
    /// MBAs (see [`Derivation::check`]): then also at every narrower width, of which either
    /// argument is as true.
    by_arithmetic: bool,
}

/// The rule a step suggests, or why it suggests none.
fn candidate(
    width: u16,
    before: &str,
    after: &str,
    cfg: &LearnConfig,
) -> Result<Result<Candidate, &'static str>, Error> {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::new(width)?);
    let (before, after) = (cx.parse(before, &o)?, cx.parse(after, &o)?);
    // The parameters: the outermost subexpressions of the result that the step's left side
    // contains too, and whatever symbols are left on either side.
    let in_before: HashSet<Expr> = cx.post_order(&[before])?.into_iter().collect();
    let mut atoms: Vec<Expr> = Vec::new();
    let mut stack = vec![after];
    let mut seen = HashSet::new();
    while let Some(e) = stack.pop() {
        if !seen.insert(e) || cx.as_const(e)?.is_some() {
            continue;
        }
        if in_before.contains(&e) {
            atoms.push(e);
        } else {
            stack.extend(cx.children(e)?);
        }
    }
    // Under an atom nothing is a parameter of its own: what is left of the left side.
    let mut stack = vec![before];
    while let Some(e) = stack.pop() {
        if !seen.insert(e) || atoms.contains(&e) {
            continue;
        }
        if matches!(cx.view(e)?, View::Sym(_)) {
            atoms.push(e);
        } else {
            stack.extend(cx.children(e)?);
        }
    }
    if atoms.is_empty() {
        return Ok(Err("no parameter: both sides are constants"));
    }
    if atoms.len() > cfg.max_parameters {
        return Ok(Err("too many parameters"));
    }
    // (An atom inside another is not replaced: the outer one goes first.)
    atoms.sort_by_key(|e| core::cmp::Reverse(e.index()));
    let mut map = Vec::with_capacity(atoms.len());
    let mut params = Vec::with_capacity(atoms.len());
    for (k, &atom) in atoms.iter().enumerate() {
        let w = cx.width(atom)?;
        let name = format!("p{k}");
        let p = cx.symbol(format!("learned.{name}").as_str(), w)?;
        map.push((atom, p));
        params.push((name, w.bits()));
    }
    let sides = cx.substitute(&[before, after], &map)?;
    if cx.tree_size(sides[0])? > cfg.max_pattern {
        return Ok(Err("the pattern is too large"));
    }
    if sides[0] == sides[1] {
        return Ok(Err("nothing left once the shared parts are parameters"));
    }
    // A parameter the pattern lost (the constructors folded it away) cannot be in the result.
    let reads = |cx: &mut Context, e: Expr| -> Result<HashSet<Expr>, Error> {
        Ok(cx.post_order(&[e])?.into_iter().collect())
    };
    let (in_pattern, in_result) = (reads(&mut cx, sides[0])?, reads(&mut cx, sides[1])?);
    if map
        .iter()
        .any(|(_, p)| in_result.contains(p) && !in_pattern.contains(p))
    {
        return Ok(Err("the result reads what the pattern does not"));
    }
    let text = |cx: &Context, e: Expr| {
        let opts = PrintOptions::default()
            .with_lets(false)
            .with_max_nodes(10_000);
        cx.display_with(e, opts)
            .to_string()
            .replace("\"learned.", "")
            .replace("learned.", "")
    };
    let (pattern, result) = (text(&cx, sides[0]), text(&cx, sides[1]));
    if pattern.contains('…') || pattern.contains('"') || result.contains('"') {
        return Ok(Err("the pattern does not print as a rule"));
    }
    let used: Vec<&(String, u16)> = (params.iter().zip(&map))
        .filter(|(_, (_, p))| in_pattern.contains(p))
        .map(|(named, _)| named)
        .collect();
    let rule = |widths: &dyn Fn(u16) -> String, generics: &str| {
        let list: Vec<String> = (used.iter())
            .map(|(name, w)| format!("{name}: {}", widths(*w)))
            .collect();
        format!(
            "{generics}({}) {{ {pattern} => {result} }}",
            list.join(", ")
        )
    };
    // At every width: nothing in the text may name a width, and every parameter is of the
    // step's.
    let plain = used.iter().all(|(_, w)| *w == width)
        && ![pattern.as_str(), result.as_str()]
            .iter()
            .any(|t| t.contains('<') && t.contains(">(") || t.contains(':'));
    let by_arithmetic = super::derive::ring_equal(&cx, sides[0], sides[1])?
        || super::derive::corners_equal(&cx, sides[0], sides[1])?;
    Ok(Ok(Candidate {
        generic: plain.then(|| rule(&|_| "W".to_string(), "<W>")),
        fixed: Some(rule(&|w| w.to_string(), "")),
        by_arithmetic,
    }))
}
