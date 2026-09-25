//! `bitwright`: check, lint, prove and catalog rule files; simplify expressions.

use std::fmt::Write as _;
use std::process::ExitCode;

use bitwright::check::{CheckConfig, Verdict, check_program};
use std::sync::Arc;

use bitwright::engine::{Engine, Run, Strategy};
use bitwright::mba::{MbaConfig, MbaTrust, NormalFormSolver};
use bitwright::rules::{Ledger, Level, Rule, RuleKind, RuleProgram, builtin_sources, explain};
use bitwright::{Assumptions, Context, ParseOptions, Reliance, Width, smtlib};

const USAGE: &str = "\
usage: bitwright <command> [options]

commands:
  check <file.bwr> [--thorough] [--prove] [--ledger <out>] [--against <ledger>]
        check every rule's soundness and examples; exit 1 unless every rule is sound and every
        example holds. `--ledger` writes the proof ledger; `--against` compares with an
        existing one. `--prove` also proves each rule with the native prover at widths too wide
        to enumerate (8, 32 and 64; binary16, binary32 and binary64 for floating-point rules;
        every assignment of a rule over fixed widths), so a rule with none small enough to
        enumerate can be proved sound.
  lint <file.bwr>
        compile and print every diagnostic; exit 1 on errors.
  smt <file.bwr> [--rule <group::name>] [--widths <w,...>]
        print each rule's soundness obligation as SMT-LIB 2.6, separated by (reset), for
        example `bitwright smt rules.bwr | z3 -in` or `| bitwuzla`: every answer must be
        `unsat`. --widths gives one width per width variable of the rules; without it, every
        admitted assignment of 8, 32 and 64 (or, for a rule admitted at none of those, three
        other admitted ones).
        A rule with no obligation prints a SKIPPED line a solver echoes, and exits 1.
  catalog [<file.bwr>]
        a Markdown catalog of the rules (the built-in rules without a file).
  lean [<file.bwr>] [--at <n>]
        the rules (the built-in ones without a file) as Lean 4 theorems over BitVec, for every
        width, their proofs left as `sorry`; with `--at`, at the widest widths up to <n> each
        rule admits, proved by `bv_decide` (`lean rules.lean` checks them).
  prove <file.opt> [--widths <w,...>] [--conflicts <n>]
        verify compiler transformations written as in the Alive paper (`Pre:`, source,
        `=>`, target): that each target refines its source under LLVM's semantics of
        poison, undefined behavior and floating point, at every width (1 to 8, 16, 32, 64)
        and format left open; a counterexample shows the inputs and each side's values as
        LLVM IR constants. Exit 1 unless every transformation is valid.
  infer <file.opt> [--widths <w,...>] [--conflicts <n>]
        infer a precondition over each transformation's symbolic constants (its own `Pre:` is
        ignored): the values where it is valid are learned as a formula over predicates
        (isPowerOf2(C), (C1 & C2) == 0, C u< width(C), …), which is then verified at every
        width. Exit 1 unless every transformation gets a verified precondition (or needs
        none).
  tv <src.ll> [<tgt.ll>] [--conflicts <n>]
        translation validation: that each function of the second file refines the function of
        the same name in the first (or @tgt refines @src of one file), for a subset of LLVM
        IR (integers, floating point, acyclic control flow, the intrinsics bitwright knows).
        Exit 1 unless every pair is valid.
  explain <code>
        what a diagnostic code means, e.g. `bitwright explain BW0302`.
  simplify <expr> [--width <n>] [--standard] [--assume <predicate>]... [--rules <file.bwr>]...
           [--float-values]
        simplify an expression (symbols default to --width, 64 if not given), assuming each
        1-bit predicate holds; prints the constraints a result relies on (`# relies on 0, 2`).
        Deobfuscates: the rules, the normal-form passes and the MBA service with the native
        normal-form solver, whose every answer bitwright proves itself. `--standard` runs only
        the rules and the standard passes (`--deobfuscate`, the default, is accepted).
        `--rules` adds a rule file's rules after the built-in ones, vouched for by the ledger
        `<file.bwr>.proof` if there is one (as `check --ledger` writes it), else checked now:
        exit 1 unless every rule is sound. `--float-values` also applies the rules that hold
        for floats as values, every NaN one value (`x · 1` is `x`): the result may then differ
        from the input in a NaN's payload or sign.

`--` ends the options: `bitwright simplify -- '-x + x'`.
";

/// Why a command did not succeed.
enum Fail {
    /// An error, with its exit code (1 for a failed lint, 2 for bad usage or input), for stderr.
    Err(u8, String),
    /// A complete report whose result is a failure (exit 1), for stdout like a passing one.
    Report(String),
}

fn usage(msg: impl Into<String>) -> Fail {
    Fail::Err(2, format!("{}\n\n{USAGE}", msg.into()))
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(out) => {
            print!("{out}");
            ExitCode::SUCCESS
        }
        Err(Fail::Report(out)) => {
            print!("{out}");
            ExitCode::from(1)
        }
        Err(Fail::Err(code, msg)) => {
            eprint!("{msg}");
            if !msg.ends_with('\n') {
                eprintln!();
            }
            ExitCode::from(code)
        }
    }
}

/// Splits `args` into positionals and `--flag [value]` options; `flags` lists the options that
/// take no value.
struct Args {
    pos: Vec<String>,
    opts: Vec<(String, Option<String>)>,
}

impl Args {
    fn parse(args: &[String], known: &[&str], flags: &[&str]) -> Result<Args, Fail> {
        let mut pos = Vec::new();
        let mut opts = Vec::new();
        let mut it = args.iter();
        while let Some(a) = it.next() {
            if a == "--" {
                pos.extend(it.by_ref().cloned());
                break;
            }
            if let Some(name) = a.strip_prefix("--") {
                if !known.contains(&name) {
                    return Err(usage(format!("unknown option --{name}")));
                }
                if flags.contains(&name) {
                    opts.push((name.to_string(), None));
                } else {
                    let v = it
                        .next()
                        .ok_or_else(|| usage(format!("--{name} needs a value")))?;
                    opts.push((name.to_string(), Some(v.clone())));
                }
            } else {
                pos.push(a.clone());
            }
        }
        Ok(Args { pos, opts })
    }

    fn flag(&self, name: &str) -> bool {
        self.opts.iter().any(|(n, _)| n == name)
    }

    fn value(&self, name: &str) -> Option<&str> {
        self.opts
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .and_then(|(_, v)| v.as_deref())
    }

    fn values<'s>(&'s self, name: &'s str) -> impl Iterator<Item = &'s str> + 's {
        self.opts
            .iter()
            .filter(move |(n, _)| n == name)
            .filter_map(|(_, v)| v.as_deref())
    }

    fn one(&self, what: &str) -> Result<&str, Fail> {
        match self.pos.as_slice() {
            [p] => Ok(p),
            [] => Err(usage(format!("missing {what}"))),
            _ => Err(usage(format!("expected one {what}"))),
        }
    }
}

fn run(args: &[String]) -> Result<String, Fail> {
    let Some((cmd, rest)) = args.split_first() else {
        return Err(usage("missing command"));
    };
    match cmd.as_str() {
        "check" => check(rest),
        "lint" => lint(rest),
        "smt" => smt(rest),
        "catalog" => catalog(rest),
        "lean" => lean(rest),
        "prove" => prove(rest),
        "tv" => tv(rest),
        "infer" => infer(rest),
        "explain" => {
            let a = Args::parse(rest, &[], &[])?;
            let code = a.one("diagnostic code")?;
            explain(code)
                .map(|e| format!("{}: {e}\n", code.to_ascii_uppercase()))
                .ok_or_else(|| Fail::Err(2, format!("unknown diagnostic code {code}")))
        }
        "simplify" => simplify(rest),
        "help" | "--help" | "-h" => Ok(USAGE.to_string()),
        other => Err(usage(format!("unknown command {other}"))),
    }
}

fn read(path: &str) -> Result<String, Fail> {
    std::fs::read_to_string(path).map_err(|e| Fail::Err(2, format!("{path}: {e}")))
}

/// Compiles `src`; on errors, every diagnostic rendered.
fn compile(path: &str, src: &str) -> Result<RuleProgram, Fail> {
    RuleProgram::compile(src).map_err(|e| Fail::Err(2, e.render(path, src)))
}

fn check(rest: &[String]) -> Result<String, Fail> {
    let a = Args::parse(
        rest,
        &["thorough", "prove", "ledger", "against"],
        &["thorough", "prove"],
    )?;
    let path = a.one("rule file")?;
    let src = read(path)?;
    let program = compile(path, &src)?;
    let mut cfg = if a.flag("thorough") {
        CheckConfig::thorough()
    } else {
        CheckConfig::default()
    };
    if a.flag("prove") {
        cfg = cfg.with_proofs(3);
    }
    let checks = check_program(&program, &cfg);
    let mut out = String::new();
    let (mut sound, mut unsound, mut inconclusive, mut bad_examples) = (0, 0, 0, 0);
    for c in &checks {
        let e = &c.evidence;
        match &c.verdict {
            Verdict::Sound => {
                sound += 1;
                let proved = if e.proved_instances + e.unproved_instances > 0 {
                    format!(
                        "; proved at {} of {} wide assignments",
                        e.proved_instances,
                        e.proved_instances + e.unproved_instances
                    )
                } else {
                    String::new()
                };
                writeln!(
                    out,
                    "sound         {}  ({} exhaustive cases to W = {}{}, {} sampled; guard held {} times{proved})",
                    c.name,
                    e.exhaustive_cases,
                    e.exhaustive_max_width,
                    if e.complete { ", complete" } else { "" },
                    e.sampled_cases,
                    e.guard_true_cases()
                )
                .ok();
            }
            Verdict::Unsound(cx) => {
                unsound += 1;
                writeln!(out, "UNSOUND       {}  {cx}", c.name).ok();
            }
            Verdict::Inconclusive(why) => {
                inconclusive += 1;
                writeln!(out, "inconclusive  {}  ({why})", c.name).ok();
            }
            _ => {
                inconclusive += 1;
                writeln!(out, "inconclusive  {}  (an unknown verdict)", c.name).ok();
            }
        }
        for f in &c.examples {
            bad_examples += 1;
            writeln!(out, "  example: {f}").ok();
        }
    }
    writeln!(
        out,
        "\n{sound} sound, {unsound} unsound, {inconclusive} inconclusive, {bad_examples} failed examples"
    )
    .ok();
    let ledger = Ledger::from_checks(&checks);
    if let Some(p) = a.value("ledger") {
        std::fs::write(p, ledger.render()).map_err(|e| Fail::Err(2, format!("{p}: {e}")))?;
        writeln!(out, "wrote {p}").ok();
    }
    let mut ok = unsound == 0 && inconclusive == 0 && bad_examples == 0;
    if let Some(p) = a.value("against") {
        let old = Ledger::parse(&read(p)?).map_err(|e| Fail::Err(2, format!("{p}: {e}")))?;
        let diff = old.diff(&ledger);
        if diff.is_empty() {
            writeln!(out, "{p} is up to date").ok();
        } else {
            ok = false;
            writeln!(out, "{p} differs:").ok();
            for d in diff {
                writeln!(out, "  {d}").ok();
            }
        }
    }
    if ok { Ok(out) } else { Err(Fail::Report(out)) }
}

fn lint(rest: &[String]) -> Result<String, Fail> {
    let a = Args::parse(rest, &[], &[])?;
    let path = a.one("rule file")?;
    let src = read(path)?;
    // A program with errors fails the lint.
    let program = compile(path, &src).map_err(|f| match f {
        Fail::Err(_, m) => Fail::Err(1, m),
        r => r,
    })?;
    let mut out = String::new();
    for d in program.diagnostics() {
        out.push_str(&d.render(path, &src));
    }
    let warnings = program
        .diagnostics()
        .iter()
        .filter(|d| d.level == Level::Warning)
        .count();
    let notes = program.diagnostics().len() - warnings;
    writeln!(
        out,
        "{}: {} rules, {warnings} warnings, {notes} notes",
        path,
        program.rules().len()
    )
    .ok();
    Ok(out)
}

/// `widths` followed by each assignment of the rule's rounding-mode variables (an index in
/// `RoundingMode::ALL` each).
fn with_modes(rule: &Rule, widths: &[u16]) -> Vec<Vec<u16>> {
    let mut out = vec![widths.to_vec()];
    for _ in &rule.modes {
        out = out
            .into_iter()
            .flat_map(|ws| {
                (0..bitwright::fp::RoundingMode::ALL.len() as u16).map(move |m| {
                    let mut v = ws.clone();
                    v.push(m);
                    v
                })
            })
            .collect();
    }
    out
}

/// Every assignment of `domain` to the rule's width variables that the rule admits (each with
/// every rounding mode of its mode variables), in order, at most `cap` width assignments.
fn admitted_over(rule: &Rule, domain: &[u16], cap: usize) -> Vec<Vec<u16>> {
    let n = rule.width_vars.len();
    let mut out = Vec::new();
    let mut found = 0;
    let mut idx = vec![0usize; n];
    loop {
        let ws: Vec<u16> = idx.iter().map(|&i| domain[i]).collect();
        let admitted: Vec<Vec<u16>> = with_modes(rule, &ws)
            .into_iter()
            .filter(|w| rule.admits(w))
            .collect();
        if !admitted.is_empty() {
            out.extend(admitted);
            found += 1;
            if found >= cap {
                return out;
            }
        }
        let mut k = 0;
        loop {
            if k == n {
                return out;
            }
            idx[k] += 1;
            if idx[k] < domain.len() {
                break;
            }
            idx[k] = 0;
            k += 1;
        }
    }
}

/// The width assignments to prove `rule` at: the given one, or every admitted assignment of
/// 8, 32 and 64, or (for a rule admitted at none of those) the first three admitted ones over
/// widths 1..=16 and a few wide ones.
fn assignments(rule: &Rule, given: Option<&[u16]>) -> Vec<Vec<u16>> {
    if let Some(g) = given {
        return with_modes(rule, g)
            .into_iter()
            .filter(|w| rule.admits(w))
            .collect();
    }
    let usual = admitted_over(rule, &[8, 32, 64], usize::MAX);
    if !usual.is_empty() {
        return usual;
    }
    let mut domain: Vec<u16> = (1..=16).collect();
    domain.extend([24, 32, 48, 64, 128, 256, 512]);
    admitted_over(rule, &domain, 3)
}

fn smt(rest: &[String]) -> Result<String, Fail> {
    let a = Args::parse(rest, &["rule", "widths"], &[])?;
    let path = a.one("rule file")?;
    let src = read(path)?;
    let program = compile(path, &src)?;
    let widths: Option<Vec<u16>> = a
        .value("widths")
        .map(|w| {
            w.split(',')
                .map(|x| x.trim().parse::<u16>())
                .collect::<Result<_, _>>()
                .map_err(|_| usage(format!("bad --widths {w}")))
        })
        .transpose()?;
    let rules: Vec<&Rule> = match a.value("rule") {
        Some(name) => vec![
            program
                .rule(name)
                .ok_or_else(|| Fail::Err(2, format!("no rule {name} in {path}")))?,
        ],
        None => program.rules().iter().collect(),
    };
    if let Some(ws) = &widths {
        // One width per width variable, each 1..=512.
        if ws.iter().any(|&w| w == 0 || w > 512) {
            return Err(usage("--widths are 1..=512"));
        }
        if let Some(r) = rules.iter().find(|r| r.width_vars.len() != ws.len()) {
            return Err(usage(format!(
                "--widths gives {} widths, but {} has {} width variables ({}); \
                 select rules with --rule",
                ws.len(),
                r.name,
                r.width_vars.len(),
                r.width_vars.join(", ")
            )));
        }
    }
    let mut out = String::new();
    let mut count = 0;
    let mut skipped = Vec::new();
    for rule in rules {
        let ws = assignments(rule, widths.as_deref());
        if ws.is_empty() {
            // A solver echoes this instead of answering, so a pipeline that expects only
            // `unsat` sees it.
            writeln!(
                out,
                "(echo \"SKIPPED {}: not admitted at these widths\")\n(reset)",
                rule.name
            )
            .ok();
            skipped.push(rule.name.clone());
        }
        for w in ws {
            let script =
                smtlib::rule_obligation(rule, &w).map_err(|e| Fail::Err(2, e.to_string()))?;
            out.push_str(&script);
            out.push_str("\n(reset)\n");
            count += 1;
        }
    }
    writeln!(out, "; {count} obligations").ok();
    if skipped.is_empty() {
        Ok(out)
    } else {
        writeln!(out, "; {} rules skipped", skipped.len()).ok();
        Err(Fail::Report(out))
    }
}

/// The verifier's configuration from `--widths` and `--conflicts`.
fn transform_config(a: &Args) -> Result<bitwright::transform::Config, Fail> {
    let mut cfg = bitwright::transform::Config::default();
    if let Some(ws) = a.value("widths") {
        let widths = ws
            .split(',')
            .map(|w| w.trim().parse::<u16>().ok().filter(|&w| w > 0))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| usage(format!("--widths: {ws} is not a list of widths")))?;
        cfg = cfg.with_widths(widths);
    }
    if let Some(c) = a.value("conflicts") {
        let n = c
            .parse::<u64>()
            .map_err(|_| usage(format!("--conflicts: {c} is not a number")))?;
        cfg = cfg.with_conflicts(n);
    }
    Ok(cfg)
}

fn reports(reports: Vec<bitwright::transform::Report>) -> Result<String, Fail> {
    use bitwright::transform::Verdict;
    let mut out = String::new();
    let (mut valid, mut invalid, mut open) = (0, 0, 0);
    for r in &reports {
        out.push_str(&r.to_string());
        match r.verdict() {
            Verdict::Valid => valid += 1,
            Verdict::Invalid(_) => invalid += 1,
            _ => open += 1,
        }
    }
    writeln!(
        out,
        "\n{valid} valid, {invalid} invalid, {open} not decided"
    )
    .ok();
    if invalid == 0 && open == 0 {
        Ok(out)
    } else {
        Err(Fail::Report(out))
    }
}

fn prove(rest: &[String]) -> Result<String, Fail> {
    let a = Args::parse(rest, &["widths", "conflicts"], &[])?;
    let path = a.one("transformation file")?;
    let src = read(path)?;
    let cfg = transform_config(&a)?;
    let ts = bitwright::transform::parse_transforms(&src)
        .map_err(|e| Fail::Err(2, format!("{path}: {e}")))?;
    reports(
        ts.iter()
            .map(|t| bitwright::transform::verify(t, &cfg))
            .collect(),
    )
}

fn infer(rest: &[String]) -> Result<String, Fail> {
    use bitwright::transform::Verdict;
    let a = Args::parse(rest, &["widths", "conflicts"], &[])?;
    let path = a.one("transformation file")?;
    let src = read(path)?;
    let cfg = transform_config(&a)?;
    let ts = bitwright::transform::parse_transforms(&src)
        .map_err(|e| Fail::Err(2, format!("{path}: {e}")))?;
    let mut out = String::new();
    let mut ok = true;
    for t in &ts {
        let i = bitwright::transform::infer(t, &cfg)
            .map_err(|e| Fail::Err(2, format!("{}: {e}", t.name)))?;
        let verdict = i.report.as_ref().map(|r| r.verdict());
        let (pos, neg) = i.examples;
        match (&i.pre, verdict) {
            (_, None) => {
                ok = false;
                writeln!(
                    out,
                    "none         {}  (no symbolic constants, or no valid value)",
                    t.name
                )
                .ok();
            }
            (None, Some(Verdict::Valid)) => {
                writeln!(out, "not needed   {}  (valid as it is)", t.name).ok();
            }
            (Some(p), Some(Verdict::Valid)) => {
                let how = if i.weakest {
                    "weakest found"
                } else {
                    "some valid values excluded"
                };
                writeln!(
                    out,
                    "Pre: {p}\n             {}  ({how}; {pos} valid and {neg} invalid examples)",
                    t.name
                )
                .ok();
            }
            (p, Some(v)) => {
                ok = false;
                let what = match v {
                    Verdict::Invalid(cx) => format!("still invalid:\n{cx}"),
                    Verdict::Unknown(w) | Verdict::Unsupported(w) => format!("not decided: {w}"),
                    Verdict::Valid => unreachable!("handled"),
                };
                writeln!(
                    out,
                    "Pre: {}\n             {}  {what}",
                    p.as_deref().unwrap_or("(none)"),
                    t.name
                )
                .ok();
            }
        }
    }
    if ok { Ok(out) } else { Err(Fail::Report(out)) }
}

fn tv(rest: &[String]) -> Result<String, Fail> {
    let a = Args::parse(rest, &["conflicts"], &[])?;
    let (first, second) = match a.pos.as_slice() {
        [p] => (read(p)?, None),
        [p, q] => (read(p)?, Some(read(q)?)),
        _ => return Err(usage("expected one or two LLVM IR files")),
    };
    let cfg = transform_config(&a)?;
    let pairs = bitwright::transform::pairs(&first, second.as_deref())
        .map_err(|e| Fail::Err(2, e.to_string()))?;
    reports(
        pairs
            .iter()
            .map(|t| bitwright::transform::verify(t, &cfg))
            .collect(),
    )
}

fn lean(rest: &[String]) -> Result<String, Fail> {
    let a = Args::parse(rest, &["at"], &[])?;
    let at = match a.value("at") {
        Some(v) => Some(
            v.parse::<u16>()
                .ok()
                .filter(|&w| w > 0)
                .ok_or_else(|| usage(format!("--at: {v} is not a width")))?,
        ),
        None => None,
    };
    let files: Vec<(String, String)> = match a.pos.as_slice() {
        [] => builtin_sources()
            .iter()
            .map(|(n, s, _)| (n.to_string(), s.to_string()))
            .collect(),
        [p] => vec![(p.clone(), read(p)?)],
        _ => return Err(usage("expected at most one rule file")),
    };
    let programs = files
        .iter()
        .map(|(path, src)| compile(path, src))
        .collect::<Result<Vec<_>, _>>()?;
    let refs: Vec<&RuleProgram> = programs.iter().collect();
    Ok(bitwright::rules::lean::lean(&refs, at))
}

fn catalog(rest: &[String]) -> Result<String, Fail> {
    let a = Args::parse(rest, &[], &[])?;
    let files: Vec<(String, String)> = match a.pos.as_slice() {
        [] => builtin_sources()
            .iter()
            .map(|(n, s, _)| (n.to_string(), s.to_string()))
            .collect(),
        [p] => vec![(p.clone(), read(p)?)],
        _ => return Err(usage("expected at most one rule file")),
    };
    let mut out = String::from(
        "# Rule catalog\n\n<!-- Generated by `bitwright catalog`; do not edit. -->\n\n",
    );
    if a.pos.is_empty() {
        out.push_str(
            "The built-in rules: `core.bwr`, the local rules the engine links by default, and \
             `eqsat.bwr`, the equations of the equality-saturation search. Every rule is \
             checked (and recorded in the file's proof ledger) and every example holds.\n\n",
        );
    }
    for (path, src) in &files {
        let program = compile(path, src)?;
        writeln!(out, "## `{path}`\n").ok();
        for g in program.groups() {
            writeln!(out, "### {}\n", g.name).ok();
            for &i in &g.rules {
                let r = &program.rules()[i];
                let short = r.name.rsplit("::").next().unwrap_or(&r.name);
                let kind = match (r.kind, r.is_directed()) {
                    (RuleKind::Rewrite, _) if r.float_values => {
                        "rule (`#[float_values]`: equal as floats, applied only on request)"
                    }
                    (RuleKind::Rewrite, _) => "rule",
                    (RuleKind::Identity, true) => "identity (directed and search)",
                    (RuleKind::Identity, false) => "identity (search only)",
                    _ => "equation",
                };
                writeln!(out, "#### `{short}` — {kind}\n").ok();
                for line in r.doc.lines() {
                    writeln!(out, "{}", line.trim()).ok();
                }
                if !r.doc.is_empty() {
                    out.push('\n');
                }
                let text = src.get(r.span.0..r.span.1).unwrap_or("");
                // The rule's own text, without its doc comment and attributes.
                let body: Vec<&str> = text
                    .lines()
                    .map(str::trim_end)
                    .filter(|l| {
                        let t = l.trim_start();
                        !t.starts_with("///") && !t.starts_with("#[")
                    })
                    .collect();
                writeln!(out, "```text\n{}\n```\n", dedent(&body)).ok();
                for (i, o) in &r.examples {
                    writeln!(out, "- `{i}` → `{o}`").ok();
                }
                if !r.examples.is_empty() {
                    out.push('\n');
                }
            }
        }
    }
    Ok(out)
}

fn dedent(lines: &[&str]) -> String {
    let indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);
    lines
        .iter()
        .map(|l| l.get(indent..).unwrap_or(l.trim_start()))
        .collect::<Vec<_>>()
        .join("\n")
}

fn simplify(rest: &[String]) -> Result<String, Fail> {
    let a = Args::parse(
        rest,
        &[
            "width",
            "deobfuscate",
            "standard",
            "assume",
            "rules",
            "float-values",
        ],
        &["deobfuscate", "standard", "float-values"],
    )?;
    if a.flag("standard") && a.flag("deobfuscate") {
        return Err(usage("--standard and --deobfuscate exclude each other"));
    }
    let src = a.one("expression")?;
    let w: u16 = match a.value("width") {
        Some(w) => w.parse().map_err(|_| usage(format!("bad --width {w}")))?,
        None => 64,
    };
    let width = Width::new(w).map_err(|_| usage("the width must be 1..=512"))?;
    let mut cx = Context::new();
    let o = ParseOptions::width(width);
    let e = cx
        .parse(src, &o)
        .map_err(|e| Fail::Err(2, format!("{e}")))?;
    let mut assumptions = Assumptions::new();
    for p in a.values("assume") {
        let p = cx
            .parse(p, &o)
            .map_err(|e| Fail::Err(2, format!("--assume {p}: {e}")))?;
        assumptions
            .assume_true(&mut cx, p)
            .map_err(|e| Fail::Err(2, format!("--assume: {e} (a predicate is 1 bit wide)")))?;
    }
    if let Some(c) = assumptions.conflict() {
        return Err(Fail::Err(
            1,
            format!(
                "the assumptions contradict each other ({})",
                constraint_ids(c)
            ),
        ));
    }
    let mut builder = Engine::builder().builtin();
    let mut strategy = if a.flag("standard") {
        Strategy::standard()
    } else {
        // The MBA service with the native solver, on bitwright's own evidence only.
        let trust = MbaTrust::default().with_backend_certificates(false);
        builder = builder.mba_solver(Arc::new(NormalFormSolver::default()));
        Strategy::deobfuscate().with_mba(MbaConfig::default().with_trust(trust))
    };
    let mut groups = Vec::new();
    for path in a.values("rules") {
        let (program, ledger) = vouched_rules(path)?;
        groups.extend(program.groups().iter().map(|g| g.name.clone()));
        builder = builder.program(program, &ledger);
    }
    if !groups.is_empty() {
        let groups: Vec<&str> = groups.iter().map(String::as_str).collect();
        strategy = strategy.with_rule_groups(&groups);
    }
    strategy = strategy.with_float_values(a.flag("float-values"));
    let engine = builder
        .strategy(strategy)
        .build()
        .map_err(|e| Fail::Err(2, format!("{e}")))?;
    let out = engine
        .run(&mut cx, &[e], Run::default().with_assumptions(&assumptions))
        .map_err(|e| Fail::Err(2, format!("{e}")))?
        .roots[0];
    let mut text = format!("{}", cx.display(out.expr));
    if !out.relies_on.is_none() {
        text.push_str(&format!(
            "    # relies on {}",
            constraint_ids(out.relies_on)
        ));
    }
    Ok(format!("{text}\n"))
}

/// A rule file for `simplify --rules`, with the ledger vouching for it: `<path>.proof` if it
/// exists, else the checker's, which must find every rule sound.
fn vouched_rules(path: &str) -> Result<(RuleProgram, Ledger), Fail> {
    let src = read(path)?;
    let program = compile(path, &src)?;
    let proof = format!("{path}.proof");
    if std::path::Path::new(&proof).exists() {
        let ledger =
            Ledger::parse(&read(&proof)?).map_err(|e| Fail::Err(2, format!("{proof}: {e}")))?;
        if let Some(r) = program
            .rules()
            .iter()
            .find(|r| !ledger.vouches_for(&r.name, r.id))
        {
            return Err(Fail::Err(
                1,
                format!(
                    "{proof} does not vouch for {} (changed since it was written? run `bitwright check {path} --ledger {proof}`)",
                    r.name
                ),
            ));
        }
        return Ok((program, ledger));
    }
    let checks = check_program(&program, &CheckConfig::default());
    let mut bad = String::new();
    for c in &checks {
        match &c.verdict {
            Verdict::Sound => {}
            Verdict::Unsound(cx) => writeln!(bad, "UNSOUND       {}  {cx}", c.name).unwrap_or(()),
            Verdict::Inconclusive(why) => {
                writeln!(bad, "inconclusive  {}  ({why})", c.name).unwrap_or(())
            }
            _ => writeln!(bad, "inconclusive  {}", c.name).unwrap_or(()),
        }
    }
    if !bad.is_empty() {
        return Err(Fail::Err(
            1,
            format!("{path}: not every rule is sound\n{bad}"),
        ));
    }
    Ok((program, Ledger::from_checks(&checks)))
}

/// The indices of the `--assume` options (from 0) a reliance names.
fn constraint_ids(r: Reliance) -> String {
    let (ids, rest) = r.indices();
    let mut ids: Vec<String> = ids.map(|i| i.to_string()).collect();
    if rest {
        ids.push("63 and later".into());
    }
    ids.join(", ")
}
