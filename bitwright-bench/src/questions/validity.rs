//! Replay one captured `#Q` validity record per file. Unknown is not a negative result.
use super::{Retry, check_witness};
use bitwright::engine::{Budget, Run};
use bitwright::prove::{self, Config, Limits, Outcome, Question, Unknown};
use bitwright::{Assumptions, Context, ParseOptions, Width};
use std::{collections::BTreeMap, error::Error, fs};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

// The captured configuration is a Debug dump, not a versioned interchange format.
// Reconstruct only settings we understand; reject, rather than ignore, any difference.
fn config(text: &str) -> Result<Config> {
    let number = |key: &str| -> Result<u64> {
        Ok(text.split_once(key).ok_or_else(|| format!("missing {key}"))?.1
            .split(',').next().unwrap().parse()?)
    };
    let mut c = Config::default().with_simplify_fuel(number("node_visits: ")?).with_sweeping(false);
    c.max_nodes = number("max_nodes: ")?.try_into()?;
    c.max_conflicts = number("max_conflicts: ")?;
    c.max_propagations = number("max_propagations: ")?;
    if format!("{c:?}") != text {
        return Err("unsupported recorded configuration".into());
    }
    Ok(c)
}

fn recoverable(o: &Outcome) -> bool {
    matches!(o, Outcome::Unknown(Unknown::Budget { .. } | Unknown::TooLarge { .. }))
}

fn check(text: &str, engines: &Retry) -> Result<(&'static str, &'static str)> {
    let (header, body) = text.split_once("\n#ROOT ").ok_or("missing #ROOT")?;
    let cfg = config(header.lines().find_map(|l| l.strip_prefix("#CFG ")).ok_or("missing #CFG")?)?;
    let record = header.lines().find_map(|l| l.strip_prefix("#Q ")).ok_or("missing #Q")?;
    if !record.split_whitespace().any(|s| s == "walk_simplifiers=true") {
        return Err("unsupported recorded simplifier profile".into());
    }
    let count: usize = record.split_whitespace().find_map(|s| s.strip_prefix("preds="))
        .ok_or("missing preds count")?.parse()?;
    let body = body.trim_end().strip_suffix("\n#END").ok_or("missing #END")?;
    let mut cx = Context::new();
    let parse = ParseOptions::width(Width::W64);
    let checks = body.split("\n#A ").map(|s| cx.parse(s, &parse)).collect::<std::result::Result<Vec<_>, _>>()?;
    let (&root, preds) = checks.split_first().ok_or("missing predicate")?;
    if preds.len() != count { return Err("assumption count mismatch".into()); }
    let mut assumptions = Assumptions::new();
    for &p in preds { assumptions.assume_true(&mut cx, p)?; }
    let under = (!preds.is_empty()).then_some(&assumptions);
    let mut outcome = prove::valid_under_with(&mut cx, root, under, &cfg, &engines.stock)?;
    let mut stage = "asked";
    if recoverable(&outcome) {
        // Simplify the counterexample, not each conjunct independently. A zero is
        // a proof even when reaching it used a relationship between two conjuncts.
        let mut bad = cx.not(root)?;
        for &p in preds { bad = cx.and(bad, p)?; }
        for _ in 0..3 {
            let run = Run::default().with_per_call(Budget::fuel(1 << 19));
            let next = engines.word.run(&mut cx, &[bad], run)?.roots[0].expr;
            if next == bad { break; }
            bad = next;
            if cx.as_const(bad)?.is_some() { break; }
        }
        if cx.as_const(bad)?.is_some_and(|v| v.is_zero()) {
            return Ok(("proved", "forms"));
        }
        let valid = cx.not(bad)?;
        let residual = cfg.with_simplify(false);
        let mut q = Question::valid(&mut cx, valid, &residual)?;
        stage = "residual";
        outcome = q.solve(&mut cx, cfg.limits())?;
        if matches!(outcome, Outcome::Unknown(Unknown::Budget { .. })) {
            // Resume the same search: no clause loss, rebuilding or repeated warmup.
            stage = "search";
            outcome = q.solve(&mut cx, Limits { conflicts: 100_000, propagations: 20_000_000 })?;
        }
    }
    match outcome {
        Outcome::Proved(_) => Ok(("proved", stage)),
        Outcome::Refuted(model) => { check_witness(&mut cx, &checks, &model)?; Ok(("refuted", stage)) }
        Outcome::Unknown(_) => Ok(("unknown", stage)),
        _ => Err("unexpected validity outcome".into()),
    }
}

pub(crate) fn validity(dir: &str) -> Result<()> {
    let mut files = fs::read_dir(dir)?.collect::<std::io::Result<Vec<_>>>()?;
    files.sort_by_key(|f| f.file_name());
    let mut counts = BTreeMap::new();
    for f in files {
        let path = f.path();
        if !f.file_type()?.is_file() || path.extension().is_none_or(|s| s != "txt") { continue; }
        // The handoff measures cold queries; don't share solver memo entries across files.
        let (answer, stage) = check(&fs::read_to_string(&path)?, &Retry::new()?)
            .map_err(|e| format!("{}: {e}", path.display()))?;
        println!("{}\t{answer}\t{stage}", f.file_name().to_string_lossy());
        *counts.entry((answer, stage)).or_insert(0usize) += 1;
    }
    if counts.is_empty() { return Err("no validity records found".into()); }
    for ((answer, stage), n) in &counts { eprintln!("{stage}\t{answer}\t{n}"); }
    if counts.keys().any(|(answer, _)| *answer == "unknown") { return Err("undecided validity records".into()); }
    Ok(())
}
