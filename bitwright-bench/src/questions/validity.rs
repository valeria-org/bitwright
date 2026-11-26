//! Replay one captured `#Q` validity record per file. Unknown is not a negative result.
use super::{Retry, check_witness};
use bitwright::batch::{self, Answer, Ask, Session, Split};
use bitwright::engine::{Budget, Engine, Run};
use bitwright::prove::{self, Config, Limits, Outcome, Question, Unknown};
use bitwright::{Assumptions, Context, Expr, ParseOptions, Width};
use std::{collections::BTreeMap, error::Error, fs};

mod large;
mod ring;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

// The captured configuration is a Debug dump, not a versioned interchange format.
// Reconstruct only settings we understand; reject, rather than ignore, any difference.
fn config(text: &str) -> Result<Config> {
    let number = |key: &str| -> Result<u64> {
        Ok(text
            .split_once(key)
            .ok_or_else(|| format!("missing {key}"))?
            .1
            .split(',')
            .next()
            .unwrap()
            .parse()?)
    };
    let mut c = Config::default()
        .with_simplify_fuel(number("node_visits: ")?)
        .with_sweeping(false);
    c.max_nodes = number("max_nodes: ")?.try_into()?;
    c.max_conflicts = number("max_conflicts: ")?;
    c.max_propagations = number("max_propagations: ")?;
    if format!("{c:?}") != text {
        return Err("unsupported recorded configuration".into());
    }
    Ok(c)
}

fn recoverable(o: &Outcome) -> bool {
    matches!(
        o,
        Outcome::Unknown(Unknown::Budget { .. } | Unknown::TooLarge { .. })
    )
}

fn reduce(
    cx: &mut Context,
    engine: &Engine,
    mut bad: Expr,
    fuel: u64,
    rounds: usize,
) -> Result<Expr> {
    for _ in 0..rounds {
        let run = Run::default().with_per_call(Budget::fuel(fuel));
        let next = engine.run(cx, &[bad], run)?.roots[0].expr;
        if next == bad {
            break;
        }
        bad = next;
        if cx.as_const(bad)?.is_some() {
            break;
        }
    }
    Ok(bad)
}

fn check(text: &str, engines: &Retry, recover: bool) -> Result<(&'static str, &'static str)> {
    let (header, body) = text.split_once("\n#ROOT ").ok_or("missing #ROOT")?;
    let cfg = config(
        header
            .lines()
            .find_map(|l| l.strip_prefix("#CFG "))
            .ok_or("missing #CFG")?,
    )?;
    let record = header
        .lines()
        .find_map(|l| l.strip_prefix("#Q "))
        .ok_or("missing #Q")?;
    let walk = match record
        .split_whitespace()
        .find_map(|s| s.strip_prefix("walk_simplifiers="))
    {
        Some("true") => true,
        Some("false") => false,
        _ => return Err("unsupported recorded simplifier profile".into()),
    };
    let count: usize = record
        .split_whitespace()
        .find_map(|s| s.strip_prefix("preds="))
        .ok_or("missing preds count")?
        .parse()?;
    let body = body
        .trim_end()
        .strip_suffix("\n#END")
        .ok_or("missing #END")?;
    let mut cx = Context::new();
    let parse = ParseOptions::width(Width::W64);
    let checks = body
        .split("\n#A ")
        .map(|s| cx.parse(s, &parse))
        .collect::<std::result::Result<Vec<_>, _>>()?;
    let (&root, preds) = checks.split_first().ok_or("missing predicate")?;
    if preds.len() != count {
        return Err("assumption count mismatch".into());
    }
    let mut assumptions = Assumptions::new();
    for &p in preds {
        assumptions.assume_true(&mut cx, p)?;
    }
    let under = (!preds.is_empty()).then_some(&assumptions);
    // Document-plan checks use the ordinary prover, without the walk's MBA
    // configuration. Keep its caches private to this cold replay as well.
    let mut outcome = if walk {
        prove::valid_under_with(&mut cx, root, under, &cfg, &engines.stock)?
    } else {
        prove::valid_under_with(&mut cx, root, under, &cfg, &prove::Simplifiers::new())?
    };
    let mut stage = "asked";
    if recover && recoverable(&outcome) {
        // Simplify the counterexample, not each conjunct independently. A zero is
        // a proof even when reaching it used a relationship between two conjuncts.
        let mut bad = cx.not(root)?;
        for &p in preds {
            bad = cx.and(bad, p)?;
        }
        bad = reduce(&mut cx, &engines.word, bad, 1 << 19, 3)?;
        if cx.as_const(bad)?.is_some_and(|v| v.is_zero()) {
            return Ok(("proved", "forms"));
        }
        let mut valid = cx.not(bad)?;
        let residual = cfg.with_simplify(false);
        let mut q = Question::valid(&mut cx, valid, &residual)?;
        stage = "residual";
        outcome = q.solve(&mut cx, cfg.limits())?;
        if matches!(outcome, Outcome::Unknown(Unknown::TooLarge { .. })) {
            // Spend more on the word expression only when its residual will not fit.
            // Rebuilding an unchanged residual with the same node cap cannot help.
            let smaller = reduce(&mut cx, &engines.word, bad, 1 << 22, 2)?;
            if cx.as_const(smaller)?.is_some_and(|v| v.is_zero()) {
                return Ok(("proved", "deep-forms"));
            }
            if smaller != bad {
                valid = cx.not(smaller)?;
                q = Question::valid(&mut cx, valid, &residual)?;
                stage = "deep-residual";
                outcome = q.solve(&mut cx, cfg.limits())?;
            }
        }
        if matches!(outcome, Outcome::Unknown(Unknown::Budget { .. })) {
            // Resume the same search: no clause loss, rebuilding or repeated warmup.
            stage = "search";
            outcome = q.solve(
                &mut cx,
                Limits {
                    conflicts: 100_000,
                    propagations: 20_000_000,
                },
            )?;
            if matches!(outcome, Outcome::Unknown(Unknown::Budget { .. })) {
                // Try bounded proofs of shared subexpressions and selector cases
                // instead of spending a third budget on the same SAT instance.
                let split_cfg = cfg
                    .with_simplify_fuel(1 << 17)
                    .with_word_sampling(true)
                    .with_max_conflicts(cfg.max_conflicts.min(2_000))
                    .with_max_propagations(cfg.max_propagations.min(20_000))
                    .with_max_nodes(cfg.max_nodes.min(200_000));
                let session = Session::with_simplifiers(
                    batch::Config::default()
                        .with_threads(1)
                        .with_prove(split_cfg)
                        .with_split(Split::shared()),
                    prove::Simplifiers::new()
                        .with_mba(engines.forms)
                        .with_mba_solver(engines.solver.clone()),
                );
                let ask = under.map_or(Ask::valid(root), |a| Ask::valid(root).under(a));
                let reply = session
                    .run(&mut cx, &[ask])?
                    .pop()
                    .ok_or("missing split result")?;
                stage = "split";
                match reply.answer {
                    Answer::Proved => outcome = Outcome::Proved(None),
                    Answer::Refuted(m) => outcome = Outcome::Refuted(m),
                    Answer::Unknown(_) => {}
                    _ => return Err("unexpected split answer".into()),
                }
            }
        }
        if recoverable(&outcome) && ring::proved(&mut cx, &engines.word, bad)? {
            return Ok(("proved", "word-equality"));
        }
        if matches!(outcome, Outcome::Unknown(Unknown::TooLarge { .. })) {
            // Only rebuild if the circuit, rather than the search, hit its ceiling.
            // A failed wide attempt can still benefit from word-level splits.
            const WIDE_NODES: usize = 1 << 19;
            if cfg.max_nodes < WIDE_NODES {
                let wider = residual.with_max_nodes(WIDE_NODES);
                let mut wide = Question::valid(&mut cx, valid, &wider)?;
                stage = "wide-residual";
                outcome = wide.solve(
                    &mut cx,
                    Limits {
                        conflicts: 2_000,
                        propagations: 200_000,
                    },
                )?;
                if matches!(outcome, Outcome::Unknown(Unknown::Budget { .. })) {
                    outcome = wide.solve(
                        &mut cx,
                        Limits {
                            conflicts: 20_000,
                            propagations: 4_000_000,
                        },
                    )?;
                }
            }
            if recoverable(&outcome)
                && let Some((answer, via)) = large::recover(&mut cx, &checks, engines)?
            {
                outcome = answer;
                stage = via;
            }
        }
    }
    match outcome {
        Outcome::Proved(_) => Ok(("proved", stage)),
        Outcome::Refuted(model) => {
            check_witness(&mut cx, &checks, &model)?;
            Ok(("refuted", stage))
        }
        Outcome::Unknown(_) => Ok(("unknown", stage)),
        _ => Err("unexpected validity outcome".into()),
    }
}

pub(crate) fn validity(dir: &str, recover: bool) -> Result<()> {
    let mut files = fs::read_dir(dir)?.collect::<std::io::Result<Vec<_>>>()?;
    files.sort_by_key(|f| f.file_name());
    let mut counts = BTreeMap::new();
    for f in files {
        let path = f.path();
        if !f.file_type()?.is_file() || path.extension().is_none_or(|s| s != "txt") {
            continue;
        }
        // The handoff measures cold queries; don't share solver memo entries across files.
        let (answer, stage) = check(&fs::read_to_string(&path)?, &Retry::new()?, recover)
            .map_err(|e| format!("{}: {e}", path.display()))?;
        println!("{}\t{answer}\t{stage}", f.file_name().to_string_lossy());
        *counts.entry((answer, stage)).or_insert(0usize) += 1;
    }
    if counts.is_empty() {
        return Err("no validity records found".into());
    }
    for ((answer, stage), n) in &counts {
        eprintln!("{stage}\t{answer}\t{n}");
    }
    if counts.keys().any(|(answer, _)| *answer == "unknown") {
        return Err("undecided validity records".into());
    }
    Ok(())
}
