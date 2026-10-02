//! bitwright's benchmarks, measured in user-space instructions retired (Linux hardware
//! counters) and thread CPU time, so that results do not move with other load on the machine.
//! See `docs/benchmarking.md`.
//!
//! ```text
//! cargo run --release -p bitwright-bench -- [FILTER...] [OPTIONS]
//!   FILTER            run benchmarks whose name contains any FILTER
//!   --list            list the benchmarks
//!   --samples N       measured samples per benchmark (default 7)
//!   --quick           a tenth of the iterations and 3 samples (a smoke run)
//!   --save FILE       write the results as CSV
//!   --compare FILE    compare with results saved earlier
//!   --threshold PCT   smallest change reported as one (default 1 for instructions, 5 for CPU time)
//!   --metric M        compare `instructions` (default when available) or `cpu`
//!   --fail-on-regression   exit 1 if a benchmark got slower beyond the threshold
//!   --corpus-diff     print how the MBA defaults differ from the signature solver's results
//!   --mixers          staged mixer/fingerprint CSV (fixed budgets; FILTERs select cases)
//!   --escalate        with --mixers: try small witnesses, then resume open native searches
//!   --escalate-fast   omit the final 500-million-propagation escalation stage
//!   --relations       with --mixers: add certified transitive bit-equality lemmas
//!   --selectors       with --mixers: initially prefer small variable-shift count bits
//!   --input-cancel    with --mixers: cancel shared inputs through bounded XOR paths
//!   --factor-joins    with --mixers: factor positive OR targets sharing an XOR operand
//!   --xor3            with --mixers: inline private XORs into three-input parity gates
//!   --carry-save      with --mixers: compress multiplier columns before the final addition
//!   --word-samples    with --mixers: try machine-word samples before building circuits
//!   --query-budget-ms N   with --mixers: require each fresh native query to settle within N ms,
//!                         including preparation, certificate checking and original model replay
//! ```

mod bench;
mod corpus_diff;
mod counter;
mod keyed_mixers;
mod suites;
mod workload;

use std::process::ExitCode;

use bench::{Saved, Summary};

#[derive(Debug)]
struct Options {
    filters: Vec<String>,
    list: bool,
    samples: usize,
    scale: f64,
    save: Option<String>,
    compare: Option<String>,
    threshold: Option<f64>,
    metric: Option<Metric>,
    fail_on_regression: bool,
    corpus_diff: bool,
    mixers: bool,
    escalate: bool,
    fast: bool,
    relations: bool,
    selectors: bool,
    input_cancellation: bool,
    join_factoring: bool,
    xor3: bool,
    carry_save: bool,
    word_sampling: bool,
    query_budget_ns: Option<u64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Metric {
    Instructions,
    Cpu,
}

fn parse_args() -> Result<Options, String> {
    let mut o = Options {
        filters: Vec::new(),
        list: false,
        samples: 7,
        scale: 1.0,
        save: None,
        compare: None,
        threshold: None,
        metric: None,
        fail_on_regression: false,
        corpus_diff: false,
        mixers: false,
        escalate: false,
        fast: false,
        relations: false,
        selectors: false,
        input_cancellation: false,
        join_factoring: false,
        xor3: false,
        carry_save: false,
        word_sampling: false,
        query_budget_ns: None,
    };
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        let mut value = |name: &str| args.next().ok_or(format!("{name} needs a value"));
        match a.as_str() {
            "--list" => o.list = true,
            "--quick" => {
                o.scale = 0.1;
                o.samples = 3;
            }
            "--samples" => {
                o.samples = value("--samples")?
                    .parse()
                    .map_err(|_| "--samples takes a number")?
            }
            "--save" => o.save = Some(value("--save")?),
            "--compare" => o.compare = Some(value("--compare")?),
            "--threshold" => {
                o.threshold = Some(
                    value("--threshold")?
                        .parse()
                        .map_err(|_| "--threshold takes a percentage")?,
                )
            }
            "--metric" => {
                o.metric = Some(match value("--metric")?.as_str() {
                    "instructions" => Metric::Instructions,
                    "cpu" => Metric::Cpu,
                    m => return Err(format!("unknown metric `{m}`")),
                })
            }
            "--fail-on-regression" => o.fail_on_regression = true,
            "--corpus-diff" => o.corpus_diff = true,
            "--mixers" => o.mixers = true,
            "--escalate" => o.escalate = true,
            "--escalate-fast" => {
                o.escalate = true;
                o.fast = true;
            }
            "--relations" => o.relations = true,
            "--selectors" => o.selectors = true,
            "--input-cancel" => o.input_cancellation = true,
            "--factor-joins" => o.join_factoring = true,
            "--xor3" => o.xor3 = true,
            "--carry-save" => o.carry_save = true,
            "--word-samples" => o.word_sampling = true,
            "--query-budget-ms" => {
                let ms: u64 = value("--query-budget-ms")?
                    .parse()
                    .map_err(|_| "--query-budget-ms takes positive whole milliseconds")?;
                o.query_budget_ns = Some(
                    ms.checked_mul(1_000_000)
                        .filter(|&ns| ns != 0)
                        .ok_or("--query-budget-ms must be positive and fit in nanoseconds")?,
                );
            }
            // `cargo bench` passes this; accept it so the binary works as a bench target too.
            "--bench" => {}
            f if f.starts_with("--") => return Err(format!("unknown option `{f}`")),
            f => o.filters.push(f.to_string()),
        }
    }
    Ok(o)
}

fn main() -> ExitCode {
    // Internal workers are separate processes for a meaningful per-fixture memory peak.
    let worker: Vec<String> = std::env::args().skip(1).collect();
    if worker.first().is_some_and(|a| a == "--mixer-case") {
        if worker.len() < 4
            || worker[4..].iter().any(|arg| {
                ![
                    "escalate",
                    "fast",
                    "relations",
                    "selectors",
                    "input-cancel",
                    "factor-joins",
                    "xor3",
                    "carry-save",
                    "word-samples",
                ]
                .contains(&arg.as_str())
                    && !arg
                        .strip_prefix("query-budget-ns=")
                        .is_some_and(|value| value.parse::<u64>().is_ok_and(|ns| ns != 0))
            })
            || !["nested", "compact"].contains(&worker[2].as_str())
            || !["raw", "simplified"].contains(&worker[3].as_str())
        {
            eprintln!("invalid keyed-mixer worker arguments");
            return ExitCode::from(2);
        }
        return keyed_mixers::worker(
            &worker[1],
            worker[2] == "compact",
            worker[3] == "simplified",
            keyed_mixers::SearchOptions {
                escalate: worker[4..]
                    .iter()
                    .any(|arg| arg == "escalate" || arg == "fast"),
                relations: worker[4..].iter().any(|arg| arg == "relations"),
                selectors: worker[4..].iter().any(|arg| arg == "selectors"),
                input_cancellation: worker[4..].iter().any(|arg| arg == "input-cancel"),
                join_factoring: worker[4..].iter().any(|arg| arg == "factor-joins"),
                xor3: worker[4..].iter().any(|arg| arg == "xor3"),
                carry_save: worker[4..].iter().any(|arg| arg == "carry-save"),
                word_sampling: worker[4..].iter().any(|arg| arg == "word-samples"),
                fast: worker[4..].iter().any(|arg| arg == "fast"),
                query_budget_ns: worker[4..]
                    .iter()
                    .find_map(|arg| arg.strip_prefix("query-budget-ns=")?.parse().ok()),
            },
        );
    }
    let opts = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::from(2);
        }
    };
    if (opts.escalate
        || opts.relations
        || opts.selectors
        || opts.input_cancellation
        || opts.join_factoring
        || opts.xor3
        || opts.carry_save
        || opts.word_sampling
        || opts.query_budget_ns.is_some())
        && !opts.mixers
    {
        eprintln!("mixer search options require --mixers");
        return ExitCode::from(2);
    }
    if opts.corpus_diff {
        corpus_diff::report();
        return ExitCode::SUCCESS;
    }
    if opts.query_budget_ns.is_some() && opts.escalate {
        eprintln!(
            "--query-budget-ms measures one fresh query and cannot be combined with escalation"
        );
        return ExitCode::from(2);
    }
    if opts.query_budget_ns.is_some() && opts.word_sampling {
        eprintln!("--query-budget-ms uses zero samples and cannot be combined with --word-samples");
        return ExitCode::from(2);
    }
    if opts.mixers {
        if worker.iter().any(|arg| {
            arg.starts_with("--")
                && ![
                    "--mixers",
                    "--escalate",
                    "--escalate-fast",
                    "--relations",
                    "--selectors",
                    "--input-cancel",
                    "--factor-joins",
                    "--xor3",
                    "--carry-save",
                    "--word-samples",
                    "--query-budget-ms",
                ]
                .contains(&arg.as_str())
        }) {
            eprintln!(
                "--mixers takes filters and search-strategy flags; redirect stdout to save staged CSV"
            );
            return ExitCode::from(2);
        }
        return keyed_mixers::report(
            &opts.filters,
            keyed_mixers::SearchOptions {
                escalate: opts.escalate,
                relations: opts.relations,
                selectors: opts.selectors,
                input_cancellation: opts.input_cancellation,
                join_factoring: opts.join_factoring,
                xor3: opts.xor3,
                carry_save: opts.carry_save,
                word_sampling: opts.word_sampling,
                fast: opts.fast,
                query_budget_ns: opts.query_budget_ns,
            },
        );
    }
    let benches: Vec<_> = suites::all()
        .into_iter()
        .filter(|b| opts.filters.is_empty() || opts.filters.iter().any(|f| b.name.contains(f)))
        .collect();
    if opts.list {
        for b in &benches {
            println!("{:<32} {:>8} x {}", b.name, b.iters, b.unit);
        }
        return ExitCode::SUCCESS;
    }
    let baseline = match &opts.compare {
        Some(path) => match std::fs::read_to_string(path)
            .map_err(|e| e.to_string())
            .and_then(|t| bench::parse_saved(&t))
        {
            Ok(v) => Some(v),
            Err(e) => {
                eprintln!("error: cannot read {path}: {e}");
                return ExitCode::from(2);
            }
        },
        None => None,
    };

    let mut counters = counter::Counters::open();
    let metric = opts.metric.unwrap_or(if counters.counts_instructions() {
        Metric::Instructions
    } else {
        Metric::Cpu
    });
    if let Some(why) = &counters.unavailable {
        eprintln!("note: instructions are not counted ({why}); comparing CPU time");
        if metric == Metric::Instructions {
            eprintln!("error: --metric instructions needs hardware counters");
            return ExitCode::from(2);
        }
    }
    let threshold = opts.threshold.unwrap_or(match metric {
        Metric::Instructions => 1.0,
        Metric::Cpu => 5.0,
    }) / 100.0;

    println!(
        "{}",
        row([
            "benchmark",
            "instr",
            "spread",
            "cpu (min)",
            "cpu (med)",
            "wall (med)",
            "per",
        ])
    );
    let mut summaries = Vec::new();
    let mut regressions = 0usize;
    for b in &benches {
        let s = bench::run(b, &mut counters, opts.samples, opts.scale);
        let (instr, spread) = match (s.instructions, s.instruction_spread()) {
            (Some((m, _, _)), Some(sp)) => (bench::si(m), format!("{:.2}%", sp * 100.0)),
            _ => ("-".into(), "-".into()),
        };
        let mut line = row([
            &s.name,
            &instr,
            &spread,
            &bench::duration(s.cpu_ns.0),
            &bench::duration(s.cpu_ns.1),
            &bench::duration(s.wall_ns),
            &s.unit,
        ]);
        if let Some(base) = &baseline
            && let Some((_, old)) = base.iter().find(|(n, _)| *n == s.name)
        {
            let (verdict, slower) = compare(&s, old, metric, threshold);
            line.push_str(&format!("   {verdict}"));
            regressions += usize::from(slower);
        }
        println!("{line}");
        if let Some(note) = b.note() {
            println!("{:32}{note}", "");
        }
        summaries.push(s);
    }
    if let Some(path) = &opts.save {
        let mut text = format!(
            "# bitwright-bench results; metric source: {}\n{}\n",
            if counters.counts_instructions() {
                "instructions + cpu"
            } else {
                "cpu only"
            },
            bench::CSV_HEADER
        );
        for s in &summaries {
            text.push_str(&bench::csv_line(s));
            text.push('\n');
        }
        if let Err(e) = std::fs::write(path, text) {
            eprintln!("error: cannot write {path}: {e}");
            return ExitCode::from(2);
        }
    }
    if opts.fail_on_regression && regressions > 0 {
        eprintln!("{regressions} benchmark(s) slower than the baseline");
        return ExitCode::from(1);
    }
    ExitCode::SUCCESS
}

/// One line of the report.
fn row(c: [&str; 7]) -> String {
    format!(
        "{:<30} {:>10} {:>7} {:>11} {:>11} {:>11}  {}",
        c[0], c[1], c[2], c[3], c[4], c[5], c[6]
    )
}

/// The change from `old` to `new` in `metric`, and whether it is a regression. A change counts
/// only past the threshold and past the samples' own spread.
fn compare(new: &Summary, old: &Saved, metric: Metric, threshold: f64) -> (String, bool) {
    let (now, then, noise) = match metric {
        Metric::Instructions => match (new.instructions, old.instructions) {
            (Some((m, _, _)), Some((o, spread))) => {
                (m, o, new.instruction_spread().unwrap_or(0.0).max(spread))
            }
            _ => return ("(no instruction counts)".into(), false),
        },
        Metric::Cpu => (new.cpu_ns.0, old.cpu_ns_min, 0.0),
    };
    if then <= 0.0 {
        return ("(no baseline)".into(), false);
    }
    let delta = now / then - 1.0;
    let significant = delta.abs() > threshold.max(2.0 * noise);
    let verdict = if !significant {
        format!("{:+.2}%", delta * 100.0)
    } else if delta < 0.0 {
        format!("{:+.2}% faster", delta * 100.0)
    } else {
        format!("{:+.2}% SLOWER", delta * 100.0)
    };
    (verdict, significant && delta > 0.0)
}
