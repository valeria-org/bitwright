//! `--walk DIR`: a walk's exported questions, one directory per boundary, each boundary one
//! batch of a session that lasts the walk. See `docs/benchmarking.md`.
//!
//! A file is one question, "is root 0 a constant?": `# config: … conflicts=N propagations=N
//! nodes=N fuel=N`, `# deep fuel: N` (the budget of the retry for what stays open),
//! `# result: Constant(0x…) | Atom(#k) | Varies | Unknown`, `# ms: N` (what the walk's own
//! decision took), then `## root 0` and `## assume == V` blocks of bitwright text. A symbol
//! has one key in every file. A file without a result may say `# sampled: 0x…`, the value
//! at the exporter's samples: it is then compared as `Constant(0x…)`.

use std::collections::BTreeMap;
use std::process::ExitCode;
use std::time::Instant;

use bitwright::batch::{Answer, Ask, Config, Session, Split, Stats};
use bitwright::prove;
use bitwright::{Assumptions, BitVec, Context, Expr, Facts, ParseOptions, Width};

struct Question {
    name: String,
    result: String,
    ms: u64,
    root: String,
    assumes: Vec<(String, String)>,
}

fn field<'a>(text: &'a str, key: &str) -> Option<&'a str> {
    text.lines()
        .take_while(|l| !l.starts_with("## "))
        .find_map(|l| l.strip_prefix(key))
        .map(str::trim)
}

fn number(text: &str, key: &str) -> Option<u64> {
    let i = text.find(key)? + key.len();
    let digits: String = text[i..].chars().take_while(char::is_ascii_digit).collect();
    digits.parse().ok()
}

fn read(name: String, text: &str) -> Option<Question> {
    let mut q = Question {
        name,
        result: match (field(text, "# result:"), field(text, "# sampled:")) {
            (Some(r), _) => r.to_string(),
            (None, Some(v)) => format!("Constant({})", v.split(':').next().unwrap_or(v)),
            (None, None) => return None,
        },
        ms: field(text, "# ms:")
            .and_then(|v| v.parse().ok())
            .unwrap_or(0),
        root: String::new(),
        assumes: Vec::new(),
    };
    let mut block: Option<Option<String>> = None;
    let mut buf = String::new();
    let flush = |block: &Option<Option<String>>, buf: &mut String, q: &mut Question| match block {
        Some(None) if q.root.is_empty() => q.root = core::mem::take(buf),
        Some(Some(v)) => q.assumes.push((v.clone(), core::mem::take(buf))),
        _ => buf.clear(),
    };
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("## ") {
            flush(&block, &mut buf, &mut q);
            block = if rest.starts_with("root 0") {
                Some(None)
            } else {
                rest.strip_prefix("assume == ")
                    .map(|v| Some(v.trim().to_string()))
            };
        } else if block.is_some() {
            buf.push_str(line);
            buf.push('\n');
        }
    }
    flush(&block, &mut buf, &mut q);
    (!q.root.is_empty()).then_some(q)
}

fn value(text: &str, w: Width) -> BitVec {
    let s = text.split(':').next().unwrap_or(text);
    let v = match s.strip_prefix("0x") {
        Some(h) => u64::from_str_radix(h, 16).unwrap_or(0),
        None => s.parse::<i64>().unwrap_or(0) as u64,
    };
    BitVec::wrapping_from_u64(w, v)
}

/// What the batch said, in the words of the walk's `# result`.
fn said(a: &Answer) -> String {
    match a {
        Answer::Constant(v) => format!("Constant({:#x})", v.limbs()[0]),
        Answer::Varies(_) => "Varies".into(),
        Answer::Unknown(_) => "Unknown".into(),
        a => format!("{a:?}"),
    }
}

/// Process CPU seconds and peak resident megabytes, where `/proc` says.
fn process() -> (f64, f64) {
    let stat = std::fs::read_to_string("/proc/self/stat").unwrap_or_default();
    let fields: Vec<&str> = (stat.rsplit(')').next().unwrap_or(""))
        .split_whitespace()
        .collect();
    let tick = |k: usize| {
        fields
            .get(k)
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0)
    };
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let peak = status
        .lines()
        .find_map(|l| l.strip_prefix("VmHWM:"))
        .and_then(|l| l.split_whitespace().next()?.parse::<f64>().ok())
        .unwrap_or(0.0);
    ((tick(11) + tick(12)) as f64 / 100.0, peak / 1024.0)
}

fn add(total: &mut Stats, s: &Stats) {
    total.asks += s.asks;
    total.asks_stored += s.asks_stored;
    total.asks_repeated += s.asks_repeated;
    total.nodes_asked += s.nodes_asked;
    total.nodes_new += s.nodes_new;
    total.tasks_solved += s.tasks_solved;
    total.tasks_stored += s.tasks_stored;
    total.hubs += s.hubs;
    total.hubs_proved += s.hubs_proved;
    total.hubs_assumed += s.hubs_assumed;
    total.regrouped += s.regrouped;
    total.case_splits += s.case_splits;
    total.store_nodes += s.store_nodes;
    total.store_answers += s.store_answers;
    total.flushes += s.flushes;
}

/// `bitwright-bench --walk DIR [--mode whole|split|eager|shared] [--threads N] [--cases N]
/// [--no-deep] [--answers FILE]`.
pub fn main(args: &[String]) -> ExitCode {
    let mut dir = String::new();
    let mut mode = "split".to_string();
    let mut threads = 1usize;
    let mut deep = true;
    let mut cases: Option<u8> = None;
    let mut answers_file = None;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut next = || it.next().cloned().unwrap_or_default();
        match a.as_str() {
            "--walk" => dir = next(),
            "--mode" => mode = next(),
            "--threads" => threads = next().parse().unwrap_or(1),
            "--no-deep" => deep = false,
            "--cases" => cases = next().parse().ok(),
            "--answers" => answers_file = Some(next()),
            other => {
                eprintln!("unknown option `{other}`");
                return ExitCode::from(2);
            }
        }
    }
    let split = match mode.as_str() {
        "whole" => Split::none(),
        "eager" => Split::eager(),
        "shared" => Split::shared(),
        _ => Split::default(),
    };
    let split = match cases {
        Some(n) => split.with_cases(n),
        None => split,
    };
    let mut boundaries: Vec<_> = match std::fs::read_dir(&dir) {
        Ok(d) => (d.filter_map(|e| e.ok().map(|e| e.path())))
            .filter(|p| p.is_dir())
            .collect(),
        Err(e) => {
            eprintln!("{dir}: {e}");
            return ExitCode::from(2);
        }
    };
    boundaries.sort();
    // Every file read before the clock starts; the budgets from the first.
    let mut walk: Vec<(String, Vec<Question>)> = Vec::new();
    let (mut fuel, mut deep_fuel, mut limits) = (1 << 14, 1 << 19, (2_000, 20_000, 200_000));
    for b in &boundaries {
        let mut files: Vec<_> = match std::fs::read_dir(b) {
            Ok(d) => d.filter_map(|e| e.ok().map(|e| e.path())).collect(),
            Err(_) => continue,
        };
        files.sort();
        let mut qs = Vec::new();
        for f in files {
            let Ok(text) = std::fs::read_to_string(&f) else {
                continue;
            };
            if walk.is_empty() && qs.is_empty() {
                fuel = number(&text, "fuel=").unwrap_or(fuel);
                deep_fuel = number(&text, "# deep fuel: ").unwrap_or(deep_fuel);
                limits = (
                    number(&text, "conflicts=").unwrap_or(limits.0),
                    number(&text, "propagations=").unwrap_or(limits.1),
                    number(&text, "nodes=").unwrap_or(limits.2),
                );
            }
            let name = f
                .file_name()
                .unwrap_or_default()
                .to_string_lossy()
                .to_string();
            qs.extend(read(name, &text));
        }
        let name = b
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        walk.push((name, qs));
    }
    let proof = |fuel: u64| {
        prove::Config::default()
            .with_max_conflicts(limits.0)
            .with_max_propagations(limits.1)
            .with_max_nodes(limits.2 as usize)
            .with_simplify_fuel(fuel)
    };
    let session_of = |fuel: u64| {
        let config = Config::default()
            .with_threads(threads)
            .with_prove(proof(fuel))
            .with_split(split);
        Session::new(config)
    };
    let (stock, retry) = (session_of(fuel), session_of(deep_fuel));
    let started = Instant::now();
    let mut lines: Vec<String> = Vec::new();
    let mut tally: BTreeMap<String, u64> = BTreeMap::new();
    let mut against: BTreeMap<String, u64> = BTreeMap::new();
    let (mut asked, mut retried, mut walk_ms) = (0u64, 0u64, 0u64);
    for (boundary, qs) in &walk {
        // One context per boundary: what its questions share is built once.
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let mut roots: Vec<Expr> = Vec::new();
        let mut facts: Vec<Assumptions> = Vec::new();
        let mut kept: Vec<&Question> = Vec::new();
        for q in qs {
            let at = cx.checkpoint();
            let mut go = || -> Result<(Expr, Assumptions), bitwright::Error> {
                let root = cx.parse(&q.root, &o)?;
                let mut a = Assumptions::new();
                for (v, t) in &q.assumes {
                    let e = cx.parse(t, &o)?;
                    let v = value(v, cx.width(e)?);
                    a.assume(&mut cx, e, Facts::constant(&v))?;
                }
                Ok((root, a))
            };
            match go() {
                Ok((root, a)) => {
                    roots.push(root);
                    facts.push(a);
                    kept.push(q);
                }
                Err(e) => {
                    let _ = cx.rollback(at);
                    eprintln!("{boundary}/{}: {e}", q.name);
                }
            }
        }
        let ask = |k: usize| match facts[k].is_empty() {
            true => Ask::constant(roots[k]),
            false => Ask::constant(roots[k]).under(&facts[k]),
        };
        let asks: Vec<Ask<'_>> = (0..roots.len()).map(ask).collect();
        let mut replies = stock.run(&mut cx, &asks).expect("the batch runs");
        if deep {
            // What stays open is asked again with the walk's larger budget.
            let open: Vec<usize> = (0..replies.len())
                .filter(|&k| matches!(replies[k].answer, Answer::Unknown(_)))
                .collect();
            let again: Vec<Ask<'_>> = open.iter().map(|&k| ask(k)).collect();
            retried += open.len() as u64;
            let deeper = retry.run(&mut cx, &again).expect("the batch runs");
            for (k, r) in open.into_iter().zip(deeper) {
                replies[k] = r;
            }
        }
        for (q, r) in kept.iter().zip(&replies) {
            asked += 1;
            walk_ms += q.ms;
            let mine = said(&r.answer);
            // An atom is not a constant: the walk's `Atom` is this question's `Varies`.
            let theirs = match q.result.starts_with("Atom") {
                true => "Varies".to_string(),
                false => q.result.clone(),
            };
            let kind = |s: &str| s.split('(').next().unwrap_or(s).to_string();
            *tally.entry(kind(&mine)).or_default() += 1;
            let verdict = match mine == theirs {
                true => "same".to_string(),
                false => format!("walk {} / batch {}", kind(&theirs), kind(&mine)),
            };
            *against.entry(verdict).or_default() += 1;
            let c = &r.cost;
            lines.push(format!(
                "{boundary}/{} {mine} visits={} pass={} mba={} conflicts={} tasks={} | walk: {}",
                q.name,
                c.simplify.node_visits,
                c.simplify.pass_work,
                c.simplify.mba_steps,
                c.conflicts,
                c.tasks,
                q.result
            ));
        }
    }
    let wall = started.elapsed().as_secs_f64();
    let (cpu, peak) = process();
    let mut stats = Stats::default();
    add(&mut stats, &stock.stats());
    add(&mut stats, &retry.stats());
    println!(
        "mode={mode} threads={threads} boundaries={} questions={asked} retried={retried} \
         wall={wall:.2}s cpu={cpu:.2}s peak={peak:.0}MB (the walk's own decisions: {:.1}s)",
        walk.len(),
        walk_ms as f64 / 1e3
    );
    println!("answers: {tally:?}");
    println!("against the walk: {against:?}");
    let held = 100.0 * (1.0 - stats.nodes_new as f64 / stats.nodes_asked.max(1) as f64);
    println!(
        "nodes asked={} new={} ({held:.1}% already held); asks stored={} repeated={}; \
         tasks solved={} stored={}; hubs={} (under assumptions {}) proved={}; regrouped={} case splits={}; \
         store nodes={} answers={} flushes={}",
        stats.nodes_asked,
        stats.nodes_new,
        stats.asks_stored,
        stats.asks_repeated,
        stats.tasks_solved,
        stats.tasks_stored,
        stats.hubs,
        stats.hubs_assumed,
        stats.hubs_proved,
        stats.regrouped,
        stats.case_splits,
        stats.store_nodes,
        stats.store_answers,
        stats.flushes
    );
    if let Some(f) = answers_file {
        let _ = std::fs::write(f, lines.join("\n") + "\n");
    }
    ExitCode::SUCCESS
}
