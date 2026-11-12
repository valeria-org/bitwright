//! `--batch DIR`: a consumer's exported questions, asked one by one as it asks them today and
//! through [`bitwright::batch`]. See `docs/benchmarking.md`.
//!
//! A file is one question: `# kind: K` (`engine`, `simplify`, `forms_simplify`, `equal`,
//! `valid_under`, `satisfy_values`), `# config: …` (`fuel=N` and `mba=stock|forms` for the
//! engine; `conflicts=N propagations=N nodes=N` for a proof), then `## root N` and
//! `## assume == V` blocks of bitwright text with symbol widths. Other lines are ignored.

use std::collections::BTreeMap;
use std::process::ExitCode;
use std::sync::Arc;
use std::time::Instant;

use bitwright::batch::{Answer, Ask, Cancel, Config, Reply, Session, Split};
use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::{MbaConfig, NfOptions, NormalFormSolver};
use bitwright::prove;
use bitwright::{Assumptions, BitVec, CmpOp, Context, Expr, Facts, ParseOptions, UnOp, Width};

#[derive(Debug)]
struct Dump {
    name: String,
    kind: String,
    config: String,
    roots: Vec<String>,
    assumes: Vec<(String, String)>,
}

fn read(name: &str, text: &str) -> Dump {
    let mut d = Dump {
        name: name.into(),
        kind: String::new(),
        config: String::new(),
        roots: Vec::new(),
        assumes: Vec::new(),
    };
    #[derive(PartialEq)]
    enum Sec {
        Head,
        Root,
        Assume(String),
        Other,
    }
    let mut sec = Sec::Head;
    let mut buf = String::new();
    let flush = |sec: &Sec, buf: &mut String, d: &mut Dump| match sec {
        Sec::Root => d.roots.push(core::mem::take(buf)),
        Sec::Assume(v) => d.assumes.push((v.clone(), core::mem::take(buf))),
        _ => buf.clear(),
    };
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("## ") {
            flush(&sec, &mut buf, &mut d);
            sec = if rest.starts_with("root") {
                Sec::Root
            } else if let Some(v) = rest.strip_prefix("assume == ") {
                Sec::Assume(v.trim().into())
            } else {
                Sec::Other
            };
        } else if sec == Sec::Head {
            if let Some(v) = line.strip_prefix("# kind: ") {
                d.kind = v.trim().into();
            } else if let Some(v) = line.strip_prefix("# config: ") {
                d.config = v.trim().into();
            }
        } else if matches!(sec, Sec::Root | Sec::Assume(_)) {
            buf.push_str(line);
            buf.push('\n');
        }
    }
    flush(&sec, &mut buf, &mut d);
    d
}

fn number(config: &str, key: &str) -> Option<u64> {
    let i = config.find(&format!("{key}="))? + key.len() + 1;
    let digits: String = config[i..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    digits.parse().ok()
}

/// `text` with every symbol `#N` renamed `#(N + base)`.
fn renamed(text: &str, base: u64) -> String {
    let mut out = String::with_capacity(text.len() + 16);
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        out.push(c);
        if c == '#' {
            let mut digits = String::new();
            while let Some(d) = chars.peek().filter(|d| d.is_ascii_digit()) {
                digits.push(*d);
                chars.next();
            }
            match digits.parse::<u64>() {
                Ok(n) => out.push_str(&(n + base).to_string()),
                Err(_) => out.push_str(&digits),
            }
        }
    }
    out
}

fn value(text: &str, w: Width) -> BitVec {
    let s = text.split(':').next().unwrap_or(text);
    let v = match s.strip_prefix("0x") {
        Some(h) => u64::from_str_radix(h, 16).unwrap_or(0),
        None => s.parse::<i64>().unwrap_or(0) as u64,
    };
    BitVec::wrapping_from_u64(w, v)
}

/// One way of asking: every question that shares it is one session's.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct How {
    engine: bool,
    forms: bool,
    fuel: u64,
    conflicts: u64,
    propagations: u64,
    nodes: u64,
}

fn how(d: &Dump) -> How {
    let engine = matches!(d.kind.as_str(), "engine" | "simplify" | "forms_simplify");
    let p = prove::Config::default();
    How {
        engine,
        forms: d.config.contains("mba=forms"),
        fuel: number(&d.config, "fuel").unwrap_or(1 << 22),
        conflicts: number(&d.config, "conflicts").unwrap_or(p.max_conflicts),
        propagations: number(&d.config, "propagations").unwrap_or(p.max_propagations),
        nodes: number(&d.config, "nodes").unwrap_or(p.max_nodes as u64),
    }
}

fn mba_of(h: &How) -> MbaConfig {
    let stock = MbaConfig::default().with_opaque_sweep(true);
    match h.forms {
        true => stock.with_noise_forms(true).with_known_atoms(true),
        false => stock,
    }
}

fn prove_of(h: &How) -> prove::Config {
    let cfg = prove::Config::default()
        .with_max_conflicts(h.conflicts)
        .with_max_propagations(h.propagations)
        .with_max_nodes(h.nodes as usize);
    match h.engine {
        // Asked as "is it a constant?", an engine question is a proof: within the
        // consumer's limits for one.
        true => cfg
            .with_simplify_fuel(h.fuel)
            .with_max_conflicts(2_000)
            .with_max_propagations(20_000)
            .with_max_nodes(200_000),
        false => cfg,
    }
}

/// Variant `v` of a question: each root plus `8 v`, as one address of many over one body.
fn vary(cx: &mut Context, roots: &mut [Expr], v: u64) {
    if v == 0 {
        return;
    }
    for r in roots {
        let w = cx.width(*r).expect("a root of the context");
        let step = cx
            .constant(&BitVec::wrapping_from_u64(w, 8 * v))
            .expect("a constant");
        *r = cx.bin(bitwright::BinOp::Add, *r, step).expect("a sum");
    }
}

/// A question built in a context: its roots and constraints.
struct Built {
    roots: Vec<Expr>,
    assumes: Vec<(Expr, BitVec)>,
}

fn build(cx: &mut Context, d: &Dump, base: u64) -> Result<Built, String> {
    let o = ParseOptions::width(Width::W64);
    let mut b = Built {
        roots: Vec::new(),
        assumes: Vec::new(),
    };
    let at = cx.checkpoint();
    let mut go = || -> Result<(), bitwright::Error> {
        for t in &d.roots {
            b.roots.push(cx.parse(&renamed(t, base), &o)?);
        }
        for (v, t) in &d.assumes {
            let e = cx.parse(&renamed(t, base), &o)?;
            b.assumes.push((e, value(v, cx.width(e)?)));
        }
        Ok(())
    };
    match go() {
        Ok(()) => Ok(b),
        Err(e) => {
            let _ = cx.rollback(at);
            Err(format!("{}: {e}", d.name))
        }
    }
}

fn label(a: &Answer) -> &'static str {
    match a {
        Answer::Simplified { .. } => "simplified",
        Answer::Constant(_) => "constant",
        Answer::Varies(_) => "varies",
        Answer::Proved => "proved",
        Answer::Refuted(_) => "refuted",
        Answer::Unknown(_) => "unknown",
        Answer::Cancelled => "cancelled",
        _ => "other",
    }
}

/// Process CPU seconds and peak resident megabytes, where `/proc` says.
fn process() -> (f64, f64) {
    let stat = std::fs::read_to_string("/proc/self/stat").unwrap_or_default();
    let fields: Vec<&str> = stat
        .rsplit(')')
        .next()
        .unwrap_or("")
        .split_whitespace()
        .collect();
    let ticks: u64 = (fields
        .get(11)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(0))
        + fields
            .get(12)
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let peak = status
        .lines()
        .find_map(|l| l.strip_prefix("VmHWM:"))
        .and_then(|l| l.split_whitespace().next()?.parse::<f64>().ok())
        .unwrap_or(0.0);
    (ticks as f64 / 100.0, peak / 1024.0)
}

/// `bitwright-bench --batch DIR [--mode before|whole|split] [--threads N] [--shared-symbols]
/// [--warm] [--constant] [--cancel-after MS] [--answers FILE] [--only KIND]`.
pub fn main(args: &[String]) -> ExitCode {
    let mut dir = None;
    let mut mode = "split".to_string();
    let mut threads = 1usize;
    let mut shared = false;
    let mut warm = false;
    let mut constant = false;
    let mut answers_file = None;
    let mut only: Option<String> = None;
    let mut cancel_after: Option<u64> = None;
    let mut split = Split::eager();
    let mut variants = 1u64;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut next = || it.next().cloned().unwrap_or_default();
        match a.as_str() {
            "--batch" => dir = Some(next()),
            "--mode" => mode = next(),
            "--threads" => threads = next().parse().unwrap_or(1),
            "--shared-symbols" => shared = true,
            "--warm" => warm = true,
            "--constant" => constant = true,
            "--answers" => answers_file = Some(next()),
            "--only" => only = Some(next()),
            "--cancel-after" => cancel_after = next().parse().ok(),
            "--no-nested" => split = split.with_nested(false),
            "--no-terms" => split = split.with_terms(false),
            "--whole-first" => split = split.with_whole_first(true),
            "--variants" => variants = next().parse().unwrap_or(1).max(1),
            "--cases" => split = split.with_cases(next().parse().unwrap_or(1)),
            "--points" => split = split.with_points(next().parse().unwrap_or(64)),
            other => {
                eprintln!("unknown option `{other}`");
                return ExitCode::from(2);
            }
        }
    }
    let Some(dir) = dir else {
        eprintln!("--batch needs a directory");
        return ExitCode::from(2);
    };
    let mut files: Vec<_> = match std::fs::read_dir(&dir) {
        Ok(d) => d.filter_map(|e| e.ok().map(|e| e.path())).collect(),
        Err(e) => {
            eprintln!("{dir}: {e}");
            return ExitCode::from(2);
        }
    };
    files.sort();
    let mut dumps = Vec::new();
    for f in files {
        let name = f
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        let Ok(text) = std::fs::read_to_string(&f) else {
            continue;
        };
        let d = read(&name, &text);
        if d.roots.is_empty()
            || only
                .as_ref()
                .is_some_and(|k| !d.kind.starts_with(k.as_str()))
        {
            continue;
        }
        dumps.push(d);
    }
    // Each question's symbols: its own, or with `--shared-symbols` those of the questions
    // before it where the widths agree. The same names in every mode: what the engine makes
    // of a question depends on its symbols' keys.
    let mut naming = Context::new();
    let bases: Vec<u64> = (dumps.iter().enumerate())
        .map(|(k, d)| match shared && build(&mut naming, d, 0).is_ok() {
            true => 0,
            false => (k as u64 + 1) * 1_000_000,
        })
        .collect();
    drop(naming);
    let started = Instant::now();
    let mut lines: Vec<String> = Vec::new();
    let mut tally: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut stats = bitwright::batch::Stats::default();
    let mut second = 0.0;
    if mode == "before" {
        // As the consumer asks today: a context per question, one solver for the engines.
        let solver = Arc::new(NormalFormSolver::new(
            NfOptions::default().with_memo(1 << 14),
        ));
        let mut engines: BTreeMap<How, Engine> = BTreeMap::new();
        for (d, base, v) in (dumps.iter().zip(&bases))
            .flat_map(|(d, base)| (0..variants).map(move |v| (d, base, v)))
        {
            let mut cx = Context::new();
            let mut b = match build(&mut cx, d, *base) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("{e}");
                    continue;
                }
            };
            vary(&mut cx, &mut b.roots, v);
            let h = how(d);
            let mut assumptions = Assumptions::new();
            for (e, v) in &b.assumes {
                let _ = assumptions.assume(&mut cx, *e, Facts::constant(v));
            }
            let under = (!b.assumes.is_empty()).then_some(&assumptions);
            let said = if h.engine {
                let engine = engines.entry(h.clone()).or_insert_with(|| {
                    Engine::builder()
                        .builtin()
                        .strategy(Strategy::deobfuscate().with_mba(mba_of(&h)))
                        .mba_solver(solver.clone())
                        .build()
                        .expect("the engine links")
                });
                let mut run = Run::default().with_per_call(Budget::fuel(h.fuel));
                if let Some(a) = under {
                    run = run.with_assumptions(a);
                }
                let out = engine
                    .run(&mut cx, &b.roots[..1], run)
                    .expect("the engine runs");
                match cx.as_const(out.roots[0].expr).is_ok_and(|v| v.is_some()) {
                    true => "constant",
                    false => "simplified",
                }
            } else {
                let cfg = prove_of(&h);
                let p = match d.kind.as_str() {
                    "satisfy_values" => cx.un(UnOp::Not, b.roots[0]),
                    _ => cx.cmp(CmpOp::Eq, b.roots[0], b.roots[1]),
                }
                .expect("the question builds");
                match prove::valid_under(&mut cx, p, under, &cfg).expect("the prover runs") {
                    prove::Outcome::Proved(_) => "proved",
                    prove::Outcome::Refuted(_) => "refuted",
                    _ => "unknown",
                }
            };
            *tally.entry(said).or_default() += 1;
            lines.push(format!("{} {said}", d.name));
        }
    } else {
        // One context for all; a session per way of asking.
        let mut cx = Context::new();
        let mut groups: BTreeMap<How, Vec<(usize, Built)>> = BTreeMap::new();
        let mut names: Vec<&Dump> = Vec::new();
        for (k, d) in dumps.iter().enumerate() {
            for v in 0..variants {
                match build(&mut cx, d, bases[k]) {
                    Ok(mut b) => {
                        vary(&mut cx, &mut b.roots, v);
                        groups.entry(how(d)).or_default().push((names.len(), b));
                        names.push(d);
                    }
                    Err(e) => eprintln!("{e}"),
                }
            }
        }
        let dumps = names;
        let mut replies: Vec<Option<Reply>> = dumps.iter().map(|_| None).collect();
        for (h, questions) in &groups {
            let config = Config::default()
                .with_threads(threads)
                .with_prove(prove_of(h))
                .with_mba(mba_of(h))
                .with_hub(
                    // A hub's proof within the consumer's limits for a proof.
                    prove_of(h)
                        .with_max_conflicts(h.conflicts.min(2_000))
                        .with_max_propagations(h.propagations.min(20_000))
                        .with_max_nodes((h.nodes as usize).min(200_000)),
                )
                .with_split(if mode == "whole" {
                    Split::none()
                } else {
                    split
                });
            let session = Session::new(config);
            let mut preds = Vec::new();
            let mut assumptions: Vec<Assumptions> = Vec::new();
            for (k, b) in questions {
                let d = dumps[*k];
                let mut a = Assumptions::new();
                for (e, v) in &b.assumes {
                    let _ = a.assume(&mut cx, *e, Facts::constant(v));
                }
                assumptions.push(a);
                preds.push(match d.kind.as_str() {
                    "satisfy_values" => cx.un(UnOp::Not, b.roots[0]).expect("builds"),
                    _ if h.engine => b.roots[0],
                    _ => cx.cmp(CmpOp::Eq, b.roots[0], b.roots[1]).expect("builds"),
                });
            }
            let cancel = Cancel::new();
            let asks: Vec<Ask<'_>> = (questions.iter().zip(&preds).zip(&assumptions))
                .map(|(((_, b), p), a)| {
                    let ask = match (h.engine, constant) {
                        (true, true) => Ask::constant(*p),
                        (true, false) => Ask::simplify(*p),
                        (false, _) => Ask::valid(*p),
                    };
                    let ask = match b.assumes.is_empty() {
                        true => ask,
                        false => ask.under(a),
                    };
                    match cancel_after {
                        Some(_) => ask.cancellable(&cancel),
                        None => ask,
                    }
                })
                .collect();
            let got = std::thread::scope(|s| {
                if let Some(ms) = cancel_after {
                    let cancel = cancel.clone();
                    s.spawn(move || {
                        std::thread::sleep(std::time::Duration::from_millis(ms));
                        cancel.cancel();
                    });
                }
                let t = Instant::now();
                let got = session.run(&mut cx, &asks).expect("the batch runs");
                if cancel_after.is_some() {
                    let late = t.elapsed().as_millis() as i64 - cancel_after.unwrap_or(0) as i64;
                    eprintln!("stopped {late} ms after the cancel");
                }
                got
            });
            if warm {
                let t = Instant::now();
                let again = session.run(&mut cx, &asks).expect("the batch runs");
                second += t.elapsed().as_secs_f64();
                assert!(
                    got.iter()
                        .zip(&again)
                        .all(|(a, b)| a.answer == b.answer && a.cost == b.cost),
                    "a stored answer differs"
                );
            }
            let s = session.stats();
            stats.asks += s.asks;
            stats.asks_stored += s.asks_stored;
            stats.asks_repeated += s.asks_repeated;
            stats.nodes_asked += s.nodes_asked;
            stats.nodes_new += s.nodes_new;
            stats.tasks_solved += s.tasks_solved;
            stats.tasks_stored += s.tasks_stored;
            stats.hubs += s.hubs;
            stats.hubs_proved += s.hubs_proved;
            stats.regrouped += s.regrouped;
            stats.case_splits += s.case_splits;
            stats.cancelled += s.cancelled;
            stats.store_nodes += s.store_nodes;
            stats.store_answers += s.store_answers;
            for ((k, _), r) in questions.iter().zip(got) {
                replies[*k] = Some(r);
            }
        }
        for (d, r) in dumps.iter().zip(&replies) {
            let Some(r) = r else { continue };
            let said = match &r.answer {
                Answer::Simplified { expr, .. }
                    if cx.as_const(*expr).is_ok_and(|v| v.is_some()) =>
                {
                    "constant"
                }
                a => label(a),
            };
            *tally.entry(said).or_default() += 1;
            let c = &r.cost;
            lines.push(format!(
                "{} {said} visits={} pass={} mba={} conflicts={} propagations={} tasks={}",
                d.name,
                c.simplify.node_visits,
                c.simplify.pass_work,
                c.simplify.mba_steps,
                c.conflicts,
                c.propagations,
                c.tasks
            ));
        }
    }
    let wall = started.elapsed().as_secs_f64();
    let (cpu, peak) = process();
    println!(
        "mode={mode} threads={threads} questions={} wall={wall:.2}s cpu={cpu:.2}s peak={peak:.0}MB{}",
        lines.len(),
        if warm {
            format!(" second={second:.3}s")
        } else {
            String::new()
        }
    );
    println!("answers: {tally:?}");
    if mode != "before" {
        let overlap = 100.0 * (1.0 - stats.nodes_new as f64 / stats.nodes_asked.max(1) as f64);
        println!(
            "nodes asked={} new={} ({overlap:.1}% already held); tasks solved={} stored={}; \
             hubs={} proved={}; regrouped={} case splits={} cancelled={}; store nodes={} answers={}",
            stats.nodes_asked,
            stats.nodes_new,
            stats.tasks_solved,
            stats.tasks_stored,
            stats.hubs,
            stats.hubs_proved,
            stats.regrouped,
            stats.case_splits,
            stats.cancelled,
            stats.store_nodes,
            stats.store_answers
        );
    }
    if let Some(f) = answers_file {
        let _ = std::fs::write(f, lines.join("\n") + "\n");
    }
    ExitCode::SUCCESS
}
