//! PROTOTYPE, not for release: how the MBA certifier's symbolic comparison is charged.
//!
//! `--symbolic-sweep FILE`: per-root results of the deobfuscation strategy with the MBA service
//! (the normal-form solver, bitwright's own evidence only) on the MBA rows' corpora and
//! `--corpus-diff`'s, at the default budget and at small fuels, as tab-separated lines in FILE,
//! to compare charge factors (`BW_SYMBOLIC_CHARGE`, see `bitwright::mba::probe`).
//!
//! `--symbolic-cost` (feature `probe`): where certificate work goes, by kind and meter, with
//! instructions and time per charged unit.

use std::io::Write;
use std::process::ExitCode;
use std::sync::Arc;
use std::time::Instant;

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::{MbaConfig, MbaTrust, NormalFormSolver};
use bitwright::{Bounded, Context, Expr, ParseOptions, PrintOptions};

use crate::counter::Counters;
use crate::workload::{self, Dag};

/// One input: its roots, built into a fresh context.
pub(crate) type Build = Box<dyn Fn(&mut Context) -> Vec<Expr>>;

pub(crate) struct Corpus {
    pub(crate) name: &'static str,
    pub(crate) inputs: Vec<Build>,
}

fn options(bits: u16) -> ParseOptions {
    ParseOptions::width(workload::width(bits))
}

/// One input per text.
fn each(texts: Vec<String>, bits: u16) -> Vec<Build> {
    texts
        .into_iter()
        .map(|t| {
            Box::new(move |cx: &mut Context| vec![cx.parse(&t, &options(bits)).expect("parses")])
                as Build
        })
        .collect()
}

/// One input of every text as a root (as the MBA bench rows run them).
fn together(texts: Vec<String>, bits: u16) -> Vec<Build> {
    vec![Box::new(move |cx: &mut Context| {
        texts
            .iter()
            .map(|t| cx.parse(t, &options(bits)).expect("parses"))
            .collect()
    })]
}

fn dags(bits: u16) -> Vec<Build> {
    (0..200u64)
        .map(|i| {
            Box::new(move |cx: &mut Context| {
                vec![workload::dag(
                    cx,
                    0x5eed + i,
                    Dag {
                        width: workload::width(bits),
                        symbols: 4,
                        nodes: 40,
                        heavy_ops: false,
                    },
                )]
            }) as Build
        })
        .collect()
}

pub(crate) fn corpora() -> Vec<Corpus> {
    vec![
        Corpus {
            name: "bench/mba-native/8",
            inputs: together(workload::mba_corpus(11, 20), 8),
        },
        Corpus {
            name: "bench/mba-native/64",
            inputs: together(workload::mba_corpus(11, 20), 64),
        },
        Corpus {
            name: "bench/mba-nonlinear/8",
            inputs: together(workload::nonlinear_mba_corpus(23, 20, 8), 8),
        },
        Corpus {
            name: "bench/mba-nonlinear/64",
            inputs: together(workload::nonlinear_mba_corpus(23, 20, 64), 64),
        },
        Corpus {
            name: "diff/linear/8",
            inputs: each(workload::mba_corpus(0x11, 200), 8),
        },
        Corpus {
            name: "diff/linear/64",
            inputs: each(workload::mba_corpus(0x11, 200), 64),
        },
        Corpus {
            name: "diff/nonlinear/8",
            inputs: each(workload::nonlinear_mba_corpus(0x23, 200, 8), 8),
        },
        Corpus {
            name: "diff/nonlinear/64",
            inputs: each(workload::nonlinear_mba_corpus(0x23, 200, 64), 64),
        },
        Corpus {
            name: "diff/dags/8",
            inputs: dags(8),
        },
        Corpus {
            name: "diff/dags/64",
            inputs: dags(64),
        },
    ]
}

/// The MBA rows' and `--corpus-diff`'s "defaults" engine.
pub(crate) fn engine() -> Engine {
    let config =
        MbaConfig::default().with_trust(MbaTrust::default().with_backend_certificates(false));
    Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(config))
        .mba_solver(Arc::new(NormalFormSolver::default()))
        .build()
        .expect("engine")
}

fn size(cx: &mut Context, e: &[Expr]) -> u32 {
    match cx.dag_size(e, u32::MAX) {
        Ok(Bounded::Exact(n)) => n,
        _ => 0,
    }
}

pub(crate) fn run_of(fuel: Option<u64>) -> Run<'static> {
    match fuel {
        None => Run::default(),
        Some(f) => Run::default().with_per_call(Budget::fuel(f)),
    }
}

pub(crate) fn fuel_label(fuel: Option<u64>) -> String {
    match fuel {
        None => "default".into(),
        Some(f) => format!("2^{}", f.trailing_zeros()),
    }
}

pub(crate) fn setting() -> String {
    let var = |v: &str, d: &str| std::env::var(v).unwrap_or_else(|_| d.into());
    format!(
        "k={} scope={} mode={} reserve={} solver={} rate={} account={} round={} floor={}",
        var("BW_SYMBOLIC_CHARGE", "1"),
        var("BW_SYMBOLIC_SCOPE", "all"),
        var("BW_SYMBOLIC_MODE", "clamp"),
        var("BW_SYMBOLIC_RESERVE", "1"),
        var("BW_SOLVER_MODE", "off"),
        var("BW_SOLVER_RATE", "64"),
        var("BW_SOLVER_ACCOUNT", "256"),
        var("BW_SOLVER_ROUND", "exact"),
        var("BW_SOLVER_FLOOR", "1")
    )
}

/// Process-wide tables (rule compile, synthesis) are built once, outside every measurement.
pub(crate) fn warm_up() {
    let e = engine();
    let mut cx = Context::new();
    let roots = together(workload::nonlinear_mba_corpus(23, 20, 64), 64)[0](&mut cx);
    let _ = e.run(&mut cx, &roots, Run::default());
}

pub fn sweep(path: &str) -> ExitCode {
    let mut out = std::io::BufWriter::new(std::fs::File::create(path).expect("create the file"));
    let mut counters = Counters::open();
    let _ = writeln!(out, "# {}", setting());
    warm_up();
    let fuels = [
        None,
        Some(1u64 << 18),
        Some(1 << 16),
        Some(1 << 14),
        Some(1 << 12),
        Some(1 << 10),
        Some(1 << 8),
    ];
    for c in corpora() {
        for fuel in fuels {
            let eng = engine();
            let (mut instr, mut pass, mut nanos, mut stopped) = (0u64, 0u64, 0u128, 0u64);
            let mut mba = bitwright::engine::MbaStats::default();
            let mut sizes = 0u64;
            for (i, build) in c.inputs.iter().enumerate() {
                let mut cx = Context::new();
                let roots = build(&mut cx);
                let t = Instant::now();
                let start = counters.start();
                let o = eng.run(&mut cx, &roots, run_of(fuel)).expect("run");
                let reading = counters.stop(start);
                nanos += t.elapsed().as_nanos();
                instr += reading.instructions.unwrap_or(0);
                pass += o.stats.pass_work;
                mba.absorb(&o.stats.mba);
                for (j, r) in o.roots.iter().enumerate() {
                    let n = size(&mut cx, &[r.expr]);
                    sizes += u64::from(n);
                    let end = format!("{:?}", r.end);
                    stopped += u64::from(end != "Completed");
                    let text = cx
                        .display_with(r.expr, PrintOptions::default().with_symbol_widths(true))
                        .to_string()
                        .replace(['\t', '\n'], " ");
                    let _ = writeln!(
                        out,
                        "R\t{}\t{}\t{i}.{j}\t{n}\t{end}\t{text}",
                        c.name,
                        fuel_label(fuel)
                    );
                }
            }
            let cs = &mba.certificates;
            let _ = writeln!(
                out,
                "T\t{}\t{}\tinstr={instr}\tpass={pass}\tsize={sizes}\tstopped={stopped}\t\
                 calls={}\tsimplified={}\tunproved={}\texhausted={}\tnot_smaller={}\t\
                 no_simpler={}\trefuted={}\tcerts={}\tproved={}\tsymbolic={}\tsparse={}\t\
                 single_bit={}\tsignature={}\tgrid={}\texhaustive={}\tcarries={}\t\
                 compositional={}\tsplit={}\tover_budget={}\tpoints={}\tms={:.1}",
                c.name,
                fuel_label(fuel),
                mba.calls,
                mba.simplified,
                mba.proof_unknown,
                mba.exhausted,
                mba.not_smaller,
                mba.no_simpler,
                mba.refuted,
                cs.calls,
                cs.proved,
                cs.symbolic,
                cs.sparse,
                cs.single_bit,
                cs.signature,
                cs.grid,
                cs.exhaustive,
                cs.carries,
                cs.compositional,
                cs.split,
                cs.over_budget,
                cs.points,
                nanos as f64 / 1e6
            );
            let _ = out.flush();
            eprintln!(
                "{} {}: pass {pass}, size {sizes}, stopped {stopped}, {:.1} M instr",
                c.name,
                fuel_label(fuel),
                instr as f64 / 1e6
            );
        }
    }
    ExitCode::SUCCESS
}

#[cfg(feature = "probe")]
pub fn probe_report() -> ExitCode {
    use bitwright::mba::probe::{self, KINDS, Tallies};
    use bitwright::prove::Config;

    let Some(clock) = crate::counter::free_running() else {
        eprintln!("instruction counters are unavailable");
        return ExitCode::FAILURE;
    };
    probe::set_clock(clock);
    let over = probe::overhead(10_000);
    let (span_instr, span_ns) = (over.instr as f64 / 1e4, over.nanos as f64 / 1e4);
    println!(
        "# {}; a span costs {span_instr:.0} instructions, {span_ns:.0} ns (subtracted per call)",
        setting()
    );
    let names = [
        "sym-first",
        "sym-fallback",
        "eval",
        "sample",
        "certificate",
        "solve",
    ];
    let print = |name: &str, total_instr: u64, pass: u64, ms: f64, t: &Tallies| {
        println!();
        println!(
            "== {name}: {:.2} M instr, {ms:.1} ms, pass work {pass}",
            total_instr as f64 / 1e6
        );
        println!(
            "{:<7} {:<13} {:>8} {:>12} {:>12} {:>14} {:>12} {:>10} {:>10} {:>8}",
            "meter",
            "kind",
            "calls",
            "work",
            "units",
            "instr",
            "ns",
            "instr/unit",
            "ns/unit",
            "instr%"
        );
        for (m, meter) in ["solver", "gate"].iter().enumerate() {
            for (k, kind) in names.iter().enumerate().take(KINDS) {
                let x = t[m][k];
                if x.calls == 0 {
                    continue;
                }
                let instr = (x.instr as f64 - span_instr * x.calls as f64).max(0.0);
                let ns = (x.nanos as f64 - span_ns * x.calls as f64).max(0.0);
                let per = |v: f64| {
                    if x.units == 0 {
                        "-".to_string()
                    } else {
                        format!("{:.2}", v / x.units as f64)
                    }
                };
                println!(
                    "{:<7} {:<13} {:>8} {:>12} {:>12} {:>14.0} {:>12.0} {:>10} {:>10} {:>7.1}%",
                    meter,
                    kind,
                    x.calls,
                    x.work,
                    x.units,
                    instr,
                    ns,
                    per(instr),
                    per(ns),
                    100.0 * instr / total_instr.max(1) as f64
                );
            }
        }
    };
    let mut counters = Counters::open();
    // The prover's MBA-heavy question (`--prover-budgets`), warmed up as there.
    let src = crate::prover_budgets::identities(48);
    let _ = crate::prover_budgets::ask(&src, bitwright::Width::W64, &Config::default());
    for (label, fuel) in [("default", 1u64 << 22), ("2^14", 1 << 14)] {
        let cfg = Config::default()
            .with_simplify_fuel(fuel)
            .with_max_conflicts(crate::prover_budgets::CONFLICTS);
        let _ = probe::take();
        let t = Instant::now();
        let start = counters.start();
        let (answer, s) = crate::prover_budgets::ask(&src, bitwright::Width::W64, &cfg);
        let reading = counters.stop(start);
        let ms = t.elapsed().as_secs_f64() * 1e3;
        let tallies = probe::take();
        print(
            &format!("prover, 48 identities, fuel {label} ({answer})"),
            reading.instructions.unwrap_or(0),
            s.simplification.spent.pass_work,
            ms,
            &tallies,
        );
    }
    warm_up();
    for c in corpora() {
        let eng = engine();
        let _ = probe::take();
        let (mut instr, mut pass, mut nanos) = (0u64, 0u64, 0u128);
        for build in &c.inputs {
            let mut cx = Context::new();
            let roots = build(&mut cx);
            let t = Instant::now();
            let start = counters.start();
            let o = eng.run(&mut cx, &roots, Run::default()).expect("run");
            let reading = counters.stop(start);
            nanos += t.elapsed().as_nanos();
            instr += reading.instructions.unwrap_or(0);
            pass += o.stats.pass_work;
        }
        let tallies = probe::take();
        print(c.name, instr, pass, nanos as f64 / 1e6, &tallies);
    }
    ExitCode::SUCCESS
}

/// A polynomial pair no evaluation test can take (degree 6 over eight 64-bit variables), so the
/// certificate falls back to the symbolic comparison: `S^6` for `S = x0 + … + x7 + 1` (3,003
/// monomials), then `chain` additions of the variables, in two orders (equal polynomials, so
/// every addition copies the whole polynomial).
#[cfg(feature = "probe")]
fn worst_pair(chain: usize) -> (bitwright::mba::MbaExpr, bitwright::mba::MbaExpr) {
    use bitwright::mba::{MOp, MbaExpr};
    use bitwright::{BitVec, Width};
    let w = Width::W64;
    let side = |shift: usize| {
        let mut m = MbaExpr::new(vec![w; 8]);
        let xs: Vec<u32> = (0..8).map(|v| m.push(MOp::Var(v), &[]).unwrap()).collect();
        let mut s = m.push(MOp::Const(BitVec::one(w)), &[]).unwrap();
        for &x in &xs {
            s = m.push(MOp::Add, &[s, x]).unwrap();
        }
        let mut p = s;
        for _ in 1..6 {
            p = m.push(MOp::Mul, &[p, s]).unwrap();
        }
        for i in 0..chain {
            p = m.push(MOp::Add, &[p, xs[(i + shift) % 8]]).unwrap();
        }
        m
    };
    (side(0), side(1))
}

#[cfg(feature = "probe")]
pub fn worst_report() -> ExitCode {
    use bitwright::mba::probe;
    use bitwright::mba::{EquivalenceProver, MbaBudget, NativeProver};
    let Some(clock) = crate::counter::free_running() else {
        eprintln!("instruction counters are unavailable");
        return ExitCode::FAILURE;
    };
    probe::set_clock(clock);
    println!("# {}", setting());
    println!(
        "{:>6} {:>6} {:>10} {:>9} {:>12} {:>12} {:>14} {:>10}",
        "chain", "nodes", "steps", "verdict", "sym work", "sym units", "instr", "ms"
    );
    for chain in [0usize, 250, 1000, 2000] {
        let (a, b) = worst_pair(chain);
        for steps in [1u64 << 16, 1 << 20, 1 << 24] {
            let prover = NativeProver::default();
            let _ = probe::take();
            let t = Instant::now();
            let verdict = prover.prove_equal(&a, &b, &MbaBudget::default().with_steps(steps));
            let ms = t.elapsed().as_secs_f64() * 1e3;
            let tallies = probe::take();
            let sym = tallies[0][1];
            let cert = tallies[0][4];
            println!(
                "{chain:>6} {:>6} {:>10} {:>9} {:>12} {:>12} {:>14} {:>10.1}",
                a.nodes().len() + b.nodes().len(),
                format!("2^{}", steps.trailing_zeros()),
                format!("{verdict:?}"),
                sym.work,
                sym.units,
                cert.instr,
                ms
            );
        }
    }
    ExitCode::SUCCESS
}
