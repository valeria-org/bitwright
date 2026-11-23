//! Runs a directory of simplifier inputs through an engine and prints, for each, its time in
//! milliseconds, the result's reachable DAG nodes and its constant value, if any.
//!
//! `cargo run --release --example engine_corpus --no-default-features --features mba,prove -- DIR`
//!
//! Each file holds `# engine: deep|forms|...` and `# fuel: N` lines and, after `## root 0`, the
//! expression in Bitwright's text form (as a devirtualizer's `--export-questions` writes them
//! under `engine/`). Supply width-annotated symbols for mixed-width inputs. The default
//! is the host's inline profile (no basis sums, kept steps 2^12); `DIR --default-strategy`
//! uses the ordinary deobfuscation profile. Neither reconstructs omitted assumptions.
use std::sync::Arc;

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::{MbaConfig, MbaSolver, NfOptions, NormalFormSolver};
use bitwright::{Bounded, Context, ParseOptions, View, Width};

fn stock() -> MbaConfig {
    MbaConfig::default().with_opaque_sweep(true)
}

fn forms() -> MbaConfig {
    stock().with_noise_forms(true).with_known_atoms(true)
}

fn main() {
    let mut args = std::env::args_os().skip(1);
    let dir = args.next().expect("directory [--default-strategy]");
    let default_strategy = match args.next() {
        None => false,
        Some(arg) if arg == "--default-strategy" && args.next().is_none() => true,
        _ => panic!("usage: engine_corpus DIR [--default-strategy]"),
    };
    let mut files: Vec<_> = std::fs::read_dir(&dir)
        .expect("read dir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    files.sort();
    let solver: Arc<dyn MbaSolver> = Arc::new(NormalFormSolver::new(
        NfOptions::default()
            .with_memo(1 << 14)
            .with_basis_sums(default_strategy),
    ));
    let build = |m| {
        let strategy = Strategy::deobfuscate().with_mba(m);
        let strategy = if default_strategy {
            strategy
        } else {
            strategy.with_basis_sums(false).with_kept_steps(1 << 12)
        };
        Engine::builder()
            .builtin()
            .strategy(strategy)
            .mba_solver(Arc::clone(&solver))
            .build()
            .unwrap()
    };
    let (stock_engine, forms_engine) = (build(stock()), build(forms()));
    let mut missing_assumptions = 0usize;
    for f in files {
        let mut cx = Context::new();
        let text = std::fs::read_to_string(&f).unwrap();
        if text.lines().any(|line| line == "# assumptions: true") {
            missing_assumptions += 1;
        }
        let what = text
            .lines()
            .find_map(|l| l.strip_prefix("# engine: "))
            .unwrap_or("deep")
            .to_owned();
        let fuel: u64 = text
            .lines()
            .find_map(|l| l.strip_prefix("# fuel: "))
            .and_then(|v| v.parse().ok())
            .unwrap_or(1 << 19);
        let Some(root) = text.split("## root 0\n").nth(1) else {
            continue;
        };
        let e = match cx.parse(root.trim(), &ParseOptions::width(Width::W64)) {
            Ok(e) => e,
            Err(err) => {
                println!("{} parse-error {err}", f.display());
                continue;
            }
        };
        let engine = if what == "forms" {
            &forms_engine
        } else {
            &stock_engine
        };
        let t = std::time::Instant::now();
        let out = engine.run(
            &mut cx,
            &[e],
            Run::default().with_per_call(Budget::fuel(fuel)),
        );
        let ms = t.elapsed().as_secs_f64() * 1e3;
        let name = f.file_name().unwrap().to_string_lossy();
        let o = match out {
            Ok(o) => o,
            Err(err) => {
                println!("{name} {what} {ms:.2} error={err}");
                continue;
            }
        };
        let r = o.roots[0].expr;
        let Bounded::Exact(nodes) = cx.dag_size(&[r], u32::MAX).expect("a result") else {
            unreachable!("the arena's node indices fit in u32")
        };
        match cx.view(r).expect("a result") {
            View::Const(v) => println!("{name} {what} {ms:.2} nodes={nodes} constant={v}"),
            _ => println!("{name} {what} {ms:.2} nodes={nodes} constant=-"),
        }
    }
    if missing_assumptions > 0 {
        eprintln!("{missing_assumptions} inputs marked as assumed were replayed unconstrained");
    }
}
