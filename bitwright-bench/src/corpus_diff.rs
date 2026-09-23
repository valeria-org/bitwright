//! `--corpus-diff`: the results of the deobfuscation strategy with the MBA service under the
//! current defaults (the signature solver; backend certificates trusted) and under a proposed
//! configuration (the normal-form solver; bitwright's own evidence only), over generated
//! corpora: linear MBA, nonlinear MBA, and random DAGs. Prints a markdown report: sizes, how
//! many results change and which way, time, the MBA service's answers, and examples.

use std::sync::Arc;
use std::time::Instant;

use bitwright::engine::{Engine, MbaStats, Strategy};
use bitwright::mba::{MbaConfig, MbaSolver, MbaTrust, NormalFormSolver, SignatureSolver};
use bitwright::{Bounded, Context, Expr, ParseOptions, PrintOptions};

use crate::counter::Counters;
use crate::workload::{self, Dag};

/// An input, built into a fresh context.
type Input = Box<dyn Fn(&mut Context) -> Expr>;

/// One configuration's results over a corpus.
struct Results {
    /// Per input: the result as text (with symbol widths, so it parses anywhere).
    texts: Vec<String>,
    sizes: Vec<u32>,
    before: u64,
    nanos: u128,
    /// User-space instructions retired, where counters are available.
    instructions: Option<u64>,
    mba: MbaStats,
}

fn engine(solver: Arc<dyn MbaSolver>, trust: MbaTrust) -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default().with_trust(trust)))
        .mba_solver(solver)
        .build()
        .expect("engine")
}

fn size(cx: &mut Context, e: Expr) -> u32 {
    match cx.dag_size(&[e], u32::MAX) {
        Ok(Bounded::Exact(n)) => n,
        _ => 0,
    }
}

fn add(total: &mut MbaStats, s: &MbaStats) {
    total.calls += s.calls;
    total.simplified += s.simplified;
    total.no_simpler += s.no_simpler;
    total.unsupported += s.unsupported;
    total.exhausted += s.exhausted;
    total.refuted += s.refuted;
    total.proof_unknown += s.proof_unknown;
    total.not_smaller += s.not_smaller;
    total.too_many_vars += s.too_many_vars;
    total.too_large += s.too_large;
    total.too_small += s.too_small;
}

/// Runs `eng` on each input (built by `build` in a fresh context).
fn run(eng: &Engine, inputs: &[Input]) -> Results {
    let mut counters = Counters::open();
    let mut r = Results {
        texts: Vec::new(),
        sizes: Vec::new(),
        before: 0,
        nanos: 0,
        instructions: counters.counts_instructions().then_some(0),
        mba: MbaStats::default(),
    };
    for build in inputs {
        let mut cx = Context::new();
        let e = build(&mut cx);
        r.before += u64::from(size(&mut cx, e));
        let t = Instant::now();
        let start = counters.start();
        let out = eng
            .run(&mut cx, &[e], Default::default())
            .expect("simplify");
        let reading = counters.stop(start);
        r.nanos += t.elapsed().as_nanos();
        r.instructions = r.instructions.zip(reading.instructions).map(|(a, b)| a + b);
        let x = out.roots[0].expr;
        r.sizes.push(size(&mut cx, x));
        r.texts.push(
            cx.display_with(x, PrintOptions::default().with_symbol_widths(true))
                .to_string(),
        );
        add(&mut r.mba, &out.stats.mba);
    }
    r
}

fn parsed(texts: Vec<String>, bits: u16) -> Vec<Input> {
    texts
        .into_iter()
        .map(|t| {
            let o = ParseOptions::width(workload::width(bits));
            Box::new(move |cx: &mut Context| cx.parse(&t, &o).expect("corpus parses")) as Input
        })
        .collect()
}

/// Instructions (the measure that does not move with other load) and wall time.
fn cost(r: &Results) -> String {
    let ms = r.nanos as f64 / 1e6;
    match r.instructions {
        Some(n) => format!("{:.2} G instr ({ms:.0} ms)", n as f64 / 1e9),
        None => format!("{ms:.1} ms"),
    }
}

/// Prints the report.
pub fn report() {
    let current = engine(Arc::new(SignatureSolver), MbaTrust::default());
    let trust_off = engine(
        Arc::new(SignatureSolver),
        MbaTrust::default().with_backend_certificates(false),
    );
    let proposed = engine(
        Arc::new(NormalFormSolver::default()),
        MbaTrust::default().with_backend_certificates(false),
    );
    let mut corpora: Vec<(String, Vec<Input>)> = Vec::new();
    for bits in [8u16, 64] {
        corpora.push((
            format!("linear MBA, {bits} bits"),
            parsed(workload::mba_corpus(0x11, 200), bits),
        ));
        corpora.push((
            format!("nonlinear MBA, {bits} bits"),
            parsed(workload::nonlinear_mba_corpus(0x23, 200, bits), bits),
        ));
    }
    for bits in [8u16, 64] {
        let dags: Vec<Input> = (0..200u64)
            .map(|i| {
                Box::new(move |cx: &mut Context| {
                    workload::dag(
                        cx,
                        0x5eed + i,
                        Dag {
                            width: workload::width(bits),
                            symbols: 4,
                            nodes: 40,
                            heavy_ops: false,
                        },
                    )
                }) as Input
            })
            .collect();
        corpora.push((format!("random DAGs, {bits} bits"), dags));
    }
    println!(
        "| corpus | inputs | nodes before | current | trust off only | proposed | changed | smaller | larger | cost current | cost proposed |"
    );
    println!("|-|-|-|-|-|-|-|-|-|-|-|");
    let mut examples: Vec<String> = Vec::new();
    let mut answers: Vec<(String, [MbaStats; 3])> = Vec::new();
    for (name, inputs) in &corpora {
        let a = run(&current, inputs);
        let t = run(&trust_off, inputs);
        let b = run(&proposed, inputs);
        let (mut changed, mut smaller, mut larger) = (0, 0, 0);
        for i in 0..inputs.len() {
            if a.texts[i] != b.texts[i] {
                changed += 1;
                if examples.len() < 12 && (b.sizes[i] > a.sizes[i] || examples.len() < 8) {
                    examples.push(format!(
                        "- {name}: `{}` ({}) → `{}` ({})",
                        a.texts[i], a.sizes[i], b.texts[i], b.sizes[i]
                    ));
                }
            }
            smaller += usize::from(b.sizes[i] < a.sizes[i]);
            larger += usize::from(b.sizes[i] > a.sizes[i]);
        }
        let total = |r: &Results| r.sizes.iter().map(|&s| u64::from(s)).sum::<u64>();
        let trust_changed = (0..inputs.len())
            .filter(|&i| a.texts[i] != t.texts[i])
            .count();
        println!(
            "| {name} | {} | {} | {} | {} ({trust_changed} changed) | {} | {changed} | {smaller} | {larger} | {} | {} |",
            inputs.len(),
            a.before,
            total(&a),
            total(&t),
            total(&b),
            cost(&a),
            cost(&b),
        );
        answers.push((name.clone(), [a.mba, t.mba, b.mba]));
    }
    println!();
    println!(
        "| corpus | configuration | calls | simplified | not smaller | no simpler | unsupported | exhausted | unproved | refuted | too small |"
    );
    println!("|-|-|-|-|-|-|-|-|-|-|-|");
    for (name, stats) in &answers {
        for (which, s) in ["current", "trust off only", "proposed"].iter().zip(stats) {
            println!(
                "| {name} | {which} | {} | {} | {} | {} | {} | {} | {} | {} | {} |",
                s.calls,
                s.simplified,
                s.not_smaller,
                s.no_simpler,
                s.unsupported,
                s.exhausted,
                s.proof_unknown,
                s.refuted,
                s.too_small
            );
        }
    }
    println!();
    println!("Examples of changed results (current → proposed, nodes):");
    println!();
    for e in examples {
        println!("{e}");
    }
}
