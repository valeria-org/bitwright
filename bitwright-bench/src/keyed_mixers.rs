//! Opt-in, per-process keyed-mixer measurements. The preparation stages use the public bit-blast and
//! CNF primitives on the fixtures' BV subset; native Question regressions cover continuation.

#[path = "../../bitwright/tests/common/keyed_mixers.rs"]
mod fixture;

use crate::counter::{Counters, Reading};
use bitwright::engine::Engine;
use bitwright::prove::{
    Config, Limits, Outcome, Question, SampleMode,
    aig::{Aig, Cnf, FALSE, L, TRUE},
    blast::{self, Bits},
    drup,
    sat::{Answer, Solver},
};
use bitwright::{BinOp, BitVec, CmpOp, Context, Expr, SymbolKey, UnOp, View};
use fixture::{Expected, Spelling};
use std::collections::HashMap;
use std::process::{Command, ExitCode};

#[derive(Debug)]
struct Circuit {
    graph: Aig,
    goal: L,
    symbols: Vec<(SymbolKey, bitwright::Width, Bits)>,
}

// This is deliberately a small fixture adapter, not a second general-purpose expression
// blaster. All arithmetic and CNF encoding run through the native prover's public primitives.
fn circuit(cx: &mut Context, root: Expr) -> Circuit {
    let mut graph = Aig::new();
    let mut values: HashMap<Expr, Bits> = HashMap::new();
    let mut symbols = Vec::new();
    for e in cx.post_order(&[root]).unwrap() {
        let width = usize::from(cx.width(e).unwrap().bits());
        let bits = match cx.view(e).unwrap() {
            View::Const(v) => blast::konst(&v),
            View::Sym(id) => {
                let known = cx.declared_known(e).unwrap();
                let bits: Bits = (0..width)
                    .map(|j| match known {
                        Some(k) if k.known_one().bit(j as u16) == Some(true) => TRUE,
                        Some(k) if k.known_zero().bit(j as u16) == Some(true) => FALSE,
                        _ => graph.input(),
                    })
                    .collect();
                symbols.push((
                    cx.symbol_key(id).unwrap().clone(),
                    cx.width(e).unwrap(),
                    bits.clone(),
                ));
                bits
            }
            View::Zext(a) => {
                let mut bits = values[&a].clone();
                bits.resize(width, FALSE);
                bits
            }
            View::Concat { hi, lo } => {
                let mut bits = values[&lo].clone();
                bits.extend_from_slice(&values[&hi]);
                bits
            }
            View::Un(UnOp::Not, a) => blast::not(&mut graph, &values[&a]),
            View::Bin(op, a, b) => {
                let (a, b) = (&values[&a], &values[&b]);
                match op {
                    BinOp::Add => blast::add(&mut graph, a, b),
                    BinOp::Mul => blast::mul(&mut graph, a, b),
                    BinOp::Xor => blast::xor(&mut graph, a, b),
                    BinOp::And => blast::and(&mut graph, a, b),
                    BinOp::Or => blast::or(&mut graph, a, b),
                    BinOp::LShr => blast::shift(&mut graph, a, b, false, FALSE),
                    _ => panic!("operator outside the keyed-mixer fixture subset: {op:?}"),
                }
            }
            View::Cmp(op, a, b) => {
                let equal = blast::eq(&mut graph, &values[&a], &values[&b]);
                vec![match op {
                    CmpOp::Eq => equal,
                    CmpOp::Ne => equal ^ 1,
                    _ => panic!("comparison outside keyed-mixer subset"),
                }]
            }
            View::Select { cond, then, els } => {
                blast::mux(&mut graph, values[&cond][0], &values[&then], &values[&els])
            }
            other => panic!("node outside the keyed-mixer fixture subset: {other:?}"),
        };
        values.insert(e, bits);
    }
    Circuit {
        goal: values[&root][0],
        graph,
        symbols,
    }
}

fn peak_kib() -> Option<u64> {
    std::fs::read_to_string("/proc/self/status")
        .ok()?
        .lines()
        .find_map(|line| {
            line.strip_prefix("VmHWM:")?
                .split_whitespace()
                .next()?
                .parse()
                .ok()
        })
}

// The parameters follow the flat CSV schema, with solver counters supplied when available.
#[allow(clippy::too_many_arguments)]
fn row(
    case: &str,
    spelling: &str,
    mode: &str,
    expected: Expected,
    phase: &str,
    reading: Reading,
    status: &str,
    graph: usize,
    vars: u32,
    clauses: usize,
    counts: Option<(u64, u64, u64, usize)>,
) {
    let (conflicts, propagations, samples, learned) = counts.unwrap_or_default();
    let instructions = reading
        .instructions
        .map_or_else(|| "unavailable".into(), |n| n.to_string());
    let peak = peak_kib().map_or_else(|| "unavailable".into(), |n| n.to_string());
    println!(
        "{case},{spelling},{mode},{expected:?},{phase},{status},{instructions},{},{},{graph},{vars},{clauses},{conflicts},{propagations},{peak},{samples},{learned}",
        reading.cpu_ns, reading.wall_ns
    );
}

fn encode(circuit: &Circuit) -> (Solver, Cnf) {
    let mut solver = Solver::new();
    solver.log_proof();
    let mut cnf = Cnf::encode(&circuit.graph, &[circuit.goal], &mut solver, true);
    cnf.assert(circuit.goal ^ 1, &mut solver);
    (solver, cnf)
}

fn verdict(
    cx: &mut Context,
    original: Expr,
    circuit: &Circuit,
    cnf: &Cnf,
    solver: &mut Solver,
    answer: &Answer,
    expected: Expected,
) -> &'static str {
    match answer {
        Answer::Unknown => "unknown-budget",
        Answer::Unsat => {
            assert_ne!(
                expected,
                Expected::Refuted,
                "a fixture with a concrete counterexample was proved"
            );
            drup::check(&cnf.clauses, &solver.take_proof().unwrap()).expect("invalid certificate");
            "proved"
        }
        Answer::Sat(bits) => {
            let mut model: Vec<(SymbolKey, BitVec)> = circuit
                .symbols
                .iter()
                .map(|(key, width, ls)| {
                    let mut limbs = [0u64; 8];
                    for (j, &l) in ls.iter().enumerate() {
                        if cnf.value(l, bits) {
                            limbs[j / 64] |= 1 << (j % 64);
                        }
                    }
                    (key.clone(), BitVec::wrapping_from_limbs(*width, &limbs))
                })
                .collect();
            for id in cx.symbols_in(&[original]).unwrap() {
                let key = cx.symbol_key(id).unwrap().clone();
                if !model.iter().any(|(k, _)| *k == key) {
                    let symbol = cx.find_symbol(&key).unwrap();
                    let value = cx.declared_known(symbol).unwrap().map_or_else(
                        || BitVec::zero(cx.symbol_width(id).unwrap()),
                        |k| k.known_one(),
                    );
                    model.push((key, value));
                }
            }
            assert_ne!(
                expected,
                Expected::Proved,
                "a known-valid fixture was refuted"
            );
            assert!(
                cx.eval(&[original], &model[..]).unwrap()[0].is_zero(),
                "witness does not replay on the original predicate"
            );
            let replay = model
                .iter()
                .map(|(k, v)| format!("{k}={v}"))
                .collect::<Vec<_>>()
                .join(";");
            eprintln!("replay: {replay}");
            "refuted-replayed"
        }
    }
}

fn native_verdict(
    cx: &mut Context,
    original: Expr,
    expected: Expected,
    answer: &Outcome,
    log_model: bool,
) -> &'static str {
    match answer {
        Outcome::Proved(Some(certificate)) => {
            assert_ne!(expected, Expected::Refuted);
            certificate.check().expect("invalid native certificate");
            "proved"
        }
        Outcome::Refuted(model) => {
            assert_ne!(expected, Expected::Proved);
            assert!(cx.eval(&[original], &model[..]).unwrap()[0].is_zero());
            if log_model {
                eprintln!("native replay: {model:?}");
            }
            "refuted-replayed"
        }
        Outcome::Unknown(_) => "unknown-budget",
        other => panic!("unexpected native outcome: {other:?}"),
    }
}

/// A single worker holds exactly one fixture, so process peak memory belongs to that case.
#[derive(Clone, Copy, Default)]
pub struct SearchOptions {
    pub escalate: bool,
    pub relations: bool,
    pub selectors: bool,
    pub input_cancellation: bool,
    pub join_factoring: bool,
    pub xor3: bool,
    pub carry_save: bool,
    pub word_sampling: bool,
    pub fast: bool,
    pub query_budget_ns: Option<u64>,
    pub exhaustive_inputs: u8,
}

fn native_config(options: SearchOptions) -> Config {
    Config::default()
        .with_relational_lemmas(options.relations)
        .with_selector_branching(options.selectors)
        .with_input_cancellation(options.input_cancellation)
        .with_join_factoring(options.join_factoring)
        .with_xor3_encoding(options.xor3)
        .with_carry_save_multiplication(options.carry_save)
        .with_word_sampling(options.word_sampling)
        .with_exhaustive_inputs(options.exhaustive_inputs)
        .with_certificate(true)
        .with_samples(0)
        .with_simplify(false)
}

fn budget_status(status: &str, elapsed_ns: u64, budget_ns: u64) -> (&'static str, bool) {
    match (status, elapsed_ns <= budget_ns) {
        ("proved", true) => ("proved-within-time", true),
        ("refuted-replayed", true) => ("refuted-replayed-within-time", true),
        ("proved", false) => ("proved-over-time", false),
        ("refuted-replayed", false) => ("refuted-replayed-over-time", false),
        ("unknown-budget", true) => ("unknown-within-time", false),
        ("unknown-budget", false) => ("unknown-over-time", false),
        _ => unreachable!("unexpected checked query status"),
    }
}

// This is a measured acceptance target, not a wall-clock cancellation mechanism. In
// particular, returning Unknown quickly does not meet the recovery requirement.
fn query_budget_worker(
    name: &str,
    compact: bool,
    options: SearchOptions,
    budget_ns: u64,
) -> ExitCode {
    let spelling = if compact {
        Spelling::Compact
    } else {
        Spelling::Nested
    };
    let mut cx = Context::new();
    let (original, expected) = fixture::claim(&mut cx, name, spelling);
    let cfg = native_config(options);
    let mut counters = Counters::open();
    let start = counters.start();
    let mut question = Question::valid(&mut cx, original, &cfg).unwrap();
    let answer = question
        .solve(
            &mut cx,
            Limits {
                conflicts: 256,
                propagations: 75_000,
            },
        )
        .unwrap();
    let status = native_verdict(&mut cx, original, expected, &answer, false);
    let reading = counters.stop(start);
    let (status, passed) = budget_status(status, reading.wall_ns, budget_ns);
    let stats = question.stats();
    let mode = format!(
        "raw+relations={}+selectors={}+input-cancel={}+factor-joins={}+xor3={}+carry-save={}+exhaustive-inputs={}",
        options.relations,
        options.selectors,
        options.input_cancellation,
        options.join_factoring,
        options.xor3,
        options.carry_save,
        options.exhaustive_inputs,
    );
    row(
        name,
        if compact { "compact" } else { "nested" },
        &mode,
        expected,
        "native-query-total",
        reading,
        status,
        stats.nodes,
        stats.vars,
        stats.clauses,
        Some((
            stats.conflicts,
            stats.propagations,
            stats.samples,
            stats.learned,
        )),
    );
    if let Outcome::Refuted(model) = &answer {
        eprintln!("native replay: {model:?}");
    }
    if passed {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

pub fn worker(name: &str, compact: bool, simplified: bool, options: SearchOptions) -> ExitCode {
    if let Some(budget_ns) = options.query_budget_ns {
        return query_budget_worker(name, compact, options, budget_ns);
    }
    let SearchOptions {
        escalate,
        relations,
        selectors,
        input_cancellation,
        join_factoring,
        xor3,
        carry_save,
        word_sampling,
        fast,
        query_budget_ns: _,
        exhaustive_inputs: _,
    } = options;
    let spelling = if compact {
        Spelling::Compact
    } else {
        Spelling::Nested
    };
    let spelling_name = if compact { "compact" } else { "nested" };
    let mode_name = format!(
        "{}{}{}{}{}{}{}{}",
        if simplified { "simplified" } else { "raw" },
        if relations { "+relations" } else { "" },
        if selectors { "+selectors" } else { "" },
        if input_cancellation {
            "+input-cancel"
        } else {
            ""
        },
        if join_factoring { "+factor-joins" } else { "" },
        if xor3 { "+xor3" } else { "" },
        if carry_save { "+carry-save" } else { "" },
        if word_sampling { "+word-samples" } else { "" }
    );
    let mode = mode_name.as_str();
    let mut cx = Context::new();
    let (original, expected) = fixture::claim(&mut cx, name, spelling);
    let engine = Engine::standard();
    let mut counters = Counters::open();
    let start = counters.start();
    let out = engine.simplify(&mut cx, original).unwrap();
    let reading = counters.stop(start);
    row(
        name,
        spelling_name,
        mode,
        expected,
        "simplify",
        reading,
        "prepared",
        0,
        0,
        0,
        None,
    );
    let root = if simplified { out.expr } else { original };
    let cfg = native_config(options);
    let start = counters.start();
    let mut native = Question::valid(&mut cx, root, &cfg).unwrap();
    let reading = counters.stop(start);
    let stats = native.stats();
    row(
        name,
        spelling_name,
        mode,
        expected,
        "native-prepare",
        reading,
        "prepared",
        stats.nodes,
        stats.vars,
        stats.clauses,
        Some((
            stats.conflicts,
            stats.propagations,
            stats.samples,
            stats.learned,
        )),
    );
    let start = counters.start();
    let answer = native
        .solve(
            &mut cx,
            Limits {
                conflicts: 200,
                propagations: 100_000,
            },
        )
        .unwrap();
    let reading = counters.stop(start);
    let status = native_verdict(&mut cx, original, expected, &answer, true);
    let stats = native.stats();
    row(
        name,
        spelling_name,
        mode,
        expected,
        "native-search",
        reading,
        status,
        stats.nodes,
        stats.vars,
        stats.clauses,
        Some((
            stats.conflicts,
            stats.propagations,
            stats.samples,
            stats.learned,
        )),
    );
    let mut sampled_model = false;
    if escalate && matches!(answer, Outcome::Unknown(_)) {
        let sample_cfg = cfg.with_samples(65_536).with_sample_mode(if word_sampling {
            SampleMode::Words
        } else {
            SampleMode::Small
        });
        let start = counters.start();
        let probe = Question::valid(&mut cx, root, &sample_cfg).unwrap();
        let reading = counters.stop(start);
        let status = match probe.outcome() {
            Some(answer) => native_verdict(&mut cx, original, expected, answer, true),
            None => "not-found",
        };
        sampled_model = matches!(probe.outcome(), Some(Outcome::Refuted(_)));
        let stats = probe.stats();
        row(
            name,
            spelling_name,
            mode,
            expected,
            "native-small-samples",
            reading,
            status,
            stats.nodes,
            stats.vars,
            stats.clauses,
            Some((
                stats.conflicts,
                stats.propagations,
                stats.samples,
                stats.learned,
            )),
        );
    }
    if escalate && !sampled_model && matches!(answer, Outcome::Unknown(_)) {
        for (stage, (conflicts, propagations)) in [
            (1_000, 500_000),
            (10_000, 5_000_000),
            (100_000, 50_000_000),
            (1_000_000, 500_000_000),
        ]
        .into_iter()
        .enumerate()
        {
            if fast && stage == 3 {
                break;
            }
            let start = counters.start();
            let answer = native
                .solve(
                    &mut cx,
                    Limits {
                        conflicts,
                        propagations,
                    },
                )
                .unwrap();
            let reading = counters.stop(start);
            let status = native_verdict(&mut cx, original, expected, &answer, true);
            let stats = native.stats();
            row(
                name,
                spelling_name,
                mode,
                expected,
                &format!("native-resume-{}", stage + 1),
                reading,
                status,
                stats.nodes,
                stats.vars,
                stats.clauses,
                Some((
                    stats.conflicts,
                    stats.propagations,
                    stats.samples,
                    stats.learned,
                )),
            );
            if !matches!(answer, Outcome::Unknown(_)) {
                break;
            }
        }
    }
    drop(native);
    let start = counters.start();
    let circuit = circuit(&mut cx, root);
    let reading = counters.stop(start);
    let nodes = circuit.graph.len();
    row(
        name,
        spelling_name,
        mode,
        expected,
        "blast",
        reading,
        "prepared",
        nodes,
        0,
        0,
        None,
    );
    let start = counters.start();
    let (mut solver, cnf) = encode(&circuit);
    let reading = counters.stop(start);
    let vars = solver.num_vars();
    let clauses = cnf.clauses.len();
    row(
        name,
        spelling_name,
        mode,
        expected,
        "cnf",
        reading,
        "prepared",
        nodes,
        vars,
        clauses,
        Some((
            solver.conflicts,
            solver.propagations,
            0,
            solver.num_learnts(),
        )),
    );
    for (stage, limits) in [
        Limits {
            conflicts: 10,
            propagations: 5_000,
        },
        Limits {
            conflicts: 40,
            propagations: 20_000,
        },
        Limits {
            conflicts: 150,
            propagations: 75_000,
        },
    ]
    .into_iter()
    .enumerate()
    {
        let start = counters.start();
        let last = solver.solve_within(limits);
        let reading = counters.stop(start);
        let status = verdict(
            &mut cx,
            original,
            &circuit,
            &cnf,
            &mut solver,
            &last,
            expected,
        );
        row(
            name,
            spelling_name,
            mode,
            expected,
            &format!("resume-{}", stage + 1),
            reading,
            status,
            nodes,
            vars,
            clauses,
            Some((
                solver.conflicts,
                solver.propagations,
                0,
                solver.num_learnts(),
            )),
        );
        if last != Answer::Unknown {
            break;
        }
    }
    drop(solver);
    drop(cnf);
    // One fresh search under the sum of the scheduled limits: encoding is outside its
    // measured search interval. Limits count additional work after CNF preparation.
    let (mut solver, cnf) = encode(&circuit);
    let start = counters.start();
    let whole = solver.solve_within(Limits {
        conflicts: 200,
        propagations: 100_000,
    });
    let reading = counters.stop(start);
    let status = verdict(
        &mut cx,
        original,
        &circuit,
        &cnf,
        &mut solver,
        &whole,
        expected,
    );
    row(
        name,
        spelling_name,
        mode,
        expected,
        "single-search",
        reading,
        status,
        nodes,
        vars,
        clauses,
        Some((
            solver.conflicts,
            solver.propagations,
            0,
            solver.num_learnts(),
        )),
    );
    ExitCode::SUCCESS
}

pub fn report(filters: &[String], options: SearchOptions) -> ExitCode {
    let SearchOptions {
        escalate,
        relations,
        selectors,
        input_cancellation,
        join_factoring,
        xor3,
        carry_save,
        word_sampling,
        fast,
        query_budget_ns,
        exhaustive_inputs,
    } = options;
    println!(
        "case,spelling,mode,expected,phase,status,instructions,cpu_ns,wall_ns,aig_nodes,cnf_vars,cnf_clauses,conflicts,propagations,process_peak_kib,samples,learned"
    );
    let executable = std::env::current_exe().expect("current executable");
    let mut passed = true;
    let mut selected = 0;
    for &case in fixture::CASES {
        if !filters.is_empty() && !filters.iter().any(|f| case.contains(f)) {
            continue;
        }
        selected += 1;
        for spelling in ["nested", "compact"] {
            let modes: &[&str] = if query_budget_ns.is_some() {
                &["raw"]
            } else {
                &["raw", "simplified"]
            };
            for &mode in modes {
                let mut command = Command::new(&executable);
                command.args(["--mixer-case", case, spelling, mode]);
                if escalate {
                    command.arg(if fast { "fast" } else { "escalate" });
                }
                if relations {
                    command.arg("relations");
                }
                if selectors {
                    command.arg("selectors");
                }
                if input_cancellation {
                    command.arg("input-cancel");
                }
                if join_factoring {
                    command.arg("factor-joins");
                }
                if xor3 {
                    command.arg("xor3");
                }
                if carry_save {
                    command.arg("carry-save");
                }
                if word_sampling {
                    command.arg("word-samples");
                }
                if let Some(ns) = query_budget_ns {
                    command.arg(format!("query-budget-ns={ns}"));
                }
                if exhaustive_inputs != 0 {
                    command.arg(format!("exhaustive-inputs={exhaustive_inputs}"));
                }
                let result = command.status().expect("keyed-mixer worker");
                if !result.success() {
                    passed = false;
                }
            }
        }
    }
    if query_budget_ns.is_some() && selected == 0 {
        eprintln!("no mixer fixtures match the complete-query acceptance filters");
        return ExitCode::from(2);
    }
    if passed {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitwright::prove::{Config, Question};

    #[test]
    fn only_checked_decisions_within_the_complete_query_budget_pass() {
        for status in ["proved", "refuted-replayed"] {
            assert!(budget_status(status, 9, 10).1);
            assert!(budget_status(status, 10, 10).1);
            assert!(!budget_status(status, 11, 10).1);
        }
        assert_eq!(
            budget_status("unknown-budget", 9, 10),
            ("unknown-within-time", false)
        );
        assert_eq!(
            budget_status("unknown-budget", 10, 10),
            ("unknown-within-time", false)
        );
        assert_eq!(
            budget_status("unknown-budget", 11, 10),
            ("unknown-over-time", false)
        );
    }

    #[test]
    fn staged_adapter_matches_native_question_encoding_before_and_after_simplification() {
        for spelling in [Spelling::Nested, Spelling::Compact] {
            for &name in fixture::CASES {
                let mut cx = Context::new();
                let (original, _) = fixture::claim(&mut cx, name, spelling);
                let simplified = Engine::standard().simplify(&mut cx, original).unwrap().expr;
                for root in [original, simplified] {
                    let staged = circuit(&mut cx, root);
                    let (solver, cnf) = encode(&staged);
                    let cfg = Config::default()
                        .with_certificate(true)
                        .with_samples(0)
                        .with_simplify(false);
                    let mut native = Question::valid(&mut cx, root, &cfg).unwrap();
                    let stats = native.stats();
                    if stats.nodes < staged.graph.len() {
                        // Native preparation can prove the outer Boolean structure without
                        // expanding the fixture's predicates; the adapter expands all of them.
                        assert_eq!(stats.nodes, 1);
                        let Outcome::Proved(Some(cert)) =
                            native.solve(&mut cx, Limits::conflicts(0)).unwrap()
                        else {
                            panic!("a reduced native circuit must be a checked tautology");
                        };
                        cert.check().unwrap();
                    } else {
                        assert_eq!(stats.nodes, staged.graph.len());
                    }
                    assert_eq!(stats.vars, solver.num_vars());
                    assert_eq!(stats.clauses, cnf.clauses.len());
                }
            }
        }
    }
}
