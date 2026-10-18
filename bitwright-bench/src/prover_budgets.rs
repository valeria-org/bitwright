//! `--prover-budgets`: what the prover's word-level simplification settles under a budget of
//! work units, and what it saves the search, on an MBA-heavy question and on invertible-mix
//! questions. Every row is run twice and must report the same work both times.

use crate::counter::Counters;
use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::MbaConfig;
use bitwright::prove::{Config, Outcome, Question, Stats};
use bitwright::{Context, Expr, ParseOptions, Width};
use std::process::ExitCode;

/// The search's budget in every row (questions it does not settle stop there).
const CONFLICTS: u64 = 20_000;

/// `n` MBA identities over fresh symbols, conjoined: linear ones and products.
fn identities(n: usize) -> String {
    let forms = [
        "((a{i} ^ b{i}) + 2 * (a{i} & b{i})) == (a{i} + b{i})",
        "((a{i} | b{i}) - (a{i} & b{i})) == (a{i} ^ b{i})",
        "(a{i} & b{i}) * (a{i} | b{i}) + (a{i} & ~b{i}) * (~a{i} & b{i}) == a{i} * b{i}",
        "((a{i} + b{i}) - (a{i} & b{i})) * c{i} == (a{i} | b{i}) * c{i}",
    ];
    (0..n)
        .map(|i| {
            format!(
                "({})",
                forms[i % forms.len()].replace("{i}", &i.to_string())
            )
        })
        .collect::<Vec<_>>()
        .join(" & ")
}

fn hash(x: u64, c: u64) -> u64 {
    let t = c.wrapping_mul(x ^ c);
    c.wrapping_mul(t ^ ((t >> 32) >> (t >> 60)))
}

fn inverse_odd(c: u64) -> u64 {
    let mut i = c;
    for _ in 0..6 {
        i = i.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(i)));
    }
    i
}

fn unhash(h: u64, c: u64) -> u64 {
    let ci = inverse_odd(c);
    let u = h.wrapping_mul(ci);
    (u ^ ((u >> 32) >> (u >> 60))).wrapping_mul(ci) ^ c
}

fn mix(v: &str, c: u64) -> String {
    let t = format!("(0x{c:x} * ({v} ^ 0x{c:x}))");
    format!("(0x{c:x} * ({t} ^ (({t} >>u 32) >>u ({t} >>u 60))))")
}

fn unmix(v: &str, c: u64) -> String {
    let ci = inverse_odd(c);
    let u = format!("({v} * 0x{ci:x})");
    format!("((({u} ^ (({u} >>u 32) >>u ({u} >>u 60))) * 0x{ci:x}) ^ 0x{c:x})")
}

const KEYS: [u64; 9] = [
    0x87c3_7b91_1142_53d5,
    0xd933_008c_f055_faf9,
    0xf215_3a1b_2303_b72d,
    0xf374_ef4e_753c_875d,
    0xc354_c462_2bc1_0a31,
    0xfc14_d111_f5d3_19a5,
    0xc8ff_640a_8b8c_13dd,
    0xfd6a_3327_3321_27b3,
    0xd219_840c_12f8_b8e5,
];

/// Questions about invertible mixes (each a predicate to prove or refute), with a label.
fn mix_questions() -> Vec<(String, String)> {
    let mut v = Vec::new();
    for c in KEYS {
        v.push((
            format!("cancel {c:016x}"),
            format!("({} == {}) == (x == y)", mix("x", c), mix("y", c)),
        ));
    }
    for c in KEYS {
        let k = 0x079c_2a2c_658e_1c19_u64;
        let x = unhash(k, c);
        debug_assert_eq!(hash(x, c), k);
        v.push((
            format!("solve  {c:016x}"),
            format!("({} == 0x{k:x}) == (x == 0x{x:x})", mix("x", c)),
        ));
    }
    for c in KEYS {
        v.push((
            format!("round  {c:016x}"),
            format!("{} == x", unmix(&mix("x", c), c)),
        ));
    }
    let [a, b, d, e] = [KEYS[5], KEYS[6], KEYS[7], KEYS[8]].map(|c| mix("p", c));
    v.push((
        "guard (free lane)".into(),
        format!(
            "~(~(X <u 0xa7686e8568a22fc5) & ((((({a} ^ {b} ^ 0x1111222233334444) \
             | ({b} ^ {d} ^ 0x5555666677778888) | ({b} ^ {e} ^ 0x9999aaaabbbbcccc)) \
             - (X ^ 0xd6ca73547960a840)) + 0x79c2a2c658e1c19) == 0))"
        ),
    ));
    v
}

/// A question's answer and work, asked once.
fn ask(src: &str, w: Width, cfg: &Config) -> (&'static str, Stats) {
    let mut cx = Context::new();
    let p = cx.parse(src, &ParseOptions::width(w)).expect("parse");
    let mut q = Question::valid(&mut cx, p, cfg).expect("question");
    let out = q.solve(&mut cx, cfg.limits()).expect("solve");
    let label = match out {
        Outcome::Proved(_) => "proved",
        Outcome::Refuted(_) => "refuted",
        Outcome::Unknown(_) => "unknown",
        _ => "?",
    };
    (label, q.stats())
}

/// The conjuncts of `src` the prover's engine leaves under `budget` (it is the engine the
/// prover simplifies with).
fn left(engine: &Engine, src: &str, w: Width, budget: Budget) -> usize {
    let mut cx = Context::new();
    let p = cx.parse(src, &ParseOptions::width(w)).expect("parse");
    let r = engine
        .run(&mut cx, &[p], Run::default().with_per_call(budget))
        .expect("run")
        .roots[0]
        .expr;
    conjuncts(&cx, r)
}

fn conjuncts(cx: &Context, e: Expr) -> usize {
    use bitwright::{BinOp, View};
    match cx.view(e).expect("view") {
        View::Bin(BinOp::And, a, b) if cx.width(e).expect("width") == Width::W1 => {
            conjuncts(cx, a) + conjuncts(cx, b)
        }
        View::Const(v) if !v.is_zero() => 0,
        _ => 1,
    }
}

fn fuel_label(fuel: Option<u64>) -> String {
    match fuel {
        None => "off".into(),
        Some(f) if f == 1 << 22 => "default".into(),
        Some(f) => format!("2^{}", f.trailing_zeros()),
    }
}

pub fn report() -> ExitCode {
    let mut counters = Counters::open();
    if let Some(why) = &counters.unavailable {
        println!("(instructions not counted: {why})");
    }
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
        .build()
        .expect("engine");
    let fuels = [
        None,
        Some(1u64 << 8),
        Some(1 << 10),
        Some(1 << 12),
        Some(1 << 14),
        Some(1 << 16),
        Some(1 << 22),
    ];
    let n = 48;
    let src = identities(n);
    // The first MBA solver call builds tables once per process: not part of any row.
    let _ = ask(&src, Width::W64, &Config::default());
    println!(
        "MBA-heavy question: {n} identities over 64-bit symbols, conjoined; search budget \
         {CONFLICTS} conflicts"
    );
    println!(
        "{:>8} {:>12} {:>8} {:>8} {:>5} {:>8} {:>8} {:>8} {:>10} {:>12} {:>9} {:>9}",
        "fuel",
        "stopped",
        "visits",
        "pass",
        "mba",
        "settled",
        "nodes",
        "answer",
        "conflicts",
        "propagations",
        "Minstr",
        "ms"
    );
    let mut ok = true;
    for fuel in fuels {
        let cfg = match fuel {
            None => Config::default().with_simplify(false),
            Some(f) => Config::default().with_simplify_fuel(f),
        }
        .with_max_conflicts(CONFLICTS);
        let start = counters.start();
        let (answer, s) = ask(&src, Width::W64, &cfg);
        let reading = counters.stop(start);
        let (answer2, s2) = ask(&src, Width::W64, &cfg);
        let same = answer == answer2 && s == s2;
        ok &= same;
        let settled = match fuel {
            None => 0,
            Some(f) => n - left(&engine, &src, Width::W64, Budget::fuel(f)),
        };
        let simp = s.simplification;
        println!(
            "{:>8} {:>12} {:>8} {:>8} {:>5} {:>8} {:>8} {:>8} {:>10} {:>12} {:>9} {:>9.1}{}",
            fuel_label(fuel),
            simp.stopped
                .map_or_else(|| "-".to_string(), |w| format!("{w:?}")),
            simp.spent.node_visits,
            simp.spent.pass_work,
            simp.spent.mba_calls,
            format!("{settled}/{n}"),
            s.nodes,
            answer,
            s.conflicts,
            s.propagations,
            reading
                .instructions
                .map_or_else(|| "-".into(), |i| format!("{:.1}", i as f64 / 1e6)),
            reading.wall_ns as f64 / 1e6,
            if same { "" } else { "  NOT REPRODUCIBLE" },
        );
    }
    println!();
    println!(
        "Invertible mixes: 27 identities of the protector's mix under nine keys and one guard \
         over four of them; search budget {CONFLICTS} conflicts"
    );
    println!(
        "{:>8} {:>8} {:>8} {:>8} {:>10} {:>12} {:>9} {:>9}",
        "fuel", "word", "search", "unknown", "conflicts", "propagations", "Minstr", "ms"
    );
    let questions = mix_questions();
    for fuel in [None, Some(1u64 << 12), Some(1 << 22)] {
        let cfg = match fuel {
            None => Config::default().with_simplify(false),
            Some(f) => Config::default().with_simplify_fuel(f),
        }
        .with_max_conflicts(CONFLICTS);
        let (mut word, mut search, mut unknown, mut conflicts, mut props) = (0, 0, 0, 0u64, 0u64);
        let start = counters.start();
        let mut rows = Vec::new();
        for (_, q) in &questions {
            let (answer, s) = ask(q, Width::W64, &cfg);
            match answer {
                "unknown" => unknown += 1,
                _ if s.simplification.decided => word += 1,
                _ => search += 1,
            }
            conflicts += s.conflicts;
            props += s.propagations;
            rows.push((answer, s));
        }
        let reading = counters.stop(start);
        let same = questions
            .iter()
            .zip(&rows)
            .all(|((_, q), r)| ask(q, Width::W64, &cfg) == *r);
        ok &= same;
        println!(
            "{:>8} {:>8} {:>8} {:>8} {:>10} {:>12} {:>9} {:>9.1}{}",
            fuel_label(fuel),
            word,
            search,
            unknown,
            conflicts,
            props,
            reading
                .instructions
                .map_or_else(|| "-".into(), |i| format!("{:.1}", i as f64 / 1e6)),
            reading.wall_ns as f64 / 1e6,
            if same { "" } else { "  NOT REPRODUCIBLE" },
        );
    }
    println!();
    println!(
        "word: decided by simplification alone; search: by the circuit; every row asked twice, \
         with identical answers and work{}",
        if ok { "" } else { " (EXCEPT THOSE MARKED)" }
    );
    if ok {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
