//! What a caller rationing the prover can rely on: simplification under a budget of work units
//! (never time) that keeps what it did and says what it spent, and a resumed question that
//! reports each search's marginal cost. Every number is the same on every run.
#![cfg(feature = "prove")]

use bitwright::engine::Budget;
use bitwright::prove::{Config, Limits, Outcome, Question, Stats};
use bitwright::{Context, Expr, ParseOptions, Width};

/// `n` MBA identities over fresh symbols, conjoined: linear ones the engine settles by rules
/// and normal forms, and products, which bit-level search finds hard.
fn identities(n: usize) -> String {
    let forms = [
        "((a{i} ^ b{i}) + 2 * (a{i} & b{i})) == (a{i} + b{i})",
        "((a{i} | b{i}) - (a{i} & b{i})) == (a{i} ^ b{i})",
        "(a{i} & b{i}) * (a{i} | b{i}) + (a{i} & ~b{i}) * (~a{i} & b{i}) == a{i} * b{i}",
        "((a{i} + b{i}) - (a{i} & b{i})) == (a{i} | b{i})",
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

fn ask(src: &str, w: Width, cfg: &Config) -> (Option<Outcome>, Stats) {
    let mut cx = Context::new();
    let p = cx.parse(src, &ParseOptions::width(w)).unwrap();
    let mut q = Question::valid(&mut cx, p, cfg).unwrap();
    let out = q.solve(&mut cx, cfg.limits()).unwrap();
    (Some(out), q.stats())
}

fn label(o: &Option<Outcome>) -> &'static str {
    match o {
        Some(Outcome::Proved(_)) => "proved",
        Some(Outcome::Refuted(_)) => "refuted",
        Some(Outcome::Unknown(_)) => "unknown",
        _ => "?",
    }
}

/// Fuel from none to the default on one question: every budget gives the same answer on
/// every run, never one that contradicts another; the engine spends within its caps and says
/// which one stopped it; what it settled before stopping stays settled, so the circuit left
/// for the search shrinks as the fuel grows, and enough fuel decides the question alone.
#[test]
fn simplification_within_a_budget() {
    assert_eq!(Budget::default(), Budget::fuel(1 << 22));
    assert_eq!(Config::default().simplify_budget, Budget::default());
    let src = identities(24);
    let w = Width::W16;
    let base = Config::default().with_max_conflicts(200).with_samples(64);
    let (off, off_stats) = ask(&src, w, &base.with_simplify(false));
    assert!(!off_stats.simplification.ran);
    assert_ne!(label(&off), "refuted");
    let mut rows = Vec::new();
    for fuel in [0u64, 1 << 6, 1 << 8, 1 << 10, 1 << 12, 1 << 22] {
        let cfg = base.with_simplify_fuel(fuel);
        let (out, s) = ask(&src, w, &cfg);
        // The same work and the same answer on every run.
        let (again, s2) = ask(&src, w, &cfg);
        assert_eq!(s, s2, "fuel {fuel}");
        assert_eq!(label(&out), label(&again));
        // The answers of a valid question: proved, or not decided.
        assert_ne!(label(&out), "refuted", "fuel {fuel}");
        let simp = s.simplification;
        assert!(simp.ran);
        assert!(
            simp.spent.node_visits <= fuel,
            "fuel {fuel}: {:?}",
            simp.spent
        );
        assert!(simp.spent.mba_calls <= Budget::fuel(fuel).mba_calls);
        if simp.stopped.is_some() {
            assert!(!simp.decided, "fuel {fuel}");
        }
        rows.push((fuel, label(&out), simp, s.nodes));
    }
    // Once a budget lets the engine finish, every larger one does.
    let first_done = rows.iter().position(|r| r.2.stopped.is_none()).unwrap();
    assert!(rows[first_done..].iter().all(|r| r.2.stopped.is_none()));
    assert!(first_done >= 2, "small budgets stop the engine: {rows:?}");
    // The circuit left shrinks with the fuel; a budget that stops the engine midway already
    // leaves a smaller one than no simplification at all.
    let mut last = off_stats.nodes;
    for r in &rows {
        assert!(r.3 <= last, "{rows:?}");
        last = r.3;
    }
    assert!(
        rows[..first_done].iter().any(|r| r.3 < off_stats.nodes),
        "no stopped run kept work: {rows:?}"
    );
    // Enough fuel decides it with no circuit and no search.
    let full = rows.last().unwrap();
    assert!(
        full.2.decided && full.1 == "proved" && full.3 == 0,
        "{full:?}"
    );
}

fn mix(v: &str) -> String {
    let c = 0x87c3_7b91_1142_53d5u64;
    let t = format!("(0x{c:x} * ({v} ^ 0x{c:x}))");
    format!("(0x{c:x} * ({t} ^ (({t} >>u 32) >>u ({t} >>u 60))))")
}

/// A question bit-level search does not settle in a few hundred conflicts.
fn hard(cx: &mut Context) -> Expr {
    let src = format!("({} == {}) == (x == y)", mix("x"), mix("y"));
    cx.parse(&src, &ParseOptions::width(Width::W64)).unwrap()
}

#[test]
fn resumed_searches_report_their_marginal_cost() {
    let cfg = Config::default().with_simplify(false).with_samples(0);
    let run = || {
        let mut cx = Context::new();
        let p = hard(&mut cx);
        let mut q = Question::valid(&mut cx, p, &cfg).unwrap();
        let built = q.stats();
        assert_eq!((built.searches, built.conflicts), (0, 0));
        let mut seen = vec![built];
        for _ in 0..3 {
            let out = q.solve(&mut cx, Limits::conflicts(100)).unwrap();
            assert!(matches!(out, Outcome::Unknown(ref why) if why.is_budget()));
            seen.push(q.stats());
        }
        seen
    };
    let first = run();
    // Deterministic: the same numbers from a second question asked the same way.
    assert_eq!(first, run());
    for (i, pair) in first.windows(2).enumerate() {
        let (a, b) = (pair[0], pair[1]);
        assert_eq!(b.searches, i as u32 + 1);
        assert_eq!(b.last_conflicts, 100);
        assert_eq!(b.conflicts, a.conflicts + b.last_conflicts);
        assert_eq!(b.propagations, a.propagations + b.last_propagations);
        assert_eq!(b.decisions, a.decisions + b.last_decisions);
        assert_eq!(b.lemmas, a.lemmas + b.last_lemmas);
        assert!(b.fixed >= a.fixed && b.fixed <= b.vars as usize);
    }
    // Resumed three times, the question has done what one search under 300 conflicts does,
    // and the last resume cost a third of the conflicts and less than that search's
    // propagations.
    let mut cx = Context::new();
    let p = hard(&mut cx);
    let mut fresh = Question::valid(&mut cx, p, &cfg).unwrap();
    assert!(matches!(
        fresh.solve(&mut cx, Limits::conflicts(300)).unwrap(),
        Outcome::Unknown(_)
    ));
    let (resumed, once) = (first[3], fresh.stats());
    assert_eq!(resumed.totals(), once.totals());
    assert!(resumed.last_propagations < once.last_propagations);
    assert_eq!(once.last_conflicts, 300);
}

/// A question is simplified with the opaque-constant sweep: a product of two forms that are
/// constant though each reads a comparison's mask (`(m ^ c) + 2·(m & c) − m` is `c`, `(m | c) −
/// (m & ~c)` is `c`) is folded before the circuit is built, and the question is decided with
/// no circuit.
#[cfg(feature = "mba")]
#[test]
fn hidden_constants_fold_before_the_circuit() {
    let src = "let m = -zext<64>(x <u y); \
         let k = ((m ^ 0x1234) + 2 * (m & 0x1234) - m) * ((m | 0x77) - (m & ~0x77)); \
         (z ^ k) * (k + 3) == (z ^ 0x8762c) * 0x8762f";
    let cfg = Config::default().with_max_conflicts(200).with_samples(64);
    let (out, s) = ask(src, Width::W64, &cfg);
    assert_eq!(label(&out), "proved");
    assert!(s.simplification.decided && s.nodes == 0, "{s:?}");
}

/// The same byte function under a narrow cast or a full-word mask. Each bit needs four
/// source bits, even though the address and the common terms are unrestricted 64-bit words.
#[cfg(feature = "mba")]
#[test]
fn weighted_byte_sums_under_shared_operations() {
    let terms = |offset: u64, coefficient: u64| format!("\
        let p = x:64 + {offset};
        let a = trunc<8>(p);
        let b = extract<8, 8>(x);
        let c = extract<16, 8>(p);
        let d = extract<24, 8>(p);
        let lhs = (zext<64>((a | b) & (c ^ d)) * {coefficient} + y + z) * m;
        let ab = ((p & ~(p >>u 8)) ^ (x >>u 8));
        let rhs = (z + (ab & (p >>u 16 ^ p >>u 24) & 255) * {coefficient} + y) * m;
    ");
    let cfg = Config::default()
        .with_max_conflicts(2_000)
        .with_max_propagations(400_000)
        .with_sweeping(false);
    // The offset leaves the low two byte lanes intact. Its other bits, the
    // coefficient (even or odd) and the mask shared by the readers can change.
    for (offset, weight, mask) in [
        (0xff000000, 0xe1827345, 17_u64),
        (0x8b6d000000, 0x70298a, 0x4071),
        (0xf917c8000000, u64::MAX - 2, 0xf0020101),
    ] {
        let terms = terms(offset, weight);
        for cmp in [String::from("lhs == rhs"), format!("((lhs | {mask}) <=u k) == ((rhs | {mask}) <=u k)")] {
            let (out, stats) = ask(&format!("{terms}{cmp}"), Width::W64, &cfg);
            assert_eq!(label(&out), "proved");
            assert!(stats.simplification.decided, "{stats:?}");
        }
    }
    // Changing the second byte of the offset invalidates the projection;
    // so does reading the wrong lane or reversing only one comparison.
    let misaligned = format!("{}lhs == rhs", terms(0xff001900, 0xe1827345));
    let terms = terms(0xff000000, 0xe1827345);
    for src in [
        misaligned,
        format!("{}lhs == rhs", terms.replace("p >>u 16 ^", "p >>u 8 ^")),
        format!("{terms}((lhs | 17) <=u k) == (k <=u (rhs | 17))"),
    ] {
        let (out, _) = ask(&src, Width::W64, &cfg);
        assert_eq!(label(&out), "refuted");
    }
}
