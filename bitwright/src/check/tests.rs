//! Checker and compiler tests: sound rules pass, unsound rules are refuted with a
//! counterexample, malformed rules are rejected with the right diagnostic.

use super::*;
use crate::rules::{CompileError, RuleProgram};

fn program(body: &str) -> RuleProgram {
    let src = format!("bitwright 1;\ngroup t {{\n{body}\n}}\n");
    RuleProgram::compile(&src).unwrap_or_else(|e| panic!("{}", e.render("t.bwr", &src)))
}

fn compile_err(body: &str) -> CompileError {
    let src = format!("bitwright 1;\ngroup t {{\n{body}\n}}\n");
    match RuleProgram::compile(&src) {
        Ok(_) => panic!("expected a compile error for:\n{body}"),
        Err(e) => e,
    }
}

fn codes(e: &CompileError) -> Vec<&'static str> {
    e.diagnostics
        .iter()
        .filter(|d| d.level == crate::rules::Level::Error)
        .map(|d| d.code)
        .collect()
}

fn check_one(body: &str) -> RuleCheck {
    let p = program(body);
    assert_eq!(p.rules().len(), 1);
    check_rule(&p.rules()[0], &CheckConfig::default())
}

#[test]
fn sound_rules_pass() {
    for body in [
        "identity add_and_or<W>(x: W, y: W) { (x & y) + (x | y) <=> x + y }",
        "identity xor_and<W>(x: W, y: W) { (x ^ y) + 2 * (x & y) <=> x + y }",
        "rule and_absorb<W>(x: W, y: W) { x & (x | y) => x }",
        "rule neg_not<W>(x: W) { -(~x) => x + 1 }",
        "rule not_neg<W>(x: W) { ~(-x) => x - 1 }",
        "rule mul_pow2<W>(x: W, c: const W) { x * c => x << k if is_pow2(c) let k: W = ctz(c) }",
        "rule mask_redundant<W>(x: W, c: const W) { x & c => x if zero_bits(x, ~c) }",
        "rule add_disjoint<W>(x: W, y: W) { x + y => x | y if disjoint(x, y) }",
        "rule eq_eq_distinct<W>(a: W, b: W, c: W) { (a == b) & (a == c) => false if proves(b != c) }",
        "rule sext_from_sign_word<W, U>(a: W) where W < U, U <= 2 * W { \
            zext<U>(a) | (zext<U>(a >>s (W - 1)) << W) => sext<U>(a) }",
        "rule divmod<W>(x: W, y: W) { sdiv(x, y) * y + srem(x, y) => x }",
        "rule zext_trunc<W, N>(x: W) where N < W { zext<W>(trunc<N>(x)) => x & lowmask(N) }",
        "rule ult_zero<W>(x: W) { x <u 1 => x == 0 }",
    ] {
        let c = check_one(body);
        assert!(c.is_sound(), "{body}\n{:?}\n{}", c.verdict, c.evidence);
        assert!(
            c.evidence.exhaustive_cases > 0 && c.evidence.guard_true_cases() > 0,
            "{body}"
        );
    }
}

#[test]
fn unsound_rules_are_refuted() {
    for (body, why) in [
        (
            "rule sext_unbounded<W, U>(a: W) where W < U { \
                zext<U>(a) | (zext<U>(a >>s (W - 1)) << W) => sext<U>(a) }",
            "missing U <= 2W",
        ),
        (
            "rule eq_eq_adjacent<W>(a: W, b: const W, c: const W) { \
                (a == b) & (a == c) => false if b <=s c - 1 }",
            "c - 1 wraps at the signed minimum",
        ),
        (
            "rule inc_below<W>(x: W) { (x + 1) <u x => false }",
            "wraps at all ones",
        ),
        (
            "rule shl_lshr<W>(x: W, c: const W) { (x << c) >>u c => x }",
            "loses high bits",
        ),
        (
            "rule udiv_self<W>(x: W) { udiv(x, x) => 1 }",
            "udiv(0, 0) = ones",
        ),
        (
            "rule rotl_rotl<W>(x: W, a: const W, b: const W) { rotl(rotl(x, a), b) => rotl(x, a + b) }",
            "a + b wraps mod 2^W, not mod W",
        ),
        (
            "rule mask_wrong<W>(x: W, c: const W) { x & c => x if zero_bits(x, c) }",
            "wrong mask",
        ),
        (
            "identity sub_comm<W>(x: W, y: W) { x - y <=> y - x }",
            "not commutative",
        ),
    ] {
        let c = check_one(body);
        match &c.verdict {
            Verdict::Unsound(cex) => {
                // The counterexample really is one.
                assert_ne!(cex.lhs, cex.rhs, "{body}");
            }
            v => panic!("{why}: expected a counterexample for\n{body}\ngot {v:?}"),
        }
    }
}

#[test]
fn counterexamples_are_small_and_readable() {
    let c = check_one("rule udiv_self<W>(x: W) { udiv(x, x) => 1 }");
    let Verdict::Unsound(cex) = c.verdict else {
        panic!()
    };
    // At W = 1, udiv(0, 0) = ones = 1: the first counterexample is at W = 2.
    assert_eq!(cex.widths, vec![("W".to_string(), 2)]);
    assert_eq!(cex.params[0].1.to_u64(), Some(0));
    assert_eq!(
        cex.to_string(),
        "W = 2; x = 0x0:2: lhs = 0x3:2, rhs = 0x1:2"
    );
}

#[test]
fn malformed_rules_are_rejected() {
    let cases: &[(&str, &str)] = &[
        (
            "rule neg_fact<W>(x: W, c: const W) { x & c => x if !zero_bits(x, c) }",
            "BW0106",
        ),
        (
            "rule impure<W>(x: W, y: W) { x & y => x if x == y }",
            "BW0105",
        ),
        (
            "identity guarded<W>(x: W) { x + 0 <=> x if true }",
            "BW0304",
        ),
        (
            "identity kinds<W>(x: W, c: const W) { x + c <=> c + x }",
            "BW0304",
        ),
        (
            "identity one_side<W>(x: W, y: W) { x & (x | y) <=> x }",
            "BW0304",
        ),
        (
            "rule grows<W>(x: W) where W > 1 { x << 1 => x * 2 }",
            "BW0302",
        ),
        // Termination is not a lint: it cannot be allowed away.
        (
            "#[allow(BW0302)] rule grows<W>(x: W) where W > 1 { x << 1 => x * 2 }",
            "BW0002",
        ),
        (
            "rule disjoint_expr<W>(x: W, y: W) { x + y => x | y if disjoint(x, y + 1) }",
            "BW0104",
        ),
        ("rule dup<W>(x: W) { x + x => x * x * x }", "BW0302"),
        // Smaller, but duplicates x: violates the variable condition (could loop).
        (
            "rule dup_small<W>(x: W, y: W) { x & (y & (y & y)) => x * x }",
            "BW0302",
        ),
        ("rule typed<W>(x: W) { x | x => x ^ lowmask(8) }", "BW0107"),
        ("rule unbound<W>(x: W, y: W) { x => y }", "BW0103"),
        ("rule widths<W, U>(x: W, y: U) { x + y => x }", "BW0101"),
        (
            "rule bad_proves<W>(x: W, y: W) { x & y => x if proves(x & y) }",
            "BW0104",
        ),
        (
            "rule proves_compound<W>(x: W, y: W) { x & y => x if proves(x + 1 == y) }",
            "BW0104",
        ),
        (
            "rule let_in_pattern<W>(x: W, c: const W) { x + k => x let k: W = c }",
            "BW0103",
        ),
        ("rule mystery<W>(x: W) { x => nope }", "BW0103"),
        ("rule lowercase<w>(x: w) { x => x }", "BW0102"),
    ];
    for (body, code) in cases {
        let e = compile_err(body);
        assert!(
            codes(&e).contains(code),
            "{body}: expected {code}, got {:?}",
            e.diagnostics
        );
    }
}

#[test]
fn termination_order_orients_canonical_forms() {
    let p = program(
        "rule a<W>(x: W, c: const W) { x * c => x << k if is_pow2(c) let k: W = ctz(c) }
         rule b<W>(x: W, y: W) { x + y => x | y if disjoint(x, y) }
         identity c<W>(x: W, y: W, z: W) { x * (y + z) <=> x * y + x * z }",
    );
    assert!(p.rules()[0].is_directed());
    assert!(p.rules()[1].is_directed());
    assert!(
        !p.rules()[2].is_directed(),
        "distribution grows: search only"
    );
    assert!(p.diagnostics().iter().any(|d| d.code == "BW0409"));
}

#[test]
fn rule_ids_ignore_names_and_formatting() {
    let a = program("rule a<W>(x: W, y: W) { x & (x | y) => x }");
    let b = program("rule other_name<V>(p: V, q: V) {\n  p & (p | q)\n  => p\n}");
    let c = program("rule a<W>(x: W, y: W) { x | (x & y) => x }");
    assert_eq!(a.rules()[0].id, b.rules()[0].id);
    assert_ne!(a.rules()[0].id, c.rules()[0].id);
}

#[test]
fn ledger_round_trips_and_detects_drift() {
    let p = program(
        "identity add_and_or<W>(x: W, y: W) { (x & y) + (x | y) <=> x + y }
         rule and_absorb<W>(x: W, y: W) { x & (x | y) => x }
         rule udiv_self<W>(x: W) { udiv(x, x) => 1 }",
    );
    let checks = check_program(&p, &CheckConfig::default());
    let ledger = Ledger::from_checks(&checks);
    let text = ledger.render();
    assert_eq!(Ledger::parse(&text).unwrap(), ledger);
    assert!(ledger.vouches_for("t::and_absorb", p.rules()[1].id));
    assert!(
        !ledger.vouches_for("t::udiv_self", p.rules()[2].id),
        "unsound rules are not entered"
    );
    let edited = text.replace("and_absorb", "and_absorbed");
    assert!(!ledger.diff(&Ledger::parse(&edited).unwrap()).is_empty());
}

#[test]
fn diagnostics_render_with_positions() {
    let src = "bitwright 1;\ngroup t {\n  rule impure<W>(x: W, y: W) { x & y => x if x == y }\n}\n";
    let e = RuleProgram::compile(src).unwrap_err();
    let text = e.render("rules.bwr", src);
    assert!(text.contains("error[BW0105]"), "{text}");
    assert!(text.contains("rules.bwr:3:"), "{text}");
    assert!(text.contains('^'), "{text}");
}

#[test]
fn unreachable_patterns_are_flagged() {
    let flagged = |body: &str| {
        program(body)
            .diagnostics()
            .iter()
            .any(|d| d.code == "BW0402")
    };
    for body in [
        "rule sub_const<W>(x: W, c: const W) { (x - c) + c => x }",
        "rule add_zero<W>(x: W) { x + 0 => x }",
        "rule not_not<W>(x: W) { ~~x => x }",
        "rule xor_self<W>(x: W, y: W) where W > 1 { (x ^ x) + y => y }",
    ] {
        assert!(flagged(body), "{body}");
    }
    for body in [
        "rule and_absorb<W>(x: W, y: W) { x & (x | y) => x }",
        "rule mul_pow2<W>(x: W, c: const W) { x * c => x << k if is_pow2(c) let k: W = ctz(c) }",
        "rule ugt_form<W>(x: W, y: W) { (x >u y) & (x == y) => false }",
        "rule const_left<W>(x: W, c: const W) { (c + x) + c => x + (c + c) }",
        "rule sext_from_sign_word<W, U>(a: W) where W < U, U <= 2 * W { \
            zext<U>(a) | (zext<U>(a >>s (W - 1)) << W) => sext<U>(a) }",
    ] {
        assert!(!flagged(body), "{body}");
    }
}

// ----- the built-in corpus ----------------------------------------------------------------------

const CORE: &str = crate::rules::corpus::CORE;
const CORE_LEDGER: &str = crate::rules::corpus::CORE_LEDGER;

fn core() -> RuleProgram {
    RuleProgram::compile(CORE).unwrap_or_else(|e| panic!("{}", e.render("core.bwr", CORE)))
}

#[test]
fn corpus_compiles_cleanly() {
    let p = core();
    let loud: Vec<_> = p
        .diagnostics()
        .iter()
        .filter(|d| d.level >= crate::rules::Level::Warning || d.code == "BW0407")
        .map(|d| d.render("core.bwr", CORE))
        .collect();
    assert!(loud.is_empty(), "{}", loud.join("\n"));
}

#[test]
fn corpus_is_sound() {
    let p = core();
    for c in check_program(&p, &CheckConfig::default()) {
        assert!(c.is_sound(), "{}: {:?} ({})", c.name, c.verdict, c.evidence);
        assert!(
            c.evidence.guard_true_cases() > 0,
            "{}: the guard never held",
            c.name
        );
    }
}

#[test]
fn corpus_examples_fire() {
    let p = core();
    for rule in p.rules() {
        for (input, output) in &rule.examples {
            let mut cx = crate::Context::new();
            let o = crate::ParseOptions::width(crate::Width::W8);
            let e = cx
                .parse(input, &o)
                .unwrap_or_else(|err| panic!("{}: {input}: {err}", rule.name));
            let root = cx.id(e).unwrap();
            let got = crate::rules::apply::try_apply(&mut cx, rule, root)
                .unwrap_or_else(|| panic!("{}: does not fire on `{input}`", rule.name));
            let want = cx
                .parse(output, &o)
                .unwrap_or_else(|err| panic!("{}: {output}: {err}", rule.name));
            assert_eq!(
                cx.handle(got),
                want,
                "{}: `{input}` gave `{}`, expected `{output}`",
                rule.name,
                cx.display(cx.handle(got))
            );
        }
    }
}

#[test]
fn corpus_ledger_is_fresh() {
    let p = core();
    let ledger = Ledger::from_checks(&check_program(&p, &CheckConfig::default()));
    let checked_in = Ledger::parse(CORE_LEDGER).unwrap();
    let diff = ledger.diff(&checked_in);
    assert!(
        diff.is_empty(),
        "the proof ledger is stale; run `cargo test -p bitwright -- --ignored write_corpus_ledger`:\n{}",
        diff.join("\n")
    );
}

/// Regenerates `core.bwr.proof` (run explicitly with `--ignored`).
#[test]
#[ignore = "writes the checked-in ledger"]
fn write_corpus_ledger() {
    let p = core();
    let ledger = Ledger::from_checks(&check_program(&p, &CheckConfig::default()));
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/rules/corpus/core.bwr.proof"
    );
    std::fs::write(path, ledger.render()).unwrap();
    let e = eqsat_corpus();
    let ledger = Ledger::from_checks(&check_program(&e, &CheckConfig::default()));
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/rules/corpus/eqsat.bwr.proof"
    );
    std::fs::write(path, ledger.render()).unwrap();
}

/// End-to-end soundness of rule application (matcher, fact guards, instantiation): instances
/// of every corpus pattern, with parameters replaced by random subexpressions, are rewritten
/// with `try_apply` and the result is compared with the input exhaustively over its symbols.
/// The checker proves each rule's semantics; this proves the engine-side reading of it.
#[test]
fn corpus_application_is_sound() {
    application_is_sound(&core());
}

/// Sound rules that exercise the guard and template features the corpus does not: `nonzero`,
/// a `proves` whose two operands can be one node, a swapped comparison, `select`, `sext`,
/// `zext` and `extract` in templates, and width literals.
const APPLY_FIXTURE: &str = r#"
bitwright 1;
group fixture {
    rule udiv_self_nz<W>(x: W) { udiv(x, x) => 1 if nonzero(x) }
    rule urem_lt<W>(a: W, b: W, c: W) { urem(a, b) <u c => true if proves(a <u c) }
    rule uge_spelled<W>(a: W, b: W) { (b <u a) | (a == b) => a >=u b }
    rule and_sext_bool<W>(c: 1, x: W) where 1 < W { x & sext<W>(c) => select(c, x, 0) }
    rule sext_masked<W, U>(a: W) where W < U { sext<U>(a) & lowmask(W) => zext<U>(a) }
    rule trunc_high<W, N>(x: W) where N < W { trunc<N>(x >>s (W - N)) => extract<W - N, N>(x) }
}
"#;

#[test]
fn fixture_application_is_sound() {
    let p = RuleProgram::compile(APPLY_FIXTURE)
        .unwrap_or_else(|e| panic!("{}", e.render("fixture.bwr", APPLY_FIXTURE)));
    let loud: Vec<_> = p
        .diagnostics()
        .iter()
        .filter(|d| d.level >= crate::rules::Level::Warning)
        .collect();
    assert!(loud.is_empty(), "{loud:?}");
    for c in check_program(&p, &CheckConfig::default()) {
        assert!(c.is_sound(), "{}: {:?} ({})", c.name, c.verdict, c.evidence);
    }
    application_is_sound(&p);
}

fn application_is_sound(p: &RuleProgram) {
    use crate::expr::FnEnv;
    use crate::rules::ParamKind;
    use crate::testutil::{Gen, Rng};

    let mut g = Gen {
        rng: Rng(0xa991_7e5d),
        max_w: 5,
        vars: Vec::new(),
    };
    for rule in p.rules() {
        let mut fired = 0u32;
        let assignments: Vec<Vec<u16>> = crate::rules::width_assignments(rule)
            .into_iter()
            .filter(|ws| ws.iter().all(|&w| w <= 5))
            .filter(|ws| crate::rules::eval::well_formed(rule, rule.lhs, ws, true).is_ok())
            .collect();
        for round in 0..600 {
            let ws = &assignments[round % assignments.len()];
            let mut cx = crate::Context::new();
            let pw: Vec<u16> = rule
                .params
                .iter()
                .map(|q| q.width.eval(ws) as u16)
                .collect();
            let consts: Vec<BitVec> = pw
                .iter()
                .map(|&w| {
                    let w16 = Width::new(w).unwrap();
                    match g.rng.below(5) {
                        0 => {
                            let k = BitVec::wrapping_from_u64(w16, g.rng.below(u64::from(w)));
                            BitVec::apply_bin(crate::BinOp::Shl, &BitVec::one(w16), &k).unwrap()
                        }
                        1 => BitVec::wrapping_from_u64(
                            w16,
                            (1u64 << g.rng.below(u64::from(w) + 1)) - 1,
                        ),
                        _ => g.constant(w),
                    }
                })
                .collect();
            let Some(root) = crate::rules::matcher::build_pattern(&mut cx, rule, ws, &consts)
            else {
                continue;
            };
            // Replace the non-constant parameters' symbols by random subexpressions.
            let mut map = Vec::new();
            for (q, &w) in rule.params.iter().zip(&pw) {
                if q.kind == ParamKind::Const {
                    continue;
                }
                let from = cx
                    .symbol(format!("${}", q.name).as_str(), Width::new(w).unwrap())
                    .unwrap();
                let depth = g.rng.below(3) as u32;
                let (to, _) = g.expr(&mut cx, w, depth);
                map.push((from, to));
            }
            let input = cx.handle(root);
            let input = cx.substitute(&[input], &map).unwrap()[0];
            let input_id = cx.id(input).unwrap();
            let Some(out) = crate::rules::apply::try_apply(&mut cx, rule, input_id) else {
                continue;
            };
            fired += 1;
            // Every real application decreases the ground order (termination, including
            // the effect of construction canonicalization on the template).
            if rule.decreasing {
                assert!(
                    crate::rules::order::ground_greater(&cx, input_id, out) == Some(true),
                    "{}: `{}` rewrote to `{}`, which is not smaller",
                    rule.name,
                    cx.display(input),
                    cx.display(cx.handle(out))
                );
            }
            let out = cx.handle(out);
            let syms = cx.symbols_in(&[input, out]).unwrap();
            let bits: u32 = syms
                .iter()
                .map(|&s| u32::from(cx.symbol_width(s).unwrap().bits()))
                .sum();
            let cases: u64 = if bits <= 12 { 1 << bits } else { 4096 };
            for case in 0..cases {
                let mut vals = Vec::new();
                let mut rest = case;
                for &s in &syms {
                    let w = cx.symbol_width(s).unwrap();
                    let v = if bits <= 12 {
                        let v = rest & ((1u64 << w.bits()) - 1);
                        rest >>= w.bits();
                        v
                    } else {
                        g.rng.next()
                    };
                    vals.push((
                        cx.symbol_key(s).unwrap().clone(),
                        BitVec::wrapping_from_u64(w, v),
                    ));
                }
                let env = FnEnv(|k: &crate::SymbolKey, _| {
                    vals.iter().find(|(kk, _)| kk == k).map(|(_, v)| *v)
                });
                let r = cx.eval(&[input, out], &env).unwrap();
                assert_eq!(
                    r[0],
                    r[1],
                    "{}: `{}` rewrote to `{}`, which differs at {vals:?}",
                    rule.name,
                    cx.display(input),
                    cx.display(out)
                );
            }
        }
        assert!(fired > 0, "{}: never fired on a random instance", rule.name);
    }
}

// ----- regressions from the M3 review ----------------------------------------------------------

/// Parses `src` with 4-bit default symbols and applies `rule` of `program` at the root.
fn apply_to(
    program: &RuleProgram,
    rule: &str,
    src: &str,
    w: u16,
) -> (crate::Context, Expr, Option<Expr>) {
    let rule = program
        .rules()
        .iter()
        .find(|r| r.name.ends_with(rule))
        .unwrap();
    let mut cx = crate::Context::new();
    let e = cx
        .parse(src, &crate::ParseOptions::width(Width::new(w).unwrap()))
        .unwrap();
    let id = cx.id(e).unwrap();
    let out = crate::rules::apply::try_apply(&mut cx, rule, id).map(|o| cx.handle(o));
    (cx, e, out)
}

use crate::Expr;

#[test]
fn where_constraints_hold_at_application() {
    // U = 16 > 2W: the corpus rule does not apply (it would be wrong there).
    let (_, _, out) = apply_to(
        &core(),
        "sext_from_sign_word",
        "zext<16>(p) | (zext<16>(p >>s 3) << 4)",
        4,
    );
    assert_eq!(out, None);
    // U = 8 = 2W: it does.
    let (mut cx, _, out) = apply_to(
        &core(),
        "sext_from_sign_word",
        "zext<8>(p) | (zext<8>(p >>s 3) << 4)",
        4,
    );
    let want = cx
        .parse(
            "sext<8>(p)",
            &crate::ParseOptions::width(Width::new(4).unwrap()),
        )
        .unwrap();
    assert_eq!(out, Some(want));
}

#[test]
fn closed_subterms_only_match_where_checked() {
    // `k` is 1 for W > 4 and 0 at W = 4, where `zext<4>(1:4)` is not a node the builder makes,
    // so the checker skips W = 4; the matcher must skip it too.
    let p = program(
        "rule z<W>(x: W, y: W) where W >= 4 { (x & zext<W>(1:4)) ^ (y & zext<W>(1:4)) => (x ^ y) & k \
         let k: W = zext<W>(W:16 != 4:16) }",
    );
    let c = check_rule(&p.rules()[0], &CheckConfig::default());
    assert!(c.is_sound(), "{:?}", c.verdict);
    let (_, _, out) = apply_to(&p, "z", "(p & 1) ^ (q & 1)", 4);
    assert_eq!(out, None, "rewrote at an unchecked width");
    let (mut cx, _, out) = apply_to(&p, "z", "(p & 1) ^ (q & 1)", 8);
    let want = cx
        .parse(
            "(p ^ q) & 1",
            &crate::ParseOptions::width(Width::new(8).unwrap()),
        )
        .unwrap();
    assert_eq!(out, Some(want));
}

#[test]
fn sound_needs_the_guard_to_hold_in_both_tiers() {
    // The guard never holds at the exhaustive widths: not Sound.
    let c = check_one(
        "rule bad<W>(x: W, y: W) where W >= 3 { x ^ y => x if (W:16 >=u 20:16) && proves(y == k) let k: W = (ones >>u 3) - W }",
    );
    assert!(!c.is_sound(), "{:?} {}", c.verdict, c.evidence);
    // A rule true at small widths and false at a wide one whose guard needs a specific value:
    // steered sampling finds the counterexample.
    // (`k` is 0 up to W = 16, then an unremarkable value no unsteered sample hits.)
    let c = check_one(
        "rule bad2<W>(x: W, y: W) where W >= 6 { x ^ y => x if proves(y == k) let k: W = ((ones >>u 16) * 37) << 1 }",
    );
    assert!(
        matches!(c.verdict, Verdict::Unsound(_)),
        "{:?} {}",
        c.verdict,
        c.evidence
    );
    // Sound everywhere, but the guard only holds above the exhaustive widths: inconclusive.
    let c = check_one("rule wide<W>(x: W) { x & x => x if W:16 >=u 20:16 }");
    assert_eq!(
        c.verdict,
        Verdict::Inconclusive("the guard never held in the exhaustive tier")
    );
    // ... and the converse: a guard that only holds at small widths says nothing wide.
    let c = check_one("rule narrow<W>(x: W) { x & x => x if W:16 <=u 3:16 }");
    assert_eq!(
        c.verdict,
        Verdict::Inconclusive("the guard never held in the sampled tier")
    );
    // A guarded rule whose admitted widths are all small is complete without sampling.
    let c = check_one("rule small<W>(x: W) where W <= 4 { x & x => x }");
    assert!(
        c.is_sound() && c.evidence.complete,
        "{:?} {}",
        c.verdict,
        c.evidence
    );
}

#[test]
fn ledger_vouches_only_for_sound_rules() {
    let p = program(
        "rule bad<W>(x: W, y: W) where W >= 20 { x ^ y => x if proves(y == k) let k: W = (ones >>u 3) - W }",
    );
    let checks = check_program(&p, &CheckConfig::default());
    assert!(!checks[0].is_sound());
    let l = Ledger::from_checks(&checks);
    assert!(!l.vouches_for(&checks[0].name, checks[0].id));
    assert!(Ledger::parse("# bitwright proof ledger v1. Generated; do not edit.\n").is_err());
}

#[test]
fn rule_ids_see_leaf_widths() {
    let a = program("rule r<W>(x: W, y: W) { x & y => x if proves(y == 0) || (200:16 <s 0:16) }");
    let b = program("rule r<W>(x: W, y: W) { x & y => x if proves(y == 0) || (200:8 <s 0:8) }");
    assert_ne!(a.rules()[0].id, b.rules()[0].id);
    // A width variable the pattern cannot bind is an error, not a rule that never fires.
    assert_eq!(
        codes(&compile_err(
            "rule and_absorb_or<W, U>(x: W, y: W) { x & (x | y) => x }"
        )),
        ["BW0102"]
    );
}

#[test]
fn looping_rules_are_rejected() {
    for body in [
        // A closed subterm is one constant, not three nodes.
        "rule a<W>(x: W) { x ^ (1 + 1 - 1) => ~(~x ^ 1) }",
        // Extract offsets are compared structurally, never as strings.
        "rule b<W>(x: W) where W == 16 { extract<8, 1>(rotl(x, 6:W)) => extract<20 - W, 1>(rotl(x, 2:W)) }",
        "rule c<W>(x: W) where W == 16 { extract<4, 1>(rotl(x, 2:W)) => extract<24 - W, 1>(rotl(x, 6:W)) }",
        // Commutative operands are a multiset: reordering is not a decrease.
        "rule d<W>(x: W, y: W) { (x ^ y) & (x | y) => (x | y) & (x ^ y) }",
        // A comparison is compared in its stored form.
        "rule e<W>(x: W, y: W) { y >u x => x <u y }",
    ] {
        assert!(codes(&compile_err(body)).contains(&"BW0302"), "{body}");
    }
}

#[test]
fn hostile_rule_text_is_rejected_not_crashed() {
    let deep_unary = format!("rule r<W>(x: W) {{ {}x => x }}", "~".repeat(100_000));
    assert!(codes(&compile_err(&deep_unary)).contains(&"BW0100"));
    let deep_width = format!(
        "rule r<W>(x: W) where W < {}W{} {{ x & x => x }}",
        "(".repeat(200_000),
        ")".repeat(200_000)
    );
    assert!(codes(&compile_err(&deep_width)).contains(&"BW0100"));
    let huge = "rule r<W>(x: W) where W < 1048576 * 1048576 * 1048576 * 1048576 { x & x => x }";
    assert!(codes(&compile_err(huge)).contains(&"BW0102"));
    // Junk yields a bounded number of diagnostics.
    let junk = format!("bitwright 1;\n{}", "junk ".repeat(100_000));
    let e = RuleProgram::compile(&junk).unwrap_err();
    assert!(e.diagnostics.len() <= 2, "{}", e.diagnostics.len());
    let many = format!(
        "bitwright 1;\ngroup g {{\n{}}}\n",
        "rule r<W>(x: W) { x => }\n".repeat(1000)
    );
    let e = RuleProgram::compile(&many).unwrap_err();
    assert!(e.diagnostics.len() <= 102, "{}", e.diagnostics.len());
    // Attributes before a group are an error, not silently dropped.
    let e = RuleProgram::compile("bitwright 1;\n#[allow(BW0302)]\ngroup g {}\n").unwrap_err();
    assert!(codes(&e).contains(&"BW0002"));
}

#[test]
fn validation_work_is_bounded() {
    let src = "bitwright 1;\ngroup g {\nrule r<W, U>(x: W, y: U) { concat(x ^ x, y) => concat(0, y) }\n}\n";
    let mut opts = crate::rules::CompileOptions::default();
    opts.limits.max_work = 1000;
    let e = RuleProgram::compile_with(src, &opts).unwrap_err();
    assert!(codes(&e).contains(&"BW0100"));
}

#[test]
fn guards_cannot_hide_facts_or_loop_lets() {
    for (body, code) in [
        (
            "rule r<W>(x: W, c: const W) { x & c => x if nonzero(c) != is_pow2(1:W) }",
            "BW0101",
        ),
        (
            "rule r<W>(x: W, c: const W) { x & c => x & k let k: W = k }",
            "BW0105",
        ),
        (
            "rule r<W>(x: W, c: const W) { x & c => x & a let a: W = b let b: W = a }",
            "BW0105",
        ),
    ] {
        assert!(codes(&compile_err(body)).contains(&code), "{body}");
    }
}

#[test]
fn widths_determined_only_by_a_sum_still_match() {
    let p = program(
        "rule cc<W, U>(x: W, y: U, z: W, t: U) { concat(x ^ z, y ^ t) => concat(x, y) ^ concat(z, t) }",
    );
    assert!(
        !p.diagnostics().iter().any(|d| d.code == "BW0402"),
        "{:?}",
        p.diagnostics()
    );
    let (_, _, out) = apply_to(&p, "cc", "concat(p ^ q, r:3 ^ s:3)", 4);
    assert!(out.is_some());
}

#[test]
fn the_matcher_is_bounded() {
    // `a0 & (a1 & ... (a59 & c))` against an And DAG with two viable operand orders per level
    // and no constant at the bottom: exponential without the step budget.
    let d = 60;
    let params: Vec<String> = (0..d).map(|i| format!("a{i}: W")).collect();
    let mut pat = String::from("c");
    for i in (0..d).rev() {
        pat = format!("a{i} & ({pat})");
    }
    let body = format!(
        "rule deep<W>({}, c: const W) {{ {pat} => 0 if zero_bits(a0, ones) }}",
        params.join(", ")
    );
    let p = RuleProgram::compile(&format!(
        "bitwright 1;\ngroup t {{\n#[allow(BW0402)]\n{body}\n}}\n"
    ))
    .unwrap();
    let rule = &p.rules()[0];
    let mut cx = crate::Context::new();
    let w = Width::new(8).unwrap();
    let mut level: Vec<u32> = (0..3)
        .map(|i| {
            let e = cx.symbol(format!("s{i}").as_str(), w).unwrap();
            cx.id(e).unwrap()
        })
        .collect();
    for _ in 0..d {
        let pairs = [(0, 1), (1, 2), (2, 0)];
        level = pairs
            .iter()
            .map(|&(i, j)| {
                let (a, b) = (cx.handle(level[i]), cx.handle(level[j]));
                let e = cx.bin(crate::BinOp::And, a, b).unwrap();
                cx.id(e).unwrap()
            })
            .collect();
    }
    let start = std::time::Instant::now();
    assert!(crate::rules::matcher::match_rule(&cx, rule, level[0]).is_none());
    assert!(start.elapsed() < std::time::Duration::from_secs(5));
}

#[test]
fn wide_exhaustive_configs_do_not_panic() {
    let p = program("rule r<W>(x: W, y: W) { x & (x | y) => x }");
    let cfg = CheckConfig {
        max_exhaustive_bits: 64,
        max_exhaustive_width: 3,
        ..CheckConfig::default()
    };
    assert!(check_rule(&p.rules()[0], &cfg).is_sound());
}

// ----- the equality-saturation identities -------------------------------------------------------

fn eqsat_corpus() -> RuleProgram {
    let src = crate::rules::corpus::EQSAT;
    RuleProgram::compile(src).unwrap_or_else(|e| panic!("{}", e.render("eqsat.bwr", src)))
}

#[test]
fn eqsat_corpus_is_sound_clean_and_recorded() {
    let p = eqsat_corpus();
    let loud: Vec<_> = p
        .diagnostics()
        .iter()
        .filter(|d| d.level >= crate::rules::Level::Warning || d.code == "BW0407")
        .map(|d| d.render("eqsat.bwr", crate::rules::corpus::EQSAT))
        .collect();
    assert!(loud.is_empty(), "{}", loud.join("\n"));
    let checks = check_program(&p, &CheckConfig::default());
    for c in &checks {
        assert!(c.is_sound(), "{}: {:?} ({})", c.name, c.verdict, c.evidence);
    }
    let ledger = Ledger::from_checks(&checks);
    let checked_in = Ledger::parse(crate::rules::corpus::EQSAT_LEDGER).unwrap();
    let diff = ledger.diff(&checked_in);
    assert!(
        diff.is_empty(),
        "stale; run `cargo test -p bitwright -- --ignored write_corpus_ledger`:\n{}",
        diff.join("\n")
    );
    // The examples hold (the authored direction, through rule application).
    for rule in p.rules() {
        for (input, output) in &rule.examples {
            let mut cx = crate::Context::new();
            let o = crate::ParseOptions::width(crate::Width::W8);
            let e = cx.parse(input, &o).unwrap();
            let want = cx.parse(output, &o).unwrap();
            let root = cx.id(e).unwrap();
            let got = crate::rules::apply::try_apply(&mut cx, rule, root)
                .unwrap_or_else(|| panic!("{}: does not fire on `{input}`", rule.name));
            assert_eq!(cx.handle(got), want, "{}: `{input}`", rule.name);
        }
    }
}

#[test]
fn examples_are_checked() {
    let src = "bitwright 1;
group g {
    #[example(\"p & (p | q)\" => \"p\")]
    rule absorb<W>(x: W, y: W) { x & (x | y) => x }

    #[example(\"p & (q | r)\" => \"p\")]
    #[example(\"p & (p | q)\" => \"q\")]
    #[example(\"p &\" => \"p\")]
    #[example(\"p:16 & (p | q)\" => \"p:16\")]
    rule absorb2<W>(x: W, y: W) { x & (x | y) => x }

    #[example(\"q & 0xf0\" => \"q\")]
    rule mask<W>(x: W, c: const W) { x & c => x if zero_bits(x, ~c) }
}";
    let p = RuleProgram::compile(src).unwrap();
    let checks = check_program(&p, &CheckConfig::default());
    assert!(checks[0].examples.is_empty(), "{:?}", checks[0].examples);
    let f = &checks[1].examples;
    assert_eq!(f.len(), 3, "{f:?}");
    assert!(matches!(&f[0], ExampleFailure::DoesNotFire { input } if input == "p & (q | r)"));
    assert!(matches!(&f[1], ExampleFailure::Differs { got, .. } if got == "p"));
    assert!(matches!(&f[2], ExampleFailure::Parse { text, .. } if text == "p &"));
    // A guard the example's input cannot prove: the rule does not fire.
    assert!(matches!(
        &checks[2].examples[..],
        [ExampleFailure::DoesNotFire { .. }]
    ));
    // Every built-in example holds.
    for r in core().rules().iter().chain(eqsat_corpus().rules()) {
        assert!(
            check_examples(r).is_empty(),
            "{}: {:?}",
            r.name,
            check_examples(r)
        );
    }
}
