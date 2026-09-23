//! Round trips: `display` then `parse` gives back the same node (in the same context) or the
//! same text (in a fresh one), for random DAGs with shared subterms, every operator, wide
//! constants, casts at limb boundaries and extension calls (`@name[k](…)`); a truncated print
//! never parses into a different expression; the derived constructors' names parse to the
//! builder's nodes. With feature `smtlib`: export then import preserves meaning up to 512 bits,
//! and (when z3 is on `PATH`) z3 proves simplification results equivalent to their inputs.
//!
//! The library's unit tests round-trip random trees up to 8 bits; the SMT-LIB ones up to 130.

mod common;

use bitwright::{BinOp, CmpOpExt, Context, ContextConfig, Expr, ParseOptions, PrintOptions, UnOp};
use common::{
    Dag, GenConfig, Rng, SMOKE_WIDTHS, Size, WIDTHS, boundary_values, ext_context, registry, w,
};

#[cfg(feature = "smtlib")]
use common::Canonical;

fn unbounded() -> PrintOptions {
    PrintOptions::default()
        .with_max_nodes(usize::MAX)
        .with_max_chars(usize::MAX)
}

/// A random DAG with a few roots, over small or wide widths, with or without extension calls.
fn random_roots(cx: &mut Context, rng: &mut Rng, size: Size, kind: u64) -> (Dag, Vec<Expr>) {
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    let mut cfg = match kind % 3 {
        0 => GenConfig::small(rng, 8, 4),
        _ => GenConfig::wide(rng, &widths, 3),
    };
    cfg.ext = kind % 3 == 2;
    let rws = cfg.widths.clone();
    let mut dag = Dag::new(cx, cfg);
    let roots = (0..3)
        .map(|_| {
            let rw = rng.pick(&rws);
            let i = dag.random(cx, rng, rw);
            dag.expr(i)
        })
        .collect();
    (dag, roots)
}

fn text_round_trip(size: Size) {
    let reg = registry();
    let mut truncated = 0;
    for seed in 0..size.pick(60, 60_000u64) {
        let mut rng = Rng(0x7e7_0000 + seed);
        let mut cx = ext_context(&reg);
        let (_, roots) = random_roots(&mut cx, &mut rng, size, seed);
        for &e in &roots {
            let what = format!("seed {:#x}", 0x7e7_0000 + seed);
            // The same context: the same node.
            let text = cx.display_with(e, unbounded()).to_string();
            let back = cx
                .parse(
                    &text,
                    &ParseOptions::default().with_existing_symbols_only(true),
                )
                .unwrap_or_else(|err| panic!("{what}: `{text}` does not parse: {err}"));
            assert_eq!(back, e, "{what}: `{text}` parsed to `{}`", cx.display(back));
            // Without `let`s the text is a tree, possibly much longer; still the same node.
            if cx.tree_size(e).unwrap() < 2_000 {
                let flat = cx.display_with(e, unbounded().with_lets(false)).to_string();
                let back = cx.parse(&flat, &ParseOptions::default()).unwrap();
                assert_eq!(back, e, "{what}: `{flat}` (no lets)");
            }
            // A fresh context with the same registry: the same text.
            let typed = cx
                .display_with(e, unbounded().with_symbol_widths(true))
                .to_string();
            let mut other = ext_context(&reg);
            let back = other
                .parse(&typed, &ParseOptions::default())
                .unwrap_or_else(|err| panic!("{what}: `{typed}` does not parse afresh: {err}"));
            assert_eq!(
                other.display_with(back, unbounded()).to_string(),
                text,
                "{what}: `{typed}` in a fresh context"
            );
            // A truncated print either parses to the node or is refused.
            let short = cx
                .display_with(
                    e,
                    PrintOptions::default().with_max_nodes(3).with_max_chars(60),
                )
                .to_string();
            if short.contains('…') {
                truncated += 1;
                if let Ok(b) = cx.parse(
                    &short,
                    &ParseOptions::default().with_existing_symbols_only(true),
                ) {
                    panic!("{what}: truncated `{short}` parsed to `{}`", cx.display(b));
                }
            }
        }
    }
    assert!(truncated > 0);
}

#[test]
fn display_then_parse_is_the_same_node_smoke() {
    text_round_trip(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn display_then_parse_is_the_same_node_heavy() {
    text_round_trip(Size::Heavy);
}

/// Every operator, comparison and cast over symbols and boundary constants, at every width.
fn every_operator(size: Size) {
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    for n in widths {
        let width = w(n);
        let mut cx = Context::new();
        let x = cx.symbol("x", width).unwrap();
        let y = cx.symbol("y", width).unwrap();
        let p = cx.symbol("p", bitwright::Width::W1).unwrap();
        let mut operands = vec![x, y];
        for v in boundary_values(width).iter().take(size.pick(4, 40)) {
            operands.push(cx.constant(v).unwrap());
        }
        let mut exprs = Vec::new();
        for &a in &operands {
            for op in UnOp::ALL {
                if let Ok(e) = cx.un(op, a) {
                    exprs.push(e);
                }
            }
            for &b in &[x, operands[operands.len() - 1]] {
                for op in BinOp::ALL {
                    exprs.push(cx.bin(op, a, b).unwrap());
                    exprs.push(cx.bin(op, b, a).unwrap());
                }
                for op in CmpOpExt::ALL {
                    exprs.push(cx.cmp(op, a, b).unwrap());
                }
                exprs.push(cx.select(p, a, b).unwrap());
            }
            for to in [n + 1, n + 64, 512] {
                if to > n && to <= 512 {
                    exprs.push(cx.zext(a, w(to)).unwrap());
                    exprs.push(cx.sext(a, w(to)).unwrap());
                }
            }
            for (lo, len) in [(0, 1), (n - 1, 1), (0, n), (n / 2, n - n / 2)] {
                exprs.push(cx.extract(a, lo, w(len)).unwrap());
            }
            if n <= 256 {
                exprs.push(cx.concat(a, y).unwrap());
            }
        }
        for e in exprs {
            let text = cx.display_with(e, unbounded()).to_string();
            let back = cx.parse(&text, &ParseOptions::default());
            assert_eq!(back, Ok(e), "{n} bits: `{text}`");
        }
    }
}

#[test]
fn every_operator_prints_and_parses_smoke() {
    every_operator(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn every_operator_prints_and_parses_heavy() {
    every_operator(Size::Heavy);
}

/// The text syntax spells the derived constructors by name; each parses to the node the builder
/// makes (at every width, where the widening products accept it).
fn derived_names(size: Size) {
    type Build = fn(&mut Context, Expr, Expr) -> Result<Expr, bitwright::Error>;
    let derived: [(&str, Build); 16] = [
        ("umin", Context::umin),
        ("umax", Context::umax),
        ("smin", Context::smin),
        ("smax", Context::smax),
        ("andn", Context::andn),
        ("orn", Context::orn),
        ("xnor", Context::xnor),
        ("abs", |cx, a, _| cx.abs(a)),
        ("add_carry", Context::add_carry),
        ("sub_borrow", Context::sub_borrow),
        ("sadd_overflow", Context::sadd_overflow),
        ("ssub_overflow", Context::ssub_overflow),
        ("add_sat_u", Context::add_sat_u),
        ("add_sat_s", Context::add_sat_s),
        ("sub_sat_u", Context::sub_sat_u),
        ("sub_sat_s", Context::sub_sat_s),
    ];
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), (1..=512).collect());
    for n in widths {
        let mut cx = Context::new();
        let x = cx.symbol("x", w(n)).unwrap();
        let y = cx.symbol("y", w(n)).unwrap();
        for (name, build) in derived {
            let want = build(&mut cx, x, y).unwrap();
            let src = if name == "abs" {
                "abs(x)".to_string()
            } else {
                format!("{name}(x, y)")
            };
            assert_eq!(
                cx.parse(&src, &ParseOptions::default()),
                Ok(want),
                "{src} at {n} bits"
            );
        }
    }
}

#[test]
fn derived_constructor_names_parse_to_the_builders_node_smoke() {
    derived_names(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn derived_constructor_names_parse_to_the_builders_node_heavy() {
    derived_names(Size::Heavy);
}

/// Two contexts with different hash seeds and different unrelated nodes built first print the
/// same DAG identically (canonical order is context-independent).
fn seeds_do_not_change_text(size: Size) {
    let reg = registry();
    for seed in 0..size.pick(30, 20_000u64) {
        let build = |hash_seed: u64, junk: u64| {
            let mut cx = Context::with_registry(
                ContextConfig::default().with_hash_seed(hash_seed),
                reg.clone(),
            );
            // Unrelated nodes first, over other symbols, so arena positions differ.
            let mut jr = Rng(junk);
            let j = cx.symbol("junk", bitwright::Width::W32).unwrap();
            let mut acc = j;
            for _ in 0..jr.below(40) {
                let c = cx.constant(&jr.bitvec(bitwright::Width::W32)).unwrap();
                acc = cx.bin(jr.pick(&BinOp::ALL), acc, c).unwrap();
            }
            let mut rng = Rng(0x5ee_0000 + seed);
            let (_, roots) = random_roots(&mut cx, &mut rng, size, seed);
            roots
                .iter()
                .map(|&e| cx.display_with(e, unbounded()).to_string())
                .collect::<Vec<_>>()
        };
        let a = build(0, 1);
        let b = build(0xdead_beef_0000 + seed, 2 + seed);
        assert_eq!(a, b, "seed {seed:#x}");
    }
}

#[test]
fn text_is_independent_of_hash_seed_and_history_smoke() {
    seeds_do_not_change_text(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn text_is_independent_of_hash_seed_and_history_heavy() {
    seeds_do_not_change_text(Size::Heavy);
}

// ----- SMT-LIB --------------------------------------------------------------------------------

/// Export then import in a fresh context computes the same function (by the reference over
/// both canonical DAGs), for every root of random DAGs up to 512 bits.
#[cfg(feature = "smtlib")]
fn smt_round_trip(size: Size) {
    use bitwright::smtlib::{export, import};
    let rounds = size.pick(30, 20_000u64);
    for seed in 0..rounds {
        let mut rng = Rng(0x5a7_0000 + seed);
        let mut cx = Context::new();
        // No extension calls: those export as uninterpreted functions, which import refuses.
        let (dag, roots) = random_roots(&mut cx, &mut rng, size, seed % 2);
        let what = format!("seed {:#x}", 0x5a7_0000 + seed);
        let script = export(&mut cx, &roots).unwrap();
        let mut other = Context::new();
        let imported = import(&mut other, &script)
            .unwrap_or_else(|err| panic!("{what}: import failed: {err}\n{script}"));
        let back: Vec<Expr> = (0..roots.len())
            .map(|k| imported.definition(&format!("root{k}")).unwrap())
            .collect();
        let before = Canonical::new(&mut cx, &roots);
        let after = Canonical::new(&mut other, &back);
        for _ in 0..size.pick(4, 12) {
            let env = dag.boundary_env(&mut rng);
            let b = dag.binding(&env);
            assert_eq!(
                before.eval(&b, &[]),
                after.eval(&b, &[]),
                "{what}: at {}\n{script}",
                dag.show_env(&env)
            );
        }
    }
}

/// A high product wider than 256 bits cannot be exported through a 2W-bit product (import, like
/// every bitwright value, stops at 512 bits); its half-word expansion imports back to the same
/// function, at odd and even widths, on boundary and random operands.
#[cfg(feature = "smtlib")]
#[test]
fn smtlib_high_products_above_256_bits_import_back() {
    use bitwright::smtlib::{export, import};
    use bitwright::{BitVec, SymbolKey, Width};
    let mut rng = Rng(0x3a1_0000);
    for bits in [257u16, 258, 301, 384, 511, 512] {
        let w = Width::new(bits).unwrap();
        let mut values = boundary_values(w);
        values.truncate(14);
        for _ in 0..6 {
            let limbs: Vec<u64> = (0..usize::from(bits).div_ceil(64))
                .map(|_| rng.next())
                .collect();
            values.push(BitVec::wrapping_from_limbs(w, &limbs));
        }
        for op in [BinOp::UMulHi, BinOp::SMulHi] {
            let mut cx = Context::new();
            let (x, y) = (cx.symbol("x", w).unwrap(), cx.symbol("y", w).unwrap());
            let e = cx.bin(op, x, y).unwrap();
            let script = export(&mut cx, &[e]).unwrap();
            let mut other = Context::new();
            let imported = import(&mut other, &script)
                .unwrap_or_else(|err| panic!("{op:?} at {bits}: import failed: {err}"));
            let back = imported.definition("root0").unwrap();
            let key = |name: &str| {
                let (_, s) = imported.symbols.iter().find(|(n, _)| n == name).unwrap();
                let id = other.symbol_id(*s).unwrap().unwrap();
                other.symbol_key(id).unwrap().clone()
            };
            let (kx, ky) = (key("x"), key("y"));
            for a in &values {
                for b in values.iter().step_by(3) {
                    let want = BitVec::apply_bin(op, a, b).unwrap();
                    let env: [(SymbolKey, BitVec); 2] = [(kx.clone(), *a), (ky.clone(), *b)];
                    let got = other.eval(&[back], &env[..]).unwrap()[0];
                    assert_eq!(got, want, "{op:?} at {bits} bits: {a:?}, {b:?}");
                }
            }
        }
    }
}

#[cfg(feature = "smtlib")]
#[test]
fn smtlib_export_then_import_keeps_meaning_smoke() {
    smt_round_trip(Size::Smoke);
}

#[cfg(feature = "smtlib")]
#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn smtlib_export_then_import_keeps_meaning_heavy() {
    smt_round_trip(Size::Heavy);
}

/// Runs z3 on a script; `None` if z3 cannot be started.
#[cfg(feature = "smtlib")]
fn z3(script: &str) -> Option<String> {
    use std::io::Write as _;
    use std::process::{Command, Stdio};
    let mut child = Command::new("z3")
        .args(["-in", "-smt2", "-t:5000"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    child.stdin.take()?.write_all(script.as_bytes()).ok()?;
    let out = child.wait_with_output().ok()?;
    Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

/// z3 proves the simplifier's results equivalent to their inputs (`unsat`), up to 512 bits.
/// A timeout or `unknown` is inconclusive and counted; `sat` is a counterexample, unless the
/// query has extension calls (uninterpreted functions, whose models need not be real). Skipped,
/// with a note, when z3 is not on `PATH`.
#[cfg(feature = "smtlib")]
fn z3_simplifications(size: Size) {
    use bitwright::engine::{Engine, Strategy};
    use bitwright::smtlib::equivalence_query;
    if z3("(check-sat)").is_none() {
        eprintln!("z3 is not on PATH; skipped");
        return;
    }
    let deobfuscate = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let (mut proved, mut inconclusive) = (0, 0);
    let mut script = String::new();
    let mut cases = Vec::new();
    let reg = registry();
    for seed in 0..size.pick(6, 600u64) {
        let mut rng = Rng(0x23_0000 + seed);
        let mut cx = ext_context(&reg);
        // Extension calls export as uninterpreted functions: `unsat` still proves.
        let (_, roots) = random_roots(&mut cx, &mut rng, size, seed);
        for e in roots {
            let r = deobfuscate.simplify(&mut cx, e).unwrap();
            if !r.changed {
                continue;
            }
            let q = equivalence_query(&mut cx, e, r.expr).unwrap();
            // One logic for the whole batch (queries with calls say QF_UFBV).
            let body: String = q
                .lines()
                .filter(|l| !l.starts_with("(set-logic"))
                .map(|l| format!("{l}\n"))
                .collect();
            script.push_str("(push 1)\n");
            script.push_str(&body);
            script.push_str("(pop 1)\n");
            cases.push((
                format!(
                    "seed {:#x}: `{}` => `{}`",
                    0x23_0000 + seed,
                    cx.display(e),
                    cx.display(r.expr)
                ),
                q.contains("QF_UFBV"),
            ));
        }
    }
    let out = z3(&format!("(set-logic ALL)\n{script}")).unwrap();
    let answers: Vec<&str> = out.lines().filter(|l| !l.starts_with('(')).collect();
    assert_eq!(answers.len(), cases.len(), "{out}");
    for (a, (case, uninterpreted)) in answers.iter().zip(&cases) {
        match *a {
            "unsat" => proved += 1,
            // With extension calls as uninterpreted functions, a model may rest on values the
            // real operation never takes (the reference suites check those results).
            "sat" if *uninterpreted => inconclusive += 1,
            "sat" => panic!("z3 found a counterexample: {case}"),
            _ => inconclusive += 1,
        }
    }
    eprintln!("z3: {proved} proved, {inconclusive} inconclusive");
    assert!(
        proved * 2 > cases.len(),
        "z3 proved only {proved} of {}",
        cases.len()
    );
}

#[cfg(feature = "smtlib")]
#[test]
fn z3_proves_simplifications_smoke() {
    z3_simplifications(Size::Smoke);
}

#[cfg(feature = "smtlib")]
#[test]
#[ignore = "heavy: run with --release -- --ignored (needs z3 on PATH; skipped without it)"]
fn z3_proves_simplifications_heavy() {
    z3_simplifications(Size::Heavy);
}
