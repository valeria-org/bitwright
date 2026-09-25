//! The `bitwright` binary, end to end.

use std::path::PathBuf;
use std::process::Command;

fn bin() -> Command {
    Command::new(env!("CARGO_BIN_EXE_bitwright"))
}

/// Runs `bitwright args…`: (exit code, stdout, stderr).
fn run(args: &[&str]) -> (i32, String, String) {
    let o = bin().args(args).output().unwrap();
    (
        o.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&o.stdout).into_owned(),
        String::from_utf8_lossy(&o.stderr).into_owned(),
    )
}

fn file(name: &str, text: &str) -> String {
    let p: PathBuf = [env!("CARGO_TARGET_TMPDIR"), name].iter().collect();
    std::fs::write(&p, text).unwrap();
    p.to_string_lossy().into_owned()
}

const SOUND: &str = "bitwright 1;
group demo {
    /// Absorption.
    #[example(\"p & (p | q)\" => \"p\")]
    rule absorb<W>(x: W, y: W) { x & (x | y) => x }
    #[allow(BW0407)]
    rule mask<W>(x: W, c: const W) { x & c => x if zero_bits(x, ~c) }
}
";

const UNSOUND: &str = "bitwright 1;
group bad {
    #[allow(BW0407)]
    rule add_is_or<W>(x: W, y: W) { x + y => x | y }
}
";

#[test]
fn usage_errors_exit_2() {
    let (code, _, err) = run(&[]);
    assert_eq!(code, 2);
    assert!(err.contains("usage: bitwright"));
    assert_eq!(run(&["frobnicate"]).0, 2);
    assert_eq!(run(&["check"]).0, 2);
    assert_eq!(run(&["check", "--bogus", "x"]).0, 2);
    assert_eq!(run(&["check", "/nonexistent/rules.bwr"]).0, 2);
    let (code, out, _) = run(&["help"]);
    assert_eq!(code, 0);
    assert!(out.contains("commands:"));
}

#[test]
fn explain_prints_the_code() {
    let (code, out, _) = run(&["explain", "bw0106"]);
    assert_eq!(code, 0);
    assert!(out.starts_with("BW0106: "), "{out}");
    assert_eq!(run(&["explain", "BW9999"]).0, 2);
}

#[test]
fn check_reports_verdicts_and_ledgers() {
    let good = file("good.bwr", SOUND);
    let (code, out, err) = run(&["check", &good]);
    assert_eq!(code, 0, "{out}{err}");
    assert!(out.contains("sound         demo::absorb"), "{out}");
    assert!(
        out.contains("2 sound, 0 unsound, 0 inconclusive, 0 failed examples"),
        "{out}"
    );
    // Write a ledger, then compare against it.
    let ledger: PathBuf = [env!("CARGO_TARGET_TMPDIR"), "good.bwr.proof"]
        .iter()
        .collect();
    let ledger = ledger.to_string_lossy().into_owned();
    assert_eq!(run(&["check", &good, "--ledger", &ledger]).0, 0);
    let (code, out, _) = run(&["check", &good, "--against", &ledger]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("is up to date"));
    // A changed rule no longer matches the ledger.
    let changed = file(
        "changed.bwr",
        &SOUND.replace("x & (x | y) => x", "x | (x & y) => x"),
    );
    let (code, out, _) = run(&["check", &changed, "--against", &ledger]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("differs"), "{out}");
    // A wrong example fails the check.
    let wrong = file(
        "wrong_example.bwr",
        &SOUND.replace("\"p & (p | q)\" => \"p\"", "\"p & (p | q)\" => \"q\""),
    );
    let (code, out, _) = run(&["check", &wrong]);
    assert_eq!(code, 1, "{out}");
    assert!(
        out.contains("example: `p & (p | q)` gave `p`, expected `q`"),
        "{out}"
    );
    // An unsound rule fails with a counterexample.
    let bad = file("bad.bwr", UNSOUND);
    let (code, out, _) = run(&["check", &bad]);
    assert_eq!(code, 1);
    assert!(out.contains("UNSOUND       bad::add_is_or"), "{out}");
}

#[test]
fn lint_renders_diagnostics() {
    let broken = file(
        "broken.bwr",
        "bitwright 1;\ngroup g {\n    rule r<W>(x: W) { x => x + x }\n}\n",
    );
    let (code, _, err) = run(&["lint", &broken]);
    assert_eq!(code, 1);
    assert!(err.contains("error[BW0302]"), "{err}");
    assert!(err.contains("broken.bwr:3:"), "{err}");
    let noted = file(
        "noted.bwr",
        "bitwright 1;\ngroup g {\n    rule r<W>(x: W) { x & x => x }\n}\n",
    );
    let (code, out, _) = run(&["lint", &noted]);
    assert_eq!(code, 0);
    assert!(out.contains("BW0407") && out.contains("1 rules"), "{out}");
}

#[test]
fn smt_prints_one_obligation_per_admitted_assignment() {
    let good = file("smt.bwr", SOUND);
    let (code, out, _) = run(&["smt", &good]);
    assert_eq!(code, 0);
    assert_eq!(out.matches("(check-sat)").count(), 6, "{out}");
    assert!(out.ends_with("; 6 obligations\n"));
    let (code, out, _) = run(&["smt", &good, "--rule", "demo::mask", "--widths", "13"]);
    assert_eq!(code, 0);
    assert_eq!(out.matches("(check-sat)").count(), 1);
    assert!(out.contains("(_ BitVec 13)"));
    assert_eq!(run(&["smt", &good, "--rule", "demo::nope"]).0, 2);
    assert_eq!(run(&["smt", &good, "--widths", "x"]).0, 2);
}

#[test]
fn catalog_lists_the_built_in_rules() {
    let (code, out, _) = run(&["catalog"]);
    assert_eq!(code, 0);
    assert!(out.contains("## `core.bwr`") && out.contains("## `eqsat.bwr`"));
    assert!(out.contains("#### `and_absorb_or` — rule"), "{out}");
    assert!(out.contains("- `(q | p) & p` → `p`"), "{out}");
    assert!(out.contains("rule and_absorb_or<W>(x: W, y: W) { x & (x | y) => x }"));
}

#[test]
fn simplify_under_assumptions_reports_what_it_relied_on() {
    let (code, out, _) = run(&[
        "simplify",
        "(p & 7) + zext<8>(x <=u n)",
        "--width",
        "8",
        "--assume",
        "x <u n",
        "--assume",
        "(p & 7) == 0",
    ]);
    assert_eq!(code, 0);
    assert_eq!(out, "1:8    # relies on 0, 1\n");
    let (code, out, _) = run(&["simplify", "x & 0xff", "--width", "8", "--assume", "y == 1"]);
    assert_eq!((code, out.as_str()), (0, "x\n"));
    let (code, _, err) = run(&[
        "simplify", "x", "--width", "8", "--assume", "x == 1", "--assume", "x == 2",
    ]);
    assert_eq!(code, 1);
    assert!(err.contains("contradict each other (0, 1)"), "{err}");
    assert_eq!(run(&["simplify", "x", "--assume", "x"]).0, 2);
}

#[test]
fn simplify_runs_the_engine() {
    let (code, out, _) = run(&["simplify", "(x - 5) + 5 + (y & ~y)", "--width", "16"]);
    assert_eq!(code, 0);
    assert_eq!(out.trim(), "x");
    let (code, out, _) = run(&["simplify", "(x ^ y) + 2 * (x & y)", "--deobfuscate"]);
    assert_eq!(code, 0);
    assert_eq!(out.trim(), "x + y");
    // The standard strategy has no linear-MBA pass.
    let mba = "2 * (x | y) - (x & ~y) - (~x & y)";
    let (code, out, _) = run(&["simplify", mba, "--standard"]);
    assert_eq!(
        (code, out.trim()),
        (0, "let %0 = x | y;\n%0 + %0 - (~y & x) - (~x & y)")
    );
    let (code, out, _) = run(&["simplify", mba, "--deobfuscate"]);
    assert_eq!((code, out.trim()), (0, "x + y"));
    assert_eq!(run(&["simplify", "x", "--standard", "--deobfuscate"]).0, 2);
    assert_eq!(run(&["simplify", "x +", "--width", "8"]).0, 2);
    assert_eq!(run(&["simplify", "x", "--width", "0"]).0, 2);
}

/// `--rules` adds a rule file's rules: checked now, or vouched for by `<file>.proof`.
#[test]
fn simplify_with_rules_of_your_own() {
    let src = "bitwright 1;
group mine {
    /// Every bit is set in x or in ~x.
    #[example(\"popcnt(p:8) + popcnt(~p:8)\" => \"8:8\")]
    rule popcnt_complement<W>(x: W) { popcnt(x) + popcnt(~x) => W }
}
";
    let expr = "popcnt(x) + popcnt(~x)";
    let (code, out, _) = run(&["simplify", expr, "--width", "16"]);
    assert_eq!((code, out.trim()), (0, expr));
    let path = file("mine.bwr", src);
    let proof = format!("{path}.proof");
    let _ = std::fs::remove_file(&proof);
    for standard in [false, true] {
        let mut args = vec!["simplify", expr, "--width", "16", "--rules", &path];
        if standard {
            args.push("--standard");
        }
        let (code, out, err) = run(&args);
        assert_eq!((code, out.trim()), (0, "16:16"), "{err}");
    }
    // With the ledger `check` writes next to it.
    assert_eq!(run(&["check", &path, "--ledger", &proof]).0, 0);
    let (code, out, err) = run(&["simplify", expr, "--width", "32", "--rules", &path]);
    assert_eq!((code, out.trim()), (0, "32:32"), "{err}");
    // A stale ledger is refused.
    let changed = file(
        "mine2.bwr",
        &src.replace("popcnt(x) + popcnt(~x) => W", "popcnt(~x) + popcnt(x) => W"),
    );
    std::fs::copy(&proof, format!("{changed}.proof")).unwrap();
    let (code, _, err) = run(&["simplify", expr, "--rules", &changed]);
    assert_eq!(code, 1);
    assert!(err.contains("does not vouch for mine::popcnt_complement"), "{err}");
    // Unsound rules are refused, with the counterexample.
    let bad = file("bad-rules.bwr", UNSOUND);
    let (code, _, err) = run(&["simplify", "x + y", "--rules", &bad]);
    assert_eq!(code, 1);
    assert!(err.contains("UNSOUND       bad::add_is_or"), "{err}");
    assert_eq!(run(&["simplify", "x", "--rules", "/nonexistent.bwr"]).0, 2);
}

/// Nonlinear MBA simplifies by default (the MBA service with the native solver).
#[test]
fn simplify_deobfuscates_nonlinear_mba() {
    for (input, simplified) in [
        (
            "-8*~y*(x&y)-8*~y*(x&~y)+10*~y*x+3*~y*~(x|y)+8*(x^y)*(x&y)+8*(x^y)*(x&~y)\
             -10*(x^y)*x-3*(x^y)*~(x|y)-3*~y*(x|~y)-1*~y*~x+3*(x^y)*(x|~y)+1*(x^y)*~x",
            "(~x ^ y) - y",
        ),
        ("(x & y) * (x | y) + (x & ~y) * (~x & y)", "x * y"),
    ] {
        let (code, out, err) = run(&["simplify", input]);
        assert_eq!(code, 0, "{err}");
        assert_eq!(out.trim(), simplified, "{input}");
    }
}

/// The book's catalog page is the output of `bitwright catalog`.
#[test]
fn the_book_catalog_is_fresh() {
    let (code, out, _) = run(&["catalog"]);
    assert_eq!(code, 0);
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../book/src/catalog.md");
    let page = std::fs::read_to_string(path).unwrap_or_default();
    assert!(
        page == out,
        "book/src/catalog.md is stale; regenerate it with \
         `cargo run -p bitwright-cli -- catalog > book/src/catalog.md`"
    );
}

#[test]
fn smt_never_checks_nothing_quietly() {
    // A rule admitted only below 8 bits gets obligations at widths it admits.
    let small = file(
        "small.bwr",
        "bitwright 1;\ngroup g {\n    #[allow(BW0407)]\n    rule wrong<W>(x: W) where W <= 4 { x * 3 => x }\n}\n",
    );
    let (code, out, _) = run(&["smt", &small]);
    assert_eq!(code, 0, "{out}");
    assert_eq!(out.matches("(check-sat)").count(), 3, "{out}");
    assert!(
        out.contains("(_ BitVec 2)") && !out.contains("(_ BitVec 8)"),
        "{out}"
    );
    // --widths gives one width per width variable.
    let good = file("smt2.bwr", SOUND);
    assert_eq!(run(&["smt", &good, "--widths", "8,16"]).0, 2);
    assert_eq!(run(&["smt", &good, "--widths", "0"]).0, 2);
    assert_eq!(run(&["smt", &good, "--widths", "513"]).0, 2);
    // A rule not admitted at the given widths is reported where a solver shows it.
    let bytes = file(
        "bytes.bwr",
        "bitwright 1;\ngroup g {\n    #[allow(BW0407)]\n    rule r<W>(x: W) where W % 8 == 0 { bswap(bswap(x)) => x }\n}\n",
    );
    let (code, out, _) = run(&["smt", &bytes, "--widths", "13"]);
    assert_eq!(code, 1, "{out}");
    assert!(out.contains("(echo \"SKIPPED g::r"), "{out}");
}

#[test]
fn a_double_dash_ends_the_options() {
    let (code, out, err) = run(&["simplify", "--width", "8", "--", "--x"]);
    assert_eq!(code, 0, "{err}");
    assert_eq!(out.trim(), "x");
}
