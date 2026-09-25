//! The Lean 4 export: the statements it writes, and (ignored; it needs `lean` on the path)
//! that Lean elaborates every one and proves every instance at 8 bits with `bv_decide`.

use bitwright::rules::lean::{lean, rule_instance, rule_theorem};
use bitwright::rules::{RuleProgram, builtin_sources};

fn builtins() -> Vec<RuleProgram> {
    builtin_sources()
        .iter()
        .map(|(_, src, _)| RuleProgram::compile(src).unwrap())
        .collect()
}

fn one(body: &str) -> RuleProgram {
    RuleProgram::compile(&format!("bitwright 1;\ngroup t {{\n{body}\n}}\n")).unwrap()
}

#[test]
fn statements() {
    let p = one("/// Masking known bits.\n\
         rule mask<W>(x: W, c: const W) where 2 < W { x & c => x if zero_bits(x, ~c) }\n\
         rule hi<W, V>(x: W, y: V) where V < W { extract<V, W>(concat(x, y)) => x }\n\
         identity rot<W>(x: W, y: W) { rotl(x, y) <=> rotr(x, -y) }\n\
         rule half<W>(x: W) { udiv(x, 2) => x >>u 1 }\n\
         rule neg_one<W>(x: W) { x * -1 => -x }\n\
         rule ctz_zero<W>(x: W) { popcnt(x) + popcnt(~x) => W }");
    let [mask, hi, rot, half, neg_one, ctz_zero] = p.rules() else {
        panic!()
    };
    assert_eq!(
        rule_theorem(mask),
        "/-- Masking known bits. -/\n\
         theorem mask (W : Nat) (hW : 0 < W) (hw0 : 2 < W) (x c : BitVec (W)) \
         (hg : (x &&& (~~~c) = 0#(W))) :\n    (x &&& c) = x := by\n  sorry\n"
    );
    // Widths in terms of the variables; `++` cast to the node's width.
    let t = rule_theorem(hi);
    assert!(
        t.contains(
            "(W V : Nat) (hW : 0 < W) (hV : 0 < V) (hw0 : V < W) (x : BitVec (W)) (y : BitVec (V))"
        ),
        "{t}"
    );
    assert!(
        t.contains("((BitVec.cast (m := W + V) (by omega) (x ++ y)).extractLsb' (V) (W)) = x"),
        "{t}"
    );
    // Rotations by a variable amount: `rotateLeft` for every width, shifts at a fixed one.
    assert!(
        rule_theorem(rot)
            .contains("(x.rotateLeft y.toNat) = (x.rotateRight (-y).toNat) := by -- an identity")
    );
    let t = rule_instance(rot, &[8]).unwrap();
    assert!(
        t.contains("((x <<< (y % 8#(8))) ||| (x >>> ((8#(8) - y % 8#(8)) % 8#(8))))"),
        "{t}"
    );
    assert!(
        t.contains("((x >>> ((-y) % 8#(8))) ||| (x <<< ((8#(8) - (-y) % 8#(8)) % 8#(8))))"),
        "{t}"
    );
    assert!(
        t.contains("(x y : BitVec (8))") && t.ends_with("  bv_decide\n"),
        "{t}"
    );
    // Division as SMT-LIB defines it; negative literals.
    assert!(rule_theorem(half).contains("(x.smtUDiv (2#(W)))"));
    assert!(rule_theorem(neg_one).contains("(x * (-(1#(W))))"));
    // What Lean's core BitVec cannot say is left out.
    assert!(rule_theorem(ctz_zero).starts_with("-- t::ctz_zero: not stated"));
    assert!(rule_instance(mask, &[2]).is_none(), "2 < W");
}

#[test]
fn builtin_rules_are_stated() {
    let programs = builtins();
    let refs: Vec<&RuleProgram> = programs.iter().collect();
    let all = lean(&refs, None);
    let theorems = all.matches("\ntheorem ").count();
    let skipped: Vec<&str> = all.lines().filter(|l| l.contains(": not stated")).collect();
    let rules: usize = programs.iter().map(|p| p.rules().len()).sum();
    assert_eq!(theorems + skipped.len(), rules);
    // Only floating point, pdep/pext and bit counts are left out.
    for l in &skipped {
        assert!(
            l.contains("floating point") || l.contains("pdep") || l.contains("bit count"),
            "{l}"
        );
    }
    assert!(theorems > 250, "{theorems}");
    // Namespaces pair up.
    assert_eq!(
        all.matches("\nnamespace ").count(),
        all.matches("\nend ").count()
    );
}

/// The directory for files the Lean checks write (inside the target directory).
fn scratch() -> std::path::PathBuf {
    let d = std::path::PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("lean");
    std::fs::create_dir_all(&d).unwrap();
    d
}

fn run_lean(name: &str, text: &str) -> Option<String> {
    let path = scratch().join(name);
    std::fs::write(&path, text).unwrap();
    let out = std::process::Command::new("lean")
        .arg(&path)
        .output()
        .ok()?;
    Some(String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr))
}

/// Lean elaborates every statement, and `bv_decide` proves the built-in rules at 8 bits,
/// never finding a counterexample (a few multiplication identities may exceed its budget).
#[test]
#[ignore = "needs lean 4 on the path; about 15 s"]
fn lean_elaborates_and_proves_instances() {
    let programs = builtins();
    let refs: Vec<&RuleProgram> = programs.iter().collect();
    let Some(out) = run_lean("rules.lean", &lean(&refs, None)) else {
        eprintln!("lean not found; skipped");
        return;
    };
    let errors: Vec<&str> = out.lines().filter(|l| l.contains("error")).collect();
    assert!(errors.is_empty(), "{out}");
    let out = run_lean("rules8.lean", &lean(&refs, Some(8))).unwrap();
    let mut timeouts = 0;
    for l in out.lines().filter(|l| l.contains("error")) {
        if l.contains("timed out") || l.contains("maximum number of heartbeats") {
            timeouts += 1;
        } else {
            panic!("{l}\n{out}");
        }
    }
    assert!(timeouts <= 4, "{out}");
}
