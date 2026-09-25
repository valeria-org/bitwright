# Checking rules

A rule is used only if it is proven. The checker (feature `check`, on by default) evaluates each
rule's obligation, *if the guard holds then the pattern equals the template*, on concrete values:

- **exhaustively** at every admitted width assignment with widths up to 6, over every value of
  the parameters when they total at most 16 bits (and under every rounding mode of a rule's
  rounding-mode parameters, so a floating-point rule is checked in every format up to
  `(6, 6)`);
- **by sampling** at 22 widths up to 512 bits (7, 8, 9, 12, 16, 31, 32, 33, 63, 64, 65, …), with
  boundary-biased values (0, 1, −1, the signed extremes, powers of two), half of them steered
  toward making the guard true.

The verdict is `Sound` only when there is no counterexample and the guard actually held in the
exhaustive tier (and in the sampled tier, unless the exhaustive tier covered every admitted
width). Otherwise it is `Unsound` with a counterexample, or `Inconclusive` with the missing tier
named. This is testing, not proof: for proof at wide widths, ask the native prover (see
[Proving rules](#proving-rules)) or export the obligations to an SMT solver (see
[SMT-LIB](smtlib.md)).

```rust
use bitwright::check::{CheckConfig, Verdict, check_program};
use bitwright::rules::RuleProgram;

let src = "bitwright 1;
group demo {
    #[example(\"p & (p | q)\" => \"p\")]
    rule absorb<W>(x: W, y: W) { x & (x | y) => x }

    #[allow(BW0407)]
    rule wrong<W>(x: W, y: W) { x + y => x | y }
}";
let program = RuleProgram::compile(src).map_err(|e| e.to_string())?;
let checks = check_program(&program, &CheckConfig::default());
assert!(checks[0].is_sound() && checks[0].examples.is_empty());
match &checks[1].verdict {
    Verdict::Unsound(cx) => println!("counterexample: {cx}"), // W = 1; x = 0x1:1, y = 0x1:1: …
    other => panic!("{other:?}"),
}
# Ok::<(), String>(())
```

## Proving rules

`CheckConfig::with_proofs(n)` (`bitwright check --prove`, with `n` = 3) also proves each rule
with bitwright's native prover at up to `n` width assignments too wide to enumerate: widths 8,
32 and 64 for a rule over bit-vectors, binary16, binary32 and binary64 for a floating-point rule
(each under every rounding mode), and every assignment of a rule over fixed widths. The prover
bit-blasts the obligation, floating-point operations included, and decides it with its own SAT
solver; a constant parameter under a guard (`c` a power of two) is split into the constants the
guard admits when the whole question is too hard. A refutation is a counterexample, checked by
evaluation; a rule with no assignment small enough to enumerate is `Sound` when every one of
its proofs succeeds; the evidence counts the assignments proved and those left open (the
solver has a conflict budget, `with_proof_conflicts`).

`prove::rule` asks about one assignment, with a certificate on request: the clauses and a DRUP
proof, checked by an independent checker. `prove::rule_all_widths` proves every assignment up
to a bound, and settles a rule of bitwise operations on its parameters and the constants 0 and
all ones for every width at once: bit `i` of each side is one Boolean function of bit `i` of
the parameters, the same at every position and every width, so width 1 decides it.

```rust
use bitwright::check::{CheckConfig, check_program};
use bitwright::prove::{self, Config, RuleOutcome};
use bitwright::rules::RuleProgram;

let src = "bitwright 1;
group demo {
    #[allow(BW0407)]
    rule wide(x: 64, y: 64) { (x ^ y) + 2 * (x & y) => x + y }

    #[example(\"p & (p | q)\" => \"p\")]
    rule absorb<W>(x: W, y: W) { x & (x | y) => x }
}";
let program = RuleProgram::compile(src).map_err(|e| e.to_string())?;
// At 64 bits there is nothing to enumerate: sampling alone would be inconclusive.
let checks = check_program(&program, &CheckConfig::default().with_proofs(3));
assert!(checks[0].is_sound());
assert_eq!(checks[0].evidence.proved_instances, 1);

// One rule at chosen widths, with a certificate that an independent checker verifies.
let absorb = &program.rules()[1];
match prove::rule(absorb, &[128], &Config::default().with_certificate(true))? {
    RuleOutcome::Proved(Some(certificate)) => certificate.check()?,
    other => panic!("{other:?}"),
}
// Bitwise operations only: width 1 settles every width.
assert!(prove::rule_all_widths(absorb, 64, &Config::default())?.every_width);
# Ok::<(), Box<dyn std::error::Error>>(())
```

### Rules as Lean theorems

`bitwright lean rules.bwr` (`rules::lean::lean`) writes the rules as Lean 4 theorems over
`BitVec`, for every width: the width variables universally quantified (positive, and meeting
the `where` constraints), the guard a hypothesis, the proof `sorry` for you to write. A proof in
Lean covers every width at once, which neither the checker nor the prover can. `--at 8` writes
each rule instead at the widest widths up to 8 it admits, proved by `bv_decide`, whose
certificates Lean's kernel checks: an oracle that shares nothing with bitwright. Division is
SMT-LIB's (`BitVec.smtUDiv`); floating point, bit counts, `pdep` and `pext`, which Lean's core
`BitVec` lacks, leave a rule out with a comment.

```text
$ bitwright lean --at 8 > rules8.lean && lean rules8.lean
```

At 8 bits `bv_decide` proves every built-in rule Lean can state but the distributivity and
associativity of multiplication, which run out of its budget.

## Proof ledgers

A proof ledger records, for every `Sound` rule, its content hash and the evidence. The engine
links a program only together with a ledger that vouches for each of its rules; change a rule
and its hash changes, so the ledger no longer vouches for it until you check it again.

```rust
use bitwright::check::{CheckConfig, check_program};
use bitwright::engine::{Engine, Run, RuleCensus, Strategy};
use bitwright::rules::{Ledger, RuleProgram};
use bitwright::{Context, ParseOptions, Width};

let src = "bitwright 1;
group my.rules {
    /// Whatever y is, x stays.
    #[example(\"(p | q) & (p | ~q)\" => \"p\")]
    rule and_or_complement<W>(x: W, y: W) { (x | y) & (x | ~y) => x }
}";
let program = RuleProgram::compile(src).map_err(|e| e.to_string())?;
let ledger = Ledger::from_checks(&check_program(&program, &CheckConfig::default()));
let text = ledger.render(); // check this in next to the rules

let engine = Engine::builder()
    .builtin()
    .program(program, &Ledger::parse(&text)?)
    .strategy(Strategy::standard().with_rule_groups(&["my.rules"]))
    .build()
    .map_err(|e| e.to_string())?;
let mut cx = Context::new();
let e = cx.parse("(a | b) & (a | ~b)", &ParseOptions::width(Width::W64)).map_err(|e| e.to_string())?;
let mut census = RuleCensus::default();
let out = engine
    .run(&mut cx, &[e], Run::default().with_observer(&mut census))
    .map_err(|e| e.to_string())?;
assert_eq!(cx.display(out.roots[0].expr).to_string(), "a");
assert_eq!(census.rules["my.rules::and_or_complement"].applied, 1);

// Without a ledger that vouches for it, a program does not link.
let again = RuleProgram::compile(src).map_err(|e| e.to_string())?;
assert!(Engine::builder().program(again, &Ledger::default()).build().is_err());
# Ok::<(), String>(())
```

For experiments, `EngineBuilder::allow_unproven(true)` with `unproven_program` links rules
without a ledger; each of their applications is then verified by sampling, and the statistics
count them.

`bitwright check rules.bwr --ledger rules.bwr.proof` writes a ledger from the command line, and
`--against` compares an existing one, which is how a CI job keeps ledgers fresh.
