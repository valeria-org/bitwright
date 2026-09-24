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
named. This is testing, not proof: for proof at wide widths, export the obligations to an SMT
solver (see [SMT-LIB](smtlib.md)).

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
