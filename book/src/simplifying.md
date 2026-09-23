# Simplifying

An `Engine` holds linked rules and a `Strategy`: an ordered list of phases, run bottom-up over
each root and repeated for a few rounds until nothing changes. Build it once and share it (it is
cheap to clone and `Send + Sync`); run it on any context.

```rust
use bitwright::engine::{Engine, Strategy};
use bitwright::{Context, ParseOptions, Width};

let engine = Engine::builder()
    .builtin() // the built-in rules, vouched for by their proof ledger
    .strategy(Strategy::standard())
    .build()?;
let mut cx = Context::new();
let e = cx.parse("((x & 0xff) | (x & 0xff00)) + (y ^ y)", &ParseOptions::width(Width::W32))?;
let out = engine.simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "x & 65535");
assert!(out.changed);
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Strategies

`Strategy::standard()` is fact folding, the built-in rules, the normal-form passes (linear
arithmetic, xor forms, casts, equalities through invertible maps, comparisons, bitwise truth
tables, demanded bits) and the rules again. `Strategy::deobfuscate()` adds the linear-MBA and
bit-shuffle passes (see [Deobfuscation and MBA](deobfuscation.md)). You can build your own from
`Phase`s.

Each pass commits a rewrite only if it makes the expression DAG strictly smaller, counted over
everything the call keeps alive, so shared subexpressions are never duplicated to "simplify"
one user. Equal-size rewrites are never made, which is why passes and rules cannot fight. The
one exception is `Phase::Invert` (see [Invertibility](invertibility.md)): like a rule, it
replaces a comparison by one of proper subterms of its operands, so it commits even when those
operands stay alive for other users.

## Budgets, allowances and deadlines

Every run is bounded. A `Budget` caps node visits, rule candidates, matcher steps, rewrites, new
nodes, fact work, pass work, MBA solver calls and equality-saturation work; `Run` carries the
per-call budget and optionally an `Allowance`, an account several calls share. Work is charged
before it is done, so a call never spends past its limit:

```rust
use bitwright::engine::{Allowance, Budget, End, Engine, Exhausted, Run};
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let e = cx.parse("((x + 1) + 2) + (y - y)", &ParseOptions::width(Width::W32))?;
let engine = Engine::standard();
let out = engine.run(&mut cx, &[e], Run::default().with_per_call(Budget::default().with_rewrites(0)))?;
assert_eq!(out.roots[0].end, End::BudgetTerminated(Exhausted::Rewrites));
assert!(!out.roots[0].changed);
// Unchanged from how it was built (construction already folded `y - y`).
assert_eq!(cx.display(out.roots[0].expr).to_string(), "x + 1 + 2");

// One account for a whole analysis.
let mut account = Allowance::new(Budget::default().with_node_visits(10_000));
let out = engine.run(&mut cx, &[e], Run::default().with_allowance(&mut account))?;
assert_eq!(out.roots[0].end, End::Completed);
assert_eq!(cx.display(out.roots[0].expr).to_string(), "x + 3");
assert!(account.spent().node_visits > 0);
# Ok::<(), Box<dyn std::error::Error>>(())
```

A root stopped by a budget still has a correct result (every rewrite made is kept); it is just
not final, and a later call with more budget continues from it. A `Deadline` stops a run at a
time your own `Clock` reports; bitwright never reads a clock itself. Budgets are the
deterministic choice; a deadline makes results depend on timing.

Admission caps (`Admission`) decline roots that are too large before any work is done.

## What the result tells you

`Outcome::roots` has one `RootOutcome` per input: the result, whether it changed, and how the
run ended (`Completed`, `BudgetTerminated`, `Declined`). `Outcome::stats` counts everything:
visits, memo hits, candidates, no-match and guard-false declines, rewrites, rejections, each
pass's calls and commits, and the MBA service's answers. Unproductive work is counted like
productive work.

Results are memoized in the context: simplifying the same node again (or a larger expression
containing it) is answered from the memo, as long as the engine, the host hooks and the
assumptions are the same.

## Hooks and observers

`Hooks` let the host veto a rewrite (`admit`) or a fold of a fact-known value into a constant
(`fold_known`). An `Observer` receives an event per rule candidate and per rewrite;
`RuleCensus` is one that counts them per rule.

```rust
use bitwright::engine::{By, Engine, Hooks, Run, RuleCensus};
use bitwright::{Context, Expr, ParseOptions, Width};

/// Keeps the linear pass out (say, because a later stage wants to see the original terms).
struct NoLinear;
impl Hooks for NoLinear {
    fn admit(&self, _: &Context, _before: Expr, _after: Expr, by: By<'_>) -> bool {
        by.name() != "linear"
    }
    fn revision(&self) -> u64 {
        1 // part of the memo key: change it whenever the policy changes
    }
}

let mut cx = Context::new();
let e = cx.parse("(x + 1) - 1 + y * 2 - y", &ParseOptions::width(Width::W8))?;
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "x + y");

let mut census = RuleCensus::default();
let out = Engine::standard().run(
    &mut cx,
    &[e],
    Run::default().with_hooks(&NoLinear).with_observer(&mut census),
)?;
assert_eq!(cx.display(out.roots[0].expr).to_string(), "x + 1 - 1 + (y << 1) - y");
assert!(out.stats.hook_vetoes > 0);
assert_eq!(census.rules["core.arith::mul_pow2"].applied, 1);
# Ok::<(), bitwright::Error>(())
```

## Verification

Rules linked from a proof ledger are trusted; every application still passes cheap
postconditions (the width is unchanged, the facts of the result are compatible with the input's,
the result is smaller in the termination order). `Verify` adds sampled evaluation of every
application (`Verify::strict()` for tests), and rules linked without a ledger
(`allow_unproven`) are always sampled.
