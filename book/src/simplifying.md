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

## Ways to simplify

The same expressions can be simplified in several ways, depending on what a tool needs:

| To | Use | See |
|-|-|-|
| clean up compiler or lifter output | `Engine::standard()` | below |
| undo obfuscation, MBA included | `Strategy::deobfuscate()` with the MBA service, or the command line's `simplify` | [Deobfuscation and MBA](deobfuscation.md) |
| run only some passes, or more rounds | a `Strategy` of your own `Phase`s | below |
| simplify under a path condition | `Run::with_assumptions` | [Constraints](constraints.md) |
| decide a condition without rewriting | `Context::prove`, `Context::facts` | [Facts and proofs](facts.md) |
| rewrite a target's own idioms | rules of your own, linked with their proof ledger | [Writing rules](rules.md) |
| find a smaller form the directed engine misses | the equality-saturation search | [Equality saturation](eqsat.md) |
| keep some rewrites out, or watch them | `Hooks` and `Observer`s | below |
| check a result independently | an SMT-LIB equivalence query | [SMT-LIB](smtlib.md) |
| use a solver's results, or simplify its terms | SMT-LIB import | [SMT-LIB](smtlib.md) |

[Examples](examples.md) shows each of them on a task from reverse engineering.

## Strategies

`Strategy::standard()` is fact folding, the built-in rules, the normal-form passes (linear
arithmetic, xor forms, casts, equalities through invertible maps, comparisons, bitwise truth
tables, demanded bits) and the rules again. `Strategy::deobfuscate()` adds the linear-MBA and
bit-shuffle passes (see [Deobfuscation and MBA](deobfuscation.md)). You can build your own from
`Phase`s.

A strategy of your own runs just the phases you name, in your order. One that only folds what
the facts pin and collects linear sums cancels additive masking and leaves everything else as
the lifter wrote it:

```rust
use bitwright::engine::{Engine, Phase, Strategy};
use bitwright::{Context, ParseOptions, Width};

let unmask = Engine::builder()
    .builtin()
    .strategy(Strategy::new("unmask", vec![Phase::FactFold, Phase::Linear]))
    .build()?;
let mut cx = Context::new();
let e = cx.parse("(x + y) * 3 - 3 * y + ((z & 0xff) | (z & 0xff00))", &ParseOptions::width(Width::W32))?;
let out = unmask.simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "x * 3 + (z & 255 | z & 65280)");
// The standard strategy merges the masks too.
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "x * 3 + (z & 65535)");
# Ok::<(), Box<dyn std::error::Error>>(())
```

`Phase::Local` runs the rules of the groups it names (the built-in groups are listed in the
[rule catalog](catalog.md)), and `Strategy::max_rounds` bounds the rounds.

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

## Many expressions at once

`Engine::run` takes several roots and processes them one after another, in one context: work
on shared subexpressions is done once, and a rewrite is weighed against every root that uses
a node. For many independent expressions (every instruction of a function, a dataset of
obfuscated expressions), `Engine::run_each` simplifies each root on its own, as a call with
that root alone would, on threads. Each root is copied into a context of its own
(`Context::import`, which also moves expressions between contexts in general), simplified
there, and its result copied back. The results do not depend on the number of threads, and
`Outcome::stats` sums the roots':

```rust
use bitwright::engine::{Each, Engine, Strategy};
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let roots = [
    cx.parse("(x ^ y) + 2 * (x & y)", &o)?,
    cx.parse("(x | y) - (x & ~y)", &o)?,
    cx.parse("((a - b) >>u 31) ^ (((a ^ b) & (a ^ (a - b))) >>u 31)", &o)?,
];
let engine = Engine::builder().builtin().strategy(Strategy::deobfuscate()).build()?;
let out = engine.run_each(&mut cx, &roots, Each::default().with_threads(4))?;
let shown: Vec<String> = out.roots.iter().map(|r| cx.display(r.expr).to_string()).collect();
assert_eq!(shown, ["x + y", "y", "zext<32>(a <s b)"]);
# Ok::<(), Box<dyn std::error::Error>>(())
```

`Each` takes a per-root budget, admission caps, assumptions (copied into each root's context)
and hooks that are `Sync`; observers, allowances and deadlines are `run`'s. On a target
without threads the calling thread does all the work. The command line's `simplify --file`
does the same for a file of expressions, one per line.

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
