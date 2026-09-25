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
| simplify every value of every function, in a compiler | `Strategy::compile()` | [below](#inside-a-compiler) |
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
`Strategy::sharing` can make the passes decide by each node's own subexpressions instead
(`Sharing::Ignored`, see [Inside a compiler](#inside-a-compiler)), and `Strategy::max_region`
bounds how many nodes a pass examines to decide.

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
a node. A rewrite held back only because another root shared its subterms is reconsidered once
every root is done, when those roots may no longer use them. For many independent expressions (every instruction of a function, a dataset of
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

## Inside a compiler

A compiler simplifies every value of every function, and most of them are already simple, so
it needs a cost per value that stays the same however large the function grows.
`Strategy::compile()` is built for that. It runs the standard phases without demanded bits, in
one round. Its passes decide as if each node's subexpressions were used by that node alone
(`Sharing::Ignored`), and look at most 64 nodes deep (`Strategy::max_region`). A decision
therefore depends only on the node, never on which other values the call has, so every
result is final and memoized. One call over every value of a function costs time in
proportion to its size. A later call over the same values, or over values built on them, is
answered from the memo.

The standard strategy weighs sharing across all the roots of a call. That gives smaller
results, but some decisions must then be made again for every root, so a call over every value
of a function costs time growing with its size. `Strategy::compile()` can leave a result
larger where values share subterms: a rewrite may keep alive a subterm another value still
uses. The compiler keeps its own use counts and decides what to replace.

Build values through the builder, not text, with the compiler's value numbers as symbol keys,
and reuse one context per function (`Context::clear` keeps its allocations, and
`Context::reserve` makes room for a function you know the size of):

```rust
use bitwright::engine::{Engine, Run, Strategy};
use bitwright::{BinOp, Context, Width};

let engine = Engine::builder().builtin().strategy(Strategy::compile()).build()?;
let mut cx = Context::new();
let w = Width::W64;
// The parameters %0 and %1.
let a = cx.symbol(0u64, w)?;
let b = cx.symbol(1u64, w)?;
let seven = cx.constant_u64(w, 7)?;
let v2 = cx.bin(BinOp::Add, a, seven)?; // %2 = add %0, 7
let v3 = cx.bin(BinOp::Sub, v2, seven)?; // %3 = sub %2, 7
let v4 = cx.bin(BinOp::And, v3, b)?; // %4 = and %3, %1
let v5 = cx.bin(BinOp::Or, v3, b)?; // %5 = or %3, %1
let v6 = cx.bin(BinOp::Add, v4, v5)?; // %6 = add %4, %5
let values = [v2, v3, v4, v5, v6];
let out = engine.run(&mut cx, &values, Run::default())?;
let shown: Vec<String> = out.roots.iter().map(|r| cx.display(r.expr).to_string()).collect();
assert_eq!(shown, ["#0 + 7", "#0", "#0 & #1", "#0 | #1", "#0 + #1"]);
// Every result is final: the same values again are answered from the memo.
let again = engine.run(&mut cx, &values, Run::default())?;
assert_eq!(again.stats.node_visits, 0);
assert_eq!(again.roots, out.roots);
# Ok::<(), Box<dyn std::error::Error>>(())
```

Equal handles always mean equal values (see [Semantics](semantics.md)). A result that is already
the expression of another value (`%3` is `%0` above) is that value, and the compiler can
replace the uses of one with the other.

A compiler also knows things about values bitwright sees only as symbols: a parameter
zero-extended from 32 bits, an aligned pointer, a load's range, a value computed in another
block. `Context::declare_known` states such knowledge as known bits of the symbol. Facts,
proofs and the simplifier all use it:

```rust
use bitwright::engine::{Engine, Strategy};
use bitwright::{BitVec, Context, KnownBits, ParseOptions, SymbolKey, Width};

let engine = Engine::builder().builtin().strategy(Strategy::compile()).build()?;
let mut cx = Context::new();
let w = Width::W64;
let o = ParseOptions::width(w);
let p = cx.symbol("p", w)?;
let n = cx.symbol("n", w)?;
// `p` is 8-byte aligned; `n` was zero-extended from 32 bits.
cx.declare_known(p, KnownBits::new(BitVec::from_u64(w, 7)?, BitVec::zero(w)).unwrap())?;
let high = BitVec::from_u64(w, 0xffff_ffff_0000_0000)?;
cx.declare_known(n, KnownBits::new(high, BitVec::zero(w)).unwrap())?;
let checks = cx.parse("((p & 7) == 0) & (zext<64>(trunc<32>(n)) == n)", &o)?;
let bump = cx.parse("(p + 8 & -8) + (n >>u 32)", &o)?;
let out = engine.simplify(&mut cx, checks)?;
assert_eq!(cx.display(out.expr).to_string(), "1:1");
let out = engine.simplify(&mut cx, bump)?;
assert_eq!(cx.display(out.expr).to_string(), "p + 8");
# Ok::<(), Box<dyn std::error::Error>>(())
```

Without the declarations both stay as they are, apart from construction's canonical forms. A
declaration becomes part of the symbol's meaning. A result is equal to its input for every
value that agrees with the declarations, and SMT-LIB export states them as assertions. Declare
right after creating a symbol: a declaration drops the facts and results the context has
cached, since they may depend on it.

One call over every value of a function is the fastest way to use it. A call per value as it
is created (`Engine::simplify`) gives the same results, and values already simplified are
answered from the memo. It costs more, because the passes' own caches last one call.
`compile/*` in `bitwright-bench` measures both shapes.

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
