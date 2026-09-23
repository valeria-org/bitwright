# Equality saturation (feature `eqsat`)

The simplifier only ever makes expressions smaller, one step at a time, so it cannot find a
result that needs a detour: factoring `x·y + x·z` into `x·(y + z)` means applying
distributivity backwards, and `x·(y + 1) − x·y` only cancels after it is expanded. The
equality-saturation service searches for such alternatives in an e-graph, where every equation
is applied without losing the original.

It is a *search service*, not a phase: you decide when to run it (at an output or checkpoint
boundary, not in routine maintenance), on which roots, and with which allowance. What it finds is
a *candidate* that your own profitability and verification decide to use.

```rust
use bitwright::eqsat::{Publication, SaturateConfig, Saturator, SearchRun};
use bitwright::{Context, ParseOptions, Width};

let (sat, report) = Saturator::builtin_groups(
    &["eqsat.distrib", "eqsat.cancel"],
    SaturateConfig::default(),
);
assert!(report.admitted.len() > 1);
let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let factor = cx.parse("x * y + x * z", &o)?;
let cancel = cx.parse("x * (y + 1) - x * y", &o)?;
let out = sat.search(&mut cx, &[factor, cancel], SearchRun::default())?;
assert_eq!(out.publication, Publication::Published);
assert_eq!(out.roots[0].candidate, Some(cx.parse("x * (y + z)", &o)?));
assert_eq!(out.roots[1].candidate, Some(cx.parse("x", &o)?));
# Ok::<(), bitwright::Error>(())
```

## Equations

Admitted equations are proven (by their ledger), unconditional, of one width, and in a
conservative fragment: `+ − * & | ^`, negation and complement, constants and symbols, widths up
to 128. Identities are used in both directions; guard-free rules (cancellations like
`(x + y) − y → x`) in their authored direction only. Other inputs are declined, never
approximated.

The built-in equations come in groups: `eqsat.assoc`, `eqsat.distrib` (`*` over `+`),
`eqsat.distrib_and` (`&` over `|` and `^`), `eqsat.distrib_or` (`|` over `&`),
`eqsat.negation` and `eqsat.cancel`. Choose the groups a search needs: some combinations never
saturate (`distrib_and` with `distrib_or` rewrite each other's results without end), and a
search that does not saturate publishes nothing.

## Publication

Each root is searched in its own e-graph, sharing only the allowance. A batch is published only
if every root it searched saturated within its bounds: reaching the iteration cap, a budget or a
deadline withholds the whole batch (`Publication::Withheld`), and the rest of the batch is not
searched (those roots are reported as stopped, or as `Skipped`). A deadline already passed when
the search starts withholds the batch even where the memo has the answer. Spent allowance stays
spent. A candidate must be strictly smaller as a tree, no larger
as a DAG, and agree with its input at sampled points.

Stable outcomes (saturated searches, admission declines) are memoized in the context, so asking
again is free; incomplete searches are not, so more budget can succeed later.

```rust
use bitwright::eqsat::{Publication, RootEnd, SaturateConfig, Saturator, SearchRun};
use bitwright::{Context, ParseOptions, Width};

let (sat, _) = Saturator::builtin_groups(
    &["eqsat.distrib_and", "eqsat.distrib_or"],
    SaturateConfig::default(),
);
let mut cx = Context::new();
let e = cx.parse("a & b | a & c", &ParseOptions::width(Width::W32))?;
let out = sat.search(&mut cx, &[e], SearchRun::default())?;
assert_eq!(out.roots[0].end, RootEnd::IterationCap);
assert!(matches!(out.publication, Publication::Withheld { .. }));
assert_eq!(out.roots[0].candidate, None);
# Ok::<(), bitwright::Error>(())
```
