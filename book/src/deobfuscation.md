# Deobfuscation and MBA

Obfuscators hide simple operations behind *mixed boolean-arithmetic* (MBA) identities, such as
`x + y = (x ^ y) + 2·(x & y)`, and behind bit shuffles that take a value apart and put it back.
`Strategy::deobfuscate()` adds two passes to the standard strategy for these (hash
comparisons through invertible mixers are handled by the standard strategy; see
[Invertibility](invertibility.md)):

- **Linear MBA.** A linear combination of bitwise functions of up to six atoms is determined by
  its values at the corners where every atom is 0 or all ones. The pass computes that signature
  and emits the cheapest equivalent form it knows, if that is smaller.
- **Shuffle.** Values assembled from slices of other values (extracts, shifts, masks, concats,
  ors of disjoint parts) are traced bit by bit, and re-emitted as the rotation, byte swap,
  extension or plain slice they are.

```rust
use bitwright::engine::{Engine, Strategy};
use bitwright::{Context, ParseOptions, Width};

let engine = Engine::builder().builtin().strategy(Strategy::deobfuscate()).build()?;
let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
for (obfuscated, plain) in [
    ("(x | y) - (x & y)", "x ^ y"),
    ("(x & 0xff) + (x & 0xff00) - 2 * (x ^ y) + (x | y) * 2 - 2 * (x & y)", "x & 65535"),
    (
        "(zext<32>(trunc<8>(x)) << 24) | (zext<32>(extract<8, 8>(x)) << 16) \
         | (zext<32>(extract<16, 8>(x)) << 8) | zext<32>(extract<24, 8>(x))",
        "bswap(x)",
    ),
] {
    let e = cx.parse(obfuscated, &o)?;
    let out = engine.simplify(&mut cx, e)?;
    assert_eq!(cx.display(out.expr).to_string(), plain);
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

## The MBA service (feature `mba`)

Nonlinear MBA (products of bitwise terms, for example) needs a solver. The MBA service lowers a
fragment of an expression into a small standalone `MbaExpr`, asks an `MbaSolver`, and publishes
the answer only through an evidence gate:

1. the answer must have the input's variables and width and agree with it at 64 seeded points
   (always);
2. then evidence, in order: bitwright's own exact evidence (equal linear signatures, or
   evaluation at every point when the variables total at most 20 bits), a configured
   `EquivalenceProver`, the backend's own `Proved` or `Certified` claim if
   `MbaTrust::backend_certificates` is set (the default), or agreement at the sampled points if
   `MbaTrust::sampled` is set (off by default);
3. the answer lifted back into the context must agree with the original, make the DAG smaller,
   and pass the usual postconditions and host veto.

Answers are cached (keyed by the lowered input, the solver's and prover's ids, the trust
setting and the lowering version) in an `MbaCacheStore` you provide; `MemoryCache` is a bounded
in-memory one.

```rust
use std::sync::Arc;
use bitwright::engine::{Engine, Strategy};
use bitwright::mba::{MbaConfig, MbaTrust, MemoryCache, SignatureSolver};
use bitwright::{Context, ParseOptions, Width};

let config = MbaConfig::default().with_trust(
    MbaTrust::default().with_backend_certificates(false), // trust only evidence we can check
);
let engine = Engine::builder()
    .builtin()
    .strategy(Strategy::deobfuscate().with_mba(config))
    .mba_solver(Arc::new(SignatureSolver)) // native, complete for linear MBA
    .mba_cache(Arc::new(MemoryCache::new(4096)))
    .build()?;
let mut cx = Context::new();
let e = cx.parse(
    "3 * (x & ~y) + 2 * (~x & y) + 5 * (x & y) - (x | y)",
    &ParseOptions::width(Width::W64),
)?;
let out = engine.run(&mut cx, &[e], Default::default())?;
assert!(out.stats.mba.calls + out.stats.mba.cache_hits > 0);
// 2·x + y + (x & y): the same function of x and y at every bit.
assert_eq!(cx.display(out.roots[0].expr).to_string(), "(x & y) + (x << 1) + y");
# Ok::<(), Box<dyn std::error::Error>>(())
```

With feature `cobra`, `CobraSolver` asks the `cobra-mba` crate, which proves its answers with
Lean certificates by default. `ThreadedSolver` wraps any solver with a hard wall-clock deadline
per question (a late answer is abandoned and never cached). Trusting backend certificates means
trusting the backend: a host that needs independent evidence turns `backend_certificates` off
and supplies an `EquivalenceProver`.
