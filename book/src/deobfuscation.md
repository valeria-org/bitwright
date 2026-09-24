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

1. the answer must have the input's variables and width and agree with it at 64 points
   (always): zero, all ones, one, the signed minimum, the constants of both sides and their
   neighbours, single bit positions, and seeded random values;
2. lifted back into the context, it must make the DAG smaller (checked before any proof, so
   an answer that would be rejected anyway is not proved);
3. then evidence, in order: bitwright's own certificates (below), a configured
   `EquivalenceProver`, the backend's own `Proved` or `Certified` claim if
   `MbaTrust::backend_certificates` is set (the default), or agreement at the sampled points
   if `MbaTrust::sampled` is set (off by default);
4. the lifted answer must agree with the original at seeded values of its symbols, and pass
   the usual postconditions and host veto.

bitwright's certificates are finite evaluation tests, each complete for its fragment:

- **linear MBA** (only 0 and all-ones constants inside bitwise parts): the values at the
  corners where every variable is 0 or all ones;
- **polynomial MBA** (sums of products of bitwise functions, any constants): the points where
  the set bits of all variables together lie in at most `d` bit positions, `d` the most bitwise
  factors in one product. For `(x & y)·(x | y) + (x & ~y)·(~x & y) = x·y` at 64 bits that is
  18,337 points;
- **polynomials** without bitwise operators: a small grid, `{0, 1, 2}` per variable for degree 2;
- every assignment when the variables total at most 20 bits;
- anything else through **atoms**: right shifts, casts and arithmetic under a bitwise operator
  are abstracted, paired between the two sides when they are provably equal (also as each
  other's complements, `x − 1` and `−x`, or when an atom's bits follow a bitwise function of
  its definition's leaves), and the two skeletons are compared by one of the tests above;
- **polynomials over symbols**: two sides that expand to the same polynomial in variables,
  conjunctions and other bitwise subterms are equal whatever values those take;
- **carries**: expressions built from `+ − ~ & | ^`, small left shifts and products by small
  constants are compared bit by bit, over every carry that can reach each position, which
  decides them exactly (`(y + y) & y & −y` is 0 at every width);
- when those leave the question open, a bitwise operation with a constant that reads only
  **known bits** of its other operand is read as arithmetic (`−2·(x & 1) | 1` is
  `−2·(x & 1) + 1`, the low bit being known to be 0), and a variable is split into **cases**
  over a few of its bits: the bits it is read through a narrow mask at (`x & 1`), or the low
  bits bitwise operations with constants read (`x ^ 1`), each case proved on its own.

A test is sized before it runs and charged to the pass-work budget; one that does not fit is not
started, and the node is asked again by a later call with more budget. `NativeProver` offers the
same checks to hosts that use the MBA module directly.

The phase asks about the largest fragment first: the question at the top of a fragment is asked
over the fragment as it is, and only when that answer is not taken are the pieces asked, inner
ones first, and the top again over them. A piece's answer can hide what only the whole shows (a
relation between two atoms that rewrites one factor of a product identity).

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
assert_eq!(cx.display(out.roots[0].expr).to_string(), "x + x + (x & y) + y");
# Ok::<(), Box<dyn std::error::Error>>(())
```

`NormalFormSolver` is bitwright's own solver beyond linear MBA. It reads bitwise functions
exactly at every width, one truth table per *bit class* (the positions every constant read by a
bitwise operator treats alike), so constants inside bitwise operators are no obstacle:
`(x ^ 0x10) + 2·(x & 0x10)` is `x + 0x10`, and `3·(x & 0x55) + 3·(x & 0xaa)` is `3·(x & 0xff)`.
Products of bitwise terms are multiplied out symbolically, so they cancel exactly:
`(x & y)·(x | y) + (x & ~y)·(~x & y)` is `x·y`, `2^63·(x·x + x)` is 0 at 64 bits, and a sum that
is a product comes out as one (`x·(x & y) + y·(x & y) − (x & y)²` is `(x | y)·(x & y)`).
Subterms it cannot see through become atoms: arithmetic under a bitwise operator (unless it is
secretly a bitwise function), right shifts and casts. Atoms with equal normal forms are one atom,
so `((x ^ y) + 2·(x & y)) & z` is `(x + y) & z` and `((x + y) & z) + ((x + y) & ~z)` is `x + y`.
A bitwise operation with a constant that reads only low bits of a polynomial that are known is
arithmetic again, so `(x + y)·(−2·(z & 1) | 1)²` is `x + y`; and an atom's definition that also
appears outside it is replaced by the atom, so `p + x + (x ^ 4) − ((x ^ 4) & p)`, with `p` any
polynomial, is `x + ((x ^ 4) | p)`.
Forms are also rendered as sums of two bitwise functions (in forms that share subterms, so
`−6·~(x | (y | z))` and the majority `(y & z) | (x & (y | z))` share `y | z`) or three, as a
bitwise function times an odd constant, group by group when their atoms fall apart, with a
bitwise function peeled off, and partly factored, so an obfuscation's pieces come back as
written: a 33-node obfuscation of `(d·a | (a ^ d)) + (a ^ (a + a))` from the QSynth dataset
comes back as exactly that. Atoms that depend on each other are seen through where a certificate
proves it: `((y + 1) & (~y + ~y)) | y | x` is `x | y`, and `−(x & −x)` is `x | −x`.
A normal form over at most three atoms is also looked up in a precomputed table of the
smallest expressions, so products the input has multiplied out come back: `x·y + x + y + 1` is
`~x·~y`, and `x² + 2·x·y + y²` is `(x + y)²`. A form from the table is used only when a
certificate proves it; one that no certificate can decide is returned, if at all, as a
sampled answer (`NfOptions::synthesis` turns the table off). Every answer is certified against
its input before it is returned, and the evidence gate checks it again. Its work is bounded by `MbaConfig::budget` (in steps: normal forms, renderings and
certificate evaluations); a question that needs more is answered `Exhausted`, counted, and left
for a later call with more budget. It remembers its recent answers (`NfOptions::memo`), which
saves time when the engine asks again and never changes an answer. It is not the library's
default solver: pass it to `mba_solver` (the command line's `simplify` uses it, on bitwright's
own evidence only). Of the 76,080 expressions of CoBRA's MBA datasets, it brings every one
whose ground truth agrees with its input (75,737) to the ground truth's size or less, 22,644
smaller; CoBRA itself reaches 85.0 % of them. See `compare/` in the repository.

```rust
use std::sync::Arc;
use bitwright::engine::{Engine, Strategy};
use bitwright::mba::{MbaConfig, MbaTrust, NormalFormSolver};
use bitwright::{Context, ParseOptions, Width};

let config = MbaConfig::default()
    .with_trust(MbaTrust::default().with_backend_certificates(false));
let engine = Engine::builder()
    .builtin()
    .strategy(Strategy::deobfuscate().with_mba(config))
    .mba_solver(Arc::new(NormalFormSolver::default()))
    .build()?;
let mut cx = Context::new();
let e = cx.parse("3 * (x & 0x55) + 3 * (x & 0xaa)", &ParseOptions::width(Width::W32))?;
let out = engine.simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "(x & 255) * 3");
# Ok::<(), Box<dyn std::error::Error>>(())
```

With feature `cobra`, `CobraSolver` asks the `cobra-mba` crate, which proves its answers with
Lean certificates by default. `ThreadedSolver` wraps any solver with a hard wall-clock deadline
per question (a late answer is abandoned and never cached). Trusting backend certificates means
trusting the backend: a host that needs independent evidence turns `backend_certificates` off.
Answers are then accepted only on bitwright's own certificates, which cover the fragments above,
or on the proof of an `EquivalenceProver` the host supplies for the rest.
