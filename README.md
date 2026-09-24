# bitwright

[![CI](https://github.com/valeria-org/bitwright/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/valeria-org/bitwright/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/bitwright.svg)](https://crates.io/crates/bitwright)
[![docs.rs](https://img.shields.io/docsrs/bitwright)](https://docs.rs/bitwright)
[![book](https://img.shields.io/badge/book-read%20online-blue)](https://valeria-org.github.io/bitwright/)
[![MSRV](https://img.shields.io/badge/rustc-1.88+-orange.svg)](#stability)

Hash-consed fixed-width bit-vector expressions for Rust: exact evaluation, bit-level facts, and
verified simplification.

bitwright is for tools that reason about machine integers: binary analyzers, deobfuscators,
decompilers and lifters. It simplifies their expressions with predictable cost and without
guessing: a rewrite preserves the value of the expression at every input, or it does not happen.

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

fn main() -> Result<(), bitwright::Error> {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    for (input, simplified) in [
        // Arithmetic and boolean masking cancel.
        ("(x & y) + (x | y)", "x + y"),
        ("((x ^ 0x5a) + 3 - 3) ^ 0x5a", "x"),
        // Multiplying by an odd constant is a bijection: equal products, equal inputs.
        ("x * 0x87c37b91114253d5 == y * 0x87c37b91114253d5", "x == y"),
        // A comparison through a keyed hash mixer becomes a comparison of its input.
        (
            "let m = (x ^ 0xd3220fb78e33751f) * 0xd3220fb78e33751f; \
             (m ^ ((m >>u 32) >>u (m >>u 60))) * 0xd3220fb78e33751f == 0",
            "x == 0xd3220fb78e33751f",
        ),
    ] {
        let e = cx.parse(input, &o)?;
        let out = engine.simplify(&mut cx, e)?;
        assert_eq!(cx.display(out.expr).to_string(), simplified);
    }
    Ok(())
}
```

## What it gives you

- **Exact values** of 1 to 512 bits. Every operator has total SMT-LIB QF_BV semantics, division
  by zero included, checked against an independent bit-serial reference evaluator.
- **A hash-consed expression arena** with canonicalization at construction, owned by a context.
  There is no global state, and the same input gives the same output on every run.
- **Bit-level facts**: known bits, unsigned and signed ranges, tri-state proofs, and
  constraints you assume (a path condition, an invariant), with the ones each result relies on
  reported back.
- **A directed simplifier** built from normal-form passes (linear arithmetic, xor forms, truth
  tables, comparison lattices, casts, demanded bits, linear MBA, bit shuffles) and a small rule
  corpus. Termination is guaranteed by construction, and every run is bounded by budgets you
  choose.
- **Invertibility**: proofs that an expression is an injective or bijective function of a
  subexpression (keyed mixers, xorshifts, T-functions), used to cancel and solve equalities, so
  a hash comparison becomes a plain one.
- **A rule language (`.bwr`)** for your own rewrites, with a mandatory soundness check
  (exhaustive at small widths, sampled up to 512 bits) and proof ledgers.
- **Optional services**: MBA simplification (a native solver for linear, semi-linear and
  polynomial MBA, pluggable backends, and answers bitwright proves itself), a bounded
  equality-saturation search, and SMT-LIB export and import, so any SMT solver can prove a rule
  at any width.

## Performance

Measured on bitwright 0.5.0 with `cargo run --release -p bitwright-bench` (Rust 1.98, Linux, one
performance core of an Intel Core Ultra 7 265). Times are the fastest of 7 runs of the thread's
CPU time. Instructions retired are the suite's main metric: they don't move with machine load,
so they are what to compare a change by ([how the suite measures](docs/benchmarking.md)).

| Operation | CPU time | Instructions |
|-|-|-|
| A 64-bit value operation (add, mul, udiv, shl) | 8 ns | 157 to 169 |
| A 512-bit multiplication / division | 29 ns / 1.3 µs | 831 / 38,457 |
| Building a node (hash-consing and canonicalization) | 49 ns | 1,020 |
| Evaluating a node | 29 ns | 482 |
| The facts of a node, computed (known bits and ranges) | 0.41 to 0.53 µs | 5,610 to 6,780 |
| A cached fact query | 28 ns | 378 |
| Parsing a 60-node expression | 16 µs | 270,000 |
| Simplifying a random 40-node expression | 0.37 ms | 5.5 M |
| Simplifying in a fresh three-node context | 4.6 µs | 77,600 |
| Deobfuscating a linear MBA expression (native solver) | 0.37 ms | 4.9 M |
| Deobfuscating a nonlinear MBA expression (native solver, 64 bits) | 0.46 ms | 11.8 M |
| Building an engine (linking the built-in rules) | 76 µs | 1.5 M |
| SMT-LIB export / import, per node | 0.28 / 0.56 µs | 7,540 / 13,330 |

On the suite's MBA inputs the native solver shrinks 20 linear MBA expressions from 125 to 84
nodes and 20 nonlinear ones from 141 to 34 (the signature solver: 93 and 73). bitwright proves
every answer itself.

## Installation

```sh
cargo add bitwright
```

bitwright needs Rust 1.88 or later. Its only required dependency is `hashbrown`. Optional
features:

| Feature | Default | Adds |
|-|-|-|
| `check` | yes | the rule soundness checker, evidence and proof ledgers |
| `smtlib` | no | SMT-LIB export and import, rule obligations for any SMT solver |
| `mba` | no | the MBA service: lowering, the native normal-form solver, solver and prover traits, the evidence gate and its certificates |
| `cobra` | no | `mba` plus a backend over the `cobra-mba` crate |
| `eqsat` | no | a bounded equality-saturation search for alternative expressions |

## Documentation

**[The bitwright book](https://valeria-org.github.io/bitwright/)** is the guide. Every example
in it is compiled and run as a test. It reads fine on GitHub too:

| Part | Chapters |
|-|-|
| Basics | [Introduction](book/src/introduction.md) · [Getting started](book/src/getting-started.md) · [Semantics](book/src/semantics.md) |
| Reasoning | [Facts and proofs](book/src/facts.md) · [Constraints](book/src/constraints.md) · [Extension operations](book/src/extensions.md) |
| Simplifying | [Simplifying](book/src/simplifying.md) · [Deobfuscation and MBA](book/src/deobfuscation.md) · [Invertibility](book/src/invertibility.md) |
| Rules | [Writing rules](book/src/rules.md) · [Checking rules](book/src/checking.md) · [Rule catalog](book/src/catalog.md) |
| Services | [Equality saturation](book/src/eqsat.md) · [SMT-LIB](book/src/smtlib.md) · [The command line](book/src/cli.md) |
| Contracts | [Stability](book/src/stability.md) |

- **[API reference](https://docs.rs/bitwright)** on docs.rs, for the latest release.
- **[Design reference](docs/design.md)**: the principles, semantics and contracts, and how each
  part is validated.
- **[Changelog](CHANGELOG.md)**.

## Command line

The `bitwright` binary checks, lints and proves rule files, and simplifies expressions:

```sh
cargo install --git https://github.com/valeria-org/bitwright bitwright-cli
```

```text
bitwright check rules.bwr --ledger rules.bwr.proof      # soundness verdicts and the proof ledger
bitwright lint rules.bwr                                # every diagnostic, rendered
bitwright smt rules.bwr | z3 -in                        # prove every rule at 8, 32 and 64 bits (or `| bitwuzla`)
bitwright catalog > RULES.md                            # the built-in rules as Markdown
bitwright explain BW0302                                # what a diagnostic means
bitwright simplify '(x & y) * (x | y) + (x & ~y) * (~x & y)'   # x * y (nonlinear MBA, proved)
bitwright simplify 'x * k == y * k' --assume '(k & 1) == 1'   # x == y, relying on the assumption
```

## Stability

bitwright is 0.x. A minor release may change the API and simplification results, and lists
every change of results under *Behavior changes* in the [changelog](CHANGELOG.md); a patch
release changes results only to fix unsoundness. The minimum supported Rust version is 1.88.
See the [stability chapter](book/src/stability.md) for the full contract.

## Development

```sh
cargo test --workspace                                                  # every test, book examples included
cargo test --workspace --release -- --ignored --skip write_corpus_ledger    # the long suites (z3 and bitwuzla on PATH for the SMT proofs)
mdbook serve book                                                       # the book at http://localhost:3000
cargo run --release -p bitwright-bench                                  # benchmarks, in instructions retired
```

Fuzz targets are in [`fuzz/`](fuzz) (`cargo +nightly fuzz run simplify_dag`),
[`docs/benchmarking.md`](docs/benchmarking.md) explains how to compare a change against its
baseline, and [`compare/`](compare) compares bitwright with other symbolic engines (egg, CoBRA,
Triton, SMT solvers) on public MBA datasets.

## License

[PolyForm Noncommercial 1.0.0](LICENSE): free for any noncommercial purpose, including personal
use, research, education, and use by charitable and public organizations. Commercial use needs a
separate license from Emergentesombra Lda. (<https://emergentelabs.com/>).

Required Notice: Copyright 2026 Emergentesombra Lda., Porto, Portugal, PT 517806843
(https://emergentelabs.com/)
