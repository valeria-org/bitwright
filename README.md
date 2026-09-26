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
- **Floating point**: IEEE 754 in any format (binary16 to binary256, bfloat16, x87's 80 bits,
  and any other), under all five rounding modes, exact and total (the canonical NaN, saturating
  conversions), in software: evaluation, expressions, facts and SMT-LIB, checked against an
  independent implementation on every input of every format up to 8 bits.
- **Bit-level facts**: known bits, an unsigned strided interval (the values `lo`, `lo + stride`,
  …, `hi`) and a signed range, each tightening the others, tri-state proofs, and
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
- **Verified compiler transformations**: peephole optimizations in the Alive syntax and pairs
  of LLVM IR functions are proved correct (refinement under LLVM's poison, undefined behavior
  and floating-point semantics, every width left open) or refuted with a small counterexample,
  and preconditions are inferred; by bitwright's own bit-blaster and SAT solver.
- **Optional services**: MBA simplification (a native solver for linear, semi-linear and
  polynomial MBA, pluggable backends, and answers bitwright proves itself), a bounded
  equality-saturation search, and SMT-LIB export and import, so any SMT solver can prove a rule
  at any width.

## Performance

bitwright 0.11.0 against other tools, each on what it is built for, on one performance core of
an Intel Core Ultra 7 265 (Linux, Rust 1.98). Every answer is read into bitwright, sized in DAG
nodes of its canonical form (a shared subterm counts once) and checked against its input; no
tool gave a wrong answer. [`compare/`](compare/README.md) reproduces the tables, and
[docs/benchmarking.md](docs/benchmarking.md#reference-numbers) has bitwright's own costs per
operation.

**Simplification, against z3 and Bitwuzla.** Random DAGs, 200 of each, over the
operators SMT-LIB has natively: arithmetic, bitwise operations, shifts, comparisons under
`ite`, truncations extended back, and in one row division, remainder and shifts by variable
amounts. Each tool starts from the same SMT-LIB text and is timed in process from it to its
answer, parsing included: bitwright's `Engine::standard()`, z3 5.1.0's `simplify` and Bitwuzla
0.9.1's `simplify_term`, with default settings. Nodes after simplification (the 200 summed) and
the median time per DAG. The floating-point rows are random DAGs of 40 operations over six
float atoms in SMT-LIB's FloatingPoint theory, with only what SMT-LIB specifies (arithmetic,
fused multiply-adds, roots, remainders, rounding to integral values, sign operations, format
round trips, choices on comparisons and tests); their answers are compared as SMT-LIB values:

| Random DAGs | Before | bitwright | z3 | Bitwuzla |
|-|-:|-:|-:|-:|
| 40 nodes, 8 bits | 10,895 | **9,223**, 0.18 ms | 63,134, 0.43 ms | 14,981, 0.17 ms |
| 40 nodes, 64 bits | 11,092 | **9,480**, 0.18 ms | 568,936, 2.2 ms | 15,331, 0.17 ms |
| 40 nodes, 64 bits, with division and variable shifts | 10,988 | **9,282**, 0.17 ms | 410,571, 1.4 ms | 16,005, 0.18 ms |
| 400 nodes, 64 bits | 59,852 | **52,365**, 1.6 ms | 3,691,595, 13 ms | 90,233, 0.67 ms |
| 40 floats, binary32 | 10,677 | **10,286**, 0.12 ms | 10,698, 0.20 ms | 11,650, 0.15 ms |
| 40 floats, binary64 | 10,686 | **10,305**, 0.11 ms | 10,707, 0.20 ms | 11,659, 0.15 ms |

bitwright's answer is the smallest of the three for all 800 bit-vector DAGs and for 392 of the
400 floating-point ones. The solvers are built to decide satisfiability, which bitwright
does not do, and they simplify toward that, not toward small expressions: z3 splits bitwise
operations with constants into slices of bits, and Bitwuzla writes `|` and `−` with `&`, `~`
and `+`, so their answers are almost always larger than the input. On 40 bit-vector nodes
bitwright and Bitwuzla take about the same time; on 400, Bitwuzla is 2.3 times faster. On floats
bitwright is the fastest.

**Identities, against z3 and Bitwuzla.** 651 identities in seven sets, written from textbook
mathematics and IEEE 754 rather than from any tool's rules ([`compare/facts/`](compare/facts)):
bit-vector algebra (Boolean algebra, ring arithmetic, two's complement, shifts, rotations,
extraction and extension, division, comparisons, if-then-else, known bits), number theory modulo
2^w, the unsigned and signed orders, bit slices, bit tricks, canonical forms and floating point
(sign operations, classification, comparisons, arithmetic, rounding, conversions); not mixed
boolean-arithmetic ones (those are CoBRA's datasets below). Each runs at 8 and 64 bits (floating
point in binary32 and binary64), over plain variables and over compound terms (2,604 cases),
from its unsimplified side, and is solved when the answer is no larger than the simpler side.
bitwright runs as the library's `Engine::standard()` and as the command line's `simplify` (the
MBA service and its normal-form solver on top). z3 and Bitwuzla prove every identity at 8 bits,
and at 64 bits all but three (quotient times divisor plus remainder, unsigned and signed, and
`(~x)² − x² = 2x + 1`), which neither finishes in ten minutes.

| Fact set | Cases | bitwright | bitwright `simplify` | z3 | Bitwuzla |
|-|-:|-:|-:|-:|-:|
| Bit-vector algebra | 1,508 | 1,434 | **1,500** | 780 | 636 |
| Number theory | 220 | 172 | **214** | 94 | 68 |
| Orders | 220 | **220** | **220** | 36 | 52 |
| Bit slices | 132 | 110 | **128** | 84 | 58 |
| Bit tricks | 140 | 108 | **140** | 31 | 15 |
| Canonical forms | 100 | 66 | 74 | **84** | 42 |
| Floating point | 284 | **260** | **260** | 180 | 208 |
| All | 2,604 | 2,370 (91 %) | **2,536 (97 %)** | 1,289 (50 %) | 1,079 (41 %) |

On these small expressions bitwright is also the fastest, with a median of 10 µs per case (12 µs
as `simplify`) against 71 µs for Bitwuzla and 99 µs for z3. `versus-smt --facts` prints
every group and what each tool misses. As `simplify`, bitwright misses the canonical forms of
long sums and products (reassociation, gathering constants), where z3 does better, and a few
cases of shifts, division, parity and extension; the library's standard engine alone also
misses distributivity, polynomial identities and the lowest-set-bit tricks, which `simplify`
solves. In floating point it leaves the six identities that hold only on values, not
on bit patterns (a NaN operand's payload is lost on one side): the rules for them apply only
on request (`--float-values`, `Strategy::with_float_values`), which these runs do not make.

**MBA, against CoBRA.** The MBA datasets [CoBRA](https://github.com/trailofbits/CoBRA)
collects: 76,080 expressions (SiMBA, GAMBA, NeuReduce, MBA-Obfuscator, MBA-Solver, QSynth,
Loki, OSES and others), 75,737 of them with a ground truth that agrees with the input. An
expression is solved when the answer is no larger than the ground truth; time runs from the
text to the answer, parsing included.

| Tool | Solved | The ground truth exactly | Median | 95th percentile |
|-|-:|-:|-:|-:|
| bitwright, `NormalFormSolver` | **75,737 (100 %)** | **49,856** | **0.21 ms** | **3.4 ms** |
| CoBRA (C++, af44b8a) | 64,396 (85.0 %) | 47,797 | 1.4 ms | 171 ms |

bitwright proves each of its answers itself; this is the configuration the command line's
`simplify` runs.

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
| `eqsat` | no | a bounded equality-saturation search for alternative expressions |

## Documentation

**[The bitwright book](https://valeria-org.github.io/bitwright/)** is the guide. Every example
in it is compiled and run as a test. It reads fine on GitHub too:

| Part | Chapters |
|-|-|
| Basics | [Introduction](book/src/introduction.md) · [Getting started](book/src/getting-started.md) · [Semantics](book/src/semantics.md) |
| Reasoning | [Facts and proofs](book/src/facts.md) · [Constraints](book/src/constraints.md) · [Extension operations](book/src/extensions.md) · [Memory](book/src/memory.md) · [Lifted code](book/src/lifting.md) |
| Simplifying | [Simplifying](book/src/simplifying.md) · [Deobfuscation and MBA](book/src/deobfuscation.md) · [Invertibility](book/src/invertibility.md) |
| Rules | [Writing rules](book/src/rules.md) · [Checking rules](book/src/checking.md) · [Verifying compiler transformations](book/src/transformations.md) · [Rule catalog](book/src/catalog.md) |
| Services | [Equality saturation](book/src/eqsat.md) · [SMT-LIB](book/src/smtlib.md) · [The command line](book/src/cli.md) · [C, C++, Python and JavaScript](book/src/bindings.md) |
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
bitwright prove opt.txt                                 # verify LLVM peephole transformations (Alive syntax)
bitwright tv before.ll after.ll                         # translation validation of LLVM IR functions
bitwright lift block.vex                                # lifted code (VEX, p-code, LLVM IR), deobfuscated
bitwright lean rules.bwr --at 8 > rules.lean            # the rules as Lean theorems (bv_decide proves them)
bitwright simplify '(x & y) * (x | y) + (x & ~y) * (~x & y)'   # x * y (nonlinear MBA, proved)
bitwright simplify 'x * k == y * k' --assume '(k & 1) == 1'   # x == y, relying on the assumption
bitwright simplify --file exprs.txt --jobs 8            # one expression per line, on 8 threads
```

## C, C++, Python and JavaScript

The same engine, from other languages: a C API (`bitwright-ffi`: a shared and a static
library, and [`bitwright.h`](bitwright-ffi/include/bitwright.h)), a header-only C++17 wrapper
over it ([`bitwright.hpp`](bitwright-ffi/include/bitwright.hpp)), a Python package
(`bitwright-py`, built with maturin), and a WebAssembly module with a JavaScript wrapper
(`bitwright-wasm`). They build, parse, inspect, evaluate and simplify expressions, with facts,
proofs, assumptions, budgets, rules of your own, SMT-LIB, memory, lifted code and the verifier
of compiler transformations, and have what a compiler needs: the compile strategy, declared
known bits, host rewrites as callbacks, templates, lowering and raising. The
[chapter on them](book/src/bindings.md) is the guide.
[`tools/plugins/`](tools/plugins/) has (untested) scripts for Ghidra, Binary Ninja and IDA.

```python
import bitwright as bw                   # pip install ./bitwright-py

cx = bw.Context()
x, y = cx.symbols("x y", 64)
print(((x & y) + (x | y)).simplify())    # x + y
print(bw.simplify("(x & y) * (x | y) + (x & ~y) * (~x & y)"))   # x * y
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
pip install ./bitwright-py pytest && pytest bitwright-py/tests          # the Python bindings
```

Fuzz targets are in [`fuzz/`](fuzz) (`cargo +nightly fuzz run simplify_dag`; `fp_dag` checks
floating point against the independent reference),
[`docs/benchmarking.md`](docs/benchmarking.md) explains how to compare a change against its
baseline, and [`compare/`](compare) compares bitwright with other symbolic engines (egg, CoBRA,
Triton, SMT solvers) on public MBA datasets.

## License

[PolyForm Noncommercial 1.0.0](LICENSE): free for any noncommercial purpose, including personal
use, research, education, and use by charitable and public organizations. Commercial use needs a
separate license from Emergentesombra Lda. (<https://emergentelabs.com/>).

Required Notice: Copyright 2026 Emergentesombra Lda., Porto, Portugal, PT 517806843
(https://emergentelabs.com/)
