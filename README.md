# bitwright

[![CI](https://github.com/valeria-org/bitwright/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/valeria-org/bitwright/actions/workflows/ci.yml)
[![crates.io](https://img.shields.io/crates/v/bitwright.svg)](https://crates.io/crates/bitwright)
[![docs.rs](https://img.shields.io/docsrs/bitwright)](https://docs.rs/bitwright)
[![book](https://img.shields.io/badge/book-read%20online-blue)](https://valeria-org.github.io/bitwright/)
[![MSRV](https://img.shields.io/badge/rustc-1.88+-orange.svg)](#stability)

A solver and simplifier for fixed-width bit-vector expressions, in Rust.

bitwright is for tools that reason about machine integers: binary analyzers, deobfuscators,
decompilers, lifters and compilers. It answers their questions at the level of words first
(facts, normal forms, and decision procedures for what obfuscators write) and falls back on a
circuit and a SAT search for the rest. It never guesses: a rewrite preserves the value of the
expression at every input, or it does not happen.

- [Quick start](#quick-start)
- [What you get](#what-you-get)
- [Benchmarks](#benchmarks)
- [Installation](#installation)
- [Command line](#command-line)
- [C, C++, Python and JavaScript](#c-c-python-and-javascript)
- [Documentation](#documentation)
- [Stability](#stability) · [Development](#development) · [License](#license)

## Quick start

```sh
cargo add bitwright
```

**Simplify.** Parse or build an expression, run an engine, read the result:

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

**Solve.** `bitwright::solve::Solver` keeps an assertion stack and answers with models and
unsatisfiable cores ([guide](book/src/solving.md)); the command line runs SMT-LIB 2 scripts the
same way:

```text
$ cat check.smt2
(set-logic QF_BV)
(declare-const input (_ BitVec 32))
(assert (= (bvmul (bvxor input #x5bd1e995) #x9e3779b1) #xdeadbeef))
(check-sat)
(get-value (input))
(assert (bvult input #x00001000))
(check-sat)

$ bitwright solve check.smt2
sat
((input #x431da30a))
unsat
```

**Deobfuscate.** `bitwright simplify` runs the deobfuscation strategy with the MBA solver, and
proves every answer it prints:

```text
$ bitwright simplify '(x & y) * (x | y) + (x & ~y) * (~x & y)'
x * y
$ bitwright simplify 'x * k == y * k' --assume '(k & 1) == 1'
x == y    # relies on 0
```

## What you get

**Sound by construction**

- Every operator has total SMT-LIB QF_BV semantics (division by zero and oversized shifts
  included), at 1 to 512 bits, checked against an independent bit-serial reference evaluator.
- Rules pass a mandatory soundness check before they can be used: exhaustive at small widths,
  sampled up to 512 bits, with proof ledgers; and each rule exports an obligation any SMT
  solver can prove.
- Input bitwright cannot handle stays unchanged and is reported as such. What it reads but
  does not model is refused, never ignored.

**Predictable**

- No global state, and no environment variable changes a result. The same input gives the
  same output on every run.
- Termination is guaranteed by construction, and every run is bounded by budgets you choose.
- One required dependency (`hashbrown`), and the library forbids `unsafe` code.

**The parts**

| Part | What it does | Guide |
|-|-|-|
| Expressions | A hash-consed arena owned by a `Context`, canonicalized at construction; exact evaluation, substitution, a text syntax | [Getting started](book/src/getting-started.md), [Semantics](book/src/semantics.md) |
| Floating point | IEEE 754 in any format (binary16 to binary256, bfloat16, x87's 80 bits), all five rounding modes, exact and in software; checked against an independent implementation on every input of every format up to 8 bits | [Floating point](book/src/floating-point.md) |
| Facts | Known bits, an unsigned strided interval and a signed range per node, each tightening the others; tri-state proofs; path conditions you assume, with the ones each result relied on reported back | [Facts](book/src/facts.md), [Constraints](book/src/constraints.md) |
| Simplifier | Normal-form passes (linear arithmetic, xor forms, truth tables, comparison lattices, casts, demanded bits, linear MBA, bit shuffles, divisions by constants, carry networks) and a small rule corpus | [Simplifying](book/src/simplifying.md) |
| Deobfuscation | Linear, semi-linear and polynomial MBA with a native solver whose answers bitwright proves itself; opaque predicates; flag computations back to comparisons; magic-number multiplications back to divisions | [Deobfuscation and MBA](book/src/deobfuscation.md) |
| Invertibility | Proofs that an expression is an injective or bijective function of a subexpression (keyed mixers, xorshifts, T-functions), used to cancel and solve equalities; strictly monotone maps do the same for orderings | [Invertibility](book/src/invertibility.md) |
| Solver | `push`/`pop`, checks with models, assumptions, unsatisfiable cores, deadlines. A check tries constants, independent slices, the last model, remembered answers and word-level repair before any circuit, then bit-blasting and CDCL; it reports which stage decided | [Solving](book/src/solving.md) |
| SMT-LIB | Export and import, and whole scripts run as a solver session, from a file or command by command through a pipe | [SMT-LIB](book/src/smtlib.md) |
| Rule language | `.bwr` files for your own rewrites, linted, checked, and exported as Lean 4 theorems | [Writing rules](book/src/rules.md), [Checking rules](book/src/checking.md) |
| Compiler verification | Alive-syntax peepholes and pairs of LLVM IR functions proved as refinements under LLVM's poison, undefined-behavior and floating-point semantics, or refuted with a small counterexample; preconditions inferred; DRUP certificates on request | [Verifying transformations](book/src/transformations.md) |
| Compilers and lifters | A compile strategy for SSA functions, host IR translation and host rewrites as callbacks; p-code, VEX and LLVM IR read into expressions; memory | [In a compiler](book/src/compilers.md), [Lifted code](book/src/lifting.md), [Memory](book/src/memory.md) |
| Traces | Every rewrite with the phase and round that made it, the rule or the pass's reasoning, the candidates dropped and the guards that failed, as JSON Lines, with a viewer | [workbench](workbench/README.md) |
| Equality saturation | A bounded e-graph search for alternative expressions | [Equality saturation](book/src/eqsat.md) |

## Benchmarks

Measured for bitwright 0.30.2 on one performance core of an Intel Core Ultra 7 265 (Linux,
Rust 1.98). In the comparisons every tool's answer is read into bitwright, sized in DAG nodes
of its canonical form (a shared subterm counts once) and checked against its input at 64
points. No tool gave a wrong answer in any run below. [`compare/`](compare/README.md)
reproduces the comparisons and [docs/benchmarking.md](docs/benchmarking.md) the engine's own
numbers.

### The engine's own costs

`cargo run --release -p bitwright-bench`; the fastest of 7 runs
([all rows](docs/benchmarking.md#reference-numbers)).

| Operation | CPU time |
|-|-:|
| A 64-bit value operation (add, mul, udiv, shl) | 7 to 8 ns |
| Building a node (hash-consing and canonicalization) | 44 ns |
| Evaluating a node of a DAG | 2 ns |
| The facts of a node, computed / cached | 0.11 µs / 28 ns |
| Simplifying in a fresh three-node context | 4.4 µs |
| Simplifying a random 40-node expression | 0.24 ms |
| Deobfuscating a linear / nonlinear MBA expression | 0.43 ms / 0.11 ms |
| An SSA function of 200 instructions, `Strategy::compile()` / again from the memo | 0.59 ms / 27 µs |

### Simplification, against z3 and Bitwuzla

Random DAGs, 200 per row, over the operators SMT-LIB has natively. Each tool starts from the
same SMT-LIB text and is timed in process from it to its answer, parsing included:
bitwright's `Engine::standard()`, z3 5.1.0's `simplify` and Bitwuzla 0.9.1's `simplify_term`,
with default settings. Each cell is the nodes after simplification (the 200 summed) and the
median time per DAG.

| Random DAGs | Before | bitwright | z3 | Bitwuzla |
|-|-:|-:|-:|-:|
| 40 nodes, 8 bits | 10,933 | **9,168**, 0.24 ms | 64,240, 0.44 ms | 14,981, 0.17 ms |
| 40 nodes, 64 bits | 11,137 | **9,439**, 0.25 ms | 572,271, 2.2 ms | 15,330, 0.18 ms |
| 40 nodes, 64 bits, with division and variable shifts | 11,041 | **9,293**, 0.23 ms | 412,472, 1.4 ms | 16,005, 0.18 ms |
| 400 nodes, 64 bits | 59,877 | **51,819**, 3.1 ms | 3,766,878, 13 ms | 90,232, 0.67 ms |
| 40 floats, binary32 | 10,677 | **10,253**, 0.17 ms | 10,698, 0.20 ms | 11,650, 0.15 ms |
| 40 floats, binary64 | 10,686 | **10,272**, 0.17 ms | 10,707, 0.20 ms | 11,659, 0.15 ms |

- **Size.** bitwright's answer is the smallest of the three for all 800 bit-vector DAGs and
  for 362 of the 400 floating-point ones. The solvers simplify toward deciding
  satisfiability, not toward small expressions (z3 splits bitwise operations with constants
  into slices of bits; Bitwuzla writes `|` and `−` with `&`, `~` and `+`), so their answers
  are almost always larger than the input.
- **Time.** Bitwuzla is the fastest: 1.4 times faster than bitwright on 40 bit-vector nodes,
  4.7 times on 400, and 1.1 times on floats. bitwright is faster than z3 in every row.

The floating-point rows are 40 operations over six float atoms in SMT-LIB's FloatingPoint
theory, with answers compared as SMT-LIB values.

### Identities, against z3 and Bitwuzla

651 identities in seven sets, written from textbook mathematics and IEEE 754 rather than from
any tool's rules ([`compare/facts/`](compare/facts)); mixed boolean-arithmetic ones are left
to the MBA datasets below. Each runs at 8 and 64 bits (binary32 and binary64 for floating
point), over plain variables and over compound terms: 2,604 cases. A case starts from its
unsimplified side and is solved when the answer is no larger than the simpler side.
bitwright runs twice: as the library's `Engine::standard()`, and as the command line's
`simplify` (the deobfuscation strategy with the MBA service).

| Fact set | Cases | bitwright | bitwright `simplify` | z3 | Bitwuzla |
|-|-:|-:|-:|-:|-:|
| Bit-vector algebra | 1,508 | 1,446 | **1,500** | 780 | 636 |
| Number theory | 220 | 172 | **210** | 94 | 68 |
| Orders | 220 | **218** | **218** | 36 | 52 |
| Bit slices | 132 | 118 | **128** | 84 | 58 |
| Bit tricks | 140 | 124 | **140** | 31 | 15 |
| Canonical forms | 100 | 74 | **86** | 84 | 42 |
| Floating point | 284 | **260** | **260** | 180 | 208 |
| All | 2,604 | 2,412 (92.6 %) | **2,542 (97.6 %)** | 1,289 (49.5 %) | 1,079 (41.4 %) |
| Median time per case | | **12 µs** | 20 µs | 99 µs | 72 µs |

What bitwright misses as `simplify`, 62 cases: 24 floating-point identities that hold only on
values, not on bit patterns (a NaN operand's payload is lost on one side; rules for them
apply only on request, with `--float-values` or `Strategy::with_float_values`), 14 canonical
forms of long sums and products, and 24 cases of shifts, division, parity, squares,
extension and monotone operations. The standard engine alone also misses distributivity,
polynomial identities and some lowest-set-bit tricks. `versus-smt --facts` prints every group
and each tool's unsolved cases.

### MBA, against CoBRA

The MBA datasets [CoBRA](https://github.com/trailofbits/CoBRA) collects: 76,080 expressions
(SiMBA, GAMBA, NeuReduce, MBA-Obfuscator, MBA-Solver, QSynth, Loki, OSES and others), 75,737
of them with a ground truth that agrees with the input. An expression is solved when the
answer is no larger than the ground truth; time runs from the text to the answer, parsing
included.

| Tool | Solved | The ground truth exactly | Median | 95th percentile |
|-|-:|-:|-:|-:|
| bitwright 0.30.2 | **75,665 (99.9 %)** | **50,543** | **0.09 ms** | **1.6 ms** |
| CoBRA (C++, af44b8a) | 64,396 (85.0 %) | 47,797 | 1.4 ms | 171 ms |

CoBRA's row is from an earlier measurement on another machine, not from this run.

- bitwright runs as the command line's `simplify` does (`NormalFormSolver`), and proves each
  of its answers itself, at every input.
- Of the 75,737 scored answers, 21,564 are smaller than the ground truth, 50,543 are the
  ground truth exactly, and 72 are larger (42 of them by one node). None is wrong and none
  failed.
- The score is deliberately not 100 %: earlier releases reported every expression solved, and
  some of those answers rested on assumptions bitwright no longer makes.
- Without the MBA service, the deobfuscation strategy solves 87.8 % and the standard strategy
  31.8 %, at medians of 0.07 and 0.09 ms.

## Installation

```sh
cargo add bitwright
```

bitwright needs Rust 1.88 or later. Its only required dependency is `hashbrown`. Every
feature is on by default; `default-features = false` leaves the core (expressions, facts,
the engine and its rules).

| Feature | Adds |
|-|-|
| `check` | The rule soundness checker, evidence and proof ledgers. Enables `prove` |
| `prove` | The native prover (bit-blasting, a CDCL SAT solver, DRUP certificates), the solver (`bitwright::solve`) and the verifier of compiler transformations |
| `smtlib` | SMT-LIB export and import, scripts run as a solver session, rule obligations for any SMT solver |
| `mba` | The MBA service: lowering, the native solvers, solver and prover traits, the evidence gate and its certificates |
| `eqsat` | A bounded equality-saturation search for alternative expressions |

## Command line

```sh
cargo install --git https://github.com/valeria-org/bitwright bitwright-cli
```

```text
bitwright simplify '(x & y) * (x | y) + (x & ~y) * (~x & y)'   # x * y (nonlinear MBA, proved)
bitwright simplify 'x * k == y * k' --assume '(k & 1) == 1'    # x == y, relying on the assumption
bitwright simplify --file exprs.txt --jobs 8            # one expression per line, on 8 threads
bitwright simplify '...' --trace run.jsonl              # every rewrite and why, for the workbench
bitwright solve script.smt2                             # an SMT-LIB 2 script as a solver (`-`: through a pipe)
bitwright lift block.vex                                # lifted code (VEX, p-code, LLVM IR), deobfuscated
bitwright prove opt.txt                                 # verify LLVM peephole transformations (Alive syntax)
bitwright tv before.ll after.ll                         # translation validation of LLVM IR functions
bitwright check rules.bwr --ledger rules.bwr.proof      # soundness verdicts and the proof ledger
bitwright lint rules.bwr                                # every diagnostic, rendered
bitwright smt rules.bwr | z3 -in                        # prove every rule at 8, 32 and 64 bits (or `| bitwuzla`)
bitwright lean rules.bwr --at 8 > rules.lean            # the rules as Lean theorems (bv_decide proves them)
bitwright catalog > RULES.md                            # the built-in rules as Markdown
bitwright explain BW0302                                # what a diagnostic means
```

The [command-line chapter](book/src/cli.md) has every command and option.

## C, C++, Python and JavaScript

The same engine, with the same results, from other languages:

| Language | Package | Entry point |
|-|-|-|
| C | `bitwright-ffi` (a shared and a static library) | [`bitwright.h`](bitwright-ffi/include/bitwright.h) |
| C++17 | header-only wrapper over the C API | [`bitwright.hpp`](bitwright-ffi/include/bitwright.hpp) |
| Python | `bitwright-py` (built with maturin) | `pip install ./bitwright-py` |
| JavaScript | `bitwright-wasm` (WebAssembly with a JavaScript wrapper) | [`bitwright-wasm/js`](bitwright-wasm/js) |

```python
import bitwright as bw                   # pip install ./bitwright-py

cx = bw.Context()
x, y = cx.symbols("x y", 64)
print(((x & y) + (x | y)).simplify())    # x + y
print(bw.simplify("(x & y) * (x | y) + (x & ~y) * (~x & y)"))   # x * y
```

The bindings build, parse, inspect, evaluate and simplify expressions, with facts, proofs,
assumptions, budgets, rules of your own, SMT-LIB, memory, lifted code and the verifier of
compiler transformations, and have what a compiler needs: the compile strategy, declared
known bits, host rewrites as callbacks, templates, lowering and raising. The
[bindings chapter](book/src/bindings.md) is the guide. [`tools/plugins/`](tools/plugins/) has
(untested) scripts for Ghidra, Binary Ninja and IDA.

## Documentation

**[The bitwright book](https://valeria-org.github.io/bitwright/)** is the guide. Every example
in it is compiled and run as a test. It reads fine on GitHub too:

| Part | Chapters |
|-|-|
| Basics | [Introduction](book/src/introduction.md) · [Getting started](book/src/getting-started.md) · [Semantics](book/src/semantics.md) · [Floating point](book/src/floating-point.md) |
| Reasoning | [Facts and proofs](book/src/facts.md) · [Constraints](book/src/constraints.md) · [Extension operations](book/src/extensions.md) · [Memory](book/src/memory.md) · [Lifted code](book/src/lifting.md) |
| Simplifying | [Simplifying](book/src/simplifying.md) · [Deobfuscation and MBA](book/src/deobfuscation.md) · [Invertibility](book/src/invertibility.md) · [Equality saturation](book/src/eqsat.md) |
| Solving | [Solving](book/src/solving.md) · [SMT-LIB](book/src/smtlib.md) |
| Rules | [Writing rules](book/src/rules.md) · [Checking rules](book/src/checking.md) · [Rule catalog](book/src/catalog.md) |
| Compilers | [In a compiler](book/src/compilers.md) · [Verifying compiler transformations](book/src/transformations.md) |
| Using it | [The command line](book/src/cli.md) · [C, C++, Python and JavaScript](book/src/bindings.md) · [Examples](book/src/examples.md) · [Examples in Python, C and C++](book/src/examples-bindings.md) |
| Contracts | [Stability](book/src/stability.md) |

- **[API reference](https://docs.rs/bitwright)** on docs.rs, for the latest release.
- **[Design reference](docs/design.md)**: the principles, semantics and contracts, and how each
  part is validated.
- **[Changelog](CHANGELOG.md)**.

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

- Fuzz targets are in [`fuzz/`](fuzz): `cargo +nightly fuzz run simplify_dag`; `fp_dag` checks
  floating point against the independent reference.
- [`docs/benchmarking.md`](docs/benchmarking.md) explains how to compare a change against its
  baseline.
- [`compare/`](compare) compares bitwright with other symbolic engines (egg, CoBRA, Triton,
  SMT solvers) on public MBA datasets.

## License

[PolyForm Noncommercial 1.0.0](LICENSE): free for any noncommercial purpose, including personal
use, research, education, and use by charitable and public organizations. Commercial use needs a
separate license from Emergentesombra Lda. (<https://emergentelabs.com/>).

Required Notice: Copyright 2026 Emergentesombra Lda., Porto, Portugal, PT 517806843
(https://emergentelabs.com/)
