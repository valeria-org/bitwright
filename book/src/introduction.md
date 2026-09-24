# Introduction

bitwright is a Rust library for machine-integer expressions: values of 1 to 512 bits, built from
the operators a processor has (arithmetic, bitwise logic, shifts and rotations, comparisons,
extensions and extracts, bit counts), and IEEE 754 floating point in any format, on the
bit-vectors that hold the encodings. It is for tools that reason about such expressions, for
example binary analyzers, deobfuscators, decompilers and lifters, and it can be used from C,
C++ and Python as well as Rust. It gives you three things:

- **Exact values.** Every operator has total semantics: the SMT-LIB QF_BV definition, including
  division by zero and shifts past the width. Any expression has exactly one value for every
  assignment of its symbols.
- **Facts.** For any expression, bitwright can tell which bits are known, which unsigned and
  signed ranges it lies in, and whether a comparison is provably true, provably false, or
  unknown.
- **Simplification you can trust.** Expressions are rewritten by rules that are checked
  (exhaustively at small widths and by sampling up to 512 bits) before they may be used, and by
  normal-form passes that decide whole fragments at once (linear arithmetic, xor forms, truth
  tables of three or fewer atoms, comparison lattices, linear mixed boolean-arithmetic). Every
  simplifier run is bounded by budgets you choose, and termination is guaranteed by
  construction.

For deobfuscation, bitwright undoes mixed boolean-arithmetic, linear and nonlinear, with its
own solver and proofs; folds opaque predicates from what is known about their operands; brings
back the comparisons that lifted flag computations stand for, integer and floating-point;
recognizes rotations, byte swaps and extensions in bit shuffles; and reduces checks of keyed
hashes to their one solution. It works under path constraints, and each result says which of
them it relied on.

## Ways to use it

- **As a library**, in Rust: build expressions or parse them, ask for facts and proofs, and run
  an engine of your choice (see [Simplifying](simplifying.md)).
- **From C, C++ and Python**, through the [bindings](bindings.md), with the same results.
- **From the command line**: `bitwright simplify` deobfuscates an expression, and the other
  commands check, lint and document rule files (see [The command line](cli.md)).
- **With your own rules**, written in a small language, checked for soundness before they can be
  used (see [Writing rules](rules.md)).
- **Next to an SMT solver**: expressions go out as SMT-LIB and come back in, and every rule has
  an obligation any solver can prove (see [SMT-LIB](smtlib.md)).

## What bitwright does not do

It does not guess. Input it cannot handle stays unchanged and is reported as such. A pass that
is not sure a rewrite is smaller does not make it, and an MBA answer from an external solver is
published only with evidence you accept. There is no global state, no environment variable
changes a result, and the same input gives the same output on every run.

## Features

| Feature | Default | Adds |
|-|-|-|
| `check` | yes | the rule soundness checker, evidence and proof ledgers |
| `smtlib` | no | SMT-LIB export and import, rule obligations for any SMT solver |
| `mba` | no | the MBA service: lowering, solver and prover traits, the evidence gate |
| `eqsat` | no | a bounded equality-saturation search for alternative expressions |

## This book

The chapters follow the order you are likely to need them: building and evaluating expressions,
their semantics, floating point, facts, simplification, writing and checking your own rules,
then the optional services, the command line and the bindings. [Examples](examples.md) and
[Examples in Python, C and C++](examples-bindings.md) are worked tasks from reverse
engineering, one per section, to start from. Every code example in this book, in every
language, is compiled and run as a test.
