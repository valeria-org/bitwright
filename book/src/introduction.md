# Introduction

bitwright is a Rust library for machine-integer expressions: values of 1 to 512 bits, built from
the operators a processor has (arithmetic, bitwise logic, shifts and rotations, comparisons,
extensions and extracts, bit counts). It is for tools that reason about such expressions, for
example binary analyzers, deobfuscators, decompilers and lifters. It gives you three things:

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
| `cobra` | no | `mba` plus a backend over the `cobra-mba` crate |
| `eqsat` | no | a bounded equality-saturation search for alternative expressions |

## This book

The chapters follow the order you are likely to need them: building and evaluating expressions,
their semantics, facts, simplification, writing and checking your own rules, then the optional
services. Every code example in this book is compiled and run as a test.
