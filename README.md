# bitwright

Hash-consed fixed-width bit-vector expressions for Rust: exact evaluation, bit-level facts, and
verified simplification.

bitwright is for tools that reason about machine integers, such as binary analyzers,
deobfuscators, decompilers and lifters. It aims to simplify such expressions with predictable
cost and without guessing.

- **Exact values** of 1 to 512 bits. Every operator has total SMT-LIB QF_BV semantics, including
  division by zero.
- **A hash-consed expression arena** with canonicalization at construction. It is owned by a
  context, and there is no global state.
- **Bit-level facts**: known bits, unsigned and signed ranges, and tri-state proofs.
- **A directed simplifier** built from normal-form passes and a small rule corpus. Termination is
  guaranteed by construction, and budgets are caller-owned.
- **Invertibility**: proofs that an expression is an injective or bijective function of a
  subexpression (keyed mixers, xorshifts, T-functions), used to cancel and solve equalities, so a
  hash comparison becomes a plain one.
- **A rule language (`.bwr`)** with a mandatory, machine-checked soundness gate.
- **Optional services**: MBA simplification with pluggable solvers, a bounded
  equality-saturation search, and SMT-LIB export and import (rule obligations included, so any
  SMT solver can prove a rule at any width).

## Documentation

The book in [`book/`](book) (`mdbook serve book`) is the guide: getting started, semantics,
facts, simplifying, writing and checking rules, deobfuscation, equality saturation, SMT-LIB, the
command line, and the built-in rule catalog. Every example in it runs as a test. The design
reference is [`docs/design.md`](docs/design.md).

## Benchmarks

`cargo run --release -p bitwright-bench` measures values, expressions, facts, constraints, the
simplifier and the services in instructions retired (hardware counters) and CPU time, so results
stay comparable on a busy machine; `--save` and `--compare` check a change against its baseline.
See [`docs/benchmarking.md`](docs/benchmarking.md).

## Command line

`bitwright-cli` builds a `bitwright` binary for rule authors:

```text
bitwright check rules.bwr --ledger rules.bwr.proof   # soundness verdicts and the proof ledger
bitwright lint rules.bwr                             # every diagnostic, rendered
bitwright smt rules.bwr | z3 -in                     # prove every rule at 8, 32 and 64 bits
bitwright catalog > RULES.md                         # the built-in rules as Markdown
bitwright explain BW0302                             # what a diagnostic means
bitwright simplify '(x ^ y) + 2 * (x & y)' --deobfuscate
```

## Status

Early development. The design is in [`docs/design.md`](docs/design.md), and the milestone plan is
in §13 of that document. Implemented so far:

| Milestone | Scope | State |
|-|-|-|
| M0 | `Width`, `BitVec` with every operator, independent reference evaluator | done |
| M1 | expression arena, canonicalization, text syntax | done |
| M2 | known bits, ranges, tri-state proofs, assumptions | done |
| M3 | rule language, soundness checker, seed rule corpus | done |
| M4 | simplification engine: budgets, memo, dispatch, telemetry | done |
| M5 | normal-form passes: fact folding, linear, xor, bitwise, compares, casts, demanded bits | done |
| M6 | deobfuscation: linear-MBA and shuffle passes, the MBA service (features `mba`, `cobra`) | done |
| M7 | equality-saturation search service (feature `eqsat`, default off) | done |
| M8 | SMT-LIB export, import and rule obligations (feature `smtlib`); CLI, book, catalog, fuzzing, semver job | done |

## License

[PolyForm Noncommercial 1.0.0](LICENSE): free for any noncommercial purpose, including personal
use, research, education, and use by charitable and public organizations. Commercial use needs a
separate license from Emergentesombra Lda. (<https://emergentelabs.com/>).

Required Notice: Copyright 2026 Emergentesombra Lda., Porto, Portugal, PT 517806843
(https://emergentelabs.com/)
