# Changelog

## 0.1.0 (unreleased)

The first release.

- **Values.** `Width` and `BitVec` for 1 to 512 bits, with total SMT-LIB QF_BV semantics for
  every operator (division by zero included), checked against an independent bit-serial
  reference evaluator.
- **Expressions.** `Context`: a hash-consed arena with canonicalization at construction, symbols,
  O(1) structural metadata, iterative traversal, evaluation, substitution (also bounded and
  resumable: `Context::substitute_bounded`, `Substitution`), and a text syntax (`parse`,
  `display`) that round-trips. Saturating arithmetic (`add_sat_u`, `add_sat_s`, `sub_sat_u`,
  `sub_sat_s`), wide products, carries and overflow flags as derived constructors, and trap
  guards for hosts that model faults (`traps::udiv`, `traps::sdiv`, `traps::shift`, …).
- **Facts.** Known bits and unsigned/signed ranges as a reduced product, computed lazily under a
  work cap, with transfers public for hosts (`Facts::apply_un/apply_bin/apply_cmp`,
  `KnownBits::apply_un/apply_bin`); tri-state proofs (`Context::prove`).
- **Constraints.** `Assumptions` holds 1-bit predicates (`assume_true`, `assume_false`) and facts
  (`assume`), numbered by `ConstraintId`, propagated backwards to operands, between comparisons
  of the same two expressions, and through equality classes. Results report the constraints they
  rely on (`RootOutcome::relies_on`, `Context::prove_under`, `Context::facts_under`, a
  `Reliance`); contradictions name theirs (`Assumptions::conflict`); sets fork cheaply by cloning.
- **Rule language.** `.bwr` rules and identities with width polymorphism, linear width
  constraints, monotone fact guards and `let`s; a compiler with stable diagnostics
  (`rules::explain`) and a Knuth–Bendix termination check; `bitwright::check` (feature `check`,
  default), the soundness checker (exhaustive at small widths, steered sampling to 512 bits),
  counterexamples, checked examples, and proof ledgers.
- **Simplifier.** `Engine` with ledger-linked rules, the built-in corpus, and
  `Strategy::standard()`: fact folding, rules, and the linear, xor, bitwise, compares, casts and
  demanded-bits passes. Caller-owned budgets and allowances, admission caps, deadlines, a memo of
  final results, telemetry, observers, host hooks, and postconditions on every rewrite. Passes
  commit only when the DAG gets strictly smaller (the invert pass, like a rule, when the
  termination order decreases).
- **Invertibility.** `Query::Injective` and `Query::Bijective` prove that an expression is an
  injective (bijective) function of one of its subexpressions, through a chain of layers: `~ -
  bswap bitrev`, `+ - ^` and rotations by anything, multiplication by a value proved odd,
  extensions and `concat`, extension outputs declaring `ExtOp::invertible`/`ExtOp::invert`, and
  triangular maps `v ^ g(v)`, `v ± g(v)` decided from per-bit dependencies (the xorshift
  involution of murmur-style mixers, xorshift steps, T-functions). `Phase::Invert` (in both
  built-in strategies) uses them at `==` and `!=` only: `f(x) == f(y)` becomes `x == y`,
  `f(x) == c` becomes `x == f⁻¹(c)` or a constant, and zero or-trees are solved leaf by leaf.
  Facts bound a right shift by a value's own top bits (`a >>u (a >>u k)` is below `2^k`).
- **Deobfuscation.** `Strategy::deobfuscate()` adds the linear-MBA pass (linear combinations of
  bitwise functions of up to six atoms, from their corner signature) and the shuffle pass (bit
  provenance of values assembled from slices).
- **Extension operations** (`bitwright::ext`). Host-defined total operations with 1 to 3
  arguments and 1 to 8 outputs (`ExtOp`), registered in a `Registry` after a contract self-test
  (`ext::check` runs it on its own; `RegistryBuilder::register_unchecked` skips it for operations
  a host tests once). Evaluation, facts, constraints, substitution, sampled verification, the
  text syntax (`@name[k](args)`) and SMT-LIB export go through the operation.
- **MBA service** (feature `mba`). `MbaExpr`, lowering and lifting, solver, prover and cache
  traits, the native `SignatureSolver`, `MemoryCache`, `ThreadedSolver` (a hard deadline around
  any solver), and `Phase::Mba` with an evidence gate. Feature `cobra` adds `CobraSolver`
  (cobra-mba 0.4).
- **Equality saturation** (feature `eqsat`). `Saturator`: a bounded search for alternative
  expressions over proven equations, with an in-crate e-graph, transactional publication per
  batch, shared allowances, a memo of stable outcomes, and built-in equations in groups.
- **SMT-LIB 2.6** (feature `smtlib`). `smtlib::export`, `smtlib::equivalence_query` (and
  `equivalence_query_under` for constraints), `smtlib::rule_obligation`, and `smtlib::import` of
  a QF_BV subset.
- **Tooling.** The book (`book/`), whose examples run as doctests; the built-in rule catalog; a
  command line for rule authors (`bitwright-cli`, not published); fuzz targets; and benchmarks
  measured in instructions retired (`bitwright-bench`, not published; `docs/benchmarking.md`).
- **License.** PolyForm Noncommercial 1.0.0; licensor Emergentesombra Lda.
