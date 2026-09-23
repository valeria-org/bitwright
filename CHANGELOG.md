# Changelog

## Unreleased

- **MBA evidence.** The evidence gate proves answers itself beyond linear MBA: polynomial MBA
  of degree `d` at the points where the set bits of all variables lie in at most `d`
  positions, polynomials on a small grid, and expressions with right shifts, casts or
  arithmetic under bitwise operators through atoms paired between the two sides. The same
  checks are `mba::NativeProver`. The always-on refutation sample now includes the constants
  of both sides and their neighbours, and single bit positions. Evaluation is batched (256
  points per block). `MbaStats::certificates` counts what decided.
- **Behavior changes.** With the MBA service, answers that needed a trusted backend certificate
  are now accepted on bitwright's own proof where one applies (with `backend_certificates`
  off, more answers are accepted); answers wrong at a constant of either side are refuted
  earlier. A certificate that does not fit the remaining pass work leaves the node non-final.

## 0.3.1

- **Memory and cache.** A `BitVec` takes 72 bytes whatever its width, so the tables holding a
  value per node now pack widths up to 64 into words. Base facts are six words per node (a
  `Facts` is 432 bytes) in a table indexed by node instead of a hash map; facts under
  assumptions and the linear and xor passes' forms are packed the same way; the rewrite memo
  keeps result nodes in pages of node indices. On a 520k-node expression, facts take a ninth of
  the memory (231 MB to 25 MB); a simplification takes a fifth (421 MB to 78 MB) and 37 % fewer
  cycles, with a third of the L1 misses and a sixth of the last-level ones. On the benchmark
  suite, in instructions: `simplify/standard` −4.7 %, `simplify/mba` −3.4 %, facts −1.3 % to
  −11.5 %; `constraints/assume` +1.4 %, and creating an empty `Context` +38 instructions.
- **SMT-LIB.** `smtlib::import` checks the whole script's syntax, then reads and evaluates one
  command at a time instead of building the script's syntax tree first (tokens are borrowed,
  not copied): memory follows the largest command, not the script. The nightly 200,000-step
  chain's 1.9 GB script needed about 40 GB to import, and the test was killed; the whole test
  now peaks at 4.4 GB. `service/smt-import` is 36 % faster.
- **Behavior changes.** None: every result is the same.

## 0.3.0

- **Invertibility.** A layer may span several nodes: a *region* between a node and a node every
  varying path goes through, proved injective by a pivot analysis (per bit, the input bits it
  reads and those that flip it on their own; injective when every input bit can be recovered
  from an output bit in turn). This subsumes the triangular maps of 0.2.0 and adds
  block-triangular ones, such as a pointer encoding whose low bits are a bijection of the
  pointer's low bits and whose high bits, given those, are one of its high bits; solving at a
  constant also proves when there is no preimage. Two sides of an equality are anti-unified to
  find the pair of subterms they differ in. A product by a factor with known low zero bits keeps
  the other factor's structure (moved up), so `2 * (x & l)` no longer blocks the analysis.
- **SMT-LIB.** bitwuzla is a tested solver alongside z3: the nightly SMT suites (evaluation of
  exported expressions, the built-in rule proofs up to 512 bits, simplifications with extension
  calls, rewrites under the constraints they rely on) run once per solver, and CI installs
  bitwuzla 0.9.1. No exported script needed to change. The book's SMT-LIB chapter has a new
  section, *Solvers*.
- **Behavior changes.** More equalities are cancelled or solved by `Phase::Invert` (both
  built-in strategies): those through such regions.
- **Fixes.** Soundness: the invertibility analysis saturated rotation counts to 64 bits, so at
  widths over 64 a rotation by a variable count at or above `2^64` was modeled as a single
  rotation, and a map that is not injective could be accepted. At 128 bits, 0.2.0 turned
  `x ^ (rotl(x, y | 2^64) & m) == z ^ (rotl(z, y | 2^64) & m)` into `x == z`, which is wrong at
  `y = 0`, where the sides are `x & ~m` and `z & ~m`. Counts are now reduced modulo the width
  exactly.

## 0.2.0

- **Invertibility.** `Query::Injective` and `Query::Bijective` prove that an expression is an
  injective (bijective) function of one of its subexpressions, through a chain of layers: `~ -
  bswap bitrev`, `+ - ^` and rotations by anything, multiplication by a value proved odd,
  extensions and `concat`, extension outputs that declare it, and triangular maps `v ^ g(v)`,
  `v ± g(v)` decided from per-bit dependencies (the xorshift involution of murmur-style mixers,
  xorshift steps, T-functions). `Phase::Invert` uses them at `==` and `!=` only: `f(x) == f(y)`
  becomes `x == y`, `f(x) == c` becomes `x == f⁻¹(c)` or a constant when `c` has no preimage,
  and zero or-trees are solved leaf by leaf. Unlike the other passes it commits like a rule,
  whether or not the operands are shared. The book has a new chapter, *Invertibility*.
- **Facts.** A right shift by a value's own top bits is bounded (`a >>u (a >>u k)` is below
  `2^k`): the data-dependent xorshift of murmur-style mixers changes only its low bits.
- **Extension operations.** `ExtOp::invertible` and `ExtOp::invert` declare that an output is
  injective or bijective in one argument and give its inverse (default: nothing declared); the
  registration self-test checks both.
- **Behavior changes.** `Strategy::standard()` and `Strategy::deobfuscate()` run
  `Phase::Invert` after `Casts`, before `Compares`, so results change wherever they contain an
  equality through an invertible map (`x + 7 == y + 7` is now `x == y`). It costs 1.5 % to 2.6 %
  more instructions on the `simplify/standard` benchmarks; fact benchmarks are unchanged.
- **Tooling.** The nightly z3 proof of the built-in rules runs one solver per core, widest
  obligations first (423 s to 60 s on 20 cores).

## 0.1.0

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
  commit only when the DAG gets strictly smaller.
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
