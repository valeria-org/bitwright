# Changelog

## Unreleased

- **A strategy for compilers, `Strategy::compile()`.** A compiler simplifies every value of
  every function. The standard strategy's passes weigh sharing against every root of a call,
  and a decision that sharing made is taken again for each root, so a call over every value of
  a function cost time growing with the function's size.
  - **`Strategy::sharing`** (`Sharing::Roots` by default): with `Sharing::Ignored` the passes
    decide as if each node's subexpressions were used by that node alone. Every result is
    final and memoized, and a value's result does not depend on the call's other values.
  - **`Strategy::max_region`** (1024 by default) caps how many nodes the passes examine to
    decide.
  - **`Strategy::compile()`** is the standard phases without demanded bits, one round,
    `Sharing::Ignored`, 64 nodes.

  On 200-instruction functions with every value a root it takes 1.4 ms, against 18.6 ms for
  the standard strategy (the same machine, CPU time), with results no larger on that
  workload. The book's *Simplifying* chapter has a section on it.
- **Cheaper calls on memoized values.** A phase whose memo holds the root answers without
  preparing a walk, and the walk's stack is reused: a call on an already simplified value costs
  about half what it did.
- **Cheaper construction.** Constants of 64 bits or fewer are interned from a word, and the
  canonicalizer's constant checks read words instead of building values: building SSA code
  takes about a quarter fewer instructions. `Context::reserve` makes room for a known number
  of nodes. The nodes built are the same.
- **Cheaper rule matching.** Whether a pattern node is closed (has no parameters) is computed
  when a rule compiles, not at every matcher step. The matcher's bindings and work lists stay
  inline instead of allocating on every attempt. Matching takes half the instructions it did,
  and a run of the rules alone a fifth fewer. The matcher's semantics and results are
  unchanged.
- **Declared known bits of symbols.** `Context::declare_known` states what the host knows of
  a symbol's value (a compiler's known bits of a parameter, a load, a call result, a value from
  another block) as part of its meaning. Facts, proofs and every simplifier phase use it, so
  an alignment check of an aligned pointer is true, and a zero-extended value's high half is
  zero. Unlike an assumption, it costs nothing per run.
  - A result is equal to its input wherever the symbols agree with their declarations.
  - Sampled verification and the equality-saturation check use points that agree with them.
  - SMT-LIB export asserts them, and `Context::import` carries them.
- **Cheaper facts up to 64 bits.** The transfers of addition, subtraction, `&`, `|` and `^`
  (and the carry chain) run on machine words for widths up to 64, the reduced product
  included, with the same results. A test compares them with the `BitVec` code. A
  compiler-shaped run takes about 6 % fewer instructions.
- **Rewrites in Rust, linked at run time.** `engine::Rewrite` is a rewrite the host writes in
  Rust: a name, a group, a revision, and a function from a node to its replacement through a
  `Site` (views, facts, construction).
  - **Linking.** `EngineBuilder::rewrite` links one with sampled verification at every
    application (it needs `allow_unproven`), and `trusted_rewrite` links one the host vouches
    for. A strategy runs it by naming its group in a rule phase; it is tried after the rules.
  - **Guarantees.** A result commits only when it is smaller in the order the rules decrease,
    so nothing cycles. It passes the rules' postconditions, a wrong one is quarantined for
    the call, and its work is charged to the budgets.
  - **Observability.** `Stats::host` counts host rewrites, and `By::Rewrite` names them to
    hooks and observers.
- **`check::rewrite`.** Tests a host rewrite offline, before it is trusted:
  - its results against their nodes, at every node of the given inputs, at every width they
    parse at, and with other constants (exhaustively over few bits);
  - width, determinism and the termination order;
  - typed failures with counterexamples.
- **`bitwright::translate`.** A host's IR in and out, without text:
  - `Semantics` for what an instruction computes;
  - `Lowering` for a function's values, with fresh (optionally declared) symbols for values
    defined outside;
  - `Raise` to emit instructions for the nodes no host value computes, value numbering
    included;
  - `Template` for semantics given as text at run time, compiled once per operand widths.
- **Book: *In a compiler*.** A chapter on translation, raising, templates, host rewrites and
  their checker, with tested examples.
- **Benchmarks: `compile/*`.** Functions as a compiler simplifies them: SSA values built
  through the builder, every value a root, one context reused. Rows for building, the rules
  alone, `Strategy::compile()` and the standard strategy, and memoized re-runs.
- **Behavior changes.** None: the default policy keeps every existing strategy's results and
  engine ids.

## 0.11.0

- **Floating point: `x / ½` is `x + x`.** Construction writes a division by one half as the
  sum, like `x · 2`: the same real number, rounded once in the same mode, so every result is
  the same bit pattern (½ is computed per format, subnormal where the exponent has two bits).
- **`simplify --rules`.** The command line's `simplify` takes rule files of your own
  (`--rules my.bwr`, repeatable), run after the built-in rules in every rule phase. A file is
  vouched for by the ledger `my.bwr.proof` next to it (as `check --ledger` writes it), or
  checked first; the command exits 1 when a rule is not sound or the ledger is stale.
- **Fuzzing floating point.** A new fuzz target, `fp_dag`, builds floating-point DAGs in tiny
  and standard formats (every operation, conversions through integers and other formats,
  comparisons and tests choosing between floats) and checks, at points with special values,
  that the built expression evaluates like the independent reference semantics applied
  operation by operation, that its facts contain every value, that the simplifier's results
  (standard, and deobfuscation with the MBA service) equal it, and that it survives SMT-LIB
  export and import. CI fuzzes it nightly with the others; `smt_import` has a floating-point
  seed.
- **More built-in rules**, for identities the comparison with z3 and Bitwuzla found missing
  (`compare/facts/`): `core.factor` takes shifts, rotations, extensions, truncations and
  extracts out of `&`, `|` and `^` (and left shifts out of `+` and `-`), and moves complements
  through arithmetic shifts and rotations; `core.select_idioms` simplifies selects whose arms
  share a term or repeat the condition, selects guarded by an equality, and the branchless
  choices `(x & m) | (y & ~m)`, `y ^ ((x ^ y) & m)` and `(x & -zext(c)) | (y & (zext(c) − 1))`
  with a mask of a condition (so the branchless minimum `y ^ ((x ^ y) & -(x <u y))` is
  `select(x <u y, x, y)`); `core.division` has the remainder of a value by itself, a
  remainder reduced twice, the division identities and signed division of a nonnegative value
  by a power of two; `core.sign_tests` reads the sign bit and sign mask (`zext(x <s 0)` is
  `x >>u (W − 1)`, `(x & smin) != 0` is `x <s 0`) and flips between signed and unsigned order
  through the sign bit; `core.bounds` decides `x & y <=u x`, `x <=u x | y`, shifts, quotients
  and remainders at most their dividend, a remainder below its divisor, the wraparounds of
  `x ± 1`, and the no-overflow sum of halves. `core.casts::trunc_and_zext` is gone: the new
  rules subsume it.
- **Orders of several terms.** The compares pass reads a combination of comparisons between
  up to five terms, and selects between them (minima and maxima however they are written), in
  every order the terms can stand in: constants in their own order, ranges the facts show
  apart, operations bounded by an operand (`x & y <=u x`, `x >>u s <=u x`, remainders and
  quotients) and monotone ones (`x <=u y` gives `x >>u 2 <=u y >>u 2`). A formula that has one
  value, equals one comparison of two terms or a part of itself, or a select that is always one
  term or the minimum or maximum of two, becomes that: transitivity (`x <u y & y <u z & z <=u x`
  is false), trichotomy, `~(x <u y) & ~(y <u x)` is `x == y`, and the lattice laws of minimum
  and maximum (`select(x <u y, x, y) == select(y <u x, y, x)` is true). Swapped arms under one
  condition combine (`min + max` is `x + y`).
- **Parity and squares.** Facts know the low bits of a square from its operand's: bit 1 of
  `x·x` is 0, an odd square is 1 modulo 8, and `(2^t·y)²` has `2t` low zeros. And the low bits
  of a polynomial (with bitwise operations and constant shifts) are read by residues: they are
  a function of its leaves' low bits, a small table over up to three leaves. So the demanded
  bits pass replaces an operand whose demanded low bits are a constant or equal a leaf's
  (`(x·x) & 1` is `x & 1`, `(x·x + x) & 1` and `x·(x+1)·(x+2)·(x+3)·32` are 0 at 8 bits), and
  the compares pass decides `e == c` when no residue of `e` matches `c` (`x·x == 2`,
  `(x·x & 7) == 5` are false).
- **Bit tests, sign extensions, concatenations, case splits.** `(x & 2^k) != 0` is
  `extract<k, 1>(x)` (and `== 0` its complement); the casts pass reads sign extension spelled
  `(x << c) >>s c` or `((x & 2^k − 1) ^ 2^(k−1)) − 2^(k−1)` as `sext(trunc<k>(x))`; new rules
  (`core.concat`) take a shared part out of `&`, `|` and `^` of concatenations, nest
  concatenations to the right, read shifts of a concatenation by its low part's width as an
  extension, and a zero low part `|` a zero-extended value as their concatenation;
  `core.single_bit` knows a power of two shares no bit with the value below it. And the linear
  pass splits an operation that reads a mask of a condition (`sext(c)`, `-zext(c)`, a sign
  mask) into `select(c, …, …)` when that is smaller: the conditional negation `(x ^ m) − m` is
  `select(c, −x, x)`.
- **Polynomial identities.** The compares pass expands `a == b` (and `!=`) over sums, products
  and constant left shifts of up to four leaves, and decides it when the polynomials are equal
  (`(x + y)·(x − y) == x·x − y·y`, the sum of cubes).
- **Floating point: more guarded rules, and floats as values on request.** `core.float` now
  divides a finite nonzero number by itself (1), subtracts a finite number from itself (+0,
  −0 toward −∞), takes the square root of a normal square to nearest (`|x|`), and widens and
  narrows back (`fp.not_nan`). A rule can claim its sides equal as floats, every NaN one value
  (`#[float_values]`, error BW0310 on a pattern without a float result): the checker and the
  SMT obligations compare them so, its id differs from the bit-exact rule's, and the engine
  applies it only when the strategy opts in (`Strategy::float_values`,
  `bitwright simplify --float-values`), verifying it modulo NaNs. The built-in
  `core.float_values` has `x · 1`, `x · −1`, `x + (−0)` to nearest, `min(x, x)`,
  `max(x, x)` and the round trip through a wider format. Rules may have four width variables
  (a conversion's two formats).
- **MBA: powers of a shifted variable.** The normal-form solver renders a polynomial in one
  variable of degree 4 or more that is `a·(x + s)^k + b` as that power, built by repeated
  squaring with the cheapest equivalent exponent (`y^k` repeats with period `2^(W−2)` from
  `k = W` on): the expansion of `(x − 1)^100` at 8 bits, which the normal form reduces to
  degree 9, is `(x − 1)^36`, 9 nodes (issue #5). Like every rendering it is certified against
  the question.
- **Linear maps over GF(2).** An expression built from one value by `^`, `~`, masks, shifts
  and rotations by constants, byte swaps and bit reversals is `M·x ⊕ c` over GF(2). The
  invertibility analysis now proves such a region injective when `M` has full rank, where the
  bit-by-bit pivot analysis gives up (`x ^ rotl(x, a) ^ rotl(x, b)`, which reads every bit
  three times), and solves it at a constant by elimination; `x ^ rotl(x, 3)`, not injective,
  stays. The xor pass writes such an expression as the xor of rotations masked by `M`'s
  diagonals when smaller: the xorshift involution `y ^ (y >>u 5) ^ (y >>u 7)` with
  `y = x ^ (x >>u 5) ^ (x >>u 7)` is `x`.
- **Round trips of extension operations.** `ExtOp::inverse` names another operation of the
  registry (with `ExtInverse`, `InverseArg`) that undoes an output in one argument; the
  registry checks it by sampled evaluation once both are registered, and the builder cancels
  the round trip (`dec(k, enc(k, x))` is `x`).
- **A native prover** (`bitwright::prove`, feature `prove`, on with `check`): expressions are
  bit-blasted into an and-inverter graph (every bit-vector operator with bitwright's total
  semantics; extension operations through their expansion), encoded as clauses, and decided by
  bitwright's own CDCL SAT solver (watched literals, VSIDS, first-UIP learning with
  minimization, Luby restarts, LBD-based clause deletion). `prove::equal`, `valid`,
  `valid_under` (with assumptions) and `satisfy` answer proved, refuted (with a counterexample
  checked by evaluation) or unknown (a conflict or size budget). A proof can come with a
  certificate: the clauses and a DRUP proof, checked by an independent forward checker
  (`Certificate::check`) and printable as DIMACS and DRAT for any other checker. Without a
  certificate, questions are first simplified by bitwright's engine, which settles what
  bit-level SAT finds hard (MBA products). Floating-point operations are blasted too (every
  operation of every format, under every rounding mode; the circuits agree with the reference
  semantics exhaustively in tiny formats and on special and random values in the standard
  ones).
- **Proving rules.** `prove::rule` proves a rule's obligation at chosen widths (guard, lets and
  fact predicates read as the SMT obligations read them), splitting a constant parameter into
  the constants its guard admits when the whole question runs out of budget, so `x / 2^k` is
  proved in binary16 and binary32. `prove::rule_all_widths` proves every assignment up to a
  bound, and settles a rule of bitwise operations for every width at width 1. The checker
  proves rules at widths too wide to enumerate on request (`CheckConfig::with_proofs`,
  `bitwright check --prove`: 8, 32 and 64 bits, binary16, binary32 and binary64): a rule with
  no assignment small enough to enumerate becomes sound by proof, and a refutation is a
  counterexample. With 20,000 conflicts per question, the built-in rules are proved at two
  assignments each of widths 4, 8 and 16 (577 proofs) but `select_swapped_mul` at 8 bits, and
  the floating-point rules in binary16, binary32 and binary64 but `x / 2^k` in binary64 and
  `√(x·x)` in binary32 and binary64.
- **Rules as Lean theorems.** `bitwright lean` (`rules::lean::lean`) writes rules as Lean 4
  theorems over `BitVec`, for every width (proofs `sorry`), or with `--at 8` at fixed widths
  proved by `bv_decide`, whose certificates Lean's kernel checks. Lean elaborates every
  statement of the built-in rules it can state (272 of 313: floating point, bit counts, `pdep`
  and `pext` are left out), and `bv_decide` proves all of them at 8 bits but two
  multiplication identities, which exceed its budget.
- **Verifying compiler transformations** (`bitwright::transform`, feature `prove`): that a
  target program refines a source program under LLVM's semantics, read from the language
  reference: values with poison (every poison-generating flag: `nsw`, `nuw`, `exact`,
  `disjoint`, `nneg`, `samesign`, `trunc nuw/nsw`), undefined behavior (division, `INT_MIN /
  -1`, branching on poison, `unreachable`, `llvm.assume`, `noundef`), and nondeterminism
  (`undef`, `freeze`, NaN signs and payloads, `nsz` zeros, `fmuladd`), chosen existentially by
  the source and universally by the target, decided by counterexample-guided search over the
  native prover. Two front ends: peephole transformations in the syntax of the Alive paper
  (`parse_transforms`, `bitwright prove`), with preconditions, constant expressions and types
  inferred and checked at every width left open (1 to 8, 16, 32, 64; half, float, double);
  and translation validation of LLVM IR function pairs (`pairs`, `bitwright tv`: integers and
  floating point, acyclic control flow with `phi` and `switch`, 35 intrinsics, the `noundef`,
  `range` and `nofpclass` attributes). Counterexamples are minimized (no poison where
  possible, 0, 1, −1, then few significant bits) and printed as LLVM IR constants.
  Preconditions are inferred from examples the prover classifies (`infer`, `bitwright
  infer`): `isPowerOf2(C)` for a multiplication as a shift, `C != 1 && !isSignBit(C)` for
  PR20186. Checked against LLVM itself: 800 random integer functions optimized by clang 21 at
  `-O2` all validate (and 59 of 60 floating-point ones, the last over budget); of 2,400
  mutations of the optimized functions, every counterexample is confirmed by an independent
  interpreter and random sampling finds no difference in the mutants judged valid. Of the
  fast-math flags, `nnan`, `ninf` and `nsz` are modeled; `reassoc`, `arcp`, `contract` and
  `afn` are not.
- **Lifted code** (`bitwright::lift`): front ends for Ghidra's p-code, VEX as pyvex prints an
  IRSB, and LLVM IR functions (loads, stores, `getelementptr`, `alloca` over one flat memory),
  each read into a block's inputs, final register values (x86-64's register parts by byte
  range), stores and exits. `bitwright lift` prints them deobfuscated.
- **Bindings for everything above.** Python: `equivalent`, `synthesize`, `saturate` (equality
  saturation, now in the package), `Memory`, `lift_pcode`, `lift_vex`, `lift_llvm`,
  `verify_transforms`, `validate_functions`, `infer_preconditions`, and engines with
  `float_values`, `refuse` (rules or passes vetoed by name) and `trace` (the rewrites of a
  run). C and C++: the same except equality saturation and traces (`bw_equivalent`,
  `bw_synthesize`, `bw_memory_*`, `bw_lift`, `bw_transform_*`,
  `bw_engine_builder_set_float_values`, `bw_engine_builder_refuse`). JavaScript: a WebAssembly
  module (`bitwright-wasm`, no bindings generator) and `bitwright.mjs`, strings in and out,
  tested under Node. Scripts for Ghidra, Binary Ninja and IDA (`tools/plugins/`, untested: none
  of the tools is available where bitwright is developed).
- **Synthesis** (`bitwright::synth`, feature `prove`): the smallest expression equal to a
  given one over its variables and constants, whatever its shape, by bottom-up enumeration
  with observational equivalence on sample points and counterexample-guided refinement, each
  answer proved by the native prover (`((x + y) & 1) ^ (x & 1)` is `y & 1`). `bitwright
  simplify --synth` runs it on the simplifier's result.
- **Memory** (`bitwright::memory`): loads and stores over an array from addresses to cells
  (bytes, usually; little- or big-endian), resolved at construction into bitwright's own
  operators, so every service works on code that reads memory. A load reads through the
  stores before it (store-to-load forwarding; a store at an address that may alias becomes a
  `select`; one base with constant offsets is decided by the offsets), known contents (read-only
  data: a constant, or a table selected by an index the facts keep in range), and unknown cells
  as symbols made consistent by address (two reads at equal addresses agree); pieces of one
  stored value reassemble into it, so a spill reloaded is the spilled value. `Memory::bind`
  gives the unknown cells their values from a memory image. SMT-LIB import reads arrays
  (QF_ABV: `select`, `store`) as memories.
- **Many expressions at once, on threads.** `Engine::run_each` simplifies each root on its own,
  as a call of `run` with that root alone would, on up to `Each::threads` threads: each root is
  copied into a context of its own, simplified there, and its result copied back. The results
  and statistics do not depend on the number of threads (200 random DAGs of 120 nodes: 197 ms
  with `run`, 139 ms with `run_each` on one thread, 31 ms on eight). `Each` takes a per-root
  budget, admission caps, assumptions and `Sync` hooks. `Context::import` copies expressions
  from another context through the constructors (symbols by key; extension operations need the
  same registry). `Stats::absorb` (and `MbaStats`, `CertStats`, `PassCounts`) add another
  call's counters. The command line's `simplify --file exprs.txt --jobs 8` simplifies a file of
  expressions, one per line; Python has `Engine.run_each(exprs, threads=…)` (the interpreter
  released), C `bw_engine_run_each`, C++ `Engine::run_each`.
- **Performance.** Against 0.10.0 (instructions, the benchmark suite): `simplify/standard`
  −11 to −13 %, `simplify/mba` −5 %, `simplify/mba-native` −17 %, `simplify/mba-nonlinear`
  −39 to −47 %, `simplify/mba-nonlinear-sig` −11 %, `value/udiv/512` −99 %, `value/mul/512`
  −38 %, `expr/eval/512` −60 %, `facts/cold/512` −19 %, `fp/sqrt/128` −46 %; `fp/simplify` +4 %
  and `simplify/tiny-context` +3 % (the new rules and passes, and the second look at several
  roots). One random DAG of 20,000 nodes −26 %; 200 roots in one call −55 %. The command line
  starts in 0.20 G instructions (0.10.0: 0.47 G). Where the time went:
  - the passes' commit rule decides which nodes stop being used by propagating counts from the
    replaced node (no scan of the region, no sort), marks the atoms in a dense set, and counts
    the uses the other roots of a call contribute once per root (it counted every root's DAG
    at every pass phase of every root);
  - the demanded-bits, linear and xor passes read only the known bits of the fact cache's two
    words instead of whole facts; the linear-MBA pass evaluates its signatures in words and
    walks in reused tables; the order, residue and GF(2) passes check cheaply before working
    (a sample of the orders, a sample of the residues, the one atom below a node, a rank that
    stops early);
  - wide division is Knuth's algorithm D instead of one bit per step, products form only the
    limbs they keep, and wide square roots start from the root of the top 128 bits;
  - the normal-form solver costs its candidates once and hashes its nodes in two words;
  - the built-in rules compile without repeating the checks their tests run.

  On versus-smt's corpora, one DAG per call, against 0.10.0: random 40-node DAGs +4 to +9 %
  (the new passes at work: their answers are smaller), 400-node DAGs −10 %, random float DAGs
  +15 %.
- **README and reference numbers, measured again.** Against z3 and Bitwuzla, bitwright's
  answer is the smallest for all 800 random bit-vector DAGs (0.10.0: 799) and 392 of the 400
  floating-point ones; on 400-node DAGs Bitwuzla is 2.3 times faster (was 2.7). The identity
  sets: 2,370 of 2,604 cases as the library (91 %, was 71 %) and 2,536 as `simplify` (97 %, was
  78 %); z3 1,289, Bitwuzla 1,079. CoBRA's datasets: every scored expression solved, 49,856 to
  the ground truth exactly, median 0.21 ms (was 0.26), 95th percentile 3.4 ms (was 4.1).
  `docs/benchmarking.md` has the new costs per operation.
- **Several roots: a second look.** `Engine::run` processes its roots one after another, and a
  rewrite that would not make the DAG smaller because another root still uses its subterms is
  not final; before, it was never reconsidered. Once every root is done, the roots with such a
  result are run again (while that changes something, at most three times; a root is skipped
  when nothing was rewritten after its result was reached), so the subterms the other roots
  have since stopped using can go. On the benchmark's nonlinear MBA inputs, 20 roots in one
  call, the results shrink from 31 nodes to 16 (0.10.0: 25) and on its linear ones from 85 to
  82 (0.10.0: 83); on calls of 20 and 100 random expressions, 94 and 114 of 12,000 results get
  smaller and none larger. It costs 4 % on `simplify/standard` and 6 to 17 % on the MBA
  benchmarks (instructions). The MBA phase also keeps each call's solver answers by question,
  so a question asked again (its answer not committed the first time) is not solved again.
- **Behavior changes.** The MBA service's defaults are the ones
  `docs/proposals/mba-defaults.md` proposed: the normal-form solver (`NormalFormSolver`)
  answers when the host sets no solver, and `MbaTrust::default()` no longer trusts a backend's
  certificates, so answers are accepted only on bitwright's own certificates or a configured
  prover's proof. Results of `Phase::Mba` with the defaults get smaller (nonlinear MBA is
  answered, not declined), at more cost on code that is not obfuscated; hosts keep the old
  behavior with `.mba_solver(Arc::new(SignatureSolver))` and
  `MbaTrust::default().with_backend_certificates(true)`. The command line and the bindings
  already used these settings; their results do not change.
  The new rules and passes (orders of several terms, parity and residues, bit tests and
  concatenations, case splits, polynomial identities, maps over GF(2), `x / ½`) change results
  wherever they apply, and so does the second look at several roots (on the corpora measured,
  only to smaller results); `core.casts::trunc_and_zext` is gone.

## 0.10.0

- **Floating-point guards.** Rules can ask the facts about a float: `fp.not_nan<E, S>(x)`,
  `fp.finite<E, S>(x)` and `fp.nonzero<E, S>(x)` are fact predicates (`FactPred::FpNotNan`,
  `FpFinite`, `FpNonZero`, the format's infinity as their second operand), true only when
  proven. So identities that hold only on ordinary numbers are rules: `x · 1 = x` if `x` is
  not a NaN, `x / x = 1` if it is finite and nonzero. The checker, the SMT obligations and the
  engine (from the operand's facts, read as floats) answer them.
- **Built-in floating-point rules.** A new group, `core.float`: division by a power of two is
  multiplication by its reciprocal (exactly: the same real number, rounded once, so every
  result is the same bit pattern), and on operands the facts show are numbers `x · 1` is `x`,
  `x · −1` is `−x`, adding a zero to a nonzero number or `−0` to anything (to nearest even)
  changes nothing, and `x == x`, `x <= x`, `min(x, x)`, `max(x, x)` fold. The rule catalog
  lists them. The rule constant `fp.max` is `fp.max_finite`, as `fp.max` is the operation.
- **Performance.** The MBA service's sparse certificates (the complete tests of nonlinear
  MBA) generate their points a column and a run at a time instead of one point at a time: the
  same points in the same order, with half the instructions for nonlinear MBA at 64 bits
  (`simplify/mba-nonlinear/64` −52 %, the normal-form solver's nonlinear corpus of
  `--corpus-diff` −48 %).
- **Book.** Two chapters of worked examples from reverse engineering: [Examples](book/src/examples.md)
  (MBA, encoded constants, opaque predicates, lifted integer and floating-point flags, bit
  shuffles, hash checks, floating point, path constraints, a rule of your own, batches, SMT-LIB)
  and the same tasks from Python, C and C++; every example runs as a test. The introduction,
  `Simplifying` (the ways to simplify, custom strategies), `Deobfuscation and MBA` (what
  besides MBA it handles), `Floating point` (the built-in rules) and `The command line`
  (`simplify` from the shell) are brought up to date.
- **Behavior changes.** Floating-point results change where the new rules apply.

## 0.9.0

- **Floating point.** IEEE 754 binary floating point on bit-vectors holding interchange
  encodings, in any format `(eb, sb)` (`FpFormat`: binary16, bfloat16, binary32, binary64,
  binary128, binary256, and any `2 ≤ eb ≤ 31`, `eb + sb ≤ 512`) and x87's 80-bit encoding
  (`x87_load`, `x87_store`), under the five rounding modes (`RoundingMode`). Total, portable
  semantics: correctly rounded results, the canonical quiet NaN for every NaN result, `min` and
  `max` as IEEE 754-2019 minimumNumber and maximumNumber (`−0 < +0`), conversions to integers
  saturating with NaN → 0, and sign-bit `neg`, `abs`, `copysign`. Exact software arithmetic,
  never the host's floating-point unit. `FpFormat` evaluates every operation on `BitVec`s;
  `Context::fp` (`FpOp`: add, mul, div, fma, sqrt, rem, round to integral, min, max, the
  comparisons, conversions between formats and to and from integers of any width) and
  `fp_sub`, `fp_neg`, `fp_abs`, `fp_copysign`, `fp_cmp`, `fp_test`, `x87_load`, `x87_store`
  build expressions (`View::Fp`), with exact identities at construction; the text syntax spells
  them `fp.add.rne.f32(a, b)` (every name starting with `fp.` is reserved). Facts bound
  floating-point results (a NaN possibility and an interval per sign), so the simplifier decides
  questions such as `fp.isnan` of an integer converted to a float. SMT-LIB export uses the
  FloatingPoint theory (`QF_BVFP`), and import reads it. The book's new chapter "Floating
  point" is the specification. Checked against an independent exact-rational implementation
  (exhaustively on every format of up to 8 bits), the host's binary32 and binary64, Bitwuzla and
  z3.
- **Facts.** Flipping or clearing the top bit (`x ^ smin`, `x & smax`) keeps the ranges exactly:
  the unsigned and signed ranges trade places, or the negative half moves down.
- **Performance.** Simplifying takes half the instructions it did. The passes' commit rule
  (does a candidate make the DAG smaller?) built hash sets and maps on every call and rebuilt the
  use counts of the whole DAG in one at every phase; they are now dense arrays the runner keeps
  and empties in constant time, with the same answers. Compiling rules (the built-in ones once
  per process: the command line's start) validates their widths without allocating and keeps
  where a one-width rule applies, so the matcher checks it with one load: `bitwright simplify`
  starts in 14 ms instead of 53. Floating point costs integer work nothing: a node's arity is
  one table load, the top-bit fact transfers are turned away on a known top bit before they
  build anything, a format packs into 16 bits, and SMT-LIB import reads indexed operators
  without allocating. Against 0.8.0 (instructions): `simplify/standard` −51 %, `simplify/mba`
  −32 %, `simplify/mba-nonlinear-sig` −28 %, `simplify/mba-native` −10 %, `expr/build` −3 %,
  `expr/eval` −8 %, `expr/substitute` −7 %, `facts/cold` −0.8 %, `service/smt-import` −1.2 %;
  none is slower.
- **Comparisons through functions, and of floats.** The compares pass combines comparisons of
  different terms when one is a function of the other it can invert on intervals (`x + k`,
  `k − x`, `−x`, `~x`, `x ^ smin`, `x & (2^j − 1)`, `x | smin`, extensions): so
  `(x - 4 <=u 5) | (x == 10)` is `x - 4 <=u 6`, and the floating-point classification tests,
  which compare `x & ~sign` or `x ^ sign`, combine on `x` (`fp.iszero(x) & fp.isnormal(x)` is
  false, the five classes cover every encoding). A floating-point comparison with a constant is
  a set of encodings and joins them, and two floats stand in one of six relations (equal, less,
  greater, unordered by either or both), of which every comparison of the two and the NaN test
  of either is a set: x86's `ucomiss` flags combined for `ja`, `jae`, `jb`, `jbe` come back as
  one comparison, `fp.lt(x, y) & fp.lt(y, x)` is false. A set is emitted as one integer or
  float comparison (or a negated one) when that is smaller.
- **Floating-point rules.** `.bwr` rules rewrite floating-point operations, written as in the
  text syntax with the format as width expressions (`fp.mul.r<E, S>(x, y)` over operands of
  width `E + S`, or a named format), with constants (`fp.one<E, S>`, `fp.inf.f64`, …) and
  rounding-mode parameters (`r: rm`, standing for all five modes). The checker checks such a
  rule in every format up to `(6, 6)` exhaustively and in wider ones by sampling, under every
  mode, and `bitwright smt` writes `QF_BVFP` obligations, one per mode. New in the rule IR:
  `RNode::Fp` (`FpNode`, `Rounding`), `Literal::Float` (`FloatLit`), `Rule::modes`,
  `Counterexample::modes`; `fp::FpKind` names an operation without its attributes. The book's
  chapter "Writing rules" has a section.
- **Bindings.** Floating point in C, C++ and Python: formats (`bw_fp_format`, `FpFormat`, the
  named ones), rounding modes, every operation, comparison and test, x87's load and store, and
  the inspection of floating-point nodes (`BW_KIND_FP`, `bw_fp_node_of`, `fp_node()`, and
  `format`, `to_format`, `rounding` in Python). The book's chapter "C, C++ and Python" has a
  section with an example in each language.
- **Behavior changes.** Results change where comparisons of related terms decide together: on a
  generated corpus of 4,000 combinations of comparisons, 214 results are smaller and none is
  larger; generated random DAGs and the integer identity sets of `compare/facts/` give the same
  results as 0.8.0.

## 0.8.0

- **C, C++ and Python.** bitwright can be used from other languages. `bitwright-ffi` builds a C
  library (`libbitwright`, shared and static) declared by `include/bitwright.h`, and
  `include/bitwright.hpp` wraps it for C++17 (objects own their C counterparts, errors are
  exceptions, expressions have operators). `bitwright-py` is the `bitwright` Python package
  (PyO3, one abi3 wheel for CPython 3.10 and later, typed). They build, parse, print, inspect,
  evaluate and substitute expressions of 1 to 512 bits; answer facts and proofs, invertibility
  included, under assumptions; and simplify with the standard or the deobfuscation engine (the
  command line's `simplify`), with budgets and with rule files linked through their proof
  ledgers; and export and import SMT-LIB. The book's new chapter "C, C++ and Python" is the
  guide, and its examples run as tests. `Expr::to_bits` and `Expr::from_bits` give a handle as
  one integer, for hosts that keep handles outside Rust; a context rejects bits it did not
  create, as it rejects any foreign handle.
- **Strided value sets.** A node's unsigned interval is a strided interval, the values `lo`,
  `lo + stride`, …, `hi` (`URange::stride`, `URange::strided`), and known bits and the intervals
  tighten each other both ways: known bits move each end of both intervals to the nearest value
  they allow (the odd values in `[4, 10]` are 5, 7 and 9) and give the stride their known low
  bits as a residue class (1 mod 4 and a stride of 3 make 9 mod 12), and the intervals give the
  known bits their bounds' common high bits and the stride's factor of two as low bits (3, 7, 11,
  15 all end in `11`). Strides follow arithmetic where it is exact: sums, differences, products,
  shifts, division and remainder by a constant, complements, negations, extensions,
  concatenations and selects. So `(x & 31) * 12 == 100` is false, and `urem((x & 31) * 12, 3)`
  and `urem((x & 7) * 6 + 1, 3)` are 0 and 1, which bitwright left as they were. The reduction
  runs on one or two machine words up to 128 bits (checked against the general code), so facts
  take about half the instructions they did: `facts/cold` −47 to −54 % at 8 to 128 bits,
  `facts/prove/64` −53 %, `constraints/facts-under/64` −45 %, `simplify/standard` −5.5 %;
  512-bit facts cost 18 % more. Cached facts are seven words instead of six. The bindings
  report the stride: `ustride` in C's `bw_facts` (after `umax`), C++'s `Facts` and Python's
  `Facts`.
- **Behavior changes.** Results change where a stride decides a comparison, a remainder or a
  mask that known bits and plain ranges left open. On the generated corpora of `--corpus-diff`
  and on the identity sets of `compare/facts/` the results are the same as before.
  `URange::contains`, `meet` and `join` respect the stride; `URange::new` is still a plain
  interval (stride 1).
- **Removed.** The `cobra` feature and its backend over the `cobra-mba` crate (`CobraSolver`,
  `CobraOptions`). bitwright's own `NormalFormSolver` answers, on its own evidence, every
  expression of CoBRA's datasets that CoBRA does. A host that wants another backend implements
  `MbaSolver` (and can bound it with `ThreadedSolver`). A public feature and types go, so this
  release is minor. `compare/` loses its `bw-cobra` tool; `cobra-cpp` (the C++ tool) and
  the `cobra` and `cobra-cert` tools (CoBRA's Rust port, called directly) remain for comparison.
- **README.** The Performance section compares bitwright with other tools, each on what it is
  built for: with the simplifiers of z3 5.1.0 and Bitwuzla 0.9.1 on random bit-vector DAGs
  (bitwright's answer is the smallest for 799 of 800; Bitwuzla is faster), and with CoBRA on
  CoBRA's MBA datasets (all 75,737 expressions with a ground truth solved, against 64,396). The
  table of bitwright's costs per operation moved to `docs/benchmarking.md`. Both are measured
  on 0.8.0.
- **Tooling.** `compare/`'s `versus-smt` (feature `native-smt`) runs bitwright's simplifier,
  z3's `simplify` and Bitwuzla's `simplify_term` in process, through their C APIs, from the
  same SMT-LIB text, on random DAGs over the operators SMT-LIB has natively, and reads every
  answer back into bitwright to size and check it.
- **Identities.** `compare/facts/` holds 580 identities in six sets, written from textbook
  mathematics: bit-vector algebra (377: Boolean algebra, ring arithmetic, two's complement,
  shifts, rotations, extraction and extension, division, comparisons, if-then-else, known
  bits), number theory modulo 2^w, the unsigned and signed orders, bit slices, bit tricks and
  canonical forms. `versus-smt --facts` runs them at 8 and 64 bits over atoms and compound
  terms (2,320 cases): `Engine::standard()` solves 1,578, bitwright as `simplify` runs it
  (`--deobfuscate`) 1,770, z3 1,109 and Bitwuzla 871. The README reports them by set.
  `--proofs DIR` writes each case's identity and bitwright's answer as SMT-LIB obligations.

## 0.7.0

- **Signed comparisons from flags.** The conditions a lifter computes from the flags of a
  subtraction (x86 `cmp`, AArch64 `subs`) simplify to the comparison they test: SF != OF is
  `a <s b`, SF == OF is `b <=s a`, and with ZF, `a <=s b` and `b <s a`. That holds in the
  spellings lifters use (sign tests, `ssub_overflow`, sign-bit extracts, sign bits shifted
  down, OF as a conjunction of sign tests) and for a constant operand on either side, at every
  width: `(a - b <s 0) != ssub_overflow(a, b)` is `a <s b`. The group `core.sign` merges sign
  tests (`(x <s 0) != (y <s 0)` is `(x ^ y) <s 0`, likewise for `^`, `==`, `&`, `|`, sign-bit
  extracts and shifts) and reads SF xor OF; `core.compare::ne_xor_zero` and the ported
  `ne_sub_zero` make `a - b != 0` into `a != b`, so the unsigned `hi` condition is `b <u a`.
- **Comparisons.** Complementing reverses the order, signed and unsigned: `~x <s ~y` is
  `y <s x`, and against a constant `5 <u ~x` is `x <u 250` (8 bits). Bits set in both
  operands outside their masks do not decide a comparison (`((x & m) | c) <s ((y & m) | c)`
  is `(x & m) <s (y & m)` when `m & c` is 0), nor the sign. `-(x | 1)` is `~x` when `x` is
  even, and `~x & y` is `y` when they share no bits.
- **Rules ported from Valeria** (PR #4): 94 rules in the `core.recovery_*` and
  `core.guarded_recovery_*` groups: MBA-style sums of `&`, `|`, `^`, carry and borrow
  comparisons, BMI2 `pdep`/`pext` cancellations, truncated arithmetic, shifts, min/max spelled
  with selects, field recombination, masks and guarded negation. Building a concatenation
  folds adjacent constants. The port's audit (`tools/valeria_rule_cases.py`, the example
  `valeria_rule_audit`, `docs/valeria-rule-coverage.md`) instantiates all 3,010 rules of
  Valeria's corpus as 28,134 cases: outputs larger than the rule's own reference fall from
  1,551 to 168 (standard) and from 1,427 to 110 (deobfuscate), and none is larger than
  0.6.0's. Rules that grew shared DAGs (a rule does not see an operand's other users) or
  reshaped MBA questions, and the port's extraction of constant shifts, were left out; the
  coverage document lists them.
- Every one of the 172 built-in rules is checked by `bitwright::check`, and z3 and bitwuzla
  prove every width the nightly proof exports up to 64 bits.
- **Behavior changes.** Results change wherever they contain a pattern of the new rules.
  Measured against 0.6.0: the generated corpora of `--corpus-diff` are no larger anywhere
  (linear MBA 1,673 to 1,672 nodes, random DAGs 9,094 to 9,087 at 8 bits and 9,466 to 9,463 at
  64); CoBRA's datasets are all still solved (`bw-nf`), with 47 answers smaller and 3 larger
  (`qsynth_ea` line 469, 6 to 7 nodes against a ground truth of 8, through
  `sum_from_double_or_xor`; OSES line 6, listed in two files, 58 to 67 against an input of
  76, through `complementary_shift_rotate`). `simplify/standard` costs 1.2 % more instructions
  and the MBA rows between 1.5 % more and 8.4 % less.
- **Building an engine** that links the built-in corpus costs 91 k instructions (6 µs) instead
  of 7.96 M (0.55 ms; 1.47 M in 0.6.0, with 37 rules instead of 172), so a host can build one
  per context. Compiling the corpus and checking it against its ledger already happened once
  per process; what remained was copying: each engine copied the rules three times, looked
  each one up in a copy of the ledger, and built the same dispatch net twice. Now the rules of a
  program, the rules the built-in ledger vouches for, and the built-in dispatch net are shared by
  every engine (phases with the same rules share one net). Cloning a `RuleProgram` no longer
  copies its rules. Results do not change.
- **Tooling.** The scheduled CI jobs pass again. `nightly-deep` never finished: Ubuntu's z3
  4.8.12 overruns its 5-second limit on a 512-bit `pext` (exported as 512 shifts by a counted
  amount) and was still on it when the runner shut down two hours later. The job now installs
  z3 5.1.0 from its release, as it does bitwuzla 0.9.1, and stops after an hour; the solver
  harnesses kill a solver that runs past twice its limit (the query counts as inconclusive),
  and each simplification query gets a solver of its own (17 s instead of 47 s). The fuzz jobs
  stopped at once on the missing `corpus/<target>` directory: they create it, keep the corpus
  between runs in the Actions cache, upload a crash's input, and fuzz five minutes per target
  instead of ten, stopping after ten. `workflow_dispatch` runs the scheduled jobs on demand.

## 0.6.0

- **Nonlinear MBA from the command line.** `bitwright simplify` deobfuscates by default: the
  rules, the normal-form passes and the MBA service with `NormalFormSolver`, every answer proved
  by bitwright itself (backend certificates are not trusted). `--standard` runs the rules and the
  standard passes only, as `simplify` did before; `--deobfuscate` is still accepted. So
  `-8*~y*(x&y) - 8*~y*(x&~y) + 10*~y*x + … + 1*(x^y)*~x` (the nonlinear MBA of the report that
  prompted this) prints `(~x ^ y) - y`, and `(x & y)*(x | y) + (x & ~y)*(~x & y)` prints `x * y`.
- **CoBRA's datasets.** Of the 76,080 expressions CoBRA collects (SiMBA, GAMBA, NeuReduce,
  MBA-Obfuscator, MBA-Solver, QSynth, Loki, OSES and others; see `compare/`), 75,737 have a
  ground truth that agrees with the input: the MBA service with `NormalFormSolver` on its own
  evidence answers every one of them no larger than the ground truth (22,644 smaller, 49,839
  the ground truth itself) and equal to the input at 64 points. The upstream C++ CoBRA
  (af44b8a) reduces 64,396 of them that far (85.0 %). The other 343 (337 lines
  without a ground truth, 6 whose ground truth disagrees with the input) are answered
  correctly too, 279 smaller than the input. 0.30 ms per expression at the median, 4.5 ms at
  the 95th percentile (CoBRA: 1.4 and 171 ms). `compare/`'s `bw-nf` tool runs that
  configuration, and `BW_FAILURES=FILE` lists the cases a bitwright tool leaves larger than
  the ground truth.
- **`compare/`.** Lines bitwright's parser declines are read in the datasets' own syntax
  (Python's operators and precedence, literals of any size modulo 2^64, `X[0]` names, a
  trailing note in words, a leading label, `(constant N)`): every line is read. A line whose
  ground truth holds only at a narrower width (some OSES lines are 8-bit arithmetic) is
  measured at the widest such width for bitwright's tools. Lines without a ground truth, or
  whose ground truth disagrees with the input at every width, are checked but not scored:
  the `no truth` column counts them and `reduced` those answered smaller than the input.
  `solved %` rounds down, so 100.0 means every scored line.
- **MBA evidence.** Two more tests, when the others leave a question open: equal polynomials
  over symbols (variables, the conjunctions of a bitwise function's leaves by its Möbius
  expansion, other bitwise subterms), which prove whatever values the symbols take, for
  polynomial sides no direct test fits (`CertStats::symbolic`); and a bit-serial comparison
  of expressions built from `+ − neg ~ & | ^`, small left shifts and products by small constants
  (T-functions: bit `j` depends on bits up to `j` through a few carries), exact over every
  reachable carry state, a difference always with a real counterexample (`(y + y) & y & −y` is
  0; `CertStats::carries`). Atoms get further: their complements join the pairing (`x − 1`
  and `−x`), an atom whose bits at the sample are a bitwise function of its definition's
  leaves has that function tried (and proved) as a member, a second skeleton reads such atoms
  as their functions and bitwise functions read arithmetically as their integer expansions,
  and an atom a side reads only linearly stands for its definition. Every skeleton is checked
  against its side at the sample, and every counterexample on the two sides, before either
  decides anything (a failure declines, counted in `CertStats::internal`).
- **Normal-form solver.** Sums of two bitwise functions (`c + a·g + b·h`, two to six atoms),
  scaled functions (`1111·x + 1111·k − 2222·(x & k)` is `(x ^ k)·1111`), independent groups of
  atoms rendered apart, a function of two or three atoms peeled off at an atom, tables of four
  to six atoms split on an atom, and functions whose bits do not all follow the classes
  (`g ^ k`). Of `p` and `−1 − p` one atom (the smaller constant); arithmetic that is a bitwise
  function once other atoms stand for their definitions, or whose bits at the sample follow
  one (`−(x & −x)` is `x | −x`, used once proved); conjunctions of dependent atoms that are
  zero, and atoms the form's values do not depend on over the patterns that occur, dropped
  once proved (`((y + 1) & (~y + ~y)) | y | x` is `x | y`); and two more forms of the function
  rendered beside it, a variable eliminated through an atom's definition and zero added to
  complete a bitwise function. A form whose atoms alone reach the question's size is not
  rendered, and an atom's definition only toward fewer nodes than the subterm. The solver's id
  is `bitwright.nf.v3`.
- **Normal-form solver, further.** Two bitwise functions of a sum rendered with forms that
  share subterms (the majority as `(y & z) | (x & (y | z))` beside `~(x | (y | z))`, and
  `~(y ^ n)` for `y ^ w` beside `n = ~w`), the minimum-form table keeping, per function,
  further forms that each bring a new subterm; a third term beside two (`(x & z) − 6·~((x &
  y) | (x ^ y ^ z)) − (x & y)`); tables of four or five atoms through a function of two or
  three of them (`~((d ^ s) | ((u | v) ^ d))`); a coefficient terms share taken out, a
  constant inside when a small multiple (`6·x − 6·y − 6` is `(x + ~y)·6`); nonlinear parts
  factored by a symbol most monomials share (`2·c·(a & c) − a·c − c² − a²` is `−(a ^ c)·c −
  a²`) and products divided by sums of the input's product operands (`(p & q)·(p | q) + (p &
  ~q)·(~p & q)` is `p·q` for bitwise `p`, `q` over atoms). Zero from one or two atom relations
  that makes the form a bitwise function (`(n & m) − 1` with `n = c − e`, `m = e − c` is
  `~(n | m)`); zero added to the form with atoms reused, so a coefficient splits between an
  atom and its definition (`(a·d | (a ^ d)) + (a ^ (a + a))`); a conjunction known to be zero
  in a class takes the others' coefficient there (`2·(~((y + y) ^ y) & 1) − (((y + y) ^ y) ^
  1)` is `1 − ((y + y) ^ y)`); a bitwise operation of two multiples of `2^k` read as `2^k`
  times one of their halves. Renderings are priced as the engine's rules leave them (`a − c`
  is `a + (−c)`; a `~(−x)` beside other uses of `−x` becomes `x − 1`, so `~(−x) ^ y` is built
  `~(−x ^ y)`). The other forms, later rounds and the fixed point only stop when the budget
  runs short (only the normal form's own rendering makes a question `Exhausted`), and the
  fixed point keeps an answer the certificates can follow. A reuse of a rendering costs its
  lookup, not the rendering's work again.
- **Engine.** The MBA phase asks the question at the top of a fragment first, over the fragment
  as it is (an answer to a part can hide a product identity only the whole shows), then walks
  the operands as before, asking the top again only if one changed; inside a chain of sums or
  products a link is not asked when its user is (a sum of `n` terms was `n` questions). Use
  counts forget replaced nodes and what only they used, so a smaller answer is no longer
  rejected for users that are gone; a constant always replaces the node it folds.
- **Passes.** The linear pass writes `2·a` as `a + a` (one node, where a shift needs its amount),
  takes the constant into a term when that is smaller (`−x − 1` is `~x`, `(y << 2) + 4` is
  `~y * −4`, `a + t + 1` is `a − ~t`, `2·t + 1` is `t − ~t`, `−1 − 2·x` is `~(x + x)`), starts
  a sum of subtractions from its constant or a product by a negative coefficient (`5 − x *
  3`, `y * −3 − z * 5`), and reads `concat(trunc(x), c)` as `x·2^|c| + c`, which the MBA
  fragment now takes too. The facts know `a + a`'s low bit.
- **API.** `MbaBudget::evidence` (default true): a caller that proves every answer itself asks
  without, and a solver may skip checking an answer it built exactly (`Claim::Unverified`);
  the engine does so when backend certificates are not trusted. `CertStats::symbolic` and
  `CertStats::carries`.
- **Performance.** In instructions against 0.5.0: `simplify/standard` −0.7 to −2.5 %,
  `simplify/mba` −0.2 %, `simplify/mba-native` −0.5 to −1.1 % (84 nodes become 83),
  `simplify/mba-nonlinear/8` +49 % and `simplify/mba-nonlinear/64` +208 % (its questions are
  asked whole first and its answers, now with atoms, proved over them; 34 nodes become 27),
  `simplify/mba-nonlinear-sig/64` +2.5 %; the rest within noise. On the corpus diff the
  default configuration takes up to 5 % fewer instructions (as many on nonlinear MBA); the
  proposed one 5 % more on linear MBA, 47 % more on nonlinear MBA at 8 bits and 2.4 times as
  many at 64, and 2.8 times as many on random DAGs (170.6 G against 60.2 G at 8 bits), for the
  searches above.
- **Fixes.** `NativeProver`'s id is `bitwright.native.v2`, as 0.5.0 announced (it kept
  `bitwright.native.v1`, so cache keys did not tell its evidence from 0.4's).
- **Behavior changes.** `MbaLimits::max_nodes` is 2,048 (was 256) and `min_nodes` 4 (was 5);
  `NfOptions::max_classes` and `max_degree` are 32 (were 16). The CLI, the solver and the
  passes change results as above. On the corpus diff the default configuration's results
  shrink from 9,142 to 9,094 nodes on random DAGs at 8 bits and from 9,511 to 9,466 at 64, and
  from 1,794 to 1,673 on linear MBA (nonlinear MBA unchanged); under the proposed
  configuration from 1,635 to 1,524 on linear MBA, from 1,005 to 901 on nonlinear MBA, and
  from 9,084 to 9,023 and from 9,477 to 9,414 on random DAGs. A rendering's reuse costs its
  lookup, so the budget goes further on questions whose products share factors.

## 0.5.0

- **MBA evidence.** When the other tests leave an equality open, the certificates read a
  bitwise operation with a constant as arithmetic where the constant reads only bits of the
  other operand that are known (`−2·(x & 1) | 1` is `−2·(x & 1) + 1`; known bits from the
  facts' transfer functions), and then split a variable into cases over a few of its bits (at
  most 16 cases, two variables deep): the bits it is read through a narrow mask at (`x & 1`),
  or the low bits that bitwise operations with constants read (`x ^ 1`, the variable standing
  for `(x << 1) + b`). Each case is proved on its own; a refutation in one case is a real
  counterexample. `CertStats::split` and `CertStats::known_bits` count them.
- **Native MBA solver.** A bitwise operation with a constant that reads only known low bits of
  a polynomial is arithmetic again, with no atom (`(x + y)·(−2·(z & 1) | 1)²` is `x + y`). An
  atom whose whole definition also appears arithmetically is reused there
  (`p + x + (x ^ 4) − ((x ^ 4) & p)` is `x + ((x ^ 4) | p)`). Two renderings span bit
  classes: a bitwise function with inputs complemented per class (`(x ^ 4) | p`), and unmasked
  atoms plus one bitwise function (`x + (x ^ 4)` for `2·(x & ~4) + 4`). `NfStats::known_bits`
  and `NfStats::reused` count them. The two examples of Arnau Gàmez i Montolio's talk "Mixed
  Boolean-Arithmetic Obfuscation: What We Build, What We Break, and What We Can't" (REcon
  2026) that the solver missed now reach their original size. The solver's id
  is `bitwright.nf.v2` and `NativeProver`'s `bitwright.native.v2`, so cached answers are not
  reused.
- **Passes.** The xor pass emits a constant that misses every mask as `| k`, each mask widened
  by it, when that leaves a mask out: `x | c`, which it reads as `(x & ~c) ⊕ c`, comes back as
  itself (it came back as `(x & ~c) ^ c`, one node larger, after an xor mask cancelled). The
  shuffle pass re-emits one source in place with constant bits as `(s & ~zeros) | ones`, not
  as a `concat` of slices (`((x >>u 2) << 2) | 3` is `x | 3`).
- **Normal-form solver.** A product over `NfOptions::max_degree` is an atom only when its
  degree stays over the cap after the exact reductions, which fold high powers into lower
  degrees at narrow widths (at 8 bits every power from `x^10` on). The question is first read
  with the certificates' known-bits reading when that leaves fewer bit classes, so a constant
  such as the `1` in `x·−100 | 1` (the core rules' spelling of `x·−100 + 1`) no longer splits
  them; `NfStats::lowered` counts such questions. The 101-term expansion of `(x − 1)^100` at 8 bits
  from the REcon talk now shrinks from 333 to 24 nodes under the defaults (the solver alone on
  the whole expansion gives 25).
- **Fixes.** A rewrite cycle in the engine's walk: a pass's result for a node is reused wherever
  the node appears, though the pass measured its decrease with the sharing where it ran, so a
  remembered result could rebuild a node a pass had just rewritten away, which the pass then
  rewrote again, until a budget stopped the call (the MBA phase did this 10,534 times on one
  node of the expansion above, with no net change). The walk now cuts such cycles in favor of
  the rewrite: in a pass's phase a node is not rebuilt into one a pass rewrote it from in the
  same call, and no node into one whose result is still being worked out;
  `Stats::cycles_cut` counts them.
- **Performance.** Recognizing a normal form as a bitwise function computed its atoms once per
  possible atom; now once. `simplify/mba-native` −0.5 to −0.8 % instructions and
  `simplify/mba-nonlinear` −0.2 to −1.1 %, the other rows unchanged; on the corpus diff the
  proposed configuration takes about 4.5 % more on random DAGs for the new rules, and the
  same on MBA corpora.
- **Behavior changes.** With the MBA service and backend certificates off, answers the gate
  could not prove before may now be proved and accepted. `NormalFormSolver` answers change as
  above. The xor and shuffle passes run in the built-in strategies, so default results change
  too: on the corpus diff's random DAGs the default configuration's results shrink from 9,146
  to 9,142 nodes at 8 bits and from 9,513 to 9,511 at 64 bits, at the same cost; the MBA
  corpora are unchanged. Under the proposed configuration (the normal-form solver, own
  evidence only) random DAGs shrink from 9,087 to 9,084 and from 9,480 to 9,477 nodes, one
  input growing by a node at 64 bits. A call that used to end on a rewrite cycle (by budget,
  or alternating between rounds) now completes on the rewrite's form.

## 0.4.1

- **Performance.** Charging work against a budget compares only the counter charged: every
  counter recorded after the fact is capped beforehand, so no other can be over (debug builds
  assert it). In instructions: `simplify/standard` −12.8 %, `simplify/mba` −8.1 %,
  `service/eqsat/32` −9 %, `simplify/tiny-context/64` −5.6 %, the normal-form solver's rows
  about −2 %; the others are unchanged.
- **Fixes.** A fact query under assumptions spent its cap on the overlay and again on each
  operand whose base facts it computed, so a call could spend more fact work than its budget.
  The overlay and the base facts now share the query's cap, and a query the cap stops answers
  `top` (as documented) and caches nothing. Results change only for calls that run out of fact
  work under assumptions.

## 0.4.0

- **MBA evidence.** The evidence gate proves answers itself beyond linear MBA: polynomial MBA
  of degree `d` at the points where the set bits of all variables lie in at most `d`
  positions, polynomials on a small grid, and expressions with right shifts, casts or
  arithmetic under bitwise operators through atoms paired between the two sides. The same
  checks are `mba::NativeProver`. The always-on refutation sample now includes the constants
  of both sides and their neighbours, and single bit positions. Evaluation is batched (256
  points per block). `MbaStats::certificates` counts what decided.
- **Native MBA solver.** `mba::NormalFormSolver` (with `NfOptions`, `NfStats`) simplifies
  linear, semi-linear and polynomial MBA from exact normal forms at full width: bitwise
  functions as truth tables per bit class (constants inside bitwise operators included),
  polynomials over masked conjunctions with exact reductions (coefficient precision, the
  falling-factorial null polynomials, one-position classes) and null parts dropped only when a
  certificate proves them zero, and the cheapest of many renderings (minimum forms, masked
  groups, indicator, conjunction and single-function forms, factored products). Subterms
  outside these fragments are atoms keyed by their own normal forms (arithmetic that is
  secretly bitwise is read as bitwise), each rendered once from its cheapest form. It certifies
  every answer itself, is never costlier than `SignatureSolver` on linear MBA, and answers are
  a fixed point (solving an answer again finds nothing smaller). Its work, rendering included,
  is bounded by the solver budget. Not the default solver; `docs/proposals/mba-defaults.md`
  proposes it (and backend certificates untrusted) as the default, with a corpus diff.
- **Memo.** `NormalFormSolver` remembers its last answers (`NfOptions::memo`, 1,024 by
  default), by question and budget: the engine asks some questions again as the expression
  around them changes, and a remembered answer is the one solving again would give. Rendering
  also renders each form once per product depth, charging the same work on reuse. Results are
  unchanged; on the corpus diff the proposed configuration takes about 30 % fewer instructions
  on random DAGs, and half to three quarters fewer on nonlinear MBA. The MBA benchmark rows now
  build a fresh engine per iteration, so no iteration is answered from an earlier one's
  memory.
- **Synthesis.** `NormalFormSolver` looks a normal form over at most three atoms up in a table
  of the smallest expressions (up to seven nodes over `+ − · & | ^ ~`, negation and the
  constant 1), keyed by their values at 24 fixed probe points and built once per process. A
  hit is used when a certificate proves it (`x·y + x + y + 1` is `~x·~y`); one no certificate
  can decide is at most a sampled answer. `NfOptions::synthesis` (on by default, part of the
  solver id); `NfStats::synth_*` count lookups, hits and their outcomes.
- **MBA solvers may see polynomials.** `MbaSolver::polynomial_fragments` (default false): a
  solver that returns true is also asked about fragments without bitwise operators in which
  two non-constants are multiplied, and fragments rooted at a constant left shift.
- **Benchmarks.** `simplify/mba-native`, `simplify/mba-nonlinear` and
  `simplify/mba-nonlinear-sig` measure the MBA service with each solver on linear and nonlinear
  MBA (the nonlinear corpus is generated in the repository). The MBA rows print what the work
  achieved and declined under their numbers. `bitwright-bench --corpus-diff` compares the
  current MBA defaults with a proposed configuration on generated corpora.
- **Behavior changes.** With the MBA service, answers that needed a trusted backend certificate
  are now accepted on bitwright's own proof where one applies (with `backend_certificates`
  off, more answers are accepted); answers wrong at a constant of either side are refuted
  earlier. A certificate that does not fit the remaining pass work leaves the node non-final.
  The gate checks that an answer would make the DAG smaller before proving it, so
  `MbaStats::not_smaller` also counts answers rejected for cost before any proof.
- **Tooling.** `compare/` compares bitwright with other symbolic engines on CoBRA's collection
  of public MBA datasets (about 76,000 expressions): egg (with bitwright's equations, and with
  MBA identities), CoBRA (the C++ tool through a batch driver, and its Rust port), Triton
  (through LLVM, and its synthesis), Z3, Bitwuzla, cvc5, claripy and Miasm. Every answer is
  checked at 64 points against its input and sized in bitwright's canonical form. It is its own
  Cargo workspace, run by hand; the datasets (mostly GPL-3.0) are fetched, not included.

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
