# Changelog

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
