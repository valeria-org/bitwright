# Benchmarking

`bitwright-bench` (an unpublished workspace member) measures bitwright's own operations.
The main metric is **user-space instructions retired**, not time.

```text
cargo run --release -p bitwright-bench -- --list            # what is measured
cargo run --release -p bitwright-bench                      # everything, 7 samples each
cargo run --release -p bitwright-bench -- facts simplify    # names containing "facts" or "simplify"
cargo run --release -p bitwright-bench -- --quick           # a tenth of the iterations, 3 samples
cargo run --release -p bitwright-bench -- --corpus-diff     # MBA defaults against the signature solver
```

## What is measured, and why instructions

Each benchmark reports its cost **per iteration**. The `per` column says what one iteration
is, for example "1024 ops", "1000 nodes" or "context". Three quantities are reported:

| Column | Meaning |
|-|-|
| `instr` | Median user-space instructions retired, from the CPU's hardware counters (Linux, `perf_event_open`). |
| `spread` | (max − min) / median of the instruction counts over the samples. It is the noise floor of that benchmark. |
| `cpu (min)`, `cpu (med)` | The thread's CPU time (`CLOCK_THREAD_CPUTIME_ID`): minimum and median over the samples. |
| `wall (med)` | Elapsed time, for reference only. |

Wall time is useless on a shared or busy machine. CPU time is better, but it still moves with
other load: shared caches and memory bandwidth, frequency scaling, and on hybrid CPUs whether
the thread ran on a performance or an efficiency core. The same run can differ by 4× between its
fastest and its median sample.

Instructions retired do not move with any of that. The count for a given workload is the same on
a performance core, an efficiency core, and a machine at full load. Two runs typically agree to
well under 1%, and the `spread` column says how well for each benchmark. The residue comes from
hash maps seeded per instance, which change probe sequences, and from allocator state.

On a hybrid CPU (separate `cpu_core` and `cpu_atom` PMUs), one counter is opened per PMU and the
counts are added. Each counter counts only while the thread runs on its kind of core. Kernel
instructions (system calls, page faults) are excluded.

Instructions are a proxy, not the truth:
- They do not see **cache misses**, **branch mispredictions** or **memory stalls**. A change that
  makes a data structure larger can keep the instruction count and still be slower.
- They weigh a division the same as an addition.

For any change that alters data layout or memory traffic, look at CPU time as well: compare the
**minimum** CPU times, and repeat on a quiet machine before believing a difference under ~5%.

If hardware counters are unavailable (another OS, a container, `perf_event_paranoid` above 2),
the tool says so and falls back to CPU time.

## Comparing a change against its baseline

Measure both sides yourself, with the same build settings, on the same machine. Do not compare
against numbers from another machine or an old report.

```text
git worktree add ../bitwright-base <base-commit>
(cd ../bitwright-base && cargo run --release -p bitwright-bench -- --save /tmp/base.csv)
cargo run --release -p bitwright-bench -- --compare /tmp/base.csv
```

`--compare` adds a column with the change of the median instruction count per benchmark. It
reports a change as `faster` or `SLOWER` only if the change exceeds both:
- the threshold (`--threshold`, default 1% for instructions and 5% for CPU time);
- twice the larger spread of the two runs.

Smaller changes are shown as a plain percentage. `--metric cpu` compares minimum CPU times
instead. `--fail-on-regression` exits with status 1 if anything got slower, for scripted checks.

When reporting a result, give the paired numbers, what was measured, and the correctness side:
the test suite passes on both commits.

## The benchmarks

| Group | Measures |
|-|-|
| `value/*` | `BitVec` arithmetic (add, mul, udiv, shl) at 8, 64, 128 and 512 bits; 1024 operations per iteration over fixed random and boundary operands. |
| `expr/*` | Building a 1000-node random DAG in a fresh context (hash-consing and canonicalization), evaluating and substituting it, parsing and displaying expressions, and creating an empty `Context`. |
| `expr/substitute-root`, `expr/unraised-owned` | Replacing an entire 10,000-node chain, and finding nodes to emit above an already-owned chain of that size. Measures pruning at replaced or host-owned values. |
| `facts/*` | Facts of every node of a fresh DAG (`cold`), a cached query (`warm`), proofs, and a fresh three-node context per query (`tiny-context`, the shape of a consumer that builds one context per instruction). |
| `constraints/*` | Assuming 40 predicates (orderings and masks), and facts under 40 assumptions. |
| `simplify/*` | The standard strategy on random DAGs; the deobfuscation strategy with the MBA service, bitwright's own evidence only: `mba` (the signature solver) and `mba-native` (the normal-form solver) on linear MBA, `mba-nonlinear` (normal-form) and `mba-nonlinear-sig` (signature) on nonlinear MBA; and one simplification in a fresh context. |
| `compile/*` | Functions as a compiler simplifies them (`workload::ssa_function`): 50 or 200 SSA instructions over four 64-bit parameters, every value a root, one context reused across functions (`clear` between them), built through the builder. `build` builds a function; `rules` runs the built-in rules alone for one round, `compile` `Strategy::compile()`, `standard` the standard strategy; `-rerun` runs the same roots again in the same context, where the memo should answer. One iteration is one function. See `docs/proposals/compiler-speed.md`. |
| `service/*` | Building an engine (linking the built-in rules, compiled once per process), equality saturation, SMT-LIB export and import. |

Workloads are generated from fixed seeds (`bitwright-bench/src/workload.rs`), so every run
measures the same expressions. The nonlinear MBA corpus is generated in the repository too
(`nonlinear_mba_corpus`): small targets (products, sums, bitwise functions) rewritten by MBA
identities at random, plus terms equal to zero that only nonlinear reasoning cancels. No
third-party dataset is vendored.

The MBA rows build a fresh engine for every iteration, outside the measurement: a solver that
remembers answers would otherwise answer every iteration after the first from memory.

Some benchmarks print a note under their row: what the measured work achieved and what it
declined, from one run outside the measurement. For the MBA rows it is the DAG size before and
after, the MBA service's answers (simplified, rejected as not smaller, no simpler, unsupported,
exhausted, unproved, refuted, refused as too small or with too many variables), and the proofs
bitwright ran itself, by test, with the points they evaluated. Declines are reported next to
successes: a faster row that simplifies less is not an improvement.

Setup that is not part of what a benchmark measures is excluded, for example building the DAG
whose facts are measured. It runs with the counters paused.

## Reference numbers

bitwright 0.11.0, `cargo run --release -p bitwright-bench` (Rust 1.98, Linux, one performance
core of an Intel Core Ultra 7 265). Times are the fastest of 7 runs of the thread's CPU time;
instructions are the median.

| Operation | CPU time | Instructions |
|-|-|-|
| A 64-bit value operation (add, mul, udiv, shl) | 8 ns | 149 to 161 |
| A 512-bit multiplication / division | 23 ns / 17 ns | 508 / 436 |
| A binary32 operation (add, mul, div, sqrt, fma) | 17 to 21 ns | 325 to 459 |
| A binary64 operation (add, mul, div, sqrt, fma) | 17 to 30 ns | 406 to 635 |
| A binary128 operation (add, mul, div, sqrt, fma) | 55 to 95 ns | 1,470 to 2,060 |
| Building a node (hash-consing and canonicalization) | 48 ns | 992 |
| Evaluating a node / a floating-point node | 27 ns / 46 ns | 442 / 777 |
| The facts of a node, computed (known bits and ranges) | 0.21 to 0.23 µs up to 128 bits, 0.43 µs at 512 | 2,610 to 2,990 up to 128 bits, 6,580 at 512 |
| The facts of a floating-point node, computed | 0.18 µs | 3,160 |
| A cached fact query | 28 ns | 380 |
| Parsing a 60-node expression | 16 µs | 281,000 |
| Simplifying a random 40-node expression (20 in one call) | 0.15 ms | 2.2 M |
| Simplifying a random 40-node floating-point expression (20 in one call) | 42 µs | 758,000 |
| Simplifying in a fresh three-node context | 3.8 µs | 69,300 |
| Deobfuscating a linear MBA expression (native solver) | 0.32 ms | 3.7 M |
| Deobfuscating a nonlinear MBA expression (native solver, 64 bits) | 0.38 ms | 9.1 M |
| Building an engine (linking the built-in rules) | 9.0 µs | 141,700 |
| SMT-LIB export / import, per node | 0.27 / 0.53 µs | 7,530 / 13,240 |

On the suite's MBA inputs the native solver shrinks 20 linear MBA expressions from 125 to 82
nodes and 20 nonlinear ones from 141 to 16 (the signature solver: 91 and 57).

## Corpus diff

`--corpus-diff` measures no instructions. It runs the deobfuscation strategy with the MBA
service on generated corpora (200 linear MBA inputs, 200 nonlinear MBA inputs and 200 random
DAGs, each at 8 and 64 bits) under three configurations: the defaults before 0.11 (the
signature solver, backend certificates trusted), the same solver with bitwright's own evidence
only, and the defaults since (the normal-form solver, bitwright's own evidence only). It prints
markdown: per corpus the result sizes, how many results change and in which direction, the
user-space instructions each configuration took (and its wall time, for orientation only), the
MBA service's answers and refusals, and examples of changed results. It was the evidence for
the change of defaults (`docs/proposals/mba-defaults.md`), and measures the MBA service's
answers whenever they change.

## Comparing with other engines

`bitwright-bench` measures bitwright against itself. [`compare/`](../compare/README.md)
measures it against other symbolic engines on public MBA datasets (CoBRA's collection, about
76,000 expressions): egg with bitwright's equations and with MBA identities, CoBRA (the C++ tool
and its Rust port), Triton (through LLVM, and its synthesis), Z3, Bitwuzla, cvc5, claripy and
Miasm. Every answer is checked against its input and sized in bitwright's canonical form, so
all engines are scored the same way: how often each reaches the dataset's ground truth, how
fast, and with how much heap. Its `versus-smt` compares bitwright's simplifier with the
simplifiers of z3 and Bitwuzla, through their C APIs, on random bit-vector DAGs over the
operators SMT-LIB has natively and on random floating-point DAGs, and on 651 identities in
seven fact sets (`compare/facts/`: bit-vector algebra, number theory, orders, slices, bit
tricks, canonical forms, floating point). It is its own Cargo workspace and needs the other engines
installed; its README has the setup. The top-level README reports both comparisons
([Performance](../README.md#performance)).

## Keyed mixers and fingerprints

`cargo run --release -p bitwright-bench -- --mixers > mixers.csv` is an opt-in staged report.
Add a case substring to select a family, for example `--mixers fingerprint` or `--mixers same-key`.
It covers same-key cancellation and inversion, a fixed four-key fingerprint on zero-extended
32-bit and unrestricted 64-bit inputs, separate masked-pair candidate/uniqueness queries,
a full-width three-pair guard, correlated target/key
exclusion, and a target-value superset above a shared predicate. Each runs with both shift
spellings, on the original expression and its standard-engine simplification.

Each case/spelling/mode runs in its own process. CSV rows measure simplification, native
`Question` preparation/search, primitive bit-blasting, CNF construction and search separately:
instructions, thread CPU and wall nanoseconds, AIG nodes,
CNF variables/clauses, conflicts, propagations, sampled assignments, current learned-clause
counts and process peak KiB (`VmHWM` on Linux;
`unavailable` elsewhere). The fixture adapter uses the prover's public bit-blast/CNF primitives;
a test compares its encoding counts with native `Question` preparation, allowing a checked
one-node proof when native preparation settles the outer Boolean structure early. Encoding retains clauses
and search logs proofs so every decided UNSAT certificate can be checked. Measurement excludes
external certificate checking and fixture witness replay; native API calls include their
mandatory internal counterexample validation. Process peak memory includes both and preparation.

Three resumed calls allow `(10 conflicts, 5,000 propagations)`, then `(40, 20,000)`, then
`(150, 75,000)` more work. A fresh search uses the sum `(200, 100,000)` for comparison; the second
encoding is outside that search's measurement. Counters are cumulative, including propagation
during CNF construction. Each call stops within its additional propagation allowance, completing
the current literal's watch list before pausing. Outcomes are
`proved`, `refuted-replayed` or `unknown-budget`; unknown is a result, not a failed benchmark.
Original-symbol counterexamples go to stderr and are evaluated against the original predicate.
This command uses one sample per stage and fixed budgets; regular benchmark options do not apply.

For the complete-query recovery target, run:

```sh
cargo run --release -p bitwright-bench -- --mixers fingerprint masked-pair-32-unique --query-budget-ms 10 > query-budget.csv
```

This mode asks each original fixture in a fresh native question, with both shift spellings.
The `native-query-total` measurement starts before circuit preparation and ends after
independent certificate checking or original-symbol model replay. Fixture construction and
process startup are outside the query measurement. There is no pre-simplified, supplied-input
or prepared-fact variant. Sampling and simplification are disabled; search gets 256 conflicts
and 75,000 propagations. Strategy flags still apply and are recorded in the mode column.
Every selected case runs even if an earlier case fails. Exit status is nonzero if any query
remains unknown or exceeds the requested wall time. The status column distinguishes
`unknown-within-time` from `unknown-over-time`, and checked decisions from either.
This is an observed acceptance target, not a clock-based cancellation guarantee. It cannot
be combined with escalation or word sampling. Empty filter selections are errors. Repeat
the command to assess run-to-run timing variation.

The native search uses `(200, 100,000)` too. Its preparation includes the bounded Boolean
overapproximation and can avoid expanding predicates that the primitive adapter always expands.
Native counters include work during CNF preparation, so the preparation row also reports its
initial propagation count.

Add `--escalate` to investigate unresolved native questions, for example:

```sh
cargo run --release -p bitwright-bench -- --mixers fingerprint cross-key-guards --escalate > unresolved.csv
```

After the initial native search, `native-small-samples` tries up to 65,536 systematic assignments
using `Config::with_sample_mode(SampleMode::Small)`. A found witness is replayed on the original
predicate and ends native escalation. `not-found` means only that these samples contained no
witness; the original input domain and original SAT question are preserved. The sample stage
includes its fresh circuit preparation and, on a miss, CNF construction. Four further calls
resume the original search with additional `(1,000 conflicts, 500,000 propagations)`,
`(10,000, 5,000,000)`, `(100,000, 50,000,000)` and `(1,000,000, 500,000,000)` allowances.
The final stage can take tens of seconds and retain a larger proof log. Certificate checking and model replay
remain outside the measured intervals. These optional stages use additional budgets; they
do not belong to the short resumed-versus-fresh comparison.

In a paired release measurement on 2026-09-30, the raw nested fixtures changed as follows:

| Fixture | AIG nodes before | AIG nodes after | Preparation instructions before | After |
| --- | ---: | ---: | ---: | ---: |
| Correlated target/key exclusion | 87,507 | 1 | 80.5 million | 0.09 million |
| Target-value superset | 87,507 | 1 | 80.5 million | 0.08 million |
| Zero-extended 32-bit fingerprint | 77,274 | 54,341 | 240.6 million | 89.1 million |
| Unrestricted 64-bit fingerprint | 87,507 | 60,342 | 267.7 million | 98.4 million |

These are single samples on one host, with certificate retention enabled and sampling and
word-level simplification disabled. Both dispatch certificates check independently. Both
fingerprint searches remain `unknown-budget`; smaller circuits do not establish reachability
or exclusion. Signed-digit multiplication reduces preparation work without narrowing the
declared input domain.
The integer gate-pair hasher and reused clause-normalization buffer reduce preparation
instructions by a further 28–31% compared with signed-digit multiplication alone, while
preserving node and clause counts. The budget fixes change where propagation-limited searches
pause; cumulative counts now stay within each call's additional allowance. These changes
improve preparation and budget control; they do not reduce the conflicts needed to solve
the remaining cross-key queries.

With majority/carry gate recognition, the narrow fingerprint's CNF drops from 29,397 variables
and 102,505 clauses to 17,478 and 74,694; the wide version drops from 32,093 and 112,425 to
17,924 and 79,364. Exhaustive polarity and sharing tests independently check the encoding and
UNSAT proofs. Fewer encoding variables do not establish a reduction in the conflicts needed
for these hard questions: both versions still report `unknown-budget` after the optional
first three resumed stages, with approximately 55 million propagations.
The final larger stage was also run on the raw nested versions: the narrow query remained
unknown after 290,446 conflicts and 555,421,873 cumulative propagations; the wide query after
539,351 conflicts and 555,557,168 propagations. That additional stage took approximately
45 and 52 seconds of thread CPU respectively, with process peaks of 179 and 264 MiB. These
are observations of budget exhaustion, not proof of either formula's verdict.

The full-width cross-key guard's small-sample stage does refute the original query:
`x = 0x4563` is found after 17,792 assignments, with zero SAT conflicts or CNF variables in
that stage. Both shift spellings and both expression modes replay the witness. The stage took
approximately 18–20 ms of thread CPU time in single measurements on this host. The library's
default remains random sampling; select the small-input search explicitly, for example:

```rust
use bitwright::prove::{Config, SampleMode};
let config = Config::default()
    .with_samples(65_536)
    .with_sample_mode(SampleMode::Small);
```

This explores a finite prefix of assignments to unknown input bits without restricting symbol
widths or assuming a finite prefix is exhaustive. Exhausted samples proceed to ordinary SAT;
proofs continue to require independently checkable certificates when requested.

The bounded fingerprint expectation is independently checked by a complete 2^32-input
masked-pair enumeration in `bitwright/tests/keyed_mixers.rs`: its sole necessary candidate is
`0x4563`, and the entire fingerprint there is zero, not the nonzero target. The 64-bit version has an open
expected verdict. No bounded-domain exclusion is asserted for it. A ground-truth expectation
does not require the native solver to decide a hard case under these short budgets.

Run ordinary regressions with `cargo test -p bitwright --test keyed_mixers`, and their two long
suites with `cargo test -p bitwright --release --test keyed_mixers -- --ignored --test-threads=1`.

### Masked relationships and selector decisions

Native preparation descends through asserted conjunctions and fixed XOR literals. In
particular, a zero target bit of an OR forces that bit of every operand to zero, exposing
signed bit equalities between mixer outputs. A one target bit retains its original coverage
constraint. A bounded signed union-find detects contradictory equality cycles; the resulting
unit and empty clauses are independently checkable RUP steps against the original CNF.
Additional transitive clauses also appear in the proof log, rather than becoming premises.
Traversal is bounded to 4,096 distinct literals, and extra lemmas to 1,024 clauses. Components
larger than eight vertices use a linear star instead of a quadratic clique.

Bitwise XOR normalization cancels small shared parity cones in the two low bits, where odd
constant multiplication is affine over XOR. Arithmetic carry networks retain their original
form. The cross-key low-two-bit identity is checked by native certificates for both shift
spellings. In paired short raw/nested measurements, native fingerprint search instructions
fell from 33.33 to 32.49 million (32-bit domain) and 33.24 to 32.36 million (64-bit domain),
approximately 2.5%; preparation instructions grew by roughly 0.5%. These searches used the
same 200-conflict allowance and all remained unknown.

Two optional strategies expose the remaining hypotheses for measured comparisons:

```rust
let config = Config::default()
    .with_relational_lemmas(true)
    .with_selector_branching(true);
```

The first adds transitive signed equalities. The second initially prefers the unknown bits
of shift counts with at most four unknown bits, allowing SAT to specialize the shift lazily.
It changes decision activity and initial phase, without assuming a selector value or
enumerating a Cartesian product of count values. Both options default to false.

```sh
cargo run --release -p bitwright-bench -- --mixers fingerprint masked-pair --relations --selectors --escalate-fast > relations.csv
```

`--escalate-fast` runs the sample stage and the first three resumed stages, omitting the final
500-million-propagation stage. Strategy choices appear in the CSV mode as `+relations` and
`+selectors`; the primitive adapter remains a control without these native preferences.
The `learned` column includes preprocessing lemmas and later retained SAT clauses, so it
can already be nonzero in a preparation row.

Single raw/nested measurements of the last 50-million-propagation stage on 2026-09-30 were:

| Query | Default CPU | Relations | Selectors | Both |
| --- | ---: | ---: | ---: | ---: |
| 32-bit fingerprint | 3.10 s | 3.04 s | 3.01 s | 3.22 s |
| 64-bit fingerprint | 3.09 s | 2.98 s | 3.11 s | 3.00 s |
| 32-bit masked-pair uniqueness | 3.53 s | 3.50 s | 3.46 s | 3.54 s |

All twelve searches remained `unknown-budget`, after roughly 55 million cumulative
propagations. The uniqueness fixture has about half the encoding (8,452 variables and
36,074 clauses), but this alone does not make it easy to prove. Its necessary candidate is
found and replayed separately; uniqueness is independently established only by the exhaustive
32-bit oracle. These single-host observations show mixed heuristic effects and do not justify
enabling either strategy by default or claiming a reduced search complexity.

### Remaining unknown queries: correlated shifts and input cancellation

The bit-blaster now recognizes a shift whose count shares Boolean literals with its data.
With at most four distinct unknown count literals, it considers all assignments to those
literals, treating other data as opaque. It folds an output only when every assignment makes
it constant or equal to a count literal (or its complement). Counts with larger support keep
the ordinary barrel circuit; repeated/complemented count bits and oversized shifts retain
their exact semantics. This is a circuit identity, not an assumption on the original domain.
For `(h >> 32) >> (h >> 60)` and `h >> (32 + (h >> 60))`, it exposes the four additional zero
bits at positions 28–31 before the second multiplication. Both forms prove the bound with
zero conflicts and independently checked certificates.

The raw nested fingerprint encodings lose 32 variables and 112 clauses each: the narrow
version becomes 17,448 variables / 74,590 clauses, and the wide 17,895 / 79,264. Preparation
instructions remain approximately unchanged. Searches still return `unknown-budget`;
these locally fixed bits alone do not settle the cross-key relationship.

An optional wider parity reduction removes a shared input occurrence along at most five XOR
levels of each operand, rebuilding only those paths. Unrelated sums/carries and separately
observed branches retain their values. It proves that paired dense odd products' high XOR
bit is independent of the input's high bit at widths 8, 32, 64 and 129 with zero conflicts.
Without the option, these certificate-mode questions remain paused under a zero-conflict
allowance. The full mixers still depend on that input through other paths, including the
self-selected shift, so this product identity does not make the full fingerprint independent
of the input bit.

```rust
let config = Config::default().with_input_cancellation(true);
```

```sh
cargo run --release -p bitwright-bench -- --mixers fingerprint masked-pair-32-unique --input-cancel --escalate > remaining.csv
```

The CSV mode includes `+input-cancel`; the primitive adapter retains default parity behavior
as a control. Input cancellation defaults to false because its circuit sizes and short-search
costs vary by workload. Single raw/nested measurements with the option on 2026-09-30 reached:

| Query | Verdict | Cumulative conflicts | Cumulative propagations | Final additional stage CPU |
| --- | --- | ---: | ---: | ---: |
| 32-bit fingerprint | unknown | 242,356 | 555,600,137 | 44.7 s |
| 64-bit fingerprint | unknown | 520,253 | 555,600,137 | 52.4 s |
| 32-bit masked-pair uniqueness | unknown | 603,358 | 555,550,281 | 69.7 s |

The final stage allows 500 million more propagations; proof logging is retained throughout.
Lower conflict counts at an exhausted propagation allowance do not establish less search is
needed. These measurements establish that the remaining queries still exceed these budgets,
even with a mathematically valid input cancellation. The complete 32-bit enumeration remains
the independent oracle for the bounded queries, rather than a native SAT certificate.

Both eager and lazy sum/carry propagation experiments were measured on the same unresolved
queries. Neither decided them, and both increased search instructions; their implementation
was removed. The retained changes are the generic correlated-shift identity, the opt-in
bounded input cancellation and their regression/measurement coverage.

### Peephole audit of the three hard queries

All three queries share the same odd-product/self-shift shape. A word-level fact gap was
found: the compact count `32 + (h >> 60)` previously lost the correlation that the nested
form retained. The range analysis now partitions the source using `count - offset` when
the offset cannot wrap, and shifts each partition by the actual count. Both spellings infer
`R <= 2^28 - 1` and 36 known high zeros. Small widths are exhaustive over shift positions,
constant offsets and source values, including the addition's wrapping boundary; wide bounds
are checked at 65, 129 and 512 bits. The bit-blaster already recognized these zero bits,
so this improves word-level analysis rather than further reducing raw native encodings.

The two fingerprint predicates additionally contain three XORs with the same mixer output.
At a single bit, this exact local identity applies:

```text
(a XOR b) OR (a XOR c) OR (a XOR d)
    = if a then NOT(b AND c AND d) else (b OR c OR d)
```

The conditional retains dependence on `a`; dropping the common XOR operand would be wrong.
Native preparation can factor the one-valued target bits this way, leaving zero-valued
target bits in their original fixed-XOR form for alias extraction. Compared with the prior
encoding, this removes 28 variables and 112 clauses from each fingerprint: 17,420 variables /
74,478 clauses for the narrow domain, and 17,867 / 79,152 for the wide domain. Original/shared
outputs retain their values, and all tested UNSAT certificates check independently.

```rust
let config = Config::default().with_join_factoring(true);
```

```sh
cargo run --release -p bitwright-bench -- --mixers fingerprint masked-pair-32-unique --factor-joins --escalate-fast > peepholes.csv
```

The option defaults to false and appears as `+factor-joins` in the mode column. Single
raw/nested measurements on this host show approximately unchanged preparation instructions,
and wide short-search instructions fall from 32.36 to 26.27 million (about 19%). At the longer
50-million-propagation stage, narrow search instructions increase about 2.3% and wide about
6.5%; all three queries remain unknown after roughly 55 million cumulative propagations.
A smaller encoding alone does not justify enabling this transformation by default.

The masked-pair uniqueness query has no three-term OR to factor, and its 8,436-variable /
36,018-clause raw nested encoding is unchanged. Its 36-bit mask includes a contiguous low
seven-bit prefix but also higher bits. At `x = 0x8d`, that low prefix is zero while the full
masked term is `0x1008654044890900`; discarding the higher bits changes the predicate.
Likewise, for the first key at `x = 0`, distributing its outer multiplication over XOR gives
`0x5a06e9c2fae93177` instead of `0x7666a7447033e507`. Both counterexamples replay on the
original DAGs for both shift spellings. Different keys prevent the common-parameter inverse
peephole from cancelling the full mixer pair; the remaining carries and masked cross-key
relationships require more than these local identities.

### Private parity intermediates and selector partitions

Most multiplier adders encode a three-input sum as two binary XOR gates, with two output
variables and eight ternary clauses. `Config::with_xor3_encoding(true)` can hide a private
intermediate and encode the same parity using one output variable and eight four-literal
clauses. Separately observed intermediates or inner products prevent fusion. Single-use
outputs retain their binary operands for root-conditioned alias extraction. Initial watches
follow the output and the outer input (typically the incoming carry); clause normalization
and certificate premises retain their original meaning.

```sh
cargo run --release -p bitwright-bench -- --mixers fingerprint masked-pair-32-unique --xor3 --escalate-fast > parity.csv
```

The option defaults to false; CSV modes include `+xor3` and the primitive adapter remains a
control using the default encoding. Raw nested variable counts change as follows:

| Query | Default variables | Three-input variables | Clauses in either encoding |
| --- | ---: | ---: | ---: |
| 32-bit fingerprint | 17,448 | 13,234 | 74,590 |
| 64-bit fingerprint | 17,895 | 12,907 | 79,264 |
| 32-bit masked-pair uniqueness | 8,436 | 6,413 | 36,018 |

This removes 24–28% of variables and approximately halves short fingerprint search
instructions in single raw/nested measurements on this host: 32.49 to 13.94 million for
the narrow query, and 32.36 to 13.61 million for the wide query, both under 200 conflicts.
Short masked-pair search instructions fall from 35.04 to 25.62 million. Clause count stays
fixed, but the eight parity clauses now contain four literals rather than three, so literal
storage and inspection can grow. At the longer 50-million-propagation stage, instructions
increase about 11%, 28% and 17% respectively; every query still exhausts its budget. These
mixed measurements justify retaining the original default.

The independent partition experiment fixes the first mixer's selector, `h >> 60`, to each
value 0–15 as a predicate assumption. A checked range certificate establishes the complete
selector range. Each conditional question retains the original 32-bit or 64-bit input width
and declarations, and receives up to 10,000 conflicts / 5 million additional propagations.
Any counterexample is replayed on both its case condition and the original query. A checked
case proof is reported as `case-proved`, rather than as an unsplit-query certificate.

```sh
cargo test -p bitwright --release --all-features --test keyed_mixers selector_partitions -- --ignored --nocapture --test-threads=1
```

All sixteen cases of each query remained unknown in the measured run: 48 unresolved cases,
zero conditional exclusions, and no original-query refutations. This experiment uses the
default binary parity encoding and does not reuse learned clauses across cases. It shows
that fixing only the first selector is insufficient at these per-case budgets, not that
all partitioning strategies must fail. The test stays ignored in normal runs because it is
an explicit search experiment, rather than a fast expected-verdict regression.

### Carry-save product columns

`Config::with_carry_save_multiplication(true)` changes modular multiplication from a chain
of row additions to column compression and one final carry-propagating addition. Each
three-bit column becomes a parity sum in the same column and a majority carry in the next.
Earlier rows are consumed before newly generated sums to avoid a serial chain in a column.
Constant rows still use signed digits when fewer rows suffice. A negative row at shift `i`
is represented by complemented operand bits at positions `i..w` plus a correction at `i`;
no complement leaks below the shift, and carry out of the word is discarded.

```rust
let config = Config::default().with_carry_save_multiplication(true);
```

```sh
cargo run --release -p bitwright-bench -- --mixers fingerprint masked-pair-32-unique --carry-save --escalate-fast > carry-save.csv
```

The option defaults to false, appears as `+carry-save` in CSV modes, and changes native
modular products. The primitive adapter stays a control using its original multiplier.
The following paired measurements use raw nested fixtures on the same host. The short
stage allows 200 conflicts / 100,000 propagations; the longer stage allows 100,000 conflicts /
50 million additional propagations after earlier resume stages. Instruction counts measure
search only, excluding preparation, sampling and certificate validation. These staged runs
enable certificates and disable sampling and native word simplification.

| Query | Variables, default → carry-save | Clauses, default → carry-save | Short instructions, default → carry-save | Longer instructions, default → carry-save |
| --- | ---: | ---: | ---: | ---: |
| 32-bit fingerprint | 17,448 → 17,341 | 74,590 → 71,183 | 32.48M → 21.95M | 25.439B → 25.440B |
| 64-bit fingerprint | 17,895 → 19,451 | 79,264 → 80,035 | 32.35M → 18.22M | 27.542B → 26.022B |
| 32-bit masked-pair uniqueness | 8,436 → 8,722 | 36,018 → 35,556 | 35.03M → 28.61M | 29.608B → 28.346B |

Short search instructions fall about 32%, 44% and 18%. Longer instructions are approximately
unchanged for the narrow fingerprint and fall about 6% and 4% for the other queries.
Preparation instructions fall only 0.5–3%, remaining 44–98 million instructions per query;
the measured preparation alone is several milliseconds on this host. These are encoding
and per-budget cost improvements, not recovered verdicts or proof-speed measurements.
All three queries remain unknown after about 55 million cumulative propagations. Fewer
conflicts at a fixed propagation budget does not establish better progress toward a proof.

Combining carry-save with `--xor3` makes the longer search 12–18% more expensive than
carry-save alone in these runs, and all verdicts stay unknown. A separate, removed experiment
matched sum and carry gates and replaced independent parity clauses with joint full-adder
clauses. Its truth tables and certificates checked, including independent input signs and
sharing fallbacks, but longer instruction costs increased and it recovered no query.

`prove::tests::carry_save` checks every pair of small operands and all constant multipliers
through six bits, independent bit-serial products through 1,024 bits, fixed and correlated
input literals, declared-known-bit model replay, fully constrained certificates, and exact
one-propagation search resumption with both parity encodings. These tests do not assume
that smaller or shallower circuits must solve the hard fixtures.

A separate three-run CPU profile uses `Config::default()` (256 samples, no certificate),
with native simplification enabled, then the same 200-conflict / 100,000-propagation search.
Each run has a fresh context and question. Medians for preparation and search separately
give the following approximate combined costs, including the carry-save option as the only
configuration change:

| Query | Default CPU time | Carry-save CPU time | Verdict in every run |
| --- | ---: | ---: | --- |
| 32-bit fingerprint | 8.90 ms | 7.25 ms | unknown |
| 64-bit fingerprint | 8.75 ms | 7.61 ms | unknown |
| 32-bit masked-pair uniqueness | 5.61 ms | 3.76 ms | unknown |

These medians characterize warmed process behavior, not a CPU-time limit. The first
default preparation for the narrow fingerprint costs about 33 ms in this profile, and
the first wide preparation about 14 ms. Removing certificate storage improves throughput,
but does not recover any of the three verdicts. An exact recovery within a small
millisecond budget remains unverified; cheaper unresolved searches do not satisfy it.

### Inverse coordinates, parity closure and reference solvers

Two exact changes of variable were profiled without retaining a new runtime option. Write
`S(h) = h XOR (h >> (32 + (h >> 60)))`, and let `I` be the first odd key's inverse modulo
`2^64`. The correction changes only low bits, so `S` preserves its own shift count and
`S(S(h)) = h`. Thus the two formulations are:

```text
inner coordinate:   y = K0 * (x XOR K0);  x = (I * y) XOR K0
output coordinate:  y = F_K0(x);          x = (I * S(I * y)) XOR K0
```

The first mixer is expressed directly in `y`; the other mixers use the recovered `x`.
For both narrow questions, `x >> 32 == 0` is asserted on this recovered word. The wide
question keeps the entire 64-bit domain, and uniqueness still excludes the original
candidate in recovered coordinates. The 24 combinations of three queries, two coordinates,
selector preferences and multiplier encodings all remained unknown at the continued
100,000-conflict / 50-million-additional-propagation stage. The reparameterization preserves
the problem but did not expose a cheap proof in these measurements.

An initial independent diagnostic extracts exact parity equations from complete groups of clauses
in the default CNF, adds all values forced by ordinary unit propagation, and performs
Gaussian elimination over GF(2). The original nonlinear carry and multiplexer constraints
remain outside this diagnostic's linear abstraction:

| Query | Parity rows before units | Bits fixed by propagation | Bits reported by the initial pass | Linear contradiction |
| --- | ---: | ---: | ---: | --- |
| 32-bit fingerprint | 9,426 | 137 | 137 | none |
| 64-bit fingerprint | 10,605 | 137 | 137 | none |
| 32-bit masked-pair uniqueness | 4,473 | 38 | 38 | none |

The linear abstraction has models. This isolated parity check therefore cannot establish
the required exclusions; further deductions need the nonlinear carry and selector
constraints too. This diagnostic does not rule out using parity reasoning during search.

External diagnostics also retain the exact original domains and arithmetic. Z3 5.1.0 and
Bitwuzla 0.9.1 return timeout/unknown on all three questions at a one-second per-query bound.
Bitwuzla's default abstraction and `--abstraction=false` were tested separately. An independent
CryptoMiniSat 5.11.21 Python run uses the default exported CNF, with and without the extracted
parity rows passed to `add_xor_clause`; all six searches remain undecided after about one
second of search. Its models would be checked against every original clause before accepting
SAT. These experiments add no external solver dependency to the library. The installed
Bitwuzla lacks its optional CryptoMiniSat backend, so that rejected configuration is excluded
from the comparison.

The method references are [bit-vector abstraction refinement](https://bitwuzla.github.io/data/NiemetzPZ-CAV24.pdf)
and [CryptoMiniSat's incremental CNF/XOR interface](https://github.com/msoos/cryptominisat#incremental-python-usage).
The measured timeouts characterize these runs; they do not establish a lower bound on
solving the expressions.

### Sampling original words before circuits

`Config::with_word_sampling(true)` evaluates a bounded integer DAG directly in machine
words before building an AIG. Supported nodes and their operands must fit in 64 bits; the
compiler visits at most 4,096 nodes. It supports the integer operators, comparisons, casts
and selects with their total bit-vector semantics. Random and ordinary small samples preserve
the circuit sampler's input ordering; reconstructed-word samples use the coordinates described
below. All modes retain declared fixed bits and 64-assignment batches. Every accepted
counterexample is replayed on the original constrained predicate, including original symbols
that simplification omitted.

```rust
let config = Config::default()
    .with_simplify(false)
    .with_word_sampling(true)
    .with_sample_mode(SampleMode::Words)
    .with_samples(65_536);
```

```sh
cargo run --release -p bitwright-bench -- --mixers cross-key-guards masked-pair-32 fingerprint --word-samples --escalate-fast > word-samples.csv
```

The option defaults to false and adds `+word-samples` to the CSV mode. The worker's initial
search remains a no-sample control; `native-small-samples` measures the early sample call
independently. The raw nested full-width cross-key guard recovers the same `x = 0x4563`
after 17,792 samples in about 2 ms / 42.8 million instructions, compared with about 18 ms /
578 million instructions through the circuit sampler. The early call builds zero AIG nodes
and zero CNF variables. The masked-pair existence witness takes about 0.8 ms. Across both
spellings and simplification modes, cross-key witnesses take 1.8–2.1 ms and masked-pair
witnesses 0.8–0.9 ms in the measured matrix.

Partial coverage never proves validity. Supported misses proceed to ordinary SAT
preparation without repeating the same samples. Wide, floating-point, extension and capped
DAGs use the original circuit sampler. No declared domain is narrowed. The two fingerprints
and masked-pair uniqueness still remain unknown in all twelve spelling/mode combinations
at the longer continuation budget. Their 65,536-sample misses plus circuit preparation cost
roughly 7–17 ms, so a large sample allowance is useful for witness recovery but is not a
uniform millisecond solution for exclusions.

Regression coverage includes exhaustive scalar integer operators through five bits,
independent wide boundary checks, generated shared DAGs against the generic evaluator,
deep/unsupported fallback, multi-symbol and fixed-bit sampling parity, restored original
declared symbols, and independently checked SAT certificates after samples exhaust.

### Complete online word domains

The ordered word path now recognizes complete coverage of its legal input domain.
`SampleMode::Small` with word sampling enabled, or `SampleMode::Words`, can return
`Proved(None)` once the joint stream enumerates all `2^n` assignments of the `n` unknown
symbol bits and none refutes the constrained predicate. Fixed declared bits stay fixed,
including sparse high bits. Assumption predicates are evaluated for every assignment.
Only joint coverage counts: finishing individual words or the diagonal does not enumerate
their Cartesian product. Random samples cannot certify coverage. Domains with 32 or more
unknown bits, insufficient allowances and unsupported DAGs retain the circuit path.
Certificate requests always retain the original bit-blast/DRUP path.

This uses the existing sample allowance in 64-assignment batches, with no offline fact
preparation or additional configuration field. For example, one word with eight unknown
bits is completely checked by 256 samples. With multiple independent words, the bounded
portfolio shares its allowance; enough joint batches must actually run before a proof
is returned. The evaluator stops once coverage is complete.

Release measurements of the original 32-bit fingerprint and masked-pair uniqueness
claims, with declared zero high bits leaving 8, 12 or 16 free low input bits, give:

| Free bits | Fingerprint online proof | Uniqueness online proof | Native controls |
| --- | ---: | ---: | --- |
| 8 | 28.2 µs | 22.3 µs | unknown, about 55–57 ms |
| 12 | 0.269 ms | 0.176 ms | unknown, about 61–62 ms |
| 16 | 4.21 ms | 2.80 ms | unknown, about 62 ms |

These are median per-query CPU times over three repetitions of both shift spellings,
including word compilation and complete evaluation. Word proofs construct zero circuit
nodes and use 256, 4,096 and 65,536 samples respectively. Native controls include preparation
and 2,000 conflicts / one million propagations, with no simplification or sampling.
Both paths retain the original 32-bit symbol and its explicit declarations. These results
do not cover the unrestricted 32-bit domain or the full-width fingerprint.

Regressions compare complete decisions and returned models against independent generated
truth tables, exercise division by zero, preserve DRUP requests, enumerate declared bits
at positions 0, 7 and 63, and force a counterexample outside the individual and diagonal
streams. Ordinary integration checks both shift spellings of both mixer claims over all
three bounded domains. The complete 32-bit and unrestricted guards remain unresolved
within the online budget.
Thirty-six cross-key guard variants cover secrets through 65,535, both shift spellings and
an optional declared high one. Every variant recovers a full-width original-symbol witness
with zero circuit nodes, verified by the separate scalar oracle.

### Reconstructed-word sampling coordinates

Loaded words often remain `concat(byte7, concat(byte6, ... byte0))` in the actual prover DAG,
even when a diagnostic renderer displays a single word name. Circuit traversal visits the
high byte first. Ordinary `SampleMode::Small` therefore varies the high bytes first and
keeps the low bytes zero throughout a 65,536-assignment prefix. A numeric word witness such
as `0x4563` is absent from that prefix.

`SampleMode::Words` instead prioritizes the unknown bits of the largest pure concatenations
and standalone symbols from low to high, then appends other unknown bits. Constants, fixed declared bits, casts and
extracts retain their original interpretation. Shared and overlapping bits get exactly one
sampling coordinate. Coordinate preparation is a permutation of the original independent
input bits; the sampling streams below select assignments in those coordinates. Shared
bytes retain their identity. The mode enables early machine-word sampling
when supported and uses ordinary small circuit ordering for unsupported DAGs. Sampling
partial-prefix exhaustion still cannot establish validity.

```sh
cargo run --release -p bitwright-bench -- --mixers cross-key-guards-bytes --word-samples --escalate-fast > byte-words.csv
```

The new `cross-key-guards-bytes` fixture uses eight original 8-bit symbols and both shift
spellings. In the raw nested control, small circuit sampling misses after all 65,536 samples,
and continued native searches still return unknown after about 55 million propagations /
3.1 seconds in the final stage. Reconstructed-word sampling recovers the exact eight-byte
model of `0x4563` after 17,792 samples in about 3 ms, with no AIG or CNF construction.
The model is replayed on the original byte-based expression and the scalar oracle. This
recovers a representation that the earlier single-symbol fixture did not exercise; it does
not establish recovery of every unknown dispatch in a separate application.

Tests compare complete small input cubes before and after reordering, with overlaps and
declared fixed bits, and check generated programs against ordinary evaluation after
reordering. A repeated-byte near miss (`concat(x,x) == 0x0102`) must never receive a model;
its native certificate still checks. A 65-bit input retains the circuit sampling fallback.

### Independent-word sampling streams

Reordering bits alone leaves later independent words at zero throughout a small prefix.
The captured fixture in `bitwright/tests/common/independent_words_dispatch.txt` needs the
second loaded word to equal 1. The first loaded word can stay zero. Both ordinary small
sampling and the earlier single reordered prefix miss this witness in 65,536 assignments.

The word mode now interleaves 64-assignment batches from the original joint prefix,
individual prefixes for at most eight maximal words, and a diagonal prefix that advances
the words together. Duplicate streams are omitted. The existing total sample allowance is
shared across at most ten streams; it is not multiplied by the word count. A single word
retains its previous enumeration order. Unvaried unknown bits stay zero, declared bits keep
their values, and shared inputs receive one assignment even when groups overlap. The
diagonal is a counterexample heuristic and never justifies a proof by exhaustion.

The captured two-word fixture now yields its original sixteen 8-bit symbol bindings after
128 samples, with zero AIG nodes. A release measurement takes approximately 0.095 ms of
thread CPU, compared with 27 ms for the unsuccessful 65,536-sample ordinary-prefix control.
The model replays to the expected target on the entire captured expression. This validates
expression semantics; it does not establish native replay, successor admission or CFG
closure in the application. The caller configuration inspected for the capture disables
sampling, so integration requires a positive sample allowance and opting into the mode.

Of eight captured unsampled-target questions, this pass resolves one; seven remain unknown
under the 65,536-assignment allowance. The misses cost about 8–68 ms before circuit work on
this host. Use a small initial allowance for throughput-sensitive calls and reserve larger
prefixes for escalation. The three existing hard exclusion/uniqueness fixtures also remain
unresolved. A 256-sample pass recovers the same witness in approximately 0.08–0.10 ms;
its misses take about 0.04–0.35 ms across these captures, including the conditional-load DAG.
These measurements include question construction but exclude circuit construction and SAT.
Unit regressions cover independent standalone words, diagonal witnesses,
assumption rejection with subsequent certificate checking, original shared-byte evaluation,
and a fixed total allowance over sixteen independent words.

The subsequent offline diagnostic enumerated every 32-bit input for each of the seven
remaining captures and found no witness in that prefix (about 6–8 CPU seconds per case).
For six full-width inputs this leaves all larger inputs open. The conditional-load capture
always constructs a 32-bit loaded value before zero-extension; its first keyed pair alone
has no preimage over that complete 32-bit domain. A separate two-mixer scalar scan confirms
this in about 3.5 CPU seconds. The durable ignored test
`bounded_loaded_word_pair_has_no_preimage_in_its_complete_domain` checks all 2^32 values;
its ordinary companion checks both shift spellings, width preservation and explicit
sampling exhaustion. This supplies an independent exclusion oracle for another runtime
unknown, not a native SAT certificate or an acceptable online proof cost. The translated
capture evaluator also agrees with ordinary expression evaluation on 294 boundary and
conditional-load assignments.
Native searches of this necessary pair remain unknown at 2,000 conflicts / one million
propagations across both shift spellings, raw/simplified inputs and both ordinary and
compressed encodings. Those searches cost about 60–82 ms including preparation. A larger
sampling prefix cannot decide this exclusion; a faster proof method is still required.

### Direct inverse guard equations and propagation search

For an odd-key guard `F_a(x) XOR F_b(x) == salt`, a direct output-coordinate
reformulation differs from substituting a recovered input into the other forward mixers:

```text
y = F_a(x)
x_a = inverse_F_a(y)
x_b = inverse_F_b(y XOR salt)
require x_a == x_b
```

Every term of a three-pair guard uses the same `y` and recovered `x_a`. A 32-bit source
additionally requires `x_a >> 32 == 0`; removing that requirement would change the question.
The mixer inverse is exact because its self-selected high shift is an involution and both
products have odd coefficients. Boundary inputs are replayed through the forward image and
the recovered input, including full-width values for the unrestricted cases.

Seven remaining captured guard cores were measured in their original coordinates and in
these direct inverse coordinates, each with ordinary encoding and with the combined
carry-save/three-input-XOR options. All 28 questions remain unknown at 2,000 conflicts /
one million propagations. Preparation plus bounded search takes approximately 59–88 ms
in these release measurements. The inverse reformulation changes the encoding but does
not recover a verdict. Any certificate from such a reformulated question would concern
that question; none is presented as a certificate of the original capture.

These measurements use audited numeric edges. Each reconstructed pair's keys, source bound
and salt are checked against the parsed original capture, then its complete 64-bit value
is replayed at boundary inputs. This corrects an earlier profile that anchored one guard's
three edges at the first listed mixer instead of the mixer shared by all three comparisons.
The ordinary `captured_shared_mixer_pairs_replay_the_numeric_edges_and_reject_a_wrong_pivot`
regression retains that typed eight-byte snapshot and checks both shift spellings. It
compares full pair values against the independent scalar oracle: merely observing that
both Boolean guards are false would miss the transcription error.

A separate reference diagnostic used Bitwuzla 0.9.1's `prop` and `preprop` engines,
described in its [official options documentation](https://bitwuzla.github.io/docs/c/enums/bitwuzlaoption.html).
For each engine, the time limits were 10 ms and 1,000 ms. The inputs are exact SMT-LIB
exports of all eight captured target equalities with their original byte widths, the three
hard fixtures, and an unrestricted cross-key guard with the known `0x4563` witness.
All 48 of those checks return unknown. In particular, propagation does not rediscover the
second-word witness found by the bounded word portfolio, and it does not find `0x4563`
in the unrestricted guard. These are search misses, not exclusion proofs.

The other twelve checks are controls: the guard fixed at `0x4563` is satisfiable, the guard
fixed at the nearby `0x4562` is unsatisfiable, and the single-key constant-image inversion is
satisfiable, across both engines and time limits. All controls return their expected status.
This reference experiment provides no evidence for replacing the native search with these
word-propagation engines or for claiming that an inverse rewrite meets the online budget.
Offline exclusion oracles and bounded online witness recovery remain separate results.

### Shared-input product projections

For inner products of the same full-width input,

```text
hi = ki * (x XOR ki)
hj = kj * (x XOR kj)
d  = ki XOR kj
t  = x XOR kj

hi*kj - hj*ki = (d - 2*(t AND d))*ki*kj       (mod 2^64)
```

This follows from `(t XOR d)-t = d-2*(t AND d)`, including even or zero keys.
For odd keys, put `ui = hi*inverse(ki)` and `uj = hj*inverse(kj)`. Then a common
input necessarily satisfies:

```text
D = d - (ui - uj) = 2*(uj AND d)
D AND NOT(2*d) = 0
```

The mask is necessary but not sufficient. For keys 3 and 5, inner words 9 and 5 give
`ui=3`, `uj=1`, and `D=4`. The mask accepts them, but their recovered inputs are 0 and 4.
Thus the exact common-input equalities must remain in any reformulation. The scaled
differences omit input positions where the key bits agree; this does not make the full
fingerprint independent of those positions. With the existing four-key fixture, flipping
input bit 0 leaves all six scaled differences unchanged and changes the fingerprint.
The new ordinary regression `common_product_projections_do_not_remove_fingerprint_input_dependencies`
covers both distinctions, wraparound, zero/even keys and high input bits.

The six difference masks for that fixture select 55 of 64 positions in their union,
including 27 of the low 32 positions. The first pair alone selects 18 of those low 32
positions. These are supports of derived projections, not smaller replacement domains
for the original input.

An independent-inner-word diagnostic used separate `hi` symbols, recovered each input
with its odd inverse, and required all recovered inputs to agree. Narrow questions also
retained the recovered input's 32-bit upper bound. The original fingerprint or uniqueness
condition is evaluated from those same `hi` words. Forward-generated boundary tuples
replay both the input and the full predicate, including the known necessary candidate.
Additional projection masks are optional redundant conditions under the exact common-input
equalities. All 24 combinations across the three hard fixtures, mask inclusion, compressed
encoding and selector preferences remain unknown at 2,000 conflicts / one million
propagations. Preparation plus these searches costs roughly 49–99 ms.

The uniqueness question was also measured with only its two observed inner words; the
other two words are unnecessary. All eight corresponding configurations remain unknown.
The ordinary encoding has 8,816 variables without the projection mask and 9,107 with it.
Its projected, default-selector variant remains unknown after two resumed 50-million-
propagation allowances: 125,229 cumulative conflicts, 100,629,720 propagations, and about
9.86 CPU seconds including preparation. The experiment retains no new runtime strategy:
neither a valid projection nor the cheaper per-conflict stages establish fast recovery.

### Output-bit cores and restart priorities

A subsequent output-core experiment keeps the entire original input and inner product,
including its self-selected shift, and truncates only the outer product and comparisons.
An exclusion of a projected target is sufficient for the full exclusion. A projected
counterexample is not sufficient for a full counterexample: at `x=0x15c4a4`, the original
fingerprint is `0xff9fef7fb9dfff80`. Its low byte matches the target's `0x80`, while the full
target is different. An ordinary regression checks this in both input widths and both
shift spellings, replays the original model, and checks the full-target certificate under
that concrete input declaration.

The fingerprint queries were projected to 8, 12, 16, 20, 24, 28, 32, 40 and 48 output bits;
the uniqueness question used 32, 48, 52, 56, 60 and 63 bits. Each used ordinary and combined
carry-save/three-input-XOR encoding. All 48 native questions remain unknown at 2,000
conflicts / one million propagations, including the known-satisfiable 8-bit projection.
Smaller circuits alone do not provide the needed proof or model.

Restart inspection found that trail reuse considered only currently unassigned variables.
A higher-priority variable implied later on the trail could be ignored, even though a
fresh restart could choose it. The corrected calculation includes the discarded suffix's
priorities and excludes root assignments. When every variable is assigned, it preserves
the completed model so the solver can return it without rebuilding the trail. Four focused
regressions check these behaviors, and the broader resumption and DRUP suites pass.
Rerunning all 48 output-core questions still yields unknowns.

Three fresh-context release measurements use the default configuration and a short
200-conflict / 100,000-propagation allowance on the full hard questions. The following
medians include preparation and search; every verdict is unknown before and after:

| Query | Encoding | Before restart correction | After |
| --- | --- | ---: | ---: |
| 32-bit fingerprint | Ordinary | 8.72 ms | 8.84 ms |
| 32-bit fingerprint | Carry-save | 7.51 ms | 7.91 ms |
| 64-bit fingerprint | Ordinary | 9.14 ms | 9.23 ms |
| 64-bit fingerprint | Carry-save | 7.65 ms | 7.55 ms |
| 32-bit masked-pair uniqueness | Ordinary | 5.54 ms | 5.60 ms |
| 32-bit masked-pair uniqueness | Carry-save | 3.79 ms | 3.79 ms |

These short searches follow the same conflict/propagation counts on both versions. The
measurements do not establish a throughput improvement or a newly recovered hard verdict.
The retained change corrects priority-based trail reuse and avoids completed-model work.

An independent integer-limb diagnostic uses
[CP-SAT](https://developers.google.com/optimization/cp/cp_solver), with 16-bit modular-product
rows, explicit carry bounds, Boolean word digits and exact selected-shift constraints.
It avoids coefficients or sums approaching 64-bit integer overflow. Eight ground mixer
checks and six one-bit-wrong output checks pass. Six additional ground projected-target
controls confirm that the concrete low-byte witness satisfies only the 8-bit target,
with the 20- and 64-bit targets excluded, in both input widths.
All 22 ungrounded checks remain unknown at 10 ms or one second: fingerprint cores of
8, 20, 32 and 64 bits for both input widths, and uniqueness cores of 32, 56 and 64 bits.
The reference model has no new runtime integration.

### Explicit verified finite-domain facts

The optional `prove::finite::CheckedPair` interface separates exhaustive verification from
subsequent query work. A fact contains the exact preimages of
`(F_a(x) XOR F_b(x) XOR salt) AND mask == 0` over `0 <= x < 2^domain_bits`.
Its fields are private and its only constructor verifies the entire domain. Insufficient
input allowance or too many candidates returns an error and supplies no partial fact.
Domains beyond 32 bits are rejected. No unchecked candidate-list import is provided.

```rust
use bitwright::prove::{Question, Config, finite::{CheckedPair, VerifyLimits}};

// Explicit preparation: this performs all 2^32 scalar evaluations.
let fact = CheckedPair::verify(
    [0xc26a114af502712b, 0xcbb4ec854c6b3e87],
    0x5327ba71a382cdf5,
    0x582bede356a9897f,
    32,
    VerifyLimits { inputs: 1 << 32, candidates: 256 },
)?;
// Reuse the checked value on a matching predicate in a Context.
let question = Question::valid_with_pairs(
    &mut context, predicate, std::slice::from_ref(&fact),
    &Config::default().with_samples(0),
)?;
```

Application checks the actual integer AST: both products' keys, the logical self-selected
shift, the shared source and the relevant salt/mask bits. Nested and compact shifts match.
A zero extension, a constant input mask or a declared high-zero range can establish the
source bound. Having only 32 unknown bits at a nonzero high address is not such a bound.
The remaining original predicate is substituted and checked at every candidate; unrelated
symbols survive in guarded residual predicates. Weaker masks and unrestricted sources
remain unchanged. A candidate outside a smaller source type is discarded, not truncated.
Rewrite work is bounded and deep DAGs fall back. The ordinary `Question::valid` API neither
registers nor implicitly applies any fact.

The existing necessary masked pair is verified to have exactly `[0x4563]` in its complete
32-bit domain. The loaded-word pair's full equality has no preimage in its complete 32-bit
domain. Each verification costs approximately four CPU seconds in a release measurement.
With these prepared values, the 32-bit fingerprint, masked-pair uniqueness and the full
captured conditional-load target exclusion return `Proved(None)` with zero circuit nodes.
The first fingerprint call takes about 23 µs and warm calls roughly 8–10 µs; uniqueness
calls take about 13–24 µs, and the 52-symbol conditional-load capture about 25 µs.
The original nodes, source widths and declared bits are retained. All full-width fingerprint
controls remain unknown when supplied the same fact.

These are warm query costs after explicit preparation, not an all-online proof of the
hard exclusions. Exhaustive preparation is not counted in the query's SAT statistics.
`Config::certificate` keeps the original question's bit-blast/DRUP path and bypasses this
fact rewrite; a finite verification record is not presented as an original DRUP certificate.
The long integration
`checked_finite_facts_settle_bounded_queries_and_keep_full_width_sources_open` independently
prepares both domains and checks both spellings, bounded/masked/declared inputs, the exact
conditional-load capture, normal-API controls and unchanged full-width behavior.
This optional path resolves three bounded examples after preparation. The remaining
unrestricted guards and an all-online solution to the full goal are still unresolved.

### Bounded corrections and decoded high-bit projections

For an odd key, the selected shift gives another necessary condition for a complete
three-pair guard. Write `h = k * (x XOR k)` and `r = h >> (32 + (h >> 60))` in wrapping
64-bit arithmetic. The existing correlated-shift bound gives `0 <= r <= B`, where
`B = 2^28 - 1`. For the actual output `f = k * (h XOR r)`:

```text
inverse(k) * f - h = (h XOR r) - h
-B <= signed(inverse(k) * f - h) <= B
(inverse(k) * f) >> 28 = h >> 28
```

The ordinary integer XOR difference is `r - 2 * (h AND r)`, so it lies between `-r`
and `r`. That interval fits the signed 64-bit domain. The high-bit equality is stronger:
the selected XOR changes only the inner product's low 28 bits.

In a full three-pair guard, use a fresh output word `y`, salts `s0 = 0, s1, s2, s3`,
and require these bounds for each `inverse(ki) * (y XOR si) - ki * (x XOR ki)`.
Every original solution extends to this necessary system with `y = F0(x)`. An UNSAT
proof of the system could therefore exclude the original guard; a SAT model of it must
still be checked against the original mixer and predicate. These conditions apply to
complete known XOR equalities, not to a fingerprint's partially masked OR target.
The original 32-bit or 64-bit source domain is retained.

All seven audited captured guards remain unknown in native searches of the exact signed
bound, a weaker 29-bit sign-extension bound, and the decoded high-bit equality. Both ordinary
and carry-save/three-input-XOR encodings are tested: 42 unresolved runs at 2,000 conflicts /
one million propagations. A linear integer encoding removes the selected-shift circuit
entirely, expanding constant XORs into signed Boolean coefficients and using bounded modular
quotients. All seven Z3 queries time out at two seconds. A separate
[CP-SAT diagnostic](https://developers.google.com/optimization/cp/cp_solver) uses exact
16-bit integer product rows and explicit carry domains. Signed-bound and high-projection
versions both remain unknown at 10 ms and one second: another 28 unresolved runs.

The controls check 114,688 scalar correction identities per native diagnostic pass,
original numeric edge replay, 99 forward-generated AST evaluations, 28 linear-integer
grounded cases and 56 CP-SAT grounded cases. The ordinary
`mixer_corrections_are_signed_small_and_relaxed_models_need_original_replay` regression
checks every selector interval's endpoints, maximal positive/negative corrections and
full-width input boundaries. Its zero-correction model satisfies all three local necessary
conditions while excluding the actual mixer image; original-model evaluation and checked
point certificates prevent that model from being presented as a recovered original case.
The diagnostics add no production reduction or claim of online-budget recovery.

### Joint arithmetic columns for the correction relaxation

Another private diagnostic expands the constant XOR operands bit by bit and places both
constant products and one signed 29-bit correction in a single modular sum. For example,
`x XOR k = k + sum((1 - 2 * bit(k,j)) * 2^j * bit(x,j))`; the products then distribute
over this integer sum. They do not distribute over the original XOR. Each of the four
rows directly encodes `inverse(ki) * (y XOR si) - ki * (x XOR ki) - di = 0 mod 2^64`.
The free correction range is `[-2^28, 2^28 - 1]`, a necessary relaxation with one extra
negative endpoint, and source widths remain unchanged.

The diagnostic compresses all contributions in each bit column with full adders before
CNF encoding. Dense coefficients and canonical signed-digit coefficients are compared,
with both ordinary and three-input XOR clauses. Signed digits reduce the circuit to
13,646–22,942 CNF variables and 73,785–92,537 clauses across these cases and encodings,
versus 37,415–55,563 variables and 198,309–221,264 clauses for the dense construction.
Signed-digit graph construction takes roughly 1.1–1.6 ms; CNF construction and bounded
search together take 45–64 ms, excluding graph construction and diagnostic checking.
All 28 free-domain searches on the seven audited captured guards remain unknown at
2,000 conflicts / one million propagations.

The controls compare every bit of 7,168 computed modular rows with independent wrapping
scalar arithmetic, not just the resulting Boolean guard, and settle 140 supplied-input
controls. SAT models satisfy every encoded clause and replay the necessary scalar system;
UNSAT transcripts pass the independent DRUP checker. Synthetic forward-generated guards
also retain their original mixer witnesses. None of these controls establishes an
unrestricted captured exclusion, and this encoding is not added to the runtime.

### Normalized rows and unary carry counts

Two further diagnostics test whether propagation benefits from exposing more arithmetic
structure. In the correction system, multiply row `i` by `ki`, then subtract the scaled
pivot row from each other row. This makes the common output's coefficient one and cancels
its contributions wherever the salt bits agree. Alternatively, scaling by `inverse(ki)`
makes the common input's coefficient one and exposes sparse differences of constant XORs.
All scale factors are odd, so these triangular changes of basis preserve the necessary
system's solutions modulo `2^64`. The original 32-bit or 64-bit source domains and all four
signed correction words are retained. Neither transform replaces a complete mixer guard
with a sufficient condition.

The two normalized forms and an unnormalized control remain unknown in all 42 searches
on the seven audited captured guards, with both ordinary and three-input XOR clauses at
2,000 conflicts / one million propagations. Their controls compare 5,376 complete modular
rows, including nonzero results, against independent scalar arithmetic and settle 210
supplied-input questions. Models replay the necessary scalar system and UNSAT transcripts
pass the independent DRUP checker. The normalized forms show no useful combined gain in circuit size
and bounded-search time that would justify runtime adoption.

A separate encoding switches the final eight or sixteen bit columns from binary carry
compression to unary threshold counts computed by sorting networks. An even column sum
requires adjacent thresholds to agree; every second threshold represents a carry into
the following column. These constraints expose more of the count relationship directly
than a sum-parity gate alone. Tests check the threshold counts, their parity equivalence,
1,344 exact modular rows and 105 supplied-input questions. All 21 free searches, including
the binary control, still stay unknown at the same allowance. Eight unary columns increase
CNF size to 53,438–85,947 variables; sixteen increase it to 88,400–145,371 variables, versus
13,646–17,129 for the binary controls. Stronger count structure does not produce a recovered
case here, and no unary carry encoding is added to the runtime.

### Grouped coefficient domains

A finite-table diagnostic groups source bits by their sign pattern across the four
constant products. A constant XOR expands into signed bit coefficients, so positions
with the same key/salt-bit pattern share a coefficient vector. Each group is split into
chunks of at most four or six bits. All `2^chunk_size` assignments are retained, with their
exact wrapping contributions to each of the four rows represented as 16-bit digits.
This changes the representation of the full source domain; it does not enumerate just a
prefix or omit any group choice. The original 32-bit source stays 32 bits, and unrestricted
sources stay 64 bits.

The signed-correction version combines these tables with exact `[-(2^28 - 1), 2^28 - 1]`
bounds and modular carry equations. A stronger version computes inner and decoded products
separately, equates their upper two 16-bit limbs, and shares the high four bits of their
next limb. This enforces the necessary high-36-bit equality without approximating it by
a small signed difference. Both versions still require original mixer replay for any SAT
model; neither necessary system is a sufficient description of the captured guard.

On the seven audited captured guards, all 56 runs remain unknown at nominal solver limits
of 10 ms and one second. Four-bit chunks yield 35–43 groups and 318–458 table rows;
six-bit chunks yield 27–32 groups and 658–992 rows. Model construction takes roughly
1.8–8.4 ms, excluding table preparation and diagnostic checks. The nominal 10 ms searches
actually consume about 11.3–23.2 ms of CPU time, including presolve; this parameter is not
a strict end-to-end query deadline.

Independent scalar comparisons check 21,504 complete modular results across both versions,
including unrestricted high input bits. All 112 supplied-input controls settle correctly,
including forward-generated original mixer witnesses and exclusions at fixed inputs.
These checks validate the table arithmetic and controls, not the unrestricted exclusions.
The grouped representation provides no verified recovery or throughput gain, so no table
backend or runtime dependency is introduced.

### Alternate SAT backend on the original full domains

A separate diagnostic uses [Kissat 4.0.4](https://github.com/arminbiere/kissat/tree/8af8e56f174b778aef3aa45af9f739b2a5f492c2),
pinned at commit `8af8e56f174b778aef3aa45af9f739b2a5f492c2`. The inputs are the primitive
CNFs of the three hard questions, the masked-pair existence control, and exact CNFs of all
eight captured target equalities with their original byte symbols and widths. Default,
`--sat` and `--unsat` presets are tested at 10 ms and one second. All 72 free-domain runs
time out, including the two known-satisfiable controls already recovered by word sampling.
Timeouts supply no exclusion proof or model.

All 36 grounded controls settle correctly: thirty UNSAT traces pass the independent native
DRUP checker against the original CNFs, and six SAT models satisfy every original clause
and replay the original predicate. Captured SAT controls retain all sixteen original byte
bindings. Captured numeric guards and CNFs are derived from their original parsed DAGs;
no source domain is truncated. The time limits include the external process, CNF parsing
and search, while CNF construction and diagnostic checking are separate. This comparison
provides no verified high-throughput recovery or reason to add a runtime backend dependency.

### Alternate backend on the necessary high-bit systems

The same pinned alternate SAT backend was also applied to the seven audited guard cores'
necessary high-36-bit equality systems. These CNFs omit the selected-shift circuits, retain
the complete original source widths, and introduce one free decoded-output word. Both
ordinary multiplication and carry-save multiplication with three-input XOR clauses are
exported. Default and UNSAT presets are tested at 10 ms and one second, including process
startup and CNF parsing, with construction and checking measured outside those limits.
All 56 unrestricted searches time out; this combination therefore provides no quick
exclusion of the captured guards.

All 42 supplied-input controls settle: fourteen UNSAT traces pass the independent native
DRUP checker against their projection CNFs plus the input premises, and twenty-eight
SAT models satisfy every encoded clause, reproduce their full-width input/output words,
and replay the independently computed necessary conditions. The positive controls use
forward-generated salts at zero and at the source domain's maximum, and also replay
successfully on the original numeric mixer guard. They validate the encoding and supplied
points. No unrestricted original-capture verdict or native successor admission is inferred
from them, and no backend dependency or production rewrite is added.

### Exact decoded guards with a shared image word

Unlike the high-bit relaxation, an exact formulation retains every selected-shift bit.
For each odd key and salts `s0 = 0, s1, s2, s3`, introduce a common image word and assert:

```text
hi = ki * (x XOR ki)
inverse(ki) * (image XOR si) = hi XOR ((hi >> 32) >> (hi >> 60))
```

Multiplication by the odd inverse cancels the original outer multiplication. The four rows
are equivalent to the original three-pair guard *together with* `image = F0(x)` over the
extended domain. Consequently the original guard has a witness exactly when the decoded
rows have a witness with some image value. The 32-bit or 64-bit source bound is unchanged.
Replacing the original Boolean predicate with those rows while leaving the image free is
not an equivalent pointwise rewrite; this diagnostic instead asks the corresponding
existential search question. It applies to complete known XOR equalities, not masked OR
fingerprints.

On all seven audited captured guard cores, both ordinary and carry-save/three-input-XOR
encodings remain unknown in fourteen native searches at 2,000 conflicts / one million
propagations. Search alone takes roughly 53–76 ms here, excluding construction and checking.
The pinned alternate backend also times out in all 56 runs with default/UNSAT presets and
10 ms/one-second limits. All 42 supplied-input controls settle: fourteen UNSAT proofs check against the exact
decoded CNFs with the independent DRUP checker, and twenty-eight complete SAT models satisfy
all clauses and replay their forward-generated numeric guards at zero and the domain maximum. Export controls compare 57,344
full-width decoded/scrambled word values with independent wrapping arithmetic. Certificates
check the decoded CNFs; they are not presented as original captured-CNF certificates.

The ordinary `decoded_mixer_guards_are_equivalent_over_complete_small_domains` regression
checks all input/image pairs of scaled 8-bit mixers with 4-bit and 8-bit sources. Both shift
spellings are also proved by complete word enumeration, and the smaller source domain has
independently checked native certificates under both arithmetic encodings. Dropping the
image link deliberately produces a counterexample whose original guard is true and whose
image is wrong. This validates the exact reformulation and its proof boundary, without
claiming a recovered unrestricted case or adding a runtime rewrite.

### Exact selector quotients and masked count facts

An exact whole-word diagnostic expresses the selected logical shift as a quotient with
an explicit remainder. For `t = h >> 60` and `r = (h >> 32) >> t`:

```text
h >> 32 = 2^t * r + remainder
0 <= remainder < 2^t
t * 2^(28-t) <= r <= (t+1) * 2^(28-t) - 1
```

Six-bit grouped product tables retain the complete source and image domains, while Boolean
low-bit relations require `decoded = h XOR r`. The high 36 product bits remain equal.
Models with and without the redundant selector-specific range cuts are tested at nominal
10 ms and one-second solver limits. All 28 unrestricted searches on the seven audited
captured guard cores remain unknown. Model construction costs about 3.2–5.9 ms; nominal
10 ms searches consume about 16.2–24.3 ms of CPU including presolve. Independent controls
check 14,336 complete modular product results, 56 supplied guard inputs and 256 selector
boundary cases, including incorrect output bits that must be rejected. This encoding is
not introduced as a runtime backend or a recovered original exclusion.

The inspection also exposed a separate range-analysis precision gap in the actual nested
shift spelling. Direct facts for `(h >> 32) >> ((h >> 60) AND 63)` previously gave only a
32-bit upper bound; the self-count relationship was hidden by the redundant mask. The
fact transfer now unwraps bounded mask chains when cached base known bits prove every bit
outside the mask is zero. It recognizes masks around constant count offsets too. This
restores the exact 28-bit upper bound and lets direct `FitsUnsigned` queries prove it
without an expression rewrite. The masked result's own narrow range is not enough to
justify unwrapping its source.

Nonredundant masks retain ordinary conservative transfer. Selector 8 masked by 7 becomes
zero and can produce `0x8fffffff`, which deliberately rules out the incorrect 28-bit bound.
Regressions exhaust source values and masked/wrapping counts through six-bit widths,
cover 65-, 129- and 512-bit words, and withdraw a declaration that had made a mask redundant.
The helper uses cached base facts without adding assumption reliance or uncapped recursive
fact computation. This improves those word-level range queries; it does not settle the
remaining full mixer exclusions or uniqueness questions.

### Conditional lower bounds through identity bit operations

The selector study exposes another fact-transfer precision gap. With the explicit assumption
`(h >> 60) != 0`, the selector's unsigned interval is `[1,15]`. AND with the redundant mask
63 previously rebuilt its facts from bit masks and discarded the positive lower endpoint.
The nested shift therefore kept a lower bound of zero, and the compact count `32 + selector`
also lost the lower endpoint needed by the self-shift partition analysis.

Bitwise transfers now retain the entire operand facts when known bits establish an identity:
AND when the other operand is one at every potentially set bit, OR when it is zero at every
potentially clear bit, and XOR with a known-zero operand. Both operand orders work. Ranges,
signed intervals and unsigned strides survive, including through nonconstant masking
operands. Assumption reliance still includes both operands, so these identities do not
make a conditional fact global.

For both masked shift spellings, direct facts under the nonzero-selector assumption now give
`15 << 13 <= R <= 2^28 - 1`. Each selector interval endpoint agrees with the independent
scalar shift. The raw word-range query changes from unknown to true. In the compact spelling,
the corresponding native conditional-bound question changes from a zero-search-budget
unknown with 852 AIG nodes and 95 CNF variables to `Proved(None)` before bit-blasting.
The nested native question already simplified successfully before this change.

Regressions check both operand dependencies, removal of either assumption, changing masks,
strides and 8-, 32-, 64-, 65-, 129- and 512-bit words. Independent original-CNF certificates
check the conditional shift bound, while reusing the same context with a zero selector
returns a replayed counterexample and prevents a simplifier-memo scope leak. Without the
nonzero condition, the lower bound remains zero. A mask of 7 still permits selector 8 to
become zero and produce a 32-bit shifted value.

The original hard-query matrix keeps exactly the same graph/CNF sizes and all twelve
bounded native and resumed outcomes remain unknown. This improves a conditional proof
and the fact service; it does not establish the remaining complete-domain exclusions.

### Zero-preserving products and logical xorshifts

The native fact service now preserves two nonzero relationships before constructing
a circuit. Multiplication by an odd value is invertible modulo `2^w`, including
variable odd factors, so a nonzero operand cannot produce zero. For
`x XOR (x >>u count)`, a positive count leaves the highest set bit of `x` intact.
The bounded correlation matcher follows at most four logical shifts of the exact
same source. It recognizes literal counts, globally cached positive counts and
nonwrapping constant offsets of a constant shift, including `32 + (h >>u 60)`.
It does not fetch conditional count facts or perform an uncapped fact traversal.

Direct `IsNonZero` product queries with a variable odd factor change from unknown
to true at widths 8, 64, 65 and 129. Native validity checks at zero search allowance
now return `Proved(None)` with zero circuit nodes; before this change they also
proved, but constructed 267, 22,667, 23,394 and 93,890 AIG nodes respectively.
Under the explicit assumption `h != 0`, both nested and compact spellings of
`h XOR ((h >>u 32) >>u (h >>u 60))` now give a true nonzero fact directly.

Seven-sample retired-instruction measurements compare the retained implementation
against a private copy with only these two rules removed. Cold fact workloads at
8, 64 and 128 bits cost about 1.0%, 1.0% and 0.5% more instructions; the 512-bit
workload costs about 0.5% less. The fifty-query proof workload costs about 1.4%
more, while cached fact queries are unchanged. Structural rejection precedes the
XOR transfer's large result temporary, and products tighten their interval before
their existing reduction. This avoids the first implementation's measured 6–7%
cold narrow-fact and 19% proof-workload regressions. These measurements describe
general fact-service overhead separately from the avoided circuit construction.

Regressions enumerate complete small product/count domains and cover strided
inputs, variable factors, widths through 512 bits, arithmetic-shift and even-factor
counterexamples, unrelated sources, wrapping count offsets, zero work allowances
and assumption withdrawal. Seven native checks prove without circuit work and
separately produce independently checked certificates of the original conditional
CNFs. Their unconditional claims return models replayed through the original
expressions, rather than retaining the conditional nonzero fact.

The complete hard-query diagnostic retains the original source domains and all
eight captured target predicates. Both shift spellings of the four fixture claims,
plus the eight captures, run with native simplification, zero samples, and either
default encoding or all six optional encoding/search features. All 32 free queries
remain unknown after 2,000 conflicts / one million propagations and a resumed
8,000 / four million allowance. All 32 supplied-input controls settle: 26 checked
original-CNF proofs and six original-expression model replays. The zero-preserving
rules improve fact queries and avoid circuit work; this matrix does not establish
recovery of the remaining unrestricted guards.

### Per-product reverse relations and chunk lookup circuits

Two private circuit diagnostics preserve the original 32-bit and 64-bit source
domains. The reverse-product diagnostic gives an odd constant product a fresh
output word and asserts `input = inverse(key) * output mod 2^w`. This equation
defines the same unique output as forward multiplication. It reverses either
inner products, outer products, or both. Another variant keeps the forward
definition and adds the reverse equation as a redundant constraint. This differs
from replacing the entire question's input coordinates with one mixer's image.

Both arithmetic/parity configurations run all seven direction choices, including
the unchanged control, on the four fixture claims and all eight exact captured
target predicates. Every one of the 168 free-domain checks remains unknown after
2,000 conflicts / one million propagations and a resumed 8,000 / four million
allowance. All 168 supplied-source controls settle: 140 checked UNSAT transcripts
against the diagnostic CNFs and 28 SAT models satisfying every clause and replaying
the original expressions. Independent scalar controls check 140,704 reverse
relations, including complete small input/output domains and wide dual-direction
boundary values. The diagnostic certificates concern the newly encoded CNFs;
they are not presented as transcripts against the previous forward-only CNFs.

Reverse-only variants change variable counts by about -0.7% to +37% and clause
counts by about -3.2% to +32%. Keeping both directions increases variables by
roughly 39–126% and clauses by 40–130%. Preparation plus both free-search stages
costs about 277–479 ms for the changed variants in these runs. Neither reverse
nor redundant directions establish a useful online proof gain.

The second diagnostic groups three, four or five original input bits into a
lookup circuit for each exact small product. It combines the shifted lookup
outputs with either a balanced tree of wrapping additions or carry-save columns.
It retains repeated, complemented and fixed input literals. Independent scalar
checks cover 30,984 products, including complete small domains, even coefficients,
wide boundary values and correlated input bits.

All 96 free checks, including the unchanged control, remain unknown at the same
resumed allowances. The 96 supplied-source controls settle with 80 checked
diagnostic-CNF UNSAT proofs and sixteen original-expression SAT model replays.
Changed lookup variants increase variables by about 22–97% and clauses by
16–51%; preparation plus resumed search costs about 214–414 ms. No product
direction option or lookup encoding is added to the high-throughput runtime.

### Grouped signed products and redundant integer channels

A separate private integer-table diagnostic combines complementary source-key bit
patterns into eight signed groups, retaining every original source bit. Eight- and
twelve-bit chunks encode the exact modular products; image-side groups retain
their original salt patterns. Across 21,504 independent scalar product checks,
every reconstructed product agrees. All 28 free captured-guard searches remain
unknown at nominal 10 ms and one-second limits. Seven fully supplied planted
source/image controls settle and replay, while all seven source-only controls
remain unknown with the image free. Nominal 10 ms searches consume roughly
39–721 ms of CPU, which rules out this model as an online-budget improvement.

Another variant adds exact source/image word-limb channels to the grouped tables,
the forward equation `image = key0 * decoded0`, and optionally the inverse equation
`inverse_key0 * h0 = source XOR key0`. These equations preserve the legal domain
and check against 14,336 independent scalar product results. All 28 free guards
remain unknown. Fourteen fully supplied source/image controls settle and replay;
only one of fourteen source-only controls recovers its image within the nominal
one-second limit. Free-search CPU time ranges from about 142 ms to 3.59 seconds,
excluding model construction. Neither diagnostic is adopted as a runtime backend,
and supplied-input successes do not prove free-domain exclusions.

### Selector lower-bound clauses and deeper cancellation diagnostics

A separate primitive diagnostic encodes `selector != 0 => OR(R[16..27])`. Every nonzero
selector has a set high source bit that survives at a position from 16 through 27.
The original CNF includes definitions of the observed OR values without asserting them.
Fifteen full-selector clauses followed by cube-resolution clauses derive four selector-bit
implications, for 37 checked RUP clauses per eligible mixer. Every clause is checked against
that CNF, and later search transcripts include the lemmas as derivations rather than premises.

Scaled eight-bit controls exhaust 512 assignments across both parity encodings, reject a
deliberately incorrect output slice, and check all thirty nonzero full-width interval
endpoints. Across the three hard fixtures, a satisfiable pair control and all eight original
captured target equalities, ordinary/compressed encodings, selector preferences and
lemmas on/off give 96 unrestricted unknown outcomes at 2,000 conflicts and one million
propagations. The 96 grounded checks have eighty checked refutations and sixteen original
model replays. The additional clauses do not demonstrate faster recovery and are kept out
of production.

Another private prototype extends shared-input cancellation from five to eight XOR levels,
with at most 96 inspected literals per operand. Arithmetic-branch, polarity, observation
and depth-bound controls pass. Its 24 unrestricted native queries remain unknown through
10,000 conflicts / five million propagations, and most CNFs grow: rebuilding deeper paths
duplicates arithmetic/parity intermediates still used by other outputs. The retained
cancellation limit stays at five levels.

### Conditional shifted-bit clauses

A private diagnostic retains selector-conditioned bit values that unconditional correlated
shift folding cannot express. It enumerates at most four count literals, preserving their
polarities and repeated occurrences. When a chosen count selects a constant or another count
literal from the data, it adds a clause of the form `selector != t OR shifted_bit = value`.
Other data bits remain opaque. No selector value or original input value is discarded.
Each added clause is checked as a RUP consequence of the original primitive CNF, rather
than introduced as a new proof premise.

The diagnostic emits 240 clauses for each two-mixer question, 480 for the fingerprints and
most captured questions, and 1,440 for the independent-word capture. Clause generation
costs about 37–187 microseconds, excluding CNF construction, clause insertion, proof checking
and subsequent search. Tests compare native and selector-first branching both with and
without these clauses on the three hard questions, the masked-pair existence control and
all eight original captured target equalities. All 48 free-domain searches remain unknown
at 2,000 conflicts / one million propagations. Some conflict counts change substantially,
but this does not establish faster recovery.

All 48 supplied-input controls settle: forty UNSAT transcripts check against the original
CNFs plus their input premises, and eight complete SAT models replay the original scalar
or byte-symbol expression. Generated small shifts cover 16,384 original input assignments,
both directions, constant and selector-dependent fills, repeated/complemented count bits
and overshifts. Their 532 conditional clauses pass independent RUP checking and satisfy
every original model. No conditional-clause option is added to the runtime.

The masked-count range improvement is also rechecked against the existing hard-query
worker: all twelve combinations of question, shift spelling and raw/simplified mode remain
unknown in native search and in the final primitive resumed search. The restored direct
range proofs do not resolve these larger exclusion/uniqueness questions.

### Lattice candidates and the paired highest-bit symmetry

A separate witness-only experiment uses [fpylll 0.6.4](https://fpylll.readthedocs.io/en/latest/modules.html)
for LLL reduction, bounded block-size-ten BKZ, and both nearest-plane implementations.
The Boolean source/image coefficients of the signed-correction equations become integer
lattice rows; four additional rows permit multiples of `2^64`. The target centers each
bit coordinate between zero and one and centers the four residuals at zero. Every returned
integer vector is checked for lattice membership, Boolean coordinates and the necessary
scalar bounds. Clamped candidates are also replayed numerically against the exact guard;
a nearby lattice point is never accepted as a Boolean model without those checks.

The necessary system has a useful symmetry. Flipping bit 63 of both source and image
flips that bit in each odd product, leaving their modular difference and high-bit equality
unchanged. For unrestricted 64-bit sources, a canonical source with bit 63 clear therefore
covers both necessary-system orbits; both original source representatives are tried during
exact replay. The original selected-shift guard does not have this symmetry.

Four synthetic satisfiable controls and seven audited captured guard cores are tested at
four coordinate weights, with two reduction modes and two nearest-plane implementations:
176 attempts in total. None returns a necessary Boolean model or an original witness,
including the known-satisfiable controls. Returned vectors have 20–49 non-Boolean coordinates.
LLL takes roughly 50–106 ms of CPU and nearest-plane work another 14–54 ms, excluding model
construction, additional BKZ work and checking. The controls verify 5,632 modular coefficient
and symmetry identities and sixteen explicit known points belonging to their lattices.
A miss supplies no exclusion proof. No lattice dependency is added to the library.

### Highest-bit parity sharing in wrapping arithmetic

The symmetry study exposes an arithmetic encoding improvement. For an odd constant `k`,
`k * (x XOR MSB) = (k * x) XOR MSB` modulo the word width. Lower product bits share their
circuits, while previously the complemented highest-bit sums built different XOR trees.
A first prototype normalizing phases in every XOR settles these identities immediately, but
increases the original hard-query CNFs by about 22–25% in clauses and 42–50% in variables:
shared XOR/majority internals prevent the existing private-cone compression.

The initial retained change normalizes phases only at modular boundaries. Wrapping addition and
subtraction construct the final parity without constructing the outgoing carry. Interior
columns and the carry-returning adder keep their existing gate shapes. Carry-save products
also share complemented sums only in their final column. This gives the highest-bit
covariance proofs one CNF variable and two clauses, with no SAT conflicts. Across three
64-bit keys and both multiplication encodings, the checked diagnostic falls from roughly
0.96–4.42 ms to 0.33–0.58 ms including construction and search. Ordinary regressions cover
1-, 8-, 32-, 64-, 65- and 129-bit words, both encodings, checked certificates and even-product
counterexamples. The default paired-odd-product test now proves without input-cancellation
hints or search. Resumption tests retain several interrupted calls and exact single-call
work/model comparisons.

The hard-query matrix still returns unknown in all twelve raw/simplified and nested/compact
combinations. Graphs lose about 1.1–1.3% of their nodes; fingerprint CNFs gain fifteen variables
and sixty clauses, and uniqueness gains two clauses without another variable. These changes
do not demonstrate faster exclusion of those full domains. A separate full-width certificate
checks the paired-MSB symmetry of the necessary high-bit system, while an original positive
input whose MSB flip fails the exact guard prevents using that symmetry to drop an input bit
from the original guard without its existential reformulation.

### Sharing logical gates without retaining unused internals

The earlier global XOR prototype's encoding overhead comes from requiring each AND inside
a recognized XOR, majority or mux to have exactly one raw graph use. Arithmetic shares
these internal products, so phase normalization prevents that compression even when the
products are not independently observed. Gate recognition now permits shared internals;
the subsequent walk follows the selected gate's logical operands. Explicit roots and
operands used by other selected gates still keep their own variables and definitions.
Ordinary AND-tree flattening retains its single-use restriction. XOR phase normalization
can consequently apply throughout the graph without the earlier CNF overhead.

Compared with the preceding masked-count implementation, the nested, unsimplified fixtures
have these sizes. Preparation includes native question construction and initial propagation;
it excludes the following search and is a single-run CPU measurement.

| Query | Variables before / after | Clauses before / after | Preparation before / after |
| --- | ---: | ---: | ---: |
| Fingerprint, 32-bit source | 17,448 / 15,634 | 74,590 / 70,417 | 8.41 / 7.28 ms |
| Fingerprint, 64-bit source | 17,895 / 16,463 | 79,264 / 75,855 | 9.90 / 8.39 ms |
| Masked-pair uniqueness, 32-bit source | 8,436 / 7,557 | 36,018 / 34,005 | 4.22 / 3.58 ms |

All twelve raw/simplified, nested/compact fixture combinations still return unknown under
the benchmark's bounded native and resumed searches. Smaller circuits do not establish
full-domain exclusions. A regression enumerates input signs, observation subsets, all
four-input assignments and both parity encodings: 16,384 SAT/UNSAT checks preserve every
observed root and independently check each refutation transcript. The full workspace tests
also cover models, continuation, arithmetic and certificates.

### Bounded modular factors for constant products

Constant multiplication has another exact representation: choose an odd small factor `m`,
then `q = k * inverse(m)` modulo `2^64`, so that `k * x = q * (m * x)` with the same input
word and wrapping semantics. This does not require `m` to divide `k` as an integer.
The implementation examines the 127 odd factors from 3 through 255, estimates active
carry columns using the existing signed-digit choice, and accepts only plans saving at
least 10% of that estimate. Each chosen stage uses the unfactored multiplier; there is no
recursive factor search. Both the ordinary and carry-save encodings use the same plan.

The unguarded prototype enlarges some circuits with narrow or repeated inputs. The retained
path consequently requires a 64-bit word whose low bit is nonconstant, whose highest bit
is not known zero, and which contains at least 32 distinct nonconstant literals, ignoring
their complements. Other widths, pure zero extensions, words below that literal threshold,
even keys and cheap constants retain the preceding encoding. These are representation heuristics;
they do not restrict any query's legal assignments or introduce proof premises.

The nested, unsimplified hard fixtures have these sizes compared with the preceding
shared-logical-gate implementation. Native preparation includes the bounded factor search
and initial propagation; the retired-instruction counts exclude the subsequent SAT search.

| Query | Variables before / after | Clauses before / after | Preparation instructions before / after |
| --- | ---: | ---: | ---: |
| Fingerprint, 32-bit source | 15,634 / 13,330 | 70,417 / 60,401 | 84.59 / 75.96 million |
| Fingerprint, 64-bit source | 16,463 / 14,273 | 75,855 / 65,499 | 90.27 / 81.50 million |
| Masked-pair uniqueness, 32-bit source | 7,557 / 6,165 | 34,005 / 27,924 | 41.36 / 35.83 million |

All twelve raw/simplified, nested/compact fixture combinations remain unknown under the
bounded native and resumed searches. The larger 2,000-conflict / one-million-propagation
diagnostic also leaves the three hard fixtures and the known-satisfiable pair control
unknown under all four factor placements and both multiplication encodings. Reduced
preparation work does not establish a fast exclusion or witness recovery.

The seven audited captured guard cores also retain their full original source widths and
numeric edges. Both encodings leave all fourteen checks unknown at 2,000 conflicts and
one million propagations, taking about 48–87 ms including preparation and bounded search
in this release diagnostic. These are the guard-core questions, rather than proofs of
every surrounding captured target expression.

Regressions check modular plan identities, rejected data shapes, 65,536 scalar product
evaluations across fixed/correlated/full words, original-input models, interrupted search,
and independent certificates. The full workspace suite has 853 passes and no failures.
A read-only caller audit supplies no further domain bound for the unrestricted captured
byte words; only the explicit 32-bit load supplies its established narrow domain. Pointer
contracts on other symbols cannot be transferred to these read-order byte words.

### Option portfolio and complete affine closure after factoring

The smaller constant-product encoding is tested with eight combinations of the existing
input cancellation, selector preferences, relational lemmas, join factoring, carry-save
and three-input parity options. The cases are the three hard fixtures, their necessary
masked-pair existence control, and all eight original captured target exclusions. All
96 unrestricted questions remain unknown after an initial 2,000-conflict / one-million-
propagation stage and a continued 8,000-conflict / four-million-propagation stage. Native
preparation plus both searches costs roughly 252–471 ms in these release measurements,
excluding creation of the original expression DAG. Lower conflict counts at an exhausted
propagation allowance do not establish better progress toward a proof.

The corresponding 96 fixed-input controls settle: eighty proofs pass independent certificate
checking, and sixteen models replay in the original expressions. Both word domains and byte
identities remain unchanged. These controls validate the encodings and supplied points;
they do not prove the unrestricted exclusions or establish native recovery of the points.
The option sweep supplies no reason to change the defaults.

The first parity diagnostic above used a triangular elimination pass whose unit scan could
miss constants requiring substitution of a nonconstant lower pivot row. For example,
`a XOR b XOR c = 0` and `a XOR b = 1` force `c = 1` even though neither input row is a unit.
The corrected diagnostic fully reduces the pivot rows, then alternates derived affine units
with original-CNF Boolean propagation until a fixed point. Complete small truth tables test
every extracted parity row and inferred constant on 768 generated CNFs, along with the
specific nonconstant-pivot example.

The current three hard fixtures and the masked-pair existence control are exported under
both ordinary and carry-save/XOR3 encodings. Each export is first checked at a complete
original input assignment, including original-CNF refutation checking or clause/model
validation. The corrected affine closure handles 2,175–9,234 parity rows per export but
finds no additional constants, no fixed original input bits and no linear contradiction
in any of the eight cases. Python closure costs about 44–115 ms here, excluding text parsing;
no affine preprocessing pass is added to the runtime from this result.

A separate pycryptosat 5.16.0 diagnostic retains every original nonlinear CNF clause, with
and without supplying those exact parity rows to the solver's XOR interface. Both encodings
are tested at requested 10 ms and 1 s search limits. All 32 unrestricted checks remain
unknown. The 32 grounded controls have the expected 24 UNSAT and eight SAT outcomes; all
eight SAT models pass clause checks and replay through the original expression evaluator.
Parsing, row extraction and solver setup are recorded separately from search. These
measurements include no external exclusion certificate for an unrestricted question, and
introduce no solver dependency or unchecked premise into production.

### Runtime fact provenance and conditional tuple correlations

Coordination with the runtime investigation traces the six outstanding captured
source words to qword context loads and full-width spill/reload chains. It finds
no additional certified high-bit mask, input equality, range or alignment contract
that narrows them. The conditional loaded-word case retains its explicit dword
load and zero extension; that fact does not constrain the pointer used for the
load. Probe-agreed carried bytes and register values remain samples or model
assumptions without a checked producer/transfer and input scope.

There is a separate precision gap at capture handoff: the closing machine receives
whole-lane constants, while incoming carried-byte memory, physical registers,
partial known bits and predecessor path relations are not represented by that
constructor interface. Preserving a certified partial mask could help a future
query, but no such predecessor certificate was found for these six words.
Per-input facts cannot become common merged facts without complete scope coverage;
caps, omitted states and unknown secondary tails remain closure barriers.

Some output correlations are already structural. The regression
`shared_boolean_casts_preserve_correlated_target_and_tail_outputs` preserves the
original unrestricted eight-byte source word and its full-width fingerprint
predicate. It defines two tail outputs conditionally on the same predicate,
using the two consistent branches recorded by the captured model. Numeric
32-bit and 64-bit zero extensions of that predicate agree after widening.
The target and tail outputs are covered by two correlated tuples, and a tuple
mixing the true target with the false tails is impossible.

All three relationships prove with zero conflicts and zero propagation allowance;
with simplification disabled, independently checked Boolean-cut certificates
fit a one-node circuit limit. Original byte models include nonzero upper words
and the highest set bit. Substituting both abstract predicate values verifies
the conditional output definitions without presenting the true value as an
original guest witness. An independent predicate used for one tail gives an
original refuting model for the incorrectly correlated tuple claim.

These are output-superset and tuple-exclusion proofs within the captured input
model. They neither decide whether the original expensive true arm is reachable
nor prove a graph containing only the sampled false tuple complete. Runtime
coverage must include the primary key and every required tail in the same scoped
question, and must retain its exit/admission policy and complete input coverage.
The unrestricted fingerprint exclusions remain unresolved.

The runtime follow-up identifies the concrete integration seam: build target,
primary key, all required tail roots and input premises in the same context at
the arm-case construction point. Prove coverage by represented successor tuples,
then check correspondence with decoded and expanded graph edges before clearing
fallback. Conservative possible successors need not each have an existential
witness, but confirmed admission retains original-model replay, and candidate
membership alone cannot prove valid decoding or coverage.

Two caller representations currently limit that route: possible-arm admission
keeps one lane map per target, and arm-case discovery skips further proving when
the primary key is already known. Supporting multiple key/tail tuples at one
target and independently checking secondary-tail completeness are necessary.
The usual profile includes a primary field plus five aligned tail fields, with
exact byte overlap for packed identity fields; the two-tail regression therefore
does not certify the complete successor identity. No caller code, admission
policy or graph-completeness barrier is changed by these tests.

The opt-in `prove::domain::analyze` service now discovers bounded joint output
supersets from shared original roots and explicit Boolean premises. It uses the
existing Boolean-cut compiler, then enumerates only inputs live in the outputs
and premises, in 64-assignment batches. Abandoned intermediate inputs do not
inflate the support. Unavailable wide outputs or exceeded construction, input,
enumeration or distinct-tuple limits return an explicit unknown without a partial
list. Returned tuple values are conservative candidates, not original-symbol
witnesses. Changing the input scope or symbol declarations requires fresh analysis.
The sealed result retains its roots and premises and can build an original scoped
coverage predicate for independent native certification.

An exact multiplication peephole makes this practical on Boolean-derived words:
when a factor has no possibly nonzero bit above bit zero, its product is a
conditional bitwise copy of the other operand. Both multiplication encodings
use the rule, and the cut compiler charges linear work for that operation.
This avoids constructing signed-digit or carry rows for extended predicates.
The independent reference checks both factor orders and polarities through
512 bits, with exhaustive negative controls for a nonzero higher multiplier bit.
Joint-domain tests additionally cover independent predicates, same-target
different-key tuples, scoped and contradictory premises, all resource stops,
dead support, multiple enumeration batches, deep DAGs, arbitrary limb boundaries,
and exhaustive arithmetic/shift outputs against the independent reference.
The native validity shortcut also exhaustively evaluates a Boolean cut with at
most eight live inputs when structural hashing does not collapse a tautology.
This uses at most 256 abstract assignments and 16,384 circuit-node evaluations,
in addition to the existing construction allowance. A late refuting assignment
or an input/work cap falls back to the original circuit; an enumerated prefix
never proves validity.

In a release diagnostic, all eight nonconstant captured target roots yield a
two-value superset under default limits. Median analysis cost is about 2.6–7.1 µs
for seven roots and 21.7 µs for the independent-word target; first-call costs are
about 3.9–33.4 µs. Parsing, certificate construction and checking are outside those
analysis timings. Thirty-one batches of 100 analyses measure each median.
Every result's original coverage predicate is independently certified and 256
full-width original-symbol assignments are replayed. All eight target coverage
certificates now use one circuit node with zero conflicts and propagations;
complete Boolean-cut evaluation settles the independent-word target too.
Including domain analysis, coverage-predicate construction, native certification
and independent certificate checking costs about 6.6–33 µs per target, still
excluding parsing. The reconstructed two-tail joint output domain costs about 5.4 µs and retains
exactly the two correlated tuples; its original coverage certificate uses one node.
Adding the shared guard or its negation as a scoped premise leaves one tuple,
without changing the unrestricted input declarations.

These measurements recover output supersets, not the original guard exclusions.
They do not establish either branch's reachability, supply missing primary/tail
expressions, or close a graph containing fewer successor domains. The full
fingerprint and uniqueness queries remain unresolved online. Both original
spellings of the three hard fixtures were rechecked at 2,000 conflicts and
1,000,000 propagations after these changes: all six remain unknown.

The follow-up runtime audit confirms that the old report lacks original primary
and full-tail expression roots, complete incoming state/premises, memory-read
versions and a reliable binding to actual successor identities. Historical graph
nodes cannot fill those gaps because their scopes and node sets differ. A fresh
focused capture must export all shared roots and access-time provenance before
the reporting path discards them. A manifest of missing fields is not a full
joint-domain fixture, and conditional output summaries are not original tail DAGs.

### Exact scoped premises and a complete fresh export

Native questions previously rejected a Facts seed unless it pinned a constant.
They now retain every original component through `Assumptions::predicates`:
known-bit equalities, unsigned bounds and anchored stride residues, and signed
bounds. The unsigned lower bound prevents subtraction wraparound from admitting
values below the interval. Power-of-two strides use low-bit masks. SMT-LIB queries
use the same typed predicates, fixing previously omitted nontrivial strides.
Complete small domains and independent SMT-LIB import/evaluation check exact
membership, with wide masks and signed crossings through 512 bits.

The word sampler fixes scoped bits only through original seed masks and pure
symbol/extract/concat/extension/NOT wiring. It preserves shared and overlapping
symbol coordinates and retains the original premises in candidate filtering and
model replay. A 64-bit source scoped to `0..3` proves `x*x <= 9` before SAT in
about 2.9 µs in the release diagnostic: 64 sample lanes, zero circuit nodes and
no global declaration. Assumption construction is outside this timing. Partial
enumeration never proves a late-refuted predicate, and certificate requests
retain the original circuit path.

Declaration changes exposed a correctness bug in assumption propagation. After
declaring bit four of eight-bit `x` zero and assuming `x` odd, withdrawing the
global declaration could leave that bit zero in the overlay. The old behavior
then proved `(x & 16) == 0`, although `x=17` satisfies the original Boolean
premise and refutes it. A private refresh-disabled baseline reproduces both a
false fact proof and a false native proof. The current code tracks declaration
revisions, repropagates original seeds and returns the checked `x=17` model.
Constraint ids, changed declarations and restored feasibility are covered.

A focused producer retry exports all seven aligned outputs from one complete
797-instruction symbolic body: target, primary key and five tails. Its first
diagnostic stopped after ten instructions on an unrecognized architectural-choice
label. Static IR inspection identifies a one-bit undefined flag producer; the
narrowly corrected private diagnostic preserves a fresh value per producer and
shared subsequent uses. Both attempts remain archived; product source, solver
searches and graph surveys were unchanged.

The complete export contains 5,182 typed nodes and 86 memory access records.
Its output cones contain 2,639 shared nodes and 116 original byte symbols. A
strict shared importer validates widths and constant limbs, and an independent
integer oracle agrees on all seven outputs for 32 full symbolic models. This
is a fresh empty-lane model with explicit private-frame separation, not the
missing old input snapshot or a native-entry reachability proof.

All 32 models produce different target values. Finite joint analysis therefore
returns `UnavailableOutput` for the seven-root question; no field is omitted or
forced constant. A bounded simplifier pass exhausts its 512-new-node allowance
in about 11 ms and leaves the root cones unchanged. The old two-target claims
remain within their original scopes. Actual incoming relationships and graph
correspondence are still needed for full successor coverage. Both spellings of
the three original hard guard/uniqueness queries remain unknown at 2,000 conflicts
and 1,000,000 propagations after these changes.

### Scoped base initialization and masked source projections

The producer follow-up identifies an explicit caller seed for the base word. A
third complete export uses only that seed, `lane 8 = 0x140005352`, and preserves
the unknown stack lane, all original source words, both tail fallbacks and the
possible symbolic-store aliases. It contains 5,170 typed nodes and 87 memory
events; the seven output cones share 2,627 nodes and 108 original byte symbols.
The seed is a constructor model assumption, not a native producer/preservation
theorem. Both earlier exports remain archived with their original scopes.

Thirty-two original symbolic models agree with the independent integer oracle
on all seven outputs. They yield three sampled target values, eight sampled
primary values and 32 values for each final tail. These counts are not complete
output sets. Reordering the bounded local phases leaves every root unchanged;
the lighter phase combinations cost roughly 0.34–1.53 ms, compared with about
11 ms for the original 512-new-node bounded standard pass. Neither timing proves
recovery, and no default strategy is changed from those unsuccessful probes.

The remaining cut representation gap is concrete: an AND with an extended
Boolean can need just one bit of an unavailable wide source. Cuts now project
only the bits retained by a mask, capped at eight, and handle single-bit extracts
the same way. Pure symbol, extract, extension, concat and NOT wiring preserves
shared bits and complements. Other projected bits remain independent shared
opaque inputs. Visits, construction work, gates and complete enumeration retain
their existing limits. An opaque projection can admit an impossible tuple; it
never supplies an original-symbol witness or an additional source restriction.

The original full tail at offset `0x1a8` now yields a three-value superset under
the default limits: `0x7d3a411876f59911`, `0x28634e30b96147a7` and
`0xa000ab116202306f`. Its cut has six live inputs and 25 nodes. First analysis
costs about 25 µs in the release run; analysis, coverage construction, native
certification and certificate checking cost about 27–32 µs per call over eleven
batches of 100 calls, excluding import. The original coverage certificate uses
one circuit node with zero conflicts and propagations. This settles that output
superset, not its individual values' reachability or the full seven-root domain.

Independent reference tests cover complete small masked domains and sparse masks
through 512 bits. Further checks cover wiring overlap, complement and sign bits,
changed partial declarations, every resource stop, spurious opaque bit pairs,
zero-search certificates and false claims requiring replayed original-symbol
models. The eight older target supersets still have checked one-node certificates;
the updated analysis-plus-coverage/check measurements are about 7.7–39 µs.
Both spellings of all three original hard guard questions remain unknown at
2,000 conflicts and one million propagations.

A separate control demonstrates why the final two tails cannot have a small
finite tuple list in this closing model. Fixing all other original input symbols
to zero leaves the sixteen original fallback bytes unrestricted. A checked native
certificate proves both tail words equal their respective eight-byte concats for
every assignment of those 128 free bits. It uses 129 circuit nodes, zero conflicts
and one propagation, with about 0.47 ms preparation and proof time. Consequently
the unrestricted closing model contains at least `2^128` distinct tail pairs.
These fixed-other-input premises establish a legal subfamily of that symbolic
model, not a narrowing of the full query or a native-entry reachability proof.

The final caller audit finds no additional source mask or Boolean relation with
both a checked producer and a preservation chain to the closing body. Entry
contracts can assume non-nullness and kernel-address bits; the latter condition
`(lane >>s 47) == -1` pins the upper seventeen bits. Candidate replay and arm
admission do not establish those premises for every native input. Partial lane
facts remain diagnostic-only, the closing constructor carries whole constant
lanes, and merged-state processing clears previously scoped possible-arm lane
facts. No new restriction on the six unrestricted qword guards follows.

### Structured full-width witnesses and independent SAT search

The original supplied full-width preimage concerns the already solved single-key
inversion at output `0x1234`; it supplies no witness for the cross-key fingerprint.
A private witness diagnostic instead gathers literal constants from each original
expression, their adjacent/complemented values, and their images through exact
single-key inverses. The six unrestricted captured guard cores each test 145
candidates; the wide fingerprint tests 136. None of these 1,006 assignments
satisfies its original query.

The same seven questions search the ranges `[0x140000000, 0x142a6d000)` and
`[0xfffff80000000000, 0xfffff80002a6d000)`, retaining their full-width source
values. These are candidate ranges rather than assumptions. All fourteen scans
of 44,486,656 assignments find no witness. Guard scans cost roughly 39–61 ms;
fingerprint scans cost about 89 ms in the recorded release runs. No range miss
is treated as a proof over an unrestricted source.

Twelve controls change only the three pair salts in the captured expressions to
plant a late witness in these ranges. Each found witness is restored through the
original byte-symbol coordinates, preserving full-width high bits, then evaluated
through the complete typed expression with the controlled salts. All twelve
return the expected target. The original captures' keys, salts and source widths
are independently audited before searching. No candidate-bank sampling change
is added to the runtime from these misses.

A separate diagnostic uses CaDiCaL 3.0.1 at commit
`818c9562f114b315a9246ced943b66b60b38e8fb`. Fresh CNF exports use the current native
AIG and ordinary or carry-save/XOR3 product encodings, without reverse-product
constraints or altered coordinates. The cases are the three hard fixtures,
their masked-pair existence control and all eight exact captured target
predicates. Every export first settles its supplied-input control through the
native solver: UNSAT controls have independently checked original-CNF DRUP
certificates, and SAT controls satisfy all original clauses.

Default external search is compared with elimination, probing, subsumption and
vivification disabled. At requested 10 ms and one-second CPU search limits, all
96 free-domain checks remain unknown. The 96 supplied-input controls return
80 UNSAT and sixteen SAT outcomes. All sixteen SAT models satisfy every original
clause and input premise, and replay through the current expression evaluator
using the full original symbol map, including captured guest bytes. External
UNSAT reports are not presented as native proof transcripts or unrestricted
exclusion certificates.

External parsing and clause admission cost about 7.5–57 ms, before search.
Actual bounded searches consume about 10.0–11.2 ms or 1.000–1.003 seconds; no
run needs its five-second process stop. Native AST/CNF generation is separate
from these timings. The additional SAT engine recovers no remaining query at
these limits, and no external dependency or default change is introduced.

### Active Gaussian elimination and startup budgets

Verbose CryptoMiniSat 5.16.0 logs establish that the earlier XOR-interface
diagnostic already ran Gaussian elimination during search. For example, the
ordinary wide fingerprint initializes a 9,125-row matrix, then compacts it to
4,627 columns. Static affine closure and active search propagation are separate
tests; enabling an XOR interface alone was not a missing capability in that run.

A further CLI diagnostic pins release commit
`2bf89cfb3e126e559d472388486327813f735f7e` and supplies all original nonlinear
clauses together with the independently extracted parity rows. It compares
automatic matrix disabling, forced retention, forced retention with startup
simplification/local search disabled, and a matrix-disabled control with startup
processing disabled. The flags follow the pinned solver's
[official option definitions](https://github.com/msoos/cryptominisat/blob/2bf89cfb3e126e559d472388486327813f735f7e/src/main.cpp).

The three complete hard fixtures and the masked-pair existence control retain
their exact 32-bit or 64-bit source domains under both ordinary and
carry-save/XOR3 encodings. At requested 10 ms and one-second bounds, all 64 free
checks return unknown. All 64 supplied-input controls return the expected
48 UNSAT and sixteen SAT results. Every SAT model satisfies all original clauses,
all supplied XOR rows and input units, agrees with independent scalar mixer
values, and replays through the current expression evaluator in both shift
spellings. These control outcomes do not establish the unrestricted exclusions;
the external UNSAT outcomes are not presented as independently checked native
certificates.

All eight one-second runs in each matrix-enabled configuration use active
matrices, and the disabled configuration uses zero in every run. At the nominal
10 ms limit, both startup-enabled configurations reach their time allowance
before initializing a usable matrix. Disabling startup processing lets six of
eight forced-matrix runs initialize one, but still supplies no verdict. The
backend's `matrix_created` flag reports initialization of the finder even when
it selects zero usable matrices; the recorded matrix counts use its explicit
`Using N matrices` messages instead.

Whole-process CPU times at the requested 10 ms limit are about 24–41 ms with
startup processing, 15–142 ms with direct forced matrices, and 12–26 ms with
direct matrix-disabled search. One-second runs consume roughly 1.01–1.12 seconds
including file parsing and startup. CNF generation and parity extraction are
outside those process timings. No run needs its five-second process stop. The
forced dynamic parity configuration therefore does not demonstrate a recovery
within a high-throughput budget, and no backend or default configuration change
is introduced.

### Exact squared-key and small-correction encodings

A private diagnostic rewrites the outer product exactly, using
`h = k * (x XOR k)` and `r = h >> (32 + (h >> 60))`:

```text
k * (h XOR r) = k² * (x XOR k) + k * (r - 2 * (h AND r))   (mod 2^64)
```

This uses the arithmetic identity `h XOR r = h + r - 2 * (h AND r)`; it does
not distribute multiplication over XOR. Since `r < 2^28`, the mathematical difference
`(h XOR r) - h` fits in a signed 29-bit word. The third encoding constructs that difference
by zero-extending both 28-bit low parts to 29 bits, subtracting, then sign-extending to
64 bits. Subtracting at 28 bits would lose the required sign/borrow information.

The three alternatives are a combined correction product, two separately scaled correction
terms, and the explicit signed 29-bit difference. All are checked against the independent
original scalar mixer on 17,280 full-width inputs across the four keys, all selector interval
endpoints and deterministic random words. These checks also verify the 28-bit shift-output
bound and the signed correction range.

The original three hard questions and the known-satisfiable masked-pair existence control
are then searched with each alternative and the original encoding, under both native and
carry-save/XOR3 configurations. All 32 free-domain searches remain unknown at 2,000 conflicts
and one million propagations. Compared with the original encoding in the same diagnostic,
the alternatives increase clauses by roughly 32–80%. Narrowing the correction does not
remove its dependency on the high bits of the inner product, while the squared-key product
and final correction addition introduce further carries. No correction rewrite is added to
the runtime; the scalar checks alone do not establish a free-domain verdict.

A separate majority prototype canonicalizes operand order and the identity
`majority(NOT a, NOT b, NOT c) = NOT majority(a, b, c)`. Permutation, complement, scalar and
existing observed-root/certificate controls pass. The twelve original hard-query fixture
variants keep the same CNF variable and clause counts and still return unknown under the
bounded native and resumed searches. This prototype is also left out of production.

### Bounded literal lookahead and carry constants

A private lookahead diagnostic temporarily chooses a literal, propagates within its
allowance, and restores the root trail and saved phases. A failed choice produces the
opposite unit as a RUP consequence. A second variant intersects the implications of both
choices: for each common value it records both conditional binary consequences before
adding the unit. Interrupted branches supply no intersection facts. Original source
widths and domains remain unchanged.

The independent checker accepts every preprocessing transcript. On 256 four-variable
CNFs at allowances 0, 1, 3 and 100, all 1,024 checks agree with exhaustive original models.
On the full mixer questions, input-bit intersections derive eleven internal constants
per fingerprint and six for uniqueness, while fixing zero original input bits. Shift-count
probes derive no additional units. Scanning all CNF variables derives 23 internal constants
per fingerprint and thirteen for uniqueness, again with zero original input bits fixed.
These same counts remain when the final query assertion is removed: the constants belong
to the mixer circuits independently of the requested exclusions.

With a one-million-propagation lookahead allowance, input probing takes roughly
0.10–0.28 ms and the complete variable scan about 2.1–4.9 ms in these release runs.
These timings exclude CNF construction, transcript checking and subsequent search.
All 48 asserted checks remain unknown after a following 2,000-conflict / one-million-
propagation search. The additional masked-pair existence control retains its known
`0x4563` model after preprocessing.

Some constant cones expose ordinary absorption and contradiction motifs such as
`a AND (a AND b)` and `NOT a AND (a AND b)`. A separate bounded, iterative AIG rewrite
prototype removes fourteen fingerprint variables / 54 clauses, and seven uniqueness
variables / 27 clauses. Its asserted lookahead/search matrix still returns unknown in
all 48 checks. This small structural reduction does not demonstrate a useful online proof
gain; neither the probing pass nor the rewrite is added to production defaults.

### Original-input decisions and binary equivalence collapse

A private diagnostic tested the three complete hard questions through the primitive CNF
adapter, retaining all 32 or 64 original input bits. Its decision policies were native
VSIDS, VSIDS restricted to unset original inputs before auxiliary variables, lowest input
bit first, and highest input bit first. The input-first variants used full Luby restarts;
the native control retained its trail reuse. These policies change search order only.
The first allowance was 2,000 conflicts / one million propagations, followed by resumed
allowances of 10,000 / five million and 100,000 / fifty million. All twelve searches remain
unknown. Some input-first runs make far fewer decisions, but still exhaust their work
allowance without a verdict. These observations do not establish a faster proof method.

Another pass performs root unit propagation, finds strongly connected components of the
binary implication graph, and substitutes the resulting signed equivalences in every
clause. It collapses 108 variables in each fingerprint CNF and 36 in the uniqueness CNF,
exposing no additional unit clauses or immediate contradiction. Root units and equivalence
clauses remain in the transformed formula. An independent RUP checker accepts every added
root unit, equivalence and substituted clause against the original CNF before search.
Repeating all four decision policies on these transformed questions leaves all twelve
searches unknown at the same allowances.

The necessary masked-pair existence question is an additional positive control: its free
searches also stay unknown, although its supplied `0x4563` assignment satisfies the scalar
predicate. Across raw and transformed CNFs, all 32 grounded checks settle correctly:
24 UNSAT exclusions with checked original-CNF transcripts and eight SAT pair checks with
complete original-clause models and independent scalar replay. These controls validate
the diagnostic transformations and supplied points, not the free-domain exclusions.
The experiments introduce no production search option or default change. Their search
timings exclude CNF construction and diagnostic transformation/checking; none is presented
as a complete online-budget recovery.

### Resolution preprocessing on the original domains

A private preprocessing diagnostic freezes every original source variable, propagates root
units, and eliminates only auxiliary variables by bounded resolution. It adds resolvents
before deleting their parent clauses, and retains the eliminated clauses for reverse model
restoration. Candidate elimination is capped at 64 occurrence pairs and 64 occurrences,
with clause-length limits of 12 or 16 and no clause-count increase per eliminated variable.
The literal-visit allowances are zero, 100,000 and one million; setup, root propagation and
heap maintenance are outside that work counter and inside the reported CPU time.

The cases are the three original hard questions, the masked-pair existence control and all
eight exact captured target equalities. At the largest allowance, elimination removes
3,091–10,915 variables, or about 22–42% of the active variables, while reducing clause
counts by about 2–9%. Preprocessing costs roughly 11.5–50.3 ms in these release runs,
excluding CNF construction, proof checking, solver setup and subsequent search. All 36
free-domain searches remain unknown at 2,000 conflicts / one million propagations.

A second pass applies bounded self-subsuming resolution before elimination. Its one-million-
literal-visit allowance shortens just one or two clauses per case. Both the initial
strengthened pass and its grounded-control repeat still have 36 unknown free-domain results.
The controls exhaustively check projected satisfiability and restored original models on
1,536 tiny cases. All preprocessing and paused-search transcripts pass independent RUP
checking. Supplying complete source inputs *after* elimination settles all 36 point controls:
30 UNSAT proofs check against the original CNF plus those input premises, and six restored
SAT models satisfy every original and input clause. These supplied points do not prove the
free-domain queries. The measured cost and unresolved verdicts do not support adding
resolution preprocessing to the high-throughput runtime.

### Joint selector and integer-equation diagnostics

The masked-pair uniqueness question was also partitioned by both selectors, giving all
256 combinations. At 1,000 conflicts / 500,000 propagations, all raw conditional cases stay
unknown. Explicitly substituting the two shift counts in each conditional expression gives
another 256 unknowns; these substituted questions are recorded separately from proofs of
the original conditional predicate. The raw cases were then rerun with a first allowance
of 1,000 conflicts / 500,000 propagations and a continued allowance of 9,000 / 4.5 million.
Every case still stays unknown, including the candidate's selector pair `(8,5)`. The total
measured CPU cost of this larger 256-case pass is about 69 seconds. Joint specialization
therefore does not supply a high-throughput proof at these limits.

An exact QF_LIA diagnostic keeps each multiplication as a modular integer equation:
`output + 2^64 * quotient = key * operand`, with Boolean bit decompositions and bounded
integer quotients. XORs and the 16 possible shift counts retain their full Boolean semantics.
The narrow input remains 32 bits and the wide input remains 64 bits. Twenty-four ground
controls check concrete multiplier/mixer values at boundaries: correct values are SAT and
one-bit output errors are UNSAT. Z3 5.1.0 still times out on each unsplit hard query under
a two-second bound. No integer backend or specialization rule was added to the library
from this unsuccessful diagnostic.

### Shared mixer-image decision priorities

A private diagnostic observes the shared first mixer image and changes only SAT
decision priorities and phases. It tests weak/strong low-bit priorities, high-bit
priorities, all-bit priorities and supplied-candidate phase controls. Every case
retains its original source width, both shift spellings and both multiplication
encodings. Free searches receive 2,000 conflicts / one million propagations,
then a resumed 6,000 / three million; these are search allowances, excluding
preparation, replay and certificate checking.

All 96 original hard-query free searches remain unknown. Across the complete
320-check matrix, the supplied-input controls have 96 independently checked UNSAT
proofs and 64 replayed original SAT models. The other 160 searches have 152 unknowns
and eight SAT models. Only the diagnostic that supplies all 64 image phases from
the externally known `0x4563` candidate solves the eight planted existence cases,
with zero conflicts and roughly 1.28–1.53 ms search. Those phases contain known
fixture information; they do not recover the original exclusions or demonstrate
a general online inference rule. No image-priority option or candidate-specific
solver default is added to production.

### Ten-millisecond target and bounded affine products

The requested target is now 10 ms per query, including circuit preparation. A
low-output-bit diagnostic retains the original 32-bit or 64-bit source and the
complete inner products and selectors. Only the outer products are truncated,
using exact modular arithmetic for 7-, 8-, 12-, 16-, 20-, 24-, 32-, 40-, 48- and
64-bit output prefixes. Six scalar boundary points check every prefix against
the original full fingerprint. The 60 checks have 28 checked supplied-input
UNSAT proofs, two supplied-input SAT models, three free models of weaker pair
conditions and 27 unknowns. No free prefix proves an original exclusion.
The seven-bit fingerprint cuts still have 5,905 or 6,833 variables: the upper
inner-product bits select the shift and feed back into those low output bits.
Reducing the output width therefore leaves substantial arithmetic search.

Another private experiment initializes every mapped SAT phase from one consistent
circuit valuation, without asserting it. Its 280 checks vary zero, all-one and
supplied-candidate valuations, with ordinary or fixed phases. All 84 free original
hard checks remain unknown. Only supplied-candidate phases recover the sixteen
planted free existence controls. These candidate-dependent successes supply no
new online inference or production search setting.

Conditional shift tables and separated fixed multiplication biases are exact in
their reference controls but increase the full circuits. Even retaining the
existing exact factors during the bias split adds variables. Those prototypes,
and a slight preference for affine plans combined with input cancellation, are
not retained from their unsuccessful unrestricted searches.

The retained change expands constant-product plans to the modular identities
`K = a*b + correction`, where `a` is one of 127 small odd factors and the
correction is zero, plus one or minus one. There are at most 381 recipes, two
multiplication stages and one final source addition or subtraction. Exact plans
win cost ties. The existing data guards and minimum 10% estimated improvement
over unfactored carry work remain. Adding the source to an even product copies
its low-zero prefix without carrying; subtraction is charged conservatively.

The initial serial scoring added preparation overhead. Bit-parallel nonadjacent
digit masks now reproduce that scoring without scanning every bit of every
candidate. Complete 16-bit coefficients, wide boundaries and 32,768 generated
64-bit coefficients compare with an independent serial-carry calculation. Both
correction signs, scalar modular identities, fixed and correlated inputs,
interrupted models and independent certificates remain covered.

Twelve original coefficient-equivalence questions that were unknown at zero
search allowance now have checked certificates in about 0.23–0.35 ms, including
preparation and checking. They cover three affine coefficient plans, full and
fixed-upper input words, and both arithmetic encodings. Their CNFs contain one
variable and two clauses. Omitting the source correction is rejected with an
original-symbol word-sampling witness; that check is not an UNSAT proof or a
claim that SAT alone rediscovered the witness within the small allowance.

The ordinary full fingerprint CNFs use about 4.8–4.9% fewer variables and clauses
than exact factorization alone; the uniqueness CNF saves about 1.3%. Four single
odd-image model queries measure roughly 0.56–0.61 ms including preparation and
original replay, compared with 0.55–0.72 ms for the earlier serial/exact planner.
Each median uses 21 batches of 50 fresh questions. These are observed costs for
those cases, not a general wall-clock guarantee.

The final 72-check original-domain matrix uses 256 conflicts and 75,000
propagations, with samples and simplification disabled. Its 36 free searches
remain unknown; all 28 supplied-input UNSAT certificates and eight original SAT
models check. The twelve free checks of the three original hard fixtures take
roughly 4.7–11.6 ms including preparation in this release run. Operation quotas
are not a strict time deadline. These full exclusions and the unrestricted
captured guards are still unresolved against the requested 10 ms target; the
coefficient-equivalence recoveries do not redefine that goal.

A further private low-bit prototype uses an exact identity for
`b * ((a * data) XOR other)` when both odd coefficients have the same residue
modulo eight. It replaces the first three product bits with a small Boolean
formula. All 4,096 low-input assignments, with deterministic high-bit noise
through widths up to 512, agree with independent wrapping arithmetic. Expression
folding legitimately removes multiplication by one at narrow widths, and the
control permits those folded cases without weakening the arithmetic comparison.
Six configurations, combining the formula, three-bit XOR cancellation and the
existing input cancellation, run 432 complete original/control checks. All 216
free searches remain unknown; the 168 supplied-input certificates and 48 original
SAT models check. Full circuits grow slightly, so the formula is not retained.
Conditional count-to-output clauses had already failed unrestricted searches in
the earlier experiment; that unchanged approach is not repeated.

The complete-query acceptance mode makes this status reproducible. In one release
run, the three hard fixtures across both spellings take 6.9–11.6 ms with ordinary
arithmetic, and 7.4–16.2 ms with carry-save multiplication and three-input XOR
encoding. All twelve return unknown and fail acceptance, including those under
10 ms. Across all ten public fixtures, ordinary arithmetic has four checked
decisions and sixteen unknowns; the compressed encoding has six checked decisions
and fourteen unknowns. Its two additional decisions are original refuting models
of the separate single-key inverse fixture, not recoveries of the hard exclusions.
Both reports retain all twenty rows despite failures. Two target-cut certificate
controls pass; a one-nanosecond diagnostic correctly rejects a checked proof as
over time. Invalid or overflowing budgets, incompatible sampling/escalation and
empty fixture selections are errors. These measurements add an acceptance check,
not a new inference rule or a recovery claim.

### Certified exhaustive decisions

The hard 32-bit fixtures have no structure a shortcut could use. Over the whole source domain,
the 36 masked conditions of `masked-pair-32-unique` follow Binomial(36, 1/2) in every bucket,
and only the planted point satisfies all of them. For low-order prefixes of 4–24 bits, no
masked bit is constant across its prefix's completions (0 of 18,432 sampled). No masked bit
correlates with any source bit beyond 3.4σ (0 of 1,152 pairs above 5σ). Bounded CDCL is still
unknown after about 7.6e5 conflicts and 100 s. The scrambled term feeds high inner-product bits
back into the low output bits, and the outer multiplication does not distribute over that XOR.
Sieves, lookup chunks, fixed-bias splits and linear methods therefore have nothing to filter on.

`Config::exhaustive_inputs` instead decides a question completely when its word-level program
has at most that many unknown input bits. Every legal assignment is evaluated, 128 at a time
per instruction, in parallel. Declared known bits, scoped assumption bits and constraints are
handled as in ordered word sampling. A failure is the first failing assignment in enumeration
order, whatever the thread count, and is replayed on the original question.

A proof with a certificate does not trust that evaluator. Its certificate is the question's
bit-blasted circuit: the same circuit that DRUP clauses encode, reduced to the cone of the
goal and constraints. `Certificate::check` simulates it at every input assignment, 1024 at a
time. Values live in a register file reused by liveness: the masked-pair circuit's 20,260
gates need 345 registers (44 KB). A goal that is a negated conjunction is simulated one
conjunct cone at a time, greedily ordered by new gates. A block stops once each lane has a
false conjunct, which is sound because any false conjunct makes the goal true. Random circuits
of up to 14 inputs agree with brute-force evaluation, including constraints and constant goals.
Block evaluation matches the per-lane evaluator at every instruction slot.

Measured with `exhaustive_inputs = 32`, certificates on, samples and simplification off, on a
hybrid 20-core host shared with other work (load average 12–34), wall times are:

| fixture | decision | certificate check |
|---|---|---|
| `masked-pair-32-unique` | 1.2–1.6 s | 7.9–8.0 s (140–144 CPU-s) |
| `fingerprint-32` | 2.2–4.5 s | 7.6–8.8 s |

The fingerprint check costs about the same as the masked pair. The first cross-key term
falsifies a conjunct at almost every assignment, so the other two terms' cones are rarely
simulated. About 9,950 of the masked pair's 20,260 gates run per block. The first segment, both
inner products and the shift selection, accounts for 8,636 of them and is needed at every
assignment. Branch misses are negligible; an AVX2 build saves only about 10%, because the
efficiency cores split 256-bit operations. Three further ideas were measured and not kept:

- Setting nearly decided lanes aside for packed batches can save at most the ~13% beyond the
  first segment, and saved nothing measurable.
- Folding block-constant high source bits into the circuit barely shrinks it. With 22 of 32
  source bits fixed, 17,275 gates remain, because the constant multipliers' carry chains stay.
- Wider registers (2048 lanes) overflow L1 and are slower.

Reading operands by reference instead of copying 128-byte registers saved about 7%.

The complete-query acceptance mode measures the whole path, preparation, decision and
certificate check included:

```sh
cargo run --release -p bitwright-bench -- --mixers fingerprint masked-pair-32-unique \
    --query-budget-ms 30000 --exhaustive-inputs 32
cargo run --release -p bitwright-bench -- --mixers fingerprint masked-pair-32-unique \
    --query-budget-ms 30000 --exhaustive-inputs 32 --carry-save --xor3
```

All eight rows of the two 32-bit fixtures pass with checked certificates: in 11.9–19.8 s under
a load average of 31–34, and within a 15 s budget in 8.3–11.1 s under a load average of 7–13.
Selecting `fingerprint-32 masked-pair-32-unique` with `--query-budget-ms 15000` exits 0. With
`fingerprint` selected the commands still exit 1, because `fingerprint-64` remains unknown.
This is not the 10 ms target: it is a complete, independently certified decision under a
raised budget.

Full-width sources remain out of reach. `fingerprint-64` needs 3 × 36 = 108 masked
conditions on a 64-bit source. The best of 2^32 random sources meets 86, and the expected
number of preimages over all 2^64 sources is about 1e-15. It is almost certainly valid and
needs an exclusion proof, not a model. The single-word captured runtime guards are three
exact 64-bit equalities over one free source word, 192 conditions on 64 bits. The best of
2^32 samples meets 138–140 per guard, and they show no prefix determination up to 48 bits
and no linear bias. Enumerating 2^64 sources at the measured rate would take decades.

Neither does a decomposition apply. Multiplication and XOR are T-functions: low result bits
depend only on low operand bits. Only the scrambled term breaks that, by moving inner-product
bit `32 + c + j` down to bit `j`. Lifting a solution from the low bits upward therefore meets
no constraint until `32 + c` source bits are chosen, for each guess of the four shift counts.
Splitting the source into halves does not separate either. The high half of each inner product
is `A_K(x_lo) + K_lo * (x_hi ^ K_hi)`, where `A_K` is the carry out of the low product, which
couples both halves in every equation. No sub-2^64 procedure for the full-width queries was
found.

The target itself argues against a `fingerprint-64` model. An OR of three 64-bit terms sets each
bit with probability 7/8, so a typical fingerprint has about 56 set bits. The target has 28, and
the probability of at most 28 is 9e-17. A structured witness search also found nothing. It tried
the six single-word guards and the fingerprint at every 33-bit value, every sign-extended
negative 32-bit value, every 32-bit value shifted into the high half, every replicated half,
every complemented 33-bit value and every 40-bit value: about 1.1e12 candidates in roughly 15 minutes. A hit would have
been an original model after replay; finding none decides nothing, and the queries stay open.
