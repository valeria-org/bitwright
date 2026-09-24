# Benchmarking

`bitwright-bench` (an unpublished workspace member) measures bitwright's own operations.
The main metric is **user-space instructions retired**, not time.

```text
cargo run --release -p bitwright-bench -- --list            # what is measured
cargo run --release -p bitwright-bench                      # everything, 7 samples each
cargo run --release -p bitwright-bench -- facts simplify    # names containing "facts" or "simplify"
cargo run --release -p bitwright-bench -- --quick           # a tenth of the iterations, 3 samples
cargo run --release -p bitwright-bench -- --corpus-diff     # results under proposed MBA defaults
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
| `facts/*` | Facts of every node of a fresh DAG (`cold`), a cached query (`warm`), proofs, and a fresh three-node context per query (`tiny-context`, the shape of a consumer that builds one context per instruction). |
| `constraints/*` | Assuming 40 predicates (orderings and masks), and facts under 40 assumptions. |
| `simplify/*` | The standard strategy on random DAGs; the deobfuscation strategy with the MBA service, bitwright's own evidence only: `mba` (the signature solver) and `mba-native` (the normal-form solver) on linear MBA, `mba-nonlinear` (normal-form) and `mba-nonlinear-sig` (signature) on nonlinear MBA; and one simplification in a fresh context. |
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

bitwright 0.7.0, `cargo run --release -p bitwright-bench` (Rust 1.98, Linux, one performance
core of an Intel Core Ultra 7 265). Times are the fastest of 7 runs of the thread's CPU time;
instructions are the median.

| Operation | CPU time | Instructions |
|-|-|-|
| A 64-bit value operation (add, mul, udiv, shl) | 8 ns | 157 to 169 |
| A 512-bit multiplication / division | 30 ns / 1.4 µs | 831 / 38,458 |
| Building a node (hash-consing and canonicalization) | 50 ns | 1,024 |
| Evaluating a node | 30 ns | 482 |
| The facts of a node, computed (known bits and ranges) | 0.42 to 0.54 µs | 5,630 to 6,840 |
| A cached fact query | 28 ns | 378 |
| Parsing a 60-node expression | 17 µs | 270,000 |
| Simplifying a random 40-node expression | 0.37 ms | 5.5 M |
| Simplifying in a fresh three-node context | 4.7 µs | 78,400 |
| Deobfuscating a linear MBA expression (native solver) | 0.40 ms | 4.9 M |
| Deobfuscating a nonlinear MBA expression (native solver, 64 bits) | 1.3 ms | 36 M |
| Building an engine (linking the built-in rules) | 5.8 µs | 90,600 |
| SMT-LIB export / import, per node | 0.28 / 0.57 µs | 7,560 / 13,330 |

On the suite's MBA inputs the native solver shrinks 20 linear MBA expressions from 125 to 83
nodes and 20 nonlinear ones from 141 to 25 (the signature solver: 92 and 71).

## Corpus diff

`--corpus-diff` measures no instructions. It runs the deobfuscation strategy with the MBA
service on generated corpora (200 linear MBA inputs, 200 nonlinear MBA inputs and 200 random
DAGs, each at 8 and 64 bits) under three configurations: the current defaults (the signature
solver, backend certificates trusted), the same solver with bitwright's own evidence only, and
the proposed defaults (the normal-form solver, bitwright's own evidence only). It prints
markdown: per corpus the result sizes, how many results change and in which direction, the
user-space instructions each configuration took (and its wall time, for orientation only), the
MBA service's answers and refusals, and examples of changed results. It is the evidence for a change of defaults, which
changes behavior; see `docs/proposals/`.

## Comparing with other engines

`bitwright-bench` measures bitwright against itself. [`compare/`](../compare/README.md)
measures it against other symbolic engines on public MBA datasets (CoBRA's collection, about
76,000 expressions): egg with bitwright's equations and with MBA identities, CoBRA (the C++ tool
and its Rust port), Triton (through LLVM, and its synthesis), Z3, Bitwuzla, cvc5, claripy and
Miasm. Every answer is checked against its input and sized in bitwright's canonical form, so
all engines are scored the same way: how often each reaches the dataset's ground truth, how
fast, and with how much heap. Its `versus-smt` compares bitwright's simplifier with the
simplifiers of z3 and Bitwuzla, through their C APIs, on random bit-vector DAGs over the
operators SMT-LIB has natively and on 580 identities in six fact sets (`compare/facts/`:
bit-vector algebra, number theory, orders, slices, bit tricks, canonical forms). It is its own Cargo workspace and needs the other engines
installed; its README has the setup. The top-level README reports both comparisons
([Performance](../README.md#performance)).
