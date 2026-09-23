# Benchmarking

`bitwright-bench` (an unpublished workspace member) measures bitwright's own operations.
The main metric is **user-space instructions retired**, not time.

```text
cargo run --release -p bitwright-bench -- --list            # what is measured
cargo run --release -p bitwright-bench                      # everything, 7 samples each
cargo run --release -p bitwright-bench -- facts simplify    # names containing "facts" or "simplify"
cargo run --release -p bitwright-bench -- --quick           # a tenth of the iterations, 3 samples
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
| `simplify/*` | The standard strategy on random DAGs, the deobfuscation strategy with the native MBA solver on linear MBA, and one simplification in a fresh context. |
| `service/*` | Building an engine (rule compilation), equality saturation, SMT-LIB export and import. |

Workloads are generated from fixed seeds (`bitwright-bench/src/workload.rs`), so every run
measures the same expressions. Setup that is not part of what a benchmark measures is excluded,
for example building the DAG whose facts are measured. It runs with the counters paused.
