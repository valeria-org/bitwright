# Proposal: charging the MBA certifier's symbolic comparison at its cost

Status: proposed, not implemented. Measured on a prototype with local switches (6a9d522 on
branch `claude/cool-taussig-d53190`, on 20fb416, the tip of `main` after 0.19.0; it reads
environment variables in the library, so it is kept off `main`). Bounding the
fallback alone changed no result measured; every higher charge changes some results under small
budgets. The choice is the user's, and any option is a "Behavior changes" entry of a minor
release (`book/src/stability.md`).

## What is charged today

Certificates count work in node evaluations: a test is charged points × nodes of both sides,
a block at a time, and the refutation sample 64 × nodes. At the engine's evidence gate that is
pass work (`Budget::pass_work`, 16 · fuel); in the normal-form solver it is the solver's own
steps (32 evaluations per step, `MbaBudget::steps`).

`symbolic_equal` counts a unit per monomial operation, and both of its callers charge those
units one for one:

- **Ahead of a long polynomial test** (`test`, since 20fb416): within
  `min(cost · lane / (2 · SYMBOLIC_UNIT), left − cost)` units, so that a comparison that
  decides nothing leaves the test affordable (the *reserve*). `SYMBOLIC_UNIT = 1024` only
  decides whether to try.
- **Where no test fits or one is over the budget** (`symbolic`, the *fallback*): run in full,
  limited only by `SYMBOLIC_TERMS` (4,096 monomials a polynomial), then charged at most what is
  left.

## Measurements

The prototype at today's settings computes what 20fb416 does: the same `--prover-budgets`
table and `--corpus-diff` report as a build of 20fb416, and the same test results.
Release builds; instructions are user-space instructions retired (hardware counters). The probe
timed each call with `Instant` on a performance core (CPU 5) of the reference machine while
other sessions loaded the rest, and subtracts its own cost (550 to 780 ns a call, measured);
its nanoseconds are for orientation.

### What a unit costs

| work | measured on | calls | units | instructions per unit | ns per unit |
|-|-|-:|-:|-:|-:|
| symbolic, ahead of a test | `--prover-budgets` question, default fuel | 12 | 516 | 2,372 | 157 |
| | `simplify/mba-nonlinear/64` corpus | 10 | 612 | 2,058 | 183 |
| | `--corpus-diff` nonlinear MBA, 64 bits | 143 | 8,334 | 2,222 | 170 |
| | `--corpus-diff` nonlinear MBA, 8 bits | 27 | 2,000 | 2,090 | 178 |
| | `--corpus-diff` random DAGs, 8 bits | 602 | 41,840 | 2,429 | 143 |
| symbolic, fallback | `--prover-budgets` question, fuel 2^14 | 12 | 516 | 2,389 | 149 |
| | random DAGs, 8 bits (gate) | 38 | 26,919 | 1,626 | 101 |
| | random DAGs, 64 bits (solver) | 78 | 145,493 | 1,190 | 73 |
| evaluation tests | the same 12 certificates, sparse test forced¹ | 12 | 3,080,616 | 11.4 | 0.51 |
| | `simplify/mba-nonlinear/8` corpus | 10 | 161,292 | 8.4 | 0.43 |
| | nonlinear MBA, 64 bits, sparse tests forced¹ | 155 | 377,129,728 | 6.5 | 0.23 |
| | random DAGs, 8 bits (gate) | 2,169 | 52,720,527 | 5.2 | 0.25 |
| small evaluation tests | linear MBA, 64 bits (signature tests, 67 units each) | 103 | 6,956 | 138 | 19 |
| refutation sample | every corpus | 12 to 1,380 | | 65 to 82 | 4.5 to 5.7 |

¹ Symbolic work charged 2^40 at the gate, so that the test runs, as before 20fb416.

On identical certificates (the consumer's question) a monomial operation costs 208 node
evaluations in instructions and 308 in time. Over the rows above the ratio to bulk evaluation
is 100 to 470 in instructions, typically 250 to 350. Small tests and the sample cost 6 to 27
times more per unit than bulk evaluation, for fixed costs per call that are not charged.

### How much of the work is symbolic

| workload | certificates decided by | instructions | pass work | per pass unit | symbolic share |
|-|-|-:|-:|-:|-:|
| `--prover-budgets` question, default fuel | symbolic, 12 of 12 | 23.2 M | 20,371 | 1,137 | 5.3 % |
| the same, sparse test forced¹ | evaluation | 56.9 M | 3,100,471 | 18.4 | 0 |
| `simplify/mba-nonlinear/64` (20 expressions) | symbolic, 8 of 9 | 32.2 M | 41,161 | 783 | 3.9 % |
| the same, forced¹ | evaluation | 182.3 M | 23,167,876 | 7.9 | 0 |
| `simplify/mba-nonlinear/8` | evaluation, 8 of 9 | 31.8 M | 195,371 | 163 | 0.7 % |
| `--corpus-diff` nonlinear MBA, 64 bits | symbolic, 120 of 132 | 295.6 M | 445,266 | 664 | 6.3 % |
| the same, forced¹ | evaluation | 2,719 M | 377,493,236 | 7.2 | 0 |
| `--corpus-diff` nonlinear MBA, 8 bits | evaluation, 118 of 132 | 299.4 M | 2,906,959 | 103 | 1.4 % |
| `simplify/mba-native/64` | signature (small) | 72.6 M | 76,005 | 955 | 0 |
| `--corpus-diff` linear MBA, 64 bits | signature (small) | 706.4 M | 353,771 | 1,997 | 0 |
| `--corpus-diff` random DAGs, 8 bits | mixed | 138.9 G | 55,550,942 | 2,501 | 0.1 % |

The symbolic comparison is a small part of the time everywhere: what is off is its charge,
not its cost. The linear rows have many instructions per pass unit for another reason: the
solver's own work (65 to 85 % of their instructions) is not pass work (see the end).

### The longest single comparison

A pair no evaluation test can take, so the certificate falls back to the symbolic
comparison: degree 6 over eight 64-bit variables (`S^6` for `S = x0 + … + x7 + 1`, 3,003
monomials), then 1,000 or 2,000 additions of the variables in two orders, through
`NativeProver` at its default budget (2^20 steps; `--symbolic-worst`):

| nodes, both sides | option | verdict | symbolic work | units charged | instructions | time |
|-|-|-|-:|-:|-:|-:|
| 2,044 | today | proved | 6,031,079 | 917,760 | 15.0 G | 1.37 s |
| 4,044 | today | proved | 12,039,079 | 789,760 | 29.9 G | 2.68 s |
| 2,044 | bound, k = 1 | unknown | 918,271 | 917,760 | 2.26 G | 233 ms |
| 4,044 | bound, k = 1 | unknown | 792,103 | 789,760 | 1.95 G | 163 ms |
| 2,044 / 4,044 | bound, k = 256 | unknown | 7,204 | 917,760 / 789,760 | 11 / 19 M | 1.6 / 2.7 ms |
| 2,044 / 4,044 | bound, k = 1024 | unknown | 2,253 | 917,504 / 789,504 | 9 / 17 M | 1.4 / 2.4 ms |

At 2^24 steps, bound with k = 1 proves both (1.3 and 2.5 s) and k = 256 stops after 14 ms.
Today the fallback is not bounded by its budget: one call took 2.7 s and was charged what was
left, 0.3 ms of evaluation. Charging more per unit does not change that while the charge is
clamped after the fact; only running the comparison within what is left does.

## The options

- **k**, units charged per unit of symbolic work: 1 (today), 64, 256, 1024.
- **Mode.** *Clamp* (today): the fallback runs in full and is charged at most what is left.
  *Bound*: it runs within `left / k` and, stopped there, reports over budget, as a test over
  the budget does (the node is not final).
- **Reserve.** Today the comparison ahead of a test runs within `(left − cost) / k`, so the
  test stays affordable. Without it, it runs within `left / k`, and a test it leaves
  unaffordable is over budget.

`k` applies to both meters, the gate's pass work and the solver's steps.

Workloads, each at the default budget and at small fuels: `--prover-budgets`; the corpora of
the `simplify/mba-native/*` and `simplify/mba-nonlinear/*` rows (20 expressions as one run)
and `--corpus-diff`'s six corpora under its "defaults" configuration (200 inputs each), at
`Budget::default()` and `Budget::fuel(2^18)` down to `2^8`, every root's result text compared
(`--symbolic-sweep`); the `--corpus-diff` report itself; and `compare/` bw-nf on CoBRA's
datasets (76,080 lines, 75,737 scored) at the default budget and fuels 2^12 and 2^10, every
answer compared.

## Results

### `--prover-budgets`

The invertible-mix table is the same under every option. The MBA-heavy question:

| option | pass work at 2^14, 2^16, default | rows that change |
|-|-:|-|
| today | 20,371 | |
| bound, k = 1 | 20,371 | none |
| k = 64, any mode | 52,879 | none |
| k = 256, any mode, either reserve | 151,951 | none |
| k = 1024, any mode, either reserve | 548,239 (2^16, default) | 2^14: stopped by pass work at 262,144 units, 41 of 48 settled instead of 48, unknown after 20,000 conflicts (15.7 G instructions) instead of proved (23 M) |

Fuels 2^12 and below stop on node visits before the MBA phase matters, under every option.

### Corpora, root by root

Roots whose result changed against today, by fuel; every change makes a result larger. The
linear MBA corpora, the `mba-native` rows and random DAGs at 64 bits are unchanged at every
fuel under every option, as is the default budget everywhere.

| option | 2^18 | 2^16 | 2^14 | 2^12 | 2^10 | 2^8 |
|-|-:|-:|-:|-:|-:|-:|
| bound, k = 1, either reserve | 0 | 0 | 0 | 0 | 0 | 0 |
| clamp, k = 64 | 0 | 0 | 4 | 1 | 10 | 3 |
| bound, k = 64, no reserve | 0 | 0 | 0 | 1 | 10 | 3 |
| clamp, k = 256 | 1 | 0 | 2 | 1 | 120 | 6 |
| bound, k = 256, no reserve | 1 | 0 | 0 | 1 | 118 | 6 |
| clamp, k = 1024 | 1 | 0 | 17 | 61 | 224 | 6 |

The roots at 2^10 and 2^8 are nonlinear MBA (at k = 256: 62 of 200 at 64 bits, 56 of 200 at 8
bits), the single ones at 2^18 and 2^12 a random DAG at 8 bits, 15 of k = 1024's 17 at 2^14 the
`mba-nonlinear/64` bench corpus. Pass work at the default budget grows on nonlinear MBA at 64
bits 2.2 times (k = 64), 5.8 times (256), 20 times (1024); on the `mba-nonlinear/64` corpus
1.9, 4.8 and 16 times; on random DAGs at 8 bits 1.08, 1.31 and 1.50 times.

Instructions do not change under bound without the reserve, at any fuel (−1.0 to +1.2 %). With
the reserve, `k > 1` skips the comparison where `left` is between `cost` and `cost + k · per`
and runs the long test instead: nonlinear MBA at 64 bits and fuel 2^14 takes 296 M
instructions today, 318 M at k = 64 and 360 to 370 M at k = 256 (15 sparse tests in place of
symbolic proofs, 22 times the pass work); its 2^14 changes above come from that.

### The `--corpus-diff` report, default budget

Under bound with k = 1 and under k = 64 the report is today's apart from the cost columns.
Under k = 256 and 1024 every result is too; on random DAGs ("defaults") the MBA service makes
one more call, finds two fewer "no simpler" and two more "exhausted" at both widths: the
solver's own budget, where its certificates are charged too.

### `compare/` bw-nf on CoBRA's datasets

Answers changed against today and lines solved (answer no larger than the ground truth):

| option | default | 2^12 | 2^10 | pass work, default |
|-|-|-|-|-:|
| today | 75,734 solved | 69,833 | 63,280 | 1.33 G |
| bound, k = 1, either reserve | 0 changed | 0 | 0 | 1.00× |
| clamp, k = 64 | 1, 75,734 | 74, 69,782 | 857, 62,439 | 1.16× |
| bound, k = 64, either reserve | 1, 75,734 | 67, 69,787 | 825, 62,470 | 1.16× |
| clamp, k = 256 | 1, 75,734 | 595, 69,291 | 2,503, 60,818 | 1.48× |
| bound, k = 256, either reserve | 1, 75,734 | 549, 69,334 | 2,482, 60,843 | 1.48× |
| clamp, k = 1024 | 6, 75,734 | 2,668, 67,234 | 2,868, 60,457 | 2.09× |

Every changed answer is larger but three of bound k = 256's at 2^10. At the default budget the
changed answers are OSES lines without ground truth (not scored) whose runs take 5.6 to 13.3 M
pass units today and now stop at the 2^26 cap; exact answers stay 49,869. At 2^12 and 2^10 the
changes are mostly on the polynomial and nonlinear sets (`mba_flatten`, `pldi_poly`,
`mba_obf_nonlinear`, `qsynth_ea`, `pldi_nonpoly`). On CoBRA the reserve makes no difference:
at these fuels the tests are over the budget outright, so the fallback decides.

### Tests

Under bound with k = 1 the suite passes unchanged (896 tests with all features). Under bound
with k = 256, with or without the reserve, 893 pass and three fail, each because it pins
today's rate:
`mba::tests::certify::a_long_test_tries_the_symbolic_comparison_first` (43 units spent, now
11,008), `mba::tests::certify::certificates_are_sized_and_budgeted` (the comparison costs at
most 64 units, now 5,632) and `tests/prove_budgets.rs` `simplification_within_a_budget` (small
fuels stop on node visits; one now stops on pass work).

## Reading the numbers

- **Cost against charge.** A unit of symbolic work costs about 250 to 350 node evaluations.
  The default fuel's pass work, 2^26 units, is 15 to 35 ms of bulk evaluation but 10 s of
  symbolic comparison, and the fallback is not bounded at all. At k = 256 the cap bounds both
  to the same order (about 40 ms of comparison).
- **Time does not change.** Raising `k` moves units, not work: instructions are today's at the
  default budget under every option, and at every fuel under bound without the reserve.
- **Results change only under small budgets, and only where symbolic certificates prove
  answers.** That is nonlinear and polynomial MBA; linear MBA is proved by signature tests,
  never symbolically. A higher charge only stops work sooner, so every change is a larger
  result (three exceptions, where an earlier stop left budget for later work).
- **More fuel brings the results back, at the same cost.** Under k = 256, a host that wants
  today's small-fuel results raises its fuel about four times: nonlinear MBA at fuel 2^12
  matches today's 2^10 (901 nodes at 64 and at 8 bits) for 1 and 4 % more instructions; CoBRA
  at 2^12 solves 69,334 lines against today's 63,280 at 2^10.
- **The reserve only costs with `k > 1`.** It binds when `left` is between `cost` and
  `cost + k · per`; there it runs the long test where the comparison would have been cheaper.
  At k = 1 it never bound (removing it changed nothing measured); at k = 64 and 256 removing
  it removed the extra instructions and every change at 2^14.
- **The consumer's question** is unchanged at every fuel up to k = 256 (151,951 units fit the
  262,144 of fuel 2^14); k = 1024 breaks it at 2^14.

## Recommendation

**Bound the fallback and charge k = 256, without the reserve, as one behavior change in a
minor release.** 256 is the measured rate (208 on the consumer's own certificates in
instructions, 308 in time; 250 to 345 on the corpora). It makes the fuel a bound on the time
of every certificate kind of the same order, closes the unbounded fallback (2.7 s in one call
today, 2.7 ms after), keeps every scored result at the default budget and the consumer's
question at every fuel, and costs nonlinear and polynomial results under small fuels (CoBRA
solved 0.7 % fewer at 2^12, 3.8 % fewer at 2^10), which about four times the fuel more than
restores, at about the same instructions. 0.19.0 is published and 20fb416 is on `main` for the
next release, so the change would go into 0.20.0 with it.

If no small-budget result may change, **bound the fallback alone, at k = 1**: nothing measured
changed (every workload, budget and test above), and the unbounded case drops from 1.4 to 2.7 s
to 0.16 to 0.23 s at the solver's default budget, but symbolic work stays charged about 250
times below its cost. k = 64 sits between the two (a third of k = 256's changes on CoBRA at
2^10, an eighth at 2^12; charged about four times below its cost). Not k = 1024, the ordering
constant's value: it charges three to four times above cost and turns the consumer's question
at fuel 2^14 from proved in 23 M instructions into unknown after a search of 15.7 G.

## If accepted

- `mba/certify.rs`: a constant for the rate (256 evaluations per monomial operation, with the
  measurement), used by `test` (try within `min(cost · lane / (2 · SYMBOLIC_UNIT),
  left / rate)`, charge `work · rate`, and return over budget when the test no longer fits)
  and by `symbolic` (limit `left / rate`, over budget when it stops there, charge
  `work · rate`). The comparison checks its limit after each node, so it can pass it by one
  node's polynomial (at most 4,096 monomials; a product is checked before it is formed).
  Whether `SYMBOLIC_UNIT` (1024, ordering only) becomes the same constant is
  open: the measured ratio says 256 for both, and a lower ordering constant tries the
  comparison ahead of shorter tests (verdicts unchanged; pass work and attribution move; not
  measured here).
- Docs: `Meter`, `Budget::pass_work` (certificate evaluations, and symbolic work at the rate),
  `MbaBudget::steps`, `NativeProver`, design §9, the book's budget section, and the changelog's
  "Behavior changes".
- Tests: the three above, restated at the rate.
- The prototype's switches (`mba::probe`, environment variables), the bench modes
  (`--symbolic-sweep`, `--symbolic-cost`, `--symbolic-worst`) and the `compare/` knobs
  (`BW_FUEL`, `BW_ANSWERS`) are for measuring and are not meant to land.

## Seen on the way, not part of this

- **The solver's own work is not pass work.** 29 to 99 % of the instructions of the corpora
  are in `MbaSolver::solve` (the prover's question is answered from the solver's memory after
  a warm-up), bounded by `mba_calls` (fuel / 1024 calls, 4,096 at the default) times the
  solver's own per-call budget (`MbaBudget::steps`, 2^20, not scaled by the fuel). On random
  DAGs that is 137 G of the 138.9 G instructions for 200 DAGs of 40 nodes, 28 M a call.
- **Fixed costs per call are not charged.** A small certificate costs 25 to 30 k instructions
  whatever its units, the refutation sample 70 to 130 k a call (so 65 to 138 instructions a
  unit against 5 to 11 for bulk evaluation).
- **Evaluation units are not weighted by lane width** when charged (a 128-bit lane costs about
  twice a 64-bit one, a wider one eight times), only in `MAX_EFFORT` and the comparison's cap.

## Reproducing

```text
cargo build --release -p bitwright-bench
BW_SYMBOLIC_CHARGE=256 BW_SYMBOLIC_MODE=bound BW_SYMBOLIC_RESERVE=0 \
    target/release/bitwright-bench --prover-budgets
BW_SYMBOLIC_CHARGE=256 BW_SYMBOLIC_MODE=bound BW_SYMBOLIC_RESERVE=0 \
    target/release/bitwright-bench --symbolic-sweep sweep-256.tsv
python3 tools/symbolic-charge/cmp_sweep.py sweep-1.tsv sweep-256.tsv
CARGO_TARGET_DIR=target/probe cargo build --release -p bitwright-bench --features probe
target/probe/release/bitwright-bench --symbolic-cost     # instructions and time per unit, by kind
target/probe/release/bitwright-bench --symbolic-worst    # the longest single comparison
```

In `compare/`, `BW_FUEL=N` runs at `Budget::fuel(2^N)` and `BW_ANSWERS=FILE` appends every
answer; `tools/symbolic-charge/cmp_answers.py` and `cmp_compare.py` compare runs (see
`tools/symbolic-charge/README.md`).
