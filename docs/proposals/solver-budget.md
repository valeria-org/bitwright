# Proposal: bounding the MBA solver's work by the engine's fuel

Status: the recommendation (`Budget::mba_steps = 4 · fuel`, `MbaSolver::solve_counted`, with
the symbolic-charge proposal's charge) is implemented on `main` after 0.20.0. The solver counts
its steps through its meters' shared count, not the prototype's thread-local counter. Measured on
a prototype with local switches (cc3df21 on
branch `claude/gracious-lamarr-d02f7e`, on top of the symbolic-charge prototype and proposal,
6a9d522 and c39d8df, on 20fb416, the tip of `main` after 0.19.0; it reads environment variables
in the library, so it is kept off `main`). Every option that bounds the
solver changes some results under small budgets; none of the recommended ones changes a scored
result at the default budget. The choice is the user's, and any option is a "Behavior changes"
entry of a minor release (`book/src/stability.md`).

## What bounds the solver today

The engine charges a solver call one `mba_calls` unit (`fuel / 1024` calls, at least one) and
runs it under `MbaConfig::budget.steps`, 2^20 by default and not scaled by the fuel (the prover's
engine uses `MbaConfig::default()`). Within a call, `NormalFormSolver` counts a step per node
visited, table word combined, monomial product, term or table entry rendered, and one per 32
node evaluations of its own certificates. None of it reaches pass work, the fuel's main cap on
MBA work. So a run at `Budget::fuel(f)` may spend:

| fuel | pass work | solver calls | solver steps, at most |
|-|-:|-:|-:|
| 2^8, 2^10 | 4,096; 16,384 | 1 | 1.0 M |
| 2^12 | 65,536 | 4 | 4.2 M |
| 2^14 | 262,144 | 16 | 16.8 M |
| 2^16 | 1.0 M | 64 | 67 M |
| 2^18 | 4.2 M | 256 | 268 M |
| 2^22 (default) | 67 M | 4,096 | 4.3 G |

About a thousand solver steps per unit of fuel, against 16 units of pass work. `design.md` §9
says a question's time is bounded by its budget, "about 40 to 60 ns per step … tens of
milliseconds at the default 2^20": true on average, not per call (below).

## Measurements

Release builds. Instructions are user-space instructions retired (hardware counters, both PMUs
summed); CPU time is the thread's (`CLOCK_THREAD_CPUTIME_ID`) on the performance cores (CPUs
0–7) of the reference machine while other sessions loaded every core, so its numbers are for
orientation. The prototype's probe (`mba::probe`, feature `cost-probe`) records every solver
call the engine makes: its steps, instructions and CPU time. At today's settings the prototype
computes what 20fb416 does: the same `--symbolic-sweep` result for each of the 8,960
root-and-budget pairs as the symbolic-charge prototype's own baseline, the same
`--prover-budgets` table, the same answer on each of CoBRA's 76,080 lines at the default budget
and fuels 2^12 and 2^10, and the test suite (896 tests with all features) passes.

### Per call

The default budget. Per call: median / 99th percentile / maximum; steps of all calls (memo hits
count 0); instructions and CPU nanoseconds per step over the calls that solved (and, in
parentheses, the per-call ratio's 1st percentile and maximum over calls of at least 1,000
steps); and the solver's share of the runs' instructions.

| corpus | calls (memo hits) | instructions per call | CPU per call | steps per call | instructions per step | ns per step | solver share |
|-|-:|-:|-:|-:|-:|-:|-:|
| bench `mba-native/{8,64}` | 66 (0) | 1.7 M / 2.7 M / 49.9 M¹ | 196 µs / 314 µs / 4.7 ms¹ | 2 k / 4 k / 4 k | 930 (502 to 1,025) | 100 | 82 % |
| bench `mba-nonlinear/{8,64}` | 36 (0) | 829 k / 3.9 M / 3.9 M | 88 µs / 379 µs / 379 µs | 859 / 7 k / 7 k | 624 (400 to 1,125) | 67 | 65 % |
| `--corpus-diff` linear MBA | 786 (118) | 1.1 M / 3.0 M / 4.1 M | 122 µs / 338 µs / 472 µs | 2 k / 4 k / 5 k | 685 (492 to 1,148) | 77 | 65 % |
| nonlinear MBA | 566 (448) | 7 k / 3.5 M / 3.6 M | 2 µs / 365 µs / 374 µs | 0 / 7 k / 7 k | 683 (451 to 1,165) | 74 | 30 % |
| random DAGs, 8 bits | 4,870 (39) | 16.2 M / 170 M / 1.11 G | 1.7 ms / 16.9 ms / 103 ms | 39 k / 479 k / 1.0 M | 392 (106 to 7,253) | 39 | 99 % |
| random DAGs, 64 bits | 4,894 (37) | 15.7 M / 172 M / 414 M | 1.7 ms / 17.5 ms / 64 ms | 40 k / 459 k / 1.0 M | 383 (103 to 5,220) | 40 | 99 % |
| 630 more random DAGs² | 25,552 (144) | 15.3 M / 181 M / 10.5 G | 1.8 ms / 19.6 ms / 949 ms | 30 k / 529 k / 1.0 M | 431 (120 to 13,384) | 48 | 99 % |
| CoBRA, all 76,080 lines | 73,315 (27,100) | 1.3 M / 31.4 M / 333 M | 175 µs / 3.7 ms / 30.6 ms | 2 k / 201 k / 1.0 M | 234 (85 to 35,548) | 28 | 45 % |
| SiMBA linear sets³ | 10,132 (6,285) | 13 k / 11.6 M / 14.5 M | 3 µs / 1.3 ms / 2.0 ms | 0 / 143 k / 155 k | 129 (79 to 1,105) | 15 | 10 % |
| GAMBA, NeuReduce, BLAST³ | 50,077 (19,309) | 1.3 M / 27.9 M / 123 M | 176 µs / 3.3 ms / 15.9 ms | 2 k / 191 k / 269 k | 202 (122 to 35,548) | 25 | 54 % |
| polynomial sets³ | 6,131 (738) | 2.2 M / 19.4 M / 81.5 M | 301 µs / 1.9 ms / 7.2 ms | 4 k / 40 k / 49 k | 556 (163 to 1,846) | 62 | 34 % |
| QSynth (`qsynth_ea`) | 1,534 (184) | 4.4 M / 102 M / 229 M | 532 µs / 11.3 ms / 22.6 ms | 15 k / 601 k / 960 k | 208 (125 to 1,402) | 25 | 91 % |
| OSES (fast, slow) | 5,392 (547) | 4.4 M / 110 M / 333 M | 496 µs / 11.3 ms / 30.6 ms | 8 k / 383 k / 1.0 M | 391 (152 to 3,592) | 41 | 80 % |

¹ The first call at 8 bits builds the synthesis table's 8-bit index (49.9 M instructions, once
per process and width); the table itself costs 135 M (14 ms) on the first call of a process.
² `--solver-dags`: 100 DAGs of 100 nodes over 4 symbols at 8 and at 64 bits and over 8 symbols,
100 of 60 nodes over 6, 100 of 40 nodes with the heavy operators, 50 of 200 nodes over 6 at 8
and at 64 bits, 30 of 400 nodes over 8; the bench's generator and seeds.
³ SiMBA linear: `e1`–`e5`, `pldi_linear`, `msimba`; GAMBA: `loki_tiny`, `mba_flatten`,
`mba_obf_*`, `neureduce`, `syntia`, with SiMBA's `test_data` and `blast_dataset*`; polynomial:
`pldi_poly`, `pldi_nonpoly`, `multivariate64`, `univariate64`, `permutation64`.

A step costs 383 to 930 instructions on average on the bench and `--corpus-diff` corpora (40 to
100 ns), 234 on CoBRA's lines: the mba-defaults proposal's 40 to 60 ns is the average. One call's
steps cost up to 13,384 instructions each on random DAGs and 35,548 on CoBRA's lines. On the
bench and `--corpus-diff` corpora (random DAGs dominate) 92 % of the instructions are the
solver's own normal forms and renderings (rendering candidates alone 56 %), 4 % the rest of its
certificates, and 2 % certificate work charged nothing at all (below).

### Per run

What one engine run spends in the solver at the default budget:

| corpus | runs asking | steps per run, p50 / p90 / p99 / max | instructions per run, p50 / p99 / max | CPU per run, max |
|-|-:|-:|-:|-:|
| random DAGs, 8 bits | 200 | 1.39 M / 3.48 M / 5.27 M / 7.02 M | 611 M / 2.02 G / 3.53 G | 311 ms |
| random DAGs, 64 bits | 200 | 1.60 M / 3.08 M / 5.09 M / 6.84 M | 613 M / 2.05 G / 2.35 G | 247 ms |
| CoBRA lines | 36,346 | 3.6 k / 84 k / 348 k / 44.0 M | 5.9 M / 71.7 M / 30.8 G | 3.05 s |

Two CoBRA lines spend more than 2^24 steps (`oses_slow` line 9: 1,962 calls, 44 M steps, 30.8 G
instructions; `oses_fast` line 265: 21 M) and seven more than 2^22, all OSES lines without a
ground truth (not scored); 33 more than 2^20, of them 17 scored QSynth lines.

### What the fuel bounds today

Instructions of the bench and `--corpus-diff` corpora (`--symbolic-sweep`: the 400 random DAGs,
and the other eight corpora together), and of bw-nf on CoBRA's lines, by fuel:

| fuel | default | 2^18 | 2^16 | 2^14 | 2^12 | 2^10 | 2^8 |
|-|-:|-:|-:|-:|-:|-:|-:|
| random DAGs | 275.5 G | 276.3 G | 275.4 G | 128.6 G | 29.9 G | 10.8 G | 0.2 G |
| MBA corpora | 2.25 G | 2.20 G | 2.21 G | 2.13 G | 2.05 G | 1.59 G | 0.54 G |
| CoBRA lines¹ | 627.9 G | | | 516.9 G | 431.2 G | 237.8 G | |

¹ Every line's engine run, through the probe build of `compare/`.

At a 64th of the default fuel random DAGs cost what they cost at the default, and at a 1,024th
still a ninth. Fuels at or below 2^8 stop on node visits before the MBA phase matters.

### The longest single call

Within the default `MbaLimits` (8 variables, 2,048 nodes), `NfOptions` and `MbaBudget`, a
question asked of a fresh solver at 2^20 steps, evidence off as the engine asks
(`--solver-worst`):

| question | instructions | CPU | steps | answer |
|-|-:|-:|-:|-:|
| the longest on the bench and CoBRA corpora (a 28-node fragment of a 40-node random DAG, 8 bits) | 1.11 G | 98 ms | 967,870 | simplified |
| the longest of the 630 more random DAGs (a 44-node, 5-variable fragment of a 200-node DAG, 8 bits) | 10.8 G | 0.97 s | 988,829 | no simpler |
| the same after a hill climb of 200 one-node mutations (`--solver-search`) | 148.4 G | 9.56 s | 1,048,576 | exhausted |

98 % of the last one is the certifier's symbolic comparison inside a certificate the solver
runs on itself (dropping a dependent atom, `nf::drop_dependent_atoms`). The compositional
certificate (`Compose`) compares pairs of nodes; a pair whose direct test is over the budget
falls back to `symbolic`, which runs in full and is charged at most what is left. Once the
call's steps are spent, every test is over the budget, so every pair runs the full comparison
for free: the symbolic-charge proposal's unbounded fallback, reached through the solver's own
step meter. One call of 2^20 steps runs 9.6 s.

With the symbolic-charge proposal's recommendation (256 units per monomial operation, the
fallback bound by what is left, no reserve), the same question costs 0.33 G instructions (27 ms);
with its bound alone (1 unit per operation), 56.9 G (3.6 s). A hill climb under the
recommendation (150 mutations from each of the two longest) found at most 4.17 G (363 ms): half
of it the compositional certificate's check of each pair's skeletons at the sample
(`Compose::agrees`, scalar evaluation) and 29 % building and comparing the skeletons, both
charged nothing; 13 % the tests that are charged.

## The options

Each ties the solver's steps to the run's budget; a call's step limit is never above
`MbaBudget::steps`:

- **scale** (rate R = 64): each call within `pass-work limit / R` (the fuel / 4: 2^20 at the
  default); nothing charged. A per-call cap only: a run's total is its number of calls times it.
- **derive** (R = 8): each call within `pass work left / R`; nothing charged.
- **charge** (R = 8): each call within its configured steps; afterwards the steps it spent are
  charged as pass work, R units each, at most what is left.
- **bound** (R = 4, 8, 32; at 8 also with the limit rounded down to a power of two): each call
  within `pass work left / R`, then charged R units of pass work per step it spent.
- **account** (c = 4, 16): an account of its own of `c · fuel` steps (2^24 and 2^26 at the
  default); each call within what is left of it, then charged to it the steps it spent.

Each also with the symbolic-charge recommendation (k = 256, bound, no reserve), marked "sym".

A charge must not depend on the solver's memory. The solver remembers its last 1,024 answers by
question and budget, and a remembered answer cost nothing, so under every charging option a
question asked twice was charged once, and results depended on what the process had asked
before (`--prover-budgets` asks each row twice: "NOT REPRODUCIBLE" at 2^14 and 2^16 under every
charging option). The prototype's memo keeps the steps each answer cost and reports them again on
a hit: the same charge whether remembered or not. Every result below is with that.

The engine has no way to learn a solver's steps today (`MbaSolver::solve` returns the answer
only); the prototype reads them from a thread-local counter of the solver's step meters.

## Results

### `--prover-budgets`

Every MBA-heavy row's answer is the same under every option: the 48-identity question is
proved at 2^14, 2^16 and the default. Its pass work there:

| option | pass work at 2^14, 2^16, default |
|-|-:|
| today, scale, derive, account 4, account 16 | 20,371 |
| bound 4 | 34,115 |
| bound 8 (exact or rounded), charge 8 | 47,859 |
| bound 32 | 130,323 |
| sym, sym + account 4 | 151,951 |
| sym + bound 4 | 165,695 |

All fit fuel 2^14's 262,144 units; its four solver calls spend 3,436 steps. Fuels 2^12 and below
stop on node visits before the MBA phase matters, under every option.

The invertible-mix table is the same under every option but scale 64 and bound 32. Under
those, at fuel 2^12, simplification decides 18 of the 28 questions instead of 27 and leaves 9
unknown after 20,000-conflict searches: 32.8 G instructions instead of 0.24 G. Their calls there
may take 1,024 and at most 2,048 steps, less than those questions' calls need (the other
options allow 8,192 or more).

### Corpora, root by root

`--symbolic-sweep`: the bench MBA rows' corpora and `--corpus-diff`'s six corpora under its
"defaults" configuration, 1,280 roots, each root's result text against today's at the default
budget and six fuels. Roots changed (of them larger):

| option | default | 2^18 | 2^16 | 2^14 | 2^12 | 2^10 | 2^8 |
|-|-:|-:|-:|-:|-:|-:|-:|
| scale 64 | 0 | 12 (11) | 29 (27) | 35 (33) | 227 (223) | 454 (452) | 16 (16) |
| derive 8 | 0 | 0 | 2 (2) | 10 (10) | 4 (4) | 111 (111) | 14 (14) |
| charge 8 | 0 | 47 (41) | 70 (65) | 91 (88) | 62 (60) | 326 (326) | 30 (28) |
| bound 4 | 0 | 18 (17) | 54 (48) | 44 (43) | 11 (11) | 69 (69) | 14 (14) |
| bound 8 | 0 | 45 (39) | 64 (59) | 69 (67) | 40 (39) | 184 (184) | 14 (14) |
| bound 8, rounded | 0 | 32 (29) | 58 (53) | 61 (57) | 24 (23) | 236 (234) | 16 (16) |
| bound 32 | 7 (7) | 67 (62) | 98 (93) | 90 (85) | 118 (118) | 449 (447) | 16 (16) |
| account 4 | 0 | 9 (8) | 31 (29) | 50 (35) | 32 (12) | 9 (3) | 8 (8) |
| account 16 | 0 | 0 | 8 (7) | 34 (18) | 21 (10) | 7 (3) | 0 |
| sym | 0 | 1 (1) | 0 | 0 | 1 (1) | 118 (118) | 6 (6) |
| sym + account 4 | 0 | 9 (8) | 31 (29) | 50 (35) | 32 (12) | 127 (121) | 14 (14) |
| sym + bound 4 | 0 | 19 (18) | 54 (48) | 54 (52) | 21 (21) | 252 (252) | 14 (14) |

The changes at 2^10 and 2^8 are nonlinear and linear MBA (sym's 118 at 2^10 are the
symbolic-charge proposal's own), the others random DAGs. Under the accounts some random DAGs come
out smaller: a solver call cut short leaves the node to the rules after it.

The random DAGs' instructions:

| option | default | 2^18 | 2^16 | 2^14 | 2^12 | 2^10 |
|-|-:|-:|-:|-:|-:|-:|
| today | 275.5 G | 276.3 G | 275.4 G | 128.6 G | 29.9 G | 10.8 G |
| scale 64 | 275.6 G | 163.4 G | 73.0 G | 17.5 G | 2.6 G | 0.9 G |
| derive 8 | 275.4 G | 274.0 G | 252.4 G | 58.9 G | 6.8 G | 1.2 G |
| charge 8 | 275.3 G | 82.2 G | 30.3 G | 21.0 G | 18.7 G | 10.8 G |
| bound 4 | 275.6 G | 145.8 G | 42.2 G | 14.1 G | 5.7 G | 1.5 G |
| bound 8 | 275.3 G | 76.5 G | 24.1 G | 9.0 G | 4.2 G | 1.2 G |
| bound 8, rounded | 275.6 G | 80.9 G | 26.5 G | 11.5 G | 4.1 G | 1.1 G |
| bound 32 | 232.6 G | 24.1 G | 9.0 G | 4.3 G | 1.9 G | 0.9 G |
| account 4 | 275.6 G | 147.7 G | 43.6 G | 15.5 G | 7.0 G | 1.7 G |
| account 16 | 275.7 G | 273.0 G | 147.6 G | 42.7 G | 13.5 G | 3.0 G |
| sym | 275.5 G | 274.6 G | 274.5 G | 128.2 G | 29.8 G | 10.8 G |
| sym + account 4 | 275.4 G | 147.4 G | 43.6 G | 15.4 G | 7.0 G | 1.7 G |
| sym + bound 4 | 275.4 G | 145.7 G | 42.1 G | 14.0 G | 5.7 G | 1.5 G |

The other corpora's instructions grow at small fuels where a call's limit varies from call to
call (the solver's memory is keyed by the limit): at 2^18, 2.20 G today, 2.35 G under account 4,
2.62 G under bound 4, 2.21 G under bound 8 rounded to powers of two.

### The `--corpus-diff` report, default budget

Under sym + account 4 and sym + bound 4 the report is today's apart from the cost columns and,
on random DAGs ("defaults"), one more solver call, two fewer "no simpler" and two more
"exhausted" at each width: the symbolic charge's own change (its proposal reports the same). The
solver's account or charge adds none.

### `compare/` bw-nf on CoBRA's datasets

Answers whose size changed against today's (all of them larger but a few dozen), and scored lines
solved (answer no larger than the ground truth; 75,737 are scored):

| option | default | 2^12 | 2^10 | pass work, default |
|-|-|-|-|-:|
| today | 75,734 solved | 69,833 | 63,280 | 1.30 G |
| scale 64 | 0 changed, 75,734 | 15,340, 62,031 | 14,767, 55,524 | 1.00× |
| derive 8 | 0, 75,734 | 9,133, 66,701 | 11,566, 58,192 | 1.00× |
| charge 8 | 2, 75,734 | 10,511, 65,486 | 14,911, 55,516 | 7.79× |
| bound 4 | 1, 75,734 | 6,292, 66,611 | 10,034, 59,132 | 4.49× |
| bound 8 | 2, 75,734 | 9,456, 66,383 | 13,263, 56,892 | 7.79× |
| bound 32 | 8, 75,734 | 13,796, 62,895 | 14,766, 55,522 | 26.9× |
| account 4 | 1, 75,734 | 4,108, 67,361 | 8,648, 60,234 | 1.00× |
| account 16 | 0, 75,734 | 802, 69,245 | 3,554, 61,066 | 1.00× |
| sym | 1, 75,734 | 549, 69,334 | 2,482, 60,843 | 1.50× |
| sym + account 4 | 2, 75,734 | 4,514, 66,975 | 10,301, 58,579 | 1.47× |
| sym + bound 4 | 2, 75,734 | 6,803, 66,115 | 11,656, 57,518 | 4.95× |

At the default budget the changed answers are two OSES lines without a ground truth (`oses_fast`
265: 2,080 nodes become 2,087 under account 4, 2,093 under bound 4; line 406, 174 → 367, is
sym's), and exact answers stay 49,869 under every option. With more fuel, and what it costs
(instructions of every line's engine run):

| option | default | 2^14 | 2^13 | 2^12 | 2^10 |
|-|-:|-:|-:|-:|-:|
| today | 75,734; 628 G | 74,580; 517 G | | 69,833; 431 G | 63,280; 238 G |
| sym + account 4 | 75,734; 610 G | 73,174; 504 G | 72,065; 417 G | 66,975; 350 G | 58,579; 152 G |
| sym + bound 4 | 75,734; 606 G | 73,032; 507 G | 71,350; 436 G | 66,115; 364 G | 57,518; 160 G |

Twice the fuel more than restores a small fuel's results: under sym + account 4, fuel 2^13
solves 72,065 lines for 417 G instructions, against today's 69,833 for 431 G at 2^12.

### The longest call, through the engine

The 44-node question of the hill climb, as an 8-bit expression through the MBA rows' engine
(`--solver-fuel`), CPU time:

| option | default | 2^18 | 2^16 | 2^14 | 2^12 | 2^10 |
|-|-:|-:|-:|-:|-:|-:|
| today | 12.8 s | 13.5 s | 13.5 s | 9.3 s | 9.5 s | 9.0 s |
| account 4 | 13.1 s | 10.1 s | 0.88 s | 39 ms | 1.7 ms | 0.7 ms |
| bound 4 | 14.1 s | 9.7 s | 0.87 s | 40 ms | 1.6 ms | 0.6 ms |
| sym | 0.18 s | 0.18 s | 0.18 s | 0.10 s | 33 ms | 28 ms |
| sym + account 4 | 0.19 s | 29 ms | 20 ms | 18 ms | 1.9 ms | 0.8 ms |
| sym + bound 4 | 0.18 s | 28 ms | 20 ms | 18 ms | 1.5 ms | 0.6 ms |
| sym + account 16 | 0.17 s | 0.15 s | 27 ms | 19 ms | 17 ms | 1.7 ms |

Today `Budget::fuel(1024)`, whose pass work is 16,384 units, lets this input run 9 s in one
solver call. Its result (39 nodes) is the same under every option, as are the other two
expressions'.

### Tests

The suite with all features (896 tests): account 4 alone passes it unchanged; bound 4 alone fails
`tests/prove_budgets.rs` `simplification_within_a_budget`, which pins that small fuels stop on
node visits (one now stops on pass work); with sym, both fail the three tests the
symbolic-charge proposal lists (that one among them), each pinning today's rate.

## Reading the numbers

- **The fuel does not bound the solver.** At a 64th of the default fuel random DAGs cost what
  they cost at the default; the solver is 99 % of their time and 45 % of CoBRA's. A run may make
  `fuel / 1024` calls of 2^20 steps each: a thousand steps per unit of fuel.
- **A step is not a unit of time.** A step costs 230 to 930 instructions on average, but one
  call's steps can cost 30 times that on generated inputs, and 140,000 instructions each in the
  worst case found, where the symbolic fallback runs uncharged. A bound in steps is only as good
  as the steps: the symbolic-charge proposal's bound brings the worst call from 9.6 s to 27 ms,
  tying the steps to the fuel brings a run at small fuels from seconds to milliseconds, and each
  without the other leaves seconds (0.9 s at 2^16 under account 4 alone) or a fifth of one (0.18
  s at 2^16 under sym alone).
- **Per-call caps do not bound a run.** derive leaves random DAGs at 2^16 at 252 G of 275 G;
  scale bounds better but cuts small-fuel MBA results hardest, its cap at 2^10 (256 steps) below
  what a linear question needs, and at 2^12 the consumer-like invertible-mix questions.
- **Charging after the call is not enough.** charge stops later work but lets every call run in
  full: random DAGs at 2^10 cost today's 10.8 G.
- **A linear bound costs small-fuel results in proportion to its rate.** account 4 and bound 4
  give the same bound, four steps per unit of fuel, and change no scored result at the default
  budget; bound 8 and 32 bound tighter and change more, 32 also at the default budget. The
  account changes fewer than bound 4 at the same rate: it does not take pass work from the passes
  and certificates (CoBRA keeps 750 to 1,100 more lines solved at 2^12 and 2^10).
- **Four steps per unit of fuel matches the cost.** Outside the solver a unit of pass work costs
  35 to 800 instructions (evaluation units are cheap, pass reads dear), so a solver step costs
  0.9 to 11 units, 2 to 3 typically: an account of `4 · fuel` steps, or a charge of 4 units per
  step, spends on the solver about what pass work spends on the rest. R = 32 (a step's own 32
  evaluations) charges a step about ten times its cost in pass work.
- **The consumer's question** is proved at every fuel from 2^14 up under every option; the most
  it is charged, 165,695 units (sym + bound 4), fits fuel 2^14's 262,144.
- **More fuel brings results back, at the same cost.** Under sym + account 4, fuel 2^13 solves
  more CoBRA lines than today's 2^12, for fewer instructions (above).

## Recommendation

**A solver account in the budget, `Budget::mba_steps = 4 · fuel` (2^24 at the default): each
call runs within `min(MbaBudget::steps, what is left)` and is charged the steps it spent, a
remembered answer the steps it saved; together with the symbolic-charge proposal's charge of
256 units per monomial operation with the bounded fallback, as one behavior change in a minor
release.** The fuel then bounds the solver's steps per run (4 per unit of fuel, the same order
of time as its pass work) and the bounded fallback keeps a step near its cost: the worst call
found drops from 9.6 s to 27 ms, and a run of it at fuel 2^16 from 13.5 s to 20 ms. No scored
result changes at the default budget (two unscored OSES lines do), the consumer's question is
unchanged at every fuel, no test changes beyond the symbolic charge's three, and small fuels lose
some nonlinear and random-DAG results (CoBRA solves 66,975 of today's 69,833 at 2^12 and 58,579
of 63,280 at 2^10, with sym's own share 499 and 2,437 of those losses), which twice the fuel more
than brings back at about the same instructions. It is a new `Budget` field and `Exhausted`
variant; the C API's `bw_budget` is a fixed struct, so it gains the field with a new
`BW_ABI_VERSION`, and Python a keyword.

If the budget should not grow a field, **charge the steps to pass work at 4 units each, each call
within what is left (bound 4)**: the same bound with no API change, but pass work then pays for
the solver too, so it changes more small-fuel results (CoBRA 66,115 and 57,518 solved with sym),
costs more memo hits (+19 % on the MBA corpora at 2^18) and, alone, changes a test (one the
symbolic charge changes too).

Not scale, derive or charge: they bound calls, not runs, or not before a call has run. Not
R = 32: about ten times a step's cost, it changes default-budget results, loses the most at
small fuels and turns nine invertible-mix questions at fuel 2^12 from decided into unknown.
account 16 changes a fifth to two fifths as many CoBRA answers as account 4 but bounds four
times looser (random DAGs at 2^16 cost 148 G, half of today's).

## If accepted

- `engine::Budget`: `mba_steps` (with `with_mba_steps`; `Budget::fuel(f)` sets `4 · f`,
  `UNLIMITED` and `ZERO` as the others), `Exhausted::MbaSteps`, `Meter`'s charge for it; the C
  `bw_budget` field and `BW_ABI_VERSION` 2, the Python keyword, the WASM binding if it exposes
  budgets.
- `MbaSolver`: a provided method reporting the steps a call spent, for example
  `solve_counted(&self, p, budget) -> (MbaAnswer, u64)`, by default `solve` with the whole limit
  reported (a solver that does not count is charged its limit); `NormalFormSolver` reports what
  its step meters consumed, and its memo keeps each answer's steps and reports them again on a
  hit; `ThreadedSolver` passes them through.
- `engine/pass/mba.rs`: a call's limit is `min(MbaConfig::budget.steps, mba_steps left)`; a call
  whose limit would be zero is not made (over budget, the node not final); afterwards its steps
  are charged; an exhausted answer under a lowered limit is over budget on `MbaSteps`.
- The symbolic-charge proposal's "If accepted".
- The solver's memo stays keyed by the limit: a lowered limit costs memo hits at small fuels (+7 %
  on the MBA corpora at 2^18 under account 4), never answers. Rounding a lowered limit down to a
  power of two keeps the hits but changes more results at 2^10 (measured with bound 8): not
  proposed.
- Docs: `Budget` and `Budget::fuel`, `MbaBudget::steps` (a per-call cap within the run's
  account), `NormalFormSolver`, design §9 (the per-step times, as measured here), the book's
  budget section, the bindings' budget docs, and the changelog's "Behavior changes".
- The prototype's switches (`BW_SOLVER_*` in `mba::probe`), its probe records and question dumps,
  the bench modes (`--solver-calls`, `--solver-dags`, `--solver-worst`, `--solver-search`,
  `--solver-fuel`) and `compare/`'s `BW_CALLS` are for measuring and are not meant to land.

## Seen on the way, not part of this

- **Uncharged certificate work.** The compositional certificate checks each pair's skeletons at
  the sample with the scalar evaluator (`Compose::agrees`) and builds the skeletons without a
  charge: 2 % of the solver's time on the corpora, but four fifths of the worst call left once
  the symbolic fallback is bound (4.2 G instructions in 2^20 steps). Charging it (the sample's
  points times the skeletons' nodes), or evaluating it batched, is the next calibration of a
  step.
- **Fixed costs per process.** The synthesis table (135 M instructions, 14 ms) and each narrower
  width's index (50 M at 8 bits) are built on the first call that needs them, uncharged.
- **A failed fixed point is free.** In `nf::run`, the fixed point's normalization of an answer
  charges the call's steps only when it succeeds; one that runs out leaves its steps to the
  self-check after it.
- **A host cache skips charges.** An answer from an `MbaCacheStore` skips the solver and the
  gate's certificate, so a warm cache leaves more budget than a cold one (true today for the
  certificates; with the solver charged, for its steps too).

## Reproducing

```text
CARGO_TARGET_DIR=target/probe cargo build --release -p bitwright-bench --features probe
target/probe/release/bitwright-bench --solver-calls calls.tsv     # every solver call
python3 tools/solver-budget/table.py calls.tsv                    # per-call table rows
BW_DUMP_OVER=300000000 BW_DUMP_FILE=worst.tsv \
    target/probe/release/bitwright-bench --solver-dags 50,200,6,8 dags.tsv
target/probe/release/bitwright-bench --solver-search worst.tsv 200
target/probe/release/bitwright-bench --solver-worst worst.tsv     # a question at three budgets
python3 tools/solver-budget/to_text.py worst.tsv > worst.txt
BW_SOLVER_MODE=account BW_SOLVER_ACCOUNT=4 BW_SYMBOLIC_MODE=bound BW_SYMBOLIC_CHARGE=256 \
    BW_SYMBOLIC_RESERVE=0 target/probe/release/bitwright-bench --solver-fuel worst.txt 8
cargo build --release -p bitwright-bench
printf '%s\n' "off 64 256 exact" "account 64 4 exact" |
    tools/solver-budget/sweeps.sh target/release/bitwright-bench out   # --prover-budgets, sweeps
python3 tools/solver-budget/sweep_tables.py out/sweep-off-64-256-exact.tsv \
    "account 4=out/sweep-account-64-4-exact.tsv"
```

`BW_SOLVER_MODE` is `off` (today), `scale`, `derive`, `charge`, `bound` or `account`, with
`BW_SOLVER_RATE` (pass-work units per step), `BW_SOLVER_ACCOUNT` (steps per unit of fuel) and
`BW_SOLVER_ROUND=pow2`; the symbolic-charge switches combine with them. For `compare/`,
`tools/solver-budget/compare-runs.sh` runs bw-nf per configuration and fuel, and with the probe
build `compare-calls.sh` records every solver call and each line's instructions;
`tools/solver-budget/README.md` lists the scripts.
