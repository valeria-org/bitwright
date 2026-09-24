# Proposal: the normal-form solver and bitwright's own evidence as the MBA defaults

Status: proposed, not implemented. Both changes alter results, so they are proposed apart
from the code that makes them possible (the `NormalFormSolver`, the gate's certificates).

## The change

Two defaults of the MBA service (feature `mba`, enabled per strategy with
`Strategy::with_mba`):

1. **The solver.** When the host sets none, the engine asks `NormalFormSolver::default()`
   instead of `SignatureSolver` (`MbaService::default` in `engine/mod.rs`).
2. **The trust.** `MbaTrust::default()` has `backend_certificates: false` instead of `true`
   (`mba/mod.rs`). Answers are then accepted only on bitwright's own certificates or a
   configured `EquivalenceProver`'s proof (or on sampling, if the host turns that on).

Nothing else changes: not `Strategy::deobfuscate()` (which does not include the MBA service),
not `SignatureSolver`, not `LOWERING_VERSION`, not the API. A host keeps today's behavior with
`.mba_solver(Arc::new(SignatureSolver))` and
`MbaTrust::default().with_backend_certificates(true)`.

## Evidence

`cargo run --release -p bitwright-bench -- --corpus-diff` runs the deobfuscation strategy
with the MBA service on corpora generated in the repository from fixed seeds: linear MBA (the
benchmark corpus), nonlinear MBA (`nonlinear_mba_corpus`: products, sums and bitwise functions
rewritten by MBA identities, plus terms equal to zero that only nonlinear reasoning cancels)
and random 40-node DAGs over four symbols, 200 inputs each, at 8 and 64 bits. It compares
three configurations: the current defaults, trust off alone, and both changes (proposed).
Sizes are the DAG nodes of the results. Cost is user-space instructions retired, which does
not move with other load; wall time on one machine is for orientation only.

| corpus | nodes before | current | trust off only | proposed | changed | smaller | larger | instructions current | instructions proposed |
|-|-|-|-|-|-|-|-|-|-|
| linear MBA, 8 bits | 3927 | 1794 | 1794 (0 changed) | 1635 | 109 | 98 | 0 | 0.33 G (26 ms) | 1.03 G (83 ms) |
| nonlinear MBA, 8 bits | 4105 | 2621 | 2621 (0 changed) | 1005 | 159 | 159 | 0 | 0.20 G (15 ms) | 0.38 G (27 ms) |
| linear MBA, 64 bits | 3927 | 1794 | 1794 (0 changed) | 1635 | 109 | 98 | 0 | 0.32 G (25 ms) | 0.86 G (69 ms) |
| nonlinear MBA, 64 bits | 4105 | 2621 | 2621 (0 changed) | 1005 | 159 | 159 | 0 | 0.21 G (15 ms) | 2.51 G (93 ms) |
| random DAGs, 8 bits | 10693 | 9146 | 9146 (0 changed) | 9085 | 31 | 30 | 1 | 1.24 G (102 ms) | 59.8 G (4.3 s) |
| random DAGs, 64 bits | 10992 | 9513 | 9513 (0 changed) | 9478 | 30 | 28 | 1 | 1.26 G (103 ms) | 60.2 G (4.0 s) |

What the MBA service answered (per corpus, summed over its questions; `unproved` answers were
refused for lack of accepted evidence, `too small` fragments were not asked about):

| corpus | configuration | calls | simplified | not smaller | no simpler | unsupported | exhausted | unproved | refuted |
|-|-|-|-|-|-|-|-|-|-|
| linear MBA, 64 bits | current | 669 | 8 | 0 | 340 | 321 | 0 | 0 | 0 |
| linear MBA, 64 bits | proposed | 823 | 157 | 57 | 609 | 0 | 0 | 0 | 0 |
| nonlinear MBA, 64 bits | current | 742 | 0 | 0 | 0 | 742 | 0 | 0 | 0 |
| nonlinear MBA, 64 bits | proposed | 780 | 257 | 2 | 521 | 0 | 0 | 0 | 0 |
| random DAGs, 64 bits | current | 4895 | 1 | 4 | 77 | 4813 | 0 | 0 | 0 |
| random DAGs, 64 bits | proposed | 6493 | 40 | 554 | 5319 | 560 | 8 | 12 | 0 |

The 8-bit rows are alike (the full report prints them all); trust off alone answered exactly
as the current defaults on every corpus.

Benchmarks (instructions per iteration of 20 expressions, a fresh engine each iteration,
bitwright's own evidence only in every row):

| row | instructions | nodes before → after |
|-|-|-|
| `simplify/mba/64` (signature solver, linear MBA) | 23.5 M | 125 → 93 |
| `simplify/mba-native/64` (normal-form solver, linear MBA) | 97.3 M | 125 → 84 |
| `simplify/mba-nonlinear-sig/64` (signature solver, nonlinear MBA) | 11.7 M | 141 → 73 |
| `simplify/mba-nonlinear/64` (normal-form solver, nonlinear MBA) | 236.6 M | 141 → 34 |

Since the first version of this proposal the solver remembers answers (about 30 % fewer
instructions on random DAGs, half to three quarters fewer on nonlinear MBA) and looks small
normal forms up in a synthesis table (linear MBA results 1,645 → 1,635 nodes, for about 4 %
more instructions on random DAGs). It also reads bitwise operations with constants that read
known low bits as arithmetic and reuses atoms whose definitions appear arithmetically, and
the certificates split variables into cases over a few bits (random DAG results 9,087 →
9,085 and 9,480 → 9,478 nodes, for about 4 % more instructions there; the MBA corpora are
unchanged).

## Reading the numbers

- **Results.** On linear MBA the results shrink by 9 % (109 of 200 change; 98 get smaller,
  11 are re-rendered at the same size, none grows). On nonlinear MBA they shrink by 62 %: the
  signature solver declines every question there, the normal-form solver simplifies a third of
  them. On random DAGs, which are not obfuscated, they shrink by 0.4 % to 0.7 %, and one input
  per width grows.
- **The larger result** (31 → 33 nodes, the same input at both widths). The solver answers a
  fragment containing `(u·c)·c` with `u·(c·c)`, which is smaller where it is asked; elsewhere
  the DAG keeps `u·c`, and the two no longer share it. Every rewrite is checked to make the
  DAG smaller when it is made, so this is a local optimum, not an unchecked step.
- **Trust.** With the signature solver, turning backend certificates off changes nothing on
  these corpora: the gate proves every answer it gives with its own certificates. Every answer
  the proposed configuration accepted was proved by bitwright itself; nothing was refuted.
- **Cost.** The proposed configuration takes 2.7 to 3.1 times the instructions on linear MBA
  (the 8-bit corpus, run first, also pays the synthesis table's one-time build), 1.9 times on
  nonlinear MBA at 8 bits and 12 times at 64 bits (degree-2 certificates grow with the
  width), and 48 times on random DAGs: about 21 ms per 40-node DAG instead of 0.5 ms here.
  Random code is the worst case. Its fragments have many atoms and bit classes, so their
  normal forms are large, and they rarely simplify (40 of 6493 questions). The signature
  solver declines almost all of them at once.

## Costs and risks

- **Time.** The solver's work per question is bounded by its budget (`MbaConfig::budget`,
  `2^20` steps by default, at most about 40 to 60 ns per step here), and `Budget::mba_calls` bounds
  the number of questions. A host that runs the MBA service over large amounts of code that is
  not obfuscated, and cares about time more than size, keeps the signature solver or lowers
  the budget.
- **Hosts using `CobraSolver`.** With trust off, cobra's answers are accepted only when
  bitwright's certificates prove them. The others are refused and counted as unproved. This is
  not measured here: this work keeps other simplifiers out of its evaluation. Hosts that accept
  cobra's own certificates set `backend_certificates` back to true.
- **Sampled answers.** A synthesized form that no certificate can decide (three atoms at
  degree 2 and 512 bits, say) is returned only as `Claim::Sampled`, after the refutation
  sample; it is the solver's only answer that is not exact by construction. With trust off
  and sampling off (both proposed or already the default) the gate accepts it only on its own
  certificate; a host that turns sampling on accepts it on the sample.
- **Caches.** Keys include the solver id and the trust setting. Stored answers from the old
  defaults are not reused under the new ones, and a persistent store refills. No invalidation
  is needed.
- **Soundness.** The gate still accepts only proved answers. With trust off, those are proofs
  bitwright runs itself: finite evaluation tests, each complete for its fragment, confirmed
  exhaustively at small widths. The normal-form solver also certifies each answer before
  returning it. Its tests check normal forms and every candidate exhaustively at widths 1 to 6
  (with the batched evaluator, itself checked against the reference evaluator), run the
  catalogs at widths up to 512, and pass lying solvers through the gate. CI builds its fuzz
  target on every run and runs it nightly.

## Alternatives

- **Trust off alone.** No result changes on these corpora and no time cost; accepted answers
  no longer depend on any backend's word. The cost falls on hosts using `CobraSolver`, as
  above.
- **The solver alone, trust on.** The normal-form solver claims `Proved` only when one of the
  gate's own certificates ran, so trusting its claim adds little: at most answers it proved
  within its own budget that the gate could not fit in the remaining pass work. Trust stays a
  separate decision about other backends.
- **Neither.** Hosts opt in with `.mba_solver(Arc::new(NormalFormSolver::default()))`, as the
  book shows; the MBA service keeps declining nonlinear MBA by default.

## If accepted

- `engine/mod.rs`: `MbaService::default` uses `NormalFormSolver::default()`; the builder's
  doc comment names it.
- `mba/mod.rs`: `MbaTrust::default()` sets `backend_certificates: false`; its doc comment
  says so.
- Tests that rely on the defaults: `tests/api.rs`, `tests/heavy_simplify.rs`
  (`mba-signature-certified`) and the MBA tests in `engine/pass/tests.rs` pass
  `MbaTrust::default()` or no solver, and would state the old values where they test them.
- Docs: the book's deobfuscation chapter (its examples set both values explicitly and keep
  working), design §9 (`MbaTrust`, the gate), and a "Behavior changes" entry in the changelog.
