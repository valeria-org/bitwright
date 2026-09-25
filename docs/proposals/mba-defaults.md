# Proposal: the normal-form solver and bitwright's own evidence as the MBA defaults

Status: accepted and implemented for the release after 0.10.0 (see the changelog). Was: proposed, not implemented. Both changes alter results, so they are proposed apart
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
| linear MBA, 8 bits | 3927 | 1673 | 1673 (0 changed) | 1524 | 98 | 96 | 0 | 0.33 G (27 ms) | 1.09 G (94 ms) |
| nonlinear MBA, 8 bits | 4105 | 2621 | 2621 (0 changed) | 901 | 164 | 164 | 0 | 0.21 G (16 ms) | 0.56 G (42 ms) |
| linear MBA, 64 bits | 3927 | 1673 | 1673 (0 changed) | 1524 | 98 | 96 | 0 | 0.31 G (25 ms) | 0.92 G (80 ms) |
| nonlinear MBA, 64 bits | 4105 | 2621 | 2621 (0 changed) | 901 | 164 | 164 | 0 | 0.21 G (16 ms) | 6.06 G (227 ms) |
| random DAGs, 8 bits | 10693 | 9094 | 9094 (0 changed) | 9023 | 26 | 25 | 0 | 1.18 G (95 ms) | 170.6 G (12.1 s) |
| random DAGs, 64 bits | 10992 | 9466 | 9466 (0 changed) | 9414 | 29 | 28 | 1 | 1.22 G (98 ms) | 161.6 G (11.4 s) |

What the MBA service answered (per corpus, summed over its questions; `unproved` answers were
refused for lack of accepted evidence, `too small` fragments were not asked about):

| corpus | configuration | calls | simplified | not smaller | no simpler | unsupported | exhausted | unproved | refuted |
|-|-|-|-|-|-|-|-|-|-|
| linear MBA, 64 bits | current | 439 | 0 | 0 | 315 | 124 | 0 | 0 | 0 |
| linear MBA, 64 bits | proposed | 520 | 102 | 2 | 416 | 0 | 0 | 0 | 0 |
| nonlinear MBA, 64 bits | current | 601 | 0 | 0 | 0 | 601 | 0 | 0 | 0 |
| nonlinear MBA, 64 bits | proposed | 321 | 170 | 0 | 151 | 0 | 0 | 0 | 0 |
| random DAGs, 64 bits | current | 6774 | 1 | 0 | 101 | 6672 | 0 | 0 | 0 |
| random DAGs, 64 bits | proposed | 7844 | 39 | 637 | 6485 | 671 | 10 | 2 | 0 |

The 8-bit rows are alike (the full report prints them all); trust off alone answered exactly
as the current defaults on every corpus.

Benchmarks (instructions per iteration of 20 expressions, a fresh engine each iteration,
bitwright's own evidence only in every row):

| row | instructions | nodes before → after |
|-|-|-|
| `simplify/mba/64` (signature solver, linear MBA) | 23.2 M | 125 → 92 |
| `simplify/mba-native/64` (normal-form solver, linear MBA) | 96.3 M | 125 → 83 |
| `simplify/mba-nonlinear-sig/64` (signature solver, nonlinear MBA) | 12.0 M | 141 → 73 |
| `simplify/mba-nonlinear/64` (normal-form solver, nonlinear MBA) | 727.8 M | 141 → 27 |

Since the first version of this proposal the solver remembers answers (about 30 % fewer
instructions on random DAGs, half to three quarters fewer on nonlinear MBA) and looks small
normal forms up in a synthesis table (linear MBA results 1,645 → 1,635 nodes, for about 4 %
more instructions on random DAGs). It also reads bitwise operations with constants that read
known low bits as arithmetic, reuses atoms whose definitions appear arithmetically, and
folds high powers before its degree cap; the certificates split variables into cases over a
few bits; and the engine keeps `x | c` as itself and cuts rewrite cycles. With these (0.5.0),
random DAG results shrink from 9,087 to 9,084 and from 9,480 to 9,477 nodes under the
proposed configuration, for about 4.5 % more instructions there, and from 9,146 to 9,142 and
from 9,513 to 9,511 under the current one, at the same cost; the MBA corpora are unchanged.

After 0.5.0, to reach every expression of CoBRA's datasets whose ground truth holds (see the
changelog), the solver gained searches (sums of two bitwise functions and their forms that
share subterms, a third term beside two, independent groups, peeled functions, wide tables and
their decompositions, partial factorings), readings of dependent and related atoms and more
forms of each function, and the certificates two more tests; the engine asks each fragment
whole first and hashes a question once, and the linear pass writes `a + a` and folds constants
into complements. The tables above are measured with all of it: results shrink on every
corpus under both configurations (linear MBA 1,635 → 1,524 and nonlinear MBA 1,005 → 901
nodes proposed, random DAGs 9,084 → 9,023 and 9,477 → 9,414; the current configuration 1,794 →
1,673 on linear MBA and 9,142 → 9,094 and 9,511 → 9,466 on random DAGs). The current
configuration costs up to 5 % less; the proposed one 5 % more on linear MBA, 2.4 times as much
on nonlinear MBA at 64 bits, whose answers now use atoms and are proved over them, and 2.8
times as much on random DAGs (60 G → 171 G at 8 bits), where the searches run on questions
that rarely simplify.

## Reading the numbers

- **Results.** On linear MBA the results shrink by 9 % (98 of 200 change; 96 get smaller,
  2 are re-rendered at the same size, none grows). On nonlinear MBA they shrink by 66 %: the
  signature solver declines every question there, the normal-form solver simplifies half of
  them. On random DAGs, which are not obfuscated, they shrink by 0.5 % to 0.8 %.
- **Larger results.** One, a random DAG at 64 bits (48 → 49 nodes): the solver writes
  `x·x − (x << 61)` as `(x + 0xe000000000000000)·x`, a node smaller where it is asked, which
  leaves the whole a node larger once the rest is simplified around it. Every rewrite is
  checked to make the DAG smaller when it is made, so a rewrite that is smaller where it is
  asked can, with sharing elsewhere, leave the whole larger (0.5.0 had three such inputs);
  these are local optima, not unchecked steps.
- **Trust.** With the signature solver, turning backend certificates off changes nothing on
  these corpora: the gate proves every answer it gives with its own certificates. Every answer
  the proposed configuration accepted was proved by bitwright itself; nothing was refuted.
- **Cost.** The proposed configuration takes 3.0 to 3.3 times the instructions on linear MBA
  (the 8-bit corpus, run first, also pays the synthesis table's one-time build), 2.7 times on
  nonlinear MBA at 8 bits and 29 times at 64 bits (degree-2 certificates grow with the width),
  and about 140 times on random DAGs: about 60 ms per 40-node DAG instead of 0.5 ms here.
  Random code is the worst case. Its fragments have many atoms and bit classes, so their
  normal forms are large, and they rarely simplify (39 of 7,844 questions). The signature
  solver declines almost all of them at once.

## Costs and risks

- **Time.** The solver's work per question is bounded by its budget (`MbaConfig::budget`,
  `2^20` steps by default, at most about 40 to 60 ns per step here), and `Budget::mba_calls` bounds
  the number of questions. A host that runs the MBA service over large amounts of code that is
  not obfuscated, and cares about time more than size, keeps the signature solver or lowers
  the budget.
- **Hosts with a backend of their own.** With trust off, a backend's answers are accepted only
  when bitwright's certificates prove them. The others are refused and counted as unproved.
  Hosts that accept their backend's certificates set `backend_certificates` back to true.
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
  returning it, unless its caller proves answers itself (the engine asks without evidence when
  backend certificates are not trusted). Its tests check normal forms and every candidate exhaustively at widths 1 to 6
  (with the batched evaluator, itself checked against the reference evaluator), run the
  catalogs at widths up to 512, and pass lying solvers through the gate. CI builds its fuzz
  target on every run and runs it nightly.

## Alternatives

- **Trust off alone.** No result changes on these corpora and no time cost; accepted answers
  no longer depend on any backend's word. The cost falls on hosts with a backend of their own,
  as above.
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
