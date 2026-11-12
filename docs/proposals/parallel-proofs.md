# Batches of questions, split and shared, on the caller's threads

Status: released in 0.31.0 as `bitwright::batch` (feature `prove`). The first three sections
are the design note written before the implementation; the rest is what was built, what it
measures, and how a consumer moves to it. New public items only (`batch`,
`prove::Simplifiers`, `prove::valid_under_with`, `Question::valid_under_with`), no existing
signature or answer changed.

## What was asked, and what the code says about it

A consumer asks thousands of questions per function ("is this expression a constant?", "is
`A == B` valid under these facts?") about MBA-obfuscated expressions of 2,000 to 8,500 nodes
that share almost all of their structure. It wants them answered on several threads, split
where noise cancels, with shared work done once, cancellable, and with answers and costs that
never depend on order, thread count or cache state.

Checked against the source at 0.30.2:

| Claim in the request | In the code |
|---|---|
| `prove::valid_under` and friends | Exist as named (`valid_under`, `valid`, `equal`, `satisfy`, `Question`). |
| The MBA memo serves an answer found under one budget to a larger one, at the old cost | True up to 0.30.0. Since 0.30.1 (`80a4992`) `NormalFormSolver`'s memo is keyed on the question, `evidence` and `steps` (the whole `MbaBudget`), compares the stored question on a hit, and returns the recorded steps. It is exact; eviction (oldest first, `NfOptions::memo`) changes time only. The consumer's wrapper is redundant from 0.30.1 on. |
| A process-wide simplifier inside `prove` | True: `prove::simplifier_of` kept three engines in a `static`, each with a `NormalFormSolver`. It could not change an answer since 0.30.1, but it was state no caller owned. Now `prove::Simplifiers`, which a caller can own; the old entry points use one for the process. |
| Passes "demanded, words, slices, limbs, known_words, linear" | `demanded`, `words` and `linear` are phases. `slices` and `limbs` are source modules of other phases and `known_words` a function of the facts: profile symbols, not passes a strategy names. |
| An abandoned proof keeps running | True of every `prove` entry point (none can be interrupted) and, by design, of `mba::ThreadedSolver`. |
| Nothing runs questions in parallel | `Engine::run_each` already simplifies roots on threads, each in a context of its own. There was no counterpart for proofs, and it shares nothing between roots. |
| `Context::fork` may copy in proportion to the context | It does: every table, the facts and the rewrite memo included. Measured below. |

One candidate the request lists conflicts with how bitwright is built: a persistent context
that workers read and merge into cannot give order-independent costs, because a context's
rewrite memo answers a remembered node for free (`docs/design.md` §6.2; `prove::Stats`: "in a
context with the same history"). A fork of a simplified base carries that history too. The
store below is content-addressed instead, and replays costs.

## Which results can be reused out of context

On the consumer's exported slow questions (52 `engine`/`simplify` questions without
assumptions, 264 sub-expressions of 12 nodes or more): the sub-expression is simplified alone
and substituted for itself, the question simplified, and the result compared node for node
with the question simplified directly, one phase at a time.

| Phase | Sub-result differed from the sub-expression | Same question result when it did |
|---|---|---|
| all phases (`deobfuscate` with MBA) | 262 | 92% |
| `local` (rules) | 88 | 98% |
| `invert`, `compares`, `shuffle` | 15, 11, 159 | 100%, 100%, 99% |
| `xor` | 214 | 83% |
| `mba` | 254 | 66% |
| `linear_mba` | 211 | 60% |
| `casts` | 42 | 40% |
| `bitwise` | 248 | 26% |
| `linear` | 166 | 13% |
| `demanded` | 144 | 12% |
| `words` | 98 | 11% |

(`fact_fold`, `division` and `carries` changed nothing here.) The rules and the passes that
decide a node from the node alone are reusable. `demanded` reads the parent's demanded bits;
`linear` and `bitwise` collect a sum or a truth table through the node; `words` and the MBA
phase cut fragments from the root; and under `Sharing::Roots`, the default, a rewrite is
weighed against the uses from every root. A stored simplified *form* substituted for a
sub-expression changes the answer about 8% of the time, so no form is stored. A proved
*constant* can be substituted: the question is the same function with the constant in place.

## Design

```rust
let session = batch::Session::new(batch::Config::default().with_threads(8));
let asks = [Ask::constant(e0), Ask::valid(p1).under(&assumptions), Ask::simplify(e2)];
let replies = session.run(&mut cx, &asks)?;          // replies[i] answers asks[i]
```

- **`Session`** owns what outlives a call: its engines (`prove::Simplifiers`, not the
  process's), their solver, and the store. Two sessions share nothing.
- **`Config`** is fixed at construction: `threads` (the calling thread and scoped threads
  that end with the call; no pool), the `prove::Config` of every task, optionally another for
  hubs (`hub`), the MBA configuration, `Split`, and `store_nodes`.
- **`Ask`**: `simplify`, `constant`, `valid`, `equal`, each optionally `.under(&Assumptions)`
  and `.cancellable(&Cancel)`. The caller builds every question of a batch in one context,
  where shared structure is one set of nodes.
- **`Reply`**: `Answer` (`Simplified`, `Constant(value)`, `Varies(two assignments)`,
  `Proved`, `Refuted(model)`, `Unknown(why)`, `Cancelled`), `Cost` (the engine's `Budget`
  spent, conflicts, propagations, decisions, circuit nodes, tasks), and `Source`.

**Tasks.** Questions are copied (`Context::import`) into the session's *store context*,
which is where a task gets its identity: hash-consing compares nodes, so equal keys are equal
questions without relying on a hash. Nothing is simplified there. A worker copies a task's
root into a new context and decides it there, so a task's answer and cost are a function of
its content and the session's `Config`. A task is one of:

1. *A hub.* Every node of the batch is evaluated at 64 assignments (zeros, ones, values
   seeded by the symbols' keys, declared bits kept), once per distinct node. A node with one
   value at all of them, above something that varies, cancels noise. The topmost such node
   is the cut, except that a chain of them that only adds a literal to the one below is cut
   at its bottom, so that siblings that differ by a constant on top share the hub. A hub is
   asked "is it that constant?" without the question's assumptions, so its answer holds in
   every question: first the engine on the hub (asked of the equality with the constant, the
   engine moves terms across it and the noise no longer meets), then a search for what is
   left. When that fails and `Split::nested` is on, the hubs below it are asked the same way
   and the hub again with those proved written as constants.
2. *Independent terms* (`Split::terms`). A chain of `+` or of `^` is regrouped by the
   symbols its terms read, where a group's sum is constant at the samples and the chain as
   written hides it. The regrouping is associativity and commutativity through the
   constructors; the group is then a hub like any other.
3. *The remainder.* The question with its proved hubs replaced, asked as it was.
4. *Cases* (`Split::cases`). A proof still undecided, whose selects test a condition `c`,
   becomes `c → p[c:=1]` and `¬c → p[c:=0]`, each a question of its own. Both proved is a
   proof; a counterexample of either is replayed on the question as asked.

A constant is written for a hub only when the engine folded the hub to it or the search
proved the equality. Sampling chooses cuts and refutes: a constant question with two values
at two samples is answered `Varies` at no cost; a hub that only samples constant is asked,
fails, and stays as written (tested with a node that is 0 at every sample and 1 at one input).

**Order.** `Split::default()` asks a question whole first and cuts only what that does not
decide. `Split::eager()` asks the hubs first. `Split::none()` never cuts.

**The store** keeps, per task, the answer and the cost. It is emptied whole when its context
holds more than `Config::store_nodes` nodes (2^20 by default) at the start of a call, when a
context configured otherwise arrives, or when a symbol arrives declared otherwise.

**Determinism.** A task's content depends only on the question: hubs are a function of the
question's nodes, and each is asked with the *answers* of the hubs below it, themselves
functions of their content. A reply's cost is the sum over its tasks, each counted once,
whether solved now, by another thread, or in an earlier call: the store keeps costs. A task
several asks share stops only when all of them are cancelled, and a stopped task stores
nothing. So threads, order, a warm or emptied store and cancellation change time only.

**Cancellation.** The engine reads a caller's clock on every charge (`Run::deadline`); a
`Cancel` is a clock that has passed once the flag is set, now threaded through
`prove::Question`. The search runs in slices of 2,000 conflicts with the flag read between
them. Building the circuit and sweeping it are not interrupted.

**Budgets of memos.**

| Memo | Exact? |
|---|---|
| `NormalFormSolver` | Yes since 0.30.1: whole-budget key, costs replayed. |
| `Context` rewrite memo | Exact answers; a hit is free, so costs depend on history. A batch never asks twice in one context. |
| `MbaCacheStore` (`MemoryCache`) | Off by default. A hit skips the solver's steps, so costs depend on it; a session uses none. |
| The session's store | Whole-task key, costs replayed. |

## "Same answers as asking alone"

What is guaranteed and tested (`bitwright/tests/batch.rs`):

- A question's reply (answer and cost, compared exactly) is the same asked alone in a new
  session, in any batch, in any order, on 1, 2, 8 or 32 threads, with the store warm, cold or
  emptied before every call, and with other asks cancelled.
- With `Split::none()`, a reply equals what `prove::valid_under` or `Engine::run` returns in
  a context that holds the question alone, statistics included.

What is not guaranteed, and cannot be while hubs are shared: equality between a *split*
question and the unsplit entry points. They are two procedures. Both are sound, so where both
decide they agree; either may answer `Unknown` where the other decides. On the measured data
the split procedure decided every question the unsplit one did, and 16 more.

One thing a consumer may not expect, found on the way and **not changed here**: the engine's
result is not a function of the expression alone. It also depends on the order the nodes
were created in. `engine_6aea389acbee3281` of the exported set, with its symbols renamed
`#18000000…`, folds to a constant when parsed into a context and does not when that context
is copied into another by `Context::import` (the same nodes, created depth-first). So the
batch, which always copies, is a function of content; a consumer that lowers each question
itself gets answers that depend on its lowering order, and may see one question in some
hundreds differ from the batch's. `Engine::run_each` documents an equivalence with `run`
that this breaks. It deserves its own fix (it changes answers, so it is not in this work).
Residual, for the same reason: two commutative operands whose order keys tie are ordered by
index, which is the one place a context's history can reach a copy.

## Measurements

The repository has no MBA inputs of the consumer's shape. These use 140 questions the
consumer exported earlier (every question that took 250 ms or more in five walks,
deduplicated, each with its symbols renamed from `#0`), replayed by
`bitwright-bench --batch DIR`. Renaming per question removes exactly the overlap between
questions that the request is about, so two sets are measured: the questions as they are,
and a round of siblings made from them (each of the 47 `engine` bodies asked as 16
constant questions, the body plus 8, 16, …: 752 questions, 94.4% of whose nodes the store
already held when asked).

The machine was shared and loaded throughout (load average 60 to 90 on 20 cores), so CPU
seconds are the comparable column and wall-clock times are indicative only. "Before" is one
context per question on one thread, as the consumer asks today.

The 140 questions as exported:

| | CPU | Wall | Peak memory | Answers |
|---|---|---|---|---|
| Before, 1 thread | 10.6 s | 10.9 s | 77 MB | 47 constant, 30 proved, 14 refuted, 49 simplified |
| Batch, `Split::none()`, 8 threads | 11.7 s | 5.2 s | 201 MB | the same but one (the order dependence above) |
| Batch, default, 8 threads | 11.6 s | 3.6 s | 241 MB | the same but that one |
| the same batch asked again | | 0.07 s | | identical answers and costs, all from the store |
| `Split::eager()`, the 47 `engine` questions only | 37.7 s against 2.3 s | | | 47 constant against 46 |

The round of 752 siblings:

| | CPU | Wall | Peak memory | Decided constant |
|---|---|---|---|---|
| Before, 1 thread | 43.2 s | 50.8 s | 66 MB | 736 |
| Batch, default, 8 threads | 60.0 s | 24.8 s | 257 MB | 752 |
| Batch, `eager`, 1 thread | 64.4 s | 166 s | 94 MB | 752 |
| Batch, `eager`, 4 threads | 61.2 s | 34.0 s | 159 MB | 752 |
| Batch, `eager`, 8 threads | 61.9 s | 28.3 s | 236 MB | 752 |
| Batch, `eager`, 8 threads, at a quieter moment | 49.8 s | 7.4 s | 243 MB | 752 |

Answers and costs were byte-identical at 1, 4 and 8 threads.

Reading them:

- **The gain here is from threads, not from sharing.** At 8 threads the round took 7.4 s
  against about 43 s serial when the machine allowed it (5.8 times), for 1.15 to 1.4 times
  the CPU. The target in the follow-up (18 s to 2–3 s at 8 threads) is the same ratio, but
  these are not that workload: see below.
- **Sharing works and does not pay on these questions.** In the eager round 1,582 hubs were
  asked once for 752 questions, and the 705 questions after the first of each body cost about
  14 ms each instead of 57 ms. But current bitwright folds 736 of the 752 whole in one engine
  run of about 57 ms, while proving a body's hubs separately costs about 16 engine runs: 753
  of the 1,582 hubs are not folded by the engine on their own (it leaves 12 to 120 nodes,
  which the search then fails on) although the same nodes fold inside the question. Roughly a
  third of the eager round's time goes to hub proofs that fail. Each failure is stored, so
  no sibling pays for it again.
- **The consumer's description is of another regime**: the whole question *fails* in about
  25 ms and over a hundred hubs fold at 3–20 ms each. There, asking the hubs once for all
  siblings is the saving, and `eager` is the setting. I could not reproduce that regime on
  0.30.2 with the data at hand: it needs one boundary's real questions.
- **Memory** grows with threads by the contexts of the tasks under way (about 20 MB each
  here), plus the store; it does not multiply a walk's total.
- **Cache hits.** The solver's memo answered 5,570 of 7,678 calls (73%) in the serial run. A
  repeated batch is answered wholly from the store.
- **Fork cost**, on one question of 2,585 nodes: `Context::fork` 22 µs (48 µs once an engine
  has run in it and it holds 7,588 nodes); `Context::import` into a new context 0.8–1.8 ms;
  parsing it 2.0 ms; one engine run 34 ms. Lowering is 3 to 6% of a question, so repeated
  lowering is not what made the consumer's thread pool slow. Forks are 40 to 80 times cheaper
  than copies, but a fork has the base's node order and whatever the base remembers, which is
  what the answers must not depend on; the batch copies.

## A real walk (added after 0.31.0)

The consumer then exported one walk with its own symbol keys: 714 "is this stack word a
constant?" questions over 26 boundaries, median 1,801 nodes, 97.2% of each question's nodes
already asked about. `bitwright-bench --walk DIR` asks each boundary as one batch of one
session, and again with the walk's deep fuel what stays open. The walk's own decisions
(stock proof, hubs by hand, retries; one thread) took 23.5 s and found 655 constants. The
machine was at load 14 to 48 on 20 cores; each configuration was run once.

| | 1 thread | 4 threads | 8 threads | CPU at 8 | Peak at 8 | Constants |
|---|---|---|---|---|---|---|
| `Split::none()` | 14.9 s | | 4.1 s | 22.9 s | 164 MB | 632 |
| default (whole first) | 31.7 s | 11.2 s | 7.2 s | 41.0 s | 225 MB | 674 |
| `Split::eager()` | 30.2 s | 9.6 s | 7.1 s | 38.6 s | 205 MB | 674 |
| `Split::shared()` (hubs first, from the bottom) | 9.5 s | 2.4 s | 1.9 s | 6.7 s | 123 MB | 674 |

Answers and costs were byte-identical at 1, 4 and 8 threads in every row, and the three
split rows give the same answers as each other.

- **Sharing is the larger part of the gain, once hubs are asked from the bottom.** A profile
  of `eager` showed 63% of the time in hub proofs the engine folds alone, 1,159 of them at
  14 ms each: a topmost hub is nearly its whole question, so asking it as written reaches
  nothing the questions share. `Split::bottom_up` asks the nodes where a varying value is
  cancelled, lowest first, and each hub above with those below written as constants: 1,393
  such proofs at 4 ms, and 1,170 tasks served from the store. On one thread that is 9.5 s
  against 30.2 s (and against the walk's 23.5 s); threads take it to 1.9 s.
- **Failing fast.** With `shared`, 11% of task time goes to 24 hubs that only sample
  constant and are refuted by the search, and under 2% to hubs left undecided; each is
  stored, so no sibling repeats it. The 27 questions that vary are answered from the
  samples at no cost.
- **Against the walk's answers**: 655 constants agree in value. 16 questions the walk calls
  `Varies` are `Constant` here; they carry path facts (`#47705 != 0`, `#47705 >=
  0x7ffffffeffff`) under which they are constant, and all 674 constants were also evaluated
  at up to 20,000 assignments satisfying each question's facts without a disagreement.
  3 the walk left `Unknown` are constants. 13 the walk calls `Varies` or `Atom` are
  `Unknown` here: `Ask::constant` does not answer "equal to an atom" (`Ask::equal` does).
- This does not carry over to the earlier stand-in questions, where hubs seldom fold on
  their own: `shared` is for questions that overlap as these do.

## Moving a consumer to it

| Consumer layer | What replaces it |
|---|---|
| Budget-exact memo around `NormalFormSolver` | Nothing: delete it from 0.30.1 on. |
| Avoiding the process-wide simplifier in `prove` | `prove::valid_under_with(.., &Simplifiers)`, or a `Session`, which owns its engines. |
| A context per question | One context per boundary; `session.run(&mut cx, &asks)`. |
| Hand-rolled hub splitting | `Config::split`: `Split::shared()` for the words of one state (questions that share most of their nodes), the default otherwise. `Config::hub` bounds a hub's proof apart from a question's. |
| Its own memo of questions | The session's store, across calls; `Reply::source` and `Session::stats` say what it served. |
| Background retry threads, abandoned proofs | `Ask::cancellable(&cancel)`; `Reply::cost` of an `Answer::Cancelled` is what was spent. A larger budget is another session (a `Config` is fixed for its session). |
| "Is it a constant?" by simplifying and looking | `Ask::constant(e)`: `Constant(value)`, `Varies(two assignments)` or `Unknown`. "Equal to a given atom" is `Ask::equal(e, atom)`. |

Per boundary: build every word's expression in one `Context`, one `Ask::constant` each with
`.under(&facts)`, one `run`. Keep one session per budget for the walk; it bounds its own
memory (`store_nodes`).

## Not verified

- Wall-clock scaling on an idle machine; every timing above was taken under heavy load.
- One walk has been measured (above). It is one round's worth per boundary, without the
  questions under 2 ms; the store never reached its limit, so eviction was not exercised.
- Case splits and term regrouping are tested on constructed inputs; on the exported
  questions one chain was regrouped and no case split was needed.
- The long suites (`--ignored`), the Python and WebAssembly bindings and the book were not
  run or extended. `cargo clippy -p bitwright --no-default-features --all-targets` fails on
  `main` already (`engine/pass/tests.rs` uses a helper gated on `prove`).

## Where the request's numbers and this repository disagree

- "29% of candidate hubs fold": with the engine asked on the hub itself, 52% of topmost
  hubs fold as written here, and with three samples instead of 64 about 7% of candidates are
  not hubs at all (11,945 against 11,149 in the exported set).
- The exported questions each took 250 ms or more when dumped (54 s in total); on 0.30.2 the
  same 140 take 10.6 s, and three `equal` questions recorded as `Unknown(Budget)` are now
  refuted.
- "A fresh context per question pays for all 2,000 nodes": about 1–2 ms of a 25–50 ms
  question here.
