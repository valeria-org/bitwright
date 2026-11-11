# Changelog

## Unreleased

- **A root that is a linear MBA whole is read as one before the first round**
  (`Stage::Whole`; `Strategy::whole_first`, on by default). The linear-MBA pass's step is
  taken at the root before the phases walk it, by the pass's own commit rule: one question
  of the root's signature, where the walk asked one of every sum below the root, and of
  the bitwise functions under those, to find the same form once the parts were in theirs.
  On CoBRA's MBA datasets the median goes from 0.28 ms to 0.09 ms, the 95th percentile
  from 3.6 ms to 1.8 ms and the whole run from 67 s to 34 s; a sum of bitwise functions of
  five variables takes 0.47 ms where it took 9 ms. 75,661 of the 75,737 scored expressions
  are solved (75,579 before): 102 more, and 20 that were, no longer (the form found from
  the root is a node or two larger than the one the walk found). To an observer the step
  is a stage with one part; it counts among the run's rewrites. Rules are learned from the
  pass's steps in its phase, not from this one (a step of the input as written is rewritten
  by the rules before a rule for it would match).
- **The normal-form solver builds half as many two-term decompositions** of a linear form
  over up to three atoms (4 of the best estimated where it built 8, 3 forms of each
  function where it tried 5, 4 pairs sharing a subterm and 4 with a coefficient taken out
  where there were 8), and a linear form that is one bitwise function is rendered as that
  without the searches for sums. On CoBRA's datasets 80 answers of 76,080 change size (41
  smaller, 39 larger), four more are solved, and the run takes 5 % less (the 95th
  percentile 1.6 ms where it was 1.7 ms); a deobfuscator's slow questions take 13 % less.
  Building a quarter as many takes 9 % less and leaves 368 answers larger, which is why
  it is a half.

## 0.30.0

bitwright becomes a solver that also simplifies (see `docs/design.md` §0 and the book's new
chapter, *Solving*).

**Solving**

- **A solver session** (`bitwright::solve`, feature `prove`): `Solver` keeps an assertion
  stack with `push` and `pop`, and answers `check`, `check_assuming` and `check_within` (a
  deadline) with a model (`model`, `value`) or an unsatisfiable core (`unsat_core`: sound, not
  minimal). A check answers from constants, independent slices, the last model, remembered
  answers, a quick search on a circuit the solver keeps, then the prover; `decided_by` says
  which.
- **A model at the level of words before any circuit** (`solve::Config::probes`,
  `DecidedBy::Probe`): the last model is repaired by solving each false predicate for one
  symbol through the operators that can be undone, then a few assignments are tried; what
  comes of it is evaluated. A new 64-bit equation that took 157 µs to blast and search takes
  2 µs, a push, an assertion, a check and a pop 2 µs where they took 121 µs, and a check on a
  path condition of 400 steps 84 µs where it took 344 µs.
- **Products and divisions as unknowns** (`solve::Config::abstraction`, off by default;
  `DecidedBy::Abstraction`): a question the quick search leaves open is asked with each
  product, quotient and remainder of two unknowns as an unknown, defined when a model gets
  it wrong. On the limb-arithmetic sets here it decides nothing the other stages do not and
  costs up to twice their time, which is why it is off.
- **Symbols that are not constrained are taken out** (`solve::Config::unconstrained`, off
  by default): a symbol that occurs once under a sum, an exclusive or, a product by an odd
  constant or an equality frees that term, and the model gives it its value back. Off
  because the simplifier decides some questions by the form of their terms: of 18 large
  equivalence questions one is no longer decided with it on.
- **A local search after the assignments** (`solve::Config::local_search`, rounds; off by
  default): a walk that repairs a false predicate or changes one of its symbols at random.
  On 200 limb slices 16 rounds find two more models and cost each unsatisfiable question
  40 µs more than its 60, which is why it is off.
- **The store learns what the quick search needs** (`solve::Config::learn_budgets`, off by
  default): `Answers` keeps, per shape of question, the most conflicts the kept circuit took
  to decide one, and with the option a shape decided several times is given a few times
  that. On the limb sets no shape recurs often enough for it to change anything.
- **The quick search has 1,000 conflicts** (200 before): on three sets of limb-arithmetic
  questions together, 579 ms where 200 conflicts took 1,218 ms.
- **Fixed: a kept circuit stopped answering once it had 50,000 gates.** A question's
  allowance of gates was counted from an empty circuit, so every later check of a long
  session went to the prover. A kept circuit that is mostly of predicates no longer asked
  is now started again.
- **What an answer rests on** (`Solver::tier`, `(get-info :tier)`, `(get-info :decided-by)`):
  a model that was evaluated; unsatisfiable by folding, by the circuit and the search alone,
  after the simplifier, from an earlier answer, or from remembered hashes.
- **One circuit and one search for many questions** (`prove::Incremental`): each predicate is
  blasted and encoded once, the search keeps what it learns, and an unsatisfiable answer
  names the predicates the last conflict went through. A path condition of 400 steps costs
  0.4 ms a check where posing each question anew cost 9.5 ms.
- **The SAT search behind a trait** (`prove::Backend`), with bitwright's own as the default
  and CaDiCaL in the new `bitwright-cadical` crate (not a default member of the workspace: it
  builds a C++ solver). `solve::Config::backend` gives the long searches to it.
- **Definitions are solved before the prover is asked** (`solve::Config::solve_equations`):
  `x == t` puts `t` for `x` in the rest of its slice, and the model gives `x` its value back.
- **Answers that outlive the process** (`solve::Answers`): what checks answered, by the
  hashes of the questions, as text the host keeps; a model from them is checked before use.
- **Results that outlive the process** (`engine::Remembered`, `Engine::run_remembering`):
  an expression the engine has simplified, or a part it took down to a few nodes, is replaced
  by the result when it appears again, in any context or run. A second pass over the 96
  simplification questions of a deobfuscator's slow log takes 8% of the first.
- **A full store of results makes room, and stores merge** (`Remembered::with_max_entries`,
  `Remembered::merge`): the eighth of the entries used longest ago is dropped when the
  store is full (it stopped learning before), and the stores of two runs are one.
- **A rollback for long sessions** (`Context::checkpoint`, `Context::rollback`,
  `Solver::forget_since`): what a question built is removed when it is answered, and the
  context stays the size of the state that lasts.
- **Proofs as LRAT** (`prove::lrat`, `Certificate::lrat`): every learned clause with the
  clauses it follows from, in the order unit propagation uses them, read off the DRUP proof
  as it is checked; `lrat::check` verifies such a proof without any search and shares no
  code with the solver or the DRUP checker, and `lrat::to_text` writes the format other
  checkers read.
- **The limb-arithmetic pass can be made to prove what it writes**
  (`Strategy::words_proved`, `prove::Config::proved_words`, `solve --proved-words`): a result
  replaces a root only once a circuit and a search have proved the two equal. Of 24 hard
  limb questions it keeps 20, where leaving the pass out keeps 13.
- **The engine's passes ask a prover through an interface**: the two passes that prove their
  candidates no longer name the prover, which the crate hands them.
- **`mba::decide`**: [`mba::equal`] with facts (expressions known to be zero, used where they
  are bitwise functions of the parts: two fields with no bit in common make a sum a
  disjunction) and with a witness when the sides differ (values of the symbols, evaluated).
- **`prove::Config::strict`**: the prover's simplifier without the limb-arithmetic pass, the
  one that commits what it derives without a proof.

**SMT-LIB**

- **Scripts run as a solver** (`smtlib::run`, `smtlib::Session`, `bitwright solve`): `push`,
  `pop`, `check-sat`, `check-sat-assuming`, `get-model`, `get-value`, `get-unsat-core`,
  `get-unsat-assumptions`, `get-assertions`, `get-info`, `get-option`, `set-option`,
  `get-proof`, `echo`, `reset`, `reset-assertions`. A `Session` is fed a script in pieces and
  answers each command when it is complete: `bitwright solve -` drives through a pipe.
- **The importer reads more**: `define-fun` with parameters, `define-const`, `define-sort`
  and `declare-sort` without parameters, `(! t :named n)`, the overflow predicates,
  uninterpreted functions (a symbol per application and a constraint per pair of them),
  and rounding-mode variables (a term is read once for each mode).
- **Arrays are compared, chosen and constant**: `=` and `distinct` over arrays (a Boolean
  with the constraints of extensionality), `ite` over arrays, `(as const …)`, and stores into
  any of them.
- **Quantifiers where a witness or a small domain decides them**: an asserted `exists` and a
  denied `forall` bind new symbols at any width; elsewhere a quantifier is read once for each
  value of up to 12 bits of variables, and a wider one is refused.
- **Bit-vectors above 512 bits in a session**, up to 65,536: read as limbs, for the bitwise
  operators, sums, differences, products, orders, shifts, rotations, `concat`, `extract`,
  the extensions, `ite`, and the divisions and remainders (a bit of the quotient at a
  time). On 38 scripts at 513 to 2,048 bits the values and answers are z3's.
- **A rounding mode chosen by a condition** (`(ite c RTP r)`), as the mode of an operation
  or compared with another: read once for each mode, like a rounding-mode variable.
- **`solve --gates <n>`**: the most gates a check's circuit may have (4,000,000 by default).
  A question of 320 stores at unknown addresses, each read back, needs more and was
  answered `unknown`; with 16,000,000 it is answered.
- **Integers where bit-vectors bound them**: `bv2nat` (`ubv_to_int`, `sbv_to_int`),
  numerals, `+ - * abs`, `div` and `mod` by a constant that is not zero, the comparisons,
  `ite` and `int2bv`, each read as a bit-vector wide enough that nothing wraps. An integer
  variable has no range and is refused. 11 of 13 scripts give z3's answers and values; the
  other two are identities z3 does not answer in a minute.
- **Fixed: terms first read by `get-value` or `check-sat-assuming`** (an application of a
  function, a read of a compared array) were answered before the constraints that tie them
  to the others were asserted.
- **What SMT-LIB leaves unspecified is open in a session**: the zero that `fp.min` and
  `fp.max` return for zeros of different signs, and `fp.to_ubv`/`fp.to_sbv` of a NaN, an
  infinity or a value out of range, were bitwright's own definitions, so a script could be
  answered `unsat` where the standard has a model.
- **`(exit)` ends a script.** The importer read the commands after it.
- **Fixed: an assertion read as a definition while it constrained its own constant.** The
  exporter's float-bits pattern `(ite (fp.isNaN T) (= c NAN) (= (to_fp c) T))` was read as the
  definition of `c` also when `T` or `NAN` read `c`, which dropped the constraint: an
  unsatisfiable script could import as satisfiable.

**Lean**

- **Theorems as rules, in the core** (`rules::lean_import`, `bitwright lean-rules`): the
  importer moved from the WebAssembly crate; it refuses a statement whose proof is `sorry`,
  reads a comparison stated `= true` or `= false` (and writes the rule for its negation too),
  and `--verify` runs `lean` on the file first. With `solve::Config::simplifier`
  (`solve --rules`) the rules take part in solving.
- **Rules that count bits are stated** (`bitwright lean`): `clz`, `ctz` and `popcnt` as Lean
  4.29's `BitVec.clz`, `BitVec.ctz` and `BitVec.cpop` (a population count only in the
  statement for every width: `bv_decide` does not read one yet). At 8 bits Lean proves 373
  of the 375 built-in rules it is given, `clz` and `ctz` among them.
- **Cores as theorems** (`prove::lean_theorem`, `Solver::lean_theorem`, `(get-proof)`): the
  conflicting assertions as a Lean 4 theorem with the proof `by bv_decide`.

**The engine**

- **Limb arithmetic is read back on words of up to 128 bits** (64 before). A sum, a
  difference or an exclusive or written in limbs, with its carries and borrows, is the
  word's own operation at any split of a word of 65 to 128 bits: a 128-bit sum in two
  64-bit halves is `x + y`, and the high digit of a 67-bit sum with its carry as a
  comparison is `extract<12, 55>(x + y)`. The pass computes in 256-bit integers for this; a
  question with no node above 64 bits is read within the bounds it had, and gives the
  results it gave.
- **A tiny simplification does not pay for the context's size.** The runner's per-node
  tables cost what they hold: a five-node expression in a context of four million nodes
  took 19 ms and takes 19 µs. In a context of at most 16,384 nodes they are the dense
  tables they were (a hash map there cost the MBA datasets up to 40 % of their time).
- **A linear MBA of five or six variables is read whole.** The linear-MBA pass looked at
  fragments of at most 256 nodes, and a sum of twelve bitwise functions of five variables
  written out has 600: such a sum was solved only where its parts happened to cancel
  first. It reads fragments of up to 2,048 nodes. Of the 1,000 expressions of CoBRA's
  `simba/e1_5vars` set 869 were solved, in 31 ms at the median; all are, in 9 ms.
- **The limb pass's wide integers cost what machine integers do where the values are
  small**: sums, products, shifts and comparisons of values of at most 64 or 128 bits take
  the machine's own, forms are hashed as two words, and a bound over the bits of an AND is
  added up a run of equal bits at a time. With 0.29.0's readings on the 256-bit integers
  the MBA datasets took 10 to 25 % longer than 0.29.0; they take what it does within 2 %.
- **Results are kept per engine and assumption set** (four sets): changing either no longer
  drops what the other had found.
- **An equality of two linear MBAs is decided by the signature of their difference**, also
  where neither side is rewritten into the other: `(s + t) == (s | t)` for disjoint `s` and
  `t` is true.
- **`Context::structural_hash`, `Context::shape_hashes`, `HASH_VERSION`**: an expression's
  hash, and the hash of its shape (constants, symbols and the order of commutative operands
  forgotten), as public, versioned functions of the expression alone.
- **`mba::equal`**: whether two expressions are equal by the MBA procedures alone.
- **The analyses without the rewriting** (`Engine::linear_form`, `xor_form`,
  `bitwise_form`, `predicate_form`, `under_mask`): an expression as the sum of constant
  multiples of terms, as the exclusive or of masked terms, as a truth table over at most
  three terms on each class of bit positions; a predicate as a set of values of one term or
  of relations of two; and an expression as it is where only some of its bits are read. What
  the linear, xor, bitwise, comparison and demanded-bits passes read, with the context's
  facts, each exact on a randomized test.
- **A rolled-back question is answered as in a context of its own**: documented and tested.
  What an earlier simplification leaves in a context can change the next one's result
  where they share parts (the passes count the nodes a run creates as uses); between a
  checkpoint and a rollback it cannot.
- **`Context::forget_results`**: drops what the engine remembers of its earlier runs in the
  context, for a host that wants a result to depend less on the expressions simplified
  before.
- **A simplification with its steps** (`Engine::derive`, `engine::Derivation`): every rewrite
  with the rule or pass that made it, grouped by phase. `Derivation::check` proves each step
  again without the engine (polynomial arithmetic, the corners of a linear MBA, or the circuit
  and the search) and says what it could not; `Derivation::lean` writes the steps as Lean
  theorems. The opaque-constant sweep reports the parts its rewrite of a root is made of
  (`Event::Part`: each subexpression it proved constant or equal to another), so a sweep is
  steps like any phase. On a deobfuscator's slow log 97% of 8,297 steps are proved and 192
  of 199 phase transitions are accounted for by their steps; no question is certified end
  to end yet.
- **Rules from what passes did** (`engine::learn`, feature `check`): a pass's step with the
  shared subexpressions as parameters, kept when the checker finds it sound and it is proved;
  returned as a rule file and its ledger. Measured on the slow log it gains nothing over the
  passes it was learned from; `Remembered` is the memory that pays there.

**The prover**

- **Fixed: shared sums could ask another question** (`Config::shared_sums`, in 0.29.0). The
  carry of a comparison is an exact quotient of three low sums as numbers. Added up as a
  64-bit form, a slice cut at another's end has its upper part under the coefficient times
  a power of two, which wraps where the coefficient is large (near `2^43`, cut at bit 21):
  the quotient was then off by a multiple of `2^(64 − k)`, which a limb kept in a register
  wider than the limb reads, and a true limb identity at a 44-bit split was written again
  as a false one (reported from 23-bit limb products as "the prover's counterexample does
  not refute"). The sum is taken per bit in 128 bits; no carry is given up for it. A slice
  whose low sum cannot be kept as a number is left as a value.
- **Divisions by constants read without the simplifier** (`Config::divisions`, opt-in): the
  simplifier's division pass alone, for a question asked with `simplify` off. With the
  simplifier (the default) `trunc<32>((zext<64>(x) · 0xcccccccd) >>u 35) == udiv(x, 10)`,
  its 64-bit form and the quotient by 10,000 are proved without a search; without it they
  are a multiplier against a divider, undecided after 200,000 conflicts, and with the
  option they are proved as before.

**Synthesis**

- **Comparisons are candidates** (`synth::Config::comparisons`, on by default): `== != <u
  <s`, each the value 0 or 1 at the target's width. `(x | −x) >>u 63` is `zext(x != 0)` and
  `((~x & y) | ((~x | y) & (x − y))) >>u 63` is `zext(x <u y)`.
- **Two terms of the enumeration make an answer**: where no term has the target's values,
  each term `t` is tried with the term that has the values of what is left of the target
  (`t + c`, `t − c`, `c − t`, `t ^ c`; the other is looked up, not searched for). An answer
  of up to twice the enumeration's size is found where its top is one of these: `x1 − 2 −
  zext((x0 == 0) | (x1 == 0))` and `(x & 0xffffff00) | zext((x & ~1) == 2)`, of 11 and 9
  nodes, are found under noise at the default size of 7, in about a second each.
- **Selects are candidates** (`synth::Config::selects`, on by default): `select(c, a, b)`
  with `c` a candidate that is 0 or 1 at every sample. `y ^ ((x ^ y) & −zext(x <u y))` is
  `select(x <u y, x, y)`. A comparison takes the place of a term of its size with its
  values (`x == 0` of `1 >>u x`), so conditions read as comparisons. A search that finds
  nothing takes the time it took: the terms kept are bounded by `max_terms` either way,
  so with more operators fewer of the largest terms are reached.
- **The constants a slice implies are candidates' constants**: bits `[lo, lo + n)` of a
  value give `2^n − 1`, that mask in place and `lo`, so `zext<64>(trunc<8>(x ^ y) ^
  trunc<8>(y))` is `x & 255`, which mentions no 255.

**Around it**

- **The features `mba`, `smtlib` and `eqsat` are on by default** (with `check`, which was).
  A build that wants the core alone says `default-features = false`.

- **The solver in C and Python** (`bw_solver_*`, `bitwright.Solver`).
- **Transformation verification asks one solver** for the rounds of a search and of a
  minimisation.
- **A ledger vouches for a rule by its content** (`Ledger::vouches_for`,
  `Ledger::vouches_for_content`, `Ledger::merge`): a rule checked under one name is vouched
  for in another file or group or under another name, since its hash is of the rule alone.
- **`CheckConfig::with_require_proofs`**: a rule the native prover left undecided at some
  width is then inconclusive, for admitting rules nobody reviewed. Off by default.
- **A fuzz target for the prover** (`prove_dag`).
## 0.29.0

- **A relation between two nodes is proved on the expression as written first.** The
  opaque-constant sweep proves a node equal to an earlier one plus a constant on their
  difference with each operand taken on the bits its user reads. That writes one value read
  under several masks once per mask, a sum with a constant as a sum of its own for each, and
  a relation that is a bitwise identity over the value was then one over several carry
  chains: half the proofs of a measured call took a thousand solver steps or more, and the
  ones the readings could not find took their whole share. The difference as written is now
  read first, within an eighth of that share. A question asked with an eighth of the usual
  fuel went from 312 nodes to 80 in half the time, and the 44 `forms_simplify` questions of
  the same set take a third less time (13% less CPU over the 140; the 16 proofs of that set
  take a tenth more, their relations being the ones the reduction proves).
- **The MBA phase leaves the sweep a part of the solver's steps.** Where the opaque-constant
  sweep runs, the phase's questions stop a sixteenth of the call's steps short. What a round
  leaves is often a sum the sweep's certificates decide in a few hundred steps, and the
  solver's last questions of the round had taken every step: the question above stops at 42
  nodes with the part kept.
- **With the solver's steps gone, the sweep's certificates are pass work.** A certificate of
  the opaque-constant sweep is charged to the call's MBA solver steps, and with none left
  the sweep asked nothing more, whatever the call still had of pass work (four fifths of it,
  in the question above). Once fewer steps are left than a small certificate takes, the
  sweep's certificates are charged as pass work, as the gate's are: 32,768 units each at
  most and an eighth of the call's pass work in all. What decides a sum over one value under
  masks is a comparison of two forms, a few hundred evaluations. The question above folds to
  its constant at its own fuel, in three quarters of the time it took to stop at 312 nodes;
  all 47 `engine` roots of the set are constants.
- **A settled root is read on either side of its condition** (`MbaConfig::noise_forms`). An
  obfuscator picks between two masked values by a flag (the parity of a byte, in the
  measured set) and computes with the one picked. With the flag fixed one of the two is a
  constant and everything computed from it folds, but the root as a whole is a function of
  both, and no pass reads it one case at a time. The root the rounds settle on is now split
  on the condition its selects test most, each side is swept and given one round, and the
  two are written as one expression again with the choice as far down as they agree
  (`select(c, a * k1 + b, a * k2 + b)` is `a * select(c, k1, k2) + b`). The smallest of the
  settled root, the select of the sides and the joined form is the result, so none is larger
  than before: 41 of the 44 `forms_simplify` roots of the set are smaller, 7,391 nodes to
  6,407 in all, for 15% more time on those questions (the 140 take the same time within
  what repeated runs differ by). A run whose budget ends on the sides reports that.
- **A fragment not answered whole is asked over its atoms.** A sum like
  `(a & b) + (b & c) - 2·(a & b & c)`, which is `(a ^ c) & b`, over an `a` and a `b` that are
  products of one value is a question about that value when read whole: costly, declined,
  and every sum holding it was then not asked at all. Such a fragment is now asked with the
  arithmetic under its bitwise operators as atoms, within the steps of a retried question.
- **Values of one or two words take a short path.** A `BitVec` holds eight limbs whatever
  its width, and equality, the hash, `is_zero`, `is_ones`, the conversions and the
  constructors read or wrote all eight: for the 64-bit values of a measured set, a tenth of
  the time. They read the active limbs now (one word at 64 bits and below); a slice, a
  concatenation and a sign extension within 128 bits are native; the internal hasher takes a
  small field in one round; and three buffers that grew a push at a time are sized once (a
  question's scan, its lowered form, and a node's samples, whose operands are looked up once
  a node, not once a point). 140 measured calls take 3 to 5% less time with the same results.
  The layout is unchanged (values up to 512 bits stay `Copy`); a `BitVec`'s hash is that of
  its width and active limbs, no longer the derived one.

Operations of many operands in the words pass, and the forms 0.28.0 names as not read whole.
On the corpus of 0.28.0, and on 592 expressions written for the purpose: one operation (XOR,
sum, AND, OR) over 2 to 128 operands, written twice in two orders and groupings and
compared, subtracted, sliced and masked; and a word made handler by handler in limbs from as
many operands (XORs spelled `x + y − 2·(x & y)`, sums, differences, and the three mixed),
its high limb read alone, against the same chain in another order, and against the word
written as nodes.

- **An XOR is one value however it was grouped.** The words pass read `x ^ y` as `x + y −
  2·(x & y)`, a different form for each grouping of three values or more: two orders of one
  XOR were not seen equal from 4 operands on, and a word XORed in limbs was not read from 5
  (62 nodes left where 10 are the answer, 2,664 at 128 operands). An XOR is now also a term
  of its own: of its operands as integers, any number of them, each once and in one order,
  the operands of an XOR among them its own and two of one gone. A slice of it is the XOR of
  the slices, so the limbs of an XOR are slices of the one term; an AND has the relation
  `2·(x & y) = x + y − (x ^ y)` with it, and every sum is kept at the member of its class
  with the fewest terms, so the XOR spelled as a sum is the same term, `(x ^ y) + 2·(x & y)`
  is `x + y` and `(x ^ y) + (x & y)` is `x | y`. `trunc<20>(((a >>u 12) ^ (b >>u 12)) ^ (c
  >>u 12))` is `extract<12, 20>(a ^ b ^ c)`.
- **A root is asked with each reading of its XORs, and the smallest answer is kept.**
  Bitwise code is read by the terms; arithmetic done on an XOR in limbs is read by the sum,
  whose carries are the arithmetic's; and the operands of a term that are truncations of
  wider words read better as the words where sums are made of them, and as the values where
  they are not. So a root is asked with the terms over the words, with them over the values
  where that differs, and with the sums (the forms the pass had) where arithmetic was done
  on an XOR. Of two answers as small the sums' is taken, and the root that is the sums'
  answer is asked with the sums again, so a root with nothing of the kind under it is read
  as before. Where the terms' answer is the smaller, the smallest is not known yet: the sums
  find what they find in several steps, each from the root the one before left, and the
  terms' smaller root is not always one anything more is found from. Both answers are then
  followed to where nothing more is found (the sums' with the sums alone, the terms' with
  every reading) and the end with the smaller DAG is taken. A later question may take about
  twice the work of the first, and once those not taken have cost a call 2^23 only the
  first is asked.
- **A chain of ANDs or of ORs is read with its operands in one order**, each once, whatever
  the order and the grouping it was written in (three operands or more, through at most 256
  nodes): `(a & b & c) ^ (c & (b & a))` is 0. Two orders of one chain were not always seen
  equal: from 4 operands of an OR on under `==`, from 6 of an AND.
- **A value chosen limb by limb between a register and a constant is the limbs of one
  choice.** With the XOR terms a choice against a constant is taken apart, `c ? K : b` being
  `K·c + (c ? 0 : b)` and `c ? a : K` being `K − K·c + (c ? a : 0)`: each limb's choice
  against its own digits of the constant is then a slice of the one choice against 0, and
  the floor of a choice against a constant is the choice between the floors. Written back,
  the constant and the choice against 0 are the choice with the constant again.
  `zext<32>(select(t, 113, trunc<12>(r))) | (zext<32>(select(t, 0x352ac, extract<12,
  20>(r))) << 12)` is `select(t, 0x352ac071, r)`.
- **A form may have 256 terms.** It had 40 at most, so a sum of 48 values was not one form:
  two orders of it were not seen equal under `==` or a mask, nor was a sum of as many made in
  limbs seen to be the word. A root with a form of more than 40 terms is asked with the
  forms of 40 too.
- **A refusal for depth is not counted against the next.** The algebra bounds how deep its
  functions call one another, at 48. A call refused at the bound did not give its level
  back, so each refusal lowered the bound for the rest of the root, and after 48 of them
  every node was read as a value of its own. Found while the XOR terms were written.
- **Writing an XOR of many operands is charged to the meter**, and looks for the XORs of
  some of its operands that are already nodes in one pass over them (the longest first).

Of the 592 expressions, two (a minimum of 96 and of 128 values written as nested `select`s)
are refused by the parser for their depth, as before. Of the 590 others, every one of one
operation in two orders is now seen to be one value, at every size, and a word XORed or
added in limbs is read at every size, alone and against the word written as nodes. Two such
chains in two orders are seen to be one value up to 48 operands (XOR) and 96 (sums); beyond
that a part of each is read. Chains that mix sums, differences and XORs are read up to 10
operands, as before, and six of them (24, 64 and 96 operands) are larger than before, by 1
to 20 nodes; no other is larger.

On the corpus the results have 6.8 percent fewer DAG nodes than with 0.28.0 (5,296,890
against 5,681,862): 0.7 percent fewer on the local windows, 7.7 percent on the deep ones.
19,309 of the 58,530 are smaller and 632 larger (by 3 nodes at the median, 81 at most,
3,733 together against 388,705 saved); the same 10 run out of budget. The forms 0.28.0
names as not read whole now are in the examples looked at: products of an XOR in limbs by a
constant (35 nodes to 24, 35 to 22 and 23 to 21), XORs of several values in different
orders (24 to 10), and a value chosen limb by limb between a constant and a register (52 to
17; a second example of it, 38 nodes, is as before). The numbers are of the build before
the last change, by which the work of the answers that are followed and not taken counts
with the questions not taken: of the 57,672 results the build with it was run on, 46 are
larger than there, by 401 nodes together, and none is smaller.

The 632 larger ones, by the first rewrite at which the two runs of a call differ: in 541
(2,928 nodes) this pass's answer is the smaller one and another pass ends larger after it,
the result of a call depending on the path the passes take; in 32 (560 nodes) this pass's
own answer is larger, the sums' question having been cut short by its allowance in the
three looked at; in 17 (87) the two answers are as large and differ in form; in 35 (147)
one of the two runs has no answer of this pass at that point; and in 7 (11) the runs
differ first in another pass.

Simplifying a sample of 3,000 of the corpus takes 1.21, 1.36 and 1.42 times the processor
time it took (three runs of each, one after the other, on a loaded machine): a root is
asked up to three times where it was asked once, and where two answers disagree both are
asked on. The 590 expressions take 0.81 to 0.85 times theirs.

More readings of limb arithmetic in the passes that run before the words pass (the carries
pass's slice fit and the borrows it reads, the linear and demanded-bits passes), on the same
corpus: a line of work begun before that pass, merged with it.

- **A word several limbs read under different masks stays one node.** The demanded pass wrote
  an operand once per mask it was read under, so a word read under 7 and under 14 bits became
  two, each with its constants reduced to its reader's bits (`x * 7 - 59` beside
  `x * -249 + 4933`). It now simplifies the operand a second time with each such node read
  under the union of its masks, and takes that where it frees no fewer nodes.
- **A narrowing uses a slice that is already there.** Where the casts pass, pushing an
  `extract` in, reaches a node whose slice something else already reads, it stops at that
  slice: `trunc<32>(zext<64>(a) + s)` beside `trunc<32>(s)` is `a + trunc<32>(s)`, where
  narrowing `s` again built it a second time and paid for neither reader.
- **Operations common to both arms of a `select` are done once.** `select(c, F(a), F(b))` is
  `F(select(c, a, b))` where the arms are the same operations over operands that differ in a
  pair or two (a pair that is the same slice of both values of another counts with it), and
  the DAG gets smaller. A register read limb by limb, each limb through its own chain of
  `select`s over slices of the registers, is the limbs of one chain over the registers.
- **Limbs of one word in a linear form are the word.** `lo(W)·K + hi(W)·(K << k)` is `W·K`:
  the linear pass reads each term that is some bits of a value (a mask, a shift, a slice, a
  digit of a digit, the bits a `concat` or an extension passes on) as coefficients on those
  bits, adds the coefficients of all terms over one value bit by bit, and writes the bits
  again as the fewest slices. Any number of limbs join, in any spelling, and so do
  `W - lo(W)` and a product of the word beside a product of one limb. An identity of the
  integers modulo the form's width: nothing is proved.
- **Limbs are joined modulo the bits that are read.** The demanded pass joins the limbs of a
  sum under a mask at the mask's width, and reads a carry at the width of the union of its
  readers' masks, where the sum's own width allowed neither.
- **A carry is read against the word a low digit was computed apart from.** A handler
  computes a low digit at the digit's own width, the word's constants reduced to it
  (`trunc<9>(x) * 177` for the low 9 bits of `x * 0x2d4b1`). Where a sum holds a high digit
  of a word and a carry of such a digit, the digit is read as the word's low bits:
  `zext(t + 301 <u t) + extract<9, 9>(x * 0x2d4b1)` with `t` that digit is
  `extract<9, 9>(x * 0x2d4b1 + 301)`.
- **`low != 0` is the borrow of a negation**: `hi(a) - hi(-b) - [lo(b) != 0]`-shaped sums are
  read like the ones with `<u`.
- **The slice fit reads more shapes.** A slice of a sum above its low bits, and a value put
  together with `|` or `concat` read whole, are looked for as slices of a wide node like a
  sum under a read of its low bits; a value whose cone holds such a slice counts as limb
  code. The proofs of these have an allowance of undecided ones of their own.
- **A difference compared with its own constant** (`a - (b + k) == -k`) is `a == b`.
- **A carry out of a middle digit is read.** A comparison of the bits `[o, o + n)` of two
  values, a constant added to either, is the comparison of their low `o + n` bits unless the
  digit of their difference is all ones and a carry comes into it; where a bit of that digit
  is known 0 the carries pass reads it so. A constant added limb by limb writes its carries
  this way: `zext(extract<10, 10>(x + 837) - 156 <u extract<10, 10>(x)) + extract<20, 12>(x)`
  is `extract<20, 12>(x + 0xd9345)`.
- **Digits computed in a register narrower than the word are the word's.** Where the sides of
  a carry are truncations of wider values, the sum reads more bits than the register has
  above the digit, and the sum holds a high digit of a value that wide, the carry is read at
  that width: the middle limb of a 64-bit `x - y` in limbs of 26 bits, its low limb computed
  in 32 bits, is `extract<26, 26>(x - y)`.
- **Digit terms that are one value written two ways meet in more spellings.** A partial
  product shifted into place beside the product's own high digit (the zeros all the
  coefficients of a form end in are dropped and the slice read that much lower); a slice of
  a sum beside the slice of the same sum under a constant that differs above the digit; a
  slice of a bitwise value under another operation beside that operation over the slices
  (`hi(a ^ b) & c` and `(hi(a) ^ hi(b)) & c`); the limbs of one word held apart by the two
  sides of a carry, joined in their difference.
- **The terms beside one high digit are taken into its word.** `A + hi_k(P)` is
  `hi_k(P + (A << k))`: where a sum is left a high digit and terms that are limbs of the
  same word once shifted (the cross products of a schoolbook high limb), it is the slice of
  the joined word: the high limb of a product by a constant in 13-bit digits is
  `extract<26, 6>(x * K)`.
- **An XOR or an OR with a constant written as a sum is read as one.** In a linear form that
  holds `a & c` for a constant `c`, a term over `a ^ c` or `a | c` is written over `a & c`
  (`a ^ c = a + c - 2·(a & c)`), so a carry whose two sides are the sum and the XOR has a
  difference that cancels; and `a + c - 2·(a & c)` alone is `a ^ c`.
- **A sum is read on the bits that reach the root.** A rewrite replaces a node by an equal
  one, so a limb's sum read through two truncations was read at neither: each reader's
  rewrite pays only once the other has let the sum go. After its walk the demanded pass now
  takes the root, computes the bits of every node below it that reach it, reads each sum
  with carries on those bits, costs each reading at its sum, and commits the root written
  over the readings where that is smaller. Taken where the round left the root unchanged.
- **A slice across the seam of a `concat` is narrowed in an arm of a `select`**:
  `extract<22, 10>(select(c, concat(a:6, concat(b:11, x)), g))` is
  `select(c, concat(a, extract<7, 4>(b)), extract<22, 10>(g))`, and `x` is no longer read.
- **Slice proofs: products as fresh symbols, and questions that are not asked twice.** In the
  scratch copy a slice proof is asked on, the highest products and variable shifts below
  the two sides are fresh symbols (an identity over a free symbol holds at the product's
  values; a copy that is refuted is asked again as it is). The proofs use the prover's
  carry-save multiplication and three-input XOR encodings. A second candidate is not asked
  after an undecided one, nor a question most of whose own sums and comparisons an undecided
  question had, nor a shape left undecided in an earlier round.
- **A slice proof is first asked with its sums written one way on both sides.** The search
  does not see through sums: `(a + b) + c` against `a + (b + c)` at 21 bits costs it a
  hundred thousand propagations, and a limb against its word is that question. The prover
  has an option, `prove::Config::shared_sums` (off by default), that reads both sides of a
  question as linear forms over slices, slices of sums as high digits and one carry,
  comparisons of low digits as carries, and writes them again in one order; the slice fit
  asks each question so first (2^14 propagations), then as it stands. One question in ten
  is decided by the form alone.
- **A carry-out detector with a carry in is the carry at the limb's upper boundary.**
  `[b + 1 & M == 0] & c | [lo(s) <u a]` (the limb below is all ones and a carry comes in, or
  the limb's own sum wrapped), the test of a middle limb's carry in an addition of three
  limbs or more, is `[lo_m(P) <u lo_m(Y)]` at the upper boundary `m` of the limb, and is
  read as the high digits like any carry: the top limb of a constant added in limbs of 13,
  13 and 6 bits is `extract<26, 6>(x + k)`. The limb's own sum is read for it as a slice of
  a word with its other terms beside it, whatever the sum itself is left; a carry whose sum
  reads more bits than its sides have is read at the width of a wider word the sum holds a
  high digit of (the top limb in a register wider than the word); and `x & M != M` is the
  borrow of subtracting 1.
- **The borrow of an XOR or an OR with a constant done in limbs is read.** The low limb of
  `x ^ c` (written `x + c − 2·(x & c)`) compared with that of `x + c` is a borrow whose two
  sides differ by `2·(x & c)`; the difference was left as `x + c − (x ^ c)`, a term with a
  high digit of its own, once the sum had become the XOR. It is read through the
  conjunction: `extract<18, 14>(x + c) − [lo(x + c) <u lo(x ^ c)]` is `extract<18, 14>(x)`
  for a `c` below the limb's top bit.
- **A carry read on more bits than its sides have is read off the sum with its carry out.**
  A register wider than the limb keeps the carry out of the word: `(a >>u 10) + (b >>u 10) +
  [lo(a + b) <u lo(a)]` on all 16 bits of a 16-bit register is no slice of `a + b`. With `S
  = zext(Q) + zext(P − Q)` the comparison is `hi(S) − hi(Q) − hi(P − Q)` of the integers, on
  any number of bits and with no fact needed. The carries of one word are read together
  (the borrow of an XOR written `a + b − 2·(a & b)` against the same `S`, where the
  difference is the conjunction), so a chain of such handlers telescopes; a window on a
  limb's raw sum, 70 nodes of carries and borrows, becomes two slices. A slice of `zext(a) +
  zext(b)` below the carry is the slice of `a + b`.
- **A carry is read over the word its sum holds a digit of, where its sides are another
  spelling of that word.** `[lo(P) <u lo(Q)]` depends on `P` and `Q` modulo `2^k` only. A
  product computed digit by digit (`lo26(x)·k0 + lo13(x)·(k1 << 13)`, the product modulo
  2^26) or with its constant reduced to the limb's bits is congruent to the product the high
  limb is a digit of; the carry is read against that one, and the sum's own digit stands
  for the carry's. The congruence is of the two linear forms with limbs joined, not a
  comparison of spellings. `x·K + C` in limbs of 17 and 15 bits, 60 nodes, is `x·K + C`.
- **One word at the root.** A sum that reaches the root on its low bits only is written over
  another sum of its width that is read on more bits where the two are congruent there (the
  product with its constant reduced to 20 bits beside the same product at 30): the limbs
  of `X·K + C` are then slices of one node, and their `concat` is a shift.
- **A constant beside a slice goes into the sum the slice is of** (`extract<lo, n>(B) + c` is
  `extract<lo, n>(B + (c << lo))`) where that is smaller; a sum with a carry under `~` (`a −
  ~c`, the way `a + c + 1` is written) is read; and the top limb of a product is joined
  with the rest where it is written over `v` for a word `X = v ^ (v >>u s)` (the two agree
  on the bits the shift leaves 0).
- **A narrow value added into the middle of a word is that word's sum.** `extract<o, n>(a) +
  t <u t`, the carry out of a digit to which a value that is no slice of anything was added,
  is the carry out of bit `o + n` of `a + (zext(t) << o)`: nothing carries into the digit,
  the shifted value being 0 below it. `zext<14>(zext<14>(b) + extract<32, 14>(a) <u
  zext<14>(b)) + extract<46, 14>(a)` is `extract<46, 14>(a + (zext<64>(b) << 32))`. Digits
  compared in a register wider than they are, are compared at their own width.
- **A limb is read as the slice of a word that is no node.** The proved slice fit looked for
  a value as a slice of a node below it. A handler that adds a constant adds it limb by
  limb, so the node the low limb is masked from has only the constant's low digit, and a
  window that reads a limb's raw sum past its register reads a word nobody computed. The
  fit now also tries `extract<o, n>(B + C)` for a wide node `B`, the constant found at one
  sample and checked at the rest, and `extract<o, n>(zext(a) ± zext(b) + C)` for a slice
  past `B`'s width, each proved before it is taken (within 2^12 propagations: nine in ten
  of those proved take none). Such a word is made in the late stage only: made below, it
  stands in the way of the slice of a node above. `x·K + C` in limbs of 9 and 7 bits is
  `extract<9, 7>(x·K + C)`.
- **More spellings of a carry's sides and of its difference meet.** A side written `(T & 1)
  << 13` is the low digit of `T << 13` (a word XORed with its own shift, in limbs); a carry
  is read over the word whose high digit the sum holds for its difference (`P − Q` in
  whatever spelling, where the sum holds the partial product shifted into place); the
  difference is taken modulo the bits the carry depends on where a side's digit is a term
  of the sum; `(t + s) − (t ^ s)` is `2·(t & s)` over `t` as it is written, where pushing a
  slice into a product had hidden it; and `hi(a) ^ hi(b)` beside `lo(a ^ b)` is `a ^ b`
  again.
- **An undecided certificate does not take the call's pass work.** One answer's certificate
  takes at most half of a call's pass work, and two answers no test decided were then the
  whole of it where limb arithmetic asks hundreds of questions an expression. Once the
  certificates that proved nothing have taken 2^24 units in a call, each further one is
  held to 2^23 (or what a direct test costs, as before).
- **A slice pushed into its operand is pushed once in a call.** The readings of limb
  arithmetic ask for the same slices of the same nodes in every round and from three passes;
  the answer reads the nodes and their facts only, and is kept.
- **The rounds have a late stage.** A reading that leaves a sum as many terms as it had (a
  carry written as the high digits it is, with nothing in the sum for them to cancel) is
  worth taking only where the whole expression gets smaller by it, and taken early it stands
  in the way of what the rounds read better (a limb proved a slice of its word one handler
  up). Once a round has changed nothing, the deeper questions and the words pass have had
  their turn, and a pass has left such a reading, the rounds go on with a flag set; under
  it the step at the root takes those readings together, costed over the whole root, and
  the stage's root is kept only if it is smaller than the one the stage began from, and
  only if no limit declined in the stage a question that none had declined before it
  (`Stage::Late` in `Event::Stage` says when it was given up).
- **A demanded-bits phase that leaves the root larger is given up.** The pass commits one
  reader at a time, each counted against the nodes it frees with the rest of the root as
  it was; several readers of one word rewritten that way can leave the root larger than
  the phase found it, and the words pass then reads less of it. The root the phase began
  from is kept.

On the corpus the results have 8.0 percent fewer DAG nodes with these readings than without
them (4,933,096 against 5,363,041): 2.3 percent fewer on the local windows, 8.9 percent on
the deep ones. 25,259 of the 58,530 are smaller and 6,442 larger (by 6 nodes at the median,
336 at most, 86,061 together against 516,006 saved): a reading taken in the rounds, before
the words pass asks, can leave it a root it reads less of. The windows with a carry left as
a number go from 16,059 to 14,501, and 3 run out of budget where 10 did (other ones). Every
result is equal to its input at 256 sampled points. The processor time is the same within
what two runs differ by (0.95 times, one run of each on a loaded machine).

## 0.28.0

Comparisons of limb arithmetic: digits of a wide number held in wider registers, compared and
tested for borrows, from a corpus of 58,530 windowed expressions of a devirtualizer's limb
engine.

- **A comparison is made at the width both sides fit in.** The invert pass compared truncations
  at their own width only where the full width decided nothing else. Where the known bits bound
  both sides of any comparison to `k` low bits, it now compares their low `k` bits, the
  narrowing pushed into each side, and a signed order becomes the unsigned one (both sign bits
  are zero): `(x & 0x1fffff) <u (y & 0x1fffff)` is `trunc<21>(x) <u trunc<21>(y)`. It commits
  where the DAG gets no larger and, on a tie, the tree gets smaller, so a digit shared by two
  comparisons no longer holds both back.
- **A zero difference spelled with a negation is equality** (`eq_neg_add_zero`,
  `ne_neg_add_zero`): `-a + b == 0` is `a == b`. The linear pass writes `-a + b` as `b - a` only
  where that frees the negation, so the borrow test `~((-a + b == 0) | (b <u a))`, which shares
  it, stayed; it is `a <u b` now.
- **A zero difference in the low bits is equality of the low bits** (`eq_trunc_sub_zero`,
  `ne_trunc_sub_zero`): `trunc<14>(a - b) == 0` is `trunc<14>(a) == trunc<14>(b)`.
- **A mask that is a slice is written as one on a tie.** The shuffle pass commits
  `zext(extract(x))` for a mask of a narrower slice also where the DAG only ties and the tree
  gets smaller: the masks of one digit share their constant, and each alone freed nothing.
- **A sum split into digits with a shift is read like one split with `concat`.** The carries
  pass reads `(hi << k) | lo` (or `+`, `^`, `-`) and constant `>>u` slices as it reads `concat`
  and `extract`, where the region also compares (the carry written `lo(s) <u lo(x)`), and its
  atoms may be of any width up to 64 bits: `((x >>u 21) + (y >>u 21) + zext(carry) << 21) |
  (x + y & 0x1fffff)` is `x + y`.
- **A carry written as a comparison of low digits is read as the high digits it completes.**
  `[lo(P) <u lo(Q)] = hi(P) − hi(Q) − hi(P − Q)`, so `hi(a) + hi(b) + [lo(a + b) <u lo(a)]` is
  `hi(a + b)`. The carries pass rewrites a sum that fits no affine form this way where that
  leaves it fewer terms and the DAG smaller, and the sum under a read of its low bits
  (`trunc<j>(s)`, `s & (2^j − 1)`) at those bits. A carry of values whose sum cannot wrap (by
  the known bits) is read at any width. Each side of the comparison is read through its
  truncations, masks and zero extensions; one that is no low digit is read as one where its
  known bits put it below `2^k`, or where it is `k` bits wide with the narrowing pushed into
  it. Terms that are one value written two ways (a shift beside a slice of the same bits, two
  spellings of one linear form) count as one.
- **A limb is the slice of the word it is a limb of.** A handler that computes in limbs
  computes its lowest limb at the register's full width and masks it, so the word is a node
  below every higher limb. Where a value's carries are not read as digits, the carries pass
  looks for the value as `extract<o, j>(B)` of a wide node `B` below it, keeps the candidates
  that agree at the verification samples, and commits the first that bitwright's prover proves
  equal within the pass's caps: the top limb of `(w + k) ^ c` in limbs of 12, 12 and 8 bits,
  ninety nodes of digits, carries and borrows, is `extract<24, 8>(w + k ^ c)`. The value is a
  sum under a read of its low bits, a shift left among them (`hi << k | lo`, the limb on its
  way back into a word, which then is the word), or what of a sum is not known to be 0. A
  slice of a node already there commits also where it leaves the DAG one node larger: the
  limb code it frees is shared with the other limbs, and what reads the slice takes it away
  again.
- **An XOR written as a sum is an XOR where its parts are shared.** The linear-MBA pass commits
  its form also where the DAG only ties and the tree gets smaller: `a + b - 2·(a & b)` whose
  `a + b` and `a & b` a carry also reads is `a ^ b`.
- **`a + a` is a shift by one to the shuffle pass**, as the linear pass writes it:
  `(hi + hi) | bit` of neighbouring bits of one value is one slice.
- **Two neighbouring slices of one bitwise value are one slice.** The casts pass reads
  `concat(hi(a) | hi(b), lo(a | b))` as the slice of `a | b` that covers both.

On that corpus the results have 16 percent fewer DAG nodes on the local windows and 22 percent
fewer on the deep ones, and 115 of the 234 that ran out of budget now finish (7 others now run
out).

Limb arithmetic read as arithmetic on the words, on the same corpus: what the comparisons
above leave, the digits themselves.

- **A new pass, `Words` (`Phase::Words`, phase name `words`), reads arithmetic done digit by
  digit as arithmetic on the words.** `Strategy::deobfuscate()` runs it after `Demanded`.
  Every node of at most 64 bits is read as an integer form `c + Σ kᵢ·tᵢ` whose terms are
  nodes, `floor(F / 2^k)` of forms, ANDs of forms and choices: a slice is two floors, a sum
  that may wrap is itself less `2^w` times a floor, `x <u y` is `−floor((x − y) / 2^k)`.
  Identities of the integers keep every floor in one shape, and in that shape the digits of
  the operands cancel against the carries between them by collecting terms: nothing is
  matched against a pattern of limb code, and nothing is proved.
  `trunc<20>((a >>u 12) + (b >>u 12) + zext<32>((a + b & 4095) <u (a & 4095)))` is
  `extract<12, 20>(a + b)`; three limbs, the carry into the third written through the carry
  into the second (`[b1 = all ones] & c0 | [s1 <u a1]`), are `extract<16, 16>(a + b)`, and
  the same of a difference with its borrows, the comparisons spelled `x <u y` or as a
  virtual machine's handlers do (`~((x == y) | (y <u x))`); `(x & 0xffff) * 0x1234567 +
  (x >>u 16) * 0x45670000` is `x * 0x1234567`; `extract<16, 16>(x * 5 + 0x1234) + 0xab` is
  `extract<16, 16>(x * 5 + 0xab1234)`; an XOR spelled `x + y − 2·(x & y)` in limbs is the
  slice of `x ^ y`; a register chosen between the low half of one value and the high half of
  another, limb by limb, is the limbs of the value chosen.
- **What is written back is decided on the whole root.** The limbs of a word share their
  carries, so no limb alone frees them. From the root down, each node's form is written out
  again (the floors of one form as slices of that one word, any part that a node below
  already is as that node), at its width and at the low bits of it that are read, sized
  against what the root reaches without the node, and the node is replaced for all its users
  at once where the root's DAG gets smaller. The result replaces the root by the commit
  rule, and is asked again until nothing is found. A root of more than 1024 nodes is left to
  its operands.
- **Each of its rewrites is compared with the root at the verification points first**, as
  the application of a rule linked without a proof is (`Verify::unproven_points`): the
  derivation does not rest on that, but a defect of the pass would be seen there, and the
  pass set aside for the call.
- **Its work is charged to the pass-work budget**, a unit for two scratch nodes or terms, and
  is capped at 2^23 a root and 2^26 a call, so that the pass alone does not use up a call's
  budget.
- **A range test of a truncation is a range test of the value.** The compares pass reads a
  set of values of `trunc<k>(x)` as one of `x` (a copy for every value of the bits dropped),
  as it does through a mask, so a test the invert pass made at the width both sides fit in
  still joins the others of the value: a NaN test narrowed to `0x7f800000 <u trunc<31>(x)`
  combines with the float comparisons of `x` as before (`ja` after `ucomiss` is
  `fp.lt.f32(y, x)`).

On that corpus, with the pass the results have 25.2 percent fewer DAG nodes than without it
(5,262,215 against 7,032,940): 10.5 percent fewer on the local windows, 27.1 percent on the
deep ones. 37,427 of the 58,530 results are smaller and 953 larger (by 3 nodes at the median,
39 at most, 4,240 together against 1,774,965 saved): where the pass leaves a shape the other
passes do less with than with the one it replaced. Among those looked at: products of an XOR
in limbs by a constant, XORs of three or more values computed in different orders, and
values chosen limb by limb between a constant and a register, none of which it reads whole.
24 of the 123 that ran out of budget now finish, and 34 others now run out (29 on the MBA
service's steps), each with a smaller result than it had. Simplifying a sample of 3,000 of
them takes about a third longer with the pass (1.28 and 1.37 times the processor time, two
runs side by side on a loaded machine). In a run of the corpus with a check added for the
purpose, every replacement of a node was compared with the node at the engine's verification
points: 582,393 replacements, no difference.

Found by looking for inputs that break the engine and the provers: random DAGs over a few
narrow symbols at widths from 1 to 512 bits, every result, every fact and every answer of the
provers checked at every assignment of the symbols; the same with symbols as wide as the
expression and the native prover looking for a point between the samples; expressions 100 000
levels deep and ladders of shared levels through every public operation; and the fuzz targets,
half an hour each. No wrong result, fact or answer in 4 000 000 cases under five strategies
and 48 of random phases. What did break:

- **A result that changed again.** A pass tries several candidates at a node, and one declined
  only because a part of the node has another user is declined for now, not for good: the
  other user may go. The linear, xor, bitwise and compares passes and the MBA phase kept that
  of their last candidate only, so a node whose first candidate was declined for sharing was
  remembered as final, and once the other user was gone it stayed as written, in that context
  only: `sext<32>(b) + 0x80000000 ^ 0x80000000` beside another use of the sum. Of 24 000
  random expressions, the results of four changed again when simplified in a fresh context
  (under each of the standard, decompile and deobfuscate strategies); of 1 660 000 after the
  change, none.
- **Deep chains of shifts.** Under `(e << k) | s` nested thousands of times only the last
  levels reach the result, and the demanded-bits pass drops the rest. The walk is operands
  first, so each level was simplified under the mask of the level above it, a window of
  levels rebuilt and walked again at every one, before the walk reached the top: 3000 levels
  took 6.4 s and built 126 655 nodes, 12 000 took 27 s, each `Completed`. A node 64 levels
  or more above its leaves that observes an operand through a mask is now asked before its
  operands are walked, and the levels out of its reach never are: 53 ms and 63 nodes, and
  0.45 s at 12 000 levels. One question covers the nodes it read, so a deep expression with
  nothing to drop is asked once per stretch of it.
- **Questions of many symbols** (`prove::valid`, `prove::equal`). The symbols of a question,
  and of its counterexample, were listed and looked up by a search of the list per symbol:
  a question of 64 000 symbols that simplification had already decided took 12 s to answer,
  one of 200 000 over two minutes. 0.13 s and 0.38 s.
- **A panic in the MBA service at 128 bits.** A coefficient that is the sign bit of a 128-bit
  word is `i128::MIN` as a signed number, and its `abs` overflows: a panic where overflow is
  checked (debug builds), and elsewhere a negative size taken for a small one. 9 of 4 000 000
  random cases reached it, all at 128 bits or more with the native MBA solver; their results
  in a release build were right.

Slow questions from walks over an obfuscated driver (140 of them, each a quarter of a second or
more): roots left at two thousand nodes with the budget gone, and equalities too large to blast.
The causes found so far, none specific to those expressions.

- **A sweep reads what an earlier one found.** The opaque-constant sweep ran once per root and
  once per side of every case it split, and asked about the nodes they share each time, so a
  call over a few roots with a common core spent its pass work on the same questions. What a
  sweep finds for a node (the node itself where it finds nothing) is now kept for the call, and
  a later sweep reads it.
- **One certificate cannot take the whole budget.** The MBA gate's exact evidence was metered
  only by what the call had left, so a single candidate whose compositional test ran long left
  nothing for the phases after it. A certificate now gets half the call's pass work at most
  (and never less than a direct test of the pair costs), and stops as undecided beyond it.
- **A change of variable.** The certificates read an arithmetic node under a bitwise operator
  as an atom, independent of the variable inside it, so an identity that holds only because
  two atoms are related through that variable was not one to them: with `t = (x ^ c) + k`,
  `(−1 − k) − (x ^ c)` is `~t`, and `(x ^ c)·d` is `(t − k)·d`. Where such an atom is a chain of
  invertible links over one variable (`^ c`, `+ c`, `c −`, `· odd`, `−`, `~`), the question is
  now also asked over the atom in the variable's place, the variable its inverse; a
  counterexample there is mapped back. A side that differs at one input of `2^64`
  (`x + (1 − ((d | −d) >> 63))` with `d = x·k₁ ^ k₂`) is refuted with that input. The
  compositional test also tries each class's bitwise representative for its minimal atoms.
- **The prover simplifies with the opaque-constant sweep.** `Config::simplify` ran the
  deobfuscation strategy without it, so a question whose constants were hidden behind a
  comparison's mask was blasted with its multipliers and came back `TooLarge`. It now runs
  with the sweep.
- **The sweep runs again between rounds**, over what the phases left: a constant that shows
  only once a round has simplified what it reads was never asked about.
- **Nodes the samples relate are asked to be related.** A varying node whose samples are an
  earlier node's up to a constant (`rep + d`, `d − rep`, `rep ^ d`) is asked to be that,
  exactly, and written so where proved.
- **An atom and its offset are one variable.** A fragment that reads both `t` and `k − t` (or
  `t + k`, `k − (−t)`, `t·−1 + k`) lowered them as two independent atoms; the lowering now
  writes the operand through the atom (`t = k − a`), so identities that hold through the pair
  are ones the solver and the certificates see.
- **A fragment the solver declined for its size is not asked again from above.** Every node
  over a root answered "too many atoms" was asked in turn, each lowering the same fragment
  (27 questions of 820 nodes, 310,000 steps each, in one call); such roots are remembered for
  the call and a fragment containing one is skipped.
- **A bottleneck is enumerated over the values it can take.** The sweep's exhaustive check,
  when it enumerates a narrow node instead of the symbols, took every value of the node's
  demanded bits and called a mismatch a refutation, though the node may never take that
  value. It now enumerates only the bits not known of the node, and a mismatch there leaves
  the candidate to the readings. A candidate its demanded-bits form leaves open is also asked
  as written.
- **A subtraction that borrows nothing is a xor.** `c − t` with `t`'s bits all among `c`'s
  (`0xff − (x & 0x0f)`) was arithmetic under a bitwise operator, an atom to the bitwise and
  xor passes and to the certificates. The rule `sub_within` writes it `t ^ c`; the linear pass
  reads `c ^ t` with `t ⊆ c` back as the difference, so no cancellation through a sum is
  lost; the certificates read sums and differences of bitwise terms that can carry or borrow
  nothing as `|` and `^` before any test; and the bitwise pass writes a function of one atom
  and any number of constants as `(x & a) ^ b`, from its values at 0 and at all ones.
- **What was asked and kept is not asked from above.** A fragment whose answer would not make
  the DAG smaller, or was not proved, or took the solver four thousand steps to find nothing
  simpler, or ran it out of steps, is remembered for the call as the ones declined for size
  were, and a fragment that holds one is not asked (five fragments of 110 to 197 nodes over
  one such core, 2.5 million steps and no rewrite, in one call). In the sweep, a candidate
  whose readings decided nothing is an atom to the readings of every candidate above it, and
  the readings of one candidate end at the first whose certificate takes most of its share
  and leaves the question open.
- **One question to the solver takes a share of the call's steps.** The solver's own limit is
  a million steps whatever the call has: in a call of two million, one question that ran out
  took half of them and the rounds after it had none. A question now gets a quarter of the
  call's solver steps at most, and one that ran out is not asked again in the call with no
  more of them. No answer committed in the 140 questions took more than that.

How long those questions take, on the same 140: what follows cut their total CPU time to a
fifth (86 s to 17 s, run back to back on a loaded machine, each question in its own process
with the engine's tables already built). The median question went from 600 ms to 120 ms, and
of the 128 that took a quarter of a second or more, five still do. More of them are
simplified further than before: 19,164 nodes left over the 44 `forms_simplify` roots where
there were 22,701, 23 of the 47 `engine` roots folded to a constant where 16 were, 10 of the
27 equalities proved and 13 refuted where 5 and 10 were, none of the 43 prover questions too
large to blast where 4 were.

- **The sweep keeps the inputs its enumerations miss at.** An enumeration that ends where the
  candidate is not its constant now keeps that input for the call, and every later candidate
  and related pair is evaluated there before anything else is asked of it. An obfuscator
  builds one value from another, and a chain of them that are constant but for one value of a
  16-bit field was enumerated up to that value at every link: of 6.6 billion node evaluations
  spent in enumerations that ended in a miss, all but five million repeated a point an
  earlier candidate had already missed at.
- **An enumeration evaluates its points a block at a time.** The word program ran once per
  point, with a table lookup per input and an operator dispatch per node; it now runs once
  per block of up to 1,024 points, one loop per instruction over its operands' lanes, with
  constants folded into the instructions. The walk that finds which symbol bits reach a
  candidate is one pass down from it over a bitmap, stops as soon as more than sixteen bits
  reach it with no node left that could be a bottleneck, and reuses its buffers across calls.
  Same answers; a point is charged an eighth of what it was, since the same enumerations take
  a twentieth of the time (charged at the old rate, enumerations of a millisecond were
  declined for their cost, and six of the 140 questions ran out of steps a third of the way
  from where they now finish).
- **A certificate costs half what it did**, with the same verdicts, counterexamples and
  charges. What it charges for, the node evaluations, was under a tenth of its time; the
  rest was bookkeeping nothing charged. The refutation sample's constant pool was built
  from every constant and then cut to 32 (now it stops when full); the compositional test
  rebuilt the two skeletons of a pair for each of its five policies (75,000 of 136,000
  comparisons repeated a pair an earlier policy had built: now compared from what was
  found, with the same charges); its node tables were hash maps keyed by whole nodes and
  rehashed with a mixer chain per word; the sample was cloned and its rows hashed to group
  nodes; sums were read as bitwise through wide values at 64 bits. The sample's
  seed-independent points are compared before the seed is hashed, which is where all but
  five of 13,621 sample refutations are found.
- **The normal-form solver takes the same steps in 58% of the time**, with the same answer
  and the same step count for every one of 9,742 recorded questions. A fifth of its time
  outside its certificates was the allocator and a quarter touched tree maps: monomials now
  hold their factors in place and a polynomial's terms are a sorted vector up to 64;
  sums merge, and scaling and the reductions work in place; a candidate rendering is
  walked, costed and finished without allocating, and its nodes are interned through a
  small index; coefficient arithmetic takes one machine word up to 64 bits; the corner sums
  of a bitwise function take a word each; a linear form is expanded once for its three
  decompositions; the synthesis table's per-width indexes are built once per process behind
  a cheap hash.
- **The sweep's reductions share what they find.** Every candidate is first taken on the bits
  its users read (`demanded::reduced`), and each call walked the whole of what the calls
  below it had walked. What one finds for a node under a mask is kept for the call, up to
  where the visit cap cut a walk short.
- **One value under several masks stays one value.** Those reductions replaced a sum's
  constant by its residue on the bits read, so `t + k` under `& 0xff` and under `& 0xffff`
  became two sums, each an atom of its own to a certificate, and what cancels through
  `t + k` was gone. For a pair the samples relate by a sum or a difference the constant now
  stays as it is: the first one added to that operand in the call that agrees with it on the
  bits read. (A pair related by a xor is still read with the residues, which is the form the
  bitwise tests decide there.)
- **A node is not asked to be related to what its operand was not.** Where `f(a)` could not
  be proved to be `rep + d`, `g(f(a))` was asked next, about the same `rep`, and failed for
  the same reason at the cost of a full certificate; the skip counts toward the sweep's cap
  on pairs left open. Of 3,230 such questions in the 140, five had been proved.
- **A block's cases are read at the samples first.** `cases_fold` built both sides of a
  condition and swept each before it looked at whether the block is constant on either: now
  the samples that fall on each side say so first, the first side is proved before the
  second is swept, and a side an earlier sweep examined is not walked again (4,364 side
  sweeps became 881, for four more folds). A sum with a node cut off is not asked of the
  solver when it holds a block the solver declined at the same cut (1,066 questions, none of
  which had an answer), and an atom a block is seen to read at one input is not tried as
  noise with the 64-point sample.
- **A fragment is lowered once where two readings are the same.** A fragment that is
  semi-linear as it is has one lowering for the whole and the semi-linear reading, and one
  per cut; the walk and the build keep their node tables in a dense map emptied in constant
  time instead of a hash map built per reading.
- **What the sweep changes under assumptions is reported as relying on them.** The sweep
  folds on facts (known bits, the values a bottleneck can take) without recording which
  constraints they came from, and a root it changed reported an empty
  `RootOutcome::relies_on`: `zext(x == k) + 5 + …` folded to `5` under the assumption
  `x != k` and said it held everywhere. Such a root now reports every constraint of the run.

How far those questions fold, on the same 140. After what follows, 46 of the 47 `engine`
roots are a constant (23 before; the last one is asked with an eighth of the others' fuel and
folds with half of theirs), the 44 `forms_simplify` roots are left at 7,422 nodes together
(19,164) and the five `simplify` roots at 685 (1,186), all 16 `valid_under` questions are
proved (3) and every one of the 27 equalities is decided, 14 proved and 13 refuted (10 and
13, four out of budget). The questions also take less time than before these changes: 15%
less CPU over the set run back to back, with the limb passes above in the strategy.

- **A question narrower than its operands is read without its casts.** `trunc<32>(x ^ y) +
  2·trunc<32>(x & y) − trunc<32>(x) − trunc<32>(y)` over 64-bit `x` and `y` left the normal
  form and the certificates with four casts for atoms. The low bits of `+ − · ~ & | ^` and of
  a left shift depend on the low bits of their operands, so such a question is computed at
  its own width over the low bits of each wide variable, and those are variables to the
  tests. (A right shift of a wider node still reads bits the question's width lacks.)
- **A sum under an extension is asked at its own width.** `zext<64>(s) + k` with `s` a 32-bit
  MBA was one question at 64 bits, where `s` is read through a mask and is a constant only
  modulo `2^32`; the sum inside was taken as covered by it and never asked. Only a truncation
  is transparent to a chain of sums now.
- **Rotations keep complements and constants outside.** `rotl(~x, s)` is `~rotl(x, s)` (and
  `rotr` likewise), and a constant under a rotation by a constant is rotated once:
  `rotl(x ^ c, s)`, `rotl(x & c, s)`, `rotl(x | c, s)`. Nested rotation layers with a mask or
  a key between them then meet (`rotl(rotl(rotl(p, 46) ^ k, 26) & m, 56)` is `p & m'`). The
  rule `not_rotl_not` is gone, shadowed by `rotl_not`. `(x | c) − c` written as an addition
  is `x & ~c` (`add_or_const`), also where `x | c` has other readers. A sum shifted back,
  `((x << c) + k) >>u c`, is `(x + (k >>u c)) & m` (`lshr_add_shl`): the constant's low bits
  carry nothing into what is kept.
- **Slices of one rotation are read as that rotation.** A fragment whose parts are bits of
  one value under shifts, rotations, masks and complements (`t << 13`, `t >>u 51`, `~(t << 13)
  & m`, products of those by `2^k·c`) is asked again with each part written over the
  rotation most of them read, `(rotl(t, r) & mask) ^ flip`: one atom where the two halves of
  a rotation were two. The value a part is a slice of is read too, where it is a node of the
  fragment's own. With or without the noise forms.
- **A fragment is asked again with a shared value cut off as one atom**, for the two values
  most of its terms read: an obfuscator writes `Σ cᵢ·fᵢ(t)` over a `t` that is a fragment of
  its own, and the whole question is over what `t` is made of. These questions and the
  slices one take a small share of the solver's steps and of the certificates' work.
- **A sum whose terms share a factor is asked without it.** `(f·a)·t₁ − (f·b)·t₂ + …`, an
  MBA scaled by a value with each coefficient spelled as a product of its own with it, is a
  polynomial over what `f` is made of; the sum with `f` taken out is linear over the atoms of
  the terms. The products are read through negations, constants and shared subproducts.
- **The sweep enumerates a cut of several places.** Where more than sixteen bits of the
  symbols reach a candidate and no one node on every path decides it, the enumeration is over
  several nodes that together cut the paths, as near the symbols as ten bits allow, each over
  the values the bits known of it leave. A shift count taken from the low bits of a product
  of a value that two unrelated conditions each give one bit of is constant, and is now seen
  to be. A truncation the samples hold constant is asked about (for its known bits and the
  enumeration, as a one-bit node is), and a `select` passes the bits read of it to its arms.
- **Sides that are a constant plus a multiple of each variable bit are compared as that.** A
  sum of products of bitwise functions of one value by constants is such a form whatever its
  carries, and under a mask the tests took it for an atom: the answer `rotl(x, 13) ^ k` to a
  150-node rotation MBA ending in a mask was found and not proved. The forms go through sums,
  products by constants and shifts, and through `& | ^` where each bit of an operand is a
  constant, a variable bit or its complement; two forms are one function exactly when they
  are the same, so the comparison decides (with an input where they differ), and it runs
  before the tests that evaluate points. A form with carries under a constant mask is read
  by the mask's fields where its low bits are a form too (`(x & m)·c & −256`: the product's
  low byte depends on the few bits of `x` the mask keeps there).
- **Sides that read a value the same way are compared without the reading.** `(s >> 8) & 9`
  against `(t >> 8) & 9` holds exactly when `s` and `t` agree on bits 8 and 11, and without
  the right shift each side is a function of the low bits of its variables, which the
  bit-serial test follows through every carry. From the roots inward, the steps both sides
  share (a right shift, `& | ^` with one constant, a complement, a cast) are taken off when a
  right shift is among them. That test also reads a variable wider than the sides through
  its truncation.
- **One leaf under masks is a symbol to the symbolic comparison.** A bitwise function of one
  leaf and constants is `f(0)` plus the leaf under the bits it sets less the leaf under the
  bits it clears, whatever spelled it: `m − (~t & m)` and `t & m` are one polynomial. A
  product of such a term with another value was proved by a sparse test over two variables,
  1.6 million units of pass work for a 20-node question, four times in one call that then ran
  out.
- **A sum that spells another is asked a group at a time.** `A + p·q + B − (A & B)` with `A`
  a sum of products is `(A | B) + p·q`, but the whole is a polynomial over everything `A` is
  made of. Where the whole is no simpler, the terms that share an atom are asked together
  with the spelled sums still atoms, as an identity beside unrelated terms already was.
- **A sum with a constant whose carries are all known is a xor**, under a mask: `t + k` (or
  `k − t`) differs from `t` in fixed bits where every carry on the bits read is known from
  the bits known of `t`. One value written twice, once through such a sum, was two
  unrelated atoms to the MBA phase. Only for a sum with no other reader (one read under
  several masks is one value to all of them), and taken at the same size.
- **A root is split on the condition its selects test most**, with the noise forms, when each
  side is one value at every sample point. At random inputs a condition like `x != y` holds
  every time: a root that is one constant where it holds and another where it does not looked
  like the first, and no proof of that exists. Each side is read at the same inputs with the
  condition put in, and the root becomes a `select` of the two, which the phases fold.
- **The words pass asks once the other phases have settled.** It asked in every round, and
  what it wrote of a root the MBA phase and the opaque-constant sweep were still folding took
  the forms their questions read: on these 140 questions (no limb arithmetic in them) seven
  of the 47 constants and four of the 16 proofs were lost, at half again the time. It now
  asks in a round over a root the other phases left as it was, and in the one round past the
  strategy's last; what it writes goes back to them.
- **Cheap questions first.** A node's own question to the solver takes 65,536 steps while
  the rounds have other questions to ask, and its quarter of the call's steps only in a round
  after one that changed nothing (over the same root, without the sweeps; or in one round
  past the strategy's last where the rounds were still changing it). Of the answers committed
  in the 140 questions, 570 of 601 took fewer steps than that; the questions the solver runs
  out of steps on stand among them in no order, and a few of those, asked at the full share
  where they stood, took a call's steps before the rest of it was asked anything. A question
  cut short this way is not a budget running out: the root ends `Completed` when the deeper
  round answers it.
- **A sum too large to ask is taken apart first.** A sum with more variables than a question
  takes was skipped, and its terms were then asked one at a time (in one measured call the
  terms of one linear MBA were most of 33 declined questions that took 785,000 of its two
  million steps). Such a sum is now read by its groups of terms before its operands are
  walked, and a fragment too large to lower whole is asked with the arithmetic under its
  bitwise operators as atoms (`Σ cᵢ·fᵢ(A, B, …)` over sums and products `A`, `B` is linear
  over them).
- **A factor is taken out of the terms that share it.** The factoring above needed every term
  of the sum to have the factor. The terms with the factor most of them have are now written
  as the factor times their sum without it, beside the rest: `y + (f·a)·t₁ − (f·b)·t₂`.
- **Selects on one condition that read one value are split together.** `(v | k) + (v & k)` is
  `v + k`, and with `v` a select and `v & k` written into its sides the two terms read two
  selects no test relates. An operation over two selects on one condition whose sides read a
  common value is `select(c, E1, E0)` when the MBA phase simplifies each side. A side, and a
  fragment whose own answer was not smaller for what it shares, is asked also with the values
  its nodes share through casts cut off (`(zext(t) | k) + zext(t & k)` is `zext(t) + k` over
  `t`, where the whole question's answer writes `t` another way).
- **An equality with an even multiple is an equality of low bits.** The invert pass solved
  `x·c == k` for an odd `c`. With `c = 2^t·d` the product's low `t` bits are zero, so the
  comparison is false when `k`'s are not, and otherwise it is `trunc<w−t>(x) == (k >> t)·d⁻¹`
  (`x << t == k` likewise): `x·0x1a8bfbc8 == 392` at 32 bits is `trunc<29>(x) == 0xde0c079`.
- **A comparison of some bits of a value is written over the value.** `(y | m) == k` reads the
  bits of `y` outside `m` (and is false when `k` lacks a bit of `m`), and the bits of a slice
  or a zero extension are bits of its operand: `(extract<lo, n>(x) | m) == k` and
  `(extract<lo, n>(x) & c) == k` are `(x & c') == k'`, or `extract<lo', n'>(x) == k'` where
  the bits are one run. A dispatcher compares one state with its cases through several
  multipliers and several widths; with this and the entry above, a measured one of 265 nodes
  whose seven-way tables each spelled their conditions differently is 199 nodes over the
  same eight conditions on three bits of one value.
- **Bits of one value added up are a population count.** A sum whose terms each count bits
  of one value with one coefficient (`extract<i, 1>(x)` extended, `x & 1`, `(x >>u i) & 1`,
  the top bit shifted down, a `popcnt` of a field of `x`) is `c·popcnt(x & m)`, the bits a
  slice of `x` where they are one run; three bits or more, no bit twice. The operand of a
  parity flag is spelled a bit at a time, `(b >>u 1 & 1) + (b & 1) + …` over a byte `b`, and
  its low bit was a sum of eight slices at one bit: it is `trunc<1>(popcnt(trunc<8>(x)))`,
  and the condition of every select in 41 of the 44 `forms_simplify` questions.
- **A flag kept in a byte is its bit.** `x == 1`, `x != 1`, `x == 0` and `x != 0` for an `x`
  whose other bits the facts know zero are the low bit of `x` or its complement, with the
  truncation pushed into `x`, where that is a smaller tree: `((zext<8>(a) & zext<8>(b)) ^ 1) &
  zext<8>(c) != 1`, three conditions combined as bytes and tested, is `~(~(a & b) & c)`. And a
  sign test of a value rotated or shifted left by a constant is the bit that lands on top
  (`rotl(x, 56) <s 0`, the sign of the low byte, is `extract<7, 1>(x)`), which then meets the
  other readings of that bit.
- **Extensions and slices written twice.** A mask inside the narrower of two zero extensions
  is taken at the operand's width, `zext<64>(~zext<32>(e) & 5)` as `zext<64>(~e & 5)`
  (`zext_and_zext`, `zext_and_not_zext`), and a slice and the low bit of one value, extended
  and concatenated back where they were, are the value under a mask
  (`concat_slice_and_bit_in_place`).
- **Rotations by a variable count.** `(x << s) | (x >>u (W − s))` with `s` proved below the
  width is `rotl(x, s)` (`variable_shift_rotate_left`, and `_right`): at zero the shift by the
  whole width gives nothing. And where the two counts are spelled apart, `x << a | x >>u b` is
  `rotl(x, a)` when both are below the width and the low bits of `a + b` are zero as a sum of
  multiples of what the counts are made of (`trunc<6>(u·83)` and `trunc<6>(u·109)`, extended,
  at 64 bits: `u·192` has no low six bits).
- **Two complements around a slice are none.** `~extract<k, n>(~x)` is `extract<k, n>(x)`
  (`not_extract_not`, `not_trunc_not`), and a select on a bit of a complement is the select
  on the bit with its sides swapped (`select_bit_of_not`, `select_low_bit_of_not`). (Moving
  every complement out of a slice instead left the sweep 3,400 nodes short on the same
  questions: its candidates are truncations.)
- **A select under the opposite comparison keeps one side.** `select(a != b, x, select(a == b,
  y, z))` is `select(a != b, x, y)`, and likewise in the chosen arm and under `==`
  (`select_then_ne_eq`, `select_else_ne_eq`, `select_then_eq_ne`, `select_else_eq_ne`); only
  the same condition repeated was read so.

## 0.27.0

Idioms of compiled and lifted code that every preset left as written, reported against 0.26.0.
`tests/lifter_idioms.rs` checks each under every preset that runs what it needs.

- **Bit counts.** `popcnt(x) + popcnt(~x)` is the width, `popcnt(x) == 0` is `x == 0` (and `!=`,
  `== W` as all ones, `ctz` or `clz` equal to the width as zero), and the count of the bits
  below the lowest set one, however its mask is spelled (`(x & -x) - 1`, `~x & (x - 1)`,
  `~(x | -x)`), is `ctz(x)`. The SWAR population count is `popcnt(x)`: the carries pass reads a
  right shift or a mask whose region is one value through arithmetic and constant shifts,
  compares it at its 64 points with `popcnt`, `ctz` and `clz` of that value, and proves the
  one that agrees (22 ms at 32 bits); so counted after a smear or a trailing mask, the same
  shape is `clz(x)` or `ctz(x)`. `ctz(x) <u 3` stays: `(x & 7) != 0` is a larger tree, and the
  engine only rewrites to smaller ones.
- **Sign and overflow flags.** A sign test beside a sign bit taken as a slice
  (`(x <s 0) ^ extract<W-1, 1>(y)`, and with `!=`, `==`, `&`, `|`) is one test of the
  combination, so `SF ^ OF` of a subtraction is `x <s y` however each flag is spelled. The
  branch-free absolute value (`((x >>s W-1) ^ x) - (x >>s W-1)`, or with the mask added first)
  is `abs(x)`. `x + y <u x` is `~x <u y`, the carry-out test the facts decide (and `false` at
  once when both are below half the range, for `Strategy::compile`'s single round).
- **Selects.** A one-bit `((x ^ y) & c) ^ y` (the bitwise pass's form of `(c & x) | (~c & y)`)
  is `select(c, x, y)`; both arms combined with one term by `&`, `|`, `*`, `-` or a shift
  factor it out (`select(c, x & y, x & z)` is `x & select(c, y, z)`); and an arm one more or
  one less than the other is the condition added (`select(c, x + 1, x)` is `x + zext(c)`).
- **Declared facts.** A sign extension of a value whose sign bit is clear is its zero
  extension, and through a truncation that drops only bits known zero, an equality with a
  constant or another such truncation is one of the whole values: with `x` and `y` declared
  below 256, `sext<64>(trunc<32>(x)) == x` is true and `trunc<8>(x) == 3` is `x == 3`.
- **Arithmetic in halves.** `add`/`adc` and `sub`/`sbb` over separate halves
  (`concat(a1 + b1 + zext(carry), a0 + b0)`) are the sum or difference of the concatenations,
  and over the halves of two values (the low halves' sum already one truncation) are `x + y`
  and `x - y`: by rules now, in every preset, in microseconds where the carries pass's proof
  took 4 and 17 ms.
- **Double-word shifts.** A word-sized window of two words, `concat(trunc<A>(h),
  extract<A, W-A>(l))` (the shuffle pass's form of `shld`), is `extract<A, W>(concat(h, l))`.
- **`Strategy::decompile()`**, for a decompiler's everyday output: the standard strategy plus
  divisions by constants, carry networks and bit counts, and bit shuffles (byte swaps,
  rotations, double-word shifts), without the MBA passes. `bitwright simplify --decompile` and
  `lift --decompile`, and the Python preset `"decompile"`.
- The rule `halves_sum_no_overflow` is gone: `x + y <u x` as a carry-out test decides it.
- **SAT sweeping** (`prove::Config::sweeping`, on by default), decided per question. While a
  question is prepared, its circuit is simulated on word-level assignments (boundary values,
  runs of ones, and values related to the word before, such as `-x` beside `x`, so long carries
  occur); nodes that agree everywhere, or disagree everywhere, are candidates. The simulation
  then decides whether to sweep: for an equality, it counts the candidate classes that join a
  node only one side has to a node only the other has, and sweeps when there are at least 4,
  and one for every 10 nodes private to a side. Otherwise the question is searched exactly as
  it would be unswept, for the cost of the simulation (`Stats::sweeping.skipped`). When it
  sweeps, the candidates are proved equivalent one pair at a time from the inputs up, by a
  solver holding only the circuit's clauses, under assumptions (`a ∧ ¬b`, then `¬a ∧ b`); a
  pair told apart refines the simulation with its counterexample and that point's neighbours.
  The equivalences go to the search as clauses, and with a certificate the sweep's own lemmas
  are logged first, so the certificate still checks independently (the sweep's solver holds a
  subset of the question's clauses, in the same variables). The sweep takes at most half of
  the configured limits, before any search, so a question solved in steps is swept as one
  solved at once; it counts in the question's totals and is reported in `Stats::sweeping`
  (`ran`, `skipped`, `crossings`, and the pairs merged, separated and undecided). Measured in
  propagations, without and with: the 64-bit prefix adder against `x + y` 0.54 M and 0.29 M
  (54 ms and 18 ms), the 64-bit MBA rewriting of `x - y` 7.6 M and 0.56 M (2.1 s and 44 ms),
  the 32-bit SWAR population count against `popcnt` 148 k and 24 k. Skipped, and unchanged:
  the shift-and-xor addition loop against `x + y`, whose carries no single node holds (at 64
  bits a sweep would save a quarter of 28.7 M, at 16 bits it costs a quarter more), products,
  and wrong adders. The carries pass's proofs over the networks it tests take 46 % less pass
  work. The solver gains a search under assumptions that leaves the clauses satisfiable when
  the assumptions are refuted.

Defects in the driver and the normal forms, found reading the engine:

- **A doubling is `a << 1`.** The builder writes `a + a` as `a << 1`, as every other power of
  two is a shift, so what reads shifts reads doublings: `(x >>u 1) + (x >>u 1)` is `x & -2`,
  and with `+ (x & 1)` it is `x`. The linear pass emits a coefficient of 2 as a shift (it wrote
  `a + a`), and the rules `and_double_const`, `or_double_const` and `xor_double_const` are gone
  (the `shl` rules beside them cover the one form). Expressions that printed `x + x` print
  `x << 1`, lifted ones included.
- **Constants in the commit rule.** A rewrite is committed when it frees more nodes than it
  builds, and a node with a use outside the rewritten region is not freed. A constant's uses
  outside are no longer counted: whether an unrelated expression happens to hold the same
  constant decided rewrites it has nothing to do with.
- **Rule results declined for sharing are decided again.** A rule guarded by `one_use` that
  declined while its operand had another use was remembered as declined for the call; it is
  asked again once a later phase has dropped the other use.
- **Rotations written as concatenations.** `concat(trunc<A>(x), extract<A, W-A>(x))`, the two
  parts of one word swapped, is `rotr(x, A)` (the rule `concat_rotate`); it stayed a
  concatenation.
- **Right shifts in sums.** The linear pass reads `k·2^j·(x >>u j)` beside the low field
  `x & (2^j − 1)` of the same `x` as `k·x − k·(x & (2^j − 1))`, so the two parts of a value
  taken apart come together: `(x >>u 3) * 24 + (x & 7) * 3` is `x * 3`.
- **Quotients under masks.** `(x >>u c) << c` becomes a mask only when the shift has no other
  use (the rule `lshr_shl`): the mask saved nothing, and hid the quotient `q` of `q·8 + q·2`
  from the division pass. That pass reads a multiply-high, or a shift or slice of one, under a
  mask `−2^m` as the quotient shifted left: `umulhi(x, 0xcccccccd) & -32` is `udiv(x, 40) << 5`,
  and the compiler's `x % 10`, `x - ((q << 3) + (q << 1))` with
  `q = umulhi(x, 0xcccccccd) >>u 3`, is `urem(x, 10)`.
- **Chains in one order.** A product of three or more values, and a chain of `&` or of `|`, is
  written with its operands in the context's order, joined left to right (up to 256 operands),
  so it is one node however it was parenthesized and ordered: `a*b*c - c*b*a` is 0 wherever the
  linear pass runs, and `(v0 & … & v6) ^ (v6 & … & v0)` wherever the bitwise pass does, at 40
  operands as at 3. The product was 0 only through the MBA service, up to 8 atoms; the `&` and
  `|` chains only up to the six atoms a truth table reads. In a chain of `&` or `|` an operand
  counts once, and beside its complement it decides the chain. A chain found in order is
  remembered for the call, so are its parts, and so is one over 256 operands (every chain over
  it is, too): two 256-factor products in opposite orders take 0.30 M units of pass work.
- **Uses of a node that took another's place.** The commit rule counted a node's uses as the
  walk had rebuilt them so far: a node rebuilt over a rewrite below it had no user until its
  users were rebuilt in turn, so one that several of them share looked like one a rewrite at the
  first could free. It now counts the uses of the node it replaced until those users are
  rebuilt over it, and is counted as live though the context held it before the call. With
  `y` reducing to `p`, `(x & (y & z)) ^ popcnt(y & z)` keeps `x & (p & z)` over the shared
  `p & z`; putting that chain in order (`p & x & z`) built a second copy of it. Over 400 random
  DAGs of 200 nodes, results are smaller in 70 and larger in 7 with one root, and with four
  roots over one shared term 43 results are larger than their input, from 73.
- **Long sums and products in the linear pass's factoring.** `a·x + a·y` is factored over a
  sum of up to 16 terms of up to 8 factors, and the pass read a sum's terms and a term's
  factors by recursion to the bottom of the chain before that bound applied, at every node of
  it. A left-nested sum of 80 000 terms, or `v0 * … * v79999 + x`, overflowed a 2 MiB thread
  stack (the process aborts), and below that a sum cost the square of its length outside any
  budget: 32 000 terms took 1.5 s and 128 000 took 29 s, each `Completed`. Both are read from
  the top now, in at most 32 steps: 140 ms and 0.58 s, as a chain of subtractions takes, and
  100 000 terms or factors on that stack. Results are the same.
- **Conditions merged in one spelling, whatever the order of construction.** Where two terms
  of a sum read one condition (`zext(c) - zext(~c)`), the linear pass merged them over the
  spelling of the first term, and a form's terms are in the order their nodes were built:
  `zext<8>(x <=s a) - zext<8>(a <s x)` with `a = udiv(1, x)` stayed as written when parsed and
  became `1 - (zext<8>(a <s x) << 1)` once imported into another context
  (`Context::import` builds operands right to left), so a result could change again when
  simplified there. The spelling kept is now the one that is no complement, then the first in
  the context's order. Of 4 000 000 random inputs per preset, three changed again in a fresh
  context, each through this; none does now.
- **Sums and xors over 64 terms.** A form of more than 64 terms is an atom of the forms over
  it, which keeps every node's form small, and so nothing cancelled through it:
  `(v0 + … + v69) - v0` was left as written, and so was the same sum minus itself in another
  order. Such a sum now keeps its whole form (its terms, with the long sums among its atoms
  taken apart in turn, up to 1024 terms), and a sum over it is read through it where a term of
  one operand is inside a long sum of the other: 74 terms less one are the other 73, 70 less
  the same 70 reversed are 0, and 200 less 100 of them are the other 100. The xor pass does the
  same for xors. A sum in which nothing meets is not taken apart (a search of the whole form
  for each term added), so a long sum of distinct terms costs what it did: 5000 terms take
  0.3 % more pass work. A sum of more than 1024 terms is an atom and no more, as before, and
  one with another use is not written out a second time.

The driver's accounting, from the same reading:

- **A quarantined pass stops.** A pass whose rewrite fails a width, verification or tripwire
  check is quarantined for the call, as a rule is. That was recorded, and only the MBA phase and
  the invert pass looked: the others went on rewriting. Every pass now stops, on every node and
  root of the call, and what it would have decided is not final.
- **Salvaging is charged.** A root a budget stops keeps the work of its stopped phase: the
  nodes above what the phase finished are rebuilt over it, by a walk of the root that nothing
  was charged for, once for every root after the stop. Reading a node the stopped phase had not
  reached is now a node visit (the ones it had reached are charged already), and a node the
  budget does not cover stays as it is. 48 roots over one shared sum of 1607 nodes, each
  stopped at its first rewrite, were 2749 node visits and are 79 501; with 8 roots' worth of
  visits, the roots after those are not read.
- **The other roots are counted once.** The commit rule's use counts of the other roots of a
  call are counted once per root and kept; every later phase run charged the count again as
  pass work, for a walk it did not make. A small root beside one of 2399 nodes took 55 980
  units and takes 48 767.
- **`Stats::rounds_capped` and `Stats::reruns_capped`.** A run that ended at
  `Strategy::max_rounds` with its last round still changing the root looked like one that had
  settled, and so did a call that stopped running roots again for what they share (three
  times) while they were still changing. Both are counted, in `Stats` and in a trace's `stats`
  line: the result is as valid as any, and simplifying it again may go further.

A wrong answer of `Context::prove`, in 0.26.0 too, which the heavy facts suite came to once
the doublings above had changed its random expressions:

- **Residues of values over 128 bits.** The residue predicates behind `Context::prove` compute
  with 128-bit values, and read an extension or a concatenation wider than that as an
  operation, because its operands fit. Its value was cut to 128 bits, so `sext<257>(x)` of a
  negative `x` was a large positive number, and `sext<257>(t * t) <=s sext<257>(x)` with
  `t = sext<33>(x)` was proved true (at `x = 2` it is `4 <=s 2`). Such a node is a leaf to the
  residues now. Only questions about expressions wider than 128 bits were answered so; the
  compares pass reads no such node.

## 0.26.0

Four ways to hide arithmetic at a width boundary, found by probing obfuscations that mix widths
(17, 20, 23, 34 bits inside 64-bit registers); none of them was specific to odd widths.

- **A constant read on a low prefix is its residue there.** The demanded-bits pass took a
  constant operand as it stood, so a multiplier that is an inverse modulo `2^17` and none at 64
  bits survived its mask: `(x * 43 * 0xbe83) & 0x1ffff` stayed `x * 0x200001 & 0x1ffff`.
  Under a low prefix of `k` bits, a constant is now replaced by its residue modulo `2^k`,
  extended with zeros or with its sign, whichever is the smaller in magnitude, and a factor that
  is −1 there negates: that example is `x & 0x1ffff`, and `(x * 0x3ffff) & 0x1ffff` is
  `-x & 0x1ffff`. A residue of 0 is left to the facts, so `Hooks::fold_known` still decides it.
- **An extract of a sum splits where the carry into it is decided.** The casts pass pushed
  `extract<lo, n>` through `+` and `−` above bit `lo` only when an operand's low `lo` bits were
  known zero. It now runs the carry from bit 0 up to `lo` over both operands' known bits (a bit
  known zero in both stops it, one known one in both makes one, a known carry passes a bit known
  to differ), so a lane of packed values with guard bits is read alone:
  `extract<21, 20>((x & 0x3ffffdffffefffff) + (y & 0x3ffffdffffefffff))` is
  `extract<21, 20>(x) + extract<21, 20>(y)`, and a decided borrow adds its `− 1`. A left shift
  that straddles a truncation is pushed as the operand's low bits shifted at the narrow width
  (`trunc<8>(zext<16>(a) << 3)` is `a << 3`).
- **A sum split at any boundary is recombined.** The carries pass read only `& | ^ ~` and
  constant left shifts. Below a `concat` it now also reads `+ − neg`, `extract`, `zext`, `sext`
  and `<u`, down to atoms of the `concat`'s width, fits the affine form and proves it as before:
  `x + y` added as 17 low bits at 18 bits and 47 high bits plus the low sum's top bit is
  `x + y` again, and so are a 23/41 split with the carry as `s <u trunc<23>(x)` and the same
  for differences and borrows; a split missing its carry, or reading it a bit too low, is
  refuted.
- **Equalities through permutation polynomials.** The pivot analysis took a product of two
  values that both vary as reading every bit at and below each output bit, with no pivots, so
  `2x² + x`, a bijection modulo every power of two, was not one to it. A product now reads `a`'s
  bits up to `k − tc` and `c`'s up to `k − ta` (`ta`, `tc` low bits known zero), a square
  `a·a` its bits below `k − ta` (and `a_ta` at `2ta`), and a factor known odd passes the other's
  pivot through; `a + a` and `a − ~a` are read as `a << 1` and `(a << 1) | 1`. So
  `2*x*x + x == 2*y*y + y`, `x*(2*x + 1) == …` and `4x³ + 2x² + 3x == …` are `x == y`,
  `2*x*x + x == 5` is `x == 72115` at 17 bits, and `x*x + x` (always even) is still refused.
  The invert pass also compares truncations at their own width when the full one decides
  nothing: `trunc<17>(2*x*x + x) == trunc<17>(2*y*y + y)` is `trunc<17>(x) == trunc<17>(y)`
  and `trunc<17>(x * 0x1234567 + 9) == 77` is `trunc<17>(x) == 110364`, committed only when the
  result is a smaller tree.
- **The demanded-bits pass no longer runs out of memory on shared chains.** Since 0.24.0 a
  phase run keeps, for every operand a step found nothing to simplify under a mask, the leaves
  its walk stopped at, and a later step copies them back. A range kept the copies its operands'
  hits had made, repeats included, and operands in a DAG share leaves, so on a ripple chain
  each level's range was the sum of its operands': 2^48 entries at 48 bits, a 16 GB
  allocation from `simplify` on a 48-bit adder written out, read through `<< 1` (the heavy
  test `carries_asks_a_region_past_its_caps_once` grew to 60 GB). Each range now keeps each
  leaf once; they are read as a set, so the boundaries the commit rule sees are the same.
  That run takes a second and 15 MB. A test outside the heavy set guards it, and the heavy
  test now asserts what changed in 0.24.0 as well: the demanded-bits pass rewrites that chain
  (146 nodes to 143), and the carries pass asks the rewritten chain once.
- **Tooling.** Scheduled `nightly-deep` runs were being cancelled at the job's 60-minute limit,
  near the end of its second step (the two take about 65 minutes), and on 8 November one
  failed at once on a 504 from the z3 release download. The job may now run two hours, and
  both solver downloads retry.

## 0.25.0

- **Orderings see through strictly monotone maps.** The invert pass cancelled and solved only
  equalities: a bijection does not preserve order. It now reads `<u`, `<=u`, `<s` and `<=s`
  through layers that are strictly monotone from an order of the inner value to an order of
  the node: `zext`, `sext` and `concat` always (`zext<32>(x) <s zext<32>(y)` is `x <u y`,
  `sext<32>(x) <s 5` is `x <s 5`), `~v` and `v ^ smin` always (`~x <u ~y` is `y <u x`,
  `(x ^ 0x80) <u (y ^ 0x80)` is `x <s y`), and `v + k`, `v - k`, `k - v`, `-v`, `v * k` and
  `v << s` where the facts keep the inner value on one piece of the wrapping operation
  (`x + 7 <u y + 7` is `x <u y` under `x <u 100` and `y <u 100`, and `x + 7 <u 50` is
  `x <u 43` there). Both sides are peeled layer by layer, the comparison moving to the order
  each layer is monotone from and swapping its sides for a decreasing one; against a constant
  the threshold is found by bisection over the inner value's range, or the comparison is
  decided. Like the rest of the pass, a rewrite replaces a comparison by one of proper
  subterms and a constant and relies on the constraints its facts used.
- **Comparisons of `select` trees are cancelled leaf by leaf.** A `select` passes what is
  observed about it, its order or its equality, to its arms, so the leaves of the trees on both
  sides of a comparison are peeled together through one common layer, injective for `==` and
  `!=`, strictly monotone for an ordering, a constant leaf standing for its exact preimage:
  `select(c, zext<16>(x), zext<16>(y)) <u zext<16>(z)` is `select(c, x, y) <u z`,
  `select(c, ~x, 5) <u ~z` is `z <u select(c, x, 0xfa)` and `select(c, x * 3, 7) == y * 3` is
  `select(c, x, 0xad) == y`; a minimum written out loses its casts in the condition too, in
  that comparison's own step. The design notes (§8.1, "Observations") set out how this, the
  equality cancellation and the demanded-bits pass are one idea with two kinds of
  representative.

## 0.24.0

- **Exhaustion certificates are scheduled in near-linear time.** `Exhaustion::check` simulates
  the goal's conjuncts cheapest cone first, and chose each round's conjunct by walking the
  unscheduled cone of every pending one with a fresh mark per node and a scan of the whole
  circuit: quadratic in the conjuncts times the circuit, serial, and below about 28 inputs
  most of the check (1.5 s of the 1.7 s a 43k-gate certificate over 24 inputs took). The
  walks now share stamped marks and are cut off at the round's best count, so a round costs
  about the pending conjuncts times that count (0.1 s there). The schedule is the same, so
  the simulation is unchanged.
- **`enumerate_values` stops at its limit.** It built every candidate of the known bits (up to
  2^20, a heap allocation each), filtered them by the ranges and threw the list away when more
  than `limit` were left. It now keeps admitted values as it goes and stops at the first past
  the limit; the same answer, at a bounded cost. The fact transfers over small value sets use
  the same enumeration.
- Tests: `value::tests::random_wide_widths_deep` (and the short `random_wide_widths`) run each
  width's samples in chunks across the available threads, each chunk on its own stream (the
  deep run takes 10 s of wall time on 20 threads, from 140); the test oracle `Canonical`
  indexes nodes by position instead of hashing them.

- **A register read through its low bits is a narrow variable to the MBA certificates.** The
  question's casts are taken out before the normal form and the certificates (`decast`), but a
  truncated register (`trunc<32>(x)`, or `x & 0xffffffff` after the rules) was left as the
  register behind masks, which put a question with products outside the fragment the
  polynomial certificates and the symbolic comparison decide: the solver found the answer to
  the lifter spelling of `c·(Z(A&B)·Z(A|B) + Z(A&~B)·Z(~A&B))` over `A = trunc<32>(x)` and
  the gate could not prove it, so the expression stayed as it was while its spelling over
  `a:32` was solved. Now, when the tests leave such a question open (and not for lack of
  budget), both sides are compared as polynomials over symbols with each root-width variable
  whose every reader demands the same low `n` bits (through truncations, masks and the
  operators whose low bits depend on low bits alone) as the atom `zext(trunc<n>(x))`, the
  masks to `n` bits over values known zero above `n` dropped: the question over 32-bit values,
  which the comparison reads. The solver's normal form keeps the registers, whose masks its
  bit classes read exactly. Results of the benchmark corpora are unchanged node for node; the
  lifter spelling above is solved like the narrow one.
- **The core passes read through extensions.** The linear-MBA, bitwise and linear passes took
  a `zext` or `sext` as an atom, so an MBA over extended narrow values was a sum of unrelated
  atoms to them (`zext(a ^ b) + 2·zext(a & b)` stayed, where `(a ^ b) + 2·(a & b)` is `a + b`)
  and only the MBA service, at normal-form cost, recovered it. Now the linear-MBA pass reads
  through a cast into the bitwise function below it, over the narrow atoms lifted by the same
  cast (`sext(f(a, b))` is `f(sext a, sext b)` for every bitwise `f`; `zext(f(a, b))` is
  `f(zext a, zext b)` when `f` is 0 at 0, else that plus `2^W`), the signature taken over the
  lifted atoms and the commit rule's boundary kept at the narrow ones; the bitwise pass hoists
  a common extension out of a tree of `& | ^ ~` over extensions of one kind and width, with
  constants (`zext(a) & ~zext(b)` is `zext(a & ~b)`, `~zext(a) & 0xffffffff` is `zext(~a)`,
  `sext(a) | sext(b)` is `sext(a | b)`), which subsumes the rules `zext_and`, `sext_xor` and
  the like at any depth; and the linear pass reads `zext(~t)` as `lowmask(W) − zext(t)` and
  `sext(~t)` as `−1 − sext(t)` in a sum that has the extension of `t` as a term too, so
  `sext(a) + sext(~a)` is `−1` without the MBA service. On the benchmark corpora over `zext<64>`ed and `sext<64>`ed
  32-bit variables, `Strategy::deobfuscate()` alone now gives 1,826 nodes instead of 3,926
  and 3,922 (the same MBAs at one width: 1,223), and with the MBA service 1,812 and 1,796
  nodes in a quarter of the time, the service being asked a sixth as often.
- **Comparisons move to the narrow term; extracts push through more.** A lone comparison
  with a constant was emitted on its own operand, so `sext<64>(a) <s 5`, `zext<64>(a) <u 5`
  and `sext<64>(a) + 3 <s 10` stayed as they were; the compares pass now emits it on the
  deepest term the operand is a function of (through extensions, offsets, complements and
  masks, as it already combined two comparisons) where that is smaller: `a <=s 4`, `a <=u 4`,
  `a <=s 6`, and `a - 3 <=u 9` for `zext<64>(a) - 3 <u 10`. A sign test is written as one
  (`a <=s -1`, not `0x80000000 <=u a`). The casts pass pushes an extract through `a + a` (the
  linear pass's spelling of `a << 1`, which hid the shift: `extract<1, 31>(x + x)` is
  `trunc<31>(x)`), through a sum or product above an operand whose low bits are known zero, and through an
  arithmetic shift (`trunc<32>(x >>s 8)` is `extract<8, 32>(x)`,
  `extract<8, 8>(x >>s 60)` is `sext<8>(extract<63, 1>(x))`).
- **Ten rules from the audit of mixed-width inputs**, each proved by the checker:
  `sub_zext_negative`, `sub_sext_negative`, `ult_zext_succ` and `masked_eq_self` in
  `core.compare` (`zext(a) - zext(b) <s 0` is `a <u b`, `zext(a) <u zext(b) + 1` is
  `a <=u b`, `x & 15 == x` is `x <u 16`); `ashr_sext_sign`, `sext_flip_zext`,
  `umulhi_from_wide` and `smulhi_from_wide` in `core.casts` (`extract<32, 32>(zext<64>(a) *
  zext<64>(b))` is `umulhi(a, b)`); `concat_sign_shift` and `concat_hi_add` in `core.concat`
  (`concat(x >>s 31, x)` is `sext<64>(x)`, `concat(extract<32, 32>(x) + 1, trunc<32>(x))` is
  `x + 0x100000000`).
- **Less repeated work in the passes and the MBA phase.** The demanded-bits pass keeps, for
  the phase run, the operands it found nothing to simplify under a mask (every mask over one
  shared chain re-walked the chain and asked the facts again at every node); the commit rule
  keeps the region it computed to ask whether building a candidate pays and reuses it to ask
  whether the result does, when nothing the counts depend on changed in between; the MBA phase
  marks every node inside a fragment within its limits as asked without scanning it again
  (along a chain of n sums that was n scans of n links), skips the links of `& | ^` chains and
  the operands of a cast whose user is asked, as it did the links of sums and products, and
  remembers the questions whose answers the gate could not prove, instead of asking, lifting
  and certifying them again; the normal-form solver's memo serves an answer to any step budget
  of at least the steps it cost (it was keyed by the exact budget, so a host whose per-call
  budget shrinks as it is spent got no hits once it fell below the per-question limit), and
  its null-conjunction search no longer builds its sample for a form with nothing to test.
  Answers are unchanged; the MBA service is asked 400 times instead of 2,404 along a 400-term
  masked `^` chain.
- **The MBA phase judges a fragment's mix without its casts.** A fragment is asked only when
  it mixes arithmetic and bitwise operators, and the test ran on the fragment as spelled, where
  `~` and casts count as neither: `sext<64>(a) + sext<64>(~a)` and
  `zext<64>(a) - zext<64>(a & b)` never reached the solver. The shape is now also taken of the
  fragment with its casts written out, as the solver reads it.
- **Extensions of narrow variables, read and written.** The normal form took a zero
  extension `zext(a)` as an atom like any other, so `zext(a) + zext(~a)` had no mask and
  `sext(a) + sext(~a)` (whose sign extensions `decast` writes as `(zext(a) ^ 2^31) − 2^31`)
  was not `−1`; and it could not write a cast at all, so the normal form of
  `(sext(a) ^ sext(b)) + 2·(sext(a) & sext(b))`, exactly `sext(a) + sext(b)`, rendered larger
  than the question, while a sum of sign extensions that did render came out as the spelling
  `0xffffffff7fffffff − (zext(z) ^ 0xffffffff7fffffff)`, a fixpoint of the whole simplifier.
  Now the operand's width of a zero extension is a class boundary and the atom is zero in the
  classes above it; the unmasking of a normal form knows that; a bitwise operation over sign
  extensions (forms `g[lo] − g[sign]`) is the sign extension of the operation over the values
  extended (`~sext(x) & sext(z)` is `sext(~x & z)`); and the renderer writes `k·sext(trunc(g))`
  for such forms and `zext(f(a, b))` (or `~zext(~f)`) for a bitwise function of zero
  extensions of one width. The certificates follow: the bit-serial comparison and the
  polynomial tests take a zero-extended narrow variable as one whose bits above its width are
  0. On the benchmark corpus of linear MBAs over `sext<64>`ed 32-bit variables, results shrink
  from 3,219 to 1,796 nodes (the same MBAs at one width: 1,223), in 4 M solver steps instead of
  30 M; over `zext<64>`ed variables from 1,822 to 1,805; the other corpora are unchanged.

- **Where events happen.** An `Observer` saw each rule tried and each rewrite, but not which
  phase or round made it, and some changes of the root it did not see at all. New events say
  where: `Event::Root` when a distinct root's work begins, `Event::PhaseBegin` and
  `Event::PhaseEnd` around every phase of every round (the end with the root the phase left,
  the work it spent as a `Budget`, and the limit that stopped it), `Event::Stage` for the MBA
  service's rewrites of the whole root outside the phases (context push, case tables, the
  opaque sweep; `Stage::{Context, Cases, Sweep}`), and `Event::Relied` after a rewrite that
  holds only under some of the run's assumptions. The root no longer changes without an event:
  from `Root` through each `Stage` and phase, the last root reported is the result.
  `Phase::name` gives each phase's short name (`local`, or the pass's name as `By::Pass` and
  `Stats::passes` give it). With no observer nothing is built.
- **What almost happened.** `Event::GuardFailed` names the guard predicate that did not hold
  and the nodes bound to its operands. `Event::NotSmaller` reports each candidate a pass built
  or estimated and dropped as not smaller, with the nodes it needs and would free; `Event::Folded`
  each node the constructors turned into another operator when rebuilding it over new operands
  (`… ^ 0` into `…`), which no event reported before.
- **The passes' reasoning.** An observer whose `Observer::detail` is `Detail::Explain` receives
  `Event::Explain` after each pass rewrite: an `Explanation` of what the pass read (fact folding's
  known bits, the linear and xor forms, the truth table, a compared pair's relation set or an
  operand's intervals, the corner values of a linear MBA, each bit's source, the demanded mask,
  the narrowing the casts pass pushed, the layers the invert pass undid with the preimage under
  each, the divisor behind a magic number, a carry network's affine form, the evidence that
  vouched for an MBA answer). `Explanation` follows the passes and may change in any release.
- **Traces.** `engine::Trace` records every event of a run and writes it out as JSON Lines
  (`Trace::to_jsonl`): a header with the strategy's phases, the rules the events name with their
  text and proof-ledger evidence, the nodes they name (operands first, numbered as in the
  context), the events in order, each root's result and the run's counters; with
  `with_explanations`, `with_facts` and `with_assumptions`, the passes' reasoning, the known bits
  and intervals of the nodes, and the run's constraints. The same run writes the same trace, so
  traces diff across engine versions, strategies and budgets. `bitwright simplify --trace <out>`
  writes one (with `--file`, one per line, one after the other), and the WebAssembly module's
  `trace` returns one.
- **The Workbench** (`workbench/`): a playground for the engine in the browser, with no build
  step. An expression is simplified as you type (through the WebAssembly module); the rewrites
  appear as a story opened step by step, each with the whole expression before and after and
  the rule as written and proved or the pass's reasoning. The width, the engine, the assumptions
  and any single phase can be changed and the run looked at again; the symbols can be given
  values and every step evaluated at them; a gallery of examples and a browser of the built-in
  rules are a click away. It imports a QF_BV script, exports the input and the result as flat
  SMT-LIB definitions with an equivalence query, as a Lean 4 `example` for `bv_decide`, or as a
  LaTeX derivation, and proves them equal with bitwright's own prover in the browser; expression
  text is highlighted, in the editor too. Rules of your own are checked and linked from a panel,
  and Lean 4 theorems about `BitVec` are translated into rules (binders to parameters,
  hypotheses to `proves` guards). The WebAssembly module gains `checkRules`, `leanToRules`, and
  `rules`/`trusted` options on `trace`.
- **The checker in one thread.** `check_program` runs on the calling thread where no thread
  can be spawned (WebAssembly) or one is all there is, instead of failing. The
  WebAssembly module gains `trace` (with a `phases` option for a strategy of chosen phases),
  `evaluate`, `rules`, `fromSmtlib`, `toLean` and `equivalenceQuery` for it.
- **The inspector** (`workbench/inspect.html`): a viewer of trace files, with no build step. Each
  step of a run with the whole expression before and after it, the rule (as written, with its
  proof) or the pass's reasoning, and the phases × rounds it ran in; the run phase by phase; why
  a rule did not fire at a node (its failed guard with the operands' known bits, its candidate
  that was not smaller); the facts under the assumptions and what relied on each; a corpus with
  a rule census; two runs side by side. It runs the engine live through the WebAssembly module.
- **Behavior change.** `PassCounts::rejected_cost` of the xor pass now also counts the GF(2)
  forms it drops as not smaller (one per `NotSmaller` event).
- **Opt-in opaque and conditional MBA recovery.** `MbaConfig::with_opaque_sweep`,
  `with_noise_forms` and `with_known_atoms` enable exact rewrites for constants hidden through
  demanded bits, casts, rotations, condition-dependent pieces and complementary shared products.
  The default strategy does not run the additional sweep. Every committed answer remains
  certificate-checked; ordinary MBA certificates retain the caller's existing run budget.
- **Reusable independent contexts.** `Context::fork` keeps existing expressions and analysis
  caches while isolating nodes and proof history added afterward.
- **MBA question keys are cached.** `MbaExpr::key` computes its content hash once and invalidates
  it when a node is added.

## 0.23.0

- **A deadline means stop now.** Since 0.19 a run its budget stops keeps the work of the
  stopped phase (`salvage`: the root is rebuilt over what the walk finished). A deadline took
  the same path, which is the opposite of what it asks for: the caller has stopped waiting,
  and salvaging walks the stopped root's whole DAG once more — then the call went on to the
  next root, stopped it at its first charge, and salvaged that one too. A call over many roots
  therefore returned long after its deadline: 31,343 roots of a 12,000-step mixed Boolean
  chain took 19,711 salvages over 230 million node visits, 24 s after the host cancelled a
  call that runs in 0.7 s. Now a deadline stops the run where it is: the root it stops is
  returned as the phases before it left it, and the roots after it are not started
  (`End::BudgetTerminated(Exhausted::Deadline)`). The same call returns in 4 ms. A budget stop
  is unchanged — every root still keeps its own work.
- **`Stats::salvaged` and `Stats::not_started`**: how many roots had a stopped phase salvaged,
  and how many a passed deadline left unstarted. A deadline-stopped call reports `salvaged: 0`.
- **Behavior changes.** Only under a deadline, and only where a run would have continued past
  it: a root a deadline stopped no longer comes back with that phase's partial work, and roots
  after it come back unchanged rather than rebuilt. Results of runs that complete, and of runs
  a budget stops, do not change.

## 0.22.0

- **Bitwise functions over up to six atoms.** The bitwise pass reads a function of at most three
  atoms and takes a region of more than three as one atom, which hid that a function depends
  on few of the atoms below: Boolean masking over more atoms was left as it was by every
  strategy (`((a ^ m) & (b ^ n)) ^ ((a ^ m) & n) ^ (m & (b ^ n)) ^ (m & n)` is `a & b`, and
  with `^ (a & b)` it is 0). A node one of whose atoms is such a region is now read again flat,
  over up to six atoms (a 64-entry table, one `u64`; regions of more than six are atoms, and
  so are constants, so a node of more than three atoms is read by classes first), and written
  as the minimum form of the three atoms or fewer it depends on. In every strategy.
- **Carry networks** (`Phase::Carries`, feature `prove`; in `Strategy::deobfuscate()` only):
  additions and subtractions written out as `& | ^ ~` and constant left shifts over up to three
  atoms (parallel-prefix adders and subtractors, ripple chains of up to about 40 bits) become
  the affine form they compute (`x + y`, `x − y`). The form is read off the network's values
  at 0 and at each atom alone, checked at 64 fixed points (some near the region's constants,
  where a sum with one carries far), and committed only when the native prover proves it
  equal, on a copy of the region in a scratch context with a fresh symbol for each atom (its
  own simplification off, so it never re-enters the engine), within 2^16 AIG nodes and 2^22
  propagations and within what is left of the pass work (4 units a propagation). A truncated
  or miswired prefix tree, or one wrong only at inputs the points miss, is left as it is; so is
  a network the prover does not decide within its caps (a ripple chain of 48 bits or more),
  and every region holding it is not asked again. `bitwright simplify` turns the 8- to 64-bit
  prefix adders and subtractors that only `--synth` recovered into `x + y` and `x - y` (0.03 s
  for the 32-bit adder; the 64-bit subtractor's proof takes 1.24 M propagations).
  `PassCounts` gains `proofs`, `proved`, `refuted` and `unknown`.
- **Synthesis budgets.** `synth::Config::propagations` caps each proof's SAT propagations
  (unlimited by default, as before), which bounds its time where `conflicts` (200,000) does
  not: one proof of `x + y` against a 32-bit protected addition took 1.08 billion propagations
  and 128 s, and was still left unproved. `synth::synthesize_report` also returns the
  candidate equal at every sample whose proof was left undecided (`Report::unproved`). The
  command line's `simplify` and `lift` take `--synth-conflicts` and `--synth-propagations`
  with `--synth`, and name such a candidate on standard error: with `--synth-propagations
  20000000` that addition ends in 2.5 s, naming `x + y`.
- **Fixes.** The LLVM IR reader (`lift::llvm`, `transform::pairs`, `bitwright lift` and `tv`)
  refused four things LLVM writes. Block labels are read by LLVM's grammar for labels, a name
  of `[-a-zA-Z$._0-9]` or a quoted one, followed by its colon: a label that starts with a dot
  (`.lr.ph:`, `.preheader:`, as optimizations name blocks) was a syntax error, and one with a
  hyphen (`if-then:`) was not read as a label, so a branch to it named an unknown block. A
  quoted name holding a bracket (`%"a[b"`) opened a statement over the lines after it.
  Metadata after a `phi`'s last pair (`, !dbg !7`, `, !annotation !0`) was read as one more
  pair; it is read as on any other instruction: debug locations and annotations are skipped,
  and a kind bitwright does not model makes a target unsupported. Debug records are skipped,
  as the book says debug metadata is: a `#dbg_value(…)` line (LLVM 19 on) was not an
  instruction, and a call of `@llvm.dbg.value` and the other `llvm.dbg` intrinsics (before)
  not one bitwright knows, so no function compiled with `-g` could be read. Present since
  0.11.0.
- **Behavior changes.** Results change only where they get smaller. On CoBRA's 76,080
  expressions (`compare/`'s `bw-nf`) 3 answers change, none wrong: three `oses_fast` lines
  (371, 397, 399) from 489, 29 and 28 nodes to 488, 16 and 16. `--corpus-diff`: the random
  DAGs' results are 17 nodes smaller in all at 8 and at 64 bits under the signature solver,
  and 11 and 17 under the defaults; the MBA corpora's are unchanged. `simplify/mba-native/*`
  ends at 80 nodes instead of 82 (two `a << 1` written `a + a`, which needs no constant). A
  label's colon must follow it directly, as LLVM requires: `entry :` was read as a label and
  is now a syntax error. `--synth` writes a note on standard error when it leaves a candidate
  unproved. `--prover-budgets` (the prover's simplification runs the deobfuscation strategy)
  settles the same questions at every fuel; the MBA-heavy question spends 152,423 units of
  pass work instead of 151,951.
- Benchmarks: instructions against 0.21.1, medians of three runs back to back:
  `simplify/standard/*` +0.6 % to +0.7 % (the flat reading), `simplify/mba/*` +1.6 % to
  +1.8 % and `simplify/mba-nonlinear-sig/64` +1.8 % (the carries walk), `simplify/mba-native/*`
  −2.8 % to −2.9 % (smaller results), `compile/standard-200/64` −4.4 % and its rerun −4.5 %;
  the others within ±1 % but `simplify/tiny-context/64`, about +1 % (it varies by 2 % between
  processes).

## 0.21.1

- **Fixes.** Soundness: a step the MBA certifier's compositional test proved on its way to the
  question could stand for the question. The test pairs atoms whose definitions it proves
  equal and eliminates an atom a side reads only as `γ·v` once it proves that reading; when
  the symbolic comparison (equal polynomials over symbols) proved such a step, it recorded
  `Proved` as the question's verdict, and a comparison of the two sides that then failed left
  it so. The evidence gate on bitwright's own evidence (the default), `NativeProver`, and the
  normal-form solver's steps that wait on a certificate (relations between atoms, null parts,
  bitwise forms, synthesis hits) could so take a pair that differs at some input as proved: at
  64 bits, `x + 2^63·y + 2^63·x` against `((x ^ s) + 2·(x & s)) ^ ((2^63 ^ ((u + 1) & ~u &
  2^63))·x)` with `s = 2^63·y` and `u = x + 598`, which differ where `x = 2^63 − 599`. The
  symbolic comparison now answers only for its pair; the question's verdict is recorded only
  where the question itself is decided. Present since 0.6.0. Found by checking every proof
  exhaustively on unequal pairs that agree at most inputs, at 21 to 25 variable bits, above
  the exhaustive certificate, so that the compositional test decides; the test of compositional
  verdicts ran only at sizes where the exhaustive certificate decides first. That check is now
  a test among the ignored ones (`proofs_above_the_exhaustive_test_hold_at_every_input`).
- **Behavior changes.** An answer changes only where it rested on such a step: none of
  CoBRA's 76,080 expressions (`compare/`'s `bw-nf`) and no `--corpus-diff` result. Of 218,770
  mutants of those expressions (one constant, operator or variable changed), 62 change: 3 are
  no longer simplified, 59 get another answer.

## 0.21.0

- **The MBA certifier's symbolic comparison is charged at its cost.** It was charged a unit of
  pass work per monomial operation, which costs about 250 node evaluations, and where no
  evaluation test fit it ran in full and was charged at most what was left (one call took
  2.7 s). It is now charged 256 units per operation (`SYMBOLIC_RATE`, the measured cost) and
  runs within what is left: stopped there, it is over budget, as a test over the budget is.
  Ahead of a long test it no longer keeps the test's budget in reserve; when it decides
  nothing and leaves too little for the test, the test is over budget.
- **The MBA solver's steps under the fuel.** New `Budget::mba_steps`, the solver's steps summed
  over a run (`Budget::fuel(f)` gives `4·f`, so 2^24 by default; a step costs about two to three
  units of pass work), and `Exhausted::MbaSteps`. Each call runs within the least of
  `MbaBudget::steps` and what is left, and is charged the steps it spent. With nothing left a
  question is not asked, and the node is not final. New `MbaSolver::solve_counted` reports a
  call's steps; its default is `solve`, charged the whole limit. `NormalFormSolver` counts its
  steps, and its memo charges a remembered answer what finding it cost, so a charge never
  depends on what it remembers. `SignatureSolver` counts its corner evaluations and does not
  compute a signature its limit cannot cover. `ThreadedSolver` passes the count through.
  `MbaStats::steps` reports them. C: `bw_budget.mba_steps`, `BW_LIMIT_MBA_STEPS` and
  `BW_ABI_VERSION` 2; Python: `Budget(mba_steps=…)`.
- Together the two make the fuel bound the MBA work's time. The input the solver-budget proposal
  found by hill climbing (44 nodes, 8 bits, five variables) took 142.5 G instructions (9 s) at
  `Budget::fuel(1024)` and 201.8 G at the default budget. It now takes 0.27 G and 2.2 G, with
  the same 39-node result at every fuel; the proposal's two other worst inputs also keep their
  results, for 0.3 to 3.1 G instead of 2.3 to 8.7 G. The measurements behind both choices are in
  `docs/proposals/symbolic-charge.md` and `docs/proposals/solver-budget.md`.
- **Behavior changes.** At the default budget no bench row and no `--prover-budgets` answer
  changes; per the proposals' measurements, neither do `--corpus-diff`'s results or any scored
  line of CoBRA's datasets. Some runs on random DAGs end "exhausted" where they ended "no
  simpler", with the same results. Under small fuels results change wherever the comparison or
  the solver needed more than the fuel now gives, and every change measured was a larger
  result. CoBRA solves 66,975 lines at fuel 2^12 instead of 69,833, and 58,579 at 2^10 instead
  of 63,280; twice the fuel brings more back than that, for fewer instructions (72,065 at 2^13).
  The MBA-heavy question of `--prover-budgets` spends 151,951 units of pass work instead of
  20,371 and is still proved from fuel 2^14 up. A solver that does not report its steps is
  charged its whole limit per call: at the default budget at most 16 calls of 2^20 steps per
  run, where 4,096 were allowed.
- Benchmarks: no row of `bitwright-bench` changes its results. Instructions against 0.20.0:
  `simplify/*` −0.4 % to +0.1 %, `compile/*` −1.2 % to 0 %, `constraints/*` +0.3 %, the others
  within ±1 % but `service/eqsat/32` (−8.8 %; it varies by about 6 % between processes) and
  `service/smt-export/64` (+1.6 %), which this change does not touch.
  Reading the one budget field it needs, where it computed the whole remaining budget, keeps the
  larger `Budget` from costing more.

## 0.20.0

- **Cheaper MBA certificates.** A polynomial test that would take far longer than reading both
  sides as polynomials over symbols now tries that first (the symbolic comparison,
  `CertStats::symbolic`, which ran only where no test fit or the test was over its budget).
  It proves only sides that are equal everywhere, which the test finds equal too, and its work
  is capped at half the test's estimated time and at what leaves the test affordable, so a
  comparison that decides nothing never costs the test its budget: every certificate's verdict
  is the same at every budget, and only its work changes. The 48 MBA identities of
  `bitwright-bench --prover-budgets` take 20,371 units of pass work and 23.2 million
  instructions under the default budget, where they took 3,100,471 and 57.0 million (12
  products at 18,337 points each); fuel `2^14` spent 20,371 before and still does.
  `simplify/mba-nonlinear/64` takes 82 % fewer instructions, `simplify/mba-nonlinear/8` 2.7 %
  fewer, and the normal-form solver's nonlinear corpus of `--corpus-diff` at 64 bits 0.30 G
  instead of 2.73 G; every `--corpus-diff` result is the same.
- **A cheaper sample check in the compositional certificate.** Its check that each pair's
  skeletons agree with their nodes at the 64 points of the refutation sample now evaluates
  them a batch of points at a time with the batched evaluator, where it evaluated them one point
  at a time; where the batched evaluator might not compute the same (a value of another width,
  a cast, anything wider than 64 bits) it still does, and debug builds check that both agree.
  The check's answer is the same, and it is charged nothing, as before. It was half of the
  longest normal-form solver calls measured: one on a 44-node fragment of a random DAG takes
  5.3 G instructions instead of 10.4 G. `simplify/mba-nonlinear/8` and `/64` take 2.8 and 3.0 %
  fewer instructions, `--corpus-diff`'s random DAGs 2.3 % (8 bits) and 0.5 % (64 bits) fewer,
  `compare/`'s `bw-nf` on CoBRA's datasets 0.7 % fewer; every result, and every count of work
  and of certificates, is the same.
- **Behavior changes.** None in results under the default budgets: `--corpus-diff`, the
  `simplify/mba*` rows and `--prover-budgets` answer as before, and so does `compare/`'s
  `bw-nf` on every expression of CoBRA's datasets (76,080). Certificates spend less of a
  budget, so a run a budget stops may get further than before. `CertStats` counts proofs the
  symbolic comparison makes first as `symbolic` (the `NativeProver` example's identity, once
  `sparse`).

## 0.19.0

- **A budget for the prover's simplification.** `prove::Config::simplify_budget`, an
  `engine::Budget`, caps the engine's work on a question before it is blasted;
  `Config::with_simplify_fuel(n)` sets it to the new `Budget::fuel(n)`, which scales every cap
  of a budget by one number in the default's proportions (`Budget::default()` is
  `Budget::fuel(1 << 22)`, the budget the prover used until now, and stays the default). Caps
  count work, never time, so a question stops at the same place on every run. A simplification
  its budget stops keeps the rewrites it made, and the rest of the question is blasted as it
  stands. The new `Stats::simplification` (`prove::Simplification`) says whether the engine
  ran, what it spent, which cap stopped it, and whether it decided the question alone. Under
  the default budget the prover simplifies as it did, apart from the new rules below. Measured
  (`bitwright-bench --prover-budgets`): 48 MBA identities over 64-bit symbols, conjoined, are
  undecided after 20,000 conflicts without simplification (2.9 s); fuel `2^10` settles 11 of
  them and `2^12` 36 before the search; `2^14` and more decide the question alone in 1.6 ms.
  Of 27 identities of a keyed invertible mix and one guard over four mixes, 18 stay undecided
  without simplification (360,521 conflicts, 403.6 million propagations, 40 s); with fuel
  `2^12` 27 are decided by simplification alone and the guard by 432 conflicts (25 ms).
- **A run its budget stops keeps its work.** When a budget (or deadline) stops the engine in
  the middle of a phase, every node that phase finished is replaced by its result, every node it
  had rewritten but not finished by what the rewrite has become, and the nodes above are rebuilt
  over them (within the new-nodes cap; no rule or pass runs). Before, the stopped phase's work
  was dropped and the root came back as the phase before had left it: 200 MBA identities over
  64-bit symbols (1,840 nodes), stopped after 4,096 node visits and 140 rewrites, came back
  unchanged, and now come back with those rewrites (1,037 nodes). Results of runs that complete
  do not change.
- **What each search costs.** `prove::Stats` reports each `Question::solve`'s own work beside the
  totals: `last_conflicts`, `last_decisions`, `last_propagations` and `last_lemmas`, with
  `searches` counting the calls that searched, `lemmas` the clauses learned in all and `fixed`
  the variables the search has settled for good (`sat::Solver::lemmas` and `num_fixed`). A
  search goes on from where the last one stopped, so the marginal costs add up to the totals:
  three resumes of 100 conflicts cost what one search of 300 does, and the last of them a third
  of its conflicts (`Stats::totals` clears the per-search counts, so two questions compare by
  their work however their searches were split). Every count is the same on every run.
- **A value compared with itself changed.** New core rules: `x + y == x` is `y == 0`, and
  likewise for `x - y`, `x ^ y` and `!=` (`eq_add_same`, `eq_sub_same`, `eq_xor_same`,
  `ne_add_same`, `ne_sub_same`, `ne_xor_same`). So `x + 1 == x` is false, and murmur3's
  finalizer at two consecutive inputs differs at the word level (`mix(x) != mix(x + 1)` is
  true, where the invert pass stopped at `x + 1 != x`).
- **Invertible mixes, as a prover meets them** (`tests/mix_identities.rs`): for the 64-bit mix
  `C·(t ^ ((t >>u 32) >>u (t >>u 60)))`, `t = C·(x ^ C)`, under nine odd keys, equal mixes are
  equal inputs, a mix at a constant is its preimage, and a mix with its inverse is its input,
  each proved by simplification alone with no circuit or search; so are murmur3's finalizer
  lemmas. Seven spellings of the data-dependent shift are recognized alike. Scaled-down mixes of
  8 and 16 bits and xorshifts below half the width are checked at every input, every shift
  amount (0 included), against an independent scalar oracle. Mixes of one value under several
  keys combined (`H(p, C1) ^ H(p, C2)`) are not injective and are not cancelled: a guard over
  them is answered by the search when it is satisfiable, and stays open when it is a preimage
  question (the `fingerprint-64` fixture).
- **Behavior changes.** Results change where the six new comparison rules apply, and a run a
  budget or deadline stops returns what it had done in the stopped phase where it returned that
  phase's input before. Completed runs change only through the new rules. No answer of the
  prover changes from proved to refuted or back; more questions are decided, by the rules and
  by `simplify_budget` where a caller raises it.
- Benchmarks: no row of `bitwright-bench` changes its results; every one is within 0.8 % of
  0.18.0's instructions (`service/eqsat/32`, which varies by about 6 % between processes, +5.6 %).

## 0.18.0

- **Masks in bitwise functions.** The bitwise pass reads a function of at most three atoms and
  some constants as one truth table per class of bit positions (where every constant is 0 or
  all-ones), so a mask no longer takes an atom's place: `~a & (~b & (y & 5))` is
  `~(a | b) & y & 5`. A function that takes two tables is written as the cheapest of `f & M`,
  `f | M`, `f ^ M` and `f ^ (g & M)`. The compares pass decides `p == q` by the same tables:
  `~y & 37 == (y & 37) ^ 37` is true, `(y & 5) == (~y & 5) | 2` false.
- **Bit subsets order values.** A term whose set bits are bits of another's, as `& | ~`,
  extractions, extensions and concatenations show, is at most that term in the compares pass's
  order reading (signed too when the other is not negative): `trunc<16>(a) & 5 <u
  trunc<16>(~b & (a & 5))` is false, and the lane minimum `select(trunc<16>(x) <u
  trunc<16>(x & y), trunc<16>(x), trunc<16>(x & y))` is `trunc<16>(x & y)`.
- **Both readings of a condition.** A linear sum with both `sext(c)` and `zext(c)` of a 1-bit
  `c` reads the first as `−zext(c)`, so `zext(c) + sext(c)` is 0.
- **One condition read several ways.** A linear sum whose terms read one 1-bit condition in
  different ways reads them all over one `zext` of it: `zext(c)`, `sext(c)`, a select between
  constants (`select(c, K1, K0)` is `K0 + (K1 − K0)·zext(c)`), and the carry out of a
  partial-width addition (`concat(H, trunc_j(x + k))`, `zext(trunc_j(x + k))` and
  `(x + k) & (2^j − 1)` are the same field over `x`, plus `k mod 2^j`, minus `2^j` when
  `trunc_j(x) >=u 2^j − (k mod 2^j)`). The condition is recognized across spellings and polarity:
  `trunc_j(x) <u t` and its `<=u` forms with a constant on either side, `x & M == 0` for a
  run of bits `M`, an extraction compared with zero, `!=` and `~`. So
  `zext<64>(trunc<16>(x) <u 64) + zext<64>(64 <=u trunc<16>(x))` is 1 and
  `((x + 65472) & 65535) + zext<64>(64 <=u trunc<16>(x)) * 65536` is `(x & 65535) + 65472`.
  The demanded-bits pass reads such a sum modulo the low bits its user reads, so a condition
  whose coefficient vanishes there is dropped. x86's `sub ax, 64` merged into the wide
  register with a constant chosen by its borrow,
  `(select((x & 0xffc0) == 0, 0xffbf, 0x1ffffffbf) - (((x + 0xffc0) & 0xffff) | (x &
  0x1ffff0000))) & 0x100050040`, deobfuscates to `~x & 0x100050040`. Readings apply only
  where two terms read one condition, and the nodes they build (the `zext`, the field over
  `x`) count against the rewrite.
- **`(x | y) - x` is `y & ~x`** (core rule `sub_or`, the dual of `sub_and`): the MBA service
  wrote the masked complement `~x & 0x100050040` as `(x | 0x100050040) - x`, which compared
  unequal to itself in its other spelling.
- **SMT-LIB import.** z3's `ext_rotate_left` and `ext_rotate_right` (rotation by a term,
  modulo the width) are read. A `let` in another's body no longer counts towards the nesting
  bound, and `let` names are looked up in constant time, so the long `let` chains z3 prints
  for large terms import (a script with 850 nested `let`s was refused before). Importing takes
  about 10 % fewer instructions.

## 0.17.0

- **Opaque predicates of number theory.** The compares pass decides a predicate by residues
  where no bit or range of its operands shows its value: each leaf's value is taken modulo
  `2^k`, the predicate is evaluated three-valued at every such class (a comparison of terms
  whose known low bits differ is false), and an undecided class is split by the next bit, as
  Hensel lifting does, until every class decides alike. So `x·x != 7·y·y − 1` is true at every
  width (a square is 0 or 1 modulo 4, `7·y·y − 1` is 2 or 3), and so are `x·(x + 1)` even
  (OLLVM's bogus control flow, `urem` or `srem`), `x·x == 8·y + 5` false, a sum of three
  squares never 7 modulo 8, and their combinations with each other and with real conditions
  (`(x & 1) == 0 | (x·x & 7) == 1` is true, `(x·x == 7·y·y − 1) | (z == 3)` is `z == 3`).
  Before, only a predicate with a constant side was decided, at a fixed 4 bits. Masks,
  extensions, extracts, concatenations, constant shifts both ways, selects and signed
  remainders by powers of two (which keep the dividend's low bits) are read through; a
  predicate over a few narrow values is decided by exhausting them.
- **Other moduli, where the arithmetic cannot wrap.** Where intervals (from extensions, masks,
  remainders, squares and constants) show that no sum, difference, product or shift wraps
  around, unsigned or signed, the predicate is decided modulo the divisors of its remainders
  and quotients, and modulo 3, 5 and 7 for its equalities: `urem(zext(a)·zext(a), 7) != 3`,
  for a short `s` `srem(sext(s)·sext(s) + 1, 3) != 0` and `srem(s³ − s, 6) == 0`, and the
  divisibility test `udiv(p, 3)·3 == p` with `p = d² + 1` (a multiple of the modulus has
  residue 0 whatever its other factor). The native prover, which simplifies a question first
  by default, now proves these in under a millisecond (its search did not finish them in
  100,000 conflicts).
- **Squares are not negative.** The facts of `x·x` include the range of a square where it
  cannot wrap: `sext<64>(a:32)·sext<64>(a:32) >=s 0` is true.
- **Disguised tests of low bits.** A predicate over one value that its low bits alone decide
  becomes the test of the fewest of them: `(x·x & 7) == 1` is `trunc<1>(x)` (`x` odd),
  `(x·x & 15) == 0` is `trunc<2>(x) == 0`, `(x·(x + 1) & 3) == 2` is
  `trunc<2>(x) − 1 <=u 1`.
- **`Context::prove`** answers a comparison, a test against zero or a bit test by residues
  when the facts leave it open (`Query::Eq(x·x, 7·y·y − 1)` is false), building no node.
- The residue searches are bounded (48 operations, 4 leaves, 16,384 operations evaluated per
  search, charged to the pass budget), run only on a predicate with a product of a value with
  itself, and stop at the first two points that disagree.
- **Divisions by constants:** deobfuscation turns the multiply-high sequences compilers emit
  for a division by a constant back into `udiv` and `sdiv` (`Phase::Division`, in
  `Strategy::deobfuscate()`): `umulhi(x, M) >>u s`, the add-and-halve form for a multiplier of
  `W + 1` bits, a pre-shift for even divisors, the product in a register twice as wide
  (`trunc<32>((zext<64>(x) * M) >>u (32 + s))`, x86-64's `imul` and `shr`, or the high half of
  a 128-bit product), and the signed forms with an arithmetic shift and a correction by the
  sign of the quotient (LLVM) or of the dividend (GCC), for either sign of divisor. A sequence
  is read as an exact function of its input, split into pieces where its bits wrap or a sign
  bit flips, and replaced only when it is proved equal to the quotient at every input the
  facts allow, in integers wide enough that nothing wraps (decided at no more than eight
  points per piece), so a multiplier valid only below a bound is recognized where the facts
  show the bound (LLVM picks those for dividends with leading zeros). A quotient shifted or
  negated further becomes one division (`udiv(x, 3) >>u 2` is `udiv(x, 12)`, `-sdiv(x, 7)`
  is `sdiv(x, -7)`). In a linear sum, `x − d·q` over such a quotient becomes the remainder,
  however the product is spelled (`x - (q + (q << 1))` for 3), and so does `x − udiv(x, y)·y`
  for any `y`. `bitwright simplify` now shows `udiv(x, 3)` for `umulhi(x, 0xaaaaaaab) >>u 1`
  and `urem(x, 7)` for the remainder by 7. The other built-in strategies keep a compiler's
  strength reduction.

### Behavior changes

- Every strategy's results change where residues decide a predicate: it becomes a constant,
  a disguised low-bit test becomes the plain one, and facts of squares are tighter. A
  comparison the compares pass re-emitted at the same size is now also checked by residues.
- `Strategy::deobfuscate()` runs `Phase::Division` after `Casts`, so its results change where
  an expression holds such a sequence: those of `bitwright simplify` and `lift`, of the C,
  Python and JavaScript bindings' deobfuscation presets, and the prover's simplification of
  a question (`Config::simplify`). A bare `umulhi(x, M)` that divides is replaced by its
  `udiv` although both are two nodes: the one rewrite a pass makes that leaves the DAG the
  same size (nothing rewrites a division back).

## 0.16.0

- **Each program's own attributes:** translation validation reads each function's parameter
  attributes for that function only (`Body::params`, `ir::ParamAttrs`). A target that adds
  `noundef`, `range` or `nofpclass` to a parameter was checked as if it had not, and judged
  valid; it now has undefined behavior (`noundef`, even on an unused parameter) or poison
  where it should. The source's attributes no longer reach the target either, which removes
  false alarms (an argument outside the source's `range` is a value to the target).
- **Call sites:** `noundef`, `range` and `nofpclass` on a call's arguments and result are
  modeled (`ir::InstAttrs`), including the `range` clang writes on `ctpop`, `ctlz` and `cttz`,
  which made a whole module unreadable before. `returned` on parameters is modeled: returning
  another value is undefined behavior.
- **Nothing silently ignored:** pointers and memory (`ptr`, `getelementptr`, `inttoptr`, …),
  which the verifier read as plain 64-bit integers (provenance and `inbounds` lost), are
  refused; so are an attribute or metadata a target declares that bitwright does not model
  (`!fpmath`, `!range`, call attribute groups, unknown parameter attributes), and a
  floating-point environment other than the default (`strictfp`, denormal flushing, relaxed
  math attributes on the target), read through attribute groups.
- **`undef` in functions:** the guard against an `undef`-derived value used twice in the
  target (or branched on) followed operands in arena order, which the function syntax does
  not keep, so it never fired for `tv`; it now propagates to a fixed point.
- **`nsz`:** the sign of a zero *result* is insignificant too, as the language reference says
  (`fadd nsz 1.0, -1.0` may be `-0.0`), for every operation, intrinsics included. Adding `nsz`
  to an instruction was judged valid where a zero comes from nonzero operands.
- **Redefined registers:** a source register that a transformation's target defines again
  must be refined as the root is (it replaces the register at its other uses), as in Alive.
  `Body::matched`; a counterexample names the register (`Counterexample::output`).
- **Type assignments:** more than `Config::max_types` (now 128, was 32) leave the verdict
  unknown instead of valid at the ones checked (`Report::unchecked`). A cast between two open
  types never reached i32 or i64 before. Fast-math flags on a `select` or `phi` make its type
  floating point (an untyped `select nnan` was only checked over integers).
- **Malformed functions:** an empty block was read as `unreachable` (a source with one proved
  anything on that path); uses not dominated by their definitions and a value read in its own
  definition (which overflowed the stack) were accepted; phis without an entry per edge too.
  Each is now a syntax error with its line, as LLVM's verifier would reject it.
- **One function at a time:** `transform::validate` and `pairs_each` read each function pair
  on its own; `bitwright tv` and the C, Python and JavaScript bindings report a function
  outside the subset as unsupported and check the others (`pairs` stays strict).
- **Inference:** a binary atom relates two constants only when they have one type at every
  assignment; examples of two widths no longer panic, and preconditions no longer force a
  type on constants.
- **Preconditions over the source's registers:** `Pre:` is read after the source, so it may
  name its registers (it named a fresh input of the same name before).
- **What a verdict rests on:** `Config::certify` (`--certify`) accepts a proof only with a DRUP
  certificate the independent checker verifies, every question blasted without the
  simplifier. `transform::smt` (`--smt`, feature `smtlib`) writes each type assignment's final
  question as SMT-LIB for another solver (`smtlib::satisfiability_query` builds such scripts).
  The SAT solver checks each lemma its preprocessing offers by unit propagation before adding
  it, so a preprocessing mistake cannot decide a question, with or without a certificate.
- **Command line:** `prove`, `tv` and `infer` take `--max-types` and `--certify`; `prove` and
  `tv` take `--smt`. The help no longer says "every width".
- **Fuzzing:** `tools/tv-fuzz` generates control flow (diamonds with phis), `freeze` and
  `ctpop`; mutants add poison flags, parameter, return and call-site attributes and swap phi
  entries; the interpreter reads attributes, phis and switches and replays a counterexample's
  choices; nondeterministic samples it cannot settle are counted apart, not as unsound.

### Behavior changes

- Transformations judged valid before may now be invalid (attributes a target adds, `nsz`
  added, a redefined register that does not refine), unsupported (pointers, memory, an
  unmodeled attribute or metadata of the target, a non-default floating-point environment,
  an `undef`-derived value used twice in a function), or unknown (more type assignments than
  `max_types`).
- Some judged invalid before may now be valid: the source's parameter attributes no longer
  apply to the target, and a source with `noundef` and `range` has undefined behavior outside
  the range.
- Transformations with two open types check up to 128 assignments instead of 32, which takes
  longer; `bitwright tv` reports a function with a syntax error as unsupported instead of
  failing the whole run, and so do the bindings' translation validation.
- `transform::Report` gains `unchecked`, `Counterexample` gains `output`, `ir::Inst` gains
  `attrs`, `ir::Body` gains `matched` and `params`, `ir::Transform` gains `pointers`,
  `unsupported` and `float_env`, and `Config` gains `certify`.

## 0.15.0

- **Repeated evaluation:** `Context::eval` caches the most recent nonempty root set,
  maps the reachable graph to registers, and reuses storage. Supported integer operations
  through 128 bits use native registers independently of wide, floating-point, extension,
  and unsupported multiply-high operations in the same batch. Values are materialized
  only at fallback boundaries; symbol bindings and widths are checked on every call.
  Measured mixed batches are about 4.1 times faster than whole-graph fallback. Earlier
  comparisons against rebuilding the schedule on every call show about 4.8–6.2 times
  faster narrow evaluation. See `docs/benchmarking.md` for workloads and limits.
- **Shared templates:** immutable compiled forms use `Arc`, and imports release the cache
  mutex before callbacks. Warm imports can proceed concurrently into independent contexts;
  the eight-worker benchmark improved about 4.7 times, with one-worker cost within noise.
- **Memory correctness:** reused unknown reads retain pending alias conditions, generated
  symbols skip occupied names, and changes to initial contents invalidate cached loads.
  Address normalization handles deep additive chains iteratively.
- **SMT array names:** imports reserve numbered symbol prefixes across the entire script,
  including declarations after an array's first read, preventing generated reads from
  capturing caller symbols.
- **Bounded parsing and comparison analysis:** deeply nested transformation constant
  expressions return syntax errors, and comparison-order modeling consumes a cumulative
  visit budget before descent. Both avoid reproduced stack overflows.
- **Benchmarking:** added cold, sparse, mixed, and cheap evaluation workloads, shared-template
  worker workloads, and `--metric wall` comparisons using saved elapsed time.

### Behavior changes

- EqSat extraction propagates reduced child costs even when the chosen child node is
  unchanged. This can produce different, cheaper equivalent expressions.
- Comparison-order analysis stops after its cumulative visit allowance is exhausted,
  including failed speculative branches. Deep or expensive patterns may remain unsimplified.
- Memory versions are specific to their memory and store history. Foreign versions and
  versions created on diverged clone branches return errors; clones still accept their
  shared history. Oversized loads return an invalid-width error before constructing cells.
- Generated memory and SMT array read names can change when caller symbols occupy the
  usual names. Existing load expressions retain their old contents when initial memory is
  changed, while subsequent loads use the new contents.
- Excessively nested transformation expressions now fail with a syntax error instead of
  overflowing the process stack.

## 0.14.0

- **Certified exhaustive decisions:** `Config::exhaustive_inputs` (default 0, off) decides
  a question with at most that many unknown input bits by evaluating every legal
  assignment of its word-level program, in blocks and in parallel across threads. A
  failure is the first failing assignment in enumeration order, replayed on the original
  question. With a certificate, the proof is a new `Exhaustion`: the question's bit-blasted
  circuit, which `Certificate::check` simulates at every assignment of its inputs,
  independently of the word-level decision. The simulation reuses registers by liveness and
  stops a block once each assignment has a false conjunct of a negated-conjunction goal.
  `Certificate` gains a public `exhaustion` field (an exhaustion certificate has no clauses
  or DRUP proof). The two valid 32-bit hard fixtures, `masked-pair-32-unique` and
  `fingerprint-32`, are now proved with checked certificates in both spellings and both
  arithmetic encodings, in 8.3–11.1 s per query (12–20 s under heavy load) on a shared
  20-core host; the benchmark's `--exhaustive-inputs N` measures this. `fingerprint-64` and full-width
  sources stay beyond enumeration.
- **Complete-query benchmark target:** `--mixers --query-budget-ms 10` measures fresh
  original native queries through preparation and independent proof/model checking.
  Unresolved queries and queries over the target fail the acceptance run, with separate
  statuses; all selected cases are still reported. This measures wall time rather than
  imposing a cancellation deadline.
- **Affine constant products:** eligible 64-bit odd coefficients can use two modular
  factors plus an addition or subtraction of the source. The bounded planner examines
  381 recipes and retains the existing input guards and 10% estimated-work threshold.
  Bit-parallel signed-digit costing matches the serial calculation on more than 98,000
  coefficients. Twelve affine equivalence checks now have zero-search certificates;
  the full fingerprint circuits use about 5% fewer variables and clauses beyond exact
  factorization. The original hard guards remain unknown within the 10 ms target.
- **Masked source projections:** bounded Boolean cuts now follow single-bit extracts and
  AND masks keeping at most eight source bits without expanding the whole source word.
  Pure wiring preserves overlaps and complements; other projected bits remain conservative
  inputs. Exhaustive reference checks, wide boundaries, declaration changes, resource caps
  and original refuting models cover the proof boundary. One original full tail now has a
  three-value superset with a one-node coverage certificate; the complete joint output and
  hard guard questions remain unknown.
- **Scoped fact premises:** native validity questions now accept partial known bits,
  unsigned and signed ranges, and unsigned strides. `Assumptions::predicates` exposes
  their exact original Boolean conditions; SMT-LIB queries use the same encoding and
  retain odd strides that were previously omitted. The word sampler fixes scoped bits
  only through original seed masks and pure wiring, preserving overlapping symbols,
  exhaustive coverage limits, original model replay and the certificate path.
- **Declaration changes and assumptions:** propagated facts are refreshed from the original
  constraints when symbol declarations change. This prevents withdrawn global bits from
  surviving in scoped facts and producing false proofs. Constraint ids remain stable,
  and explicitly refreshing a set also updates its infeasibility diagnostics.
- **Bounded joint output domains:** `prove::domain::analyze` computes a conservative
  tuple superset from original output roots and scoped Boolean premises, preserving
  shared predicates, casts and distinct keys/tails at one target. Explicit construction,
  live-input, enumeration and tuple caps discard incomplete results. Coverage predicates
  retain the original expressions for independent certification. Both multiplication
  encodings now treat a zero-extended Boolean factor as a conditional bitwise copy.
  Complete cut evaluation with at most eight live predicates proves Boolean tautologies
  that structural hashing alone leaves open, under a separate fixed work allowance.
  The eight captured nonconstant targets expose their output domains within the default
  limits and one-node coverage certificates; their original fingerprint reachability
  questions remain unresolved.
- **Correlated dispatch-tail regressions:** shared Boolean predicates retain the same
  numeric value through 32-bit and 64-bit casts. A captured full-width target and
  its conditional tail outputs prove their two-tuple superset and exclude mismatched
  tuples with zero search work and one-node checked certificates. Original byte models,
  both abstract predicate values, and independent-predicate counterexamples preserve
  the distinction between output correlation, arm reachability and graph closure.
- **Zero-preserving facts:** wrapping multiplication by a known-odd value retains
  nonzero operands, including variable factors. XOR with a positive logical right
  shift of the same source also retains nonzero values, including nested and
  self-selected counts. The bounded matcher checks count offsets for wraparound
  and uses global count facts; conditional source dependencies remain tracked.
  These queries now prove before circuit construction. Complete small domains,
  words through 512 bits, negative controls, scope changes and original-CNF
  certificates cover the rules. The complete hard mixer queries remain unknown.
- **Bitwise identity facts:** AND, OR and zero-XOR transfers retain the operand's complete
  ranges and strides when known bits establish that the operation preserves its value.
  Both operand dependencies remain tracked under assumptions. A redundant selector mask
  now preserves its nonzero lower bound, letting the compact conditional shift bound prove
  before bit-blasting. Wide words, changing masks, scope withdrawal and original-CNF
  certificates are covered. The complete hard mixer queries remain unknown.
- **Bounded constant-product factorization:** eligible 64-bit odd products use two exact
  modular factors, optionally corrected by the source, when a bounded search predicts
  at least 10% less carry work.
  Words with fewer than 32 distinct nonconstant literals, a fixed low bit or a known-zero
  high bit retain the existing encoding. Both multiplication encodings are covered by
  scalar, model, continuation and certificate checks. The three hard
  fixtures use 13–18% fewer variables and 14–18% fewer clauses than the shared-gate encoding;
  their full-domain verdicts remain unknown at the measured budgets.
- **Shared logical-gate encoding:** XOR, majority and mux recognition now bypasses shared
  AND internals while preserving separately observed roots and operands. Complemented XORs
  share their graph representation throughout arithmetic. The three hard-query fixtures
  use about 8–10% fewer CNF variables and 4–6% fewer clauses; their full-domain verdicts
  remain unknown. Exhaustive signed-input and observation-set checks validate models and
  independent refutation certificates.
- **Wrapping arithmetic at the highest bit:** additions and subtractions skip their
  discarded outgoing carry and share complemented XORs in that final column. Carry-save
  products share their final-column parity too. Highest-bit covariance of odd products now
  proves with zero conflicts, including the default paired-product encoding. Tests check
  even-product counterexamples, wide words, certificates and the boundary between necessary
  mixer symmetries and exact guards. The full hard queries remain unknown at tested budgets.
- **Masked self-selected counts:** range analysis now recognizes redundant constant masks
  around a self-selected shift count or its constant offset. The masked mixer shift now
  gets the same 28-bit bound as its unmasked form without first rewriting the expression.
  Masks that change the count stay conservative. Tests cover complete small domains,
  declaration withdrawal, wrapping offsets and widths through 512 bits.
- **Exact decoded-guard checks:** complete small input/image domains, both shift spellings
  and independent native certificates check cancellation of odd outer products with a
  shared image word. A counterexample rejects dropping the image link. The corresponding
  unrestricted captured guards still exhaust the tested search budgets.
- **Necessary-condition model checks:** mixer regressions cover signed correction bounds
  and decoded high-bit preservation, including selector endpoints and full-width values.
  A supplied model satisfies the relaxed conditions while failing to match the original
  image; original-expression replay and independent point certificates enforce that boundary.
- **Captured pair replay:** a typed eight-byte dispatch regression checks all three numeric
  mixer pairs against independent scalar values, including full-width boundary inputs and
  both shift spellings. It detects choosing the first listed mixer as the common term when
  another mixer is shared across the comparisons, even when both resulting guards are false.
- **Complete online word domains:** ordered word enumeration now returns `Proved(None)`
  after the joint stream covers every legal assignment without a counterexample. Partial,
  random, individual-word and diagonal coverage cannot prove validity. Declared sparse bits
  and assumptions are respected; certificate requests retain the original circuit path.
  Fingerprint and uniqueness fixtures with 8, 12 or 16 free input bits now prove online in
  about 22 µs–4.2 ms, with zero circuit nodes. Complete 32-bit and unrestricted 64-bit domains
  still need further work. Independent generated truth tables and late witnesses test the
  proof boundary.
- **Explicit verified finite facts:** `prove::finite::CheckedPair::verify` completely
  enumerates a requested source domain before producing a reusable masked-pair fact.
  `Question::valid_with_pairs` applies it only to matching integer mixers with the same
  source and an established bound. The prepared facts settle the 32-bit fingerprint,
  masked-pair uniqueness and a captured 32-bit loaded-word guard without circuit work.
  Their preparation costs seconds; warm queries take tens of microseconds. This path is
  opt-in, replays original models, and preserves the original path for DRUP requests.
  Unrestricted 64-bit cases remain unknown.
- **Restart priorities:** SAT trail reuse now includes higher-priority implied variables
  that a restart would free, while keeping root assignments out of that comparison.
  Completed models are returned without undoing and rebuilding their trail. Focused
  regressions cover implication priorities, retained prefixes, root priorities and model
  completion. The hard mixer verdicts remain unknown in the measured short budgets.
- **Independent-word streams:** `SampleMode::Words` shares its existing allowance between
  joint, individual-word and diagonal prefixes, so later words can expose witnesses without
  enumerating an earlier 64-bit word. A captured two-word dispatch now returns its original
  sixteen-byte model in 128 samples / about 0.1 ms without constructing a circuit. Standalone
  symbols, shared bytes, bounded exhaustion and constrained diagonal witnesses are covered.
  Remaining captured exclusions still require further work; application replay is separate.
  A complete independent 32-bit oracle also establishes a captured loaded-word pair's
  exclusion; the native solver still needs a faster proof path for it.
- **Reconstructed-word coordinates:** opt-in `SampleMode::Words` searches the low bits of
  maximal pure concatenations before the remaining symbol bits. Original byte symbols,
  overlapping bits and fixed declarations retain their identity. A byte-concatenated
  cross-key guard that ordinary small-input order leaves unknown recovers its eight-byte
  witness in about 3 ms without a circuit. Generated programs, complete small input cubes,
  repeated-byte near misses and wide fallback cover the new ordering.
- **Early word sampling:** opt-in `Config::with_word_sampling(true)` searches for
  counterexamples directly on bounded integer DAGs of words through 64 bits before
  bit-blasting. It preserves sampling order, declared bits, assumptions and original-model
  replay. Incomplete sample coverage resumes normal SAT preparation; wide, floating-point,
  extension and oversized DAGs use the existing circuit path. `--word-samples` exposes the
  staged measurements: the full-width cross-key witness takes about 2 ms, versus 18 ms
  through the circuit sampler. Tests include 36 guard variants and independent scalar
  operator checks. The three hard exclusion/uniqueness queries remain unresolved.
- **Carry-save products:** opt-in `Config::with_carry_save_multiplication(true)` compresses
  modular product columns before one final carry-propagating addition. Constant rows use
  signed digits with exact complement/correction handling. Exhaustive small products,
  independent reference checks through 1,024 bits, fixed/correlated inputs, declared-bit
  models, certificates and exact resumed searches cover the option. `--carry-save` exposes
  staged measurements: short hard-query search instructions fall 18–44%, while the three
  hard verdicts remain unknown at the measured longer budgets.
- **Three-input parity encoding:** opt-in `Config::with_xor3_encoding(true)` inlines a
  private intermediate XOR, reducing the hard-query encodings by 24–28% of variables with
  the same clause count. Initial watches follow the output and outer-input roles. All
  polarities, repeated operands, observed intermediates, root aliases, declared models and
  exact resumption are checked. `--xor3` exposes staged measurements; longer searches remain
  mixed, so the default encoding is retained.
- **Selector partition regression:** an opt-in long suite checks the complete first-selector
  range and all 16 conditional cases for each hard query, preserving original domains and
  distinguishing conditional proofs from an unsplit proof. All 48 cases remain unknown at
  the measured 10,000-conflict / 5-million-propagation limits.

- **Peepholes for hard queries:** word-level self-shift bounds also recognize nonwrapping
  constant offsets in the count, giving compact and nested spellings the same 28-bit bound.
  Wrapping counts are conservatively left to ordinary transfer; exhaustive tests cover small
  widths and wide bounds through 512 bits.
- **Positive OR target factoring:** opt-in `Config::with_join_factoring(true)` factors ORs
  of XORs sharing an operand into a conditional gate. Zero target bits retain direct XOR
  aliases. The fingerprint fixtures lose another 28 variables / 112 clauses; the masked-pair
  uniqueness encoding is unchanged. `--factor-joins` exposes measurements, with checked
  polarity/sharing proofs and original-symbol models. Longer-search performance is mixed,
  and all three queries remain unknown under measured budgets.
- **Masked-pair near misses:** concrete original-expression regressions reject dropping the
  higher mask bits and distributing multiplication over XOR.

- **Correlated shift counts:** the bit-blaster evaluates a count's Boolean support when at
  most four count literals also occur in the data. Constant and literal-valued outputs fold
  without constraining that support; this exposes the upper zero bits of self-selected
  shifts before subsequent products. Differential tests cover signs, repeated/complemented
  count bits, overshifts and widths through 1,024 bits.
- **Shared input cancellation:** opt-in `Config::with_input_cancellation(true)` removes a
  shared input occurrence along bounded XOR paths while retaining other arithmetic branches.
  Paired dense odd products lose their direct high-bit dependency, with zero-conflict checked
  certificates at 8–129 bits. Original-symbol models, declared bits and exact resumption are
  retained. `bitwright-bench --mixers --input-cancel` measures the option; hard fingerprint
  and masked-pair uniqueness searches still exhaust the measured larger budgets.

- **Masked-bit relationships:** native preparation extracts fixed XOR relationships below
  asserted conjunctions and closes inconsistent signed-equality cycles without SAT conflicts.
  Derived clauses are proof steps, never certificate premises. Low-bit bitwise XOR cones
  cancel shared terms without changing arithmetic carry networks.
- **Optional search strategies:** `Config::with_relational_lemmas(true)` adds bounded,
  certified transitive equality lemmas; `with_selector_branching(true)` initially prefers
  small shift-count bits without fixing their values. Benchmarks expose `--relations`,
  `--selectors`, `--escalate-fast` and learned-clause counts, plus separate masked-pair
  candidate and uniqueness workloads. Hard fingerprint and uniqueness queries remain unknown
  under the measured budgets; the strategies remain opt-in because performance is mixed.
- **Relational regressions:** checked proof prefixes on satisfiable inputs, signed equality
  cycles and long chains, OR-target coverage, bounded XOR rewriting, exact resumed selector
  search, and original-symbol mixer low-bit identities and masked-pair witnesses.

- **Unknown-query workloads:** opt-in `SampleMode::Small` enumerates small assignments of
  unknown input bits, finding replayable wide-domain counterexamples without narrowing the
  domain. Sample exhaustion leaves proof search open. The full-width cross-key guard fixture
  is refuted at `x = 0x4563` after 17,792 sampled assignments.
- **Carry encoding:** majority gates with private inner products use one CNF variable and
  six clauses. Polarity, shared inner gates and near misses are checked against exhaustive
  truth tables, with independently verified UNSAT proofs.
- **Longer mixer searches:** `bitwright-bench --mixers --escalate` tries small witnesses and
  resumes unresolved native questions with larger explicit budgets; CSV includes sample counts.

- **Search limits and statistics:** zero allowances preserve an undecided search, and
  propagation budgets pause between literals instead of after an entire implication chain.
  Resuming preserves models, proofs and total search work. Preparation statistics now include
  propagation during CNF construction.
- **Cheaper prover preparation:** AIG gate pairs use the internal integer hasher, and
  incoming SAT clauses normalize in a reused buffer rather than allocating temporary vectors
  for each clause. Circuit identities, clause ordering and proof logging are preserved.

- **Native prover preparation:** a bounded Boolean overapproximation proves correlated
  dispatch/target tautologies before expanding their arithmetic predicates, including in
  certificate mode. Constant multipliers use signed digits when these need fewer arithmetic
  rows; already blasted subtrees are skipped on subsequent requests.

- **Keyed mixer/fingerprint workloads:** exact odd-key cancellation/inversion for both shift
  spellings, even-key collisions, original-symbol replay, correlated target/key exclusions,
  bounded fingerprint domain regressions and full enumeration, and bounded cross-key search escalation.
  `bitwright-bench --mixers` reports preparation/search stages and per-process peak memory, retaining
  explicit unknown outcomes and checking decided answers.

- **Broader native prover test suites:** structured and incremental SAT with checked proofs,
  exhaustive small-width and boundary-width circuits against the independent reference,
  solver-only arithmetic and memory workloads, declared model enumeration, floating-point
  classification, and SMT-LIB fixtures; large-width circuits run in the nightly suites.

- **Known memory regions:** preserve address offsets above 64 bits and resolve regions that
  cover the entire address space. A region larger than its address space is rejected.
- **Native proofs respect declared known bits** in circuit sampling, SAT search and
  certificates, including counterexamples for symbols eliminated by simplification.
- **Raising stops at host-owned values:** their internal nodes need no emission or symbol
  owner. Stale and foreign handles are rejected before consulting ownership.
- **Substitution skips replaced subtrees**, while still visiting shared descendants reached
  elsewhere. Identity substitutions return without walking the graph.
- **Breaking:** `prove::Certificate` gains the public field `exhaustion`, so code that builds
  a `Certificate` literal must set it (`None` for a DRUP certificate). With
  `exhaustive_inputs` left at 0, which is the default, the prover decides questions as before.

## 0.13.0

- **A constant and a left shift have one form.** `(x << k) & m` (and `(x + x) & m`, as the
  linear pass writes `2·x`) becomes `(x & (m >>u k)) << k`, and `|` and `^` likewise when `m`
  sets no bit the shift clears (`core.shift_canonical`). So `(x & K) << 1 == (x << 1) & 2K`
  is decided, and the rules written with the constant below the shift (`add_xor_and`,
  `xor_from_sum_double_and`, …) fire on either spelling. A mask the shift makes dead goes
  (`(x & 0x7fffffff) << 1` is `x + x`). The termination order ranks `Shl` below `&`, `|` and
  `^` on ties to allow it; no other rule changes direction. The two
  `guarded_recovery_mba_normalized` rules now match the new form.
- **`one_use(e)` in rule guards**, for a parameter or a subterm written as in the pattern: the
  node it matched has no other user, so the rewrite frees it rather than adding nodes beside it
  (LLVM's `m_OneUse`). It is about sharing, not values: checking, proving and the SMT-LIB and
  Lean exports take it as true, and so does the engine under `Sharing::Ignored`. Otherwise the
  engine answers it from the use counts of the live DAG, which rule phases now keep as the
  passes do (counted on first need), and a "no" from it leaves the node not final. The shift
  canonicalization uses it: with it, the random-DAG corpora come out the size they did before
  that canonicalization (9,043 and 9,422 nodes against 9,043 and 9,421), where without it they
  grew by 6 and 7.
- **`check::preempted`: rules the engine never lets fire.** For each rule it simplifies
  instances of the pattern and the rule's result at them, and reports the instances where a
  rule or pass rewrites a part of the pattern first and the result is larger than the rule's,
  so a pattern written in a spelling the engine does not keep is found when it is written.
  It also reports rules that never fire because another rule or a pass always gets to their
  instances first, with the same result (`PreemptionKind::Shadowed`): dead rules, such as a
  rule a later one duplicates. `bitwright check` warns of both, and the built-in corpus is
  tested to have none.
- **Rules for the spellings the engine keeps**, for the 14 built-in rules `check::preempted`
  found preempted: complementary selects and min/max of 1 or all ones as `zext`/`sext` of the
  condition, in either operand order; disjoint adds as ors (`split_mask_or_or`, `recombine_extracted_field_or`, `or_constant_to_concat`,
  `shifted_or_constant`); `shifted_add_constant` for a mask `and_mask_redundant` removes; and
  `sdiv_pow2_identity` for the shift `mul_pow2` makes of the product.
- **Prover questions decided in steps, with the reason and the work reported** (issue #11).
  - **`prove::Question`** is a question simplified, blasted and encoded once, then solved
    under as many budgets as its caller likes (`Question::solve(cx, Limits)`). A search that
    stops on its limits keeps its trail, learned clauses and restart schedule, so 5,000
    conflicts and then 15,000 more do exactly what 20,000 do in one call. Escalating a budget
    no longer pays for simplification, blasting, encoding and the search again.
    `valid`, `valid_under` and `equal` are one step of one.
  - **Breaking: `Outcome::Unknown` holds a `prove::Unknown`**, not a `String`:
    `Budget { conflicts, propagations }` (a larger budget may decide it), `TooLarge { nodes }`
    (the same under any search budget with that `max_nodes`) or `Unsupported(reason)`.
    `Unknown` prints the old messages. `RuleOutcome::Unknown` and `satisfy`'s error are the
    same type.
  - **`prove::Stats`** (`Question::stats`) reports the AIG nodes, samples, CNF variables and
    clauses, learned clauses kept, and conflicts, decisions and propagations.
  - **`Config::max_propagations`**, a deterministic budget that tracks time more closely
    than conflicts do: a conflict costs more propagation on a larger circuit. At 10,000
    conflicts, eight queries of one family took 11.6 to 56.9 million propagations and 0.8 to
    6.9 s.
  - **Sampling before the search (`Config::samples`, 256 by default).** The circuit is
    evaluated on 64 assignments at a time from a fixed seed. An assignment that refutes the
    question is its counterexample (checked by evaluation, as the solver's are), found with no
    clauses built. On queries of the issue's shape that a sixteenth of the values refute, the
    search took 5 to 40 s to find a refutation; the first 64 samples find it in milliseconds.
- **A faster SAT solver and a smaller encoding.**
  - Clauses in one arena, binary clauses (most of a circuit's clauses) in watch lists of
    their own, deleted clauses collected. A restart keeps the decisions the search would take
    again (trail reuse), so it does not propagate a large circuit from the top.
  - The CNF encoding recognizes exclusive ors and multiplexers (one variable and four clauses
    each, not three variables and nine) and trees of and-gates (one variable). A circuit of
    1.65 M AIG nodes has 0.92 M variables, where it had 1.6 M. The clauses are kept only for a
    certificate. The full adder's carry folds constant and repeated inputs.
  - Three 1.65 M-node queries of the issue's shape, at 5,000 conflicts each, took 7.0 s in
    all, down from 12.8 s, and peak memory fell from 1.09 GB to 510 MB. Multiplier MBA
    identities at 6 to 8 bits, proved by SAT alone, took 108 s in all, down from 144.5 s.
    The time a search takes still varies widely with its path: a search that has assigned
    most of a large circuit may propagate a large part of it again at every conflict.
- **The `prove` feature builds without `check`.**
- **The compiler integration in the C, C++, Python and JavaScript APIs** (issue #9): what 0.12.0
  added to the Rust API.
  - **The compile strategy.** `BW_PRESET_COMPILE`, `Engine::compile()` (C++),
    `Engine.compile()` (Python), `engine: "compile"` (JavaScript). Builders set sharing
    (`BW_SHARING_ROOTS`, `BW_SHARING_IGNORED`) and the region cap on any preset.
  - **Declared known bits.** `bw_declare_known` (up to 64 bits), `bw_declare_known_value`,
    `bw_declared_known`, and `Context.declare_known` in C++ and Python; `known` in JavaScript.
    `bw_context_reserve` and `Context.reserve`.
  - **Host rewrites as callbacks.** A C `bw_rewrite` (a function pointer with a user pointer,
    released when no engine holds it), a C++ `bitwright::Rewrite` over a `std::function`, a
    Python `Rewrite` over a callable, a JavaScript function. Each sees the node through a site:
    views, facts under the run's assumptions, construction. The engine holds them to the checks
    it holds a Rust rewrite to.
  - **Checking a rewrite offline:** `bw_check_rewrite`, `check_rewrite`, `checkRewrite`, with
    the failure's node, result and assignment.
  - **Templates** (`bw_template_*`, `Template`) and **lowering and raising** with host values
    as 64-bit integers (`bw_lowering_*`, `Lowering`; not in JavaScript, which keeps no context
    between calls).
  - **Counters of a run**, host rewrites included: `bw_engine_run_stats`,
    `bw_engine_run_each_stats`, and a `stats` argument in C++, Python and JavaScript.
- **`Lowering::detach` and `Lowered::attach`**: a lowering's values kept between calls while
  the context is used on its own (a binding cannot keep a borrow of it). **`Lowering::unraised`
  and `Lowering::emitted`** raise in steps, for a host that emits with the context released.
  `Lowering::raise` now fails on a symbol no host value stands for before emitting anything.
- **Python:** a host rewrite that uses the context being simplified gets a `BitwrightError`
  instead of waiting for itself.
- **Behavior changes.** Results change where the shift canonical form or the new rules apply:
  a constant `&`, `|` or `^` above a left shift is written below it when the shift has no
  other user, and the built-in rules' patterns for selects of one or all ones, disjoint adds
  and shifted products now match the forms the engine keeps. The built-in corpus changes, so
  engines that link it get new ids and contexts start new memos. On the generated corpora of
  `bitwright-bench --corpus-diff`, MBA results are identical and random DAGs come out at
  9,043 and 9,422 nodes (9,043 and 9,421 before). `one_use` is a reserved word in the
  expression syntax, so a symbol of that name must be written in its quoted form. Breaking:
  `prove::Outcome::Unknown` holds a `prove::Unknown` (see above); the additions to
  `FactPred` and `Preemption` are to `#[non_exhaustive]` types.

## 0.12.0

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
- **Behavior changes.** None. The default commit policy keeps every existing strategy's
  results and engine ids (so contexts keep their memos). The word-sized fact transfers, the
  matcher and construction give the same facts, matches and nodes as before, and
  declarations and host rewrites act only where a host uses them. The additions to public
  types (`Strategy::sharing` and `max_region`, `Stats::host`, `By::Rewrite`,
  `BuildError::UnprovenRewrite`) are to `#[non_exhaustive]` ones.

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
