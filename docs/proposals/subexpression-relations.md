# Sharing subexpression relations in the deobfuscation solver

Design proposal against Bitwright 0.32.23 (`cc252b6`).

The [follow-up investigation](../subexpression-coverage.md) tests width changes, caller context,
sharing, and the x64 and ARM64 lifting boundary before choosing an implementation.

Keep the typed expression DAG and the specialized word-level solvers. Change what a pass can give to
another pass. Today a reader can discover that two pieces compute the same value, yet the next reader
often benefits only if the first one rewrote the DAG. Let a reader also publish a proved relation that
other readers can use, even when rewriting either piece alone saves nothing. Start with MBA atom
selection and equality comparisons as the two consumers.

The first implementation shares full-width proofs within one run and lets comparisons and
demanded-bit queries consume them. The broader proposal below also covers conditional
relations and atom offsets. The [regression suite](../../bitwright/tests/equivalence_audit.rs)
checks the original misses.

## A miss on 0.32.23

At width 8, take `p = popcnt(x)` and simplify `(p & z) + (q | z) - p`. When `q = p`, the answer is `z`
because `(p & z) + (p | z) = p + z`. Now spell only the second occurrence as `q = popcnt(rotl(x, k))`.
Rotation permutes the bits, so their count is the same for every `x` and every `k`.

| Experiment on 0.32.23 | Observed result |
|---|---|
| Default CLI, `q = p` | `z` |
| Default CLI, `q = popcnt(rotl(x, k))` | `(popcnt(rotl(x, k)) \| z) - (~z & popcnt(x))` |
| Same input with `MbaConfig::with_opaque_sweep(true)` | `z`. The derivation first replaces the rotated popcount with the other popcount, then collapses the parent. |
| Same input with CLI `--synth` | `z` |
| Only `popcnt(rotl(x, k))`, with the opaque sweep enabled | `popcnt(rotl(x, k))`. This input contains no node for `popcnt(x)`. |

The native prover with simplification disabled produced certificates for both the equality of the
popcounts and the equality of the modified expression to `z`. Both certificates checked. With both
popcounts present, finding their relation suffices. With just the rotated popcount present, someone
must *propose* the smaller expression. A checked identity for popcount over bit permutations could
serve that second case. These observations are from the eight-bit probe.

```sh
bitwright simplify --width 8 'let p = popcnt(x); let q = popcnt(rotl(x, k)); (p & z) + (q | z) - p'
bitwright simplify --width 8 'let p = popcnt(x); let q = popcnt(rotl(x, k)); (p & z) + (q | z) - p' --synth
```

## Where the responsibility belongs

| Layer | What it contributes to binary deobfuscation |
|---|---|
| Lifting and semantics | P-code, VEX and LLVM front ends translate supported operations into typed terms, register values, memory effects and exits. Memory state, ISA shift-count rules and path assumptions determine which equations are valid. A host can ask about a block's live outputs or a branch under its incoming path conditions. |
| Expression DAG and facts | Structural interning shares identical constructed terms. Known bits, ranges and demanded bits describe which values are possible and which bits reach an output. These supply guards for word-level reasoning. |
| Word-level procedures | Linear and nonlinear MBA recover disguised arithmetic. Shuffle traces bit fields. Carries and Words recover limb operations. Comparisons, residues and invertibility handle lifted flags, opaque guards and mixer checks. Each procedure has a representation in which its own identities are cheap. |
| Simplification and decision | The engine chooses expressions under sharing and cost constraints. A constant target, infeasible branch or valid equality can also be asked about directly. Word-level procedures and bounded circuit search can decide such a query or produce a counterexample. A proof can succeed even when the simplifier leaves a large term. |

The proposed relation index belongs between the DAG and the word procedures, scoped to a run. Keep
cheap context-free conventions, such as ordering commutative operands, in the constructors. Ask
whether two terms agree on a mask or under a path condition at the use site, where both the
observation and the budget are known. The solver can use these procedures when answering a query.
Eliminating a symbol and reconstructing its value when returning a model belongs inside the solver.
Only value-preserving equalities under their recorded premises can flow back to the simplifier.
[Solver design](../design.md#0-direction-a-solver-first) ·
[Lifted blocks and host requests](../../book/src/lifting.md) ·
[Deobfuscation families](../../book/src/deobfuscation.md)

## What the changelog tells us

| Recurring failure | Evidence in the repository | Architectural consequence |
|---|---|---|
| A fragment counts correlated leaves as independent inputs | The 0.32.20 regression exercises a linear reading with nine raw atoms and a limit of eight. Two XOR-offset words and three related masks need only two independent words between them. 0.32.21 added chains of dependencies and opposite-sign products. [Peer-atom regressions](../../bitwright/tests/width_and_canonical_regressions.rs) | Resolve cheap relations while choosing the boundary. A cut is a choice made by a reader. Rotation can be opaque to MBA and transparent to a bit-provenance reader. |
| Equivalent interiors survive beneath a large parent | A 0.32.22 regression places two spellings of a masked field inside degree-three products. Another uses two selects that agree on just the bits their users read. [Demanded-bits implementation](../../bitwright/src/engine/pass/demanded.rs) | Keep the inner proof even when neither child becomes cheaper in isolation. Record the exact bits it covers. |
| Several passes need the same relation | Comparisons peel shared structure and ask several equality procedures. The MBA sweep has its own candidate classes and proof sequence. The polynomial pass also groups equivalent subterms. [Comparisons](../../bitwright/src/engine/pass/compares.rs) · [MBA sweep](../../bitwright/src/engine/pass/mba.rs) · [Polynomial forms](../../bitwright/src/engine/pass/poly.rs) | Give consumers one way to ask what has already been established. Keep each procedure's fast path. |
| Rewrites go backwards or a shared walk explodes | 0.32.21–0.32.23 record rewrite reversals, provisional results treated as final, and repeated traversal of a shared DAG. [Changelog](../../CHANGELOG.md) | Keep proof, scheduling and cost separate. The relation index itself needs visited sets, invalidation and a work allowance. These failures need their own regressions. |

## How a shared relation would work

1. **State the question precisely.** A query names two typed expressions, the observed mask and any
   assumptions. For equal-width words the obligation is `assumptions ⇒ ((a ^ b) & mask) == 0`.
   Cross-width uses supply an explicit extract or extension. An offset such as `q = p ^ 6` defines `q`
   over one independent word. Only unconditional full-width equality permits putting the original
   nodes in the same global equivalence class. A low-byte equality is useful to a low-byte consumer. A
   second output that reads the high byte retains its original value.
2. **Choose a few candidates.** Start with exact structural relations, existing normal forms, shared
   operands and the deterministic sample classes the MBA sweep already builds. Its classes find
   additive offsets, negated offsets and XOR offsets. Demanded-mask signatures serve projected
   queries. Index reachable nodes once and try promising pairs near a refused cut, repeated use or
   unresolved comparison. Cap representatives and work per bucket. A simulation collision earns a
   proof attempt.
3. **Prove and record.** Try the relevant existing procedure first, such as bitwise equivalence,
   polynomial equality modulo the observed width, or an MBA certificate. Fall back to the bounded
   circuit-only equality oracle when the prospective simplification warrants it. Admit exact evidence
   with its premises. A validated counterexample on original inputs can split a sample bucket. A
   counterexample over abstract atoms can assign incompatible values to two views of one word. In that
   case, expand the relevant boundary or add a proved binding, then retry within the remaining
   allowance. Budget exhaustion leaves the question open.
   [Atom lowering](../../bitwright/src/mba/lower.rs) ·
   [Engine equality oracle](../../bitwright/src/engine/oracle.rs)
4. **Let parents consume the result.** MBA lowering can bind `p = t ^ 3` and `q = t ^ 5` using
   `q = p ^ 6`, then count the independent atoms. Comparisons can reuse equality immediately. For
   same-width full equalities, indexing a pure operator by its type, parameters and proved operand
   representatives also exposes equal parents. Revisit affected parents when a new relation arrives.
   Carry a projection or a branch premise only where the consumer establishes it.
5. **Choose what to write back.** Keep the current expression as an alternative. A relation can help a
   parent without changing the child that established it. When a replacement is ready, apply the
   existing verification, hook, reliance and profitability checks against the live roots, including
   sharing. Keep entries only for valid arena nodes, including after a scratch rollback. Charge
   discovery, proof attempts and revisits against the caller's allowance.

Bitwright already uses simulation and proved equivalences within its circuit search. Those facts live
on Boolean gates. A reader choosing word-sized MBA atoms needs word expressions, widths and masks it
can name. Simulation-guided equivalence checking has a precedent in circuit synthesis.
[Bitwright circuit sweep](../../bitwright/src/prove/sweep.rs) ·
[Mishchenko et al., *FRAIGs*](https://people.eecs.berkeley.edu/~alanmi/publications/2005/tech05_fraigs.pdf)

When the desired expression is absent, a specialist can emit a candidate from its normal form, a
checked identity can introduce it, or bounded synthesis can search a small residual. The existing
equality-saturation service is another option for algebraic detours in its supported fragment. Its
current vocabulary excludes popcount, rotations and mixed-width casts. Global saturation would still
need providers for those meanings and a cost policy for extraction.
[Equality saturation](../../book/src/eqsat.md) · [Bounded synthesis](../../bitwright/src/synth.rs)

## First experiment and decision criteria

Start with an opt-in prototype at the MBA boundary. The existing lowerer admits a bounded number of
extra raw atoms (`max_vars + 4`) before peer reduction. Try structural bindings during collection so a
cheap, known relation can prevent early refusal. Let an unresolved equality in the comparison pass
consult the same recorded result. Begin with unconditional, same-width equality and existing
constant-offset bindings. Add projected equality through the demanded-bits pass once the
implementation can track which uses observe which bits.

Build a paired corpus from the regressions. Start each pair with an expression known to collapse,
change one occurrence by a verified identity, and run both with the same strategy and fuel. Vary a
shared atom's spelling, replace a mask with an equivalent typed slice, reverse predicate polarity with
its select arms, and embed the result under a second consumer. Include near-misses that differ in one
observed bit or hold on only one path. Exhaust small widths or check an independent circuit proof
before scoring a pair. Extend the existing family generators and rule preemption checks to preserve a
minimized input, expected result and budget for every miss.
[Condition-reading generator](../../bitwright/tests/condition_readings.rs) ·
[Rule preemption checks](../../bitwright/src/check/preempt.rs)

Compare the current default, the existing opaque sweep and the prototype. Score recovery of the known
constant, target, predicate or expression size, accounting for shared DAG nodes. For each miss record
whether a pair was proposed, whether proof succeeded, whether a consumer used it and whether the
replacement paid for itself. Track atom counts before and after binding, queries rescued before the
cap, cross-pass proof reuse, and work per recovered result. Replay ordinary compiler expressions,
large shared DAGs and small-budget queries alongside obfuscated cases.
[Benchmark and replay workloads](../benchmarking.md)

Adopt the index if both consumers recover held-out spellings at the same budget, and check p95 work
and decision rates on ordinary workloads against the same baseline. If gains come only from a new
popcount identity, ship that identity. If the existing opaque sweep recovers the same cases for the
same cost, improve its scheduling. The reason to introduce a shared index is measurable reuse across
families.
