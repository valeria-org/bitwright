# Solving (feature `prove`)

A [`Solver`](https://docs.rs/bitwright/latest/bitwright/solve/struct.Solver.html) answers
whether a set of 1-bit predicates can hold together: with a model when they can, and with the
predicates that conflict when they cannot. It is the answer to "is this path feasible", "which
value takes this branch", "is this predicate opaque", asked of the expressions a tool already
holds.

```rust
use bitwright::solve::{CoreItem, Solver, Status};
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let mut s = Solver::default();

// A path condition: a keyed check of an input.
let path = cx.parse("(input ^ 0x5bd1e995) * 0x9e3779b1 == 0xdeadbeef", &o)?;
s.assert(&cx, path)?;
assert_eq!(s.check(&mut cx)?, Status::Sat);
// The multiplier is odd, so there is one such input, and the model has it.
let input = cx.parse("input", &o)?;
let found = s.value(&mut cx, input)?.unwrap();
let again = cx.eval(&[path], &[("input".into(), found)][..])?;
assert_eq!(again[0].to_u64(), Some(1));

// A question against the path, in a scope of its own.
s.push();
let small = cx.parse("input <u 0x1000", &o)?;
s.assert(&cx, small)?;
assert_eq!(s.check(&mut cx)?, Status::Unsat);
assert_eq!(
    s.unsat_core(&mut cx)?.unwrap(),
    [CoreItem::Assertion(0), CoreItem::Assertion(1)]
);
s.pop(1)?;

// Or without asserting it: an assumption is of one check.
assert_eq!(s.check_assuming(&mut cx, &[small])?, Status::Unsat);
assert_eq!(s.check(&mut cx)?, Status::Sat);
# Ok::<(), bitwright::Error>(())
```

## What a check does

A check stops at the first of these that decides, and
[`decided_by`](https://docs.rs/bitwright/latest/bitwright/solve/struct.Solver.html#method.decided_by)
says which:

1. **Constants.** Construction already folds much of what obfuscation writes.
2. **Slices.** The assertions that share no symbol with the others are answered on their own:
   smaller questions, remembered apart, and a core within one.
3. **The last model.** A path condition that grows usually keeps its model.
4. **Memory.** The answers of slices seen before, and of unsatisfiable subsets of this one.
5. **A few assignments** (`Config::probes`, four by default), before any circuit. First the
   last model repaired at the level of words: a predicate that is false there is made true
   by solving it for one symbol through the operators that can be undone (an equality to
   either side, sums, exclusive ors, products by an odd constant, masks, shifts, extracts),
   the predicate with the fewest symbols still open first, so that a chain of definitions
   is followed like one. Then every symbol all ones, and values drawn from zero, one, small
   numbers and any number. What comes of it is evaluated: a hit is a model for microseconds.
6. **A quick search** (1,000 conflicts by default) on a circuit the solver keeps: each
   assertion is built once, and what one search learns the next ones use.
7. **The prover**: definitions solved (`x == t` puts `t` for `x`), the simplifier with its
   word-level procedures, then a circuit and a search of its own.

Most satisfiable path conditions end at 3, 5 or 6, and most questions about obfuscated
arithmetic at 7, in the simplifier. A check never runs longer than its budgets, and with a deadline
([`check_within`](https://docs.rs/bitwright/latest/bitwright/solve/struct.Solver.html#method.check_within))
not much longer than that.

## A session that lasts

A context grows with every expression built in it. A tool that asks millions of small
questions against a state that stays takes a checkpoint, and rolls back to it after each
question:

```rust
use bitwright::solve::{Solver, Status};
use bitwright::{Context, ParseOptions, Width};

let (mut cx, mut s) = (Context::new(), Solver::default());
let o = ParseOptions::width(Width::W32);
let path = cx.parse("x * 3 <u 100", &o)?;
s.assert(&cx, path)?;
let (base, size) = (cx.checkpoint(), cx.len());
for k in 0..100u32 {
    s.push();
    let q = cx.parse(&format!("(x ^ {k}) + {k} == 77"), &o)?;
    s.assert(&cx, q)?;
    assert!(!matches!(s.check(&mut cx)?, Status::Unknown(_)));
    s.pop(1)?;
    // Before the rollback: the solver forgets what it holds of the question.
    s.forget_since(base)?;
    cx.rollback(base)?;
}
assert_eq!(cx.len(), size);
# Ok::<(), bitwright::Error>(())
```

Handles created after a checkpoint must not be used after the rollback: see
[`Context::rollback`](https://docs.rs/bitwright/latest/bitwright/struct.Context.html#method.rollback).

The rollback also makes a question's answer the one a context of its own would give. What
the simplifier makes of an expression can depend on what the context was given before, where
the two share parts: always an equal expression, not always the same one. Asked between a
checkpoint and a rollback, each of 96 questions of a deobfuscator's log gets exactly the
result it gets alone, in either order; asked one after another without it, 12 of the 27 that
share parts do not.

## Answers that outlive the process

[`Answers`](https://docs.rs/bitwright/latest/bitwright/solve/struct.Answers.html) are what
checks answered, kept by what the questions are and not where they were asked: a solver that is
given them answers a question it has seen, in any context and any later run, from them. A model
from them is checked before it is used; an "unsatisfiable" is taken on the question's hashes,
and `decided_by` says `Remembered`. bitwright does no IO: the host keeps the text.

```rust
use bitwright::solve::{Answers, DecidedBy, Solver, Status};
use bitwright::{Context, ParseOptions, Width};

let o = ParseOptions::width(Width::W64);
let hard = "(x ^ y) + 2 * (x & y) + (x | z) - (x & z) - (x ^ z) != x + y";
let text = {
    let (mut cx, mut s) = (Context::new(), Solver::default().with_answers(Answers::new()));
    let e = cx.parse(hard, &o)?;
    s.assert(&cx, e)?;
    assert_eq!(s.check(&mut cx)?, Status::Unsat);
    s.answers().unwrap().to_text()
};
let (mut cx, mut s) =
    (Context::new(), Solver::default().with_answers(Answers::from_text(&text)?));
let e = cx.parse(hard, &o)?;
s.assert(&cx, e)?;
assert_eq!(s.check(&mut cx)?, Status::Unsat);
assert_eq!(s.decided_by(), Some(DecidedBy::Remembered));
# Ok::<(), bitwright::Error>(())
```

The simplifier has the same for its results
([`Remembered`](https://docs.rs/bitwright/latest/bitwright/engine/struct.Remembered.html),
[`Engine::run_remembering`](https://docs.rs/bitwright/latest/bitwright/engine/struct.Engine.html#method.run_remembering)):
an expression it has simplified, or a part of one that it took down to a few nodes, is replaced
by the result the next time it appears, whatever is around it.

## Rules while solving, and theorems from Lean

A solver given a simplifier of the host's
([`Config::simplifier`](https://docs.rs/bitwright/latest/bitwright/solve/struct.Config.html#structfield.simplifier))
runs it on what a check has left before the prover is asked, each conjunct under the ones
before it: the host's rules take part in solving. They may be theorems: `bitwright lean-rules`
reads `theorem` statements about `BitVec` from a Lean 4 file and writes them as a rule file,
refusing any whose proof is `sorry`, and with `--verify` only after `lean` has checked the file.

```text
$ cat theorems.lean
theorem udiv_mul_ule {w : Nat} (x y : BitVec w) (h : y != 0#w) :
    ((x / y) * y).ule x = true := by
  ...
$ bitwright lean-rules theorems.lean --verify > theorems.bwr
$ bitwright check theorems.bwr
$ bitwright solve --rules theorems.bwr question.smt2
```

That theorem (a quotient times its divisor does not pass the dividend) decides in a
millisecond a 64-bit question that z3, Bitwuzla and bitwright alone do not decide in twenty
seconds.

The other way, an unsatisfiable core is a theorem for Lean to prove again:
[`Solver::lean_theorem`](https://docs.rs/bitwright/latest/bitwright/solve/struct.Solver.html#method.lean_theorem)
(and `(get-proof)` in a script) writes it with the proof `by bv_decide`. The statement is the
conflicting assertions as given, so nothing of bitwright is in what Lean trusts. Lean proves
again what a circuit and a search can prove; what bitwright decided at the level of words (a
multiplication done limb by limb) it mostly does not.

## How an answer is known

[`Solver::tier`](https://docs.rs/bitwright/latest/bitwright/solve/struct.Solver.html#method.tier)
(in a script, `(get-info :tier)`) says which of these the last answer is:

| Answer | By | What it rests on |
|---|---|---|
| `Sat` | any stage | the model, checked by evaluation |
| `Unsat` | the kept circuit, the search | bitwright's circuit and SAT search; `lean_theorem` for an independent check |
| `Unsat` | the prover's simplifier | proved rules and passes that are decision procedures, and the limb-arithmetic pass, which commits what it derives without a proof. [`prove::Config::strict`](https://docs.rs/bitwright/latest/bitwright/prove/struct.Config.html#structfield.strict) (`solve --strict`) leaves that pass out, and `proved_words` (`solve --proved-words`) has it write only what a circuit and a search prove: of 24 hard limb questions the default decides 24, that 20, and `strict` 13 |
| `Unsat` | `Remembered` | an earlier answer, by the hashes of the question |

## A simplification that can be checked

An answer of the search has its clauses to show. A simplification has its steps:
[`Engine::derive`](https://docs.rs/bitwright/latest/bitwright/engine/struct.Engine.html#method.derive)
runs the engine and returns, with the result, a `Derivation`: every rewrite with the rule or
pass that made it and both sides as text, grouped into the stretches of the phases that ran.
`Derivation::check` then proves each step again without the engine: by polynomial
arithmetic, by the values of a linear MBA at the corners, or by the circuit and the search.
What it could not prove it lists, and `certified()` says whether the whole chain from the
expression to the result stands on proved steps alone.

```rust
use bitwright::engine::{Engine, Run, Strategy};
use bitwright::{Context, ParseOptions, Width};

let engine = Engine::builder().builtin().strategy(Strategy::deobfuscate()).build()?;
let mut cx = Context::new();
let e = cx.parse("(x ^ y) + 2 * (x & y) - y", &ParseOptions::width(Width::W64))?;
let (_, derivation) = engine.derive(&mut cx, e, Run::default())?;
assert_eq!(derivation.to, "x:64");
let checked = derivation.check(&bitwright::prove::Config::default())?;
assert!(checked.unproved.is_empty());
# Ok::<(), Box<dyn std::error::Error>>(())
```

On 12 simplification questions of the slow log, 97% of 8,297 steps are proved this way and
192 of 199 stretches are accounted for step by step, the opaque-constant sweep's among them
(it reports each subexpression it proves constant). No question is certified from end to
end yet: the nearest is one step and one stretch short, and what is left are steps of the MBA
passes that this check cannot follow. `Derivation::lean` writes the steps as Lean theorems.

With the feature `check`, `engine::learn` turns the steps passes made into rules: the
subexpressions both sides share become parameters, and a candidate is kept when the rule
checker finds it sound and it is proved at the widths asked about. The rules come with the
ledger an engine asks for. This is the narrow kind of memory: on the slow log, rules learned
from half of the questions matched 347 times in the other half and made nothing smaller or
faster, where remembering whole results ([above](#answers-that-outlive-the-process)) takes a
second pass to 8% of the first. It is there for a host whose passes are its own.

## Another search

bitwright's own SAT search has no dependency and is enough for what the word level leaves it.
For long searches the `bitwright-cadical` crate puts CaDiCaL behind
[`prove::Backend`](https://docs.rs/bitwright/latest/bitwright/prove/trait.Backend.html)
(`solve --cadical` in a build with the `cadical` feature): the solver's kept circuit is
searched by it, and after the prover's own short search it is given what the simplifier left.
