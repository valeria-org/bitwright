# Constraints

A *constraint* is something you guarantee about the values that occur: a branch condition on
the path being analysed, an ABI invariant, a division known not to fault. It restricts values and
never changes what an operator means. So every proof made under constraints is still a proof,
valid wherever those constraints hold, and the simplifier can use them to fire guarded rules and
fold what they imply.

`Assumptions` holds a set of constraints. There are two kinds:

- `assume_true(p)` and `assume_false(p)` take a 1-bit predicate: `idx <u n` after a `jb` that was
  taken, `(rsp & 15) == 0` at a call boundary, `!trap` on a path that does not fault.
- `assume(e, facts)` states known bits or ranges of any expression directly.

Each call returns the constraint's `ConstraintId`, which is its position, counting from 0.

```rust
use bitwright::engine::{Engine, Run};
use bitwright::{Assumptions, Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W64);
let mut a = Assumptions::new();
let aligned = cx.parse("(rsp & 15) == 0", &o)?;
let taken = cx.parse("idx <u n", &o)?;
let abi = a.assume_true(&mut cx, aligned)?;
let path = a.assume_true(&mut cx, taken)?;

let e = cx.parse("((rsp + 32) & 15) + zext<64>(idx <=u n)", &o)?;
let out = Engine::standard().run(&mut cx, &[e], Run::default().with_assumptions(&a))?;
let r = out.roots[0];
assert_eq!(r.expr, cx.parse("1", &o)?);
// The result relies on both constraints.
assert!(r.relies_on.may_use(abi) && r.relies_on.may_use(path));
# Ok::<(), bitwright::Error>(())
```

## Propagation

Adding a constraint propagates it, within a fixed number of steps.

**Backwards to the operands.** A constraint on an expression gives facts about its operands:

- `(rsp & 15) == 0` makes the low four bits of `rsp` known to be zero;
- `x + 8 <u 64` bounds `x`;
- `zext<32>(b) == 0x41` makes `b` exactly `0x41`;
- `ctz(m) == 3` makes the low four bits of `m` exactly `1000`;
- `p && q` assumed true makes both true, and `p || q` assumed false makes both false.

Every backward transfer is checked exhaustively at small widths, like the forward ones.

**Between comparisons of the same two expressions.** Assuming `x <u y` also decides:

- `x <=u y` (true),
- `x == y` (false),
- `y <u x` (false).

This holds for every expression over the pair, not just the one assumed. It works for any two
expressions, not only constants, and the propagation also bounds each side by the other's range.
Equalities are transitive: after `x == y` and `y == z`, the constraint `x != z` is a
contradiction, and `y <u w` decides `x <u w`.

Constraints that contradict each other make the set *infeasible*, and `conflict()` names the
constraints involved. An infeasible set would justify any rewrite, so the simplifier ignores it: it
simplifies as it would with no constraints, and reports that nothing relies on them. The one place
it matters is `prove_under`, which answers `True` (anything holds where nothing can) and reports the
conflicting constraints as what the answer relies on.

```rust
use bitwright::{Assumptions, Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W8);
let mut a = Assumptions::new();
let lo = cx.parse("x <u 5", &o)?;
let hi = cx.parse("x >u 7", &o)?;
let first = a.assume_true(&mut cx, lo)?;
let second = a.assume_true(&mut cx, hi)?;
let conflict = a.conflict().unwrap();
assert!(conflict.may_use(first) && conflict.may_use(second));
# Ok::<(), bitwright::Error>(())
```

## What a result relies on

Every `RootOutcome` reports `relies_on`, a `Reliance`: the constraints that the rewrites
producing the result relied on.

- An empty reliance means the result holds everywhere.
- Otherwise the result holds wherever the constraints it relies on hold.

This matters when the scope of a constraint is narrower than the use of the result. Put the
invariants that hold everywhere (ABI rules, facts about the whole program) first, and the path
conditions after them. Then `relies_on.all_before(first_path_id)` tells you whether a rewrite can
be committed outside the path.

`Reliance` over-approximates: it may name a constraint that was not really needed, but it never
misses one. `may_use(id) == false` and `all_before(id) == true` are therefore definite. Constraints
from the 64th on are tracked together.

`Context::prove_under` answers a `Query` together with what the answer relies on, and
`Context::facts_under` gives an expression's facts together with theirs.

## Forking

Cloning an `Assumptions` is cheap: clones share their contents until one of them changes. A
symbolic executor can build the invariants once and extend a clone per path. Constraints keep
their ids in every clone, so the `ConstraintId`s of the invariants mean the same thing in every
path.

```rust
use bitwright::engine::{Engine, Run};
use bitwright::{Assumptions, Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W16);
let mut invariants = Assumptions::new();
let aligned = cx.parse("(sp & 15) == 0", &o)?;
invariants.assume_true(&mut cx, aligned)?; // constraint 0 in every path
let cond = cx.parse("x == 7", &o)?;
let mut taken = invariants.clone();
let mut not_taken = invariants.clone();
let t = taken.assume_true(&mut cx, cond)?;
not_taken.assume_false(&mut cx, cond)?;

let e = cx.parse("zext<16>(x == 7)", &o)?;
let engine = Engine::standard();
let on_taken = engine.run(&mut cx, &[e], Run::default().with_assumptions(&taken))?.roots[0];
let on_not_taken = engine.run(&mut cx, &[e], Run::default().with_assumptions(&not_taken))?.roots[0];
assert_eq!(on_taken.expr, cx.parse("1", &o)?);
assert_eq!(on_not_taken.expr, cx.parse("0", &o)?);
// It relies on the path condition, so it holds only on that path.
assert!(!on_taken.relies_on.all_before(t));
// This one relies only on the invariant, so it holds on every path.
let slot = cx.parse("(sp + 16) & 15", &o)?;
let r = engine.run(&mut cx, &[slot], Run::default().with_assumptions(&taken))?.roots[0];
assert_eq!(r.expr, cx.parse("0", &o)?);
assert!(r.relies_on.all_before(t));
# Ok::<(), bitwright::Error>(())
```

The simplifier's memo is keyed by the exact constraint set, so results never leak between paths.

## Faults and undefined values

bitwright's division is total, so a host that models a faulting division describes the fault
with a trap guard (`traps::udiv`, `traps::sdiv`, and so on). On a path that does not fault, assume
the guard false:

```rust
use bitwright::{Assumptions, Context, ParseOptions, Query, Truth, Width, traps};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let (q, d) = (cx.parse("q", &o)?, cx.parse("d", &o)?);
let trap = traps::udiv(&mut cx, q, d)?;
let mut a = Assumptions::new();
let no_fault = a.assume_false(&mut cx, trap)?;
let p = cx.prove_under(Query::IsNonZero(d), &a)?;
assert_eq!(p.truth, Truth::True);
assert!(p.relies_on.may_use(no_fault));
# Ok::<(), bitwright::Error>(())
```

A value an ISA leaves undefined, such as a flag after some instructions, needs no constraint.
Model it as a fresh symbol: nothing is known about it, and that is exactly what the ISA
guarantees.

## Checking a rewrite with a solver

With feature `smtlib`, `smtlib::equivalence_query_under(cx, before, after, &a, relies_on)` writes
a script that asserts exactly the constraints the rewrite relied on. A solver's `unsat` then
proves the rewrite valid wherever those constraints hold, independently of bitwright.
