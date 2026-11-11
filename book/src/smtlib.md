# SMT-LIB (feature `smtlib`)

bitwright's semantics are SMT-LIB's, so every expression has an exact QF_BV counterpart, and any
SMT-LIB 2.6 solver (z3, cvc5, bitwuzla, …) can evaluate it, check an equivalence, or prove a rule.

## Export

`smtlib::export` writes a `declare-const` per symbol and a `define-fun` per node (so sharing is
kept), then `root0`, `root1`, … for the roots. Operators QF_BV lacks (population count, leading
and trailing zeros, byte swap, bit reverse, `pdep`, `pext`, the high half of a product, rotation
by a variable count) are expanded exactly.

```rust
use bitwright::{Context, ParseOptions, Width, smtlib};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let a = cx.parse("(x ^ y) + 2 * (x & y)", &o)?;
let b = cx.parse("x + y", &o)?;
let script = smtlib::equivalence_query(&mut cx, a, b)?;
// `unsat` from a solver proves a = b at 32 bits.
assert!(script.ends_with("(assert (not (= root0 root1)))\n(check-sat)\n"));
# Ok::<(), bitwright::Error>(())
```

`smtlib::equivalence_query_under` does the same under [constraints](constraints.md). It asserts
the constraints a rewrite relied on (its `relies_on`), so `unsat` proves the rewrite wherever they
hold.

## Import

`smtlib::import` reads a QF_BV subset: declarations and definitions without parameters,
assertions, `let`, `ite`, `=`, `distinct`, the Boolean operators, every QF_BV operator, and
z3's rotations by a term (`ext_rotate_left`, `ext_rotate_right`). Booleans become 1-bit
expressions. A chain of `let`s, each in the body of the one before (z3 prints large terms so),
may be as long as the script: only other nesting is bounded. Arrays from bit-vectors to bit-vectors (QF_ABV) become
[memories](memory.md): `select` a load, `store` a store, resolved as the memory chapter
describes; arrays that are compared, chosen by `ite` or constant are read element by element
(see the session below). Anything else is an error, never a guess, and the
reader is iterative and bounded, so hostile input cannot exhaust the stack.

```rust
use bitwright::{Context, smtlib};

let mut cx = Context::new();
let script = smtlib::import(
    &mut cx,
    "(declare-const x (_ BitVec 8))
     (define-fun twice () (_ BitVec 8) (let ((t (bvadd x x))) t))
     (assert (bvult twice #x10))",
)?;
let twice = script.definition("twice").unwrap();
assert_eq!(cx.display(twice).to_string(), "x << 1");
assert_eq!(script.assertions.len(), 1);
# Ok::<(), bitwright::Error>(())
```

## Solving

With the `prove` feature, `smtlib::run` runs a script as a solver, on a
[`solve::Solver`](https://docs.rs/bitwright/latest/bitwright/solve/struct.Solver.html): the
importer's declarations, definitions and assertions, and `push`, `pop`, `check-sat`,
`check-sat-assuming`, `get-model`, `get-value`, `get-unsat-core`, `get-unsat-assumptions`,
`get-info`, `set-option`, `echo`, `reset`, `reset-assertions` and `exit`, each answered as the
standard prescribes. `bitwright solve` is the same from the shell:

```text
$ bitwright solve - <<'EOF'
(declare-const x (_ BitVec 64))
(assert (= (bvmul (bvxor x #xd3220fb78e33751f) #xd3220fb78e33751f) #x0000000000001234))
(check-sat)
(get-value (x))
(push)
(assert (! (bvult x #x0000000000010000) :named small))
(check-sat)
(get-unsat-core)
EOF
sat
((x #x5a01246bd1cb6653))
unsat
(small)
```

A check answers by the stages the chapter [Solving](solving.md) describes, on a circuit the
session keeps from one check to the next, and a core is sound but not minimal. Beyond the
quantifier-free theories the session reads:

- **Uninterpreted functions and sorts** a script declares: a symbol for each application and
  a constraint for each pair of them.
- **Arrays that are compared, chosen and constant**: `(= a b)` and `distinct` over arrays,
  `(ite c a b)`, `((as const (Array I E)) v)` and stores into any of them. An equality is a
  Boolean with the constraints of extensionality: an index where the two differ when it is
  false, agreement at every index the script reads or writes when it is true.
- **Quantifiers** where they can be decided by what is already there: an asserted `exists`
  and a denied `forall` take new symbols for their variables, at any width, and a quantifier
  anywhere else is read once for each value of its variables, up to 12 bits of them. A wider
  one is refused.

- **Bit-vectors above 512 bits**, up to 65,536: read as limbs of 256 bits, for the operators
  that are limb by limb (the bitwise ones, `ite`, `=`, `distinct`), a chain of carries
  (`bvadd`, `bvsub`, `bvneg`, the orders), a choice of limbs (shifts, rotations, `concat`,
  `extract`, the extensions, `repeat`), a sum of limb products (`bvmul`) or the schoolbook
  division (`bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod`: a circuit of as many steps as
  bits, which answers at values and is slow to reason about). A function, an array or a
  quantifier over them is refused. `get-model`
  and `get-value` print them whole. (A value of the library still holds 512 bits at most,
  so `smtlib::import` refuses them as before: it lists each name with one expression.)

A term that `get-value` or `check-sat-assuming` reads for the first time (an application, a
read of a compared array) is tied to the others before it is answered.

- **Integers where a bit-vector bounds them**: `(bv2nat x)`, numerals, sums, differences,
  products, `div` and `mod` by a constant that is not zero, comparisons, `ite` and
  `((_ int2bv n) i)`. Each is read as a bit-vector wide enough that nothing it computes
  wraps (up to 512 bits), so the arithmetic is the integers' own. A variable of sort `Int`
  has no such bound and is refused, as is a division by anything else.

A command that needs what is not read answers `(error "…")` and the script goes on. The 65 scripts this was measured on are answered as z3 and Bitwuzla
answer them.

## Rule obligations

`smtlib::rule_obligation(rule, widths)` states a rule's soundness at one width assignment: the
parameters are free, the guard is asserted, and the two sides are asserted to differ. It is
translated from the rule itself, not from expressions built through the canonicalizing
constructors, so nothing stands between the rule and the proof. `unsat` proves the rule at those
widths; `sat` comes with a counterexample. A rule with floating-point operations gives a
`QF_BVFP` script, and the assignment lists its rounding-mode parameters after the widths, each
as an index in `RoundingMode::ALL` (`bitwright smt` writes one obligation per mode).

```rust
use bitwright::rules::RuleProgram;
use bitwright::smtlib;

let src = "bitwright 1;
group g {
    #[allow(BW0407)]
    rule mask<W>(x: W, c: const W) { x & c => x if zero_bits(x, ~c) }
}";
let program = RuleProgram::compile(src).map_err(|e| e.to_string())?;
let rule = program.rule("g::mask").unwrap();
assert!(rule.admits(&[256]));
let script = smtlib::rule_obligation(rule, &[256]).map_err(|e| e.to_string())?;
assert!(script.contains("(declare-const |x| (_ BitVec 256))"));
# Ok::<(), String>(())
```

From the command line, `bitwright smt rules.bwr | z3 -in` (or `| bitwuzla`) prints one answer
per obligation; every answer must be `unsat`.

## Solvers

bitwright runs no other solver itself. Its nightly tests run every kind of script it writes
through both z3 and bitwuzla: exported expressions evaluated at random points, every built-in
rule proved at widths up to 512, simplification results proved equal to their inputs (with
extension calls as uninterpreted functions), and rewrites proved under the constraints they rely
on. Both read a script from standard input:

```text
bitwright smt rules.bwr | z3 -in
bitwright smt rules.bwr | bitwuzla
```

On the widest obligations (shifts and division at 256 bits) each gives up on a few, not always
the same ones. A per-query time limit is `-t:<ms>` for z3 and `--time-limit-per=<ms>` for
bitwuzla; either answers `unknown` when it runs out.
