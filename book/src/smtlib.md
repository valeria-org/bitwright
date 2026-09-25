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
assertions, `let`, `ite`, `=`, `distinct`, the Boolean operators, and every QF_BV operator.
Booleans become 1-bit expressions. Arrays from bit-vectors to bit-vectors (QF_ABV) become
[memories](memory.md): `select` a load, `store` a store, resolved as the memory chapter
describes (equality of arrays is refused). Anything else is an error, never a guess, and the
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
assert_eq!(cx.display(twice).to_string(), "x + x");
assert_eq!(script.assertions.len(), 1);
# Ok::<(), bitwright::Error>(())
```

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

bitwright never runs a solver itself. Its nightly tests run every kind of script it writes
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
