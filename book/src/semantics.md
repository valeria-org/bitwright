# Semantics

## Widths and values

A width is 1 to 512 bits. A value is an unsigned bit pattern of its width; operators that care
about sign (`sdiv`, `srem`, `>>s`, `<s`, `sext`, …) read it as two's complement. Operands of an
operator have the same width unless the operator says otherwise (extensions, extracts, concat,
select's 1-bit condition), and a width mismatch is an error, never a silent cast.

## Total semantics

Every operator is defined for every input, exactly as SMT-LIB QF_BV defines it:

| Operator | Result |
|-|-|
| `udiv(x, 0)` | all ones |
| `urem(x, 0)` | `x` |
| `sdiv(x, 0)` | `1` if `x <s 0`, else `-1` |
| `sdiv(smin, -1)` | `smin` |
| `srem(x, 0)` | `x` |
| `x << c`, `x >>u c` with `c ≥ W` | `0` |
| `x >>s c` with `c ≥ W` | the sign, in every bit |
| `rotl(x, c)`, `rotr(x, c)` | rotation by `c mod W` (any W) |
| `clz(0)`, `ctz(0)` | `W` |

Because there is no undefined behavior, equal handles always mean equal values, and every rule
is a closed statement a solver can check. A host that needs fault semantics (a division that
traps) builds the trap condition as its own expression; see `bitwright::traps`.

```rust
use bitwright::{BitVec, BinOp, Width};

let w = Width::new(12)?;
let smin = BitVec::smin(w);
let minus_one = BitVec::ones(w);
assert_eq!(BitVec::apply_bin(BinOp::SDiv, &smin, &minus_one)?, smin);
let big = BitVec::from_u64(w, 40)?;
assert!(BitVec::apply_bin(BinOp::Shl, &minus_one, &big)?.is_zero());
# Ok::<(), Box<dyn std::error::Error>>(())
```

## The text syntax

The parser and printer share one syntax. Unsigned and signed variants are always explicit:
`>>u` and `>>s`, `<u` and `<s`; a bare `>>` or `<` is an error. Widths are inferred where
possible and written with a colon where not (`0xff:8`, `x:64`); casts take their width in angle
brackets (`zext<32>(x)`, `trunc<8>(x)`, `extract<lo, len>(x)`).

```rust
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let e = cx.parse("select(x <s 0, -x, x) + zext<32>(trunc<8>(y))", &o)?;
let text = cx.display(e).to_string();
// Printing and parsing again gives the same node.
assert_eq!(cx.parse(&text, &o)?, e);
// A shift without its signedness is an error, not a guess.
assert!(cx.parse("x >> 1", &o).is_err());
# Ok::<(), bitwright::Error>(())
```

## Canonical form

Construction puts every node in a canonical form that does not depend on the order you built
things in or on which context you used: commutative operands are ordered by a structural key,
constants go right, all-constant subterms are folded, and a handful of identities that never
lose information (`x + 0`, `x & x`, double negation, …) are applied. Everything beyond that is
the simplifier's job, so construction stays cheap and predictable.

```rust
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
for (written, built) in [
    ("(y | x) + (x & y)", "(x & y) + (x | y)"), // commutative operands in one order
    ("5 + x", "x + 5"),                         // constants on the right
    ("x + 2 * 3", "x + 6"),                     // constant subterms folded
    ("~~x & x", "x"),                           // identities that lose nothing
    ("(x + 1) + 2", "x + 1 + 2"),               // not reassociated: the simplifier's job
] {
    let e = cx.parse(written, &o)?;
    assert_eq!(cx.display(e).to_string(), built);
}
# Ok::<(), bitwright::Error>(())
```
