# Writing rules

Rules live in `.bwr` files: a header, then groups of rules and identities.

```text
bitwright 1;

group my.bitwise {
    /// Absorption.
    #[example("p & (p | q)" => "p")]
    rule and_absorb_or<W>(x: W, y: W) { x & (x | y) => x }

    /// A mask that keeps every bit x can have is redundant.
    #[example("(p & 0x0f) & 0xff" => "p & 0x0f")]
    rule and_mask_redundant<W>(x: W, c: const W) {
        x & c => x
        if zero_bits(x, ~c)
    }
}
```

## Rules

A `rule` rewrites left to right: `pattern => template`. It is generic over one to three width
variables (`<W>`, `<W, U>`), which may be constrained: `where W < U, U <= 2 * W`, or moduli such
as `W % 8 == 0`.

**Parameters** are declared with their width and what they may bind:

| Declaration | Binds |
|-|-|
| `x: W` | anything of width `W` |
| `c: const W` | only constants |
| `s: sym W` | only symbols |
| `n: nonconst W` | anything but constants |

The template may only use parameters that occur in the pattern.

**Literals** are typed from their context: `0`, `42`, `-1`, `0xff`, `true`, `false`, and the
rule-only literals `ones`, `zero`, `one`, `smin_lit`, `smax_lit`, `lowmask(N)` (the low `N` bits
set) and `bit(K)`. A width expression in value position (`W - 1`) is a literal of the inferred
width. A literal that does not fit at some admitted width is a compile error, never truncated.

**Guards** follow `if`, combined with `&&`, `||` and `!`:

- *fact predicates*, true only when the facts prove them: `zero_bits(x, m)` (every bit of the
  mask `m` is zero in `x`), `one_bits(x, m)`, `nonzero(x)`, `disjoint(x, y)` (no bit is one in
  both), and `proves(a op b)` for a comparison of parameters, literals and `let`s; on a
  float of a format, `fp.not_nan<E, S>(x)`, `fp.finite<E, S>(x)` (neither a NaN nor an
  infinity) and `fp.nonzero<E, S>(x)` (not a zero of either sign). Fact predicates cannot be
  negated: the facts can only prove, never refute.
- *constant predicates* on `const` parameters: `is_pow2`, `is_lowmask`, `is_shifted_mask`.
- *pure conditions*: comparisons and arithmetic over `const` parameters, literals and `let`s.

**Lets** compute constants from constant parameters when the rule matches:

```text
rule mul_pow2<W>(x: W, c: const W) {
    x * c => x << k
    if is_pow2(c)
    let k: W = ctz(c)
}
```

## Termination

Every `rule` must make its input strictly smaller in a fixed termination order (a Knuth-Bendix
order over the canonical form), and must not duplicate a variable more often than the pattern
has it. The compiler checks this, so no set of rules can loop. A rewrite that does not decrease
is an `identity`.

## Identities

```text
identity mul_add<W>(x: W, y: W, z: W) { x * (y + z) <=> x * y + x * z }
```

An identity is an unconditional equation: no guard, no `let`, no capture kinds, every parameter
on both sides. The directed engine uses it left to right only if that direction decreases the
order; the [equality-saturation search](eqsat.md) uses identities in both directions.

## Floating point

Rules can rewrite [floating-point](floating-point.md) operations. They are written as in the
text syntax, with the format as width expressions: `fp.mul.rne<E, S>(x, y)` is a product in the
format with `E` exponent and `S` significand bits, whose operands have width `E + S`; a named
format (`fp.mul.rne.f32(x, y)`) needs no width variables. A rounding-mode parameter, declared
`r: rm`, stands for all five modes: the pattern binds it from the node it matches
(`fp.mul.r<E, S>(…)`), and the template can use it. A rule has at most two.

Constants are written `fp.zero`, `fp.nzero` (−0), `fp.inf`, `fp.ninf`, `fp.nan`, `fp.one`,
`fp.none` (−1), `fp.two`, `fp.half`, `fp.min_normal`, `fp.min_subnormal` and `fp.max` (the
largest finite value), each with its format: `fp.one<E, S>`, `fp.inf.f64`. The operations the
builder makes from other operators (`fp.neg`, `fp.abs`, `fp.copysign`, `fp.sub`, `fp.gt`,
`fp.ge` and the tests `fp.isnan` …) are written out as the builder writes them, so a pattern
of them matches what it builds. They have no floating-point node of their own, so a pattern
whose format is generic must also contain an operation that is one (it binds `E` apart from
`S`), or name its format. x87's load and store are not available in rules.

The fact predicates on floats let a rule use an identity that holds only on ordinary numbers:
`x · 1` is `x` except for a NaN operand (whose payload the product drops), so

```text
rule mul_one<E, S>(x: E + S, r: rm) {
    fp.mul.r<E, S>(x, fp.one<E, S>) => x
    if fp.not_nan<E, S>(x)
}
```

rewrites `fp.mul.rtz.f64(fp.from_sbv.rne.f64(i), 1.0)`, whose operand the facts know is no NaN,
and leaves `x · 1.0` of an unknown `x` alone.

```rust
use bitwright::check::{CheckConfig, Verdict, check_program};
use bitwright::rules::RuleProgram;

let src = "bitwright 1;
group float {
    /// A square is never negative: the sign of a product of equal signs is clear, and a NaN
    /// result is the canonical one.
    #[example(\"fp.abs.f64(fp.mul.rtz.f64(x:64, x:64))\" => \"fp.mul.rtz.f64(x:64, x:64)\")]
    rule abs_square<E, S>(x: E + S, r: rm) {
        fp.abs<E, S>(fp.mul.r<E, S>(x, x)) => fp.mul.r<E, S>(x, x)
    }

    /// Wrong: x · 1 is x only on values, a NaN operand's payload is lost.
    #[allow(BW0407)]
    rule mul_one<E, S>(x: E + S, r: rm) { fp.mul.r<E, S>(x, fp.one<E, S>) => x }
}";
let program = RuleProgram::compile(src).map_err(|e| e.render("float.bwr", src))?;
let checks = check_program(&program, &CheckConfig::default());
assert!(checks[0].is_sound() && checks[0].examples.is_empty());
let Verdict::Unsound(cx) = &checks[1].verdict else { panic!() };
// E = 2, S = 2, r = rne; x = 0xf:4: lhs = 0x7:4, rhs = 0xf:4 (−NaN becomes the NaN)
assert_eq!(cx.lhs.to_u64(), Some(0x7));
# Ok::<(), String>(())
```

The [checker](checking.md) checks a floating-point rule in every format whose widths it
enumerates exhaustively (`E` and `S` up to 6, which is where formats are strangest) and at
sampled wider ones, under every rounding mode of its mode parameters. It finds what holds
almost everywhere: rounding a value to an integral one and then converting it to an integer
is not the same as converting it directly in a format such as `(2, 3)`, where 3.5 rounds to 4,
which is past the largest finite value, so the rule needs `where S <= E` (a format in which
every value with a large enough exponent is an integer).

## Attributes and diagnostics

`/// doc comments` and `#[example("input" => "output")]` document a rule; examples are checked
by the checker. `#[allow(BW0402)]` and `#[allow(BW0407)]` silence the two allowable lints (an
unreachable pattern, a missing example); errors cannot be allowed. Every diagnostic has a stable
code; `bitwright explain BW0302` (or `rules::explain`) says what it means.

```rust
use bitwright::rules::{Level, RuleProgram};

let src = "bitwright 1;
group demo {
    #[example(\"p & (p | q)\" => \"p\")]
    rule absorb<W>(x: W, y: W) { x & (x | y) => x }
    rule no_example<W>(x: W, y: W) { x | (x & y) => x }
}";
let program = RuleProgram::compile(src).map_err(|e| e.render("demo.bwr", src))?;
assert_eq!(program.rules().len(), 2);
assert_eq!(program.rule("demo::absorb").unwrap().params.len(), 2);
// A note for the missing example, with its code and position.
let d = &program.diagnostics()[0];
assert_eq!((d.code, d.level), ("BW0407", Level::Note));

// A rule that could loop is rejected.
let looping = "bitwright 1;\ngroup g {\n    rule r<W>(x: W) { x => x + 0 }\n}\n";
let err = RuleProgram::compile(looping).unwrap_err();
assert!(err.render("g.bwr", looping).contains("BW0302"));
# Ok::<(), String>(())
```

The built-in rules are listed in the [rule catalog](catalog.md).
