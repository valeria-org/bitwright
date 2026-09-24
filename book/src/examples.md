# Examples

Worked examples, one task each, in the order a reverse engineer tends to meet them: code an
obfuscator made unreadable, conditions a lifter spelled out from flags, values a compiler
shuffled, floating point, and what to do with the results. Every one is a complete program that
runs as a test; the chapters they point to explain the machinery.

Most examples use one of two engines:

- `Engine::standard()`: the built-in rules and the normal-form passes. Fast, and enough for
  anything that is not mixed boolean-arithmetic.
- The deobfuscation engine, what the command line's `simplify` runs: the deobfuscation strategy
  and the MBA service with bitwright's own normal-form solver, taking only answers bitwright can
  prove itself (see [Deobfuscation and MBA](deobfuscation.md)).

## Undoing mixed boolean-arithmetic

Obfuscators replace an operation with an identity that mixes arithmetic and bitwise logic. The
deobfuscation engine reads such expressions as functions of their bits and brings them back,
linear ones, ones with constants inside the bitwise parts, and products:

```rust
use std::sync::Arc;
use bitwright::engine::{Engine, Strategy};
use bitwright::mba::{MbaConfig, MbaTrust, NormalFormSolver};
use bitwright::{Context, ParseOptions, Width};

// The command line's `simplify`: answers are published only on bitwright's own proof.
let engine = Engine::builder()
    .builtin()
    .strategy(Strategy::deobfuscate().with_mba(
        MbaConfig::default().with_trust(MbaTrust::default().with_backend_certificates(false)),
    ))
    .mba_solver(Arc::new(NormalFormSolver::default()))
    .build()?;
let mut cx = Context::new();
let o = ParseOptions::width(Width::W64);
for (obfuscated, plain) in [
    ("(x ^ y) + 2 * (x & y)", "x + y"),
    ("(x + y) - 2 * (x & y)", "x ^ y"),
    ("(x & ~y) - (~x & y)", "x - y"),
    ("(x ^ 0x10) + 2 * (x & 0x10)", "x + 16"),
    ("3 * (x & 0x55) + 3 * (x & 0xaa)", "(x & 255) * 3"),
    ("(x & y) * (x | y) + (x & ~y) * (~x & y)", "x * y"),
] {
    let e = cx.parse(obfuscated, &o)?;
    let out = engine.simplify(&mut cx, e)?;
    assert_eq!(cx.display(out.expr).to_string(), plain, "{obfuscated}");
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Encoded constants and arithmetic

Constants are hidden behind multiplications by an odd number and its inverse, complements that
cancel, and terms that add up to nothing. The standard engine folds them; no MBA solver is
needed:

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

let engine = Engine::standard();
let simplify = |src: &str, w: Width| -> Result<String, bitwright::Error> {
    let mut cx = Context::new(); // a symbol has one width in a context
    let e = cx.parse(src, &ParseOptions::width(w))?;
    let out = engine.simplify(&mut cx, e)?;
    Ok(cx.display(out.expr).to_string())
};
// 7 · 183 = 1281 = 1 (mod 256): multiplying by 7 and then by 183 is multiplying by 1.
assert_eq!(simplify("x * 7 * 183", Width::W8)?, "x");
// `a ^ 0xffff` is `~a` at 16 bits, and `~a` is `−a − 1`: the constants cancel.
assert_eq!(simplify("((x + 0x1234) ^ 0xffff) + 0x1235 + (x ^ 0xffff) + 1", Width::W16)?, "x * -2");
// A term, twice, minus twice the term.
assert_eq!(simplify("(x ^ 0x5a5a5a5a) + (x ^ 0x5a5a5a5a) - 2 * (x ^ 0x5a5a5a5a)", Width::W32)?, "0:32");
# Ok::<(), bitwright::Error>(())
```

## Opaque predicates and dead code

An opaque predicate is a condition the obfuscator knows the value of, which guards a branch
that never runs. When the value follows from which bits of the operands are known, or from their
ranges, facts decide it and the simplifier folds it; `Context::prove` answers the question
without rewriting anything:

```rust
use bitwright::engine::Engine;
use bitwright::{CmpOpExt, Context, ParseOptions, Query, Truth, Width};

let engine = Engine::standard();
let mut cx = Context::new();
let o = ParseOptions::width(Width::W8);
for (predicate, value) in [
    ("((x | 1) & 1) == 1", "1:1"), // an odd number is odd
    ("(x | 0x80) >u 0x7f", "1:1"), // with the top bit set, above 127
    ("(x & 0x0f) + 1 == 0", "0:1"), // at most 16
    ("((x * 4) & 3) != 0", "0:1"), // a multiple of 4 has no low bits
] {
    let e = cx.parse(predicate, &o)?;
    let out = engine.simplify(&mut cx, e)?;
    assert_eq!(cx.display(out.expr).to_string(), value, "{predicate}");
}
// Asked directly: the bits a shift pushed out are gone.
let dead = cx.parse("(x & 0x0f) >>u 4", &o)?;
assert_eq!(cx.prove(Query::IsZero(dead))?, Truth::True);
let low = cx.parse("x & 0x0f", &o)?;
let sixteen = cx.parse("16", &o)?;
assert_eq!(cx.prove(Query::Cmp(CmpOpExt::Ult, low, sixteen))?, Truth::True);
# Ok::<(), bitwright::Error>(())
```

## Conditions from lifted flags

A lifter turns a compare-and-branch into the flags the instruction sets and the condition the
branch tests. For a signed `jl` after `cmp a, b` that is `SF != OF`, with the sign flag and the
overflow flag of the subtraction written out bit by bit; the simplifier brings back the
comparison. Range checks that a compiler emitted for a `switch` combine into one:

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

let engine = Engine::standard();
let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
for (lifted, condition) in [
    // SF ^ OF, both as bit 31 of an expression.
    ("((a - b) >>u 31) ^ (((a ^ b) & (a ^ (a - b))) >>u 31)", "zext<32>(a <s b)"),
    // The same with the text syntax's overflow operator.
    ("(a - b <s 0) != ssub_overflow(a, b)", "a <s b"),
    // `case 4 ... 9:` and `case 10:` of a switch.
    ("(x - 4 <=u 5) | (x == 10)", "x - 4 <=u 6"),
] {
    let e = cx.parse(lifted, &o)?;
    let out = engine.simplify(&mut cx, e)?;
    assert_eq!(cx.display(out.expr).to_string(), condition, "{lifted}");
}
# Ok::<(), bitwright::Error>(())
```

Floating-point comparisons set the flags too: after `ucomiss x, y`, ZF is "equal or
unordered", PF "unordered" and CF "less or unordered", and `ja` tests `!CF & !ZF`. The
comparisons combine as floats, NaNs included:

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let unordered = "(fp.isnan.f32(x) | fp.isnan.f32(y))";
let cf = format!("(fp.lt.f32(x, y) | {unordered})");
let zf = format!("(fp.eq.f32(x, y) | {unordered})");
let e = cx.parse(&format!("~{cf} & ~{zf}"), &o)?; // ja
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "fp.lt.f32(y, x)");
let e = cx.parse(&format!("{cf} | {zf}"), &o)?; // jbe
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "~fp.lt.f32(y, x)");
# Ok::<(), bitwright::Error>(())
```

## Shuffled bits

Values taken apart and put back, and shifts that only clear bits, come back as the one
operation they are:

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

let engine = Engine::standard();
let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
for (shuffled, plain) in [
    ("(x << 8) | (x >>u 24)", "rotl(x, 8)"),
    ("(x >>u 3) << 3", "x & -8"),
    ("trunc<8>(zext<32>(b:8) + 256)", "b"),
] {
    let e = cx.parse(shuffled, &o)?;
    let out = engine.simplify(&mut cx, e)?;
    assert_eq!(cx.display(out.expr).to_string(), plain, "{shuffled}");
}
# Ok::<(), bitwright::Error>(())
```

The deobfuscation strategy traces bits through extracts, shifts and masks as well, and
recognizes byte swaps and extensions (see [Deobfuscation and MBA](deobfuscation.md)).

## Hash comparisons

A license check compares a keyed hash of the input with a constant. Each step of the hash is
invertible, so the comparison is one of the input with the constant's preimage (see
[Invertibility](invertibility.md)):

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let e = cx.parse("((x ^ 0x5a) * 0x1d) == 0x33", &ParseOptions::width(Width::W8))?;
let out = Engine::standard().simplify(&mut cx, e)?;
// (0xd5 ^ 0x5a) · 0x1d = 0x33 (mod 256), and no other input hashes to 0x33.
assert_eq!(cx.display(out.expr).to_string(), "x == -43");
# Ok::<(), bitwright::Error>(())
```

## Floating point

Floats are bit-vectors holding their encodings (see [Floating point](floating-point.md)).
Construction applies what holds bit for bit, facts read encodings as sets of floats, and the
built-in floating-point rules apply identities on numbers where the facts show an operand is no
NaN:

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

let engine = Engine::standard();
let mut cx = Context::new();
let o = ParseOptions::width(Width::W64);
for (float, plain) in [
    // An integer converted to a float is never a NaN.
    ("fp.isnan.f64(fp.from_sbv.rne.f64(i:32))", "0:1"),
    // ... so multiplying it by 1.0 changes nothing.
    ("fp.mul.rne.f64(fp.from_sbv.rne.f64(i:32), 0x3ff0000000000000)", "fp.from_sbv.rne.f64(i)"),
    // Dividing by 4.0 is multiplying by 0.25, exactly.
    ("fp.div.rne.f64(x, 0x4010000000000000)", "fp.mul.rne.f64(x, 0x3fd0000000000000)"),
    // A 16-bit integer survives a round trip through binary64.
    ("fp.to_sbv.rtz.f64<32>(fp.from_sbv.rne.f64(j:16))", "sext<32>(j)"),
    // Every encoding is in one of the five classes.
    ("fp.isnan.f64(x) | fp.isinf.f64(x) | fp.iszero.f64(x) | fp.isnormal.f64(x) \
      | fp.issubnormal.f64(x)", "1:1"),
] {
    let e = cx.parse(float, &o)?;
    let out = engine.simplify(&mut cx, e)?;
    assert_eq!(cx.display(out.expr).to_string(), plain, "{float}");
}
# Ok::<(), bitwright::Error>(())
```

`x · 1.0` of an unknown `x` stays: for a NaN with a payload the product is the canonical NaN, a
different bit pattern.

## Under path constraints

On a path through a function, the branches taken so far constrain the values. `Assumptions`
carries them, and each result says which of them it relied on, so it is used only where they
hold (see [Constraints](constraints.md)):

```rust
use bitwright::engine::{Engine, Run};
use bitwright::{Assumptions, Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let mut path = Assumptions::new();
let bounded = cx.parse("x <u 16", &o)?; // after `cmp x, 16; jae skip`, not taken
let three = cx.parse("y == 3", &o)?;
let b = path.assume_true(&mut cx, bounded)?;
let t = path.assume_true(&mut cx, three)?;

let e = cx.parse("(x & 0xf0) + y * x", &o)?;
let out = Engine::standard().run(&mut cx, &[e], Run::default().with_assumptions(&path))?;
let r = out.roots[0];
assert_eq!(cx.display(r.expr).to_string(), "x * 3");
assert!(r.relies_on.may_use(b) && r.relies_on.may_use(t));
// Without them, nothing is known.
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "x * y + (x & 240)");
# Ok::<(), bitwright::Error>(())
```

## A rule of your own

When a target has an idiom of its own, write it as a rule, check it, and link it with the
ledger the check produces (see [Writing rules](rules.md) and [Checking rules](checking.md)).
A guard can ask the facts: this rule drops a shift pair whose low bits are known to be zero:

```rust
use bitwright::check::{CheckConfig, check_program};
use bitwright::engine::Engine;
use bitwright::rules::{Ledger, RuleProgram};
use bitwright::{Context, ParseOptions, Width};

let src = "bitwright 1;
group my.idioms {
    /// Shifting right and back left clears the low bits; when they are zero already, it
    /// changes nothing.
    #[example(\"((p & 0xf0) >>u 4) << 4\" => \"p & 0xf0\")]
    rule shift_pair_known_zero<W>(x: W, c: const W) {
        (x >>u c) << c => x
        if zero_bits(x, m)
        let m: W = (one << c) - 1
    }
}";
let program = RuleProgram::compile(src).map_err(|e| e.render("idioms.bwr", src))?;
let checks = check_program(&program, &CheckConfig::default());
assert!(checks.iter().all(|c| c.is_sound() && c.examples.is_empty()));
let ledger = Ledger::from_checks(&checks);

// Only this rule, to show it at work.
let engine = Engine::builder().program(program, &ledger).build().map_err(|e| e.to_string())?;
let mut cx = Context::new();
let e = cx.parse("((r & 0xffff0000) >>u 16) << 16", &ParseOptions::width(Width::W32))
    .map_err(|e| e.to_string())?;
let out = engine.simplify(&mut cx, e).map_err(|e| e.to_string())?;
assert_eq!(cx.display(out.expr).to_string(), "r & -65536");
# Ok::<(), String>(())
```

## Many expressions at once

An analysis simplifies many expressions that share subterms. `Engine::run` takes them together;
work on a shared subterm is done once, and results are remembered in the context, so asking
again costs nothing:

```rust
use bitwright::engine::{Engine, Run};
use bitwright::{Context, ParseOptions, Width};

let engine = Engine::standard();
let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let roots = [
    cx.parse("((a ^ b) + 2 * (a & b)) & 0xff", &o)?,
    cx.parse("((a ^ b) + 2 * (a & b)) >>u 24", &o)?,
    cx.parse("(a ^ b) + 2 * (a & b) == 0", &o)?,
];
let out = engine.run(&mut cx, &roots, Run::default())?;
let shown: Vec<String> = out.roots.iter().map(|r| cx.display(r.expr).to_string()).collect();
assert_eq!(shown, ["a + b & 255", "a + b >>u 24", "a + b == 0"]);
// The same roots again: answered from the context's memory.
let again = engine.run(&mut cx, &roots, Run::default())?;
assert!(again.stats.memo_hits > 0);
# Ok::<(), bitwright::Error>(())
```

## Handing results to a solver

A result can be checked independently: `smtlib::equivalence_query` writes an SMT-LIB script that
asserts the input and the result differ, which any solver answers `unsat` if they are equal. And
a script from another tool reads back into a context (see [SMT-LIB](smtlib.md)):

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width, smtlib};

let mut cx = Context::new();
let e = cx.parse("(x | y) - (x & y)", &ParseOptions::width(Width::W32))?;
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "x ^ y");
let query = smtlib::equivalence_query(&mut cx, e, out.expr)?;
assert!(query.contains("(check-sat)")); // `z3 -in` or `bitwuzla` answers `unsat`

// A term from another tool, simplified.
let script = "(declare-const a (_ BitVec 16))
(declare-const b (_ BitVec 16))
(define-fun t () (_ BitVec 16) (bvadd (bvxor a b) (bvmul #x0002 (bvand a b))))";
let t = smtlib::import(&mut cx, script)?.definition("t").expect("t");
let out = Engine::standard().simplify(&mut cx, t)?;
assert_eq!(cx.display(out.expr).to_string(), "a + b");
# Ok::<(), bitwright::Error>(())
```

The same operations are in the C, C++ and Python bindings; [Examples in Python, C and
C++](examples-bindings.md) has examples in each.
