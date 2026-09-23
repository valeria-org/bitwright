# Invertibility

Hash functions and mixers are usually chains of invertible steps: xor with a key, multiply by
an odd constant, rotate, a data-dependent xorshift. bitwright proves when an expression is an
*injective* or *bijective* function of one of its subexpressions, and the simplifier uses that
at equalities:

- **cancel**: `f(x) == f(y)` is `x == y` when `f` is injective (`!=` likewise);
- **move a constant across**: `f(x) == c` is `x == f⁻¹(c)`, or `false` when `c` has no
  preimage. A hash comparison becomes a plain equality.

Orderings are never touched: a bijection does not preserve them, so `f(x) <u c` says nothing
about `x`.

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

// A keyed mixer: F_K(v) = S((v ^ K) * K) * K, with S(h) = h ^ ((h >>u 32) >>u (h >>u 60)).
const K: &str = "0xd3220fb78e33751f";
let fk = |v: &str, k: &str| {
    let m = format!("(({v} ^ {k}) * {k})");
    format!("(({m} ^ (({m} >>u 32) >>u ({m} >>u 60))) * {k})")
};
let engine = Engine::standard();
let mut cx = Context::new();
let o = ParseOptions::width(Width::W64);
let mut simplify = |src: String| -> Result<String, bitwright::Error> {
    let e = cx.parse(&src, &o)?;
    let out = engine.simplify(&mut cx, e)?;
    Ok(cx.display(out.expr).to_string())
};
// Equal hashes under one key: equal inputs.
assert_eq!(simplify(format!("{} == {}", fk("x", K), fk("y", K)))?, "x == y");
// Solved at a constant: F_K(x) is 0 at exactly one input, the key.
assert_eq!(simplify(format!("{} == 0", fk("x", K)))?, "x == 0xd3220fb78e33751f");
// Two keys ored are 0 only where both are: at two different inputs, so never.
let two = format!("({} | {}) == 0", fk("x", K), fk("x", "0xfa173d6f19f30f7d"));
assert_eq!(simplify(two)?, "0:1");
// Feeding the input back in destroys injectivity: F_K(x) ^ x is not cancelled.
let mix = |v: &str| format!("({} ^ {v})", fk(v, K));
assert_ne!(simplify(format!("{} == {}", mix("x"), mix("y")))?, "x == y");
// Nothing about orderings.
assert!(simplify(format!("{} <u 0x1000", fk("x", K)))?.contains("<u"));
# Ok::<(), Box<dyn std::error::Error>>(())
```

The round trip `F_K⁻¹(F_K(x)) = x` needs no special support: the passes cancel it from the
middle out (`y * K * K⁻¹` is `y`, and `S(S(y))` is `y` once the demanded-bits pass sees that
`S` leaves bits 32 to 63 alone).

## Layers

An expression is read as a chain of *layers* from a subexpression up to its root. A layer is
one node that is an injective function of one operand when every other operand (a
*parameter*) is fixed:

| Layer | Kind |
|-|-|
| `~v`, `-v`, `bswap(v)`, `bitrev(v)` | bijective |
| `v + k`, `v - k`, `k - v`, `v ^ k`, `rotl(v, k)`, `rotr(v, k)`, any `k` | bijective |
| `v * k` with `k` proved odd (a constant, or known bits, or an assumption) | bijective |
| `zext(v)`, `sext(v)`, `concat(v, k)`, `concat(k, v)` | injective |
| an extension output declared invertible in an argument | as declared |
| `v ^ g(v)`, `v + g(v)`, `v - g(v)`, `g(v) - v`, when triangular (below) | bijective |

Composing layers keeps injectivity, so a chain of them is injective in its innermost value.
Cancelling needs the parameters to be the same on both sides (the same subexpressions): a map
injective for each fixed parameter can collide across two parameters. Moving a constant across
needs them to be constants, so the preimage is one.

A node combining two values that *both* depend on the inner one is not a layer in general,
even when each is a bijection: `f(x) ^ x`, `f_a(x) ^ f_b(x)` and `f_a(x) | f_b(x)` all
collide. The one exception is the triangular form.

## Triangular maps

In `v ^ g(v)`, `v + g(v)` or `v - g(v)`, the analysis computes, for every bit `i` of `g`, the
bits of `v` it can depend on: bitwise operators bit by bit, arithmetic from the bits below,
shifts and rotations re-indexed (by a variable count, over the count's range), and nothing for
the bits the facts pin. Those facts are computed with `v` unknown, so the answer holds for
every value of `v`, not just the ones it takes in context. Then:

- `v ^ g(v)` is a bijection when no bit depends on itself through `g`, directly or through
  other bits (the dependencies are acyclic): `v` is recovered in dependency order. This covers
  xorshift steps like `x ^ (x << 13)`, and the mixer's `S`, whose low half reads only the high
  half, which it leaves alone.
- `v ± g(v)` is a bijection when every bit of `g` depends only on lower bits of `v`: carries
  run upward only, so `v` is recovered from bit 0 up.

```rust
use bitwright::{Context, ParseOptions, Query, Truth, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::new(22)?);
let u = cx.parse("u", &o)?;
// Bit i of ((u << 1) | b) & h reads only bit i - 1 of u: a bijection of u, for every b and h.
let t = cx.parse("u - (((u << 1) | b) & h)", &o)?;
assert_eq!(cx.prove(Query::Bijective { e: t, of: u })?, Truth::True);
// Without the shift, bit i reads bit i: not proved (and not injective).
let t0 = cx.parse("u - ((u | b) & h)", &o)?;
assert_eq!(cx.prove(Query::Injective { e: t0, of: u })?, Truth::Unknown);
// Independent of `u`, or narrower than it: disproved.
let y = cx.parse("y * 3", &o)?;
assert_eq!(cx.prove(Query::Injective { e: y, of: u })?, Truth::False);
# Ok::<(), Box<dyn std::error::Error>>(())
```

`Query::Injective { e, of }` and `Query::Bijective { e, of }` answer the question for any
subexpression `of`, with every value that does not depend on it held fixed. Like every proof,
`True` is proved and `Unknown` is always possible; `False` is reserved for the cases with a
simple witness (`e` does not depend on `of`, or is narrower than it). Under
[assumptions](constraints.md) (`prove_under`), facts assumed about parameters count, and the
answer reports the constraints it relied on: `x * k` is a bijection of `x` wherever `k & 1 == 1`
is assumed.

The analysis looks at no more than 256 nodes of `g`, and at inner values of at most 128 bits;
larger layers are simply not recognized. Maps that are bijective for reasons it does not
model, such as a GF(2)-linear map with cyclic dependencies (`x ^ rotl(x, 5) ^ rotl(x, 9)` at
32 bits), are not recognized either.

## Knowing more about data-dependent shifts

`h ^ ((h >>u 32) >>u (h >>u 60))` shifts the high half by its own top four bits. When those
bits are `t`, the high half is at most `(t + 1) · 2^28 - 1`, and shifting it right by `t` keeps
it below `2^28`, so `S` changes only bits 0 to 27. The facts for a right shift by a value's own
top bits (`a >>u (a >>u k)`, however the two shifts are spelled) take this into account, so the
demanded-bits pass can drop `S` under any mask or shift that ignores the low 28 bits:

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W64);
let src = |n: u32| format!("let m = x * 0xd3220fb78e33751f; (m ^ ((m >>u 32) >>u (m >>u 60))) >>u {n}");
let e = cx.parse(&src(28), &o)?;
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "x * 0xd3220fb78e33751f >>u 28");
// One bit lower it would be wrong (S can change bit 27), and nothing happens.
let e = cx.parse(&src(27), &o)?;
assert!(!Engine::standard().simplify(&mut cx, e)?.changed);
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Extension operations

An [extension operation](extensions.md) declares, per output and argument, whether the output is
injective or bijective in that argument with the others fixed, and supplies the inverse at a
value. The declaration may depend on the known bits of the other arguments (a key known to be
odd, say). Registration checks both at sampled points: `invert` must recover the argument from
the output, and for a bijection find an argument for any value. The simplifier checks every
answer of `invert` by evaluation before using it.

```rust
use bitwright::engine::Engine;
use bitwright::ext::{ExtOp, ExtSig, Invertible, Registry};
use bitwright::{BinOp, BitVec, CmpOpExt, Context, ContextConfig, KnownBits, Width};
use std::sync::Arc;

/// `rotl(x ^ k, 7)`: a bijection of `x` for every `k`.
struct Scramble;
impl ExtOp for Scramble {
    fn name(&self) -> &str { "acme.scramble" }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [x, k] if x == k && x.bits() == 32 => Ok(ExtSig::new(&[("s", *x)])),
            _ => Err("two 32-bit operands".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let t = BitVec::apply_bin(BinOp::Xor, &args[0], &args[1]).unwrap();
        out[0] = BitVec::apply_bin(BinOp::RotL, &t, &BitVec::from_u64(Width::W32, 7).unwrap()).unwrap();
    }
    fn invertible(&self, _output: u8, arg: u8, _args: &[KnownBits]) -> Invertible {
        if arg == 0 { Invertible::Bijective } else { Invertible::No }
    }
    fn invert(&self, _output: u8, _arg: u8, args: &[BitVec], value: &BitVec) -> Option<BitVec> {
        let t = BitVec::apply_bin(BinOp::RotR, value, &BitVec::from_u64(Width::W32, 7).unwrap()).ok()?;
        BitVec::apply_bin(BinOp::Xor, &t, &args[1]).ok()
    }
}

let reg = Arc::new(Registry::builder().register(Scramble)?.build());
let mut cx = Context::with_registry(ContextConfig::default(), reg.clone());
let op = reg.id("acme.scramble").unwrap();
let (x, y, k) = (cx.symbol("x", Width::W32)?, cx.symbol("y", Width::W32)?, cx.symbol("k", Width::W32)?);
let (a, b) = (cx.ext(op, &[x, k])?[0], cx.ext(op, &[y, k])?[0]);
let e = cx.cmp(CmpOpExt::Eq, a, b)?;
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "x == y");
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Facts proved elsewhere

Some facts hold only on a finite domain and were proved by exhaustion elsewhere, for example
"below `2^32`, `F_A(x) ^ F_B(x)` equals the salt only at `x = 0`". Such a fact is a rule, guarded
by a fact predicate that proves the input fits:

```text
bitwright 1;

group eos.facts32 {
    rule fact00<W>(x: W) where W == 64 {
        FA(x) ^ FB(x) == 0xd734e14a2ead11b5 => x == 0
        if proves(x <=u 0xffffffff)
    }
}
```

(with `FA(x)` and `FB(x)` written out in full). The [checker](checking.md) cannot enumerate
`2^32` inputs and reports it inconclusive, so no ledger vouches for it: link it with
`EngineBuilder::unproven_program` and `allow_unproven(true)`, which states that you vouch for
it, and add its group with `Strategy::with_rule_groups`. It then fires only where the facts
prove `x <=u 0xffffffff` (a zero extension, a mask, or an assumption).
