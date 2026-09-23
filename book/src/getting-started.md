# Getting started

Add bitwright to `Cargo.toml`:

```toml
[dependencies]
bitwright = "0.3"
```

## Values

A `BitVec` is a value of a given `Width` (1 to 512 bits). Every operator is total:

```rust
use bitwright::{BinOp, BitVec, Width};

let x = BitVec::from_u64(Width::W8, 200)?;
let y = BitVec::from_u64(Width::W8, 100)?;
assert_eq!(BitVec::apply_bin(BinOp::Add, &x, &y)?.to_u64(), Some(44)); // modulo 2^8
let zero = BitVec::zero(Width::W8);
assert!(BitVec::apply_bin(BinOp::UDiv, &x, &zero)?.is_ones()); // x / 0 is all ones
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Expressions

Expressions live in a `Context`, an arena that owns them. An `Expr` is a small handle into it.
Equal expressions are the same node (hash-consing), and construction already puts them in a
canonical form, so building the same expression twice gives the same handle:

```rust
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let a = cx.parse("y + x", &o)?;
let b = cx.parse("x + y", &o)?;
assert_eq!(a, b);
// Construction canonicalizes and folds constants, but does not simplify further.
let c = cx.parse("(x - (2 + 3)) + 5", &o)?;
assert_eq!(cx.display(c).to_string(), "x - 5 + 5");
# Ok::<(), bitwright::Error>(())
```

You can also build expressions directly:

```rust
use bitwright::{BinOp, CmpOpExt, Context, UnOp, Width};

let mut cx = Context::new();
let x = cx.symbol("x", Width::W16)?;
let y = cx.symbol("y", Width::W16)?;
let sum = cx.bin(BinOp::Add, x, y)?;
let not_x = cx.un(UnOp::Not, x)?;
let less = cx.cmp(CmpOpExt::Ult, sum, not_x)?; // a 1-bit value
let picked = cx.select(less, sum, not_x)?;
let low = cx.trunc(picked, Width::W8)?;
assert_eq!(cx.width(low)?, Width::W8);
# Ok::<(), bitwright::Error>(())
```

Symbols are keyed by a name, a number or a fresh key, and each key has one width in a context.

## Evaluating

`eval` takes the values of the symbols from an environment, such as a map or a closure:

```rust
use std::collections::BTreeMap;
use bitwright::{BitVec, Context, ParseOptions, SymbolKey, Width};

let mut cx = Context::new();
let e = cx.parse("(x * 3) >>u 1", &ParseOptions::width(Width::W8))?;
let env: BTreeMap<SymbolKey, BitVec> =
    [(SymbolKey::from("x"), BitVec::from_u64(Width::W8, 100)?)].into_iter().collect();
assert_eq!(cx.eval(&[e], &env)?[0].to_u64(), Some(22)); // (300 mod 256) / 2
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Simplifying

The built-in simplifier is one call:

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let e = cx.parse("(x - 5) + 5 + (y & ~y)", &ParseOptions::width(Width::W32))?;
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "x");
# Ok::<(), bitwright::Error>(())
```

The chapter [Simplifying](simplifying.md) covers strategies, budgets and what the result tells
you.
