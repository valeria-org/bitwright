# Facts and proofs

For any expression, `Context::facts` returns what bitwright knows about its value without
knowing the symbols: known bits, an unsigned strided interval (the values `lo`, `lo + stride`,
…, `hi`) and a signed range, combined so that each part tightens the others. Facts are always
sound: every value the expression can take lies within them.

```rust
use bitwright::{Context, ParseOptions, Width};

let mut cx = Context::new();
let e = cx.parse("(x << 4) | 3", &ParseOptions::width(Width::W8))?;
let f = cx.facts(e)?;
// The low four bits are known: 0011.
assert_eq!(f.known().known().to_u64(), Some(0x0f));
assert_eq!(f.known().known_one().to_u64(), Some(0x03));
assert_eq!(f.urange().lo().to_u64(), Some(3));
# Ok::<(), bitwright::Error>(())
```

The stride carries what arithmetic keeps. `(x & 7) * 3 + 1` takes the values 1, 4, 7, …, 22, so
it is never 5, although 5 lies between its bounds; and known bits and the interval tighten each
other both ways (an odd value between 4 and 10 is between 5 and 9, and a stride of 4 fixes the two
low bits):

```rust
use bitwright::{BitVec, Context, ParseOptions, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W32);
let e = cx.parse("(x & 7) * 3 + 1", &o)?;
let u = cx.facts(e)?.urange();
assert_eq!((u.lo().to_u64(), u.hi().to_u64(), u.stride()), (Some(1), Some(22), 3));
let q = cx.parse("(x & 7) * 3 + 1 == 5", &o)?;
assert_eq!(cx.exact(q)?, Some(BitVec::from_bool(false)));
# Ok::<(), bitwright::Error>(())
```

Facts are computed on demand, iteratively (no recursion, so deep expressions are fine), and
cached per node for the life of the context. Each query is bounded by a work cap
(`ContextConfig::fact_work`): when the cap is reached the answer is the sound "anything", and
the next query continues where this one stopped.

## Proofs

`Context::prove` answers a question with `Truth::True`, `Truth::False` or `Truth::Unknown`.
`Unknown` means the facts do not decide it, never that it is false:

```rust
use bitwright::{CmpOpExt, Context, ParseOptions, Query, Truth, Width};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W16);
let small = cx.parse("zext<16>(trunc<8>(x))", &o)?;
let limit = cx.parse("256", &o)?;
assert_eq!(cx.prove(Query::Cmp(CmpOpExt::Ult, small, limit))?, Truth::True);
let odd = cx.parse("x | 1", &o)?;
assert_eq!(cx.prove(Query::IsZero(odd))?, Truth::False);
let y = cx.parse("y", &o)?;
assert_eq!(cx.prove(Query::IsZero(y))?, Truth::Unknown); // y may or may not be zero
# Ok::<(), bitwright::Error>(())
```

`Query::Injective` and `Query::Bijective` ask whether an expression is an invertible function
of one of its subexpressions; see [Invertibility](invertibility.md).

## Assumptions

Facts about a path (after a branch, for example) are given as `Assumptions`. They never change
the context's own facts; queries under assumptions use a separate overlay. The next chapter,
[Constraints](constraints.md), covers predicates, propagation, and what results rely on.

```rust
use bitwright::{
    Assumptions, BitVec, CmpOpExt, Context, Facts, KnownBits, ParseOptions, Query, Truth, Width,
};

let mut cx = Context::new();
let o = ParseOptions::width(Width::W8);
let x = cx.parse("x", &o)?;
let odd = cx.parse("x & 1", &o)?;
let zero = cx.parse("0", &o)?;
// On this path, x is known to have its low bit set.
let kb = KnownBits::new(BitVec::zero(Width::W8), BitVec::one(Width::W8)).unwrap();
let mut a = Assumptions::new();
a.assume(&mut cx, x, Facts::from_known(kb))?;
assert_eq!(cx.prove_with(Query::Cmp(CmpOpExt::Ne, odd, zero), &a)?, Truth::True);
assert_eq!(cx.prove(Query::Cmp(CmpOpExt::Ne, odd, zero))?, Truth::Unknown);
# Ok::<(), bitwright::Error>(())
```

Rule guards (the next chapters) are answered by these same facts, which is why a guard can only
ever say "proven", never "disproven".
