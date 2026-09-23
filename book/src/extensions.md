# Extension operations

An instruction set has operations that bitwright's operators express only clumsily or not at
all: a flags bundle, a funnel shift, a vendor-defined count. A host registers such an operation
as an `ExtOp`. It is total, deterministic, and takes 1 to 3 arguments. It has 1 to 8 outputs, and
each output is a node of its own.

An operation provides:

- `signature`: its outputs' roles and widths, given the argument widths;
- `eval`: the exact values;
- optionally `known_bits`, for facts;
- optionally `expand`: the same operation built from bitwright's own operators;
- optionally `smtlib`: a term for solvers;
- optionally `invertible` and `invert`: which outputs are injective or bijective in which
  argument, and the inverse at a value (see [Invertibility](invertibility.md)).

Registration runs a self-test at the argument widths the signature accepts, mixed widths
included, up to 512 bits. It checks that `eval` is deterministic and returns the declared widths,
that a commutative operation really is, that `known_bits` and `expand` agree with `eval`, and
that `invert` undoes `eval` wherever invertibility is declared. The test samples inputs, so it
catches most broken operations, not all of them.

```rust
use std::sync::Arc;
use bitwright::ext::{ExtOp, ExtSig, Registry};
use bitwright::{BitVec, BinOp, CmpOpExt, Context, ContextConfig, KnownBits, SymbolKey, Width};

/// x86 `add` with its carry flag: the sum and CF.
struct AddCf;
impl ExtOp for AddCf {
    fn name(&self) -> &str { "x86.add_cf" }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b] if a == b => Ok(ExtSig::new(&[("sum", *a), ("cf", Width::W1)])),
            _ => Err("two operands of one width".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let s = BitVec::apply_bin(BinOp::Add, &args[0], &args[1]).unwrap();
        out[1] = BitVec::from_bool(BitVec::apply_cmp(CmpOpExt::Ult, &s, &args[0]).unwrap());
        out[0] = s;
    }
    fn known_bits(&self, args: &[KnownBits], out: &mut [KnownBits]) {
        // The sum's bits come from bitwright's own transfer.
        out[0] = KnownBits::apply_bin(BinOp::Add, &args[0], &args[1]).unwrap();
    }
}

let registry = Arc::new(Registry::builder().register(AddCf)?.build());
let add_cf = registry.id("x86.add_cf").unwrap();
let mut cx = Context::with_registry(ContextConfig::default(), registry);
let x = cx.symbol("x", Width::W32)?;
let y = cx.symbol("y", Width::W32)?;
let out = cx.ext(add_cf, &[x, y])?;
assert_eq!(cx.display(out[1]).to_string(), "@x86.add_cf[1](x, y)");
// Parsed back in the same context, it is the same node.
assert_eq!(cx.parse("@x86.add_cf[1](x, y)", &Default::default())?, out[1]);
// 0xffffffff + 1 wraps to 0 and sets the carry.
let env = [
    (SymbolKey::from("x"), BitVec::ones(Width::W32)),
    (SymbolKey::from("y"), BitVec::one(Width::W32)),
];
let v = cx.eval(&out, &env[..])?;
assert!(v[0].is_zero() && v[1].is_ones());
# Ok::<(), Box<dyn std::error::Error>>(())
```

The simplifier treats an extension node as an atom: no rule or pass looks inside it (an
invertibility declaration is the one thing it uses, at equalities). It still
simplifies the arguments and rebuilds the call, unless the operation's `traits()` mark it
`opaque`. Facts come from `known_bits`, and are exact when every argument is known. Constraints
work through extension nodes like any other. With feature `smtlib`, an operation without an
`smtlib` term exports as an uninterpreted function, and the script declares `QF_UFBV`. A solver's
`unsat` still proves equality, but a `sat` model may rely on values the real operation never
produces.

An operation that must never be merged with another call on the same arguments (for example a
read of a volatile resource) takes a fresh symbol as one of its arguments.
