# In a compiler

A compiler uses bitwright on its own IR, not on text: it translates instructions into
expressions, simplifies every value of a function, translates results back, and may have
rewrites of its own that the rule language cannot say. This chapter covers those pieces.

- **`bitwright::translate`**:
  - `Semantics` says what an instruction computes.
  - `Lowering` turns a function into expressions.
  - `Raise` turns results back into instructions.
  - `Template` gives semantics as text, read at run time.
- **`Strategy::compile()`**: the simplifier tuned for every value of every function. See
  [Simplifying](simplifying.md#inside-a-compiler).
- **`Context::declare_known`**: what the compiler knows of values defined elsewhere.
- **`engine::Rewrite`**: rewrites written in Rust, linked into an engine at run time.
  `check::rewrite` tests them before they are trusted.

## Translating instructions

The compiler implements `Semantics` for its instruction type once: the value an instruction
defines, and its expression over its operands. A `Lowering` holds one function's translation:
the expression of every value, and a symbol for every value defined outside it (a parameter,
a load, a call result), with the known bits the compiler has of it, if any.

```rust
use bitwright::translate::{Lowering, Semantics};
use bitwright::{BinOp, BitVec, Context, Error, Expr, KnownBits, Width};

/// `dst = op a, b` over 64-bit values numbered by `u32`.
struct Inst {
    dst: u32,
    op: BinOp,
    a: u32,
    b: u32,
}

impl Semantics for Inst {
    type Value = u32;
    fn result(&self) -> Option<u32> {
        Some(self.dst)
    }
    fn lower(&self, lw: &mut Lowering<'_, u32>) -> Result<Expr, Error> {
        let a = lw.value(self.a, Width::W64)?;
        let b = lw.value(self.b, Width::W64)?;
        lw.context().bin(self.op, a, b)
    }
}

let mut cx = Context::new();
let mut lw = Lowering::new(&mut cx);
// %0 is a parameter the compiler knows is 16-byte aligned.
let aligned = KnownBits::new(BitVec::from_u64(Width::W64, 15)?, BitVec::zero(Width::W64)).unwrap();
lw.input(0, Width::W64, Some(aligned))?;
lw.lower_all(&[
    Inst { dst: 2, op: BinOp::And, a: 0, b: 1 },
    Inst { dst: 3, op: BinOp::Add, a: 2, b: 0 },
])?;
assert_eq!(lw.inputs().len(), 2); // %0, and %1 on first use
let v3 = lw.get(3).unwrap();
assert_eq!(lw.context().display(v3).to_string(), "($0 & $1) + $0");
# Ok::<(), Box<dyn std::error::Error>>(())
```

Values defined outside get fresh symbols (`$0`, `$1`). `Lowering::input_named` gives one a
name of the compiler's choosing instead.

A compiler with many instructions, or one that loads its instruction set from a description
file, can give semantics as text instead. A `Template` is an expression over named
parameters, read at run time. It is compiled once for each combination of operand widths and
then instantiated by copying, with no parsing:

```rust
use bitwright::translate::Template;
use bitwright::{Context, Width};

let umin = Template::new("select(a <u b, a, b)", &["a", "b"])?;
let pick = Template::new("select(c, a + 1, b)", &["c", "a", "b"])?;
// Check at startup instead of at the first use.
pick.check(&[Width::W1, Width::W32, Width::W32])?;

let mut cx = Context::new();
let (x, y) = (cx.symbol("x", Width::W32)?, cx.symbol("y", Width::W32)?);
let m = umin.instantiate(&mut cx, &[x, y])?;
assert_eq!(cx.display(m).to_string(), "select(x <u y, x, y)");
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Raising results

After simplifying, `Lowering::raise` turns a result back into instructions through the
compiler's `Raise`. Equal expressions are equal values, so a node some host value already
computes is that value, and raising doubles as value numbering. Only nodes no value computes
are emitted, operands first:

```rust
use bitwright::engine::{Engine, Strategy};
use bitwright::translate::{Lowering, Raise};
use bitwright::{BinOp, Context, Error, Expr, View, Width};

struct Emit(Vec<String>);
impl Raise for Emit {
    type Value = u32;
    fn emit(&mut self, _: &Context, _: Expr, node: &View, ops: &[u32]) -> Result<u32, Error> {
        let dst = 100 + self.0.len() as u32;
        self.0.push(match node {
            View::Const(c) => format!("%{dst} = const {c}"),
            View::Bin(op, ..) => format!("%{dst} = {op:?} %{}, %{}", ops[0], ops[1]),
            other => return Err(Error::Unsupported(format!("{other:?}"))),
        });
        Ok(dst)
    }
}

let engine = Engine::builder().builtin().strategy(Strategy::compile()).build()?;
let mut cx = Context::new();
let mut lw = Lowering::new(&mut cx);
let (x, y) = (lw.value(0, Width::W32)?, lw.value(1, Width::W32)?);
// %2 = (x ^ y) + 2·(x & y), obfuscated x + y.
let cx = lw.context();
let xor = cx.bin(BinOp::Xor, x, y)?;
let and = cx.bin(BinOp::And, x, y)?;
let one = cx.constant_u64(Width::W32, 1)?;
let twice = cx.bin(BinOp::Shl, and, one)?;
let v2 = cx.bin(BinOp::Add, xor, twice)?;
lw.define(2, v2)?;
let out = engine.simplify(lw.context(), v2)?;
let mut emit = Emit(Vec::new());
let v = lw.raise(out.expr, &mut emit)?;
assert_eq!(emit.0, ["%100 = Add %0, %1"]);
assert_eq!(v, 100);
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Rewrites in Rust

Some rewrites need more than the rule language has: a target's legality, a cost model, the
compiler's own analyses. A compiler writes those as an `engine::Rewrite`: a name, a group, a
revision, and a function from a node to its replacement. The function works through a `Site`,
which gives views of nodes, their facts, and construction. It is linked into an engine at run
time, and runs in the rule phases whose strategy names its group, after the phase's rules:

```rust
use std::sync::Arc;
use bitwright::engine::{Engine, Rewrite, Site, Strategy};
use bitwright::{BinOp, Context, Expr, ParseOptions, View, Width};

/// `x % c` (unsigned) as `x` when the facts show `x < c`: a remainder the compiler's
/// range analysis would remove too.
struct NeedlessRem;
impl Rewrite for NeedlessRem {
    fn name(&self) -> &str { "acme.needless_rem" }
    fn group(&self) -> &str { "acme" }
    fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
        let View::Bin(BinOp::URem, x, c) = site.view(e)? else { return None };
        let c = site.as_u64(c)?;
        let hi = site.facts(x)?.urange().hi().to_u64()?;
        (hi < c).then_some(x)
    }
}

let engine = Engine::builder()
    .builtin()
    .rewrite(Arc::new(NeedlessRem))
    .allow_unproven(true) // sampled at every application; see below
    .strategy(Strategy::compile().with_rule_groups(&["acme"]))
    .build()?;
let mut cx = Context::new();
cx.symbol("b", Width::W8)?; // `b` is 8 bits wide
let e = cx.parse("urem(zext<32>(b), 1000)", &ParseOptions::width(Width::W32))?;
// The built-in rules and passes leave it.
let plain = Engine::builder().builtin().strategy(Strategy::compile()).build()?;
assert_eq!(plain.simplify(&mut cx, e)?.expr, e);
let out = engine.simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "zext<32>(b)");
# Ok::<(), Box<dyn std::error::Error>>(())
```

A host rewrite simplifies: its results must be smaller (below). Rewrites that make code
larger for a target, such as expanding an instruction the target lacks, belong in the
compiler's `Raise`.

Arbitrary code has no static proof, so the engine holds a host rewrite to more checks than a
rule:

- **Termination.** A result is committed only when it is smaller than the node in the order
  every rule decreases (tree size, then operator precedence), so rules and host rewrites
  together cannot cycle. A result that is not smaller is left, and `Stats::host` counts it.
- **Verification.** A rewrite linked with `EngineBuilder::rewrite` (which needs
  `allow_unproven`, like an unproven rule program) is compared with the node at sampled points
  at every application. One found wrong is quarantined for the rest of the call.
- **Everything a rule gets.** Its width is checked, the fact tripwire applies when it is on,
  and `Hooks::admit` can veto it (it is named as `By::Rewrite`). What it builds and the facts
  it asks for are charged to the call's budgets.
- **Memoization.** Its name, revision and trust enter the engine's configuration hash. Bump
  `Rewrite::revision` whenever its results change, and keep it deterministic.

## Checking a rewrite

Sampling at every application costs time in the compiler. `check::rewrite` tests a rewrite
offline, in the compiler's own test suite:
- **Where it applies.** At every node of inputs the compiler gives, at every width they parse
  at, and on variations with other constants.
- **Values.** Every result compared with its node, exhaustively when their symbols have few
  bits, at boundary-biased points otherwise.
- **The engine's contract.** Width, determinism, and the termination order.

A rewrite that passes can be linked with `EngineBuilder::trusted_rewrite`, without sampling:

```rust
use bitwright::check::{RewriteCheckConfig, RewriteFailure, rewrite};
use bitwright::engine::{Rewrite, Site};
use bitwright::{BinOp, Expr, View};

/// `(x ^ y) ^ y` as `x`.
struct XorTwice;
impl Rewrite for XorTwice {
    fn name(&self) -> &str { "acme.xor_twice" }
    fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
        let View::Bin(BinOp::Xor, a, y) = site.view(e)? else { return None };
        let View::Bin(BinOp::Xor, x, z) = site.view(a)? else { return None };
        if z == y { Some(x) } else if x == y { Some(z) } else { None }
    }
}
let report = rewrite(&XorTwice, &["(x ^ y) ^ y", "((a + 1) ^ 7) ^ 7"], &RewriteCheckConfig::default())?;
assert!(report.applications > 0 && report.exhaustive > 0);

/// `(x + c) - c` as `x + c`: wrong, and caught with a counterexample.
struct Wrong;
impl Rewrite for Wrong {
    fn name(&self) -> &str { "acme.wrong" }
    fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
        let View::Bin(BinOp::Add, a, _) = site.view(e)? else { return None };
        matches!(site.view(a)?, View::Bin(BinOp::Add, ..)).then_some(a)
    }
}
match rewrite(&Wrong, &["(x + 3) - 3"], &RewriteCheckConfig::default()) {
    Err(RewriteFailure::Differs { node, result, assignment }) => {
        assert!(!assignment.is_empty());
        println!("{node} => {result} differs at {assignment:?}");
    }
    other => panic!("{other:?}"),
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

This is testing, not proof: it covers the shapes the inputs exercise. Give inputs where the
rewrite applies and where it nearly does.
