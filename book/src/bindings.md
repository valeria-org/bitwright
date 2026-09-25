# C, C++, Python and JavaScript

bitwright can be used from C, C++, Python and, compiled to WebAssembly, JavaScript. The bindings
cover what a host needs to hand its expressions to bitwright and read the results back:

- building, parsing, printing and inspecting expressions, at any width from 1 to 512 bits;
- IEEE 754 [floating point](floating-point.md) in any format and under every rounding mode, on
  the bit-vectors that hold the encodings;
- evaluation and substitution;
- facts (known bits, and ranges with a stride) and tri-state proofs, including invertibility,
  under assumptions, with the assumptions each answer relies on;
- simplification with the standard engine or the deobfuscation engine (the command line's
  `simplify`: the MBA service with the native solver, on bitwright's own evidence), with budgets,
  and with rule files of your own, linked with their proof ledgers;
- SMT-LIB export and import;
- proofs of equivalence by the native prover, synthesis, and (Python) equality saturation;
- [memory](memory.md) (loads and stores as expressions) and [lifted code](lifting.md) (p-code,
  VEX, LLVM IR);
- [verifying compiler transformations](transformations.md): transformations in the Alive
  syntax, translation validation of LLVM IR, precondition inference;
- engines that refuse rewrites by rule or pass name, and (Python) the trace of a run's
  rewrites.

Extension operations, host hooks as callbacks, deadlines, allowances, custom strategies and
other MBA backends are Rust only. The bindings have the version of the crate they are built
with, and give the same results. JavaScript has a string API: text in, text out.

## Python

The `bitwright` package is built from `bitwright-py/` with [maturin](https://www.maturin.rs/),
which needs a Rust toolchain; one wheel serves CPython 3.10 and later.

```text
pip install ./bitwright-py
```

```python
import bitwright as bw

cx = bw.Context()
x, y = cx.symbols("x y", 64)

# Operators build expressions; an int is a constant of the other operand's width.
e = (x & y) + (x | y)
assert str(e.simplify()) == "x + y"

# Text, and the deobfuscation engine for MBA. `bw.simplify` is the command line's `simplify`.
mba = cx.parse("(x & y) * (x | y) + (x & ~y) * (~x & y)")
assert str(bw.Engine.deobfuscate().simplify(mba)) == "x * y"
assert bw.simplify("(x & y) * (x | y) + (x & ~y) * (~x & y)") == "x * y"

# Values are Python ints, exact at any width.
assert (x * 3 + 1).eval(x=2**64 - 1) == 2**64 - 2
w = cx.symbol("w", 256)
assert (w + 1).eval(w=2**256 - 1) == 0

# Facts, proofs, assumptions.
b = cx.symbol("b", 8)
f = ((b & 0xF0) | 1).facts()
assert (f.known_zero, f.known_one, f.umin, f.umax) == (0x0E, 0x01, 1, 0xF1)
assert f.ustride == 16  # the values are 1, 17, 33, ..., 241
small = bw.Assumptions(b.ult(16))
assert (b & 0xF0).eq(0).prove() is None  # not decided
assert (b & 0xF0).eq(0).prove(small) is True
out = bw.Engine().run([b & 0xF0], assumptions=small)[0]
assert str(out.expr) == "0:8" and out.relies_on == (0,)  # holds where assumption 0 does

# Invertibility: a keyed mixer is a bijection of its input.
assert ((b ^ 0x5A) * 0x1D).prove_injective(b, bijective=True) is True
```

Structurally equal expressions of a context are one node, so `==` on expressions is identity
and expressions can be dictionary keys. Comparisons that build a 1-bit expression are methods
(`eq`, `ne`, `ult`, `ule`, `ugt`, `uge`, `slt`, `sle`, `sgt`, `sge`), since `<` could be signed
or unsigned; an expression has no truth value (`if x.ult(y):` raises `TypeError`: ask
`prove()`). `>>` is the logical shift (`ashr` is the arithmetic one), `//` and `%` are unsigned,
and an int operand must fit the width: `0 <= v < 2**w`, or a negative value in two's
complement down to `-2**(w - 1)`. `kind`, `op`, `children`, `value` and `name` inspect a node.

Rules of your own are checked once, and linked with their proof ledger:

```python
import bitwright as bw

rules = """bitwright 1;
group my.rules {
    rule and_or_complement<W>(x: W, y: W) { (x | y) & (x | ~y) => x }
}"""
ledger = bw.check_rules(rules)  # raises RuleError with a counterexample if a rule is unsound
engine = bw.Engine(rules=[(rules, ledger)])

cx = bw.Context()
e = cx.parse("(a | b) & (a | ~b)", 64)
assert str(engine.simplify(e)) == "a"

# Budgets bound the work; a stopped result is still correct, just not final. (A result the
# context already holds, like `e`'s now, costs nothing.)
fresh = cx.parse("(p | q) & (p | ~q)", 64)
stopped = engine.run([fresh], budget=bw.Budget(node_visits=0))[0]
assert stopped.end == "budget" and stopped.limit == "node visits"
assert engine.run([e], budget=bw.Budget(node_visits=0))[0].end == "completed"
```

Errors are exceptions: `ParseError` for text, `WidthError` for width rules, `RuleError` for rule
files and ledgers, `BitwrightError` (their base) for the rest, `ValueError` for an int that does
not fit and `TypeError` for an operand that is not an expression or an int. Contexts and engines
may be shared between threads: a context serializes the operations on it, and simplification
releases the interpreter. The package is typed (`py.typed`).

## C

`bitwright-ffi/` builds `libbitwright` as a shared and a static library, declared by
`bitwright-ffi/include/bitwright.h`:

```text
cargo build --release -p bitwright-ffi
cc -I bitwright-ffi/include app.c -L target/release -lbitwright
```

(The static library also needs the system libraries Rust's standard library uses:
`-lpthread -ldl -lm` on Linux.)

```c
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bitwright.h"

static void check(bw_status s) {
    if (s != BW_OK) {
        fprintf(stderr, "bitwright error %d: %s\n", s, bw_last_error());
        exit(1);
    }
}

int main(void) {
    bw_context *cx = bw_context_new();
    bw_engine *engine = bw_engine_new(BW_PRESET_STANDARD);
    bw_expr e, s, b, k, f;
    char *text;

    assert(bw_abi_version() == BW_ABI_VERSION);
    check(bw_parse(cx, "(x & y) + (x | y)", 64, &e));
    check(bw_simplify(engine, cx, e, &s));
    check(bw_print(cx, s, 0, &text));
    assert(strcmp(text, "x + y") == 0);
    bw_string_free(text);

    /* Constructors, and evaluation: b * 3 at 8 bits, b = 100, is 300 mod 256. */
    bw_value v = bw_value_u64(8, 100), r;
    check(bw_symbol(cx, "b", 8, &b));
    check(bw_const_u64(cx, 8, 3, &k));
    check(bw_bin(cx, BW_MUL, b, k, &f));
    check(bw_eval(cx, f, &b, &v, 1, &r));
    assert(r.width == 8 && r.limbs[0] == 44);

    /* Errors are status codes, described by bw_last_error. */
    bw_status st = bw_bin(cx, BW_ADD, e, b, &f);
    assert(st == BW_ERR_WIDTH);
    assert(strstr(bw_last_error(), "widths differ") != NULL);

    bw_engine_free(engine);
    bw_context_free(cx);
    return 0;
}
```

The conventions, stated in full at the top of the header:

- A fallible function returns a `bw_status`, `BW_OK` or an error code; `bw_last_error()`
  describes the last error on the thread. Output parameters are written only on success.
- Objects come from a `*_new` function and go back to the matching `*_free`, which accepts
  NULL; strings the library returns go back to `bw_string_free`.
- A `bw_expr` is a 64-bit handle, valid in the context that made it until the context is cleared
  or freed. A handle from another context, or from before a clear, is rejected, never mistaken
  for another node. 0 (`BW_NULL_EXPR`) is never a handle.
- A `bw_value` holds up to 512 bits in eight little-endian 64-bit limbs; bits above the width
  must be zero. `bw_value_u64` and `bw_value_i64` make one.
- Enumerations cross as `int`, with fixed values; an unknown value is an error. Assumptions and
  proofs report the constraints they rely on as a mask: bit `i` for constraint `i` below 63,
  bit 63 for any from 63 on.
- A context or an assumption set is used by one thread at a time; an engine may be shared by
  any number of threads.

`BW_ABI_VERSION` changes whenever a declaration does; check `bw_abi_version()` against it when
the library is loaded at run time. `bitwright-ffi/examples/` has more: facts, proofs and
assumptions from C, and a tour of the C++ wrapper.

## C++

`bitwright-ffi/include/bitwright.hpp` is a header-only C++17 wrapper over the C API: objects own
their C counterparts, errors are thrown as `bitwright::Error` (with the status code), and
expressions are small values with operators. It links against the same library.

```cpp
#include <cassert>

#include "bitwright.hpp"

namespace bw = bitwright;

int main() {
    bw::Context cx;
    bw::Expr x = cx.symbol("x", 64), y = cx.symbol("y", 64);

    // Operators build expressions; integers are constants of the other operand's width.
    bw::Engine engine = bw::Engine::standard();
    assert(engine.simplify((x & y) + (x | y)) == x + y);
    assert(engine.simplify(((x ^ 0x5a) + 3 - 3) ^ 0x5a) == x);
    bw::Expr mba = cx.parse("(x & y) * (x | y) + (x & ~y) * (~x & y)");
    assert(bw::Engine::deobfuscate().simplify(mba).str() == "x * y");

    // Facts, and proofs under assumptions.
    bw::Expr b = cx.symbol("b", 8);
    bw::Facts f = bw::facts((b & 0xf0) | 1);
    assert(f.known_zero == bw::Value(8, 0x0e) && f.ustride == 16);
    bw::Assumptions small;
    small.assume(b.ult(b.constant(16)));
    assert(bw::prove((b & 0xf0).eq(b.constant(0)), &small));

    // Rules of your own, checked when they are added (or pass their ledger).
    bw::Engine mine = bw::EngineBuilder()
                          .rules("bitwright 1;\n"
                                 "group my.rules {\n"
                                 "    rule and_or_complement<W>(x: W, y: W) {\n"
                                 "        (x | y) & (x | ~y) => x\n"
                                 "    }\n"
                                 "}")
                          .build();
    assert(mine.simplify((x | y) & (x | ~y)) == x);

    // Errors are exceptions.
    try {
        cx.parse("x +");
        assert(false);
    } catch (const bw::Error &e) {
        assert(e.status() == BW_ERR_SYNTAX);
    }
    return 0;
}
```

`==` on expressions compares handles (equal handles, equal expressions); `eq`, `ult`, `slt` and
the other comparison methods build 1-bit expressions. `>>` is the logical shift. An `Expr` refers
to its `Context` without owning it, so the context must outlive it; `Engine` is cheap to copy and
thread-safe.

## Floating point

The three bindings build, print, inspect and evaluate the operations of the
[chapter on floating point](floating-point.md). A floating-point value is a bit-vector holding
an IEEE 754 encoding, so operands and results are bit patterns of the format's width: `eb + sb`
bits for the format `(eb, sb)`, with `eb` exponent bits and `sb` significand bits, the hidden
bit included. The named formats are `F16`, `BF16`, `F32`, `F64`, `F128`, `F256` and `X87` (in C
`BW_F32` and so on, and `bw_fp_format_of(eb, sb)` for any other); the rounding modes are `rne`,
`rna`, `rtp`, `rtn` and `rtz`, `rne` by default in Python and C++. Operations have the names of
the text syntax: in Python and C++ they are methods (`fadd`, `fsqrt`, `feq`, `fisnan`,
`fconvert`, `to_float`, `to_int`, ...); in C, `bw_fp` builds the node of a `bw_fpop`, and
`bw_fp_sub`, `bw_fp_neg`, `bw_fp_abs`, `bw_fp_copysign`, `bw_fp_cmp`, `bw_fp_test`,
`bw_x87_load` and `bw_x87_store` build the other operations as the text syntax does, from those
nodes and bit-vector operators. A node of an operation has the kind `fp` (`BW_KIND_FP`) and its
operation as `op`; its format and rounding mode are `format` and `rounding` in Python,
`fp_node()` in C++ and `bw_fp_node_of` in C.

```python
import struct

import bitwright as bw


def f32(v: float) -> int:
    """The binary32 encoding of `v`."""
    return int(struct.unpack("<I", struct.pack("<f", v))[0])


cx = bw.Context()
a, b = cx.symbols("a b", 32)

# Methods named after the text syntax's operations take the format and a rounding mode.
s = a.fadd(b, bw.F32)
assert str(s) == "fp.add.rne.f32(a, b)"
assert (s.kind, s.op, s.format, s.rounding) == ("fp", "add", bw.F32, "rne")

# 0.1 + 0.2 in binary32: to nearest it rounds up, toward zero one unit in the last place lower.
assert s.eval(a=f32(0.1), b=f32(0.2)) == f32(0.3) == 0x3E99999A
assert a.fadd(b, bw.F32, rm="rtz").eval(a=f32(0.1), b=f32(0.2)) == 0x3E999999

# Integers of any width convert to any format and back, saturating.
i = cx.symbol("i", 16)
x = i.to_float(bw.F64)  # signed; `signed=False` reads `i` as unsigned
assert x.to_int(8, bw.F64, rm="rtz").eval(i=1000) == 0x7F

# Facts see through floating point: a product of converted integers is never a NaN.
nan = x.fmul(x, bw.F64).fisnan(bw.F64)
assert nan.prove() is False
assert str(nan.simplify()) == "0:1"
```

```c
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bitwright.h"

static void check(bw_status s) {
    if (s != BW_OK) {
        fprintf(stderr, "bitwright error %d: %s\n", s, bw_last_error());
        exit(1);
    }
}

int main(void) {
    bw_context *cx = bw_context_new();
    bw_expr ab[2], s, t, h;
    bw_value v[2], r;
    bw_fp_node n;
    bw_status st;
    char *text;

    /* fp.add.rtz.f32(a, b): the operation, its rounding mode and format, the operands, and the
     * target format and integer width that only conversions read. */
    check(bw_symbol(cx, "a", 32, &ab[0]));
    check(bw_symbol(cx, "b", 32, &ab[1]));
    check(bw_fp(cx, BW_FP_ADD, BW_RTZ, BW_F32, ab, 2, BW_F32, 0, &s));
    check(bw_print(cx, s, 0, &text));
    assert(strcmp(text, "fp.add.rtz.f32(a, b)") == 0);
    bw_string_free(text);

    /* 0.1 + 0.2 in binary32, toward zero. */
    v[0] = bw_value_u64(32, 0x3dcccccd);
    v[1] = bw_value_u64(32, 0x3e4ccccd);
    check(bw_eval(cx, s, ab, v, 2, &r));
    assert(r.limbs[0] == 0x3e999999);

    /* Inspecting the node. */
    check(bw_fp_node_of(cx, s, &n));
    assert(n.op == BW_FP_ADD && n.rm == BW_RTZ && n.format.eb == 8 && n.format.sb == 24);

    /* To a 16-bit signed integer, saturating: 1e10 gives 0x7fff. */
    check(bw_fp(cx, BW_FP_TO_SBV, BW_RTZ, BW_F32, ab, 1, BW_F32, 16, &t));
    v[0] = bw_value_u64(32, 0x501502f9);
    check(bw_eval(cx, t, ab, v, 1, &r));
    assert(r.width == 16 && r.limbs[0] == 0x7fff);

    /* Errors: a format outside 2 <= eb <= 31, sb >= 2, eb + sb <= 512, an operand of another
     * width. */
    st = bw_fp_neg(cx, bw_fp_format_of(1, 9), ab[0], &t);
    assert(st == BW_ERR_WIDTH);
    check(bw_symbol(cx, "h", 16, &h));
    st = bw_fp_test(cx, BW_FP_ISNAN, BW_F32, h, &t);
    assert(st == BW_ERR_WIDTH);

    bw_context_free(cx);
    return 0;
}
```

```cpp
#include <cassert>

#include "bitwright.hpp"

namespace bw = bitwright;

int main() {
    bw::Context cx;
    bw::Expr a = cx.symbol("a", 32), b = cx.symbol("b", 32);

    // 0.1 + 0.2 in binary32, to nearest and toward zero.
    bw::Expr near = a.fadd(b, bw::F32), down = a.fadd(b, bw::F32, bw::Rounding::Rtz);
    assert(near.str() == "fp.add.rne.f32(a, b)");
    bw::Value tenth(32, 0x3dcccccd), fifth(32, 0x3e4ccccd);
    assert(cx.eval(near, {{a, tenth}, {b, fifth}}) == bw::Value(32, 0x3e99999a));
    assert(cx.eval(down, {{a, tenth}, {b, fifth}}) == bw::Value(32, 0x3e999999));

    // Inspecting a node, and building it again with the generic `fp`.
    bw::FpNode n = *down.fp_node();
    assert(down.kind() == bw::Kind::Fp && n.op == bw::FpOp::Add && n.format == bw::F32);
    assert(n.rm == bw::Rounding::Rtz && !n.to && !n.int_width);
    assert(bw::fp(n.op, n.format, down.children(), *n.rm) == down);

    // Facts: an integer converted to a float is never a NaN.
    bw::Expr i = cx.symbol("i", 16);
    assert(bw::prove(i.to_float(bw::F64).fisnan(bw::F64)).truth == bw::Truth::False);

    // Errors are exceptions: an operand of another width.
    try {
        a.fadd(i, bw::F32);
        assert(false);
    } catch (const bw::Error &e) {
        assert(e.status() == BW_ERR_WIDTH);
    }
    return 0;
}
```

## Proofs, memory, lifted code and transformations

The same services from each language: an equivalence proved by bitwright's own SAT solver,
synthesis, a spill reloaded through memory, a lifted VEX block, and a transformation refuted.

```python
import bitwright as bw

cx = bw.Context()
x, y = cx.symbols("x y", 32)
assert ((x ^ y) + 2 * (x & y)).equivalent(x + y) is True
cex = (x + y).equivalent(x | y)  # a counterexample: {"x": ..., "y": ...}
assert isinstance(cex, dict)
assert str((((x + y) & 1) ^ (x & 1)).synthesize()) == "y & 1"
z = cx.symbol("z", 32)
assert str((x * y + x * z).saturate()) == "(y + z) * x"

# Memory: a spill and its reload.
sp, v = cx.symbols("sp v", 64)
m = bw.Memory(cx)
m.store(sp - 8, v)
assert m.load(sp - 8, 8) == v

# Lifted code: an MBA as pyvex prints it, back to the sum.
block = bw.lift_vex(
    cx,
    """t0 = GET:I64(rdi)
       t1 = GET:I64(rsi)
       t2 = Xor64(t0,t1)
       t3 = And64(t0,t1)
       t4 = Add64(t3,t3)
       t5 = Add64(t2,t4)
       PUT(rax) = t5""",
)
assert str(block.register("rax").simplify(bw.Engine.deobfuscate())) == "rdi + rsi"

# A transformation, and the precondition it needs.
(r,) = bw.verify_transforms("%r = select %c, %x, false\n=>\n%r = and %c, %x")
assert r.verdict == "invalid" and "poison" in r.text
(i,) = bw.infer_preconditions("%r = mul %x, C\n=>\n%r = shl %x, log2(C)")
assert i.pre == "isPowerOf2(C)"

# The rewrites of a run, and an engine that refuses a pass.
out, steps = bw.Engine().trace(x * 3 - x - x)
assert str(out) == "x" and steps
kept = bw.Engine(refuse=["linear"]).simplify(x * 3 - x - x)
assert kept.equivalent(x) is True
```

```c
#include <assert.h>
#include <stdio.h>
#include <string.h>

#include "bitwright.h"

int main(void) {
    bw_context *cx = bw_context_new();
    bw_expr a, b, s;
    bw_parse(cx, "(x ^ y) + 2 * (x & y)", 32, &a);
    bw_parse(cx, "x + y", 32, &b);
    int verdict;
    bw_equivalent(cx, a, b, 1000000, &verdict);
    assert(verdict == BW_EQUIVALENT);

    bool found;
    bw_parse(cx, "((x + y) & 1) ^ (x & 1)", 32, &a);
    bw_synthesize(cx, a, 7, &s, &found);
    char *text;
    bw_print(cx, s, 0, &text);
    assert(found && strcmp(text, "y & 1") == 0);
    bw_string_free(text);

    /* Memory: a spill and its reload. */
    bw_memory *m = bw_memory_new("mem", 64, 8, false);
    bw_expr slot, v, back;
    bw_parse(cx, "sp - 8", 64, &slot);
    bw_symbol(cx, "v", 64, &v);
    bw_memory_store(m, cx, slot, v);
    bw_memory_load(m, cx, slot, 8, &back);
    assert(back == v);
    bw_memory_free(m);

    /* Lifted VEX. */
    bw_lifted *l;
    assert(bw_lift(cx, BW_LIFT_VEX, "t0 = GET:I64(rdi)\nt1 = Add64(t0,t0)\nPUT(rax) = t1", NULL,
                   &l) == BW_OK);
    const char *name;
    bw_expr rax;
    bw_lifted_get(l, BW_LIFTED_OUTPUTS, 0, &name, &rax, NULL);
    assert(strcmp(name, "rax") == 0);
    bw_lifted_free(l);

    /* A transformation refuted. */
    char *report;
    bw_transform_counts counts;
    bw_transform_verify("%r = select %c, %x, false\n=>\n%r = and %c, %x", 0, &report, &counts);
    assert(counts.invalid == 1);
    printf("%s", report);
    bw_string_free(report);
    bw_context_free(cx);
    return 0;
}
```

```cpp
#include <cassert>

#include "bitwright.hpp"

namespace bw = bitwright;

int main() {
    bw::Context cx;
    bw::Expr e = cx.parse("(x ^ y) + 2 * (x & y)", 32);
    assert(bw::equivalent(e, cx.parse("x + y", 32)) == true);
    assert(bw::synthesize(cx.parse("((x + y) & 1) ^ (x & 1)", 32))->str() == "y & 1");

    bw::Memory m;
    bw::Expr slot = cx.parse("sp - 8", 64), v = cx.parse("v", 64);
    m.store(slot, v);
    assert(m.load(slot, 8).raw() == v.raw());

    auto block = bw::lift(cx, bw::FrontEnd::Vex, "t0 = GET:I64(rdi)\nt1 = Add64(t0,t0)\nPUT(rax) = t1");
    assert(block.reg("rax")->str() == "rdi + rdi");

    auto report = bw::verify_transforms("%r = select %c, %x, false\n=>\n%r = and %c, %x");
    assert(report.invalid == 1);
    return 0;
}
```

## JavaScript (WebAssembly)

`bitwright-wasm/` builds bitwright as a WebAssembly module with no bindings generator, and
`bitwright-wasm/js/bitwright.mjs` wraps it for JavaScript, in a browser or Node: every
function takes and returns strings.

```text
cargo build --release -p bitwright-wasm --target wasm32-unknown-unknown
# target/wasm32-unknown-unknown/release/bitwright_wasm.wasm
```

```js
import { readFile } from "node:fs/promises";
import { instantiate } from "./bitwright.mjs";

const bw = await instantiate(await readFile("bitwright_wasm.wasm")); // or fetch(url)
bw.simplify("(x & y) * (x | y) + (x & ~y) * (~x & y)", 64); // "x * y"
bw.synthesize("((x + y) & 1) ^ (x & 1)", 32);               // "y & 1"
bw.equivalent("x * 2", "x + x", 16);                         // "equivalent"
bw.prove("%r = select %c, %x, false\n=>\n%r = and %c, %x");   // "INVALID …" and why
bw.lift("vex", "t0 = GET:I64(rdi)\nt1 = Add64(t0,t0)\nPUT(rax) = t1"); // "rax = rdi + rdi\n"
```

`validate` (translation validation), `infer` (preconditions) and `toSmtlib` complete it;
`bitwright-wasm/js/test.mjs` exercises each under Node.
