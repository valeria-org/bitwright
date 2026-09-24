# C, C++ and Python

bitwright can be used from C, C++ and Python. The bindings cover what a host needs to hand its
expressions to bitwright and read the results back:

- building, parsing, printing and inspecting expressions, at any width from 1 to 512 bits;
- evaluation and substitution;
- facts (known bits and ranges) and tri-state proofs, including invertibility, under
  assumptions, with the assumptions each answer relies on;
- simplification with the standard engine or the deobfuscation engine (the command line's
  `simplify`: the MBA service with the native solver, on bitwright's own evidence), with budgets,
  and with rule files of your own, linked with their proof ledgers;
- SMT-LIB export and import.

Extension operations, host hooks, observers, deadlines, allowances, custom strategies, other MBA
backends and equality saturation are Rust only. The bindings have the version of the crate they
are built with, and give the same results.

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
    assert(bw::facts((b & 0xf0) | 1).known_zero == bw::Value(8, 0x0e));
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
