# Examples in Python, C and C++

The tasks of the [Rust examples](examples.md), from the [bindings](bindings.md): feeding a
disassembler's or a lifter's expressions to bitwright and taking the results back. Every example
is a complete program, run as a test.

## Python

### A batch of obfuscated expressions

`bw.Engine.deobfuscate()` is the command line's `simplify`: the deobfuscation strategy and the MBA
service, publishing only what bitwright proves. Text that a script collected, say from a
decompiler's output, parses at the width of its variables:

```python
import bitwright as bw

cx = bw.Context()
engine = bw.Engine.deobfuscate()
collected = {
    "(x ^ y) + 2 * (x & y)": "x + y",
    "(x & ~y) - (~x & y)": "x - y",
    "(x ^ 0x10) + 2 * (x & 0x10)": "x + 16",
    "(x & y) * (x | y) + (x & ~y) * (~x & y)": "x * y",
    "(x ^ 0x5a5a5a5a) + (x ^ 0x5a5a5a5a) - 2 * (x ^ 0x5a5a5a5a)": "0:32",
}
for text, plain in collected.items():
    assert str(engine.simplify(cx.parse(text, 32))) == plain, text

# One expression, without a context: the command line's `simplify` exactly.
assert bw.simplify("x * 7 * 183", 8) == "x"
assert bw.simplify("x & 0xf0", 32, assume=["x <u 16"]) == "0:32"
```

### From a lifter's instructions

A lifter hands over instructions, not text. Operators and methods build the expressions they
compute; here a signed `jl` after `cmp eax, ebx`, with the flags written out as the instruction
defines them:

```python
import bitwright as bw

cx = bw.Context()
regs = {"eax": cx.symbol("a", 32), "ebx": cx.symbol("b", 32)}

# cmp eax, ebx; jl target
a, b = regs["eax"], regs["ebx"]
diff = a - b
sf = diff.bit(31)                   # the sign of the difference
of = ((a ^ b) & (a ^ diff)).bit(31)  # the operands' signs differ, and the result's is b's
jl = sf ^ of

assert str(jl.simplify()) == "a <s b"
# The other signed conditions follow from it.
assert str((~jl).simplify()) == "b <=s a"  # jge
```

### Opaque predicates

Walking a function's branches, each condition is either decided, so the other arm is dead code,
or not. `prove()` answers `True`, `False` or `None`:

```python
import bitwright as bw

cx = bw.Context()
x = cx.symbol("x", 32)
branches = {
    "odd": ((x | 1) & 1).eq(1),        # always taken
    "aligned": ((x << 2) & 3).ne(0),   # never: shifted by 2, the low bits are 0
    "overflow": (x & 0xFF).ugt(0xFF),  # never
    "input": x.ugt(100),               # depends on the input
}
decided = {name: cond.prove() for name, cond in branches.items()}
assert decided == {"odd": True, "aligned": False, "overflow": False, "input": None}
```

### Under a path condition

The branches taken to reach a block are assumptions; each result says which of them it relied
on, so it is kept only where they hold:

```python
import bitwright as bw

cx = bw.Context()
x, y = cx.symbols("x y", 32)
path = bw.Assumptions()
bounded = path.assume(x.ult(16))  # constraint 0
three = path.assume(y.eq(3))      # constraint 1

out = bw.Engine().run([(x & 0xF0) + y * x, x + 1], assumptions=path)
assert str(out[0].expr) == "x * 3" and out[0].relies_on == (bounded, three)
assert str(out[1].expr) == "x + 1" and out[1].relies_on == ()

# A branch not taken assumes the negation.
path.assume(x.eq(0), holds=False)
assert x.ugt(0).prove(path) is True
```

### A keyed check

A serial check compares a keyed hash with a constant. Each step is invertible, so the check has
exactly one solution, which the simplifier finds:

```python
import bitwright as bw

cx = bw.Context()
k = cx.symbol("k", 8)
h = (k ^ 0x5A) * 0x1D
assert h.prove_injective(k, bijective=True) is True
check = h.eq(0x33)
assert str(check.simplify()) == "k == -43"
assert h.eval(k=0xD5) == 0x33  # -43 is 0xd5
```

### Floating-point flags

After `ucomiss xmm0, xmm1`, `ja` tests that neither the carry flag ("less, or unordered") nor
the zero flag ("equal, or unordered") is set. Built from the flags, the condition comes back as
one comparison:

```python
import bitwright as bw

cx = bw.Context()
x, y = cx.symbols("x y", 32)
f = bw.F32
unordered = x.fisnan(f) | y.fisnan(f)
cf = x.flt(y, f) | unordered
zf = x.feq(y, f) | unordered
ja = ~cf & ~zf
assert str(ja.simplify()) == "fp.lt.f32(y, x)"

# Integers that went through a float and back.
i = cx.symbol("i", 16)
round_trip = i.to_float(bw.F64).to_int(32, bw.F64, rm="rtz")
assert str(round_trip.simplify()) == "sext<32>(i)"
```

### To a solver and back

`to_smtlib` writes the expressions as an SMT-LIB script for any solver; `from_smtlib` reads one
back, symbols, definitions and assertions:

```python
import bitwright as bw

cx = bw.Context()
x, y = cx.symbols("x y", 32)
before = (x | y) - (x & y)
after = before.simplify()
assert str(after) == "x ^ y"
script = cx.to_smtlib(before, after)
assert "(define-fun root0 " in script and "(define-fun root1 " in script

other = bw.Context()
read = other.from_smtlib(script)
root0, root1 = read.definitions["root0"], read.definitions["root1"]
assert root0.simplify() == root1  # one node: `x ^ y` in the other context
```

## C

### Deobfuscating under assumptions

The deobfuscation preset, several roots in one call, and the constraints each result relies on
as a mask:

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

static void expect(bw_context *cx, bw_expr e, const char *want) {
    char *text;
    check(bw_print(cx, e, 0, &text));
    if (strcmp(text, want) != 0) {
        fprintf(stderr, "got %s, want %s\n", text, want);
        exit(1);
    }
    bw_string_free(text);
}

int main(void) {
    bw_context *cx = bw_context_new();
    bw_engine *engine = bw_engine_new(BW_PRESET_DEOBFUSCATE);
    bw_assumptions *path = bw_assumptions_new();
    bw_expr roots[2], cond;
    bw_outcome out[2];
    uint32_t id;

    check(bw_parse(cx, "(x & y) * (x | y) + (x & ~y) * (~x & y)", 64, &roots[0]));
    check(bw_parse(cx, "(x & 0xf0) + (x ^ y) + 2 * (x & y)", 64, &roots[1]));

    /* On this path, x is below 16. */
    check(bw_parse(cx, "x <u 16", 64, &cond));
    check(bw_assume(path, cx, cond, true, &id));
    assert(id == 0);

    check(bw_engine_run(engine, cx, roots, 2, NULL, path, out));
    expect(cx, out[0].expr, "x * y");
    assert(out[0].end == BW_END_COMPLETED && out[0].relies_on == 0);
    expect(cx, out[1].expr, "x + y");
    assert(out[1].relies_on == 1); /* bit 0: constraint 0 */

    bw_assumptions_free(path);
    bw_engine_free(engine);
    bw_context_free(cx);
    return 0;
}
```

### Deciding branches

`bw_prove` and `bw_prove_cmp` answer `BW_TRUE`, `BW_FALSE` or `BW_UNKNOWN`; `bw_facts_of` says
what is known about a value:

```c
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "bitwright.h"

static void check(bw_status s) {
    if (s != BW_OK) {
        fprintf(stderr, "bitwright error %d: %s\n", s, bw_last_error());
        exit(1);
    }
}

int main(void) {
    bw_context *cx = bw_context_new();
    bw_expr odd, low, limit, input;
    bw_proof p;
    bw_facts f;

    check(bw_parse(cx, "((x | 1) & 1) == 1", 32, &odd));
    check(bw_prove(cx, odd, NULL, &p));
    assert(p.truth == BW_TRUE);

    check(bw_parse(cx, "x & 0xff", 32, &low));
    check(bw_const_u64(cx, 32, 0x100, &limit));
    check(bw_prove_cmp(cx, BW_ULT, low, limit, NULL, &p));
    assert(p.truth == BW_TRUE);

    check(bw_parse(cx, "x >u 100", 32, &input));
    check(bw_prove(cx, input, NULL, &p));
    assert(p.truth == BW_UNKNOWN);

    /* The low byte, shifted up by 4, then with bit 0 set. */
    check(bw_parse(cx, "(x & 0xff) << 4 | 1", 32, &low));
    check(bw_facts_of(cx, low, NULL, &f));
    assert(f.known_one.limbs[0] == 1 && f.known_zero.limbs[0] == 0xfffff00e);
    assert(f.umin.limbs[0] == 1 && f.umax.limbs[0] == 0xff1 && f.ustride == 16);

    bw_context_free(cx);
    return 0;
}
```

### An SMT-LIB script in, a simplified one out

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
    const char *script = "(declare-const a (_ BitVec 32))\n"
                         "(declare-const b (_ BitVec 32))\n"
                         "(define-fun t () (_ BitVec 32) (bvadd (bvxor a b) (bvmul #x00000002 "
                         "(bvand a b))))\n";
    bw_context *cx = bw_context_new();
    bw_engine *engine = bw_engine_new(BW_PRESET_DEOBFUSCATE);
    bw_smt_import *imp;
    bw_expr t, s;
    const char *name;
    char *out;

    check(bw_smtlib_import(cx, script, &imp));
    assert(bw_smt_import_count(imp, BW_SMT_SYMBOLS) == 2);
    assert(bw_smt_import_count(imp, BW_SMT_DEFINITIONS) == 1);
    check(bw_smt_import_get(imp, BW_SMT_DEFINITIONS, 0, &t, &name));
    assert(strcmp(name, "t") == 0);
    bw_smt_import_free(imp);

    check(bw_simplify(engine, cx, t, &s));
    check(bw_smtlib_export(cx, &s, 1, &out));
    /* root0 is (bvadd |a| |b|): the MBA is gone. */
    assert(strstr(out, "(define-fun root0 () (_ BitVec 32)") != NULL);
    assert(strstr(out, "bvadd") != NULL && strstr(out, "bvand") == NULL);
    bw_string_free(out);

    bw_engine_free(engine);
    bw_context_free(cx);
    return 0;
}
```

## C++

### Flags from a lifter

The `jl` of the Python example, and the carry flag of an unsigned compare, built with the C++
wrapper's operators:

```cpp
#include <cassert>

#include "bitwright.hpp"

namespace bw = bitwright;

int main() {
    bw::Context cx;
    bw::Expr a = cx.symbol("a", 32), b = cx.symbol("b", 32);
    bw::Engine engine = bw::Engine::standard();

    // cmp a, b
    bw::Expr diff = a - b;
    bw::Expr sf = diff.extract(31, 1);
    bw::Expr of = ((a ^ b) & (a ^ diff)).extract(31, 1);
    bw::Expr cf = a.ult(b);
    bw::Expr zf = diff.eq(diff.constant(0));

    assert(engine.simplify(sf ^ of).str() == "a <s b");  // jl
    assert(engine.simplify(cf | zf).str() == "a <=u b"); // jbe
    assert(engine.simplify(~cf & ~zf).str() == "b <u a"); // ja
    return 0;
}
```

### Proofs, invertibility and budgets

```cpp
#include <cassert>

#include "bitwright.hpp"

namespace bw = bitwright;

int main() {
    bw::Context cx;
    bw::Expr k = cx.symbol("k", 8);

    // A keyed mixer is a bijection of its key, so a check against a constant has one solution.
    bw::Expr h = (k ^ 0x5a) * 0x1d;
    assert(bw::prove_injective(h, k, true));
    assert(bw::Engine::standard().simplify(h.eq(k.constant(0x33))).str() == "k == -43");

    // Opaque predicates, under a path condition.
    bw::Assumptions path;
    uint32_t small = path.assume(k.ult(k.constant(16)));
    bw::Proof p = bw::prove((k & 0xf0).eq(k.constant(0)), &path);
    assert(p.truth == bw::Truth::True && p.relies_on == (uint64_t{1} << small));
    assert(bw::prove(k.ugt(k.constant(100))).truth == bw::Truth::Unknown);

    // A budget bounds the work; a stopped result is correct, just not final.
    bw::Expr mba = cx.parse("(x & y) * (x | y) + (x & ~y) * (~x & y)", 64);
    bw::Budget none;
    none.node_visits = 0;
    bw::Engine deob = bw::Engine::deobfuscate();
    assert(deob.run({mba}, &none)[0].end == bw::End::Budget);
    std::vector<bw::Outcome> out = deob.run({mba});
    assert(out[0].end == bw::End::Completed && out[0].expr.str() == "x * y");
    return 0;
}
```

### Floating point

```cpp
#include <cassert>

#include "bitwright.hpp"

namespace bw = bitwright;

int main() {
    bw::Context cx;
    bw::Expr x = cx.symbol("x", 32), y = cx.symbol("y", 32);
    bw::Engine engine = bw::Engine::standard();

    // ucomiss x, y; ja
    bw::Expr unordered = x.fisnan(bw::F32) | y.fisnan(bw::F32);
    bw::Expr cf = x.flt(y, bw::F32) | unordered, zf = x.feq(y, bw::F32) | unordered;
    assert(engine.simplify(~cf & ~zf).str() == "fp.lt.f32(y, x)");

    // An integer converted to a double: never a NaN, so multiplying it by 1.0 is a no-op.
    bw::Expr i = cx.symbol("i", 32);
    bw::Expr d = i.to_float(bw::F64);
    bw::Expr one = d.constant(0x3ff0000000000000);
    assert(engine.simplify(d.fmul(one, bw::F64)) == d);
    // Dividing by 4.0 is multiplying by 0.25, exactly.
    bw::Expr four = d.constant(0x4010000000000000);
    assert(engine.simplify(d.fdiv(four, bw::F64)).str() ==
           "fp.mul.rne.f64(fp.from_sbv.rne.f64(i), 0x3fd0000000000000)");
    return 0;
}
```
