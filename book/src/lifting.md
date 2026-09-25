# Lifted code

A disassembler or a lifter turns machine code into an IR; `bitwright::lift` reads three of them
into expressions, so that what a block computes can be simplified, compared or proved:

- **p-code**, Ghidra's IR, one operation per line, varnodes `(space, offset, size)` as Ghidra
  prints them, or with a register name for the offset (`(register, RAX, 8)`);
- **VEX**, the IR of Valgrind and angr, as pyvex prints an IRSB;
- **LLVM IR** functions (feature `prove`), with loads, stores and `getelementptr` over one flat
  memory.

A block becomes a `Block`: the registers it reads before writing them (symbols named after
them), the final value of each register it writes, its stores, its conditional exits, and
where it continues. Registers are read and written by byte range, so x86-64's `eax`, `ax`,
`al` and `ah` are parts of `rax`; memory is a [memory](memory.md), so a value stored and loaded
back is the value. One block is read straight through: an exit is recorded, and the code after
it runs as if the exit was not taken.

```rust
use bitwright::engine::Engine;
use bitwright::lift::{pcode, vex};
use bitwright::Context;

let mut cx = Context::new();
// An MBA, as pyvex prints the IRSB of `(x & y) * (x | y) + (x & ~y) * (~x & y)`.
let block = vex(
    &mut cx,
    "t0 = GET:I64(rdi)
     t1 = GET:I64(rsi)
     t2 = And64(t0,t1)
     t3 = Or64(t0,t1)
     t4 = Mul64(t2,t3)
     t5 = Not64(t1)
     t6 = And64(t0,t5)
     t7 = Not64(t0)
     t8 = And64(t7,t1)
     t9 = Mul64(t6,t8)
     t10 = Add64(t4,t9)
     PUT(rax) = t10",
)?;
let engine = bitwright::engine::Engine::builder()
    .builtin()
    .strategy(bitwright::engine::Strategy::deobfuscate().with_mba(Default::default()))
    .build()?;
let rax = engine.simplify(&mut cx, block.register("rax").unwrap())?;
assert_eq!(cx.display(rax.expr).to_string(), "rdi * rsi");

// A stack spill in p-code, Ghidra's register offsets: the reload is the spilled value.
let block = pcode(
    &mut cx,
    "(register, 0x20, 8) = INT_SUB (register, 0x20, 8) , (const, 0x8, 8)
     STORE (const, 0x1b1, 4) , (register, 0x20, 8) , (register, 0x38, 8)
     (register, 0x0, 8) = LOAD (const, 0x1b1, 4) , (register, 0x20, 8)
     (register, 0x0, 8) = INT_ADD (register, 0x0, 8) , (const, 0x1, 8)",
)?;
let rax = Engine::standard().simplify(&mut cx, block.register("reg_0x0").unwrap())?;
assert_eq!(cx.display(rax.expr).to_string(), "reg_0x38 + 1");
# Ok::<(), Box<dyn std::error::Error>>(())
```

`bitwright lift file.vex` (or `.pcode`, `.ll`, or `--from`) prints each register a block writes,
each store and each exit, deobfuscated; `--synth` also searches for a smaller equal expression.
A call, a helper VEX leaves opaque (an unknown value, for a helper call such as a flag
computation), a loop or an operation outside the front end's subset is reported, not guessed.

[`tools/plugins/`](https://github.com/valeria-org/bitwright/tree/main/tools/plugins) has scripts
for Ghidra (p-code), Binary Ninja (its low-level IL) and IDA Pro with Hex-Rays (the ctree) that
hand the code at the cursor to the Python package. They are written against each tool's
documented API and are not tested, as none of the tools is available where bitwright is
developed.
