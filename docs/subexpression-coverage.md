# Where equivalent expressions diverge

The measurements below are the baseline on Bitwright 0.32.23 (`cc252b6`), with x64 and ARM64 as the target architectures.
Two different failures show up. A register relationship can disappear while importing lifted code.
A relationship present in well-formed IL can also be provable and still fail to simplify a caller.
The fixes belong at different boundaries.

## A register relationship lost during lifting

I assembled two small blocks with LLVM and translated their bytes with the Ghidra SLEIGH languages
bundled in pypcode 3.3.3. For each translation I retained all operations other than instruction
markers. I passed the same varnodes to `bitwright lift` twice, using register names or numeric
register-space offsets. Both machine-code blocks set the observed destination to 1.

| Block | Bytes in instruction order | Result with names | Result with offsets |
|---|---|---|---|
| ARM64, `mov x0, #1` then `mov w1, w0` | `200080d2 e103002a` | `x1 = zext<64>(w0)` | `reg_0x4008 = 1:64` |
| x64, `mov rax, 1` then `mov ecx, eax` | `48c7c001000000 89c1` | `RCX = 1:64` | `reg_0x8 = 1:64` |

The ARM64 lift already contains the destination zero-extension. The failure is on the **read**.
Writing eight bytes at register offset `0x4000` defines the next four-byte read at that offset.
In the named input those two varnodes are `x0` and `w0`. Bitwright's name resolver knows the x64
aliases and gives each unknown name its own storage. The Ghidra script prefers names when Ghidra
supplies them. The named result therefore admits an impossible input. The reproducer exercises
the Rust text importer and the name/offset encodings, independently of the Ghidra UI.
[Register resolver](../bitwright/src/lift/mod.rs) · [P-code reader](../bitwright/src/lift/pcode.rs) ·
[Ghidra adapter](../tools/plugins/ghidra_bitwright.py) · [Ghidra varnode semantics](https://ghidra.re/ghidra_docs/languages/html/pcoderef.html)

Use register-space identity, byte offset and size from the lifter as the semantic key. Carry the
name separately for display. A named-only interface needs the target's register layout. Keep the
explicit destination write emitted by the lifter. A raw four-byte p-code `COPY` writes four bytes.
At the ISA level a write to `W1` or a normal 32-bit x64 GPR result clears the destination's upper
32 bits. A write to `AL` or `AX` preserves the remaining bits. These distinctions must survive
translation before a generic solver can reason about them.
[Arm register semantics](https://developer.arm.com/-/media/Arm%20Developer%20Community/PDF/Learn%20the%20Architecture/Armv8-A%20Instruction%20Set%20Architecture.pdf) · [Intel SDM, vol. 1 §3.4.1.1](https://cdrdv2-public.intel.com/868137/325462-089-sdm-vol-1-2abcd-3abcd-4.pdf)

## Equivalent IL, different outcomes

For each pair `p,q`, ask the simplifier for `p == q`, then for `(p & z) + (q | z) - p` with a
fresh word `z`. The expected answers are `1:1` and `z`, respectively. Repeating either
spelling in both positions recovers `z` for every row and both configurations. Each measurement
starts in a fresh context. The circuit prover, with simplification disabled, produced a checked
certificate for every pair in this table. A miss means the strategy completed with ordinary
budgets, without hitting its round cap, and left a nontrivial expression.

| Equivalent pair | Default equality | Default parent | Opaque sweep equality | Opaque sweep parent |
|---|---|---|---|---|
| Add at 8 bits then zero-extend, or add at 16 bits then mask | hit | hit | hit | hit |
| Low-byte left shift by 3, written at either width | hit | hit | hit | hit |
| Left shift of an 8-bit word by a variable, written at 8 or 16 bits with the result masked | miss | miss | hit | miss |
| 32-bit variable shift masked by 31, computed at 32 or 64 bits | miss | miss | hit | miss |
| Leading-zero count at 8 bits, or at 16 bits after zero-extension with the extra 8 subtracted | miss | miss | hit | hit |
| Unsigned division before or after zero-extension, divisor forced odd | miss | miss | hit | hit |
| Unsigned remainder before or after zero-extension, divisor unrestricted | miss | miss | hit | hit |
| Rotate the low byte by 4, or assemble it with shifts and masks | hit | miss | hit | hit |
| Rotate the low 32 bits by 16, or assemble them with shifts and masks | hit | miss | hit | hit |
| Bit 7 of a sum, or XOR of the operand bits and the carry from the lower seven bits | miss | hit | hit | hit |
| Select either word's low byte when the bytes agree, with the same fallback in both expressions | miss | miss | hit | miss |
| `(x << k) << u` and `(x << u) << k`, at 16 bits | miss | miss | miss | miss |

Three observations narrow down the causes.

1. **A consumer can change which equality is found.** In the byte-rotation comparison, the trace
   shows `Invert` exposing a narrow equality and `Compares` discharging it. In the arithmetic
   parent, `Shuffle` constructs a concat and the two spellings survive. An API that asks about two
   projected operands could let the second caller use the same reasoning.
2. **Liveness influences which algebra is available.** The carry comparison stays open on its own,
   with an unrelated live root, and with its left operand live. Keeping just its right operand as
   a second output makes the comparison fold to true. The trace then shows `Casts` distribute a
   one-bit extract over XOR and `Words` discharge the equality. Alone, the earlier factoring rule
   leaves the extract outside XOR. Both runs complete. This favors allowing a proof procedure to
   read an alternative spelling without requiring that spelling to win a rewrite on the live DAG.
3. **Width changes what operations mean.** The default folds
   `rotl(rotl(x,k),u) == rotl(rotl(x,u),k)` at 8, 16, 32, 64 and 128 bits. It misses at the
   adjacent widths tested, including 31, 33, 63 and 65. Checked certificates at widths 7, 8 and 9
   confirm both sides of the first transition. Rotations commute at every width. The current
   shuffle rule adds counts in a machine word, which is valid for power-of-two rotation widths.
   At width 9, counts 511 and 1 sum to zero in nine-bit arithmetic, but their combined rotation
   is by 8. Canonically ordering two rotation counts could recognize this identity without ever
   forming the overflowing sum. [Variable-rotation pass](../bitwright/src/engine/pass/shuffle.rs)

Ordinary reordering was a useful control. In a separate exploratory run, the default recovered all
70 answers obtained by regrouping and permuting sums, products, XORs, ANDs and ORs over 3, 4, 5,
6, 8, 10 and 12 distinct 16-bit operands, tested in both query shapes. That points attention to
crossing an operator, width, guard or consumer boundary.

## What the target ISA changes in the IL

For a 32-bit x64 scalar `SHL` with a register count, or an ARM64 `LSLV` on W registers, the
effective count uses the low five bits. Both can be expressed as `a:32 << (b:32 & 31)` for the
value result. Bitwright's bare logical shift yields zero when its count reaches the width.
With `a = 1, b = 32`, the machine operation gives 1 and the bare IL shift gives 0. Encode the
mask during lifting so the generic solver can use it as a fact. Track live flags separately.
[Intel shift semantics](https://cdrdv2-public.intel.com/835757/325383-sdm-vol-2abcd.pdf) · [Arm scalar shifts](https://developer.arm.com/-/media/Files/pdf/graphics-and-multimedia/ARMv8_InstructionSetOverview.pdf) · [Bitwright semantics](../book/src/semantics.md)

Even with that mask present, the 32/64-bit row above still misses. Both sides below fit in a
zero-extended 32-bit destination. The outstanding question is how a reader at 64 bits recognizes
the computation on the low 32.

```text
p = zext<64>(a:32 << (b:32 & 31))
q = (zext<64>(a:32) << (zext<64>(b:32) & 31)) & 0xffffffff
```

The architectural change worth testing is a common description of **which bits a use reads and
which operation produced them**. A shift needs its effective count. A low sum depends on the
low operands, and a higher slice can need a carry from below. A guarded byte equality can be used
in the selected arm. For example, equality of two low bytes licenses exchanging `x & 255` and
`y & 255` there. Exchanging full-width `x` and `y` can change the answer. The replay includes
counterexamples to that stronger claim and to four other tempting shortcuts.

For x64/ARM64, prioritize pairs arising from 8-, 16- and 32-bit values used in a 64-bit register,
plus flags, carry bits and fields of intermediate width. Compare named and numeric lifts before
measuring solver coverage. Then measure equality, a parent using that equality, and a second live
output at the same budget. These checks distinguish missing machine semantics, missing word-level
relations and rewrites that happen only under a particular sharing pattern.

## Replay

The regression suite now requires the expected answer for every row of the baseline table in
both configurations. It also checks the four carry liveness cases, rotations at all 15 tested
widths and the named and numeric register encodings. The five counterexamples are checked again
after simplification.

The cast pass can narrow the shift when the count fits in the narrower word. It can also narrow
unsigned remainder and division with a known nonzero divisor. The shuffle pass orders variable
counts without summing them at odd widths and removes bit permutations beneath popcount.
For small mixed-width computations, the demanded-bits pass tests candidate peers with the
circuit oracle. Successful same-width proofs can be reused by a comparison, by a masked query,
or when rebuilding a parent. The pass keeps the existing cost check against the live outputs.
The whole-root search covers integer DAGs of up to 48 nodes and words up to 64 bits, subject
to the strategy's region limit. A larger DAG can still nominate a small pair through demanded
bits. Each sweep gets up to eight circuit questions, with a shared allowance across the call.
[Relation discovery and proof limits](../bitwright/src/engine/pass/views.rs)

```sh
cargo test --release --locked -p bitwright --test equivalence_audit
```

The register fixtures use the p-code from the two translations above and run without an
external lifter.
[Replay source and exact expressions](../bitwright/tests/equivalence_audit.rs)
