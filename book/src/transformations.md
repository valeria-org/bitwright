# Verifying compiler transformations

`bitwright::transform` (feature `prove`) proves that one program *refines* another under
LLVM's semantics: whatever the target may do, the source may do too. It reads peephole
transformations in the syntax the Alive paper introduced (Lopes et al., PLDI 2015), and pairs
of functions in a subset of LLVM IR (translation validation); it infers preconditions; and
when a transformation is wrong it shows why, with inputs small enough to read, as LLVM IR
constants.

## A first proof, step by step

Say a compiler turns unsigned division by a constant into a shift. Write the rewrite in a
file, `div.opt`: the source instructions, `=>`, and the target instructions. `%x` is an input,
`C` a symbolic constant (any value, the same on both sides), and no type is given, so every
width is checked:

```text
Name: udiv by a power of two
%r = udiv %x, C
  =>
%r = lshr %x, log2(C)
```

`bitwright prove div.opt` answers with a counterexample at the smallest width where one
exists:

```text
INVALID      udiv by a power of two
the values differ (i2)
  %x = i2 -2
  C = i2 -1
source:
  %r = i2 0
target:
  %r = i2 1
source result: i2 0
target result: i2 1

0 valid, 1 invalid, 0 not decided
```

Values are printed as LLVM IR constants, which are signed: at two bits, `-2` is 2 and `-1` is
3. So 2 / 3 is 0, but `log2(3)` is 1 and 2 >> 1 is 1. The rewrite needs a condition on `C`.
`bitwright infer div.opt` finds one:

```text
Pre: isPowerOf2OrZero(C)
             udiv by a power of two  (weakest found; 14 valid and 258 invalid examples)
```

Zero is allowed because dividing by zero is undefined behavior in the source, and a target may
do anything where its source is undefined. Add the condition as a `Pre:` line and prove again:

```text
Name: udiv by a power of two
Pre: isPowerOf2OrZero(C)
%r = udiv %x, C
  =>
%r = lshr %x, log2(C)
```

```text
$ bitwright prove div.opt
unknown      udiv by a power of two  (i64: no answer within 200000 conflicts)
```

Every width up to 32 was proved, but 64-bit division is too large a circuit for the solver's
default budget. The answer is unknown, never valid. Name the widths you care about with
`--widths`, or give the type (`%r = udiv i32 %x, C`), or raise `--conflicts`:

```text
$ bitwright prove --widths 1,2,3,4,5,6,7,8,16,32 div.opt
valid        udiv by a power of two  (i1; i2; i3; i4; i5; i6; i7; i8; i16; i32)

1 valid, 0 invalid, 0 not decided
```

`bitwright prove` exits with 0 only when every transformation in the file is valid, so a
file of transformations can be checked in CI as it is. The same check from Rust, as a test
(with `include_str!("transforms.opt")` in place of the text):

```rust
use bitwright::transform::{Config, Verdict, parse_transforms, verify};

let text = "
Name: udiv by a power of two
Pre: isPowerOf2OrZero(C)
%r = udiv %x, C
  =>
%r = lshr %x, log2(C)
";
let cfg = Config::default().with_widths(vec![1, 2, 3, 4, 5, 6, 7, 8, 16]);
for t in parse_transforms(text)? {
    let report = verify(&t, &cfg);
    // A report prints as `bitwright prove` does, counterexample included.
    assert!(matches!(report.verdict(), Verdict::Valid), "{report}");
}
# Ok::<(), Box<dyn std::error::Error>>(())
```

The rest of this chapter describes each part: what "valid" means, the syntax, inference,
whole functions, and floating point.

## Refinement

A value is its bits and a poison flag. A program also has undefined behavior, a condition on
its inputs. For every input (each may be a value or poison, unless `noundef`), the target is
correct when the source has undefined behavior, or when the target has none and either the
source is poison or both give the same value and the target is not poison:

```text
∀ inputs, target choices. ∃ source choices.
    ub_src ∨ (¬ub_tgt ∧ (poison_src ∨ (¬poison_tgt ∧ value_tgt = value_src)))
```

The choices are what LLVM leaves open: each use of `undef`, the value of a frozen poison, the
sign and payload of a NaN a floating-point operation returns, the sign of a zero under `nsz`,
whether `llvm.fmuladd` fuses. The source's are chosen for it; the target's are any. The
question is decided by counterexample-guided search over bitwright's own SAT solver: a
candidate input that no source choice found so far answers, then a source choice that answers
it or a proof that none does.

The semantics come from LLVM's language reference: poison from `nsw`, `nuw`, `exact`,
`disjoint`, `nneg`, `samesign` and `trunc`'s flags, from shifts past the width and from
`select` on poison; undefined behavior from division by zero or by poison, `INT_MIN / -1`
(a poison dividend included), a branch on poison, `unreachable`, a false `llvm.assume`, and
returning poison from a `noundef` function.

## Transformations

A transformation is an optional `Name:`, an optional `Pre:` condition, the source
instructions, `=>`, and the target instructions. Registers the source reads without defining
them are inputs; words in operands (`C`, `C1`) are symbolic constants, the same in both
programs and never poison; operands may be constant expressions (`-C`, `C1 + C2`,
`log2(C)`, `width(%x)`). Types may be omitted: they are inferred, and each width left open
is checked in turn (1 to 8, 16, 32 and 64 bits; half, float and double), smallest first.

```rust
use bitwright::transform::{Config, Mismatch, Verdict, parse_transforms, verify};

let text = "
Name: PR20186
%a = sdiv %X, C
%r = sub 0, %a
  =>
%r = sdiv %X, -C

Name: mul by a power of two
Pre: isPowerOf2(C)
%r = mul %x, C
  =>
%r = shl %x, log2(C)
";
let ts = parse_transforms(text)?;
let cfg = Config::default();
// Negating a quotient is not dividing by the negated divisor: INT_MIN / -1 is undefined.
match verify(&ts[0], &cfg).verdict() {
    Verdict::Invalid(cx) => {
        assert_eq!(cx.mismatch, Mismatch::TargetUb);
        assert_eq!(cx.types, "i2"); // the smallest width where it fails
    }
    v => panic!("{v:?}"),
}
assert!(matches!(verify(&ts[1], &cfg).verdict(), Verdict::Valid));
# Ok::<(), Box<dyn std::error::Error>>(())
```

`bitwright prove file.opt` checks every transformation of a file:

```text
INVALID      PR20186
the target has undefined behavior where the source has none (i2)
  %X = i2 -2
  C = i2 1
source:
  %a = i2 -2
  %r = i2 -2
target:
  %r = i2 -2
the target's undefined behavior
valid        mul by a power of two  (i1; i2; i3; i4; i5; i6; i7; i8; i16; i32; i64)
```

A counterexample is made small before it is shown: inputs that need not be poison are not,
values are 0, 1 or −1 when they can be, and otherwise have as few significant bits as they
can. `select c, x, false` is not `and c, x`:

```text
INVALID      select to and
the target is poison where the source is not
  %c = i1 false
  %x = i1 poison
```

and `freeze` repairs it (`%f = freeze %x`, `%r = and %c, %f`). The target may use the
source's registers; those instructions stay in the target program.

A counterexample lists the inputs and symbolic constants, then each named value of the source
and of the target at those inputs, then the results. When the source makes choices (an `undef`,
a `freeze`, a NaN), the source values shown are one of its executions, and none of its
executions matches the target; the report says so on its last line.

The precondition language has `&&`, `||`, `!`, signed comparisons (`<`, `<=`, …), unsigned
ones (`u<`, `u<=`, …), and the predicates `isPowerOf2`, `isPowerOf2OrZero`, `isSignBit`,
`isMask`, `isShiftedMask`, `MaskedValueIsZero(%x, C)` and the `WillNotOverflow{Signed,Unsigned}{Add,Sub,Mul,Shl}`
family, each read as what it states about the values. Constant expressions have `+ - * & | ^
<< >> u>> / /u %`, `~` and `-`, and the functions `abs`, `log2`, `width`, `trunc`, `zext`,
`sext`, `umax`, `umin`, `smax`, `smin`, `countLeadingZeros`, `countTrailingZeros`,
`popcount`, `udiv`, `urem`, `sdiv`, `srem`.

## Precondition inference

`transform::infer` (`bitwright infer file.opt`) finds the condition on the symbolic constants
under which a transformation holds, from data, as Alive-Infer does (Menendez and Nagarakatte,
PLDI 2017): the prover sorts values of the constants into valid and invalid ones (every value
at small widths, a sample otherwise), a formula over a vocabulary of predicates is learned that
excludes every invalid value and admits as many valid ones as it can, and the transformation
is then verified with it at every width. A failure at another width adds that width's values
and learns again.

```rust
use bitwright::transform::{Config, Verdict, infer, parse_transforms};

let ts = parse_transforms(
    "%a = sdiv i8 %X, C
     %r = sub 0, %a
       =>
     %r = sdiv %X, -C",
)?;
let i = infer(&ts[0], &Config::default()).map_err(|e| e.to_string())?;
// Valid except where the negation or the division overflows.
assert_eq!(i.pre.as_deref(), Some("C != 1 && !isSignBit(C)"));
assert!(i.weakest);
assert!(matches!(i.report.unwrap().verdict(), Verdict::Valid));
# Ok::<(), Box<dyn std::error::Error>>(())
```

Disjunctions come out too: two shifts by constants are one shift when either amount is past the
width (the source is poison) or both and their sum are within it.

From the command line, each transformation gets a `Pre:` line (or `none`) and a summary:
whether the condition is the weakest the examples allow, and how many valid and invalid
values were seen. The condition is then verified at every width, so the budget limits
of `prove` apply. Without the `i8` above, PR20186 is inferred but not verified:

```text
Pre: C != 1 && !isSignBit(C)
             PR20186  not decided: i16: no answer within 200000 conflicts
```

Give division and multiplication a type, or narrow `--widths`, when inferring.

## Translation validation

`bitwright tv before.ll after.ll` checks that each function of the second file refines the
function of the same name in the first; `bitwright tv pair.ll` checks that `@tgt` refines
`@src`. Parameters are the inputs, matched by position.

### Checking an optimizer

Take `before.ll`:

```text
define i32 @clamp(i32 %x) {
entry:
  %neg = icmp slt i32 %x, 0
  br i1 %neg, label %zero, label %high
zero:
  ret i32 0
high:
  %big = icmp sgt i32 %x, 255
  %r = select i1 %big, i32 255, i32 %x
  ret i32 %r
}

define i32 @avg(i32 %a, i32 %b) {
  %x = and i32 %a, %b
  %y = xor i32 %a, %b
  %h = lshr i32 %y, 1
  %r = add i32 %x, %h
  ret i32 %r
}

define i1 @bits(i8 %x) {
  %m = and i8 %x, 12
  %c = icmp eq i8 %m, 12
  %n = and i8 %x, 4
  %d = icmp ne i8 %n, 0
  %r = and i1 %c, %d
  ret i1 %r
}
```

Optimize it and validate each function:

```text
$ clang -x ir -O2 -S -emit-llvm before.ll -o after.ll
$ bitwright tv before.ll after.ll
valid        clamp
valid        avg
valid        bits

3 valid, 0 invalid, 0 not decided
```

clang made `@clamp` a `smax` and a `umin` with a `range(i32 0, 256)` return attribute, and
`@bits` a single test of both bits. Attributes, metadata and declarations that the check
does not need are skipped. To check one pass rather than a pipeline, run `opt` instead:
`opt -passes=instcombine -S before.ll -o after.ll`.

A wrong rewrite fails. Here `after.ll`'s `@avg` has `add nsw` in place of `add`:

```text
$ bitwright tv before.ll after.ll
valid        clamp
INVALID      avg
the target is poison where the source is not
  %a = i32 1
  %b = i32 -1
source:
  %x = i32 1
  %y = i32 -2
  %h = i32 2147483647
  %r = i32 -2147483648
target:
  %x = i32 1
  %y = i32 -2
  %h = i32 2147483647
  %r = i32 poison
source result: i32 -2147483648
target result: i32 poison
valid        bits

2 valid, 1 invalid, 0 not decided
```

The average never wraps as unsigned, so `add nuw` validates; it can wrap as signed.

`tv` reads functions in SSA form. clang's `-O0` output keeps each local variable in stack
memory (`alloca`, `load`, `store`), which is outside the subset, so promote the variables to
registers first:

```text
$ clang -O0 -Xclang -disable-O0-optnone -S -emit-llvm f.c -o f0.ll
$ opt -passes=sroa -S f0.ll -o before.ll
$ clang -x ir -O2 -S -emit-llvm before.ll -o after.ll
$ bitwright tv before.ll after.ll
```

(`-disable-O0-optnone` keeps clang from marking the functions `optnone`, which `opt` would
leave alone.) `tools/tv-fuzz` in the repository runs this check at scale: random functions
optimized by clang, and mutants of the results, which bitwright must call invalid at inputs
an independent interpreter confirms.

### From Rust

`transform::pairs` reads the two modules (or one with `@src` and `@tgt`) into
transformations, which `verify` checks as it checks the Alive syntax:

```rust
use bitwright::transform::{Config, Mismatch, Verdict, pairs, verify};

let before = "
define i32 @avg(i32 %a, i32 %b) {
  %x = and i32 %a, %b
  %y = xor i32 %a, %b
  %h = lshr i32 %y, 1
  %r = add i32 %x, %h
  ret i32 %r
}";
let after = "
define i32 @avg(i32 %a, i32 %b) {
  %x = and i32 %b, %a
  %y = xor i32 %b, %a
  %h = lshr i32 %y, 1
  %r = add nsw i32 %h, %x
  ret i32 %r
}";
let fixed = after.replace("add nsw", "add nuw");
let cfg = Config::default();
let bad = &pairs(before, Some(after))?[0];
match verify(bad, &cfg).verdict() {
    Verdict::Invalid(cx) => assert_eq!(cx.mismatch, Mismatch::TargetPoison),
    v => panic!("{v:?}"),
}
let good = &pairs(before, Some(&fixed))?[0];
assert!(matches!(verify(good, &cfg).verdict(), Verdict::Valid));
# Ok::<(), Box<dyn std::error::Error>>(())
```

### The subset

The subset: integers and `half`, `bfloat`, `float`, `double` and `fp128`; every arithmetic,
bitwise, shift, comparison, conversion and `select` instruction with its flags, `freeze`,
`phi`, and acyclic control flow (`br`, `switch`, `ret`, `unreachable`); the intrinsics
`umin`, `umax`, `smin`, `smax`, `abs`, `ctpop`, `ctlz`, `cttz`, `bswap`, `bitreverse`,
`fshl`, `fshr`, the saturating additions and subtractions, `assume`, `fabs`, `copysign`,
`sqrt`, `fma`, `fmuladd`, `minnum`, `maxnum`, `minimum`, `maximum`, `minimumnum`,
`maximumnum`, `floor`, `ceil`, `trunc`, `round`, `roundeven`, `rint` and `nearbyint`; the
attributes `noundef`, `range` and `nofpclass` on parameters and return values. Loops, memory
and calls to other functions are outside it.

Branching on poison is undefined, selecting on it is not, so branches that merge into a
`select` are a valid rewrite and the reverse is not. With both functions in `pair.ll`:

```text
define i8 @src(i8 %x, i1 %c) {
entry:
  br i1 %c, label %a, label %b
a:
  %y = add i8 %x, 1
  br label %m
b:
  %z = sub i8 %x, 1
  br label %m
m:
  %r = phi i8 [ %y, %a ], [ %z, %b ]
  ret i8 %r
}

define i8 @tgt(i8 %x, i1 %c) {
  %d = select i1 %c, i8 1, i8 -1
  %r = add i8 %x, %d
  ret i8 %r
}
```

`bitwright tv pair.ll` finds it valid. With `@src` and `@tgt` swapped, the branch is on a
poison `%c` where the `select` only returned poison:

```text
INVALID      src => tgt
the target has undefined behavior where the source has none
  %x = i8 0
  %c = i1 poison
source:
  %d = i8 poison
  %r = i8 poison
target:
  %z = i8 -1
  %y = i8 1
  %r = i8 -1
the target's undefined behavior
```

Each value is shown as the program computes it at the counterexample, whether its block runs
or not.

## Floating point

Values follow IEEE 754 in the default environment (round to nearest, subnormals kept). A NaN
an operation returns has any sign, and a quiet bit and payload that are preferred (quiet, zero
payload) or copied from a NaN operand (quieted or unchanged; `fpext` and `fptrunc` keep a
payload's high bits), as the language reference says; `fneg`, `fabs` and `copysign` only
touch the sign. So `fadd %x, -0.0` is `%x` (a NaN result may be the operand itself), and
`%x` is not `fmul %x, 1.0` (whose NaN sign is free). `frem` is `fmod`.

Of the fast-math flags, `nnan` and `ninf` make NaNs and infinities among the operands and the
result poison, and `nsz` lets zero operands flip sign (so `fadd nsz %x, 0.0` is `%x`). The
flags whose meaning is which rewrites are allowed, `reassoc`, `arcp`, `contract` and `afn`,
are not modeled: a transformation that needs them is checked against exact IEEE semantics and
reported invalid.

Open floating-point types are checked as `half`, `float` and `double`. A file of the usual
suspects:

```text
Name: add -0.0
%r = fadd %x, -0.0
  =>
%r = %x

Name: add +0.0
%r = fadd %x, 0.0
  =>
%r = %x

Name: add +0.0, nsz
%r = fadd nsz %x, 0.0
  =>
%r = %x

Name: x - x
%r = fsub %x, %x
  =>
%r = 0.0

Name: x - x, nnan
%r = fsub nnan %x, %x
  =>
%r = 0.0

Name: double negation to multiply by 1
%a = fneg %x
%r = fneg %a
  =>
%r = fmul %x, 1.0
```

```text
valid        add -0.0  (half; float; double)
INVALID      add +0.0
the values differ (half)
  %x = half -0.0
source:
  %r = half 0.0
target:
  %r = half -0.0
source result: half 0.0
target result: half -0.0
(the source's choices shown are one of its executions; none matches)
valid        add +0.0, nsz  (half; float; double)
INVALID      x - x
the values differ (half)
  %x = half 0xH7C00 (+inf)
source:
  %r = half 0xH7E00 (NaN)
target:
  %r = half 0.0
source result: half 0xH7E00 (NaN)
target result: half 0.0
(the source's choices shown are one of its executions; none matches)
valid        x - x, nnan  (half; float; double)
INVALID      double negation to multiply by 1
the values differ (half)
  %x = half 0xH7E00 (NaN)
source:
  %a = half 0xHFE00 (NaN)
  %r = half 0xH7E00 (NaN)
target:
  %r = half 0xHFE00 (NaN)
source result: half 0xH7E00 (NaN)
target result: half 0xHFE00 (NaN)

3 valid, 3 invalid, 0 not decided
```

−0.0 + +0.0 is +0.0, so adding +0.0 is not the identity until `nsz` makes the sign of a zero
free. ∞ − ∞ is NaN, so `x - x` is 0.0 only when `nnan` makes a NaN result poison (`ninf` is
not needed: a NaN from infinite operands is already covered by `nnan`). `fneg` only flips the
sign, so negating twice gives `%x` back bit for bit, while `fmul` may return a NaN of either
sign. Floating-point values print as LLVM writes them: a short exact decimal when there is
one, else the hexadecimal encoding, with NaNs and infinities named in parentheses.

A rewrite that `reassoc` permits is still checked exactly, and fails:

```text
Name: reassociate
%a = fadd reassoc float %x, %y
%r = fadd reassoc %a, %z
  =>
%b = fadd reassoc %y, %z
%r = fadd reassoc %x, %b
```

```text
INVALID      reassociate
the values differ
  %x = float 1.0
  %y = float 1.0
  %z = float -33554432.0
```

Only rewrites that are exact under IEEE semantics, given the flags `nnan`, `ninf` and `nsz`,
are proved.

## Limits

- `undef` inputs are not modeled (inputs are values or poison). An `undef` in the source is a
  value per use; a value derived from `undef` has one value, not a value per use, which gives
  the source fewer behaviors than LLVM's (never an unsound answer) and is refused in the
  target where it is used twice.
- Wide multiplication and division, and double-precision arithmetic the two programs do
  differently, can exceed the SAT solver's budget (`--conflicts`): the verdict is then
  unknown, never valid.
- A transformation is checked at 32 type assignments at most (`Config::max_types`).
- "Valid" is valid at each type assignment checked, not at every width: a rewrite that fails
  only at, say, 12 bits passes the default widths. Add such widths with `--widths`
  (`Config::widths`).
