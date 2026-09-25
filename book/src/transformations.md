# Verifying compiler transformations

`bitwright::transform` (feature `prove`) proves that one program *refines* another under
LLVM's semantics: whatever the target may do, the source may do too. It reads peephole
transformations in the syntax the Alive paper introduced (Lopes et al., PLDI 2015), and pairs
of functions in a subset of LLVM IR (translation validation); it infers preconditions; and
when a transformation is wrong it shows why, with inputs small enough to read, as LLVM IR
constants.

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

## Translation validation

`bitwright tv before.ll after.ll` checks that each function of the second file refines the
function of the same name in the first; `bitwright tv pair.ll` checks that `@tgt` refines
`@src`. For example, the output of an optimizer against its input:

```text
$ clang -x ir -O2 -S -emit-llvm before.ll -o after.ll
$ bitwright tv before.ll after.ll
```

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
`select` are a valid rewrite and the reverse is not:

```text
INVALID      g
the target has undefined behavior where the source has none
  %x = i8 0
  %c = i1 poison
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

## Limits

- `undef` inputs are not modeled (inputs are values or poison). An `undef` in the source is a
  value per use; a value derived from `undef` has one value, not a value per use, which gives
  the source fewer behaviors than LLVM's (never an unsound answer) and is refused in the
  target where it is used twice.
- Wide multiplication and division, and double-precision arithmetic the two programs do
  differently, can exceed the SAT solver's budget (`--conflicts`): the verdict is then
  unknown, never valid.
- A transformation is checked at 32 type assignments at most (`Config::max_types`).
