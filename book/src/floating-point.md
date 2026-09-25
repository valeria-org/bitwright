# Floating point

A floating-point value is a bit-vector holding an IEEE 754 interchange encoding, the way a
register or memory holds it. bitwright evaluates, builds, simplifies and reasons about IEEE 754
binary arithmetic on such values, in any format, under every rounding mode, exactly: every
operation is defined for every input pattern and gives exactly one result pattern. The
arithmetic is done in software, never on the host's floating-point unit, so results do not
depend on the machine or on a flush-to-zero or rounding mode a host program may have set.

## Formats

A format `(eb, sb)` has `eb` exponent bits and `sb` significand bits, the hidden bit included
(SMT-LIB's convention), so an encoding is `eb + sb` bits wide: a sign bit, the biased exponent,
then the trailing `sb − 1` significand bits. Any `2 ≤ eb ≤ 31`, `sb ≥ 2`, `eb + sb ≤ 512` is a
format (`FpFormat::new`); the named ones:

| Format | `(eb, sb)` | Width | Name in the text syntax |
|-|-|-:|-|
| binary16 | `(5, 11)` | 16 | `f16` |
| bfloat16 | `(8, 8)` | 16 | `bf16` |
| binary32 | `(8, 24)` | 32 | `f32` |
| binary64 | `(11, 53)` | 64 | `f64` |
| binary128 | `(15, 113)` | 128 | `f128` |
| binary256 | `(19, 237)` | 256 | `f256` |
| x87 extended (values) | `(15, 64)` | 79 | — |

x87's 80-bit memory encoding has an explicit integer bit; `x87_load` and `x87_store`
convert between it and `(15, 64)`, with x87's reading of its non-canonical encodings: a
pseudo-denormal is the normal value it stands for, and an unnormal, a pseudo-infinity or a
pseudo-NaN is invalid, so it loads as the NaN.

## Semantics

Results are correctly rounded: the exact mathematical result, rounded once in the operation's
rounding mode (`RoundingMode`: `Rne` to nearest with ties to even, `Rna` ties away from zero,
`Rtp` toward +∞, `Rtn` toward −∞, `Rtz` toward zero), with gradual underflow, and past the
largest finite value ∞ or the largest finite value as the mode says. Where IEEE 754 or SMT-LIB
leave a result open, bitwright fixes one, the same on every host:

| | bitwright |
|-|-|
| A NaN result | the format's canonical quiet NaN: sign 0, exponent all ones, only the top significand bit set (`0x7fc00000` in binary32). NaN payloads do not propagate. |
| `neg`, `abs`, `copysign` | change the sign bit only, of a NaN too (IEEE 754 §5.5.1) |
| `min`, `max` | IEEE 754-2019 minimumNumber and maximumNumber: a NaN operand is ignored (two give the NaN), and `−0 < +0` |
| Conversion to an integer | rounded by the operation's mode, then saturated to the integer's range; a NaN converts to 0 |
| `rem` | IEEE `remainder`: `a − n·b`, `n` the integer nearest `a / b`, ties to even (exact) |
| A zero sum `x + (−x)` | `+0`, or `−0` toward −∞ |

The semantics are those of RISC-V, of ARM with default NaNs, and of SMT-LIB's single NaN. An
instruction set that propagates NaN payloads or has an asymmetric minimum (x86's `minss` is
`a < b ? a : b`) is a composition of these operations with `select`, which bitwright simplifies
like any other expression.

## Values

`FpFormat` has every operation on `BitVec`s; the operands' widths must be the format's.

```rust
use bitwright::fp::{FpCmpOp, FpFormat, RoundingMode::*};
use bitwright::{BitVec, Width};

let f = FpFormat::F64;
let (a, b) = (BitVec::from_f64(1.0), BitVec::from_f64(3.0));
// 1/3 to nearest, and rounded up: one unit in the last place apart.
let near = f.div(Rne, &a, &b)?;
let up = f.div(Rtp, &a, &b)?;
assert_eq!(near.to_f64(), Some(1.0 / 3.0));
assert_eq!(up.to_f64().unwrap().to_bits(), (1.0f64 / 3.0).to_bits() + 1);
// A NaN result is the canonical one, whatever the operands were.
let nan = f.sqrt(Rne, &BitVec::from_f64(-1.0))?;
assert_eq!(nan, f.nan());
assert!(!f.cmp(FpCmpOp::Eq, &nan, &nan)?);
// Conversions saturate: 1e10 does not fit 32 bits; a NaN gives 0.
assert_eq!(f.to_sint(Rtz, &BitVec::from_f64(1e10), Width::W32)?.to_u64(), Some(0x7fff_ffff));
assert_eq!(f.to_sint(Rtz, &nan, Width::W32)?.to_u64(), Some(0));
// Any format: binary16 has 11 bits of precision, so 2049 rounds to 2048 or 2050.
let h = FpFormat::F16;
let i = BitVec::from_u64(Width::W16, 2049)?;
assert_eq!(h.from_uint(Rne, &i), h.from_uint(Rne, &BitVec::from_u64(Width::W16, 2048)?));
assert_eq!(h.from_uint(Rtp, &i), h.from_uint(Rne, &BitVec::from_u64(Width::W16, 2050)?));
# Ok::<(), Box<dyn std::error::Error>>(())
```

## Expressions

`Context::fp` builds an operation node (`FpOp`): `Add`, `Mul`, `Div`, `Fma`, `Sqrt`,
`RoundToIntegral` and the conversions take a rounding mode; `Rem`, `Min`, `Max` and the
comparisons `Eq`, `Lt`, `Le` (1 bit) do not. The operations that look only at the sign and
exponent are built from bit-vector operators, so every pass sees through them:
`Context::fp_neg` is `x ^ sign`, `Context::fp_abs` is `x & ~sign`, each test of
`Context::fp_test` (`isNaN`, `isInfinite`, `isZero`, `isNormal`, `isSubnormal`, `isNegative`,
`isPositive`) is one unsigned comparison of the encoding, `Context::fp_sub` is the sum with the
negation, and `>` and `≥` are `<` and `≤` swapped.

The text syntax writes an operation as `fp.<op>[.<mode>]<format>(operands)`, the format by name
(`.f32`) or as `<eb, sb>`. Every identifier that starts with `fp.` is reserved.

| Text | Operation |
|-|-|
| `fp.add.rne.f32(a, b)`, `fp.sub`, `fp.mul`, `fp.div` | arithmetic |
| `fp.fma.rtz.f64(a, b, c)` | `a · b + c`, rounded once |
| `fp.sqrt.rne.f64(a)`, `fp.round.rtn.f64(a)` | square root, rounding to an integral value |
| `fp.rem.f64(a, b)`, `fp.min.f64(a, b)`, `fp.max.f64(a, b)` | exact, no mode |
| `fp.eq.f32(a, b)`, `fp.lt`, `fp.le`, `fp.gt`, `fp.ge` | comparisons, 1 bit |
| `fp.neg.f32(a)`, `fp.abs`, `fp.copysign.f32(a, b)` | sign operations |
| `fp.isnan.f32(a)`, `fp.isinf`, `fp.iszero`, `fp.isnormal`, `fp.issubnormal`, `fp.isneg`, `fp.ispos` | tests, 1 bit |
| `fp.convert.rne.f64.f32(a)`, `fp.convert.rne<11, 53, 3, 4>(a)` | between formats |
| `fp.from_sbv.rne.f64(i)`, `fp.from_ubv` | from a signed or unsigned integer of any width |
| `fp.to_sbv.rtz.f64<32>(a)`, `fp.to_ubv` | to an integer of the given width, saturating |
| `fp.x87_load(x)`, `fp.x87_store(a)` | x87's 80-bit encoding |

```rust
use bitwright::fp::{FpFormat, FpOp, RoundingMode};
use bitwright::{BitVec, Context, ParseOptions, SymbolKey};

let mut cx = Context::new();
let o = ParseOptions::default();
let e = cx.parse("fp.fma.rne.f32(x, y, fp.neg.f32(z))", &o)?;
assert_eq!(cx.display(e).to_string(), "fp.fma.rne.f32(x, y, z ^ 0x80000000)");
// Operations on constants fold, exactly.
let tenth = cx.constant(&BitVec::from_f32(0.1))?;
let s = cx.fp(FpOp::Add(RoundingMode::Rne), FpFormat::F32, &[tenth, tenth])?;
assert_eq!(cx.as_const(s)?.and_then(|v| v.to_f32()), Some(0.2));
// And evaluate at a point.
let env = [
    (SymbolKey::from("x"), BitVec::from_f32(2.0)),
    (SymbolKey::from("y"), BitVec::from_f32(3.0)),
    (SymbolKey::from("z"), BitVec::from_f32(1.0)),
];
assert_eq!(cx.eval(&[e], &env[..])?[0].to_f32(), Some(5.0));
# Ok::<(), bitwright::Error>(())
```

[Rules](rules.md#floating-point) can rewrite floating-point operations too, generic in the
format and the rounding mode, and the checker checks them in every small format.

Construction applies the identities that hold bit for bit on every encoding (a NaN operand gives
the canonical NaN on both sides, zeros keep their signs) and add no node: `fma(x, 1, y)` is `x +
y`, `fma(x, y, −0)` is `x · y` except toward −∞, `x · 2` and `x / ½` are `x + x`, `(−a) · (−b)`
is `a · b` (and so for `/`), `−a < −b` is `b < a`, `x < x` is false, rounding to an integral
value twice is rounding once, and a signed conversion of a zero or sign extension converts the
operand itself.

Identities that hold only on some encodings (`x · 1 = x` fails for a NaN with a payload,
`x + (−0) = x` for `+0` toward −∞) are the built-in rules of the group `core.float`, each
guarded by what it needs: that an operand is no NaN (`fp.not_nan`), no zero (`fp.nonzero`) or
finite (`fp.finite`), which the [facts](#facts) prove or do not. Dividing by a power of two
whose reciprocal is a normal number becomes multiplying by the reciprocal, which is the same
real number rounded once in the same mode. So a float that came from an integer, which the
facts know is no NaN, loses a multiplication by 1.0, and `x · 1.0` of an unknown `x` stays:

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions, Width};

let engine = Engine::standard();
let mut cx = Context::new();
let o = ParseOptions::width(Width::W64);
for (float, simplified) in [
    ("fp.mul.rne.f64(fp.from_sbv.rne.f64(i:32), 0x3ff0000000000000)", "fp.from_sbv.rne.f64(i)"),
    ("fp.mul.rne.f64(x, 0x3ff0000000000000)", "fp.mul.rne.f64(x, 0x3ff0000000000000)"),
    ("fp.div.rtz.f64(x, 0x4010000000000000)", "fp.mul.rtz.f64(x, 0x3fd0000000000000)"),
    ("fp.eq.f64(fp.sqrt.rne.f64(fp.from_ubv.rne.f64(u:32)), fp.sqrt.rne.f64(fp.from_ubv.rne.f64(u:32)))", "1:1"),
] {
    let e = cx.parse(float, &o)?;
    let out = engine.simplify(&mut cx, e)?;
    assert_eq!(cx.display(out.expr).to_string(), simplified, "{float}");
}
# Ok::<(), bitwright::Error>(())
```

The rules are listed in the [rule catalog](catalog.md), and a rule of your own can use the same
guards (see [Writing rules](rules.md#floating-point)).

Comparisons and class tests of one operand combine as the bit-vector conditions do: a lifted
`ucomiss` followed by `ja`, `(¬(x < y ∨ unordered)) ∧ ¬(x = y ∨ unordered)`, is `y < x`,
and `iszero(x) ∨ issubnormal(x)` is one unsigned comparison of `x` without its sign bit (see
[Examples](examples.md#conditions-from-lifted-flags)).

## Facts

The [facts](facts.md) of a floating-point result come from its operands' facts, read as sets of
floats: whether a NaN may occur, and an interval of values per sign. An operation is applied to
the ends of those intervals in its own rounding mode (correct rounding is monotonic, so the ends
bound every result), and falls back to every value where a special case may occur (`0 · ∞`,
`∞ − ∞`, a divisor that may be 0). So facts show that an integer converted to a float is never a
NaN, that the square root of a non-negative value is not either, or that a converted byte is
below 256, and the simplifier folds such questions:

```rust
use bitwright::engine::Engine;
use bitwright::{Context, ParseOptions};

let mut cx = Context::new();
let e = cx.parse("fp.isnan.f64(fp.mul.rne.f64(fp.from_sbv.rne.f64(a:16), fp.from_sbv.rne.f64(b:16)))",
                 &ParseOptions::default())?;
let out = Engine::standard().simplify(&mut cx, e)?;
assert_eq!(cx.display(out.expr).to_string(), "0:1");
# Ok::<(), bitwright::Error>(())
```

## SMT-LIB

With feature `smtlib`, floating-point operations export to SMT-LIB's FloatingPoint theory
(`QF_BVFP`): an operand is read with `((_ to_fp eb sb) x)`, and a result's bits are declared and
pinned by one assertion (SMT-LIB has no standard `fp.to_ieee_bv`, since a NaN has many
encodings), the canonical NaN included. What SMT-LIB leaves open is written out as bitwright
defines it. `smtlib::import` reads the FloatingPoint theory back: the
float sorts, literals and special values, every `fp.` operator, `to_fp` from bits, floats,
integers and real constants (rounded exactly), and z3's `fp.to_ieee_bv`.

## How it is checked

- An independent implementation, `bitwright-ref::fp`, written from this specification alone by
  exact rational arithmetic, agrees with bitwright on every input of every format of up to 8
  bits, every operation under every mode (fma on every triple up to 6 bits), and on random
  operands of binary16, bfloat16, binary32, binary64, x87, binary128 and a 512-bit format.
- binary32 and binary64 agree with the host's hardware (round to nearest even), and the integer
  frames of the software arithmetic agree with each other.
- The exported terms agree with Bitwuzla on binary16 to binary128 and with z3 on formats of
  precision 4 and more. (z3 5.1.0 is wrong below that: its fma at precision 3 or less and its
  roundToIntegral with a 2-bit exponent.)
- Every fact transfer is checked sound on every format of 4 to 6 bits against every member of
  structured and random operand facts.

