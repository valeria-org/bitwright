//! Independent reference semantics for IEEE 754 binary floating point (test oracle).
//!
//! Written from bitwright's floating-point contract (formats `(eb, sb)` with SMT-LIB's
//! convention that `sb` counts the hidden bit, the rounding function `round_F(r, m)`, and each
//! operation's special cases), not from any floating-point implementation. The method is exact
//! rational arithmetic, deliberately unlike a softfloat's:
//!
//! 1. Every operand is decoded to an exact value: NaN, `±∞`, `±0`, or `(-1)^s · m · 2^e` with an
//!    integer significand `m > 0` (a private arbitrary-precision natural number type).
//! 2. The operation computes its exact mathematical result: a dyadic rational for `add`, `mul`,
//!    `fma`, conversions and `rem`; a rational `num / den · 2^k` for `div`; and for `sqrt`, the
//!    exact real square root, handled through integer square roots and exact comparisons of
//!    squares.
//! 3. `round_F` is applied literally, steps 1 to 5: `e = floor(log2 |r|)` by comparing
//!    bit lengths and then the exact values, the quantum `q = max(e, emin) - p + 1`,
//!    `M = floor(|r| / 2^q)` and its remainder by exact integer division, the fraction's
//!    position against `1/2` by an exact comparison with the midpoint, the mode's choice of `M`
//!    or `M + 1`, then the zero, overflow and encoding steps.
//!
//! No host floating point is used anywhere in this module.
//!
//! **Supported formats**: `2 <= eb <= 15`, `sb >= 2`, `eb + sb <= 512` (binary16, bfloat16,
//! binary32, binary64, binary128, x87's `(15, 64)`, every tiny format, significands up to 497
//! bits). Wider exponent fields panic: exact values are materialized as integers, and an `eb`-bit
//! exponent spans about `2^eb` binades, so beyond `eb = 15` (numbers of tens of thousands of bits)
//! exact materialization is out of scope for this oracle.
//!
//! Every function panics with a message when an operand's width does not match its format or a
//! format is invalid or unsupported; valid inputs never panic. NaN results are always the
//! canonical NaN (sign 0, exponent all ones, only the top trailing-significand bit set), except
//! for the sign-bit operations and for operations that return an operand unchanged (`min`/`max`
//! with one NaN, `rem(finite, ∞)`) or keep a payload (`x87_load`).

use crate::Bits;
use nat::{Nat, cmp_scaled};
use std::cmp::Ordering;

mod nat;

/// A binary floating-point format: `eb` exponent bits and precision `sb` (counting the hidden
/// bit), stored in `eb + sb` bits as sign, biased exponent, trailing significand.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Format {
    /// Exponent field width, `2..=15` here.
    pub eb: u16,
    /// Precision in bits, counting the hidden bit (the trailing significand has `sb - 1`).
    pub sb: u16,
}

impl Format {
    /// The encoding width `eb + sb`.
    pub fn width(self) -> u16 {
        self.eb
            .checked_add(self.sb)
            .expect("bitwright-ref: fp: format width overflows u16")
    }
}

/// A rounding mode: to nearest with ties to even (`Rne`) or away from zero (`Rna`), toward
/// `+∞` (`Rtp`), toward `-∞` (`Rtn`), toward zero (`Rtz`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Rm {
    /// To nearest, ties to even.
    Rne,
    /// To nearest, ties away from zero.
    Rna,
    /// Toward `+∞`.
    Rtp,
    /// Toward `-∞`.
    Rtn,
    /// Toward zero.
    Rtz,
}

impl Rm {
    /// Every rounding mode.
    pub const ALL: [Rm; 5] = [Rm::Rne, Rm::Rna, Rm::Rtp, Rm::Rtn, Rm::Rtz];
}

// ---------------------------------------------------------------------------------------------
// Formats, decoding and encoding
// ---------------------------------------------------------------------------------------------

/// A validated format with its derived constants.
#[derive(Clone, Copy, Debug)]
struct Fmt {
    eb: u64,
    /// The precision `sb`.
    p: u64,
    w: u64,
    /// `emax = bias = 2^(eb-1) - 1`.
    emax: i64,
    /// `emin = 1 - bias`.
    emin: i64,
    /// `2^eb - 1`, the biased exponent of infinities and NaNs.
    e_special: u64,
}

impl Fmt {
    fn new(f: Format) -> Fmt {
        assert!(
            f.eb >= 2 && f.sb >= 2 && u32::from(f.eb) + u32::from(f.sb) <= 512,
            "bitwright-ref: fp: (eb = {}, sb = {}) is not a format (2 <= eb, 2 <= sb, eb + sb <= 512)",
            f.eb,
            f.sb
        );
        assert!(
            f.eb <= 15,
            "bitwright-ref: fp: format (eb = {}, sb = {}) is unsupported: the oracle materializes \
             exact values as integers, and exponent fields wider than 15 bits span too many \
             binades for that (eb <= 15 covers binary16 to binary128 and x87)",
            f.eb,
            f.sb
        );
        let eb = u64::from(f.eb);
        let bias = (1i64 << (eb - 1)) - 1;
        Fmt {
            eb,
            p: u64::from(f.sb),
            w: eb + u64::from(f.sb),
            emax: bias,
            emin: 1 - bias,
            e_special: (1u64 << eb) - 1,
        }
    }

    fn bias(&self) -> i64 {
        self.emax
    }

    fn pi(&self) -> i64 {
        self.p as i64
    }

    /// The quantum exponent of subnormals and of the smallest binade: `emin - p + 1`.
    fn qmin(&self) -> i64 {
        self.emin - self.pi() + 1
    }

    /// The quantum exponent of the largest binade: `Ω = (2^p - 1) · 2^qmax`.
    fn qmax(&self) -> i64 {
        self.emax - self.pi() + 1
    }
}

/// An operand's exact value.
#[derive(Clone, Debug)]
enum Val {
    Nan,
    Inf(bool),
    Zero(bool),
    /// `(-1)^neg · m · 2^e` with `m > 0`.
    Fin {
        neg: bool,
        m: Nat,
        e: i64,
    },
}

/// Panics unless `a` has the format's width.
fn check(fm: &Fmt, a: &Bits, op: &str) {
    assert_eq!(
        u64::from(a.width()),
        fm.w,
        "bitwright-ref: fp::{op}: operand of width {} for a format of width {}",
        a.width(),
        fm.w
    );
}

/// Sign, biased exponent and trailing significand of an encoding.
fn fields(fm: &Fmt, a: &Bits, op: &str) -> (bool, u64, Nat) {
    check(fm, a, op);
    let v = Nat::from_limbs(a.to_limbs());
    let t = v.low_bits(fm.p - 1);
    let e = v
        .shr(fm.p - 1)
        .low_bits(fm.eb)
        .to_u64()
        .expect("exponent field fits in u64");
    (v.bit(fm.w - 1), e, t)
}

fn decode(fm: &Fmt, a: &Bits, op: &str) -> Val {
    let (s, e, t) = fields(fm, a, op);
    if e == fm.e_special {
        if t.is_zero() { Val::Inf(s) } else { Val::Nan }
    } else if e == 0 {
        if t.is_zero() {
            Val::Zero(s)
        } else {
            // Subnormal: T · 2^(emin - p + 1).
            Val::Fin {
                neg: s,
                m: t,
                e: fm.qmin(),
            }
        }
    } else {
        // Normal: (2^(p-1) + T) · 2^(E - bias - p + 1).
        Val::Fin {
            neg: s,
            m: Nat::pow2(fm.p - 1).add(&t),
            e: e as i64 - fm.bias() - fm.pi() + 1,
        }
    }
}

/// The encoding with sign `neg`, biased exponent `biased` and trailing significand `t`.
fn pack(fm: &Fmt, neg: bool, biased: u64, t: &Nat) -> Bits {
    debug_assert!(biased <= fm.e_special && t.bit_len() < fm.p);
    let mut v = t.add(&Nat::from_u64(biased).shl(fm.p - 1));
    if neg {
        v = v.add(&Nat::pow2(fm.w - 1));
    }
    Bits::from_limbs(fm.w as u16, v.limbs())
}

fn nan(fm: &Fmt) -> Bits {
    pack(fm, false, fm.e_special, &Nat::pow2(fm.p - 2))
}

fn inf(fm: &Fmt, neg: bool) -> Bits {
    pack(fm, neg, fm.e_special, &Nat::zero())
}

fn zero(fm: &Fmt, neg: bool) -> Bits {
    pack(fm, neg, 0, &Nat::zero())
}

/// `±Ω`.
fn max_finite(fm: &Fmt, neg: bool) -> Bits {
    pack(fm, neg, fm.e_special - 1, &Nat::ones(fm.p - 1))
}

/// `±0` by the zero rule: `+0`, except `-0` when the mode is `Rtn`.
fn zero_rule(fm: &Fmt, rm: Rm) -> Bits {
    zero(fm, rm == Rm::Rtn)
}

/// `c · 2^k`, which must be an integer.
fn shift_exact(c: &Nat, k: i64) -> Nat {
    if k >= 0 {
        c.shl(k as u64)
    } else {
        let k = k.unsigned_abs();
        assert!(
            c.low_bits(k).is_zero(),
            "bitwright-ref: fp: encoding an unrepresentable value"
        );
        c.shr(k)
    }
}

/// The encoding of `(-1)^neg · c · 2^q`, a nonzero finite value of the format.
fn encode(fm: &Fmt, neg: bool, c: &Nat, q: i64) -> Bits {
    assert!(!c.is_zero());
    let e = c.bit_len() as i64 - 1 + q; // floor(log2) of the magnitude
    if e >= fm.emin {
        assert!(e <= fm.emax, "bitwright-ref: fp: encoding a value above Ω");
        // The p-bit significand c · 2^(q - (e - p + 1)), minus the hidden bit.
        let sig = shift_exact(c, q - (e - fm.pi() + 1));
        let t = sig.sub(&Nat::pow2(fm.p - 1));
        pack(fm, neg, (e + fm.bias()) as u64, &t)
    } else {
        pack(fm, neg, 0, &shift_exact(c, q - fm.qmin()))
    }
}

/// The encoding with `a`'s exponent and trailing significand and the sign bit `neg`.
fn with_sign(a: &Bits, neg: bool) -> Bits {
    let w = a.width();
    let mut bits: Vec<bool> = (0..w).map(|i| a.bit(i)).collect();
    bits[usize::from(w) - 1] = neg;
    Bits::from_bools(bits)
}

// ---------------------------------------------------------------------------------------------
// round_F
// ---------------------------------------------------------------------------------------------

/// The fraction `f` of step 1, located against `1/2`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Frac {
    /// `f = 0`.
    Zero,
    /// `0 < f < 1/2`.
    Below,
    /// `f = 1/2`.
    Half,
    /// `1/2 < f < 1`.
    Above,
}

/// Locates `f = r / d` (`0 <= r < d`) by comparing `2r` with `d`.
fn classify(r: &Nat, d: &Nat) -> Frac {
    if r.is_zero() {
        return Frac::Zero;
    }
    match r.shl(1).cmp(d) {
        Ordering::Less => Frac::Below,
        Ordering::Equal => Frac::Half,
        Ordering::Greater => Frac::Above,
    }
}

/// Step 2: whether the mode chooses `M + 1` (rather than `M`) for a value of sign `neg` whose
/// magnitude is `M + f`. With a quantum of 1 this is also the integer rounding of
/// `roundToIntegral` (nearest-even, nearest-away, ceiling, floor, truncation on the magnitude).
fn round_up(rm: Rm, neg: bool, m: &Nat, f: Frac) -> bool {
    match rm {
        Rm::Rne => f == Frac::Above || (f == Frac::Half && m.is_odd()),
        Rm::Rna => f == Frac::Above || f == Frac::Half,
        Rm::Rtz => false,
        Rm::Rtp => f != Frac::Zero && !neg,
        Rm::Rtn => f != Frac::Zero && neg,
    }
}

/// Steps 2 to 5 for a value of sign `neg` and magnitude `(m + f) · 2^q`.
fn finish(fm: &Fmt, rm: Rm, neg: bool, m: Nat, f: Frac, q: i64) -> Bits {
    let c = if round_up(rm, neg, &m, f) {
        m.add(&Nat::one())
    } else {
        m
    };
    if c.is_zero() {
        return zero(fm, neg);
    }
    // Overflow: c · 2^q > Ω = (2^p - 1) · 2^qmax.
    if cmp_scaled(&c, q, &Nat::ones(fm.p), fm.qmax()) == Ordering::Greater {
        return match rm {
            Rm::Rne | Rm::Rna => inf(fm, neg),
            Rm::Rtz => max_finite(fm, neg),
            Rm::Rtp if neg => max_finite(fm, true),
            Rm::Rtp => inf(fm, false),
            Rm::Rtn if neg => inf(fm, true),
            Rm::Rtn => max_finite(fm, false),
        };
    }
    encode(fm, neg, &c, q)
}

/// `round_F((-1)^neg · num / den · 2^exp, rm)` for nonzero `num`, `den`.
fn round_ratio(fm: &Fmt, rm: Rm, neg: bool, num: &Nat, den: &Nat, exp: i64) -> Bits {
    // Step 1. With L = len(num) - len(den), num / den lies in (2^(L-1), 2^(L+1)), and it is at
    // least 2^L exactly when num >= den · 2^L.
    let l = num.bit_len() as i64 - den.bit_len() as i64;
    let e = exp
        + if cmp_scaled(num, 0, den, l) == Ordering::Less {
            l - 1
        } else {
            l
        };
    let q = e.max(fm.emin) - fm.pi() + 1;
    // M = floor(num · 2^(exp - q) / den); f = remainder / divisor.
    let (n, d) = if exp >= q {
        (num.shl((exp - q) as u64), den.clone())
    } else {
        (num.clone(), den.shl((q - exp) as u64))
    };
    let (m, r) = n.divrem(&d);
    debug_assert!(if e >= fm.emin {
        m.bit_len() == fm.p
    } else {
        m.bit_len() < fm.p
    });
    finish(fm, rm, neg, m, classify(&r, &d), q)
}

/// `round_F(sqrt(m · 2^k), rm)` for `m > 0`, rounded from the exact real square root.
fn round_sqrt(fm: &Fmt, rm: Rm, m: &Nat, k: i64) -> Bits {
    // Make the exponent even, so that sqrt(2^k) = 2^(k/2).
    let (m, k) = if k.rem_euclid(2) == 1 {
        (m.shl(1), k - 1)
    } else {
        (m.clone(), k)
    };
    // e = floor(log2 sqrt(X)) = floor(floor(log2 X) / 2) for X = m · 2^k.
    let e = (m.bit_len() as i64 - 1 + k).div_euclid(2);
    let q = e.max(fm.emin) - fm.pi() + 1;
    // sqrt(X) / 2^q = sqrt(Y) with Y = m · 2^(k - 2q) = y / 2^u (u >= 0).
    let t = k - 2 * q;
    let (y, u) = if t >= 0 {
        (m.shl(t as u64), 0)
    } else {
        (m, t.unsigned_abs())
    };
    // M = floor(sqrt(Y)) = floor(sqrt(floor(Y))).
    let root = y.shr(u).isqrt();
    // f = sqrt(Y) - M is zero iff Y = M^2; against 1/2 iff 4Y against (2M + 1)^2.
    let frac = if root.mul(&root).shl(u) == y {
        Frac::Zero
    } else {
        let mid = root.shl(1).add(&Nat::one());
        match y.shl(2).cmp(&mid.mul(&mid).shl(u)) {
            Ordering::Less => Frac::Below,
            Ordering::Equal => Frac::Half,
            Ordering::Greater => Frac::Above,
        }
    };
    debug_assert!(if e >= fm.emin {
        root.bit_len() == fm.p
    } else {
        root.bit_len() < fm.p
    });
    finish(fm, rm, false, root, frac, q)
}

/// The magnitude of the integer obtained from `(-1)^neg · m · 2^e` by the mode: nearest with
/// ties to even (`Rne`) or away (`Rna`), ceiling (`Rtp`), floor (`Rtn`), truncation (`Rtz`).
fn integral(rm: Rm, neg: bool, m: &Nat, e: i64) -> Nat {
    if e >= 0 {
        return m.shl(e as u64);
    }
    let d = Nat::pow2(e.unsigned_abs());
    let (k, r) = m.divrem(&d);
    if round_up(rm, neg, &k, classify(&r, &d)) {
        k.add(&Nat::one())
    } else {
        k
    }
}

// ---------------------------------------------------------------------------------------------
// Exact signed dyadic values
// ---------------------------------------------------------------------------------------------

/// `(-1)^neg · m · 2^e`; `m` may be zero.
struct Dy {
    neg: bool,
    m: Nat,
    e: i64,
}

impl Dy {
    fn of(v: &Val) -> Dy {
        match v {
            Val::Zero(s) => Dy {
                neg: *s,
                m: Nat::zero(),
                e: 0,
            },
            Val::Fin { neg, m, e } => Dy {
                neg: *neg,
                m: m.clone(),
                e: *e,
            },
            Val::Nan | Val::Inf(_) => unreachable!("not a finite value"),
        }
    }

    /// The exact sum.
    fn add(self, other: Dy) -> Dy {
        if self.m.is_zero() {
            return other;
        }
        if other.m.is_zero() {
            return self;
        }
        let e = self.e.min(other.e);
        let x = self.m.shl((self.e - e) as u64);
        let y = other.m.shl((other.e - e) as u64);
        if self.neg == other.neg {
            Dy {
                neg: self.neg,
                m: x.add(&y),
                e,
            }
        } else if x >= y {
            Dy {
                neg: self.neg,
                m: x.sub(&y),
                e,
            }
        } else {
            Dy {
                neg: other.neg,
                m: y.sub(&x),
                e,
            }
        }
    }

    /// `round_F` of a nonzero value.
    fn round(&self, fm: &Fmt, rm: Rm) -> Bits {
        round_ratio(fm, rm, self.neg, &self.m, &Nat::one(), self.e)
    }
}

// ---------------------------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------------------------

/// The canonical NaN of `f`: sign 0, exponent all ones, trailing significand `2^(sb-2)`.
pub fn canonical_nan(f: Format) -> Bits {
    nan(&Fmt::new(f))
}

/// IEEE addition, `round(a + b)`, with the contract's zero-sign rules.
pub fn add(f: Format, rm: Rm, a: &Bits, b: &Bits) -> Bits {
    let fm = Fmt::new(f);
    let (x, y) = (decode(&fm, a, "add"), decode(&fm, b, "add"));
    match (&x, &y) {
        (Val::Nan, _) | (_, Val::Nan) => nan(&fm),
        (Val::Inf(s), Val::Inf(t)) if s != t => nan(&fm),
        (Val::Inf(s), _) | (_, Val::Inf(s)) => inf(&fm, *s),
        (Val::Zero(s), Val::Zero(t)) if s == t => zero(&fm, *s),
        _ => {
            let r = Dy::of(&x).add(Dy::of(&y));
            if r.m.is_zero() {
                zero_rule(&fm, rm)
            } else {
                r.round(&fm, rm)
            }
        }
    }
}

/// `add(a, neg(b))`.
pub fn sub(f: Format, rm: Rm, a: &Bits, b: &Bits) -> Bits {
    add(f, rm, a, &neg(f, b))
}

/// IEEE multiplication.
pub fn mul(f: Format, rm: Rm, a: &Bits, b: &Bits) -> Bits {
    let fm = Fmt::new(f);
    let (x, y) = (decode(&fm, a, "mul"), decode(&fm, b, "mul"));
    let s = sign_bit(&fm, a) ^ sign_bit(&fm, b);
    match (&x, &y) {
        (Val::Nan, _) | (_, Val::Nan) => nan(&fm),
        (Val::Zero(_), Val::Inf(_)) | (Val::Inf(_), Val::Zero(_)) => nan(&fm),
        (Val::Inf(_), _) | (_, Val::Inf(_)) => inf(&fm, s),
        (Val::Zero(_), _) | (_, Val::Zero(_)) => zero(&fm, s),
        (Val::Fin { m: ma, e: ea, .. }, Val::Fin { m: mb, e: eb, .. }) => {
            round_ratio(&fm, rm, s, &ma.mul(mb), &Nat::one(), ea + eb)
        }
    }
}

/// IEEE division.
pub fn div(f: Format, rm: Rm, a: &Bits, b: &Bits) -> Bits {
    let fm = Fmt::new(f);
    let (x, y) = (decode(&fm, a, "div"), decode(&fm, b, "div"));
    let s = sign_bit(&fm, a) ^ sign_bit(&fm, b);
    match (&x, &y) {
        (Val::Nan, _) | (_, Val::Nan) => nan(&fm),
        (Val::Zero(_), Val::Zero(_)) | (Val::Inf(_), Val::Inf(_)) => nan(&fm),
        (Val::Inf(_), _) => inf(&fm, s),
        (_, Val::Inf(_)) => zero(&fm, s),
        (Val::Fin { .. }, Val::Zero(_)) => inf(&fm, s),
        (Val::Zero(_), Val::Fin { .. }) => zero(&fm, s),
        (Val::Fin { m: ma, e: ea, .. }, Val::Fin { m: mb, e: eb, .. }) => {
            round_ratio(&fm, rm, s, ma, mb, ea - eb)
        }
    }
}

/// Fused multiply-add, `round(a · b + c)` with a single rounding.
pub fn fma(f: Format, rm: Rm, a: &Bits, b: &Bits, c: &Bits) -> Bits {
    let fm = Fmt::new(f);
    let (x, y, z) = (
        decode(&fm, a, "fma"),
        decode(&fm, b, "fma"),
        decode(&fm, c, "fma"),
    );
    let sp = sign_bit(&fm, a) ^ sign_bit(&fm, b);
    if matches!(x, Val::Nan) || matches!(y, Val::Nan) || matches!(z, Val::Nan) {
        return nan(&fm);
    }
    match (&x, &y) {
        (Val::Zero(_), Val::Inf(_)) | (Val::Inf(_), Val::Zero(_)) => return nan(&fm),
        (Val::Inf(_), _) | (_, Val::Inf(_)) => {
            return match z {
                Val::Inf(sc) if sc != sp => nan(&fm),
                _ => inf(&fm, sp),
            };
        }
        _ => {}
    }
    if let Val::Inf(_) = z {
        return c.clone();
    }
    // All finite: the exact product, then the exact sum.
    let product = match (&x, &y) {
        (Val::Fin { m: ma, e: ea, .. }, Val::Fin { m: mb, e: eb, .. }) => Dy {
            neg: sp,
            m: ma.mul(mb),
            e: ea + eb,
        },
        _ => Dy {
            neg: sp,
            m: Nat::zero(),
            e: 0,
        },
    };
    let product_is_zero = product.m.is_zero();
    let r = product.add(Dy::of(&z));
    if !r.m.is_zero() {
        return r.round(&fm, rm);
    }
    match z {
        Val::Zero(sc) if product_is_zero && sc == sp => zero(&fm, sp),
        _ => zero_rule(&fm, rm),
    }
}

/// Square root, rounded from the exact real square root.
pub fn sqrt(f: Format, rm: Rm, a: &Bits) -> Bits {
    let fm = Fmt::new(f);
    match decode(&fm, a, "sqrt") {
        Val::Nan => nan(&fm),
        Val::Zero(s) => zero(&fm, s),
        Val::Inf(false) => inf(&fm, false),
        Val::Inf(true) | Val::Fin { neg: true, .. } => nan(&fm),
        Val::Fin { neg: false, m, e } => round_sqrt(&fm, rm, &m, e),
    }
}

/// IEEE `remainder`: `a - n · b` with `n` the integer nearest `a / b`, ties to even (exact; no
/// rounding mode).
pub fn rem(f: Format, a: &Bits, b: &Bits) -> Bits {
    let fm = Fmt::new(f);
    let (x, y) = (decode(&fm, a, "rem"), decode(&fm, b, "rem"));
    let (mb, eb) = match (&x, &y) {
        (Val::Nan, _) | (_, Val::Nan) | (Val::Inf(_), _) | (_, Val::Zero(_)) => return nan(&fm),
        (_, Val::Inf(_)) => return a.clone(),
        (_, Val::Fin { m, e, .. }) => (m, *e),
    };
    let sa = sign_bit(&fm, a);
    let (ma, ea) = match &x {
        Val::Fin { m, e, .. } => (m.clone(), *e),
        _ => (Nat::zero(), eb), // a zero: the quotient is 0 and so is the remainder
    };
    // With a common exponent e0: |v(a)| = A · 2^e0, |v(b)| = B · 2^e0, |v(a) / v(b)| = A / B.
    let e0 = ea.min(eb);
    let big_a = ma.shl((ea - e0) as u64);
    let big_b = mb.shl((eb - e0) as u64);
    // |n|: A / B rounded to the nearest integer, ties to even (rounding is symmetric in sign).
    let (k, r) = big_a.divrem(&big_b);
    let n = if round_up(Rm::Rne, false, &k, classify(&r, &big_b)) {
        k.add(&Nat::one())
    } else {
        k
    };
    // v(a) - n · v(b) = (-1)^sa · 2^e0 · (A - |n| · B).
    let nb = n.mul(&big_b);
    let (neg, diff) = if big_a >= nb {
        (sa, big_a.sub(&nb))
    } else {
        (!sa, nb.sub(&big_a))
    };
    if diff.is_zero() {
        zero(&fm, sa)
    } else {
        encode(&fm, neg, &diff, e0)
    }
}

/// `roundToIntegral`: the integer obtained from `a` by the mode, as a value of the format.
pub fn round_to_integral(f: Format, rm: Rm, a: &Bits) -> Bits {
    let fm = Fmt::new(f);
    match decode(&fm, a, "round_to_integral") {
        Val::Nan => nan(&fm),
        Val::Inf(_) | Val::Zero(_) => a.clone(),
        Val::Fin { neg, m, e } => {
            let k = integral(rm, neg, &m, e);
            if k.is_zero() {
                zero(&fm, neg)
            } else {
                round_ratio(&fm, rm, neg, &k, &Nat::one(), 0)
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Comparisons and sign operations
// ---------------------------------------------------------------------------------------------

/// Orders non-NaN values numerically (`-0 = +0`).
fn cmp_vals(x: &Val, y: &Val) -> Ordering {
    fn rank(v: &Val) -> i8 {
        match v {
            Val::Inf(true) => -2,
            Val::Fin { neg: true, .. } => -1,
            Val::Zero(_) => 0,
            Val::Fin { neg: false, .. } => 1,
            Val::Inf(false) => 2,
            Val::Nan => unreachable!("NaN has no order"),
        }
    }
    match (x, y) {
        (
            Val::Fin {
                neg: s,
                m: ma,
                e: ea,
            },
            Val::Fin {
                neg: t,
                m: mb,
                e: eb,
            },
        ) if s == t => {
            let magnitude = cmp_scaled(ma, *ea, mb, *eb);
            if *s { magnitude.reverse() } else { magnitude }
        }
        _ => rank(x).cmp(&rank(y)),
    }
}

/// The order of `min` and `max`: numeric, with `-0 < +0`.
fn cmp_signed_zeros(x: &Val, y: &Val) -> Ordering {
    match (x, y) {
        (Val::Zero(s), Val::Zero(t)) => t.cmp(s), // negative (true) sorts first
        _ => cmp_vals(x, y),
    }
}

/// IEEE 754-2019 `minimumNumber`: a NaN operand is ignored unless both are NaN; `-0 < +0`;
/// equal values give `a`.
pub fn min(f: Format, a: &Bits, b: &Bits) -> Bits {
    let fm = Fmt::new(f);
    let (x, y) = (decode(&fm, a, "min"), decode(&fm, b, "min"));
    match (&x, &y) {
        (Val::Nan, Val::Nan) => nan(&fm),
        (Val::Nan, _) => b.clone(),
        (_, Val::Nan) => a.clone(),
        _ if cmp_signed_zeros(&x, &y) == Ordering::Greater => b.clone(),
        _ => a.clone(),
    }
}

/// IEEE 754-2019 `maximumNumber`: a NaN operand is ignored unless both are NaN; `-0 < +0`;
/// equal values give `a`.
pub fn max(f: Format, a: &Bits, b: &Bits) -> Bits {
    let fm = Fmt::new(f);
    let (x, y) = (decode(&fm, a, "max"), decode(&fm, b, "max"));
    match (&x, &y) {
        (Val::Nan, Val::Nan) => nan(&fm),
        (Val::Nan, _) => b.clone(),
        (_, Val::Nan) => a.clone(),
        _ if cmp_signed_zeros(&x, &y) == Ordering::Less => b.clone(),
        _ => a.clone(),
    }
}

/// The numeric order of `a` and `b`, or `None` if either is NaN.
fn compare(f: Format, a: &Bits, b: &Bits, op: &str) -> Option<Ordering> {
    let fm = Fmt::new(f);
    let (x, y) = (decode(&fm, a, op), decode(&fm, b, op));
    match (&x, &y) {
        (Val::Nan, _) | (_, Val::Nan) => None,
        _ => Some(cmp_vals(&x, &y)),
    }
}

/// `v(a) = v(b)`; false if either is NaN (`+0 = -0`).
pub fn eq(f: Format, a: &Bits, b: &Bits) -> bool {
    compare(f, a, b, "eq") == Some(Ordering::Equal)
}

/// `v(a) < v(b)`; false if either is NaN.
pub fn lt(f: Format, a: &Bits, b: &Bits) -> bool {
    compare(f, a, b, "lt") == Some(Ordering::Less)
}

/// `v(a) <= v(b)`; false if either is NaN.
pub fn le(f: Format, a: &Bits, b: &Bits) -> bool {
    matches!(
        compare(f, a, b, "le"),
        Some(Ordering::Less | Ordering::Equal)
    )
}

fn sign_bit(fm: &Fmt, a: &Bits) -> bool {
    a.bit((fm.w - 1) as u16)
}

/// `a` with its sign bit flipped (NaNs included; no canonicalization).
pub fn neg(f: Format, a: &Bits) -> Bits {
    let fm = Fmt::new(f);
    check(&fm, a, "neg");
    with_sign(a, !sign_bit(&fm, a))
}

/// `a` with its sign bit cleared (NaNs included; no canonicalization).
pub fn abs(f: Format, a: &Bits) -> Bits {
    check(&Fmt::new(f), a, "abs");
    with_sign(a, false)
}

/// `a` with the sign bit of `b` (NaNs included; no canonicalization).
pub fn copysign(f: Format, a: &Bits, b: &Bits) -> Bits {
    let fm = Fmt::new(f);
    check(&fm, a, "copysign");
    check(&fm, b, "copysign");
    with_sign(a, sign_bit(&fm, b))
}

// ---------------------------------------------------------------------------------------------
// Classification
// ---------------------------------------------------------------------------------------------

/// Whether `a` is a NaN (exponent all ones, nonzero trailing significand).
pub fn is_nan(f: Format, a: &Bits) -> bool {
    let fm = Fmt::new(f);
    let (_, e, t) = fields(&fm, a, "is_nan");
    e == fm.e_special && !t.is_zero()
}

/// Whether `a` is `±∞`.
pub fn is_infinite(f: Format, a: &Bits) -> bool {
    let fm = Fmt::new(f);
    let (_, e, t) = fields(&fm, a, "is_infinite");
    e == fm.e_special && t.is_zero()
}

/// Whether `a` is `±0`.
pub fn is_zero(f: Format, a: &Bits) -> bool {
    let fm = Fmt::new(f);
    let (_, e, t) = fields(&fm, a, "is_zero");
    e == 0 && t.is_zero()
}

/// Whether `a` is normal (`1 <= E <= 2^eb - 2`).
pub fn is_normal(f: Format, a: &Bits) -> bool {
    let fm = Fmt::new(f);
    let (_, e, _) = fields(&fm, a, "is_normal");
    e != 0 && e != fm.e_special
}

/// Whether `a` is subnormal (`E = 0`, `T != 0`).
pub fn is_subnormal(f: Format, a: &Bits) -> bool {
    let fm = Fmt::new(f);
    let (_, e, t) = fields(&fm, a, "is_subnormal");
    e == 0 && !t.is_zero()
}

/// Whether `a`'s sign bit is set and it is not a NaN (true for `-0`).
pub fn is_negative(f: Format, a: &Bits) -> bool {
    let fm = Fmt::new(f);
    let (s, _, _) = fields(&fm, a, "is_negative");
    s && !is_nan(f, a)
}

/// Whether `a`'s sign bit is clear and it is not a NaN (true for `+0`).
pub fn is_positive(f: Format, a: &Bits) -> bool {
    let fm = Fmt::new(f);
    let (s, _, _) = fields(&fm, a, "is_positive");
    !s && !is_nan(f, a)
}

// ---------------------------------------------------------------------------------------------
// Conversions
// ---------------------------------------------------------------------------------------------

/// Converts between formats: NaN to the canonical NaN, `±∞` and `±0` kept, otherwise
/// `round_to(v(a), rm)`.
pub fn to_fp(from: Format, to: Format, rm: Rm, a: &Bits) -> Bits {
    let src = Fmt::new(from);
    let dst = Fmt::new(to);
    match decode(&src, a, "to_fp") {
        Val::Nan => nan(&dst),
        Val::Inf(s) => inf(&dst, s),
        Val::Zero(s) => zero(&dst, s),
        Val::Fin { neg, m, e } => round_ratio(&dst, rm, neg, &m, &Nat::one(), e),
    }
}

fn check_int_width(width: u16, op: &str) {
    assert!(
        (1..=512).contains(&width),
        "bitwright-ref: fp::{op}: integer width {width} is outside 1..=512"
    );
}

/// Rounds the integer `(-1)^neg · k` (`0` gives `+0`).
fn from_int(fm: &Fmt, rm: Rm, neg: bool, k: &Nat) -> Bits {
    if k.is_zero() {
        zero(fm, false)
    } else {
        round_ratio(fm, rm, neg, k, &Nat::one(), 0)
    }
}

/// Converts a two's-complement integer of any width `1..=512`.
pub fn from_sint(to: Format, rm: Rm, x: &Bits) -> Bits {
    let fm = Fmt::new(to);
    check_int_width(x.width(), "from_sint");
    let n = u64::from(x.width());
    let v = Nat::from_limbs(x.to_limbs());
    if v.bit(n - 1) {
        from_int(&fm, rm, true, &Nat::pow2(n).sub(&v))
    } else {
        from_int(&fm, rm, false, &v)
    }
}

/// Converts an unsigned integer of any width `1..=512`.
pub fn from_uint(to: Format, rm: Rm, x: &Bits) -> Bits {
    let fm = Fmt::new(to);
    check_int_width(x.width(), "from_uint");
    from_int(&fm, rm, false, &Nat::from_limbs(x.to_limbs()))
}

fn int_bits(width: u16, v: &Nat) -> Bits {
    Bits::from_limbs(width, v.limbs())
}

/// Converts to a `width`-bit two's-complement integer: the integer obtained by the mode (as in
/// [`round_to_integral`]), saturated; NaN gives 0.
pub fn to_sint(from: Format, rm: Rm, a: &Bits, width: u16) -> Bits {
    let fm = Fmt::new(from);
    check_int_width(width, "to_sint");
    let n = u64::from(width);
    let max = Nat::ones(n - 1); // 2^(n-1) - 1
    let min_mag = Nat::pow2(n - 1); // |-2^(n-1)|
    let negate = |k: &Nat| {
        if k.is_zero() {
            Nat::zero()
        } else {
            Nat::pow2(n).sub(k)
        }
    };
    let v = match decode(&fm, a, "to_sint") {
        Val::Nan | Val::Zero(_) => Nat::zero(),
        Val::Inf(false) => max,
        Val::Inf(true) => negate(&min_mag),
        Val::Fin { neg, m, e } => {
            let k = integral(rm, neg, &m, e);
            match (neg, k) {
                (false, k) => k.min(max),
                (true, k) => negate(&k.min(min_mag)),
            }
        }
    };
    int_bits(width, &v)
}

/// Converts to a `width`-bit unsigned integer: the integer obtained by the mode (as in
/// [`round_to_integral`]), saturated (negative values give 0); NaN gives 0.
pub fn to_uint(from: Format, rm: Rm, a: &Bits, width: u16) -> Bits {
    let fm = Fmt::new(from);
    check_int_width(width, "to_uint");
    let max = Nat::ones(u64::from(width));
    let v = match decode(&fm, a, "to_uint") {
        Val::Nan | Val::Zero(_) | Val::Inf(true) => Nat::zero(),
        Val::Inf(false) => max,
        // A negative integer saturates to 0 (and so does a negative value rounding to 0).
        Val::Fin { neg: true, .. } => Nat::zero(),
        Val::Fin { neg: false, m, e } => integral(rm, false, &m, e).min(max),
    };
    int_bits(width, &v)
}

// ---------------------------------------------------------------------------------------------
// x87 extended precision
// ---------------------------------------------------------------------------------------------

/// The format of x87 values.
const X87: Format = Format { eb: 15, sb: 64 };

/// Loads an 80-bit x87 encoding (sign 79, exponent 78-64, integer bit 63, fraction 62-0) as a
/// `(15, 64)` value (79 bits). Pseudo-denormals become normals of exponent 1; unnormals,
/// pseudo-infinities and pseudo-NaNs become the canonical NaN; NaN payloads are kept.
pub fn x87_load(x: &Bits) -> Bits {
    assert_eq!(
        x.width(),
        80,
        "bitwright-ref: fp::x87_load: operand of width {} (want 80)",
        x.width()
    );
    let fm = Fmt::new(X87);
    let v = Nat::from_limbs(x.to_limbs());
    let frac = v.low_bits(63);
    let int_bit = v.bit(63);
    let e = v.shr(64).low_bits(15).to_u64().expect("15-bit exponent");
    let s = v.bit(79);
    match (e, int_bit) {
        // Zero or denormal.
        (0, false) => pack(&fm, s, 0, &frac),
        // Pseudo-denormal, value 1.f · 2^-16382.
        (0, true) => pack(&fm, s, 1, &frac),
        // Infinity or NaN (payload kept).
        (32767, true) => pack(&fm, s, 32767, &frac),
        // Pseudo-infinity, pseudo-NaN.
        (32767, false) => nan(&fm),
        // Normal.
        (_, true) => pack(&fm, s, e, &frac),
        // Unnormal.
        (_, false) => nan(&fm),
    }
}

/// Stores a `(15, 64)` value (79 bits) as an 80-bit x87 encoding with the explicit integer bit
/// `E != 0` (payloads kept).
pub fn x87_store(a: &Bits) -> Bits {
    let fm = Fmt::new(X87);
    let (s, e, t) = fields(&fm, a, "x87_store");
    let mut v = t.add(&Nat::from_u64(e).shl(64));
    if e != 0 {
        v = v.add(&Nat::pow2(63));
    }
    if s {
        v = v.add(&Nat::pow2(79));
    }
    Bits::from_limbs(80, v.limbs())
}

#[cfg(test)]
mod tests;
