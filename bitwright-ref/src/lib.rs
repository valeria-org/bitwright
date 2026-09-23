//! Independent, bit-serial reference evaluator for bitwright's bit-vector operator semantics.
//!
//! This crate is a **test oracle**. It is written from the semantics specification (SMT-LIB
//! `QF_BV`, total), not from the library it checks, and it is deliberately slow and simple: a
//! value is a vector of bits, least-significant first, and every arithmetic operation is spelled
//! out over individual bits (ripple-carry addition, negation as complement plus one,
//! shift-and-add multiplication, restoring long division). Native integers appear only to convert
//! inputs and outputs, and to turn a shift/rotate count into a bit position.
//!
//! Invalid inputs (width mismatches, out-of-range widths or bit positions) panic with a message;
//! valid inputs never panic. The only partial operation is [`UnOp::Bswap`], which [`un`] reports
//! as `None` when the width is not a multiple of 8.

#![forbid(unsafe_code)]

/// Largest width a caller may construct. Double-width products of 512-bit operands need 1024.
const MAX_WIDTH: u16 = 1024;

fn check_width(width: usize) {
    assert!(
        (1..=MAX_WIDTH as usize).contains(&width),
        "bitwright-ref: width {width} is outside 1..={MAX_WIDTH}"
    );
}

/// A fixed-width bit vector, least-significant bit first. Its length is its width.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Bits {
    bits: Vec<bool>,
}

impl Bits {
    /// Internal constructor without the public width cap (used for 2W-bit intermediates).
    fn raw(bits: Vec<bool>) -> Bits {
        assert!(!bits.is_empty(), "bitwright-ref: zero-width value");
        Bits { bits }
    }

    fn raw_zero(width: usize) -> Bits {
        Bits::raw(vec![false; width])
    }

    fn raw_ones(width: usize) -> Bits {
        Bits::raw(vec![true; width])
    }

    /// Width as `usize`, for internal indexing.
    fn w(&self) -> usize {
        self.bits.len()
    }

    fn msb(&self) -> bool {
        self.bits[self.w() - 1]
    }

    fn is_zero(&self) -> bool {
        self.bits.iter().all(|&b| !b)
    }

    /// The all-zero value of `width` bits.
    pub fn zero(width: u16) -> Bits {
        check_width(width as usize);
        Bits::raw_zero(width as usize)
    }

    /// `value` truncated to `width` bits; bits at 128 and above are zero.
    pub fn from_u128(width: u16, value: u128) -> Bits {
        check_width(width as usize);
        Bits::raw(
            (0..width as usize)
                .map(|i| i < 128 && (value >> i) & 1 == 1)
                .collect(),
        )
    }

    /// Two's-complement `value`, sign-extended to `width` bits and then truncated.
    pub fn from_i128(width: u16, value: i128) -> Bits {
        check_width(width as usize);
        Bits::raw(
            (0..width as usize)
                .map(|i| {
                    if i < 128 {
                        (value >> i) & 1 == 1
                    } else {
                        value < 0
                    }
                })
                .collect(),
        )
    }

    /// Little-endian `u64` limbs; bits beyond `width` are ignored and missing limbs read as zero.
    pub fn from_limbs(width: u16, limbs: &[u64]) -> Bits {
        check_width(width as usize);
        Bits::raw(
            (0..width as usize)
                .map(|i| limbs.get(i / 64).is_some_and(|l| (l >> (i % 64)) & 1 == 1))
                .collect(),
        )
    }

    /// `ceil(width / 64)` little-endian limbs; unused high bits are zero.
    pub fn to_limbs(&self) -> Vec<u64> {
        let mut limbs = vec![0u64; self.w().div_ceil(64)];
        for (i, &b) in self.bits.iter().enumerate() {
            if b {
                limbs[i / 64] |= 1u64 << (i % 64);
            }
        }
        limbs
    }

    /// The unsigned value, if it fits in a `u128`.
    pub fn to_u128(&self) -> Option<u128> {
        let mut value = 0u128;
        for (i, &b) in self.bits.iter().enumerate() {
            if b {
                if i >= 128 {
                    return None;
                }
                value |= 1u128 << i;
            }
        }
        Some(value)
    }

    /// The width in bits.
    pub fn width(&self) -> u16 {
        self.w() as u16
    }

    /// Bit `i` (0 = least significant). Panics if `i >= width`.
    pub fn bit(&self, i: u16) -> bool {
        assert!(
            (i as usize) < self.w(),
            "bitwright-ref: bit index {i} out of range for width {}",
            self.w()
        );
        self.bits[i as usize]
    }

    /// Builds a value from its bits, least-significant first. The length is the width.
    pub fn from_bools(bits: Vec<bool>) -> Bits {
        check_width(bits.len());
        Bits::raw(bits)
    }
}

/// Unary operators, `W -> W`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum UnOp {
    Not,
    Neg,
    Popcnt,
    Clz,
    Ctz,
    Bswap,
    BitRev,
}

/// Binary operators, `W, W -> W`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    UMulHi,
    SMulHi,
    UDiv,
    URem,
    SDiv,
    SRem,
    And,
    Or,
    Xor,
    Shl,
    LShr,
    AShr,
    RotL,
    RotR,
    Pdep,
    Pext,
}

/// Comparisons, `W, W -> 1`.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum CmpOp {
    Eq,
    Ne,
    Ult,
    Ule,
    Ugt,
    Uge,
    Slt,
    Sle,
    Sgt,
    Sge,
}

// ---------------------------------------------------------------------------------------------
// Bit-serial primitives
// ---------------------------------------------------------------------------------------------

fn same_width(what: &str, a: &Bits, b: &Bits) {
    assert_eq!(
        a.w(),
        b.w(),
        "bitwright-ref: {what}: operand widths differ ({} vs {})",
        a.w(),
        b.w()
    );
}

/// Ripple-carry addition. Returns the W-bit sum and the carry out of the top bit.
fn add_with_carry(a: &Bits, b: &Bits, carry_in: bool) -> (Bits, bool) {
    same_width("add", a, b);
    let mut carry = carry_in;
    let mut out = Vec::with_capacity(a.w());
    for (&x, &y) in a.bits.iter().zip(&b.bits) {
        out.push(x ^ y ^ carry);
        carry = (x & y) | (carry & (x ^ y));
    }
    (Bits::raw(out), carry)
}

fn not_bits(a: &Bits) -> Bits {
    Bits::raw(a.bits.iter().map(|&b| !b).collect())
}

fn add_bits(a: &Bits, b: &Bits) -> Bits {
    add_with_carry(a, b, false).0
}

/// Two's-complement negation: complement, then add one.
fn neg_bits(a: &Bits) -> Bits {
    add_with_carry(&not_bits(a), &Bits::raw_zero(a.w()), true).0
}

/// `a - b` as `a + !b + 1`.
fn sub_bits(a: &Bits, b: &Bits) -> Bits {
    add_with_carry(a, &not_bits(b), true).0
}

/// Shift left by a bit position `k` (any `k`; `k >= W` gives zero).
fn shl_by(a: &Bits, k: usize) -> Bits {
    Bits::raw((0..a.w()).map(|i| i >= k && a.bits[i - k]).collect())
}

/// Logical shift right by a bit position `k`.
fn lshr_by(a: &Bits, k: usize) -> Bits {
    let n = a.w();
    Bits::raw(
        (0..n)
            .map(|i| i.checked_add(k).is_some_and(|j| j < n && a.bits[j]))
            .collect(),
    )
}

/// Arithmetic shift right by a bit position `k`: vacated positions take the sign bit.
fn ashr_by(a: &Bits, k: usize) -> Bits {
    let n = a.w();
    let sign = a.msb();
    Bits::raw(
        (0..n)
            .map(|i| match i.checked_add(k) {
                Some(j) if j < n => a.bits[j],
                _ => sign,
            })
            .collect(),
    )
}

/// Shift-and-add multiplication modulo 2^W.
fn mul_bits(a: &Bits, b: &Bits) -> Bits {
    same_width("mul", a, b);
    let mut acc = Bits::raw_zero(a.w());
    for (i, &bi) in b.bits.iter().enumerate() {
        if bi {
            acc = add_bits(&acc, &shl_by(a, i));
        }
    }
    acc
}

/// Unsigned `a < b`, compared from the most significant bit down.
fn ult_bits(a: &Bits, b: &Bits) -> bool {
    same_width("compare", a, b);
    for i in (0..a.w()).rev() {
        if a.bits[i] != b.bits[i] {
            return b.bits[i];
        }
    }
    false
}

/// Signed (two's-complement) `a < b`.
fn slt_bits(a: &Bits, b: &Bits) -> bool {
    same_width("compare", a, b);
    match (a.msb(), b.msb()) {
        (true, false) => true,
        (false, true) => false,
        // Same sign: two's-complement order agrees with unsigned order.
        _ => ult_bits(a, b),
    }
}

fn zext_raw(a: &Bits, to: usize) -> Bits {
    assert!(to >= a.w(), "bitwright-ref: zext to {to} < width {}", a.w());
    let mut bits = a.bits.clone();
    bits.resize(to, false);
    Bits::raw(bits)
}

fn sext_raw(a: &Bits, to: usize) -> Bits {
    assert!(to >= a.w(), "bitwright-ref: sext to {to} < width {}", a.w());
    let sign = a.msb();
    let mut bits = a.bits.clone();
    bits.resize(to, sign);
    Bits::raw(bits)
}

fn extract_raw(a: &Bits, lo: usize, n: usize) -> Bits {
    assert!(n >= 1, "bitwright-ref: extract of zero bits");
    assert!(
        lo.checked_add(n).is_some_and(|end| end <= a.w()),
        "bitwright-ref: extract [{lo}, {lo}+{n}) out of range for width {}",
        a.w()
    );
    Bits::raw(a.bits[lo..lo + n].to_vec())
}

/// Restoring long division. `b` must be nonzero. Returns `(quotient, remainder)`.
fn udivrem_nonzero(a: &Bits, b: &Bits) -> (Bits, Bits) {
    same_width("divide", a, b);
    assert!(!b.is_zero());
    let n = a.w();
    // The partial remainder stays below b < 2^W before each shift, so W + 1 bits hold 2r + 1.
    let divisor = zext_raw(b, n + 1);
    let mut rem = Bits::raw_zero(n + 1);
    let mut quot = vec![false; n];
    for i in (0..n).rev() {
        rem = shl_by(&rem, 1);
        rem.bits[0] = a.bits[i];
        if !ult_bits(&rem, &divisor) {
            rem = sub_bits(&rem, &divisor);
            quot[i] = true;
        }
    }
    (Bits::raw(quot), extract_raw(&rem, 0, n))
}

fn udiv_bits(a: &Bits, b: &Bits) -> Bits {
    same_width("udiv", a, b);
    if b.is_zero() {
        Bits::raw_ones(a.w())
    } else {
        udivrem_nonzero(a, b).0
    }
}

fn urem_bits(a: &Bits, b: &Bits) -> Bits {
    same_width("urem", a, b);
    if b.is_zero() {
        a.clone()
    } else {
        udivrem_nonzero(a, b).1
    }
}

/// `bvsdiv`, by the four sign cases.
fn sdiv_bits(a: &Bits, b: &Bits) -> Bits {
    match (a.msb(), b.msb()) {
        (false, false) => udiv_bits(a, b),
        (true, false) => neg_bits(&udiv_bits(&neg_bits(a), b)),
        (false, true) => neg_bits(&udiv_bits(a, &neg_bits(b))),
        (true, true) => udiv_bits(&neg_bits(a), &neg_bits(b)),
    }
}

/// `bvsrem`, by the four sign cases (the remainder follows the dividend's sign).
fn srem_bits(a: &Bits, b: &Bits) -> Bits {
    match (a.msb(), b.msb()) {
        (false, false) => urem_bits(a, b),
        (true, false) => neg_bits(&urem_bits(&neg_bits(a), b)),
        (false, true) => urem_bits(a, &neg_bits(b)),
        (true, true) => neg_bits(&urem_bits(&neg_bits(a), &neg_bits(b))),
    }
}

/// High W bits of the 2W-bit product of the zero- or sign-extended operands.
fn mulhi_bits(a: &Bits, b: &Bits, signed: bool) -> Bits {
    same_width("mulhi", a, b);
    let n = a.w();
    let ext = |x: &Bits| {
        if signed {
            sext_raw(x, 2 * n)
        } else {
            zext_raw(x, 2 * n)
        }
    };
    extract_raw(&mul_bits(&ext(a), &ext(b)), n, n)
}

/// The unsigned value of `a` as a bit position, if it is below `limit`; `None` otherwise.
/// Horner from the MSB; once the running value reaches `limit` it can only grow.
fn count_below(a: &Bits, limit: usize) -> Option<usize> {
    let mut v = 0usize;
    for i in (0..a.w()).rev() {
        v = 2 * v + usize::from(a.bits[i]);
        if v >= limit {
            return None;
        }
    }
    Some(v)
}

/// The unsigned value of `a` modulo `m` (`m >= 1`), by Horner: `r = (2r + bit) mod m`.
fn value_mod(a: &Bits, m: usize) -> usize {
    let mut r = 0usize;
    for i in (0..a.w()).rev() {
        r = (2 * r + usize::from(a.bits[i])) % m;
    }
    r
}

/// A small count as a W-bit value. Every count used here is at most W < 2^W.
fn count_to_bits(width: usize, count: usize) -> Bits {
    let bits: Vec<bool> = (0..width)
        .map(|i| i < usize::BITS as usize && (count >> i) & 1 == 1)
        .collect();
    let out = Bits::raw(bits);
    debug_assert!(width >= usize::BITS as usize || count >> width == 0);
    out
}

fn rotl_by(a: &Bits, c: usize) -> Bits {
    let n = a.w();
    // Result bit i comes from bit (i - c) mod W.
    Bits::raw((0..n).map(|i| a.bits[(i + n - c) % n]).collect())
}

fn rotr_by(a: &Bits, c: usize) -> Bits {
    let n = a.w();
    // Result bit i comes from bit (i + c) mod W.
    Bits::raw((0..n).map(|i| a.bits[(i + c) % n]).collect())
}

fn pdep_bits(x: &Bits, m: &Bits) -> Bits {
    same_width("pdep", x, m);
    let mut out = vec![false; x.w()];
    let mut k = 0;
    for (i, &mi) in m.bits.iter().enumerate() {
        if mi {
            out[i] = x.bits[k];
            k += 1;
        }
    }
    Bits::raw(out)
}

fn pext_bits(x: &Bits, m: &Bits) -> Bits {
    same_width("pext", x, m);
    let mut out = vec![false; x.w()];
    let mut k = 0;
    for (i, &mi) in m.bits.iter().enumerate() {
        if mi {
            out[k] = x.bits[i];
            k += 1;
        }
    }
    Bits::raw(out)
}

// ---------------------------------------------------------------------------------------------
// Public operator entry points
// ---------------------------------------------------------------------------------------------

/// Evaluates a unary operator. `None` only for `Bswap` when the width is not a multiple of 8.
pub fn un(op: UnOp, a: &Bits) -> Option<Bits> {
    let n = a.w();
    Some(match op {
        UnOp::Not => not_bits(a),
        UnOp::Neg => neg_bits(a),
        UnOp::Popcnt => count_to_bits(n, a.bits.iter().filter(|&&b| b).count()),
        UnOp::Clz => count_to_bits(n, a.bits.iter().rev().take_while(|&&b| !b).count()),
        UnOp::Ctz => count_to_bits(n, a.bits.iter().take_while(|&&b| !b).count()),
        UnOp::Bswap => {
            if !n.is_multiple_of(8) {
                return None;
            }
            let bytes = n / 8;
            // Result byte j is source byte (bytes - 1 - j); bit order inside a byte is kept.
            Bits::raw(
                (0..n)
                    .map(|i| a.bits[(bytes - 1 - i / 8) * 8 + i % 8])
                    .collect(),
            )
        }
        UnOp::BitRev => Bits::raw((0..n).map(|i| a.bits[n - 1 - i]).collect()),
    })
}

/// Evaluates a binary operator. Both operands must have the same width.
pub fn bin(op: BinOp, a: &Bits, b: &Bits) -> Bits {
    same_width("bin", a, b);
    let n = a.w();
    match op {
        BinOp::Add => add_bits(a, b),
        BinOp::Sub => sub_bits(a, b),
        BinOp::Mul => mul_bits(a, b),
        BinOp::UMulHi => mulhi_bits(a, b, false),
        BinOp::SMulHi => mulhi_bits(a, b, true),
        BinOp::UDiv => udiv_bits(a, b),
        BinOp::URem => urem_bits(a, b),
        BinOp::SDiv => sdiv_bits(a, b),
        BinOp::SRem => srem_bits(a, b),
        BinOp::And => Bits::raw(a.bits.iter().zip(&b.bits).map(|(&x, &y)| x & y).collect()),
        BinOp::Or => Bits::raw(a.bits.iter().zip(&b.bits).map(|(&x, &y)| x | y).collect()),
        BinOp::Xor => Bits::raw(a.bits.iter().zip(&b.bits).map(|(&x, &y)| x ^ y).collect()),
        BinOp::Shl => match count_below(b, n) {
            Some(c) => shl_by(a, c),
            None => Bits::raw_zero(n),
        },
        BinOp::LShr => match count_below(b, n) {
            Some(c) => lshr_by(a, c),
            None => Bits::raw_zero(n),
        },
        BinOp::AShr => match count_below(b, n) {
            Some(c) => ashr_by(a, c),
            None => Bits::raw(vec![a.msb(); n]),
        },
        BinOp::RotL => rotl_by(a, value_mod(b, n)),
        BinOp::RotR => rotr_by(a, value_mod(b, n)),
        BinOp::Pdep => pdep_bits(a, b),
        BinOp::Pext => pext_bits(a, b),
    }
}

/// Evaluates a comparison. Both operands must have the same width.
pub fn cmp(op: CmpOp, a: &Bits, b: &Bits) -> bool {
    same_width("cmp", a, b);
    match op {
        CmpOp::Eq => a == b,
        CmpOp::Ne => a != b,
        CmpOp::Ult => ult_bits(a, b),
        CmpOp::Ule => !ult_bits(b, a),
        CmpOp::Ugt => ult_bits(b, a),
        CmpOp::Uge => !ult_bits(a, b),
        CmpOp::Slt => slt_bits(a, b),
        CmpOp::Sle => !slt_bits(b, a),
        CmpOp::Sgt => slt_bits(b, a),
        CmpOp::Sge => !slt_bits(a, b),
    }
}

/// Zero extension to `to >= width` bits (equal width is the identity).
pub fn zext(a: &Bits, to: u16) -> Bits {
    check_width(to as usize);
    zext_raw(a, to as usize)
}

/// Sign extension to `to >= width` bits (equal width is the identity).
pub fn sext(a: &Bits, to: u16) -> Bits {
    check_width(to as usize);
    sext_raw(a, to as usize)
}

/// Bits `[lo, lo + n)`; requires `n >= 1` and `lo + n <= width`.
pub fn extract(a: &Bits, lo: u16, n: u16) -> Bits {
    extract_raw(a, lo as usize, n as usize)
}

/// `hi * 2^lo.width + lo`; the result width is the sum of the widths.
pub fn concat(hi: &Bits, lo: &Bits) -> Bits {
    let mut bits = lo.bits.clone();
    bits.extend_from_slice(&hi.bits);
    check_width(bits.len());
    Bits::raw(bits)
}

/// `t` if the single bit of `c` is set, else `f`.
pub fn select(c: &Bits, t: &Bits, f: &Bits) -> Bits {
    assert_eq!(c.w(), 1, "bitwright-ref: select condition must be 1 bit");
    same_width("select", t, f);
    if c.bits[0] { t.clone() } else { f.clone() }
}

// ---------------------------------------------------------------------------------------------
// Expression terms
// ---------------------------------------------------------------------------------------------

/// A small expression tree over the operators above, evaluated against an environment of values.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Const(Bits),
    /// `env[index]`, which must have the given width.
    Var(usize, u16),
    Un(UnOp, Box<Term>),
    Bin(BinOp, Box<Term>, Box<Term>),
    /// A 1-bit result.
    Cmp(CmpOp, Box<Term>, Box<Term>),
    Zext(Box<Term>, u16),
    Sext(Box<Term>, u16),
    /// `Extract(t, lo, n)`: bits `[lo, lo + n)` of `t`.
    Extract(Box<Term>, u16, u16),
    /// `Concat(hi, lo)`.
    Concat(Box<Term>, Box<Term>),
    /// `Select(c, t, f)`.
    Select(Box<Term>, Box<Term>, Box<Term>),
}

impl Term {
    /// The width of the term's value (not validated against its operands).
    pub fn width(&self) -> u16 {
        match self {
            Term::Const(b) => b.width(),
            Term::Var(_, w) => *w,
            Term::Un(_, a) | Term::Bin(_, a, _) => a.width(),
            Term::Cmp(..) => 1,
            Term::Zext(_, w) | Term::Sext(_, w) | Term::Extract(_, _, w) => *w,
            Term::Concat(hi, lo) => hi.width() + lo.width(),
            Term::Select(_, t, _) => t.width(),
        }
    }

    /// Evaluates the term. `None` only when a `Bswap` is applied at a width that is not a
    /// multiple of 8. Panics on an ill-typed term or a missing/mis-sized variable.
    pub fn eval(&self, env: &[Bits]) -> Option<Bits> {
        Some(match self {
            Term::Const(b) => b.clone(),
            Term::Var(i, w) => {
                let v = env.get(*i).unwrap_or_else(|| {
                    panic!(
                        "bitwright-ref: variable {i} not in environment of {}",
                        env.len()
                    )
                });
                assert_eq!(
                    v.width(),
                    *w,
                    "bitwright-ref: variable {i} has width {} but the term declares {w}",
                    v.width()
                );
                v.clone()
            }
            Term::Un(op, a) => un(*op, &a.eval(env)?)?,
            Term::Bin(op, a, b) => bin(*op, &a.eval(env)?, &b.eval(env)?),
            Term::Cmp(op, a, b) => Bits::raw(vec![cmp(*op, &a.eval(env)?, &b.eval(env)?)]),
            Term::Zext(a, w) => zext(&a.eval(env)?, *w),
            Term::Sext(a, w) => sext(&a.eval(env)?, *w),
            Term::Extract(a, lo, n) => extract(&a.eval(env)?, *lo, *n),
            Term::Concat(hi, lo) => concat(&hi.eval(env)?, &lo.eval(env)?),
            Term::Select(c, t, f) => select(&c.eval(env)?, &t.eval(env)?, &f.eval(env)?),
        })
    }
}

#[cfg(test)]
mod tests;
