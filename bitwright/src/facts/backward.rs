//! Backward transfer: what an operator's operands must be, given facts about its result.
//!
//! The dual of [`super::transfer`]. Given facts `r` that the result is known to satisfy (an
//! assumption) and the facts of the operands, [`backward`] returns facts each operand must then
//! satisfy. Sound: for every operand tuple inside the operands' facts whose result lies inside
//! `r`, operand `k` lies inside `out[k]`. `None` for an operand means nothing is learned; the
//! whole answer is `None` when no operand tuple can produce a result inside `r` (the assumption is
//! infeasible). The suite in `tests.rs` checks this exhaustively at small widths.

use super::Facts;
use super::known::{
    KnownBits, bv_and, bv_lshr, bv_not, bv_or, bv_shl, bv_xor, high_mask, low_mask,
};
use super::range::{SRange, URange, sle, slt, ule, ult};
use super::transfer::TOp;
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::{BitVec, Width};

/// Facts for each operand (`None`: nothing learned), or `None` if infeasible.
pub(crate) type Operands = Option<[Option<Facts>; 3]>;

fn sub(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Sub, a, b)
}

fn add(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Add, a, b)
}

fn mul(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Mul, a, b)
}

/// Facts from known-bit masks; `None` when a bit is both.
fn from_masks(zero: BitVec, one: BitVec) -> Option<Facts> {
    Some(Facts::from_known(KnownBits::new(zero, one)?))
}

/// Facts of a value in `[lo, hi]` unsigned (empty: `None`).
fn in_urange(lo: BitVec, hi: BitVec) -> Option<Facts> {
    let w = lo.width();
    Facts::reduce(KnownBits::unknown(w), URange::new(lo, hi)?, SRange::full(w))
}

/// Facts of a value in `[lo, hi]` signed (empty: `None`).
fn in_srange(lo: BitVec, hi: BitVec) -> Option<Facts> {
    let w = lo.width();
    Facts::reduce(KnownBits::unknown(w), URange::full(w), SRange::new(lo, hi)?)
}

/// The number of low bits known in `k`, counting from bit 0 up to the first unknown one.
fn known_low_run(k: &KnownBits) -> u32 {
    super::known::trailing_zeros(&k.unknown_mask())
}

/// `{v + c : v in [lo, hi]}` as a non-wrapping unsigned interval, if it is one.
fn shift_urange(u: &URange, c: &BitVec) -> Option<URange> {
    let (lo, hi) = (add(&u.lo(), c), add(&u.hi(), c));
    if ule(&lo, &hi) {
        URange::new(lo, hi)
    } else {
        None
    }
}

/// `{v + c : v in [lo, hi]}` as a non-wrapping signed interval, if it is one.
fn shift_srange(s: &SRange, c: &BitVec) -> Option<SRange> {
    let (lo, hi) = (add(&s.lo(), c), add(&s.hi(), c));
    if sle(&lo, &hi) {
        SRange::new(lo, hi)
    } else {
        None
    }
}

/// Facts of `v + c` for every value `v` of `f` (ranges only where they do not wrap; known low
/// bits where the carry chain is known).
fn plus_const(f: &Facts, c: &BitVec) -> Facts {
    let w = f.width();
    let k = known_low_run(&f.known).min(u32::from(w.bits()));
    let low = low_mask(w, k);
    let v = bv_and(&add(&f.known.known_one(), c), &low);
    let known = KnownBits::from_masks(bv_and(&bv_not(&v), &low), v);
    let u = shift_urange(&f.urange, c).unwrap_or(URange::full(w));
    let s = shift_srange(&f.srange, c).unwrap_or(SRange::full(w));
    Facts::reduce(known, u, s).unwrap_or_else(|| Facts::top(w))
}

/// `c - v` for every value `v` of `f`.
fn const_minus(c: &BitVec, f: &Facts) -> Facts {
    plus_const(&negated(f), c)
}

/// Facts of `-v` for every value `v` of `f`.
fn negated(f: &Facts) -> Facts {
    let w = f.width();
    if let Some(v) = f.as_constant() {
        return Facts::constant(&BitVec::un_unchecked(UnOp::Neg, &v));
    }
    // Trailing zeros are kept: -v has as many as v.
    let tz = super::known::trailing_zeros(&bv_not(&f.known.known_zero())).min(u32::from(w.bits()));
    let known = KnownBits::from_masks(low_mask(w, tz), BitVec::zero(w));
    // -v = ~v + 1 reverses an unsigned interval not containing 0.
    let u = if f.urange.lo().is_zero() {
        URange::full(w)
    } else {
        URange::new(
            BitVec::un_unchecked(UnOp::Neg, &f.urange.hi()),
            BitVec::un_unchecked(UnOp::Neg, &f.urange.lo()),
        )
        .unwrap_or(URange::full(w))
    };
    Facts::reduce(known, u, SRange::full(w)).unwrap_or_else(|| Facts::top(w))
}

/// The inverse of an odd `c` modulo `2^W`.
fn odd_inverse(c: &BitVec) -> BitVec {
    let w = c.width();
    let two = BitVec::wrapping_from_u64(w, 2);
    // Newton's iteration doubles the correct low bits; `c` itself is correct to 3.
    let mut x = *c;
    for _ in 0..9 {
        x = mul(&x, &sub(&two, &mul(c, &x)));
    }
    x
}

/// Facts about `v` from facts about `v · c` for an odd constant `c`: the known low bits
/// determine `v`'s low bits.
fn div_odd(r: &Facts, c: &BitVec) -> Facts {
    let w = r.width();
    let inv = odd_inverse(c);
    let k = known_low_run(&r.known).min(u32::from(w.bits()));
    let low = low_mask(w, k);
    let v = bv_and(&mul(&r.known.known_one(), &inv), &low);
    Facts::from_known(KnownBits::from_masks(bv_and(&bv_not(&v), &low), v))
}

/// Known bits `k` rearranged by a bit permutation `p` (applied to both masks).
fn permute(k: &KnownBits, p: impl Fn(&BitVec) -> BitVec) -> Option<Facts> {
    from_masks(p(&k.known_zero()), p(&k.known_one()))
}

/// The constant shift or rotation count `c` as a `u32` below the width, if it is one.
fn small_count(c: &Facts, w: Width) -> Option<u32> {
    let v = c.as_constant()?.to_u64()?;
    (v < u64::from(w.bits())).then_some(v as u32)
}

fn unary(op: UnOp, r: &Facts, x: &Facts) -> Operands {
    let w = x.width();
    let bits = u32::from(w.bits());
    let out = match op {
        UnOp::Not => {
            let known = KnownBits::from_masks(r.known.known_one(), r.known.known_zero());
            let u = URange::new(bv_not(&r.urange.hi()), bv_not(&r.urange.lo()))?;
            let s = SRange::new(bv_not(&r.srange.hi()), bv_not(&r.srange.lo()))?;
            Some(Facts::reduce(known, u, s)?)
        }
        UnOp::Neg => Some(negated(r)),
        UnOp::Bswap | UnOp::BitRev => permute(&r.known, |m| BitVec::un_unchecked(op, m)),
        UnOp::Popcnt | UnOp::Clz | UnOp::Ctz => {
            // The count lies in [lo, hi] (and is at most W).
            let cap = |v: BitVec| v.to_u64().map_or(bits, |v| v.min(u64::from(bits)) as u32);
            let (lo, hi) = (cap(r.urange.lo()), cap(r.urange.hi()));
            let nonzero = in_urange(BitVec::one(w), BitVec::ones(w))?;
            let mut f = Facts::top(w);
            match op {
                UnOp::Popcnt => {
                    if hi == 0 {
                        f = f.meet(&Facts::constant(&BitVec::zero(w)))?;
                    }
                    if lo >= bits {
                        f = f.meet(&Facts::constant(&BitVec::ones(w)))?;
                    }
                    if lo > 0 {
                        f = f.meet(&nonzero)?;
                    }
                    if hi < bits {
                        let below_ones = sub(&BitVec::ones(w), &BitVec::one(w));
                        f = f.meet(&in_urange(BitVec::zero(w), below_ones)?)?;
                    }
                }
                UnOp::Clz => {
                    // At least `lo` leading zeros: below 2^(W-lo).
                    f = f.meet(&in_urange(BitVec::zero(w), low_mask(w, bits - lo))?)?;
                    if hi < bits {
                        // At most `hi` leading zeros: at least 2^(W-1-hi).
                        let min = bv_shl(&BitVec::one(w), bits - 1 - hi);
                        f = f.meet(&in_urange(min, BitVec::ones(w))?)?;
                    }
                }
                _ => {
                    // At least `lo` trailing zeros.
                    f = f.meet(&from_masks(low_mask(w, lo), BitVec::zero(w))?)?;
                    if hi < bits {
                        f = f.meet(&nonzero)?;
                    }
                    if lo == hi && hi < bits {
                        let one = bv_shl(&BitVec::one(w), hi);
                        f = f.meet(&from_masks(BitVec::zero(w), one)?)?;
                    }
                }
            }
            Some(f)
        }
    };
    Some([out, None, None])
}

/// Operand facts for `x op y ∈ r`, learning about `x` from `y` (the caller also asks with the
/// operands swapped, for commutative operators).
fn binary_left(op: BinOp, r: &Facts, x: &Facts, y: &Facts) -> Option<Option<Facts>> {
    let w = x.width();
    Some(match op {
        BinOp::And => {
            // Ones of the result are ones of both; a zero of the result where y is one is a
            // zero of x. x & y <= x (unsigned).
            let one = r.known.known_one();
            let zero = bv_and(&r.known.known_zero(), &y.known.known_one());
            let f = from_masks(zero, one)?;
            Some(f.meet(&in_urange(r.urange.lo(), BitVec::ones(w))?)?)
        }
        BinOp::Or => {
            let zero = r.known.known_zero();
            let one = bv_and(&r.known.known_one(), &y.known.known_zero());
            let f = from_masks(zero, one)?;
            Some(f.meet(&in_urange(BitVec::zero(w), r.urange.hi())?)?)
        }
        BinOp::Xor => {
            let both = bv_and(&r.known.known(), &y.known.known());
            let v = bv_xor(&r.known.known_one(), &y.known.known_one());
            Some(from_masks(bv_and(&bv_not(&v), &both), bv_and(&v, &both))?)
        }
        // x = r - y.
        BinOp::Add => Some(match y.as_constant() {
            Some(c) => plus_const(r, &BitVec::un_unchecked(UnOp::Neg, &c)),
            None => low_bits_of(r, y, sub),
        }),
        // x = r + y.
        BinOp::Sub => Some(match y.as_constant() {
            Some(c) => plus_const(r, &c),
            None => low_bits_of(r, y, add),
        }),
        BinOp::Mul => match y.as_constant() {
            Some(c) if c.bit(0) == Some(true) => Some(div_odd(r, &c)),
            _ => None,
        },
        BinOp::Shl => small_count(y, w).and_then(|k| {
            let keep = low_mask(w, u32::from(w.bits()) - k);
            from_masks(
                bv_and(&bv_lshr(&r.known.known_zero(), k), &keep),
                bv_and(&bv_lshr(&r.known.known_one(), k), &keep),
            )
        }),
        BinOp::LShr | BinOp::AShr => small_count(y, w).and_then(|k| {
            from_masks(
                bv_shl(&r.known.known_zero(), k),
                bv_shl(&r.known.known_one(), k),
            )
        }),
        BinOp::RotL | BinOp::RotR => match y.as_constant() {
            Some(c) => {
                let inverse = if op == BinOp::RotL {
                    BinOp::RotR
                } else {
                    BinOp::RotL
                };
                permute(&r.known, |m| BitVec::bin_unchecked(inverse, m, &c))
            }
            None => None,
        },
        _ => None,
    })
}

/// Facts of `x` from `x = f(r, y)` where `f` is addition or subtraction: the low bits known in
/// both `r` and `y` (no carry from unknown bits reaches them).
fn low_bits_of(r: &Facts, y: &Facts, f: impl Fn(&BitVec, &BitVec) -> BitVec) -> Facts {
    let w = r.width();
    let k = known_low_run(&r.known).min(known_low_run(&y.known));
    let low = low_mask(w, k);
    let v = bv_and(&f(&r.known.known_one(), &y.known.known_one()), &low);
    Facts::from_known(KnownBits::from_masks(bv_and(&bv_not(&v), &low), v))
}

fn binary(op: BinOp, r: &Facts, x: &Facts, y: &Facts) -> Operands {
    let left = binary_left(op, r, x, y)?;
    let right = match op {
        BinOp::And | BinOp::Or | BinOp::Xor | BinOp::Add | BinOp::Mul => binary_left(op, r, y, x)?,
        // y = x - r.
        BinOp::Sub => Some(match x.as_constant() {
            Some(c) => const_minus(&c, r),
            None => low_bits_of(r, x, |a, b| sub(b, a)),
        }),
        _ => None,
    };
    Some([left, right, None])
}

/// The comparison `op(a, b)` known to have the value `holds`, as a stored predicate that holds
/// (with the operands possibly swapped).
pub(crate) fn holding(op: CmpOp, holds: bool) -> (CmpOp, bool) {
    match (op, holds) {
        (op, true) => (op, false),
        (CmpOp::Eq, false) => (CmpOp::Ne, false),
        (CmpOp::Ne, false) => (CmpOp::Eq, false),
        (CmpOp::Ult, false) => (CmpOp::Ule, true),
        (CmpOp::Ule, false) => (CmpOp::Ult, true),
        (CmpOp::Slt, false) => (CmpOp::Sle, true),
        (CmpOp::Sle, false) => (CmpOp::Slt, true),
    }
}

/// Facts of `a` and `b` given that `op(a, b)` holds.
fn compare_holds(op: CmpOp, a: &Facts, b: &Facts) -> Option<[Option<Facts>; 2]> {
    let w = a.width();
    let one = BitVec::one(w);
    Some(match op {
        CmpOp::Eq => {
            let m = a.meet(b)?;
            [Some(m), Some(m)]
        }
        CmpOp::Ne => {
            let excl = |x: &Facts, y: &Facts| -> Option<Option<Facts>> {
                let Some(c) = y.as_constant() else {
                    return Some(None);
                };
                Some(Some(excluding(x, &c)?))
            };
            [excl(a, b)?, excl(b, a)?]
        }
        CmpOp::Ult => {
            if b.urange.hi().is_zero() || a.urange.lo().is_ones() {
                return None;
            }
            [
                Some(in_urange(BitVec::zero(w), sub(&b.urange.hi(), &one))?),
                Some(in_urange(add(&a.urange.lo(), &one), BitVec::ones(w))?),
            ]
        }
        CmpOp::Ule => [
            Some(in_urange(BitVec::zero(w), b.urange.hi())?),
            Some(in_urange(a.urange.lo(), BitVec::ones(w))?),
        ],
        CmpOp::Slt => {
            if b.srange.hi() == BitVec::smin(w) || a.srange.lo() == BitVec::smax(w) {
                return None;
            }
            [
                Some(in_srange(BitVec::smin(w), sub(&b.srange.hi(), &one))?),
                Some(in_srange(add(&a.srange.lo(), &one), BitVec::smax(w))?),
            ]
        }
        CmpOp::Sle => [
            Some(in_srange(BitVec::smin(w), b.srange.hi())?),
            Some(in_srange(a.srange.lo(), BitVec::smax(w))?),
        ],
    })
}

/// `f` without the value `c`: an end of either interval moves inward. `None` if `c` was the
/// only value.
fn excluding(f: &Facts, c: &BitVec) -> Option<Facts> {
    let w = f.width();
    if f.as_constant().as_ref() == Some(c) {
        return None;
    }
    let one = BitVec::one(w);
    let mut u = f.urange;
    if u.lo() == *c {
        u = URange::new(add(c, &one), u.hi())?;
    } else if u.hi() == *c {
        u = URange::new(u.lo(), sub(c, &one))?;
    }
    let mut s = f.srange;
    if s.lo() == *c {
        s = SRange::new(add(c, &one), s.hi())?;
    } else if s.hi() == *c {
        s = SRange::new(s.lo(), sub(c, &one))?;
    }
    Facts::reduce(f.known, u, s)
}

/// Operand facts of `op` given that its result lies in `r` and its operands in `args`.
pub(crate) fn backward(op: &TOp, r: &Facts, args: &[&Facts]) -> Operands {
    match *op {
        // Floating point: nothing is learned about the operands (yet).
        TOp::Const(_) | TOp::Top(_) | TOp::Fp(_) => Some([None, None, None]),
        TOp::Un(u) => unary(u, r, args[0]),
        TOp::Bin(b) => binary(b, r, args[0], args[1]),
        TOp::Cmp(c) => {
            let Some(v) = r.as_constant() else {
                return Some([None, None, None]);
            };
            let (held, swap) = holding(c, !v.is_zero());
            let (a, b) = if swap {
                (args[1], args[0])
            } else {
                (args[0], args[1])
            };
            let [fa, fb] = compare_holds(held, a, b)?;
            Some(if swap { [fb, fa, None] } else { [fa, fb, None] })
        }
        TOp::Zext(_) => {
            let x = args[0];
            let (w, to) = (x.width(), r.width());
            let n = u32::from(w.bits());
            // The high bits must be zero.
            if !bv_and(
                &r.known.known_one(),
                &high_mask(to, u32::from(to.bits()) - n),
            )
            .is_zero()
            {
                return None;
            }
            let t = |v: &BitVec| v.trunc(w).unwrap_or(BitVec::zero(w));
            let max = low_mask(to, n);
            if ult(&max, &r.urange.lo()) {
                return None;
            }
            let hi = if ule(&r.urange.hi(), &max) {
                r.urange.hi()
            } else {
                max
            };
            let f = from_masks(t(&r.known.known_zero()), t(&r.known.known_one()))?
                .meet(&in_urange(t(&r.urange.lo()), t(&hi))?)?;
            Some([Some(f), None, None])
        }
        TOp::Sext(_) => {
            let x = args[0];
            let (w, to) = (x.width(), r.width());
            let n = u32::from(w.bits());
            let t = |v: &BitVec| v.trunc(w).unwrap_or(BitVec::zero(w));
            // Bits n-1.. of the result are all the sign bit of x.
            let sign_bits = high_mask(to, u32::from(to.bits()) - n + 1);
            let mut zero = t(&r.known.known_zero());
            let mut one = t(&r.known.known_one());
            let top = bv_shl(&BitVec::one(w), n - 1);
            if !bv_and(&r.known.known_zero(), &sign_bits).is_zero() {
                zero = bv_or(&zero, &top);
            }
            if !bv_and(&r.known.known_one(), &sign_bits).is_zero() {
                one = bv_or(&one, &top);
            }
            let mut f = from_masks(zero, one)?;
            // The signed interval, clamped to what a sign extension can produce.
            let lo_x = BitVec::smin(w).sext(to).unwrap_or(BitVec::smin(to));
            let hi_x = BitVec::smax(w).sext(to).unwrap_or(BitVec::smax(to));
            let lo = if slt(&r.srange.lo(), &lo_x) {
                lo_x
            } else {
                r.srange.lo()
            };
            let hi = if slt(&hi_x, &r.srange.hi()) {
                hi_x
            } else {
                r.srange.hi()
            };
            if slt(&hi, &lo) {
                return None;
            }
            f = f.meet(&in_srange(t(&lo), t(&hi))?)?;
            Some([Some(f), None, None])
        }
        TOp::Extract { lo, .. } => {
            let x = args[0];
            let w = x.width();
            let place = |v: &BitVec| bv_shl(&v.zext(w).unwrap_or(BitVec::zero(w)), u32::from(lo));
            let f = from_masks(place(&r.known.known_zero()), place(&r.known.known_one()))?;
            Some([Some(f), None, None])
        }
        TOp::Concat => {
            let (h, l) = (args[0], args[1]);
            let (wh, wl) = (h.width(), l.width());
            let hi_of = |v: &BitVec| v.extract(wl.bits(), wh).unwrap_or(BitVec::zero(wh));
            let lo_of = |v: &BitVec| v.trunc(wl).unwrap_or(BitVec::zero(wl));
            let fh = from_masks(hi_of(&r.known.known_zero()), hi_of(&r.known.known_one()))?
                .meet(&in_urange(hi_of(&r.urange.lo()), hi_of(&r.urange.hi()))?)?;
            let mut fl = from_masks(lo_of(&r.known.known_zero()), lo_of(&r.known.known_one()))?;
            if hi_of(&r.urange.lo()) == hi_of(&r.urange.hi()) {
                fl = fl.meet(&in_urange(lo_of(&r.urange.lo()), lo_of(&r.urange.hi()))?)?;
            }
            Some([Some(fh), Some(fl), None])
        }
        TOp::Select => {
            let (c, t, e) = (args[0], args[1], args[2]);
            let one = Facts::constant(&BitVec::one(Width::W1));
            let zero = Facts::constant(&BitVec::zero(Width::W1));
            let can_t = c.meet(&one).is_some() && t.meet(r).is_some();
            let can_e = c.meet(&zero).is_some() && e.meet(r).is_some();
            Some(match (can_t, can_e) {
                (false, false) => return None,
                (true, false) => [Some(one), Some(t.meet(r)?), None],
                (false, true) => [Some(zero), None, Some(e.meet(r)?)],
                (true, true) => [None, None, None],
            })
        }
    }
}
