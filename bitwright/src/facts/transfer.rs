//! Transfer functions: facts of an operator's result from facts of its operands.
//!
//! Every function here must be sound: for every concrete operand tuple inside the operands'
//! facts, the concrete result must be inside the returned facts. The suite in `tests.rs`
//! checks this exhaustively at small widths against the reference evaluator. Precision is
//! best-effort; `Facts::top` is always a correct answer.

use super::Facts;
use super::known;
use super::known::{
    KnownBits, bv_add, bv_and, bv_lshr, bv_not, bv_or, bv_shl, bv_xor, count_ones, high_mask,
    leading_zeros, low_mask, trailing_zeros,
};
use super::range::{SRange, URange, gcd, rem, sle, slt, ule, ult};
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::{BitVec, Width};

/// The operator whose result facts are being computed.
#[derive(Clone, Copy, Debug)]
pub(crate) enum TOp {
    Const(BitVec),
    /// A value about which nothing is known (a symbol).
    Top(Width),
    Un(UnOp),
    Bin(BinOp),
    Cmp(CmpOp),
    Zext(Width),
    Sext(Width),
    Extract {
        lo: u16,
        width: Width,
    },
    Concat,
    Select,
}

fn small(w: Width, v: u64) -> BitVec {
    BitVec::wrapping_from_u64(w, v)
}

// ----- strides ---------------------------------------------------------------------------------

/// A stride dividing `g` that fits in 64 bits: `g` itself, or its largest power of two that fits.
fn fit(g: u128) -> u64 {
    u64::try_from(g).unwrap_or(1 << g.trailing_zeros().min(63))
}

fn gcd128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// A stride of `stride · 2^c` (0 stays 0).
fn stride_shl(stride: u64, c: u32) -> u64 {
    if stride == 0 {
        0
    } else if c < 64 && u128::from(stride) << c <= u128::from(u64::MAX) {
        stride << c
    } else {
        1 << (stride.trailing_zeros() + c).min(63)
    }
}

/// `2^c mod m` (`m >= 1`).
fn pow2_mod(c: u32, m: u64) -> u64 {
    let m = u128::from(m);
    let mut r = 1 % m;
    for _ in 0..c {
        r = (r * 2) % m;
    }
    r as u64
}

/// `[lo, hi]` by `stride`, or the plain interval if that is not a strided interval.
fn strided(lo: BitVec, hi: BitVec, stride: u64, full: URange) -> URange {
    URange::strided(lo, hi, stride)
        .or_else(|| URange::new(lo, hi))
        .unwrap_or(full)
}

/// The facts of a value in `[lo, hi]` (unsigned), with known bits from the common prefix.
fn from_urange(lo: BitVec, hi: BitVec) -> Facts {
    let w = lo.width();
    Facts::reduce(
        KnownBits::unknown(w),
        URange::new(lo, hi).unwrap_or(URange::full(w)),
        SRange::full(w),
    )
    .unwrap_or_else(|| Facts::top(w))
}

/// Up to `limit` concrete values consistent with `f`, if there are that few.
fn small_set(f: &Facts, limit_bits: u32) -> Option<Vec<BitVec>> {
    let vals = f.known.enumerate(limit_bits)?;
    Some(vals.into_iter().filter(|v| f.contains(v)).collect())
}

/// Join of `g(v)` over every value `v` of `f`, if there are at most 16.
fn over_values(f: &Facts, mut g: impl FnMut(&BitVec) -> Facts) -> Option<Facts> {
    let vals = small_set(f, 4)?;
    let mut it = vals.iter();
    let first = g(it.next()?);
    Some(it.fold(first, |acc, v| acc.hull(&g(v))))
}

// ----- known-bits helpers ----------------------------------------------------------------------

/// Known bits of `a + b + carry_in` (LLVM's computeForAddCarry, width-generic).
fn kb_add_carry(a: &KnownBits, b: &KnownBits, carry_one: bool) -> KnownBits {
    let w = a.width();
    let carry = if carry_one {
        BitVec::one(w)
    } else {
        BitVec::zero(w)
    };
    let possible_sum_zero = bv_add(&bv_add(&a.umax(), &b.umax()), &carry);
    let possible_sum_one = bv_add(&bv_add(&a.umin(), &b.umin()), &carry);
    let carry_known_zero = bv_not(&bv_xor(
        &bv_xor(&possible_sum_zero, &a.known_zero()),
        &b.known_zero(),
    ));
    let carry_known_one = bv_xor(&bv_xor(&possible_sum_one, &a.known_one()), &b.known_one());
    let known = bv_and(
        &bv_and(&a.known(), &b.known()),
        &bv_or(&carry_known_zero, &carry_known_one),
    );
    KnownBits::from_masks(
        bv_and(&bv_not(&possible_sum_zero), &known),
        bv_and(&possible_sum_one, &known),
    )
}

fn kb_not(a: &KnownBits) -> KnownBits {
    KnownBits::from_masks(a.known_one(), a.known_zero())
}

fn kb_mul(a: &KnownBits, b: &KnownBits) -> KnownBits {
    let w = a.width();
    let wb = u32::from(w.bits());
    let tz = (a.trailing_known_zeros() + b.trailing_known_zeros()).min(wb);
    let k = a.known_low_prefix().min(b.known_low_prefix());
    let low = low_mask(w, k);
    let p = BitVec::bin_unchecked(
        BinOp::Mul,
        &bv_and(&a.known_one(), &low),
        &bv_and(&b.known_one(), &low),
    );
    let zero = bv_or(&low_mask(w, tz), &bv_and(&bv_not(&p), &low));
    let one = bv_and(&p, &low);
    // Bits below `tz` are zero in both descriptions, so they agree.
    KnownBits::from_masks(bv_and(&zero, &bv_not(&one)), one)
}

fn kb_shift_const(op: BinOp, a: &KnownBits, c: u32) -> KnownBits {
    let w = a.width();
    let wb = u32::from(w.bits());
    match op {
        BinOp::Shl => {
            if c >= wb {
                return KnownBits::constant(&BitVec::zero(w));
            }
            KnownBits::from_masks(
                bv_or(&bv_shl(&a.known_zero(), c), &low_mask(w, c)),
                bv_shl(&a.known_one(), c),
            )
        }
        BinOp::LShr => {
            if c >= wb {
                return KnownBits::constant(&BitVec::zero(w));
            }
            KnownBits::from_masks(
                bv_or(&bv_lshr(&a.known_zero(), c), &high_mask(w, c)),
                bv_lshr(&a.known_one(), c),
            )
        }
        BinOp::AShr => {
            let c = c.min(wb - 1);
            let sign = a.bit(w.bits() - 1);
            let (mut zero, mut one) = (bv_lshr(&a.known_zero(), c), bv_lshr(&a.known_one(), c));
            match sign {
                Some(false) => zero = bv_or(&zero, &high_mask(w, c)),
                Some(true) => one = bv_or(&one, &high_mask(w, c)),
                None => {}
            }
            KnownBits::from_masks(zero, one)
        }
        BinOp::RotL | BinOp::RotR => {
            let r = c % wb;
            let k = if op == BinOp::RotL { r } else { (wb - r) % wb };
            let rot = |m: &BitVec| BitVec::bin_unchecked(BinOp::RotL, m, &small(w, u64::from(k)));
            KnownBits::from_masks(rot(&a.known_zero()), rot(&a.known_one()))
        }
        _ => KnownBits::unknown(w),
    }
}

// ----- per-operator transfers ------------------------------------------------------------------

fn unary(op: UnOp, a: &Facts) -> Facts {
    let w = a.width();
    let wb = u64::from(w.bits());
    match op {
        UnOp::Not => {
            // ~x = ones − x: the order reverses, the spacing stays.
            let u = URange::strided(
                bv_not(&a.urange.hi()),
                bv_not(&a.urange.lo()),
                a.urange.stride(),
            );
            let s = SRange::new(bv_not(&a.srange.hi()), bv_not(&a.srange.lo()));
            Facts::reduce(
                kb_not(&a.known),
                u.unwrap_or(URange::full(w)),
                s.unwrap_or(SRange::full(w)),
            )
            .unwrap_or_else(|| Facts::top(w))
        }
        UnOp::Neg => {
            let known = kb_add_carry(
                &kb_not(&a.known),
                &KnownBits::constant(&BitVec::zero(w)),
                true,
            );
            let neg = |v: &BitVec| BitVec::un_unchecked(UnOp::Neg, v);
            let u = if a.urange.lo().is_zero() && a.urange.hi().is_zero() {
                URange::constant(&BitVec::zero(w))
            } else if !a.urange.lo().is_zero() {
                // −x = 2^W − x for x ≠ 0: the order reverses, the spacing stays.
                strided(
                    neg(&a.urange.hi()),
                    neg(&a.urange.lo()),
                    a.urange.stride(),
                    URange::full(w),
                )
            } else {
                URange::full(w)
            };
            let s = if a.srange.lo() != BitVec::smin(w) {
                SRange::new(neg(&a.srange.hi()), neg(&a.srange.lo())).unwrap_or(SRange::full(w))
            } else {
                SRange::full(w)
            };
            Facts::reduce(known, u, s).unwrap_or_else(|| Facts::top(w))
        }
        UnOp::Popcnt => {
            let lo = u64::from(count_ones(&a.known.known_one()));
            let hi = wb - u64::from(count_ones(&a.known.known_zero()));
            from_urange(small(w, lo), small(w, hi))
        }
        UnOp::Clz => {
            let lo = u64::from(a.known.leading_known_zeros());
            let one = a.known.known_one();
            let hi = if one.is_zero() {
                wb
            } else {
                u64::from(leading_zeros(&one))
            };
            from_urange(small(w, lo), small(w, hi.max(lo)))
        }
        UnOp::Ctz => {
            let lo = u64::from(a.known.trailing_known_zeros());
            let one = a.known.known_one();
            let hi = if one.is_zero() {
                wb
            } else {
                u64::from(trailing_zeros(&one))
            };
            from_urange(small(w, lo), small(w, hi.max(lo)))
        }
        UnOp::Bswap | UnOp::BitRev => {
            let p = |m: &BitVec| BitVec::un_unchecked(op, m);
            Facts::from_known(KnownBits::from_masks(
                p(&a.known.known_zero()),
                p(&a.known.known_one()),
            ))
        }
    }
}

fn binary(op: BinOp, a: &Facts, b: &Facts) -> Facts {
    let w = a.width();
    let top = Facts::top(w);
    let full_u = URange::full(w);
    let full_s = SRange::full(w);
    let bin = |x: &BitVec, y: &BitVec| BitVec::bin_unchecked(op, x, y);
    // An exactly known count is handled precisely for every shift and rotate.
    let count = b.known.as_constant().and_then(|c| {
        c.to_u64()
            .map(|v| v.min(u64::from(u32::MAX)) as u32)
            .or(Some(u32::MAX))
    });
    let reduce = |k: KnownBits, u: URange, s: SRange| Facts::reduce(k, u, s).unwrap_or(top);
    match op {
        BinOp::Add | BinOp::Sub => {
            let known = if op == BinOp::Add {
                kb_add_carry(&a.known, &b.known, false)
            } else {
                kb_add_carry(&a.known, &kb_not(&b.known), true)
            };
            let (au, bu, as_, bs) = (a.urange, b.urange, a.srange, b.srange);
            // Without wrap-around, a sum or difference of members steps by the strides' gcd.
            let stride = gcd(au.stride(), bu.stride());
            let u = if op == BinOp::Add {
                let hi = bin(&au.hi(), &bu.hi());
                if ule(&au.hi(), &hi) {
                    strided(bin(&au.lo(), &bu.lo()), hi, stride, full_u)
                } else {
                    full_u
                }
            } else if ule(&bu.hi(), &au.lo()) {
                strided(
                    bin(&au.lo(), &bu.hi()),
                    bin(&au.hi(), &bu.lo()),
                    stride,
                    full_u,
                )
            } else {
                full_u
            };
            let s = {
                // No signed overflow at either end means none in between.
                let (lo, hi) = if op == BinOp::Add {
                    ((as_.lo(), bs.lo()), (as_.hi(), bs.hi()))
                } else {
                    ((as_.lo(), bs.hi()), (as_.hi(), bs.lo()))
                };
                match (
                    signed_exact(op, &lo.0, &lo.1),
                    signed_exact(op, &hi.0, &hi.1),
                ) {
                    (Some(l), Some(h)) => SRange::new(l, h).unwrap_or(full_s),
                    _ => full_s,
                }
            };
            reduce(known, u, s)
        }
        BinOp::Mul => {
            let known = kb_mul(&a.known, &b.known);
            let (au, bu) = (a.urange, b.urange);
            let u = if BitVec::bin_unchecked(BinOp::UMulHi, &au.hi(), &bu.hi()).is_zero() {
                // (la + i·sa)(lb + j·sb) − la·lb is a multiple of gcd(la·sb, lb·sa, sa·sb).
                let (sa, sb) = (u128::from(au.stride()), u128::from(bu.stride()));
                let stride = match (au.lo().to_u64(), bu.lo().to_u64()) {
                    (Some(la), Some(lb)) => fit(gcd128(
                        gcd128(u128::from(la) * sb, u128::from(lb) * sa),
                        sa * sb,
                    )),
                    _ => 1,
                };
                strided(
                    bin(&au.lo(), &bu.lo()),
                    bin(&au.hi(), &bu.hi()),
                    stride,
                    full_u,
                )
            } else {
                full_u
            };
            let s = signed_corners(w, a, b, |x, y| x.checked_mul(y)).unwrap_or(full_s);
            reduce(known, u, s)
        }
        BinOp::UMulHi => {
            let (au, bu) = (a.urange, b.urange);
            from_urange(bin(&au.lo(), &bu.lo()), bin(&au.hi(), &bu.hi()))
        }
        BinOp::SMulHi => top,
        BinOp::UDiv => {
            let (au, bu) = (a.urange, b.urange);
            if bu.hi().is_zero() {
                return Facts::constant(&BitVec::ones(w));
            }
            let lo = bin(&au.lo(), &bu.hi());
            let hi = if bu.lo().is_zero() {
                BitVec::ones(w)
            } else {
                bin(&au.hi(), &bu.lo())
            };
            let mut f = from_urange(lo, hi);
            // Members spaced by a multiple of the divisor divide to members spaced by the
            // quotient: (lo + i·s) / d = lo / d + i·(s / d) when d divides s.
            if let Some(d) = b.known.as_constant().and_then(|d| d.to_u64())
                && d > 0
                && au.stride().is_multiple_of(d)
                && let Some(u) = URange::strided(lo, hi, au.stride() / d)
            {
                f = f.meet_urange(&u).unwrap_or(f);
            }
            // Division by a known power of two is a right shift.
            if let Some(c) = b.known.as_constant()
                && count_ones(&c) == 1
            {
                let k = kb_shift_const(BinOp::LShr, &a.known, trailing_zeros(&c));
                f = f.meet_known(&k).unwrap_or(f);
            }
            f
        }
        BinOp::URem => {
            let (au, bu) = (a.urange, b.urange);
            // The remainder never exceeds the dividend (for b = 0 it is the dividend).
            let mut hi = au.hi();
            if !bu.lo().is_zero() {
                let bm1 = BitVec::bin_unchecked(BinOp::Sub, &bu.hi(), &BitVec::one(w));
                if ult(&bm1, &hi) {
                    hi = bm1;
                }
            }
            let mut f = from_urange(BitVec::zero(w), hi);
            // Every remainder by d is congruent to `lo` modulo gcd(stride, d).
            if let Some(d) = b.known.as_constant().and_then(|d| d.to_u64())
                && d > 0
            {
                let g = gcd(au.stride(), d);
                if let Some(u) = f.urange.meet_class(rem(&au.lo(), g), g) {
                    f = f.meet_urange(&u).unwrap_or(f);
                }
            }
            if let Some(c) = b.known.as_constant()
                && count_ones(&c) == 1
            {
                let mask = BitVec::bin_unchecked(BinOp::Sub, &c, &BitVec::one(w));
                let k = KnownBits::from_masks(
                    bv_or(&a.known.known_zero(), &bv_not(&mask)),
                    bv_and(&a.known.known_one(), &mask),
                );
                f = f.meet_known(&k).unwrap_or(f);
            }
            f
        }
        BinOp::SDiv => {
            // Truncating division is monotone in each argument within one divisor sign, so
            // the extremes are at the corners (narrow widths, divisor range excluding 0).
            let (d_lo, d_hi) = (b.srange.lo(), b.srange.hi());
            let zero = BitVec::zero(w);
            let one_sided = slt(&zero, &d_lo) || slt(&d_hi, &zero);
            if one_sided {
                let q = |x: i128, y: i128| {
                    if y == -1 && x == min_signed(w) {
                        None // wraps to smin: not monotone across this corner
                    } else {
                        Some(x / y)
                    }
                };
                if let Some(s) = signed_corners(w, a, b, q) {
                    return reduce(KnownBits::unknown(w), full_u, s);
                }
            }
            top
        }
        BinOp::SRem => {
            // |r| < |d| and the sign follows the dividend (narrow widths).
            let (d_lo, d_hi) = (b.srange.lo(), b.srange.hi());
            let zero = BitVec::zero(w);
            let bound = if slt(&zero, &d_lo) {
                d_hi.to_i128().filter(|_| w.bits() <= 64)
            } else if slt(&d_hi, &zero) && d_lo != BitVec::smin(w) {
                d_lo.to_i128().filter(|_| w.bits() <= 64).map(|v| -v)
            } else {
                None
            };
            if let (Some(m), Some(alo), Some(ahi)) =
                (bound, a.srange.lo().to_i128(), a.srange.hi().to_i128())
            {
                let lim = m - 1;
                let (lo, hi) = if alo >= 0 {
                    (0, ahi.min(lim))
                } else if ahi <= 0 {
                    (alo.max(-lim), 0)
                } else {
                    (-lim, lim)
                };
                let s = SRange::new(
                    BitVec::wrapping_from_i128(w, lo),
                    BitVec::wrapping_from_i128(w, hi),
                )
                .unwrap_or(full_s);
                return reduce(KnownBits::unknown(w), full_u, s);
            }
            top
        }
        BinOp::And => {
            let known = KnownBits::from_masks(
                bv_or(&a.known.known_zero(), &b.known.known_zero()),
                bv_and(&a.known.known_one(), &b.known.known_one()),
            );
            let hi = if ult(&a.urange.hi(), &b.urange.hi()) {
                a.urange.hi()
            } else {
                b.urange.hi()
            };
            reduce(
                known,
                URange::new(BitVec::zero(w), hi).unwrap_or(full_u),
                full_s,
            )
        }
        BinOp::Or => {
            let known = KnownBits::from_masks(
                bv_and(&a.known.known_zero(), &b.known.known_zero()),
                bv_or(&a.known.known_one(), &b.known.known_one()),
            );
            let lo = if ult(&a.urange.lo(), &b.urange.lo()) {
                b.urange.lo()
            } else {
                a.urange.lo()
            };
            reduce(
                known,
                URange::new(lo, BitVec::ones(w)).unwrap_or(full_u),
                full_s,
            )
        }
        BinOp::Xor => {
            let (az, ao, bz, bo) = (
                a.known.known_zero(),
                a.known.known_one(),
                b.known.known_zero(),
                b.known.known_one(),
            );
            Facts::from_known(KnownBits::from_masks(
                bv_or(&bv_and(&az, &bz), &bv_and(&ao, &bo)),
                bv_or(&bv_and(&az, &bo), &bv_and(&ao, &bz)),
            ))
        }
        BinOp::Shl | BinOp::LShr | BinOp::AShr | BinOp::RotL | BinOp::RotR => {
            if let Some(c) = count {
                let rotate = matches!(op, BinOp::RotL | BinOp::RotR);
                let c = if rotate {
                    // The count's full value modulo W.
                    let cv = b.known.as_constant().unwrap_or(BitVec::zero(w));
                    let m = BitVec::bin_unchecked(BinOp::URem, &cv, &small(w, u64::from(w.bits())));
                    m.to_u64().unwrap_or(0) as u32
                } else {
                    c
                };
                let known = kb_shift_const(op, &a.known, c);
                let (u, s) = shift_ranges(op, a, c);
                return reduce(known, u, s);
            }
            if let Some(f) = over_values(b, |cv| binary(op, a, &Facts::constant(cv))) {
                return f;
            }
            shift_symbolic(op, a, b)
        }
        BinOp::Pdep | BinOp::Pext => bit_permute(op, a, b),
    }
}

/// `x op y` exactly, if it does not overflow as a signed operation.
fn signed_exact(op: BinOp, x: &BitVec, y: &BitVec) -> Option<BitVec> {
    let r = BitVec::bin_unchecked(op, x, y);
    let (sx, sy, sr) = (x.msb(), y.msb(), r.msb());
    let overflow = match op {
        BinOp::Add => sx == sy && sr != sx,
        BinOp::Sub => sx != sy && sr != sx,
        _ => true,
    };
    (!overflow).then_some(r)
}

fn min_signed(w: Width) -> i128 {
    -(1i128 << (w.bits() - 1))
}

/// The signed interval of `f(x, y)` over the corners of `a`'s and `b`'s signed ranges, for
/// operations whose extremes lie at the corners. Narrow widths only (at most 64 bits);
/// `None` if any corner is undefined for `f` or does not fit the width.
fn signed_corners(
    w: Width,
    a: &Facts,
    b: &Facts,
    f: impl Fn(i128, i128) -> Option<i128>,
) -> Option<SRange> {
    if w.bits() > 64 {
        return None;
    }
    let (min, max) = (min_signed(w), -min_signed(w) - 1);
    let xs = [a.srange.lo().to_i128()?, a.srange.hi().to_i128()?];
    let ys = [b.srange.lo().to_i128()?, b.srange.hi().to_i128()?];
    let mut lo = i128::MAX;
    let mut hi = i128::MIN;
    for x in xs {
        for y in ys {
            let v = f(x, y)?;
            if v < min || v > max {
                return None;
            }
            lo = lo.min(v);
            hi = hi.max(v);
        }
    }
    SRange::new(
        BitVec::wrapping_from_i128(w, lo),
        BitVec::wrapping_from_i128(w, hi),
    )
}

fn shift_ranges(op: BinOp, a: &Facts, c: u32) -> (URange, SRange) {
    let w = a.width();
    let wb = u32::from(w.bits());
    let (fu, fs) = (URange::full(w), SRange::full(w));
    if c >= wb && op != BinOp::AShr {
        return (fu, fs);
    }
    let cc = small(w, u64::from(c.min(wb - 1)));
    let sh = |v: &BitVec| BitVec::bin_unchecked(op, v, &cc);
    match op {
        BinOp::LShr => {
            // Members spaced by a multiple of 2^c keep their low c bits, so they shift apart
            // evenly.
            let s = a.urange.stride();
            let stride = if s != 0 && s.trailing_zeros() >= c {
                s >> c
            } else {
                1
            };
            (
                strided(sh(&a.urange.lo()), sh(&a.urange.hi()), stride, fu),
                fs,
            )
        }
        BinOp::AShr => (
            fu,
            SRange::new(sh(&a.srange.lo()), sh(&a.srange.hi())).unwrap_or(fs),
        ),
        BinOp::Shl => {
            // Monotone while the largest value does not lose bits.
            let hi = sh(&a.urange.hi());
            if bv_lshr(&hi, c) == a.urange.hi() {
                let stride = stride_shl(a.urange.stride(), c);
                (strided(sh(&a.urange.lo()), hi, stride, fu), fs)
            } else {
                (fu, fs)
            }
        }
        _ => (fu, fs),
    }
}

fn shift_symbolic(op: BinOp, a: &Facts, b: &Facts) -> Facts {
    let w = a.width();
    let wb = u32::from(w.bits());
    let as_count = |v: BitVec| {
        v.to_u64()
            .map_or(u32::MAX, |v| v.min(u64::from(u32::MAX)) as u32)
    };
    let cmin = as_count(b.urange.lo());
    let cmax = as_count(b.urange.hi());
    let clamp = |x: u32| x.min(wb);
    match op {
        BinOp::Shl => {
            if cmin >= wb {
                return Facts::constant(&BitVec::zero(w));
            }
            let tz = clamp(a.known.trailing_known_zeros().saturating_add(cmin));
            // Shifting left by at most cmax keeps at least lz(a) - cmax leading zeros.
            let lz = a.known.leading_known_zeros().saturating_sub(cmax);
            Facts::from_known(KnownBits::from_masks(
                known::bv_or(&low_mask(w, tz), &high_mask(w, lz)),
                BitVec::zero(w),
            ))
        }
        BinOp::LShr => {
            if cmin >= wb {
                return Facts::constant(&BitVec::zero(w));
            }
            let lz = clamp(a.known.leading_known_zeros().saturating_add(cmin));
            let mut f = Facts::from_known(KnownBits::from_masks(high_mask(w, lz), BitVec::zero(w)));
            // A right shift by at least cmin never exceeds hi >> cmin.
            if let Some(u) = URange::new(BitVec::zero(w), bv_lshr(&a.urange.hi(), cmin)) {
                f = f.meet_urange(&u).unwrap_or(f);
            }
            f
        }
        BinOp::AShr => {
            // Monotone in the count toward the sign fill: extremes at cmin and cmax.
            let lo_c = small(w, u64::from(cmin.min(wb - 1)));
            let hi_c = small(w, u64::from(cmax.min(wb - 1)));
            let sh = |v: &BitVec, c: &BitVec| BitVec::bin_unchecked(BinOp::AShr, v, c);
            let (alo, ahi) = (a.srange.lo(), a.srange.hi());
            let cands = [
                sh(&alo, &lo_c),
                sh(&alo, &hi_c),
                sh(&ahi, &lo_c),
                sh(&ahi, &hi_c),
            ];
            let mut lo = cands[0];
            let mut hi = cands[0];
            for c in &cands[1..] {
                if slt(c, &lo) {
                    lo = *c;
                }
                if slt(&hi, c) {
                    hi = *c;
                }
            }
            let s = SRange::new(lo, hi).unwrap_or(SRange::full(w));
            let known = match a.known.bit(w.bits() - 1) {
                Some(false) => {
                    let lz = clamp(
                        a.known
                            .leading_known_zeros()
                            .saturating_add(cmin.min(wb - 1)),
                    );
                    KnownBits::from_masks(high_mask(w, lz), BitVec::zero(w))
                }
                Some(true) => {
                    let lo1 = leading_zeros(&bv_not(&a.known.known_one()));
                    let lo1 = clamp(lo1.saturating_add(cmin.min(wb - 1)));
                    KnownBits::from_masks(BitVec::zero(w), high_mask(w, lo1))
                }
                None => KnownBits::unknown(w),
            };
            Facts::reduce(known, URange::full(w), s).unwrap_or_else(|| Facts::top(w))
        }
        BinOp::RotL | BinOp::RotR => {
            // Rotation preserves the number of ones.
            let ones = a.known.known_one();
            let zeros = a.known.known_zero();
            if zeros.is_ones() || ones.is_ones() {
                Facts::from_known(a.known)
            } else {
                Facts::top(w)
            }
        }
        _ => Facts::top(w),
    }
}

fn bit_permute(op: BinOp, x: &Facts, m: &Facts) -> Facts {
    let w = x.width();
    if let Some(mask) = m.known.as_constant() {
        let (mut zero, mut one) = (Vec::new(), Vec::new());
        let wb = w.bits();
        let mut z = vec![0u64; 8];
        let mut o = vec![0u64; 8];
        let mut k: u16 = 0;
        for p in 0..wb {
            if mask.bit(p) != Some(true) {
                continue;
            }
            let (src, dst) = if op == BinOp::Pdep { (k, p) } else { (p, k) };
            match x.known.bit(src) {
                Some(true) => o[dst as usize / 64] |= 1 << (dst % 64),
                Some(false) => z[dst as usize / 64] |= 1 << (dst % 64),
                None => {}
            }
            k += 1;
        }
        // Result bits not written: pdep leaves zeros where the mask is 0; pext above popcount.
        for p in 0..wb {
            let written = if op == BinOp::Pdep {
                mask.bit(p) == Some(true)
            } else {
                p < k
            };
            if !written {
                z[p as usize / 64] |= 1 << (p % 64);
            }
        }
        zero.extend_from_slice(&z);
        one.extend_from_slice(&o);
        return Facts::from_known(KnownBits::from_masks(
            BitVec::wrapping_from_limbs(w, &zero),
            BitVec::wrapping_from_limbs(w, &one),
        ));
    }
    if x.known.known_zero().is_ones() {
        return Facts::constant(&BitVec::zero(w));
    }
    match op {
        BinOp::Pdep => {
            Facts::from_known(KnownBits::from_masks(m.known.known_zero(), BitVec::zero(w)))
        }
        _ => {
            let max_pop = u32::from(w.bits()) - count_ones(&m.known.known_zero());
            Facts::from_known(KnownBits::from_masks(
                bv_not(&low_mask(w, max_pop)),
                BitVec::zero(w),
            ))
        }
    }
}

/// Decides a comparison from facts, if they determine it.
pub(crate) fn decide(op: CmpOp, a: &Facts, b: &Facts) -> Option<bool> {
    let (au, bu, as_, bs) = (a.urange, b.urange, a.srange, b.srange);
    let disjoint =
        a.known.meet(&b.known).is_none() || au.meet(&bu).is_none() || as_.meet(&bs).is_none();
    let both_equal_constants = matches!(
        (a.as_constant(), b.as_constant()),
        (Some(x), Some(y)) if x == y
    );
    match op {
        CmpOp::Eq => {
            if disjoint {
                Some(false)
            } else if both_equal_constants {
                Some(true)
            } else {
                None
            }
        }
        CmpOp::Ne => decide(CmpOp::Eq, a, b).map(|v| !v),
        CmpOp::Ult => {
            if ult(&au.hi(), &bu.lo()) {
                Some(true)
            } else if ule(&bu.hi(), &au.lo()) {
                Some(false)
            } else {
                None
            }
        }
        CmpOp::Ule => {
            if ule(&au.hi(), &bu.lo()) {
                Some(true)
            } else if ult(&bu.hi(), &au.lo()) {
                Some(false)
            } else {
                None
            }
        }
        CmpOp::Slt => {
            if slt(&as_.hi(), &bs.lo()) {
                Some(true)
            } else if sle(&bs.hi(), &as_.lo()) {
                Some(false)
            } else {
                None
            }
        }
        CmpOp::Sle => {
            if sle(&as_.hi(), &bs.lo()) {
                Some(true)
            } else if slt(&bs.hi(), &as_.lo()) {
                Some(false)
            } else {
                None
            }
        }
    }
}

/// The facts of an operator's result.
pub(crate) fn transfer(op: &TOp, args: &[&Facts]) -> Facts {
    match *op {
        TOp::Const(v) => Facts::constant(&v),
        TOp::Top(w) => Facts::top(w),
        TOp::Un(u) => unary(u, args[0]),
        TOp::Bin(b) => binary(b, args[0], args[1]),
        TOp::Cmp(c) => match decide(c, args[0], args[1]) {
            Some(v) => Facts::constant(&BitVec::from_bool(v)),
            None => Facts::top(Width::W1),
        },
        TOp::Zext(to) => {
            let a = args[0];
            let z = |v: &BitVec| v.zext(to).unwrap_or(BitVec::zero(to));
            let known = KnownBits::from_masks(
                bv_or(
                    &z(&a.known.known_zero()),
                    &bv_not(&low_mask(to, u32::from(a.width().bits()))),
                ),
                z(&a.known.known_one()),
            );
            let u = strided(
                z(&a.urange.lo()),
                z(&a.urange.hi()),
                a.urange.stride(),
                URange::full(to),
            );
            let s = SRange::new(u.lo(), u.hi()).unwrap_or(SRange::full(to));
            Facts::reduce(known, u, s).unwrap_or_else(|| Facts::top(to))
        }
        TOp::Sext(to) => {
            let a = args[0];
            let s = |v: &BitVec| v.sext(to).unwrap_or(BitVec::zero(to));
            let known = KnownBits::from_masks(s(&a.known.known_zero()), s(&a.known.known_one()));
            let sr = SRange::new(s(&a.srange.lo()), s(&a.srange.hi())).unwrap_or(SRange::full(to));
            Facts::reduce(known, URange::full(to), sr).unwrap_or_else(|| Facts::top(to))
        }
        TOp::Extract { lo, width } => {
            let a = args[0];
            let x = |v: &BitVec| v.extract(lo, width).unwrap_or(BitVec::zero(width));
            let known = KnownBits::from_masks(x(&a.known.known_zero()), x(&a.known.known_one()));
            let mut f = Facts::from_known(known);
            // A low truncation of a value that already fits keeps its range.
            if lo == 0
                && bv_lshr(&a.urange.hi(), u32::from(width.bits())).is_zero()
                && let Some(u) =
                    URange::strided(x(&a.urange.lo()), x(&a.urange.hi()), a.urange.stride())
            {
                f = f.meet_urange(&u).unwrap_or(f);
            }
            f
        }
        TOp::Concat => {
            let (h, l) = (args[0], args[1]);
            let cat = |x: &BitVec, y: &BitVec| BitVec::concat(x, y).ok();
            let (Some(z), Some(o), Some(lo), Some(hi)) = (
                cat(&h.known.known_zero(), &l.known.known_zero()),
                cat(&h.known.known_one(), &l.known.known_one()),
                cat(&h.urange.lo(), &l.urange.lo()),
                cat(&h.urange.hi(), &l.urange.hi()),
            ) else {
                return Facts::top(Width::W1);
            };
            let w = z.width();
            // hi·2^L + lo steps by gcd(stride_hi·2^L, stride_lo).
            let (sh, sl) = (h.urange.stride(), l.urange.stride());
            let lw = u32::from(l.width().bits());
            let stride = if sl == 0 {
                stride_shl(sh, lw)
            } else {
                let shifted = u128::from(sh % sl) * u128::from(pow2_mod(lw, sl));
                gcd(sl, (shifted % u128::from(sl)) as u64)
            };
            let u = strided(lo, hi, stride, URange::full(w));
            Facts::reduce(KnownBits::from_masks(z, o), u, SRange::full(w))
                .unwrap_or_else(|| Facts::top(w))
        }
        TOp::Select => {
            let (c, t, f) = (args[0], args[1], args[2]);
            match c.as_constant() {
                Some(v) if v.is_zero() => *f,
                Some(_) => *t,
                None => t.hull(f),
            }
        }
    }
}
