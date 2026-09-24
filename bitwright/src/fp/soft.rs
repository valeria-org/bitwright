//! IEEE 754 arithmetic in software, exactly as the semantics chapter specifies it, generic over
//! the integer [`Frame`] it computes in.
//!
//! Every finite nonzero operand is decoded to `(−1)^s · m · 2^e` with `m` normalized to exactly
//! `p` bits. Each operation computes its exact result, or a truncation of it with at least two
//! bits below the result's last place and a sticky bit ORed into bit 0 ("jammed"), and [`round`]
//! turns that into an encoding. The jammed bit then lies at least two places below the rounding
//! position, so it decides inexactness and breaks would-be ties, and never makes one.

use core::cmp::Ordering;

use super::RoundingMode;
use super::frame::Frame;

/// A format's parameters, precomputed.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Fmt {
    /// Exponent bits.
    pub(crate) eb: u32,
    /// Precision (significand bits, the hidden one included).
    pub(crate) p: u32,
    /// Width: `eb + p`.
    pub(crate) w: u32,
    pub(crate) bias: i64,
    pub(crate) emin: i64,
}

impl Fmt {
    pub(crate) fn new(eb: u32, sb: u32) -> Fmt {
        let bias = (1i64 << (eb - 1)) - 1;
        Fmt {
            eb,
            p: sb,
            w: eb + sb,
            bias,
            emin: 1 - bias,
        }
    }

    /// The biased exponent of infinities and NaNs.
    fn e_max_field(&self) -> u64 {
        (1u64 << self.eb) - 1
    }
}

/// A decoded operand.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Val<S> {
    Nan,
    Inf(bool),
    Zero(bool),
    /// `(−1)^sign · sig · 2^exp`, `sig` exactly `p` bits.
    Fin {
        sign: bool,
        sig: S,
        exp: i64,
    },
}

fn field<S: Frame>(x: S, lo: u32, len: u32) -> u64 {
    let mut l = [0u64; 1];
    x.shr(lo).low(len).write_limbs(&mut l);
    l[0]
}

pub(crate) fn decode<S: Frame>(f: &Fmt, x: S) -> Val<S> {
    let sign = x.bit(f.w - 1);
    let e = field(x, f.p - 1, f.eb);
    let t = x.low(f.p - 1);
    if e == f.e_max_field() {
        if t.is_zero() {
            Val::Inf(sign)
        } else {
            Val::Nan
        }
    } else if e == 0 {
        if t.is_zero() {
            Val::Zero(sign)
        } else {
            let shift = f.p - t.bits();
            Val::Fin {
                sign,
                sig: t.shl(shift),
                exp: f.emin - i64::from(f.p) + 1 - i64::from(shift),
            }
        }
    } else {
        Val::Fin {
            sign,
            sig: t.add(S::pow2(f.p - 1)),
            exp: e as i64 - f.bias - i64::from(f.p) + 1,
        }
    }
}

fn pack<S: Frame>(f: &Fmt, sign: bool, e: u64, t: S) -> S {
    let s = if sign { S::pow2(f.w - 1) } else { S::zero() };
    s.add(S::from_u64(e).shl(f.p - 1)).add(t)
}

pub(crate) fn nan<S: Frame>(f: &Fmt) -> S {
    pack(f, false, f.e_max_field(), S::pow2(f.p - 2))
}

pub(crate) fn inf<S: Frame>(f: &Fmt, sign: bool) -> S {
    pack(f, sign, f.e_max_field(), S::zero())
}

pub(crate) fn zero<S: Frame>(f: &Fmt, sign: bool) -> S {
    pack(f, sign, 0, S::zero())
}

fn max_finite<S: Frame>(f: &Fmt, sign: bool) -> S {
    pack(f, sign, f.e_max_field() - 1, S::pow2(f.p - 1).sub(S::one()))
}

/// The sign bit.
pub(crate) fn sign_of<S: Frame>(f: &Fmt, x: S) -> bool {
    x.bit(f.w - 1)
}

/// `x` without its sign bit.
pub(crate) fn magnitude<S: Frame>(f: &Fmt, x: S) -> S {
    x.low(f.w - 1)
}

pub(crate) fn is_nan<S: Frame>(f: &Fmt, x: S) -> bool {
    magnitude(f, x) > inf(f, false)
}

fn overflow<S: Frame>(f: &Fmt, rm: RoundingMode, sign: bool) -> S {
    use RoundingMode::*;
    match (rm, sign) {
        (Rne | Rna, _) | (Rtp, false) | (Rtn, true) => inf(f, sign),
        (Rtz, _) | (Rtp, true) | (Rtn, false) => max_finite(f, sign),
    }
}

/// How `x mod 2^d` compares with half of `2^d` (`d ≥ 1`).
fn half_cmp<S: Frame>(x: S, d: u32) -> Ordering {
    if d > x.bits() {
        return Ordering::Less;
    }
    x.low(d).cmp(&S::pow2(d - 1))
}

/// Whether rounding the magnitude `hi + frac` (`frac` described by its comparison with one half
/// and whether it is nonzero) goes up to `hi + 1`.
fn round_up(rm: RoundingMode, sign: bool, hi_odd: bool, half: Ordering, inexact: bool) -> bool {
    use RoundingMode::*;
    match rm {
        Rne => half == Ordering::Greater || (half == Ordering::Equal && hi_odd),
        Rna => half != Ordering::Less,
        Rtz => false,
        Rtp => inexact && !sign,
        Rtn => inexact && sign,
    }
}

/// Rounds `(−1)^sign · (sig + δ) · 2^exp` to `f`, where `δ ∈ [0, 1)` is nonzero exactly when
/// `sticky`. Inexact inputs carry at least `p + 1` bits in `sig` (a jammed sticky bit in bit 0
/// counts as `sticky = false` with two or more bits beyond the precision). `sig` is nonzero.
pub(crate) fn round<S: Frame>(
    f: &Fmt,
    rm: RoundingMode,
    sign: bool,
    sig: S,
    exp: i64,
    sticky: bool,
) -> S {
    debug_assert!(!sig.is_zero());
    let p = i64::from(f.p);
    let e = i64::from(sig.bits()) - 1 + exp;
    let mut q = e.max(f.emin) - p + 1;
    let d = q - exp;
    let mut m = if d <= 0 {
        debug_assert!(!sticky, "an inexact input without a round bit");
        sig.shl((-d) as u32)
    } else {
        let d = u32::try_from(d).unwrap_or(u32::MAX);
        let hi = sig.shr(d);
        let half = match half_cmp(sig, d) {
            Ordering::Equal if sticky => Ordering::Greater,
            h => h,
        };
        let inexact = sticky || !sig.low(d).is_zero();
        if round_up(rm, sign, hi.bit(0), half, inexact) {
            hi.add(S::one())
        } else {
            hi
        }
    };
    if m.is_zero() {
        return zero(f, sign);
    }
    if m.bits() > f.p {
        // Rounded up to 2^p: the next binade's first value.
        m = m.shr(1);
        q += 1;
    }
    if m.bits() == f.p {
        let biased = q + p - 1 + f.bias;
        if biased >= f.e_max_field() as i64 {
            return overflow(f, rm, sign);
        }
        pack(f, sign, biased as u64, m.sub(S::pow2(f.p - 1)))
    } else {
        debug_assert_eq!(q, f.emin - p + 1);
        pack(f, sign, 0, m)
    }
}

/// The exact value `(−1)^sign · mag · 2^exp` (nonzero, representable) encoded.
fn exact<S: Frame>(f: &Fmt, sign: bool, mag: S, exp: i64) -> S {
    round(f, RoundingMode::Rne, sign, mag, exp, false)
}

/// `x + y` for finite nonzero operands (`Fin` fields), by the guard-and-jam alignment.
fn add_finite<S: Frame>(
    f: &Fmt,
    rm: RoundingMode,
    (sx, mx, ex): (bool, S, i64),
    (sy, my, ey): (bool, S, i64),
) -> S {
    let ((sx, mx, ex), (sy, my, ey)) = if ex >= ey {
        ((sx, mx, ex), (sy, my, ey))
    } else {
        ((sy, my, ey), (sx, mx, ex))
    };
    let x = mx.shl(3);
    let diff = u32::try_from(ex - ey).unwrap_or(u32::MAX);
    let y = my.shl(3).shr_jam(diff);
    let (sign, s) = if sx == sy {
        (sx, x.add(y))
    } else if x >= y {
        (sx, x.sub(y))
    } else {
        (sy, y.sub(x))
    };
    if s.is_zero() {
        return zero(f, rm == RoundingMode::Rtn);
    }
    round(f, rm, sign, s, ex - 3, false)
}

pub(crate) fn add<S: Frame>(f: &Fmt, rm: RoundingMode, a: S, b: S) -> S {
    match (decode(f, a), decode(f, b)) {
        (Val::Nan, _) | (_, Val::Nan) => nan(f),
        (Val::Inf(x), Val::Inf(y)) => {
            if x == y {
                inf(f, x)
            } else {
                nan(f)
            }
        }
        (Val::Inf(s), _) | (_, Val::Inf(s)) => inf(f, s),
        (Val::Zero(x), Val::Zero(y)) => {
            if x == y {
                zero(f, x)
            } else {
                zero(f, rm == RoundingMode::Rtn)
            }
        }
        (Val::Zero(_), _) => b,
        (_, Val::Zero(_)) => a,
        (
            Val::Fin {
                sign: sx,
                sig: mx,
                exp: ex,
            },
            Val::Fin {
                sign: sy,
                sig: my,
                exp: ey,
            },
        ) => add_finite(f, rm, (sx, mx, ex), (sy, my, ey)),
    }
}

/// `a` with its sign bit flipped.
pub(crate) fn neg<S: Frame>(f: &Fmt, a: S) -> S {
    let s = S::pow2(f.w - 1);
    if a.bit(f.w - 1) { a.sub(s) } else { a.add(s) }
}

pub(crate) fn sub<S: Frame>(f: &Fmt, rm: RoundingMode, a: S, b: S) -> S {
    add(f, rm, a, neg(f, b))
}

pub(crate) fn mul<S: Frame>(f: &Fmt, rm: RoundingMode, a: S, b: S) -> S {
    let sign = sign_of(f, a) != sign_of(f, b);
    match (decode(f, a), decode(f, b)) {
        (Val::Nan, _) | (_, Val::Nan) => nan(f),
        (Val::Inf(_), Val::Zero(_)) | (Val::Zero(_), Val::Inf(_)) => nan(f),
        (Val::Inf(_), _) | (_, Val::Inf(_)) => inf(f, sign),
        (Val::Zero(_), _) | (_, Val::Zero(_)) => zero(f, sign),
        (
            Val::Fin {
                sig: mx, exp: ex, ..
            },
            Val::Fin {
                sig: my, exp: ey, ..
            },
        ) => round(f, rm, sign, mx.mul(my), ex + ey, false),
    }
}

pub(crate) fn div<S: Frame>(f: &Fmt, rm: RoundingMode, a: S, b: S) -> S {
    let sign = sign_of(f, a) != sign_of(f, b);
    match (decode(f, a), decode(f, b)) {
        (Val::Nan, _) | (_, Val::Nan) => nan(f),
        (Val::Zero(_), Val::Zero(_)) | (Val::Inf(_), Val::Inf(_)) => nan(f),
        (Val::Inf(_), _) | (_, Val::Zero(_)) => inf(f, sign),
        (_, Val::Inf(_)) | (Val::Zero(_), _) => zero(f, sign),
        (
            Val::Fin {
                sig: mx, exp: ex, ..
            },
            Val::Fin {
                sig: my, exp: ey, ..
            },
        ) => {
            let (q, r) = mx.shl(f.p + 2).divrem(my);
            round(f, rm, sign, q, ex - ey - i64::from(f.p) - 2, !r.is_zero())
        }
    }
}

pub(crate) fn sqrt<S: Frame>(f: &Fmt, rm: RoundingMode, a: S) -> S {
    match decode(f, a) {
        Val::Nan => nan(f),
        Val::Zero(_) => a,
        Val::Inf(false) => a,
        Val::Inf(true) | Val::Fin { sign: true, .. } => nan(f),
        Val::Fin {
            sign: false,
            sig,
            exp,
        } => {
            // Make the exponent even, then scale so the root has at least p + 2 bits.
            let (m, e) = if exp.rem_euclid(2) == 1 {
                (sig.shl(1), exp - 1)
            } else {
                (sig, exp)
            };
            let k = (2 * f.p + 4).saturating_sub(m.bits()).div_ceil(2);
            let n = m.shl(2 * k);
            let r = n.isqrt();
            let sticky = r.mul(r) != n;
            round(f, rm, false, r, e / 2 - i64::from(k), sticky)
        }
    }
}

pub(crate) fn fma<S: Frame>(f: &Fmt, rm: RoundingMode, a: S, b: S, c: S) -> S {
    let sp = sign_of(f, a) != sign_of(f, b);
    let (va, vb, vc) = (decode(f, a), decode(f, b), decode(f, c));
    match (va, vb, vc) {
        (Val::Nan, _, _) | (_, Val::Nan, _) | (_, _, Val::Nan) => return nan(f),
        (Val::Inf(_), Val::Zero(_), _) | (Val::Zero(_), Val::Inf(_), _) => return nan(f),
        (Val::Inf(_), _, _) | (_, Val::Inf(_), _) => {
            return match vc {
                Val::Inf(sc) if sc != sp => nan(f),
                _ => inf(f, sp),
            };
        }
        (_, _, Val::Inf(_)) => return c,
        _ => {}
    }
    let (mp, ep) = match (va, vb) {
        (
            Val::Fin {
                sig: mx, exp: ex, ..
            },
            Val::Fin {
                sig: my, exp: ey, ..
            },
        ) => (mx.mul(my), ex + ey),
        // A zero product: exactly `c + (±0)`.
        _ => {
            return match vc {
                Val::Zero(sc) if sc == sp => zero(f, sc),
                Val::Zero(_) => zero(f, rm == RoundingMode::Rtn),
                _ => c,
            };
        }
    };
    let (sc, mc, ec) = match vc {
        Val::Fin { sign, sig, exp } => (sign, sig, exp),
        _ => return round(f, rm, sp, mp, ep, false),
    };
    // Align the addend and the product in one frame, the larger magnitude with three guard
    // bits, the smaller jammed below it when it reaches past them.
    let hp = i64::from(mp.bits()) - 1 + ep;
    let hc = i64::from(f.p) - 1 + ec;
    let ((sx, x, base), (sy, ym, ye)) = if hc > hp + 2 {
        ((sc, mc.shl(3), ec - 3), (sp, mp, ep))
    } else {
        ((sp, mp.shl(3), ep - 3), (sc, mc, ec))
    };
    let y = if ye >= base {
        ym.shl(u32::try_from(ye - base).expect("aligned within the frame"))
    } else {
        ym.shr_jam(u32::try_from(base - ye).unwrap_or(u32::MAX))
    };
    let (sign, s) = if sx == sy {
        (sx, x.add(y))
    } else if x >= y {
        (sx, x.sub(y))
    } else {
        (sy, y.sub(x))
    };
    if s.is_zero() {
        return zero(f, rm == RoundingMode::Rtn);
    }
    round(f, rm, sign, s, base, false)
}

/// `2^d mod m` (`m ≥ 2`).
fn pow2_mod<S: Frame>(d: u64, m: S) -> S {
    let mut result = S::one().divrem(m).1;
    let mut base = S::from_u64(2).divrem(m).1;
    let mut d = d;
    while d != 0 {
        if d & 1 == 1 {
            result = result.mul_mod(base, m);
        }
        base = base.mul_mod(base, m);
        d >>= 1;
    }
    result
}

pub(crate) fn rem<S: Frame>(f: &Fmt, a: S, b: S) -> S {
    let (sx, mx, ex, my, ey) = match (decode(f, a), decode(f, b)) {
        (Val::Nan, _) | (_, Val::Nan) | (Val::Inf(_), _) | (_, Val::Zero(_)) => return nan(f),
        (Val::Zero(_), _) | (_, Val::Inf(_)) => return a,
        (
            Val::Fin {
                sign,
                sig: mx,
                exp: ex,
            },
            Val::Fin {
                sig: my, exp: ey, ..
            },
        ) => (sign, mx, ex, my, ey),
    };
    if ex < ey {
        // |a| < |b|: the quotient rounds to 0 or ±1.
        if ey - ex >= 2 {
            return a;
        }
        // ey = ex + 1: compare 2|a| = mx·2^ey with |b| = my·2^ey.
        return match mx.cmp(&my) {
            Ordering::Less | Ordering::Equal => a,
            Ordering::Greater => exact(f, !sx, my.shl(1).sub(mx), ex),
        };
    }
    // (mx · 2^d) mod 2my gives the remainder of the truncated quotient and its parity.
    let d = (ex - ey) as u64;
    let two_my = my.shl(1);
    let r2 = mx.mul_mod(pow2_mod(d, two_my), two_my);
    let (r, odd) = if r2 >= my {
        (r2.sub(my), true)
    } else {
        (r2, false)
    };
    let twice = r.shl(1);
    let down = match twice.cmp(&my) {
        Ordering::Less => false,
        Ordering::Greater => true,
        Ordering::Equal => odd,
    };
    let (sign, mag) = if down { (!sx, my.sub(r)) } else { (sx, r) };
    if mag.is_zero() {
        return zero(f, sx);
    }
    exact(f, sign, mag, ey)
}

/// The integer `(−1)^sign · sig · 2^exp` rounds to by `rm` (`exp < 0`), as a magnitude.
fn integral<S: Frame>(rm: RoundingMode, sign: bool, sig: S, exp: i64) -> S {
    let d = u32::try_from(-exp).unwrap_or(u32::MAX);
    let hi = sig.shr(d);
    let inexact = !sig.low(d).is_zero();
    if round_up(rm, sign, hi.bit(0), half_cmp(sig, d), inexact) {
        hi.add(S::one())
    } else {
        hi
    }
}

pub(crate) fn round_to_integral<S: Frame>(f: &Fmt, rm: RoundingMode, a: S) -> S {
    match decode(f, a) {
        Val::Nan => nan(f),
        Val::Inf(_) | Val::Zero(_) => a,
        Val::Fin { exp, .. } if exp >= 0 => a,
        Val::Fin { sign, sig, exp } => {
            let k = integral(rm, sign, sig, exp);
            if k.is_zero() {
                zero(f, sign)
            } else {
                round(f, rm, sign, k, 0, false)
            }
        }
    }
}

/// `−0 < +0` ordering of two non-NaN encodings: sign-magnitude comparison.
fn total_cmp<S: Frame>(f: &Fmt, a: S, b: S) -> Ordering {
    let (sa, sb) = (sign_of(f, a), sign_of(f, b));
    let (ma, mb) = (magnitude(f, a), magnitude(f, b));
    match (sa, sb) {
        (false, false) => ma.cmp(&mb),
        (true, true) => mb.cmp(&ma),
        (false, true) => Ordering::Greater,
        (true, false) => Ordering::Less,
    }
}

/// IEEE comparison of two non-NaN encodings (`+0 = −0`).
fn value_cmp<S: Frame>(f: &Fmt, a: S, b: S) -> Ordering {
    if magnitude(f, a).is_zero() && magnitude(f, b).is_zero() {
        Ordering::Equal
    } else {
        total_cmp(f, a, b)
    }
}

pub(crate) fn min<S: Frame>(f: &Fmt, a: S, b: S) -> S {
    match (is_nan(f, a), is_nan(f, b)) {
        (true, true) => nan(f),
        (true, false) => b,
        (false, true) => a,
        (false, false) => {
            if total_cmp(f, b, a) == Ordering::Less {
                b
            } else {
                a
            }
        }
    }
}

pub(crate) fn max<S: Frame>(f: &Fmt, a: S, b: S) -> S {
    match (is_nan(f, a), is_nan(f, b)) {
        (true, true) => nan(f),
        (true, false) => b,
        (false, true) => a,
        (false, false) => {
            if total_cmp(f, b, a) == Ordering::Greater {
                b
            } else {
                a
            }
        }
    }
}

/// `eq`, `lt` and `le`: `None` when unordered (a NaN operand).
pub(crate) fn compare<S: Frame>(f: &Fmt, a: S, b: S) -> Option<Ordering> {
    if is_nan(f, a) || is_nan(f, b) {
        None
    } else {
        Some(value_cmp(f, a, b))
    }
}

/// Converts between formats (`from` and `to` may be the same).
pub(crate) fn convert<S: Frame>(from: &Fmt, to: &Fmt, rm: RoundingMode, a: S) -> S {
    match decode(from, a) {
        Val::Nan => nan(to),
        Val::Inf(s) => inf(to, s),
        Val::Zero(s) => zero(to, s),
        Val::Fin { sign, sig, exp } => round(to, rm, sign, sig, exp, false),
    }
}

/// The integer `a` converts to by `rm`: its sign and magnitude, or `Huge` when the magnitude
/// reaches `2^cap_bits` (the frame must hold `cap_bits` bits).
pub(crate) enum IntVal<S> {
    Nan,
    PosInf,
    NegInf,
    /// `(−1)^sign · mag`, `mag` below `2^cap_bits`.
    Int {
        sign: bool,
        mag: S,
    },
    /// A magnitude of at least `2^cap_bits`.
    Huge {
        sign: bool,
    },
}

pub(crate) fn to_integer<S: Frame>(f: &Fmt, rm: RoundingMode, a: S, cap_bits: u32) -> IntVal<S> {
    match decode(f, a) {
        Val::Nan => IntVal::Nan,
        Val::Inf(false) => IntVal::PosInf,
        Val::Inf(true) => IntVal::NegInf,
        Val::Zero(s) => IntVal::Int {
            sign: s,
            mag: S::zero(),
        },
        Val::Fin { sign, sig, exp } => {
            if exp >= 0 {
                if i64::from(sig.bits()) + exp > i64::from(cap_bits) {
                    return IntVal::Huge { sign };
                }
                IntVal::Int {
                    sign,
                    mag: sig.shl(exp as u32),
                }
            } else {
                let k = integral(rm, sign, sig, exp);
                if k.bits() > cap_bits {
                    IntVal::Huge { sign }
                } else {
                    IntVal::Int { sign, mag: k }
                }
            }
        }
    }
}
