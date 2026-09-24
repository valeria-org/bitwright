//! Exhaustive checks on tiny formats against a brute-force oracle.
//!
//! The brute force never computes a quantum or an exponent. It lists every finite value of the
//! format as an integer multiple of the smallest subnormal (`u128`), writes each operation's
//! exact result as a comparison function (`i128`/`u128` cross-multiplication, or squares for
//! square roots), and rounds IEEE's way: find the two neighbours of `|r|` among the listed values
//! plus `2^(emax + 1)` (the next value with an unbounded exponent), pick one by the mode (the
//! even neighbour on a tie), and treat picking `2^(emax + 1)` or lying beyond it as overflow.

use super::*;
use std::cmp::Ordering;

/// A tiny format's value of an encoding: NaN, `±∞`, or `(-1)^neg · units · 2^qmin`
/// (`units = 0` is a zero).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Tv {
    Nan,
    Inf(bool),
    Fin(bool, u128),
}

/// Every value of a tiny format, as integers in units of `2^qmin`.
struct Tiny {
    f: Format,
    w: u32,
    p: u32,
    eb: u32,
    /// `emin - p + 1`, negative for every format.
    qmin: i32,
    /// The non-negative finite values in increasing order, with their encodings.
    pos: Vec<(u128, u128)>,
    /// `2^(emax + 1)` in units.
    top: u128,
}

impl Tiny {
    fn new(f: Format) -> Tiny {
        let (eb, p) = (u32::from(f.eb), u32::from(f.sb));
        let bias = (1i32 << (eb - 1)) - 1;
        let emin = 1 - bias;
        let qmin = emin - p as i32 + 1;
        let mut t = Tiny {
            f,
            w: eb + p,
            p,
            eb,
            qmin,
            pos: Vec::new(),
            top: 1u128 << (bias + 1 - qmin),
        };
        for bits in 0..(1u128 << (t.w - 1)) {
            if let Tv::Fin(_, u) = t.decode(bits) {
                t.pos.push((u, bits));
            }
        }
        t.pos.sort_unstable();
        t
    }

    fn count(&self) -> u128 {
        1u128 << self.w
    }

    fn decode(&self, x: u128) -> Tv {
        let s = (x >> (self.w - 1)) & 1 == 1;
        let e = (x >> (self.p - 1)) & ((1 << self.eb) - 1);
        let t = x & ((1 << (self.p - 1)) - 1);
        if e == (1 << self.eb) - 1 {
            if t == 0 { Tv::Inf(s) } else { Tv::Nan }
        } else if e == 0 {
            Tv::Fin(s, t)
        } else {
            // (2^(p-1) + T) · 2^(E - bias - p + 1) = (2^(p-1) + T) · 2^(E - 1) units.
            Tv::Fin(s, ((1 << (self.p - 1)) + t) << (e - 1))
        }
    }

    fn signed(&self, neg: bool, x: u128) -> u128 {
        (u128::from(neg) << (self.w - 1)) | x
    }

    fn nan(&self) -> u128 {
        (((1 << self.eb) - 1) << (self.p - 1)) | (1 << (self.p - 2))
    }

    fn inf(&self, neg: bool) -> u128 {
        self.signed(neg, ((1 << self.eb) - 1) << (self.p - 1))
    }

    fn zero(&self, neg: bool) -> u128 {
        self.signed(neg, 0)
    }

    fn max_finite(&self, neg: bool) -> u128 {
        self.signed(neg, self.pos.last().unwrap().1)
    }

    /// The encoding of an exactly representable finite value.
    fn exact(&self, neg: bool, units: u128) -> u128 {
        let i = self
            .pos
            .binary_search_by_key(&units, |&(u, _)| u)
            .unwrap_or_else(|_| panic!("{units} units not representable in {:?}", self.f));
        self.signed(neg, self.pos[i].1)
    }

    fn overflow(&self, rm: Rm, neg: bool) -> u128 {
        match rm {
            Rm::Rne | Rm::Rna => self.inf(neg),
            Rm::Rtz => self.max_finite(neg),
            Rm::Rtp => {
                if neg {
                    self.max_finite(true)
                } else {
                    self.inf(false)
                }
            }
            Rm::Rtn => {
                if neg {
                    self.inf(true)
                } else {
                    self.max_finite(false)
                }
            }
        }
    }

    /// Rounds a nonzero real of sign `neg` whose magnitude `m` is known through `half(x)`, the
    /// order of `x / 2` against `m` (for `x` in units).
    fn round(&self, rm: Rm, neg: bool, half: impl Fn(u128) -> Ordering) -> u128 {
        let n = self.pos.len() + 1; // candidates: the listed values, then `top`
        let cand = |i: usize| {
            if i < self.pos.len() {
                self.pos[i].0
            } else {
                self.top
            }
        };
        let at_or_above = |i: usize| half(2 * cand(i)) != Ordering::Less;
        // The first candidate >= m, by bisection.
        let (mut lo, mut hi) = (0, n);
        while lo < hi {
            let mid = (lo + hi) / 2;
            if at_or_above(mid) {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }
        if lo == n {
            return self.overflow(rm, neg); // beyond 2^(emax + 1)
        }
        let chosen = if half(2 * cand(lo)) == Ordering::Equal {
            lo
        } else {
            let (below, above) = (lo - 1, lo); // cand(0) = 0 < m
            let even_below = self.pos[below].1 & 1 == 0;
            let midpoint = half(cand(below) + cand(above));
            match rm {
                Rm::Rne => match midpoint {
                    Ordering::Greater => below,
                    Ordering::Less => above,
                    Ordering::Equal if even_below => below,
                    Ordering::Equal => above,
                },
                Rm::Rna => match midpoint {
                    Ordering::Greater => below,
                    _ => above,
                },
                Rm::Rtz => below,
                Rm::Rtp if neg => below,
                Rm::Rtp => above,
                Rm::Rtn if neg => above,
                Rm::Rtn => below,
            }
        };
        if chosen == self.pos.len() {
            return self.overflow(rm, neg);
        }
        self.signed(neg, self.pos[chosen].1)
    }

    /// `2^-qmin`: one unit is `1 / den1()` in value.
    fn den1(&self) -> u128 {
        1u128 << (-self.qmin)
    }
}

/// `half` for the magnitude `num / den` units.
fn ratio(num: u128, den: u128) -> impl Fn(u128) -> Ordering {
    move |x| {
        x.checked_mul(den)
            .expect("no overflow")
            .cmp(&num.checked_mul(2).expect("no overflow"))
    }
}

/// `half` for the magnitude `sqrt(sq)` units.
fn root(sq: u128) -> impl Fn(u128) -> Ordering {
    move |x| {
        x.checked_mul(x)
            .expect("no overflow")
            .cmp(&sq.checked_mul(4).expect("no overflow"))
    }
}

fn sgn(neg: bool, x: u128) -> i128 {
    let x = i128::try_from(x).expect("fits");
    if neg { -x } else { x }
}

/// The zero of an exact zero sum: `+0`, or `-0` under `Rtn`.
fn zero_rule(t: &Tiny, rm: Rm) -> u128 {
    t.zero(rm == Rm::Rtn)
}

fn bf_add(t: &Tiny, rm: Rm, a: u128, b: u128) -> u128 {
    match (t.decode(a), t.decode(b)) {
        (Tv::Nan, _) | (_, Tv::Nan) => t.nan(),
        (Tv::Inf(s), Tv::Inf(u)) if s != u => t.nan(),
        (Tv::Inf(s), _) | (_, Tv::Inf(s)) => t.inf(s),
        (Tv::Fin(s, x), Tv::Fin(u, y)) => {
            let sum = sgn(s, x) + sgn(u, y);
            if sum != 0 {
                t.round(rm, sum < 0, ratio(sum.unsigned_abs(), 1))
            } else if x == 0 && y == 0 && s == u {
                t.zero(s)
            } else {
                zero_rule(t, rm)
            }
        }
    }
}

fn bf_mul(t: &Tiny, rm: Rm, a: u128, b: u128) -> u128 {
    let s = ((a ^ b) >> (t.w - 1)) & 1 == 1;
    match (t.decode(a), t.decode(b)) {
        (Tv::Nan, _) | (_, Tv::Nan) => t.nan(),
        (Tv::Inf(_), Tv::Fin(_, 0)) | (Tv::Fin(_, 0), Tv::Inf(_)) => t.nan(),
        (Tv::Inf(_), _) | (_, Tv::Inf(_)) => t.inf(s),
        (Tv::Fin(_, 0), _) | (_, Tv::Fin(_, 0)) => t.zero(s),
        // x · y · 2^(2 qmin) = (x · y / 2^-qmin) units.
        (Tv::Fin(_, x), Tv::Fin(_, y)) => t.round(rm, s, ratio(x * y, t.den1())),
    }
}

fn bf_div(t: &Tiny, rm: Rm, a: u128, b: u128) -> u128 {
    let s = ((a ^ b) >> (t.w - 1)) & 1 == 1;
    match (t.decode(a), t.decode(b)) {
        (Tv::Nan, _) | (_, Tv::Nan) => t.nan(),
        (Tv::Fin(_, 0), Tv::Fin(_, 0)) | (Tv::Inf(_), Tv::Inf(_)) => t.nan(),
        (Tv::Inf(_), _) => t.inf(s),
        (_, Tv::Inf(_)) => t.zero(s),
        (Tv::Fin(_, _), Tv::Fin(_, 0)) => t.inf(s),
        (Tv::Fin(_, 0), _) => t.zero(s),
        // (x / y) in value = (x · 2^-qmin / y) units.
        (Tv::Fin(_, x), Tv::Fin(_, y)) => t.round(rm, s, ratio(x * t.den1(), y)),
    }
}

fn bf_fma(t: &Tiny, rm: Rm, a: u128, b: u128, c: u128) -> u128 {
    let sp = ((a ^ b) >> (t.w - 1)) & 1 == 1;
    match (t.decode(a), t.decode(b), t.decode(c)) {
        (Tv::Nan, _, _) | (_, Tv::Nan, _) | (_, _, Tv::Nan) => t.nan(),
        (Tv::Inf(_), Tv::Fin(_, 0), _) | (Tv::Fin(_, 0), Tv::Inf(_), _) => t.nan(),
        (Tv::Inf(_), _, Tv::Inf(sc)) | (_, Tv::Inf(_), Tv::Inf(sc)) if sc != sp => t.nan(),
        (Tv::Inf(_), _, _) | (_, Tv::Inf(_), _) => t.inf(sp),
        (_, _, Tv::Inf(_)) => c,
        (Tv::Fin(_, x), Tv::Fin(_, y), Tv::Fin(sc, z)) => {
            // In units of 2^(2 qmin): the product x·y and the addend z · 2^-qmin.
            let sum = sgn(sp, x * y) + sgn(sc, z * t.den1());
            if sum != 0 {
                t.round(rm, sum < 0, ratio(sum.unsigned_abs(), t.den1()))
            } else if x * y == 0 && z == 0 && sc == sp {
                t.zero(sp)
            } else {
                zero_rule(t, rm)
            }
        }
    }
}

fn bf_sqrt(t: &Tiny, rm: Rm, a: u128) -> u128 {
    match t.decode(a) {
        Tv::Nan | Tv::Inf(true) => t.nan(),
        Tv::Inf(false) => a,
        Tv::Fin(s, 0) => t.zero(s),
        Tv::Fin(true, _) => t.nan(),
        // sqrt(x · 2^qmin) = sqrt(x · 2^-qmin) units.
        Tv::Fin(false, x) => t.round(rm, false, root(x * t.den1())),
    }
}

fn bf_rem(t: &Tiny, a: u128, b: u128) -> u128 {
    match (t.decode(a), t.decode(b)) {
        (Tv::Nan, _) | (_, Tv::Nan) | (Tv::Inf(_), _) | (_, Tv::Fin(_, 0)) => t.nan(),
        (_, Tv::Inf(_)) => a,
        (Tv::Fin(sa, x), Tv::Fin(_, y)) => {
            // n = the integer nearest x / y, ties to even (magnitudes; the sign cancels out).
            let (q, r) = (x / y, x % y);
            let n = if 2 * r > y || (2 * r == y && q % 2 == 1) {
                q + 1
            } else {
                q
            };
            let diff = sgn(false, x) - sgn(false, n * y);
            if diff == 0 {
                t.zero(sa)
            } else {
                t.exact(sa ^ (diff < 0), diff.unsigned_abs())
            }
        }
    }
}

/// The integer obtained from `(-1)^neg · x` units by the mode, by signed floor division.
fn bf_integer(t: &Tiny, rm: Rm, neg: bool, x: u128) -> i128 {
    let d = sgn(false, t.den1());
    let v = sgn(neg, x); // the value is v / d
    let floor = v.div_euclid(d);
    let frac = v - floor * d; // in [0, d)
    let ceil = if frac == 0 { floor } else { floor + 1 };
    match rm {
        Rm::Rtn => floor,
        Rm::Rtp => ceil,
        Rm::Rtz => {
            if v >= 0 {
                floor
            } else {
                ceil
            }
        }
        Rm::Rne | Rm::Rna => match (2 * frac).cmp(&d) {
            Ordering::Less => floor,
            Ordering::Greater => floor + 1,
            Ordering::Equal if rm == Rm::Rne => {
                if floor.rem_euclid(2) == 0 {
                    floor
                } else {
                    floor + 1
                }
            }
            Ordering::Equal => {
                if v > 0 {
                    floor + 1
                } else {
                    floor
                }
            }
        },
    }
}

fn bf_round_to_integral(t: &Tiny, rm: Rm, a: u128) -> u128 {
    match t.decode(a) {
        Tv::Nan => t.nan(),
        Tv::Inf(_) | Tv::Fin(_, 0) => a,
        Tv::Fin(s, x) => {
            let k = bf_integer(t, rm, s, x);
            if k == 0 {
                t.zero(s)
            } else {
                t.round(rm, k < 0, ratio(k.unsigned_abs() * t.den1(), 1))
            }
        }
    }
}

/// `to_sint`/`to_uint` of width `n`, as the `n`-bit pattern.
fn bf_to_int(t: &Tiny, rm: Rm, a: u128, n: u32, signed: bool) -> u128 {
    let (lo, hi) = if signed {
        (-(1i128 << (n - 1)), (1i128 << (n - 1)) - 1)
    } else {
        (0, (1i128 << n) - 1)
    };
    let k = match t.decode(a) {
        Tv::Nan => 0,
        Tv::Inf(false) => hi,
        Tv::Inf(true) => lo,
        Tv::Fin(s, x) => bf_integer(t, rm, s, x).clamp(lo, hi),
    };
    (k as u128) & ((1u128 << n) - 1)
}

/// The value's order key: numeric, with `-0 < +0`, and the numeric value alone.
fn key(t: &Tiny, a: u128) -> Option<(i128, bool)> {
    match t.decode(a) {
        Tv::Nan => None,
        Tv::Inf(s) => Some((if s { i128::MIN } else { i128::MAX }, !s)),
        Tv::Fin(s, x) => Some((sgn(s, x), !s)),
    }
}

fn bf_min_max(t: &Tiny, a: u128, b: u128, want_max: bool) -> u128 {
    match (key(t, a), key(t, b)) {
        (None, None) => t.nan(),
        (None, _) => b,
        (_, None) => a,
        (Some(ka), Some(kb)) => {
            if (want_max && kb > ka) || (!want_max && kb < ka) {
                b
            } else {
                a
            }
        }
    }
}

fn check_binary_ops(f: Format) {
    let t = Tiny::new(f);
    let w = f.width();
    for a in 0..t.count() {
        let x = bw(w, a);
        for b in 0..t.count() {
            let y = bw(w, b);
            for rm in Rm::ALL {
                let ctx = || format!("{f:?} {rm:?} a={a:#x} b={b:#x}");
                assert_eq!(
                    val(&add(f, rm, &x, &y)),
                    bf_add(&t, rm, a, b),
                    "add {}",
                    ctx()
                );
                let nb = b ^ (1 << (w - 1));
                assert_eq!(
                    val(&sub(f, rm, &x, &y)),
                    bf_add(&t, rm, a, nb),
                    "sub {}",
                    ctx()
                );
                assert_eq!(
                    val(&mul(f, rm, &x, &y)),
                    bf_mul(&t, rm, a, b),
                    "mul {}",
                    ctx()
                );
                assert_eq!(
                    val(&div(f, rm, &x, &y)),
                    bf_div(&t, rm, a, b),
                    "div {}",
                    ctx()
                );
            }
            assert_eq!(
                val(&rem(f, &x, &y)),
                bf_rem(&t, a, b),
                "rem {f:?} {a:#x} {b:#x}"
            );
            assert_eq!(
                val(&min(f, &x, &y)),
                bf_min_max(&t, a, b, false),
                "min {a:#x} {b:#x}"
            );
            assert_eq!(
                val(&max(f, &x, &y)),
                bf_min_max(&t, a, b, true),
                "max {a:#x} {b:#x}"
            );
            let (ka, kb) = (key(&t, a), key(&t, b));
            let (va, vb) = (ka.map(|k| k.0), kb.map(|k| k.0));
            let both = va.is_some() && vb.is_some();
            assert_eq!(eq(f, &x, &y), both && va == vb, "eq {f:?} {a:#x} {b:#x}");
            assert_eq!(lt(f, &x, &y), both && va < vb, "lt {f:?} {a:#x} {b:#x}");
            assert_eq!(le(f, &x, &y), both && va <= vb, "le {f:?} {a:#x} {b:#x}");
        }
    }
}

fn check_unary_ops(f: Format) {
    let t = Tiny::new(f);
    let w = f.width();
    for a in 0..t.count() {
        let x = bw(w, a);
        for rm in Rm::ALL {
            assert_eq!(
                val(&sqrt(f, rm, &x)),
                bf_sqrt(&t, rm, a),
                "sqrt {f:?} {rm:?} {a:#x}"
            );
            assert_eq!(
                val(&round_to_integral(f, rm, &x)),
                bf_round_to_integral(&t, rm, a),
                "round_to_integral {f:?} {rm:?} {a:#x}"
            );
            for n in 1..=12u16 {
                for signed in [false, true] {
                    let got = if signed {
                        to_sint(f, rm, &x, n)
                    } else {
                        to_uint(f, rm, &x, n)
                    };
                    assert_eq!(
                        val(&got),
                        bf_to_int(&t, rm, a, u32::from(n), signed),
                        "to_int {f:?} {rm:?} {a:#x} n={n} signed={signed}"
                    );
                }
            }
        }
    }
}

/// Runs `check` on each format in its own thread.
fn per_format(formats: impl IntoIterator<Item = Format>, check: fn(Format)) {
    std::thread::scope(|scope| {
        for f in formats {
            scope.spawn(move || check(f));
        }
    });
}

#[test]
fn tiny_binary_ops_exhaustive() {
    per_format(TINY, check_binary_ops);
}

#[test]
fn tiny_unary_ops_exhaustive() {
    for f in TINY {
        check_unary_ops(f);
    }
}

#[test]
fn tiny_fma_exhaustive() {
    per_format(TINY.into_iter().filter(|f| f.width() <= 6), check_fma);
}

fn check_fma(f: Format) {
    let t = Tiny::new(f);
    let w = f.width();
    for a in 0..t.count() {
        for b in 0..t.count() {
            for c in 0..t.count() {
                let (x, y, z) = (bw(w, a), bw(w, b), bw(w, c));
                for rm in Rm::ALL {
                    assert_eq!(
                        val(&fma(f, rm, &x, &y, &z)),
                        bf_fma(&t, rm, a, b, c),
                        "fma {f:?} {rm:?} {a:#x} {b:#x} {c:#x}"
                    );
                }
            }
        }
    }
}

#[test]
fn tiny_fma_sampled_width_7_and_8() {
    let mut rng = Rng(0x5eed_0007);
    for f in TINY.into_iter().filter(|f| f.width() >= 7) {
        let t = Tiny::new(f);
        let w = f.width();
        for _ in 0..40_000 {
            let [a, b, c] = [0; 3].map(|_| u128::from(rng.next()) % t.count());
            let (x, y, z) = (bw(w, a), bw(w, b), bw(w, c));
            for rm in Rm::ALL {
                assert_eq!(
                    val(&fma(f, rm, &x, &y, &z)),
                    bf_fma(&t, rm, a, b, c),
                    "fma {f:?} {rm:?} {a:#x} {b:#x} {c:#x}"
                );
            }
        }
    }
}

#[test]
fn tiny_conversions_exhaustive() {
    for from in TINY {
        let src = Tiny::new(from);
        for to in TINY {
            let dst = Tiny::new(to);
            // x units of 2^qmin_src = x · 2^(qmin_src - qmin_dst) units of the destination.
            let shift = src.qmin - dst.qmin;
            for a in 0..src.count() {
                let x = bw(from.width(), a);
                for rm in Rm::ALL {
                    let want = match src.decode(a) {
                        Tv::Nan => dst.nan(),
                        Tv::Inf(s) => dst.inf(s),
                        Tv::Fin(s, 0) => dst.zero(s),
                        Tv::Fin(s, u) if shift >= 0 => dst.round(rm, s, ratio(u << shift, 1)),
                        Tv::Fin(s, u) => dst.round(rm, s, ratio(u, 1 << -shift)),
                    };
                    assert_eq!(
                        val(&to_fp(from, to, rm, &x)),
                        want,
                        "to_fp {from:?} -> {to:?} {rm:?} {a:#x}"
                    );
                }
            }
        }
        // Integers of every width up to 9 bits, both signednesses.
        for n in 1..=9u16 {
            for v in 0..(1u128 << n) {
                let x = bw(n, v);
                let sv = if v >> (n - 1) == 1 {
                    v as i128 - (1i128 << n)
                } else {
                    v as i128
                };
                for rm in Rm::ALL {
                    for (k, got) in [
                        (v as i128, from_uint(from, rm, &x)),
                        (sv, from_sint(from, rm, &x)),
                    ] {
                        let want = if k == 0 {
                            src.zero(false)
                        } else {
                            src.round(rm, k < 0, ratio(k.unsigned_abs() * src.den1(), 1))
                        };
                        assert_eq!(val(&got), want, "from_int {from:?} {rm:?} n={n} v={v:#x}");
                    }
                }
            }
        }
    }
}
