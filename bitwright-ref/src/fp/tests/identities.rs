//! Internal consistency: identities of the contract, exhaustively on tiny formats, and the
//! private big-natural arithmetic against native `u128` arithmetic.

use super::super::nat::{Nat, cmp_scaled};
use super::*;
use std::cmp::Ordering;

/// Runs `check` on each format in its own thread.
fn per_format(formats: &[Format], check: fn(Format)) {
    std::thread::scope(|scope| {
        for &f in formats {
            scope.spawn(move || check(f));
        }
    });
}

fn tiny_up_to(width: u16) -> Vec<Format> {
    TINY.into_iter().filter(|f| f.width() <= width).collect()
}

/// The encoding of 1.0: biased exponent `bias`, trailing significand 0.
fn one(f: Format) -> Bits {
    enc(f, false, (1u128 << (f.eb - 1)) - 1, 0)
}

fn identities(f: Format) {
    let w = f.width();
    let nan = canonical_nan(f);
    let (one, nz) = (one(f), enc(f, true, 0, 0));
    let vals: Vec<Bits> = (0..1u128 << w).map(|x| bw(w, x)).collect();
    let canonical = |x: &Bits, what: &str| {
        assert!(
            !is_nan(f, x) || *x == nan,
            "{what}: non-canonical NaN {x:?}"
        );
    };
    for a in &vals {
        let classes = [
            is_nan(f, a),
            is_infinite(f, a),
            is_zero(f, a),
            is_normal(f, a),
            is_subnormal(f, a),
        ];
        assert_eq!(classes.iter().filter(|&&c| c).count(), 1, "{f:?} {a:?}");
        assert_eq!(neg(f, &neg(f, a)), *a);
        assert_eq!(abs(f, &neg(f, a)), abs(f, a));
        assert_eq!(copysign(f, a, a), *a);
        assert_eq!(copysign(f, &abs(f, a), &nz), neg(f, &abs(f, a)));
        if !is_nan(f, a) {
            assert_eq!(is_negative(f, &neg(f, a)), is_positive(f, a));
            assert!(eq(f, a, a) && le(f, a, a) && !lt(f, a, a));
        }
        for rm in Rm::ALL {
            let r = round_to_integral(f, rm, a);
            canonical(&r, "round_to_integral");
            assert_eq!(
                round_to_integral(f, rm, &r),
                r,
                "rti idempotent {f:?} {a:?}"
            );
            canonical(&sqrt(f, rm, a), "sqrt");
            if !is_nan(f, a) {
                assert_eq!(mul(f, rm, a, &one), *a, "a * 1 {f:?} {rm:?} {a:?}");
                assert_eq!(div(f, rm, a, &one), *a, "a / 1 {f:?} {rm:?} {a:?}");
                // a + (-0) = a, except +0 + -0 = -0 under Rtn.
                if !(rm == Rm::Rtn && is_zero(f, a)) {
                    assert_eq!(add(f, rm, a, &nz), *a, "a + -0 {f:?} {rm:?} {a:?}");
                }
            }
        }
        for b in &vals {
            for rm in Rm::ALL {
                let s = add(f, rm, a, b);
                canonical(&s, "add");
                assert_eq!(s, add(f, rm, b, a), "add commutes {f:?} {rm:?} {a:?} {b:?}");
                assert_eq!(sub(f, rm, a, b), add(f, rm, a, &neg(f, b)));
                // a · 1 is exact, and its zero has a's sign: fma(a, 1, b) is a + b.
                assert_eq!(
                    fma(f, rm, a, &one, b),
                    s,
                    "fma(a, 1, b) {f:?} {rm:?} {a:?} {b:?}"
                );
                let p = mul(f, rm, a, b);
                canonical(&p, "mul");
                assert_eq!(p, mul(f, rm, b, a), "mul commutes {f:?} {rm:?} {a:?} {b:?}");
                canonical(&div(f, rm, a, b), "div");
            }
            canonical(&rem(f, a, b), "rem");
            let (lo, hi) = (min(f, a, b), max(f, a, b));
            canonical(&lo, "min");
            canonical(&hi, "max");
            assert_eq!(lo, min(f, b, a), "min commutes {f:?} {a:?} {b:?}");
            assert_eq!(hi, max(f, b, a), "max commutes {f:?} {a:?} {b:?}");
            assert_eq!(eq(f, a, b), eq(f, b, a));
            if !is_nan(f, a) && !is_nan(f, b) {
                let three = [lt(f, a, b), eq(f, a, b), lt(f, b, a)];
                assert_eq!(three.iter().filter(|&&c| c).count(), 1, "{f:?} {a:?} {b:?}");
                assert_eq!(le(f, a, b), three[0] || three[1]);
                assert!(le(f, &lo, &hi));
                // min and max return one operand each; different ones unless a = b.
                assert!((lo == *a && hi == *b) || (lo == *b && hi == *a));
            } else {
                assert!(!lt(f, a, b) && !le(f, a, b) && !eq(f, a, b));
            }
        }
    }
    // lt is a strict total order on the non-NaN values (the sort panics on an inconsistent
    // order), and consecutive sorted values are ordered or equal.
    let mut sorted: Vec<&Bits> = vals.iter().filter(|x| !is_nan(f, x)).collect();
    sorted.sort_by(|x, y| {
        if lt(f, x, y) {
            Ordering::Less
        } else if lt(f, y, x) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    });
    for pair in sorted.windows(2) {
        assert!(le(f, pair[0], pair[1]));
    }
    // Only +0 and -0 are equal without being identical.
    let equal_pairs = sorted.windows(2).filter(|p| eq(f, p[0], p[1])).count();
    assert_eq!(equal_pairs, 1, "{f:?}");
}

#[test]
fn tiny_identities_exhaustive() {
    per_format(&tiny_up_to(7), identities);
}

#[test]
fn widening_is_exact_and_narrowing_inverts_it() {
    // (eb, sb) embeds in (eb', sb') when eb <= eb' and sb <= sb'.
    let wide = [
        Format { eb: 4, sb: 6 },
        Format { eb: 6, sb: 6 },
        B32,
        B64,
        X87V,
    ];
    for f in TINY {
        for g in wide.into_iter().filter(|g| g.eb >= f.eb && g.sb >= f.sb) {
            for x in 0..1u128 << f.width() {
                let a = bw(f.width(), x);
                for rm in Rm::ALL {
                    let up = to_fp(f, g, rm, &a);
                    let back = to_fp(g, f, rm, &up);
                    if is_nan(f, &a) {
                        assert_eq!(up, canonical_nan(g));
                        assert_eq!(back, canonical_nan(f));
                    } else {
                        assert_eq!(back, a, "{f:?} -> {g:?} -> back, {rm:?}, {x:#x}");
                        assert_eq!(to_fp(g, g, rm, &up), up, "to_fp to the same format");
                    }
                }
            }
        }
    }
}

// --- big naturals ------------------------------------------------------------------------------

fn nat(x: u128) -> Nat {
    Nat::from_limbs(vec![x as u64, (x >> 64) as u64])
}

fn native(n: &Nat) -> u128 {
    let l = n.limbs();
    assert!(l.len() <= 2, "too wide for u128");
    u128::from(l.first().copied().unwrap_or(0)) | (u128::from(l.get(1).copied().unwrap_or(0)) << 64)
}

fn gen_nat_u128(rng: &mut Rng) -> u128 {
    let r = (u128::from(rng.next()) << 64) | u128::from(rng.next());
    match rng.below(6) {
        0 => u128::from(rng.below(5)),
        1 => 1u128 << rng.below(128),
        2 => u128::MAX >> rng.below(128),
        _ => r >> rng.below(128),
    }
}

#[test]
fn naturals_match_native() {
    let mut rng = Rng(0x5eed_0009);
    for _ in 0..200_000 {
        let (a, b) = (gen_nat_u128(&mut rng), gen_nat_u128(&mut rng));
        let (na, nb) = (nat(a), nat(b));
        assert_eq!(na.cmp(&nb), a.cmp(&b));
        assert_eq!(na.bit_len(), u64::from(128 - a.leading_zeros()));
        assert_eq!(na.is_pow2(), a.is_power_of_two());
        assert_eq!(na.is_odd(), a % 2 == 1);
        if let Some(s) = a.checked_add(b) {
            assert_eq!(native(&na.add(&nb)), s);
        }
        if a >= b {
            assert_eq!(native(&na.sub(&nb)), a - b);
        }
        let (a64, b64) = (a as u64, b as u64);
        assert_eq!(
            native(&nat(a64.into()).mul(&nat(b64.into()))),
            u128::from(a64) * u128::from(b64)
        );
        if let (Some(q0), Some(r0)) = (a.checked_div(b), a.checked_rem(b)) {
            let (q, r) = na.divrem(&nb);
            assert_eq!((native(&q), native(&r)), (q0, r0), "{a} divrem {b}");
        }
        assert_eq!(native(&na.isqrt()), a.isqrt());
        let k = rng.below(140);
        if k < 128 {
            assert_eq!(native(&na.shr(k)), a >> k);
            assert_eq!(native(&na.low_bits(k)), a & ((1u128 << k) - 1));
            assert_eq!(na.bit(k), (a >> k) & 1 == 1);
            if a.leading_zeros() as u64 >= k {
                assert_eq!(native(&na.shl(k)), a << k);
            }
        } else {
            assert!(na.shr(k).is_zero());
            assert_eq!(na.low_bits(k), na);
            assert!(!na.bit(k));
        }
        // cmp_scaled against shifting both sides into u128 range.
        if a != 0 && b != 0 {
            let (x, y) = (rng.below(8) as i64 - 4, rng.below(8) as i64 - 4);
            let (a2, b2) = (a >> 8, b >> 8); // room for shifts up to 7
            if a2 != 0 && b2 != 0 {
                let s = x.min(y);
                let want = (a2 << (x - s)).cmp(&(b2 << (y - s)));
                assert_eq!(cmp_scaled(&nat(a2), x, &nat(b2), y), want);
            }
        }
    }
}

fn wide_nat(rng: &mut Rng, max_limbs: u64) -> Nat {
    let n = 1 + rng.below(max_limbs) as usize;
    let mut limbs: Vec<u64> = (0..n)
        .map(|_| match rng.below(4) {
            0 => 0,
            1 => u64::MAX,
            _ => rng.next(),
        })
        .collect();
    if rng.coin() {
        limbs[n - 1] >>= rng.below(64);
    }
    Nat::from_limbs(limbs)
}

#[test]
fn wide_naturals_are_consistent() {
    let mut rng = Rng(0x5eed_000a);
    for _ in 0..3_000 {
        let (a, b) = (wide_nat(&mut rng, 12), wide_nat(&mut rng, 12));
        assert_eq!(a.add(&b).sub(&b), a);
        assert_eq!(a.add(&b), b.add(&a));
        assert_eq!(a.mul(&b), b.mul(&a));
        if !b.is_zero() {
            assert_eq!(a.mul(&b).divrem(&b), (a.clone(), Nat::zero()));
            let (q, r) = a.divrem(&b);
            assert!(r < b);
            assert_eq!(q.mul(&b).add(&r), a);
        }
        let k = rng.below(300);
        assert_eq!(a.shl(k).shr(k), a);
        assert_eq!(a.shr(k).shl(k).add(&a.low_bits(k)), a);
        assert_eq!(a.shl(k), a.mul(&Nat::pow2(k)));
        let s = a.isqrt();
        let s1 = s.add(&Nat::one());
        assert!(s.mul(&s) <= a && s1.mul(&s1) > a);
        assert_eq!(a.mul(&a).isqrt(), a);
    }
    // 2^2k - 1 has root 2^k - 1, and 2^2k = 1 (mod 2^k - 1) since 2^k = 1 (mod 2^k - 1).
    for k in [2u64, 63, 64, 65, 127, 500, 5000] {
        let m = Nat::ones(k);
        assert_eq!(Nat::ones(2 * k).isqrt(), m);
        assert_eq!(Nat::pow2(2 * k).isqrt(), Nat::pow2(k));
        assert_eq!(Nat::pow2(2 * k).divrem(&m).1, Nat::one());
    }
}
