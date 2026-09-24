//! The floating-point arithmetic against the independent reference (`bitwright-ref`'s exact
//! rational implementation of the same specification): exhaustively on small formats, every
//! operation under every rounding mode, and on random operands of the standard formats.

use super::*;
use crate::testutil::Rng;
use bitwright_ref::Bits;
use bitwright_ref::fp as r;

fn rf(f: FpFormat) -> r::Format {
    r::Format {
        eb: f.eb() as u16,
        sb: f.sb() as u16,
    }
}

fn rm(m: RoundingMode) -> r::Rm {
    match m {
        RoundingMode::Rne => r::Rm::Rne,
        RoundingMode::Rna => r::Rm::Rna,
        RoundingMode::Rtp => r::Rm::Rtp,
        RoundingMode::Rtn => r::Rm::Rtn,
        RoundingMode::Rtz => r::Rm::Rtz,
    }
}

fn bits(v: &BitVec) -> Bits {
    Bits::from_limbs(v.width().bits(), v.limbs())
}

fn back(b: &Bits) -> BitVec {
    let w = Width::new(b.width()).unwrap();
    BitVec::wrapping_from_limbs(w, &b.to_limbs())
}

/// Every binary operation (and the comparisons) of `f` on `a`, `b`, both ways.
fn check_pair(f: FpFormat, a: &BitVec, b: &BitVec) {
    let (ra, rb, g) = (bits(a), bits(b), rf(f));
    let what = |op: &str| format!("{f:?} {op} {a} {b}");
    for m in RoundingMode::ALL {
        let op = |s: &str| format!("{} {m:?}", what(s));
        assert_eq!(
            f.add(m, a, b).unwrap(),
            back(&r::add(g, rm(m), &ra, &rb)),
            "{}",
            op("add")
        );
        assert_eq!(
            f.sub(m, a, b).unwrap(),
            back(&r::sub(g, rm(m), &ra, &rb)),
            "{}",
            op("sub")
        );
        assert_eq!(
            f.mul(m, a, b).unwrap(),
            back(&r::mul(g, rm(m), &ra, &rb)),
            "{}",
            op("mul")
        );
        assert_eq!(
            f.div(m, a, b).unwrap(),
            back(&r::div(g, rm(m), &ra, &rb)),
            "{}",
            op("div")
        );
    }
    assert_eq!(
        f.rem(a, b).unwrap(),
        back(&r::rem(g, &ra, &rb)),
        "{}",
        what("rem")
    );
    assert_eq!(
        f.min(a, b).unwrap(),
        back(&r::min(g, &ra, &rb)),
        "{}",
        what("min")
    );
    assert_eq!(
        f.max(a, b).unwrap(),
        back(&r::max(g, &ra, &rb)),
        "{}",
        what("max")
    );
    assert_eq!(
        f.cmp(FpCmpOp::Eq, a, b).unwrap(),
        r::eq(g, &ra, &rb),
        "{}",
        what("eq")
    );
    assert_eq!(
        f.cmp(FpCmpOp::Lt, a, b).unwrap(),
        r::lt(g, &ra, &rb),
        "{}",
        what("lt")
    );
    assert_eq!(
        f.cmp(FpCmpOp::Le, a, b).unwrap(),
        r::le(g, &ra, &rb),
        "{}",
        what("le")
    );
    assert_eq!(
        f.copysign(a, b).unwrap(),
        back(&r::copysign(g, &ra, &rb)),
        "{}",
        what("copysign")
    );
}

/// Every unary operation, conversion and test of `f` on `a`.
fn check_one(f: FpFormat, a: &BitVec, others: &[FpFormat], int_widths: &[u16]) {
    let (ra, g) = (bits(a), rf(f));
    let what = |op: &str| format!("{f:?} {op} {a}");
    for m in RoundingMode::ALL {
        let op = |s: &str| format!("{} {m:?}", what(s));
        assert_eq!(
            f.sqrt(m, a).unwrap(),
            back(&r::sqrt(g, rm(m), &ra)),
            "{}",
            op("sqrt")
        );
        assert_eq!(
            f.round_to_integral(m, a).unwrap(),
            back(&r::round_to_integral(g, rm(m), &ra)),
            "{}",
            op("roundToIntegral")
        );
        for &to in others {
            assert_eq!(
                f.convert(to, m, a).unwrap(),
                back(&r::to_fp(g, rf(to), rm(m), &ra)),
                "{} to {to:?}",
                op("convert")
            );
        }
        for &n in int_widths {
            let w = Width::new(n).unwrap();
            assert_eq!(
                f.to_sint(m, a, w).unwrap(),
                back(&r::to_sint(g, rm(m), &ra, n)),
                "{} to {n}",
                op("to_sint")
            );
            assert_eq!(
                f.to_uint(m, a, w).unwrap(),
                back(&r::to_uint(g, rm(m), &ra, n)),
                "{} to {n}",
                op("to_uint")
            );
        }
    }
    assert_eq!(f.neg(a).unwrap(), back(&r::neg(g, &ra)), "{}", what("neg"));
    assert_eq!(f.abs(a).unwrap(), back(&r::abs(g, &ra)), "{}", what("abs"));
    for (t, rt) in [
        (FpTest::Nan, r::is_nan as fn(r::Format, &Bits) -> bool),
        (FpTest::Infinite, r::is_infinite),
        (FpTest::Zero, r::is_zero),
        (FpTest::Normal, r::is_normal),
        (FpTest::Subnormal, r::is_subnormal),
        (FpTest::Negative, r::is_negative),
        (FpTest::Positive, r::is_positive),
    ] {
        assert_eq!(f.test(t, a).unwrap(), rt(g, &ra), "{} {t:?}", what("test"));
    }
}

fn check_fma(f: FpFormat, a: &BitVec, b: &BitVec, c: &BitVec) {
    let g = rf(f);
    for m in RoundingMode::ALL {
        assert_eq!(
            f.fma(m, a, b, c).unwrap(),
            back(&r::fma(g, rm(m), &bits(a), &bits(b), &bits(c))),
            "{f:?} fma {m:?} {a} {b} {c}"
        );
    }
}

fn all_values(f: FpFormat) -> Vec<BitVec> {
    let w = f.width();
    (0..1u64 << w.bits())
        .map(|v| BitVec::wrapping_from_u64(w, v))
        .collect()
}

/// Every format of `eb + sb` between the bounds.
fn formats(min_width: u32, max_width: u32) -> Vec<FpFormat> {
    let mut out = Vec::new();
    for w in min_width..=max_width {
        for eb in 2..w - 1 {
            if let Ok(f) = FpFormat::new(eb, w - eb) {
                out.push(f);
            }
        }
    }
    out
}

fn exhaustive(max_pair_width: u32, max_fma_width: u32) {
    let tiny = formats(4, max_pair_width);
    for &f in &tiny {
        let vals = all_values(f);
        for a in &vals {
            for b in &vals {
                check_pair(f, a, b);
            }
            check_one(f, a, &tiny, &[1, 2, 3, 5, 8, 13]);
        }
        if f.width().bits() as u32 <= max_fma_width {
            for a in &vals {
                for b in &vals {
                    for c in &vals {
                        check_fma(f, a, b, c);
                    }
                }
            }
        }
        // Every integer of up to 9 bits, both readings.
        for n in 1..=9u16 {
            let w = Width::new(n).unwrap();
            for v in 0..1u64 << n {
                let x = BitVec::wrapping_from_u64(w, v);
                for m in RoundingMode::ALL {
                    assert_eq!(
                        f.from_sint(m, &x),
                        back(&r::from_sint(rf(f), rm(m), &bits(&x))),
                        "{f:?} from_sint {m:?} {x}"
                    );
                    assert_eq!(
                        f.from_uint(m, &x),
                        back(&r::from_uint(rf(f), rm(m), &bits(&x))),
                        "{f:?} from_uint {m:?} {x}"
                    );
                }
            }
        }
    }
}

#[test]
fn small_formats_match_the_reference_exhaustively() {
    // Every format of 4 to 6 bits: every pair, every value; fma on every triple up to 5 bits.
    exhaustive(6, 5);
}

#[test]
#[ignore = "long: formats of 7 and 8 bits, and fma on every triple of 6 bits"]
fn small_formats_match_the_reference_exhaustively_heavy() {
    exhaustive(8, 6);
}

#[test]
fn standard_formats_match_the_reference() {
    let mut rng = Rng(21);
    let wide = FpFormat::new(15, 497).unwrap();
    for (f, n) in [
        (FpFormat::F16, 3000),
        (FpFormat::BF16, 3000),
        (FpFormat::F32, 3000),
        (FpFormat::F64, 3000),
        (FpFormat::X87, 1500),
        (FpFormat::F128, 1500),
        (FpFormat::new(9, 40).unwrap(), 1500),
        (wide, 150),
    ] {
        let others = [FpFormat::F16, FpFormat::F32, FpFormat::F64, FpFormat::X87];
        for _ in 0..n {
            let (a, b, c) = (
                super::tests::sample(&mut rng, f),
                super::tests::sample(&mut rng, f),
                super::tests::sample(&mut rng, f),
            );
            check_pair(f, &a, &b);
            check_one(f, &a, &others, &[1, 8, 16, 32, 64, 65, 128]);
            check_fma(f, &a, &b, &c);
            let n = 1 + rng.below(200) as u16;
            let x = BitVec::wrapping_from_limbs(
                Width::new(n).unwrap(),
                &[rng.next(), rng.next(), rng.next(), rng.next()],
            );
            for m in RoundingMode::ALL {
                assert_eq!(
                    f.from_sint(m, &x),
                    back(&r::from_sint(rf(f), rm(m), &bits(&x))),
                    "{f:?} from_sint {m:?} {x}"
                );
                assert_eq!(
                    f.from_uint(m, &x),
                    back(&r::from_uint(rf(f), rm(m), &bits(&x))),
                    "{f:?} from_uint {m:?} {x}"
                );
            }
        }
    }
}

#[test]
fn x87_encodings_match_the_reference() {
    let mut rng = Rng(22);
    let w80 = Width::new(80).unwrap();
    for k in 0..20_000 {
        let mut v = u128::from(rng.next()) << 64 | u128::from(rng.next());
        match k % 4 {
            0 => v &= !(0x7fff << 64),
            1 => v |= 0x7fff << 64,
            _ => {}
        }
        let x = BitVec::wrapping_from_u128(w80, v);
        assert_eq!(
            x87_load(&x).unwrap(),
            back(&r::x87_load(&bits(&x))),
            "load {x}"
        );
        let a = super::tests::sample(&mut rng, FpFormat::X87);
        assert_eq!(
            x87_store(&a).unwrap(),
            back(&r::x87_store(&bits(&a))),
            "store {a}"
        );
    }
}
