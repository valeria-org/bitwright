//! Kernel tests against the independent reference evaluator (`bitwright-ref`).
//!
//! Every operator is checked three ways: through the public dispatch (native path at <= 128
//! bits), through the limb kernels directly (so the general path is exercised at narrow widths
//! too), and against the reference. Exhaustive at small widths, boundary-biased random at
//! widths that straddle the u64 / u128 / limb boundaries.

use super::*;
use bitwright_ref as r;

// ----- conversions and op mapping -------------------------------------------------------------

fn to_ref(v: &BitVec) -> r::Bits {
    r::Bits::from_limbs(v.width().bits(), v.limbs())
}

fn from_ref(b: &r::Bits) -> BitVec {
    BitVec::wrapping_from_limbs(Width::new(b.width()).unwrap(), &b.to_limbs())
}

fn ref_un(op: UnOp) -> r::UnOp {
    match op {
        UnOp::Not => r::UnOp::Not,
        UnOp::Neg => r::UnOp::Neg,
        UnOp::Popcnt => r::UnOp::Popcnt,
        UnOp::Clz => r::UnOp::Clz,
        UnOp::Ctz => r::UnOp::Ctz,
        UnOp::Bswap => r::UnOp::Bswap,
        UnOp::BitRev => r::UnOp::BitRev,
    }
}

fn ref_bin(op: BinOp) -> r::BinOp {
    match op {
        BinOp::Add => r::BinOp::Add,
        BinOp::Sub => r::BinOp::Sub,
        BinOp::Mul => r::BinOp::Mul,
        BinOp::UMulHi => r::BinOp::UMulHi,
        BinOp::SMulHi => r::BinOp::SMulHi,
        BinOp::UDiv => r::BinOp::UDiv,
        BinOp::URem => r::BinOp::URem,
        BinOp::SDiv => r::BinOp::SDiv,
        BinOp::SRem => r::BinOp::SRem,
        BinOp::And => r::BinOp::And,
        BinOp::Or => r::BinOp::Or,
        BinOp::Xor => r::BinOp::Xor,
        BinOp::Shl => r::BinOp::Shl,
        BinOp::LShr => r::BinOp::LShr,
        BinOp::AShr => r::BinOp::AShr,
        BinOp::RotL => r::BinOp::RotL,
        BinOp::RotR => r::BinOp::RotR,
        BinOp::Pdep => r::BinOp::Pdep,
        BinOp::Pext => r::BinOp::Pext,
    }
}

fn ref_cmp(op: CmpOpExt) -> r::CmpOp {
    match op {
        CmpOpExt::Eq => r::CmpOp::Eq,
        CmpOpExt::Ne => r::CmpOp::Ne,
        CmpOpExt::Ult => r::CmpOp::Ult,
        CmpOpExt::Ule => r::CmpOp::Ule,
        CmpOpExt::Ugt => r::CmpOp::Ugt,
        CmpOpExt::Uge => r::CmpOp::Uge,
        CmpOpExt::Slt => r::CmpOp::Slt,
        CmpOpExt::Sle => r::CmpOp::Sle,
        CmpOpExt::Sgt => r::CmpOp::Sgt,
        CmpOpExt::Sge => r::CmpOp::Sge,
    }
}

// ----- checkers -------------------------------------------------------------------------------

fn check_un(op: UnOp, a: &BitVec) {
    let w = a.width().bits();
    let expected = r::un(ref_un(op), &to_ref(a));
    let got = BitVec::apply_un(op, a);
    match expected {
        None => assert_eq!(
            got,
            Err(WidthError::NotByteMultiple { bits: w }),
            "{op:?} {a}"
        ),
        Some(e) => {
            let e = from_ref(&e);
            assert_eq!(got, Ok(e), "{op:?} {a} (dispatch)");
            let wide = BitVec::from_canonical(a.width(), wide::un(op, w, a.raw()));
            assert_eq!(wide, e, "{op:?} {a} (limbs)");
        }
    }
}

fn check_bin(op: BinOp, a: &BitVec, b: &BitVec) {
    let w = a.width().bits();
    let e = from_ref(&r::bin(ref_bin(op), &to_ref(a), &to_ref(b)));
    assert_eq!(
        BitVec::apply_bin(op, a, b),
        Ok(e),
        "{op:?} {a} {b} (dispatch)"
    );
    let wide = BitVec::from_canonical(a.width(), wide::bin(op, w, a.raw(), b.raw()));
    assert_eq!(wide, e, "{op:?} {a} {b} (limbs)");
}

fn check_cmp(op: CmpOpExt, a: &BitVec, b: &BitVec) {
    let e = r::cmp(ref_cmp(op), &to_ref(a), &to_ref(b));
    assert_eq!(
        BitVec::apply_cmp(op, a, b),
        Ok(e),
        "{op:?} {a} {b} (dispatch)"
    );
    let (c, swap) = op.canonical();
    let (x, y) = if swap { (b, a) } else { (a, b) };
    let w = a.width().bits();
    assert_eq!(
        wide::cmp(c, w, x.raw(), y.raw()),
        e,
        "{op:?} {a} {b} (limbs)"
    );
}

fn all_values(w: u16) -> impl Iterator<Item = BitVec> {
    let width = Width::new(w).unwrap();
    (0..(1u128 << w)).map(move |v| BitVec::from_u128(width, v).unwrap())
}

// ----- exhaustive small widths ----------------------------------------------------------------

#[test]
fn exhaustive_unary_w1_to_w10() {
    for w in 1..=10 {
        for a in all_values(w) {
            for op in UnOp::ALL {
                check_un(op, &a);
            }
        }
    }
}

#[test]
fn exhaustive_binary_w1_to_w8() {
    for w in 1..=8 {
        let vals: Vec<_> = all_values(w).collect();
        for a in &vals {
            for b in &vals {
                for op in BinOp::ALL {
                    check_bin(op, a, b);
                }
            }
        }
    }
}

#[test]
fn exhaustive_compare_w1_to_w8() {
    for w in 1..=8 {
        let vals: Vec<_> = all_values(w).collect();
        for a in &vals {
            for b in &vals {
                for op in CmpOpExt::ALL {
                    check_cmp(op, a, b);
                }
            }
        }
    }
}

#[test]
fn exhaustive_casts_small() {
    for w in 1..=8u16 {
        for a in all_values(w) {
            let ra = to_ref(&a);
            for to in w..=12 {
                let tw = Width::new(to).unwrap();
                assert_eq!(
                    a.zext(tw).unwrap(),
                    from_ref(&r::zext(&ra, to)),
                    "zext {a} {to}"
                );
                assert_eq!(
                    a.sext(tw).unwrap(),
                    from_ref(&r::sext(&ra, to)),
                    "sext {a} {to}"
                );
            }
            for lo in 0..w {
                for len in 1..=(w - lo) {
                    let got = a.extract(lo, Width::new(len).unwrap()).unwrap();
                    assert_eq!(
                        got,
                        from_ref(&r::extract(&ra, lo, len)),
                        "extract {a} {lo} {len}"
                    );
                }
            }
        }
    }
    for hw in 1..=5u16 {
        for lw in 1..=5u16 {
            for h in all_values(hw) {
                for l in all_values(lw) {
                    let got = BitVec::concat(&h, &l).unwrap();
                    assert_eq!(
                        got,
                        from_ref(&r::concat(&to_ref(&h), &to_ref(&l))),
                        "concat {h} {l}"
                    );
                }
            }
        }
    }
}

// ----- boundary-biased random at wide widths --------------------------------------------------

/// SplitMix64 with an explicit seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

const WIDE_WIDTHS: [u16; 23] = [
    9, 16, 31, 32, 33, 63, 64, 65, 96, 127, 128, 129, 192, 255, 256, 257, 300, 320, 384, 385, 448,
    511, 512,
];

/// A value biased toward boundaries: 0, 1, 2, all ones, smin, smax, powers of two and their
/// neighbours, small counts near the width, dense and sparse random bit patterns.
fn biased(rng: &mut Rng, width: Width) -> BitVec {
    let w = width.bits();
    let random = |rng: &mut Rng| {
        let limbs: Vec<u64> = (0..8).map(|_| rng.next()).collect();
        BitVec::wrapping_from_limbs(width, &limbs)
    };
    let pow2 = |k: u16| {
        let mut l = [0u64; 8];
        l[k as usize / 64] = 1 << (k % 64);
        BitVec::wrapping_from_limbs(width, &l)
    };
    let one = BitVec::one(width);
    match rng.below(16) {
        14 | 15 => {
            // A random value with a random significant length, so multi-limb divisors and
            // quotients of every size occur.
            let len = 1 + rng.below(u64::from(w)) as u16;
            let v = random(rng);
            v.trunc(Width::new(len).unwrap())
                .and_then(|t| t.zext(width))
                .unwrap_or(v)
        }
        0 => BitVec::zero(width),
        1 => one,
        2 => BitVec::wrapping_from_u64(width, 2),
        3 => BitVec::ones(width),
        4 => BitVec::smin(width),
        5 => BitVec::smax(width),
        6 => pow2(rng.below(u64::from(w)) as u16),
        7 => {
            let p = pow2(rng.below(u64::from(w)) as u16);
            BitVec::bin_unchecked(BinOp::Sub, &p, &one)
        }
        8 => {
            let p = pow2(rng.below(u64::from(w)) as u16);
            BitVec::bin_unchecked(BinOp::Add, &p, &one)
        }
        9 => BitVec::wrapping_from_u64(width, u64::from(w) + rng.below(3) - 1), // counts W-1, W, W+1
        10 => BitVec::wrapping_from_u64(width, rng.below(u64::from(w))),
        11 => {
            // sparse
            let a = random(rng);
            let b = random(rng);
            let c = BitVec::bin_unchecked(BinOp::And, &a, &b);
            BitVec::bin_unchecked(BinOp::And, &c, &random(rng))
        }
        12 => BitVec::un_unchecked(UnOp::Neg, &random(rng)),
        _ => random(rng),
    }
}

fn random_wide_battery(samples: usize, seed: u64) {
    let mut rng = Rng(seed);
    for w in WIDE_WIDTHS {
        let width = Width::new(w).unwrap();
        for _ in 0..samples {
            let a = biased(&mut rng, width);
            let b = biased(&mut rng, width);
            for op in UnOp::ALL {
                check_un(op, &a);
            }
            for op in BinOp::ALL {
                check_bin(op, &a, &b);
            }
            for op in CmpOpExt::ALL {
                check_cmp(op, &a, &b);
            }
            // Casts across the limb boundaries.
            let ra = to_ref(&a);
            let to = w + rng.below(u64::from(Width::MAX_BITS - w) + 1) as u16;
            let tw = Width::new(to).unwrap();
            assert_eq!(
                a.zext(tw).unwrap(),
                from_ref(&r::zext(&ra, to)),
                "zext {a} {to}"
            );
            assert_eq!(
                a.sext(tw).unwrap(),
                from_ref(&r::sext(&ra, to)),
                "sext {a} {to}"
            );
            let lo = rng.below(u64::from(w)) as u16;
            let len = 1 + rng.below(u64::from(w - lo)) as u16;
            assert_eq!(
                a.extract(lo, Width::new(len).unwrap()).unwrap(),
                from_ref(&r::extract(&ra, lo, len)),
                "extract {a} {lo} {len}"
            );
            // Concatenation with an operand of an unrelated width.
            if w < 512 {
                let lw = 1 + rng.below(u64::from(512 - w)) as u16;
                let l = biased(&mut rng, Width::new(lw).unwrap());
                assert_eq!(
                    BitVec::concat(&a, &l).unwrap(),
                    from_ref(&r::concat(&ra, &to_ref(&l))),
                    "concat {a} {l}"
                );
            }
            check_signed_conversion(&a);
        }
    }
}

/// `to_i128` against the reference: fits iff bits [127, W) all equal the sign.
fn check_signed_conversion(a: &BitVec) {
    let ra = to_ref(a);
    let w = ra.width();
    let expected = if w <= 128 {
        let v = r::sext(&ra, 128).to_u128().unwrap() as i128;
        Some(v)
    } else {
        let sign = ra.bit(127);
        (128..w).all(|i| ra.bit(i) == sign).then(|| {
            let low = r::extract(&ra, 0, 128).to_u128().unwrap();
            low as i128
        })
    };
    assert_eq!(a.to_i128(), expected, "to_i128 {a}");
    if let Some(v) = expected {
        assert_eq!(
            BitVec::from_i128(a.width(), v).unwrap(),
            *a,
            "from_i128 {a}"
        );
    }
}

#[test]
fn every_width_sweep() {
    let mut rng = Rng(0x5eed_0003);
    for w in 1..=512u16 {
        let width = Width::new(w).unwrap();
        for _ in 0..3 {
            let a = biased(&mut rng, width);
            let b = biased(&mut rng, width);
            for op in UnOp::ALL {
                check_un(op, &a);
            }
            for op in BinOp::ALL {
                check_bin(op, &a, &b);
            }
            for op in CmpOpExt::ALL {
                check_cmp(op, &a, &b);
            }
            check_signed_conversion(&a);
        }
    }
}

#[test]
fn random_wide_widths() {
    random_wide_battery(150, 0x5eed_0001);
}

/// The long version of `random_wide_widths` (run with `--ignored`, e.g. nightly).
#[test]
#[ignore = "long-running; run nightly with --ignored"]
fn random_wide_widths_deep() {
    random_wide_battery(20_000, 0x5eed_0002);
}

// ----- API ------------------------------------------------------------------------------------

#[test]
fn width_bounds() {
    assert!(Width::new(0).is_err());
    assert!(Width::new(513).is_err());
    assert_eq!(Width::new(512).unwrap(), Width::W512);
}

#[test]
fn constructors_check_fit() {
    let w8 = Width::W8;
    assert!(BitVec::from_u64(w8, 255).is_ok());
    assert!(BitVec::from_u64(w8, 256).is_err());
    assert_eq!(BitVec::wrapping_from_u64(w8, 256), BitVec::zero(w8));
    assert_eq!(BitVec::from_i128(w8, -128).unwrap(), BitVec::smin(w8));
    assert!(BitVec::from_i128(w8, -129).is_err());
    assert!(BitVec::from_i128(w8, 128).is_err());
    assert_eq!(
        BitVec::from_i128(Width::W512, -1).unwrap(),
        BitVec::ones(Width::W512)
    );
    assert_eq!(BitVec::ones(Width::W512).to_i128(), Some(-1));
    assert_eq!(BitVec::smin(Width::W512).to_i128(), None);
    assert!(BitVec::from_limbs(Width::new(65).unwrap(), &[0, 2]).is_err());
    assert!(BitVec::from_limbs(Width::new(65).unwrap(), &[7, 1]).is_ok());
}

#[test]
fn mismatched_widths_are_errors() {
    let a = BitVec::zero(Width::W8);
    let b = BitVec::zero(Width::W16);
    assert_eq!(
        BitVec::apply_bin(BinOp::Add, &a, &b),
        Err(WidthError::Mismatch { left: 8, right: 16 })
    );
    assert!(BitVec::apply_cmp(CmpOp::Eq, &a, &b).is_err());
    assert!(a.sext(Width::W1).is_err());
    assert!(a.extract(4, Width::new(5).unwrap()).is_err());
    assert!(BitVec::concat(&BitVec::zero(Width::W512), &a).is_err());
}

#[test]
fn display_parse_round_trip() {
    let mut rng = Rng(7);
    for w in WIDE_WIDTHS.iter().copied().chain([1, 2, 3, 8]) {
        let width = Width::new(w).unwrap();
        for _ in 0..50 {
            let v = biased(&mut rng, width);
            assert_eq!(BitVec::parse(&v.to_string()).unwrap(), v, "{v}");
        }
    }
    assert_eq!(BitVec::parse("255:8").unwrap(), BitVec::ones(Width::W8));
    assert_eq!(BitVec::parse("-128:8").unwrap(), BitVec::smin(Width::W8));
    assert!(BitVec::parse("-129:8").is_err());
    assert!(BitVec::parse("256:8").is_err());
    assert_eq!(BitVec::parse("0b1010:4").unwrap().to_u64(), Some(10));
    assert_eq!(BitVec::parse("16'hbeef").unwrap().to_u64(), Some(0xbeef));
    assert!(BitVec::parse("12").is_err());
    let too_big = format!("0x1{}:512", "0".repeat(128));
    assert!(
        BitVec::parse(&too_big).is_err(),
        "literal wider than 512 bits"
    );
    for bad in [
        "8'h",
        "'h1",
        "8'x1",
        "_:8",
        "2:1",
        "0x1:",
        "0x1:abc",
        "0x1:99999999999",
        "-0x81:8",
    ] {
        assert!(BitVec::parse(bad).is_err(), "{bad}");
    }
    assert_eq!(BitVec::parse("-0:8").unwrap(), BitVec::zero(Width::W8));
    assert_eq!(BitVec::parse("-0x80:8").unwrap(), BitVec::smin(Width::W8));
    assert_eq!("0xff:8".parse::<BitVec>().unwrap(), BitVec::ones(Width::W8));
    assert_eq!(
        format!("{:#x}", BitVec::smin(Width::W128)),
        format!("0x8{}", "0".repeat(31))
    );
    assert!(BitVec::parse("0xfg:8").is_err());
    assert_eq!(BitVec::zero(Width::W16).to_string(), "0x0:16");
    let big = BitVec::smin(Width::W512).to_string();
    assert!(big.starts_with("0x8") && big.ends_with(":512") && big.len() == 2 + 128 + 4);
}

#[test]
fn ordering_is_width_then_unsigned_value() {
    let w = Width::W128;
    let lo = BitVec::wrapping_from_u128(w, 1 << 64);
    let hi = BitVec::wrapping_from_u128(w, (1 << 64) + 1);
    assert!(lo < hi);
    assert!(BitVec::ones(Width::W8) < BitVec::zero(Width::W16));
    let mut v = vec![BitVec::ones(w), BitVec::zero(w), lo];
    v.sort();
    assert_eq!(v, vec![BitVec::zero(w), lo, BitVec::ones(w)]);
}
