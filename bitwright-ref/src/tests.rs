//! Self-checks for the reference evaluator.
//!
//! None of these re-run the evaluator's own algorithms. They use (1) native `u128`/`i128`
//! arithmetic as a structurally different oracle for widths up to 128, written directly from the
//! SMT-LIB conventions; (2) algebraic identities; and (3) hand-computed wide examples.

use super::*;

const UNOPS: [UnOp; 7] = [
    UnOp::Not,
    UnOp::Neg,
    UnOp::Popcnt,
    UnOp::Clz,
    UnOp::Ctz,
    UnOp::Bswap,
    UnOp::BitRev,
];

const BINOPS: [BinOp; 19] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::UMulHi,
    BinOp::SMulHi,
    BinOp::UDiv,
    BinOp::URem,
    BinOp::SDiv,
    BinOp::SRem,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::LShr,
    BinOp::AShr,
    BinOp::RotL,
    BinOp::RotR,
    BinOp::Pdep,
    BinOp::Pext,
];

const CMPOPS: [CmpOp; 10] = [
    CmpOp::Eq,
    CmpOp::Ne,
    CmpOp::Ult,
    CmpOp::Ule,
    CmpOp::Ugt,
    CmpOp::Uge,
    CmpOp::Slt,
    CmpOp::Sle,
    CmpOp::Sgt,
    CmpOp::Sge,
];

fn b(w: u16, v: u128) -> Bits {
    Bits::from_u128(w, v)
}

fn i(w: u16, v: i128) -> Bits {
    Bits::from_i128(w, v)
}

fn val(x: &Bits) -> u128 {
    x.to_u128().expect("value fits in u128")
}

fn ones(w: u16) -> Bits {
    Bits::from_bools(vec![true; w as usize])
}

/// 2^k at width w.
fn pow2(w: u16, k: u16) -> Bits {
    let mut v = vec![false; w as usize];
    v[k as usize] = true;
    Bits::from_bools(v)
}

fn smin(w: u16) -> Bits {
    pow2(w, w - 1)
}

// --- native oracle (w <= 128; the high-product ops need w <= 64) -----------------------------

fn mask(w: u32) -> u128 {
    if w == 128 {
        u128::MAX
    } else {
        (1u128 << w) - 1
    }
}

fn signed(w: u32, x: u128) -> i128 {
    if w < 128 && (x >> (w - 1)) & 1 == 1 {
        (x | !mask(w)) as i128 // sign-extend by filling the bits above w
    } else {
        x as i128
    }
}

/// Software pdep via "isolate lowest set bit of the mask, then clear it".
fn native_pdep(x: u128, mut m: u128) -> u128 {
    let mut r = 0;
    let mut k = 0;
    while m != 0 {
        let low = m & m.wrapping_neg();
        if (x >> k) & 1 == 1 {
            r |= low;
        }
        m &= m - 1;
        k += 1;
    }
    r
}

fn native_pext(x: u128, mut m: u128) -> u128 {
    let mut r = 0;
    let mut k = 0;
    while m != 0 {
        let low = m & m.wrapping_neg();
        if x & low != 0 {
            r |= 1 << k;
        }
        m &= m - 1;
        k += 1;
    }
    r
}

fn native_bin(op: BinOp, w: u32, a: u128, b: u128) -> Option<u128> {
    let m = mask(w);
    let (sa, sb) = (signed(w, a), signed(w, b));
    Some(match op {
        BinOp::Add => a.wrapping_add(b) & m,
        BinOp::Sub => a.wrapping_sub(b) & m,
        BinOp::Mul => a.wrapping_mul(b) & m,
        BinOp::UMulHi if w <= 64 => (a * b) >> w,
        BinOp::SMulHi if w <= 64 => ((sa * sb) >> w) as u128 & m,
        BinOp::UMulHi | BinOp::SMulHi => return None,
        BinOp::UDiv => a.checked_div(b).unwrap_or(m),
        BinOp::URem => a.checked_rem(b).unwrap_or(a),
        BinOp::SDiv => {
            if b == 0 {
                if sa < 0 { 1 } else { m }
            } else {
                sa.wrapping_div(sb) as u128 & m
            }
        }
        BinOp::SRem => {
            if b == 0 {
                a
            } else {
                sa.wrapping_rem(sb) as u128 & m
            }
        }
        BinOp::And => a & b,
        BinOp::Or => a | b,
        BinOp::Xor => a ^ b,
        BinOp::Shl => {
            if b >= w as u128 {
                0
            } else {
                (a << b) & m
            }
        }
        BinOp::LShr => {
            if b >= w as u128 {
                0
            } else {
                a >> b
            }
        }
        BinOp::AShr => {
            if b >= w as u128 {
                if sa < 0 { m } else { 0 }
            } else {
                (sa >> b) as u128 & m
            }
        }
        BinOp::RotL => {
            let c = (b % w as u128) as u32;
            if c == 0 {
                a
            } else {
                ((a << c) | (a >> (w - c))) & m
            }
        }
        BinOp::RotR => {
            let c = (b % w as u128) as u32;
            if c == 0 {
                a
            } else {
                ((a >> c) | (a << (w - c))) & m
            }
        }
        BinOp::Pdep => native_pdep(a, b),
        BinOp::Pext => native_pext(a, b),
    })
}

fn native_un(op: UnOp, w: u32, a: u128) -> Option<u128> {
    Some(match op {
        UnOp::Not => !a & mask(w),
        UnOp::Neg => a.wrapping_neg() & mask(w),
        UnOp::Popcnt => a.count_ones() as u128,
        UnOp::Clz => (a.leading_zeros() - (128 - w)) as u128,
        UnOp::Ctz => a.trailing_zeros().min(w) as u128,
        UnOp::Bswap => {
            if !w.is_multiple_of(8) {
                return None;
            }
            a.swap_bytes() >> (128 - w)
        }
        UnOp::BitRev => a.reverse_bits() >> (128 - w),
    })
}

fn native_cmp(op: CmpOp, w: u32, a: u128, b: u128) -> bool {
    let (sa, sb) = (signed(w, a), signed(w, b));
    match op {
        CmpOp::Eq => a == b,
        CmpOp::Ne => a != b,
        CmpOp::Ult => a < b,
        CmpOp::Ule => a <= b,
        CmpOp::Ugt => a > b,
        CmpOp::Uge => a >= b,
        CmpOp::Slt => sa < sb,
        CmpOp::Sle => sa <= sb,
        CmpOp::Sgt => sa > sb,
        CmpOp::Sge => sa >= sb,
    }
}

fn check_pair_against_native(w: u16, a: u128, bv: u128) {
    let (x, y) = (b(w, a), b(w, bv));
    for op in BINOPS {
        if let Some(want) = native_bin(op, w as u32, a, bv) {
            let got = bin(op, &x, &y);
            assert_eq!(got.width(), w);
            assert_eq!(val(&got), want, "{op:?} w={w} a={a:#x} b={bv:#x}");
        }
    }
    for op in CMPOPS {
        assert_eq!(
            cmp(op, &x, &y),
            native_cmp(op, w as u32, a, bv),
            "{op:?} w={w} a={a:#x} b={bv:#x}"
        );
    }
}

fn check_un_against_native(w: u16, a: u128) {
    let x = b(w, a);
    for op in UNOPS {
        let got = un(op, &x);
        let want = native_un(op, w as u32, a);
        assert_eq!(got.as_ref().map(val), want, "{op:?} w={w} a={a:#x}");
        if let Some(g) = got {
            assert_eq!(g.width(), w);
        }
    }
}

/// xorshift64*, deterministic.
struct Rng(u64);
impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
    /// A w-bit value, biased toward boundary cases.
    fn value(&mut self, w: u32) -> u128 {
        let m = mask(w);
        let smin = 1u128 << (w - 1);
        let r = ((self.next_u64() as u128) << 64) | self.next_u64() as u128;
        match self.next_u64() % 12 {
            0 => 0,
            1 => 1,
            2 => m,
            3 => smin,
            4 => smin.wrapping_sub(1) & m,
            5 => (smin + 1) & m,
            6 => r % (2 * w as u128 + 2), // small (shift/rotate counts around W)
            7 => (r >> (self.next_u64() % 128)) & m,
            _ => r & m,
        }
    }
}

// --- native cross-checks ----------------------------------------------------------------------

#[test]
fn exhaustive_small_widths_match_native() {
    for w in 1..=8u16 {
        for a in 0..(1u128 << w) {
            check_un_against_native(w, a);
            for bv in 0..(1u128 << w) {
                check_pair_against_native(w, a, bv);
            }
        }
    }
}

#[test]
fn exhaustive_unary_16_bits_match_native() {
    for a in 0..(1u128 << 16) {
        check_un_against_native(16, a);
    }
}

#[test]
fn random_widths_up_to_128_match_native() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for w in [9u16, 12, 16, 24, 31, 32, 33, 63, 64, 65, 100, 127, 128] {
        for _ in 0..1500 {
            let (a, bv) = (rng.value(w as u32), rng.value(w as u32));
            check_un_against_native(w, a);
            check_pair_against_native(w, a, bv);
        }
    }
}

// --- representation ---------------------------------------------------------------------------

#[test]
fn conversions_round_trip() {
    for w in [1u16, 7, 64, 127, 128, 129, 512, 1024] {
        for v in [0u128, 1, 5, u64::MAX as u128, u128::MAX, 1 << 127] {
            let x = b(w, v);
            assert_eq!(x.width(), w);
            let want = v & mask(w.min(128) as u32);
            assert_eq!(x.to_u128(), Some(want));
            assert_eq!(Bits::from_limbs(w, &x.to_limbs()), x);
            assert_eq!(x.to_limbs().len(), (w as usize).div_ceil(64));
        }
    }
    // Width above 128: -1 sign-extends to all ones; bits past 128 make to_u128 fail.
    let m1 = i(200, -1);
    assert_eq!(m1, ones(200));
    assert_eq!(m1.to_limbs(), vec![u64::MAX, u64::MAX, u64::MAX, 0xff]);
    assert_eq!(m1.to_u128(), None);
    assert_eq!(i(8, -1), b(8, 0xff));
    assert_eq!(i(8, 300), b(8, 300 & 0xff));
    assert_eq!(i(200, 5), b(200, 5));
    // Extra limbs and bits past the width are ignored; missing limbs are zero.
    let x = Bits::from_limbs(70, &[u64::MAX, u64::MAX, 7]);
    assert_eq!(x.to_limbs(), vec![u64::MAX, 0x3f]);
    assert_eq!(Bits::from_limbs(130, &[3]).to_limbs(), vec![3, 0, 0]);
    assert!(pow2(129, 128).to_u128().is_none());
    assert_eq!(Bits::zero(5), b(5, 0));
    let y = Bits::from_bools(vec![true, false, true]);
    assert_eq!(val(&y), 5);
    assert!(y.bit(0) && !y.bit(1) && y.bit(2));
}

#[test]
#[should_panic]
fn bit_out_of_range_panics() {
    b(4, 0).bit(4);
}

#[test]
#[should_panic]
fn width_mismatch_panics() {
    bin(BinOp::Add, &b(4, 0), &b(5, 0));
}

// --- identities requested by the spec --------------------------------------------------------

#[test]
fn division_identities_exhaustive() {
    for w in 1..=8u16 {
        let sm = smin(w);
        let m1 = ones(w);
        for a in 0..(1u128 << w) {
            let x = b(w, a);
            // b = 0 conventions.
            let z = Bits::zero(w);
            assert_eq!(bin(BinOp::UDiv, &x, &z), ones(w));
            assert_eq!(bin(BinOp::URem, &x, &z), x);
            let sd0 = bin(BinOp::SDiv, &x, &z);
            if x.bit(w - 1) {
                assert_eq!(sd0, b(w, 1));
            } else {
                assert_eq!(sd0, m1);
            }
            assert_eq!(bin(BinOp::SRem, &x, &z), x);
            for bv in 1..(1u128 << w) {
                let y = b(w, bv);
                let q = bin(BinOp::UDiv, &x, &y);
                let r = bin(BinOp::URem, &x, &y);
                assert!(cmp(CmpOp::Ult, &r, &y));
                assert_eq!(bin(BinOp::Add, &bin(BinOp::Mul, &q, &y), &r), x);
                // Signed: a = q*b + r with |r| < |b|, and r is zero or has a's sign.
                let sq = bin(BinOp::SDiv, &x, &y);
                let sr = bin(BinOp::SRem, &x, &y);
                assert_eq!(bin(BinOp::Add, &bin(BinOp::Mul, &sq, &y), &sr), x);
                let r_zero = sr == Bits::zero(w);
                assert!(r_zero || sr.bit(w - 1) == x.bit(w - 1), "srem sign w={w}");
                let (sa, sb) = (signed(w as u32, a), signed(w as u32, bv));
                let rv = signed(w as u32, val(&sr));
                assert!(rv.abs() < sb.abs(), "srem magnitude w={w} a={sa} b={sb}");
                // Quotient sign: positive iff the operand signs agree (unless it is zero or the
                // single overflow case smin / -1).
                let qv = signed(w as u32, val(&sq));
                if !(x == sm && y == m1) && qv != 0 {
                    assert_eq!(qv > 0, (sa < 0) == (sb < 0));
                }
            }
        }
        assert_eq!(bin(BinOp::SDiv, &sm, &m1), sm);
        assert_eq!(bin(BinOp::SRem, &sm, &m1), Bits::zero(w));
    }
}

#[test]
fn additive_identities_exhaustive() {
    for w in 1..=8u16 {
        let one = b(w, 1);
        for a in 0..(1u128 << w) {
            let x = b(w, a);
            let not = un(UnOp::Not, &x).unwrap();
            assert_eq!(un(UnOp::Neg, &x).unwrap(), bin(BinOp::Add, &not, &one));
            let pc = |v: &Bits| val(&un(UnOp::Popcnt, v).unwrap());
            assert_eq!(pc(&x) + pc(&not), w as u128);
            for bv in 0..(1u128 << w) {
                let y = b(w, bv);
                let s = bin(BinOp::Add, &x, &y);
                assert_eq!(bin(BinOp::Sub, &s, &y), x);
            }
        }
    }
}

#[test]
fn clz_ctz_on_powers_of_two() {
    for w in (1..=130u16).chain([256, 511, 512, 1024]) {
        for k in 0..w {
            let p = pow2(w, k);
            assert_eq!(un(UnOp::Clz, &p).unwrap(), b(w, (w - 1 - k) as u128));
            assert_eq!(un(UnOp::Ctz, &p).unwrap(), b(w, k as u128));
            assert_eq!(un(UnOp::Popcnt, &p).unwrap(), b(w, 1));
        }
        let z = Bits::zero(w);
        assert_eq!(un(UnOp::Clz, &z).unwrap(), b(w, w as u128));
        assert_eq!(un(UnOp::Ctz, &z).unwrap(), b(w, w as u128));
        assert_eq!(un(UnOp::Popcnt, &ones(w)).unwrap(), b(w, w as u128));
    }
}

#[test]
fn rotate_inverse_width_7() {
    for x in 0..128u128 {
        for c in 0..128u128 {
            let (xv, cv) = (b(7, x), b(7, c));
            let rr = bin(BinOp::RotR, &xv, &cv);
            assert_eq!(bin(BinOp::RotL, &rr, &cv), xv);
            let rl = bin(BinOp::RotL, &xv, &cv);
            assert_eq!(bin(BinOp::RotR, &rl, &cv), xv);
            // Rotation by c equals rotation by c mod 7.
            assert_eq!(rl, bin(BinOp::RotL, &xv, &b(7, c % 7)));
        }
    }
    // Hand examples: 127 mod 7 = 1, 64 mod 7 = 1, 7 mod 7 = 0.
    assert_eq!(
        bin(BinOp::RotL, &b(7, 0b1000001), &b(7, 127)),
        b(7, 0b0000011)
    );
    assert_eq!(
        bin(BinOp::RotR, &b(7, 0b0000011), &b(7, 64)),
        b(7, 0b1000001)
    );
    assert_eq!(
        bin(BinOp::RotL, &b(7, 0b0010110), &b(7, 7)),
        b(7, 0b0010110)
    );
}

#[test]
fn pdep_pext_inverse_exhaustive() {
    for w in 1..=8u16 {
        for x in 0..(1u128 << w) {
            for m in 0..(1u128 << w) {
                let (xv, mv) = (b(w, x), b(w, m));
                let k = m.count_ones();
                let low = if k == 0 { 0 } else { (1u128 << k) - 1 };
                let dep = bin(BinOp::Pdep, &xv, &mv);
                assert_eq!(bin(BinOp::Pext, &dep, &mv), b(w, x & low));
                let ext = bin(BinOp::Pext, &xv, &mv);
                assert_eq!(bin(BinOp::Pdep, &ext, &mv), b(w, x & m));
            }
        }
    }
    // Hand examples: mask bits at 1, 3, 4.
    assert_eq!(
        bin(BinOp::Pdep, &b(5, 0b101), &b(5, 0b11010)),
        b(5, 0b10010)
    );
    assert_eq!(
        bin(BinOp::Pext, &b(5, 0b10110), &b(5, 0b11010)),
        b(5, 0b101)
    );
}

// --- hand-computed wide examples --------------------------------------------------------------

#[test]
fn wide_multiplication() {
    // W = 128.
    let o = ones(128);
    assert_eq!(val(&bin(BinOp::UMulHi, &o, &o)), u128::MAX - 1);
    assert_eq!(bin(BinOp::Mul, &o, &o), b(128, 1));
    assert_eq!(
        bin(BinOp::Mul, &pow2(128, 127), &b(128, 2)),
        Bits::zero(128)
    );
    assert_eq!(bin(BinOp::SMulHi, &o, &o), Bits::zero(128)); // (-1)(-1) = 1
    assert_eq!(bin(BinOp::SMulHi, &smin(128), &smin(128)), pow2(128, 126)); // 2^254
    assert_eq!(bin(BinOp::SMulHi, &smin(128), &b(128, 1)), o); // -2^127 fills the high half
    let smax = b(128, u128::MAX >> 1);
    // (2^127 - 1)^2 = (2^126 - 1) * 2^128 + 1.
    assert_eq!(val(&bin(BinOp::SMulHi, &smax, &smax)), (1u128 << 126) - 1);
    assert_eq!(bin(BinOp::Mul, &smax, &smax), b(128, 1));
    assert_eq!(bin(BinOp::UMulHi, &pow2(128, 127), &b(128, 2)), b(128, 1));

    // W = 129: (2^129 - 1)^2 = 2^258 - 2^130 + 1, high half = 2^129 - 2.
    let o129 = ones(129);
    assert_eq!(
        bin(BinOp::UMulHi, &o129, &o129),
        Bits::from_limbs(129, &[u64::MAX - 1, u64::MAX, 1])
    );
    assert_eq!(bin(BinOp::Mul, &o129, &o129), b(129, 1));

    // W = 512: (2^256 + 1)(2^256 - 1) = 2^512 - 1.
    let p = bin(BinOp::Add, &pow2(512, 256), &b(512, 1));
    let q = Bits::from_limbs(512, &[u64::MAX; 4]);
    assert_eq!(bin(BinOp::Mul, &p, &q), ones(512));
    assert_eq!(bin(BinOp::UMulHi, &p, &q), Bits::zero(512));
    let mut hi = vec![u64::MAX; 8];
    hi[0] = u64::MAX - 1;
    assert_eq!(
        bin(BinOp::UMulHi, &ones(512), &ones(512)),
        Bits::from_limbs(512, &hi)
    );
}

#[test]
fn wide_division() {
    let o = ones(512);
    let q = Bits::from_limbs(512, &[u64::MAX; 4]); // 2^256 - 1
    let p = Bits::from_limbs(512, &[1, 0, 0, 0, 1]); // 2^256 + 1
    assert_eq!(bin(BinOp::UDiv, &o, &p), q);
    assert_eq!(bin(BinOp::URem, &o, &p), Bits::zero(512));
    assert_eq!(bin(BinOp::UDiv, &o, &pow2(512, 256)), q);
    assert_eq!(bin(BinOp::URem, &o, &pow2(512, 256)), q);
    assert_eq!(bin(BinOp::UDiv, &o, &Bits::zero(512)), o);
    assert_eq!(bin(BinOp::URem, &q, &Bits::zero(512)), q);
    assert_eq!(bin(BinOp::UDiv, &q, &o), Bits::zero(512));
    assert_eq!(bin(BinOp::URem, &q, &o), q);

    // Signed, truncating, remainder follows the dividend.
    for w in [128u16, 129, 512] {
        let cases = [
            (-7, 2, -3, -1),
            (7, -2, -3, 1),
            (-7, -2, 3, -1),
            (7, 2, 3, 1),
        ];
        for (a, d, qq, rr) in cases {
            assert_eq!(
                bin(BinOp::SDiv, &i(w, a), &i(w, d)),
                i(w, qq),
                "w={w} {a}/{d}"
            );
            assert_eq!(
                bin(BinOp::SRem, &i(w, a), &i(w, d)),
                i(w, rr),
                "w={w} {a}%{d}"
            );
        }
        assert_eq!(bin(BinOp::SDiv, &smin(w), &i(w, -1)), smin(w));
        assert_eq!(bin(BinOp::SRem, &smin(w), &i(w, -1)), Bits::zero(w));
        assert_eq!(bin(BinOp::SDiv, &i(w, -5), &Bits::zero(w)), b(w, 1));
        assert_eq!(bin(BinOp::SDiv, &i(w, 5), &Bits::zero(w)), ones(w));
        assert_eq!(bin(BinOp::SRem, &i(w, -5), &Bits::zero(w)), i(w, -5));
        // smin / 2 = -2^(w-2).
        assert_eq!(
            bin(BinOp::SDiv, &smin(w), &b(w, 2)),
            neg(&pow2(w, w - 2)),
            "w={w}"
        );
    }
    // 2^128 - 1 at W = 129 divided by 3.
    let x = Bits::from_limbs(129, &[u64::MAX, u64::MAX]);
    assert_eq!(val(&bin(BinOp::UDiv, &x, &b(129, 3))), u128::MAX / 3);
}

fn neg(x: &Bits) -> Bits {
    un(UnOp::Neg, x).unwrap()
}

#[test]
fn wide_shifts_and_rotates() {
    let w = 512;
    let one = b(w, 1);
    let sm = smin(w);
    let smax = un(UnOp::Not, &sm).unwrap();
    let sh = |op, x: &Bits, c: u128| bin(op, x, &b(w, c));
    assert_eq!(sh(BinOp::Shl, &one, 511), sm);
    assert_eq!(sh(BinOp::Shl, &one, 512), Bits::zero(w));
    assert_eq!(sh(BinOp::Shl, &one, 513), Bits::zero(w));
    assert_eq!(sh(BinOp::LShr, &sm, 511), one);
    assert_eq!(sh(BinOp::LShr, &sm, 512), Bits::zero(w));
    assert_eq!(sh(BinOp::LShr, &sm, 513), Bits::zero(w));
    for c in [511, 512, 513] {
        assert_eq!(sh(BinOp::AShr, &sm, c), ones(w));
    }
    assert_eq!(sh(BinOp::AShr, &smax, 510), one);
    assert_eq!(sh(BinOp::AShr, &smax, 511), Bits::zero(w));
    assert_eq!(sh(BinOp::AShr, &smax, 512), Bits::zero(w));
    assert_eq!(sh(BinOp::AShr, &sm, 1), bin(BinOp::Or, &pow2(w, 510), &sm));
    // A count whose only set bits are far above W still shifts everything out.
    let huge = bin(BinOp::Add, &pow2(w, 300), &one);
    assert_eq!(bin(BinOp::Shl, &one, &huge), Bits::zero(w));
    assert_eq!(bin(BinOp::AShr, &sm, &huge), ones(w));
    // Rotates: 513 mod 512 = 1; (2^300 + 1) mod 512 = 1; (2^9) mod 512 = 0.
    assert_eq!(sh(BinOp::RotL, &one, 513), b(w, 2));
    assert_eq!(sh(BinOp::RotL, &sm, 513), one);
    assert_eq!(sh(BinOp::RotR, &one, 513), sm);
    assert_eq!(bin(BinOp::RotL, &sm, &huge), one);
    assert_eq!(sh(BinOp::RotL, &sm, 512), sm);
    // W = 129, count 2^128: 2^7 = 128 = -1 (mod 129), so 2^128 = (2^7)^18 * 2^2 = 4 (mod 129).
    assert_eq!(bin(BinOp::RotL, &b(129, 1), &pow2(129, 128)), b(129, 16));
}

#[test]
fn byte_and_bit_reversal() {
    assert_eq!(un(UnOp::Bswap, &b(16, 0x1234)), Some(b(16, 0x3412)));
    assert_eq!(un(UnOp::Bswap, &b(24, 0x123456)), Some(b(24, 0x563412)));
    assert_eq!(un(UnOp::Bswap, &b(8, 0xa5)), Some(b(8, 0xa5)));
    for w in [1u16, 7, 12, 129, 513] {
        assert_eq!(un(UnOp::Bswap, &b(w, 1)), None);
    }
    let x = Bits::from_limbs(512, &[0x0102_0304_0506_0708]);
    let mut want = [0u64; 8];
    want[7] = 0x0807_0605_0403_0201;
    assert_eq!(un(UnOp::Bswap, &x), Some(Bits::from_limbs(512, &want)));
    assert_eq!(un(UnOp::BitRev, &b(5, 0b00011)), Some(b(5, 0b11000)));
    assert_eq!(un(UnOp::BitRev, &b(1, 1)), Some(b(1, 1)));
    assert_eq!(un(UnOp::BitRev, &b(129, 1)), Some(pow2(129, 128)));
}

#[test]
fn extension_extract_concat_select() {
    let x = b(8, 0x9c);
    assert_eq!(zext(&x, 8), x);
    assert_eq!(sext(&x, 8), x);
    assert_eq!(zext(&x, 16), b(16, 0x9c));
    assert_eq!(sext(&x, 16), b(16, 0xff9c));
    assert_eq!(sext(&b(8, 0x7c), 16), b(16, 0x7c));
    assert_eq!(sext(&x, 1024), i(1024, -100));
    assert_eq!(extract(&x, 2, 4), b(4, 0x7));
    assert_eq!(extract(&x, 0, 8), x);
    assert_eq!(extract(&x, 7, 1), b(1, 1));
    assert_eq!(concat(&b(4, 0xa), &b(8, 0x5c)), b(12, 0xa5c));
    assert_eq!(concat(&ones(512), &Bits::zero(512)).width(), 1024);
    let (t, f) = (b(8, 1), b(8, 2));
    assert_eq!(select(&b(1, 1), &t, &f), t);
    assert_eq!(select(&b(1, 0), &t, &f), f);
}

#[test]
fn signed_comparisons_wide() {
    let w = 512;
    let m1 = ones(w);
    let z = Bits::zero(w);
    assert!(cmp(CmpOp::Slt, &m1, &z));
    assert!(cmp(CmpOp::Ugt, &m1, &z));
    assert!(cmp(CmpOp::Slt, &smin(w), &m1));
    assert!(cmp(CmpOp::Sle, &m1, &m1));
    assert!(!cmp(CmpOp::Sgt, &m1, &m1));
    assert!(cmp(CmpOp::Sge, &z, &smin(w)));
    assert!(cmp(CmpOp::Ne, &z, &m1));
}

#[test]
fn term_evaluation() {
    let x = || Box::new(Term::Var(0, 8));
    let y = || Box::new(Term::Var(1, 8));
    // (x + 1) == y
    let t = Term::Cmp(
        CmpOp::Eq,
        Box::new(Term::Bin(BinOp::Add, x(), Box::new(Term::Const(b(8, 1))))),
        y(),
    );
    assert_eq!(t.width(), 1);
    assert_eq!(t.eval(&[b(8, 0xff), b(8, 0)]), Some(b(1, 1)));
    assert_eq!(t.eval(&[b(8, 3), b(8, 5)]), Some(b(1, 0)));

    // select(x <s 0, concat(extract(x, 4, 4), 0x03), sext(popcnt x, 12))
    let t2 = Term::Select(
        Box::new(Term::Cmp(
            CmpOp::Slt,
            x(),
            Box::new(Term::Const(Bits::zero(8))),
        )),
        Box::new(Term::Concat(
            Box::new(Term::Extract(x(), 4, 4)),
            Box::new(Term::Const(b(8, 0x3))),
        )),
        Box::new(Term::Sext(Box::new(Term::Un(UnOp::Popcnt, x())), 12)),
    );
    assert_eq!(t2.width(), 12);
    assert_eq!(t2.eval(&[b(8, 0xa1)]), Some(b(12, 0xa03)));
    assert_eq!(t2.eval(&[b(8, 0x71)]), Some(b(12, 4)));
    let t3 = Term::Zext(Box::new(Term::Un(UnOp::Neg, y())), 16);
    assert_eq!(t3.eval(&[b(8, 0), b(8, 1)]), Some(b(16, 0xff)));

    // An invalid Bswap anywhere makes the whole evaluation None.
    let bad = Term::Bin(
        BinOp::Add,
        Box::new(Term::Un(UnOp::Bswap, Box::new(Term::Const(b(12, 0))))),
        Box::new(Term::Const(b(12, 0))),
    );
    assert_eq!(bad.width(), 12);
    assert_eq!(bad.eval(&[]), None);
}
