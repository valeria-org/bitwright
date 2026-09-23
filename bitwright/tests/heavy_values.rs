//! Values at the edges: every operator, comparison and cast at boundary values of widths around
//! every representation boundary (1 to 512 bits), against the bit-serial reference; the SMT-LIB
//! special cases (division by zero and by −1, `smin / −1`, out-of-range shift and rotate
//! counts, empty and full `pdep`/`pext` masks, high products at the extremes) against closed
//! forms; and the same operators built as expressions, where construction-time folding and
//! identities with a constant operand take their own code paths.
//!
//! The library's unit tests already check the kernels exhaustively to 8 bits and on random
//! boundary-biased pairs; this suite adds the deterministic boundary × boundary cross product
//! at every interesting width, and the expression layer.

mod common;

use bitwright::{BinOp, BitVec, CmpOpExt, Context, Expr, SymbolKey, UnOp, Width, WidthError};
use bitwright_ref as r;
use common::{
    SMOKE_WIDTHS, Size, WIDTHS, boundary_values, core_values, from_ref, ones_range, pow2, ref_bin,
    ref_cmp, ref_un, to_ref, w,
};

fn widths(size: Size) -> Vec<u16> {
    size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec())
}

/// The values crossed with each other at a width: the full boundary list in heavy runs, a
/// shorter one in smoke runs (shorter still above 64 bits, where the reference is slow).
fn values(size: Size, width: Width) -> Vec<BitVec> {
    match size {
        Size::Smoke if width.bits() > 64 => core_values(width)[..6].to_vec(),
        Size::Smoke => core_values(width),
        Size::Heavy => boundary_values(width),
    }
}

// ----- the value kernels at boundary values -------------------------------------------------

fn check_un(op: UnOp, a: &BitVec) {
    let got = BitVec::apply_un(op, a);
    match r::un(ref_un(op), &to_ref(a)) {
        None => assert_eq!(
            got,
            Err(WidthError::NotByteMultiple {
                bits: a.width().bits()
            }),
            "{op:?}({a})"
        ),
        Some(want) => assert_eq!(got, Ok(from_ref(&want)), "{op:?}({a})"),
    }
}

fn check_bin(op: BinOp, a: &BitVec, b: &BitVec) {
    let want = from_ref(&r::bin(ref_bin(op), &to_ref(a), &to_ref(b)));
    assert_eq!(BitVec::apply_bin(op, a, b), Ok(want), "{op:?}({a}, {b})");
}

fn check_cmp(op: CmpOpExt, a: &BitVec, b: &BitVec) {
    let want = r::cmp(ref_cmp(op), &to_ref(a), &to_ref(b));
    assert_eq!(BitVec::apply_cmp(op, a, b), Ok(want), "{op:?}({a}, {b})");
}

fn boundary_operators(size: Size) {
    for n in widths(size) {
        let width = w(n);
        let vals = values(size, width);
        for a in &vals {
            for op in UnOp::ALL {
                check_un(op, a);
            }
            for b in &vals {
                for op in BinOp::ALL {
                    check_bin(op, a, b);
                }
                for op in CmpOpExt::ALL {
                    check_cmp(op, a, b);
                }
                for c in [false, true] {
                    let want = if c { a } else { b };
                    assert_eq!(
                        BitVec::select(&BitVec::from_bool(c), a, b),
                        Ok(*want),
                        "select({c}, {a}, {b})"
                    );
                }
            }
        }
    }
}

#[test]
fn boundary_operators_match_reference_smoke() {
    boundary_operators(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn boundary_operators_match_reference_heavy() {
    boundary_operators(Size::Heavy);
}

/// Extract offsets that straddle limbs and the native paths.
fn extract_offsets(n: u16) -> Vec<u16> {
    let mut v: Vec<u16> = [
        0, 1, 31, 32, 33, 62, 63, 64, 65, 127, 128, 129, 191, 255, 256, 257,
    ]
    .into_iter()
    .chain([n / 2, n.saturating_sub(1), n.saturating_sub(64)])
    .filter(|&lo| lo < n)
    .collect();
    v.sort_unstable();
    v.dedup();
    v
}

fn extract_lengths(n: u16) -> Vec<u16> {
    let mut v: Vec<u16> = [1, 2, 31, 63, 64, 65, 127, 128, 129, 256, 511]
        .into_iter()
        .chain([n, n.saturating_sub(1)])
        .filter(|&len| (1..=n).contains(&len))
        .collect();
    v.sort_unstable();
    v.dedup();
    v
}

fn boundary_casts(size: Size) {
    let all = widths(size);
    // Extension and truncation targets: every width in heavy runs.
    let targets: Vec<u16> = size.pick(all.clone(), (1..=512).collect());
    for &n in &all {
        let width = w(n);
        let vals = values(size, width);
        for a in &vals {
            let ra = to_ref(a);
            for &to in targets.iter().filter(|&&to| to >= n) {
                let tw = w(to);
                assert_eq!(
                    a.zext(tw),
                    Ok(from_ref(&r::zext(&ra, to))),
                    "zext<{to}>({a})"
                );
                assert_eq!(
                    a.sext(tw),
                    Ok(from_ref(&r::sext(&ra, to))),
                    "sext<{to}>({a})"
                );
            }
            for &to in targets.iter().filter(|&&to| to < n) {
                assert!(a.zext(w(to)).is_err(), "zext<{to}>({a}) narrows");
                assert_eq!(
                    a.trunc(w(to)),
                    Ok(from_ref(&r::extract(&ra, 0, to))),
                    "trunc<{to}>({a})"
                );
            }
            for lo in extract_offsets(n) {
                for len in extract_lengths(n) {
                    let got = a.extract(lo, w(len));
                    if u32::from(lo) + u32::from(len) > u32::from(n) {
                        assert!(got.is_err(), "extract<{lo}, {len}>({a}) is out of range");
                    } else {
                        assert_eq!(
                            got,
                            Ok(from_ref(&r::extract(&ra, lo, len))),
                            "extract<{lo}, {len}>({a})"
                        );
                    }
                }
            }
            // Concatenation with a few values of every width that fits.
            for &lw in &all {
                let lwidth = w(lw);
                let lows = core_values(lwidth);
                for l in lows.iter().take(size.pick(2, 5)) {
                    let got = BitVec::concat(a, l);
                    if u32::from(n) + u32::from(lw) > 512 {
                        assert!(got.is_err(), "concat({a}, {l}) is wider than 512 bits");
                    } else {
                        assert_eq!(
                            got,
                            Ok(from_ref(&r::concat(&ra, &to_ref(l)))),
                            "concat({a}, {l})"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn boundary_casts_match_reference_smoke() {
    boundary_casts(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn boundary_casts_match_reference_heavy() {
    boundary_casts(Size::Heavy);
}

// ----- the special cases against closed forms -----------------------------------------------

fn un(op: UnOp, a: &BitVec) -> BitVec {
    BitVec::apply_un(op, a).unwrap()
}

fn bin(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::apply_bin(op, a, b).unwrap()
}

/// `c mod m` for a value of any width, by Horner over its bits.
fn value_mod(c: &BitVec, m: u16) -> u16 {
    (0..c.width().bits()).rev().fold(0u32, |acc, i| {
        (2 * acc + u32::from(c.bit(i).unwrap())) % u32::from(m)
    }) as u16
}

/// `x` with its bits moved by `f(i)`: result bit `i` is source bit `f(i)`, or 0 for `None`.
fn permute(x: &BitVec, f: impl Fn(u16) -> Option<u16>) -> BitVec {
    let n = x.width().bits();
    let mut l = [0u64; 8];
    for i in 0..n {
        if f(i).is_some_and(|j| x.bit(j) == Some(true)) {
            l[usize::from(i / 64)] |= 1 << (i % 64);
        }
    }
    BitVec::wrapping_from_limbs(x.width(), &l)
}

/// The SMT-LIB special cases at one width, against closed forms computed without the kernels'
/// arithmetic (bit moves and constants only).
fn special_cases_at(n: u16) {
    let width = w(n);
    let zero = BitVec::zero(width);
    let one = BitVec::one(width);
    let ones = BitVec::ones(width);
    let smin = BitVec::smin(width);
    let smax = BitVec::smax(width);
    let count = |c: u64| BitVec::wrapping_from_u64(width, c);
    let wv = count(u64::from(n));
    for x in boundary_values(width) {
        let neg_x = un(UnOp::Neg, &x);
        // Division and remainder by zero, one, and all ones (−1).
        assert!(bin(BinOp::UDiv, &x, &zero).is_ones(), "udiv({x}, 0)");
        assert_eq!(bin(BinOp::URem, &x, &zero), x, "urem({x}, 0)");
        let sdiv0 = if x.msb() { one } else { ones };
        assert_eq!(bin(BinOp::SDiv, &x, &zero), sdiv0, "sdiv({x}, 0)");
        assert_eq!(bin(BinOp::SRem, &x, &zero), x, "srem({x}, 0)");
        for op in [BinOp::UDiv, BinOp::SDiv] {
            assert_eq!(bin(op, &x, &one), x, "{op:?}({x}, 1)");
        }
        for op in [BinOp::URem, BinOp::SRem] {
            assert!(bin(op, &x, &one).is_zero(), "{op:?}({x}, 1)");
        }
        let (q, rem) = if x.is_ones() { (one, zero) } else { (zero, x) };
        assert_eq!(bin(BinOp::UDiv, &x, &ones), q, "udiv({x}, ones)");
        assert_eq!(bin(BinOp::URem, &x, &ones), rem, "urem({x}, ones)");
        // sdiv by −1 is negation, smin / −1 = smin included; srem by −1 is 0.
        assert_eq!(bin(BinOp::SDiv, &x, &ones), neg_x, "sdiv({x}, -1)");
        assert!(bin(BinOp::SRem, &x, &ones).is_zero(), "srem({x}, -1)");
        assert_eq!(
            bin(BinOp::UDiv, &x, &x),
            if x.is_zero() { ones } else { one },
            "udiv({x}, {x})"
        );
        // Shifts by 0, W − 1, W, W + 1, 2W and huge counts.
        for op in [
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
            BinOp::RotL,
            BinOp::RotR,
        ] {
            assert_eq!(bin(op, &x, &zero), x, "{op:?}({x}, 0)");
        }
        let top = n - 1;
        assert_eq!(
            bin(BinOp::Shl, &x, &count(u64::from(top))),
            permute(&x, |i| (i == top).then_some(0)),
            "shl({x}, W-1)"
        );
        assert_eq!(
            bin(BinOp::LShr, &x, &count(u64::from(top))),
            permute(&x, |i| (i == 0).then_some(top)),
            "lshr({x}, W-1)"
        );
        let fill = if x.msb() { ones } else { zero };
        assert_eq!(
            bin(BinOp::AShr, &x, &count(u64::from(top))),
            fill,
            "ashr({x}, W-1)"
        );
        let mut huge = vec![count(u64::from(n)), count(u64::from(n) + 1), ones, smin];
        if n > 64 {
            huge.push(BitVec::wrapping_from_limbs(width, &[1, 1])); // 2^64 + 1
            huge.push(pow2(width, n - 1));
        }
        for c in &huge {
            // A count >= W (n + 1 wraps below W only at W = 1, where it is 0).
            if c.to_u64().is_some_and(|v| v < u64::from(n)) {
                continue;
            }
            assert!(bin(BinOp::Shl, &x, c).is_zero(), "shl({x}, {c})");
            assert!(bin(BinOp::LShr, &x, c).is_zero(), "lshr({x}, {c})");
            assert_eq!(bin(BinOp::AShr, &x, c), fill, "ashr({x}, {c})");
        }
        for c in huge.iter().chain([&count(2 * u64::from(n) + 1), &wv]) {
            let m = value_mod(c, n);
            let rotl = permute(&x, |i| Some((i + n - m) % n));
            let rotr = permute(&x, |i| Some((i + m) % n));
            assert_eq!(
                bin(BinOp::RotL, &x, c),
                rotl,
                "rotl({x}, {c}) = rotl by {m}"
            );
            assert_eq!(
                bin(BinOp::RotR, &x, c),
                rotr,
                "rotr({x}, {c}) = rotr by {m}"
            );
        }
        // pdep and pext with the empty and the full mask.
        for op in [BinOp::Pdep, BinOp::Pext] {
            assert_eq!(bin(op, &x, &ones), x, "{op:?}({x}, ones)");
            assert!(bin(op, &x, &zero).is_zero(), "{op:?}({x}, 0)");
        }
        assert_eq!(bin(BinOp::Pdep, &ones, &x), x, "pdep(ones, {x})");
        let pop = un(UnOp::Popcnt, &x).to_u64().unwrap() as u16;
        assert_eq!(
            bin(BinOp::Pext, &x, &x),
            ones_range(width, 0, pop),
            "pext({x}, {x})"
        );
        // High products against 1, 0 and themselves.
        assert!(bin(BinOp::UMulHi, &x, &one).is_zero(), "umulhi({x}, 1)");
        if n >= 2 {
            // (At one bit, 1 is −1.)
            assert_eq!(bin(BinOp::SMulHi, &x, &one), fill, "smulhi({x}, 1)");
        }
        assert!(bin(BinOp::UMulHi, &x, &zero).is_zero(), "umulhi({x}, 0)");
        assert!(bin(BinOp::SMulHi, &x, &zero).is_zero(), "smulhi({x}, 0)");
        // umulhi(x, ones) = x - 1 for x != 0 (x * (2^W - 1) = x * 2^W - x).
        let want = if x.is_zero() {
            zero
        } else {
            bin(BinOp::Sub, &x, &one)
        };
        assert_eq!(bin(BinOp::UMulHi, &x, &ones), want, "umulhi({x}, ones)");
        // smulhi(x, -1) is the high half of -x as a 2W-bit value: 0 for x <= 0 except smin,
        // whose negation 2^(W-1) is positive too; ones for x > 0.
        let positive = !x.msb() && !x.is_zero();
        let want = if positive { ones } else { zero };
        assert_eq!(bin(BinOp::SMulHi, &x, &ones), want, "smulhi({x}, -1)");
    }
    // Fixed points of the extremes.
    assert_eq!(un(UnOp::Neg, &smin), smin, "neg(smin)");
    assert_eq!(un(UnOp::Not, &smin), smax, "not(smin)");
    assert_eq!(bin(BinOp::SDiv, &smin, &ones), smin, "sdiv(smin, -1)");
    assert!(bin(BinOp::SRem, &smin, &ones).is_zero(), "srem(smin, -1)");
    assert_eq!(bin(BinOp::Mul, &smin, &ones), smin, "smin * -1");
    let umax_sq = bin(BinOp::Sub, &ones, &one);
    assert_eq!(
        bin(BinOp::UMulHi, &ones, &ones),
        umax_sq,
        "umulhi(ones, ones)"
    );
    assert!(bin(BinOp::SMulHi, &ones, &ones).is_zero(), "smulhi(-1, -1)");
    let smin_sq = if n >= 2 { pow2(width, n - 2) } else { zero };
    assert_eq!(
        bin(BinOp::SMulHi, &smin, &smin),
        smin_sq,
        "smulhi(smin, smin)"
    );
    assert_eq!(
        bin(BinOp::UMulHi, &smin, &smin),
        if n >= 2 { pow2(width, n - 2) } else { zero }
    );
    // smin * smax = -2^(2W-2) + 2^(W-1): high half is -2^(W-2) (all ones above bit W-2).
    if n >= 2 {
        let want = un(UnOp::Neg, &pow2(width, n - 2));
        assert_eq!(bin(BinOp::SMulHi, &smin, &smax), want, "smulhi(smin, smax)");
    }
    // Counts.
    assert_eq!(un(UnOp::Clz, &zero), wv, "clz(0)");
    assert_eq!(un(UnOp::Ctz, &zero), wv, "ctz(0)");
    assert_eq!(un(UnOp::Popcnt, &ones), wv, "popcnt(ones)");
    assert!(un(UnOp::Clz, &smin).is_zero(), "clz(smin)");
    assert_eq!(un(UnOp::Ctz, &smin), count(u64::from(n - 1)), "ctz(smin)");
    assert_eq!(un(UnOp::Clz, &one), count(u64::from(n - 1)), "clz(1)");
    assert_eq!(un(UnOp::BitRev, &one), smin, "bitrev(1)");
    if n.is_multiple_of(8) {
        assert_eq!(un(UnOp::Bswap, &one), pow2(width, n - 8), "bswap(1)");
        assert_eq!(un(UnOp::Bswap, &smin), pow2(width, 7), "bswap(smin)");
    } else {
        assert!(
            BitVec::apply_un(UnOp::Bswap, &one).is_err(),
            "bswap at {n} bits"
        );
    }
}

fn special_cases(size: Size) {
    let all: Vec<u16> = size.pick(WIDTHS.to_vec(), (1..=512).collect());
    for n in all {
        special_cases_at(n);
    }
}

#[test]
fn special_cases_are_exact_smoke() {
    special_cases(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn special_cases_are_exact_heavy() {
    special_cases(Size::Heavy);
}

// ----- the same operators built as expressions ------------------------------------------------

/// Which value computes an expected result: the bit-serial reference, or the value kernels
/// (used at wide widths, where `boundary_operators_match_reference_*` has already checked the
/// kernels against the reference on exactly the same value pairs).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Oracle {
    Reference,
    Kernels,
}

/// An operand of a shape: the symbol `x`, the symbol `y`, or a constant.
#[derive(Clone, Debug)]
enum Arg {
    X,
    Y,
    C(BitVec),
}

/// An expression shape over `x`, `y` (`W` bits) and `p` (1 bit).
#[derive(Clone, Debug)]
enum Shape {
    Un(UnOp),
    Bin(BinOp, Arg, Arg),
    Cmp(CmpOpExt, Arg, Arg),
    /// `select(p, a, b)`.
    Select(Arg, Arg),
    Zext(u16),
    Sext(u16),
    Extract(u16, u16),
    /// `concat(x, y)`.
    Concat,
}

fn build(cx: &mut Context, shape: &Shape, x: Expr, y: Expr, p: Expr) -> Expr {
    let arg = |cx: &mut Context, a: &Arg| match a {
        Arg::X => x,
        Arg::Y => y,
        Arg::C(c) => cx.constant(c).unwrap(),
    };
    match shape {
        Shape::Un(op) => cx.un(*op, x).unwrap(),
        Shape::Bin(op, a, b) => {
            let (a, b) = (arg(cx, a), arg(cx, b));
            cx.bin(*op, a, b).unwrap()
        }
        Shape::Cmp(op, a, b) => {
            let (a, b) = (arg(cx, a), arg(cx, b));
            cx.cmp(*op, a, b).unwrap()
        }
        Shape::Select(a, b) => {
            let (a, b) = (arg(cx, a), arg(cx, b));
            cx.select(p, a, b).unwrap()
        }
        Shape::Zext(to) => cx.zext(x, w(*to)).unwrap(),
        Shape::Sext(to) => cx.sext(x, w(*to)).unwrap(),
        Shape::Extract(lo, len) => cx.extract(x, *lo, w(*len)).unwrap(),
        Shape::Concat => cx.concat(x, y).unwrap(),
    }
}

fn expected(shape: &Shape, x: &BitVec, y: &BitVec, p: bool, oracle: Oracle) -> BitVec {
    let val = |a: &Arg| match a {
        Arg::X => *x,
        Arg::Y => *y,
        Arg::C(c) => *c,
    };
    let pv = BitVec::from_bool(p);
    match oracle {
        Oracle::Kernels => match shape {
            Shape::Un(op) => un(*op, x),
            Shape::Bin(op, a, b) => bin(*op, &val(a), &val(b)),
            Shape::Cmp(op, a, b) => {
                BitVec::from_bool(BitVec::apply_cmp(*op, &val(a), &val(b)).unwrap())
            }
            Shape::Select(a, b) => BitVec::select(&pv, &val(a), &val(b)).unwrap(),
            Shape::Zext(to) => x.zext(w(*to)).unwrap(),
            Shape::Sext(to) => x.sext(w(*to)).unwrap(),
            Shape::Extract(lo, len) => x.extract(*lo, w(*len)).unwrap(),
            Shape::Concat => BitVec::concat(x, y).unwrap(),
        },
        Oracle::Reference => {
            let rv = |a: &Arg| to_ref(&val(a));
            let rx = to_ref(x);
            from_ref(&match shape {
                Shape::Un(op) => r::un(ref_un(*op), &rx).unwrap(),
                Shape::Bin(op, a, b) => r::bin(ref_bin(*op), &rv(a), &rv(b)),
                Shape::Cmp(op, a, b) => {
                    r::Bits::from_bools(vec![r::cmp(ref_cmp(*op), &rv(a), &rv(b))])
                }
                Shape::Select(a, b) => r::select(&to_ref(&pv), &rv(a), &rv(b)),
                Shape::Zext(to) => r::zext(&rx, *to),
                Shape::Sext(to) => r::sext(&rx, *to),
                Shape::Extract(lo, len) => r::extract(&rx, *lo, *len),
                Shape::Concat => r::concat(&rx, &to_ref(y)),
            })
        }
    }
}

/// Every shape at width `n`: each operator over `x` and every constant (both sides), `x op x`,
/// `x op y`, the unary and comparison forms, selects, and casts across the limb boundaries.
/// Construction folds constants and applies identities (`x udiv 1`, shifts by a constant
/// `>= W`, `rotr` by a constant, `x - c`, reflexive compares, …), so each shape exercises a
/// different construction path.
fn shapes(n: u16, consts: &[BitVec]) -> Vec<Shape> {
    let mut v = Vec::new();
    for op in UnOp::ALL {
        if op != UnOp::Bswap || n.is_multiple_of(8) {
            v.push(Shape::Un(op));
        }
    }
    for op in BinOp::ALL {
        v.push(Shape::Bin(op, Arg::X, Arg::Y));
        v.push(Shape::Bin(op, Arg::X, Arg::X));
        for c in consts {
            v.push(Shape::Bin(op, Arg::X, Arg::C(*c)));
            v.push(Shape::Bin(op, Arg::C(*c), Arg::X));
        }
    }
    for op in CmpOpExt::ALL {
        v.push(Shape::Cmp(op, Arg::X, Arg::Y));
        v.push(Shape::Cmp(op, Arg::X, Arg::X));
        for c in consts {
            v.push(Shape::Cmp(op, Arg::X, Arg::C(*c)));
            v.push(Shape::Cmp(op, Arg::C(*c), Arg::X));
        }
    }
    v.push(Shape::Select(Arg::X, Arg::Y));
    v.push(Shape::Select(Arg::X, Arg::X));
    for c in consts.iter().take(4) {
        v.push(Shape::Select(Arg::X, Arg::C(*c)));
        v.push(Shape::Select(Arg::C(*c), Arg::X));
    }
    for to in [n + 1, n + 63, n + 64, n + 65, 2 * n, 512] {
        if n < to && to <= 512 {
            v.push(Shape::Zext(to));
            v.push(Shape::Sext(to));
        }
    }
    for lo in extract_offsets(n) {
        for len in extract_lengths(n) {
            if lo + len <= n {
                v.push(Shape::Extract(lo, len));
            }
        }
    }
    if n <= 256 {
        v.push(Shape::Concat);
    }
    v
}

/// Builds every shape at width `n` and evaluates all of them at every `x` of `xs`, with `y`
/// from the first few of `xs` and `p` both ways.
fn expressions_at(n: u16, consts: &[BitVec], xs: &[BitVec], oracle: Oracle) {
    let width = w(n);
    let mut cx = Context::new();
    let x = cx.symbol("x", width).unwrap();
    let y = cx.symbol("y", width).unwrap();
    let p = cx.symbol("p", Width::W1).unwrap();
    if !n.is_multiple_of(8) {
        assert!(cx.un(UnOp::Bswap, x).is_err(), "bswap at {n} bits");
    }
    let shapes = shapes(n, consts);
    let roots: Vec<Expr> = shapes.iter().map(|s| build(&mut cx, s, x, y, p)).collect();
    let ys = &xs[..xs.len().min(if xs.len() > 16 { 3 } else { 16 })];
    for vx in xs {
        for vy in ys {
            for vp in [false, true] {
                let env = [
                    (SymbolKey::from("x"), *vx),
                    (SymbolKey::from("y"), *vy),
                    (SymbolKey::from("p"), BitVec::from_bool(vp)),
                ];
                let got = cx.eval(&roots, &env[..]).unwrap();
                for ((shape, root), g) in shapes.iter().zip(&roots).zip(&got) {
                    let want = expected(shape, vx, vy, vp, oracle);
                    assert_eq!(
                        *g,
                        want,
                        "{n} bits: {shape:?} built as `{}`, at x = {vx}, y = {vy}, p = {vp}",
                        cx.display(*root)
                    );
                }
            }
        }
    }
}

fn every_value(n: u16) -> Vec<BitVec> {
    (0..1u64 << n)
        .map(|v| BitVec::wrapping_from_u64(w(n), v))
        .collect()
}

/// Every constant and every operand value at the small widths.
fn exhaustive_expressions(size: Size) {
    for n in 1..=size.pick(3, 7) {
        let all = every_value(n);
        expressions_at(n, &all, &all, Oracle::Reference);
    }
}

#[test]
fn small_widths_through_expressions_smoke() {
    exhaustive_expressions(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn small_widths_through_expressions_heavy() {
    exhaustive_expressions(Size::Heavy);
}

/// Boundary constants and operand values at the wide widths.
fn boundary_expressions(size: Size) {
    for n in widths(size) {
        let width = w(n);
        let vals = values(size, width);
        let oracle = if n <= 64 {
            Oracle::Reference
        } else {
            Oracle::Kernels
        };
        expressions_at(n, &vals, &vals, oracle);
    }
}

#[test]
fn boundary_values_through_expressions_smoke() {
    boundary_expressions(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn boundary_values_through_expressions_heavy() {
    boundary_expressions(Size::Heavy);
}

// ----- constant folding --------------------------------------------------------------------

/// Every operator on two constants folds at construction to the reference value.
fn constant_folding(size: Size) {
    for n in widths(size) {
        let width = w(n);
        let vals = values(size, width);
        let mut cx = Context::new();
        for a in &vals {
            let ea = cx.constant(a).unwrap();
            for op in UnOp::ALL {
                if let Some(want) = r::un(ref_un(op), &to_ref(a)) {
                    let e = cx.un(op, ea).unwrap();
                    assert_eq!(
                        cx.as_const(e).unwrap(),
                        Some(from_ref(&want)),
                        "{op:?}({a})"
                    );
                }
            }
            for b in &vals {
                let eb = cx.constant(b).unwrap();
                for op in BinOp::ALL {
                    let e = cx.bin(op, ea, eb).unwrap();
                    let want = from_ref(&r::bin(ref_bin(op), &to_ref(a), &to_ref(b)));
                    assert_eq!(cx.as_const(e).unwrap(), Some(want), "{op:?}({a}, {b})");
                }
                for op in CmpOpExt::ALL {
                    let e = cx.cmp(op, ea, eb).unwrap();
                    let want = BitVec::from_bool(r::cmp(ref_cmp(op), &to_ref(a), &to_ref(b)));
                    assert_eq!(cx.as_const(e).unwrap(), Some(want), "{op:?}({a}, {b})");
                }
            }
        }
    }
}

#[test]
fn constants_fold_to_the_reference_smoke() {
    constant_folding(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn constants_fold_to_the_reference_heavy() {
    constant_folding(Size::Heavy);
}

// ----- text form of values -----------------------------------------------------------------

/// Every boundary value prints and parses back at every width, in its display form, in hex, and
/// (when negative) as a negated magnitude; one past the largest value of a width is refused.
fn value_text(size: Size) {
    let all: Vec<u16> = size.pick(WIDTHS.to_vec(), (1..=512).collect());
    for n in all {
        let width = w(n);
        for v in boundary_values(width) {
            let text = v.to_string();
            assert_eq!(BitVec::parse(&text), Ok(v), "{text}");
            assert_eq!(text.parse::<BitVec>(), Ok(v), "{text}");
            let hex = format!("{v:#x}:{n}");
            assert_eq!(BitVec::parse(&hex), Ok(v), "{hex}");
            if v.msb() {
                // `-m` where `m` is the magnitude (smin is its own negation).
                let neg = format!("-{:#x}:{n}", un(UnOp::Neg, &v));
                assert_eq!(BitVec::parse(&neg), Ok(v), "{neg}");
            }
        }
        if n < 512 {
            let too_big = format!("{:#x}:{n}", pow2(w(n + 1), n));
            assert!(BitVec::parse(&too_big).is_err(), "{too_big}");
        }
    }
}

#[test]
fn values_print_and_parse_back_smoke() {
    value_text(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn values_print_and_parse_back_heavy() {
    value_text(Size::Heavy);
}
