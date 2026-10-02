//! Solver-facing workloads: modular arithmetic, models, assumptions, memory aliasing,
//! floating-point classification, and complete SMT-LIB scripts with known verdicts.

use super::*;
use crate::{
    KnownBits,
    memory::{Endian, Memory},
};

fn sat_only() -> Config {
    Config::default()
        .with_simplify(false)
        .with_samples(0)
        .with_certificate(true)
        .with_max_conflicts(100_000)
        .with_max_propagations(20_000_000)
}

fn expect_valid(cx: &mut Context, p: Expr, assumptions: Option<&Assumptions>) {
    match valid_under(cx, p, assumptions, &sat_only()).unwrap() {
        Outcome::Proved(Some(certificate)) => certificate.check().unwrap(),
        other => panic!("{}: {other:?}", cx.display(p)),
    }
}

#[test]
fn modular_arithmetic_identities_and_near_misses_require_the_native_solver() {
    let identities = [
        "(x + y) - y == x",
        "((x ^ y) + 2 * (x & y)) == x + y",
        "(x * 3 == y * 3) == (x == y)",
        "udiv(x, y) * y + urem(x, y) == x",
        "sdiv(x, y) * y + srem(x, y) == x",
        "(x <s y) == ((x ^ 0x8) <u (y ^ 0x8))",
    ];
    // The sign-bias identity's literal is specifically for four-bit operands.
    for bits in [2, 3, 4, 5] {
        let mut cx = Context::new();
        let options = ParseOptions::width(Width::new(bits).unwrap());
        for text in identities {
            if text.contains("0x8") && bits != 4 {
                continue;
            }
            let p = cx.parse(text, &options).unwrap();
            expect_valid(&mut cx, p, None);
        }
        for text in [
            "x + y == x | y",
            "udiv(x, y) * y == x",
            "sdiv(x, y) == udiv(x, y)",
            "(x << y) >>u y == x",
            "(x <s y) == (x <u y)",
        ] {
            let p = cx.parse(text, &options).unwrap();
            let Outcome::Refuted(model) = valid(&mut cx, p, &sat_only()).unwrap() else {
                panic!("{text} at {bits} bits should have a counterexample");
            };
            assert!(cx.eval(&[p], &model[..]).unwrap()[0].is_zero());
        }
    }
}

#[test]
fn unsigned_overflow_and_overshifts_under_path_conditions() {
    for bits in [3, 7, 8, 16, 31, 64, 65] {
        let w = Width::new(bits).unwrap();
        let wide = Width::new(bits + 1).unwrap();
        let mut cx = Context::new();
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let sum = cx.add(x, y).unwrap();
        let overflow = cx.ult(sum, x).unwrap();
        let ex = cx.zext(x, wide).unwrap();
        let ey = cx.zext(y, wide).unwrap();
        let extended = cx.add(ex, ey).unwrap();
        let carry = cx.bit(extended, bits).unwrap();
        let same = cx.eq(overflow, carry).unwrap();
        expect_valid(&mut cx, same, None);

        let limit = cx.constant_u64(w, u64::from(bits)).unwrap();
        let oversized = cx.uge(y, limit).unwrap();
        let mut assumptions = Assumptions::new();
        assumptions.assume_true(&mut cx, oversized).unwrap();
        let zero = cx.zero(w).unwrap();
        for op in [BinOp::Shl, BinOp::LShr] {
            let shifted = cx.bin(op, x, y).unwrap();
            let p = cx.eq(shifted, zero).unwrap();
            expect_valid(&mut cx, p, Some(&assumptions));
        }
        let signed = cx.bin(BinOp::AShr, x, y).unwrap();
        let negative = cx.slt(x, zero).unwrap();
        let ones = cx.ones(w).unwrap();
        let fill = cx.select(negative, ones, zero).unwrap();
        let p = cx.eq(signed, fill).unwrap();
        expect_valid(&mut cx, p, Some(&assumptions));
    }
}

#[test]
fn enumerate_declared_models_until_unsat_in_all_search_modes() {
    for simplify in [false, true] {
        for samples in [0, 256] {
            let mut cx = Context::new();
            let x = cx.symbol("x", Width::W8).unwrap();
            let known = KnownBits::new(
                BitVec::from_u64(Width::W8, 0xf0).unwrap(),
                BitVec::one(Width::W8),
            )
            .unwrap();
            cx.declare_known(x, known).unwrap();
            let upper = cx.constant_u64(Width::W8, 16).unwrap();
            let mut p = cx.ult(x, upper).unwrap();
            // Certificates intentionally bypass simplification; disable them in the engine
            // configurations so this matrix exercises both actual execution paths.
            let cfg = sat_only()
                .with_certificate(!simplify)
                .with_simplify(simplify)
                .with_samples(samples);
            let mut seen = std::collections::BTreeSet::new();
            for _ in 0..8 {
                let model = satisfy(&mut cx, p, &cfg)
                    .unwrap()
                    .unwrap()
                    .expect("an unblocked model");
                assert_eq!(
                    cx.eval(&[p], &model[..]).unwrap()[0],
                    BitVec::from_bool(true)
                );
                let value = model
                    .iter()
                    .find(|(k, _)| *k == SymbolKey::from("x"))
                    .unwrap()
                    .1;
                assert!(known.contains(&value));
                assert!(
                    seen.insert(value.to_u64().unwrap()),
                    "a blocked model was returned"
                );
                let k = cx.constant(&value).unwrap();
                let block = cx.ne(x, k).unwrap();
                p = cx.and(p, block).unwrap();
            }
            assert_eq!(seen, (1..16).step_by(2).collect());
            assert!(satisfy(&mut cx, p, &cfg).unwrap().unwrap().is_none());
            let unsatisfiable = cx.un(UnOp::Not, p).unwrap();
            expect_valid(&mut cx, unsatisfiable, None);
        }
    }
}

#[test]
fn assumption_counterexamples_satisfy_the_path_and_contradictions_are_vacuous() {
    for bits in [1, 4, 8, 65, 128] {
        let mut cx = Context::new();
        let w = Width::new(bits).unwrap();
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let path = cx.ult(x, y).unwrap();
        let mut assumptions = Assumptions::new();
        assumptions.assume_true(&mut cx, path).unwrap();
        let ordering = cx.ule(x, y).unwrap();
        expect_valid(&mut cx, ordering, Some(&assumptions));
        let equal = cx.eq(x, y).unwrap();
        let Outcome::Refuted(model) =
            valid_under(&mut cx, equal, Some(&assumptions), &sat_only()).unwrap()
        else {
            panic!("a strict ordering excludes equality");
        };
        assert_eq!(
            cx.eval(&[path, equal], &model[..]).unwrap(),
            [BitVec::from_bool(true), BitVec::from_bool(false)]
        );
        let contradiction = cx.uge(x, y).unwrap();
        assumptions.assume_true(&mut cx, contradiction).unwrap();
        let falsehood = cx.zero(Width::W1).unwrap();
        expect_valid(&mut cx, falsehood, Some(&assumptions));
    }
}

#[test]
fn aliasing_stores_commute_only_when_the_addresses_differ() {
    let mut cx = Context::new();
    let p = cx.symbol("p", Width::new(4).unwrap()).unwrap();
    let q = cx.symbol("q", Width::new(4).unwrap()).unwrap();
    let at = cx.symbol("at", Width::new(4).unwrap()).unwrap();
    let a = cx.symbol("a", Width::W8).unwrap();
    let b = cx.symbol("b", Width::W8).unwrap();
    let mut first = Memory::new("m", Width::new(4).unwrap(), Width::W8, Endian::Little).zeroed();
    let mut second = first.clone();
    let s = first.store(&mut cx, first.initial(), p, a).unwrap();
    let s = first.store(&mut cx, s, q, b).unwrap();
    let left = first.load(&mut cx, s, at, 1).unwrap();
    let t = second.store(&mut cx, second.initial(), q, b).unwrap();
    let t = second.store(&mut cx, t, p, a).unwrap();
    let right = second.load(&mut cx, t, at, 1).unwrap();
    let same = cx.eq(left, right).unwrap();
    let different = cx.ne(p, q).unwrap();
    let mut assumptions = Assumptions::new();
    assumptions.assume_true(&mut cx, different).unwrap();
    expect_valid(&mut cx, same, Some(&assumptions));
    let Outcome::Refuted(model) = valid(&mut cx, same, &sat_only()).unwrap() else {
        panic!("aliased stores of different values need not commute");
    };
    assert!(cx.eval(&[same], &model[..]).unwrap()[0].is_zero());
    assert_eq!(
        cx.eval(&[p, q], &model[..]).unwrap()[0],
        cx.eval(&[p, q], &model[..]).unwrap()[1]
    );
}

#[test]
fn nan_classification_and_ieee_equality_have_certified_models_and_proofs() {
    use crate::fp::{FpFormat, FpOp, FpTest};
    for format in [
        FpFormat::new(2, 3).unwrap(),
        FpFormat::F16,
        FpFormat::F32,
        FpFormat::F64,
        FpFormat::F128,
    ] {
        let mut cx = Context::new();
        let x = cx.symbol("x", format.width()).unwrap();
        let nan = cx.fp_test(format, FpTest::Nan, x).unwrap();
        let eq = cx.fp(FpOp::Eq, format, &[x, x]).unwrap();
        let unequal = cx.un(UnOp::Not, eq).unwrap();
        let claim = cx.eq(nan, unequal).unwrap();
        expect_valid(&mut cx, claim, None);
        let model = satisfy(&mut cx, nan, &sat_only())
            .unwrap()
            .unwrap()
            .unwrap();
        let value = model
            .iter()
            .find(|(k, _)| *k == SymbolKey::from("x"))
            .unwrap()
            .1;
        assert!(bitwright_ref::fp::is_nan(
            bitwright_ref::fp::Format {
                eb: format.eb() as u16,
                sb: format.sb() as u16
            },
            &bitwright_ref::Bits::from_limbs(value.width().bits(), value.limbs())
        ));
        assert_eq!(
            cx.eval(&[nan, eq], &model[..]).unwrap(),
            [BitVec::from_bool(true), BitVec::from_bool(false)]
        );
    }
}

#[cfg(feature = "smtlib")]
#[test]
fn smtlib_bitvector_array_boolean_and_float_scripts_have_known_verdicts() {
    let cases = [
        (
            "overflow",
            true,
            "(declare-const x (_ BitVec 8)) (assert (bvult (bvadd x #x01) x))",
        ),
        (
            "wrap invalidates ordering",
            false,
            "(declare-const x (_ BitVec 8)) (assert (= x #xff)) (assert (bvult x (bvadd x #x01)))",
        ),
        (
            "unsigned division by zero",
            false,
            "(declare-const x (_ BitVec 8)) (assert (distinct (bvudiv x #x00) #xff))",
        ),
        (
            "signed division by zero",
            false,
            "(declare-const x (_ BitVec 8)) (assert (= x #x80)) (assert (distinct (bvsdiv x #x00) #x01))",
        ),
        (
            "wide nonoverlapping addition",
            false,
            "(declare-const x (_ BitVec 65)) (declare-const y (_ BitVec 65)) (assert (= (bvand x y) (_ bv0 65))) (assert (distinct (bvadd x y) (bvxor x y)))",
        ),
        (
            "maximum-width overshift",
            false,
            "(declare-const x (_ BitVec 512)) (assert (distinct (bvlshr x (_ bv512 512)) (_ bv0 512)))",
        ),
        (
            "parallel let bindings",
            true,
            "(declare-const x (_ BitVec 8)) (assert (= x #x01)) (assert (let ((x #x02) (y x)) (and (= x #x02) (= y #x01))))",
        ),
        (
            "parallel let near miss",
            false,
            "(declare-const x (_ BitVec 8)) (assert (= x #x01)) (assert (let ((x #x02) (y x)) (= y #x02)))",
        ),
        (
            "Boolean and bit-vector choices",
            true,
            "(declare-const a Bool) (declare-const b Bool) (declare-const x (_ BitVec 8)) (assert (xor a b)) (assert (= (ite a x (bvnot x)) #x5a))",
        ),
        (
            "read over write",
            false,
            "(declare-const m (Array (_ BitVec 4) (_ BitVec 8))) (declare-const p (_ BitVec 4)) (declare-const q (_ BitVec 4)) (declare-const v (_ BitVec 8)) (assert (distinct (select (store m p v) q) (ite (= p q) v (select m q))))",
        ),
        (
            "NaN is not IEEE reflexive",
            false,
            "(declare-const x Float32) (assert (fp.isNaN x)) (assert (fp.eq x x))",
        ),
        (
            "NaN witness",
            true,
            "(declare-const x Float64) (assert (fp.isNaN x)) (assert (not (fp.eq x x)))",
        ),
        (
            "negative zero equals positive zero",
            true,
            "(declare-const x Float32) (assert (fp.eq x (_ +zero 8 24))) (assert (= (fp.to_ieee_bv x) #x80000000))",
        ),
    ];
    for (name, expected_sat, script) in cases {
        let mut cx = Context::new();
        let imported =
            crate::smtlib::import(&mut cx, script).unwrap_or_else(|e| panic!("{name}: {e}"));
        let mut conjunction = cx.one(Width::W1).unwrap();
        for &p in &imported.assertions {
            conjunction = cx.and(conjunction, p).unwrap();
        }
        let negation = cx.un(UnOp::Not, conjunction).unwrap();
        match valid(&mut cx, negation, &sat_only()).unwrap() {
            Outcome::Refuted(model) => {
                assert!(expected_sat, "{name}: unexpected SAT");
                for &p in &imported.assertions {
                    assert_eq!(
                        cx.eval(&[p], &model[..]).unwrap()[0],
                        BitVec::from_bool(true),
                        "{name}"
                    );
                }
            }
            Outcome::Proved(Some(certificate)) => {
                assert!(!expected_sat, "{name}: unexpected UNSAT");
                certificate.check().unwrap();
            }
            other => panic!("{name}: {other:?}"),
        }
    }
}

#[cfg(feature = "smtlib")]
#[test]
fn unsupported_smt_theories_are_refused_instead_of_partially_imported() {
    for script in [
        "(assert (forall ((x (_ BitVec 8))) (= x x)))",
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8)) (assert (= (f #x00) #x01))",
        "(declare-const a (Array (_ BitVec 4) (_ BitVec 8))) (declare-const b (Array (_ BitVec 4) (_ BitVec 8))) (assert (= a b))",
        "(declare-const rm RoundingMode) (declare-const x Float32) (assert (fp.eq (fp.add rm x x) x))",
    ] {
        assert!(
            crate::smtlib::import(&mut Context::new(), script).is_err(),
            "accepted unsupported theory: {script}"
        );
    }
}
