//! Floating-point expressions: building, folding, printing and parsing, evaluation.

use super::*;
use crate::testutil::Rng;
use crate::{Context, Expr, ParseOptions, SymbolKey};

fn rm_all() -> [RoundingMode; 5] {
    RoundingMode::ALL
}

/// Every operation of `f` on the symbols `a`, `b`, `c` (and an integer `i` of 20 bits), with
/// each rounding mode where it takes one.
fn every_op(cx: &mut Context, f: FpFormat) -> Vec<Expr> {
    let w = f.width();
    let (a, b, c) = (
        cx.symbol("a", w).unwrap(),
        cx.symbol("b", w).unwrap(),
        cx.symbol("c", w).unwrap(),
    );
    let i = cx.symbol("i", Width::new(20).unwrap()).unwrap();
    let mut out = Vec::new();
    for rm in rm_all() {
        out.push(cx.fp(FpOp::Add(rm), f, &[a, b]).unwrap());
        out.push(cx.fp_sub(f, rm, a, b).unwrap());
        out.push(cx.fp(FpOp::Mul(rm), f, &[a, b]).unwrap());
        out.push(cx.fp(FpOp::Div(rm), f, &[a, b]).unwrap());
        out.push(cx.fp(FpOp::Fma(rm), f, &[a, b, c]).unwrap());
        out.push(cx.fp(FpOp::Sqrt(rm), f, &[a]).unwrap());
        out.push(cx.fp(FpOp::RoundToIntegral(rm), f, &[a]).unwrap());
        let to = if f == FpFormat::F64 {
            FpFormat::F32
        } else {
            FpFormat::new(9, 17).unwrap()
        };
        out.push(cx.fp(FpOp::Convert { to, rm }, f, &[a]).unwrap());
        out.push(cx.fp(FpOp::FromSInt(rm), f, &[i]).unwrap());
        out.push(cx.fp(FpOp::FromUInt(rm), f, &[i]).unwrap());
        out.push(cx.fp(FpOp::ToSInt(rm, Width::W16), f, &[a]).unwrap());
        out.push(cx.fp(FpOp::ToUInt(rm, Width::W8), f, &[a]).unwrap());
    }
    for op in [
        FpOp::Rem,
        FpOp::Min,
        FpOp::Max,
        FpOp::Eq,
        FpOp::Lt,
        FpOp::Le,
    ] {
        out.push(cx.fp(op, f, &[a, b]).unwrap());
    }
    for op in [FpCmpOp::Gt, FpCmpOp::Ge] {
        out.push(cx.fp_cmp(f, op, a, b).unwrap());
    }
    out.push(cx.fp_neg(f, a).unwrap());
    out.push(cx.fp_abs(f, a).unwrap());
    out.push(cx.fp_copysign(f, a, b).unwrap());
    for t in [
        FpTest::Nan,
        FpTest::Infinite,
        FpTest::Zero,
        FpTest::Subnormal,
        FpTest::Normal,
        FpTest::Negative,
        FpTest::Positive,
    ] {
        out.push(cx.fp_test(f, t, a).unwrap());
    }
    out
}

#[test]
fn printing_and_parsing_round_trip() {
    for f in [
        FpFormat::F32,
        FpFormat::F64,
        FpFormat::BF16,
        FpFormat::new(3, 4).unwrap(),
        FpFormat::X87,
    ] {
        let mut cx = Context::new();
        for e in every_op(&mut cx, f) {
            let text = cx.display(e).to_string();
            let back = cx
                .parse(&text, &ParseOptions::default())
                .unwrap_or_else(|err| panic!("{text}: {err}"));
            assert_eq!(back, e, "{text}");
        }
    }
}

#[test]
fn the_syntax_names_formats_and_modes() {
    let mut cx = Context::new();
    let o = ParseOptions::default();
    let e = cx.parse("fp.add.rtz.f32(x, y)", &o).unwrap();
    assert_eq!(cx.display(e).to_string(), "fp.add.rtz.f32(x, y)");
    let e = cx.parse("fp.mul.rne<5, 11>(h, h)", &o).unwrap();
    // Named formats print by name.
    assert_eq!(cx.display(e).to_string(), "fp.mul.rne.f16(h, h)");
    let e = cx.parse("fp.convert.rne.f64.f32(d)", &o).unwrap();
    assert_eq!(cx.display(e).to_string(), "fp.convert.rne.f64.f32(d)");
    let e = cx.parse("fp.convert.rtz<11, 53, 3, 4>(d)", &o).unwrap();
    assert_eq!(cx.display(e).to_string(), "fp.convert.rtz<11, 53, 3, 4>(d)");
    let e = cx.parse("fp.to_sbv.rtz.f64<32>(d)", &o).unwrap();
    assert_eq!(cx.width(e).unwrap(), Width::W32);
    let e = cx.parse("fp.from_sbv.rne.f64(5:32)", &o).unwrap();
    assert_eq!(cx.display(e).to_string(), "0x4014000000000000:64");
    let e = cx.parse("fp.lt.f64(d, fp.neg.f64(d))", &o).unwrap();
    assert_eq!(cx.width(e).unwrap(), Width::W1);
    // Errors: a missing mode, an unknown format, too few formats, a reserved symbol name.
    for bad in [
        "fp.add.f32(x, y)",
        "fp.add.rne.f33(x, y)",
        "fp.convert.rne.f32(x)",
        "fp.add.rne<1, 5>(x, y)",
        "fp.frob.f32(x)",
        "fp.x + 1",
    ] {
        assert!(cx.parse(bad, &o).is_err(), "{bad}");
    }
    // A symbol named like an fp call prints quoted, and reads back.
    let s = cx.symbol("fp.add", Width::W8).unwrap();
    let text = cx.display(s).to_string();
    assert_eq!(cx.parse(&text, &o).unwrap(), s, "{text}");
}

#[test]
fn constants_fold_and_commutative_operands_are_ordered() {
    let mut cx = Context::new();
    let f = FpFormat::F64;
    let one = cx.constant(&BitVec::from_f64(1.0)).unwrap();
    let tenth = cx.constant(&BitVec::from_f64(0.1)).unwrap();
    let e = cx
        .fp(FpOp::Add(RoundingMode::Rtp), f, &[one, tenth])
        .unwrap();
    let expect = f
        .add(
            RoundingMode::Rtp,
            &BitVec::from_f64(1.0),
            &BitVec::from_f64(0.1),
        )
        .unwrap();
    assert_eq!(cx.as_const(e).unwrap(), Some(expect));
    let x = cx.symbol("x", Width::W64).unwrap();
    let y = cx.symbol("y", Width::W64).unwrap();
    for op in [
        FpOp::Add(RoundingMode::Rne),
        FpOp::Mul(RoundingMode::Rna),
        FpOp::Min,
        FpOp::Max,
        FpOp::Eq,
    ] {
        assert_eq!(
            cx.fp(op, f, &[x, y]).unwrap(),
            cx.fp(op, f, &[y, x]).unwrap(),
            "{op:?}"
        );
    }
    // Not commutative: division, and the order comparisons.
    assert_ne!(
        cx.fp(FpOp::Div(RoundingMode::Rne), f, &[x, y]).unwrap(),
        cx.fp(FpOp::Div(RoundingMode::Rne), f, &[y, x]).unwrap()
    );
    // fma: the product's operands commute.
    let z = cx.symbol("z", Width::W64).unwrap();
    let rne = FpOp::Fma(RoundingMode::Rne);
    assert_eq!(
        cx.fp(rne, f, &[x, y, z]).unwrap(),
        cx.fp(rne, f, &[y, x, z]).unwrap()
    );
    // Different modes, different nodes.
    assert_ne!(
        cx.fp(FpOp::Add(RoundingMode::Rne), f, &[x, y]).unwrap(),
        cx.fp(FpOp::Add(RoundingMode::Rtz), f, &[x, y]).unwrap()
    );
    // Widths are checked.
    let s = cx.symbol("s", Width::W32).unwrap();
    assert!(cx.fp(FpOp::Add(RoundingMode::Rne), f, &[x, s]).is_err());
    assert!(cx.fp(FpOp::Add(RoundingMode::Rne), f, &[x]).is_err());
}

#[test]
fn conversions_to_formats_of_one_width_are_different_nodes() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let rm = RoundingMode::Rne;
    let a = cx
        .fp(
            FpOp::Convert {
                to: FpFormat::F32,
                rm,
            },
            FpFormat::F64,
            &[x],
        )
        .unwrap();
    let b = cx
        .fp(
            FpOp::Convert {
                to: FpFormat::new(5, 27).unwrap(),
                rm,
            },
            FpFormat::F64,
            &[x],
        )
        .unwrap();
    assert_ne!(a, b);
    let env = [(SymbolKey::from("x"), BitVec::from_f64(3.0))];
    let (va, vb) = (
        cx.eval(&[a], &env[..]).unwrap()[0],
        cx.eval(&[b], &env[..]).unwrap()[0],
    );
    assert_eq!(va.to_f32(), Some(3.0));
    assert_ne!(va, vb);
    match cx.view(b).unwrap() {
        crate::View::Fp { op, format, args } => {
            assert_eq!(
                op,
                FpOp::Convert {
                    to: FpFormat::new(5, 27).unwrap(),
                    rm
                }
            );
            assert_eq!(format, FpFormat::F64);
            assert_eq!(args.as_slice(), &[x]);
        }
        v => panic!("{v:?}"),
    }
}

/// Random values for the symbols `a`, `b`, `c` (format `f`) and `i` (20 bits).
fn env(rng: &mut Rng, f: FpFormat) -> Vec<(SymbolKey, BitVec)> {
    let sample = |rng: &mut Rng| super::tests::sample(rng, f);
    vec![
        (SymbolKey::from("a"), sample(rng)),
        (SymbolKey::from("b"), sample(rng)),
        (SymbolKey::from("c"), sample(rng)),
        (
            SymbolKey::from("i"),
            BitVec::wrapping_from_u64(Width::new(20).unwrap(), rng.next()),
        ),
    ]
}

#[test]
fn expressions_evaluate_like_the_value_operations() {
    let mut rng = Rng(11);
    for f in [FpFormat::F32, FpFormat::new(3, 4).unwrap(), FpFormat::X87] {
        let mut cx = Context::new();
        let exprs = every_op(&mut cx, f);
        for _ in 0..300 {
            let env = env(&mut rng, f);
            let (a, b, c, i) = (&env[0].1, &env[1].1, &env[2].1, &env[3].1);
            let vals = cx.eval(&exprs, &env[..]).unwrap();
            let mut expect = Vec::new();
            for rm in rm_all() {
                let to = if f == FpFormat::F64 {
                    FpFormat::F32
                } else {
                    FpFormat::new(9, 17).unwrap()
                };
                expect.push(f.add(rm, a, b).unwrap());
                expect.push(f.sub(rm, a, b).unwrap());
                expect.push(f.mul(rm, a, b).unwrap());
                expect.push(f.div(rm, a, b).unwrap());
                expect.push(f.fma(rm, a, b, c).unwrap());
                expect.push(f.sqrt(rm, a).unwrap());
                expect.push(f.round_to_integral(rm, a).unwrap());
                expect.push(f.convert(to, rm, a).unwrap());
                expect.push(f.from_sint(rm, i));
                expect.push(f.from_uint(rm, i));
                expect.push(f.to_sint(rm, a, Width::W16).unwrap());
                expect.push(f.to_uint(rm, a, Width::W8).unwrap());
            }
            expect.push(f.rem(a, b).unwrap());
            expect.push(f.min(a, b).unwrap());
            expect.push(f.max(a, b).unwrap());
            for op in [
                FpCmpOp::Eq,
                FpCmpOp::Lt,
                FpCmpOp::Le,
                FpCmpOp::Gt,
                FpCmpOp::Ge,
            ] {
                expect.push(BitVec::from_bool(f.cmp(op, a, b).unwrap()));
            }
            expect.push(f.neg(a).unwrap());
            expect.push(f.abs(a).unwrap());
            expect.push(f.copysign(a, b).unwrap());
            for t in [
                FpTest::Nan,
                FpTest::Infinite,
                FpTest::Zero,
                FpTest::Subnormal,
                FpTest::Normal,
                FpTest::Negative,
                FpTest::Positive,
            ] {
                expect.push(BitVec::from_bool(f.test(t, a).unwrap()));
            }
            assert_eq!(vals.len(), expect.len());
            for (k, (got, want)) in vals.iter().zip(&expect).enumerate() {
                assert_eq!(
                    got,
                    want,
                    "{f:?} #{k} {} with a={a} b={b} c={c} i={i}",
                    cx.display(exprs[k])
                );
            }
        }
    }
}

#[test]
fn x87_expressions_evaluate_like_the_value_functions() {
    let mut cx = Context::new();
    let w80 = Width::new(80).unwrap();
    let x = cx.symbol("x", w80).unwrap();
    let load = cx.x87_load(x).unwrap();
    let y = cx.symbol("y", FpFormat::X87.width()).unwrap();
    let store = cx.x87_store(y).unwrap();
    let mut rng = Rng(12);
    for k in 0..4_000 {
        // Bias toward the exponent fields that matter: 0, max, and the integer bit.
        let mut bits = u128::from(rng.next()) << 64 | u128::from(rng.next());
        match k % 4 {
            0 => bits &= !(0x7fff << 64),
            1 => bits |= 0x7fff << 64,
            _ => {}
        }
        let xv = BitVec::wrapping_from_u128(w80, bits);
        let yv = super::tests::sample(&mut rng, FpFormat::X87);
        let env = [(SymbolKey::from("x"), xv), (SymbolKey::from("y"), yv)];
        let got = cx.eval(&[load, store], &env[..]).unwrap();
        assert_eq!(got[0], x87_load(&xv).unwrap(), "load {xv}");
        assert_eq!(got[1], x87_store(&yv).unwrap(), "store {yv}");
    }
}

/// A random DAG over binary32 values mixing floating-point operations, comparisons used as
/// select conditions, bit operations on the encodings, and conversions through integers.
fn mixed_dag(cx: &mut Context, rng: &mut Rng) -> Expr {
    let f = FpFormat::F32;
    let w = f.width();
    let mut pool: Vec<Expr> = ["a", "b", "c"]
        .iter()
        .map(|n| cx.symbol(*n, w).unwrap())
        .collect();
    for v in [1.0f32, -0.0, 0.5, f32::INFINITY] {
        pool.push(cx.constant(&BitVec::from_f32(v)).unwrap());
    }
    let rms = RoundingMode::ALL;
    for _ in 0..24 {
        let pick = |rng: &mut Rng, pool: &Vec<Expr>| {
            // Mostly recent nodes (depth), sometimes anything (sharing).
            let n = pool.len();
            let k = if rng.chance(2, 3) {
                n - 1 - rng.below(4.min(n as u64)) as usize
            } else {
                rng.below(n as u64) as usize
            };
            pool[k]
        };
        let (x, y, z) = (pick(rng, &pool), pick(rng, &pool), pick(rng, &pool));
        let rm = rms[rng.below(5) as usize];
        let e = match rng.below(14) {
            0 => cx.fp(FpOp::Add(rm), f, &[x, y]),
            1 => cx.fp_sub(f, rm, x, y),
            2 => cx.fp(FpOp::Mul(rm), f, &[x, y]),
            3 => cx.fp(FpOp::Div(rm), f, &[x, y]),
            4 => cx.fp(FpOp::Fma(rm), f, &[x, y, z]),
            5 => cx.fp(FpOp::Sqrt(rm), f, &[x]),
            6 => cx.fp(FpOp::RoundToIntegral(rm), f, &[x]),
            7 => cx.fp(
                if rng.chance(1, 2) {
                    FpOp::Min
                } else {
                    FpOp::Max
                },
                f,
                &[x, y],
            ),
            8 => cx.fp(FpOp::Rem, f, &[x, y]),
            9 => {
                let op =
                    [FpCmpOp::Eq, FpCmpOp::Lt, FpCmpOp::Le, FpCmpOp::Gt][rng.below(4) as usize];
                let c = cx.fp_cmp(f, op, x, y).unwrap();
                cx.select(c, y, z)
            }
            10 => {
                let t = cx.fp_test(f, FpTest::Nan, x).unwrap();
                cx.select(t, z, x)
            }
            11 => cx.xor(x, y),
            12 => {
                let i = cx.fp(FpOp::ToSInt(rm, Width::W32), f, &[x]).unwrap();
                cx.fp(FpOp::FromSInt(rm), f, &[i])
            }
            _ => {
                let n = cx.fp_neg(f, x).unwrap();
                cx.fp_copysign(f, n, y)
            }
        }
        .unwrap();
        pool.push(e);
    }
    *pool.last().unwrap()
}

#[test]
fn the_engine_keeps_floating_point_expressions_equal() {
    use crate::engine::{Engine, Strategy};
    let engines = [
        Engine::standard(),
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap(),
    ];
    let mut rng = Rng(13);
    for _ in 0..60 {
        let mut cx = Context::new();
        let e = mixed_dag(&mut cx, &mut rng);
        let envs: Vec<_> = (0..40).map(|_| env(&mut rng, FpFormat::F32)).collect();
        let before: Vec<BitVec> = envs
            .iter()
            .map(|env| cx.eval(&[e], &env[..]).unwrap()[0])
            .collect();
        for engine in &engines {
            let out = engine.simplify(&mut cx, e).unwrap().expr;
            for (env, want) in envs.iter().zip(&before) {
                assert_eq!(
                    cx.eval(&[out], &env[..]).unwrap()[0],
                    *want,
                    "{} simplified to {}",
                    cx.display(e),
                    cx.display(out)
                );
            }
        }
        // Facts over floating-point nodes hold (they are at least sound, if weak).
        let facts = cx.facts(e).unwrap();
        for (env, v) in envs.iter().zip(&before) {
            let _ = env;
            assert!(facts.known().contains(v), "facts {facts:?} exclude {v}");
        }
    }
}

/// What facts decide about floating-point results, so the engine folds the question.
#[test]
fn facts_decide_floating_point_questions() {
    use crate::engine::Engine;
    let f = FpFormat::F64;
    let rne = RoundingMode::Rne;
    let mut cx = Context::new();
    let x32 = cx.symbol("x32", Width::W32).unwrap();
    let x8 = cx.symbol("x8", Width::W8).unwrap();
    let (a16, b16) = (
        cx.symbol("a16", Width::W16).unwrap(),
        cx.symbol("b16", Width::W16).unwrap(),
    );
    let y = cx.symbol("y", Width::W64).unwrap();
    let from32 = cx.fp(FpOp::FromSInt(rne), f, &[x32]).unwrap();
    let from8 = cx.fp(FpOp::FromUInt(rne), f, &[x8]).unwrap();
    let fa = cx.fp(FpOp::FromSInt(rne), f, &[a16]).unwrap();
    let fb = cx.fp(FpOp::FromSInt(rne), f, &[b16]).unwrap();
    let c256 = cx.constant(&BitVec::from_f64(256.0)).unwrap();
    let mut cases: Vec<(Expr, bool)> = vec![
        (cx.fp_test(f, FpTest::Nan, from32).unwrap(), false),
        (cx.fp_test(f, FpTest::Infinite, from32).unwrap(), false),
        (cx.fp_cmp(f, FpCmpOp::Lt, from8, c256).unwrap(), true),
        (cx.fp_cmp(f, FpCmpOp::Ge, from8, c256).unwrap(), false),
    ];
    let abs = cx.fp_abs(f, y).unwrap();
    cases.push((cx.fp_test(f, FpTest::Negative, abs).unwrap(), false));
    let root = cx.fp(FpOp::Sqrt(rne), f, &[from8]).unwrap();
    cases.push((cx.fp_test(f, FpTest::Nan, root).unwrap(), false));
    let prod = cx.fp(FpOp::Mul(rne), f, &[fa, fb]).unwrap();
    cases.push((cx.fp_test(f, FpTest::Nan, prod).unwrap(), false));
    cases.push((cx.fp_test(f, FpTest::Infinite, prod).unwrap(), false));
    let neg = cx.fp_neg(f, from8).unwrap();
    cases.push((cx.fp_test(f, FpTest::Positive, neg).unwrap(), false));
    let back = cx
        .fp(FpOp::ToSInt(RoundingMode::Rtz, Width::W32), f, &[fa])
        .unwrap();
    let limit = cx
        .constant(&BitVec::from_u64(Width::W32, 40_000).unwrap())
        .unwrap();
    cases.push((cx.cmp(crate::CmpOp::Slt, back, limit).unwrap(), true));
    let engine = Engine::standard();
    for (e, want) in cases {
        let text = cx.display(e).to_string();
        let out = engine.simplify(&mut cx, e).unwrap().expr;
        assert_eq!(
            cx.as_const(out).unwrap(),
            Some(BitVec::from_bool(want)),
            "{text} simplified to {}",
            cx.display(out)
        );
    }
}

/// The construction-time identities are exact: every shape they rewrite, built from symbols,
/// evaluates like the operation it came from, on every input of tiny formats, in every mode.
#[test]
fn construction_identities_are_exact() {
    for f in [
        FpFormat::new(2, 3).unwrap(),
        FpFormat::new(3, 3).unwrap(),
        FpFormat::new(3, 2).unwrap(),
    ] {
        let w = f.width();
        let n = 1u64 << w.bits();
        let one = f.from_uint(RoundingMode::Rne, &BitVec::one(Width::W8));
        let two = f.from_uint(RoundingMode::Rne, &BitVec::wrapping_from_u64(Width::W8, 2));
        let half = f.div(RoundingMode::Rne, &one, &two).unwrap();
        for rm in RoundingMode::ALL {
            let mut cx = Context::new();
            let (x, y) = (cx.symbol("x", w).unwrap(), cx.symbol("y", w).unwrap());
            let i = cx.symbol("i", Width::new(3).unwrap()).unwrap();
            let c1 = cx.constant(&one).unwrap();
            let c2 = cx.constant(&two).unwrap();
            let ch = cx.constant(&half).unwrap();
            let nz = cx.constant(&f.zero(true)).unwrap();
            let (nx, ny) = (cx.fp_neg(f, x).unwrap(), cx.fp_neg(f, y).unwrap());
            let i5 = cx.zext(i, Width::new(5).unwrap()).unwrap();
            let s5 = cx.sext(i, Width::new(5).unwrap()).unwrap();
            let rti = cx
                .fp(FpOp::RoundToIntegral(RoundingMode::Rtz), f, &[x])
                .unwrap();
            // (expression, its meaning from the operand values)
            type Meaning = Box<dyn Fn(&[BitVec]) -> BitVec>;
            let neg = move |b: BitVec| f.neg(&b).unwrap();
            let cases: Vec<(Expr, Meaning)> = vec![
                (
                    cx.fp(FpOp::Fma(rm), f, &[x, c1, y]).unwrap(),
                    Box::new(move |a| f.fma(rm, &a[0], &one, &a[1]).unwrap()),
                ),
                (
                    cx.fp(FpOp::Fma(rm), f, &[c1, x, y]).unwrap(),
                    Box::new(move |a| f.fma(rm, &one, &a[0], &a[1]).unwrap()),
                ),
                (
                    cx.fp(FpOp::Fma(rm), f, &[x, y, nz]).unwrap(),
                    Box::new(move |a| f.fma(rm, &a[0], &a[1], &f.zero(true)).unwrap()),
                ),
                (
                    cx.fp(FpOp::Mul(rm), f, &[x, c2]).unwrap(),
                    Box::new(move |a| f.mul(rm, &a[0], &two).unwrap()),
                ),
                (
                    cx.fp(FpOp::Div(rm), f, &[x, ch]).unwrap(),
                    Box::new(move |a| f.div(rm, &a[0], &half).unwrap()),
                ),
                (
                    cx.fp(FpOp::Mul(rm), f, &[nx, ny]).unwrap(),
                    Box::new(move |a| f.mul(rm, &neg(a[0]), &neg(a[1])).unwrap()),
                ),
                (
                    cx.fp(FpOp::Div(rm), f, &[nx, ny]).unwrap(),
                    Box::new(move |a| f.div(rm, &neg(a[0]), &neg(a[1])).unwrap()),
                ),
                (
                    cx.fp(FpOp::Lt, f, &[nx, ny]).unwrap(),
                    Box::new(move |a| {
                        BitVec::from_bool(f.cmp(FpCmpOp::Lt, &neg(a[0]), &neg(a[1])).unwrap())
                    }),
                ),
                (
                    cx.fp(FpOp::Le, f, &[nx, ny]).unwrap(),
                    Box::new(move |a| {
                        BitVec::from_bool(f.cmp(FpCmpOp::Le, &neg(a[0]), &neg(a[1])).unwrap())
                    }),
                ),
                (
                    cx.fp(FpOp::Eq, f, &[nx, ny]).unwrap(),
                    Box::new(move |a| {
                        BitVec::from_bool(f.cmp(FpCmpOp::Eq, &neg(a[0]), &neg(a[1])).unwrap())
                    }),
                ),
                (
                    cx.fp(FpOp::Lt, f, &[x, x]).unwrap(),
                    Box::new(move |a| BitVec::from_bool(f.cmp(FpCmpOp::Lt, &a[0], &a[0]).unwrap())),
                ),
                (
                    cx.fp(FpOp::RoundToIntegral(rm), f, &[rti]).unwrap(),
                    Box::new(move |a| {
                        let inner = f.round_to_integral(RoundingMode::Rtz, &a[0]).unwrap();
                        f.round_to_integral(rm, &inner).unwrap()
                    }),
                ),
                (
                    cx.fp(FpOp::FromSInt(rm), f, &[i5]).unwrap(),
                    Box::new(move |a| f.from_sint(rm, &a[3].zext(Width::new(5).unwrap()).unwrap())),
                ),
                (
                    cx.fp(FpOp::FromUInt(rm), f, &[i5]).unwrap(),
                    Box::new(move |a| f.from_uint(rm, &a[3].zext(Width::new(5).unwrap()).unwrap())),
                ),
                (
                    cx.fp(FpOp::FromSInt(rm), f, &[s5]).unwrap(),
                    Box::new(move |a| f.from_sint(rm, &a[3].sext(Width::new(5).unwrap()).unwrap())),
                ),
            ];
            let mut cases = cases;
            let (fs, fu) = (
                cx.fp(FpOp::FromSInt(rm), f, &[i]).unwrap(),
                cx.fp(FpOp::FromUInt(rm), f, &[i]).unwrap(),
            );
            let w4 = Width::new(4).unwrap();
            cases.push((
                cx.fp(FpOp::RoundToIntegral(rm), f, &[fs]).unwrap(),
                Box::new(move |a| f.round_to_integral(rm, &f.from_sint(rm, &a[3])).unwrap()),
            ));
            cases.push((
                cx.fp(FpOp::ToSInt(RoundingMode::Rtz, w4), f, &[fs])
                    .unwrap(),
                Box::new(move |a| {
                    f.to_sint(RoundingMode::Rtz, &f.from_sint(rm, &a[3]), w4)
                        .unwrap()
                }),
            ));
            cases.push((
                cx.fp(FpOp::ToUInt(rm, w4), f, &[fu]).unwrap(),
                Box::new(move |a| f.to_uint(rm, &f.from_uint(rm, &a[3]), w4).unwrap()),
            ));
            cases.push((
                cx.fp(FpOp::ToSInt(rm, w4), f, &[fu]).unwrap(),
                Box::new(move |a| f.to_sint(rm, &f.from_uint(rm, &a[3]), w4).unwrap()),
            ));
            for xv in 0..n {
                for yv in 0..n {
                    let vals = [
                        BitVec::wrapping_from_u64(w, xv),
                        BitVec::wrapping_from_u64(w, yv),
                        BitVec::zero(w),
                        BitVec::wrapping_from_u64(Width::new(3).unwrap(), xv),
                    ];
                    let env = [
                        (SymbolKey::from("x"), vals[0]),
                        (SymbolKey::from("y"), vals[1]),
                        (SymbolKey::from("i"), vals[3]),
                    ];
                    for (e, meaning) in &cases {
                        assert_eq!(
                            cx.eval(&[*e], &env[..]).unwrap()[0],
                            meaning(&vals),
                            "{f:?} {rm:?} {} at {vals:?}",
                            cx.display(*e)
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn construction_identities_fire() {
    let mut cx = Context::new();
    let o = ParseOptions::default();
    for (src, want) in [
        ("fp.fma.rtp.f32(x, 0x3f800000, y)", "fp.add.rtp.f32(x, y)"),
        ("fp.fma.rne.f32(x, y, 0x80000000)", "fp.mul.rne.f32(x, y)"),
        ("fp.mul.rtz.f32(x, 0x40000000)", "fp.add.rtz.f32(x, x)"),
        (
            "fp.div.rtn.f64(d:64, 0x3fe0000000000000)",
            "fp.add.rtn.f64(d, d)",
        ),
        (
            "fp.mul.rne.f32(fp.neg.f32(x), fp.neg.f32(y))",
            "fp.mul.rne.f32(x, y)",
        ),
        ("fp.lt.f32(fp.neg.f32(x), fp.neg.f32(y))", "fp.lt.f32(y, x)"),
        ("fp.lt.f32(x, x)", "0:1"),
        (
            "fp.round.rne.f32(fp.round.rtz.f32(x))",
            "fp.round.rtz.f32(x)",
        ),
        (
            "fp.from_sbv.rne.f32(zext<32>(b:8))",
            "fp.from_ubv.rne.f32(b)",
        ),
    ] {
        let e = cx.parse(src, &o).unwrap();
        assert_eq!(cx.display(e).to_string(), want, "{src}");
    }
    // Not toward −∞: there +0 + −0 is −0, not the product's +0.
    let e = cx.parse("fp.fma.rtn.f32(x, y, 0x80000000)", &o).unwrap();
    assert!(cx.display(e).to_string().starts_with("fp.fma"));
    // Not across formats of one width.
    let e = cx
        .parse("fp.round.rne.bf16(fp.round.rtz.f16(h))", &o)
        .unwrap();
    assert!(
        cx.display(e)
            .to_string()
            .starts_with("fp.round.rne.bf16(fp.round")
    );
    // Integers: already integral, and back exactly when the format holds them.
    for (src, want) in [
        (
            "fp.round.rtp.f32(fp.from_sbv.rne.f32(i:32))",
            "fp.from_sbv.rne.f32(i)",
        ),
        (
            "fp.to_sbv.rtz.f64<32>(fp.from_sbv.rne.f64(j:16))",
            "sext<32>(j)",
        ),
        ("fp.to_sbv.rtz.f64<16>(fp.from_sbv.rne.f64(j))", "j"),
        ("fp.to_ubv.rne.f32<24>(fp.from_ubv.rne.f32(k:24))", "k"),
        (
            "fp.to_sbv.rne.f32<25>(fp.from_ubv.rne.f32(k))",
            "zext<25>(k)",
        ),
    ] {
        let e = cx.parse(src, &o).unwrap();
        assert_eq!(cx.display(e).to_string(), want, "{src}");
    }
    // Not when the integer may not convert exactly (25 bits in binary32), or may not fit.
    for src in [
        "fp.to_ubv.rne.f32<32>(fp.from_ubv.rne.f32(u:25))",
        "fp.to_sbv.rtz.f64<8>(fp.from_sbv.rne.f64(j:16))",
        "fp.to_ubv.rtz.f64<32>(fp.from_sbv.rne.f64(j:16))",
        "fp.to_sbv.rtz.f64<16>(fp.from_ubv.rne.f64(q:16))",
    ] {
        let e = cx.parse(src, &o).unwrap();
        assert!(cx.display(e).to_string().starts_with("fp.to_"), "{src}");
    }
}
