//! Regressions for equivalent register views and the parents that consume them.
#![cfg(all(feature = "mba", feature = "prove"))]

use bitwright::engine::{Engine, Run, Strategy};
use bitwright::lift::{pcode, vex};
use bitwright::mba::MbaConfig;
use bitwright::prove::{self, Outcome};
use bitwright::{BitVec, Context, ParseOptions, Width};

const CARRY: (&str, &str) = (
    "zext<16>(extract<7, 1>(x + y))",
    "zext<16>((extract<7, 1>(x) ^ extract<7, 1>(y)) ^ ((trunc<7>(x) + trunc<7>(y)) <u trunc<7>(x)))",
);

// Each positive pair names the same word. z in the parent is a fresh word of that width.
const CASES: &[(&str, u16, &str, &str)] = &[
    (
        "low add",
        16,
        "zext<16>(trunc<8>(x) + trunc<8>(y))",
        "(x + y) & 255",
    ),
    (
        "constant shift",
        16,
        "zext<16>(trunc<8>(x) << 3)",
        "(x << 3) & 255",
    ),
    (
        "variable shift",
        16,
        "zext<16>(a:8 << b:8)",
        "(zext<16>(a:8) << zext<16>(b:8)) & 255",
    ),
    (
        "masked machine shift",
        64,
        "zext<64>(a:32 << (b:32 & 31))",
        "(zext<64>(a:32) << (zext<64>(b:32) & 31)) & 0xffffffff",
    ),
    (
        "leading zeros",
        16,
        "zext<16>(clz(a:8))",
        "clz(zext<16>(a:8)) - 8",
    ),
    (
        "nonzero divisor",
        16,
        "zext<16>(udiv(a:8, b:8 | 1))",
        "udiv(zext<16>(a:8), zext<16>(b:8 | 1))",
    ),
    (
        "remainder",
        16,
        "zext<16>(urem(a:8, b:8))",
        "urem(zext<16>(a:8), zext<16>(b:8))",
    ),
    (
        "byte rotation",
        16,
        "zext<16>(rotl(trunc<8>(x), 4))",
        "((x << 4) | ((x & 255) >>u 4)) & 255",
    ),
    ("carry bit", 16, CARRY.0, CARRY.1),
    (
        "rotation of a low 32-bit register",
        64,
        "zext<64>(rotl(trunc<32>(x), 16))",
        "((x << 16) | ((x & 0xffffffff) >>u 16)) & 0xffffffff",
    ),
    (
        "guarded byte",
        16,
        "select(trunc<8>(x) == trunc<8>(y), x & 255, t)",
        "select(trunc<8>(x) == trunc<8>(y), y & 255, t)",
    ),
    ("shift order", 16, "(x << k) << u", "(x << u) << k"),
    (
        "logical right shift order",
        16,
        "(x >>u k) >>u u",
        "(x >>u u) >>u k",
    ),
    (
        "arithmetic right shift order",
        16,
        "(x >>s k) >>s u",
        "(x >>s u) >>s k",
    ),
    ("rotated popcount", 8, "popcnt(x)", "popcnt(rotl(x, k))"),
];

fn check_pair(opts: &ParseOptions, left: &str, right: &str, equal: bool) {
    let mut cx = Context::new();
    let a = cx.parse(left, opts).unwrap();
    let b = cx.parse(right, opts).unwrap();
    let cfg = prove::Config::default()
        .with_simplify(false)
        .with_certificate(true)
        .with_max_conflicts(12_000)
        .with_max_propagations(400_000)
        .with_max_nodes(100_000);
    match prove::equal(&mut cx, a, b, &cfg).unwrap() {
        Outcome::Proved(Some(c)) if equal => c.check().unwrap(),
        Outcome::Refuted(_) if !equal => {}
        other => panic!("{left} vs {right}: {other:?}"),
    }
}

fn assert_recovers(
    engine: &Engine,
    opts: &ParseOptions,
    source: &str,
    extra: Option<&str>,
    want: &str,
) {
    // Only the requested roots exist before the run. Even parsing a reference term can
    // intern subexpressions a pass looks up in the arena.
    let mut cx = Context::new();
    let mut roots = vec![cx.parse(source, opts).unwrap()];
    if let Some(other) = extra {
        roots.push(cx.parse(other, opts).unwrap());
    }
    let result = engine.run(&mut cx, &roots, Run::default()).unwrap();
    let actual = result.roots[0].expr;
    assert_eq!(
        actual,
        cx.parse(want, opts).unwrap(),
        "{source} with extra {extra:?} simplified to {} ({:?})",
        cx.display(actual),
        result.roots[0].end
    );
    if roots.len() == 2 {
        let preserved = prove::equal(
            &mut cx,
            roots[1],
            result.roots[1].expr,
            &prove::Config::default().with_simplify(false),
        )
        .unwrap();
        assert!(
            matches!(preserved, Outcome::Proved(_)),
            "live output {extra:?}: {preserved:?}"
        );
    }
}

fn engine(sweep: bool) -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default().with_opaque_sweep(sweep)))
        .build()
        .unwrap()
}

#[test]
fn equivalence_coverage() {
    let engines = [engine(false), engine(true)];
    for &(_, w, p, q) in CASES {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        check_pair(&opts, p, q, true);
        let parent = |l: &str, r: &str| format!("let p = {l}; let q = {r}; (p & z) + (q | z) - p");
        let equality = format!("let p = {p}; let q = {q}; p == q");
        for engine in &engines {
            for side in [p, q] {
                assert_recovers(engine, &opts, &parent(side, side), None, "z");
            }
            assert_recovers(engine, &opts, &equality, None, "1:1");
            assert_recovers(engine, &opts, &parent(p, q), None, "z");
        }
    }

    let opts = ParseOptions::width(Width::W16);
    let eq = format!("let p = {}; let q = {}; p == q", CARRY.0, CARRY.1);
    for extra in [None, Some("spare:16"), Some(CARRY.0), Some(CARRY.1)] {
        assert_recovers(&engines[0], &opts, &eq, extra, "1:1");
    }

    let (p, q) = ("rotl(rotl(x, k), u)", "rotl(rotl(x, u), k)");
    let eq = format!("({p}) == ({q})");
    for w in [7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129] {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        if w <= 9 {
            check_pair(&opts, p, q, true);
        }
        for engine in &engines {
            assert_recovers(engine, &opts, &eq, None, "1:1");
        }
    }
    assert_recovers(
        &engines[0],
        &opts,
        "popcnt(bswap(rotr(bitrev(x), k)))",
        None,
        "popcnt(x)",
    );
}

#[test]
fn refuted_relations_survive_simplification() {
    let engine = engine(false);
    for (w, left, right) in [
        (16, "zext<16>(a:8 + b:8)", "zext<16>(a:8) + zext<16>(b:8)"),
        (
            16,
            "zext<16>(udiv(a:8, b:8))",
            "udiv(zext<16>(a:8), zext<16>(b:8))",
        ),
        (16, "zext<16>(trunc<8>(x) << trunc<8>(k))", "(x << k) & 255"),
        (
            16,
            "select(trunc<8>(x) == trunc<8>(y), x, t)",
            "select(trunc<8>(x) == trunc<8>(y), y, t)",
        ),
        (9, "rotl(rotl(x, k), u)", "rotl(x, k + u)"),
    ] {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        check_pair(&opts, left, right, false);
        let mut cx = Context::new();
        let eq = cx.parse(&format!("({left}) == ({right})"), &opts).unwrap();
        let simplified = engine.simplify(&mut cx, eq).unwrap().expr;
        // The simplified comparison must accept and reject the same inputs.
        let outcome = prove::equal(
            &mut cx,
            eq,
            simplified,
            &prove::Config::default().with_simplify(false),
        )
        .unwrap();
        assert!(
            matches!(outcome, Outcome::Proved(_)),
            "{left} vs {right}: {outcome:?}"
        );
    }
}

#[test]
fn merge_inside_a_parent_whose_answer_is_absent() {
    let opts = ParseOptions::width(Width::W16);
    let p = "zext<16>(clz(a:8))";
    let q = "clz(zext<16>(a:8)) - 8";
    let src = format!("let p = {p}; let q = {q}; ((p ^ z) + 7) ^ ((q ^ z) + 7)");
    assert_recovers(&engine(false), &opts, &src, Some(q), "0:16");
    // Two nodes per division take this outside the small whole-root search.
    // Equality of the mask operands still has a small proof.
    let data = (0..26).fold(String::from("x"), |acc, i| format!("udiv({acc}, d{i})"));
    let mask = format!("(({p} ^ z) + 7) ^ ((({q}) ^ z) + 7)");
    let large = format!("pext({data}, {mask})");
    assert_recovers(&engine(false), &opts, &large, None, "0:16");
}

#[test]
fn register_views() {
    // SLEIGH p-code for the two machine-code sequences in the report, excluding IMARK.
    let cases = [
        (
            "ARM64 names",
            "x1",
            "(register, x0, 8) = COPY (const, 1, 8)\n(register, x1, 8) = INT_ZEXT (register, w0, 4)",
        ),
        (
            "ARM64 offsets",
            "reg_0x4008",
            "(register, 0x4000, 8) = COPY (const, 1, 8)\n(register, 0x4008, 8) = INT_ZEXT (register, 0x4000, 4)",
        ),
        (
            "x64 names",
            "RCX",
            "(register, RAX, 8) = COPY (const, 1, 8)\n(register, ECX, 4) = COPY (register, EAX, 4)\n(register, RCX, 8) = INT_ZEXT (register, ECX, 4)",
        ),
        (
            "x64 offsets",
            "reg_0x8",
            "(register, 0x0, 8) = COPY (const, 1, 8)\n(register, 0x8, 4) = COPY (register, 0x0, 4)\n(register, 0x8, 8) = INT_ZEXT (register, 0x8, 4)",
        ),
    ];
    let engine = engine(false);
    for (label, output, src) in cases {
        let mut cx = Context::new();
        let block = pcode(&mut cx, src).unwrap();
        let value = engine
            .simplify(&mut cx, block.register(output).unwrap())
            .unwrap()
            .expr;
        assert_eq!(
            cx.as_const(value).unwrap(),
            Some(BitVec::one(Width::W64)),
            "{label}"
        );
    }
}

#[test]
fn partial_register_writes_preserve_unwritten_bytes() {
    let mut cx = Context::new();
    let wide = 0xffff_ffff_0000_002au64;
    for (full, part) in [("X30", "W30"), ("SP", "WSP"), ("RAX", "EAX")] {
        let text = format!(
            "(register, {full}, 8) = COPY (const, 0xffffffffffffffff, 8)\n(register, {part}, 4) = COPY (const, 42, 4)"
        );
        let value = pcode(&mut cx, &text).unwrap().register(full).unwrap();
        assert_eq!(cx.as_const(value).unwrap().unwrap().to_u64(), Some(wide));
    }
    let text = "t0:Ity_I32 t1:Ity_I64\nt0 = GET:I32(w0)\nt1 = 32Uto64(t0)\nPUT(x1) = t1";
    let block = vex(&mut cx, text).unwrap();
    assert_eq!(cx.width(block.register("x0").unwrap()).unwrap(), Width::W64);
    assert!(block.register("x1").is_some());
}
