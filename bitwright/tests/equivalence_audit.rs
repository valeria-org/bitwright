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

#[test]
fn multi_width_bit_provenance_and_poly_refinement() {
    let eng = engine(false);
    // 1. Bit-provenance with complement/bitrev/rotate across odd and wide widths `7..=512`.
    for w in [7u16, 8, 9, 16, 31, 32, 33, 63, 64, 65, 128, 256, 512] {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        let sh = (w / 2).max(1);
        let eq = format!("bitrev(~rotl(x, {sh})) == ~rotr(bitrev(x), {sh})");
        assert_recovers(&eng, &opts, &eq, None, "1:1");
    }

    // 2. Coalesced sign-bit provenance: `sext<W>(a:K)` vs `(zext<W>(a:K) ^ 2^(K-1)) - 2^(K-1)`
    //    inside ring polynomial expressions across odd and wide vector widths.
    for (k, w) in [
        (7u16, 15u16),
        (8, 16),
        (9, 31),
        (31, 63),
        (32, 64),
        (64, 128),
        (128, 256),
        (256, 512),
    ] {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        let mut cx = Context::new();
        let sign = BitVec::bin_unchecked_for_test_pow2(w, k - 1);
        let s_lit = format!("{sign}");
        let src = format!(
            "let lhs = sext<{w}>(a:{k}) * 5 + y; \
             let rhs = ((zext<{w}>(a:{k}) ^ {s_lit}) - {s_lit}) * 5 + y; \
             lhs - rhs"
        );
        let e = cx.parse(&src, &opts).unwrap();
        let out = eng.simplify(&mut cx, e).unwrap().expr;
        assert_eq!(
            out,
            cx.parse("0", &opts).unwrap(),
            "sext/zext-xor K={k} W={w}: got {}",
            cx.display(out)
        );
    }

    // 3. Disjoint slice partition & overlapping mask Venn refinement in ring polynomials (`1..=512`).
    for (k, w) in [
        (4u16, 9u16),
        (15, 31),
        (32, 64),
        (64, 129),
        (128, 256),
        (256, 512),
    ] {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        let rest = w - k;
        let shift = BitVec::bin_unchecked_for_test_pow2(w, k);
        let src = format!(
            "let split = zext<{w}>(extract<0, {k}>(x)) + zext<{w}>(extract<{k}, {rest}>(x)) * {shift}; \
             (split * 3 + z) - (x * 3 + z)"
        );
        assert_recovers(&eng, &opts, &src, None, &format!("0:{w}"));
    }

    for w in [16u16, 64, 128, 256, 512] {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        // Overlapping masks `0xff` and `0x3fc`: `(x & m1) + (x & m2) == (x & (m1 | m2)) + (x & (m1 & m2))`.
        let src = "((x & 0xff) + (x & 0x3fc)) - ((x & 0x3ff) + (x & 0xfc))";
        assert_recovers(&eng, &opts, src, None, &format!("0:{w}"));
    }

    // 4. Wide linear MBA rotation-union & complement atom merging at widths `65, 128, 256, 512`.
    for w in [65u16, 128, 256, 512] {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        let rsh = w - 5;
        let src = format!(
            "let r1 = rotl(x, 5); \
             let r2 = (x << 5) | (x >>u {rsh}); \
             (r1 & y) + (r1 | y) - (r2 + y)"
        );
        assert_recovers(&eng, &opts, &src, None, &format!("0:{w}"));
    }
}

trait Pow2Ext {
    fn bin_unchecked_for_test_pow2(w: u16, bit: u16) -> BitVec;
}

impl Pow2Ext for BitVec {
    fn bin_unchecked_for_test_pow2(w: u16, bit: u16) -> BitVec {
        let width = Width::new(w).unwrap();
        let one = BitVec::one(width);
        let amt = BitVec::wrapping_from_u64(width, u64::from(bit));
        BitVec::apply_bin(bitwright::BinOp::Shl, &one, &amt).unwrap()
    }
}

#[test]
fn multi_root_relations_and_z_floor_lens() {
    let eng = engine(false);
    // Multi-root runs `[parent(p, q), p]` and `[parent(p, q), q]` across widths `16, 64, 128, 256`.
    for (w, p, q) in [
        (16u16, "zext<16>(clz(a:8))", "clz(zext<16>(a:8)) - 8"),
        (
            64,
            "zext<64>(a:32 << (b:32 & 31))",
            "(zext<64>(a:32) << (zext<64>(b:32) & 31)) & 0xffffffff",
        ),
        (
            128,
            "concat(extract<64, 64>(x ^ y), trunc<64>(x ^ y))",
            "x ^ y",
        ),
        (256, "(x & 0xff00) + (x & 0x00ff)", "x & 0xffff"),
    ] {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        let parent = format!("let p = {p}; let q = {q}; ((p ^ z) + 9) ^ ((q ^ z) + 9)");
        let zero = format!("0:{w}");
        for extra in [None, Some(p), Some(q)] {
            assert_recovers(&eng, &opts, &parent, extra, &zero);
        }
    }

    // Z-floor (`words::prove_equal`) carry/quotient identity inside `Compares` / `Relations`.
    let opts32 = ParseOptions::width(Width::W32);
    assert_recovers(
        &eng,
        &opts32,
        "((((x >>u 4) + (y >>u 4) + (((x & 15) + (y & 15)) >>u 4)) & 0x0fffffff) == ((x + y) >>u 4))",
        None,
        "1:1",
    );
}

#[test]
fn scoped_relational_slice_and_affine_propagation_is_sound() {
    let eng = engine(false);
    let std_eng = Engine::standard();

    // 1. Positive `Select` arm and boolean `And` spine specialization across `16, 64, 256`.
    for w in [16u16, 64, 256] {
        let opts = ParseOptions::width(Width::new(w).unwrap());
        // Partial-slice guard specializes matching demanded slice `(x & 255) ^ (y & 255) -> 0`.
        assert_recovers(
            &eng,
            &opts,
            "select(trunc<8>(x) == trunc<8>(y), (x & 255) ^ (y & 255), z)",
            None,
            "select(trunc<8>(x) == trunc<8>(y), 0, z)",
        );
        // Full-width affine guard `x == y + 5` specializes `x - y -> 5`.
        assert_recovers(
            &eng,
            &opts,
            "select(x == y + 5, x - y, z)",
            None,
            "select(x == y + 5, 5, z)",
        );
        // Boolean `And` spine contradiction on slice equality vs inequality and affine offset.
        assert_recovers(
            &std_eng,
            &opts,
            "((x & 255) == (y & 255)) & (trunc<8>(x) != trunc<8>(y))",
            None,
            "0:1",
        );
        assert_recovers(&std_eng, &opts, "(x == y + 7) & (x - y != 7)", None, "0:1");
    }

    // 2. `Assumptions` projected slice congruence + `Reliance` tracking + unmasked soundness check.
    let mut cx = Context::new();
    let opts = ParseOptions::width(Width::W64);
    let pred = cx.parse("trunc<8>(x) == trunc<8>(y)", &opts).unwrap();
    let masked_diff = cx.parse("(x & 0x0f) ^ (y & 0x0f)", &opts).unwrap();
    let unmasked_diff = cx.parse("x ^ y", &opts).unwrap();
    let wider_diff = cx.parse("(x & 0x1ff) ^ (y & 0x1ff)", &opts).unwrap();

    let mut assump = bitwright::Assumptions::new();
    let cid = assump.assume_true(&mut cx, pred).unwrap();
    let out = std_eng
        .run(
            &mut cx,
            &[masked_diff, unmasked_diff, wider_diff],
            Run::default().with_assumptions(&assump),
        )
        .unwrap();
    assert_eq!(out.roots[0].expr, cx.parse("0", &opts).unwrap());
    assert!(out.roots[0].relies_on.may_use(cid));

    // Soundness: unmasked `x ^ y` and wider `(x & 0x1ff) ^ (y & 0x1ff)` MUST NOT collapse to 0!
    // Evaluate at `x = 0x12a`, `y = 0x02a` (which satisfies `trunc<8>(x) == trunc<8>(y) == 0x2a`).
    let env = [
        (
            bitwright::SymbolKey::from("x"),
            BitVec::from_u64(Width::W64, 0x12a).unwrap(),
        ),
        (
            bitwright::SymbolKey::from("y"),
            BitVec::from_u64(Width::W64, 0x02a).unwrap(),
        ),
    ];
    let vals = cx
        .eval(
            &[
                unmasked_diff,
                out.roots[1].expr,
                wider_diff,
                out.roots[2].expr,
            ],
            env.as_slice(),
        )
        .unwrap();
    assert_eq!(vals[0], vals[1]);
    assert_ne!(vals[1], BitVec::zero(Width::W64));
    assert_eq!(vals[2], vals[3]);
    assert_ne!(vals[3], BitVec::zero(Width::W64));

    // Near-miss `Select` guard (`trunc<8>(x) == trunc<8>(y)` guarding `x & 511`) must be refuted.
    let opts16 = ParseOptions::width(Width::W16);
    check_pair(
        &opts16,
        "select(trunc<8>(x) == trunc<8>(y), x & 511, t)",
        "select(trunc<8>(x) == trunc<8>(y), y & 511, t)",
        false,
    );
}
