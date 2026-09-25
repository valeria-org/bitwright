//! Copying expressions between contexts (`Context::import`), and simplifying roots each on its
//! own, on threads (`Engine::run_each`).

use std::sync::Arc;

use bitwright::engine::{Each, Engine, Run, Stats, Strategy};
use bitwright::ext::{ExtOp, ExtSig, Registry};
use bitwright::{
    Assumptions, BinOp, BitVec, Context, ContextConfig, Expr, FnEnv, ParseOptions, PrintOptions,
    SymbolKey, Width,
};

fn text(cx: &Context, e: Expr) -> String {
    cx.display_with(e, PrintOptions::default().with_symbol_widths(true))
        .to_string()
}

/// Every symbol bound to a value derived from its key and `seed`.
fn values_at(cx: &mut Context, roots: &[Expr], seed: u64) -> Vec<BitVec> {
    let env = FnEnv(move |k: &SymbolKey, w: Width| {
        let mut h = seed ^ 0x9e37_79b9_7f4a_7c15;
        for b in k.to_string().bytes() {
            h = (h ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3);
        }
        Some(BitVec::wrapping_from_limbs(
            w,
            &[h, h.rotate_left(17), !h, h ^ 0x55],
        ))
    });
    cx.eval(roots, &env).unwrap()
}

const TEXTS: [&str; 8] = [
    "(x + y) * (x ^ 0x1234) - z",
    "select(x <u y, x, y) & 0xff",
    "zext<64>(trunc<16>(x)) | zext<64>(y)",
    "bswap(rotl(x, 3)) + popcnt(y)",
    "(x ^ y) + 2 * (x & y)",
    "(x | y) - (x & ~y) + 0",
    "udiv(x, 7) * 7 + urem(x, 7)",
    "sext<64>(x) >>s 3",
];

fn parsed(cx: &mut Context) -> Vec<Expr> {
    let o = ParseOptions::width(Width::W32);
    TEXTS.iter().map(|t| cx.parse(t, &o).unwrap()).collect()
}

#[test]
fn import_copies_structure_and_values() {
    let mut a = Context::new();
    let roots = parsed(&mut a);
    let mut b = Context::new();
    let got = b.import(&a, &roots).unwrap();
    for (r, g) in roots.iter().zip(&got) {
        assert_eq!(text(&a, *r), text(&b, *g));
    }
    for seed in 0..8 {
        assert_eq!(
            values_at(&mut a, &roots, seed),
            values_at(&mut b, &got, seed)
        );
    }
    // The copies are hash-consed: importing again finds them.
    assert_eq!(b.import(&a, &roots).unwrap(), got);
    // A context that already has some of the structure shares it.
    let before = b.len();
    let o = ParseOptions::width(Width::W32);
    let sub = a.parse("x ^ 0x1234", &o).unwrap();
    b.import(&a, &[sub]).unwrap();
    assert_eq!(b.len(), before);
}

#[test]
fn import_keeps_symbol_keys_and_their_widths() {
    let mut a = Context::new();
    let x = a.parse("x + 1", &ParseOptions::width(Width::W32)).unwrap();
    let mut b = Context::new();
    let y = b.parse("x", &ParseOptions::width(Width::W32)).unwrap();
    let got = b.import(&a, &[x]).unwrap()[0];
    // The imported `x` is b's `x`.
    let one = b.constant_u64(Width::W32, 1).unwrap();
    assert_eq!(got, b.add(y, one).unwrap());
    // A key b has at another width is an error.
    let mut c = Context::new();
    c.parse("x", &ParseOptions::width(Width::W8)).unwrap();
    assert!(c.import(&a, &[x]).is_err());
}

#[test]
fn import_copies_wide_constants_and_floats() {
    let mut a = Context::new();
    let o = ParseOptions::width(Width::new(300).unwrap());
    let w = a
        .parse(
            "x * 0x123456789abcdef0123456789abcdef0123456789 + udiv(y, 3)",
            &o,
        )
        .unwrap();
    let f = a
        .parse(
            "fp.add.rne.f32(fp.mul.rne.f32(p, q), fp.sqrt.rtz.f32(p))",
            &ParseOptions::width(Width::W32),
        )
        .unwrap();
    let mut b = Context::new();
    let got = b.import(&a, &[w, f]).unwrap();
    assert_eq!(text(&a, w), text(&b, got[0]));
    assert_eq!(text(&a, f), text(&b, got[1]));
    for seed in 0..8 {
        assert_eq!(
            values_at(&mut a, &[w, f], seed),
            values_at(&mut b, &got, seed)
        );
    }
}

struct Mix;

impl ExtOp for Mix {
    fn name(&self) -> &str {
        "t.mix"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a] => Ok(ExtSig::new(&[("h", *a)])),
            _ => Err("one operand".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let k = BitVec::wrapping_from_u64(args[0].width(), 0x9e37_79b9);
        out[0] = BitVec::apply_bin(BinOp::Mul, &args[0], &k).unwrap();
    }
}

#[test]
fn import_needs_the_same_extension_operations() {
    let r = Arc::new(Registry::builder().register(Mix).unwrap().build());
    let mut a = Context::with_registry(ContextConfig::default(), r.clone());
    let x = a.parse("x", &ParseOptions::width(Width::W32)).unwrap();
    let mix = r.id("t.mix").unwrap();
    let m = a.ext_output(mix, 0, &[x]).unwrap();
    let e = a.add(m, x).unwrap();
    let mut b = Context::with_registry(ContextConfig::default(), r.clone());
    let got = b.import(&a, &[e]).unwrap()[0];
    assert_eq!(text(&a, e), text(&b, got));
    // Without the operation: an error, not a wrong node.
    let mut c = Context::new();
    assert!(c.import(&a, &[e]).is_err());
}

fn deobfuscate() -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap()
}

#[test]
fn run_each_answers_as_calls_with_one_root_would() {
    let engine = deobfuscate();
    let mut cx = Context::new();
    let mut roots = parsed(&mut cx);
    // A repeated root is answered at each position.
    roots.push(roots[4]);
    // The expectation: each root alone, in a fresh context.
    let mut want: Vec<(String, bitwright::engine::End)> = Vec::new();
    let mut stats = Stats::default();
    for t in TEXTS {
        let mut solo = Context::new();
        let x = solo.parse(t, &ParseOptions::width(Width::W32)).unwrap();
        let out = engine.run(&mut solo, &[x], Run::default()).unwrap();
        want.push((text(&solo, out.roots[0].expr), out.roots[0].end));
        stats.absorb(&out.stats);
    }
    want.push(want[4].clone());
    for threads in [1, 3, 16] {
        let out = engine
            .run_each(&mut cx, &roots, Each::default().with_threads(threads))
            .unwrap();
        assert_eq!(out.roots.len(), roots.len());
        for (i, r) in out.roots.iter().enumerate() {
            assert_eq!(
                (text(&cx, r.expr), r.end),
                want[i],
                "root {i} with {threads} threads"
            );
            assert_eq!(r.changed, r.expr != roots[i]);
        }
        assert_eq!(out.stats, stats, "statistics with {threads} threads");
    }
}

#[test]
fn run_each_reads_the_assumptions() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let root = cx.parse("x & 15", &o).unwrap();
    let other = cx.parse("y + 0", &o).unwrap();
    let p = cx.parse("x <u 16", &o).unwrap();
    let mut a = Assumptions::new();
    a.assume_true(&mut cx, p).unwrap();
    let out = engine
        .run_each(
            &mut cx,
            &[root, other],
            Each::default().with_threads(2).with_assumptions(&a),
        )
        .unwrap();
    let x = cx.parse("x", &o).unwrap();
    assert_eq!(out.roots[0].expr, x);
    assert!(!out.roots[0].relies_on.is_none());
    let seq = engine
        .run(&mut cx, &[root], Run::default().with_assumptions(&a))
        .unwrap();
    assert_eq!(seq.roots[0].relies_on, out.roots[0].relies_on);
    assert!(out.roots[1].relies_on.is_none());
}
