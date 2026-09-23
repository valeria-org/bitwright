//! Invertibility on a real keyed mixer (murmur-style: odd multiplies around a data-dependent
//! xorshift), through the public API: the rewrites the proofs about it license, the ones they
//! refuse (each with its counterexample), invertibility queries, extension operations that
//! declare their inverses, and a finite-domain fact linked as a rule.

use std::sync::Arc;

use bitwright::engine::{Engine, Run, Strategy};
use bitwright::ext::{ExtError, ExtOp, ExtSig, Invertible, Registry};
use bitwright::rules::RuleProgram;
use bitwright::{
    BinOp, BitVec, CmpOpExt, Context, ContextConfig, Expr, FnEnv, KnownBits, ParseOptions, Query,
    SymbolKey, Truth, Width,
};

const C: u64 = 0x87c3_7b91_1142_53d5;
const K1: u64 = 0xd322_0fb7_8e33_751f;
const K1_INV: u64 = 0xcfcb_c386_7989_c6df;
const K2: u64 = 0xfa17_3d6f_19f3_0f7d;
const K3: u64 = 0xd703_63ea_b411_220b;
const K3_INV: u64 = 0xfeed_9c08_5b34_d9a3;
const K4: u64 = 0xeb00_9e78_8015_7ecb;
const K4_INV: u64 = 0xe1b0_4a3f_069d_76e3;

fn k(cx: &mut Context, v: u64) -> Expr {
    cx.constant_u64(Width::W64, v).unwrap()
}

/// `S(h) = h ^ ((h >>u 32) >>u (h >>u 60))`: changes only bits 0 to 27, and is an involution.
fn s(cx: &mut Context, h: Expr) -> Expr {
    let (a, b) = (k(cx, 32), k(cx, 60));
    let hi = cx.bin(BinOp::LShr, h, a).unwrap();
    let n = cx.bin(BinOp::LShr, h, b).unwrap();
    let g = cx.bin(BinOp::LShr, hi, n).unwrap();
    cx.bin(BinOp::Xor, h, g).unwrap()
}

fn mul(cx: &mut Context, x: Expr, c: u64) -> Expr {
    let c = k(cx, c);
    cx.bin(BinOp::Mul, x, c).unwrap()
}

fn xor(cx: &mut Context, x: Expr, c: u64) -> Expr {
    let c = k(cx, c);
    cx.bin(BinOp::Xor, x, c).unwrap()
}

/// The murmur mixer `F(x) = S(x * C) * C`.
fn f(cx: &mut Context, x: Expr) -> Expr {
    let m = mul(cx, x, C);
    let s = s(cx, m);
    mul(cx, s, C)
}

/// The keyed mixer `F_K(x) = S((x ^ K) * K) * K`.
fn fk(cx: &mut Context, key: u64, x: Expr) -> Expr {
    let t = xor(cx, x, key);
    let m = mul(cx, t, key);
    let s = s(cx, m);
    mul(cx, s, key)
}

/// Its inverse `(S(y * K⁻¹) * K⁻¹) ^ K`.
fn fk_inv(cx: &mut Context, key: u64, inv: u64, y: Expr) -> Expr {
    let m = mul(cx, y, inv);
    let s = s(cx, m);
    let t = mul(cx, s, inv);
    xor(cx, t, key)
}

fn sym(cx: &mut Context, name: &str) -> Expr {
    cx.symbol(name, Width::W64).unwrap()
}

fn at(cx: &mut Context, e: Expr, env: &[(&str, u64)]) -> BitVec {
    let env: Vec<(SymbolKey, BitVec)> = env
        .iter()
        .map(|(n, v)| {
            (
                SymbolKey::from(*n),
                BitVec::from_u64(Width::W64, *v).unwrap(),
            )
        })
        .collect();
    let env = FnEnv(|key: &SymbolKey, _| env.iter().find(|(k, _)| k == key).map(|(_, v)| *v));
    cx.eval(&[e], &env).unwrap()[0]
}

fn simplify(cx: &mut Context, e: Expr) -> Expr {
    Engine::standard().simplify(cx, e).unwrap().expr
}

#[test]
fn positive_rewrites() {
    let mut cx = Context::new();
    let (x, y) = (sym(&mut cx, "x"), sym(&mut cx, "y"));
    let zero = k(&mut cx, 0);

    // P7: F_K(x) = 0 has exactly one solution, x = K.
    let a = fk(&mut cx, K1, x);
    let e = cx.cmp(CmpOpExt::Eq, a, zero).unwrap();
    let k0 = k(&mut cx, K1);
    let want = cx.cmp(CmpOpExt::Eq, x, k0).unwrap();
    assert_eq!(simplify(&mut cx, e), want);

    // P5 with R1: equal hashes under one key, equal inputs.
    let (a, b) = (fk(&mut cx, K2, x), fk(&mut cx, K2, y));
    let e = cx.cmp(CmpOpExt::Eq, a, b).unwrap();
    let want = cx.cmp(CmpOpExt::Eq, x, y).unwrap();
    assert_eq!(simplify(&mut cx, e), want);

    // P5 with R2: a hash compared with a constant is the input compared with its preimage.
    let c = 0x0123_4567_89ab_cdef;
    let a = fk(&mut cx, K3, x);
    let k1 = k(&mut cx, c);
    let e = cx.cmp(CmpOpExt::Ne, a, k1).unwrap();
    let k2 = k(&mut cx, c);
    let inv = fk_inv(&mut cx, K3, K3_INV, k2);
    let pre = cx.as_const(inv).unwrap().unwrap().to_u64().unwrap();
    let k3 = k(&mut cx, pre);
    let want = cx.cmp(CmpOpExt::Ne, x, k3).unwrap();
    assert_eq!(simplify(&mut cx, e), want);
    assert_eq!(at(&mut cx, a, &[("x", pre)]).to_u64(), Some(c));

    // R3: the round trip.
    let a = fk(&mut cx, K4, x);
    let e = fk_inv(&mut cx, K4, K4_INV, a);
    assert_eq!(simplify(&mut cx, e), x);

    // Projection through the mixer: S changes only bits 0 to 27.
    let a = fk(&mut cx, K1, x);
    let m = mul(&mut cx, a, K1_INV);
    let k4 = k(&mut cx, 28);
    let e = cx.bin(BinOp::LShr, m, k4).unwrap();
    let t = xor(&mut cx, x, K1);
    let t = mul(&mut cx, t, K1);
    let k5 = k(&mut cx, 28);
    let want = cx.bin(BinOp::LShr, t, k5).unwrap();
    assert_eq!(simplify(&mut cx, e), want);
}

#[test]
fn refused_rewrites_and_their_counterexamples() {
    let mut cx = Context::new();
    let (x, y) = (sym(&mut cx, "x"), sym(&mut cx, "y"));

    // The projection one bit lower is wrong at h = 0x0fffffffffffffff.
    let a = fk(&mut cx, K1, x);
    let m = mul(&mut cx, a, K1_INV);
    let k6 = k(&mut cx, 27);
    let e = cx.bin(BinOp::LShr, m, k6).unwrap();
    let t = xor(&mut cx, x, K1);
    let t = mul(&mut cx, t, K1);
    let k7 = k(&mut cx, 27);
    let wrong = cx.bin(BinOp::LShr, t, k7).unwrap();
    let r = simplify(&mut cx, e);
    assert_ne!(r, wrong);
    let h = 0x0fff_ffff_ffff_ffffu64;
    let x0 = h.wrapping_mul(K1_INV) ^ K1;
    assert_ne!(
        at(&mut cx, e, &[("x", x0)]),
        at(&mut cx, wrong, &[("x", x0)])
    );
    assert_eq!(at(&mut cx, e, &[("x", x0)]), at(&mut cx, r, &[("x", x0)]));

    // Feeding the input back in: mix(x) = F(x) ^ x is not injective.
    let fa = f(&mut cx, x);
    let ma = cx.bin(BinOp::Xor, fa, x).unwrap();
    let fb = f(&mut cx, y);
    let mb = cx.bin(BinOp::Xor, fb, y).unwrap();
    let e = cx.cmp(CmpOpExt::Eq, ma, mb).unwrap();
    let r = simplify(&mut cx, e);
    let (p, q) = (0x0c9c_4900_0000_0000, 0xbb23_b900_0000_0000);
    assert_eq!(
        at(&mut cx, ma, &[("x", p)]).to_u64(),
        Some(0x28d8_4847_4467_3db3)
    );
    assert_eq!(
        at(&mut cx, ma, &[("x", q)]).to_u64(),
        Some(0x28d8_4847_4467_3db3)
    );
    assert!(at(&mut cx, r, &[("x", p), ("y", q)]).bit(0).unwrap());

    // Two keys xored: not injective for any pair (the colliding pair for K1, K2 below).
    let keys = [K1, K2, K3, K4];
    for (i, &ka) in keys.iter().enumerate() {
        for &kb in &keys[i + 1..] {
            let (a1, b1) = (fk(&mut cx, ka, x), fk(&mut cx, kb, x));
            let xa = cx.bin(BinOp::Xor, a1, b1).unwrap();
            let (a2, b2) = (fk(&mut cx, ka, y), fk(&mut cx, kb, y));
            let xb = cx.bin(BinOp::Xor, a2, b2).unwrap();
            let e = cx.cmp(CmpOpExt::Eq, xa, xb).unwrap();
            let r = simplify(&mut cx, e);
            assert_ne!(r, cx.cmp(CmpOpExt::Eq, x, y).unwrap());
            if (ka, kb) == (K1, K2) {
                let (p, q) = (0x263a_0926_a928_bf8e, 0x9e7d_25b9_28ab_d0ae);
                assert_eq!(at(&mut cx, xa, &[("x", p)]), at(&mut cx, xa, &[("x", q)]));
                assert!(at(&mut cx, r, &[("x", p), ("y", q)]).bit(0).unwrap());
            }
            let q = Query::Injective { e: xa, of: x };
            assert_ne!(cx.prove(q).unwrap(), Truth::True);
        }
    }

    // Two keys ored: zero has no preimage at all, so the comparison is false, not solved.
    let (a, b) = (fk(&mut cx, K1, x), fk(&mut cx, K2, x));
    let o = cx.bin(BinOp::Or, a, b).unwrap();
    let k8 = k(&mut cx, 0);
    let e = cx.cmp(CmpOpExt::Eq, o, k8).unwrap();
    assert_eq!(
        simplify(&mut cx, e),
        cx.constant(&BitVec::from_bool(false)).unwrap()
    );

    // Ordering does not survive a bijection: nothing is concluded about x.
    let a = fk(&mut cx, K1, x);
    for op in [CmpOpExt::Ult, CmpOpExt::Ule, CmpOpExt::Sgt] {
        let k9 = k(&mut cx, 0x1000);
        let e = cx.cmp(op, a, k9).unwrap();
        let r = simplify(&mut cx, e);
        assert_eq!(r, e, "{}", cx.display(r));
    }
}

#[test]
fn invertibility_queries() {
    let mut cx = Context::new();
    let (x, p) = (sym(&mut cx, "x"), sym(&mut cx, "p"));
    let ask = |cx: &mut Context, e: Expr, of: Expr| {
        (
            cx.prove(Query::Injective { e, of }).unwrap(),
            cx.prove(Query::Bijective { e, of }).unwrap(),
        )
    };
    let yes = (Truth::True, Truth::True);
    let unknown = (Truth::Unknown, Truth::Unknown);
    // Bijections, and chains of them.
    let e = fk(&mut cx, K1, x);
    assert_eq!(ask(&mut cx, e, x), yes);
    let e = s(&mut cx, x);
    assert_eq!(ask(&mut cx, e, x), yes);
    let e = f(&mut cx, x);
    let e = xor(&mut cx, e, 0x5a5a);
    assert_eq!(ask(&mut cx, e, x), yes);
    let e = cx.bin(BinOp::RotL, x, p).unwrap();
    assert_eq!(ask(&mut cx, e, x), yes);
    // Not provably injective (and in fact not): the answer is only "unknown".
    let fx = f(&mut cx, x);
    let e = cx.bin(BinOp::Xor, fx, x).unwrap();
    assert_eq!(ask(&mut cx, e, x), unknown);
    let e = mul(&mut cx, x, 6);
    assert_eq!(ask(&mut cx, e, x), unknown);
    // Injective into a wider width, never bijective; independent of `of`: neither.
    let x32 = cx.symbol("x32", Width::W32).unwrap();
    let e = cx.zext(x32, Width::W64).unwrap();
    assert_eq!(ask(&mut cx, e, x32), (Truth::True, Truth::False));
    let e = fk(&mut cx, K1, p);
    assert_eq!(ask(&mut cx, e, x), (Truth::False, Truth::False));

    // A T-function on 22 bits: u - (((u << 1) | b) & h) is a bijection of u, for any b, h;
    // with a shift of 0 it is not (bit i reads bit i).
    let o = ParseOptions::width(Width::new(22).unwrap());
    let u = cx.parse("u", &o).unwrap();
    let t = cx.parse("u - (((u << 1) | b) & h)", &o).unwrap();
    assert_eq!(ask(&mut cx, t, u), yes);
    let t0 = cx.parse("u - ((u | b) & h)", &o).unwrap();
    assert_eq!(ask(&mut cx, t0, u), unknown);
    // Both sides with the same b and h: cancelled; with different ones: not.
    let e = cx
        .parse("u - (((u << 1) | b) & h) == v - (((v << 1) | b) & h)", &o)
        .unwrap();
    let want = cx.parse("u == v", &o).unwrap();
    assert_eq!(simplify(&mut cx, e), want);
    let e = cx
        .parse("u - (((u << 1) | b) & h) == v - (((v << 1) | c) & h)", &o)
        .unwrap();
    assert_ne!(simplify(&mut cx, e), want);
}

// ----- extension operations that declare their inverses --------------------------------------

/// The keyed mixer as one operation, `@t.fk(key, x)`: a bijection of `x` for every odd key.
struct KeyedMixer;

fn mixer_value(key: u64, x: u64) -> u64 {
    let s = |h: u64| h ^ ((h >> 32) >> (h >> 60));
    s((x ^ key).wrapping_mul(key)).wrapping_mul(key)
}

fn inverse_odd(key: u64) -> u64 {
    let mut i: u64 = 1;
    for _ in 0..6 {
        i = i.wrapping_mul(2u64.wrapping_sub(key.wrapping_mul(i)));
    }
    i
}

impl ExtOp for KeyedMixer {
    fn name(&self) -> &str {
        "t.fk"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b] if a.bits() == 64 && b.bits() == 64 => Ok(ExtSig::new(&[("h", Width::W64)])),
            _ => Err("a 64-bit key and value".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let (key, x) = (args[0].to_u64().unwrap_or(0), args[1].to_u64().unwrap_or(0));
        out[0] = BitVec::wrapping_from_u64(Width::W64, mixer_value(key, x));
    }
    fn invertible(&self, _output: u8, arg: u8, args: &[KnownBits]) -> Invertible {
        // In the value, when the key is odd.
        if arg == 1 && args[0].bit(0) == Some(true) {
            Invertible::Bijective
        } else {
            Invertible::No
        }
    }
    fn invert(&self, _output: u8, _arg: u8, args: &[BitVec], value: &BitVec) -> Option<BitVec> {
        let (key, y) = (args[0].to_u64()?, value.to_u64()?);
        let i = inverse_odd(key);
        let s = |h: u64| h ^ ((h >> 32) >> (h >> 60));
        Some(BitVec::wrapping_from_u64(
            Width::W64,
            s(y.wrapping_mul(i)).wrapping_mul(i) ^ key,
        ))
    }
}

/// A pointer compaction `@t.compact(x, p)`: the 32-bit pointer xored and rotated by its 8-bit
/// tag, with the tag kept above it. Injective in `x` for each fixed `p` only.
struct Compact;

fn spread(p: u64) -> u64 {
    p * 0x0101_0101
}

impl ExtOp for Compact {
    fn name(&self) -> &str {
        "t.compact"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b] if a.bits() == 32 && b.bits() == 8 => Ok(ExtSig::new(&[("c", Width::W64)])),
            _ => Err("a 32-bit pointer and an 8-bit tag".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let (x, p) = (args[0].to_u64().unwrap_or(0), args[1].to_u64().unwrap_or(0));
        let lo = ((x ^ spread(p)) as u32).rotate_left(p as u32 % 32);
        out[0] = BitVec::wrapping_from_u64(Width::W64, (p << 32) | u64::from(lo));
    }
    fn invertible(&self, _output: u8, arg: u8, _args: &[KnownBits]) -> Invertible {
        if arg == 0 {
            Invertible::Injective
        } else {
            Invertible::No
        }
    }
    fn invert(&self, _output: u8, _arg: u8, args: &[BitVec], value: &BitVec) -> Option<BitVec> {
        let (p, c) = (args[1].to_u64()?, value.to_u64()?);
        if c >> 32 != p {
            return None;
        }
        let x = u64::from((c as u32).rotate_right(p as u32 % 32)) ^ spread(p);
        Some(BitVec::wrapping_from_u64(Width::W32, x))
    }
}

#[test]
fn extension_operations_declare_their_inverses() {
    let reg = Arc::new(
        Registry::builder()
            .register(KeyedMixer)
            .unwrap()
            .register(Compact)
            .unwrap()
            .build(),
    );
    let mut cx = Context::with_registry(ContextConfig::default(), reg.clone());
    let (op, cp) = (reg.id("t.fk").unwrap(), reg.id("t.compact").unwrap());
    let (x, y, key) = (sym(&mut cx, "x"), sym(&mut cx, "y"), sym(&mut cx, "key"));
    let k1 = k(&mut cx, K1);
    let call = |cx: &mut Context, a: Expr, b: Expr| cx.ext(op, &[a, b]).unwrap()[0];

    // Cancelled on both sides, and solved at a constant.
    let (a, b) = (call(&mut cx, k1, x), call(&mut cx, k1, y));
    let e = cx.cmp(CmpOpExt::Eq, a, b).unwrap();
    assert_eq!(simplify(&mut cx, e), cx.cmp(CmpOpExt::Eq, x, y).unwrap());
    let c = k(&mut cx, 0x42);
    let e = cx.cmp(CmpOpExt::Eq, a, c).unwrap();
    let r = simplify(&mut cx, e);
    let pre = BitVec::from_u64(Width::W64, 0x42).unwrap();
    let want_x = KeyedMixer.invert(
        0,
        1,
        &[BitVec::from_u64(Width::W64, K1).unwrap(), pre],
        &pre,
    );
    let want = cx.constant(&want_x.unwrap()).unwrap();
    assert_eq!(r, cx.cmp(CmpOpExt::Eq, x, want).unwrap());
    // A key not known to be odd: nothing; the same key assumed odd: cancelled.
    let (a, b) = (call(&mut cx, key, x), call(&mut cx, key, y));
    let e = cx.cmp(CmpOpExt::Eq, a, b).unwrap();
    assert_eq!(simplify(&mut cx, e), e);
    let one = k(&mut cx, 1);
    let low = cx.bin(BinOp::And, key, one).unwrap();
    let odd = cx.cmp(CmpOpExt::Eq, low, one).unwrap();
    let mut assumptions = bitwright::Assumptions::new();
    let id = assumptions.assume_true(&mut cx, odd).unwrap();
    let out = Engine::standard()
        .run(&mut cx, &[e], Run::default().with_assumptions(&assumptions))
        .unwrap()
        .roots[0];
    assert_eq!(out.expr, cx.cmp(CmpOpExt::Eq, x, y).unwrap());
    assert!(out.relies_on.may_use(id));

    // Injective per fixed parameter only: across different tags nothing is concluded, and a
    // constant with another tag has no preimage.
    let o = ParseOptions::width(Width::W32);
    let (px, py) = (cx.parse("px", &o).unwrap(), cx.parse("py", &o).unwrap());
    let w8 = Width::W8;
    let (t1, t2) = (
        cx.constant_u64(w8, 1).unwrap(),
        cx.constant_u64(w8, 0).unwrap(),
    );
    let (a, b) = (
        cx.ext(cp, &[px, t1]).unwrap()[0],
        cx.ext(cp, &[py, t1]).unwrap()[0],
    );
    let e = cx.cmp(CmpOpExt::Eq, a, b).unwrap();
    assert_eq!(simplify(&mut cx, e), cx.cmp(CmpOpExt::Eq, px, py).unwrap());
    let b0 = cx.ext(cp, &[py, t2]).unwrap()[0];
    let e = cx.cmp(CmpOpExt::Eq, a, b0).unwrap();
    assert_eq!(simplify(&mut cx, e), e);
    let other_tag = cx.constant_u64(Width::W64, 2 << 32).unwrap();
    let e = cx.cmp(CmpOpExt::Eq, a, other_tag).unwrap();
    assert_eq!(
        simplify(&mut cx, e),
        cx.constant(&BitVec::from_bool(false)).unwrap()
    );
    assert_eq!(
        cx.prove(Query::Injective { e: a, of: px }).unwrap(),
        Truth::True
    );
    assert_eq!(
        cx.prove(Query::Bijective { e: a, of: px }).unwrap(),
        Truth::False
    );
}

/// A declaration the operation does not live up to is refused at registration.
#[test]
fn broken_declarations_are_refused() {
    /// Claims to be a bijection of `x`, but masks it.
    struct Masked;
    impl ExtOp for Masked {
        fn name(&self) -> &str {
            "t.masked"
        }
        fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
            match args {
                [a] => Ok(ExtSig::new(&[("m", *a)])),
                _ => Err("one argument".into()),
            }
        }
        fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
            out[0] =
                BitVec::apply_bin(BinOp::And, &args[0], &BitVec::smax(args[0].width())).unwrap();
        }
        fn invertible(&self, _: u8, _: u8, _: &[KnownBits]) -> Invertible {
            Invertible::Bijective
        }
        fn invert(&self, _: u8, _: u8, _: &[BitVec], value: &BitVec) -> Option<BitVec> {
            Some(*value)
        }
    }
    /// Declares an injection but has no inverse to show for it.
    struct Silent;
    impl ExtOp for Silent {
        fn name(&self) -> &str {
            "t.silent"
        }
        fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
            match args {
                [a] => Ok(ExtSig::new(&[("m", *a)])),
                _ => Err("one argument".into()),
            }
        }
        fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
            out[0] = BitVec::apply_un(bitwright::UnOp::Not, &args[0]).unwrap();
        }
        fn invertible(&self, _: u8, _: u8, _: &[KnownBits]) -> Invertible {
            Invertible::Injective
        }
    }
    for r in [
        Registry::builder().register(Masked).map(|_| ()),
        Registry::builder().register(Silent).map(|_| ()),
    ] {
        match r {
            Err(ExtError::Contract(_, why)) => assert!(why.contains("invert"), "{why}"),
            other => panic!("accepted: {other:?}"),
        }
    }
}

/// A fact proved by exhaustion elsewhere (below 2^32, `F_A(x) ^ F_B(x)` is the salt only at
/// `x = 0`) enters as a rule the host vouches for, guarded by the facts proving `x` fits.
#[test]
fn finite_domain_facts_as_rules() {
    let src = include_str!("invert_facts32.bwr");
    let program = RuleProgram::compile(src).unwrap();
    let engine = Engine::builder()
        .builtin()
        .unproven_program(program)
        .allow_unproven(true)
        .strategy(Strategy::standard().with_rule_groups(&["eos.facts32"]))
        .build()
        .unwrap();
    let (a, b, salt) = (
        0xcd90_63b6_53a0_c1b1,
        0xd215_910f_abd5_1aeb,
        0xd734_e14a_2ead_11b5u64,
    );
    let mut cx = Context::new();
    let x32 = cx.symbol("x", Width::W32).unwrap();
    let wide = sym(&mut cx, "wide");
    for (input, fits) in [(cx.zext(x32, Width::W64).unwrap(), true), (wide, false)] {
        let (fa, fb) = (fk(&mut cx, a, input), fk(&mut cx, b, input));
        let t = cx.bin(BinOp::Xor, fa, fb).unwrap();
        let t = xor(&mut cx, t, salt);
        let k10 = k(&mut cx, 0);
        let e = cx.cmp(CmpOpExt::Eq, t, k10).unwrap();
        let r = engine.simplify(&mut cx, e).unwrap().expr;
        if fits {
            let zero = cx.constant_u64(Width::W32, 0).unwrap();
            assert_eq!(
                r,
                cx.cmp(CmpOpExt::Eq, x32, zero).unwrap(),
                "{}",
                cx.display(r)
            );
        } else {
            // Not known to fit in 32 bits: the fact says nothing.
            let k11 = k(&mut cx, 0);
            assert_ne!(r, cx.cmp(CmpOpExt::Eq, wide, k11).unwrap());
        }
    }
}
