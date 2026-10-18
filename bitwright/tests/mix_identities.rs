//! Invertible mixes as a prover meets them: `H(x, C) = C·(t ^ ((t >>u 32) >>u (t >>u 60)))`
//! with `t = C·(x ^ C)` and `C` odd, the xor-fold whose shift amount is a function of the value,
//! and murmur3's 32-bit finalizer. The word-level identities (equal mixes of one key are equal
//! inputs, a mix at a constant is its unique preimage, a round with its inverse is the input)
//! decide these questions with no search, and they are checked here at every input of
//! scaled-down mixes, every shift amount included, against an independent scalar oracle. A
//! guard combining mixes of one value under several keys is not injective; with the other lane
//! free it is satisfiable, and the prover finds a value for it.
#![cfg(all(feature = "prove", feature = "mba"))]

use bitwright::engine::Engine;
use bitwright::prove::{self, Config, Outcome, Question};
use bitwright::{BitVec, Context, Expr, ParseOptions, SymbolKey, Width};

/// Odd keys of one function of a protected driver.
const KEYS: [u64; 9] = [
    0x87c3_7b91_1142_53d5,
    0xd933_008c_f055_faf9,
    0xf215_3a1b_2303_b72d,
    0xf374_ef4e_753c_875d,
    0xc354_c462_2bc1_0a31,
    0xfc14_d111_f5d3_19a5,
    0xc8ff_640a_8b8c_13dd,
    0xfd6a_3327_3321_27b3,
    0xd219_840c_12f8_b8e5,
];

/// The protector's mix, on words.
fn hash(x: u64, c: u64) -> u64 {
    let t = c.wrapping_mul(x ^ c);
    let r = (t >> 32) >> (t >> 60);
    c.wrapping_mul(t ^ r)
}

/// The inverse of an odd `c` modulo 2^64 by Newton's iteration.
fn inverse_odd(c: u64) -> u64 {
    let mut i = c;
    for _ in 0..6 {
        i = i.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(i)));
    }
    assert_eq!(c.wrapping_mul(i), 1);
    i
}

/// The inverse mix, on words.
fn unhash(h: u64, c: u64) -> u64 {
    let ci = inverse_odd(c);
    let u = h.wrapping_mul(ci);
    let t = u ^ ((u >> 32) >> (u >> 60));
    t.wrapping_mul(ci) ^ c
}

/// The mix as an expression.
fn h(v: &str, c: u64) -> String {
    let t = format!("(0x{c:x} * ({v} ^ 0x{c:x}))");
    format!("(0x{c:x} * ({t} ^ (({t} >>u 32) >>u ({t} >>u 60))))")
}

/// The inverse mix as an expression.
fn unh(v: &str, c: u64) -> String {
    let ci = inverse_odd(c);
    let u = format!("({v} * 0x{ci:x})");
    format!("((({u} ^ (({u} >>u 32) >>u ({u} >>u 60))) * 0x{ci:x}) ^ 0x{c:x})")
}

fn parse(cx: &mut Context, src: &str, w: Width) -> Expr {
    cx.parse(src, &ParseOptions::width(w))
        .unwrap_or_else(|e| panic!("{src}: {e}"))
}

/// Asks whether `src` holds, and requires a proof by simplification alone: no circuit, no
/// search.
fn proved_at_word_level(src: &str, w: Width) {
    let mut cx = Context::new();
    let p = parse(&mut cx, src, w);
    let cfg = Config::default();
    let mut q = Question::valid(&mut cx, p, &cfg).unwrap();
    let out = q.solve(&mut cx, cfg.limits()).unwrap();
    assert!(matches!(out, Outcome::Proved(_)), "{src}: {out:?}");
    let s = q.stats();
    assert!(s.simplification.decided, "{src}: not decided by the engine");
    assert_eq!((s.nodes, s.conflicts, s.searches), (0, 0, 0), "{src}");
}

#[test]
fn equal_mixes_of_one_key_are_equal_inputs() {
    for c in KEYS {
        let (hx, hy) = (h("x", c), h("y", c));
        proved_at_word_level(&format!("({hx} == {hy}) == (x == y)"), Width::W64);
        proved_at_word_level(&format!("({hx} != {hy}) == (x != y)"), Width::W64);
    }
}

#[test]
fn a_mix_at_a_constant_is_its_preimage() {
    for (i, c) in KEYS.into_iter().enumerate() {
        for k in [0, 1, 0x1234, 0x079c_2a2c_658e_1c19, u64::MAX, c] {
            let x = unhash(k, c);
            assert_eq!(hash(x, c), k, "the scalar oracle at key {i}");
            proved_at_word_level(
                &format!("({} == 0x{k:x}) == (x == 0x{x:x})", h("x", c)),
                Width::W64,
            );
        }
    }
}

#[test]
fn a_mix_and_its_inverse_cancel() {
    for c in KEYS {
        proved_at_word_level(&format!("{} == x", unh(&h("x", c), c)), Width::W64);
        proved_at_word_level(&format!("{} == x", h(&unh("x", c), c)), Width::W64);
    }
}

/// The 32-bit murmur3 finalizer and its inverse (the shift by 13 takes two correction terms to
/// undo).
#[test]
fn murmur3_finalizer_lemmas() {
    let xs = |v: &str, s: u32| format!("(({v}) ^ (({v}) >>u {s}))");
    let mul = |v: &str, k: u32| format!("(({v}) * 0x{k:x})");
    let mix = |v: &str| {
        let a = xs(v, 16);
        let a = mul(&a, 0x85eb_ca6b);
        let a = xs(&a, 13);
        let a = mul(&a, 0xc2b2_ae35);
        xs(&a, 16)
    };
    let unmix = |v: &str| {
        let a = xs(v, 16);
        let a = mul(&a, 0x7ed1_b41d);
        let a = format!("(({a}) ^ (({a}) >>u 13) ^ (({a}) >>u 26))");
        let a = mul(&a, 0xa5cb_9243);
        xs(&a, 16)
    };
    let w = Width::W32;
    proved_at_word_level(&format!("{} == x", unmix(&mix("x"))), w);
    proved_at_word_level(&format!("{} != {}", mix("x"), mix("x + 1")), w);
    proved_at_word_level(&format!("({} == {}) == (x == y)", mix("x"), mix("y")), w);
}

/// The scaled-down mix of `w` bits (8 or 16): `C·(t ^ ((t >>u w/2) >>u (t >>u (w − s))))` with
/// a shift amount of `s` bits, from 0 to `2^s − 1 < w/2`.
fn small_mix(v: &str, c: u64, w: u32, s: u32) -> String {
    let t = format!("(0x{c:x} * ({v} ^ 0x{c:x}))");
    let (half, top) = (w / 2, w - s);
    format!("(0x{c:x} * ({t} ^ (({t} >>u {half}) >>u ({t} >>u {top}))))")
}

fn small_mix_word(x: u64, c: u64, w: u32, s: u32) -> u64 {
    let m = (1u64 << w) - 1;
    let t = c.wrapping_mul(x ^ c) & m;
    let r = (t >> (w / 2)) >> (t >> (w - s));
    c.wrapping_mul(t ^ r) & m
}

fn env(w: Width, vals: &[(&str, u64)]) -> Vec<(SymbolKey, BitVec)> {
    vals.iter()
        .map(|&(k, v)| (SymbolKey::from(k), BitVec::wrapping_from_u64(w, v)))
        .collect()
}

/// What the engine makes of the mix's identities agrees with the scalar oracle at every input
/// (and so at every shift amount, 0 included) of 8-bit mixes, and at every input of a 16-bit
/// one solved at constants.
#[test]
fn small_mixes_are_exact_at_every_input() {
    let eng = Engine::standard();
    let w8 = Width::W8;
    for c in [0x3bu64, 0xa5, 0xc7, 0x01, 0xff] {
        // Shift amounts of 1 and 2 bits: 0..=1 and 0..=3, below the half width.
        for s in [1, 2] {
            let mut cx = Context::new();
            let src = format!("{} == {}", small_mix("x", c, 8, s), small_mix("y", c, 8, s));
            let e = parse(&mut cx, &src, w8);
            let r = eng.simplify(&mut cx, e).unwrap().expr;
            assert_eq!(cx.display(r).to_string(), "x == y", "{src}");
            for k in 0..256u64 {
                let src = format!("{} == {k}", small_mix("x", c, 8, s));
                let e = parse(&mut cx, &src, w8);
                let r = eng.simplify(&mut cx, e).unwrap().expr;
                for x in 0..256u64 {
                    let want = small_mix_word(x, c, 8, s) == k;
                    let got = cx.eval(&[r], &env(w8, &[("x", x)])[..]).unwrap()[0];
                    assert_eq!(!got.is_zero(), want, "{src} at x = {x}: {}", cx.display(r));
                }
            }
        }
    }
    let w16 = Width::W16;
    let c = 0x9e37u64;
    let mut cx = Context::new();
    for k in [0u64, 1, 0x1234, 0xffff] {
        let src = format!("{} == {k}", small_mix("x", c, 16, 3));
        let e = parse(&mut cx, &src, w16);
        let r = eng.simplify(&mut cx, e).unwrap().expr;
        for x in 0..1u64 << 16 {
            let want = small_mix_word(x, c, 16, 3) == k;
            let got = cx.eval(&[r], &env(w16, &[("x", x)])[..]).unwrap()[0];
            assert_eq!(!got.is_zero(), want, "{src} at x = {x}: {}", cx.display(r));
        }
    }
}

/// Xorshifts below half the width (inverted by ⌈w/s⌉ − 1 correction terms), right and left,
/// at every input of 8 bits.
#[test]
fn small_xorshifts_are_exact_at_every_input() {
    let eng = Engine::standard();
    let w8 = Width::W8;
    for (f, inv) in [
        ("((v) ^ ((v) >>u 3))", "((v) ^ ((v) >>u 3) ^ ((v) >>u 6))"),
        ("((v) ^ ((v) << 3))", "((v) ^ ((v) << 3) ^ ((v) << 6))"),
        (
            "((v) ^ ((v) >>u 2))",
            "((v) ^ ((v) >>u 2) ^ ((v) >>u 4) ^ ((v) >>u 6))",
        ),
    ] {
        let at = |v: &str| f.replace('v', v);
        let mut cx = Context::new();
        // Equal images, equal inputs.
        let src = format!("{} == {}", at("x"), at("y"));
        let e = parse(&mut cx, &src, w8);
        let r = eng.simplify(&mut cx, e).unwrap().expr;
        assert_eq!(cx.display(r).to_string(), "x == y", "{src}");
        // The inverse undoes it.
        let src = inv.replace('v', &at("x"));
        let e = parse(&mut cx, &src, w8);
        let r = eng.simplify(&mut cx, e).unwrap().expr;
        assert_eq!(cx.display(r).to_string(), "x", "{src}");
        // Solved at every constant, checked at every input.
        for k in 0..256u64 {
            let src = format!("{} == {k}", at("x"));
            let e = parse(&mut cx, &src, w8);
            let r = eng.simplify(&mut cx, e).unwrap().expr;
            for x in 0..256u64 {
                let v = cx.eval(&[e, r], &env(w8, &[("x", x)])[..]).unwrap();
                assert_eq!(v[0], v[1], "{src} at x = {x}: {}", cx.display(r));
            }
        }
    }
}

/// A guard of the shape a virtual machine's branches take: an unsigned bound on one lane and
/// an equality between ors of xors of mixes of another lane under four keys and a function of
/// the first. The mixes of one value under several keys do not cancel; with `X` free the guard
/// is satisfiable, and the prover finds a value for it within its default budget. With the
/// lane's top byte fixed below the bound it is never true, which the facts show at once.
#[test]
fn cross_key_guards_are_answered() {
    let c = [KEYS[5], KEYS[6], KEYS[7], KEYS[8]];
    let (k1, k2, k3) = (
        0x1111_2222_3333_4444u64,
        0x5555_6666_7777_8888u64,
        0x9999_aaaa_bbbb_ccccu64,
    );
    let (k, kk, bound) = (
        0xd6ca_7354_7960_a840u64,
        0x079c_2a2c_658e_1c19u64,
        0xa768_6e85_68a2_2fc5u64,
    );
    let or = |x: u64| {
        let (a, b, d, e) = (hash(x, c[0]), hash(x, c[1]), hash(x, c[2]), hash(x, c[3]));
        (a ^ b ^ k1) | (b ^ d ^ k2) | (b ^ e ^ k3)
    };
    let guard = |lane: &str| {
        let (a, b, d, e) = (h("p", c[0]), h("p", c[1]), h("p", c[2]), h("p", c[3]));
        format!(
            "~({lane} <u 0x{bound:x}) & ((((({a} ^ {b} ^ 0x{k1:x}) | ({b} ^ {d} ^ 0x{k2:x}) \
             | ({b} ^ {e} ^ 0x{k3:x})) - ({lane} ^ 0x{k:x})) + 0x{kk:x}) == 0)"
        )
    };
    let cfg = Config::default();
    // A free lane: satisfiable.
    let mut cx = Context::new();
    let g = parse(&mut cx, &guard("X"), Width::W64);
    let ng = cx.not(g).unwrap();
    let mut q = Question::valid(&mut cx, ng, &cfg).unwrap();
    let out = q.solve(&mut cx, cfg.limits()).unwrap();
    let Outcome::Refuted(model) = out else {
        panic!("not refuted: {out:?}")
    };
    assert!(q.stats().conflicts < cfg.max_conflicts);
    let val = |name: &str| {
        let key = SymbolKey::from(name);
        model
            .iter()
            .find(|(k, _)| *k == key)
            .unwrap()
            .1
            .to_u64()
            .unwrap()
    };
    let (p, x) = (val("p"), val("X"));
    assert!(x >= bound && (or(p).wrapping_sub(x ^ k)).wrapping_add(kk) == 0);
    // A lane whose top byte is 0x12: below the bound, so never true.
    let mut cx = Context::new();
    let lane = "((s & 0x00ffffffffffffff) | 0x1200000000000000)";
    let g = parse(&mut cx, &guard(lane), Width::W64);
    let ng = cx.not(g).unwrap();
    let mut q = Question::valid(&mut cx, ng, &cfg).unwrap();
    let out = q.solve(&mut cx, cfg.limits()).unwrap();
    assert!(matches!(out, Outcome::Proved(_)), "{out:?}");
    assert_eq!(q.stats().conflicts, 0);
    // Without simplification the same answers, from the circuit.
    let off = Config::default().with_simplify(false);
    let mut cx = Context::new();
    let g = parse(&mut cx, &guard(lane), Width::W64);
    let ng = cx.not(g).unwrap();
    assert!(matches!(
        prove::valid(&mut cx, ng, &off).unwrap(),
        Outcome::Proved(_)
    ));
}
