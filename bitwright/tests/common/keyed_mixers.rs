//! Reproducible keyed-mixer and four-key fingerprint workloads, with fixed keys, salts and
//! targets. The scalar oracle uses wrapping u64 arithmetic and logical shifts independently
//! of bitwright.
#![allow(dead_code)]

use bitwright::{BinOp, Context, Expr, Width};

pub const GOLDEN: u64 = 0x9e37_79b9_7f4a_7c15;
pub const KEYS: [u64; 4] = [
    0xc26a_114a_f502_712b,
    0xcbb4_ec85_4c6b_3e87,
    0xce8b_b36c_f4ae_36f5,
    0xd9d7_620d_5093_d5a1,
];
pub const SALTS: [u64; 3] = [
    0x5327_ba71_a382_cdf5,
    0x75b7_c277_ba12_0c08,
    0xda4d_31e6_8bb6_9cd1,
];
pub const TARGET: u64 = 0xa7d4_121c_a956_7680;
pub const CANDIDATE: u64 = 0x4563;
pub const PREIMAGE: u64 = 0x4259_34c1_44f1_9fa3;
pub const ANCHOR: u64 = 0x1_4000_5352;
pub const DISPLACEMENT: u64 = 0x3613e1;

#[derive(Clone, Copy, Debug)]
pub enum Spelling {
    Nested,
    Compact,
}

#[inline(always)]
pub fn scalar(key: u64, x: u64) -> u64 {
    let h = key.wrapping_mul(x ^ key);
    key.wrapping_mul(h ^ ((h >> 32) >> (h >> 60)))
}

pub fn scalar_terms(x: u64) -> [u64; 3] {
    let a = scalar(KEYS[0], x);
    std::array::from_fn(|i| a ^ scalar(KEYS[i + 1], x) ^ SALTS[i])
}

pub fn scalar_fingerprint(x: u64) -> u64 {
    scalar_terms(x).into_iter().fold(0, |a, b| a | b)
}

pub fn constant(cx: &mut Context, value: u64) -> Expr {
    cx.constant_u64(Width::W64, value).unwrap()
}

pub fn mixer(cx: &mut Context, x: Expr, key: u64, spelling: Spelling) -> Expr {
    let key = constant(cx, key);
    let masked = cx.xor(x, key).unwrap();
    let h = cx.mul(key, masked).unwrap();
    let sixty = constant(cx, 60);
    let top = cx.bin(BinOp::LShr, h, sixty).unwrap();
    let thirty_two = constant(cx, 32);
    let shifted = match spelling {
        Spelling::Nested => {
            let sixty_three = constant(cx, 63);
            let count = cx.and(top, sixty_three).unwrap();
            let hi = cx.bin(BinOp::LShr, h, thirty_two).unwrap();
            cx.bin(BinOp::LShr, hi, count).unwrap()
        }
        Spelling::Compact => {
            let count = cx.add(thirty_two, top).unwrap();
            cx.bin(BinOp::LShr, h, count).unwrap()
        }
    };
    let scrambled = cx.xor(h, shifted).unwrap();
    cx.mul(key, scrambled).unwrap()
}

pub fn terms(cx: &mut Context, x: Expr, spelling: Spelling) -> [Expr; 3] {
    let a = mixer(cx, x, KEYS[0], spelling);
    std::array::from_fn(|i| {
        let b = mixer(cx, x, KEYS[i + 1], spelling);
        let pair = cx.xor(a, b).unwrap();
        let salt = constant(cx, SALTS[i]);
        cx.xor(pair, salt).unwrap()
    })
}

pub fn fingerprint(cx: &mut Context, x: Expr, spelling: Spelling) -> Expr {
    let [a, b, c] = terms(cx, x, spelling);
    let ab = cx.or(a, b).unwrap();
    cx.or(ab, c).unwrap()
}

pub fn dispatch(cx: &mut Context, p: Expr) -> (Expr, Expr) {
    let bit = cx.zext(p, Width::W64).unwrap();
    let delta = constant(cx, DISPLACEMENT);
    let delta = cx.mul(bit, delta).unwrap();
    let anchor = constant(cx, ANCHOR);
    let target = cx.add(anchor, delta).unwrap();
    let a = constant(cx, KEYS[0]);
    let b = constant(cx, KEYS[1]);
    let next_key = cx.select(p, a, b).unwrap();
    (target, next_key)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expected {
    Proved,
    Refuted,
    Open,
}

pub const CASES: &[&str] = &[
    "same-key-cancel",
    "same-key-inverse",
    "fingerprint-32",
    "fingerprint-64",
    "masked-pair-32",
    "masked-pair-32-unique",
    "cross-key-guards",
    "cross-key-guards-bytes",
    "correlated-pair",
    "target-cut",
];

pub fn claim(cx: &mut Context, name: &str, spelling: Spelling) -> (Expr, Expected) {
    if name == "cross-key-guards-bytes" {
        let bytes: Vec<_> = (0..8)
            .map(|i| cx.symbol(format!("byte{i}"), Width::W8).unwrap())
            .collect();
        let mut word = bytes[0];
        for &high in &bytes[1..] {
            word = cx.concat(high, word).unwrap();
        }
        return (cross_key_exclusion(cx, word, spelling), Expected::Refuted);
    }
    let width = if name == "fingerprint-32" || name.starts_with("masked-pair-32") {
        Width::W32
    } else {
        Width::W64
    };
    let original = cx.symbol("x", width).unwrap();
    let x = cx.zext(original, Width::W64).unwrap();
    match name {
        "same-key-cancel" => {
            let y = cx.symbol("y", Width::W64).unwrap();
            let a = mixer(cx, x, GOLDEN, spelling);
            let b = mixer(cx, y, GOLDEN, spelling);
            let mixed = cx.eq(a, b).unwrap();
            let plain = cx.eq(x, y).unwrap();
            (cx.eq(mixed, plain).unwrap(), Expected::Proved)
        }
        "same-key-inverse" => {
            let a = mixer(cx, x, GOLDEN, spelling);
            let value = constant(cx, 0x1234);
            (cx.eq(a, value).unwrap(), Expected::Refuted)
        }
        "masked-pair-32" | "masked-pair-32-unique" => {
            let a = mixer(cx, x, KEYS[0], spelling);
            let b = mixer(cx, x, KEYS[1], spelling);
            let pair = cx.xor(a, b).unwrap();
            let salt = constant(cx, SALTS[0]);
            let pair = cx.xor(pair, salt).unwrap();
            let mask = constant(cx, !TARGET);
            let masked = cx.and(pair, mask).unwrap();
            let zero = constant(cx, 0);
            let fails_mask = cx.ne(masked, zero).unwrap();
            if name == "masked-pair-32" {
                (fails_mask, Expected::Refuted)
            } else {
                let candidate = cx.constant_u64(Width::W32, CANDIDATE).unwrap();
                let at_candidate = cx.eq(original, candidate).unwrap();
                (cx.or(fails_mask, at_candidate).unwrap(), Expected::Proved)
            }
        }
        "fingerprint-32" | "fingerprint-64" => {
            let value = fingerprint(cx, x, spelling);
            let target = constant(cx, TARGET);
            let expected = if name == "fingerprint-32" {
                Expected::Proved
            } else {
                Expected::Open
            };
            (cx.ne(value, target).unwrap(), expected)
        }
        "cross-key-guards" => (cross_key_exclusion(cx, x, spelling), Expected::Refuted),
        "correlated-pair" | "target-cut" => {
            let value = fingerprint(cx, x, spelling);
            let target = constant(cx, TARGET);
            let p = cx.eq(value, target).unwrap();
            let (target, key) = dispatch(cx, p);
            let anchor = constant(cx, ANCHOR);
            let other = constant(cx, ANCHOR + DISPLACEMENT);
            let a = cx.eq(target, anchor).unwrap();
            let b = cx.eq(target, other).unwrap();
            let result = if name == "target-cut" {
                cx.or(a, b).unwrap()
            } else {
                let ka = constant(cx, KEYS[0]);
                let with_key = cx.eq(key, ka).unwrap();
                let impossible = cx.and(a, with_key).unwrap();
                cx.not(impossible).unwrap()
            };
            (result, Expected::Proved)
        }
        _ => panic!("unknown keyed-mixer fixture {name}"),
    }
}

fn cross_key_exclusion(cx: &mut Context, x: Expr, spelling: Spelling) -> Expr {
    let [a, b, c] = terms(cx, x, spelling);
    let zero = constant(cx, 0);
    let a = cx.eq(a, zero).unwrap();
    let b = cx.eq(b, zero).unwrap();
    let c = cx.eq(c, zero).unwrap();
    let ab = cx.and(a, b).unwrap();
    let all = cx.and(ab, c).unwrap();
    cx.not(all).unwrap()
}
