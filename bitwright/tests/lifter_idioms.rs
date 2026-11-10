//! Idioms of compiled and lifted code, under every preset: bit counts, sign and overflow
//! flags, branch-free selects, facts declared about symbols, wide arithmetic done in halves,
//! and double-word shifts. Each is decided by every preset that runs what it needs.

use bitwright::engine::{Engine, Strategy};
use bitwright::{BinOp, BitVec, Context, KnownBits, ParseOptions, Width};

/// The presets, and whether each runs the passes past the standard ones (divisions, carries
/// and bit counts, shuffles).
fn presets() -> Vec<(&'static str, Engine, bool)> {
    let build = |s: Strategy| Engine::builder().builtin().strategy(s).build().unwrap();
    vec![
        ("standard", build(Strategy::standard()), false),
        ("compile", build(Strategy::compile()), false),
        ("decompile", build(Strategy::decompile()), true),
        ("deobfuscate", build(Strategy::deobfuscate()), true),
    ]
}

/// `input` at `w` bits simplifies to `want` under every preset (or only the ones that run the
/// passes past the standard ones, with `extended`), with each symbol of `small` declared
/// below `2^bits`.
fn check(w: u16, input: &str, want: &str, small: &[(&str, u16)], extended: bool) {
    for (name, engine, has_extended) in presets() {
        if extended && !has_extended {
            continue;
        }
        let mut cx = Context::new();
        let width = Width::new(w).unwrap();
        let o = ParseOptions::width(width);
        for &(sym, bits) in small {
            let x = cx.parse(sym, &o).unwrap();
            let shift = BitVec::from_u64(width, u64::from(bits)).unwrap();
            let high = BitVec::apply_bin(BinOp::Shl, &BitVec::ones(width), &shift).unwrap();
            let known = KnownBits::new(high, BitVec::zero(width)).unwrap();
            cx.declare_known(x, known).unwrap();
        }
        let e = cx.parse(input, &o).unwrap();
        let got = engine.simplify(&mut cx, e).unwrap().expr;
        let want = cx.parse(want, &o).unwrap();
        assert_eq!(got, want, "{name}: {input} gave {}", cx.display(got));
    }
}

#[test]
fn bit_counts() {
    check(64, "popcnt(x) + popcnt(~x)", "64", &[], false);
    check(64, "popcnt((x & -x) - 1)", "ctz(x)", &[], false);
    check(64, "popcnt(~x & (x - 1))", "ctz(x)", &[], false);
    check(64, "popcnt(x) == 0", "x == 0", &[], false);
    check(64, "ctz(x) == 64", "x == 0", &[], false);
    // The SWAR population count, recognized and proved by the carries pass.
    #[cfg(feature = "prove")]
    for w in [16u16, 32, 64] {
        let ones = u64::MAX >> (64 - w);
        let src = format!(
            "let a = x - ((x >>u 1) & {:#x}); let b = (a & {:#x}) + ((a >>u 2) & {:#x}); \
             let c = (b + (b >>u 4)) & {:#x}; (c * {:#x}) >>u {}",
            ones / 3,
            ones / 5,
            ones / 5,
            ones / 17,
            ones / 255,
            w - 8
        );
        check(w, &src, "popcnt(x)", &[], true);
    }
}

#[test]
fn sign_and_overflow_flags() {
    // SF ^ OF of a subtraction, one flag a slice and the other a test.
    check(
        32,
        "extract<31, 1>(x - y) ^ ssub_overflow(x, y)",
        "x <s y",
        &[],
        false,
    );
    check(64, "((x >>s 63) ^ x) - (x >>s 63)", "abs(x)", &[], false);
    check(64, "(x + (x >>s 63)) ^ (x >>s 63)", "abs(x)", &[], false);
    check(64, "x + y <u x", "~x <u y", &[], false);
}

#[test]
fn branch_free_selects() {
    check(1, "(c & a) | (~c & b)", "select(c, a, b)", &[], false);
    check(64, "select(c:1, x + 1, x)", "x + zext<64>(c:1)", &[], false);
    check(
        64,
        "select(c:1, x, x - 1)",
        "x - zext<64>(~c:1)",
        &[],
        false,
    );
    check(
        64,
        "select(c:1, x & y, x & z)",
        "x & select(c:1, y, z)",
        &[],
        false,
    );
    check(
        64,
        "select(c:1, x - y, x - z)",
        "x - select(c:1, y, z)",
        &[],
        false,
    );
}

#[test]
fn declared_facts() {
    let small = [("x", 8u16), ("y", 8)];
    check(64, "sext<64>(trunc<32>(x)) == x", "true", &small, false);
    check(64, "x + y <u x", "false", &small, false);
    check(64, "trunc<8>(x) == 3", "x == 3", &small, false);
}

#[test]
fn arithmetic_in_halves() {
    // `add`/`adc` and `sub`/`sbb` over separate 32-bit halves.
    check(
        64,
        "let lo = a0:32 + b0:32; concat(a1:32 + b1:32 + zext<32>(lo <u a0:32), lo)",
        "concat(a1:32, a0:32) + concat(b1:32, b0:32)",
        &[],
        false,
    );
    check(
        64,
        "concat(a1:32 - b1:32 - zext<32>(a0:32 <u b0:32), a0:32 - b0:32)",
        "concat(a1:32, a0:32) - concat(b1:32, b0:32)",
        &[],
        false,
    );
    // The same over the halves of two 64-bit values.
    check(
        64,
        "let lo = trunc<32>(x) + trunc<32>(y); \
         concat(extract<32, 32>(x) + extract<32, 32>(y) + zext<32>(lo <u trunc<32>(x)), lo)",
        "x + y",
        &[],
        false,
    );
    check(
        64,
        "concat(extract<32, 32>(x) - extract<32, 32>(y) - zext<32>(trunc<32>(x) <u trunc<32>(y)), \
         trunc<32>(x) - trunc<32>(y))",
        "x - y",
        &[],
        false,
    );
}

#[test]
fn double_word_shifts() {
    // `shld`: a window of the two words, by the shuffle pass and a `concat` rule.
    check(
        32,
        "(h << 5) | (l >>u 27)",
        "extract<27, 32>(concat(h, l))",
        &[],
        true,
    );
}
