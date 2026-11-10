//! The words pass: soundness (exhaustive over narrow symbols), what it reads, that it reaches a
//! fixed point, and that it does not depend on how an expression was built.

use crate::engine::tests::{equivalent, generator};
use crate::engine::{End, Engine, Phase, Run, Strategy};
use crate::hash::IdMap;
use crate::testutil::Rng;
use crate::{BitVec, Context, Expr, ParseOptions, SymbolKey, Width};

fn engine(phases: Vec<Phase>) -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::new("t", phases))
        .build()
        .unwrap()
}

fn simplify(eng: &Engine, src: &str, w: u16) -> String {
    let mut cx = Context::new();
    let e = cx
        .parse(src, &ParseOptions::width(Width::new(w).unwrap()))
        .unwrap();
    let out = eng.simplify(&mut cx, e).unwrap();
    cx.display(out.expr).to_string()
}

/// `x <u y` as a virtual machine's handlers spell it.
fn below(x: &str, y: &str) -> String {
    format!("~((-{x} + {y} == 0) | ({y} <u {x}))")
}

#[test]
fn words_fixtures() {
    let eng = engine(vec![Phase::Words]);
    let mut wrong = Vec::new();
    for (src, w, want) in [
        // The high digit of a sum: the digits of the operands and the carry out of the low
        // digits, written as a comparison.
        (
            "trunc<20>((a:32 >>u 12) + (b:32 >>u 12) + zext<32>((a + b & 4095) <u (a & 4095)))"
                .to_string(),
            20,
            "extract<12, 20>(a + b)",
        ),
        // At the registers' width the sum's own carry is there too: the sum is one bit wider.
        (
            "(a >>u 12) + (b >>u 12) + zext<32>((a + b & 4095) <u (a & 4095))".to_string(),
            32,
            "zext<32>(extract<12, 21>(zext<33>(b) + zext<33>(a)))",
        ),
        // Of a difference, with the borrow.
        (
            "trunc<20>((a:32 >>u 12) - (b:32 >>u 12) - zext<32>((a & 4095) <u (b & 4095)))"
                .to_string(),
            20,
            "extract<12, 20>(a - b)",
        ),
        // The comparison spelled with an equality, sign-extended and subtracted.
        (
            format!(
                "trunc<20>((a:32 >>u 12) + (b:32 >>u 12) - sext<32>({}))",
                below("(a + b & 4095)", "(a & 4095)")
            ),
            20,
            "extract<12, 20>(a + b)",
        ),
        // Three limbs of 8 bits: the carry into the third is the carry out of the second,
        // which has a carry in (`b1` all ones and a carry in, or the sum below `a1`).
        (
            "let %0 = zext<32>((a:32 + b:32 & 255) <u (a & 255)); \
             let %1 = (a >>u 8 & 255) + (b >>u 8 & 255) + %0; \
             let %2 = zext<32>(((b >>u 8) + 1 & 255) == 0) & %0 \
             | zext<32>((%1 & 255) <u (a >>u 8 & 255)); \
             trunc<16>((a >>u 16) + (b >>u 16) + %2)"
                .to_string(),
            16,
            "extract<16, 16>(a + b)",
        ),
        // The same with the comparisons spelled as a virtual machine does, and the digit
        // compared with all ones.
        (
            format!(
                "let %0 = zext<32>({}); \
                 let %1 = (a >>u 8 & 255) + (b >>u 8 & 255) + %0; \
                 let %2 = zext<32>((b >>u 8 & 255) == 255) & %0 | zext<32>({}); \
                 trunc<16>((a >>u 16) + (b >>u 16) + %2)",
                below("(a:32 + b:32 & 255)", "(a & 255)"),
                below("(%1 & 255)", "(a >>u 8 & 255)")
            ),
            16,
            "extract<16, 16>(a + b)",
        ),
        // Of a difference: the borrow into the third limb is the borrow out of the second,
        // which has a borrow in (`b1` all ones and a borrow in, or `a1` below the digit left).
        (
            format!(
                "let %0 = zext<32>({}); \
                 let %1 = (a >>u 8 & 255) - (b >>u 8 & 255) - %0; \
                 let %2 = zext<32>((~(b >>u 8) & 255) == 0) & %0 | zext<32>({}); \
                 trunc<16>((a >>u 16) - (b >>u 16) - %2)",
                below("(a:32 & 255)", "(b:32 & 255)"),
                below("(a >>u 8 & 255)", "(%1 & 255)")
            ),
            16,
            "extract<16, 16>(a - b)",
        ),
        // An operand that is the high half of a register: the word is the sum with that
        // half, not a wider one with the register.
        (
            "trunc<16>((x:32 >>u 16) + (extract<32, 32>(s:64) >>u 16) \
             + zext<32>((x + extract<32, 32>(s) & 0xffff) <u (x & 0xffff)))"
                .to_string(),
            16,
            "extract<16, 16>(extract<32, 32>(s) + x)",
        ),
        // And an XOR of it in limbs, written `x + y − 2·(x & y)`.
        (
            "let %0 = extract<32, 32>(s:64); let %1 = x:32 & %0; \
             trunc<16>((x >>u 16) + (%0 >>u 16) - (%1 >>u 15) \
             - zext<32>((x + %0 & 0xffff) <u (x + %0 - %1 * 2 & 0xffff)) \
             + zext<32>((x + %0 & 0xffff) <u (x & 0xffff)))"
                .to_string(),
            16,
            "extract<16, 16>(extract<32, 32>(s) ^ x)",
        ),
        // A product by a constant done on the limbs: each limb by its own shift of the
        // constant.
        (
            "(x & 0xffff) * 0x1234567 + (x >>u 16) * 0x45670000".to_string(),
            32,
            "x * 0x1234567",
        ),
        // A constant added limb by limb: the word with the low limb's part is a node, the
        // high limb adds its own part to a slice of it.
        (
            "extract<16, 16>(x:32 * 5 + 0x1234) + 0xab".to_string(),
            16,
            "extract<16, 16>(x * 5 + 0xab1234)",
        ),
        // A value chosen limb by limb is the limbs of the value chosen.
        (
            "concat(select(c:1, extract<8, 8>(x:32), extract<8, 8>(y:32)), \
             select(c, trunc<8>(x), trunc<8>(y)))"
                .to_string(),
            16,
            "select(c, trunc<16>(x), trunc<16>(y))",
        ),
        // Chosen between the low half of one register and the high half of another: the
        // limbs are taken from different places of the two.
        (
            "concat(select(c:1, extract<8, 8>(x:64), extract<40, 8>(y:64)), \
             select(c, trunc<8>(x), extract<32, 8>(y)))"
                .to_string(),
            16,
            "select(c, trunc<16>(x), extract<32, 16>(y))",
        ),
        // A sum with such a value, its high limb chosen on its own: a limb of the sum with
        // the value chosen.
        (
            "let %0 = select(c:1, trunc<32>(p:64), extract<32, 32>(q:64)); \
             trunc<16>((x:32 >>u 16) + zext<32>(select(c, extract<16, 16>(p), \
             extract<48, 16>(q))) + zext<32>((x + %0 & 0xffff) <u (x & 0xffff)))"
                .to_string(),
            16,
            "extract<16, 16>(select(c, trunc<32>(p), extract<32, 32>(q)) + x)",
        ),
        // And an XOR with it in limbs.
        (
            "let %0 = select(c:1, trunc<32>(p:64), extract<32, 32>(q:64)); let %1 = x:32 & %0; \
             trunc<16>((x >>u 16) + (%0 >>u 16) - (%1 >>u 15) \
             - zext<32>((x + %0 & 0xffff) <u (x + %0 - %1 * 2 & 0xffff)) \
             + zext<32>((x + %0 & 0xffff) <u (x & 0xffff)))"
                .to_string(),
            16,
            "extract<16, 16>(select(c, trunc<32>(p), extract<32, 32>(q)) ^ x)",
        ),
        // A borrow chosen: the two arms are 1 apart modulo the width, each wrapped on its
        // own.
        (
            "trunc<20>(select((a:32 & 4095) <u (b:32 & 4095), (a >>u 12) + ~(b >>u 12), \
             (a >>u 12) - (b >>u 12)))"
                .to_string(),
            20,
            "extract<12, 20>(a - b)",
        ),
        // An OR and an XOR of the same operands, as sums: one AND is left.
        ("(a ^ b) + (a & b) * 3".to_string(), 32, "a + b + (a & b)"),
        // The carry out of a sum of one bit and a constant is the bit.
        ("extract<8, 1>(zext<9>(c:1) + 255)".to_string(), 1, "c"),
        // A digit of a value (what one slice of it has more than the next, shifted up) is
        // below its base: with 0xff00 it does not reach bit 16.
        (
            "trunc<8>(((x:32 >>u 8) - ((x >>u 16) << 8) + 0xff00) >>u 16)".to_string(),
            8,
            "0:8",
        ),
        // Read only in its low 33 bits, a value is written as any value that has them: `x`
        // itself, not its two slices put together.
        (
            "~concat(zext<48>(extract<16, 17>(x)), trunc<16>(x)) & 0x100050040".to_string(),
            64,
            "-1 - x & 0x100050040",
        ),
        // An XOR with twice the AND of the two is their sum; with the AND, their OR.
        ("(a:32 ^ b:32) + (a & b) * 2".to_string(), 32, "a + b"),
        ("(a:32 ^ b:32) + (a & b)".to_string(), 32, "a | b"),
        // XORs of three values, grouped two ways, are one value;
        (
            "((a:32 ^ b:32) ^ c:32) - (b ^ (c ^ a))".to_string(),
            32,
            "0:32",
        ),
        // in limbs they are the limbs of the one XOR,
        (
            "trunc<20>(((a:32 >>u 12) ^ (b:32 >>u 12)) ^ (c:32 >>u 12))".to_string(),
            20,
            "extract<12, 20>(a ^ c ^ b)",
        ),
        (
            "((a:32 & 4095) ^ (b:32 & 4095) ^ (c:32 & 4095)) \
             | (((a >>u 12) ^ (b >>u 12) ^ (c >>u 12)) << 12)"
                .to_string(),
            32,
            "a ^ c ^ b",
        ),
        // and an AND of two of them with the third has its relation with it.
        (
            "(a:32 ^ b:32 ^ c:32) + 2 * ((a ^ b) & c) - (a ^ b) - c".to_string(),
            32,
            "0:32",
        ),
        // A product of an XOR by a constant, the XOR and the product both done limb by limb.
        (
            "((a:32 & 0xffff) ^ (b:32 & 0xffff)) * 0x1234567 \
             + ((a >>u 16) ^ (b >>u 16)) * 0x45670000"
                .to_string(),
            32,
            "(a ^ b) * 0x1234567",
        ),
        (
            "((a:32 & 0xffff) ^ (b:32 & 0xffff) ^ (c:32 & 0xffff)) * 0x1234567 \
             + ((c >>u 16) ^ (a >>u 16) ^ (b >>u 16)) * 0x45670000"
                .to_string(),
            32,
            "(a ^ c ^ b) * 0x1234567",
        ),
        // Two of one value cancel, under truncations.
        (
            "trunc<16>(x:32 ^ y:32) ^ trunc<16>(y) ^ trunc<16>(z:32)".to_string(),
            16,
            "trunc<16>(z) ^ trunc<16>(x)",
        ),
        // A value chosen limb by limb between a constant and a register is the limbs of the
        // one choice: each limb is chosen against its own digits of the constant.
        (
            "zext<32>(select(c:1, 113, trunc<12>(r:32))) \
             | (zext<32>(select(c, 0x352ac, extract<12, 20>(r))) << 12)"
                .to_string(),
            32,
            "select(c, 0x352ac071, r)",
        ),
        (
            "select(c:1, 0x352ac071, r:32) - (zext<32>(select(c, 113, trunc<12>(r))) \
             | (zext<32>(select(c, 0x352ac, extract<12, 20>(r))) << 12))"
                .to_string(),
            32,
            "0:32",
        ),
        (
            "extract<12, 20>(select(c:1, r:32, 0x352ac071)) - select(c, extract<12, 20>(r), 0x352ac)"
                .to_string(),
            20,
            "0:20",
        ),
        // ANDs and ORs of three, grouped two ways.
        (
            "(a:32 & b:32 & c:32) ^ (c & (b & a))".to_string(),
            32,
            "0:32",
        ),
        (
            "(a:32 | b:32 | c:32) - (c | (a | b))".to_string(),
            32,
            "0:32",
        ),
        // No digits and nothing that cancels: as it was.
        (
            "a * b + (a >>u 3 ^ b)".to_string(),
            32,
            "a * b + (a >>u 3 ^ b)",
        ),
    ] {
        let got = simplify(&eng, &src, w);
        if got != want {
            wrong.push(format!("{src}\n   got: {got}\n  want: {want}"));
        }
    }
    assert!(wrong.is_empty(), "\n{}", wrong.join("\n"));
}

/// The high limb of `a ^ b` in limbs of 25 and 7 bits, the XOR written `a + b − 2·(a & b)`:
/// the digits, the carry of the sum and the borrow of the difference.
fn xor_high() -> String {
    let m = "0x1ffffff";
    format!(
        "let %0 = a:32 & b:32; let %1 = a + b; let %2 = -(%0 << 1) + %1; \
         trunc<7>((a >>u 25) + (b >>u 25) - (%0 >>u 24) + sext<32>({}) + zext<32>({}))",
        below(&format!("(%1 & {m})"), &format!("(%2 & {m})")),
        below(&format!("(%1 & {m})"), &format!("(a & {m})")),
    )
}

#[test]
fn words_reads_an_xor_in_limbs_as_a_slice_of_the_word() {
    // Alone, the word is as the limbs spell it; with the linear-MBA pass after it, an XOR.
    let eng = engine(vec![Phase::Words]);
    assert_eq!(simplify(&eng, &xor_high(), 32), "extract<25, 7>(a ^ b)");
    let eng = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    assert_eq!(simplify(&eng, &xor_high(), 32), "extract<25, 7>(a ^ b)");
}

/// A random expression built the way limb code is, right or wrong: digits of values of
/// 4-bit symbols held in 8-bit registers, in several spellings; carries and borrows as
/// comparisons of digits, with and without a carry in; products of digits by constants;
/// and-terms; choices; slices at other bits, of a value that may be extended from one of
/// its middle bits (so that a floor of it holds floors of itself); summed, and read whole,
/// masked, truncated, shifted or joined.
fn limb_text(g: &mut Rng) -> (String, u16) {
    let w = 8u64;
    let sym = |g: &mut Rng| format!("zext<8>({}:4)", ["a", "b", "c"][g.below(3) as usize]);
    let value = |g: &mut Rng| {
        let (x, y) = (sym(g), sym(g));
        let c = g.below(1 << w);
        match g.below(9) {
            0 | 1 => x,
            2 => format!("({x} + {y})"),
            3 => format!("({x} - {y})"),
            4 => format!("({x} + {c})"),
            5 => format!("({x} + {y} - ({x} & {y}) * 2)"),
            6 => format!("({x} * {c})"),
            7 => format!("({x} << {})", g.below(5)),
            _ => format!("({x} | {y} << 4)"),
        }
    };
    let k = 1 + g.below(w - 1);
    let mask = (1u64 << k) - 1;
    let lo = |g: &mut Rng, v: &str| match g.below(3) {
        0 => format!("({v} & {mask})"),
        1 => format!("zext<8>(trunc<{k}>({v}))"),
        _ => format!("({v} - (({v} >>u {k}) << {k}))"),
    };
    let hi = |g: &mut Rng, v: &str| match g.below(3) {
        0 => format!("({v} >>u {k})"),
        1 => format!("zext<8>(extract<{k}, {}>({v}))", w - k),
        _ => format!("(({v} & {}) >>u {k})", 255 & !mask),
    };
    let (p, q) = (value(g), value(g));
    let s = match g.below(4) {
        0 => format!("({p} + {q})"),
        1 => format!("({p} - {q})"),
        2 => value(g),
        _ => format!("({p} + {q} + 1)"),
    };
    let s = if g.chance(1, 4) {
        let j = 1 + g.below(6);
        let (high, low) = (256 - (1u64 << j), (1u64 << j) - 1);
        format!("(zext<8>(extract<{j}, 1>({s})) * {high} | {s} & {low})")
    } else {
        s
    };
    let compare = |g: &mut Rng, x: &str, y: &str| match g.below(6) {
        0 => format!("({x} <u {y})"),
        1 => below(x, y),
        2 => format!("({x} <=u {y})"),
        3 => format!("({x} == {y})"),
        4 => format!("({x} <s {y})"),
        _ => format!("~({y} <=u {x})"),
    };
    let bit = |g: &mut Rng| {
        let (x, y) = match g.below(4) {
            0 => (lo(g, &s), lo(g, &p)),
            1 => (lo(g, &p), lo(g, &q)),
            2 => (lo(g, &s), lo(g, &q)),
            _ => {
                let v = value(g);
                (lo(g, &v), format!("{}", g.below(1 << k)))
            }
        };
        let c = compare(g, &x, &y);
        // A carry in: the other operand's digit all ones and the carry below.
        if g.chance(1, 4) {
            let (x2, y2) = (lo(g, &p), lo(g, &q));
            let below = compare(g, &x2, &y2);
            let ones = match g.below(2) {
                0 => format!("(({q} + 1 & {mask}) == 0)"),
                _ => format!("((~{q} & {mask}) == 0)"),
            };
            format!("({ones} & {below} | {c})")
        } else {
            c
        }
    };
    let mut src = String::new();
    for i in 0..2 + g.below(5) {
        let t = match g.below(14) {
            0 | 1 => {
                let ext = if g.chance(1, 4) { "sext" } else { "zext" };
                format!("{ext}<8>({})", bit(g))
            }
            2 => hi(g, &p),
            3 => hi(g, &q),
            4 => hi(g, &s),
            5 => format!("({} * {})", lo(g, &p), g.below(1 << w)),
            6 => format!("({} * {})", hi(g, &p), g.below(1 << w)),
            7 => format!(
                "({} & ({} * 2 + ({} >>u {})))",
                hi(g, &p),
                hi(g, &q),
                lo(g, &q),
                k - 1
            ),
            8 => format!("select({}, {}, {})", bit(g), hi(g, &p), hi(g, &q)),
            // A choice between slices from different places, or of different lengths; and
            // between two values a constant apart, each wrapped on its own.
            11 => format!("select({}, {}, {})", bit(g), lo(g, &p), hi(g, &q)),
            12 => format!("select({}, {}, ({q} >>u {}))", bit(g), lo(g, &p), w - k),
            13 => {
                let (u, v) = (hi(g, &p), hi(g, &q));
                let c = g.below(3);
                format!("select({}, ({u} - {v}), ({u} + ~{v} + {c}))", bit(g))
            }
            9 => {
                let r = g.below(7);
                let len = 1 + g.below(8 - r);
                format!("(zext<8>(extract<{r}, {len}>({s})) * {})", g.below(256))
            }
            _ => format!("(({s} >>u {}) * {})", g.below(8), g.below(256)),
        };
        let sign = if i > 0 && g.chance(1, 3) { '-' } else { '+' };
        if i == 0 {
            src.push_str(&t);
        } else {
            src.push_str(&format!(" {sign} {t}"));
        }
    }
    match g.below(6) {
        0 => (format!("({src}) & {mask}"), 8),
        1 => {
            let j = 1 + g.below(7);
            (format!("trunc<{j}>({src})"), j as u16)
        }
        2 => (format!("(({src}) << {k}) | {}", lo(g, &s)), 8),
        3 => (
            format!("concat(trunc<{}>({src}), trunc<{k}>({s}))", w - k),
            8,
        ),
        4 => (format!("({src}) >>u {}", g.below(4)), 8),
        _ => (src, 8),
    }
}

/// A sum or a difference of two values of 4-bit symbols in three limbs, as limb code writes
/// it, right or wrong: the carry or borrow into the second limb a comparison of the first,
/// the one into the third that of the second with the one below coming in, the comparisons
/// and the test for a digit of all ones in several spellings (some of them another
/// comparison). Read as its top limb, or all three joined.
fn chain_text(g: &mut Rng) -> (String, u16) {
    let sym = |g: &mut Rng| format!("zext<8>({}:4)", ["a", "b", "c"][g.below(3) as usize]);
    let value = |g: &mut Rng| {
        let (x, y) = (sym(g), sym(g));
        match g.below(4) {
            0 => x,
            1 => format!("({x} | {y} << 4)"),
            2 => format!("({x} * {})", g.below(256)),
            _ => format!("({x} + ({y} << {}))", g.below(5)),
        }
    };
    let (p, q) = (value(g), value(g));
    let k1 = 1 + g.below(3);
    let n = 1 + g.below(3);
    let k2 = k1 + n;
    let (m1, m2) = ((1u64 << k1) - 1, (1u64 << n) - 1);
    let digits = |v: &str| {
        (
            format!("({v} & {m1})"),
            format!("({v} >>u {k1} & {m2})"),
            format!("({v} >>u {k2})"),
        )
    };
    let ((p0, p1, p2), (q0, q1, q2)) = (digits(&p), digits(&q));
    // `x <u y`, mostly.
    let less = |g: &mut Rng, x: &str, y: &str| match g.below(8) {
        0 | 1 => format!("({x} <u {y})"),
        2..=4 => below(x, y),
        5 | 6 => format!("~({y} <=u {x})"),
        _ => format!("({x} <=u {y})"),
    };
    // Whether a digit is all ones, mostly.
    let ones = |g: &mut Rng, d: &str, m: u64| match g.below(7) {
        0 | 1 => format!("(({d} + 1 & {m}) == 0)"),
        2 | 3 => format!("((~{d} & {m}) == 0)"),
        4 | 5 => format!("({d} == {m})"),
        _ => format!("({d} == 0)"),
    };
    let sub = g.chance(1, 2);
    let op = if sub { '-' } else { '+' };
    let low = format!("({p0} {op} {q0})");
    let c0 = if sub {
        less(g, &p0, &q0)
    } else {
        less(g, &format!("({low} & {m1})"), &p0)
    };
    let mid = format!("({p1} {op} {q1} {op} zext<8>({c0}))");
    let digit = format!("({mid} & {m2})");
    let out = if sub {
        less(g, &p1, &digit)
    } else {
        less(g, &digit, &p1)
    };
    let c1 = format!("({} & {c0} | {out})", ones(g, &q1, m2));
    let top = format!("({p2} {op} {q2} {op} zext<8>({c1}))");
    match g.below(3) {
        0 => {
            let j = 8 - k2 as u16;
            (format!("trunc<{j}>({top})"), j)
        }
        1 => (top, 8),
        _ => (
            format!(
                "concat(concat(trunc<{}>({top}), trunc<{n}>({mid})), trunc<{k1}>({low}))",
                8 - k2
            ),
            8,
        ),
    }
}

/// `ops` joined by `op` in a random order and association.
fn tree(g: &mut Rng, ops: &[String], op: &str) -> String {
    let mut xs = ops.to_vec();
    for i in (1..xs.len()).rev() {
        xs.swap(i, g.below(i as u64 + 1) as usize);
    }
    while xs.len() > 1 {
        let i = g.below(xs.len() as u64 - 1) as usize;
        let joined = format!("({} {op} {})", xs[i], xs[i + 1]);
        xs.splice(i..i + 2, [joined]);
    }
    xs.remove(0)
}

/// Bitwise operations of several values in random orders, mixed with sums, masks, shifts and
/// constants, over 3-bit symbols in 6-bit registers: XORs and ANDs of the same operands
/// written in different orders, an XOR spelled `x + y − 2·(x & y)` beside the one written
/// `^`, complements, and slices of them.
fn bitwise_text(g: &mut Rng) -> (String, u16) {
    let sym = |g: &mut Rng| format!("zext<6>({}:3)", ["a", "b", "c", "d"][g.below(4) as usize]);
    let value = |g: &mut Rng| {
        let x = sym(g);
        match g.below(8) {
            0..=2 => x,
            3 => format!("({x} << {})", g.below(4)),
            4 => format!("({x} + {})", sym(g)),
            5 => format!("({x} * {})", g.below(64)),
            6 => format!("~{x}"),
            _ => format!("{}:6", g.below(64)),
        }
    };
    let n = 2 + g.below(4) as usize;
    let ops: Vec<String> = (0..n).map(|_| value(g)).collect();
    let word = |g: &mut Rng, ops: &[String]| {
        let op = ["^", "^", "&", "|"][g.below(4) as usize];
        match g.below(4) {
            // Spelled as sums: `x + y − 2·(x & y)`, `x + y − (x & y)`.
            0 => {
                let mut x = ops[0].clone();
                for o in &ops[1..] {
                    let k = if g.chance(1, 4) { 1 } else { 2 };
                    x = format!("({x} + {o} - ({x} & {o}) * {k})");
                }
                x
            }
            _ => tree(g, ops, op),
        }
    };
    let (x, y) = (word(g, &ops), word(g, &ops));
    let k = 1 + g.below(5);
    match g.below(7) {
        0 => (format!("{x} - {y}"), 6),
        1 => (format!("({x} >>u {k}) - ({y} >>u {k})"), 6),
        2 => (format!("{x} + {y} * {}", g.below(64)), 6),
        3 => (format!("({x} & {}) ^ ({y} & {})", sym(g), sym(g)), 6),
        4 => (format!("trunc<{k}>({x}) ^ trunc<{k}>({y})"), k as u16),
        5 => (format!("({x} ^ {}) + ({y} | {})", g.below(64), sym(g)), 6),
        _ => (format!("{x} == {y}"), 1),
    }
}

/// Every node's form has the node's value, at every assignment of the symbols: the reading
/// and the algebra, apart from what is written back; with each of the three kinds of forms a
/// root is asked with.
#[test]
fn forms_have_the_values_of_their_nodes() {
    let mut g = generator(0x3074_0005);
    for i in 0..1600 {
        let mut cx = Context::new();
        let e = if i % 4 == 0 {
            let w = 1 + g.rng.below(6) as u16;
            g.expr(&mut cx, w, 5).0
        } else {
            let (src, w) = match i % 4 {
                1 => limb_text(&mut g.rng),
                2 => chain_text(&mut g.rng),
                _ => bitwise_text(&mut g.rng),
            };
            cx.parse(&src, &ParseOptions::width(Width::new(w).unwrap()))
                .unwrap()
        };
        let order: Vec<Expr> = cx.post_order(&[e]).unwrap();
        let ids: Vec<u32> = order.iter().map(|&x| cx.id(x).unwrap()).collect();
        let mut lift = match i % 3 {
            0 => super::lift::Lift::default(),
            1 => super::lift::Lift::values(),
            _ => super::lift::Lift::plain(),
        };
        for &n in &ids {
            lift.read(&cx, n);
        }
        let syms = cx.symbols_in(&[e]).unwrap();
        let keys: Vec<(SymbolKey, Width)> = syms
            .iter()
            .map(|&s| {
                (
                    cx.symbol_key(s).unwrap().clone(),
                    cx.symbol_width(s).unwrap(),
                )
            })
            .collect();
        let bits: u32 = keys.iter().map(|(_, w)| u32::from(w.bits())).sum();
        let cases: u64 = if bits <= 12 { 1 << bits } else { 512 };
        for case in 0..cases {
            let mut rest = if bits <= 12 { case } else { g.rng.next() };
            let vals: Vec<(SymbolKey, BitVec)> = keys
                .iter()
                .map(|(k, w)| {
                    let v = rest & ((1u64 << w.bits()) - 1);
                    rest = rest.rotate_right(u32::from(w.bits()));
                    (k.clone(), BitVec::wrapping_from_u64(*w, v))
                })
                .collect();
            let mut at: IdMap<u32, BitVec> = IdMap::default();
            for &n in &ids {
                let v = cx
                    .eval_node(
                        n,
                        |j| at[&j],
                        |k, _| vals.iter().find(|(kk, _)| kk == k).map(|(_, v)| *v),
                    )
                    .unwrap();
                at.insert(n, v);
            }
            let leaf = |n: u32| at[&n].to_u128().map_or(0, |v| v as i128);
            for &n in &ids {
                if cx.node(n).width > 64 {
                    continue;
                }
                let f = lift.value(&cx, n).unwrap();
                let (got, want) = (lift.alg.eval(&f, &leaf), leaf(n));
                assert_eq!(
                    got,
                    want,
                    "{} (in {}) at {vals:?}",
                    cx.display(cx.handle(n)),
                    cx.display(e)
                );
            }
        }
    }
}

#[test]
fn words_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Words]);
    let mut g = generator(0x3074_0001);
    let mut rng = Rng(5);
    let mut changed = 0;
    for i in 0..4000 {
        let mut cx = Context::new();
        // Limb code, right and wrong; bitwise code in several orders; and every operator the
        // pass reads, in any mixture.
        let e = if i % 5 == 0 {
            let w = 1 + g.rng.below(6) as u16;
            g.expr(&mut cx, w, 5).0
        } else {
            let (src, w) = match i % 5 {
                3 => chain_text(&mut g.rng),
                4 => bitwise_text(&mut g.rng),
                _ => limb_text(&mut g.rng),
            };
            cx.parse(&src, &ParseOptions::width(Width::new(w).unwrap()))
                .unwrap()
        };
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(r.end, End::Completed);
        assert_eq!(out.stats.rejected, 0, "{}", cx.display(e));
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        changed += u64::from(r.changed);
        // A fixed point (recomputed, not answered from the memo).
        cx.memo.clear();
        let out2 = eng.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert!(
            !out2.roots[0].changed,
            "not idempotent: {} -> {}",
            cx.display(r.expr),
            cx.display(out2.roots[0].expr)
        );
    }
    assert!(changed > 300, "{changed}");
}

/// The same with every other pass of the deobfuscating strategy around it.
#[test]
fn words_is_sound_among_the_other_passes() {
    let eng = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let mut g = Rng(0x3074_0002);
    let mut rng = Rng(6);
    for i in 0..800 {
        let mut cx = Context::new();
        let (src, w) = match i % 4 {
            2 => chain_text(&mut g),
            3 => bitwise_text(&mut g),
            _ => limb_text(&mut g),
        };
        let e = cx
            .parse(&src, &ParseOptions::width(Width::new(w).unwrap()))
            .unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(out.stats.rejected, 0, "{src}");
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{src} vs {}",
            cx.display(r.expr)
        );
    }
}

#[test]
fn words_is_independent_of_construction_order() {
    let eng = engine(vec![Phase::Words]);
    let mut g = Rng(0x3074_0003);
    for i in 0..600 {
        // The same expression in two contexts whose symbols were created in opposite orders
        // (so node indices differ), the second read back from the text of the first.
        let (src, w) = if i % 3 == 2 {
            chain_text(&mut g)
        } else {
            limb_text(&mut g)
        };
        let mut c1 = Context::new();
        let mut c2 = Context::new();
        for name in ["c", "b", "a"] {
            c2.symbol(name, Width::new(4).unwrap()).unwrap();
        }
        let o = ParseOptions::width(Width::new(w).unwrap());
        let e1 = c1.parse(&src, &o).unwrap();
        let text = c1.display(e1).to_string();
        let e2 = c2.parse(&text, &o).unwrap();
        let r1 = eng.simplify(&mut c1, e1).unwrap().expr;
        let r2 = eng.simplify(&mut c2, e2).unwrap().expr;
        assert_eq!(
            c1.display(r1).to_string(),
            c2.display(r2).to_string(),
            "{src}"
        );
    }
}

/// A root with more nodes under it than the pass reads is not asked, whatever the budget;
/// its operands are, and the call completes.
#[test]
fn a_root_over_the_bound_is_left_to_its_operands() {
    let eng = engine(vec![Phase::Words]);
    let mut cx = Context::new();
    // 3000 distinct terms in a chain, the limb code at the bottom.
    let mut src = String::from(
        "let %0 = (a:32 >>u 12) + (b:32 >>u 12) + zext<32>((a + b & 4095) <u (a & 4095)); ",
    );
    for i in 1..3000 {
        src.push_str(&format!("let %{i} = (%{} ^ {i}) * 3; ", i - 1));
    }
    src.push_str("%2999");
    let e = cx.parse(&src, &ParseOptions::width(Width::W32)).unwrap();
    let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
    assert_eq!(out.roots[0].end, End::Completed);
    // The chain is left as it is (no other pass runs), and the sum under it is read.
    let text = cx.display(out.roots[0].expr).to_string();
    assert!(
        text.contains("zext<33>(b) + zext<33>(a)"),
        "{}",
        &text[..200.min(text.len())]
    );
    assert!(!text.contains("<u"));
}

/// A word made handler by handler in limbs of `k` and `32 − k` bits: each operand after the
/// first joins it by XOR (`x`, written `w + o − 2·(w & o)`), by addition (`a`) or by
/// subtraction (`s`), with the carries and borrows between the limbs. The handlers, and the
/// high limb as a 32-bit value.
fn limbs(ops: &[String], kinds: &[u8], k: u32) -> (String, String) {
    fn add(lets: &mut Vec<String>, e: String) -> String {
        lets.push(e);
        format!("%{}", lets.len() - 1)
    }
    let m = (1u64 << k) - 1;
    let mut lets: Vec<String> = Vec::new();
    let mut word = ops[0].clone();
    let mut low = add(&mut lets, format!("{word} & {m}"));
    let mut high = add(&mut lets, format!("{word} >>u {k}"));
    for (o, kind) in ops[1..].iter().zip(kinds) {
        let ol = add(&mut lets, format!("{o} & {m}"));
        match kind {
            b'a' => {
                let s = add(&mut lets, format!("{word} + {o}"));
                let sl = add(&mut lets, format!("{s} & {m}"));
                let carry = below(&sl, &low);
                high = add(
                    &mut lets,
                    format!("{high} + ({o} >>u {k}) + zext<32>({carry})"),
                );
                (word, low) = (s, sl);
            }
            b's' => {
                let s = add(&mut lets, format!("{word} - {o}"));
                let sl = add(&mut lets, format!("{s} & {m}"));
                let borrow = below(&low, &ol);
                high = add(
                    &mut lets,
                    format!("{high} - ({o} >>u {k}) - zext<32>({borrow})"),
                );
                (word, low) = (s, sl);
            }
            _ => {
                let a = add(&mut lets, format!("{word} & {o}"));
                let s = add(&mut lets, format!("{word} + {o}"));
                let x = add(&mut lets, format!("{s} + {a} * -2"));
                let sl = add(&mut lets, format!("{s} & {m}"));
                let xl = add(&mut lets, format!("{x} & {m}"));
                let carry = format!("zext<32>({})", below(&sl, &low));
                let borrow = format!("sext<32>({})", below(&sl, &xl));
                let both = format!(
                    "trunc<32>((zext<64>({high}) << 1) + zext<64>({low} >>u {}))",
                    k - 1
                );
                high = add(
                    &mut lets,
                    format!(
                        "-({o} >>u {} & {both}) + ({high} + ({o} >>u {k}) + {carry}) + {borrow}",
                        k - 1
                    ),
                );
                (word, low) = (x, xl);
            }
        }
    }
    let text = lets
        .iter()
        .enumerate()
        .map(|(i, e)| format!("let %{i} = {e}; "))
        .collect();
    (text, high)
}

/// One operation over many values is one value, whatever the order and the grouping it was
/// written in: of 3 operands as of 100.
#[test]
fn many_operands_in_any_order_are_one_value() {
    let eng = engine(vec![Phase::Words]);
    let mut g = Rng(0x6d61_6e79);
    for n in [3, 5, 12, 40, 100] {
        let ops: Vec<String> = (0..n).map(|i| format!("v{i}:32")).collect();
        for op in ["^", "+", "&", "|"] {
            let (t, u) = (tree(&mut g, &ops, op), tree(&mut g, &ops, op));
            assert_eq!(
                simplify(&eng, &format!("{t} - {u}"), 32),
                "0:32",
                "{op} of {n}"
            );
            assert_eq!(
                simplify(&eng, &format!("{t} == {u}"), 1),
                "1:1",
                "{op} of {n}"
            );
            // In a slice of the two, and under a mask.
            let slices = format!("extract<7, 25>({t}) - extract<7, 25>({u})");
            assert_eq!(simplify(&eng, &slices, 25), "0:25", "{op} of {n}");
            let masked = format!("({t} & m:32) - ({u} & m:32)");
            assert_eq!(simplify(&eng, &masked, 32), "0:32", "{op} of {n}");
        }
    }
}

/// A word made in limbs from many operands is read as the word: the high limb is the slice
/// of the word the operations make, whatever order that one is written in.
#[test]
fn a_word_made_in_limbs_of_many_operands_is_the_word() {
    let eng = engine(vec![Phase::Words]);
    let mut g = Rng(0x6c69_6d62);
    for (kind, op, sizes) in [
        (b'x', "^", [2usize, 3, 5, 9, 24]),
        (b'a', "+", [2, 3, 5, 9, 60]),
    ] {
        for n in sizes {
            for k in [7, 18] {
                let ops: Vec<String> = (0..n).map(|i| format!("v{i}:32")).collect();
                let (lets, high) = limbs(&ops, &vec![kind; n - 1], k);
                let w = 32 - k;
                let word = tree(&mut g, &ops, op);
                let src = format!("{lets}trunc<{w}>({high}) - extract<{k}, {w}>({word})");
                let zero = format!("0:{w}");
                assert_eq!(simplify(&eng, &src, w as u16), zero, "{op} of {n} at {k}");
            }
        }
    }
    // The operations mixed: the word is the operands joined in the handlers' order.
    let ops: Vec<String> = (0..7).map(|i| format!("v{i}:32")).collect();
    let (lets, high) = limbs(&ops, b"axsxas", 12);
    let word = "((((((v0:32 + v1:32) ^ v2:32) - v3:32) ^ v4:32) + v5:32) - v6:32)";
    let src = format!("{lets}trunc<20>({high}) - extract<12, 20>({word})");
    assert_eq!(simplify(&eng, &src, 20), "0:20");
}
