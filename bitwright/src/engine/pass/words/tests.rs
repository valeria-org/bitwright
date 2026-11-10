//! The words pass: soundness (exhaustive over narrow symbols), what it reads, that it reaches a
//! fixed point, and that it does not depend on how an expression was built.

use crate::engine::tests::{equivalent, generator};
use crate::engine::{End, Engine, Phase, Run, Strategy};
use crate::testutil::Rng;
use crate::{Context, ParseOptions, Width};

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

#[test]
fn words_is_sound_and_idempotent() {
    let eng = engine(vec![Phase::Words]);
    let mut g = generator(0x3074_0001);
    let mut rng = Rng(5);
    let mut changed = 0;
    for i in 0..3200 {
        let mut cx = Context::new();
        // Limb code, right and wrong; and every operator the pass reads, in any mixture.
        let e = if i % 4 == 0 {
            let w = 1 + g.rng.below(6) as u16;
            g.expr(&mut cx, w, 5).0
        } else {
            let (src, w) = if i % 4 == 3 {
                chain_text(&mut g.rng)
            } else {
                limb_text(&mut g.rng)
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
    for i in 0..600 {
        let mut cx = Context::new();
        let (src, w) = if i % 3 == 2 {
            chain_text(&mut g)
        } else {
            limb_text(&mut g)
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
