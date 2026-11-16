//! Sums of masked bitwise functions of two values that a bitwise operator reads, which a
//! devirtualizer's documents kept as named computations of a VM's handlers.
//!
//! Thirty-one products `cᵢ·fᵢ(x, y)` over bitwise functions with constant masks add up to
//! `(x ^ y) & m | k`. The sum sits under `&` with another function of `x` and `y`, then under
//! `^` with constants and a shift, and the result is a constant or one value. The solver
//! finds that; the certificates took the sum under `&` for an atom unrelated to `x` and `y`,
//! so the answer was not proved and the fragment stayed as it was.
//!
//! A side is now also read as a constant plus, at every bit position, a multiple of each
//! product of the variables' bits there. Sums, differences and products by constants keep
//! such a form; a bitwise operator takes operands that carry nothing (each bit a function of
//! the variables' bits at one position) and gives one. A value has at most one such form, so
//! two sides with forms are compared exactly.
//!
//! Every result is compared with its input by `prove::equal`.
#![cfg(all(feature = "mba", feature = "prove"))]

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::{self, MbaBudget, MbaConfig, MbaLimits, Verdict};
use bitwright::prove::{self, Outcome};
use bitwright::{Context, Expr, ParseOptions, Width};

/// `__vm_f2_80662a5f_8`: bits 19 and 23 of a masked sum of 31 products under `&`, `^`.
const SUM_UNDER_AND: &str = include_str!("sums/80662a5f_8.txt");
/// `__vm_f2_fb749cd7_b`: the same sum with other masks, read through a 32-bit shift.
const SUM_WITH_DIFFERENCE: &str = include_str!("sums/fb749cd7_b.txt");
/// `__vm_f3_0f424748_d`: the same sum over two values, added to a third.
const SUM_BESIDE_A_VALUE: &str = include_str!("sums/0f424748_d.txt");

fn parse(cx: &mut Context, text: &str) -> Expr {
    cx.parse(text, &ParseOptions::width(Width::W64))
        .unwrap_or_else(|err| panic!("{err}"))
}

/// The engine as the devirtualizer asks it; `strict`: every step proved.
fn engine(strict: bool) -> Engine {
    let mba = MbaConfig::default().with_opaque_sweep(true);
    Engine::builder()
        .builtin()
        .strategy(
            Strategy::deobfuscate()
                .with_mba(mba)
                .with_words_proved(strict),
        )
        .build()
        .expect("an engine")
}

fn nodes(cx: &mut Context, e: Expr) -> u32 {
    match cx.dag_size(&[e], 1 << 20).expect("a size") {
        bitwright::Bounded::Exact(n) => n,
        other => panic!("{other:?}"),
    }
}

/// What both engines leave of `text` within the devirtualizer's fuel: the same expression,
/// proved equal to `text`.
fn simplified(cx: &mut Context, text: &str) -> (Expr, Expr) {
    let e = parse(cx, text);
    let run = || Run::default().with_per_call(Budget::fuel(1 << 21));
    let out = engine(false).run(cx, &[e], run()).expect("a run").roots[0].expr;
    let strict = engine(true).run(cx, &[e], run()).expect("a run").roots[0].expr;
    assert_eq!(out, strict, "the strict engine leaves the same");
    assert!(
        matches!(
            prove::equal(cx, e, out, &Default::default()),
            Ok(Outcome::Proved(_))
        ),
        "not proved equal: {}",
        cx.display(out)
    );
    (e, out)
}

fn equal(a: &str, b: &str) -> Verdict {
    let mut cx = Context::new();
    let (a, b) = (parse(&mut cx, a), parse(&mut cx, b));
    mba::equal(&mut cx, a, b, &MbaLimits::default(), &MbaBudget::default()).expect("a verdict")
}

#[test]
fn a_masked_sum_under_a_bitwise_operator_is_the_function_it_is() {
    for (text, before, want) in [
        (SUM_UNDER_AND, 273, "1:64"),
        (SUM_WITH_DIFFERENCE, 281, "0:64"),
        (
            SUM_BESIDE_A_VALUE,
            289,
            "x2 + 0x13afd5fcffa93483 & 0x3001fffff2df",
        ),
    ] {
        let mut cx = Context::new();
        let (e, out) = simplified(&mut cx, text);
        assert_eq!(nodes(&mut cx, e), before);
        assert_eq!(cx.display(out).to_string(), want);
    }
}

/// The certificates on their own: a sum that is a bitwise function, read by a bitwise
/// operator beside the values it is made of and compared with a function of those values
/// that does not spell the sum.
#[test]
fn a_sum_that_carries_nothing_is_a_bitwise_function_of_its_values() {
    // `(x & y) + (x | y) = x + y` at every bit class, so the products by 3 cancel and the
    // sum is `(x ^ y) & 0x0ff0 | 0x7000000a`.
    let sum = "((x & y & 0xf0f0) * 3 + ((x | y) & 0xf0f0) * 3 - (x & 0xf0f0) * 3 \
               - (y & 0xf0f0) * 3 + ((x | y) & 0x0ff0) - (x & y & 0x0ff0) + 0x7000000a)";
    // That, under `& (x | 0xff00ff)`, as its minterms.
    let is = "((x & ~y & 0xff0) | (~x & y & 0xf0) | (x & 0x7000000a) | 0xa)";
    assert_eq!(
        equal(&format!("{sum} & (x | 0xff00ff)"), is),
        Verdict::Proved
    );
    // Read through a constant and a shift: the tests before this one leave it open.
    assert_eq!(
        equal(
            &format!("({sum} & (x | 0xff00ff) ^ 0x5d6c) >>u 3 & 0x11"),
            &format!("({is} ^ 0x5d6c) >>u 3 & 0x11")
        ),
        Verdict::Proved
    );
    // Three values.
    assert_eq!(
        equal(
            "(((x & y) + (x | y) - x - (y & z) - (y & ~z) + (x & z) + (x & ~z)) & (y | z) ^ 9) \
             >>u 2 & 5",
            "((x & y | x & z) ^ 9) >>u 2 & 5"
        ),
        Verdict::Proved
    );
    // One step away: another constant, another mask, a sum that does carry.
    assert_eq!(
        equal(
            &format!("({sum} & (x | 0xff00ff) ^ 0x5d6c) >>u 3 & 0x11"),
            "(((x & ~y & 0xff0) | (~x & y & 0xf0) | (x & 0x7000000a) | 0x8a) ^ 0x5d6c) >>u 3 \
             & 0x11"
        ),
        Verdict::Refuted
    );
    assert_ne!(
        equal(
            &format!("({sum} & (x | 0xff00ff) ^ 0x5d6c) >>u 3 & 0x11"),
            "(((x & ~y & 0xff0) | (~x & y & 0x70) | (x & 0x7000000a) | 0xa) ^ 0x5d6c) >>u 3 \
             & 0x11"
        ),
        Verdict::Proved
    );
    assert_ne!(
        equal(
            "(((x & 0xff) + (y & 0xff)) & (x | 0xff00ff) ^ 0x5d6c) >>u 3 & 0x11",
            "(((x ^ y) & 0xff) & (x | 0xff00ff) ^ 0x5d6c) >>u 3 & 0x11"
        ),
        Verdict::Proved
    );
}
