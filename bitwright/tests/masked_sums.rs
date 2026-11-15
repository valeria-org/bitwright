//! Two families a devirtualizer's documents kept (named computations of a VM's handlers):
//! linear MBA whose bitwise terms carry constant masks, and sums of products read on a few
//! low bits.
//!
//! - **Masks.** `Σ cᵢ·fᵢ` over bitwise functions `fᵢ` with general masks has one truth table
//!   per bit class (the positions every mask treats alike), so the normal form is a sum of
//!   masked conjunctions per class. Read through `& 0xffffffff` only the classes below bit
//!   32 count and every coefficient counts modulo `2^32`; the solver takes the sum's low
//!   bits for an atom rendered from that part (its `low_read`), with one product per
//!   coefficient up to sign. The certificate for it is `s·2^(W−j) = t·2^(W−j)` for the two
//!   sums `s` and `t`: equal low `j` bits.
//! - **Atoms that are sums.** `p & (Σ …)` over a `p = x + 608` the sum also adds: the
//!   certificate reads `p` as one variable wherever it is read, and a constant a bitwise
//!   operator puts on a left shift inside the shift.
//! - **Demanded bits.** `(m·C + …) & 0x7f` reads the low seven bits of each operand: a mask
//!   under it is its low seven bits, and an operand whose demanded bits are known is gone.
//!
//! Every result is compared with its input by `prove::equal`.
#![cfg(all(feature = "mba", feature = "prove"))]

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::{self, MbaBudget, MbaConfig, MbaLimits, Verdict};
use bitwright::prove::{self, Outcome};
use bitwright::{Context, Expr, ParseOptions, Width};

/// `__vm_f2_021feff5_7` (a `uint32_t`): seven masks, six multipliers, two variables.
const MASKED_SUM_LOW_32: &str = "(((((x0 & x1) & 0x31b06fba0000c3a0) | (0xce4f904564fc3c5f & ~(x0 & x1))) * 0x746607c05b0e3a6e) + (((~(x1 & 0xce4fb045fffffc5f)) * 0xc5ccfc1fd278e2c9) + (((~((x0 & ~x1) ^ 0xce4f904564fc3c5f)) * 0xc5ccfc1fd278e2c9) + ((((x0 | x1) & (0xce4f904564fc3c5f & ~(x0 & x1))) * 0x5166f45f776aa85b) + (((x1 | 0x31b05fbb64fc33ef) * 0x8b99f83fa4f1c592) + (((x1 | 0xffffeffe9b03cfb0) * 0x746607c05b0e3a6e) + (((x1 & 0x100164fc304f) * 0x3a3303e02d871d37) + ((x1 ^ 0x20009b03c000) * 0xc5ccfc1fd278e2c9)))))))) & 0xffffffff";

/// `__vm_f4_883ecf45_7`: one mask over `x1`, `x0 + 608` and `x2 + x3`, read by `&`.
const MASKED_SUM_UNDER_AND: &str = "((x0 + 0x308) - 0xa8) & ((((((((((((~x1) & 0x3001fffff0af) ^ (x2 + x3)) << 1) + (~(((~x1) & 0x3001fffff0af) & (x2 + x3)))) - (x1 ^ ((~((x2 + x3) & 0x3001fffff0af)) & ((x2 + x3) | ~((x0 + 0x308) - 0xa8))))) + (~((x2 + x3) ^ (x1 & 0x3001fffff0af)))) + ((((x0 + 0x308) - 0xa8) & (x1 | ~(x2 + x3))) * 0xfffffffffffffffe)) + ((~((x2 + x3) ^ (x1 & 0x3001fffff0af))) << 1)) + (((~x1) & (~((x2 + x3) & 0x3001fffff0af))) * 0xfffffffffffffffe)) - ((((~x1) | (x2 + x3)) & ((x1 | ~(x2 + x3)) & 0x3001fffff0af)) << 2)) + ((~x1) & ((x2 + x3) | ~((x0 + 0x308) - 0xa8))))";

/// `__vm_f4_0462fb4b_8`: the same sum, read by `|`, `&` and `~`.
const MASKED_SUM_UNDER_OR: &str = "(((((((((((((~x0) & 0x3001fffff0af) ^ (x1 + x2)) << 1) + (~(((~x0) & 0x3001fffff0af) & (x1 + x2)))) - (x0 ^ ((~((x1 + x2) & 0x3001fffff0af)) & ((x1 + x2) | ~((x3 + 0x308) - 0xa8))))) + (~((x1 + x2) ^ (x0 & 0x3001fffff0af)))) + ((((x3 + 0x308) - 0xa8) & (x0 | ~(x1 + x2))) * 0xfffffffffffffffe)) + ((~((x1 + x2) ^ (x0 & 0x3001fffff0af))) << 1)) + (((~x0) & (~((x1 + x2) & 0x3001fffff0af))) * 0xfffffffffffffffe)) - ((((~x0) | (x1 + x2)) & ((x0 | ~(x1 + x2)) & 0x3001fffff0af)) << 2)) + ((~x0) & ((x1 + x2) | ~((x3 + 0x308) - 0xa8)))) | (x3 + 0x260)) & ~(((x3 + 0x308) - 0xa8) & ((((((((((((~x0) & 0x3001fffff0af) ^ (x1 + x2)) << 1) + (~(((~x0) & 0x3001fffff0af) & (x1 + x2)))) - (x0 ^ ((~((x1 + x2) & 0x3001fffff0af)) & ((x1 + x2) | ~((x3 + 0x308) - 0xa8))))) + (~((x1 + x2) ^ (x0 & 0x3001fffff0af)))) + ((((x3 + 0x308) - 0xa8) & (x0 | ~(x1 + x2))) * 0xfffffffffffffffe)) + ((~((x1 + x2) ^ (x0 & 0x3001fffff0af))) << 1)) + (((~x0) & (~((x1 + x2) & 0x3001fffff0af))) * 0xfffffffffffffffe)) - ((((~x0) | (x1 + x2)) & ((x0 | ~(x1 + x2)) & 0x3001fffff0af)) << 2)) + ((~x0) & ((x1 + x2) | ~((x3 + 0x308) - 0xa8)))))";

/// `__vm_f2_dd43a3fd_9`: three products of masked shifts, read by `& 0x7f`.
const PRODUCTS_LOW_7: &str = "((((((~((~((x0 ^ 0xad780cfe70032406) << 0x35)) & (~((x0 ^ 0xad780cfe70032406) >>u 0xb)))) >>u 0x1a) & 0x2441201) * 0xceed791241c52709) + (((((((~((x0 ^ 0xad780cfe70032406) << 0x35)) & (~((x0 ^ 0xad780cfe70032406) >>u 0xb))) >>u 0x39) & 1) * 0x1b38cc5f73930924) + x1) | ((((~((x0 ^ 0xad780cfe70032406) >>u 0xb)) >>u 0x10) & 0x1000000001) * 0x4b7e46ed32f942a))) & 0x7f) ^ 0x2e4c69e89bb4d03d";

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

#[test]
fn a_masked_sum_read_on_its_low_half_is_one_product_a_multiplier() {
    let mut cx = Context::new();
    let (e, out) = simplified(&mut cx, MASKED_SUM_LOW_32);
    let want = parse(
        &mut cx,
        "(((x0 & x1 & 0x64fc3c5f) - (x1 & 3088)) * 0xe3a39213 + (x0 & 0x64fc3c5f) * 0x49e38b24 \
         + (((x1 & 928) | (x0 & x1 & 0x9b030000)) - (x0 & 0x9b03c3a0) - (x0 & x1 & 50080)) * 0xd278e2c9 \
         + 0xdafed397) & 0xffffffff",
    );
    assert_eq!(nodes(&mut cx, e), 48);
    assert_eq!(out, want, "{}", cx.display(out));
    assert_eq!(nodes(&mut cx, out), 32);
}

#[test]
fn a_masked_sum_over_sums_a_bitwise_operator_reads_is_its_normal_form() {
    for (text, before, after) in [
        (MASKED_SUM_UNDER_AND, 49, 28),
        (MASKED_SUM_UNDER_OR, 54, 28),
    ] {
        let mut cx = Context::new();
        let (e, out) = simplified(&mut cx, text);
        assert_eq!(nodes(&mut cx, e), before);
        assert_eq!(nodes(&mut cx, out), after, "{}", cx.display(out));
        // By the MBA certificates alone, too.
        let verdict = mba::equal(
            &mut cx,
            e,
            out,
            &MbaLimits::default(),
            &MbaBudget::default(),
        );
        assert_eq!(verdict.expect("a verdict"), Verdict::Proved);
    }
}

#[test]
fn products_read_on_seven_bits_keep_seven_bits_of_their_factors() {
    let mut cx = Context::new();
    let (e, out) = simplified(&mut cx, PRODUCTS_LOW_7);
    let want = parse(
        &mut cx,
        "((zext<64>(extract<37, 1>(~x0)) * 9 \
         + ((zext<64>(~extract<4, 1>(x0)) * 36 + x1) | zext<64>(~extract<27, 1>(x0)) * 42)) & 127) \
         ^ 0x2e4c69e89bb4d03d",
    );
    assert_eq!(nodes(&mut cx, e), 37);
    assert_eq!(out, want, "{}", cx.display(out));
    assert_eq!(nodes(&mut cx, out), 24);
}

/// The certificates on their own: each pair is equal, and one step from it is not proved.
#[test]
fn the_certificates_decide_the_families() {
    let (limits, budget) = (MbaLimits::default(), MbaBudget::default());
    for (a, b, equal) in [
        // An atom the sum both reads bitwise and adds.
        (
            "(x + 608) & (((x + 608) & y) + ((x + 608) | y) - (x + 608))",
            "(x + 608) & y",
            true,
        ),
        (
            "(x + 608) & (((x + 608) & y) + ((x + 608) | y) - (x + 607))",
            "(x + 608) & y",
            false,
        ),
        // Its complement written as arithmetic (`−609 − x`), under a mask.
        (
            "(x + 608) & (((-609 - x) & y & 0xff00) + ((x + 608) & y & 0xff00) + (y & 0xff))",
            "(x + 608) & y & 0xffff",
            true,
        ),
        // A constant on a left shift.
        (
            "(z + 3) & ((((x & y) << 1) ^ 0xf0) + ((x | y) << 1))",
            "(z + 3) & ((x + y << 1) + 0xf0 - ((x & y & 0x78) << 2))",
            true,
        ),
        (
            "(z + 3) & ((((x & y) << 1) ^ 0xf0) + ((x | y) << 1))",
            "(z + 3) & ((x + y << 1) + 0xf0 - ((x & y & 0x70) << 2))",
            false,
        ),
    ] {
        let mut cx = Context::new();
        let (ea, eb) = (parse(&mut cx, a), parse(&mut cx, b));
        let verdict = mba::equal(&mut cx, ea, eb, &limits, &budget).expect("a verdict");
        assert_eq!(verdict == Verdict::Proved, equal, "{a} = {b}");
        let proved = matches!(
            prove::equal(&mut cx, ea, eb, &Default::default()),
            Ok(Outcome::Proved(_))
        );
        assert_eq!(proved, equal, "{a} = {b}");
    }
}

/// The solver's answer for a sum read on its low bits, with its own certificate: the sums
/// differ above the bits read.
#[test]
fn the_low_bits_of_a_sum_are_those_of_its_low_classes() {
    use bitwright::mba::{Claim, MbaAnswer, MbaSolver, NormalFormSolver, lift, lower};
    for (text, want) in [
        (
            "(x * 0x100000007 + (y & 0xff00000000)) & 0xffffffff",
            Some("x * 7 & 0xffffffff"),
        ),
        (
            "(x * 0x100000007 + (y & 0xff00000000) + (x & y & 0xf0) * 0xffffffff00000003 \
             + (x & y & 0xf) * 0x300000003) & 0xffffffff",
            Some("(x * 7 + (x & y & 0xff) * 3) & 0xffffffff"),
        ),
        // Every term is read as it is: nothing to drop.
        ("(x * 7 + (y & 0xff000000)) & 0xffffffff", None),
    ] {
        let mut cx = Context::new();
        let e = parse(&mut cx, text);
        let (m, bindings) = lower(&cx, e, &MbaLimits::default()).expect("a fragment");
        let answer = NormalFormSolver::default().solve(&m, &MbaBudget::default());
        match (answer, want) {
            (MbaAnswer::Simplified { expr, claim }, Some(want)) => {
                assert_eq!(claim, Claim::Proved, "{text}");
                let out = lift(&mut cx, &expr, &bindings).expect("an expression");
                let want = parse(&mut cx, want);
                assert_eq!(out, want, "{text}: {}", cx.display(out));
                assert!(matches!(
                    prove::equal(&mut cx, e, out, &Default::default()),
                    Ok(Outcome::Proved(_))
                ));
            }
            (MbaAnswer::NoSimpler, None) => {}
            (other, _) => panic!("{text}: {other:?}"),
        }
    }
}

/// Demanded bits through a product, a sum and a disjunction.
#[test]
fn a_mask_under_a_narrower_one_is_the_bits_read() {
    for (text, want) in [
        // The factor's mask has one bit below 7; the multiplier counts modulo 128. (With
        // the mask `1` there already: constants alone, one for one, are no smaller.)
        (
            "((x >>u 26 & 0x2441201) * 0xceed791241c52709 + (y & 1)) & 0x7f",
            "zext<64>(extract<26, 1>(x)) * 9 + (y & 1)",
        ),
        // No bit below 7: the product is gone.
        (
            "((x >>u 26 & 0x2441200) * 0xceed791241c52709 + y) & 0x7f",
            "y & 127",
        ),
        // An operand whose demanded bits are all ones leaves the other.
        (
            "((~(x << 53) & y) >>u 26) & 1",
            "zext<64>(extract<26, 1>(y))",
        ),
    ] {
        let mut cx = Context::new();
        let (_, out) = simplified(&mut cx, text);
        let want = parse(&mut cx, want);
        assert_eq!(out, want, "{text}: {}", cx.display(out));
    }
}
