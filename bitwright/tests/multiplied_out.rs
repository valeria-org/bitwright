//! Sums of products whose factors are affine in one value: `Σ (αᵢ·t + βᵢ)·gᵢ + rest`, the
//! `gᵢ` bitwise functions of `t` and other values. An obfuscator multiplies a linear MBA
//! term by term with values it derives from one value, so the whole is a polynomial over
//! what `t` is made of: a question as large as `t`, which the solver runs out of steps on
//! or which is kept from it for a part that did. Multiplied out over the factors it is
//! `t·Σ αᵢ·gᵢ + (Σ βᵢ·gᵢ + rest)`, two linear MBAs over the atoms of the `gᵢ`, and a value
//! the `gᵢ` read that the sum does not depend on is gone from each.
//!
//! The questions under `questions/` are a devirtualizer's, as exported ("is this value the
//! constant every sample gave?"), of one function: nine that are constants, undecided at
//! 200 million propagations and by Z3 in a minute, and six that are not constants, which
//! must never be proved.
#![cfg(all(feature = "mba", feature = "prove"))]

use bitwright::engine::{Engine, Run, Strategy};
use bitwright::mba::MbaConfig;
use bitwright::prove::{self, Config, Outcome};
use bitwright::{BitVec, Context, Expr, ParseOptions, SymbolKey, Width};

/// The questions whose value is the constant every sample gave.
const CONSTANTS: [&str; 9] = [
    include_str!("questions/multiplied_out_0026.txt"),
    include_str!("questions/multiplied_out_0027.txt"),
    include_str!("questions/multiplied_out_0028.txt"),
    include_str!("questions/multiplied_out_0029.txt"),
    include_str!("questions/multiplied_out_0030.txt"),
    include_str!("questions/multiplied_out_0031.txt"),
    include_str!("questions/multiplied_out_0032.txt"),
    include_str!("questions/multiplied_out_0033.txt"),
    include_str!("questions/multiplied_out_0034.txt"),
];

/// Questions of the same function whose value is not the one every sample gave: a
/// comparison with a free 32-bit value.
const COMPARISONS: [&str; 3] = [
    include_str!("questions/multiplied_out_0004.txt"),
    include_str!("questions/multiplied_out_0005.txt"),
    include_str!("questions/multiplied_out_0006.txt"),
];

/// And three that differ from it at [`WITNESS`].
const WITNESSED: [&str; 3] = [
    include_str!("questions/multiplied_out_0007.txt"),
    include_str!("questions/multiplied_out_0008.txt"),
    include_str!("questions/multiplied_out_0009.txt"),
];

/// Values of the symbols at which the questions of [`WITNESSED`] are 1 where every sample
/// gave 0.
const WITNESS: [(u64, u64); 7] = [
    (3, 0xffff_ffff_ffff_ffff),
    (8, 0xd6e1_bf16_0e17_0b92),
    (15, 0),
    (7052, 0x1015_5c21_9041_7114),
    (7063, 0xbeef_ff35_e7bf_df5f),
    (7064, 0x5440_1210_8000_0040),
    (7630, 0x5e7d_53ca_c90c_a666),
];

fn parse(cx: &mut Context, text: &str) -> Expr {
    cx.parse(text, &ParseOptions::width(Width::W64))
        .unwrap_or_else(|err| panic!("{text}: {err}"))
}

/// A question file's root and its sampled value as a constant of the root's width.
fn question(cx: &mut Context, file: &str) -> (Expr, Expr) {
    let sampled = file
        .lines()
        .find_map(|l| l.strip_prefix("# sampled: 0x"))
        .map(|v| u64::from_str_radix(v, 16).expect("a sampled value"))
        .expect("a `# sampled:` line");
    let (_, root) = file
        .split_once("## root 0\n")
        .or_else(|| file.split_once("## root 0\r\n"))
        .expect("a root");
    assert!(
        !root.contains("## assume"),
        "a question without assumptions"
    );
    let e = parse(cx, root);
    let w = cx.width(e).expect("a width");
    let k = cx
        .constant(&BitVec::wrapping_from_u64(w, sampled))
        .expect("a constant");
    (e, k)
}

fn deobfuscate(cx: &mut Context, e: Expr) -> Expr {
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
        .build()
        .expect("an engine");
    engine.run(cx, &[e], Run::default()).expect("a run").roots[0].expr
}

/// A consumer's limits: 2,000 conflicts, 20,000 propagations, 200,000 nodes.
fn limits(fuel: Option<u64>) -> Config {
    let mut cfg = Config::default();
    cfg.max_conflicts = 2_000;
    cfg.max_propagations = 20_000;
    cfg.max_nodes = 200_000;
    match fuel {
        Some(fuel) => cfg.with_simplify_fuel(fuel),
        None => cfg,
    }
}

/// The names of the symbols `e` reads.
fn symbols(cx: &mut Context, e: Expr) -> Vec<String> {
    let ids = cx.symbols_in(&[e]).expect("symbols");
    let mut names: Vec<String> = (ids.into_iter())
        .filter_map(|id| match cx.symbol_key(id)? {
            SymbolKey::Str(name) => Some(name.to_string()),
            other => Some(format!("{other:?}")),
        })
        .collect();
    names.sort();
    names
}

/// Seeded values of `e`'s symbols, `points` of them: zero, all ones, sparse, dense and
/// uniform words.
fn seeded(cx: &mut Context, e: Expr, seed: u64, points: usize) -> Vec<Vec<(SymbolKey, BitVec)>> {
    let ids = cx.symbols_in(&[e]).expect("symbols");
    let keys: Vec<(SymbolKey, Width)> = (ids.into_iter())
        .filter_map(|id| Some((cx.symbol_key(id)?.clone(), cx.symbol_width(id)?)))
        .collect();
    let mut state = 0x243f_6a88_85a3_08d3_u64 ^ seed;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state.wrapping_mul(0x2545_f491_4f6c_dd1d)
    };
    (0..points)
        .map(|_| {
            (keys.iter())
                .map(|(key, w)| {
                    let v = match next() % 8 {
                        0 => 0,
                        1 => u64::MAX,
                        2 => next() & next(),
                        3 => next() | next(),
                        _ => next(),
                    };
                    (key.clone(), BitVec::wrapping_from_u64(*w, v))
                })
                .collect()
        })
        .collect()
}

/// `text` simplified, shown, with the symbols the result reads; the result is the input
/// at seeded points (by the evaluator: a search does not decide 64-bit products).
fn simplified(text: &str) -> (String, Vec<String>) {
    let mut cx = Context::new();
    let e = parse(&mut cx, text);
    let r = deobfuscate(&mut cx, e);
    for model in seeded(&mut cx, e, 0, 1024) {
        let values = cx.eval(&[e, r], &model[..]).expect("values");
        assert_eq!(
            values[0],
            values[1],
            "{text}\n  is not\n{} at {model:?}",
            cx.display(r)
        );
    }
    (cx.display(r).to_string(), symbols(&mut cx, r))
}

#[test]
fn complementary_cofactors_cancel() {
    assert_eq!(simplified("x * a + x * ~a").0, "-x");
    // Factors that are the value more or less a constant, or a multiple of it.
    assert_eq!(
        simplified("(x + 1) * (a | b) - x * (a & b) - (x + 1) * (a ^ b) - (a & b)").0,
        "0:64"
    );
    assert_eq!(
        simplified("(3 * x + 5) * (a | b) - (3 * x + 1) * (a & b) - (3 * x + 5) * (a ^ b) - 4 * (a & b) + x").0,
        "x"
    );
}

/// The value the factors are affine in is any subterm: a quotient, a product, a sum of
/// several values; and the cofactors may read it too, as itself or as a value affine in it.
#[test]
fn the_value_is_any_subterm() {
    let (r, _) = simplified(
        "(udiv(p, 7) + 1) * (a | b) - udiv(p, 7) * (a & b) - (udiv(p, 7) + 1) * (a ^ b) - (a & b)",
    );
    assert_eq!(r, "0:64");
    // Over a product, the cofactors bitwise functions of `7 − t`.
    let (r, syms) = simplified(
        "let t = (s ^ 0x1fe73e30a8480f31) * q; let u = 7 - t; \
         (3 * t + 5) * (u | b) - (3 * t + 1) * (u & b) - (3 * t + 5) * (u ^ b) - 4 * (u & b) \
         + t * (~b | u) + t * (b & ~u)",
    );
    assert_eq!(r, "-(s ^ 0x1fe73e30a8480f31) * q");
    assert_eq!(syms, ["q", "s"]);
    // Over a sum of two values (`t` is no atom of the linear forms: its two terms are).
    let (r, syms) = simplified(
        "let t = (s ^ 0x1fe73e30a8480f31) * q + udiv(p, 7); let u = 7 - t; \
         (3 * t + 5) * (u | b) - (3 * t + 1) * (u & b) - (3 * t + 5) * (u ^ b) - 4 * (u & b) \
         + t * (~b | u) + t * (b & ~u)",
    );
    assert_eq!(r, "-(s ^ 0x1fe73e30a8480f31) * q - udiv(p, 7)");
    assert_eq!(syms, ["p", "q", "s"]);
}

/// The questions' core: three products over `z = s ^ k` (a constant of many bit runs, so
/// `z` read whole is a bitwise function per run), the cofactors over `r` and
/// `y = 0x1fffff·z − 23783`. On its low 21 bits the sum does not depend on `r`.
const CORE: &str = "(~(y + 23783) * 0xfffffffffff6db6e + 0xfffffffffffb8842) * (~r ^ y) \
     + (~(y + 23783) * 0x92492 + 0x477be) * (~r & ~y) \
     + ~y * ((y & r) * 0x92492 + 0xfffffffffff24925)";

#[test]
fn a_variable_the_sum_does_not_depend_on_is_gone() {
    // As the questions read it: one bit of the sum under a xor and an addition.
    let (r, syms) = simplified(&format!(
        "let z = s ^ 0x1fe73e30a8480f31; let y = z * 0x1fffff - 23783; \
         extract<20, 1>((({CORE} - z * 0x1b6db724924 + 0xffffffffffe8fcc2) ^ 0x1fe73e30a8480f31) \
         + 0xfffffffffff63edf)"
    ));
    assert_eq!(syms, ["s"], "{r}");
    // Over a sum of two values, under a mask.
    let (r, syms) = simplified(&format!(
        "let z = (s ^ 0x1fe73e30a8480f31) + q * q; let y = z * 0x1fffff - 23783; \
         ({CORE}) & 0x1fffff"
    ));
    assert_eq!(syms, ["q", "s"], "{r}");
    // At the full width `r` stays, in one term: the sum does depend on it there.
    let (r, syms) = simplified(&format!(
        "let z = (s ^ 0x1fe73e30a8480f31) + q * q; let y = z * 0x1fffff - 23783; {CORE}"
    ));
    assert_eq!(syms, ["q", "r", "s"], "{r}");
    assert_eq!(r.matches('r').count(), 1, "{r}");
}

/// The simplifier alone makes each question its sampled constant.
#[test]
fn the_questions_simplify_to_their_constants() {
    for (i, file) in CONSTANTS.iter().enumerate() {
        let mut cx = Context::new();
        let (e, k) = question(&mut cx, file);
        let r = deobfuscate(&mut cx, e);
        assert_eq!(r, k, "question {i}: {}", cx.display(r));
    }
}

/// The prover decides each at a consumer's limits, the engine on 131,072 or 524,288 units
/// of fuel or on its default; the search alone does not at ten thousand times those.
#[test]
fn the_questions_are_proved_at_small_limits() {
    for (i, file) in CONSTANTS.iter().enumerate() {
        for fuel in [Some(1 << 17), Some(1 << 19), None] {
            let mut cx = Context::new();
            let (e, k) = question(&mut cx, file);
            let cfg = limits(fuel);
            let out = prove::equal(&mut cx, e, k, &cfg).expect("a question");
            assert!(
                matches!(out, Outcome::Proved(_)),
                "question {i}, fuel {fuel:?}: {out:?}"
            );
            let p = cx.eq(e, k).expect("an equality");
            let out = prove::valid_under(&mut cx, p, None, &cfg).expect("a question");
            assert!(
                matches!(out, Outcome::Proved(_)),
                "question {i}, fuel {fuel:?}: {out:?}"
            );
        }
    }
}

/// The constants are constants at seeded values of the symbols too (every case of the
/// selects among them), by the evaluator and not by the engine.
#[test]
fn the_constants_hold_at_seeded_points() {
    for (i, file) in CONSTANTS.iter().enumerate() {
        let mut cx = Context::new();
        let (e, k) = question(&mut cx, file);
        let want = cx.eval(&[k], &[][..]).expect("a constant")[0];
        for (point, model) in seeded(&mut cx, e, i as u64, 4096).into_iter().enumerate() {
            let got = cx.eval(&[e], &model[..]).expect("a value")[0];
            assert_eq!(got, want, "question {i}, point {point}: {model:?}");
        }
    }
}

/// The questions that are not constants are not proved to be, at those limits or with the
/// engine's default budget, and the simplified root still takes another value where the
/// question does.
#[test]
fn what_is_not_a_constant_is_not_proved_one() {
    for (i, file) in COMPARISONS.iter().chain(&WITNESSED).enumerate() {
        for fuel in [Some(1 << 14), Some(1 << 17), Some(1 << 19), None] {
            let mut cx = Context::new();
            let (e, k) = question(&mut cx, file);
            let cfg = limits(fuel);
            let out = prove::equal(&mut cx, e, k, &cfg).expect("a question");
            assert!(
                !matches!(out, Outcome::Proved(_)),
                "question {i}, fuel {fuel:?}: {out:?}"
            );
        }
    }
    for (i, file) in WITNESSED.iter().enumerate() {
        let mut cx = Context::new();
        let (e, k) = question(&mut cx, file);
        let r = deobfuscate(&mut cx, e);
        let model: Vec<(SymbolKey, BitVec)> = (WITNESS.iter())
            .map(|&(key, v)| {
                (
                    SymbolKey::U64(key),
                    BitVec::wrapping_from_u64(Width::W64, v),
                )
            })
            .collect();
        let values = cx.eval(&[e, r, k], &model[..]).expect("values");
        assert_ne!(values[0], values[2], "question {i}");
        assert_eq!(values[0], values[1], "question {i}: {}", cx.display(r));
    }
    // A comparison with a free value: the root is that value's equal at some value of it.
    for (i, file) in COMPARISONS.iter().enumerate() {
        let mut cx = Context::new();
        let (e, _) = question(&mut cx, file);
        let r = deobfuscate(&mut cx, e);
        assert!(
            symbols(&mut cx, r).contains(&"U64(7064)".to_owned()),
            "question {i}: {}",
            cx.display(r)
        );
    }
}
