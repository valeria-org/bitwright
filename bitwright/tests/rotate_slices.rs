//! Opaque predicates over two spellings of one slice of a rotated value: `(t >>u 57) & k` and
//! `rotl(t, 7) & 0x74` are the same four bits of `t`, their difference is 0, and what an
//! obfuscator multiplies by `(difference · c) | 1` is multiplied by 1. Written over one
//! rotation the difference is gone at construction, so the MBA phase has no question left to
//! ask a solver: the fragment as rewritten is the answer.
//!
//! The questions under `questions/` are a devirtualizer's, as exported ("is this value the
//! constant every sample gave?"): one family of thirteen, each over a 64 by 64 bit product
//! that a search does not decide once the identity is missed.
#![cfg(all(feature = "mba", feature = "prove"))]

use bitwright::engine::{Engine, Run, Strategy};
use bitwright::mba::MbaConfig;
use bitwright::prove::{self, Config, Outcome};
use bitwright::{BitVec, Context, Expr, ParseOptions, Width};

/// The exported questions: the value every sample gave, and the expression.
const QUESTIONS: [&str; 13] = [
    include_str!("questions/rotate_mask_8665.txt"),
    include_str!("questions/rotate_mask_8666.txt"),
    include_str!("questions/rotate_mask_8667.txt"),
    include_str!("questions/rotate_mask_8668.txt"),
    include_str!("questions/rotate_mask_8669.txt"),
    include_str!("questions/rotate_mask_8670.txt"),
    include_str!("questions/rotate_mask_8671.txt"),
    include_str!("questions/rotate_mask_8672.txt"),
    include_str!("questions/rotate_mask_8673.txt"),
    include_str!("questions/rotate_mask_8674.txt"),
    include_str!("questions/rotate_mask_8675.txt"),
    include_str!("questions/rotate_mask_8676.txt"),
    include_str!("questions/rotate_mask_8677.txt"),
];

/// A question file's sampled value and its root, parsed, with the value as a constant of
/// the root's width.
fn question(cx: &mut Context, file: &str) -> (Expr, Expr) {
    let sampled = file
        .lines()
        .find_map(|l| l.strip_prefix("# sampled: 0x"))
        .map(|v| u64::from_str_radix(v, 16).expect("a sampled value"))
        .expect("a `# sampled:` line");
    let (_, root) = file.split_once("## root 0\n").expect("a root");
    assert!(
        !root.contains("## assume"),
        "a question without assumptions"
    );
    let e = cx
        .parse(root, &ParseOptions::width(Width::W64))
        .unwrap_or_else(|err| panic!("{err}"));
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

fn simplified(text: &str) -> String {
    let mut cx = Context::new();
    let e = cx
        .parse(text, &ParseOptions::width(Width::W64))
        .unwrap_or_else(|err| panic!("{text}: {err}"));
    let r = deobfuscate(&mut cx, e);
    cx.display(r).to_string()
}

#[test]
fn two_spellings_of_one_slice_cancel() {
    // Bits 2, 4, 5 and 6 of `rotl(x, 7)`: the shift has seven bits, of which the first mask
    // keeps those four.
    let a = "(x >>u 57 & 0xea00b727740fb274)";
    let b = "(rotl(x, 7) & 116)";
    assert_eq!(simplified(&format!("{a} - {b}")), "0:64");
    assert_eq!(simplified(&format!("{b} - {a}")), "0:64");
    assert_eq!(
        simplified(&format!("(({a} - {b}) * 0x924924924924925 | 1) * y")),
        "y"
    );
    // Over a value that is arithmetic itself, and the high bits a left shift keeps.
    assert_eq!(
        simplified("let t = rotl(x + 3, 44) + y; (rotl(t, 9) & 0x1400) - ((t & 10) << 9)"),
        "0:64"
    );
    // Not the same bits: nothing to cancel, and the same value at every point.
    let other = simplified(&format!("(x >>u 57 & 0x70) - {b}"));
    assert_ne!(other, "0:64");
}

/// The simplifier alone makes each question its sampled constant.
#[test]
fn the_questions_simplify_to_their_constants() {
    for (i, file) in QUESTIONS.iter().enumerate() {
        let mut cx = Context::new();
        let (e, k) = question(&mut cx, file);
        let r = deobfuscate(&mut cx, e);
        assert_eq!(r, k, "question {i}: {}", cx.display(r));
    }
}

/// The prover decides each at a consumer's limits (2,000 conflicts, 20,000 propagations,
/// 200,000 nodes, the engine on 131,072 or 524,288 units of fuel or on its default), which
/// the search alone does not at ten thousand times those. (The engine takes about 5,000
/// node visits and 800,000 units of pass work to bring a question to the two slices: on
/// 65,536 units of fuel or fewer it stops before them, and the question is not decided.)
#[test]
fn the_questions_are_proved_at_small_limits() {
    for (i, file) in QUESTIONS.iter().enumerate() {
        for fuel in [Some(1 << 17), Some(1 << 19), None] {
            let mut cx = Context::new();
            let (e, k) = question(&mut cx, file);
            let mut cfg = Config::default();
            cfg.max_conflicts = 2_000;
            cfg.max_propagations = 20_000;
            cfg.max_nodes = 200_000;
            if let Some(fuel) = fuel {
                cfg = cfg.with_simplify_fuel(fuel);
            }
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
