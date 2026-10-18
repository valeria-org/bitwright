//! Sums that read one condition several ways: `zext`/`sext` of it, a select between constants,
//! and the carry of a partial-width sum (`concat(H, trunc_j(x + k))`, `zext(trunc_j(x + k))`,
//! `(x + k) & (2^j − 1)`), the condition spelled as a threshold on the low `j` bits of `x`, a
//! masked zero test, an extraction compared with zero, or negated. The linear pass merges them
//! at full width and the demanded-bits pass modulo the bits a mask reads: sound exhaustively at
//! small widths (each pass alone, and the standard and deobfuscating strategies), proved by z3
//! and bitwuzla (each when it is on `PATH`) at 64 bits, and the identities fold.

mod common;

use bitwright::engine::{Engine, Phase, Strategy};
use bitwright::{BitVec, Context, Expr, ParseOptions, SymbolKey, Width};
use common::{Rng, Size};

/// A random sum over `x` (`w` bits) and `y` (2 bits) whose terms read conditions on the low
/// `j` bits of `x`, most with one threshold, maybe under a mask or a truncation.
fn random_sum(rng: &mut Rng, w: u16, j: u16) -> String {
    let full = |v: u128| v & ((1u128 << w) - 1);
    let mask_j = (1u128 << j) - 1;
    // `trunc_j(x) <u t`; a carry of `x + k` is `trunc_j(x) ≥u 2^j − k`.
    let t = 1 + u128::from(rng.below(mask_j as u64));
    let pick = |rng: &mut Rng| u128::from(rng.next()) | (u128::from(rng.next()) << 64);
    let cond = |rng: &mut Rng| -> String {
        let t = if rng.chance(1, 8) {
            1 + u128::from(rng.below(mask_j as u64))
        } else {
            t
        };
        let tr = format!("trunc<{j}>(x)");
        let s = t.trailing_zeros() as u16;
        let pow2 = t.is_power_of_two();
        let (c, eq) = match rng.below(7) {
            0 => (format!("{tr} <u {t}:{j}"), false),
            1 => (format!("{}:{j} <u {tr}", t - 1), false),
            2 => (format!("{tr} <=u {}:{j}", t - 1), false),
            3 => (format!("{t}:{j} <=u {tr}"), false),
            4 if pow2 => (
                format!("(x & {}:{w}) == 0:{w}", mask_j - ((1u128 << s) - 1)),
                true,
            ),
            5 if pow2 => (format!("extract<{s}, {}>(x) == 0:{}", j - s, j - s), true),
            _ => (format!("(x & {mask_j}:{w}) <u {t}:{w}"), false),
        };
        let c = if eq && rng.chance(1, 4) {
            c.replace("==", "!=")
        } else {
            c
        };
        if rng.chance(1, 4) {
            format!("~({c})")
        } else {
            c
        }
    };
    // `x + k`, `k ≡ 2^j − t` on the low bits (other bits random), so its carry meets `cond`.
    let plus = |rng: &mut Rng| {
        let k = if rng.chance(1, 8) {
            1 + u128::from(rng.below(mask_j as u64))
        } else {
            (1u128 << j) - t
        };
        format!("(x + {}:{w})", full((pick(rng) << j) | k))
    };
    let term = |rng: &mut Rng| -> String {
        match rng.below(9) {
            8 => {
                let lo = 1 + rng.below(u64::from(w) - 1);
                let len = 1 + rng.below(u64::from(w) - lo);
                format!(
                    "zext<{w}>(extract<{lo}, {len}>(x & {}:{w}))",
                    full(pick(rng))
                )
            }
            0 => format!("zext<{w}>({})", cond(rng)),
            1 => format!("sext<{w}>({})", cond(rng)),
            2 => format!(
                "select({}, {}:{w}, {}:{w})",
                cond(rng),
                full(pick(rng)),
                full(pick(rng))
            ),
            3 => {
                let h = match rng.below(3) {
                    0 => format!("extract<{j}, {}>(x)", w - j),
                    1 if w - j > 2 => format!("zext<{}>(y)", w - j),
                    _ => format!("{}:{}", pick(rng) & ((1u128 << (w - j)) - 1), w - j),
                };
                format!("concat({h}, trunc<{j}>({}))", plus(rng))
            }
            4 => format!("zext<{w}>(trunc<{j}>({}))", plus(rng)),
            5 => format!("({} & {mask_j}:{w})", plus(rng)),
            6 => "x".to_string(),
            _ => format!("zext<{w}>(y)"),
        }
    };
    let mut e = term(rng);
    for _ in 0..1 + rng.below(3) {
        let t = term(rng);
        let t = if rng.chance(1, 3) {
            format!("({t}) * {}:{w}", full(pick(rng)))
        } else {
            t
        };
        e = format!("({e}) {} ({t})", if rng.chance(1, 2) { "+" } else { "-" });
    }
    match rng.below(7) {
        0 | 1 => format!("({e}) & {}:{w}", full(pick(rng))),
        2 => format!("trunc<{}>({e})", 1 + rng.below(u64::from(w) - 1)),
        3 => {
            let lo = 1 + rng.below(u64::from(w) - 1);
            let len = 1 + rng.below(u64::from(w) - lo);
            format!("extract<{lo}, {len}>(({e}) & {}:{w})", full(pick(rng)))
        }
        _ => e,
    }
}

fn engines() -> Vec<(&'static str, Engine)> {
    let phases = |name: &'static str, p: Phase| {
        let s = Strategy::new(name, vec![p]);
        (
            name,
            Engine::builder().builtin().strategy(s).build().unwrap(),
        )
    };
    vec![
        phases("linear", Phase::Linear),
        phases("demanded", Phase::Demanded),
        ("standard", Engine::standard()),
        (
            "deobfuscate",
            Engine::builder()
                .builtin()
                .strategy(Strategy::deobfuscate())
                .build()
                .unwrap(),
        ),
    ]
}

/// Whether `a` and `b` agree for every `x` (`w` bits) and `y` (2 bits).
fn agree(cx: &mut Context, a: Expr, b: Expr, w: u16) -> bool {
    let (kx, ky): (SymbolKey, SymbolKey) = ("x".into(), "y".into());
    let width = Width::new(w).unwrap();
    for x in 0..1u64 << w {
        for y in 0..4 {
            let env = [
                (kx.clone(), BitVec::wrapping_from_u64(width, x)),
                (
                    ky.clone(),
                    BitVec::wrapping_from_u64(Width::new(2).unwrap(), y),
                ),
            ];
            let v = cx.eval(&[a, b], &env[..]).unwrap();
            if v[0] != v[1] {
                return false;
            }
        }
    }
    true
}

fn parse(cx: &mut Context, src: &str, w: u16) -> Expr {
    cx.symbol("y", Width::new(2).unwrap()).unwrap();
    cx.parse(src, &ParseOptions::width(Width::new(w).unwrap()))
        .unwrap_or_else(|e| panic!("{src}: {e}"))
}

fn exhaustive(size: Size) {
    let engines = engines();
    let mut rng = Rng(0xc0_4d17);
    let mut smaller = vec![0u32; engines.len()];
    let cases = size.pick(250, 4000);
    for _ in 0..cases {
        let w = 3 + rng.below(4) as u16;
        let j = 1 + rng.below(u64::from(w) - 1) as u16;
        let src = random_sum(&mut rng, w, j);
        for (i, (name, eng)) in engines.iter().enumerate() {
            let mut cx = Context::new();
            let e = parse(&mut cx, &src, w);
            let r = eng.simplify(&mut cx, e).unwrap().expr;
            let rw = cx.width(r).unwrap().bits();
            assert!(
                agree(&mut cx, e, r, w),
                "{name} at {w} bits: `{src}` => `{}` ({rw} bits)",
                cx.display(r)
            );
            if cx.tree_size(r).unwrap() < cx.tree_size(e).unwrap() {
                smaller[i] += 1;
            }
        }
    }
    eprintln!("smaller of {cases}: {smaller:?}");
    // Many sums fold, through each pass alone too.
    assert!(smaller.iter().all(|&s| s * 5 > cases), "{smaller:?}");
}

#[test]
fn condition_readings_are_sound_smoke() {
    exhaustive(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn condition_readings_are_sound_heavy() {
    exhaustive(Size::Heavy);
}

/// Above 64 bits (fields up to the width, wider than a threshold key takes): sound on sampled
/// inputs.
#[test]
fn condition_readings_are_sound_wide() {
    let engines = engines();
    let mut rng = Rng(0x0128_c4d1);
    for _ in 0..30 {
        let w = rng.pick(&[65u16, 100, 127]);
        let j = 1 + rng.below(u64::from(w) - 1) as u16;
        let src = random_sum(&mut rng, w, j);
        for (name, eng) in &engines {
            let mut cx = Context::new();
            let e = parse(&mut cx, &src, w);
            let r = eng.simplify(&mut cx, e).unwrap().expr;
            let (kx, ky): (SymbolKey, SymbolKey) = ("x".into(), "y".into());
            for _ in 0..64 {
                let x = rng.bitvec(Width::new(w).unwrap());
                let y = BitVec::wrapping_from_u64(Width::new(2).unwrap(), rng.below(4));
                let env = [(kx.clone(), x), (ky.clone(), y)];
                let v = cx.eval(&[e, r], &env[..]).unwrap();
                assert_eq!(
                    v[0],
                    v[1],
                    "{name} at {w} bits: `{src}` => `{}`",
                    cx.display(r)
                );
            }
        }
    }
}

fn simplify(eng: &Engine, src: &str, w: u16) -> String {
    let mut cx = Context::new();
    let e = parse(&mut cx, src, w);
    let r = eng.simplify(&mut cx, e).unwrap().expr;
    cx.display(r).to_string()
}

#[test]
fn condition_readings_fold() {
    let eng = Engine::standard();
    for (src, want) in [
        // Both polarities of one threshold, spelled two ways.
        (
            "zext<64>(trunc<16>(x) <u 64:16) + zext<64>(64:16 <=u trunc<16>(x))",
            "1:64",
        ),
        (
            "zext<64>((x & 0xffc0) == 0) - zext<64>(trunc<16>(x) <u 64:16)",
            "0:64",
        ),
        (
            "zext<64>(extract<6, 10>(x) == 0:10) + sext<64>(trunc<16>(x) <u 64:16)",
            "0:64",
        ),
        // A select between constants beside its condition.
        (
            "select(trunc<16>(x) <u 64:16, 5:64, 3:64) - zext<64>(x & 0xffc0 == 0) * 2",
            "3:64",
        ),
        // A 16-bit field of `x + k` is the field of `x`, plus `k`, minus its carry.
        (
            "concat(extract<16, 48>(x), trunc<16>(x + 65472)) - x \
             + zext<64>(64:16 <=u trunc<16>(x)) * 65536",
            "65472:64",
        ),
        (
            "((x + 65472) & 65535) + zext<64>(64:16 <=u trunc<16>(x)) * 65536",
            "(x & 65535) + 65472",
        ),
        // The bits an or adds (the core rule `sub_or`).
        ("(x | 0x100050040) - x", "~x & 0x100050040"),
    ] {
        assert_eq!(simplify(&eng, src, 64), want, "{src}");
    }
    // Each spelling of `trunc<16>(x) <u 64` (or of its negation) meets the plain one.
    let below = "zext<64>(trunc<16>(x) <u 64:16)";
    for (spelling, negated) in [
        ("trunc<16>(x) <=u 63:16", false),
        ("(x & 0xffc0) == 0", false),
        ("extract<6, 10>(x) == 0:10", false),
        ("(x & 0xffff) <u 64", false),
        ("~(64:16 <=u trunc<16>(x))", false),
        ("63:16 <u trunc<16>(x)", true),
        ("64:16 <=u trunc<16>(x)", true),
        ("(x & 0xffc0) != 0", true),
        ("~(trunc<16>(x) <u 64:16)", true),
    ] {
        let (op, want) = if negated {
            ("+", "1:64")
        } else {
            ("-", "0:64")
        };
        let src = format!("zext<64>({spelling}) {op} {below}");
        assert_eq!(simplify(&eng, &src, 64), want, "{src}");
    }
    // `sub ax, 64` merged into the register, and a constant chosen by its borrow: under the
    // mask the borrow's own bit (2^33) is not read. (The standard strategy leaves the two
    // disjoint fields of `x` it reads as `~(x & 0x1ffff0000) - (x & 65535)`.)
    let deobfuscate = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let borrow = "(select((x & 0xffc0) == 0, 0xffbf, 0x1ffffffbf) \
                  - (((x + 0xffc0) & 0xffff) | (x & 0x1ffff0000))) & 0x100050040";
    assert_eq!(simplify(&deobfuscate, borrow, 64), "~x & 0x100050040");
    // One reading alone stays: a `zext` built for a lone select would not be smaller.
    let lone = "select(trunc<16>(x) <u 64:16, 5:64, 3:64) + x";
    assert_eq!(
        simplify(&eng, lone, 64),
        "select(trunc<16>(x) <u 64, 5:64, 3) + x"
    );
    // Different thresholds do not meet.
    let apart = "zext<64>(trunc<16>(x) <u 64:16) + zext<64>(65:16 <=u trunc<16>(x))";
    assert_eq!(
        simplify(&eng, apart, 64),
        "let %0 = trunc<16>(x);\nzext<64>(%0 <u 64) + zext<64>(65 <=u %0)"
    );
}

/// z3 and bitwuzla prove the results at 64 bits equivalent to their inputs. A timeout or
/// `unknown` is inconclusive and counted; `sat` is a counterexample. Skipped, with a note, when
/// the solver is not on `PATH`.
#[cfg(feature = "smtlib")]
fn solver_proves(solver: common::Solver, size: Size) {
    use bitwright::smtlib::equivalence_query;
    if !solver.available() {
        return;
    }
    let engines = engines();
    let mut rng = Rng(0x64_c4d1);
    let mut queries = Vec::new();
    for _ in 0..size.pick(40, 600) {
        let j = 1 + rng.below(63) as u16;
        let src = random_sum(&mut rng, 64, j);
        let (name, eng) = &engines[rng.below(engines.len() as u64) as usize];
        let mut cx = Context::new();
        let e = parse(&mut cx, &src, 64);
        let r = eng.simplify(&mut cx, e).unwrap();
        if r.changed {
            let q = equivalence_query(&mut cx, e, r.expr).unwrap();
            queries.push((format!("{name}: `{src}` => `{}`", cx.display(r.expr)), q));
        }
    }
    let (mut proved, mut inconclusive) = (0, 0);
    for (case, q) in &queries {
        let out = solver.run(q, Some(2000)).unwrap();
        let answers: Vec<&str> = out.lines().filter(|l| !l.starts_with('(')).collect();
        match answers[..] {
            ["unsat"] => proved += 1,
            ["sat"] => panic!("{} found a counterexample: {case}", solver.name()),
            _ => {
                eprintln!("inconclusive: {case}");
                inconclusive += 1
            }
        }
    }
    eprintln!(
        "{}: {proved} proved, {inconclusive} inconclusive of {}",
        solver.name(),
        queries.len()
    );
    assert!(
        proved * 4 > queries.len() * 3,
        "{proved} of {}",
        queries.len()
    );
}

#[cfg(feature = "smtlib")]
#[test]
fn z3_proves_condition_readings_smoke() {
    solver_proves(common::Solver::Z3, Size::Smoke);
}

#[cfg(feature = "smtlib")]
#[test]
fn bitwuzla_proves_condition_readings_smoke() {
    solver_proves(common::Solver::Bitwuzla, Size::Smoke);
}

#[cfg(feature = "smtlib")]
#[test]
#[ignore = "heavy: run with --release -- --ignored (needs z3 on PATH; skipped without it)"]
fn z3_proves_condition_readings_heavy() {
    solver_proves(common::Solver::Z3, Size::Heavy);
}

#[cfg(feature = "smtlib")]
#[test]
#[ignore = "heavy: run with --release -- --ignored (needs bitwuzla on PATH; skipped without it)"]
fn bitwuzla_proves_condition_readings_heavy() {
    solver_proves(common::Solver::Bitwuzla, Size::Heavy);
}
