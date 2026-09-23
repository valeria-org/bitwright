//! Expressions: random DAGs with shared subterms and mixed widths (through every cast) evaluate
//! like their reference twins, both through the context's evaluator and through the reference
//! applied to the context's own canonical DAG; substitution (simultaneous, of symbols and of
//! interior nodes, bounded and resumed) preserves meaning; the derived constructors and trap
//! guards are exact at boundary values of wide widths.
//!
//! The library's unit tests generate trees (sharing only `x op x`) up to 130 bits with random
//! environments; these DAGs share subterms freely, reach 512 bits, and are evaluated
//! exhaustively at small widths and at boundary environments at wide ones.

mod common;

use bitwright::{BitVec, Context, ContextConfig, Expr, Substitution, SymbolKey, traps};
use bitwright_ref as r;
use common::{
    Canonical, Dag, GenConfig, Rng, SMOKE_WIDTHS, Size, WIDTHS, assert_matches_reference,
    boundary_values, core_values, envs_for, from_ref, ref_bool, test_context, to_ref, w,
};

// ----- random DAGs --------------------------------------------------------------------------

/// Builds a random DAG with a few roots, then checks every node against the reference under
/// `envs`, and the roots' canonical form (evaluated by the reference alone) too.
/// Returns the number of node evaluations checked.
fn check_dag(
    cx: &mut Context,
    dag: &Dag,
    roots: &[usize],
    envs: &[Vec<BitVec>],
    what: &str,
) -> usize {
    let root_exprs: Vec<Expr> = roots.iter().map(|&i| dag.expr(i)).collect();
    let canon = Canonical::new(cx, &root_exprs);
    for env in envs {
        assert_matches_reference(cx, dag, env, what);
        let want = dag.eval_ref(env);
        let got = canon.eval(&dag.binding(env), &[]);
        for (k, &i) in roots.iter().enumerate() {
            assert_eq!(
                got[k],
                want[i],
                "{what}: the canonical form `{}` of root {k} disagrees with the reference at {}",
                cx.display(root_exprs[k]),
                dag.show_env(env)
            );
        }
    }
    envs.len() * dag.nodes.len()
}

fn small_dags(size: Size) {
    let dags = size.pick(60, 20_000);
    let max_bits = size.pick(8, 12);
    let mut checked = 0;
    for seed in 0..dags {
        let mut rng = Rng(0x1ea_0000 + seed);
        let mut cx = test_context(ContextConfig::default());
        let cfg = GenConfig::small(&mut rng, 4, 1 + (seed % 5) as u32).with_ext(seed % 3 == 2);
        let mut dag = Dag::new(&mut cx, cfg);
        let roots: Vec<usize> = (0..3)
            .map(|_| {
                let rw = 1 + rng.below(4) as u16;
                dag.random(&mut cx, &mut rng, rw)
            })
            .collect();
        let envs = envs_for(&dag, &mut rng, max_bits, 64);
        checked += check_dag(&mut cx, &dag, &roots, &envs, &format!("seed {seed:#x}"));
    }
    eprintln!("{checked} node evaluations checked");
    assert!(
        checked > dags as usize * 500,
        "only {checked} node evaluations"
    );
}

#[test]
fn small_dags_match_the_reference_smoke() {
    small_dags(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn small_dags_match_the_reference_heavy() {
    small_dags(Size::Heavy);
}

fn wide_dags(size: Size) {
    let dags = size.pick(40, 10_000);
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    let mut checked = 0;
    for seed in 0..dags {
        let mut rng = Rng(0x1ea_8000 + seed);
        let mut cx = test_context(ContextConfig::default());
        let cfg = GenConfig::wide(&mut rng, &widths, 2 + (seed % 4) as u32).with_ext(seed % 3 == 2);
        let mut dag = Dag::new(&mut cx, cfg);
        let roots: Vec<usize> = (0..2)
            .map(|_| {
                let rw = rng.pick(&widths);
                dag.random(&mut cx, &mut rng, rw)
            })
            .collect();
        let envs: Vec<Vec<BitVec>> = (0..size.pick(4, 12))
            .map(|_| dag.boundary_env(&mut rng))
            .collect();
        checked += check_dag(&mut cx, &dag, &roots, &envs, &format!("seed {seed:#x}"));
    }
    eprintln!("{checked} node evaluations checked");
    assert!(
        checked > dags as usize * 40,
        "only {checked} node evaluations"
    );
}

#[test]
fn wide_dags_match_the_reference_smoke() {
    wide_dags(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn wide_dags_match_the_reference_heavy() {
    wide_dags(Size::Heavy);
}

// ----- substitution ---------------------------------------------------------------------------

/// Substitutes a random set of symbols and interior nodes by random expressions (which may
/// mention the replaced symbols: the substitution is simultaneous), and checks the result
/// against the original's canonical DAG evaluated with the replaced nodes' values overridden.
/// `substitute_bounded`, resumed with a small visit limit, must reach the same result.
fn substitution(size: Size, wide: bool) {
    let rounds = size.pick(40, 8000);
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    for seed in 0..rounds {
        let mut rng = Rng(0x5b5_0000 + seed + if wide { 1 << 32 } else { 0 });
        let mut cx = test_context(ContextConfig::default());
        let cfg = if wide {
            GenConfig::wide(&mut rng, &widths, 3)
        } else {
            GenConfig::small(&mut rng, 4, 4)
        }
        .with_ext(seed % 3 == 2);
        let mut dag = Dag::new(&mut cx, cfg);
        let rw = if wide {
            rng.pick(&widths)
        } else {
            1 + rng.below(4) as u16
        };
        let root = dag.random(&mut cx, &mut rng, rw);
        let e = dag.expr(root);
        // Targets: nodes of the canonical DAG (symbols and interior nodes alike).
        let order = cx.post_order(&[e]).unwrap();
        let mut map: Vec<(Expr, Expr)> = Vec::new();
        for _ in 0..1 + rng.below(3) {
            let t = rng.pick(&order);
            if map.iter().any(|(f, _)| *f == t) {
                continue;
            }
            let tw = cx.width(t).unwrap().bits();
            let to = dag.random(&mut cx, &mut rng, tw);
            map.push((t, dag.expr(to)));
        }
        let what = format!(
            "seed {seed:#x}: `{}` with {}",
            cx.display(e),
            map.iter()
                .map(|(f, t)| format!("`{}` := `{}`", cx.display(*f), cx.display(*t)))
                .collect::<Vec<_>>()
                .join(", ")
        );
        let replaced = cx.substitute(&[e], &map).unwrap()[0];
        assert_eq!(cx.width(replaced).unwrap(), cx.width(e).unwrap(), "{what}");

        // Bounded and resumed: the same node.
        let mut sub = Substitution::new();
        for &(f, t) in &map {
            sub.replace(&cx, f, t).unwrap();
        }
        let limit = 1 + rng.below(4);
        let mut calls = 0;
        let bounded = loop {
            calls += 1;
            assert!(
                calls < 100_000,
                "{what}: bounded substitution never finishes"
            );
            if let Some(v) = cx.substitute_bounded(&[e], &mut sub, limit).unwrap() {
                break v[0];
            }
        };
        assert_eq!(bounded, replaced, "{what}: bounded substitution differs");

        let before = Canonical::new(&mut cx, &[e]);
        let after = Canonical::new(&mut cx, &[replaced]);
        let images = Canonical::new(&mut cx, &map.iter().map(|m| m.1).collect::<Vec<_>>());
        let envs = envs_for(&dag, &mut rng, 12, size.pick(8, 24));
        for env in &envs {
            let b = dag.binding(env);
            let values = images.eval(&b, &[]);
            let overrides: Vec<(Expr, r::Bits)> = map.iter().map(|m| m.0).zip(values).collect();
            let want = &before.eval(&b, &overrides)[0];
            let got = &after.eval(&b, &[])[0];
            assert_eq!(got, want, "{what}: at {}", dag.show_env(env));
            let direct = cx.eval(&[replaced], &b[..]).unwrap()[0];
            assert_eq!(
                direct,
                from_ref(want),
                "{what}: eval at {}",
                dag.show_env(env)
            );
        }
    }
}

#[test]
fn substitution_preserves_meaning_smoke() {
    substitution(Size::Smoke, false);
    substitution(Size::Smoke, true);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn substitution_preserves_meaning_heavy() {
    substitution(Size::Heavy, false);
    substitution(Size::Heavy, true);
}

// ----- derived constructors and trap guards -----------------------------------------------------

/// Reference definitions of the derived constructors, written independently of the library's
/// own (which use `ult(a + b, a)`, xor tricks and selects).
fn derived_reference(name: &str, a: &r::Bits, b: &r::Bits) -> Option<r::Bits> {
    use r::{BinOp as B, CmpOp as C, UnOp as U};
    let n = a.width();
    let msb = |x: &r::Bits| x.bit(n - 1);
    let zero = r::Bits::zero(n);
    let ones = r::un(U::Not, &zero).unwrap();
    let smin = r::Bits::from_bools((0..n).map(|i| i == n - 1).collect());
    let smax = r::un(U::Not, &smin).unwrap();
    let sum = r::bin(B::Add, a, b);
    let diff = r::bin(B::Sub, a, b);
    // Carry out of a + b: b > ~a.
    let carry = r::cmp(C::Ult, &r::un(U::Not, a).unwrap(), b);
    let add_ovf = msb(a) == msb(b) && msb(&sum) != msb(a);
    let sub_ovf = msb(a) != msb(b) && msb(&diff) != msb(a);
    let limit = if msb(a) { smin.clone() } else { smax.clone() };
    let pick = |c: bool, t: &r::Bits, f: &r::Bits| if c { t.clone() } else { f.clone() };
    Some(match name {
        "umin" => pick(r::cmp(C::Ule, a, b), a, b),
        "umax" => pick(r::cmp(C::Uge, a, b), a, b),
        "smin" => pick(r::cmp(C::Sle, a, b), a, b),
        "smax" => pick(r::cmp(C::Sge, a, b), a, b),
        "andn" => r::bin(B::And, a, &r::un(U::Not, b).unwrap()),
        "orn" => r::bin(B::Or, a, &r::un(U::Not, b).unwrap()),
        "xnor" => r::un(U::Not, &r::bin(B::Xor, a, b)).unwrap(),
        "abs" => pick(msb(a), &r::un(U::Neg, a).unwrap(), a),
        "add_carry" => ref_bool(carry),
        "sub_borrow" => ref_bool(r::cmp(C::Ult, a, b)),
        "sadd_overflow" => ref_bool(add_ovf),
        "ssub_overflow" => ref_bool(sub_ovf),
        "add_sat_u" => pick(carry, &ones, &sum),
        "sub_sat_u" => pick(r::cmp(C::Ult, a, b), &zero, &diff),
        "add_sat_s" => pick(add_ovf, &limit, &sum),
        "sub_sat_s" => pick(sub_ovf, &limit, &diff),
        "mul_wide_u" if 2 * n <= 512 => r::bin(B::Mul, &r::zext(a, 2 * n), &r::zext(b, 2 * n)),
        "mul_wide_s" if 2 * n <= 512 => r::bin(B::Mul, &r::sext(a, 2 * n), &r::sext(b, 2 * n)),
        "trap_udiv" => ref_bool(*b == zero),
        "trap_sdiv" => ref_bool(*b == zero || (*a == smin && *b == ones)),
        "trap_shift" => ref_bool(r::cmp(C::Uge, b, &r::Bits::from_u128(n, u128::from(n)))),
        _ => return None,
    })
}

type Derived = fn(&mut Context, Expr, Expr) -> Result<Expr, bitwright::Error>;

const DERIVED: [(&str, Derived); 21] = [
    ("umin", Context::umin),
    ("umax", Context::umax),
    ("smin", Context::smin),
    ("smax", Context::smax),
    ("andn", Context::andn),
    ("orn", Context::orn),
    ("xnor", Context::xnor),
    ("abs", |cx, a, _| cx.abs(a)),
    ("add_carry", Context::add_carry),
    ("sub_borrow", Context::sub_borrow),
    ("sadd_overflow", Context::sadd_overflow),
    ("ssub_overflow", Context::ssub_overflow),
    ("add_sat_u", Context::add_sat_u),
    ("sub_sat_u", Context::sub_sat_u),
    ("add_sat_s", Context::add_sat_s),
    ("sub_sat_s", Context::sub_sat_s),
    ("mul_wide_u", Context::mul_wide_u),
    ("mul_wide_s", Context::mul_wide_s),
    ("trap_udiv", traps::udiv),
    ("trap_sdiv", traps::sdiv),
    ("trap_shift", |cx, _, b| traps::shift(cx, b)),
];

fn derived(size: Size) {
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    for n in widths {
        let width = w(n);
        let mut cx = Context::new();
        let x = cx.symbol("x", width).unwrap();
        let y = cx.symbol("y", width).unwrap();
        let mut built = Vec::new();
        for (name, f) in DERIVED {
            match f(&mut cx, x, y) {
                Ok(e) => built.push((name, e)),
                // Only the widening products refuse a width, and only above 256 bits.
                Err(err) => assert!(
                    name.starts_with("mul_wide") && n > 256,
                    "{name} at {n} bits: {err}"
                ),
            }
        }
        let roots: Vec<Expr> = built.iter().map(|b| b.1).collect();
        let vals = size.pick(core_values(width), boundary_values(width));
        for a in &vals {
            for b in &vals {
                let env = [(SymbolKey::from("x"), *a), (SymbolKey::from("y"), *b)];
                let got = cx.eval(&roots, &env[..]).unwrap();
                for ((name, _), g) in built.iter().zip(&got) {
                    let want = derived_reference(name, &to_ref(a), &to_ref(b)).unwrap();
                    assert_eq!(*g, from_ref(&want), "{name}({a}, {b}) at {n} bits");
                }
            }
        }
    }
}

#[test]
fn derived_constructors_and_traps_are_exact_smoke() {
    derived(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn derived_constructors_and_traps_are_exact_heavy() {
    derived(Size::Heavy);
}
