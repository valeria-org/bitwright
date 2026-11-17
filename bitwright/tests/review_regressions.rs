//! Regression tests for all solver soundness, performance, Lean import/export, and CoBRA MBA
//! fixes from the full solver review.
#![cfg(all(
    feature = "check",
    feature = "mba",
    feature = "smtlib",
    feature = "eqsat"
))]

mod common;

use bitwright::engine::{Budget, End, Engine, Exhausted, Phase, Run, Strategy};
use bitwright::mba::{
    self, Decided, MOp, MbaAnswer, MbaBudget, MbaConfig, MbaExpr, MbaLimits, MbaSolver, NfOptions,
    NormalFormSolver, Verdict,
};
use bitwright::prove::{
    self, Config as ProveConfig, Incremental, IncrementalAnswer, Limits, Outcome, lean_theorem,
};
use bitwright::rules::RuleProgram;
use bitwright::rules::lean::rule_theorem;
use bitwright::rules::lean_import::to_bwr;
use bitwright::solve::{Answers, CoreItem, Solver, Status};
use bitwright::{BitVec, CmpOp, Context, KnownBits, ParseOptions, Width};

// ---------------------------------------------------------------------------
// Bug S1: `Context::declare_known` honored across `Solver` & `Incremental`
// ---------------------------------------------------------------------------

#[test]
fn bug_s1_solver_honors_declare_known_and_invalidates_on_change() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let x = cx.parse("x", &o).unwrap();
    let y = cx.parse("y", &o).unwrap();
    let x_eq_zero = cx.parse("x == 0", &o).unwrap();
    let taut = cx.parse("y == y", &o).unwrap();

    // Declare bit 0 of `x` = 1 (odd), and bits `0xAA` of `y` = 1.
    let odd = KnownBits::new(BitVec::zero(Width::W32), BitVec::one(Width::W32)).unwrap();
    let mask_y = BitVec::from_u64(Width::W32, 0xAA).unwrap();
    let known_y = KnownBits::new(BitVec::zero(Width::W32), mask_y).unwrap();
    cx.declare_known(x, odd).unwrap();
    cx.declare_known(y, known_y).unwrap();

    let mut solver = Solver::default();
    solver.push();
    solver.assert(&cx, x_eq_zero).unwrap();
    assert_eq!(solver.check(&mut cx).unwrap(), Status::Unsat);
    solver.pop(1).unwrap();

    // Unconstrained symbol `y` must still respect `declared_known` in completed models.
    solver.assert(&cx, taut).unwrap();
    assert_eq!(solver.check(&mut cx).unwrap(), Status::Sat);
    let y_val = solver.value(&mut cx, y).unwrap().unwrap();
    assert_eq!(y_val.to_u64().unwrap() & 0xAA, 0xAA);
    let x_val = solver.value(&mut cx, x).unwrap().unwrap();
    assert_eq!(x_val.to_u64().unwrap() & 1, 1);

    // Withdrawing `odd` on `x` makes `x == 0` satisfiable again on the same `Solver`.
    cx.declare_known(x, KnownBits::unknown(Width::W32)).unwrap();
    solver.assert(&cx, x_eq_zero).unwrap();
    assert_eq!(solver.check(&mut cx).unwrap(), Status::Sat);
    assert_eq!(
        solver.value(&mut cx, x).unwrap().unwrap(),
        BitVec::zero(Width::W32)
    );
}

#[test]
fn bug_s1_shared_answers_distinguish_declared_known_across_contexts() {
    let shared = Answers::new();
    let o = ParseOptions::width(Width::W16);

    // Context 1: `x` is declared odd, so `(x & 1) == 0` is Unsat.
    let mut cx1 = Context::new();
    let x1 = cx1.parse("x", &o).unwrap();
    let even1 = cx1.parse("(x & 1) == 0", &o).unwrap();
    cx1.declare_known(
        x1,
        KnownBits::new(BitVec::zero(Width::W16), BitVec::one(Width::W16)).unwrap(),
    )
    .unwrap();
    let mut s1 = Solver::default().with_answers(shared.clone());
    s1.assert(&cx1, even1).unwrap();
    assert_eq!(s1.check(&mut cx1).unwrap(), Status::Unsat);

    // Context 2: `x` has no `declared_known`, so the same formula `(x & 1) == 0` MUST be Sat.
    let mut cx2 = Context::new();
    let even2 = cx2.parse("(x & 1) == 0", &o).unwrap();
    let mut s2 = Solver::default().with_answers(shared);
    s2.assert(&cx2, even2).unwrap();
    assert_eq!(s2.check(&mut cx2).unwrap(), Status::Sat);
}

#[test]
fn bug_s1_incremental_tracks_dynamic_declare_known_and_withdrawal() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let x = cx.parse("x", &o).unwrap();
    let p = cx.parse("x <u 4", &o).unwrap();

    let mut inc = Incremental::new(1 << 16);
    let lim = Limits::conflicts(10_000);
    assert!(matches!(
        inc.solve(&mut cx, &[p], lim).unwrap(),
        IncrementalAnswer::Sat(_)
    ));

    // Fix bit 4 of `x` to 1 (`x >= 16`), contradicting `x <u 4` without rebuilding the circuit.
    let hi = BitVec::from_u64(Width::W8, 16).unwrap();
    cx.declare_known(x, KnownBits::new(BitVec::zero(Width::W8), hi).unwrap())
        .unwrap();
    assert!(matches!(
        inc.solve(&mut cx, &[p], lim).unwrap(),
        IncrementalAnswer::Unsat(_)
    ));

    // Withdraw declaration: `x <u 4` becomes Sat again.
    cx.declare_known(x, KnownBits::unknown(Width::W8)).unwrap();
    assert!(matches!(
        inc.solve(&mut cx, &[p], lim).unwrap(),
        IncrementalAnswer::Sat(_)
    ));
}

#[test]
fn incremental_unsat_core_minimization_shrinks_redundant_assumptions() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let mut s = Solver::default();
    let base = cx.parse("x * 3 == 9", &o).unwrap();
    s.assert(&cx, base).unwrap();

    // All 16 redundant assumptions mention `x` so they stay in the same slice as `base`.
    let mut assumptions = Vec::new();
    for i in 0..16u32 {
        assumptions.push(cx.parse(&format!("(x ^ y_{i}) != {i}"), &o).unwrap());
    }
    let conflict = cx.parse("x != 3", &o).unwrap();
    assumptions.push(conflict);

    assert_eq!(
        s.check_assuming(&mut cx, &assumptions).unwrap(),
        Status::Unsat
    );
    let core = s.unsat_core(&mut cx).unwrap().unwrap();
    assert!(core.contains(&CoreItem::Assertion(0)));
    assert!(core.contains(&CoreItem::Assumption(16)));
    assert_eq!(
        core.len(),
        2,
        "core should drop all 16 irrelevant assumptions: {core:?}"
    );
}

// ---------------------------------------------------------------------------
// Bug S2: `mba::decide` input validation, `declare_known`, and >256-bit limbs
// ---------------------------------------------------------------------------

#[test]
fn bug_s2_mba_decide_validates_foreign_handles_and_wide_witnesses() {
    let mut cx1 = Context::new();
    let mut cx2 = Context::new();
    let foreign = cx1
        .parse("x + 1", &ParseOptions::width(Width::W32))
        .unwrap();
    let (limits, budget) = (MbaLimits::default(), MbaBudget::default());

    // Passing `foreign == foreign` into `cx2` must error, never `Ok(Decided::Equal)`.
    assert!(mba::decide(&mut cx2, foreign, foreign, &[], &limits, &budget).is_err());

    // 512-bit expressions differing only at bit 320 must find a witness.
    let w512 = Width::new(512).unwrap();
    let o512 = ParseOptions::width(w512);
    let a = cx2.parse("(udiv(x, 1) >>u 320) & 1", &o512).unwrap();
    let b = cx2.parse("0", &o512).unwrap();
    match mba::decide(&mut cx2, a, b, &[], &limits, &budget).unwrap() {
        Decided::Differ(model) => {
            let vals = cx2.eval(&[a, b], &model[..]).unwrap();
            assert_ne!(vals[0], vals[1]);
        }
        other => panic!("expected 512-bit witness, got {other:?}"),
    }

    // Witness respects `declare_known`: `x` declared with bit 0 = 1 must be odd in witness.
    let mut cx3 = Context::new();
    let o32 = ParseOptions::width(Width::W32);
    let x = cx3.parse("x", &o32).unwrap();
    cx3.declare_known(
        x,
        KnownBits::new(BitVec::zero(Width::W32), BitVec::one(Width::W32)).unwrap(),
    )
    .unwrap();
    let lhs = cx3.parse("udiv(x, 3)", &o32).unwrap();
    let rhs = cx3.parse("0x12345678", &o32).unwrap();
    if let Decided::Differ(model) = mba::decide(&mut cx3, lhs, rhs, &[], &limits, &budget).unwrap()
    {
        assert_eq!(model[0].1.to_u64().unwrap() & 1, 1);
    } else {
        panic!("expected witness");
    }
}

// ---------------------------------------------------------------------------
// Bug S3: `SweepNotes` not poisoned when `mba_steps` is budget-starved
// ---------------------------------------------------------------------------

#[test]
fn bug_s3_budget_starved_sweep_does_not_poison_context_sweep_notes() {
    let eng = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    // Opaque constant over non-MBA atom `udiv(x, 7)`: requires opaque sweep certificate.
    let s = "udiv(x, 7)";
    let t = "udiv(y, 11)";
    let opaque = cx
        .parse(
            &format!("(({s} ^ {t}) + 2 * ({s} & {t}) - ({s} + {t}) + 0xdeadbeef) * 3"),
            &o,
        )
        .unwrap();

    // First run: 1 MBA step -> starved!
    let starved = eng
        .run(
            &mut cx,
            &[opaque],
            Run::default().with_per_call(Budget::UNLIMITED.with_mba_steps(1)),
        )
        .unwrap();
    assert!(matches!(
        starved.roots[0].end,
        End::BudgetTerminated(Exhausted::MbaSteps) | End::Completed
    ));

    // Second run on the SAME `Context` with full budget must fold to the constant!
    let full = eng.run(&mut cx, &[opaque], Run::default()).unwrap();
    let want = cx
        .parse(&format!("{}", 0xdeadbeefu64.wrapping_mul(3)), &o)
        .unwrap();
    assert_eq!(full.roots[0].expr, want);
}

// ---------------------------------------------------------------------------
// Bug S4 & S5: Empty-clause DRUP certificate & >64-bit `sums.rs` overflow check
// ---------------------------------------------------------------------------

#[test]
fn bug_s4_s9d_unit_contradiction_certificate_verifies() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let x = cx.parse("x", &o).unwrap();
    // Hardwire `x` to 5 via `declare_known`, then ask if `x == 5` is valid with a certificate
    // (unit clauses alone derive the contradiction at decision level 0).
    let five = BitVec::from_u64(Width::W8, 5).unwrap();
    cx.declare_known(x, KnownBits::constant(&five)).unwrap();
    let eq = cx.parse("x == 5", &o).unwrap();
    let cfg = ProveConfig::default()
        .with_simplify(false)
        .with_samples(0)
        .with_certificate(true);
    match prove::valid(&mut cx, eq, &cfg).unwrap() {
        Outcome::Proved(Some(cert)) => assert!(cert.check().is_ok()),
        other => panic!("expected verified DRUP certificate, got {other:?}"),
    }
}

#[test]
fn bug_s5_shared_sums_does_not_truncate_wide_constants_to_low_limb() {
    let mut cx = Context::new();
    let w128 = Width::new(128).unwrap();
    let w64 = Width::W64;
    let a = cx.symbol("a", w64).unwrap();
    let b = cx.symbol("b", w64).unwrap();
    let sum64 = cx.bin(bitwright::BinOp::Add, a, b).unwrap();
    let zsum = cx.zext(sum64, w128).unwrap();

    // `c = (1 << 64) + 5`: low 64-bit limb is `5`, high limb is `1`.
    // `c <u zext<128>(a + b)` is FALSE for ALL 64-bit `a, b` because `zext<128>(a + b) < 2^64 < c`!
    let c = BitVec::wrapping_from_limbs(w128, &[5, 1, 0, 0, 0, 0, 0, 0]);
    let c_expr = cx.constant(&c).unwrap();
    let claim = cx.cmp(CmpOp::Ult, c_expr, zsum).unwrap();

    let cfg = ProveConfig::default()
        .with_simplify(false)
        .with_samples(0)
        .with_shared_sums(true);
    match prove::valid(&mut cx, claim, &cfg).unwrap() {
        Outcome::Refuted(_) => {}
        other => panic!("wide constant truncated to low limb! got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Bug S6, S7, S8: RuleId separation, Lean export/import, FFma order
// ---------------------------------------------------------------------------

#[test]
fn bug_s6_rule_id_separates_guard_from_trailing_let() {
    let p1 = RuleProgram::compile(
        "bitwright 1;\ngroup g { rule r<W>(x: W, c: const W) { x + c => x if c == 0 } }\n",
    )
    .unwrap();
    let p2 = RuleProgram::compile(
        "bitwright 1;\ngroup g { rule r<W>(x: W, c: const W) where 0 < W { x + c => x } }\n",
    )
    .unwrap();
    let p3 = RuleProgram::compile(
        "bitwright 1;\ngroup g { rule r<W>(x: W, c: const W) { (x + c) + 0 => x let k: 1 = c == 0 } }\n",
    )
    .unwrap();
    let p4 = RuleProgram::compile(
        "bitwright 1;\ngroup g { rule r<W>(x: W, c: const W) { (x + c) + 0 => x if c == 0 } }\n",
    )
    .unwrap();
    assert_ne!(p1.rules()[0].id, p2.rules()[0].id);
    assert_ne!(p3.rules()[0].id, p4.rules()[0].id);
}

#[test]
fn bug_s7_lean_export_and_import_soundness() {
    // 1. `lean_import` rejects non-SMT `/` (Lean `/` on 0 is 0, whereas SMT `udiv` on 0 is all-ones),
    //    supports `.smtUDiv`, `<`, right-associative `∧`, `.truncate`, and wraps `256#8` mod 2^8.
    let lean_src = "
        theorem bad_div {w : Nat} (x y : BitVec w) : x / y = x := by sorry_free
        theorem good_div {w : Nat} (x y : BitVec w) : x.smtUDiv 1#w = x := by sorry_free
        theorem conj_lt {w : Nat} (x y : BitVec w) (h : x < y ∧ y != 0#w) :
            (x &&& y) = (x &&& y) := by sorry_free
        theorem wrapped (x : BitVec 8) : x + 256#8 = x := by sorry_free
    ";
    let bwr = to_bwr(lean_src);
    assert!(bwr.contains("bad_div: not translated"), "{bwr}");
    assert!(bwr.contains("udiv(x, 1) => x"), "{bwr}");
    assert!(bwr.contains("proves(x <u y) && proves(y != 0)"), "{bwr}");
    assert!(bwr.contains("x + 0 => x"), "{bwr}");

    // 2. `prove::lean_theorem` includes `declared_known` hypotheses!
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let x = cx.parse("x", &o).unwrap();
    cx.declare_known(
        x,
        KnownBits::new(BitVec::zero(Width::W8), BitVec::one(Width::W8)).unwrap(),
    )
    .unwrap();
    let pred = cx.parse("(x & 1) == 0", &o).unwrap();
    let thm = lean_theorem(&mut cx, "lemma", &[pred], "test").unwrap();
    assert!(thm.contains("theorem «lemma»"), "{thm}");
    assert!(thm.contains("h_known_"), "{thm}");

    // 3. `rules::lean::rule_theorem` avoids Nat truncating subtraction on negative width terms.
    let prog = RuleProgram::compile(
        "bitwright 1;\ngroup g { rule r<W, V>(x: W) where V < W { extract<0, V>(x) + 0 => extract<0, V>(x) } }\n",
    )
    .unwrap();
    let rt = rule_theorem(&prog.rules()[0]);
    assert!(rt.contains("V < W"), "{rt}");
}

#[test]
fn bug_s8_ffma_first_two_operands_commute_in_termination_order() {
    // `fp.fma.rne.f32(~a, b, c) => fp.fma.rne.f32(a, ~b, c)` loops with `(a := ~b, b := ~a)`
    // because `FFma` commutes in its first two multiplicands!
    let looping = RuleProgram::compile(
        "bitwright 1;\ngroup g { #[float_values] identity fma_swap(a: 32, b: 32, c: 32) { fp.fma.rne.f32(~a, b, c) <=> fp.fma.rne.f32(a, ~b, c) } }\n",
    )
    .unwrap();
    assert!(
        !looping.rules()[0].is_directed(),
        "commuting FFma swap must NOT be oriented as a terminating directed rewrite"
    );
}

// ---------------------------------------------------------------------------
// Bugs M1–M4 & CoBRA Change-of-Basis MBA Solver
// ---------------------------------------------------------------------------

fn verify_mba_simplifies_to(src: &str, max_nodes: u32, width: Width) {
    let eng = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
        .build()
        .unwrap();
    let o = ParseOptions::width(width);
    let mut cx = Context::new();
    let orig = cx.parse(src, &o).unwrap();
    let out = eng.run(&mut cx, &[orig], Run::default()).unwrap();
    let simp = out.roots[0].expr;
    assert_eq!(
        mba::equal(
            &mut cx,
            orig,
            simp,
            &MbaLimits::default(),
            &MbaBudget::default()
        )
        .unwrap(),
        Verdict::Proved,
        "`{src}` -> `{}` failed exact MBA proof",
        cx.display(simp)
    );
    let nodes = match cx.dag_size(&[simp], u32::MAX).unwrap() {
        bitwright::Bounded::Exact(n) => n,
        other => panic!("{other:?}"),
    };
    assert!(
        nodes <= max_nodes,
        "`{src}` simplified to `{}` ({nodes} nodes), expected <= {max_nodes} nodes",
        cx.display(simp)
    );
}

#[test]
fn bug_m1_halves_width_aware_modulus_at_top_bit() {
    let solver = NormalFormSolver::default();
    let w = Width::W64;
    // Build `(((~x) << 63) & ((~y) << 63)) - (((~(x | y)) << 63))` directly in `MbaExpr` so
    // `Pass::halves` is exercised directly without engine shift rules pre-folding it.
    let mut m = MbaExpr::new(vec![w, w]);
    let x = m.push(MOp::Var(0), &[]).unwrap();
    let y = m.push(MOp::Var(1), &[]).unwrap();
    let nx = m.push(MOp::Not, &[x]).unwrap();
    let ny = m.push(MOp::Not, &[y]).unwrap();
    let s_nx = m.push(MOp::Shl(63), &[nx]).unwrap();
    let s_ny = m.push(MOp::Shl(63), &[ny]).unwrap();
    let lhs = m.push(MOp::And, &[s_nx, s_ny]).unwrap();
    let x_or_y = m.push(MOp::Or, &[x, y]).unwrap();
    let n_or = m.push(MOp::Not, &[x_or_y]).unwrap();
    let rhs = m.push(MOp::Shl(63), &[n_or]).unwrap();
    let _diff = m.push(MOp::Sub, &[lhs, rhs]).unwrap();

    match solver.solve(&m, &MbaBudget::default()) {
        MbaAnswer::Simplified { expr, .. } => {
            assert_eq!(expr.nodes().len(), 1);
            assert_eq!(expr.nodes()[0].op, MOp::Const(BitVec::zero(w)));
        }
        other => panic!("expected 0 via Pass::halves at shift 63, got {other:?}"),
    }
}

#[test]
fn bug_m2_cancelled_derived_constant_refines_bit_classes() {
    // Neither `0x0f` nor `0xf0` appears directly under `&`: both arise from MBA cancellation
    // inside `+`, then enter `& z`. Dynamic class refinement splits `[0xff]` -> `[0x0f, 0xf0]`
    // and collapses `(0x0f & z) + (0xf0 & z)` to `z`!
    let solver = NormalFormSolver::default();
    let w = Width::W8;
    let mut cx = Context::new();
    let o = ParseOptions::width(w);
    let e = cx
        .parse(
            "((((x ^ y) + 2 * (x & y) - x - y + 0x0f) & z) + (((x | y) + (x & y) - x - y + 0xf0) & z))",
            &o,
        )
        .unwrap();
    let (m, _) = mba::lower(&cx, e, &MbaLimits::default()).unwrap();
    match solver.solve(&m, &MbaBudget::default()) {
        MbaAnswer::Simplified { expr, .. } => {
            assert_eq!(
                expr.nodes().len(),
                1,
                "expected single variable `z`, got {expr:?}"
            );
        }
        other => panic!("expected simplification to `z`, got {other:?}"),
    }
}

#[test]
fn bug_m4_solve_counted_never_exceeds_step_budget() {
    let solver = NormalFormSolver::new(NfOptions::default());
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let e = cx
        .parse(
            "5 * ((x + y) - 2 * (x & y)) + 7 * ((x + z) - (x & z)) + 3 * ((y + z) - (y | z))",
            &o,
        )
        .unwrap();
    let (m, _) = mba::lower(&cx, e, &MbaLimits::default()).unwrap();
    for steps in (50..=2500).step_by(37) {
        let budget = MbaBudget::default().with_steps(steps);
        let (_, spent) = solver.solve_counted(&m, &budget);
        assert!(
            spent <= steps,
            "solve_counted spent {spent} > budget {steps}"
        );
    }
}

#[test]
fn cobra_multi_term_arbitrary_coefficients_and_degree1_cancellation() {
    // 1. 3-term overlapping arbitrary coefficients: `5*(x ^ y) + 3*(y & z) + 7*(x | z)`
    //    expanded into obfuscated MBA identities.
    verify_mba_simplifies_to(
        "5 * ((x | y) - (x & y)) + 3 * ((y + z) - (y | z)) + 7 * ((x ^ z) + (x & z))",
        14,
        Width::W64,
    );

    // 2. Degree-1 cancellation trap: `5*(x ^ y) + 7*(x | z) - 5*(y | z)`
    //    (`y` has net degree-1 conjunction coefficient `5 - 5 = 0`, which breaks naive greedy!).
    verify_mba_simplifies_to(
        "12 * x + 2 * z - 10 * (x & y) - 7 * (x & z) + 5 * (y & z)",
        14,
        Width::W64,
    );

    // 3. 4-variable 4-term MBA with 3-input XOR (`x ^ y ^ z`), OR, negated AND, and 2-input XOR:
    //    `13 * (x ^ y ^ z) - 9 * (w | x) + 5 * (y & ~z) + 3 * (w ^ z)` expanded into conjunctions!
    verify_mba_simplifies_to(
        "4 * x + 18 * y + 16 * z - 6 * w \
         - 26 * (x & y) - 26 * (x & z) - 31 * (y & z) \
         + 9 * (w & x) - 6 * (w & z) + 52 * (x & y & z)",
        22,
        Width::W64,
    );
}

#[test]
fn cobra_masked_semilinear_multi_term_mba() {
    // Semi-linear masked MBA: `5 * ((x ^ y) & 0xff) + 3 * ((x | z) & 0xff)` written in expanded
    // masked conjunctions `8*(x & 0xff) + 5*(y & 0xff) + 3*(z & 0xff) - 10*(x & y & 0xff) - 3*(x & z & 0xff)`.
    verify_mba_simplifies_to(
        "8 * (x & 0xff) + 5 * (y & 0xff) + 3 * (z & 0xff) \
         - 10 * (x & y & 0xff) - 3 * (x & z & 0xff)",
        16,
        Width::W64,
    );

    // Masked complement constant trading: `5 * 0xff - 5 * (x & 0xff)` -> `5 * (~x & 0xff)`!
    verify_mba_simplifies_to("1275 - 5 * (x & 0xff)", 7, Width::W64);
}

#[test]
fn cobra_lazy_lin_prevents_intermediate_max_terms_atomization() {
    // Construct an 11-variable MBA (`2^11 = 2048 > max_terms = 1024`!) where `(x0 ^ ... ^ x10)`
    // alone has 2047 conjunction monomials (which previously hit `p.len() > max_terms` and
    // atomized!), then subtract `((x0 ^ ... ^ x10) ^ x0) + ...` or cancel two obfuscated copies:
    // `3 * (x0 ^ x1 ^ ... ^ x9 ^ x10) - 3 * ((x0 ^ x1) ^ (x2 ^ ... ^ x10)) + (x0 ^ x1)` -> `x0 ^ x1`!
    // Use 10 variables (`2^10 - 1 = 1023` terms) scaled and shifted with a second 10-var Boolean
    // function whose intermediate sum has >1024 terms under `max_terms = 64`!
    let opts = NfOptions::default().with_max_terms(64);
    let solver = NormalFormSolver::new(opts);
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    // `B1 = x0 ^ x1 ^ x2 ^ x3 ^ x4 ^ x5 ^ x6` (127 monomials > 64!)
    // `B2 = (x0 ^ x1) ^ (x2 ^ x3 ^ x4 ^ x5 ^ x6)` (also 127 monomials > 64!)
    // `7 * B1 - 7 * B2 + ((x0 | x1) - (x0 & x1))` == `x0 ^ x1` (only 3 monomials after cancellation!).
    let e = cx
        .parse(
            "7 * (x0 ^ x1 ^ x2 ^ x3 ^ x4 ^ x5 ^ x6) \
             - 7 * ((x0 + x1 - 2 * (x0 & x1)) ^ x2 ^ x3 ^ x4 ^ x5 ^ x6) \
             + ((x0 | x1) - (x0 & x1))",
            &o,
        )
        .unwrap();
    let (m, _) = mba::lower(&cx, e, &MbaLimits::default()).unwrap();
    match solver.solve(&m, &MbaBudget::default()) {
        MbaAnswer::Simplified { expr, .. } => {
            assert!(
                expr.nodes().len() <= 3,
                "expected `x0 ^ x1` (3 nodes) even under max_terms=64, got {} nodes: {expr:?}",
                expr.nodes().len()
            );
        }
        other => panic!("expected simplification without max_terms atomization, got {other:?}"),
    }
}

#[test]
fn bug_m3_parent_cancels_previously_kept_sub_mbas() {
    // Ensure `Phase::Mba` simplifies `core_a - core_b` to `0` even when `core_a` alone has no
    // simpler form and was visited earlier in the same context/engine!
    let eng = Engine::builder()
        .builtin()
        .strategy(Strategy::new(
            "mba_only",
            vec![Phase::Mba(MbaConfig::default())],
        ))
        .build()
        .unwrap();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    let core_a = cx
        .parse("5 * (x ^ y) + 3 * (y & z) + 7 * (x | z)", &o)
        .unwrap();
    let core_b = cx
        .parse(
            "5 * ((x | y) - (x & y)) + 3 * (y & z) + 7 * ((x ^ z) + (x & z))",
            &o,
        )
        .unwrap();
    let diff = cx.bin(bitwright::BinOp::Sub, core_a, core_b).unwrap();
    let out = eng.run(&mut cx, &[core_a, diff], Run::default()).unwrap();
    let zero = cx.parse("0", &o).unwrap();
    assert_eq!(out.roots[1].expr, zero);
}

// ---------------------------------------------------------------------------
// Review follow-ups: Lean `∧` as a value, `toNat` arithmetic, deferred linear-MBA links
// ---------------------------------------------------------------------------

#[test]
fn lean_import_conjunction_as_a_value_compiles() {
    // In an `if` condition `∧` is a 1-bit value: the guard's `&&` does not compile there.
    let bwr = to_bwr(
        "theorem ite_conj {w : Nat} (x y : BitVec w) :
            (if x < y ∧ y != 0#w then x else x) = x := by sorry_free",
    );
    assert!(!bwr.contains("not translated"), "{bwr}");
    assert!(bwr.contains("((x <u y) & (y != 0))"), "{bwr}");
    RuleProgram::compile(&bwr).unwrap_or_else(|e| panic!("{e:?}\n{bwr}"));
}

#[test]
fn lean_import_reads_to_nat_only_where_it_does_not_wrap() {
    let bwr = to_bwr(
        "theorem nat_sum {w : Nat} (x y : BitVec w) (h : x.toNat + 1 < y.toNat) :
            x + 0#w = x := by sorry_free
        theorem nat_lt {w : Nat} (x y : BitVec w) (h : x.toNat < y.toNat) :
            x + 0#w = x := by sorry_free
        theorem nat_big (x : BitVec 8) (h : x.toNat < 300) : x + 0#8 = x := by sorry_free
        theorem nat_bound {w : Nat} (x : BitVec w) (h : x.toNat < 300) :
            x + 0#w = x := by sorry_free",
    );
    // `Nat` addition does not wrap: `x.toNat + 1 < y.toNat` is not `x + 1 <u y`.
    assert!(bwr.contains("nat_sum: not translated"), "{bwr}");
    // A comparison of two `toNat`s is the unsigned one.
    assert!(bwr.contains("proves(x <u y)"), "{bwr}");
    // 300 is no 8-bit value: `x <u 300` at 8 bits would be `x <u 44`.
    assert!(bwr.contains("nat_big: not translated"), "{bwr}");
    // At a width variable the literal bounds it instead: 300 needs 9 bits.
    assert!(
        bwr.contains("rule nat_bound<W>(x: W) where W >= 9"),
        "{bwr}"
    );
}

#[test]
fn linear_mba_link_left_to_a_declining_chain_top_is_solved() {
    // `(x & y) + (x | y)` is `x + y`. It leaves its solve to the sum above it, a fitting
    // linear-MBA region whose own form is no smaller (the bitwise term is cheaper as written):
    // that one declines, and the link is solved after all.
    let o = ParseOptions::width(Width::W64);
    for whole in [true, false] {
        let engine = Engine::builder()
            .builtin()
            .strategy(Strategy::new("t", vec![Phase::LinearMba]).with_whole_first(whole))
            .build()
            .unwrap();
        for src in [
            "((x & y) + (x | y)) + (a ^ b ^ c ^ d)",
            "((x & y) + (x | y)) + ((a & b & c) | (~a & d) | (b ^ c))",
            "(((x & y) + (x | y)) + z) - (((a & ~b) | (c ^ d)) & (a | b | e))",
        ] {
            let mut cx = Context::new();
            let e = cx.parse(src, &o).unwrap();
            let out = engine.simplify(&mut cx, e).unwrap().expr;
            let shown = cx.display(out).to_string();
            assert!(
                !shown.contains("x & y") && !shown.contains("x | y"),
                "whole_first={whole}: `{src}` -> `{shown}`"
            );
            assert_eq!(
                mba::equal(
                    &mut cx,
                    e,
                    out,
                    &MbaLimits::default(),
                    &MbaBudget::default()
                )
                .unwrap(),
                Verdict::Proved,
                "`{src}` -> `{shown}`"
            );
        }
    }
}

#[test]
fn lean_import_concat_associates_left_with_addition() {
    // Lean's `++` and `+` are both `infixl:65`: `a ++ b + c` is `(a ++ b) + c`.
    let bwr = to_bwr(
        "theorem cat_add (a b : BitVec 4) (c : BitVec 8) :
            a ++ b + c = c + (a ++ b) := by sorry_free",
    );
    assert!(
        bwr.contains("concat(a, b) + c => c + concat(a, b)"),
        "{bwr}"
    );
}

#[test]
fn lean_import_rejects_literals_past_128_bits() {
    // 2^128 is 0 modulo 2^8: never all ones (what an unparsed literal used to read as).
    let bwr = to_bwr(
        "theorem huge (x : BitVec 8) :
            x + 340282366920938463463374607431768211456#8 = x := by sorry_free
        theorem wrapped (x : BitVec 8) : x + 300#8 = x + 44#8 := by sorry_free",
    );
    assert!(bwr.contains("huge: not translated"), "{bwr}");
    assert!(!bwr.contains("255"), "{bwr}");
    assert!(
        bwr.contains("(x + 44) => (x + 44)") || bwr.contains("x + 44 => x + 44"),
        "{bwr}"
    );
}

#[test]
fn lean_theorem_names_hypotheses_apart_from_symbols() {
    // A symbol named `h_known_0` would be shadowed by a hypothesis binder of that name.
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let x = cx.parse("x", &o).unwrap();
    let odd = KnownBits::new(BitVec::zero(Width::W8), BitVec::one(Width::W8)).unwrap();
    cx.declare_known(x, odd).unwrap();
    let pred = cx.parse("(x & 1) == h_known_0", &o).unwrap();
    let thm = lean_theorem(&mut cx, "lemma", &[pred], "test").unwrap();
    assert!(thm.contains("(h_known_0 : BitVec 8)"), "{thm}");
    assert!(thm.contains("(h_known_0' : (x &&& "), "{thm}");
}
