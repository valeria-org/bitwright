//! The public configuration API as another crate sees it: every configuration struct is
//! non-exhaustive, so it is built from `Default` (or a constructor) and `with_*` setters. This
//! file only compiles if that works.

use bitwright::engine::{Admission, Budget, Clock, Deadline, Engine, Run, Strategy, Verify};
use bitwright::{Context, ContextConfig, ParseOptions, Width};

struct Never;
impl Clock for Never {
    fn now_ticks(&self) -> u64 {
        0
    }
}

#[test]
fn configurations_are_built_with_setters() {
    let budget = Budget::default()
        .with_node_visits(1 << 16)
        .with_candidates(1 << 16)
        .with_match_steps(1 << 20)
        .with_rewrites(1 << 12)
        .with_new_nodes(1 << 16)
        .with_fact_work(1 << 20)
        .with_pass_work(1 << 20)
        .with_mba_calls(0)
        .with_eqsat_nodes(0)
        .with_eqsat_work(0);
    assert_eq!(budget.node_visits, 1 << 16);
    let admission = Admission::default()
        .with_max_root_height(64)
        .with_max_root_tree_size(1 << 20)
        .with_max_root_dag_size(4096);
    assert_eq!(admission.max_root_dag_size, Some(4096));
    let verify = Verify::default()
        .with_sampled_points(4)
        .with_unproven_points(16)
        .with_tripwire(true)
        .with_termination(true);
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::standard())
        .verify(verify)
        .build()
        .unwrap();
    let clock = Never;
    let deadline = Deadline::new(&clock, u64::MAX).with_check_every(16);
    let mut cx = Context::with_config(ContextConfig::default().with_max_nodes(1 << 20));
    let e = cx
        .parse("(x - 5) + 5", &ParseOptions::width(Width::W32))
        .unwrap();
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run::default()
                .with_per_call(budget)
                .with_admission(admission)
                .with_deadline(deadline),
        )
        .unwrap();
    assert_eq!(cx.display(out.roots[0].expr).to_string(), "x");
}

#[cfg(feature = "check")]
#[test]
fn checker_and_compiler_configurations_are_built_with_setters() {
    use bitwright::check::CheckConfig;
    use bitwright::rules::{CompileLimits, CompileOptions, RuleProgram};
    let check = CheckConfig::default()
        .with_max_exhaustive_width(4)
        .with_max_exhaustive_bits(12)
        .with_sample_widths(vec![8, 64])
        .with_samples(8)
        .with_seed(1);
    assert_eq!(check.sample_widths, vec![8, 64]);
    let opts = CompileOptions::default().with_limits(
        CompileLimits::default()
            .with_max_source(1 << 16)
            .with_max_rules(64)
            .with_max_nodes(1 << 12)
            .with_max_work(1 << 20)
            .with_max_diagnostics(16),
    );
    let program = RuleProgram::compile_with(
        "bitwright 1;\ngroup g {\n    #[allow(BW0407)]\n    rule r<W>(x: W) { x & x => x }\n}\n",
        &opts,
    )
    .unwrap();
    assert!(bitwright::check::check_program(&program, &check)[0].is_sound());
}

#[cfg(feature = "mba")]
#[test]
fn mba_configurations_are_built_with_setters() {
    use bitwright::mba::{MbaBudget, MbaConfig, MbaLimits, MbaTrust};
    let cfg = MbaConfig::default()
        .with_limits(
            MbaLimits::default()
                .with_max_vars(4)
                .with_max_nodes(256)
                .with_max_width(64)
                .with_min_nodes(3),
        )
        .with_trust(
            MbaTrust::default()
                .with_backend_certificates(false)
                .with_sampled(false),
        )
        .with_budget(MbaBudget::default().with_steps(1 << 10));
    assert_eq!(cfg.limits.max_vars, 4);
}

#[cfg(feature = "eqsat")]
#[test]
fn eqsat_configurations_are_built_with_setters() {
    use bitwright::eqsat::{Fragment, SaturateConfig, Saturator, SearchRun, UnsupportedPolicy};
    let cfg = SaturateConfig::default()
        .with_fragment(Fragment::conservative().with_max_width(64))
        .with_iterations(8)
        .with_matches_per_rule_iter(16)
        .with_admission(Admission::default())
        .with_unsupported(UnsupportedPolicy::Decline)
        .with_max_root_nodes(1024);
    let (sat, _) = Saturator::builtin_groups(&["eqsat.distrib"], cfg);
    let mut cx = Context::new();
    let e = cx
        .parse("x * y + x * z", &ParseOptions::width(Width::W32))
        .unwrap();
    let clock = Never;
    let out = sat
        .search(
            &mut cx,
            &[e],
            SearchRun::default()
                .with_per_call(SearchRun::DEFAULT_BUDGET)
                .with_deadline(Deadline::new(&clock, u64::MAX)),
        )
        .unwrap();
    assert!(out.roots[0].candidate.is_some());
}
