//! Ports are useful only if the default strategy actually reaches them.
use bitwright::engine::Engine;
use bitwright::rules::{RuleProgram, builtin_sources};
use bitwright::{Context, ParseOptions, Width};

#[test]
fn standard_strategy_reaches_recovery_rule_examples() {
    let program = RuleProgram::compile(builtin_sources()[0].1).unwrap();
    let engine = Engine::standard();
    let mut checked = 0;
    for rule in program
        .rules()
        .iter()
        .filter(|r| r.name.starts_with("core.recovery_"))
    {
        assert!(
            !rule.examples.is_empty(),
            "{} has no coverage example",
            rule.name
        );
        for (input, reference) in &rule.examples {
            let mut cx = Context::new();
            let options = ParseOptions::width(Width::W8);
            let input = cx.parse(input, &options).unwrap();
            let reference = cx.parse(reference, &options).unwrap();
            let got = engine.simplify(&mut cx, input).unwrap().expr;
            let want = engine.simplify(&mut cx, reference).unwrap().expr;
            assert_eq!(
                got,
                want,
                "{}: got {}, expected {}",
                rule.name,
                cx.display(got),
                cx.display(want)
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 64);
}
