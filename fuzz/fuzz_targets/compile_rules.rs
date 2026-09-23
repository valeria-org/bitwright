//! The rule compiler and the engine's program validation: no panic on any text; a program that
//! compiles links (unproven rules allowed) and its obligations translate and read back.
#![no_main]

use bitwright::engine::Engine;
use bitwright::rules::{Ledger, RuleProgram};
use bitwright::{Context, smtlib};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };
    let Ok(program) = RuleProgram::compile(src) else {
        return;
    };
    for rule in program.rules() {
        let vars = rule.width_vars.len();
        for w in [1u16, 2, 8, 13] {
            let ws = vec![w; vars];
            if rule.admits(&ws) {
                let smt = smtlib::rule_obligation(rule, &ws).expect("admitted obligation");
                smtlib::import(&mut Context::new(), &smt)
                    .unwrap_or_else(|e| panic!("obligation does not read back: {e}\n{smt}"));
            }
        }
    }
    // Linking validates the program (examples included); it may refuse, never panic.
    let _ = Engine::builder()
        .program(program, &Ledger::default())
        .allow_unproven(true)
        .build();
});
