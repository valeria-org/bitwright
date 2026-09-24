//! Read id/width/input/reference TSV; report built-in coverage, never assume it.
use std::io::{self, BufRead};

use bitwright::engine::{Engine, Strategy};
use bitwright::{BitVec, Context, FnEnv, ParseOptions, SymbolKey, Width};

fn main() {
    let strategy = if std::env::args().any(|a| a == "--deobfuscate") {
        Strategy::deobfuscate()
    } else {
        Strategy::standard()
    };
    let engine = Engine::builder()
        .builtin()
        .strategy(strategy)
        .build()
        .unwrap();
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        let fields: Vec<_> = line.split('\t').collect();
        if fields.len() != 4 {
            panic!("expected id/width/input/reference");
        }
        let mut cx = Context::new();
        let options = ParseOptions::width(Width::new(fields[1].parse().unwrap()).unwrap());
        let result = (|| -> Result<_, Box<dyn std::error::Error>> {
            let input = cx.parse(fields[2], &options)?;
            let reference = cx.parse(fields[3], &options)?;
            let before = cx.tree_size(input)?;
            // Refute mistranslated/invalid corpus instances before treating them
            // as coverage gaps. Passing samples is not proof of a new rule.
            for seed in 0..32_u64 {
                let env = FnEnv(|key: &SymbolKey, width: Width| {
                    let hash = format!("{key:?}")
                        .bytes()
                        .fold(seed.wrapping_mul(0x9e3779b97f4a7c15), |state, byte| {
                            state.wrapping_mul(0x100000001b3) ^ u64::from(byte)
                        });
                    Some(match seed {
                        0 => BitVec::zero(width),
                        1 => BitVec::ones(width),
                        _ => BitVec::wrapping_from_limbs(width, &[hash]),
                    })
                });
                let values = cx.eval(&[input, reference], &env)?;
                if values[0] != values[1] {
                    return Ok((
                        "invalid-reference",
                        before,
                        before,
                        cx.tree_size(reference)?,
                        cx.display(input).to_string().replace(['\n', '\t'], " "),
                        cx.display(reference).to_string().replace(['\n', '\t'], " "),
                    ));
                }
            }
            let output = engine.simplify(&mut cx, input)?.expr;
            let want = engine.simplify(&mut cx, reference)?.expr;
            let after = cx.tree_size(output)?;
            let target = cx.tree_size(want)?;
            let status = if output == want {
                "covered"
            } else if after > target {
                "gap"
            } else {
                "different-form"
            };
            Ok((
                status,
                before,
                after,
                target,
                cx.display(output).to_string().replace(['\n', '\t'], " "),
                cx.display(want).to_string().replace(['\n', '\t'], " "),
            ))
        })();
        match result {
            Ok((status, before, after, target, output, want)) => println!(
                "{}\t{}\t{status}\t{before}\t{after}\t{target}\t{output}\t{want}",
                fields[0], fields[1]
            ),
            Err(error) => println!(
                "{}\t{}\terror\t{}",
                fields[0],
                fields[1],
                error.to_string().replace(['\n', '\t'], " ")
            ),
        }
    }
}
