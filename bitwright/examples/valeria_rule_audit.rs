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
    let mut invalid = false;
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
            if !agrees(&mut cx, &[input, reference])? {
                return Ok((
                    "invalid-reference",
                    before,
                    before,
                    cx.tree_size(reference)?,
                    cx.display(input).to_string().replace(['\n', '\t'], " "),
                    cx.display(reference).to_string().replace(['\n', '\t'], " "),
                ));
            }
            let output = engine.simplify(&mut cx, input)?.expr;
            let want = engine.simplify(&mut cx, reference)?.expr;
            let after = cx.tree_size(output)?;
            let target = cx.tree_size(want)?;
            let status = if !agrees(&mut cx, &[input, reference, output, want])? {
                "invalid-output"
            } else if output == want {
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
            Ok((status, before, after, target, output, want)) => {
                invalid |= status.starts_with("invalid-");
                println!(
                    "{}\t{}\t{status}\t{before}\t{after}\t{target}\t{output}\t{want}",
                    fields[0], fields[1]
                );
            }
            Err(error) => {
                invalid = true;
                println!(
                    "{}\t{}\terror\t{}",
                    fields[0],
                    fields[1],
                    error.to_string().replace(['\n', '\t'], " ")
                );
            }
        }
    }
    if invalid {
        std::process::exit(1);
    }
}

// Refutation only, not a proof: exercise every limb, including bits above 64.
fn agrees(cx: &mut Context, roots: &[bitwright::Expr]) -> Result<bool, bitwright::Error> {
    for seed in 0..32_u64 {
        let env = FnEnv(|key: &SymbolKey, width: Width| {
            let mut state = format!("{key:?}")
                .bytes()
                .fold(seed.wrapping_mul(0x9e3779b97f4a7c15), |state, byte| {
                    state.wrapping_mul(0x100000001b3) ^ u64::from(byte)
                });
            let limbs: Vec<_> = (0..width.bits().div_ceil(64))
                .map(|_| {
                    state = state.wrapping_add(0x9e3779b97f4a7c15);
                    let mut value = state;
                    value = (value ^ (value >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
                    value = (value ^ (value >> 27)).wrapping_mul(0x94d049bb133111eb);
                    value ^ (value >> 31)
                })
                .collect();
            Some(match seed {
                0 => BitVec::zero(width),
                1 => BitVec::ones(width),
                _ => BitVec::wrapping_from_limbs(width, &limbs),
            })
        });
        let values = cx.eval(roots, &env)?;
        if values.iter().any(|v| *v != values[0]) {
            return Ok(false);
        }
    }
    Ok(true)
}
