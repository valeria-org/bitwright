//! The prover on arbitrary byte-encoded claims, against itself: no panic; a counterexample
//! falsifies the claim when evaluated; a proved claim holds at sampled points and its
//! certificate, when asked for, checks; and the word-level path (the simplifier first), the
//! bit-level path (blasting alone) and the certified path never disagree on a verdict.
#![no_main]

use bitwright::prove::{self, Config, Outcome};
use bitwright::{BitVec, CmpOp, Context, Expr, FnEnv, Width};
use libfuzzer_sys::fuzz_target;

mod common;
use common::{Bytes, build, fit};

/// The claim at 16 points derived from the symbols' names: whether it held at each.
fn holds_at_samples(cx: &mut Context, p: Expr) -> bool {
    (0..16u64).all(|k| {
        let env = FnEnv(|key: &bitwright::SymbolKey, w| {
            let h = format!("{key:?}")
                .bytes()
                .fold(k, |h, c| (h ^ u64::from(c)).wrapping_mul(0x100_0000_01b3));
            let pick = [0, !0, 1, h, h >> 7, 1 << (h % 64)];
            Some(BitVec::wrapping_from_limbs(
                w,
                &[pick[(k % 6) as usize], h.rotate_left(17)],
            ))
        });
        !cx.eval(&[p], &env).unwrap()[0].is_zero()
    })
}

fuzz_target!(|data: &[u8]| {
    let mut b = Bytes(data);
    let shape = b.byte();
    let mut cx = Context::new();
    let Some(e) = build(&mut cx, &mut b) else {
        return;
    };
    // A claim about the DAG: its low bit, or a comparison with a second DAG over the same
    // symbols (mostly false, sometimes an identity the simplifier or the search must find).
    let p = if shape % 4 == 0 {
        cx.trunc(e, Width::W1).unwrap_or(e)
    } else {
        let Some(f) = build(&mut cx, &mut b) else {
            return;
        };
        let w = cx.width(e).unwrap();
        let f = fit(&mut cx, f, w);
        let op = CmpOp::ALL[usize::from(shape >> 2) % CmpOp::ALL.len()];
        cx.cmp(op, e, f).unwrap()
    };
    let p = fit(&mut cx, p, Width::W1);
    // Small budgets: an undecided claim is not a finding.
    let base = Config::default()
        .with_max_conflicts(2_000)
        .with_max_nodes(50_000)
        .with_simplify_fuel(1 << 14);
    let configs = [
        ("word", base.clone()),
        ("bit", base.clone().with_simplify(false).with_sweeping(false)),
        ("certified", base.clone().with_certificate(true)),
    ];
    let mut verdicts: Vec<(&str, bool)> = Vec::new();
    for (name, cfg) in configs {
        match prove::valid(&mut cx, p, &cfg).unwrap() {
            Outcome::Proved(cert) => {
                assert!(
                    holds_at_samples(&mut cx, p),
                    "{name} proved a claim that fails at a sample: {}",
                    cx.display(p)
                );
                if let Some(cert) = cert {
                    cert.check().unwrap_or_else(|why| {
                        panic!("{name}: certificate rejected ({why}): {}", cx.display(p))
                    });
                }
                verdicts.push((name, true));
            }
            Outcome::Refuted(model) => {
                let at = cx.eval(&[p], model.as_slice()).unwrap();
                assert!(
                    at[0].is_zero(),
                    "{name}: the counterexample satisfies the claim: {}",
                    cx.display(p)
                );
                verdicts.push((name, false));
            }
            _ => {}
        }
    }
    if let Some(&(first, v)) = verdicts.first() {
        for &(name, u) in &verdicts[1..] {
            assert_eq!(v, u, "{first} and {name} disagree on {}", cx.display(p));
        }
    }
});
