//! Constraints over arbitrary byte-encoded DAGs: no panic; a result equals its input wherever the
//! constraints it relies on hold, and facts under the constraints contain every value those
//! points give (at points derived from the input).
#![no_main]

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::{Assumptions, BitVec, Context, FnEnv, Width};
use libfuzzer_sys::fuzz_target;

mod common;
use common::{Bytes, build, fit};

fuzz_target!(|data: &[u8]| {
    let mut b = Bytes(data);
    let mut cx = Context::new();
    // Up to three predicates, each assumed true or false, then the expression to simplify.
    let mut a = Assumptions::new();
    let mut preds = Vec::new();
    for _ in 0..1 + b.byte() % 3 {
        let Some(e) = build(&mut cx, &mut b) else {
            return;
        };
        let p = fit(&mut cx, e, Width::W1);
        let holds = b.byte() % 2 == 0;
        let id = if holds {
            a.assume_true(&mut cx, p).unwrap()
        } else {
            a.assume_false(&mut cx, p).unwrap()
        };
        preds.push((id, p, holds));
    }
    let Some(e) = build(&mut cx, &mut b) else {
        return;
    };
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::standard())
        .build()
        .unwrap();
    let run = Run::default().with_assumptions(&a).with_per_call(
        Budget::default()
            .with_node_visits(1 << 16)
            .with_pass_work(1 << 18),
    );
    let out = engine.run(&mut cx, &[e], run).unwrap();
    let r = out.roots[0];
    assert_eq!(cx.width(r.expr).unwrap(), cx.width(e).unwrap());
    if !r.changed {
        assert!(r.relies_on.is_none());
    }
    let facts = cx.facts_with(e, &a).unwrap();
    for k in 0..64u64 {
        let env = FnEnv(|key: &bitwright::SymbolKey, w| {
            let h = format!("{key:?}")
                .bytes()
                .fold(k, |h, c| (h ^ u64::from(c)).wrapping_mul(0x100_0000_01b3));
            let pick = [0, !0, 1, h, h >> 7, 1 << (h % 64), h % 16];
            Some(BitVec::wrapping_from_limbs(
                w,
                &[pick[(k % 7) as usize], h.rotate_left(17)],
            ))
        });
        let mut all = true;
        let mut relied = true;
        for &(id, p, holds) in &preds {
            let v = cx.eval(&[p], &env).unwrap()[0];
            let ok = v.is_zero() != holds;
            all &= ok;
            relied &= ok || !r.relies_on.may_use(id);
        }
        let (x, z) = (
            cx.eval(&[e], &env).unwrap(),
            cx.eval(&[r.expr], &env).unwrap(),
        );
        if relied {
            assert_eq!(
                x,
                z,
                "{} became {} relying on {:?}",
                cx.display(e),
                cx.display(r.expr),
                r.relies_on
            );
        }
        if all {
            assert!(
                !a.is_infeasible(),
                "a satisfying point, but called infeasible"
            );
            let f = facts.expect("feasible");
            assert!(
                f.contains(&x[0]),
                "{} = {} not in {f:?}",
                cx.display(e),
                x[0]
            );
        }
    }
});
