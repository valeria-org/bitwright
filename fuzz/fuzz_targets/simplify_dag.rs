//! The simplifier on arbitrary byte-encoded DAGs: no panic, and every result equals its input
//! (at points derived from the input).
#![no_main]

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::{BitVec, Context, FnEnv};
use libfuzzer_sys::fuzz_target;

mod common;
use common::{Bytes, build};

fuzz_target!(|data: &[u8]| {
    let mut b = Bytes(data);
    let strategy = if b.byte() % 2 == 0 {
        Strategy::standard()
    } else {
        Strategy::deobfuscate()
    };
    let mut cx = Context::new();
    let Some(e) = build(&mut cx, &mut b) else {
        return;
    };
    let engine = Engine::builder()
        .builtin()
        .strategy(strategy)
        .build()
        .unwrap();
    let run = Run::default().with_per_call(
        Budget::default()
            .with_node_visits(1 << 16)
            .with_pass_work(1 << 18),
    );
    let out = engine.run(&mut cx, &[e], run).unwrap();
    let r = out.roots[0].expr;
    assert_eq!(cx.width(r).unwrap(), cx.width(e).unwrap());
    for k in 0..16u64 {
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
        let (a, z) = (cx.eval(&[e], &env).unwrap(), cx.eval(&[r], &env).unwrap());
        assert_eq!(a, z, "{} became {}", cx.display(e), cx.display(r));
    }
});
