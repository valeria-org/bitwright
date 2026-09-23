//! SMT-LIB import: no panic on any text; what imports exports and imports back to the same
//! function.
#![no_main]

use bitwright::{BitVec, Context, FnEnv, SymbolKey, Width, smtlib};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(src) = std::str::from_utf8(data) else {
        return;
    };
    let mut cx = Context::new();
    let Ok(script) = smtlib::import(&mut cx, src) else {
        return;
    };
    let roots: Vec<_> = script.definitions.iter().map(|&(_, e)| e).collect();
    if roots.is_empty() {
        return;
    }
    let text = smtlib::export(&mut cx, &roots).expect("export");
    let mut other = Context::new();
    let back = smtlib::import(&mut other, &text)
        .unwrap_or_else(|e| panic!("export does not read back: {e}\n{text}"));
    // Each symbol gets its own value when every key survives the round trip; export renames
    // a name it cannot spell, and then symbols are bound by width only.
    let syms = cx.symbols_in(&roots).unwrap();
    let by_key = syms
        .iter()
        .all(|&id| other.find_symbol(cx.symbol_key(id).unwrap()).is_some());
    for seed in [0x9e37_79b9_7f4a_7c15u64, 0x0123_4567_89ab_cdef] {
        let env = FnEnv(|key: &SymbolKey, w: Width| {
            let h = if by_key {
                format!("{key:?}").bytes().fold(seed, |h, c| {
                    (h ^ u64::from(c)).wrapping_mul(0x100_0000_01b3)
                })
            } else {
                seed.wrapping_mul(u64::from(w.bits()))
            };
            Some(BitVec::wrapping_from_limbs(
                w,
                &[
                    h,
                    h.rotate_left(13),
                    h ^ seed,
                    h.rotate_left(29),
                    h,
                    !h,
                    h,
                    seed,
                ],
            ))
        });
        let want = cx.eval(&roots, &env).unwrap();
        let got: Vec<BitVec> = (0..roots.len())
            .map(|k| {
                let e = back.definition(&format!("root{k}")).unwrap();
                other.eval(&[e], &env).unwrap()[0]
            })
            .collect();
        assert_eq!(got, want, "{text}");
    }
});
