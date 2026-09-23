//! Contracts of extension operations: the defects an independent review found, fixed.

mod common;

use std::sync::Arc;

use bitwright::engine::{Engine, Run};
use bitwright::ext::{ExtOp, ExtSig, ExtTraits, Registry};
use bitwright::{BinOp, BitVec, CmpOpExt, Context, ContextConfig, KnownBits, ParseOptions, Width};
#[cfg(feature = "smtlib")]
use common::Solver;

fn bin(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::apply_bin(op, a, b).unwrap()
}

// ---------------------------------------------------------------------------------------------
// 1. Mixed-width signatures: never exercised by the self-test, or refused outright.

/// `rotl(a: W, n: W8)`: a natural ISA op (x86 `rol r, cl`). Accepts only mixed widths.
struct RotByte;
impl ExtOp for RotByte {
    fn name(&self) -> &str {
        "r.rolb"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, n] if n.bits() == 8 && a.bits() != 8 => Ok(ExtSig::new(&[("r", *a)])),
            _ => Err("a value and an 8-bit count".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let w = args[0].width();
        let n = args[1]
            .zext(w)
            .unwrap_or_else(|_| args[1].trunc(w).unwrap());
        out[0] = bin(BinOp::RotL, &args[0], &n);
    }
}

#[test]
fn an_operation_accepting_only_mixed_widths_registers() {
    let r = Registry::builder().register(RotByte);
    assert!(r.is_ok(), "valid mixed-width op refused: {:?}", r.err());
}

/// Only 256-bit (AVX2-like) operands.
struct Wide256;
impl ExtOp for Wide256 {
    fn name(&self) -> &str {
        "r.w256"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a] if a.bits() == 256 => Ok(ExtSig::new(&[("r", *a)])),
            _ => Err("256 bits".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        out[0] = args[0];
    }
}

#[test]
fn an_operation_accepting_only_256_bits_registers() {
    let r = Registry::builder().register(Wide256);
    assert!(r.is_ok(), "valid 256-bit op refused: {:?}", r.err());
}

/// `f(a: W, c: W1)`: accepted homogeneously only at W = 1, so the self-test never checks
/// its known bits at W > 1, where they are unsound (claims bit 0 of the result is 0).
struct LyingFlagAdd;
impl ExtOp for LyingFlagAdd {
    fn name(&self) -> &str {
        "r.lying"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, c] if c.bits() == 1 => Ok(ExtSig::new(&[("r", *a)])),
            _ => Err("a and a 1-bit c".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let c = args[1].zext(args[0].width()).unwrap_or(args[1]);
        out[0] = bin(BinOp::Add, &args[0], &c);
    }
    fn known_bits(&self, args: &[KnownBits], out: &mut [KnownBits]) {
        let w = args[0].width();
        if w.bits() > 1 {
            // Unsound: claims bit 0 is always 0.
            out[0] = KnownBits::new(BitVec::one(w), BitVec::zero(w)).unwrap();
        }
    }
}

#[test]
fn known_bits_unsound_only_at_mixed_widths_are_refused() {
    match Registry::builder().register(LyingFlagAdd) {
        Err(bitwright::ext::ExtError::Contract(_, why)) => {
            assert!(why.contains("known bits"), "{why}")
        }
        other => panic!("{:?}", other.map(|_| ())),
    }
}

// ---------------------------------------------------------------------------------------------
// 2. `commutative` is trusted, never self-tested.

struct SubClaimedCommutative;
impl ExtOp for SubClaimedCommutative {
    fn name(&self) -> &str {
        "r.sub"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b] if a == b => Ok(ExtSig::new(&[("d", *a)])),
            _ => Err("two of one width".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        out[0] = bin(BinOp::Sub, &args[0], &args[1]);
    }
    fn traits(&self) -> ExtTraits {
        ExtTraits::default().with_commutative(true)
    }
}

#[test]
fn a_false_commutative_claim_is_refused() {
    let r = Registry::builder().register(SubClaimedCommutative);
    match &r {
        Err(bitwright::ext::ExtError::Contract(_, why)) => {
            assert!(why.contains("commutative"), "{why}")
        }
        _ => panic!("registered a false commutative claim"),
    }
    let Ok(b) = r else { return };
    let reg = Arc::new(b.build());
    let id = reg.id("r.sub").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let five = cx.constant_u64(Width::W8, 5).unwrap();
    let three = cx.constant_u64(Width::W8, 3).unwrap();
    let d = cx.ext(id, &[five, three]).unwrap()[0];
    assert_eq!(
        cx.as_const(d).unwrap().and_then(|v| v.to_u64()),
        Some(2),
        "5 - 3 folded wrongly (registration accepted a false commutative claim)"
    );
}

/// Commutative in value at equal widths; output width = first argument's width.
struct MaxW;
impl ExtOp for MaxW {
    fn name(&self) -> &str {
        "r.maxw"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, _] => Ok(ExtSig::new(&[("m", *a)])),
            _ => Err("two".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let w = args[0].width();
        let b = if args[1].width().bits() > w.bits() {
            args[1].extract(0, w).unwrap()
        } else {
            args[1].zext(w).unwrap()
        };
        let lt = BitVec::apply_cmp(CmpOpExt::Ult, &args[0], &b).unwrap();
        out[0] = if lt { b } else { args[0] };
    }
    fn traits(&self) -> ExtTraits {
        ExtTraits::default().with_commutative(true)
    }
}

#[test]
fn commutative_arguments_of_different_widths_keep_their_places() {
    let reg = Arc::new(Registry::builder().register(MaxW).unwrap().build());
    let id = reg.id("r.maxw").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let x = cx.symbol("x", Width::W8).unwrap();
    let y = cx.symbol("y", Width::W16).unwrap();
    // y > x in the canonical order, so the builder swaps them.
    let m = cx.ext(id, &[y, x]).unwrap()[0];
    let w = cx.width(m).unwrap();
    let env = [
        (
            bitwright::SymbolKey::from("x"),
            BitVec::wrapping_from_u64(Width::W8, 1),
        ),
        (
            bitwright::SymbolKey::from("y"),
            BitVec::wrapping_from_u64(Width::W16, 2),
        ),
    ];
    let v = cx.eval(&[m], &env[..]);
    match v {
        Ok(v) => assert_eq!(
            v[0].width(),
            w,
            "eval gave a {}-bit value for a {}-bit node",
            v[0].width().bits(),
            w.bits()
        ),
        Err(e) => panic!("eval failed: {e}"),
    }
}

// ---------------------------------------------------------------------------------------------
// 3. Text: width inference when arguments default and the output width differs.

struct AddFlags;
impl ExtOp for AddFlags {
    fn name(&self) -> &str {
        "r.addf"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b] if a == b => Ok(ExtSig::new(&[("sum", *a), ("cf", Width::W1)])),
            _ => Err("two of one width".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let s = bin(BinOp::Add, &args[0], &args[1]);
        out[1] = BitVec::from_bool(BitVec::apply_cmp(CmpOpExt::Ult, &s, &args[0]).unwrap());
        out[0] = s;
    }
}

#[test]
fn parse_infers_flag_width_with_defaulted_arguments() {
    let reg = Arc::new(Registry::builder().register(AddFlags).unwrap().build());
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let e = cx.parse("@r.addf[1](x, y) ^ 1", &ParseOptions::width(Width::W32));
    assert!(e.is_ok(), "{:?}", e.err());
}

#[test]
fn print_parse_round_trip_in_a_fresh_context() {
    let reg = Arc::new(Registry::builder().register(AddFlags).unwrap().build());
    let mut cx = Context::with_registry(ContextConfig::default(), reg.clone());
    let id = reg.id("r.addf").unwrap();
    let x = cx.symbol("x", Width::W32).unwrap();
    let y = cx.symbol("y", Width::W32).unwrap();
    let f = cx.ext(id, &[x, y]).unwrap()[1];
    let z = cx.symbol("z", Width::W1).unwrap();
    let e = cx.xor(f, z).unwrap();
    let text = cx.display(e).to_string();
    let mut fresh = Context::with_registry(ContextConfig::default(), reg);
    let back = fresh.parse(&text, &ParseOptions::width(Width::W32));
    assert!(back.is_ok(), "`{text}`: {:?}", back.err());
}

/// Signature returns 9 outputs at width 7 (not in the self-test battery).
struct NineAt7;
impl ExtOp for NineAt7 {
    fn name(&self) -> &str {
        "r.nine"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a] if a.bits() == 7 => Ok(ExtSig::new(&[("r", *a); 9])),
            [a] => Ok(ExtSig::new(&[("r", *a)])),
            _ => Err("one".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        for o in out.iter_mut() {
            *o = args[0];
        }
    }
}

#[test]
fn a_failed_parse_of_a_call_leaves_the_context_unchanged() {
    let reg = Arc::new(Registry::builder().register(NineAt7).unwrap().build());
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let before = (cx.len(), cx.symbol_count());
    let r = cx.parse("@r.nine(fresh:7)", &ParseOptions::default());
    assert!(r.is_err());
    assert_eq!(
        (cx.len(), cx.symbol_count()),
        before,
        "a failed parse grew the context"
    );
}

// ---------------------------------------------------------------------------------------------
// 4. Canonical order independent of registration order.

struct Named(&'static str);
impl ExtOp for Named {
    fn name(&self) -> &str {
        self.0
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a] => Ok(ExtSig::new(&[("r", *a)])),
            _ => Err("one".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let k = BitVec::wrapping_from_u64(args[0].width(), self.0.len() as u64);
        out[0] = bin(BinOp::Xor, &args[0], &k);
    }
}

#[test]
fn canonical_order_is_independent_of_registration_order() {
    let show = |first: &'static str, second: &'static str| {
        let reg = Arc::new(
            Registry::builder()
                .register(Named(first))
                .unwrap()
                .register(Named(second))
                .unwrap()
                .build(),
        );
        let mut cx = Context::with_registry(ContextConfig::default(), reg.clone());
        let x = cx.symbol("x", Width::W8).unwrap();
        let a = cx.ext(reg.id("r.aa").unwrap(), &[x]).unwrap()[0];
        let b = cx.ext(reg.id("r.bbb").unwrap(), &[x]).unwrap()[0];
        let s = cx.add(a, b).unwrap();
        cx.display(s).to_string()
    };
    assert_eq!(show("r.aa", "r.bbb"), show("r.bbb", "r.aa"));
}

// ---------------------------------------------------------------------------------------------
// 5. Lexer/parser edge cases must not panic.

#[test]
fn parser_edge_cases_do_not_panic() {
    let reg = Arc::new(Registry::builder().register(AddFlags).unwrap().build());
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let o = ParseOptions::width(Width::W8);
    for s in [
        "@",
        "@r",
        "@r.addf",
        "@r.addf(",
        "@r.addf()",
        "@r.addf[",
        "@r.addf[1",
        "@r.addf[999](x, y)",
        "@r.addf[8](x, y)",
        "@r.addf(x, y, x, y)",
        "@r.addf(x:8, y:16)",
        "@.",
        "@r..addf(x,y)",
        "let t = @r.addf(x, y); t + t",
        "@r.addf(x, y) ++ @r.addf[1](x, y)",
        "@r.addf(@r.addf(x, y), @r.addf[1](x, y))",
        "x @r.addf(x,y)",
        "@é(x)",
    ] {
        let _ = cx.parse(s, &o);
    }
}

#[test]
fn ext_in_let_binding_parses() {
    let reg = Arc::new(Registry::builder().register(AddFlags).unwrap().build());
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let o = ParseOptions::width(Width::W8);
    let r = cx.parse("let t = @r.addf(x, y); t + t", &o);
    assert!(r.is_ok(), "{:?}", r.err());
}

#[test]
fn round_trip_every_output_and_arity() {
    struct Multi;
    impl ExtOp for Multi {
        fn name(&self) -> &str {
            "r.multi"
        }
        fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
            let w = args[0];
            if args.iter().any(|a| *a != w) {
                return Err("one width".into());
            }
            Ok(ExtSig::new(&[("o", w); 8]))
        }
        fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
            for (k, o) in out.iter_mut().enumerate() {
                let mut v = BitVec::wrapping_from_u64(args[0].width(), k as u64);
                for a in args {
                    v = bin(BinOp::Add, &v, a);
                }
                *o = v;
            }
        }
    }
    let reg = Arc::new(Registry::builder().register(Multi).unwrap().build());
    let id = reg.id("r.multi").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let xs: Vec<_> = ["x", "y", "z"]
        .iter()
        .map(|n| cx.symbol(*n, Width::W16).unwrap())
        .collect();
    for arity in 1..=3 {
        let outs = cx.ext(id, &xs[..arity]).unwrap();
        assert_eq!(outs.len(), 8);
        for &o in &outs {
            let t = cx.display(o).to_string();
            assert_eq!(cx.parse(&t, &ParseOptions::default()).unwrap(), o, "{t}");
        }
    }
}

// ---------------------------------------------------------------------------------------------
// 6. Robustness: malicious ops must not panic bitwright.

/// Signature widths depend on a global counter after registration: non-deterministic.
struct Flaky(std::sync::atomic::AtomicU32);
impl ExtOp for Flaky {
    fn name(&self) -> &str {
        "r.flaky"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        let n = self.0.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        match args {
            [a] if n > 100_000 && a.bits() < 512 => {
                Ok(ExtSig::new(&[("r", Width::new(a.bits() + 1).unwrap())]))
            }
            [a] => Ok(ExtSig::new(&[("r", *a)])),
            _ => Err("one".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let w = out[0].width();
        out[0] = if w == args[0].width() {
            args[0]
        } else {
            args[0].zext(w).unwrap()
        };
    }
}

#[test]
fn a_nondeterministic_signature_does_not_panic_downstream() {
    let op = Flaky(std::sync::atomic::AtomicU32::new(0));
    let reg = Arc::new(Registry::builder().register(op).unwrap().build());
    let id = reg.id("r.flaky").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg.clone());
    let x = cx.symbol("x", Width::W8).unwrap();
    let e = cx.ext(id, &[x]).unwrap()[0];
    let one = cx.constant_u64(Width::W8, 1).unwrap();
    let s = cx.add(e, one).unwrap();
    // Flip the signature.
    if let Some(o) = reg.op(id) {
        for _ in 0..100_001 {
            let _ = o.signature(&[Width::W8]);
        }
    }
    let env = [(
        bitwright::SymbolKey::from("x"),
        BitVec::wrapping_from_u64(Width::W8, 1),
    )];
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = cx.eval(&[s], &env[..]);
        let _ = Engine::standard().run(&mut cx, &[s], Run::default());
        let _ = cx.display(s).to_string();
    }));
    assert!(r.is_ok(), "panicked");
}

#[test]
fn commutative_mixed_width_calls_rebuild_at_their_width() {
    let reg = Arc::new(Registry::builder().register(MaxW).unwrap().build());
    let id = reg.id("r.maxw").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let a = cx.symbol("a", Width::W8).unwrap();
    let b = cx.symbol("b", Width::W8).unwrap();
    let y = cx.symbol("y", Width::W16).unwrap();
    // t = (a & b) | (a & ~b): a compound the engine reduces to `a`.
    let nb = cx.not(b).unwrap();
    let l = cx.and(a, b).unwrap();
    let r = cx.and(a, nb).unwrap();
    let t = cx.or(l, r).unwrap();
    let m = cx.ext(id, &[y, t]).unwrap()[0];
    println!("m = {} : {}", cx.display(m), cx.width(m).unwrap().bits());
    let one = cx.constant_u64(cx.width(m).unwrap(), 1).unwrap();
    let s = cx.add(m, one).unwrap();
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        Engine::standard().run(&mut cx, &[s], Run::default())
    }));
    match res {
        Err(_) => panic!("engine panicked"),
        Ok(Err(e)) => panic!("engine error: {e}"),
        Ok(Ok(out)) => {
            let e = out.roots[0].expr;
            println!("-> {} : {}", cx.display(e), cx.width(e).unwrap().bits());
            assert_eq!(cx.width(e).unwrap(), cx.width(s).unwrap());
        }
    }
}

#[test]
fn shared_ext_node_prints_and_parses_back() {
    let reg = Arc::new(Registry::builder().register(AddFlags).unwrap().build());
    let id = reg.id("r.addf").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let x = cx.symbol("x", Width::W32).unwrap();
    let y = cx.symbol("y", Width::W32).unwrap();
    let s = cx.ext(id, &[x, y]).unwrap()[0];
    let mut e = s;
    for _ in 0..6 {
        let t = cx.ext(id, &[e, e]).unwrap()[0];
        e = cx.mul(t, e).unwrap();
    }
    let text = cx.display(e).to_string();
    let back = cx.parse(&text, &ParseOptions::default());
    assert_eq!(back.ok(), Some(e), "{text}");
}

#[cfg(feature = "smtlib")]
#[test]
fn smtlib_export_import_with_uninterpreted_function() {
    let reg = Arc::new(Registry::builder().register(AddFlags).unwrap().build());
    let id = reg.id("r.addf").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg.clone());
    let x = cx.symbol("x", Width::W32).unwrap();
    let y = cx.symbol("y", Width::W32).unwrap();
    let s = cx.ext(id, &[x, y]).unwrap();
    let text = bitwright::smtlib::export(&mut cx, &s).unwrap();
    let mut cx2 = Context::with_registry(ContextConfig::default(), reg);
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        bitwright::smtlib::import(&mut cx2, &text).map(|_| ())
    }));
    assert!(r.is_ok());
}

/// A host SMT-LIB term that is not one balanced expression is refused.
#[cfg(feature = "smtlib")]
#[test]
fn a_host_smtlib_term_must_be_one_expression() {
    struct Bad;
    impl ExtOp for Bad {
        fn name(&self) -> &str {
            "r.bad"
        }
        fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
            match args {
                [a] => Ok(ExtSig::new(&[("r", *a)])),
                _ => Err("one".into()),
            }
        }
        fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
            out[0] = args[0];
        }
        fn smtlib(&self, _: u8, _: &[&str], _: &[Width]) -> Option<String> {
            Some(")) (assert false) ((".into())
        }
    }
    let reg = Arc::new(Registry::builder().register(Bad).unwrap().build());
    let id = reg.id("r.bad").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let x = cx.symbol("x", Width::W32).unwrap();
    let s = cx.ext(id, &[x]).unwrap();
    assert!(bitwright::smtlib::export(&mut cx, &s).is_err());
}

/// With uninterpreted functions, the script declares a logic that has them, and a solver
/// accepts it (checked with z3 and bitwuzla, each when it is on PATH).
#[cfg(feature = "smtlib")]
#[test]
fn equivalence_queries_with_calls_declare_uninterpreted_functions() {
    let reg = Arc::new(Registry::builder().register(AddFlags).unwrap().build());
    let id = reg.id("r.addf").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let x = cx.symbol("x", Width::W32).unwrap();
    let y = cx.symbol("y", Width::W32).unwrap();
    let a = cx.ext(id, &[x, y]).unwrap()[0];
    let b = cx.add(x, y).unwrap();
    let q = bitwright::smtlib::equivalence_query(&mut cx, a, b).unwrap();
    assert!(q.starts_with("(set-logic QF_UFBV)\n"), "{q}");
    let plain = bitwright::smtlib::equivalence_query(&mut cx, b, b).unwrap();
    assert!(plain.starts_with("(set-logic QF_BV)\n"));
    for solver in Solver::ALL {
        if let Some(out) = solver.run(&q, None) {
            assert!(!out.contains("error"), "{}: {out}", solver.name());
        }
    }
}

/// A symbol spelled like an exported function name is renamed, not confused with it.
#[cfg(feature = "smtlib")]
#[test]
fn exported_function_names_cannot_collide_with_symbols() {
    let reg = Arc::new(Registry::builder().register(AddFlags).unwrap().build());
    let id = reg.id("r.addf").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let x = cx.symbol("x", Width::W32).unwrap();
    let evil = cx.symbol("ext!r.addf#1[0]@32,32", Width::W32).unwrap();
    let a = cx.ext(id, &[x, x]).unwrap()[0];
    let s = cx.add(a, evil).unwrap();
    let q = bitwright::smtlib::equivalence_query(&mut cx, s, x).unwrap();
    assert_eq!(
        q.matches("(declare-fun |ext!r.addf#1[0]@32,32|").count(),
        1,
        "{q}"
    );
    assert_eq!(
        q.matches("(declare-const |ext!r.addf#1[0]@32,32|").count(),
        0,
        "{q}"
    );
    for solver in Solver::ALL {
        if let Some(out) = solver.run(&q, None) {
            assert!(!out.contains("error"), "{}: {out}", solver.name());
        }
    }
}

#[test]
fn an_id_from_another_registry_is_refused() {
    let ra = Arc::new(Registry::builder().register(AddFlags).unwrap().build());
    let rb = Arc::new(Registry::builder().register(Wide256).unwrap().build());
    let id_a = ra.id("r.addf").unwrap();
    let mut cxb = Context::with_registry(ContextConfig::default(), rb);
    let x = cxb.symbol("x", Width::W8).unwrap();
    let y = cxb.symbol("y", Width::W8).unwrap();
    let r = cxb.ext(id_a, &[x, y]);
    assert!(
        r.is_err(),
        "built {:?} with a foreign id",
        r.map(|v| cxb.display(v[0]).to_string())
    );
}

/// Unsigned division and remainder: two outputs of one width.
struct DivMod;
impl ExtOp for DivMod {
    fn name(&self) -> &str {
        "r.divmod"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b] if a == b => Ok(ExtSig::new(&[("q", *a), ("r", *a)])),
            _ => Err("two of one width".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        out[0] = bin(BinOp::UDiv, &args[0], &args[1]);
        out[1] = bin(BinOp::URem, &args[0], &args[1]);
    }
}

#[test]
fn calls_on_constants_fold_to_the_right_output() {
    let reg = Arc::new(Registry::builder().register(DivMod).unwrap().build());
    let id = reg.id("r.divmod").unwrap();
    let mut cx = Context::with_registry(ContextConfig::default(), reg);
    let a = cx.constant_u64(Width::W8, 47).unwrap();
    let b = cx.constant_u64(Width::W8, 10).unwrap();
    let out = cx.ext(id, &[a, b]).unwrap();
    let v: Vec<u64> = out
        .iter()
        .map(|&e| cx.as_const(e).unwrap().unwrap().to_u64().unwrap())
        .collect();
    assert_eq!(v, vec![4, 7]);
    // And through a rebuild: an argument simplified to a constant.
    let x = cx.symbol("x", Width::W8).unwrap();
    let noisy = cx
        .parse("(x | 47) & 47", &ParseOptions::width(Width::W8))
        .unwrap();
    let _ = x;
    let r = cx.ext(id, &[noisy, b]).unwrap()[1];
    let out = Engine::standard().simplify(&mut cx, r).unwrap();
    assert_eq!(
        cx.as_const(out.expr).unwrap().and_then(|v| v.to_u64()),
        Some(7)
    );
}

#[test]
fn unchecked_registration_skips_only_the_self_test() {
    // The self-test would refuse it; unchecked registration takes it, and check() reports it.
    assert!(Registry::builder().register(SubClaimedCommutative).is_err());
    assert!(
        Registry::builder()
            .register_unchecked(SubClaimedCommutative)
            .is_ok()
    );
    assert!(bitwright::ext::check(&SubClaimedCommutative).is_err());
    assert!(bitwright::ext::check(&AddFlags).is_ok());
    // Names are still checked.
    let dup = Registry::builder()
        .register_unchecked(AddFlags)
        .unwrap()
        .register_unchecked(AddFlags);
    assert!(matches!(dup, Err(bitwright::ext::ExtError::Duplicate(_))));
}
