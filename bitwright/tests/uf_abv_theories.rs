//! End-to-end tests for native `QF_UFBV` (`ExtOp` congruence, injectivity, and lazy
//! point-evaluation refinement in `prove` and `solve`) and `QF_ABV` / `QF_UFBV` model &
//! value reconstruction in `smtlib`.
#![cfg(all(feature = "prove", feature = "smtlib"))]

use std::sync::Arc;

use bitwright::ext::{ExtInverse, ExtOp, ExtSig, ExtTraits, InverseArg, Invertible, Registry};
use bitwright::prove::{
    self, Config as ProveConfig, Incremental, IncrementalAnswer, Limits, Outcome,
};
use bitwright::solve::{Config as SolveConfig, Solver, Status};
use bitwright::{
    BinOp, BitVec, CmpOp, Context, ContextConfig, KnownBits, ParseOptions, SymbolKey, UnOp, Width,
};

/// Unexpanded opaque hash/mixer `h(x) = (x * 0x9df9) ^ bitrev(x)` (`expand() == None`).
struct OpaqueHash;

impl ExtOp for OpaqueHash {
    fn name(&self) -> &str {
        "uf.hash"
    }

    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [w] => Ok(ExtSig::new(&[("out", *w)])),
            _ => Err("expected 1 operand".into()),
        }
    }

    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let w = args[0].width();
        let k = BitVec::wrapping_from_u64(w, 0x9df9_79b9_7f4a_7c15);
        let prod = BitVec::apply_bin(BinOp::Mul, &args[0], &k).unwrap();
        let rev = BitVec::apply_un(UnOp::BitRev, &args[0]).unwrap();
        out[0] = BitVec::apply_bin(BinOp::Xor, &prod, &rev).unwrap();
    }

    fn traits(&self) -> ExtTraits {
        ExtTraits::default().with_opaque(true)
    }
}

/// Unexpanded keyed bijection `enc(k, x) = rotl(x ^ k, 3)` (no `expand`, declares `Bijective` +
/// `invert` and `inverse` `dec`).
struct KeyedEnc;
struct KeyedDec;

impl ExtOp for KeyedEnc {
    fn name(&self) -> &str {
        "uf.enc"
    }

    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [k, x] if k == x => Ok(ExtSig::new(&[("y", *x)])),
            _ => Err("expected (k, x) of equal width".into()),
        }
    }

    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let w = args[0].width();
        let xk = BitVec::apply_bin(BinOp::Xor, &args[1], &args[0]).unwrap();
        let three = BitVec::wrapping_from_u64(w, 3);
        out[0] = BitVec::apply_bin(BinOp::RotL, &xk, &three).unwrap();
    }

    fn invertible(&self, output: u8, arg: u8, _args: &[KnownBits]) -> Invertible {
        if output == 0 && arg == 1 {
            Invertible::Bijective
        } else {
            Invertible::No
        }
    }

    fn invert(&self, output: u8, arg: u8, args: &[BitVec], value: &BitVec) -> Option<BitVec> {
        if output != 0 || arg != 1 {
            return None;
        }
        let w = value.width();
        let three = BitVec::wrapping_from_u64(w, 3);
        let rot = BitVec::apply_bin(BinOp::RotR, value, &three).ok()?;
        BitVec::apply_bin(BinOp::Xor, &rot, &args[0]).ok()
    }

    fn inverse(&self, output: u8, arg: u8) -> Option<ExtInverse> {
        (output == 0 && arg == 1)
            .then(|| ExtInverse::new("uf.dec", 0, &[InverseArg::Arg(0), InverseArg::Output]))
    }
}

impl ExtOp for KeyedDec {
    fn name(&self) -> &str {
        "uf.dec"
    }

    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [k, y] if k == y => Ok(ExtSig::new(&[("x", *y)])),
            _ => Err("expected (k, y) of equal width".into()),
        }
    }

    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let w = args[0].width();
        let three = BitVec::wrapping_from_u64(w, 3);
        let rot = BitVec::apply_bin(BinOp::RotR, &args[1], &three).unwrap();
        out[0] = BitVec::apply_bin(BinOp::Xor, &rot, &args[0]).unwrap();
    }
}

fn uf_context() -> Context {
    let reg = Arc::new(
        Registry::builder()
            .register(OpaqueHash)
            .unwrap()
            .register(KeyedEnc)
            .unwrap()
            .register(KeyedDec)
            .unwrap()
            .build(),
    );
    Context::with_registry(ContextConfig::default(), reg)
}

#[test]
fn prove_decides_congruence_over_unexpanded_ext_ops_with_certificates() {
    let mut cx = uf_context();
    let o = ParseOptions::width(Width::W32);
    // `a == b` disguised via `(a ^ b) == 0`, nested through two unexpanded `@uf.hash` calls.
    // Because `OpaqueHash` is `opaque`, the simplifier leaves arguments inside `@uf.hash` alone,
    // exercising the prover's Ackermann congruence clauses directly — with DRUP certification!
    let p = cx
        .parse(
            "(x + y != z) | (@uf.hash(@uf.hash((x ^ y) + 2 * (x & y))) == @uf.hash(@uf.hash(z)))",
            &o,
        )
        .unwrap();
    let cfg = ProveConfig::default()
        .with_simplify(false)
        .with_certificate(true);
    let Outcome::Proved(Some(cert)) = prove::valid(&mut cx, p, &cfg).unwrap() else {
        panic!("expected certified congruence proof");
    };
    cert.check().expect("DRUP certificate checks cleanly");
}

#[test]
fn prove_uses_declared_injectivity_and_lazy_eval_refinement_on_unexpanded_ext() {
    let mut cx = uf_context();
    let o = ParseOptions::width(Width::W16);

    // 1. Declared injectivity: `@uf.enc(k, x) == @uf.enc(k, y)` implies `x == y` even with
    //    simplification off and `expand() == None`.
    let inj = cx
        .parse("(@uf.enc(k, x) != @uf.enc(k, y)) | (x == y)", &o)
        .unwrap();
    let out = prove::valid(
        &mut cx,
        inj,
        &ProveConfig::default()
            .with_simplify(false)
            .with_certificate(true),
    )
    .unwrap();
    let Outcome::Proved(Some(cert)) = out else {
        panic!("expected certified injectivity proof, got {out:?}");
    };
    cert.check().unwrap();

    // 2. Lazy point-evaluation CEGAR: `x == 0x1234 => @uf.hash(x) == H(0x1234)` with
    //    `simplify = false` (so `x == 0x1234` is not substituted before blasting).
    let mut want_buf = [BitVec::zero(Width::W16)];
    OpaqueHash.eval(
        &[BitVec::from_u64(Width::W16, 0x1234).unwrap()],
        &mut want_buf,
    );
    let want_u64 = want_buf[0].to_u64().unwrap();
    let point_valid = cx
        .parse(&format!("(x != 0x1234) | (@uf.hash(x) == {want_u64})"), &o)
        .unwrap();
    assert!(matches!(
        prove::valid(
            &mut cx,
            point_valid,
            &ProveConfig::default().with_simplify(false)
        )
        .unwrap(),
        Outcome::Proved(None)
    ));

    // 3. Genuine counterexample refutation on wrong constant `want_u64 ^ 1`: verified against `eval`.
    let point_invalid = cx
        .parse(
            &format!("(x != 0x1234) | (@uf.hash(x) == {})", want_u64 ^ 1),
            &o,
        )
        .unwrap();
    let Outcome::Refuted(ce) = prove::valid(
        &mut cx,
        point_invalid,
        &ProveConfig::default().with_simplify(false).with_samples(0),
    )
    .unwrap() else {
        panic!("expected verified counterexample");
    };
    let x_val = ce
        .iter()
        .find(|(k, _)| *k == SymbolKey::from("x"))
        .unwrap()
        .1;
    assert_eq!(x_val.to_u64(), Some(0x1234));
}

#[test]
fn incremental_and_solver_handle_unexpanded_and_bijective_ext_equations() {
    // 1. Incremental solver on 8-bit unexpanded `@uf.hash` with lazy `eval` refinement.
    let mut cx = uf_context();
    let o8 = ParseOptions::width(Width::W8);
    let p1 = cx.parse("x == 0x2a", &o8).unwrap();
    let mut h2a = [BitVec::zero(Width::W8)];
    OpaqueHash.eval(&[BitVec::from_u64(Width::W8, 0x2a).unwrap()], &mut h2a);
    let p_wrong = cx
        .parse(
            &format!("@uf.hash(x) == {}", h2a[0].to_u64().unwrap() ^ 1),
            &o8,
        )
        .unwrap();
    let p_right = cx
        .parse(&format!("@uf.hash(x) == {}", h2a[0].to_u64().unwrap()), &o8)
        .unwrap();
    let mut inc = Incremental::new(1 << 16);
    assert!(matches!(
        inc.solve(&mut cx, &[p1, p_wrong], Limits::conflicts(10_000))
            .unwrap(),
        IncrementalAnswer::Unsat(_)
    ));
    let IncrementalAnswer::Sat(m) = inc
        .solve(&mut cx, &[p1, p_right], Limits::conflicts(10_000))
        .unwrap()
    else {
        panic!("expected Sat");
    };
    assert_eq!(
        cx.eval(&[p1, p_right], &m[..]).unwrap(),
        [BitVec::from_bool(true), BitVec::from_bool(true)]
    );

    // 2. Full `Solver` isolating a 64-bit symbol through chained `@uf.enc` (`ExtOp::inverse`)
    //    AND through unexpanded `@mixer.round` (`ExtOp::invert`).
    let mut cx64 = uf_context();
    let o64 = ParseOptions::width(Width::W64);
    let eq_enc = cx64
        .parse("@uf.enc(k1, @uf.enc(k2, secret) + 9) == target", &o64)
        .unwrap();
    let k1_pin = cx64.parse("k1 == 0x1122334455667788", &o64).unwrap();
    let k2_pin = cx64.parse("k2 == 0x99aabbccddeeff00", &o64).unwrap();
    let tgt_pin = cx64.parse("target == 0xfeedfacecafebabe", &o64).unwrap();
    let mut solver = Solver::new(SolveConfig::default());
    for a in [eq_enc, k1_pin, k2_pin, tgt_pin] {
        solver.assert(&cx64, a).unwrap();
    }
    assert_eq!(solver.check(&mut cx64).unwrap(), Status::Sat);
    let secret = cx64.parse("secret", &o64).unwrap();
    let sv = solver.value(&mut cx64, secret).unwrap().unwrap();
    let env = [
        (
            SymbolKey::from("k1"),
            BitVec::from_u64(Width::W64, 0x1122_3344_5566_7788).unwrap(),
        ),
        (
            SymbolKey::from("k2"),
            BitVec::from_u64(Width::W64, 0x99aa_bbcc_ddee_ff00).unwrap(),
        ),
        (
            SymbolKey::from("target"),
            BitVec::from_u64(Width::W64, 0xfeed_face_cafe_babe).unwrap(),
        ),
        (SymbolKey::from("secret"), sv),
    ];
    assert_eq!(
        cx64.eval(&[eq_enc], &env[..]).unwrap()[0],
        BitVec::from_bool(true)
    );

    // Unexpanded 64-bit `@mixer.round` inverted via `ExtOp::invert` inside `Solver`.
    let mreg = Arc::new(prove::mixer::registry());
    let mut mcx = Context::with_registry(ContextConfig::default(), mreg);
    let x = mcx.symbol("x", Width::W64).unwrap();
    let r1 = prove::mixer::mk_round(&mut mcx, x, 0x3188_e5d3_9d63_b2d3).unwrap();
    let r2 = prove::mixer::mk_round(&mut mcx, r1, 0x9b1d_b13a_6e8e_3927).unwrap();
    let goal_const = mcx.constant_u64(Width::W64, 0x0123_4567_89ab_cdef).unwrap();
    let eq_round = mcx.cmp(CmpOp::Eq, r2, goal_const).unwrap();
    let mut msolver = Solver::default();
    msolver.assert(&mcx, eq_round).unwrap();
    assert_eq!(msolver.check(&mut mcx).unwrap(), Status::Sat);
    let xv = msolver.value(&mut mcx, x).unwrap().unwrap();
    assert_eq!(
        mcx.eval(&[eq_round], &[(SymbolKey::from("x"), xv)][..])
            .unwrap()[0],
        BitVec::from_bool(true)
    );
}

#[cfg(feature = "smtlib")]
#[test]
fn smtlib_session_reconstructs_qf_abv_and_qf_ufbv_models_and_values() {
    let script = "
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const idx (_ BitVec 8))
        (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
        (assert (= idx #x04))
        (assert (= (select a idx) #x2a))
        (assert (= (select (store a #x05 #x99) #x05) (f idx)))
        (assert (= (f #x07) #x11))
        (check-sat)
        (get-value (a (store a #x05 #x99) (f idx) (f #x07)))
        (get-model)
    ";
    let mut cx = Context::new();
    let mut out = String::new();
    let summary =
        bitwright::smtlib::run(&mut cx, script, &SolveConfig::default(), &mut out).unwrap();
    assert_eq!((summary.sat, summary.errors), (1, 0), "{out}");
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines[0], "sat");
    assert!(lines[1].contains("((f idx) #x99)"), "{out}");
    assert!(lines[1].contains("((f #x07) #x11)"), "{out}");
    assert!(
        lines[1].contains("(as const (Array (_ BitVec 8) (_ BitVec 8)))"),
        "{out}"
    );

    // Validate the emitted `(get-model)` by feeding its `define-fun`s back into `smtlib::import`
    // and checking that every asserted formula in the original script evaluates to `true`!
    let model_start = out.find("\n(\n").expect("model block");
    let model_block = out[model_start + 1..].trim();
    let inner_defs = model_block
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .expect("parenthesized model");
    let validation_script = format!(
        "{inner_defs}
         (assert (= idx #x04))
         (assert (= (select a idx) #x2a))
         (assert (= (select (store a #x05 #x99) #x05) (f idx)))
         (assert (= (f #x07) #x11))"
    );
    let mut check_cx = Context::new();
    let imported = bitwright::smtlib::import(&mut check_cx, &validation_script).unwrap();
    assert!(
        imported.symbols.is_empty(),
        "all declarations defined by model"
    );
    for (k, &assertion) in imported.assertions.iter().enumerate() {
        let v = check_cx.eval(&[assertion], &[][..]).unwrap()[0];
        assert_eq!(
            v,
            BitVec::from_bool(true),
            "assertion {k} failed in reconstructed model:\n{inner_defs}"
        );
    }
}
