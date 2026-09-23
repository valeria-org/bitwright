//! Extension operations: registration and its contract self-test, construction, evaluation,
//! facts, simplification around them, text and SMT-LIB.

use std::sync::Arc;

use bitwright::engine::{Engine, Run};
use bitwright::ext::{ExtError, ExtOp, ExtSig, ExtTraits, Registry};
use bitwright::{
    Assumptions, BinOp, BitVec, Context, ContextConfig, Error, Expr, KnownBits, ParseOptions,
    SymbolKey, UnOp, View, Width,
};

fn bin(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::apply_bin(op, a, b).unwrap()
}

/// `a + b + cin` (cin 1 bit): the sum and the carry out. Commutative in `a` and `b`, with
/// known bits and an expansion.
struct AddC;

impl ExtOp for AddC {
    fn name(&self) -> &str {
        "t.addc"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a, b, c] if a == b && c.bits() == 1 => {
                Ok(ExtSig::new(&[("sum", *a), ("carry", Width::W1)]))
            }
            _ => Err("a, b of one width and a 1-bit carry".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let w = args[0].width();
        let c = args[2].zext(w).unwrap_or(args[2]);
        let s1 = bin(BinOp::Add, &args[0], &args[1]);
        let s = bin(BinOp::Add, &s1, &c);
        // Carry out: the sum wrapped below an operand.
        let carry = BitVec::apply_cmp(bitwright::CmpOpExt::Ult, &s1, &args[0]).unwrap()
            || BitVec::apply_cmp(bitwright::CmpOpExt::Ult, &s, &s1).unwrap();
        out[0] = s;
        out[1] = BitVec::from_bool(carry);
    }
    fn known_bits(&self, args: &[KnownBits], out: &mut [KnownBits]) {
        // The sum's low bit is known when all three low bits are.
        let w = args[0].width();
        let bits: Option<Vec<bool>> = args.iter().map(|k| k.bit(0)).collect();
        if let Some(b) = bits {
            let one = b.iter().filter(|x| **x).count() % 2 == 1;
            let v = BitVec::one(w);
            let zero_mask = if one { BitVec::zero(w) } else { v };
            let one_mask = if one { v } else { BitVec::zero(w) };
            out[0] = KnownBits::new(zero_mask, one_mask).unwrap();
        }
    }
    fn expand(&self, cx: &mut Context, args: &[Expr]) -> Option<Result<Vec<Expr>, Error>> {
        Some((|| {
            let w = cx.width(args[0])?;
            let c = cx.zext(args[2], w).or_else(|_| Ok::<_, Error>(args[2]))?;
            let s1 = cx.add(args[0], args[1])?;
            let s = cx.add(s1, c)?;
            let c1 = cx.add_carry(args[0], args[1])?;
            let c2 = cx.add_carry(s1, c)?;
            let carry = cx.or(c1, c2)?;
            Ok(vec![s, carry])
        })())
    }
    fn traits(&self) -> ExtTraits {
        ExtTraits::default().with_commutative(true)
    }
}

/// A mixing function the simplifier must leave alone, arguments included.
struct Mix;

impl ExtOp for Mix {
    fn name(&self) -> &str {
        "t.mix"
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a] => Ok(ExtSig::new(&[("h", *a)])),
            _ => Err("one operand".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        let w = args[0].width();
        let k = BitVec::wrapping_from_u64(w, 0x9e37_79b9_7f4a_7c15);
        out[0] = bin(
            BinOp::Xor,
            &bin(BinOp::Mul, &args[0], &k),
            &BitVec::apply_un(UnOp::BitRev, &args[0]).unwrap(),
        );
    }
    fn traits(&self) -> ExtTraits {
        ExtTraits::default().with_opaque(true)
    }
}

fn registry() -> Arc<Registry> {
    Arc::new(
        Registry::builder()
            .register(AddC)
            .unwrap()
            .register(Mix)
            .unwrap()
            .build(),
    )
}

fn context() -> (Context, Arc<Registry>) {
    let r = registry();
    (
        Context::with_registry(ContextConfig::default(), r.clone()),
        r,
    )
}

// ----- registration -------------------------------------------------------------------------

/// An operation with configurable defects.
struct Broken {
    name: &'static str,
    wrong_width: bool,
    unsound_bits: bool,
    bad_expand: bool,
}

impl ExtOp for Broken {
    fn name(&self) -> &str {
        self.name
    }
    fn signature(&self, args: &[Width]) -> Result<ExtSig, String> {
        match args {
            [a] => Ok(ExtSig::new(&[("r", *a)])),
            _ => Err("one operand".into()),
        }
    }
    fn eval(&self, args: &[BitVec], out: &mut [BitVec]) {
        out[0] = if self.wrong_width {
            // One bit too wide, at every width.
            BitVec::zero(Width::new(args[0].width().bits() + 1).unwrap())
        } else {
            BitVec::apply_un(UnOp::Not, &args[0]).unwrap()
        };
    }
    fn known_bits(&self, args: &[KnownBits], out: &mut [KnownBits]) {
        if self.unsound_bits {
            // Claims the input's known bits unchanged (wrong: the result is complemented).
            out[0] = args[0];
        }
    }
    fn expand(&self, cx: &mut Context, args: &[Expr]) -> Option<Result<Vec<Expr>, Error>> {
        self.bad_expand
            .then(|| Ok(vec![args[0]]))
            .or_else(|| Some(cx.not(args[0]).map(|e| vec![e])))
    }
}

#[test]
fn registration_runs_the_contract_self_test() {
    let ok = Broken {
        name: "t.not",
        wrong_width: false,
        unsound_bits: false,
        bad_expand: false,
    };
    assert!(Registry::builder().register(ok).is_ok());
    for (b, what) in [
        (
            Broken {
                name: "t.w",
                wrong_width: true,
                unsound_bits: false,
                bad_expand: false,
            },
            "bits, declared",
        ),
        (
            Broken {
                name: "t.k",
                wrong_width: false,
                unsound_bits: true,
                bad_expand: false,
            },
            "known bits",
        ),
        (
            Broken {
                name: "t.e",
                wrong_width: false,
                unsound_bits: false,
                bad_expand: true,
            },
            "expand disagrees",
        ),
    ] {
        match Registry::builder().register(b) {
            Err(ExtError::Contract(n, why)) => assert!(why.contains(what), "{n}: {why}"),
            other => panic!("{:?}", other.map(|_| ())),
        }
    }
    for bad in ["", "1x", "a..b", "a.", "a b", "a-b"] {
        let b = Broken {
            name: bad,
            wrong_width: false,
            unsound_bits: false,
            bad_expand: false,
        };
        assert!(
            matches!(Registry::builder().register(b), Err(ExtError::BadName(_))),
            "{bad}"
        );
    }
    let dup = Registry::builder().register(AddC).unwrap().register(AddC);
    assert!(matches!(dup, Err(ExtError::Duplicate(_))));
}

// ----- construction and evaluation ----------------------------------------------------------

#[test]
fn calls_are_hash_consed_folded_and_width_checked() {
    let (mut cx, r) = context();
    let addc = r.id("t.addc").unwrap();
    let w = Width::W8;
    let (x, y) = (cx.symbol("x", w).unwrap(), cx.symbol("y", w).unwrap());
    let c = cx.symbol("c", Width::W1).unwrap();
    let out = cx.ext(addc, &[x, y, c]).unwrap();
    assert_eq!(out.len(), 2);
    assert_eq!(cx.width(out[0]).unwrap(), w);
    assert_eq!(cx.width(out[1]).unwrap(), Width::W1);
    // Hash-consed, and the commutative operands in canonical order.
    assert_eq!(cx.ext(addc, &[y, x, c]).unwrap(), out);
    assert_eq!(cx.ext_output(addc, 1, &[x, y, c]).unwrap(), out[1]);
    match cx.view(out[1]).unwrap() {
        View::Ext { op, output, args } => {
            assert_eq!((op, output), (addc, 1));
            assert_eq!(args.as_slice().len(), 3);
        }
        v => panic!("{v:?}"),
    }
    // Constants fold.
    let a = cx.constant_u64(w, 200).unwrap();
    let b = cx.constant_u64(w, 100).unwrap();
    let one = cx.constant_u64(Width::W1, 1).unwrap();
    let f = cx.ext(addc, &[a, b, one]).unwrap();
    assert_eq!(cx.as_const(f[0]).unwrap().unwrap().to_u64(), Some(45));
    assert_eq!(cx.as_const(f[1]).unwrap().unwrap().to_u64(), Some(1));
    // Rejected shapes are errors, not guesses.
    assert!(cx.ext(addc, &[x, y]).is_err());
    assert!(cx.ext(addc, &[x, c, c]).is_err());
    assert!(cx.ext_output(addc, 2, &[x, y, c]).is_err());
    let mut plain = Context::new();
    let z = plain.symbol("z", w).unwrap();
    assert!(plain.ext(addc, &[z, z, z]).is_err());
}

#[test]
fn evaluation_facts_and_substitution_agree_with_the_operation() {
    let (mut cx, r) = context();
    let addc = r.id("t.addc").unwrap();
    for w in [1u16, 7, 8, 64, 100] {
        let w = Width::new(w).unwrap();
        let (x, y) = (
            cx.symbol(format!("x{}", w.bits()).as_str(), w).unwrap(),
            cx.symbol(format!("y{}", w.bits()).as_str(), w).unwrap(),
        );
        let c = cx.symbol("c", Width::W1).unwrap();
        let one = cx_one(&mut cx, w);
        let x2 = cx.bin(BinOp::Or, x, one).unwrap();
        let out = cx.ext(addc, &[x2, y, c]).unwrap();
        let facts: Vec<_> = out.iter().map(|&e| cx.facts(e).unwrap()).collect();
        let mut s = 0x1234_5678u64;
        for _ in 0..200 {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            let (vx, vy, vc) = (
                BitVec::wrapping_from_limbs(w, &[s, s.rotate_left(17)]),
                BitVec::wrapping_from_limbs(w, &[s.rotate_left(31), !s]),
                BitVec::from_bool(s >> 63 == 1),
            );
            let env: Vec<(SymbolKey, BitVec)> = vec![
                (SymbolKey::from(format!("x{}", w.bits()).as_str()), vx),
                (SymbolKey::from(format!("y{}", w.bits()).as_str()), vy),
                (SymbolKey::from("c"), vc),
            ];
            let got = cx.eval(&out, &env[..]).unwrap();
            let one = BitVec::one(w);
            let mut want = vec![BitVec::zero(w), BitVec::zero(Width::W1)];
            AddC.eval(&[bin(BinOp::Or, &vx, &one), vy, vc], &mut want);
            assert_eq!(got, want);
            for (f, v) in facts.iter().zip(&got) {
                assert!(f.contains(v));
            }
        }
        // Substitution goes through the call.
        let k = cx.constant_u64(w, 0).unwrap();
        let sub = cx.substitute(&out, &[(y, k)]).unwrap();
        assert_eq!(sub, cx.ext(addc, &[x2, k, c]).unwrap());
    }
}

fn cx_one(cx: &mut Context, w: Width) -> Expr {
    cx.constant(&BitVec::one(w)).unwrap()
}

#[test]
fn facts_use_the_operations_known_bits_and_constraints() {
    let (mut cx, r) = context();
    let addc = r.id("t.addc").unwrap();
    let w = Width::W16;
    let o = ParseOptions::width(w);
    // Low bits known: x odd, y even, carry in 0: the sum is odd.
    let x = cx.parse("x | 1", &o).unwrap();
    let y = cx.parse("y << 1", &o).unwrap();
    let zero = cx.constant_u64(Width::W1, 0).unwrap();
    let sum = cx.ext(addc, &[x, y, zero]).unwrap()[0];
    assert_eq!(cx.facts(sum).unwrap().known().bit(0), Some(true));
    // Under constraints pinning the arguments, the outputs are exact.
    let (px, py) = (cx.parse("p", &o).unwrap(), cx.parse("q", &o).unwrap());
    let out = cx.ext(addc, &[px, py, zero]).unwrap();
    let mut a = Assumptions::new();
    let p0 = cx.parse("p == 0xffff", &o).unwrap();
    let p1 = cx.parse("q == 2", &o).unwrap();
    a.assume_true(&mut cx, p0).unwrap();
    a.assume_true(&mut cx, p1).unwrap();
    let f = cx.facts_with(out[0], &a).unwrap().unwrap();
    assert_eq!(f.as_constant().and_then(|v| v.to_u64()), Some(1));
    let f = cx.facts_with(out[1], &a).unwrap().unwrap();
    assert_eq!(f.as_constant().and_then(|v| v.to_u64()), Some(1));
}

// ----- simplification -----------------------------------------------------------------------

#[test]
fn the_simplifier_rewrites_arguments_unless_the_call_is_opaque() {
    let (mut cx, r) = context();
    let (addc, mix) = (r.id("t.addc").unwrap(), r.id("t.mix").unwrap());
    let w = Width::W32;
    let o = ParseOptions::width(w);
    let noisy = cx.parse("(x + 0) ^ (y & y)", &o).unwrap();
    let clean = cx.parse("x ^ y", &o).unwrap();
    let c = cx.symbol("c", Width::W1).unwrap();
    let z = cx.symbol("z", w).unwrap();
    let e = cx.ext(addc, &[noisy, z, c]).unwrap()[1];
    let engine = Engine::standard();
    let out = engine.simplify(&mut cx, e).unwrap();
    assert_eq!(out.expr, cx.ext(addc, &[clean, z, c]).unwrap()[1]);
    // `x + 0` folds at construction, so the opaque argument is built by hand from a node the
    // simplifier would rewrite: `(x | y) - (x & y)` is `x ^ y`.
    let mba = cx.parse("(x | y) - (x & y)", &o).unwrap();
    let h = cx.ext(mix, &[mba]).unwrap()[0];
    let out = engine.simplify(&mut cx, h).unwrap();
    assert!(!out.changed, "{}", cx.display(out.expr));
    // Around a call, everything else is simplified as usual, and results evaluate equal.
    let around = cx.parse("(z + zext<32>(c)) - z", &o).unwrap();
    let sum = cx.add(h, around).unwrap();
    let out = engine.simplify(&mut cx, sum).unwrap();
    assert!(out.changed);
    let env: Vec<(SymbolKey, BitVec)> = vec![
        (
            SymbolKey::from("x"),
            BitVec::wrapping_from_u64(w, 0xdead_beef),
        ),
        (
            SymbolKey::from("y"),
            BitVec::wrapping_from_u64(w, 0x1234_5678),
        ),
        (SymbolKey::from("c"), BitVec::one(Width::W1)),
        (SymbolKey::from("z"), BitVec::wrapping_from_u64(w, 77)),
    ];
    assert_eq!(
        cx.eval(&[sum], &env[..]).unwrap(),
        cx.eval(&[out.expr], &env[..]).unwrap()
    );
    // Strict verification evaluates the calls too.
    let strict = Engine::builder()
        .builtin()
        .verify(bitwright::engine::Verify::strict())
        .build()
        .unwrap();
    let out = strict.run(&mut cx, &[e, sum], Run::default()).unwrap();
    assert_eq!(out.stats.rejected, 0);
}

// ----- text and SMT-LIB ---------------------------------------------------------------------

#[test]
fn calls_print_and_parse_back() {
    let (mut cx, r) = context();
    let addc = r.id("t.addc").unwrap();
    let w = Width::W8;
    let (x, y) = (cx.symbol("x", w).unwrap(), cx.symbol("y", w).unwrap());
    let c = cx.symbol("c", Width::W1).unwrap();
    let k = cx.constant_u64(w, 100).unwrap();
    let out = cx.ext(addc, &[x, k, c]).unwrap();
    let e = cx.add(out[0], y).unwrap();
    let text = cx.display(e).to_string();
    assert!(text.contains("@t.addc(x, 100:8, c)"), "{text}");
    let back = cx.parse(&text, &ParseOptions::default()).unwrap();
    assert_eq!(back, e);
    let text = cx.display(out[1]).to_string();
    assert_eq!(text, "@t.addc[1](x, 100:8, c)");
    assert_eq!(cx.parse(&text, &ParseOptions::default()).unwrap(), out[1]);
    // The result width comes from the operation.
    let e = cx
        .parse("zext<16>(@t.addc[1](x, y, c))", &ParseOptions::default())
        .unwrap();
    assert_eq!(cx.width(e).unwrap(), Width::W16);
    for bad in [
        "@t.nope(x)",
        "@t.addc(x, y)",
        "@t.addc[2](x, y, c)",
        "@t.addc[1](x, y, c) + x",
        "@(x)",
        "@t.addc[](x, y, c)",
    ] {
        assert!(cx.parse(bad, &ParseOptions::default()).is_err(), "{bad}");
    }
    let mut plain = Context::new();
    assert!(
        plain
            .parse("@t.addc(x, y, c)", &ParseOptions::width(w))
            .is_err()
    );
}

#[cfg(feature = "smtlib")]
#[test]
fn calls_export_as_uninterpreted_functions() {
    let (mut cx, r) = context();
    let addc = r.id("t.addc").unwrap();
    let w = Width::W8;
    let (x, y) = (cx.symbol("x", w).unwrap(), cx.symbol("y", w).unwrap());
    let c = cx.symbol("c", Width::W1).unwrap();
    let out = cx.ext(addc, &[x, y, c]).unwrap();
    let s = bitwright::smtlib::export(&mut cx, &out).unwrap();
    assert!(
        s.contains(
            "(declare-fun |ext!t.addc#1[0]@8,8,1| ((_ BitVec 8) (_ BitVec 8) (_ BitVec 1)) (_ BitVec 8))"
        ),
        "{s}"
    );
    assert!(s.contains("(declare-fun |ext!t.addc#1[1]@8,8,1|"), "{s}");
}

/// Random DAGs mixing extension calls with built-in operators: every simplified result
/// evaluates equal to its input, under both built-in strategies.
#[test]
fn simplified_results_with_calls_are_equivalent() {
    use bitwright::engine::Strategy;
    let (_, r) = context();
    let (addc, mix) = (r.id("t.addc").unwrap(), r.id("t.mix").unwrap());
    let mut state = 0x0e47_0001u64;
    let mut next = move || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        state >> 11
    };
    let engines = [
        Engine::standard(),
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap(),
    ];
    let mut changed = 0;
    for _ in 0..300 {
        let mut cx = Context::with_registry(ContextConfig::default(), r.clone());
        let w = Width::new([8u16, 13, 32, 64][(next() % 4) as usize]).unwrap();
        let syms: Vec<Expr> = ["a", "b", "d"]
            .iter()
            .map(|n| cx.symbol(*n, w).unwrap())
            .collect();
        let c = cx.symbol("c", Width::W1).unwrap();
        let mut pool = syms.clone();
        for _ in 0..12 {
            let x = pool[(next() % pool.len() as u64) as usize];
            let y = pool[(next() % pool.len() as u64) as usize];
            let e = match next() % 7 {
                0 => cx.ext(addc, &[x, y, c]).unwrap()[0],
                1 => {
                    let carry = cx.ext(addc, &[x, y, c]).unwrap()[1];
                    cx.zext(carry, w).unwrap()
                }
                2 => cx.ext(mix, &[x]).unwrap()[0],
                3 => cx.add(x, y).unwrap(),
                4 => cx.xor(x, y).unwrap(),
                5 => {
                    let k = cx.constant_u64(w, next() % 256).unwrap();
                    cx.and(x, k).unwrap()
                }
                _ => {
                    let one = cx_one(&mut cx, w);
                    cx.sub(x, one).unwrap()
                }
            };
            pool.push(e);
        }
        let root = *pool.last().unwrap();
        for engine in &engines {
            let out = engine.simplify(&mut cx, root).unwrap();
            changed += usize::from(out.changed);
            for _ in 0..8 {
                let env: Vec<(SymbolKey, BitVec)> = vec![
                    (SymbolKey::from("a"), BitVec::wrapping_from_u64(w, next())),
                    (SymbolKey::from("b"), BitVec::wrapping_from_u64(w, next())),
                    (SymbolKey::from("d"), BitVec::wrapping_from_u64(w, next())),
                    (SymbolKey::from("c"), BitVec::from_bool(next() % 2 == 0)),
                ];
                assert_eq!(
                    cx.eval(&[root], &env[..]).unwrap(),
                    cx.eval(&[out.expr], &env[..]).unwrap(),
                    "{} became {}",
                    cx.display(root),
                    cx.display(out.expr)
                );
            }
        }
    }
    assert!(changed > 30, "only {changed} changed");
}

#[test]
fn a_context_adopts_a_registry_that_extends_its_own() {
    let small = Arc::new(Registry::builder().register(AddC).unwrap().build());
    let mut cx = Context::with_registry(ContextConfig::default(), small.clone());
    let addc = small.id("t.addc").unwrap();
    let w = Width::W8;
    let (x, y) = (cx.symbol("x", w).unwrap(), cx.symbol("y", w).unwrap());
    let c = cx.symbol("c", Width::W1).unwrap();
    let before = cx.ext(addc, &[x, y, c]).unwrap();
    // Registered after: same position for t.addc.
    let big = registry();
    cx.extend_registry(big.clone()).unwrap();
    assert_eq!(cx.ext(addc, &[x, y, c]).unwrap(), before);
    let mix = big.id("t.mix").unwrap();
    assert!(cx.ext(mix, &[x]).is_ok());
    // Not an extension: another operation where t.addc was.
    let other = Arc::new(Registry::builder().register(Mix).unwrap().build());
    assert!(cx.extend_registry(other).is_err());
    assert_eq!(cx.ext(addc, &[x, y, c]).unwrap(), before);
}
