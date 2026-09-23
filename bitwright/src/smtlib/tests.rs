use std::collections::BTreeMap;

use super::*;
use crate::testutil::{Gen, Rng};
use crate::{BitVec, Context, ParseOptions, SymbolKey, Width};

fn gen_w(seed: u64, max_w: u16) -> Gen {
    Gen {
        rng: Rng(seed),
        max_w,
        vars: Vec::new(),
    }
}

/// A random value for every symbol under `roots`, by key.
fn point(cx: &mut Context, roots: &[Expr], rng: &mut Rng) -> BTreeMap<SymbolKey, BitVec> {
    let mut env = BTreeMap::new();
    for id in cx.symbols_in(roots).unwrap() {
        let w = cx.symbol_width(id).unwrap();
        let limbs: Vec<u64> = (0..8)
            .map(|_| match rng.below(4) {
                0 => 0,
                1 => !0,
                _ => rng.next(),
            })
            .collect();
        env.insert(
            cx.symbol_key(id).unwrap().clone(),
            BitVec::wrapping_from_limbs(w, &limbs),
        );
    }
    env
}

#[test]
fn export_then_import_is_the_same_function() {
    let mut rng = Rng(0x5317);
    for i in 0..600 {
        let max_w = [6, 16, 70, 130][i % 4];
        let mut g = gen_w(0x5317 + i as u64, max_w);
        let mut cx = Context::new();
        let w = 1 + g.rng.below(u64::from(max_w)) as u16;
        let (e, _) = g.expr(&mut cx, w, 4);
        let smt = export(&mut cx, &[e]).unwrap();
        let mut other = Context::new();
        let script = import(&mut other, &smt).unwrap();
        let back = script.definition("root0").unwrap();
        assert_eq!(other.width(back).unwrap(), cx.width(e).unwrap());
        for _ in 0..8 {
            let env = point(&mut cx, &[e], &mut rng);
            let want = cx.eval(&[e], &env).unwrap();
            // Symbols the expression folded away are not declared; bind every key anyway.
            let got = other.eval(&[back], &env).unwrap();
            assert_eq!(got, want, "{}\n{smt}", cx.display(e));
        }
    }
}

#[test]
fn directly_mapped_operators_read_back_to_the_same_expression() {
    let o = ParseOptions::width(Width::W16);
    for src in [
        "x + y * 3 - (x & ~y)",
        "udiv(x, y) + urem(x, 7) + sdiv(y, x) + srem(x, y)",
        "(x << y) | (x >>u 3) | (y >>s x)",
        "select(x <u y, x, zext<16>(trunc<8>(y)))",
        "concat(extract<4, 8>(x), extract<0, 8>(y))",
        "(x == y) ^ (x <s 5)",
    ] {
        let mut cx = Context::new();
        let e = cx.parse(src, &o).unwrap();
        let smt = export(&mut cx, &[e]).unwrap();
        let mut other = Context::new();
        let back = import(&mut other, &smt)
            .unwrap()
            .definition("root0")
            .unwrap();
        assert_eq!(
            other.display(back).to_string(),
            cx.display(e).to_string(),
            "{smt}"
        );
    }
}

#[test]
fn symbol_names_round_trip_and_never_collide() {
    let w = Width::W8;
    let mut cx = Context::new();
    let names = [
        SymbolKey::from("x"),
        SymbolKey::from("n0"),    // the exporter's own name form
        SymbolKey::from("root0"), // likewise
        SymbolKey::from("a|b"),   // unspellable
        SymbolKey::from("#12"),   // would read back as an integer key
        SymbolKey::from("with space"),
        SymbolKey::U64(12),
        SymbolKey::U64(7),
    ];
    let syms: Vec<Expr> = names
        .iter()
        .map(|k| cx.symbol(k.clone(), w).unwrap())
        .collect();
    let f = cx.fresh_symbol(w).unwrap();
    let mut sum = f;
    for &s in &syms {
        let t = cx.bin(crate::BinOp::Mul, sum, s).unwrap();
        sum = cx.bin(crate::BinOp::Add, t, s).unwrap();
    }
    let smt = export(&mut cx, &[sum]).unwrap();
    let mut other = Context::new();
    let script = import(&mut other, &smt).unwrap();
    assert_eq!(script.symbols.len(), names.len() + 1);
    let back = script.definition("root0").unwrap();
    // Spellable keys come back as themselves.
    for k in [
        SymbolKey::from("x"),
        SymbolKey::from("with space"),
        SymbolKey::U64(12),
        SymbolKey::U64(7),
    ] {
        assert!(other.find_symbol(&k).is_some(), "{k:?}\n{smt}");
    }
    let fk = cx
        .symbol_key(cx.symbol_id(f).unwrap().unwrap())
        .unwrap()
        .clone();
    assert!(other.find_symbol(&fk).is_some());
    // The same function, each symbol bound through its exported name.
    let mut rng = Rng(3);
    for _ in 0..16 {
        let mut env = BTreeMap::new();
        let mut env2 = BTreeMap::new();
        for id in cx.symbols_in(&[sum]).unwrap() {
            let key = cx.symbol_key(id).unwrap().clone();
            let name = export::symbol_name(&key, id.index());
            let name = name.trim_matches('|');
            let (_, e2) = script.symbols.iter().find(|(n, _)| n == name).unwrap();
            let id2 = other.symbol_id(*e2).unwrap().unwrap();
            let v = BitVec::wrapping_from_u64(w, rng.next());
            env.insert(key, v);
            env2.insert(other.symbol_key(id2).unwrap().clone(), v);
        }
        assert_eq!(
            other.eval(&[back], &env2).unwrap(),
            cx.eval(&[sum], &env).unwrap()
        );
    }
}

#[test]
fn import_reads_the_qf_bv_theory() {
    let mut cx = Context::new();
    let s = import(
        &mut cx,
        r#"
        ; a comment
        (set-logic QF_BV)
        (set-info :source |anything (at all)|)
        (set-info :status "a ""quoted"" string")
        (declare-const x (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (declare-const p Bool)
        (define-fun a () (_ BitVec 8) (let ((t (bvadd x y)) (x #x01)) (bvmul t x)))
        (define-fun b () (_ BitVec 8) (bvsmod x y))
        (define-fun c () (_ BitVec 16) ((_ zero_extend 8) ((_ rotate_left 3) x)))
        (define-fun d () (_ BitVec 24) ((_ repeat 3) ((_ extract 7 0) y)))
        (define-fun e () Bool (and (bvule x y) (distinct x y #b00000000) (=> p (= x y) p)))
        (define-fun f () (_ BitVec 8) (ite (xor p (bvsgt x y)) (_ bv200 8) (bvnand x y)))
        (define-fun g () (_ BitVec 1) (bvcomp x y))
        (assert (not p))
        (check-sat)
        (get-model)
        (exit)
        "#,
    )
    .unwrap();
    assert_eq!(s.symbols.len(), 3);
    assert_eq!(s.assertions.len(), 1);
    let w8 = Width::W8;
    let x = cx.find_symbol(&SymbolKey::from("x")).unwrap();
    let y = cx.find_symbol(&SymbolKey::from("y")).unwrap();
    let p = cx.find_symbol(&SymbolKey::from("p")).unwrap();
    assert_eq!(cx.width(p).unwrap(), Width::W1);
    let d = |n: &str| s.definition(n).unwrap();
    // `let` is parallel: `x` inside `t` is the outer one.
    let o = ParseOptions::width(w8);
    let want = cx.parse("x + y", &o).unwrap();
    assert_eq!(d("a"), want);
    let _ = (x, y);
    // bvsmod against its definition, exhaustively at 8 bits for a few divisors.
    for xv in 0..256u64 {
        for yv in [0u64, 1, 3, 0x7f, 0x80, 0xfd, 0xff] {
            let env: BTreeMap<SymbolKey, BitVec> = [
                (SymbolKey::from("x"), BitVec::from_u64(w8, xv).unwrap()),
                (SymbolKey::from("y"), BitVec::from_u64(w8, yv).unwrap()),
                (SymbolKey::from("p"), BitVec::zero(Width::W1)),
            ]
            .into_iter()
            .collect();
            let got = cx.eval(&[d("b")], &env).unwrap()[0].to_u64().unwrap();
            let (s8, t8) = (xv as u8 as i8 as i64, yv as u8 as i8 as i64);
            let want = if t8 == 0 {
                s8
            } else {
                let r = s8.rem_euclid(t8.abs());
                // The result takes the divisor's sign (zero stays zero).
                if r != 0 && t8 < 0 { r + t8 } else { r }
            };
            assert_eq!(got, (want as u8) as u64, "smod({s8}, {t8})");
        }
    }
    assert_eq!(cx.width(d("c")).unwrap().bits(), 16);
    assert_eq!(cx.width(d("d")).unwrap().bits(), 24);
    assert_eq!(cx.width(d("e")).unwrap().bits(), 1);
    assert_eq!(cx.width(d("g")).unwrap().bits(), 1);
    let env: BTreeMap<SymbolKey, BitVec> = [
        (SymbolKey::from("x"), BitVec::from_u64(w8, 5).unwrap()),
        (SymbolKey::from("y"), BitVec::from_u64(w8, 9).unwrap()),
        (SymbolKey::from("p"), BitVec::one(Width::W1)),
    ]
    .into_iter()
    .collect();
    let v = |cx: &mut Context, n: &str| cx.eval(&[d(n)], &env).unwrap()[0].to_u64().unwrap();
    assert_eq!(v(&mut cx, "c"), 40); // rotl(5, 3)
    assert_eq!(v(&mut cx, "d"), 0x090909);
    // p ⇒ ((x = y) ⇒ p) holds; 5 ≤ 9; 5, 9, 0 distinct.
    assert_eq!(v(&mut cx, "e"), 1);
    // p xor (5 >s 9) = 1: the 200 arm.
    assert_eq!(v(&mut cx, "f"), 200);
    assert_eq!(v(&mut cx, "g"), 0);
}

#[test]
fn import_rejects_what_it_does_not_model_without_panicking() {
    let bad = [
        "(declare-const x (_ BitVec 0))",
        "(declare-const x (_ BitVec 513))",
        "(declare-const x (_ BitVec 99999999999))",
        "(declare-const x Int)",
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))",
        "(define-fun f ((a (_ BitVec 8))) (_ BitVec 8) a)",
        "(declare-const x (_ BitVec 8)) (declare-const x (_ BitVec 8))",
        "(assert y)",
        "(declare-const x (_ BitVec 8)) (assert x)",
        "(declare-const x (_ BitVec 8)) (define-fun a () (_ BitVec 16) x)",
        "(declare-const x (_ BitVec 8)) (define-fun a () (_ BitVec 8) (bvadd x))",
        "(declare-const x (_ BitVec 8)) (define-fun a () (_ BitVec 8) ((_ extract 8 0) x))",
        "(declare-const x (_ BitVec 8)) (define-fun a () (_ BitVec 8) ((_ extract 1 2) x))",
        "(declare-const x (_ BitVec 8)) (define-fun a () (_ BitVec 16) (bvadd x #x0001))",
        "(define-fun a () (_ BitVec 8) (_ bv256 8))",
        "(define-fun a () (_ BitVec 8) 5)",
        "(define-fun a () (_ BitVec 8) #xg0)",
        "(define-fun a () (_ BitVec 8) (bvfoo #x00 #x00))",
        "(define-fun a () Bool (= true #b1))",
        "(push 1)",
        "(check-sat",
        ")",
        "(set-info :x |unterminated",
        "(set-info :x \"unterminated",
        "()",
        "(declare-const x (_ BitVec 400)) (define-fun a () (_ BitVec 800) (concat x x))",
        "(declare-const x (_ BitVec 400)) (define-fun a () (_ BitVec 800) ((_ repeat 2) x))",
    ];
    for src in bad {
        let mut cx = Context::new();
        assert!(import(&mut cx, src).is_err(), "{src}");
    }
    // Nesting beyond the cap is refused, not a stack overflow.
    let deep = format!(
        "(declare-const x (_ BitVec 8)) (define-fun a () (_ BitVec 8) {}x{})",
        "(bvnot ".repeat(100_000),
        ")".repeat(100_000)
    );
    assert!(import(&mut Context::new(), &deep).is_err());
    // Mutations of a valid script: any result, never a panic.
    let mut cx = Context::new();
    let e = cx.parse(
        "popcnt(x) + rotl(x, y) * clz(y) - pdep(x, y) + (x <s y)",
        &ParseOptions::width(Width::W8),
    );
    let e = match e {
        Ok(e) => e,
        Err(_) => cx
            .parse("x + rotl(x, y) * y", &ParseOptions::width(Width::W8))
            .unwrap(),
    };
    let smt = export(&mut cx, &[e]).unwrap();
    let mut rng = Rng(9);
    let bytes = smt.as_bytes();
    for _ in 0..3000 {
        let mut m = bytes.to_vec();
        for _ in 0..1 + rng.below(4) {
            let at = rng.below(m.len() as u64) as usize;
            match rng.below(3) {
                0 => {
                    m.remove(at);
                }
                1 => m.insert(at, b"()|#x_ 90abvn"[rng.below(13) as usize]),
                _ => m[at] = b"()|#x_ 90abvn"[rng.below(13) as usize],
            }
        }
        if let Ok(s) = std::str::from_utf8(&m) {
            let _ = import(&mut Context::new(), s);
        }
    }
}

#[test]
fn equivalence_queries_are_well_formed() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let a = cx.parse("(x ^ y) + 2 * (x & y)", &o).unwrap();
    let b = cx.parse("x + y", &o).unwrap();
    let q = equivalence_query(&mut cx, a, b).unwrap();
    assert!(q.starts_with("(set-logic QF_BV)"));
    assert!(q.ends_with("(assert (not (= root0 root1)))\n(check-sat)\n"));
    let s = import(&mut Context::new(), &q).unwrap();
    assert_eq!(s.assertions.len(), 1);
    let narrow = cx.symbol("z", Width::W8).unwrap();
    assert!(equivalence_query(&mut cx, a, narrow).is_err());
}

/// z3 on `PATH` evaluates exported expressions exactly as bitwright does. Needs z3; skipped
/// (with a note) when it is not installed.
#[test]
#[ignore = "needs z3 on PATH"]
fn z3_agrees_with_the_evaluator() {
    use std::io::Write as _;
    use std::process::{Command, Stdio};
    let run = |script: &str| -> Option<String> {
        let mut child = Command::new("z3")
            .args(["-in", "-smt2"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .ok()?;
        child.stdin.take()?.write_all(script.as_bytes()).ok()?;
        let out = child.wait_with_output().ok()?;
        Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
    };
    if run("(check-sat)").is_none() {
        eprintln!("z3 is not on PATH; skipped");
        return;
    }
    let mut rng = Rng(0x23);
    let mut script = String::new();
    let mut expected = 0;
    for i in 0..400u64 {
        let max_w = [5, 8, 33, 64, 100][i as usize % 5];
        let mut g = gen_w(0x2300 + i, max_w);
        let mut cx = Context::new();
        let w = 1 + g.rng.below(u64::from(max_w)) as u16;
        let (e, _) = g.expr(&mut cx, w, 4);
        let env = point(&mut cx, &[e], &mut rng);
        let want = cx.eval(&[e], &env).unwrap()[0];
        // One script per case, separated by push/pop: the value is forced by the symbols'
        // values, so `(not (= root0 want))` must be unsat.
        script.push_str("(push 1)\n");
        script.push_str(&export(&mut cx, &[e]).unwrap());
        for id in cx.symbols_in(&[e]).unwrap() {
            let key = cx.symbol_key(id).unwrap().clone();
            let name = export::symbol_name(&key, id.index());
            script.push_str(&format!(
                "(assert (= {name} {}))\n",
                export::literal(&env[&key])
            ));
        }
        script.push_str(&format!(
            "(assert (not (= root0 {})))\n(check-sat)\n(pop 1)\n",
            export::literal(&want)
        ));
        expected += 1;
    }
    let out = run(&format!("(set-logic QF_BV)\n{script}")).unwrap();
    let answers: Vec<&str> = out.lines().collect();
    assert_eq!(answers.len(), expected, "{out}");
    for (k, a) in answers.iter().enumerate() {
        assert_eq!(*a, "unsat", "case {k}");
    }
}

// ----- rule obligations -------------------------------------------------------------------------

use crate::rules::RuleProgram;
use crate::rules::corpus::{CORE, EQSAT};
use crate::rules::eval::{Val, eval, eval_lets};

/// The built-in rules, and a few unsound ones (which compile: soundness is the checker's).
fn programs() -> Vec<RuleProgram> {
    let unsound = "bitwright 1;
        group bad {
            rule add_is_or<W>(x: W, y: W) { x + y => x | y }
            rule wrong_guard<W>(x: W, c: const W) { (x & c) >>u 1 => x >>u 1 if zero_bits(x, c) }
            rule off_by_one<W>(x: W) { udiv(x, 2) => x >>u 2 }
        }";
    // Every construct of the rule IR, soundness aside.
    let coverage = "bitwright 1;
        group cover {
            identity cmp_ext<W>(x: W, y: W) { (x >u y) | (x >=s y) <=> (y <u x) ^ (x <=s y) }
            identity cmp_ext2<W>(x: W, y: W) { (x >=u y) & (x >s y) <=> (y <=u x) & (y <s x) }
            rule guards<W>(x: W, y: W, c: const W, d: const W) {
                ((x & c) | y) ^ d => x
                if (is_shifted_mask(c) || is_lowmask(d)) && !(c == d) || (nonzero(x) && one_bits(y, c))
            }
            rule guards2<W>(x: W, c: const W) { x ^ c => x if is_pow2(c) || proves(x >u c) }
            identity unary<W>(x: W) { popcnt(x) + clz(x) <=> ctz(x) - bitrev(~x) + (-x) }
            identity bytes<W>(x: W) where W % 8 == 0 { bswap(x) <=> x }
            identity binary<W>(x: W, y: W) {
                umulhi(x, y) - smulhi(x, y) <=> pdep(x, y) ^ pext(y, x) ^ rotl(x, y) ^ rotr(y, x)
            }
            identity division<W>(x: W, y: W) {
                udiv(x, y) + urem(x, y) <=> sdiv(x, y) * srem(y, x) | (x >>s y) & (y << x)
            }
            identity literals<W>(x: W) where W >= 4 {
                x + smin_lit <=> (x & smax_lit) | lowmask(W - 2) | bit(W - 1) | (W - 1)
            }
            identity casts<W, U>(a: W) where W < U, U <= 2 * W {
                zext<U>(a) <=> concat(extract<0, U - W>(sext<U>(a)), a)
            }
            identity sel<W>(c: 1, x: W, y: W) { select(c, x, y) <=> select(~c, y, x) }
            rule lets<W>(x: W, c: const W) { x * c => x << k if nonzero(c) let k: W = ctz(c) }
        }";
    [CORE, EQSAT, unsound, coverage]
        .iter()
        .map(|s| RuleProgram::compile(s).unwrap())
        .collect()
}

/// Width assignments to check: admitted, every width in a fixed set, at most `cap` of them.
fn assignments(rule: &crate::rules::Rule, cap: usize) -> Vec<Vec<u16>> {
    const SET: &[u16] = &[1, 2, 3, 4, 5, 7, 8, 13, 16, 32, 33, 64, 65, 128, 256, 512];
    let all: Vec<Vec<u16>> = crate::rules::compile::width_assignments(rule)
        .into_iter()
        .filter(|ws| ws.iter().all(|w| SET.contains(w)) && rule.admits(ws))
        .collect();
    let stride = all.len().div_ceil(cap).max(1);
    all.into_iter().step_by(stride).collect()
}

#[test]
fn obligations_state_what_the_checker_evaluates() {
    let mut rng = Rng(0x0b1);
    let mut checked = 0;
    for program in programs() {
        for rule in program.rules() {
            for ws in assignments(rule, 12) {
                let smt = rule_obligation(rule, &ws).unwrap();
                let mut cx = Context::new();
                let script = import(&mut cx, &smt).unwrap_or_else(|e| panic!("{e}\n{smt}"));
                assert_eq!(script.assertions.len(), 2);
                let def = |n: u16| script.definition(&format!("bw!{n}")).unwrap();
                let (lhs, rhs) = (def(rule.lhs), def(rule.rhs));
                for _ in 0..16 {
                    let params: Vec<BitVec> = rule
                        .params
                        .iter()
                        .map(|p| {
                            let w = Width::new(p.width.eval(&ws) as u16).unwrap();
                            let limbs: Vec<u64> = (0..8).map(|_| rng.next()).collect();
                            let v = BitVec::wrapping_from_limbs(w, &limbs);
                            // Small values often, so guards fire.
                            if rng.chance(1, 2) {
                                BitVec::wrapping_from_u64(w, rng.below(4))
                            } else {
                                v
                            }
                        })
                        .collect();
                    let env: BTreeMap<SymbolKey, BitVec> = rule
                        .params
                        .iter()
                        .zip(&params)
                        .map(|(p, v)| (SymbolKey::from(p.name.as_str()), *v))
                        .collect();
                    let lets = eval_lets(rule, &ws, &params);
                    let want = |n: u16| eval(rule, n, &ws, &params, &lets).unwrap();
                    let got = cx.eval(&[lhs, rhs], &env).unwrap();
                    assert_eq!(Val::Bv(got[0]), want(rule.lhs), "{} {ws:?}", rule.name);
                    assert_eq!(Val::Bv(got[1]), want(rule.rhs), "{} {ws:?}", rule.name);
                    if let Some(g) = rule.guard {
                        let gv = cx.eval(&[def(g)], &env).unwrap()[0];
                        assert_eq!(!gv.is_zero(), want(g).truthy(), "{} {ws:?}", rule.name);
                    }
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 5000, "{checked}");
    // Not at widths where the rule does not apply.
    let p = &programs()[2];
    let r = p.rule("bad::add_is_or").unwrap();
    assert!(rule_obligation(r, &[0]).is_err());
    assert!(rule_obligation(r, &[513]).is_err());
    assert!(rule_obligation(r, &[8, 8]).is_err());
}

/// Every built-in rule proved by z3 at widths up to 512, and the unsound ones refuted. Needs z3
/// on `PATH`; skipped (with a note) when it is not installed.
#[test]
#[ignore = "needs z3 on PATH; minutes"]
fn z3_proves_the_built_in_rules() {
    use std::io::Write as _;
    use std::process::{Command, Stdio};
    let solve = |script: &str| -> Option<String> {
        let mut child = Command::new("z3")
            .args(["-in", "-smt2", "-T:60"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .ok()?;
        child.stdin.take()?.write_all(script.as_bytes()).ok()?;
        let out = child.wait_with_output().ok()?;
        Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
    };
    if solve("(check-sat)").is_none() {
        eprintln!("z3 is not on PATH; skipped");
        return;
    }
    let mut failures = Vec::new();
    // A solver that gives up (wide division and shifts bit-blast to large circuits) proves
    // nothing but refutes nothing either: tolerated above 64 bits, and only rarely.
    let mut gave_up = Vec::new();
    let mut proved = 0;
    // The built-in rules must be proved and the unsound ones refuted; the coverage rules are
    // neither.
    for (k, program) in programs().iter().enumerate().take(3) {
        for rule in program.rules() {
            let unsound = k == 2;
            let mut refuted = false;
            for ws in assignments(rule, 8) {
                let answer = solve(&rule_obligation(rule, &ws).unwrap()).unwrap();
                match (answer.as_str(), unsound) {
                    ("unsat", false) => proved += 1,
                    ("sat", true) => refuted = true,
                    ("unsat", true) => {}
                    ("unknown" | "timeout", _) if ws.iter().any(|&w| w > 64) => {
                        gave_up.push(format!("{} {ws:?}", rule.name));
                    }
                    (a, _) => failures.push(format!("{} {ws:?}: {a}", rule.name)),
                }
            }
            if unsound && !refuted {
                failures.push(format!("{}: never refuted", rule.name));
            }
        }
    }
    eprintln!(
        "{proved} obligations proved; z3 gave up on {}: {gave_up:?}",
        gave_up.len()
    );
    assert!(failures.is_empty(), "{failures:#?}");
    assert!(gave_up.len() * 50 < proved, "{gave_up:#?}");
}

// ----- regressions from the M8 review ------------------------------------------------------------

#[test]
fn reserved_names_are_never_used_as_symbols() {
    let w = Width::W8;
    for name in [
        "and", "true", "false", "_", "bvadd", "let", "bv12", "=", "BitVec",
    ] {
        let mut cx = Context::new();
        let x = cx.symbol(name, w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let o = cx.bin(crate::BinOp::Or, x, y).unwrap();
        let e = cx.bin(crate::BinOp::And, x, o).unwrap();
        let smt = export(&mut cx, &[e]).unwrap();
        assert!(!smt.contains(&format!("|{name}|")), "{name}:\n{smt}");
        let mut other = Context::new();
        let back = import(&mut other, &smt)
            .unwrap_or_else(|err| panic!("{name}: {err}\n{smt}"))
            .definition("root0")
            .unwrap();
        assert_eq!(other.width(back).unwrap(), w);
    }
    // Rule parameters likewise.
    let p = RuleProgram::compile(
        "bitwright 1;\ngroup g {\n    #[allow(BW0407)]\n    rule r<W>(and: W, y: W) { and & (and | y) => and }\n}\n",
    )
    .unwrap();
    let smt = rule_obligation(&p.rules()[0], &[8]).unwrap();
    assert!(!smt.contains("|and|"), "{smt}");
    import(&mut Context::new(), &smt).unwrap();
}

#[test]
fn wide_expansions_stay_small() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::new(512).unwrap());
    let e = cx
        .parse("pdep(x, y) + clz(x) + pext(y, x) + ctz(y)", &o)
        .unwrap();
    let smt = export(&mut cx, &[e]).unwrap();
    // Every helper was a 512-bit binary literal before (about 2 MB here).
    assert!(smt.len() < 400_000, "{}", smt.len());
}

/// z3 answers `unsat` for a true equality over symbols named after SMT-LIB built-ins.
#[test]
#[ignore = "needs z3 on PATH"]
fn z3_proves_equalities_over_reserved_names() {
    use std::io::Write as _;
    use std::process::{Command, Stdio};
    let Ok(mut child) = Command::new("z3")
        .args(["-in", "-smt2"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
    else {
        eprintln!("z3 is not on PATH; skipped");
        return;
    };
    let mut script = String::new();
    for name in ["and", "true", "false", "_"] {
        let mut cx = Context::new();
        let x = cx.symbol(name, Width::W8).unwrap();
        let y = cx.symbol("y", Width::W8).unwrap();
        let o = cx.bin(crate::BinOp::Or, x, y).unwrap();
        let e = cx.bin(crate::BinOp::And, x, o).unwrap();
        script.push_str(&equivalence_query(&mut cx, e, x).unwrap());
        script.push_str("(reset)\n");
    }
    child
        .stdin
        .take()
        .unwrap()
        .write_all(script.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    let out = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.lines().collect::<Vec<_>>(), ["unsat"; 4], "{out}");
}

#[test]
fn equivalence_under_constraints_asserts_exactly_the_relied_on_ones() {
    use crate::Assumptions;
    let o = ParseOptions::width(Width::W16);
    let mut cx = Context::new();
    let mut a = Assumptions::new();
    let p0 = cx.parse("(p & 7) == 0", &o).unwrap();
    let p1 = cx.parse("x <u 100", &o).unwrap();
    let i0 = a.assume_true(&mut cx, p0).unwrap();
    a.assume_true(&mut cx, p1).unwrap();
    let e = cx.parse("p & 0xfff8", &o).unwrap();
    let p = cx.parse("p", &o).unwrap();
    let out = crate::engine::Engine::standard()
        .run(
            &mut cx,
            &[e],
            crate::engine::Run::default().with_assumptions(&a),
        )
        .unwrap();
    let r = out.roots[0];
    assert_eq!(r.expr, p);
    assert!(r.relies_on.may_use(i0));
    let q = super::equivalence_query_under(&mut cx, e, r.expr, &a, r.relies_on).unwrap();
    // The alignment predicate asserted true, and nothing about x.
    assert!(q.contains("(define-fun root2 () (_ BitVec 1)"), "{q}");
    assert!(q.contains("(assert (= (bvand root2 #b1) #b1))"), "{q}");
    assert!(!q.contains("root3"), "{q}");
    assert!(q.ends_with("(assert (not (= root0 root1)))\n(check-sat)\n"));
}

/// Every rewrite made under random constraints is proved by z3 under the constraints it relies
/// on. Needs z3; skipped (with a note) when it is not installed.
#[test]
#[ignore = "needs z3 on PATH"]
fn z3_proves_rewrites_under_the_constraints_they_rely_on() {
    use crate::Assumptions;
    use std::io::Write as _;
    use std::process::{Command, Stdio};
    let run = |script: &str| -> Option<String> {
        let mut child = Command::new("z3")
            .args(["-in", "-smt2"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .ok()?;
        child.stdin.take()?.write_all(script.as_bytes()).ok()?;
        let out = child.wait_with_output().ok()?;
        Some(String::from_utf8_lossy(&out.stdout).trim().to_string())
    };
    if run("(check-sat)").is_none() {
        eprintln!("z3 is not on PATH; skipped");
        return;
    }
    let engine = crate::engine::Engine::standard();
    let mut script = String::from("(set-logic QF_BV)\n");
    let mut relied = 0;
    let mut needed = 0;
    for i in 0..2000u64 {
        let max_w = [8, 16, 32, 64][i as usize % 4];
        let mut g = gen_w(0xc5_0000 + i, max_w);
        let mut cx = Context::new();
        let w = 1 + g.rng.below(u64::from(max_w)) as u16;
        let mut a = Assumptions::new();
        for _ in 0..3 {
            let (x, _) = g.expr(&mut cx, w, 2);
            // Small constants, so the constraints bound something.
            let k = BitVec::wrapping_from_u64(crate::testutil::width(w), g.rng.below(64));
            let k = cx.constant(&k).unwrap();
            let op = crate::CmpOpExt::ALL[g.rng.below(10) as usize];
            let p = cx.cmp(op, x, k).unwrap();
            a.assume_true(&mut cx, p).unwrap();
        }
        if a.is_infeasible() {
            continue;
        }
        let roots: Vec<Expr> = (0..3).map(|_| g.expr(&mut cx, w, 4).0).collect();
        let out = engine
            .run(
                &mut cx,
                &roots,
                crate::engine::Run::default().with_assumptions(&a),
            )
            .unwrap();
        for (e, r) in roots.iter().zip(&out.roots) {
            if !r.changed || r.relies_on.is_none() {
                continue;
            }
            relied += 1;
            let q = super::equivalence_query_under(&mut cx, *e, r.expr, &a, r.relies_on).unwrap();
            script.push_str("(push 1)\n");
            script.push_str(&q.replace("(set-logic QF_BV)\n", ""));
            script.push_str("(pop 1)\n");
            // Without the constraints, count how many genuinely needed them.
            let q = equivalence_query(&mut cx, *e, r.expr).unwrap();
            if run(&q).as_deref() == Some("sat") {
                needed += 1;
            }
        }
    }
    let out = run(&script).unwrap();
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), relied, "{out}");
    assert!(lines.iter().all(|l| *l == "unsat"), "{out}");
    assert!(
        relied > 60 && needed > 40,
        "relied {relied}, needed {needed}"
    );
}
