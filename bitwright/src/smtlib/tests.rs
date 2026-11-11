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

/// A chain of `let`s, each in the previous one's body (as z3 prints a large term), imports
/// however long it is, with each name the innermost binding's (and the outer one again after
/// the inner one's body).
#[test]
fn long_let_chains_import() {
    let n = 200_000usize;
    let mut s = String::from("(declare-const x (_ BitVec 8)) (define-fun a () (_ BitVec 8) ");
    for k in 0..n {
        let prev = if k == 0 {
            "x".to_string()
        } else {
            format!("(bvadd v{} #x01)", k - 1)
        };
        s += &format!("(let ((v{k} {prev})) ");
    }
    s += &format!("v{})", n - 1);
    s.insert_str(s.len() - 1, &")".repeat(n));
    let mut cx = Context::new();
    let imp = import(&mut cx, &s).unwrap();
    let w8 = Width::W8;
    let env: BTreeMap<SymbolKey, BitVec> =
        [(SymbolKey::from("x"), BitVec::from_u64(w8, 5).unwrap())]
            .into_iter()
            .collect();
    let a = imp.definition("a").unwrap();
    assert_eq!(
        cx.eval(&[a], &env).unwrap()[0].to_u64(),
        Some(((5 + n - 1) % 256) as u64)
    );
    let mut cx = Context::new();
    let imp = import(
        &mut cx,
        "(declare-const x (_ BitVec 8))
         (define-fun a () (_ BitVec 8)
           (let ((t x)) (let ((u t)) (bvadd (let ((t #x02)) (bvmul t u)) t))))",
    )
    .unwrap();
    let want = cx.parse("x * 3", &ParseOptions::width(w8)).unwrap();
    let got = imp.definition("a").unwrap();
    for xv in 0..256u64 {
        let env: BTreeMap<SymbolKey, BitVec> =
            [(SymbolKey::from("x"), BitVec::from_u64(w8, xv).unwrap())]
                .into_iter()
                .collect();
        assert_eq!(
            cx.eval(&[got], &env).unwrap(),
            cx.eval(&[want], &env).unwrap()
        );
    }
    // Nesting in a binding still counts.
    let deep = format!(
        "(declare-const x (_ BitVec 8)) (define-fun a () (_ BitVec 8) {}x{})",
        "(let ((t ".repeat(1000),
        ")) t)".repeat(1000)
    );
    assert!(import(&mut Context::new(), &deep).is_err());
}

/// z3's rotations by a term, `ext_rotate_left` and `ext_rotate_right`, rotate by the count
/// modulo the width (exhaustively at a few widths).
#[test]
fn z3_rotations_by_a_term_import() {
    for w in [1u16, 3, 5, 8] {
        let mut cx = Context::new();
        let imp = import(
            &mut cx,
            &format!(
                "(declare-const x (_ BitVec {w})) (declare-const y (_ BitVec {w}))
                 (define-fun l () (_ BitVec {w}) (ext_rotate_left x y))
                 (define-fun r () (_ BitVec {w}) (ext_rotate_right x y))"
            ),
        )
        .unwrap();
        let (l, r) = (imp.definition("l").unwrap(), imp.definition("r").unwrap());
        let width = Width::new(w).unwrap();
        let m = (1u64 << w) - 1;
        for xv in 0..1u64 << w {
            for yv in 0..1u64 << w {
                let env: BTreeMap<SymbolKey, BitVec> = [
                    (SymbolKey::from("x"), BitVec::from_u64(width, xv).unwrap()),
                    (SymbolKey::from("y"), BitVec::from_u64(width, yv).unwrap()),
                ]
                .into_iter()
                .collect();
                let k = yv % u64::from(w);
                let rotl = ((xv << k) | (xv >> ((u64::from(w) - k) % u64::from(w)))) & m;
                let rotr = ((xv >> k) | (xv << ((u64::from(w) - k) % u64::from(w)))) & m;
                let got = cx.eval(&[l, r], &env).unwrap();
                assert_eq!(got[0].to_u64(), Some(rotl), "rotl({xv}, {yv}) at {w}");
                assert_eq!(got[1].to_u64(), Some(rotr), "rotr({xv}, {yv}) at {w}");
            }
        }
    }
}

#[test]
fn import_rejects_what_it_does_not_model_without_panicking() {
    let bad = [
        "(declare-const x (_ BitVec 0))",
        "(declare-const x (_ BitVec 513))",
        "(declare-const x (_ BitVec 99999999999))",
        "(declare-const x Int)",
        "(declare-fun f ((Array (_ BitVec 8) (_ BitVec 8))) (_ BitVec 8))",
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8)) (define-fun a () (_ BitVec 8) (f #b1))",
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8)) (declare-const f Bool)",
        "(define-sort Word (X) (_ BitVec 8))",
        "(define-sort Bool () (_ BitVec 8))",
        "(define-fun f ((a (_ BitVec 8))) (_ BitVec 8) a) (define-fun g () (_ BitVec 8) (f))",
        "(define-fun f ((a (_ BitVec 8))) (_ BitVec 8) a) (define-fun g () (_ BitVec 8) (f #b1))",
        "(define-fun f ((a (_ BitVec 8))) (_ BitVec 4) a) (define-fun g () (_ BitVec 4) (f #x01))",
        "(define-fun f ((a (_ BitVec 8))) (_ BitVec 8) (f a)) (define-fun g () (_ BitVec 8) (f #x01))",
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

// ----- solvers ----------------------------------------------------------------------------------

/// An SMT solver the ignored suites run exported scripts through, when it is on `PATH`. Each
/// suite runs once per solver, so an export that only one of them accepts fails.
#[derive(Copy, Clone, Debug)]
enum Solver {
    Z3,
    Bitwuzla,
}

impl Solver {
    fn name(self) -> &'static str {
        match self {
            Solver::Z3 => "z3",
            Solver::Bitwuzla => "bitwuzla",
        }
    }

    /// The solver's output for `script` read from stdin, with `limit_ms` per `check-sat` (after
    /// which it answers `unknown`); its stderr is appended when it fails. A solver does not
    /// always stop at its own limit (z3 4.8 runs for hours on some 512-bit queries), so with a
    /// limit it is also killed after twice that per `check-sat` and ten seconds more; its output
    /// then ends with `timeout`. `None` if it cannot be started.
    fn run(self, script: &str, limit_ms: Option<u32>) -> Option<String> {
        use std::io::{Read, Write as _};
        use std::process::{Command, Stdio};
        use std::time::{Duration, Instant};
        fn drain(mut r: impl Read + Send + 'static) -> std::thread::JoinHandle<Vec<u8>> {
            std::thread::spawn(move || {
                let mut b = Vec::new();
                let _ = r.read_to_end(&mut b);
                b
            })
        }
        let mut cmd = Command::new(self.name());
        match (self, limit_ms) {
            (Solver::Z3, l) => {
                cmd.args(["-in", "-smt2"]);
                cmd.args(l.map(|ms| format!("-t:{ms}")));
            }
            (Solver::Bitwuzla, l) => {
                cmd.args(l.map(|ms| format!("--time-limit-per={ms}")));
            }
        }
        let checks = script.matches("(check-sat)").count() as u64;
        let deadline = limit_ms
            .map(|ms| Instant::now() + Duration::from_millis(2 * u64::from(ms) * checks + 10_000));
        let mut child = cmd
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .ok()?;
        // Fed and drained on their own threads, so the deadline is watched while it works.
        let mut stdin = child.stdin.take()?;
        let script = script.to_owned();
        let feed = std::thread::spawn(move || stdin.write_all(script.as_bytes()));
        let (out, err) = (drain(child.stdout.take()?), drain(child.stderr.take()?));
        let status = loop {
            if let Some(status) = child.try_wait().ok()? {
                break Some(status);
            }
            if deadline.is_some_and(|d| Instant::now() >= d) {
                let _ = child.kill();
                let _ = child.wait();
                break None;
            }
            std::thread::sleep(Duration::from_millis(5));
        };
        let _ = feed.join();
        let out = out.join().ok()?;
        let mut s = String::from_utf8_lossy(&out).trim().to_string();
        match status {
            Some(status) if status.success() => {}
            Some(_) => {
                s.push('\n');
                s.push_str(String::from_utf8_lossy(&err.join().ok()?).trim());
            }
            None => s = format!("{s}\ntimeout").trim_start().to_string(),
        }
        Some(s)
    }

    /// Whether the solver can be started; prints a note when it cannot.
    fn available(self) -> bool {
        let ok = self.run("(check-sat)", None).is_some();
        if !ok {
            eprintln!("{} is not on PATH; skipped", self.name());
        }
        ok
    }
}

/// A solver evaluates exported expressions exactly as bitwright does. Skipped (with a note) for
/// a solver that is not installed.
fn solver_agrees_with_the_evaluator(solver: Solver) {
    if !solver.available() {
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
    let out = solver
        .run(&format!("(set-logic QF_BV)\n{script}"), None)
        .unwrap();
    let answers: Vec<&str> = out.lines().collect();
    assert_eq!(answers.len(), expected, "{}: {out}", solver.name());
    for (k, a) in answers.iter().enumerate() {
        assert_eq!(*a, "unsat", "{}: case {k}", solver.name());
    }
}

#[test]
#[ignore = "needs z3 on PATH"]
fn z3_agrees_with_the_evaluator() {
    solver_agrees_with_the_evaluator(Solver::Z3);
}

#[test]
#[ignore = "needs bitwuzla on PATH"]
fn bitwuzla_agrees_with_the_evaluator() {
    solver_agrees_with_the_evaluator(Solver::Bitwuzla);
}

/// Every floating-point operation, under every rounding mode, on random operands of each format:
/// the solver's FloatingPoint theory computes exactly bitwright's result (so `unsat` for any
/// other).
fn solver_agrees_with_floating_point(solver: Solver, formats: &[crate::fp::FpFormat]) {
    use crate::fp::{FpCmpOp, FpFormat, FpOp, FpTest, RoundingMode};
    if !solver.available() {
        return;
    }
    let mut rng = Rng(0x24);
    let mut script = String::new();
    let mut expected = 0;
    for &f in formats {
        for round in 0..6 {
            let mut cx = Context::new();
            let w = f.width();
            let (a, b, c) = (
                cx.symbol("a", w).unwrap(),
                cx.symbol("b", w).unwrap(),
                cx.symbol("c", w).unwrap(),
            );
            let i = cx.symbol("i", Width::new(24).unwrap()).unwrap();
            let rm = RoundingMode::ALL[round % 5];
            let other = if f == FpFormat::F32 {
                FpFormat::F64
            } else {
                FpFormat::F32
            };
            let mut exprs = vec![
                cx.fp(FpOp::Add(rm), f, &[a, b]).unwrap(),
                cx.fp_sub(f, rm, a, b).unwrap(),
                cx.fp(FpOp::Mul(rm), f, &[a, b]).unwrap(),
                cx.fp(FpOp::Div(rm), f, &[a, b]).unwrap(),
                cx.fp(FpOp::Fma(rm), f, &[a, b, c]).unwrap(),
                cx.fp(FpOp::Sqrt(rm), f, &[a]).unwrap(),
                cx.fp(FpOp::RoundToIntegral(rm), f, &[a]).unwrap(),
                cx.fp(FpOp::Rem, f, &[a, b]).unwrap(),
                cx.fp(FpOp::Min, f, &[a, b]).unwrap(),
                cx.fp(FpOp::Max, f, &[a, b]).unwrap(),
                cx.fp(FpOp::Convert { to: other, rm }, f, &[a]).unwrap(),
                cx.fp(FpOp::FromSInt(rm), f, &[i]).unwrap(),
                cx.fp(FpOp::FromUInt(rm), f, &[i]).unwrap(),
                cx.fp(FpOp::ToSInt(rm, Width::W16), f, &[a]).unwrap(),
                cx.fp(FpOp::ToUInt(rm, Width::W8), f, &[a]).unwrap(),
                cx.fp(FpOp::ToSInt(rm, Width::W64), f, &[a]).unwrap(),
            ];
            for op in [FpCmpOp::Eq, FpCmpOp::Lt, FpCmpOp::Le] {
                exprs.push(cx.fp_cmp(f, op, a, b).unwrap());
            }
            for t in [FpTest::Nan, FpTest::Subnormal, FpTest::Negative] {
                exprs.push(cx.fp_test(f, t, a).unwrap());
            }
            for _ in 0..12 {
                let env: Vec<(SymbolKey, BitVec)> = vec![
                    (SymbolKey::from("a"), crate::fp::tests::sample(&mut rng, f)),
                    (SymbolKey::from("b"), crate::fp::tests::sample(&mut rng, f)),
                    (SymbolKey::from("c"), crate::fp::tests::sample(&mut rng, f)),
                    (
                        SymbolKey::from("i"),
                        BitVec::wrapping_from_u64(
                            Width::new(24).unwrap(),
                            rng.next() >> rng.below(40),
                        ),
                    ),
                ];
                for &e in &exprs {
                    let want = cx.eval(&[e], &env[..]).unwrap()[0];
                    script.push_str("(push 1)\n");
                    script.push_str(&export(&mut cx, &[e]).unwrap());
                    for id in cx.symbols_in(&[e]).unwrap() {
                        let key = cx.symbol_key(id).unwrap().clone();
                        let name = export::symbol_name(&key, id.index());
                        let v = env.iter().find(|(k, _)| *k == key).unwrap().1;
                        script.push_str(&format!("(assert (= {name} {}))\n", export::literal(&v)));
                    }
                    script.push_str(&format!(
                        "(assert (not (= root0 {})))\n(check-sat)\n(pop 1)\n",
                        export::literal(&want)
                    ));
                    expected += 1;
                }
            }
        }
    }
    let out = solver
        .run(&format!("(set-logic ALL)\n{script}"), None)
        .unwrap();
    let answers: Vec<&str> = out.lines().collect();
    assert_eq!(answers.len(), expected, "{}: {out}", solver.name());
    let wrong: Vec<usize> = (0..expected).filter(|&k| answers[k] != "unsat").collect();
    assert!(
        wrong.is_empty(),
        "{}: cases {wrong:?} are not unsat",
        solver.name()
    );
}

#[test]
#[ignore = "needs z3 on PATH"]
fn z3_agrees_with_floating_point() {
    use crate::fp::FpFormat;
    let f = |eb, sb| FpFormat::new(eb, sb).unwrap();
    // Not the tiniest formats, where z3 5.1.0 is wrong and bitwright agrees with the independent
    // reference on every input: its fma at precision 3 or less (in (3, 3), fma(0.375, 2^-4, +0)
    // gives 0.125, not +0), and its roundToIntegral with a 2-bit exponent (in (2, 2),
    // roundToIntegral(RNE, 0.5) gives 1.0, not +0).
    solver_agrees_with_floating_point(
        Solver::Z3,
        &[
            f(3, 4),
            f(4, 4),
            FpFormat::F16,
            FpFormat::BF16,
            FpFormat::F32,
            FpFormat::F64,
            FpFormat::X87,
            FpFormat::F128,
        ],
    );
}

#[test]
#[ignore = "needs bitwuzla on PATH"]
fn bitwuzla_agrees_with_floating_point() {
    use crate::fp::FpFormat;
    // Bitwuzla's release builds take the four standard formats only.
    solver_agrees_with_floating_point(
        Solver::Bitwuzla,
        &[FpFormat::F16, FpFormat::F32, FpFormat::F64, FpFormat::F128],
    );
}

// ----- floating point ----------------------------------------------------------------------------

/// Every floating-point operation of `f` on the symbols `a`, `b`, `c`, `i` (20 bits).
fn float_ops(cx: &mut Context, f: crate::fp::FpFormat) -> Vec<Expr> {
    use crate::fp::{FpCmpOp, FpFormat, FpOp, FpTest, RoundingMode};
    let w = f.width();
    let (a, b, c) = (
        cx.symbol("a", w).unwrap(),
        cx.symbol("b", w).unwrap(),
        cx.symbol("c", w).unwrap(),
    );
    let i = cx.symbol("i", Width::new(20).unwrap()).unwrap();
    let other = if f == FpFormat::F32 {
        FpFormat::F64
    } else {
        FpFormat::F32
    };
    let mut v = Vec::new();
    for rm in [RoundingMode::Rne, RoundingMode::Rtn] {
        v.push(cx.fp(FpOp::Add(rm), f, &[a, b]).unwrap());
        v.push(cx.fp_sub(f, rm, a, b).unwrap());
        v.push(cx.fp(FpOp::Mul(rm), f, &[a, b]).unwrap());
        v.push(cx.fp(FpOp::Div(rm), f, &[a, b]).unwrap());
        v.push(cx.fp(FpOp::Fma(rm), f, &[a, b, c]).unwrap());
        v.push(cx.fp(FpOp::Sqrt(rm), f, &[a]).unwrap());
        v.push(cx.fp(FpOp::RoundToIntegral(rm), f, &[a]).unwrap());
        v.push(cx.fp(FpOp::Convert { to: other, rm }, f, &[a]).unwrap());
        v.push(cx.fp(FpOp::FromSInt(rm), f, &[i]).unwrap());
        v.push(cx.fp(FpOp::FromUInt(rm), f, &[i]).unwrap());
        v.push(cx.fp(FpOp::ToSInt(rm, Width::W16), f, &[a]).unwrap());
        v.push(cx.fp(FpOp::ToUInt(rm, Width::W8), f, &[a]).unwrap());
    }
    for op in [FpOp::Rem, FpOp::Min, FpOp::Max] {
        v.push(cx.fp(op, f, &[a, b]).unwrap());
    }
    for op in [FpCmpOp::Eq, FpCmpOp::Lt, FpCmpOp::Ge] {
        v.push(cx.fp_cmp(f, op, a, b).unwrap());
    }
    v.push(cx.fp_test(f, FpTest::Subnormal, a).unwrap());
    v
}

#[test]
fn floating_point_exports_read_back_as_the_same_functions() {
    use crate::fp::FpFormat;
    let mut rng = Rng(0x25);
    for f in [
        FpFormat::F32,
        FpFormat::F16,
        FpFormat::new(4, 5).unwrap(),
        FpFormat::X87,
    ] {
        let mut cx = Context::new();
        let exprs = float_ops(&mut cx, f);
        for &e in &exprs {
            let script = export(&mut cx, &[e]).unwrap();
            let mut other = Context::new();
            let back = import(&mut other, &script)
                .unwrap_or_else(|err| panic!("{err}\n{script}"))
                .definition("root0")
                .unwrap();
            // The operations that round are read back as the very same node.
            if matches!(cx.view(e).unwrap(), crate::View::Fp { .. }) {
                let (t1, t2) = (cx.display(e).to_string(), other.display(back).to_string());
                let is_minmax_or_int = t1.starts_with("fp.min")
                    || t1.starts_with("fp.max")
                    || t1.starts_with("fp.to_");
                if !is_minmax_or_int {
                    assert_eq!(t1, t2, "{script}");
                }
            }
            for _ in 0..40 {
                let env: Vec<(SymbolKey, BitVec)> = vec![
                    (SymbolKey::from("a"), crate::fp::tests::sample(&mut rng, f)),
                    (SymbolKey::from("b"), crate::fp::tests::sample(&mut rng, f)),
                    (SymbolKey::from("c"), crate::fp::tests::sample(&mut rng, f)),
                    (
                        SymbolKey::from("i"),
                        BitVec::wrapping_from_u64(Width::new(20).unwrap(), rng.next()),
                    ),
                ];
                let want = cx.eval(&[e], &env[..]).unwrap()[0];
                let got = other.eval(&[back], &env[..]).unwrap()[0];
                assert_eq!(got, want, "{} at {env:?}", cx.display(e));
            }
        }
    }
}

#[test]
fn floating_point_scripts_import() {
    let script = "
        (set-logic QF_BVFP)
        (declare-const x Float32)
        (declare-const y (_ FloatingPoint 8 24))
        (define-fun tenth () Float32 ((_ to_fp 8 24) RNE 0.1))
        (define-fun third () Float64 ((_ to_fp 11 53) RTZ (/ 1 3)))
        (define-fun neg () Float32 ((_ to_fp 8 24) RNE (- 2.5)))
        (define-fun one () Float32 (fp #b0 #x7f #b00000000000000000000000))
        (define-fun s () Float32 (fp.add roundNearestTiesToEven x tenth))
        (define-fun chain () Bool (fp.lt (_ -oo 8 24) x y (_ +oo 8 24)))
        (define-fun nan_eq () Bool (= (_ NaN 8 24) ((_ to_fp 8 24) #x7f800001)))
        (define-fun zeros () Bool (= (_ +zero 8 24) (_ -zero 8 24)))
        (define-fun bits () (_ BitVec 32) (fp.to_ieee_bv (fp.mul RTP one tenth)))
        (define-fun wide () Float64 ((_ to_fp 11 53) RNE x))
        (define-fun back () (_ BitVec 8) ((_ fp.to_sbv 8) RTZ neg))
        (assert (fp.isNormal s))
        (check-sat)
    ";
    let mut cx = Context::new();
    let im = import(&mut cx, script).unwrap();
    let c = |name: &str| cx.as_const(im.definition(name).unwrap()).unwrap();
    assert_eq!(c("tenth").unwrap().to_f32(), Some(0.1f32));
    assert_eq!(
        c("third").unwrap().to_f64(),
        Some(f64::from_bits((1.0f64 / 3.0).to_bits()))
    );
    assert_eq!(c("neg").unwrap().to_f32(), Some(-2.5));
    assert_eq!(c("one").unwrap().to_f32(), Some(1.0));
    // NaNs are one value for `=`; +0 and −0 are two.
    assert_eq!(c("nan_eq").unwrap(), BitVec::from_bool(true));
    assert_eq!(c("zeros").unwrap(), BitVec::from_bool(false));
    assert_eq!(
        c("bits").unwrap().to_u64(),
        Some(u64::from((0.1f32).to_bits()))
    );
    assert_eq!(c("back").unwrap().to_u64(), Some(0xfe)); // −2.5 toward zero: −2
    let env = [
        (SymbolKey::from("x"), BitVec::from_f32(1.0)),
        (SymbolKey::from("y"), BitVec::from_f32(2.0)),
    ];
    let mut v = |name: &str| cx.eval(&[im.definition(name).unwrap()], &env[..]).unwrap()[0];
    assert_eq!(v("s").to_f32(), Some(1.0f32 + 0.1f32));
    assert_eq!(v("chain"), BitVec::from_bool(true));
    assert_eq!(v("wide").to_f64(), Some(1.0));
    assert_eq!(im.assertions.len(), 1);
    // A rounding-mode variable is a 3-bit symbol, asserted to be one of the five modes.
    let mut cx = Context::new();
    let im = import(&mut cx, "(declare-const m RoundingMode)").unwrap();
    assert_eq!((im.symbols.len(), im.assertions.len()), (1, 1));
    assert_eq!(cx.width(im.symbols[0].1).unwrap().bits(), 3);
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
    let n = rule.width_vars.len();
    // A floating-point rule over (E, S): the standard formats (the ones Bitwuzla has), and a
    // small one.
    let float = n == 2
        && rule
            .nodes
            .iter()
            .any(|node| matches!(node, crate::rules::RNode::Fp(_)));
    let formats: &[[u16; 2]] = &[[5, 11], [8, 24], [11, 53], [15, 113], [3, 4]];
    let all: Vec<Vec<u16>> = crate::rules::compile::width_assignments(rule)
        .into_iter()
        .filter(|ws| {
            let widths = &ws[..n];
            let chosen = if float {
                formats.iter().any(|f| widths == f)
            } else {
                widths.iter().all(|w| SET.contains(w))
            };
            chosen && rule.admits(ws)
        })
        .collect();
    let stride = all.len().div_ceil(cap).max(1);
    all.into_iter().step_by(stride).collect()
}

/// Whether an obligation's floating-point formats are all ones Bitwuzla has (binary16, 32, 64
/// and 128, without its experimental formats).
fn bitwuzla_formats(script: &str) -> bool {
    script.match_indices("(_ to_fp ").all(|(i, _)| {
        let rest = &script[i + 9..];
        ["5 11)", "8 24)", "11 53)", "15 113)"]
            .iter()
            .any(|f| rest.starts_with(f))
    })
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

/// Every built-in rule proved by a solver at widths up to 512, and the unsound ones refuted.
/// Skipped (with a note) for a solver that is not installed. The obligations are independent,
/// so they are solved by one solver process per available core, and the answers are read back
/// in order: the report does not depend on scheduling.
fn solver_proves_the_built_in_rules(solver: Solver) {
    use std::sync::OnceLock;
    use std::sync::atomic::{AtomicUsize, Ordering};
    if !solver.available() {
        return;
    }
    // The built-in rules must be proved and the unsound ones refuted; the coverage rules are
    // neither. Every obligation first, then all of them solved at once.
    let mut rules = Vec::new();
    let mut jobs: Vec<(Vec<u16>, String)> = Vec::new();
    for (k, program) in programs().iter().enumerate().take(3) {
        for rule in program.rules() {
            let start = jobs.len();
            for ws in assignments(rule, 8) {
                let script = rule_obligation(rule, &ws).unwrap();
                jobs.push((ws, script));
            }
            rules.push((rule.name.clone(), k == 2, start..jobs.len()));
        }
    }
    // One solver process per core, widest obligations (the slow ones) first, so that none of them
    // starts last and stretches the run; each answer lands in its obligation's slot.
    let mut order: Vec<usize> = (0..jobs.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(jobs[i].0.iter().max().copied()));
    let next = AtomicUsize::new(0);
    let answers: Vec<OnceLock<Option<String>>> = jobs.iter().map(|_| OnceLock::new()).collect();
    let workers = std::thread::available_parallelism().map_or(1, |n| n.get());
    std::thread::scope(|s| {
        for _ in 0..workers.min(jobs.len()) {
            s.spawn(|| {
                while let Some(&i) = order.get(next.fetch_add(1, Ordering::Relaxed)) {
                    // A format Bitwuzla does not have proves nothing either way.
                    let answer =
                        if matches!(solver, Solver::Bitwuzla) && !bitwuzla_formats(&jobs[i].1) {
                            Some("skipped".to_string())
                        } else {
                            solver.run(&jobs[i].1, Some(60_000))
                        };
                    let _ = answers[i].set(answer);
                }
            });
        }
    });
    let mut failures = Vec::new();
    // A solver that gives up proves nothing but refutes nothing either: tolerated where the
    // obligation bit-blasts to a large circuit, and only rarely. That is above 64 bits;
    // products, quotients and remainders from 16 bits (multiplier and divider circuits); bit
    // deposits and extractions above 32 bits (quadratic); floats of binary32's precision or
    // more. (The rules are established by bitwright's own checker and prover; hosted CI
    // runners reach the time limit on these.)
    let heavy = |name: &str, ws: &[u16], script: &str| {
        let widest = ws.iter().copied().max().unwrap_or(0);
        let nonlinear = ["bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod"]
            .iter()
            .any(|op| script.contains(op));
        widest > 64
            || (nonlinear && widest >= 16)
            || ((name.contains("pdep") || name.contains("pext")) && widest > 32)
            // Bit counts are exported as sums of bits, which z3 decides slowly past 32.
            || (name.starts_with("core.bit_counts") && widest > 32)
            || (name.starts_with("core.float") && widest >= 24)
    };
    let mut gave_up = Vec::new();
    let mut proved = 0;
    for (name, unsound, range) in &rules {
        let mut refuted = false;
        for i in range.clone() {
            let ws = &jobs[i].0;
            let answer = answers[i].get().cloned().flatten().unwrap();
            match (answer.as_str(), *unsound) {
                ("skipped", _) => {}
                ("unsat", false) => proved += 1,
                ("sat", true) => refuted = true,
                ("unsat", true) => {}
                ("unknown" | "timeout", _) if heavy(name, ws, &jobs[i].1) => {
                    gave_up.push(format!("{name} {ws:?}"));
                }
                (a, _) => failures.push(format!("{name} {ws:?}: {a}")),
            }
        }
        if *unsound && !refuted {
            failures.push(format!("{name}: never refuted"));
        }
    }
    eprintln!(
        "{proved} obligations proved; {} gave up on {}: {gave_up:?}",
        solver.name(),
        gave_up.len()
    );
    assert!(failures.is_empty(), "{}: {failures:#?}", solver.name());
    assert!(
        gave_up.len() * 20 < proved,
        "{}: {gave_up:#?}",
        solver.name()
    );
}

#[test]
#[ignore = "needs z3 on PATH; minutes"]
fn z3_proves_the_built_in_rules() {
    solver_proves_the_built_in_rules(Solver::Z3);
}

#[test]
#[ignore = "needs bitwuzla on PATH; minutes"]
fn bitwuzla_proves_the_built_in_rules() {
    solver_proves_the_built_in_rules(Solver::Bitwuzla);
}

/// A program of floating-point rules: sound ones, then one that is not.
const FP_RULES: &str = "bitwright 1;
group fp {
    #[allow(BW0407)]
    rule abs_square<E, S>(x: E + S, r: rm) {
        fp.abs<E, S>(fp.mul.r<E, S>(x, x)) => fp.mul.r<E, S>(x, x)
    }
    #[allow(BW0407)]
    rule sqrt_neg<E, S>(x: E + S, r: rm) {
        fp.isneg<E, S>(fp.sqrt.r<E, S>(x)) => x == smin_lit
    }
    #[allow(BW0407)]
    rule to_int_of_round<E, S, W>(x: E + S, r: rm, q: rm) where S <= E {
        fp.to_sbv.q<E, S, W>(fp.round.r<E, S>(x)) => fp.to_sbv.r<E, S, W>(x)
    }
    #[allow(BW0407)]
    rule mul_one_number<E, S>(x: E + S, r: rm) {
        fp.mul.r<E, S>(x, fp.one<E, S>) => x if fp.not_nan<E, S>(x)
    }
    #[allow(BW0407)]
    rule div_self<E, S>(x: E + S, r: rm) {
        fp.div.r<E, S>(x, x) => fp.one<E, S> if fp.finite<E, S>(x) && fp.nonzero<E, S>(x)
    }
    #[allow(BW0407)]
    rule mul_one<E, S>(x: E + S, r: rm) { fp.mul.r<E, S>(x, fp.one<E, S>) => x }
}
";

/// The obligations of [`FP_RULES`] at standard formats, every rounding mode: `(rule, sound,
/// assignment, script)`.
fn fp_obligations() -> Vec<(String, bool, Vec<u16>, String)> {
    let p =
        RuleProgram::compile(FP_RULES).unwrap_or_else(|e| panic!("{}", e.render("t", FP_RULES)));
    let mut out = Vec::new();
    for rule in p.rules() {
        let widths: &[&[u16]] = if rule.width_vars.len() == 3 {
            &[&[8, 8, 8], &[5, 5, 16]]
        } else {
            &[&[5, 11], &[8, 24], &[11, 53]]
        };
        for ws in widths {
            for full in crate::rules::compile::with_modes(rule, ws.to_vec()) {
                assert!(rule.admits(&full), "{} {full:?}", rule.name);
                let script = rule_obligation(rule, &full).unwrap();
                out.push((
                    rule.name.clone(),
                    !rule.name.ends_with("mul_one"),
                    full,
                    script,
                ));
            }
        }
    }
    out
}

#[test]
fn floating_point_obligations_read_back() {
    for (name, _, ws, script) in fp_obligations() {
        assert!(
            script.contains("(set-logic QF_BVFP)"),
            "{name} {ws:?}:\n{script}"
        );
        import(&mut Context::new(), &script).unwrap_or_else(|e| panic!("{name}: {e}\n{script}"));
    }
}

/// The floating-point rules proved, and the unsound one refuted, by a solver.
fn solver_proves_floating_point_rules(solver: Solver) {
    if !solver.available() {
        return;
    }
    let mut refuted = false;
    for (name, sound, ws, script) in fp_obligations() {
        // Bitwuzla has only binary16, 32, 64 and 128 (without its experimental formats).
        let standard = [[5, 11], [8, 24], [11, 53], [15, 113]]
            .iter()
            .any(|f| ws[..2] == f[..]);
        if matches!(solver, Solver::Bitwuzla) && !standard {
            continue;
        }
        let answer = solver.run(&script, Some(60_000)).unwrap();
        match (answer.trim(), sound) {
            ("unsat", true) => {}
            ("sat", false) => refuted = true,
            ("unsat", false) => {}
            (a, _) => panic!("{}: {name} {ws:?}: {a}", solver.name()),
        }
    }
    assert!(refuted, "{}: mul_one never refuted", solver.name());
}

#[test]
#[ignore = "needs z3 on PATH"]
fn z3_proves_floating_point_rules() {
    solver_proves_floating_point_rules(Solver::Z3);
}

#[test]
#[ignore = "needs bitwuzla on PATH"]
fn bitwuzla_proves_floating_point_rules() {
    solver_proves_floating_point_rules(Solver::Bitwuzla);
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

/// A solver answers `unsat` for a true equality over symbols named after SMT-LIB built-ins.
fn solver_proves_equalities_over_reserved_names(solver: Solver) {
    if !solver.available() {
        return;
    }
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
    let out = solver.run(&script, None).unwrap();
    assert_eq!(
        out.lines().collect::<Vec<_>>(),
        ["unsat"; 4],
        "{}: {out}",
        solver.name()
    );
}

#[test]
#[ignore = "needs z3 on PATH"]
fn z3_proves_equalities_over_reserved_names() {
    solver_proves_equalities_over_reserved_names(Solver::Z3);
}

#[test]
#[ignore = "needs bitwuzla on PATH"]
fn bitwuzla_proves_equalities_over_reserved_names() {
    solver_proves_equalities_over_reserved_names(Solver::Bitwuzla);
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
    assert!(q.contains("(assert (= root2 #b1))"), "{q}");
    assert!(!q.contains("root3"), "{q}");
    assert!(q.ends_with("(assert (not (= root0 root1)))\n(check-sat)\n"));
}

#[test]
fn exported_fact_constraints_preserve_unsigned_strides_and_signed_membership() {
    use crate::{Assumptions, Facts, KnownBits, SRange, URange};
    for (lo, hi, stride) in [(13, 223, 7), (64, 200, 17), (3, 227, 8)] {
        let mut cx = Context::new();
        let w = Width::W8;
        let x = cx.symbol("x", w).unwrap();
        let facts = Facts::new(
            KnownBits::unknown(w),
            URange::strided(
                BitVec::from_u64(w, lo).unwrap(),
                BitVec::from_u64(w, hi).unwrap(),
                stride,
            )
            .unwrap(),
            SRange::full(w),
        )
        .unwrap();
        let mut assumptions = Assumptions::new();
        let id = assumptions.assume(&mut cx, x, facts).unwrap();
        let zero = cx.zero(w).unwrap();
        let one = cx.one(w).unwrap();
        let text =
            equivalence_query_under(&mut cx, zero, one, &assumptions, crate::Reliance::of(id))
                .unwrap();
        let mut parsed = Context::new();
        let imported = import(&mut parsed, &text).unwrap();
        for value in 0..256 {
            let value = BitVec::from_u64(w, value).unwrap();
            let env = [(SymbolKey::from("x"), value)];
            let satisfies = parsed
                .eval(&imported.assertions, &env[..])
                .unwrap()
                .iter()
                .all(|v| !v.is_zero());
            assert_eq!(satisfies, facts.contains(&value), "{facts:?}, {value:?}");
        }
    }
}

/// Every rewrite made under random constraints is proved by a solver under the constraints it
/// relies on. Skipped (with a note) for a solver that is not installed.
fn solver_proves_rewrites_under_the_constraints_they_rely_on(solver: Solver) {
    use crate::Assumptions;
    if !solver.available() {
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
            if solver.run(&q, None).as_deref() == Some("sat") {
                needed += 1;
            }
        }
    }
    let out = solver.run(&script, None).unwrap();
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), relied, "{}: {out}", solver.name());
    assert!(
        lines.iter().all(|l| *l == "unsat"),
        "{}: {out}",
        solver.name()
    );
    assert!(
        relied > 60 && needed > 40,
        "relied {relied}, needed {needed}"
    );
}

#[test]
#[ignore = "needs z3 on PATH"]
fn z3_proves_rewrites_under_the_constraints_they_rely_on() {
    solver_proves_rewrites_under_the_constraints_they_rely_on(Solver::Z3);
}

#[test]
#[ignore = "needs bitwuzla on PATH"]
fn bitwuzla_proves_rewrites_under_the_constraints_they_rely_on() {
    solver_proves_rewrites_under_the_constraints_they_rely_on(Solver::Bitwuzla);
}

#[test]
fn array_reads_do_not_capture_script_names() {
    for (before, after) in [
        ("(declare-const m.0 (_ BitVec 8))", ""),
        ("", "(declare-const m.0 (_ BitVec 8))"),
        (
            "(declare-const |m.0| (_ BitVec 8)) (declare-const m.reads0.0 (_ BitVec 32))",
            "",
        ),
    ] {
        let script = format!(
            "(declare-const m (Array (_ BitVec 8) (_ BitVec 8)))
             {before}
             (define-fun first () (_ BitVec 8) (select m #x00))
             {after}
             (assert (distinct first m.0))"
        );
        let mut cx = Context::new();
        let imported = import(&mut cx, &script).unwrap();
        let read = imported.definition("first").unwrap();
        let user = cx.find_symbol(&SymbolKey::from("m.0")).unwrap();
        assert_ne!(read, user);
        let read_key = cx
            .symbol_key(cx.symbol_id(read).unwrap().unwrap())
            .unwrap()
            .clone();
        let env = [
            (read_key, BitVec::wrapping_from_u64(Width::W8, 42)),
            (
                SymbolKey::from("m.0"),
                BitVec::wrapping_from_u64(Width::W8, 99),
            ),
        ];
        assert_eq!(
            cx.eval(&imported.assertions, &env[..]).unwrap(),
            [BitVec::from_bool(true)]
        );
    }
}

#[test]
fn arrays_import_as_memory() {
    let script = "
(set-logic QF_ABV)
(declare-fun m () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(declare-const v (_ BitVec 8))
(define-fun m1 () (Array (_ BitVec 32) (_ BitVec 8)) (store m a v))
(assert (= (select m1 a) v))
(assert (= (select m1 b) (ite (= a b) v (select m b))))
(assert (= (select (store m1 (bvadd a #x00000001) #x07) a) v))
(check-sat)
";
    let mut cx = Context::new();
    let imp = crate::smtlib::import(&mut cx, script).unwrap();
    assert_eq!(imp.arrays.len(), 1);
    assert_eq!(imp.assertions.len(), 3);
    // Read over write decides the first and last at once; the middle one is valid.
    for (k, &e) in imp.assertions.iter().enumerate() {
        match k {
            0 | 2 => assert_eq!(
                cx.as_const(e).unwrap(),
                Some(BitVec::from_bool(true)),
                "{k}"
            ),
            _ => assert!(matches!(
                crate::prove::valid(&mut cx, e, &crate::prove::Config::default()).unwrap(),
                crate::prove::Outcome::Proved(_)
            )),
        }
    }
}

/// Arrays beyond declared ones: chosen by `ite`, constant, stored into, and compared
/// (extensionality). The answers are z3's.
#[test]
fn arrays_are_compared_chosen_and_constant() {
    let header = "(set-logic QF_ABV)
        (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
        (declare-const v (_ BitVec 8)) (declare-const w (_ BitVec 8))
        (declare-const p Bool)
        (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const c (Array (_ BitVec 8) (_ BitVec 8)))";
    let cases: &[(&str, &str)] = &[
        (
            "(assert (= b (store a x #x01))) (assert (not (= (select b x) #x01))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= b (store a x #x01))) (assert (not (= (select b y) (select a y)))) (check-sat)",
            "sat",
        ),
        (
            "(assert (= b (store a x #x01))) (assert (distinct x y)) (assert (not (= (select b y) (select a y)))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= b (store a x v))) (assert (= b (store a x w))) (assert (distinct v w)) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= b (store a x v))) (assert (= b (store a y w))) (assert (distinct v w)) (check-sat)",
            "sat",
        ),
        ("(assert (not (= a b))) (check-sat)", "sat"),
        ("(assert (not (= a a))) (check-sat)", "unsat"),
        (
            "(assert (not (= (store a x v) (store a x v)))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (distinct x y)) (assert (not (= (store (store a x v) y w) (store (store a y w) x v)))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (not (= (store (store a x v) y w) (store (store a y w) x v)))) (check-sat)",
            "sat",
        ),
        (
            "(assert (= a b)) (assert (= b c)) (assert (not (= a c))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= a b)) (assert (= b c)) (assert (distinct (select a x) (select c x))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (not (= (select (ite p a b) x) (ite p (select a x) (select b x))))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= c (store (ite p a b) x v))) (assert p) (assert (distinct x y)) (assert (distinct (select c y) (select a y))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (not (= (select ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) x) #x07))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= a (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) x #x05))) (assert (= (select a y) #x05)) (assert (distinct x y)) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) v))) (assert (= (select a x) #x09)) (check-sat)",
            "sat",
        ),
        (
            "(assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) v))) (assert (distinct (select a x) (select a y))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (not (= (store a x (select a x)) a))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (or (= a b) (= a c))) (assert (distinct (select a x) (select b x))) (assert (distinct (select a x) (select c x))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (or (= a b) (= a c))) (assert (distinct (select a x) (select b x))) (check-sat)",
            "sat",
        ),
        (
            "(assert (= a b)) (push 1) (assert (distinct (select a x) (select b x))) (check-sat) (pop 1) (check-sat) (assert (distinct (select a y) (select b y))) (check-sat)",
            "unsat sat unsat",
        ),
        (
            "(assert (distinct (select a x) (select b x))) (check-sat) (assert (= a b)) (check-sat)",
            "sat unsat",
        ),
        (
            "(assert (distinct a b c)) (assert (= (store a x v) (store b x v))) (check-sat)",
            "sat",
        ),
        (
            "(assert (= (ite p a b) c)) (assert (not p)) (assert (distinct (select b x) (select c x))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= b (store (store a x (select a y)) y (select a x)))) (assert (= c (store (store b x (select b y)) y (select b x)))) (assert (not (= a c))) (check-sat)",
            "unsat",
        ),
    ];
    let cfg = crate::solve::Config::default();
    for (body, expected) in cases {
        let mut out = String::new();
        run(
            &mut Context::new(),
            &format!("{header}{body}"),
            &cfg,
            &mut out,
        )
        .unwrap();
        assert_eq!(
            out.split_whitespace().collect::<Vec<_>>().join(" "),
            *expected,
            "{body}"
        );
    }
    // A read first made by `get-value` has the value the equality gives it, and an
    // equality first read as an assumption is part of that question.
    let mut out = String::new();
    let script = format!(
        "{header}
         (assert (= a ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x09)))
         (assert (= (select b x) #x01))
         (check-sat)
         (get-value ((select a #x44)))
         (check-sat-assuming ((= a b)))
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
         (assert (= (f x) #x07))
         (check-sat)
         (get-value ((f x) (= (f y) (f x))))
         (check-sat-assuming ((= x y) (distinct (f y) #x07)))"
    );
    run(&mut Context::new(), &script, &cfg, &mut out).unwrap();
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines[..3],
        ["sat", "(((select a #x44) #x09))", "unsat"],
        "{out}"
    );
    assert_eq!(lines[3], "sat", "{out}");
    assert!(lines[4].starts_with("(((f x) #x07) "), "{out}");
    assert_eq!(lines[5], "unsat", "{out}");
    // Sorts are checked.
    let err = crate::smtlib::import(
        &mut Context::new(),
        "(declare-fun m () (Array (_ BitVec 8) (_ BitVec 8)))
         (declare-fun n () (Array (_ BitVec 16) (_ BitVec 8)))
         (assert (= m n))",
    )
    .unwrap_err();
    assert!(err.to_string().contains("different sorts"), "{err}");
}

/// A symbol's declared known bits are stated in the script (a result may rely on them), and
/// read back as an assertion.
#[test]
fn declared_known_bits_are_asserted() {
    let w = Width::W8;
    let mut cx = Context::new();
    let e = cx.parse("x & 15", &ParseOptions::width(w)).unwrap();
    let x = cx.find_symbol(&SymbolKey::from("x")).unwrap();
    let k = crate::KnownBits::new(
        BitVec::from_u64(w, 0xf0).unwrap(),
        BitVec::from_u64(w, 0x01).unwrap(),
    )
    .unwrap();
    cx.declare_known(x, k).unwrap();
    let q = equivalence_query(&mut cx, e, x).unwrap();
    assert!(
        q.contains("(assert (= (bvand |x| #b11110001) #b00000001))"),
        "{q}"
    );
    let mut back = Context::new();
    let imported = import(&mut back, &export(&mut cx, &[e]).unwrap()).unwrap();
    assert_eq!(imported.assertions.len(), 1);
}

#[test]
fn exit_ends_the_script() {
    let mut cx = Context::new();
    let s = import(
        &mut cx,
        "(declare-const x (_ BitVec 8))
         (assert (= x #x01))
         (check-sat)
         (exit)
         (declare-const y (_ BitVec 8))
         (assert (= x #x02))",
    )
    .unwrap();
    assert_eq!(s.symbols.len(), 1);
    assert_eq!(s.assertions.len(), 1);
    // The text after it must still be well formed, and `exit` takes no argument.
    assert!(import(&mut Context::new(), "(exit) (assert").is_err());
    assert!(import(&mut Context::new(), "(exit 1)").is_err());
}

/// The exporter's float-bits pattern is a definition of `c` only when neither `T` nor `NAN`
/// reads `c`. Read as one when they do, the constraint was dropped and each of these
/// unsatisfiable scripts had a model.
#[test]
fn a_float_bits_assertion_that_reads_its_constant_stays_an_assertion() {
    for script in [
        "(declare-const c (_ BitVec 32))
         (assert (ite (fp.isNaN (fp.add RNE ((_ to_fp 8 24) c) ((_ to_fp 8 24) #x3f800000)))
                      (= c #x7fc00000)
                      (= ((_ to_fp 8 24) c)
                         (fp.add RNE ((_ to_fp 8 24) c) ((_ to_fp 8 24) #x3f800000)))))
         (assert (= c #x00000000))",
        "(declare-const x Float32)
         (declare-const c (_ BitVec 32))
         (assert (ite (fp.isNaN x) (= c (bvnot c)) (= ((_ to_fp 8 24) c) x)))
         (assert (fp.isNaN x))",
    ] {
        let mut cx = Context::new();
        let s = import(&mut cx, script).unwrap();
        assert_eq!(s.assertions.len(), 2, "{script}");
        assert!(s.symbols.iter().any(|(n, _)| n == "c"), "{script}");
        let mut all = s.assertions[0];
        for &a in &s.assertions[1..] {
            all = cx.bin(crate::BinOp::And, all, a).unwrap();
        }
        assert!(
            matches!(
                crate::prove::satisfy(&mut cx, all, &crate::prove::Config::default()),
                Ok(Ok(None))
            ),
            "{script}"
        );
    }
    // The pattern as exported, `c` read by neither side, is still its definition.
    let mut cx = Context::new();
    let s = import(
        &mut cx,
        "(declare-const x Float32)
         (declare-const c (_ BitVec 32))
         (assert (ite (fp.isNaN (fp.neg x)) (= c #x7fc00000) (= ((_ to_fp 8 24) c) (fp.neg x))))",
    )
    .unwrap();
    assert!(s.assertions.is_empty());
    assert!(s.symbols.iter().all(|(n, _)| n != "c"));
}

/// The overflow predicates against exact integer arithmetic, on every pair of operands at
/// widths 1 to 5.
#[test]
fn overflow_predicates_are_exact() {
    const OPS: [&str; 7] = [
        "bvuaddo", "bvsaddo", "bvusubo", "bvssubo", "bvumulo", "bvsmulo", "bvsdivo",
    ];
    for w in 1..=5u16 {
        let mut script = format!(
            "(declare-const a (_ BitVec {w}))(declare-const b (_ BitVec {w}))\
             (define-fun nego () Bool (bvnego a))"
        );
        for op in OPS {
            script.push_str(&format!("(define-fun {op} () Bool ({op} a b))"));
        }
        let mut cx = Context::new();
        let s = import(&mut cx, &script).unwrap();
        let width = Width::new(w).unwrap();
        let roots: Vec<Expr> = (["nego"].iter().chain(&OPS))
            .map(|n| s.definition(n).unwrap())
            .collect();
        let signed = |v: i64| if v >= 1 << (w - 1) { v - (1 << w) } else { v };
        let (umax, smin, smax) = ((1i64 << w) - 1, -(1i64 << (w - 1)), (1i64 << (w - 1)) - 1);
        let out = |v: i64| v < smin || v > smax;
        for a in 0..=umax {
            for b in 0..=umax {
                let env: BTreeMap<SymbolKey, BitVec> = [("a", a), ("b", b)]
                    .into_iter()
                    .map(|(n, v)| {
                        (
                            SymbolKey::from(n),
                            BitVec::from_u64(width, v as u64).unwrap(),
                        )
                    })
                    .collect();
                let got: Vec<bool> = (cx.eval(&roots, &env).unwrap().iter())
                    .map(|v| !v.is_zero())
                    .collect();
                let (sa, sb) = (signed(a), signed(b));
                let want = [
                    sa == smin,
                    a + b > umax,
                    out(sa + sb),
                    a < b,
                    out(sa - sb),
                    a * b > umax,
                    out(sa * sb),
                    sa == smin && sb == -1,
                ];
                assert_eq!(got, want, "width {w}, a = {a}, b = {b}");
            }
        }
    }
}

fn session(script: &str) -> String {
    let mut out = String::new();
    run(
        &mut Context::new(),
        script,
        &crate::solve::Config::default(),
        &mut out,
    )
    .unwrap();
    out
}

#[test]
fn a_session_answers_checks_models_and_cores() {
    // Scopes: assertions and declarations go with them, and a name may come back wider.
    assert_eq!(
        session(
            "(set-logic QF_BV)
             (declare-const x (_ BitVec 8))
             (assert (bvult x #x10))
             (push 1)
             (declare-const y (_ BitVec 8))
             (assert (= (bvadd x y) #xff))
             (assert (bvult y #x10))
             (check-sat)
             (pop 1)
             (check-sat)
             (declare-const y (_ BitVec 16))
             (assert (= y #x1234))
             (check-sat)
             (get-value (y ((_ extract 3 0) y)))
             (pop 1)
             (check-sat)"
        ),
        "unsat\nsat\nsat\n((y #x1234) (((_ extract 3 0) y) #x4))\n\
         (error \"unsupported: pop 1 with 0 scopes open\")\nsat\n"
    );
    // A function with parameters, applied twice and inside another; named assertions and
    // assumptions in a core.
    assert_eq!(
        session(
            "(define-fun mix ((v (_ BitVec 32)) (k (_ BitVec 32))) (_ BitVec 32)
               (bvmul (bvxor v k) #x9e3779b1))
             (define-fun twice ((v (_ BitVec 32))) (_ BitVec 32) (mix (mix v #x00000001) #x00000002))
             (declare-const x (_ BitVec 32))
             (declare-const p Bool)
             (assert (! (= (twice x) (twice #x0000002a)) :named same))
             (assert (! (not (= x #x0000002a)) :named differs))
             (assert (! (=> p (bvugt x #x00000000)) :named unused))
             (check-sat)
             (get-unsat-core)
             (get-model)
             (reset-assertions)
             (assert (= x #x00000007))
             (check-sat-assuming (p (bvult x #x00000005)))
             (get-unsat-assumptions)
             (check-sat-assuming (p))
             (get-value (p x))
             (get-model)"
        ),
        "unsat\n(same differs)\n(error \"unsupported: no model: the last check was not sat\")\n\
         unsat\n((bvult x #x00000005))\nsat\n((p true) (x #x00000007))\n\
         (\n  (define-fun x () (_ BitVec 32) #x00000007)\n  (define-fun p () Bool true)\n)\n"
    );
    // A failing command answers an error and the script goes on; `exit` ends it.
    assert_eq!(
        session(
            "(set-option :print-success true)
             (declare-const q Int)
             (declare-const b (_ BitVec 3))
             (assert (= b #b101))
             (set-option :print-success false)
             (check-sat)
             (get-value (b))
             (echo \"done\")
             (get-info :name)
             (exit)
             (check-sat)"
        ),
        "success\n(error \"unsupported: a variable of sort Int (integers are read where a \
         bit-vector bounds them) (at bytes 63..66)\")\n\
         success\nsuccess\nsat\n((b #b101))\n\"done\"\n(:name \"bitwright\")\n"
    );
    // A float's value is its bits; a reset forgets the declarations too.
    assert_eq!(
        session(
            "(declare-const f Float32)
             (assert (= f (fp.add RNE ((_ to_fp 8 24) #x3f800000) ((_ to_fp 8 24) #x3f800000))))
             (check-sat)
             (get-value (f))
             (reset)
             (declare-const f (_ BitVec 4))
             (assert (= f #xa))
             (check-sat)
             (get-model)"
        ),
        "sat\n((f (fp #b0 #b10000000 #b00000000000000000000000)))\nsat\n\
         (\n  (define-fun f () (_ BitVec 4) #xa)\n)\n"
    );
}

/// What SMT-LIB leaves unspecified is open in a session (z3 answers each of these the same
/// way), while every specified case keeps its value.
#[test]
fn a_session_leaves_unspecified_float_results_open() {
    let x = "(declare-const x Float32)";
    let ubv = "((_ fp.to_ubv 8) RNE x)";
    for (script, want) in [
        // Either zero, but one zero for one order of the operands.
        (
            "(assert (fp.isPositive (fp.min (_ +zero 8 24) (_ -zero 8 24))))".to_string(),
            "sat",
        ),
        (
            "(assert (fp.isNegative (fp.min (_ +zero 8 24) (_ -zero 8 24))))".to_string(),
            "sat",
        ),
        (
            "(assert (fp.isNegative (fp.max (_ -zero 8 24) (_ +zero 8 24))))".to_string(),
            "sat",
        ),
        (
            "(assert (not (fp.isZero (fp.min (_ +zero 8 24) (_ -zero 8 24)))))".to_string(),
            "unsat",
        ),
        (
            "(assert (fp.isNegative (fp.min (_ +zero 8 24) (_ +zero 8 24))))".to_string(),
            "unsat",
        ),
        (
            format!(
                "{x}(declare-const y Float32)(assert (= x (_ +zero 8 24)))\
                 (assert (= y (_ -zero 8 24)))\
                 (assert (not (= (fp.min x y) (fp.min (_ +zero 8 24) (_ -zero 8 24)))))"
            ),
            "unsat",
        ),
        // A NaN, an infinity and a value out of range convert to anything.
        (
            format!("{x}(assert (fp.isNaN x))(assert (= {ubv} #x55))"),
            "sat",
        ),
        (
            format!("{x}(assert (fp.isInfinite x))(assert (= {ubv} #x55))"),
            "sat",
        ),
        (
            format!("{x}(assert (fp.gt x ((_ to_fp 8 24) RNE 1000.0)))(assert (= {ubv} #x55))"),
            "sat",
        ),
        (
            format!("{x}(assert (= x ((_ to_fp 8 24) RNE (- 1.0))))(assert (= {ubv} #x77))"),
            "sat",
        ),
        (
            format!("{x}(assert (fp.isNaN x))(assert (not (= {ubv} {ubv})))"),
            "unsat",
        ),
        // In range, to the last value that rounds into it.
        (
            format!("{x}(assert (= x ((_ to_fp 8 24) RNE 3.7)))(assert (not (= {ubv} #x04)))"),
            "unsat",
        ),
        (
            format!("{x}(assert (= x ((_ to_fp 8 24) RNE 255.4)))(assert (not (= {ubv} #xff)))"),
            "unsat",
        ),
        (
            format!("{x}(assert (= x ((_ to_fp 8 24) RNE 255.5)))(assert (= {ubv} #x11))"),
            "sat",
        ),
        (
            format!("{x}(assert (= x ((_ to_fp 8 24) RNE (- 0.25))))(assert (not (= {ubv} #x00)))"),
            "unsat",
        ),
        (
            format!(
                "{x}(assert (= x ((_ to_fp 8 24) RNE (- 128.4))))\
                 (assert (not (= ((_ fp.to_sbv 8) RNE x) #x80)))"
            ),
            "unsat",
        ),
        (
            format!(
                "{x}(assert (= x ((_ to_fp 8 24) RNE (- 128.6))))\
                 (assert (= ((_ fp.to_sbv 8) RNE x) #x33))"
            ),
            "sat",
        ),
        // A target wider than the format's range: every finite value converts.
        (
            "(declare-const h Float16)(assert (fp.geq h (_ +zero 5 11)))\
             (assert (not (fp.isInfinite h)))\
             (assert (= ((_ fp.to_ubv 64) RTZ h) #xffffffffffffffff))"
                .to_string(),
            "unsat",
        ),
    ] {
        assert_eq!(
            session(&format!("{script}(check-sat)")),
            format!("{want}\n"),
            "{script}"
        );
    }
    // The importer alone keeps bitwright's definitions: no symbol stands for a result.
    let mut cx = Context::new();
    let s = import(
        &mut cx,
        "(define-fun m () Float32 (fp.min (_ +zero 8 24) (_ -zero 8 24)))",
    );
    assert!(
        cx.as_const(s.unwrap().definition("m").unwrap())
            .unwrap()
            .is_some()
    );
}

#[test]
fn a_session_fed_in_pieces_answers_each_command_once_complete() {
    let mut cx = Context::new();
    let cfg = crate::solve::Config::default();
    let whole = "(declare-const |a b| (_ BitVec 8)) ; a ( in a comment\n\
                 (assert (= |a b| #x2a))(check-sat)(echo \"a ) and a \"\" in a string\")\n\
                 (get-value (|a b|))(exit)(check-sat)";
    let mut expected = String::new();
    run(&mut Context::new(), whole, &cfg, &mut expected).unwrap();
    // Cut anywhere: the answers are the same.
    for cut in [1, 2, 3, 7, 16, 64] {
        let mut s = Session::new(&mut cx, &cfg);
        let mut out = String::new();
        let bytes = whole.as_bytes();
        for piece in bytes.chunks(cut) {
            s.feed(core::str::from_utf8(piece).unwrap(), &mut out)
                .unwrap();
        }
        assert_eq!(out, expected, "cut every {cut}");
        assert!(s.exited() && !s.pending());
        assert_eq!(s.summary().sat, 1);
    }
    // A command that is not well formed is an error of its own; the next one runs.
    let mut s = Session::new(&mut cx, &cfg);
    let mut out = String::new();
    s.feed("(assert #b2) ) (check-sat)", &mut out).unwrap();
    assert_eq!(out.lines().count(), 3, "{out}");
    assert!(out.ends_with("sat\n") && out.starts_with("(error"), "{out}");
    assert_eq!(s.summary().errors, 2);
    s.feed("(check-sat", &mut out).unwrap();
    assert!(s.pending());
}

#[test]
fn uninterpreted_functions_are_functions_and_nothing_more() {
    let d = "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
             (declare-fun p ((_ BitVec 8) Bool) Bool)
             (define-sort Byte () (_ BitVec 8))
             (declare-const x Byte)(declare-const y Byte)(declare-const z Byte)";
    for (body, want) in [
        // Equal arguments, equal results; through any number of applications.
        ("(assert (= x y))(assert (not (= (f x) (f y))))", "unsat"),
        (
            "(assert (= (f x) y))(assert (= (f y) z))(assert (= x z))\
          (assert (not (= (f (f (f x))) y)))",
            "unsat",
        ),
        (
            "(assert (p x true))(assert (not (p y true)))(assert (= x y))",
            "unsat",
        ),
        // Nothing else is known of them.
        ("(assert (not (= (f x) (f y))))", "sat"),
        ("(assert (p x true))(assert (not (p x false)))", "sat"),
        // Three values of f need three arguments.
        (
            "(assert (distinct (f #x00) (f #x01) (f x)))(assert (bvult x #x02))",
            "unsat",
        ),
        (
            "(assert (distinct (f #x00) (f #x01) (f x)))(assert (bvult x #x03))",
            "sat",
        ),
    ] {
        assert_eq!(
            session(&format!("{d}{body}(check-sat)")),
            format!("{want}\n"),
            "{body}"
        );
    }
    // An application made in a scope is forgotten with it; one from before is not.
    assert_eq!(
        session(&format!(
            "{d}(assert (= (f x) #x05))(push)(assert (= (f y) #x06))(assert (= x y))(check-sat)
             (pop)(check-sat)(get-value ((f x)))(assert (= (f z) #x07))(assert (= z x))
             (check-sat)(get-assertions)"
        )),
        "unsat\nsat\n(((f x) #x05))\nunsat\n((= (f x) #x05)\n (= (f z) #x07)\n (= z x))\n"
    );
    // The importer alone states the function's meaning as assertions of its own.
    let mut cx = Context::new();
    let s = import(&mut cx, &format!("{d}(assert (= (f x) (f y)))")).unwrap();
    assert_eq!(s.assertions.len(), 2);
}

/// A rounding-mode variable is one of the five modes, and a term reads it as whichever it is
/// (z3 and Bitwuzla answer each of these the same way).
#[test]
fn a_rounding_mode_variable_is_one_of_five() {
    let d = "(declare-const a Float32)(declare-const b Float32)\
             (declare-const r RoundingMode)(declare-const q RoundingMode)";
    let third = "(fp.div RNE ((_ to_fp 8 24) RNE 1.0) ((_ to_fp 8 24) RNE 3.0))";
    let by_r = "(fp.div r ((_ to_fp 8 24) RNE 1.0) ((_ to_fp 8 24) RNE 3.0))";
    for (body, want) in [
        // One variable is one mode; two may be two.
        (
            "(assert (not (= (fp.add r a b) (fp.add r b a))))".to_string(),
            "unsat",
        ),
        (
            "(assert (not (= (fp.add r a b) (fp.add q a b))))".to_string(),
            "sat",
        ),
        (
            "(assert (= r q))(assert (not (= (fp.add r a b) (fp.add q a b))))".to_string(),
            "unsat",
        ),
        // The nearest float to a third is above it: only rounding down gives less.
        (
            format!("(assert (fp.lt {by_r} {third}))(assert (not (or (= r RTZ) (= r RTN))))"),
            "unsat",
        ),
        (format!("(assert (fp.lt {by_r} {third}))"), "sat"),
        (format!("(assert (fp.gt {by_r} {third}))"), "unsat"),
        // Five modes, no sixth.
        (
            "(declare-const c RoundingMode)(declare-const d RoundingMode)\
             (declare-const e RoundingMode)(assert (distinct r q c d e))"
                .to_string(),
            "sat",
        ),
        (
            "(declare-const c RoundingMode)(declare-const d RoundingMode)\
             (declare-const e RoundingMode)(declare-const f RoundingMode)\
             (assert (distinct r q c d e f))"
                .to_string(),
            "unsat",
        ),
        // Through an indexed conversion, and through a `let`.
        (
            "(assert (= a ((_ to_fp 8 24) RNE 2.5)))(assert (= ((_ fp.to_ubv 8) r a) #x03))\
             (assert (not (or (= r RTP) (= r RNA))))"
                .to_string(),
            "unsat",
        ),
        (
            "(assert (let ((m r)) (not (= (fp.mul m a b) (fp.mul r a b)))))".to_string(),
            "unsat",
        ),
    ] {
        assert_eq!(
            session(&format!("{d}{body}(check-sat)")),
            format!("{want}\n"),
            "{body}"
        );
    }
    // A model names the mode.
    assert_eq!(
        session(&format!(
            "{d}(assert (fp.lt {by_r} {third}))(assert (not (= r RTZ)))(check-sat)(get-value (r))"
        )),
        "sat\n((r RTN))\n"
    );
}

/// Quantifiers: an asserted `exists` or a denied `forall` has a witness of any width, and
/// one anywhere else is read once for each value of a small domain. The answers are z3's.
#[test]
fn quantifiers_are_witnessed_or_expanded() {
    let header = "(set-logic BV)
        (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
        (declare-const u (_ BitVec 64))";
    let cases: &[(&str, &str)] = &[
        (
            "(assert (forall ((z (_ BitVec 8))) (= (bvand z x) #x00))) (assert (not (= x #x00))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (exists ((z (_ BitVec 8))) (= (bvmul z #x02) (bvor x #x01)))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (exists ((z (_ BitVec 8))) (= (bvmul z #x03) x))) (assert (= x #x07)) (check-sat)",
            "sat",
        ),
        (
            "(assert (forall ((z (_ BitVec 8))) (= (bvand z x) (bvand x z)))) (check-sat)",
            "sat",
        ),
        (
            "(assert (not (forall ((z (_ BitVec 64))) (= (bvmul z u) z)))) (assert (= u #x0000000000000001)) (check-sat)",
            "unsat",
        ),
        (
            "(assert (not (forall ((z (_ BitVec 64))) (= (bvmul z u) z)))) (check-sat)",
            "sat",
        ),
        (
            "(assert (exists ((z (_ BitVec 64))) (and (= (bvadd z z) u) (= ((_ extract 0 0) u) #b1)))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (forall ((z (_ BitVec 4))) (exists ((t (_ BitVec 4))) (= (bvadd z t) #x0)))) (check-sat)",
            "sat",
        ),
        (
            "(assert (exists ((t (_ BitVec 4))) (forall ((z (_ BitVec 4))) (= (bvadd z t) #x0)))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (or (= x #x01) (forall ((z (_ BitVec 8))) (bvule z x)))) (assert (distinct x #x01)) (assert (distinct x #xff)) (check-sat)",
            "unsat",
        ),
        (
            "(assert (or (= x #x01) (forall ((z (_ BitVec 8))) (bvule z x)))) (assert (distinct x #x01)) (check-sat) (get-value (x))",
            "sat ((x #xff))",
        ),
        (
            "(assert (forall ((b Bool) (z (_ BitVec 4))) (=> b (= (bvxor z z) #x0)))) (check-sat)",
            "sat",
        ),
        (
            "(assert (exists ((a (_ BitVec 64)) (b (_ BitVec 64))) (and (= (bvadd a b) u) (= (bvsub a b) #x0000000000000004)))) (assert (= u #x0000000000000007)) (check-sat)",
            "unsat",
        ),
        (
            "(assert (exists ((z (_ BitVec 8))) (let ((q (bvadd z #x01))) (and (= q x) (bvult q z))))) (check-sat) (get-value (x))",
            "sat ((x #x00))",
        ),
        (
            "(assert (forall ((z (_ BitVec 8))) (! (= (bvor z x) z) :pattern ((bvor z x))))) (assert (distinct x #x00)) (check-sat)",
            "unsat",
        ),
    ];
    let cfg = crate::solve::Config::default();
    for (body, expected) in cases {
        let mut out = String::new();
        run(
            &mut Context::new(),
            &format!("{header}{body}"),
            &cfg,
            &mut out,
        )
        .unwrap();
        assert_eq!(
            out.split_whitespace().collect::<Vec<_>>().join(" "),
            *expected,
            "{body}"
        );
    }
    // A wide domain that needs every value is refused, not guessed.
    let err = crate::smtlib::import(
        &mut Context::new(),
        "(declare-const u (_ BitVec 64))
         (assert (forall ((z (_ BitVec 64))) (= (bvand z u) #x0000000000000000)))",
    )
    .unwrap_err();
    assert!(err.to_string().contains("quantifier"), "{err}");
}

/// What z3 prints for the divisions in `bit_vectors_above_512_bits_are_read_as_limbs`.
const WIDE_DIVISIONS: &str = "sat (((bvurem a b) #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000061d9)  ((bvsrem a b) #xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff28098)  ((bvsmod a b) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c2db)  ((bvudiv a (_ bv0 520)) #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)  (((_ extract 31 0) (bvudiv a b)) #x6fb6191a)  (((_ extract 31 0) (bvsdiv a b)) #xc8c55945))";

/// Bit-vectors above 512 bits are read as limbs: the operators that are limb by limb, a chain
/// of carries or a choice of limbs. The answers and the values are z3's.
#[test]
fn bit_vectors_above_512_bits_are_read_as_limbs() {
    let header = "(set-logic QF_BV)
        (declare-const x (_ BitVec 600)) (declare-const y (_ BitVec 600))";
    let cases: &[(&str, &str)] = &[
        (
            "(assert (= (bvlshr x (_ bv599 600)) (_ bv1 600))) (assert (= ((_ extract 7 0) x) #x5a))",
            "sat",
        ),
        ("(assert (bvult x y)) (assert (bvslt y x))", "sat"),
        (
            "(assert (= (bvadd x y) (_ bv12345678901234567890123456789012345678901234567890 600))) (assert (= x (bvmul y (_ bv3 600))))",
            "unsat",
        ),
        ("(assert (not (= (bvadd x y) (bvadd y x))))", "unsat"),
        (
            "(assert (not (= (concat ((_ extract 599 300) x) ((_ extract 299 0) x)) x)))",
            "unsat",
        ),
        (
            "(assert (not (= (bvadd (bvxor x y) (bvshl (bvand x y) (_ bv1 600))) (bvadd x y))))",
            "unsat",
        ),
        ("(assert (bvult x y)) (assert (bvult y x))", "unsat"),
        (
            "(assert (not (= (bvshl x (_ bv3 600)) (bvmul x (_ bv8 600)))))",
            "unsat",
        ),
        (
            "(assert (bvslt x (_ bv0 600))) (assert (= ((_ extract 599 599) x) #b0))",
            "unsat",
        ),
        (
            "(assert (not (= (bvsub x y) (bvadd x (bvneg y)))))",
            "unsat",
        ),
        ("(assert (= (bvadd x x) (_ bv1 600)))", "unsat"),
    ];
    let cfg = crate::solve::Config::default();
    for (body, expected) in cases {
        let mut out = String::new();
        run(
            &mut Context::new(),
            &format!("{header}{body}(check-sat)"),
            &cfg,
            &mut out,
        )
        .unwrap();
        assert_eq!(out.trim(), *expected, "{body}");
    }
    // Every operator at values: what z3 prints.
    let script = "(set-logic QF_BV) (declare-const x (_ BitVec 600)) (declare-const y (_ BitVec 600)) (declare-const s (_ BitVec 600)) (assert (= x ((_ repeat 75) #xa7))) (assert (= y (concat ((_ repeat 37) #x3c5e) #x12))) (assert (= s (_ bv77 600))) (check-sat) (get-value ((bvadd x y) (bvsub x y) (bvmul x y) (bvneg x) (bvshl x y) (bvlshr x s) (bvashr x s) (bvult x y) (bvsle x y) ((_ extract 598 3) x) ((_ extract 700 250) (concat x y)) ((_ sign_extend 300) x) ((_ rotate_left 131) x) (ite (bvult x y) (bvadd x x) (bvxor x y)) ((_ extract 63 0) (bvmul x (bvadd y y))) (bvcomp x y) (bvxnor x y)))";
    let expected = "sat (((bvadd x y) #xe405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405e405b9)  ((bvsub x y) #x6b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b496b4995)  ((bvmul x y) #x43e269078e2cb351d876fd9c22c147e66d0b9230b755dc7b01a026c54bea710f9634bb59e07f05a42ac94fee75139a38bf5de48309a82ecd53f279179e3cc361e8870dac32d157f67d1bbe)  ((bvneg x) #x585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585858585859)  ((bvshl x y) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)  ((bvlshr x s) #x000000000000000000053d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d)  ((bvashr x s) #xfffffffffffffffffffd3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d)  ((bvult x y) false)  ((bvsle x y) true)  (((_ extract 598 3) x) #x4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4)  (((_ extract 700 250) (concat x y)) #b0011110100111101001111010011110100111101001111010011110100111101001111010011110100111101001111010011100111100010111100011110001011110001111000101111000111100010111100011110001011110001111000101111000111100010111100011110001011110001111000101111000111100010111100011110001011110001111000101111000111100010111100011110001011110001111000101111000111100010111100011110001011110001111000101111000111100010111100011110001011110001111000101111000111100010111)  (((_ sign_extend 300) x) #xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7a7)  (((_ rotate_left 131) x) #x3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d3d)  ((ite (bvult x y) (bvadd x x) (bvxor x y)) #x9bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf99bf9b5)  (((_ extract 63 0) (bvmul x (bvadd y y))) #x5865a2afecfa377c)  ((bvcomp x y) #b0)  ((bvxnor x y) #x64066406640664066406640664066406640664066406640664066406640664066406640664066406640664066406640664066406640664066406640664066406640664066406640664064a))";
    let mut out = String::new();
    run(&mut Context::new(), script, &cfg, &mut out).unwrap();
    let squeeze = |s: &str| s.split_whitespace().collect::<String>();
    assert_eq!(squeeze(&out), squeeze(expected));
    // Divisions, by the schoolbook: quotient and remainder of values, a divisor of zero,
    // and the signed ones (the values are z3's).
    let script = "(declare-const a (_ BitVec 520)) (declare-const b (_ BitVec 520))
        (assert (= a (concat #xf1 ((_ repeat 64) #xa7)))) (assert (= b (_ bv1000003 520)))
        (check-sat)
        (get-value ((bvurem a b) (bvsrem a b) (bvsmod a b) (bvudiv a (_ bv0 520))
                    ((_ extract 31 0) (bvudiv a b)) ((_ extract 31 0) (bvsdiv a b))))";
    let mut out = String::new();
    run(&mut Context::new(), script, &cfg, &mut out).unwrap();
    assert_eq!(squeeze(&out), squeeze(WIDE_DIVISIONS), "{out}");
}

/// A rounding mode chosen by a condition, as an operand and compared. The answers are z3's.
#[test]
fn rounding_modes_are_chosen_by_conditions() {
    let header = "(set-logic QF_BVFP)
        (declare-const a Float32) (declare-const b Float32)
        (declare-const r RoundingMode) (declare-const q RoundingMode)
        (declare-const c Bool) (declare-const x (_ BitVec 32))";
    let cases: &[(&str, &str)] = &[
        (
            "(assert (not (= (fp.add (ite c RTP RTN) a b) (ite c (fp.add RTP a b) (fp.add RTN a b))))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= (ite c RTP RTN) RTP)) (assert (not c)) (check-sat)",
            "unsat",
        ),
        ("(assert (= (ite c RTP r) RTN)) (check-sat)", "sat"),
        (
            "(assert (not (= (fp.mul (ite c r RTZ) a b) (ite c (fp.mul r a b) (fp.mul RTZ a b))))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (not (= (fp.sqrt (ite c (ite (= x #x00000001) RNA r) q) a) (fp.sqrt (ite c (ite (= x #x00000001) RNA r) q) a)))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (distinct (fp.div (ite c RTP RTN) a b) (fp.div RTN a b))) (check-sat)",
            "sat",
        ),
        (
            "(assert (not (= ((_ to_fp 8 24) (ite c RTP RTN) x) (ite c ((_ to_fp 8 24) RTP x) ((_ to_fp 8 24) RTN x))))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (distinct ((_ fp.to_ubv 8) (ite c RTP RTN) a) ((_ fp.to_ubv 8) RTN a))) (assert (fp.lt a ((_ to_fp 8 24) RNE 3.0))) (assert (fp.gt a ((_ to_fp 8 24) RNE 2.0))) (check-sat)",
            "sat",
        ),
        (
            "(assert (distinct (fp.div (ite c RTP RTN) a b) (fp.div RTN a b))) (assert (not c)) (check-sat)",
            "unsat",
        ),
    ];
    let cfg = crate::solve::Config::default();
    for (body, expected) in cases {
        let mut out = String::new();
        run(
            &mut Context::new(),
            &format!("{header}{body}"),
            &cfg,
            &mut out,
        )
        .unwrap();
        assert_eq!(out.trim(), *expected, "{body}");
    }
}

/// Integers where bit-vectors bound them: `bv2nat`, numerals, arithmetic, quotients and
/// remainders by constants, comparisons, `int2bv`. The answers and values are z3's (which
/// does not answer the two identities within a minute; they are unsatisfiable).
#[test]
fn integers_are_read_where_bit_vectors_bound_them() {
    let header = "(set-logic ALL)
        (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
        (declare-const w (_ BitVec 32))";
    let cases: &[(&str, &str)] = &[
        ("(assert (>= (bv2nat x) 256)) (check-sat)", "unsat"),
        (
            "(assert (= (+ (bv2nat x) (bv2nat y)) 300)) (assert (= x #xc8)) (check-sat) (get-value ((bv2nat y) (- (bv2nat x) (bv2nat y)) (* (bv2nat x) (bv2nat y))))",
            "sat (((bv2nat y) 100) ((- (bv2nat x) (bv2nat y)) 100) ((* (bv2nat x) (bv2nat y)) 20000))",
        ),
        (
            "(assert (not (= ((_ int2bv 8) (mod (+ (bv2nat x) (bv2nat y)) 256)) (bvadd x y)))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (not (= ((_ int2bv 8) (bv2nat x)) x))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (= x #xf7)) (check-sat) (get-value ((div (bv2nat x) 10) (mod (bv2nat x) 10) (div (- (bv2nat x)) 10) (mod (- (bv2nat x)) 10) (div (bv2nat x) (- 7)) (mod (bv2nat x) (- 7)) (abs (- 5 (bv2nat x)))))",
            "sat (((div (bv2nat x) 10) 24) ((mod (bv2nat x) 10) 7) ((div (- (bv2nat x)) 10) (- 25)) ((mod (- (bv2nat x)) 10) 3) ((div (bv2nat x) (- 7)) (- 35)) ((mod (bv2nat x) (- 7)) 2) ((abs (- 5 (bv2nat x))) 242))",
        ),
        (
            "(assert (not (= ((_ int2bv 8) (div (* (bv2nat x) (bv2nat y)) 256)) ((_ extract 15 8) (bvmul ((_ zero_extend 8) x) ((_ zero_extend 8) y)))))) (check-sat)",
            "unsat",
        ),
        (
            "(assert (< 3 (bv2nat x) (bv2nat y) 6)) (check-sat) (get-value (x y))",
            "sat ((x #x04) (y #x05))",
        ),
        (
            "(assert (distinct (bv2nat x) (bv2nat y) 0 255)) (assert (bvult x #x02)) (assert (bvugt y #xfd)) (check-sat) (get-value (x y))",
            "sat ((x #x01) (y #xfe))",
        ),
        (
            "(assert (= (ite (bvult x y) (bv2nat x) (- (bv2nat y))) (- 200))) (check-sat) (get-value (y))",
            "sat ((y #xc8))",
        ),
        (
            "(assert (= (* (bv2nat w) (bv2nat w)) 18446744065119617025)) (check-sat) (get-value (w))",
            "sat ((w #xffffffff))",
        ),
        (
            "(assert (not (= ((_ int2bv 8) (- (bv2nat x))) (bvneg x)))) (check-sat)",
            "unsat",
        ),
        (
            "(define-fun n ((a (_ BitVec 8))) Int (+ (bv2nat a) 1)) (assert (let ((k (n x))) (and (> k 250) (= (mod k 2) 0)))) (check-sat) (get-value ((n x)))",
            "sat (((n x) 256))",
        ),
        (
            "(assert (= (mod (bv2nat x) 2) 1)) (assert (= ((_ extract 0 0) x) #b0)) (check-sat)",
            "unsat",
        ),
    ];
    let cfg = crate::solve::Config::default();
    let squeeze = |s: &str| s.split_whitespace().collect::<String>();
    for (body, expected) in cases {
        let mut out = String::new();
        run(
            &mut Context::new(),
            &format!("{header}{body}"),
            &cfg,
            &mut out,
        )
        .unwrap();
        assert_eq!(squeeze(&out), squeeze(expected), "{body}");
    }
    // An integer variable has no range, and a division by an unknown no meaning to give.
    for (script, why) in [
        ("(declare-const i Int)", "a variable of sort Int"),
        (
            "(declare-const x (_ BitVec 8)) (assert (= (div 7 (bv2nat x)) 1))",
            "by anything but a constant",
        ),
    ] {
        let mut out = String::new();
        run(&mut Context::new(), script, &cfg, &mut out).unwrap();
        assert!(out.contains(why), "{out}");
    }
}
