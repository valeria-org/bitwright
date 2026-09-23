//! Limits and robustness:
//!
//! - very deep linear chains (200k nodes in heavy runs) of several shapes (arithmetic, casts,
//!   selects over comparisons, unary counts, extension calls) go through evaluation, facts,
//!   proofs, constraints, printing and parsing, substitution, simplification, SMT-LIB export and
//!   the saturation search without overflowing the stack or panicking, and give right answers;
//! - a context at its node limit returns `ArenaFull` from every building path (builders,
//!   parser, substitution, extension calls, SMT-LIB import) and stays usable, and the engine
//!   reports the limit as how a run ended;
//! - hostile text (deep nesting, huge literals, widths 0 and 513, random token soup) gives
//!   errors, never panics, in the expression parser, the value parser and the SMT-LIB importer;
//! - results are deterministic: fresh contexts with different hash seeds and histories give the
//!   same facts, simplifications and exports.

mod common;

use std::collections::HashMap;

use bitwright::engine::{End, Engine, Exhausted, Run, Strategy};
use bitwright::{
    Assumptions, BinOp, BitVec, CmpOpExt, Context, ContextConfig, Error, Expr, ParseOptions,
    PrintOptions, Query, Substitution, SymbolKey, UnOp, Width,
};
use common::{Dag, GenConfig, Rng, SMOKE_WIDTHS, Size, WIDTHS, ext_context, registry, w};

// ----- deep chains ---------------------------------------------------------------------------

/// The chain shapes. Each step builds one new node on top of the previous one (and cheap leaves),
/// and computes the same step on values, so the expected value is known without the library's
/// evaluator.
#[derive(Copy, Clone, Debug)]
enum Chain {
    /// `e * k + y`, `e ^ y`, `e - k`, `rotl(e, y)`, `e >>u 1 | y` in turn.
    Arith,
    /// `trunc<64>(concat(e, bit_k))`: the value shifts left and takes in a bit of `y`.
    Casts,
    /// `select(e <u y, e + 1, e ^ y)`.
    Selects,
    /// `e + popcnt(e ^ y)`, `bitrev(e) - clz(e)`.
    Counts,
    /// `@hv.addc[0](e, y, bit_k)`.
    Ext,
}

const W64: Width = Width::W64;

fn bin(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::apply_bin(op, a, b).unwrap()
}

fn un(op: UnOp, a: &BitVec) -> BitVec {
    BitVec::apply_un(op, a).unwrap()
}

/// Builds a chain of `n` steps over `x` and `y` (64 bits), returning the root and the value at
/// `x = xv, y = yv`.
fn chain(cx: &mut Context, kind: Chain, n: usize, xv: BitVec, yv: BitVec) -> (Expr, BitVec) {
    let x = cx.symbol("x", W64).unwrap();
    let y = cx.symbol("y", W64).unwrap();
    let reg = cx.registry().map(|r| r.id("hv.addc").unwrap());
    let one = cx.one(W64).unwrap();
    let (mut e, mut v) = (x, xv);
    for k in 0..n {
        let kv = BitVec::wrapping_from_u64(W64, (k as u64).wrapping_mul(0x9e37_79b9) | 1);
        let ke = cx.constant(&kv).unwrap();
        let bit = (k % 64) as u16;
        let bv = yv.extract(bit, Width::W1).unwrap();
        let be = cx.extract(y, bit, Width::W1).unwrap();
        (e, v) = match kind {
            Chain::Arith => match k % 5 {
                0 => {
                    let m = cx.mul(e, ke).unwrap();
                    (
                        cx.add(m, y).unwrap(),
                        bin(BinOp::Add, &bin(BinOp::Mul, &v, &kv), &yv),
                    )
                }
                1 => (cx.xor(e, y).unwrap(), bin(BinOp::Xor, &v, &yv)),
                2 => (cx.sub(e, ke).unwrap(), bin(BinOp::Sub, &v, &kv)),
                3 => (
                    cx.bin(BinOp::RotL, e, y).unwrap(),
                    bin(BinOp::RotL, &v, &yv),
                ),
                _ => {
                    let s = cx.bin(BinOp::LShr, e, one).unwrap();
                    (
                        cx.or(s, y).unwrap(),
                        bin(BinOp::Or, &bin(BinOp::LShr, &v, &BitVec::one(W64)), &yv),
                    )
                }
            },
            Chain::Casts => {
                let c = cx.concat(e, be).unwrap();
                let cv = BitVec::concat(&v, &bv).unwrap();
                (cx.trunc(c, W64).unwrap(), cv.trunc(W64).unwrap())
            }
            Chain::Selects => {
                let c = cx.cmp(CmpOpExt::Ult, e, y).unwrap();
                let t = cx.add(e, one).unwrap();
                let f = cx.xor(e, y).unwrap();
                let taken = BitVec::apply_cmp(CmpOpExt::Ult, &v, &yv).unwrap();
                (
                    cx.select(c, t, f).unwrap(),
                    if taken {
                        bin(BinOp::Add, &v, &BitVec::one(W64))
                    } else {
                        bin(BinOp::Xor, &v, &yv)
                    },
                )
            }
            Chain::Counts => {
                if k % 2 == 0 {
                    let xr = cx.xor(e, y).unwrap();
                    let p = cx.un(UnOp::Popcnt, xr).unwrap();
                    (
                        cx.add(e, p).unwrap(),
                        bin(BinOp::Add, &v, &un(UnOp::Popcnt, &bin(BinOp::Xor, &v, &yv))),
                    )
                } else {
                    let r = cx.un(UnOp::BitRev, e).unwrap();
                    let c = cx.un(UnOp::Clz, e).unwrap();
                    (
                        cx.sub(r, c).unwrap(),
                        bin(BinOp::Sub, &un(UnOp::BitRev, &v), &un(UnOp::Clz, &v)),
                    )
                }
            }
            Chain::Ext => {
                let id = reg.expect("an extension chain needs the test registry");
                let out = cx.ext(id, &[e, y, be]).unwrap();
                let s = bin(
                    BinOp::Add,
                    &bin(BinOp::Add, &v, &yv),
                    &bv.zext(W64).unwrap(),
                );
                (out[0], s)
            }
        };
    }
    (e, v)
}

fn deep_chains(size: Size) {
    let n = size.pick(600, 200_000);
    let reg = registry();
    let xv = BitVec::wrapping_from_u64(W64, 0x0123_4567_89ab_cdef);
    let yv = BitVec::wrapping_from_u64(W64, 0xfedc_ba98_7654_3211);
    let env: HashMap<SymbolKey, BitVec> =
        [(SymbolKey::from("x"), xv), (SymbolKey::from("y"), yv)].into();
    for kind in [
        Chain::Arith,
        Chain::Casts,
        Chain::Selects,
        Chain::Counts,
        Chain::Ext,
    ] {
        let what = format!("{kind:?} chain of {n}");
        let mut cx = ext_context(&reg);
        let (e, want) = chain(&mut cx, kind, n, xv, yv);
        assert!(cx.height(e).unwrap() as usize >= n / 2, "{what}: height");

        // Evaluation, traversal and metadata.
        assert_eq!(cx.eval(&[e], &env).unwrap()[0], want, "{what}: eval");
        let order = cx.post_order(&[e]).unwrap();
        assert!(order.len() >= n, "{what}: post_order");
        assert_eq!(cx.symbols_in(&[e]).unwrap().len(), 2, "{what}: symbols");
        assert_eq!(
            cx.dag_size(&[e], 10).unwrap(),
            bitwright::Bounded::AtLeast(11),
            "{what}: bounded dag_size"
        );

        // Facts, proofs, enumeration, and constraints on the root.
        let f = cx.facts(e).unwrap();
        assert!(f.contains(&want), "{what}: facts {f:?} exclude {want}");
        let t = cx.prove(Query::IsZero(e)).unwrap();
        assert_ne!(t, bitwright::Truth::True, "{what}: proved zero");
        let _ = cx.enumerate_values(e, 16).unwrap();
        let mut a = Assumptions::new();
        let c = cx.constant(&want).unwrap();
        let p = cx.cmp(CmpOpExt::Eq, e, c).unwrap();
        a.assume_true(&mut cx, p).unwrap();
        let fx = cx.facts_with(e, &a).unwrap().expect("feasible");
        assert!(fx.contains(&want), "{what}: facts under a true constraint");

        // Printing: bounded by default; unbounded text parses back to the same node.
        let short = cx.display(e).to_string();
        assert!(
            short.len() <= PrintOptions::default().max_chars + 4096
                && (order.len() <= PrintOptions::default().max_nodes || short.contains('…')),
            "{what}: the default print is bounded and marked, but has {} characters",
            short.len()
        );
        let text = cx.display_with(e, unbounded()).to_string();
        let back = cx.parse(&text, &ParseOptions::default()).unwrap();
        assert_eq!(back, e, "{what}: parse(display(e))");

        // Substitution, plain and bounded: y := x.
        let x = cx.find_symbol(&SymbolKey::from("x")).unwrap();
        let y = cx.find_symbol(&SymbolKey::from("y")).unwrap();
        let r = cx.substitute(&[e], &[(y, x)]).unwrap()[0];
        let (_, want_r) = {
            let mut other = ext_context(&reg);
            chain(&mut other, kind, n, xv, xv)
        };
        assert_eq!(
            cx.eval(&[r], &env).unwrap()[0],
            want_r,
            "{what}: substitute"
        );
        let mut sub = Substitution::new();
        sub.replace(&cx, y, x).unwrap();
        let bounded = loop {
            if let Some(v) = cx.substitute_bounded(&[e], &mut sub, 4096).unwrap() {
                break v[0];
            }
        };
        assert_eq!(bounded, r, "{what}: substitute_bounded");

        // Simplification: a result equal at the point (and no stack overflow).
        for engine in [
            Engine::standard(),
            Engine::builder()
                .builtin()
                .strategy(Strategy::deobfuscate())
                .build()
                .unwrap(),
        ] {
            let out = engine.run(&mut cx, &[e], Run::default()).unwrap();
            let s = out.roots[0].expr;
            assert_eq!(cx.eval(&[s], &env).unwrap()[0], want, "{what}: simplified");
        }

        #[cfg(feature = "smtlib")]
        {
            let script = bitwright::smtlib::export(&mut cx, &[e]).unwrap();
            if !matches!(kind, Chain::Ext) {
                // Operators without a QF_BV counterpart export as expansions, so the import can
                // outgrow the node limit: that must be an error, not a panic.
                let mut other = Context::new();
                match bitwright::smtlib::import(&mut other, &script) {
                    Ok(back) => {
                        let root = back.definition("root0").unwrap();
                        assert_eq!(
                            other.eval(&[root], &env).unwrap()[0],
                            want,
                            "{what}: SMT-LIB"
                        );
                    }
                    Err(Error::ArenaFull { .. }) => {}
                    Err(err) => panic!("{what}: SMT-LIB import: {err}"),
                }
            }
        }
        #[cfg(feature = "eqsat")]
        {
            use bitwright::eqsat::{SaturateConfig, Saturator, SearchRun};
            let (sat, _) = Saturator::builtin(SaturateConfig::default());
            let out = sat.search(&mut cx, &[e], SearchRun::default()).unwrap();
            if let Some(c) = out.roots[0].candidate {
                assert_eq!(cx.eval(&[c], &env).unwrap()[0], want, "{what}: eqsat");
            }
        }
    }
}

#[test]
fn deep_chains_need_no_recursion_smoke() {
    deep_chains(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn deep_chains_need_no_recursion_heavy() {
    deep_chains(Size::Heavy);
}

// ----- the node limit ------------------------------------------------------------------------

fn arena_full<T: std::fmt::Debug>(r: Result<T, Error>, what: &str) -> Option<T> {
    match r {
        Ok(v) => Some(v),
        Err(Error::ArenaFull { .. }) => None,
        Err(e) => panic!("{what}: expected ArenaFull, got {e:?}"),
    }
}

/// Grows a random DAG in a context limited to `limit` nodes through every building path until
/// the limit refuses more; every refusal is `ArenaFull`, and the nodes already built still
/// evaluate, have facts, print and simplify.
fn node_limit(size: Size) {
    let reg = registry();
    let limits: Vec<u32> = size.pick(
        vec![1, 2, 3, 5, 8, 40, 200],
        (1..=64).chain([100, 200, 500, 1000, 5000]).collect(),
    );
    for &limit in &limits {
        for seed in 0..size.pick(2, 20u64) {
            let what = format!("limit {limit}, seed {seed}");
            let mut rng = Rng(0x11_0000 + u64::from(limit) * 0x100 + seed);
            let mut cx =
                Context::with_registry(ContextConfig::default().with_max_nodes(limit), reg.clone());
            let widths = [1u16, 8, 64, 65, 512];
            let mut pool: Vec<Expr> = Vec::new();
            let addc = reg.id("hv.addc").unwrap();
            for step in 0..(limit as usize + 20) * 2 {
                let n = w(rng.pick(&widths));
                let same: Vec<Expr> = pool
                    .iter()
                    .copied()
                    .filter(|&e| cx.width(e).unwrap() == n)
                    .collect();
                let pick = |rng: &mut Rng| (!same.is_empty()).then(|| rng.pick(&same));
                let r = match step % 9 {
                    0 => cx.symbol(format!("v{}_{}", step % 5, n.bits()).as_str(), n),
                    1 => cx.constant(&rng.bitvec(n)),
                    2 => match (pick(&mut rng), pick(&mut rng)) {
                        (Some(a), Some(b)) => cx.bin(rng.pick(&BinOp::ALL), a, b),
                        _ => continue,
                    },
                    3 => match (pick(&mut rng), pick(&mut rng)) {
                        (Some(a), Some(b)) => cx.umax(a, b),
                        _ => continue,
                    },
                    4 => cx.parse(
                        &format!("(p{step}:{b} + 1) * q{b}:{b}", b = n.bits()),
                        &ParseOptions::default(),
                    ),
                    5 => match (pick(&mut rng), pick(&mut rng)) {
                        (Some(a), Some(b)) => {
                            let c = cx.fresh_symbol(Width::W1);
                            match arena_full(c, &what) {
                                Some(c) => cx.ext(addc, &[a, b, c]).map(|o| o[0]),
                                None => continue,
                            }
                        }
                        _ => continue,
                    },
                    6 => match (pick(&mut rng), pick(&mut rng)) {
                        (Some(a), Some(b)) => cx.substitute(&[a], &[(b, a)]).map(|v| v[0]),
                        _ => continue,
                    },
                    7 => match pick(&mut rng) {
                        Some(a) if n.bits() < 512 => cx.zext(a, w(n.bits() + 1)),
                        _ => continue,
                    },
                    _ => {
                        #[cfg(feature = "smtlib")]
                        {
                            let src = format!(
                                "(declare-const s{step} (_ BitVec {b})) \
                                 (define-fun d () (_ BitVec {b}) (bvmul (bvadd s{step} #b{one}) s{step}))",
                                b = n.bits(),
                                one = "1".repeat(usize::from(n.bits())),
                            );
                            match bitwright::smtlib::import(&mut cx, &src) {
                                Ok(s) => Ok(s.definition("d").unwrap()),
                                Err(e) => Err(e),
                            }
                        }
                        #[cfg(not(feature = "smtlib"))]
                        continue;
                    }
                };
                if let Some(e) = arena_full(r, &what) {
                    pool.push(e);
                }
                assert!(cx.len() <= limit as usize, "{what}: {} nodes", cx.len());
            }
            // Everything built still works (every symbol bound to 0x5555…).
            let env = |_: &SymbolKey, width: Width| Some(BitVec::wrapping_from_u64(width, 0x5555));
            for &e in &pool {
                cx.eval(&[e], &bitwright::FnEnv(env)).unwrap();
                cx.facts(e).unwrap();
                assert!(!cx.display(e).to_string().is_empty());
            }
            if let Some(&e) = pool.last() {
                let out = Engine::standard()
                    .run(&mut cx, &[e], Run::default())
                    .unwrap();
                let end = out.roots[0].end;
                assert!(
                    matches!(
                        end,
                        End::Completed | End::BudgetTerminated(Exhausted::ArenaCapacity)
                    ),
                    "{what}: the engine ended {end:?}"
                );
                let before = cx.eval(&[e], &bitwright::FnEnv(env)).unwrap();
                let after = cx
                    .eval(&[out.roots[0].expr], &bitwright::FnEnv(env))
                    .unwrap();
                assert_eq!(before, after, "{what}: simplified at the limit");
            }
        }
    }
}

#[test]
fn the_node_limit_is_an_error_everywhere_smoke() {
    node_limit(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn the_node_limit_is_an_error_everywhere_heavy() {
    node_limit(Size::Heavy);
}

fn unbounded() -> PrintOptions {
    PrintOptions::default()
        .with_max_nodes(usize::MAX)
        .with_max_chars(usize::MAX)
}

// ----- hostile text --------------------------------------------------------------------------

/// Inputs every parser must refuse (or accept) without panicking.
fn hostile_expressions(n: usize) -> Vec<String> {
    let mut v: Vec<String> = [
        "",
        " ",
        "(",
        ")",
        "x:0",
        "x:513",
        "x:65535",
        "x:65536",
        "x:99999999999999999999",
        "0:0",
        "1:513",
        "0x1:0",
        "-0:0",
        "zext<0>(x:8)",
        "zext<513>(x:8)",
        "zext<65536>(x:8)",
        "sext<8>(x:8)",
        "trunc<0>(x:8)",
        "trunc<9>(x:8)",
        "extract<0, 0>(x:8)",
        "extract<8, 1>(x:8)",
        "extract<7, 2>(x:8)",
        "extract<65535, 1>(x:8)",
        "extract<1, 65535>(x:8)",
        "concat(x:256, y:257)",
        "bswap(x:7)",
        "select(c:2, a:8, b:8)",
        "@",
        "@x",
        "@x()",
        "@x[9](y:8)",
        "@hv.addc[3](a:8, b:8, c:1)",
        "@hv.addc[256](a:8)",
        "let %0 = x:8; let %0 = y:8; %0",
        "let %0 = %0; %0",
        "%0",
        "%99999999999999999999",
        "x:8 +",
        "+ x:8",
        "x:8 ++ y:8",
        "x:8 >> y:8",
        "x:8 < y:8",
        "x:8 == y:16",
        "\u{0}",
        "\u{feff}x:8",
        "x\u{0}:8",
        "é:8",
        "x:8 # comment",
        "0b:8",
        "0x:8",
        "8'h",
        "8'hfff",
        "0'h0",
        "513'h0",
        "-0x81:8",
        "99999999999999999999999999999999999999999:8",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    v.push(format!("{}x:8{}", "(".repeat(n), ")".repeat(n)));
    v.push(format!("{}x:8", "-".repeat(n)));
    v.push(format!("{}x:8", "~".repeat(n)));
    v.push(format!("{}x:8{}", "popcnt(".repeat(n), ")".repeat(n)));
    v.push(format!("{}x:8{}", "zext<8>(".repeat(n), ")".repeat(n)));
    v.push(format!("{}x:8", "x:8 + ".repeat(n)));
    v.push(format!("0x{}:512", "f".repeat(n)));
    v.push(format!("{}:512", "9".repeat(n)));
    v.push(format!("0x{}:8", "0".repeat(n)));
    v.push("x".repeat(n) + ":8");
    v.push(format!("x:{}", "9".repeat(n)));
    v.push(
        (0..n)
            .map(|k| format!("let %{k} = %{};\n", k + 1))
            .collect::<String>()
            + "%0",
    );
    v
}

/// Random soup from the syntax's own tokens (deterministic).
fn token_soup(rng: &mut Rng) -> String {
    const TOKENS: [&str; 48] = [
        "x", "y:8", "z:64", "0", "1", "0xff:8", "-1:8", "8'h7f", "(", ")", "<", ">", ",", ";", "+",
        "-", "*", "&", "|", "^", "~", "<<", ">>u", ">>s", "<u", "<=s", "==", "!=", "zext", "sext",
        "trunc", "extract", "concat", "select", "udiv", "rotl", "popcnt", "let", "%0", "%1", "=",
        "@hv.addc", "[1]", ":", "512", "0", "umin", "abs",
    ];
    let len = 1 + rng.below(24);
    (0..len)
        .map(|_| rng.pick(&TOKENS))
        .collect::<Vec<_>>()
        .join(if rng.chance(1, 2) { " " } else { "" })
}

fn hostile_text(size: Size) {
    let reg = registry();
    let n = size.pick(600, 200_000);
    for src in hostile_expressions(n) {
        for opts in [
            ParseOptions::default(),
            ParseOptions::width(Width::W8),
            ParseOptions::width(Width::W512),
        ] {
            let mut cx = ext_context(&reg);
            if let Ok(e) = cx.parse(&src, &opts) {
                // Accepted text is a real expression: it prints and parses back.
                let text = cx.display_with(e, unbounded()).to_string();
                assert_eq!(cx.parse(&text, &opts).ok(), Some(e), "{src:.80}");
            }
        }
        let _ = BitVec::parse(&src);
    }
    let mut rng = Rng(0x50_0000);
    for _ in 0..size.pick(3_000, 1_000_000) {
        let src = token_soup(&mut rng);
        let mut cx = ext_context(&reg);
        if let Ok(e) = cx.parse(&src, &ParseOptions::width(Width::W8)) {
            let text = cx.display(e).to_string();
            assert_eq!(
                cx.parse(&text, &ParseOptions::width(Width::W8)).ok(),
                Some(e),
                "`{src}` printed as `{text}`"
            );
        }
    }
}

#[test]
fn hostile_text_is_an_error_not_a_panic_smoke() {
    hostile_text(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn hostile_text_is_an_error_not_a_panic_heavy() {
    hostile_text(Size::Heavy);
}

/// Hostile SMT-LIB: deep nesting, bad widths, huge literals, out-of-range extracts, token soup.
#[cfg(feature = "smtlib")]
fn hostile_smtlib(size: Size) {
    use bitwright::smtlib::import;
    let n = size.pick(600, 200_000);
    let decl = "(declare-const x (_ BitVec 8))";
    let mut scripts: Vec<String> = [
        "(declare-const x (_ BitVec 0))",
        "(declare-const x (_ BitVec 513))",
        "(declare-const x (_ BitVec 99999999999999999999))",
        "(declare-const x (_ BitVec -1))",
        "(define-fun f () (_ BitVec 8) (_ bv256 8))",
        "(define-fun f () (_ BitVec 8) (_ bv99999999999999999999999999 8))",
        "(define-fun f () (_ BitVec 8) ((_ extract 8 0) x))",
        "(define-fun f () (_ BitVec 8) ((_ extract 0 7) x))",
        "(define-fun f () (_ BitVec 8) ((_ zero_extend 600) x))",
        "(define-fun f () (_ BitVec 8) ((_ rotate_left 99999999999999999999) x))",
        "(define-fun f () (_ BitVec 8) ((_ repeat 0) x))",
        "(define-fun f () (_ BitVec 8) ((_ repeat 100) x))",
        "(define-fun f ((y (_ BitVec 8))) (_ BitVec 8) y)",
        "(define-fun f () (_ BitVec 8) (bvadd x))",
        "(define-fun f () (_ BitVec 8) (let ((x x)) x))",
        "(define-fun f () (_ BitVec 8) |unterminated)",
        "(assert (= x #b))",
        "(assert (= x #x))",
        "(assert (= x #xg0))",
        "(check-sat",
        ")",
        "((((",
        "(declare-fun g ((_ BitVec 8)) (_ BitVec 8))",
    ]
    .iter()
    .map(|s| format!("{decl}\n{s}"))
    .collect();
    scripts.push(format!(
        "{decl}(define-fun f () (_ BitVec 8) {}x{})",
        "(bvnot ".repeat(n),
        ")".repeat(n)
    ));
    scripts.push(format!(
        "{decl}(define-fun f () (_ BitVec 8) {}x{})",
        "(let ((y x)) ".repeat(n),
        ")".repeat(n)
    ));
    scripts.push(format!("{decl}(assert {}", "(".repeat(n)));
    scripts.push(format!("{decl}(assert (= x #b{}))", "1".repeat(n)));
    scripts.push(format!("{decl}(assert (= x #x{}))", "f".repeat(n)));
    for s in &scripts {
        let mut cx = Context::new();
        let _ = import(&mut cx, s);
    }
    let mut rng = Rng(0x5a_0000);
    const TOKENS: [&str; 30] = [
        "(",
        ")",
        "declare-const",
        "define-fun",
        "assert",
        "x",
        "y",
        "(_ BitVec 8)",
        "_",
        "BitVec",
        "8",
        "0",
        "bvadd",
        "bvudiv",
        "ite",
        "let",
        "=",
        "distinct",
        "and",
        "#b1",
        "#xff",
        "(_ bv1 8)",
        "extract",
        "zero_extend",
        "true",
        "|a b|",
        "()",
        "concat",
        "bvsmod",
        "not",
    ];
    for _ in 0..size.pick(3_000, 1_000_000) {
        let len = 1 + rng.below(30);
        let src: Vec<&str> = (0..len).map(|_| rng.pick(&TOKENS)).collect();
        let mut cx = Context::new();
        let _ = import(&mut cx, &src.join(" "));
    }
}

#[cfg(feature = "smtlib")]
#[test]
fn hostile_smtlib_is_an_error_not_a_panic_smoke() {
    hostile_smtlib(Size::Smoke);
}

#[cfg(feature = "smtlib")]
#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn hostile_smtlib_is_an_error_not_a_panic_heavy() {
    hostile_smtlib(Size::Heavy);
}

// ----- determinism -----------------------------------------------------------------------------

/// What a DAG gives: the printed facts of every node and the printed simplifications, and with
/// `exact` also the run statistics and the SMT-LIB export (whose internal names follow arena
/// positions), which depend on the history.
fn fingerprint(size: Size, seed: u64, hash_seed: u64, junk: u64, exact: bool) -> Vec<String> {
    let reg = registry();
    let mut cx = Context::with_registry(
        ContextConfig::default().with_hash_seed(hash_seed),
        reg.clone(),
    );
    // Unrelated nodes first.
    let j = cx.symbol("junk", Width::W16).unwrap();
    let mut acc = j;
    let mut jr = Rng(junk);
    for _ in 0..jr.below(64) {
        let c = cx.constant(&jr.bitvec(Width::W16)).unwrap();
        acc = cx.bin(jr.pick(&BinOp::ALL), acc, c).unwrap();
    }
    let mut rng = Rng(0xde7_0000 + seed);
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    let mut cfg = if seed.is_multiple_of(2) {
        GenConfig::small(&mut rng, 6, 4)
    } else {
        GenConfig::wide(&mut rng, &widths, 3)
    };
    cfg.ext = seed.is_multiple_of(3);
    let rw = rng.pick(&cfg.widths.clone());
    let mut dag = Dag::new(&mut cx, cfg);
    let i = dag.random(&mut cx, &mut rng, rw);
    let e = dag.expr(i);
    let mut out = Vec::new();
    for x in cx.post_order(&[e]).unwrap() {
        let f = cx.facts(x).unwrap();
        out.push(format!("{} : {f:?}", cx.display(x)));
    }
    for engine in [
        Engine::standard(),
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap(),
    ] {
        let r = engine.run(&mut cx, &[e], Run::default()).unwrap();
        out.push(cx.display(r.roots[0].expr).to_string());
        // Statistics count nodes the run created, and a node an unrelated earlier build made
        // already is not new: they depend on the history, so only the hash seed must not
        // change them.
        if exact {
            out.push(format!("{:?}", r.stats));
        }
    }
    #[cfg(feature = "smtlib")]
    if exact {
        out.push(bitwright::smtlib::export(&mut cx, &[e]).unwrap());
    }
    out
}

/// The same history with different hash seeds gives identical results, statistics and SMT-LIB
/// text included; a different history gives identical facts and simplifications.
fn determinism(size: Size) {
    for seed in 0..size.pick(20, 20_000u64) {
        let a = fingerprint(size, seed, 0, 1, true);
        let b = fingerprint(size, seed, 0x0123_4567_89ab_cdef ^ seed, 1, true);
        assert_eq!(a, b, "seed {seed:#x}: hash seed");
        let a = fingerprint(size, seed, 0, 1, false);
        let c = fingerprint(size, seed, 0x0123_4567_89ab_cdef ^ seed, 2 + seed, false);
        assert_eq!(a, c, "seed {seed:#x}: history");
    }
}

#[test]
fn results_are_independent_of_hash_seed_and_history_smoke() {
    determinism(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn results_are_independent_of_hash_seed_and_history_heavy() {
    determinism(Size::Heavy);
}
