//! The native MBA solver through the engine, on bitwright's own evidence only (backend
//! certificates and sampling off): the MBA catalog at several widths, its negative cases,
//! adversarial solvers, no regression against the signature solver, determinism, and budgets.
//! Equivalence is checked by the bit-serial reference over both canonical DAGs.
#![cfg(feature = "mba")]

mod common;

use std::sync::Arc;

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::mba::{
    Claim, MNode, MOp, MbaAnswer, MbaBudget, MbaConfig, MbaExpr, MbaSolver, MbaTrust, NfOptions,
    NormalFormSolver, SignatureSolver,
};
use bitwright::{BitVec, Bounded, Context, Expr, ParseOptions, SymbolKey, Width};
use common::{Canonical, Rng, every_env};

fn trust_off() -> MbaConfig {
    MbaConfig::default().with_trust(MbaTrust::default().with_backend_certificates(false))
}

fn engine(solver: Arc<dyn MbaSolver>) -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(trust_off()))
        .mba_solver(solver)
        .build()
        .unwrap()
}

fn native() -> Engine {
    engine(Arc::new(NormalFormSolver::default()))
}

fn dag_size(cx: &mut Context, e: Expr) -> u32 {
    match cx.dag_size(&[e], u32::MAX).unwrap() {
        Bounded::Exact(n) => n,
        other => panic!("{other:?}"),
    }
}

/// Panics unless `a` and `b` agree (by the reference) at every input when the symbols have at
/// most 12 bits, else at boundary-biased and random points.
fn assert_equivalent(cx: &mut Context, a: Expr, b: Expr, what: &str) {
    let syms: Vec<(SymbolKey, Width)> = cx
        .symbols_in(&[a, b])
        .unwrap()
        .into_iter()
        .map(|id| {
            (
                cx.symbol_key(id).unwrap().clone(),
                cx.symbol_width(id).unwrap(),
            )
        })
        .collect();
    let mut rng = Rng(0x5eed ^ syms.len() as u64);
    let envs: Vec<Vec<BitVec>> = every_env(&syms, 12).unwrap_or_else(|| {
        (0..200)
            .map(|k| {
                syms.iter()
                    .map(|(_, w)| {
                        if k % 2 == 0 {
                            rng.biased(*w)
                        } else {
                            rng.bitvec(*w)
                        }
                    })
                    .collect()
            })
            .collect()
    });
    let dag = Canonical::new(cx, &[a, b]);
    for vals in envs {
        let env: Vec<(SymbolKey, BitVec)> = syms.iter().map(|s| s.0.clone()).zip(vals).collect();
        let v = dag.eval(&env, &[]);
        assert_eq!(
            v[0],
            v[1],
            "{what}: `{}` and `{}` differ at {env:?}",
            cx.display(a),
            cx.display(b)
        );
    }
}

/// `2^(w−1)`, as a literal.
fn half(w: u16) -> String {
    format!("{}", BitVec::smin(Width::new(w).unwrap()))
        .split(':')
        .next()
        .unwrap()
        .to_string()
}

/// Simplifies `src` at each width with the native engine: the result must equal the input and
/// be no larger than `want` (both with `{half}` for 2^(W−1)).
fn catalog(src: &str, want: &str, widths: &[u16]) {
    let eng = native();
    for &w in widths {
        let o = ParseOptions::width(Width::new(w).unwrap());
        let (src, want) = (
            src.replace("{half}", &half(w)),
            want.replace("{half}", &half(w)),
        );
        let mut cx = Context::new();
        let e = cx.parse(&src, &o).unwrap();
        let goal = cx.parse(&want, &o).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0].expr;
        assert_equivalent(&mut cx, e, r, &src);
        let (got, limit) = (dag_size(&mut cx, r), dag_size(&mut cx, goal));
        assert!(
            got <= limit,
            "w={w}: `{src}` gave `{}` ({got} nodes), want `{want}` ({limit})",
            cx.display(r)
        );
        assert_eq!(out.stats.mba.proof_unknown, 0, "w={w}: `{src}`");
    }
}

const WIDTHS: [u16; 6] = [8, 16, 32, 64, 128, 512];

#[test]
fn the_linear_catalog() {
    catalog("(x ^ y) + 2*(x & y)", "x + y", &WIDTHS);
    catalog("(x | y) - (x & y)", "x ^ y", &WIDTHS);
    catalog("(x & ~y) - (~x & y)", "x - y", &WIDTHS);
}

#[test]
fn the_semi_linear_catalog() {
    catalog("(x ^ 0x10) + 2*(x & 0x10)", "x + 0x10", &WIDTHS);
    catalog("(x & 0xff) + (x & 0xff00)", "x & 0xffff", &WIDTHS[1..]);
    catalog("3*(x & 0x55) + 3*(x & 0xaa)", "3*(x & 0xff)", &WIDTHS);
}

#[test]
fn the_polynomial_catalog() {
    // Degree-2 certificates at 512 bits are over the effort cap: checked up to 128 bits.
    catalog(
        "(x & y)*(x | y) + (x & ~y)*(~x & y)",
        "x*y",
        &[8, 16, 32, 64, 128],
    );
    catalog("{half}*(x*x + x)", "0", &WIDTHS);
    catalog("(x + 1)*(x + 1) - x*x - 2*x", "1", &WIDTHS);
    catalog(
        "x*(x & y) + y*(x & y) - (x & y)*(x & y)",
        "(x | y)*(x & y)",
        &[8, 16, 32, 64],
    );
}

#[test]
fn the_synthesis_catalog() {
    // Products the input has only multiplied out, found in the synthesis table. The gate's
    // degree-2 certificates over two variables fit up to 128 bits here.
    const UP_TO_128: [u16; 5] = [8, 16, 32, 64, 128];
    catalog("x*y + x + y + 1", "~x * ~y", &UP_TO_128);
    catalog("x*y - x - y + 1", "(1 - x)*(1 - y)", &UP_TO_128);
    catalog("x*x + 2*x*y + y*y", "(x + y)*(x + y)", &UP_TO_128);
    catalog("x*y + x*z + y + z", "(x + 1)*(y + z)", &[8, 16, 32, 64]);
}

#[test]
fn the_abstraction_catalog() {
    catalog("((x + y) & z) + ((x + y) & ~z)", "x + y", &WIDTHS);
    catalog("((x ^ y) + 2*(x & y)) & z", "(x + y) & z", &WIDTHS);
}

/// `x + [x = K]`, spelled `x + (~((x ^ K) | -(x ^ K)) >>u (W−1))`, for a random `K`.
fn point_function(w: u16, rng: &mut Rng) -> (String, BitVec) {
    let width = Width::new(w).unwrap();
    let k = rng.bitvec(width);
    let ks = format!("{k}").split(':').next().unwrap().to_string();
    (
        format!("x + (~((x ^ {ks}) | -(x ^ {ks})) >>u {})", w - 1),
        k,
    )
}

#[test]
fn negatives_stay_or_are_only_re_rendered_equal() {
    let eng = native();
    let mut rng = Rng(0x9e9);
    for w in [8u16, 64, 128] {
        let o = ParseOptions::width(Width::new(w).unwrap());
        let (point, key) = point_function(w, &mut rng);
        for src in [
            "x*y - (x & y)".to_string(),
            "(x & ~y)*(~x & y)".to_string(),
            "x + w*w - w".to_string(),
            point.clone(),
        ] {
            let mut cx = Context::new();
            let e = cx.parse(&src, &o).unwrap();
            let before = dag_size(&mut cx, e);
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            let r = out.roots[0].expr;
            assert_equivalent(&mut cx, e, r, &src);
            assert!(dag_size(&mut cx, r) <= before, "`{src}` grew");
            // `w` must stay: `w² − w` is not zero.
            if src.contains("w*w") {
                assert!(cx.display(r).to_string().contains('w'), "{}", cx.display(r));
            }
            // The point function is never x.
            let x = cx.parse("x", &o).unwrap();
            assert_ne!(r, x, "`{src}`");
            if src == point {
                let xs = cx.find_symbol(&SymbolKey::from("x")).unwrap();
                let v = cx
                    .eval(
                        &[r],
                        &bitwright::FnEnv(|k: &SymbolKey, _| {
                            (*k == SymbolKey::from("x")).then_some(key)
                        }),
                    )
                    .unwrap()[0];
                let _ = xs;
                assert_eq!(
                    v,
                    BitVec::apply_bin(bitwright::BinOp::Add, &key, &BitVec::one(key.width()))
                        .unwrap()
                );
            }
        }
    }
}

// ----- adversarial solvers ------------------------------------------------------------------

/// A copy of `p`'s nodes, then `extra(m, root)` built on its root.
fn with(p: &MbaExpr, extra: impl FnOnce(&mut MbaExpr, u32) -> u32) -> MbaExpr {
    let mut m = MbaExpr::new(p.vars().to_vec());
    for n in p.nodes() {
        let args = &n.args[..n.op.arity()];
        match n.op {
            MOp::Zext | MOp::Sext | MOp::Trunc => m.push_cast(n.op, args[0], n.width),
            op => m.push(op, args),
        }
        .unwrap();
    }
    let root = m.root().unwrap();
    extra(&mut m, root);
    m
}

/// Answers the input plus `(x & ~y)·(~x & y)`: wrong, but right at every corner.
struct CornerLiar;
impl MbaSolver for CornerLiar {
    fn id(&self) -> &str {
        "test.corner-liar"
    }
    fn solve(&self, p: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
        if p.vars().len() < 2 || p.vars()[0] != p.vars()[1] {
            return MbaAnswer::Unsupported("two variables".into());
        }
        let expr = with(p, |m, root| {
            let (x, y) = (
                m.push(MOp::Var(0), &[]).unwrap(),
                m.push(MOp::Var(1), &[]).unwrap(),
            );
            let (nx, ny) = (
                m.push(MOp::Not, &[x]).unwrap(),
                m.push(MOp::Not, &[y]).unwrap(),
            );
            let a = m.push(MOp::And, &[x, ny]).unwrap();
            let b = m.push(MOp::And, &[nx, y]).unwrap();
            let t = m.push(MOp::Mul, &[a, b]).unwrap();
            m.push(MOp::Add, &[root, t]).unwrap()
        });
        MbaAnswer::Simplified {
            expr,
            claim: Claim::Certified,
        }
    }
}

/// Answers the input plus `2^(W−1)` when twelve particular bits of `x` are set and one is
/// clear: a polynomial MBA term almost no sampled point reaches, of a degree whose certificate
/// is far over any budget.
struct RareLiar;
impl MbaSolver for RareLiar {
    fn id(&self) -> &str {
        "test.rare-liar"
    }
    fn solve(&self, p: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
        let Some(w) = p.width() else {
            return MbaAnswer::Unsupported("empty".into());
        };
        if p.vars().is_empty() || p.vars()[0] != w || w.bits() < 64 {
            return MbaAnswer::Unsupported("64 bits".into());
        }
        let expr = with(p, |m, root| {
            let x = m.push(MOp::Var(0), &[]).unwrap();
            let nx = m.push(MOp::Not, &[x]).unwrap();
            // Π_j (x & 2^j) for j in 0..12, times (~x & 2^12): 2^(0+…+11+12) = 2^78 at 128
            // bits; scaled so the product is 2^(W−1) when every bit matches.
            let mut acc: Option<u32> = None;
            let mut shift = 0u32;
            for j in 0..13u32 {
                let src = if j == 12 { nx } else { x };
                let c = m
                    .push(MOp::Const(BitVec::wrapping_from_u64(w, 1 << j)), &[])
                    .unwrap();
                let t = m.push(MOp::And, &[src, c]).unwrap();
                shift += j;
                acc = Some(match acc {
                    None => t,
                    Some(a) => m.push(MOp::Mul, &[a, t]).unwrap(),
                });
            }
            let scale = u32::from(w.bits()) - 1 - shift.min(u32::from(w.bits()) - 1);
            let k = m
                .push(
                    MOp::Const(
                        BitVec::apply_bin(
                            bitwright::BinOp::Shl,
                            &BitVec::one(w),
                            &BitVec::wrapping_from_u64(w, u64::from(scale)),
                        )
                        .unwrap(),
                    ),
                    &[],
                )
                .unwrap();
            let t = m.push(MOp::Mul, &[acc.unwrap(), k]).unwrap();
            m.push(MOp::Add, &[root, t]).unwrap()
        });
        MbaAnswer::Simplified {
            expr,
            claim: Claim::Certified,
        }
    }
}

/// Answers `x` for anything over one variable.
struct PointLiar;
impl MbaSolver for PointLiar {
    fn id(&self) -> &str {
        "test.point-liar"
    }
    fn solve(&self, p: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
        if p.vars().len() != 1 {
            return MbaAnswer::Unsupported("one variable".into());
        }
        let mut m = MbaExpr::new(p.vars().to_vec());
        m.push(MOp::Var(0), &[]).unwrap();
        MbaAnswer::Simplified {
            expr: m,
            claim: Claim::Certified,
        }
    }
}

#[test]
fn liars_never_get_through_with_trust_off() {
    let mut rng = Rng(0x11a5);
    for (name, solver) in [
        ("corner", Arc::new(CornerLiar) as Arc<dyn MbaSolver>),
        ("rare", Arc::new(RareLiar)),
        ("point", Arc::new(PointLiar)),
    ] {
        let eng = engine(solver);
        for w in [64u16, 128] {
            let o = ParseOptions::width(Width::new(w).unwrap());
            let (point, _) = point_function(w, &mut rng);
            for src in [
                "(x ^ y) + 2*(x & y) + x*y - (x & y)*(x | y)",
                "(x & y)*(x | y) + (x & ~y)*(~x & y) + x",
                "x*y - (x & y)",
                &point,
            ] {
                let mut cx = Context::new();
                let e = cx.parse(src, &o).unwrap();
                let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
                assert_equivalent(&mut cx, e, out.roots[0].expr, &format!("[{name}] {src}"));
                assert_eq!(out.stats.mba.simplified, 0, "[{name}] {src}");
            }
        }
    }
}

// ----- the signature solver -----------------------------------------------------------------

/// Linear MBA over `x` and `y`: random combinations of Boolean functions and zero terms.
#[allow(dead_code)]
fn linear_corpus(seed: u64, n: usize) -> Vec<String> {
    const BASIS: [&str; 10] = [
        "(x & y)", "(x | y)", "(x ^ y)", "(x & ~y)", "(~x & y)", "~(x | y)", "~(x ^ y)", "x", "y",
        "~x",
    ];
    let mut rng = Rng(seed);
    (0..n)
        .map(|_| {
            let mut parts = Vec::new();
            for _ in 0..2 + rng.below(4) {
                let c = rng.below(9) as i64 - 4;
                if c != 0 {
                    parts.push(format!("{c} * {}", BASIS[rng.below(10) as usize]));
                }
            }
            let k = 1 + rng.below(5);
            parts.push(format!("{k} * ((x ^ y) - (x | y) + (x & y))"));
            parts.join(" + ").replace("+ -", "- ")
        })
        .collect()
}

/// The distinct nodes an expression's root uses, counting a shift's amount as the constant it
/// is in the arena (shared with an equal constant).
fn mba_cost(m: &MbaExpr) -> usize {
    let n = m.nodes();
    let mut live = vec![false; n.len()];
    if let Some(l) = live.last_mut() {
        *l = true;
    }
    for i in (0..n.len()).rev() {
        if live[i] {
            for &k in &n[i].args[..n[i].op.arity()] {
                live[k as usize] = true;
            }
        }
    }
    let mut seen: std::collections::HashMap<MNode, usize> = std::collections::HashMap::new();
    let mut canon: Vec<usize> = Vec::new();
    for (i, node) in n.iter().enumerate() {
        let mut key = *node;
        for k in 0..node.op.arity() {
            key.args[k] = canon[node.args[k] as usize] as u32;
        }
        if matches!(key.op, MOp::Add | MOp::Mul | MOp::And | MOp::Or | MOp::Xor)
            && key.args[0] > key.args[1]
        {
            key.args.swap(0, 1);
        }
        let c = *seen.entry(key).or_insert(i);
        canon.push(c);
    }
    let mut consts: Vec<BitVec> = (0..n.len())
        .filter(|&i| live[i])
        .filter_map(|i| match n[i].op {
            MOp::Const(v) => Some(v),
            _ => None,
        })
        .collect();
    let mut amounts = 0;
    for i in (0..n.len()).filter(|&i| live[i]) {
        if let MOp::Shl(k) | MOp::LShr(k) = n[i].op {
            let v = BitVec::wrapping_from_u64(n[i].width, u64::from(k));
            if !consts.contains(&v) {
                consts.push(v);
                amounts += 1;
            }
        }
    }
    (0..n.len()).filter(|&i| live[i] && canon[i] == i).count() + amounts
}

/// Asks the native and the signature solver every question and answers with the native one;
/// counts questions where the native answer (or the input, when it declines) is larger than
/// the signature solver's.
struct Paired {
    native: NormalFormSolver,
    asked: std::sync::atomic::AtomicUsize,
    worse: std::sync::Mutex<Vec<String>>,
}

impl MbaSolver for Paired {
    fn id(&self) -> &str {
        "test.paired"
    }
    fn polynomial_fragments(&self) -> bool {
        true
    }
    fn solve(&self, p: &MbaExpr, b: &MbaBudget) -> MbaAnswer {
        let ours = self.native.solve(p, b);
        let theirs = SignatureSolver.solve(p, b);
        let cost = |a: &MbaAnswer| match a {
            MbaAnswer::Simplified { expr, .. } => mba_cost(expr),
            _ => mba_cost(p),
        };
        self.asked
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if cost(&ours) > cost(&theirs)
            && let Ok(mut v) = self.worse.lock()
        {
            v.push(format!("{p:?}\n ours {ours:?}\n sig {theirs:?}"));
        }
        ours
    }
}

/// Linear MBA over `x` and `y` in the benchmark corpus's shape (`workload::mba_corpus`):
/// random coefficients on Boolean functions, plus a multiple of a zero.
fn bench_corpus(seed: u64, n: usize) -> Vec<String> {
    const BASIS: [&str; 8] = [
        "(x & y)", "(x | y)", "(x ^ y)", "(x & ~y)", "(~x & y)", "~(x | y)", "x", "y",
    ];
    let mut rng = Rng(seed);
    (0..n)
        .map(|_| {
            let mut parts = Vec::new();
            for _ in 0..3 + rng.below(4) {
                let c = rng.below(9) as i64 - 4;
                if c != 0 {
                    parts.push(format!("{c} * {}", BASIS[rng.below(8) as usize]));
                }
            }
            let k = 1 + rng.below(5);
            parts.push(format!("{k} * ((x ^ y) - (x | y) + (x & y))"));
            parts.join(" + ").replace("+ -", "- ")
        })
        .collect()
}

#[test]
fn never_costlier_than_the_signature_solver() {
    // Every question the engine asks on the corpora, answered by both.
    let paired = Arc::new(Paired {
        native: NormalFormSolver::default(),
        asked: Default::default(),
        worse: Default::default(),
    });
    let eng = engine(paired.clone());
    let sig = engine(Arc::new(SignatureSolver));
    let (mut total_ours, mut total_sig) = (0u64, 0u64);
    let (mut wins, mut losses) = (0, 0);
    for (i, w) in [8u16, 32, 64].into_iter().enumerate() {
        let o = ParseOptions::width(Width::new(w).unwrap());
        let corpus = linear_corpus(0x7a11 + i as u64, 200)
            .into_iter()
            .chain(bench_corpus(11 + i as u64, 200));
        for src in corpus {
            let mut cx = Context::new();
            let e = cx.parse(&src, &o).unwrap();
            let a = eng.run(&mut cx, &[e], Run::default()).unwrap().roots[0].expr;
            assert_equivalent(&mut cx, e, a, &src);
            let mut cx2 = Context::new();
            let e2 = cx2.parse(&src, &o).unwrap();
            let b = sig.run(&mut cx2, &[e2], Run::default()).unwrap().roots[0].expr;
            let (sa, sb) = (dag_size(&mut cx, a), dag_size(&mut cx2, b));
            wins += usize::from(sa < sb);
            losses += usize::from(sa > sb);
            total_ours += u64::from(sa);
            total_sig += u64::from(sb);
        }
    }
    let worse = paired.worse.lock().unwrap();
    assert!(
        worse.is_empty(),
        "{} costlier answers, e.g.\n{}",
        worse.len(),
        worse[0]
    );
    let asked = paired.asked.load(std::sync::atomic::Ordering::Relaxed);
    eprintln!(
        "{asked} questions, none answered more expensively; end to end: native {total_ours} \
         nodes, signature {total_sig}; smaller on {wins} inputs, larger on {losses}"
    );
    // End to end the passes after the MBA phase can still reach forms from either answer;
    // in aggregate the native solver leaves less.
    assert!(
        total_ours < total_sig && losses * 50 < wins,
        "{wins} {losses}"
    );
}

// ----- properties -----------------------------------------------------------------------------

#[test]
fn results_are_deterministic_and_independent_of_construction_order() {
    let eng = native();
    let o = ParseOptions::width(Width::W64);
    for (a, b) in [
        (
            "(x & y)*(x | y) + (x & ~y)*(~x & y) + 3*(x & 0x55)",
            "3*(0x55 & x) + (~x & y)*(x & ~y) + (y | x)*(y & x)",
        ),
        (
            "x*(x & y) + y*(x & y) - (x & y)*(x & y) + (z ^ 0x10) + 2*(z & 0x10)",
            "2*(0x10 & z) + (0x10 ^ z) - (y & x)*(x & y) + (y & x)*y + (x & y)*x",
        ),
    ] {
        let mut shown = Vec::new();
        for src in [a, b, a] {
            let mut cx = Context::new();
            let e = cx.parse(src, &o).unwrap();
            let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
            shown.push(cx.display(out.roots[0].expr).to_string());
        }
        assert!(shown.windows(2).all(|p| p[0] == p[1]), "{shown:?}");
    }
}

/// A solver that records every question and its answer.
struct Recording {
    inner: NormalFormSolver,
    asked: std::sync::Mutex<Vec<(MbaExpr, MbaBudget, MbaAnswer)>>,
}

impl MbaSolver for Recording {
    fn id(&self) -> &str {
        self.inner.id()
    }
    fn polynomial_fragments(&self) -> bool {
        true
    }
    fn solve(&self, p: &MbaExpr, b: &MbaBudget) -> MbaAnswer {
        let a = self.inner.solve(p, b);
        self.asked.lock().unwrap().push((p.clone(), *b, a.clone()));
        a
    }
}

#[test]
fn the_memo_changes_nothing() {
    // Memo off, the default one, and one so small it forgets all the time: the same results
    // through the engine, question by question, at any budget.
    let solvers = || {
        [0u32, 1024, 2].map(|memo| {
            Arc::new(Recording {
                inner: NormalFormSolver::new(NfOptions::default().with_memo(memo)),
                asked: Default::default(),
            })
        })
    };
    let recorders = solvers();
    let engines: Vec<Engine> = recorders
        .iter()
        .map(|r| engine(r.clone() as Arc<dyn MbaSolver>))
        .collect();
    let o = ParseOptions::width(Width::W64);
    let corpus = linear_corpus(0x3e30, 60).into_iter().chain([
        "(x & y)*(x | y) + (x & ~y)*(~x & y) + ((x + y) & z) + ((x + y) & ~z)".to_string(),
        "x*(x & y) + y*(x & y) - (x & y)*(x & y) + (x ^ 0x10) + 2*(x & 0x10)".to_string(),
        "((x ^ y) + 2*(x & y)) & z | ((x >>u 3) + (y >>u 3)) ^ (x * y + z)".to_string(),
    ]);
    for src in corpus {
        let outs: Vec<String> = engines
            .iter()
            .map(|eng| {
                let mut cx = Context::new();
                let e = cx.parse(&src, &o).unwrap();
                let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
                format!("{} {:?}", cx.display(out.roots[0].expr), out.stats.mba)
            })
            .collect();
        assert!(outs.windows(2).all(|p| p[0] == p[1]), "{src}: {outs:#?}");
    }
    let asked: Vec<_> = recorders
        .iter()
        .map(|r| r.asked.lock().unwrap().clone())
        .collect();
    assert!(asked.windows(2).all(|p| p[0] == p[1]));
    // Every question again, and at smaller budgets, against fresh solvers and the used ones.
    let fresh = solvers();
    let mut hits = 0;
    for (p, b, a) in &asked[0] {
        for steps in [b.steps, 1 << 12, 300] {
            let budget = MbaBudget::default().with_steps(steps);
            let want = if steps == b.steps {
                a.clone()
            } else {
                fresh[0].solve(p, &budget)
            };
            for s in fresh.iter().chain(&recorders) {
                assert_eq!(s.solve(p, &budget), want, "{p:?} at {steps}");
            }
        }
        hits += 1;
    }
    assert!(hits > 50, "{hits}");
    let used = recorders[1].inner.stats();
    assert!(used.memo_hits > 0, "{used:?}");
    assert_eq!(recorders[0].inner.stats().memo_hits, 0);
}

#[test]
fn every_budget_is_safe() {
    let o = ParseOptions::width(Width::W64);
    let src = "(x & y)*(x | y) + (x & ~y)*(~x & y) + ((x + y) & z) + ((x + y) & ~z)";
    for k in (0..40).chain([100, 1000, 10_000, 100_000, 1_000_000]) {
        for budget in [
            Budget::default().with_pass_work(k),
            Budget::default().with_mba_calls(k),
            Budget::default().with_node_visits(k),
            Budget::default().with_new_nodes(k),
        ] {
            let mut cx = Context::new();
            let e = cx.parse(src, &o).unwrap();
            let out = native()
                .run(&mut cx, &[e], Run::default().with_per_call(budget))
                .unwrap();
            assert_equivalent(&mut cx, e, out.roots[0].expr, &format!("{budget:?}"));
        }
    }
    // And the solver itself, at every step budget.
    let mut cx = Context::new();
    let e = cx.parse(src, &o).unwrap();
    let lim = bitwright::mba::MbaLimits::default().with_min_nodes(0);
    let (m, _) = bitwright::mba::lower(&cx, e, &lim).unwrap();
    let solver = NormalFormSolver::default();
    for steps in (0..200).chain((8..24).map(|k| 1u64 << k)) {
        match solver.solve(&m, &MbaBudget::default().with_steps(steps)) {
            MbaAnswer::Simplified { expr, .. } => assert!(expr.nodes().len() < m.nodes().len()),
            MbaAnswer::Exhausted | MbaAnswer::NoSimpler => {}
            other => panic!("{steps}: {other:?}"),
        }
    }
    let _ = MNode::clone;
}
