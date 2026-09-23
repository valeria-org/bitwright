//! Simplifier soundness: every engine configuration (standard, deobfuscate, and with features
//! `mba` and `cobra` the MBA service, with `eqsat` the saturation search) on random DAGs and on
//! adversarial MBA-shaped inputs gives a result equivalent to its input. Equivalence is decided
//! by the bit-serial reference over both canonical DAGs (never by the context's evaluator):
//! exhaustively at small widths, at boundary environments up to 512 bits.
//!
//! Also: re-simplifying a result in a fresh context never makes it larger, and budgets cut to a
//! handful of units (each alone, and all together, and a shared allowance) still give sound
//! results, never overspend, and report how they ended.
//!
//! The library's unit tests check the standard strategy at up to 6 bits with the context's
//! evaluator; the fuzz target checks both strategies at 16 points. This suite adds wide widths,
//! MBA-shaped inputs, the MBA and eqsat services, and budget edges.

mod common;

use bitwright::engine::{Allowance, Budget, End, Engine, Run, Strategy};
use bitwright::{
    BinOp, BitVec, Bounded, Context, ContextConfig, Expr, ParseOptions, PrintOptions, SymbolKey,
    UnOp, Width,
};
use common::{
    Canonical, Dag, GenConfig, Rng, SMOKE_WIDTHS, Size, WIDTHS, every_env, test_context, w,
};

// ----- engines ---------------------------------------------------------------------------------

fn engines() -> Vec<(&'static str, Engine)> {
    #[cfg_attr(not(feature = "mba"), allow(unused_mut))]
    let mut v = vec![
        ("standard", Engine::standard()),
        (
            "deobfuscate",
            Engine::builder()
                .builtin()
                .strategy(Strategy::deobfuscate())
                .build()
                .unwrap(),
        ),
    ];
    #[cfg(feature = "mba")]
    {
        use bitwright::mba::{MbaConfig, MbaTrust, MemoryCache, SignatureSolver};
        use std::sync::Arc;
        // Our own evidence only, and also the solver's certificates (the default).
        for (name, trust) in [
            (
                "mba-signature",
                MbaTrust::default().with_backend_certificates(false),
            ),
            ("mba-signature-certified", MbaTrust::default()),
        ] {
            v.push((
                name,
                Engine::builder()
                    .builtin()
                    .strategy(
                        Strategy::deobfuscate().with_mba(MbaConfig::default().with_trust(trust)),
                    )
                    .mba_solver(Arc::new(SignatureSolver))
                    .mba_cache(Arc::new(MemoryCache::new(1024)))
                    .build()
                    .unwrap(),
            ));
        }
    }
    v
}

#[cfg(feature = "cobra")]
fn cobra_engine() -> Engine {
    use bitwright::mba::{CobraSolver, MbaConfig};
    use std::sync::Arc;
    Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
        .mba_solver(Arc::new(CobraSolver::default()))
        .build()
        .unwrap()
}

// ----- equivalence by the reference -------------------------------------------------------------

/// Environments for the symbols under `roots`: every assignment when there are at most
/// `max_bits` of them, else boundary-biased samples.
fn envs(
    cx: &mut Context,
    roots: &[Expr],
    rng: &mut Rng,
    max_bits: u32,
    samples: usize,
) -> Vec<Vec<(SymbolKey, BitVec)>> {
    let syms: Vec<(SymbolKey, Width)> = cx
        .symbols_in(roots)
        .unwrap()
        .into_iter()
        .map(|id| {
            (
                cx.symbol_key(id).unwrap().clone(),
                cx.symbol_width(id).unwrap(),
            )
        })
        .collect();
    let bind = |vals: Vec<BitVec>| syms.iter().map(|s| s.0.clone()).zip(vals).collect();
    match every_env(&syms, max_bits) {
        Some(all) => all.into_iter().map(bind).collect(),
        None => (0..samples)
            .map(|_| bind(syms.iter().map(|(_, sw)| rng.biased(*sw)).collect()))
            .collect(),
    }
}

/// Panics unless `after` equals `before` at every environment, by the reference.
fn assert_equivalent(
    cx: &mut Context,
    before: Expr,
    after: Expr,
    envs: &[Vec<(SymbolKey, BitVec)>],
    what: &str,
) {
    assert_eq!(
        cx.width(before).unwrap(),
        cx.width(after).unwrap(),
        "{what}: width"
    );
    let dag = Canonical::new(cx, &[before, after]);
    for env in envs {
        let v = dag.eval(env, &[]);
        if v[0] != v[1] {
            panic!(
                "{what}: `{}`\n  simplified to `{}`\n  differs at {env:?}: {} vs {}",
                cx.display(before),
                cx.display(after),
                common::from_ref(&v[0]),
                common::from_ref(&v[1]),
            );
        }
    }
}

fn dag_size(cx: &mut Context, e: Expr) -> u32 {
    match cx.dag_size(&[e], u32::MAX).unwrap() {
        Bounded::Exact(n) => n,
        other => panic!("{other:?}"),
    }
}

// ----- MBA-shaped inputs --------------------------------------------------------------------------

/// Builds mixed Boolean-arithmetic expressions: a plain target (a sum, difference, product,
/// bitwise function or constant of the variables) with its operations replaced, recursively,
/// by MBA identities (`a + b = (a ^ b) + 2(a & b)`, `a * b = (a & b)(a | b) + (a & ~b)(~a & b)`,
/// …), zero terms added, and random linear combinations of bitwise functions mixed in.
struct Mba<'a> {
    cx: &'a mut Context,
    rng: &'a mut Rng,
    vars: Vec<Expr>,
    width: Width,
}

impl Mba<'_> {
    fn c(&mut self, v: i128) -> Expr {
        let b = BitVec::wrapping_from_i128(self.width, v);
        self.cx.constant(&b).unwrap()
    }
    fn bin(&mut self, op: BinOp, a: Expr, b: Expr) -> Expr {
        self.cx.bin(op, a, b).unwrap()
    }
    fn not(&mut self, a: Expr) -> Expr {
        self.cx.un(UnOp::Not, a).unwrap()
    }
    fn times(&mut self, k: i128, a: Expr) -> Expr {
        let c = self.c(k);
        self.bin(BinOp::Mul, c, a)
    }
    fn times_bv(&mut self, k: BitVec, a: Expr) -> Expr {
        let c = self.cx.constant(&k).unwrap();
        self.bin(BinOp::Mul, c, a)
    }
    fn var(&mut self) -> Expr {
        let v = self.vars.clone();
        self.rng.pick(&v)
    }

    /// A random Boolean function of the variables (depth ≤ 2).
    fn bitwise(&mut self, depth: u32) -> Expr {
        if depth == 0 || self.rng.chance(1, 4) {
            let v = self.var();
            return if self.rng.chance(1, 3) {
                self.not(v)
            } else {
                v
            };
        }
        let (a, b) = (self.bitwise(depth - 1), self.bitwise(depth - 1));
        let op = self.rng.pick(&[BinOp::And, BinOp::Or, BinOp::Xor]);
        let e = self.bin(op, a, b);
        if self.rng.chance(1, 4) {
            self.not(e)
        } else {
            e
        }
    }

    /// `a op b` spelled through an identity, with the operands obfuscated further.
    fn obfuscated(&mut self, op: BinOp, a: Expr, b: Expr, depth: u32) -> Expr {
        if depth == 0 || self.rng.chance(1, 5) {
            return self.bin(op, a, b);
        }
        let d = depth - 1;
        let ob = |s: &mut Self, op: BinOp, x: Expr, y: Expr| s.obfuscated(op, x, y, d);
        match (op, self.rng.below(3)) {
            (BinOp::Add, 0) => {
                let x = ob(self, BinOp::Xor, a, b);
                let n = ob(self, BinOp::And, a, b);
                let t = self.times(2, n);
                ob(self, BinOp::Add, x, t)
            }
            (BinOp::Add, 1) => {
                let o = ob(self, BinOp::Or, a, b);
                let n = ob(self, BinOp::And, a, b);
                ob(self, BinOp::Add, o, n)
            }
            (BinOp::Add, _) => {
                let o = ob(self, BinOp::Or, a, b);
                let t = self.times(2, o);
                let x = ob(self, BinOp::Xor, a, b);
                ob(self, BinOp::Sub, t, x)
            }
            (BinOp::Sub, 0) => {
                let x = ob(self, BinOp::Xor, a, b);
                let na = self.not(a);
                let n = ob(self, BinOp::And, na, b);
                let t = self.times(2, n);
                ob(self, BinOp::Sub, x, t)
            }
            (BinOp::Sub, _) => {
                // a - b = a + ~b + 1
                let nb = self.not(b);
                let s = ob(self, BinOp::Add, a, nb);
                let one = self.c(1);
                ob(self, BinOp::Add, s, one)
            }
            (BinOp::Xor, 0) => {
                let o = ob(self, BinOp::Or, a, b);
                let n = ob(self, BinOp::And, a, b);
                ob(self, BinOp::Sub, o, n)
            }
            (BinOp::Xor, _) => {
                let s = ob(self, BinOp::Add, a, b);
                let n = ob(self, BinOp::And, a, b);
                let t = self.times(2, n);
                ob(self, BinOp::Sub, s, t)
            }
            (BinOp::Or, 0) => {
                let x = ob(self, BinOp::Xor, a, b);
                let n = ob(self, BinOp::And, a, b);
                ob(self, BinOp::Add, x, n)
            }
            (BinOp::Or, _) => {
                let s = ob(self, BinOp::Add, a, b);
                let n = ob(self, BinOp::And, a, b);
                ob(self, BinOp::Sub, s, n)
            }
            (BinOp::And, 0) => {
                let o = ob(self, BinOp::Or, a, b);
                let x = ob(self, BinOp::Xor, a, b);
                ob(self, BinOp::Sub, o, x)
            }
            (BinOp::And, _) => {
                let s = ob(self, BinOp::Add, a, b);
                let o = ob(self, BinOp::Or, a, b);
                ob(self, BinOp::Sub, s, o)
            }
            (BinOp::Mul, _) => {
                let p = ob(self, BinOp::And, a, b);
                let q = ob(self, BinOp::Or, a, b);
                let nb = self.not(b);
                let na = self.not(a);
                let r = ob(self, BinOp::And, a, nb);
                let s = ob(self, BinOp::And, na, b);
                let pq = self.bin(BinOp::Mul, p, q);
                let rs = self.bin(BinOp::Mul, r, s);
                ob(self, BinOp::Add, pq, rs)
            }
            _ => self.bin(op, a, b),
        }
    }

    /// A zero spelled as `(a | b) - (a & b) - (a ^ b)`, times a random coefficient.
    fn zero_term(&mut self) -> Expr {
        let (a, b) = (self.bitwise(1), self.bitwise(1));
        let o = self.bin(BinOp::Or, a, b);
        let n = self.bin(BinOp::And, a, b);
        let x = self.bin(BinOp::Xor, a, b);
        let d = self.bin(BinOp::Sub, o, n);
        let z = self.bin(BinOp::Sub, d, x);
        let k = self.coefficient();
        self.times_bv(k, z)
    }

    /// 1, −1, 2, the signed minimum, or a small signed value.
    fn coefficient(&mut self) -> BitVec {
        let w = self.width;
        match self.rng.below(6) {
            0 => BitVec::one(w),
            1 => BitVec::ones(w),
            2 => BitVec::wrapping_from_u64(w, 2),
            3 => BitVec::smin(w),
            _ => BitVec::wrapping_from_i128(w, (self.rng.next() % 1000) as i128 - 500),
        }
    }

    /// A small random term over `+ - * & | ^ ~` and negation (the saturation fragment).
    #[cfg_attr(not(feature = "eqsat"), allow(dead_code))]
    fn plain(&mut self, depth: u32) -> Expr {
        if depth == 0 || self.rng.chance(1, 4) {
            return if self.rng.chance(1, 5) {
                let k = self.coefficient();
                self.cx.constant(&k).unwrap()
            } else {
                self.var()
            };
        }
        match self.rng.below(8) {
            0 => {
                let a = self.plain(depth - 1);
                self.not(a)
            }
            1 => {
                let a = self.plain(depth - 1);
                self.cx.un(UnOp::Neg, a).unwrap()
            }
            _ => {
                let op = self.rng.pick(&[
                    BinOp::Add,
                    BinOp::Sub,
                    BinOp::Mul,
                    BinOp::And,
                    BinOp::Or,
                    BinOp::Xor,
                ]);
                let (a, b) = (self.plain(depth - 1), self.plain(depth - 1));
                self.bin(op, a, b)
            }
        }
    }

    /// An obfuscated input: a plain target, rewritten, plus zero terms and a random linear
    /// combination of Boolean functions.
    fn input(&mut self, depth: u32) -> Expr {
        let (a, b) = (self.var(), self.var());
        let op = self.rng.pick(&[
            BinOp::Add,
            BinOp::Sub,
            BinOp::Xor,
            BinOp::Or,
            BinOp::And,
            BinOp::Mul,
        ]);
        let mut e = self.obfuscated(op, a, b, depth);
        for _ in 0..self.rng.below(3) {
            let z = self.zero_term();
            e = self.bin(BinOp::Add, e, z);
        }
        if self.rng.chance(1, 2) {
            for _ in 0..1 + self.rng.below(3) {
                let f = self.bitwise(2);
                let k = self.coefficient();
                let t = self.times_bv(k, f);
                e = self.bin(BinOp::Add, e, t);
            }
        }
        e
    }
}

/// An MBA-shaped input over 2 or 3 fresh variables of `width` in `cx`.
fn mba_input(cx: &mut Context, rng: &mut Rng, width: Width, depth: u32) -> Expr {
    mba(cx, rng, width).input(depth)
}

/// An MBA builder over 2 or 3 fresh variables of `width` in `cx`.
fn mba<'a>(cx: &'a mut Context, rng: &'a mut Rng, width: Width) -> Mba<'a> {
    let n = 2 + rng.below(2) as usize;
    let vars: Vec<Expr> = (0..n)
        .map(|k| {
            cx.symbol(format!("m{k}_{}", width.bits()).as_str(), width)
                .unwrap()
        })
        .collect();
    Mba {
        cx,
        rng,
        vars,
        width,
    }
}

// ----- the properties -------------------------------------------------------------------------

/// Simplifies `e` with every engine and checks each result. Also checks that re-simplifying a
/// result in a fresh context (no memo) gives a result that is no larger. Returns how many
/// results changed.
fn check_engines(
    cx: &mut Context,
    engines: &[(&str, Engine)],
    e: Expr,
    envs: &[Vec<(SymbolKey, BitVec)>],
    what: &str,
) -> usize {
    let mut changed = 0;
    for (name, engine) in engines {
        let out = engine.run(cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert!(
            matches!(r.end, End::Completed),
            "{what} [{name}]: ended {:?}",
            r.end
        );
        assert!(
            r.relies_on.is_none(),
            "{what} [{name}]: relies on constraints"
        );
        assert_equivalent(cx, e, r.expr, envs, &format!("{what} [{name}]"));
        changed += usize::from(r.changed);
        // Again in a fresh context, from the printed result: never larger.
        let text = cx
            .display_with(r.expr, PrintOptions::default().with_symbol_widths(true))
            .to_string();
        let mut fresh = test_context(ContextConfig::default());
        let back = fresh.parse(&text, &ParseOptions::default()).unwrap();
        let again = engine
            .run(&mut fresh, &[back], Run::default())
            .unwrap()
            .roots[0];
        let (s1, s2) = (dag_size(&mut fresh, back), dag_size(&mut fresh, again.expr));
        assert!(
            s2 <= s1,
            "{what} [{name}]: re-simplifying `{text}` grew it to `{}`",
            fresh.display(again.expr)
        );
    }
    changed
}

fn random_dags(size: Size, wide: bool) -> usize {
    let engines = engines();
    let rounds = size.pick(if wide { 6 } else { 15 }, if wide { 1500 } else { 3000 });
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    let mut changed = 0;
    for seed in 0..rounds {
        let seed = seed + if wide { 0x51_8000 } else { 0x51_0000 };
        let mut rng = Rng(seed);
        let mut cx = test_context(ContextConfig::default());
        let cfg = if wide {
            GenConfig::wide(&mut rng, &widths, 2 + (seed % 3) as u32)
        } else {
            GenConfig::small(&mut rng, 4, 2 + (seed % 4) as u32)
        }
        .with_ext(seed % 3 == 2);
        let rw = rng.pick(&cfg.widths.clone());
        let mut dag = Dag::new(&mut cx, cfg);
        let i = dag.random(&mut cx, &mut rng, rw);
        let e = dag.expr(i);
        let envs = envs(&mut cx, &[e], &mut rng, 12, size.pick(8, 24));
        changed += check_engines(&mut cx, &engines, e, &envs, &format!("seed {seed:#x}"));
    }
    changed
}

#[test]
fn random_dags_simplify_soundly_smoke() {
    let changed = random_dags(Size::Smoke, false) + random_dags(Size::Smoke, true);
    assert!(changed > 0, "nothing simplified");
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn random_dags_simplify_soundly_heavy() {
    assert!(random_dags(Size::Heavy, false) > 0, "nothing simplified");
    assert!(random_dags(Size::Heavy, true) > 0, "nothing simplified");
}

fn mba_inputs(size: Size) {
    let engines = engines();
    let rounds = size.pick(16, 2500);
    let widths: Vec<u16> = size.pick(
        vec![1, 3, 4, 8, 64, 512],
        vec![
            1, 2, 3, 4, 5, 6, 8, 16, 31, 32, 33, 64, 65, 128, 129, 256, 512,
        ],
    );
    let (mut changed, mut shrunk) = (0, 0);
    for seed in 0..rounds {
        let seed = 0x3ba_0000 + seed;
        let mut rng = Rng(seed);
        let mut cx = Context::new();
        let width = w(rng.pick(&widths));
        let e = mba_input(&mut cx, &mut rng, width, 1 + (seed % 3) as u32);
        let before = dag_size(&mut cx, e);
        let envs = envs(&mut cx, &[e], &mut rng, 12, size.pick(8, 32));
        changed += check_engines(&mut cx, &engines, e, &envs, &format!("seed {seed:#x}"));
        let out = engines[1].1.simplify(&mut cx, e).unwrap();
        if dag_size(&mut cx, out.expr) < before {
            shrunk += 1;
        }
    }
    eprintln!("{changed} results changed; deobfuscate shrank {shrunk} of {rounds}");
    assert!(
        shrunk * 2 > rounds as usize,
        "the passes should undo most MBA ({shrunk})"
    );
}

#[test]
fn mba_inputs_simplify_soundly_smoke() {
    mba_inputs(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn mba_inputs_simplify_soundly_heavy() {
    mba_inputs(Size::Heavy);
}

/// The cobra backend (feature `cobra`) on MBA-shaped inputs.
#[cfg(feature = "cobra")]
fn cobra(size: Size) {
    let engines = vec![("cobra", cobra_engine())];
    for seed in 0..size.pick(4, 300) {
        let seed = 0xc0b_0000 + seed;
        let mut rng = Rng(seed);
        let mut cx = Context::new();
        let width = w(rng.pick(&[4, 8, 32, 64]));
        let e = mba_input(&mut cx, &mut rng, width, 2);
        let envs = envs(&mut cx, &[e], &mut rng, 12, 32);
        check_engines(&mut cx, &engines, e, &envs, &format!("seed {seed:#x}"));
    }
}

#[cfg(feature = "cobra")]
#[test]
fn cobra_results_are_sound_smoke() {
    cobra(Size::Smoke);
}

#[cfg(feature = "cobra")]
#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn cobra_results_are_sound_heavy() {
    cobra(Size::Heavy);
}

// ----- tiny budgets ------------------------------------------------------------------------------

/// Budgets with one field cut to `k` units (the rest default), and all fields at `k`.
fn tiny_budgets(k: u64) -> Vec<(String, Budget)> {
    let d = Budget::default();
    let mut v = vec![
        ("node_visits".into(), d.with_node_visits(k)),
        ("candidates".into(), d.with_candidates(k)),
        ("match_steps".into(), d.with_match_steps(k)),
        ("rewrites".into(), d.with_rewrites(k)),
        ("new_nodes".into(), d.with_new_nodes(k)),
        ("fact_work".into(), d.with_fact_work(k)),
        ("pass_work".into(), d.with_pass_work(k)),
        ("mba_calls".into(), d.with_mba_calls(k)),
    ];
    v.push((
        "everything".into(),
        Budget::ZERO
            .with_node_visits(k)
            .with_candidates(k)
            .with_match_steps(k)
            .with_rewrites(k)
            .with_new_nodes(k)
            .with_fact_work(k)
            .with_pass_work(k)
            .with_mba_calls(k),
    ));
    v
}

/// Every field of `spent` is at most the matching field of `cap`, except the fields with a known
/// overspend (pinned by `new_nodes_budget_is_never_overspent`,
/// `fact_work_budget_is_never_overspent` and `pass_work_budget_is_never_overspent`; drop them
/// from this list once fixed).
fn within(spent: &Budget, cap: &Budget) -> bool {
    const KNOWN_OVERSPENT: [usize; 3] = [4, 5, 6]; // new_nodes, fact_work, pass_work
    let f = |b: &Budget| {
        [
            b.node_visits,
            b.candidates,
            b.match_steps,
            b.rewrites,
            b.new_nodes,
            b.fact_work,
            b.pass_work,
            b.mba_calls,
            b.eqsat_nodes,
            b.eqsat_work,
        ]
    };
    f(spent)
        .iter()
        .zip(f(cap))
        .enumerate()
        .all(|(i, (s, c))| *s <= c || KNOWN_OVERSPENT.contains(&i))
}

fn budgets(size: Size) {
    let engines = engines();
    let ks: Vec<u64> = size.pick(vec![0, 1, 7], vec![0, 1, 2, 3, 7, 33, 200]);
    for seed in 0..size.pick(4, 250) {
        let seed = 0xb0d_0000 + seed;
        let mut rng = Rng(seed);
        let mut cx = Context::new();
        let e = if seed.is_multiple_of(2) {
            let width = w(rng.pick(&[3, 4, 8, 64, 256]));
            mba_input(&mut cx, &mut rng, width, 2)
        } else {
            let cfg = GenConfig::small(&mut rng, 4, 4);
            let mut dag = Dag::new(&mut cx, cfg);
            let i = dag.random(&mut cx, &mut rng, 4);
            dag.expr(i)
        };
        let envs = envs(&mut cx, &[e], &mut rng, 12, 16);
        for (name, engine) in &engines {
            for &k in &ks {
                for (field, budget) in tiny_budgets(k) {
                    // A fresh context per run, so the memo of an earlier run cannot answer.
                    let text = cx
                        .display_with(e, PrintOptions::default().with_symbol_widths(true))
                        .to_string();
                    let mut fresh = Context::new();
                    let x = fresh.parse(&text, &ParseOptions::default()).unwrap();
                    let mut account = Allowance::new(budget);
                    let out = engine
                        .run(
                            &mut fresh,
                            &[x],
                            Run::default().with_allowance(&mut account),
                        )
                        .unwrap();
                    let r = out.roots[0];
                    let what = format!("seed {seed:#x} [{name}] {field} = {k} on `{text}`");
                    assert!(
                        within(&account.spent(), &budget),
                        "{what}: spent {:?} of {budget:?}",
                        account.spent()
                    );
                    assert!(
                        matches!(r.end, End::Completed | End::BudgetTerminated(_)),
                        "{what}: ended {:?}",
                        r.end
                    );
                    if k == 0 && field == "everything" && !fresh.is_leaf(x).unwrap() {
                        assert_ne!(r.end, End::Completed, "{what}: completed with no budget");
                    }
                    let fresh_envs: Vec<Vec<(SymbolKey, BitVec)>> = envs.clone();
                    assert_equivalent(&mut fresh, x, r.expr, &fresh_envs, &what);
                }
            }
        }
    }
}

#[test]
fn tiny_budgets_stay_sound_smoke() {
    budgets(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn tiny_budgets_stay_sound_heavy() {
    budgets(Size::Heavy);
}

/// One allowance shared by many runs is never overspent, and every result stays sound.
fn shared_allowance(size: Size) {
    let engine = &engines()[1].1;
    for seed in 0..size.pick(3, 1000) {
        let seed = 0xa11_0000 + seed;
        let mut rng = Rng(seed);
        let cap = Budget::ZERO
            .with_node_visits(rng.below(400))
            .with_candidates(rng.below(400))
            .with_match_steps(rng.below(4000))
            .with_rewrites(rng.below(40))
            .with_new_nodes(rng.below(400))
            .with_fact_work(rng.below(4000))
            .with_pass_work(rng.below(4000));
        let mut account = Allowance::new(cap);
        let mut cx = Context::new();
        for k in 0..size.pick(4, 12) {
            let width = w(rng.pick(&[4, 8, 32]));
            let e = mba_input(&mut cx, &mut rng, width, 2);
            let out = engine
                .run(&mut cx, &[e], Run::default().with_allowance(&mut account))
                .unwrap();
            let what = format!("seed {seed:#x} run {k}");
            assert!(within(&account.spent(), &cap), "{what}: overspent");
            let envs = envs(&mut cx, &[e], &mut rng, 12, 16);
            assert_equivalent(&mut cx, e, out.roots[0].expr, &envs, &what);
        }
    }
}

#[test]
fn a_shared_allowance_is_never_overspent_smoke() {
    shared_allowance(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn a_shared_allowance_is_never_overspent_heavy() {
    shared_allowance(Size::Heavy);
}

/// The book: "Work is charged before it is done, so a call never spends past its limit." A zero
/// `new_nodes` budget creates no node (they used to be recorded after they were built).
#[test]
fn new_nodes_budget_is_never_overspent() {
    let deobfuscate = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    for (src, engine) in [
        ("sext<8>(x:6)", &deobfuscate),
        ("sext<8>(trunc<6>(zext<7>(x:4)))", &Engine::standard()),
    ] {
        let mut cx = Context::new();
        let e = cx.parse(src, &ParseOptions::default()).unwrap();
        let budget = Budget::default().with_new_nodes(0);
        let mut account = Allowance::new(budget);
        let out = engine
            .run(&mut cx, &[e], Run::default().with_allowance(&mut account))
            .unwrap();
        assert_eq!(out.stats.new_nodes, 0, "`{src}`: new nodes counted");
        assert_eq!(account.spent().new_nodes, 0, "`{src}`: new nodes spent");
    }
}

/// The design: fact work is charged per transfer and "each fact query is capped by what
/// remains, so the budget is never overrun". A guard's queries used to be capped one by one,
/// so together they ran past the limit (11 of 10).
#[test]
fn fact_work_budget_is_never_overspent() {
    let mut cx = Context::new();
    let src = "(y & 1) + (y | 1) + z * 128";
    let e = cx.parse(src, &ParseOptions::width(Width::W8)).unwrap();
    let mut account = Allowance::new(Budget::default().with_fact_work(10));
    let out = Engine::standard()
        .run(&mut cx, &[e], Run::default().with_allowance(&mut account))
        .unwrap();
    assert!(
        out.stats.fact_work <= 10,
        "`{src}`: counted {}",
        out.stats.fact_work
    );
    assert!(
        account.spent().fact_work <= 10,
        "`{src}`: spent {} of 10",
        account.spent().fact_work
    );
}

/// The same promise for `pass_work` (work used to be recorded after it ran: 6 of 5 on `~x`, 43
/// of 30 on a small MBA input).
#[test]
fn pass_work_budget_is_never_overspent() {
    let deobfuscate = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    for (src, engine, limit) in [
        ("~x:8", &Engine::standard(), 5),
        (
            "(x:32 & 0xff) + (x & 0xff00) - 2 * (x ^ y) + (x | y) * 2 - 2 * (x & y)",
            &deobfuscate,
            30,
        ),
    ] {
        let mut cx = Context::new();
        let e = cx.parse(src, &ParseOptions::default()).unwrap();
        let mut account = Allowance::new(Budget::default().with_pass_work(limit));
        engine
            .run(&mut cx, &[e], Run::default().with_allowance(&mut account))
            .unwrap();
        assert!(
            account.spent().pass_work <= limit,
            "`{src}`: spent {} of {limit}",
            account.spent().pass_work
        );
    }
}

// ----- equality saturation --------------------------------------------------------------------

/// Candidates of the saturation search (feature `eqsat`) are equivalent to their inputs, with
/// every built-in equation group and with tiny budgets.
#[cfg(feature = "eqsat")]
fn eqsat(size: Size) {
    use bitwright::eqsat::{Publication, SaturateConfig, Saturator, SearchRun};
    let groups: [&[&str]; 4] = [
        &["eqsat.distrib", "eqsat.cancel"],
        &["eqsat.assoc", "eqsat.negation", "eqsat.cancel"],
        &["eqsat.distrib_and"],
        &["eqsat.distrib_or", "eqsat.negation"],
    ];
    let mut published = 0;
    for seed in 0..size.pick(24, 30_000) {
        let seed = 0xe5a_0000 + seed;
        let mut rng = Rng(seed);
        let mut cx = Context::new();
        let width = w(rng.pick(&[1, 2, 3, 4, 8, 32, 64, 128]));
        let e = match seed % 3 {
            0 => mba(&mut cx, &mut rng, width).plain(3),
            1 => mba_input(&mut cx, &mut rng, width, 1),
            _ => {
                // Detours the directed simplifier cannot take: `p·(q + 1) − p·q`, `p·q + p·r`,
                // `(p + q) − q`, over small random terms.
                let mut m = mba(&mut cx, &mut rng, width);
                let (p, q, r) = (m.plain(1), m.plain(1), m.plain(1));
                match m.rng.below(3) {
                    0 => {
                        let one = m.c(1);
                        let q1 = m.bin(BinOp::Add, q, one);
                        let a = m.bin(BinOp::Mul, p, q1);
                        let b = m.bin(BinOp::Mul, p, q);
                        m.bin(BinOp::Sub, a, b)
                    }
                    1 => {
                        let a = m.bin(BinOp::Mul, p, q);
                        let b = m.bin(BinOp::Mul, p, r);
                        m.bin(BinOp::Add, a, b)
                    }
                    _ => {
                        let a = m.bin(BinOp::Add, p, q);
                        m.bin(BinOp::Sub, a, q)
                    }
                }
            }
        };
        let envs = envs(&mut cx, &[e], &mut rng, 12, 24);
        let g = groups[(seed % 4) as usize];
        let config = if seed.is_multiple_of(3) {
            SaturateConfig::exploratory()
        } else {
            SaturateConfig::default()
        };
        let (sat, _) = Saturator::builtin_groups(g, config);
        // The default budget half the time, a tiny one otherwise (which must withhold, not lie).
        let budget = if rng.chance(1, 2) {
            SearchRun::DEFAULT_BUDGET
        } else {
            SearchRun::DEFAULT_BUDGET
                .with_eqsat_nodes(rng.pick(&[0, 1, 8, 64]))
                .with_eqsat_work(rng.pick(&[0, 1, 16, 1000]))
        };
        let out = sat
            .search(&mut cx, &[e], SearchRun::default().with_per_call(budget))
            .unwrap();
        let what = format!("seed {seed:#x} {g:?}");
        if let Some(c) = out.roots[0].candidate {
            assert_eq!(out.publication, Publication::Published, "{what}");
            assert_equivalent(&mut cx, e, c, &envs, &what);
            published += 1;
        }
    }
    eprintln!("{published} candidates published");
    assert!(published > 0, "no search published a candidate");
}

#[cfg(feature = "eqsat")]
#[test]
fn eqsat_candidates_are_equivalent_smoke() {
    eqsat(Size::Smoke);
}

#[cfg(feature = "eqsat")]
#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn eqsat_candidates_are_equivalent_heavy() {
    eqsat(Size::Heavy);
}
