//! Engine properties: results are value-equivalent and normal, the dispatch net is a pure
//! prefilter, runs are idempotent, deterministic and order-independent, the memo is reused and
//! invalidated correctly, and budgets, admission, deadlines, hooks, observers, linking and
//! assumptions behave as documented.

use super::*;
use crate::facts::{Facts, KnownBits, Query, SRange, Truth, URange};
use crate::testutil::{Gen, Rng};
use crate::{BinOp, FnEnv, ParseOptions, SymbolKey};

/// The dispatch net of the engine's first `Local` phase.
fn net(engine: &Engine) -> &DispatchNet {
    engine
        .inner
        .phases
        .iter()
        .find_map(|p| match p {
            PhaseImpl::Local(n) => Some(n),
            _ => None,
        })
        .unwrap()
}

/// The built-in rules alone (no passes), for tests of the rule machinery.
fn rules_only() -> Strategy {
    Strategy::new(
        "rules",
        vec![Phase::Local {
            groups: builtin()
                .0
                .groups()
                .iter()
                .map(|g| g.name.clone())
                .collect(),
        }],
    )
}

fn strict_rules() -> Engine {
    Engine::builder()
        .builtin()
        .strategy(rules_only())
        .verify(Verify::strict())
        .build()
        .unwrap()
}

fn strict() -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::standard())
        .verify(Verify::strict())
        .build()
        .unwrap()
}

pub(crate) fn generator(seed: u64) -> Gen {
    Gen {
        rng: Rng(seed),
        max_w: 6,
        vars: Vec::new(),
    }
}

/// Whether `a` and `b` agree on every assignment of their symbols (sampled above 14 bits).
pub(crate) fn equivalent(cx: &mut Context, a: Expr, b: Expr, rng: &mut Rng) -> bool {
    let syms = cx.symbols_in(&[a, b]).unwrap();
    let keys: Vec<(SymbolKey, Width)> = syms
        .iter()
        .map(|&s| {
            (
                cx.symbol_key(s).unwrap().clone(),
                cx.symbol_width(s).unwrap(),
            )
        })
        .collect();
    let bits: u32 = keys.iter().map(|(_, w)| u32::from(w.bits())).sum();
    let exhaustive = bits <= 14;
    let cases: u64 = if exhaustive { 1 << bits } else { 2048 };
    for case in 0..cases {
        let mut rest = case;
        let vals: Vec<(SymbolKey, BitVec)> = keys
            .iter()
            .map(|(k, w)| {
                let v = if exhaustive {
                    let v = rest & ((1u64 << w.bits()) - 1);
                    rest >>= w.bits();
                    v
                } else {
                    // Random in every limb (wide widths included).
                    let limbs: Vec<u64> = (0..8).map(|_| rng.next()).collect();
                    return (k.clone(), BitVec::wrapping_from_limbs(*w, &limbs));
                };
                (k.clone(), BitVec::wrapping_from_u64(*w, v))
            })
            .collect();
        let env = FnEnv(|k: &SymbolKey, _| vals.iter().find(|(kk, _)| kk == k).map(|(_, v)| *v));
        let r = cx.eval(&[a, b], &env).unwrap();
        if r[0] != r[1] {
            return false;
        }
    }
    true
}

/// Every node of `e`'s DAG is normal: no directed rule of `engine` applies (reference path).
fn assert_normal(engine: &Engine, cx: &mut Context, e: Expr) {
    let order = cx.post_order(&[e]).unwrap();
    for n in order {
        let id = cx.id(n).unwrap();
        for l in &engine.inner.rules {
            if !l.rule.decreasing {
                continue;
            }
            if let Some(r) = crate::rules::apply::try_apply(cx, &l.rule, id)
                && r != id
            {
                panic!(
                    "{}: `{}` is not normal (rewrites to `{}`)",
                    l.rule.name,
                    cx.display(n),
                    cx.display(cx.handle(r))
                );
            }
        }
    }
}

/// A random instance of a random directed rule's pattern at a small admitted width, its
/// parameters replaced by random subexpressions, combined with a random expression.
fn redex_rich(engine: &Engine, g: &mut Gen, cx: &mut Context) -> Expr {
    let rules: Vec<&Rule> = engine
        .inner
        .rules
        .iter()
        .map(|l| &l.rule)
        .filter(|r| r.decreasing)
        .collect();
    loop {
        let rule = rules[g.rng.below(rules.len() as u64) as usize];
        let widths: Vec<Vec<u16>> = crate::rules::width_assignments(rule)
            .into_iter()
            .filter(|ws| ws.iter().all(|&w| w <= 6))
            .filter(|ws| crate::rules::eval::admitted(rule, ws))
            .collect();
        if widths.is_empty() {
            continue;
        }
        let ws = &widths[g.rng.below(widths.len() as u64) as usize];
        let pw: Vec<Width> = rule
            .params
            .iter()
            .map(|p| Width::new(p.width.eval(ws) as u16).unwrap())
            .collect();
        let consts: Vec<BitVec> = pw.iter().map(|w| g.constant(w.bits())).collect();
        let Some(root) = crate::rules::matcher::build_pattern(cx, rule, ws, &consts) else {
            continue;
        };
        let mut map = Vec::new();
        for (p, w) in rule.params.iter().zip(&pw) {
            use crate::rules::ParamKind;
            let depth = match p.kind {
                ParamKind::Any => g.rng.below(3) as u32,
                ParamKind::NonConst => 1 + g.rng.below(2) as u32,
                _ => continue,
            };
            let from = cx.symbol(format!("${}", p.name).as_str(), *w).unwrap();
            let mut to = g.expr(cx, w.bits(), depth).0;
            // A `nonconst` parameter must stay non-constant (and is sometimes compound).
            while p.kind == ParamKind::NonConst && cx.as_const(to).unwrap().is_some() {
                to = g.expr(cx, w.bits(), depth).0;
            }
            map.push((from, to));
        }
        let e = cx.handle(root);
        let e = cx.substitute(&[e], &map).unwrap()[0];
        let w = cx.width(e).unwrap();
        let (other, _) = g.expr(cx, w.bits(), 2);
        let op = [BinOp::Add, BinOp::Xor, BinOp::And, BinOp::Or][g.rng.below(4) as usize];
        return cx.bin(op, e, other).unwrap();
    }
}

#[test]
fn results_are_equivalent_normal_and_idempotent() {
    let engine = strict();
    let mut g = generator(0xe161_0001);
    let mut rng = Rng(7);
    let mut rewrites = 0;
    for i in 0..600 {
        let mut cx = Context::new();
        let e = if i % 2 == 0 {
            let w = 1 + g.rng.below(6) as u16;
            g.expr(&mut cx, w, 4).0
        } else {
            redex_rich(&engine, &mut g, &mut cx)
        };
        let out = engine.run(&mut cx, &[e], Run::default()).unwrap();
        let r = out.roots[0];
        assert_eq!(r.end, End::Completed);
        assert_eq!(
            out.stats.rejected, 0,
            "a postcondition rejected an application"
        );
        assert!(
            equivalent(&mut cx, e, r.expr, &mut rng),
            "{} vs {}",
            cx.display(e),
            cx.display(r.expr)
        );
        assert_normal(&engine, &mut cx, r.expr);
        // Idempotent, and answered from the memo.
        let again = engine.run(&mut cx, &[r.expr], Run::default()).unwrap();
        assert_eq!(again.roots[0].expr, r.expr);
        assert!(!again.roots[0].changed);
        rewrites += out.stats.rewrites;
    }
    assert!(
        rewrites > 100,
        "the random inputs exercise few rules ({rewrites})"
    );
}

/// Instances built to contain redexes of every corpus rule, simplified inside larger
/// expressions: the result is equivalent, normal, and every rule fires somewhere.
#[test]
fn every_rule_fires_inside_larger_expressions() {
    let engine = strict_rules();
    let mut census = RuleCensus::default();
    let mut rng = Rng(11);
    for rule in engine.inner.rules.iter().map(|l| &l.rule) {
        for (input, _) in &rule.examples {
            let mut cx = Context::new();
            let o = ParseOptions::width(Width::W8);
            let e = cx.parse(input, &o).unwrap();
            // Embed it: (e ^ z) + e, so the redex is below the root and shared.
            let z = cx.symbol("z", cx.width(e).unwrap()).unwrap();
            let x = cx.bin(BinOp::Xor, e, z).unwrap();
            let root = cx.bin(BinOp::Add, x, e).unwrap();
            let out = engine
                .run(
                    &mut cx,
                    &[root],
                    Run {
                        observer: Some(&mut census),
                        ..Run::default()
                    },
                )
                .unwrap();
            let r = out.roots[0].expr;
            assert!(equivalent(&mut cx, root, r, &mut rng));
            assert_normal(&engine, &mut cx, r);
        }
    }
    for rule in engine.inner.rules.iter().map(|l| &l.rule) {
        let c = census.rules.get(&rule.name).copied().unwrap_or_default();
        assert!(
            c.applied > 0,
            "{} never applied inside a larger expression",
            rule.name
        );
    }
}

#[test]
fn dispatch_is_a_pure_prefilter() {
    let engine = strict();
    let mut g = generator(0xd15_7a7c);
    let mut matched = 0;
    for _ in 0..300 {
        let mut cx = Context::new();
        let w = 1 + g.rng.below(6) as u16;
        let (e, _) = g.expr(&mut cx, w, 4);
        for n in cx.post_order(&[e]).unwrap() {
            let id = cx.id(n).unwrap();
            let cands: Vec<u32> = net(&engine).candidates(&cx, id).collect();
            for (ri, l) in engine.inner.rules.iter().enumerate() {
                if !l.rule.decreasing {
                    continue;
                }
                if crate::rules::matcher::match_rule(&cx, &l.rule, id).is_some() {
                    matched += 1;
                    assert!(
                        cands.contains(&(ri as u32)),
                        "{} matches `{}` but was filtered out",
                        l.rule.name,
                        cx.display(n)
                    );
                }
            }
        }
    }
    assert!(matched > 20, "{matched}");
}

#[test]
fn runs_are_deterministic_and_order_independent() {
    let engine = Engine::standard();
    let mut g1 = generator(42);
    let mut g2 = generator(42);
    for _ in 0..100 {
        let (mut c1, mut c2) = (Context::new(), Context::new());
        let (a1, _) = g1.expr(&mut c1, 5, 3);
        let (b1, _) = g1.expr(&mut c1, 5, 3);
        let (a2, _) = g2.expr(&mut c2, 5, 3);
        let (b2, _) = g2.expr(&mut c2, 5, 3);
        let o1 = engine.run(&mut c1, &[a1, b1, a1], Run::default()).unwrap();
        let o2 = engine.run(&mut c2, &[b2, a2], Run::default()).unwrap();
        assert_eq!(o1.roots[0], o1.roots[2]);
        let s = |cx: &Context, e: Expr| cx.display(e).to_string();
        assert_eq!(s(&c1, o1.roots[0].expr), s(&c2, o2.roots[1].expr));
        assert_eq!(s(&c1, o1.roots[1].expr), s(&c2, o2.roots[0].expr));
    }
}

fn big(cx: &mut Context) -> Expr {
    let o = ParseOptions::width(Width::W16);
    let mut e = cx.parse("(a & b) + (a | b)", &o).unwrap();
    for i in 0..20 {
        let s = format!("((q{i} ^ ~q{i}) & p{i}) | (p{i} & (p{i} | r{i}))");
        let t = cx.parse(&s, &o).unwrap();
        e = cx.bin(BinOp::Xor, e, t).unwrap();
    }
    e
}

#[test]
fn memo_is_reused_and_invalidated() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let e = big(&mut cx);
    let first = engine.simplify(&mut cx, e).unwrap();
    let again = engine.run(&mut cx, &[e], Run::default()).unwrap();
    assert_eq!(again.roots[0], first);
    assert_eq!(again.stats.node_visits, 0);
    assert!(again.stats.memo_hits > 0);
    // Another engine (different epoch) starts afresh.
    let other = Engine::builder()
        .builtin()
        .verify(Verify::strict())
        .build()
        .unwrap();
    let o = other.run(&mut cx, &[e], Run::default()).unwrap();
    assert!(o.stats.node_visits > 0);
    assert_eq!(o.roots[0].expr, first.expr);
    // New assumptions start afresh too.
    let x = cx.symbol("a", Width::W16).unwrap();
    let mut a = Assumptions::new();
    a.assume(&mut cx, x, Facts::constant(&BitVec::zero(Width::W16)))
        .unwrap();
    let o = engine
        .run(
            &mut cx,
            &[e],
            Run {
                assumptions: Some(&a),
                ..Run::default()
            },
        )
        .unwrap();
    assert!(o.stats.node_visits > 0);
    // clear() drops it.
    let mut cx2 = Context::new();
    let e2 = big(&mut cx2);
    engine.simplify(&mut cx2, e2).unwrap();
    cx2.clear();
    assert!(cx2.memo.phases.is_empty());
}

#[test]
fn budgets_stop_runs_and_are_never_refunded() {
    let engine = Engine::standard();
    let mut rng = Rng(3);
    for cap in [0u64, 1, 5, 20, 60] {
        let mut cx = Context::new();
        let e = big(&mut cx);
        let out = engine
            .run(
                &mut cx,
                &[e],
                Run {
                    per_call: Budget {
                        node_visits: cap,
                        ..Budget::UNLIMITED
                    },
                    ..Run::default()
                },
            )
            .unwrap();
        let r = out.roots[0];
        assert_eq!(
            r.end,
            End::BudgetTerminated(Exhausted::NodeVisits),
            "cap {cap}"
        );
        assert!(out.stats.node_visits <= cap + 1);
        assert!(equivalent(&mut cx, e, r.expr, &mut rng));
    }
    // An allowance spans calls; what one call spends the next cannot use.
    let mut allowance = Allowance::new(Budget {
        node_visits: 40,
        ..Budget::UNLIMITED
    });
    let mut ends = Vec::new();
    let mut total = 0;
    for _ in 0..4 {
        let mut cx = Context::new();
        let e = big(&mut cx);
        let out = engine
            .run(
                &mut cx,
                &[e],
                Run {
                    allowance: Some(&mut allowance),
                    per_call: Budget::UNLIMITED,
                    ..Run::default()
                },
            )
            .unwrap();
        total += out.stats.node_visits;
        ends.push(out.roots[0].end);
    }
    assert_eq!(allowance.spent().node_visits, total);
    assert!(total <= 40 + 4);
    assert!(ends.iter().all(|e| matches!(e, End::BudgetTerminated(_))));
    // A budget-terminated run memoizes only completed nodes: finishing later agrees with a
    // fresh run.
    let mut cx = Context::new();
    let e = big(&mut cx);
    let _ = engine.run(
        &mut cx,
        &[e],
        Run {
            per_call: Budget {
                rewrites: 3,
                ..Budget::UNLIMITED
            },
            ..Run::default()
        },
    );
    let later = engine.simplify(&mut cx, e).unwrap();
    let mut fresh = Context::new();
    let f = big(&mut fresh);
    let want = engine.simplify(&mut fresh, f).unwrap();
    assert_eq!(later.end, End::Completed);
    assert_eq!(
        cx.display(later.expr).to_string(),
        fresh.display(want.expr).to_string()
    );
}

#[test]
fn admission_declines_before_any_work() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let e = big(&mut cx);
    for (adm, cap) in [
        (
            Admission {
                max_root_height: 2,
                ..Admission::default()
            },
            Cap::Height,
        ),
        (
            Admission {
                max_root_tree_size: 10,
                ..Admission::default()
            },
            Cap::TreeSize,
        ),
        (
            Admission {
                max_root_dag_size: Some(10),
                ..Admission::default()
            },
            Cap::DagSize,
        ),
    ] {
        let out = engine
            .run(
                &mut cx,
                &[e],
                Run {
                    admission: adm,
                    ..Run::default()
                },
            )
            .unwrap();
        assert_eq!(out.roots[0].end, End::Declined(Decline::AdmissionCap(cap)));
        assert_eq!(out.roots[0].expr, e);
        assert_eq!(out.stats.node_visits, 0);
    }
}

struct Ticker(core::cell::Cell<u64>);

impl Clock for Ticker {
    fn now_ticks(&self) -> u64 {
        let t = self.0.get();
        self.0.set(t + 1);
        t
    }
}

#[test]
fn deadlines_stop_runs() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let e = big(&mut cx);
    let clock = Ticker(core::cell::Cell::new(0));
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                deadline: Some(Deadline {
                    clock: &clock,
                    at: 3,
                    check_every: 2,
                }),
                ..Run::default()
            },
        )
        .unwrap();
    assert_eq!(out.roots[0].end, End::BudgetTerminated(Exhausted::Deadline));
}

struct VetoAll(u64);

impl Hooks for VetoAll {
    fn admit(&self, _: &Context, _: Expr, _: Expr, _: By<'_>) -> bool {
        false
    }
    fn revision(&self) -> u64 {
        self.0
    }
}

#[test]
fn hooks_veto_and_their_revision_keys_the_memo() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let e = big(&mut cx);
    let veto = VetoAll(1);
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                hooks: Some(&veto),
                ..Run::default()
            },
        )
        .unwrap();
    assert!(!out.roots[0].changed);
    assert!(out.stats.hook_vetoes > 0);
    // Without the hook (a different revision) the memo from the vetoed run is not reused.
    let out = engine.simplify(&mut cx, e).unwrap();
    assert!(out.changed);
}

#[test]
fn census_agrees_with_stats() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let e = big(&mut cx);
    let mut census = RuleCensus::default();
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                observer: Some(&mut census),
                ..Run::default()
            },
        )
        .unwrap();
    let sum = |f: fn(&RuleCounts) -> u64| census.rules.values().map(f).sum::<u64>();
    assert_eq!(sum(|c| c.applied), out.stats.rewrites);
    assert_eq!(sum(|c| c.candidates), out.stats.candidates);
    assert_eq!(sum(|c| c.no_match), out.stats.no_match);
    assert_eq!(sum(|c| c.guard_false), out.stats.guard_false);
    assert!(out.stats.rewrites > 0);
}

#[test]
fn linking_requires_proof_unless_allowed() {
    let src = "bitwright 1;\ngroup x.g {\n#[allow(BW0407)]\nrule wrong<W>(x: W, y: W) { (x & y) | (x ^ y) => x }\n}\n";
    let p = RuleProgram::compile(src).unwrap();
    assert!(matches!(
        Engine::builder().unproven_program(p.clone()).build(),
        Err(BuildError::Unproven { .. })
    ));
    // Allowed, the unsound rule is caught by sampled verification and quarantined.
    let engine = Engine::builder()
        .allow_unproven(true)
        .unproven_program(p)
        .build()
        .unwrap();
    let mut cx = Context::new();
    let e = cx
        .parse("(a & b) | (a ^ b)", &ParseOptions::width(Width::W8))
        .unwrap();
    let out = engine.run(&mut cx, &[e], Run::default()).unwrap();
    assert!(!out.roots[0].changed);
    assert_eq!(out.stats.quarantined, 1);
    // A ledger for another rule does not vouch for this one.
    let q = RuleProgram::compile(src).unwrap();
    let (_, ledger) = builtin();
    assert!(Engine::builder().program(q, ledger).build().is_err());
    // Unknown groups are errors.
    assert!(matches!(
        Engine::builder()
            .builtin()
            .strategy(Strategy::new(
                "x",
                vec![Phase::Local {
                    groups: vec!["nope".into()]
                }]
            ))
            .build(),
        Err(BuildError::UnknownGroup(_))
    ));
}

#[test]
fn assumptions_enable_fact_guards() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let w = Width::W8;
    let e = cx.parse("x & 15", &ParseOptions::width(w)).unwrap();
    assert!(!engine.simplify(&mut cx, e).unwrap().changed);
    let x = cx.symbol("x", w).unwrap();
    let small = Facts::new(
        KnownBits::unknown(w),
        URange::new(BitVec::zero(w), BitVec::from_u64(w, 15).unwrap()).unwrap(),
        SRange::full(w),
    )
    .unwrap();
    let mut a = Assumptions::new();
    a.assume(&mut cx, x, small).unwrap();
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                assumptions: Some(&a),
                ..Run::default()
            },
        )
        .unwrap();
    assert_eq!(out.roots[0].expr, x);
    // Without them again, the earlier (unassumed) result comes back.
    assert!(!engine.simplify(&mut cx, e).unwrap().changed);
}

#[test]
fn fact_limits_end_runs_honestly_and_are_not_memoized() {
    let engine = Engine::standard();
    let o = ParseOptions::width(Width::W8);
    // The call's own fact budget: the run stops, and nothing it skipped is memoized.
    let mut cx = Context::new();
    let e = cx.parse("((q & 0xf0) & 15) ^ z", &o).unwrap();
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                per_call: Budget {
                    fact_work: 0,
                    ..Budget::UNLIMITED
                },
                ..Run::default()
            },
        )
        .unwrap();
    assert_eq!(out.roots[0].end, End::BudgetTerminated(Exhausted::FactWork));
    let out = engine.simplify(&mut cx, e).unwrap();
    assert_eq!(out.end, End::Completed);
    assert_eq!(cx.display(out.expr).to_string(), "z");
    // The context's per-query cap: the run finishes, but the root is not final (the rule
    // needed more facts than one query may compute), and nothing above it is memoized.
    let mut cx = Context::with_config(crate::ContextConfig::default().with_fact_work(1));
    let deep = cx
        .parse("((((q & 0xf0) + (r & 0xf0)) & 0xf0) & 15) ^ z", &o)
        .unwrap();
    let out = engine.run(&mut cx, &[deep], Run::default()).unwrap();
    assert_eq!(out.roots[0].end, End::BudgetTerminated(Exhausted::FactWork));
    assert!(out.stats.degraded > 0);
    let again = engine.run(&mut cx, &[deep], Run::default()).unwrap();
    assert!(
        again.stats.node_visits > 0,
        "a non-final result was memoized"
    );
}

#[test]
fn match_step_budgets_end_runs() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let e = cx
        .parse("(x & y) + (x | y)", &ParseOptions::width(Width::W8))
        .unwrap();
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                per_call: Budget {
                    match_steps: 0,
                    ..Budget::UNLIMITED
                },
                ..Run::default()
            },
        )
        .unwrap();
    assert_eq!(
        out.roots[0].end,
        End::BudgetTerminated(Exhausted::MatchSteps)
    );
    let out = engine.simplify(&mut cx, e).unwrap();
    assert_eq!(cx.display(out.expr).to_string(), "x + y");
}

#[test]
fn rewrite_chains_reach_the_normal_form() {
    // One round: a `Local` phase reaches the normal form by itself (later rounds exist for the
    // interplay of phases, and must not hide an incomplete one).
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::standard().with_max_rounds(1))
        .verify(Verify::strict())
        .build()
        .unwrap();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    // `-~x` becomes `x + 1`, whose operands share no bits, so it becomes `x | 1`: two rewrites
    // at the same node.
    let e = cx.parse("-(~(y << 1))", &o).unwrap();
    let mut census = RuleCensus::default();
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                observer: Some(&mut census),
                ..Run::default()
            },
        )
        .unwrap();
    assert_eq!(out.stats.rewrites, 2, "{census:?}");
    assert_eq!(cx.parse("(y << 1) | 1", &o).unwrap(), out.roots[0].expr);
}

/// Rules covering every parameter kind and every kind of pattern root, for the dispatch net.
const DISPATCH_FIXTURE: &str = r#"
bitwright 1;
group f {
    rule k_const<W>(x: W, c: const W) { (x & c) & c => x & c }
    rule k_sym<W>(s: sym W, y: W) { (s | y) & s => s }
    rule k_nonconst<W>(n: nonconst W, y: W) { (n ^ y) ^ n => y }
    rule r_cmp<W>(a: W, b: W) { (a >u b) & (a == b) => 0 }
    rule r_ugt<W>(a: W, b: W) { (a & b) >u a => 0 }
    rule r_select<W>(c: 1, x: W, y: W) { select(c, x, y) & (x & y) => x & y }
    rule r_extract<W>(x: W) where W >= 2 { extract<1, 1>(x << 1) => trunc<1>(x) }
    rule r_sext<W, U>(x: W, y: W) where W < U { trunc<W>(sext<U>(x) ^ sext<U>(y)) => x ^ y }
    rule r_concat<W, U>(x: W, y: U, z: W, t: U) { concat(x ^ z, y ^ t) => concat(x, y) ^ concat(z, t) }
    rule r_un<W>(x: W) { popcnt(bitrev(x)) => popcnt(x) }
}
"#;

#[test]
fn dispatch_is_a_pure_prefilter_for_every_pattern_kind() {
    let p = RuleProgram::compile_with(DISPATCH_FIXTURE, &crate::rules::CompileOptions::default());
    let p = match p {
        Ok(p) => p,
        Err(e) => panic!("{}", e.render("fixture", DISPATCH_FIXTURE)),
    };
    let unreachable: Vec<String> = p
        .diagnostics()
        .iter()
        .filter(|d| d.code == "BW0402")
        .map(|d| d.render("fixture", DISPATCH_FIXTURE))
        .collect();
    assert!(unreachable.is_empty(), "{}", unreachable.join("\n"));
    let engine = Engine::builder()
        .allow_unproven(true)
        .unproven_program(p)
        .build()
        .unwrap();
    let mut g = generator(0xf1c5);
    let mut matched = vec![0u32; engine.inner.rules.len()];
    for i in 0..3000 {
        let mut cx = Context::new();
        let e = if i % 2 == 0 {
            let w = 1 + g.rng.below(6) as u16;
            g.expr(&mut cx, w, 3).0
        } else {
            redex_rich(&engine, &mut g, &mut cx)
        };
        for n in cx.post_order(&[e]).unwrap() {
            let id = cx.id(n).unwrap();
            let cands: Vec<u32> = net(&engine).candidates(&cx, id).collect();
            for (ri, l) in engine.inner.rules.iter().enumerate() {
                if crate::rules::matcher::match_rule(&cx, &l.rule, id).is_some() {
                    matched[ri] += 1;
                    assert!(
                        cands.contains(&(ri as u32)),
                        "{} matches `{}` but was filtered out",
                        l.rule.name,
                        cx.display(n)
                    );
                }
            }
        }
    }
    for (l, m) in engine.inner.rules.iter().zip(&matched) {
        if l.rule.decreasing {
            assert!(*m > 0, "{} never matched", l.rule.name);
        }
    }
}

#[test]
fn arena_capacity_stops_runs() {
    let engine = Engine::standard();
    let mut cx = Context::with_config(crate::ContextConfig::default().with_max_nodes(64));
    let o = ParseOptions::width(Width::W8);
    let e = cx
        .parse("(a & b) + (a | b) + ((c ^ d) + 2 * (c & d))", &o)
        .unwrap();
    let before = cx.len();
    let mut filler = cx.symbol("f0", Width::W8).unwrap();
    while cx.len() < 63 {
        let s = cx
            .symbol(format!("f{}", cx.len()).as_str(), Width::W8)
            .unwrap();
        filler = cx.bin(BinOp::Xor, filler, s).unwrap_or(filler);
        if cx.len() == before {
            break;
        }
    }
    let out = engine.run(&mut cx, &[e], Run::default()).unwrap();
    assert!(matches!(
        out.roots[0].end,
        End::BudgetTerminated(Exhausted::ArenaCapacity) | End::Completed
    ));
}

// ----- regressions from the M4 review ------------------------------------------------------------

/// A host that implements only `admit` (default revision 0).
struct VetoDefault;

impl Hooks for VetoDefault {
    fn admit(&self, _: &Context, _: Expr, _: Expr, _: By<'_>) -> bool {
        false
    }
}

#[test]
fn hooks_with_the_default_revision_never_share_a_memo_with_no_hooks() {
    let engine = Engine::standard();
    let o = ParseOptions::width(Width::W8);
    // No hooks first, then the veto: the veto must hold.
    let mut cx = Context::new();
    let e = cx.parse("(x & y) + (x | y)", &o).unwrap();
    assert!(engine.simplify(&mut cx, e).unwrap().changed);
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                hooks: Some(&VetoDefault),
                ..Run::default()
            },
        )
        .unwrap();
    assert!(!out.roots[0].changed);
    // The veto first, then no hooks: the rewrite must happen.
    let mut cx = Context::new();
    let e = cx.parse("(x & y) + (x | y)", &o).unwrap();
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                hooks: Some(&VetoDefault),
                ..Run::default()
            },
        )
        .unwrap();
    assert!(!out.roots[0].changed);
    assert!(engine.simplify(&mut cx, e).unwrap().changed);
}

#[test]
fn a_rewrite_after_a_degraded_candidate_is_not_final() {
    // `f` needs facts (declined when a query is capped); `p`, below it, always applies.
    let src = "bitwright 1;\ngroup g {\n\
        #[allow(BW0407)] rule f<W>(x: W, c: const W) { (x ^ c) & c => c if zero_bits(x, c) }\n\
        #[allow(BW0407)] rule p<W>(x: W, c: const W) { (x ^ c) & c => ~x & c }\n}\n";
    let p = RuleProgram::compile(src).unwrap();
    let engine = Engine::builder()
        .allow_unproven(true)
        .unproven_program(p)
        .build()
        .unwrap();
    let o = ParseOptions::width(Width::W8);
    let mut fresh = Context::new();
    let e = fresh.parse("((q & 0xf0) ^ 0x0f) & 0x0f", &o).unwrap();
    let want = engine.simplify(&mut fresh, e).unwrap();
    assert_eq!(fresh.display(want.expr).to_string(), "15:8");
    // With a per-query cap of one transfer, `f` is declined and `p` applies: not final.
    let mut cx = Context::with_config(crate::ContextConfig::default().with_fact_work(1));
    let e = cx.parse("((q & 0xf0) ^ 0x0f) & 0x0f", &o).unwrap();
    let first = engine.simplify(&mut cx, e).unwrap();
    assert_eq!(first.end, End::BudgetTerminated(Exhausted::FactWork));
    // Capped queries resume, so later runs converge to the budget-free answer, never
    // answering from a memoized non-final result.
    let mut last = first;
    for _ in 0..8 {
        last = engine.simplify(&mut cx, e).unwrap();
        if last.end == End::Completed {
            break;
        }
    }
    assert_eq!(last.end, End::Completed);
    assert_eq!(cx.display(last.expr).to_string(), "15:8");
}

#[test]
fn a_passed_deadline_stops_every_later_root() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let roots: Vec<Expr> = (0..50)
        .map(|i| {
            cx.parse(&format!("(a{i} & b{i}) + (a{i} | b{i})"), &o)
                .unwrap()
        })
        .collect();
    let clock = Ticker(core::cell::Cell::new(0));
    let out = engine
        .run(
            &mut cx,
            &roots,
            Run {
                deadline: Some(Deadline {
                    clock: &clock,
                    at: 1,
                    check_every: 20,
                }),
                ..Run::default()
            },
        )
        .unwrap();
    let first = out
        .roots
        .iter()
        .position(|r| r.end == End::BudgetTerminated(Exhausted::Deadline))
        .expect("the deadline passed");
    for r in &out.roots[first..] {
        assert_eq!(r.end, End::BudgetTerminated(Exhausted::Deadline));
    }
}

#[test]
fn fact_budgets_are_not_overrun() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let w = Width::W8;
    let mut e = cx.symbol("x", w).unwrap();
    for i in 0..2000 {
        let s = cx.symbol(format!("s{i}").as_str(), w).unwrap();
        e = cx.bin(BinOp::Mul, e, s).unwrap();
    }
    let fifteen = cx.constant_u64(w, 15).unwrap();
    let e = cx.bin(BinOp::And, e, fifteen).unwrap();
    let out = engine
        .run(
            &mut cx,
            &[e],
            Run {
                per_call: Budget {
                    fact_work: 1,
                    ..Budget::UNLIMITED
                },
                ..Run::default()
            },
        )
        .unwrap();
    assert!(out.stats.fact_work <= 1, "{}", out.stats.fact_work);
    assert_eq!(out.roots[0].end, End::BudgetTerminated(Exhausted::FactWork));
}

#[test]
fn a_full_arena_is_not_an_error_when_nothing_is_built() {
    let engine = Engine::standard();
    let mut probe = Context::new();
    let o = ParseOptions::width(Width::W8);
    probe.parse("x & 15", &o).unwrap();
    let mut cx =
        Context::with_config(crate::ContextConfig::default().with_max_nodes(probe.len() as u32));
    let e = cx.parse("x & 15", &o).unwrap();
    let out = engine.simplify(&mut cx, e).unwrap();
    assert_eq!(out.end, End::Completed);
    assert!(!out.changed);
}

#[test]
fn sampled_verification_is_linear_in_the_dag() {
    let engine = strict_rules();
    let mut cx = Context::new();
    let w = Width::W16;
    let n = 1500u64;
    let mut e = cx.symbol("x", w).unwrap();
    for i in 0..n {
        let s = cx.symbol(format!("s{i}").as_str(), w).unwrap();
        let t = cx.symbol(format!("t{i}").as_str(), w).unwrap();
        let o = cx.bin(BinOp::Or, e, s).unwrap();
        let a = cx.bin(BinOp::And, e, o).unwrap();
        e = cx.bin(BinOp::Xor, a, t).unwrap();
    }
    let out = engine.run(&mut cx, &[e], Run::default()).unwrap();
    assert_eq!(out.roots[0].end, End::Completed);
    assert!(out.stats.rewrites >= n);
    assert!(out.stats.node_visits < 30 * n, "{}", out.stats.node_visits);
}

#[test]
fn saturated_tree_sizes_do_not_block_strict_rewrites() {
    let engine = strict();
    let mut cx = Context::new();
    let w = Width::W8;
    let mut b = cx.symbol("b", w).unwrap();
    for i in 0..40 {
        let s = cx.symbol(format!("s{i}").as_str(), w).unwrap();
        let t = cx.bin(BinOp::Add, b, s).unwrap();
        b = cx.bin(BinOp::Mul, b, t).unwrap();
    }
    assert_eq!(cx.tree_size(b).unwrap(), u32::MAX);
    let y = cx.symbol("y", w).unwrap();
    let o = cx.bin(BinOp::Or, b, y).unwrap();
    let e = cx.bin(BinOp::And, b, o).unwrap();
    let out = engine.simplify(&mut cx, e).unwrap();
    assert_eq!(out.expr, b);
}

// ----- consumer-defined constraints -------------------------------------------------------------

fn run_under(engine: &Engine, cx: &mut Context, e: Expr, a: &Assumptions) -> RootOutcome {
    engine
        .run(cx, &[e], Run::default().with_assumptions(a))
        .unwrap()
        .roots[0]
}

#[test]
fn constraints_on_predicates_simplify_what_they_imply() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W64);
    // An ABI invariant: the stack pointer is 16-byte aligned.
    let aligned = cx.parse("(rsp & 15) == 0", &o).unwrap();
    // A path condition: the bounds check `cmp idx, n; jb` was taken.
    let bounds = cx.parse("idx <u n", &o).unwrap();
    // Integer division on a path that does not fault.
    let d = cx.parse("d", &o).unwrap();
    let q = cx.parse("q", &o).unwrap();
    let trap = crate::traps::udiv(&mut cx, q, d).unwrap();

    let mut a = Assumptions::new();
    let inv = a.assume_true(&mut cx, aligned).unwrap();
    let path = a.assume_true(&mut cx, bounds).unwrap();
    let no_fault = a.assume_false(&mut cx, trap).unwrap();
    assert!(!a.is_infeasible());

    let check = |cx: &mut Context, src: &str, want: &str| {
        let e = cx.parse(src, &o).unwrap();
        let out = run_under(&engine, cx, e, &a);
        let w = cx.width(e).unwrap();
        let want = cx.parse(want, &ParseOptions::width(w)).unwrap();
        assert_eq!(out.expr, want, "{src} gave {}", cx.display(out.expr));
        out.relies_on
    };
    // Alignment makes the low bits known.
    let r = check(&mut cx, "(rsp + 32) & 15", "0");
    assert!(r.may_use(inv) && !r.may_use(path) && !r.may_use(no_fault));
    assert!(r.all_before(path), "{r:?}");
    let r = check(&mut cx, "rsp & 0xfffffffffffffff0", "rsp");
    assert!(r.all_before(path), "{r:?}");
    // The branch condition decides every comparison of the same pair.
    let r = check(&mut cx, "idx <=u n", "1");
    assert!(r.may_use(path) && !r.may_use(inv), "{r:?}");
    check(&mut cx, "n == idx", "0");
    check(&mut cx, "n <u idx", "0");
    // ... and bounds n from below.
    check(&mut cx, "n != 0", "1");
    // The trap known not to happen: the divisor is not zero.
    let r = check(&mut cx, "d == 0", "0");
    assert!(r.may_use(no_fault) && !r.may_use(path), "{r:?}");
    // What relies on nothing reports nothing.
    let e = cx.parse("(x & 0xff) & 0xf0", &o).unwrap();
    let out = run_under(&engine, &mut cx, e, &a);
    assert!(out.changed && out.relies_on.is_none());
    // An unchanged result relies on nothing, whatever was consulted.
    let e = cx.parse("idx + n", &o).unwrap();
    let out = run_under(&engine, &mut cx, e, &a);
    assert!(!out.changed && out.relies_on.is_none());
}

#[test]
fn constraints_propagate_through_casts_and_bit_counts() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let mut a = Assumptions::new();
    // A byte zero-extended into a register and compared against 'A'.
    let p = cx.parse("zext<32>(b:8) == 0x41", &o).unwrap();
    a.assume_true(&mut cx, p).unwrap();
    // A bit scan found bit 3 lowest.
    let p = cx.parse("ctz(m) == 3", &o).unwrap();
    a.assume_true(&mut cx, p).unwrap();
    // An unsigned count masked by the caller: below 32.
    let p = cx.parse("c <u 32", &o).unwrap();
    a.assume_true(&mut cx, p).unwrap();
    for (src, want) in [
        ("zext<32>(b:8) + 1", "0x42"),
        ("m & 15", "8"),
        ("c & 31", "c"),
        ("c >>u 5", "0"),
        // `|` of operands disjoint only under the constraint: `+` (linear) and `^` (xor).
        ("(c | (d << 5)) - c", "d << 5"),
        ("(c | (d << 5)) ^ c", "d << 5"),
    ] {
        let e = cx.parse(src, &o).unwrap();
        let out = run_under(&engine, &mut cx, e, &a);
        let want = cx.parse(want, &o).unwrap();
        assert_eq!(out.expr, want, "{src} gave {}", cx.display(out.expr));
        assert!(!out.relies_on.is_none());
    }
}

#[test]
fn contradictory_constraints_are_reported_and_prove_nothing_in_the_engine() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let mut a = Assumptions::new();
    let p0 = cx.parse("y == 3", &o).unwrap();
    let p1 = cx.parse("x <u 5", &o).unwrap();
    let p2 = cx.parse("x >u 7", &o).unwrap();
    let i0 = a.assume_true(&mut cx, p0).unwrap();
    let i1 = a.assume_true(&mut cx, p1).unwrap();
    assert!(!a.is_infeasible());
    let i2 = a.assume_true(&mut cx, p2).unwrap();
    assert!(a.is_infeasible());
    let c = a.conflict().unwrap();
    assert!(c.may_use(i1) && c.may_use(i2) && !c.may_use(i0), "{c:?}");
    // The engine proves nothing from them (the result is still valid everywhere).
    let e = cx.parse("x & 0xf0", &o).unwrap();
    let out = run_under(&engine, &mut cx, e, &a);
    assert!(!out.changed);
    // prove_under reports every question as true, relying on the conflict.
    let x = cx.parse("x", &o).unwrap();
    let p = cx.prove_under(Query::IsZero(x), &a).unwrap();
    assert_eq!(p.truth, Truth::True);
    assert_eq!(p.relies_on, c);
}

#[test]
fn forked_constraint_sets_share_invariants_and_keep_their_own_paths() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W16);
    let mut inv = Assumptions::new();
    let p = cx.parse("(p & 3) == 0", &o).unwrap();
    let i = inv.assume_true(&mut cx, p).unwrap();
    let cond = cx.parse("x == 7", &o).unwrap();
    let mut taken = inv.clone();
    let mut not_taken = inv.clone();
    let t = taken.assume_true(&mut cx, cond).unwrap();
    let n = not_taken.assume_false(&mut cx, cond).unwrap();
    assert_eq!((t, n), (inv.next_id(), inv.next_id()));
    assert_eq!(inv.len(), 1);
    let e = cx.parse("zext<16>(x == 7) + (p & 1)", &o).unwrap();
    let a = run_under(&engine, &mut cx, e, &taken);
    let b = run_under(&engine, &mut cx, e, &not_taken);
    let c = run_under(&engine, &mut cx, e, &inv);
    assert_eq!(a.expr, cx.parse("1", &o).unwrap(), "{}", cx.display(a.expr));
    assert_eq!(b.expr, cx.parse("0", &o).unwrap(), "{}", cx.display(b.expr));
    assert!(a.relies_on.may_use(t) && a.relies_on.may_use(i));
    assert!(c.changed && c.relies_on.all_before(t));
    assert_ne!(c.expr, a.expr);
    // Asking the first again is a memo hit only if the set did not change.
    let again = engine
        .run(&mut cx, &[e], Run::default().with_assumptions(&taken))
        .unwrap();
    assert_eq!(again.roots[0], a);
}

#[test]
fn strict_verification_compares_only_where_the_relied_on_constraints_hold() {
    // Sampled points ignore constraints: a rewrite valid only under them must not be rejected
    // (or its rule quarantined) because a random point violates them.
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::standard())
        .verify(Verify::strict())
        .build()
        .unwrap();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let mut a = Assumptions::new();
    let p = cx.parse("x <u 16", &o).unwrap();
    a.assume_true(&mut cx, p).unwrap();
    let p = cx.parse("(y & 0xff00) == 0x1200", &o).unwrap();
    a.assume_true(&mut cx, p).unwrap();
    let e = cx.parse("(x & 15) + ((y >>u 8) & 0xff)", &o).unwrap();
    let out = engine
        .run(&mut cx, &[e], Run::default().with_assumptions(&a))
        .unwrap();
    assert_eq!(out.stats.rejected, 0, "{:?}", out.stats);
    assert_eq!(out.stats.quarantined, 0);
    let want = cx.parse("x + 0x12", &o).unwrap();
    assert_eq!(
        out.roots[0].expr,
        want,
        "got {}",
        cx.display(out.roots[0].expr)
    );
}

#[test]
fn every_result_holds_wherever_the_constraints_it_relies_on_hold() {
    use std::collections::HashMap;
    let engine = Engine::standard();
    let mut changed = 0;
    let mut relied = 0;
    for seed in 0..1200u64 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0x5e1f_0000 + seed),
            max_w: 3,
            vars: Vec::new(),
        };
        let w = 2 + g.rng.below(2) as u16;
        let mut preds = Vec::new();
        for _ in 0..3 {
            let (x, _) = g.expr(&mut cx, w, 1);
            let k = cx
                .constant(&BitVec::wrapping_from_u64(
                    crate::testutil::width(w),
                    g.rng.below(8),
                ))
                .unwrap();
            let op = crate::CmpOpExt::ALL[g.rng.below(10) as usize];
            preds.push(cx.cmp(op, x, k).unwrap());
        }
        let roots: Vec<Expr> = (0..4).map(|_| g.expr(&mut cx, w, 3).0).collect();
        let bits: u32 = g.vars.iter().map(|(_, w)| u32::from(*w)).sum();
        if bits > 12 {
            continue;
        }
        let mut a = Assumptions::new();
        let ids: Vec<_> = preds
            .iter()
            .map(|&p| a.assume_true(&mut cx, p).unwrap())
            .collect();
        let out = engine
            .run(&mut cx, &roots, Run::default().with_assumptions(&a))
            .unwrap();
        for (root, r) in roots.iter().zip(&out.roots) {
            if !r.changed {
                assert!(r.relies_on.is_none());
                continue;
            }
            changed += 1;
            if !r.relies_on.is_none() {
                relied += 1;
            }
            for code in 0..(1u64 << bits) {
                let mut c = code;
                let env: HashMap<SymbolKey, BitVec> = g
                    .vars
                    .iter()
                    .map(|(n, w)| {
                        let v = BitVec::wrapping_from_u64(crate::testutil::width(*w), c);
                        c >>= w;
                        (SymbolKey::from(n.as_str()), v)
                    })
                    .collect();
                let pv = cx.eval(&preds, &env).unwrap();
                let hold = ids
                    .iter()
                    .zip(&pv)
                    .all(|(&id, v)| !r.relies_on.may_use(id) || !v.is_zero());
                if !hold {
                    continue;
                }
                let v = cx.eval(&[*root, r.expr], &env).unwrap();
                assert_eq!(
                    v[0],
                    v[1],
                    "seed {seed}: {} -> {} relying on {:?} differs at {env:?}",
                    cx.display(*root),
                    cx.display(r.expr),
                    r.relies_on
                );
            }
        }
    }
    assert!(
        changed > 150 && relied > 60,
        "changed {changed}, relied {relied}"
    );
}

// ----- constraint reliance: fuzzing and the gaps an independent review found -------------------

mod reliance {
    use super::*;
    use crate::facts::{ConstraintId, Facts, Query, Truth};
    use crate::testutil::{Gen, Rng};
    use crate::{BitVec, CmpOp, CmpOpExt, SymbolKey, UnOp};
    use std::collections::HashMap;

    fn envs(vars: &[(String, u16)]) -> Option<Vec<HashMap<SymbolKey, BitVec>>> {
        let bits: u32 = vars.iter().map(|(_, w)| u32::from(*w)).sum();
        if bits > 12 {
            return None;
        }
        Some(
            (0..(1u64 << bits))
                .map(|code| {
                    let mut c = code;
                    vars.iter()
                        .map(|(n, w)| {
                            let v = BitVec::wrapping_from_u64(crate::testutil::width(*w), c);
                            c >>= w;
                            (SymbolKey::from(n.as_str()), v)
                        })
                        .collect()
                })
                .collect(),
        )
    }

    fn atom(g: &mut Gen, cx: &mut Context, depth: u32) -> Expr {
        let w = 1 + g.rng.below(3) as u16;
        let (a, _) = g.expr(cx, w, depth);
        match g.rng.below(5) {
            0 => {
                let m = cx.constant(&g.constant(w)).unwrap();
                let c = cx.constant(&g.constant(w)).unwrap();
                let am = cx.bin(BinOp::And, a, m).unwrap();
                cx.cmp(CmpOp::Eq, am, c).unwrap()
            }
            1 => {
                let c = cx.constant(&g.constant(w)).unwrap();
                let op = CmpOpExt::ALL[g.rng.below(10) as usize];
                cx.cmp(op, a, c).unwrap()
            }
            _ => {
                let (b, _) = g.expr(cx, w, depth);
                let op = CmpOpExt::ALL[g.rng.below(10) as usize];
                cx.cmp(op, a, b).unwrap()
            }
        }
    }

    fn pred(g: &mut Gen, cx: &mut Context, depth: u32) -> Expr {
        let p = atom(g, cx, depth);
        match g.rng.below(5) {
            0 => {
                let q = atom(g, cx, depth);
                cx.bin(BinOp::And, p, q).unwrap()
            }
            1 => {
                let q = atom(g, cx, depth);
                cx.bin(BinOp::Or, p, q).unwrap()
            }
            2 => cx.un(UnOp::Not, p).unwrap(),
            _ => p,
        }
    }

    fn holds_relied(a: &Assumptions, rel: Reliance, vals: &[(ConstraintIdX, bool)]) -> bool {
        let _ = a;
        vals.iter().all(|&(id, h)| !rel.may_use(id.0) || h)
    }
    #[derive(Copy, Clone)]
    struct ConstraintIdX(ConstraintId);

    /// Facts-level reliance: every node's facts under the assumptions hold wherever the constraints
    /// they report relying on hold.
    #[test]
    fn fact_reliance_is_sound_where_only_the_relied_on_constraints_hold() {
        let mut checked = 0u64;
        let mut partial = 0u64;
        for seed in 0..600u64 {
            let mut cx = Context::new();
            let mut g = Gen {
                rng: Rng(0x7e71_0000 + seed),
                max_w: 3,
                vars: Vec::new(),
            };
            let n = 1 + g.rng.below(4);
            let preds: Vec<(Expr, bool)> = (0..n)
                .map(|_| (pred(&mut g, &mut cx, 2), g.rng.chance(1, 2)))
                .collect();
            let w = 1 + g.rng.below(3) as u16;
            let probe = g.expr(&mut cx, w, 3).0;
            let Some(es) = envs(&g.vars) else { continue };
            let mut a = Assumptions::new();
            let mut ids = Vec::new();
            for &(p, v) in &preds {
                ids.push(if v {
                    a.assume_true(&mut cx, p).unwrap()
                } else {
                    a.assume_false(&mut cx, p).unwrap()
                });
            }
            if a.is_infeasible() {
                continue;
            }
            let mut nodes: Vec<Expr> = preds.iter().map(|&(p, _)| p).collect();
            nodes.push(probe);
            let all = cx.post_order(&nodes).unwrap();
            let cap = cx.config().fact_work;
            let fs: Vec<(Facts, Reliance)> = all
                .iter()
                .map(|&x| cx.facts_under_cap(x, &a, cap).unwrap().unwrap())
                .collect();
            let ps: Vec<Expr> = preds.iter().map(|&(p, _)| p).collect();
            for env in &es {
                let pv = cx.eval(&ps, env).unwrap();
                let hv: Vec<(ConstraintIdX, bool)> = ids
                    .iter()
                    .zip(&pv)
                    .zip(&preds)
                    .map(|((&id, v), &(_, want))| (ConstraintIdX(id), v.is_zero() != want))
                    .collect();
                let all_hold = hv.iter().all(|x| x.1);
                let vals = cx.eval(&all, env).unwrap();
                for ((x, (f, rel)), v) in all.iter().zip(&fs).zip(&vals) {
                    if holds_relied(&a, *rel, &hv) {
                        if !all_hold {
                            partial += 1;
                        }
                        checked += 1;
                        assert!(
                            f.contains(v),
                            "seed {seed}: {} = {v}, facts {f:?} relying on {rel:?}; assumed {:?} holds {:?}",
                            cx.display(*x),
                            preds
                                .iter()
                                .map(|&(p, v)| (cx.display(p).to_string(), v))
                                .collect::<Vec<_>>(),
                            hv.iter().map(|x| x.1).collect::<Vec<_>>()
                        );
                    }
                }
                // Proofs: every query answered under partial reliance.
            }
            // prove_under on every pair of same-width nodes
            for i in 0..all.len() {
                for j in 0..all.len() {
                    if seed % 8 != 0
                        || i == j
                        || cx.width(all[i]).unwrap() != cx.width(all[j]).unwrap()
                    {
                        continue;
                    }
                    for op in CmpOpExt::ALL {
                        let p = cx.prove_under(Query::Cmp(op, all[i], all[j]), &a).unwrap();
                        if p.truth == Truth::Unknown {
                            continue;
                        }
                        for env in &es {
                            let pv = cx.eval(&ps, env).unwrap();
                            let hv: Vec<(ConstraintIdX, bool)> = ids
                                .iter()
                                .zip(&pv)
                                .zip(&preds)
                                .map(|((&id, v), &(_, want))| {
                                    (ConstraintIdX(id), v.is_zero() != want)
                                })
                                .collect();
                            if !holds_relied(&a, p.relies_on, &hv) {
                                continue;
                            }
                            let v = cx.eval(&[all[i], all[j]], env).unwrap();
                            assert_eq!(
                                BitVec::apply_cmp(op, &v[0], &v[1]).unwrap(),
                                p.truth == Truth::True,
                                "seed {seed} prove {} {} {} rel {:?}",
                                cx.display(all[i]),
                                op.symbol(),
                                cx.display(all[j]),
                                p.relies_on
                            );
                        }
                    }
                }
            }
        }
        assert!(
            checked > 100_000 && partial > 1_000,
            "checked {checked}, partial {partial}"
        );
    }

    fn check_engine(engine: &Engine, seeds: std::ops::Range<u64>, budget: bool, two_calls: bool) {
        let seeds_len = seeds.end - seeds.start;
        let mut changed = 0;
        let mut relied = 0;
        for seed in seeds {
            let mut cx = Context::new();
            let mut g = Gen {
                rng: Rng(0x5eed_0000 + seed),
                max_w: 3,
                vars: Vec::new(),
            };
            let w = 2 + g.rng.below(2) as u16;
            let n = 1 + g.rng.below(4);
            let preds: Vec<(Expr, bool)> = (0..n)
                .map(|_| (pred(&mut g, &mut cx, 1), g.rng.chance(1, 2)))
                .collect();
            let roots: Vec<Expr> = (0..4).map(|_| g.expr(&mut cx, w, 3).0).collect();
            let roots2: Vec<Expr> = (0..4).map(|_| g.expr(&mut cx, w, 3).0).collect();
            let Some(es) = envs(&g.vars) else { continue };
            let mut a = Assumptions::new();
            let ids: Vec<_> = preds
                .iter()
                .map(|&(p, v)| {
                    if v {
                        a.assume_true(&mut cx, p).unwrap()
                    } else {
                        a.assume_false(&mut cx, p).unwrap()
                    }
                })
                .collect();
            if a.is_infeasible() {
                continue;
            }
            let mut calls: Vec<Vec<Expr>> = vec![roots.clone()];
            if two_calls {
                calls.push(roots2.clone());
                calls.push(roots.iter().chain(&roots2).copied().collect());
            }
            for rs in calls {
                let mut run = Run::default().with_assumptions(&a);
                if budget {
                    let mut b = Budget::UNLIMITED;
                    b.node_visits = 5 + g.rng.below(60);
                    b.fact_work = 3 + g.rng.below(200);
                    b.rewrites = 1 + g.rng.below(10);
                    run = run.with_per_call(b);
                }
                let out = engine.run(&mut cx, &rs, run).unwrap();
                let ps: Vec<Expr> = preds.iter().map(|&(p, _)| p).collect();
                for (root, r) in rs.iter().zip(&out.roots) {
                    if !r.changed {
                        assert!(r.relies_on.is_none());
                        continue;
                    }
                    changed += 1;
                    if !r.relies_on.is_none() {
                        relied += 1;
                    }
                    for env in &es {
                        let pv = cx.eval(&ps, env).unwrap();
                        let hold = ids
                            .iter()
                            .zip(&pv)
                            .zip(&preds)
                            .all(|((&id, v), &(_, want))| {
                                !r.relies_on.may_use(id) || (v.is_zero() != want)
                            });
                        if !hold {
                            continue;
                        }
                        let v = cx.eval(&[*root, r.expr], env).unwrap();
                        assert_eq!(
                            v[0],
                            v[1],
                            "seed {seed}: {} -> {} relying on {:?} (end {:?}) differs at {env:?}; preds {:?}",
                            cx.display(*root),
                            cx.display(r.expr),
                            r.relies_on,
                            r.end,
                            preds
                                .iter()
                                .map(|&(p, v)| (cx.display(p).to_string(), v))
                                .collect::<Vec<_>>()
                        );
                    }
                }
            }
        }
        let n = seeds_len as usize;
        assert!(
            changed * 40 > n && relied * 150 > n,
            "changed {changed}, relied {relied}"
        );
    }

    #[test]
    fn engine_results_hold_where_their_constraints_hold() {
        check_engine(&Engine::standard(), 0..2500, false, true);
    }

    #[test]
    fn budget_stopped_results_report_their_constraints() {
        check_engine(&Engine::standard(), 0..2500, true, true);
    }

    #[test]
    fn deobfuscation_results_hold_where_their_constraints_hold() {
        let e = Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap();
        check_engine(&e, 0..800, false, true);
    }

    fn w8(cx: &mut Context, v: u64) -> Expr {
        cx.constant(&BitVec::from_u64(crate::Width::W8, v).unwrap())
            .unwrap()
    }

    #[test]
    fn reliance_survives_refining_one_node_twice() {
        // P10: two facts on the same symbol.
        let mut cx = Context::new();
        let w = crate::Width::W8;
        let x = cx.symbol("x", w).unwrap();
        let mut a = Assumptions::new();
        let lo5 = Facts::new(
            crate::KnownBits::unknown(w),
            crate::URange::new(BitVec::zero(w), BitVec::from_u64(w, 5).unwrap()).unwrap(),
            crate::SRange::full(w),
        )
        .unwrap();
        let hi3 = Facts::new(
            crate::KnownBits::unknown(w),
            crate::URange::new(BitVec::from_u64(w, 3).unwrap(), BitVec::ones(w)).unwrap(),
            crate::SRange::full(w),
        )
        .unwrap();
        let i0 = a.assume(&mut cx, x, lo5).unwrap();
        let _i1 = a.assume(&mut cx, x, hi3).unwrap();
        let c6 = w8(&mut cx, 6);
        let p = cx
            .prove_under(Query::Cmp(CmpOpExt::Ule, x, c6), &a)
            .unwrap();
        assert_eq!(p.truth, Truth::True);
        assert!(p.relies_on.may_use(i0), "{:?}", p.relies_on);
    }

    #[test]
    fn reliance_includes_the_other_operands_constraints() {
        // P11: x + y == 10 with y == 3 gives x == 7, relying on both.
        let mut cx = Context::new();
        let w = crate::Width::W8;
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let c3 = w8(&mut cx, 3);
        let c10 = w8(&mut cx, 10);
        let c7 = w8(&mut cx, 7);
        let py = cx.cmp(CmpOpExt::Eq, y, c3).unwrap();
        let s = cx.bin(BinOp::Add, x, y).unwrap();
        let ps = cx.cmp(CmpOpExt::Eq, s, c10).unwrap();
        let mut a = Assumptions::new();
        let i0 = a.assume_true(&mut cx, py).unwrap();
        let i1 = a.assume_true(&mut cx, ps).unwrap();
        let p = cx.prove_under(Query::Eq(x, c7), &a).unwrap();
        assert_eq!(p.truth, Truth::True);
        assert!(
            p.relies_on.may_use(i0) && p.relies_on.may_use(i1),
            "{:?}",
            p.relies_on
        );
    }

    #[test]
    fn reliance_survives_narrowing_an_ordering_twice() {
        // P9: x <=u y then x != y gives x <u y relying on both.
        let mut cx = Context::new();
        let w = crate::Width::W8;
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let le = cx.cmp(CmpOpExt::Ule, x, y).unwrap();
        let ne = cx.cmp(CmpOpExt::Ne, x, y).unwrap();
        let mut a = Assumptions::new();
        let i0 = a.assume_true(&mut cx, le).unwrap();
        let i1 = a.assume_true(&mut cx, ne).unwrap();
        let p = cx.prove_under(Query::Cmp(CmpOpExt::Ult, x, y), &a).unwrap();
        assert_eq!(p.truth, Truth::True);
        assert!(
            p.relies_on.may_use(i0) && p.relies_on.may_use(i1),
            "{:?}",
            p.relies_on
        );
    }

    #[test]
    fn a_comparison_decided_by_an_ordering_relies_on_it() {
        // P7: a comparison node decided by an assumed ordering relies on it.
        let mut cx = Context::new();
        let w = crate::Width::W8;
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let lt = cx.cmp(CmpOpExt::Ult, x, y).unwrap();
        let le = cx.cmp(CmpOpExt::Ule, x, y).unwrap();
        let mut a = Assumptions::new();
        let i0 = a.assume_true(&mut cx, lt).unwrap();
        let p = cx.prove_under(Query::IsNonZero(le), &a).unwrap();
        assert_eq!(p.truth, Truth::True);
        assert!(p.relies_on.may_use(i0), "{:?}", p.relies_on);
    }

    #[test]
    fn a_rule_guard_decided_by_an_ordering_relies_on_it() {
        // P1: eq_eq_distinct via the assumed ordering b != c.
        let mut cx = Context::new();
        let w = crate::Width::W8;
        let a_ = cx.symbol("a", w).unwrap();
        let b = cx.symbol("b", w).unwrap();
        let c = cx.symbol("c", w).unwrap();
        let ne = cx.cmp(CmpOpExt::Ne, b, c).unwrap();
        let ab = cx.cmp(CmpOpExt::Eq, a_, b).unwrap();
        let ac = cx.cmp(CmpOpExt::Eq, a_, c).unwrap();
        let e = cx.bin(BinOp::And, ab, ac).unwrap();
        let mut asm = Assumptions::new();
        let i0 = asm.assume_true(&mut cx, ne).unwrap();
        let out = Engine::standard()
            .run(&mut cx, &[e], Run::default().with_assumptions(&asm))
            .unwrap();
        let r = out.roots[0];
        assert!(r.changed);
        assert!(r.relies_on.may_use(i0), "{:?}", r.relies_on);
    }

    #[test]
    fn an_equality_refuted_by_an_ordering_relies_on_it() {
        // P7: x != y decides the node x == y (no operand facts are learned from !=).
        let mut cx = Context::new();
        let w = crate::Width::W8;
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let ne = cx.cmp(CmpOpExt::Ne, x, y).unwrap();
        let eq = cx.cmp(CmpOpExt::Eq, x, y).unwrap();
        let mut a = Assumptions::new();
        let i0 = a.assume_true(&mut cx, ne).unwrap();
        let p = cx.prove_under(Query::IsZero(eq), &a).unwrap();
        assert_eq!(p.truth, Truth::True);
        assert!(p.relies_on.may_use(i0), "{:?}", p.relies_on);
    }
}

#[test]
fn stale_or_foreign_constraint_sets_are_errors_not_wrong_results() {
    // A rules-only engine (no pass queries facts first): the only check is the run's own.
    let engine = Engine::builder()
        .builtin()
        .strategy(rules_only())
        .build()
        .unwrap();
    let o = ParseOptions::width(Width::W8);
    let mut cx = Context::new();
    let mut a = Assumptions::new();
    let ne = cx.parse("b != c", &o).unwrap();
    a.assume_true(&mut cx, ne).unwrap();
    cx.clear();
    // After the clear, the same indices mean something else: q and r may be equal.
    let _ = cx.parse("q != r", &o).unwrap();
    let e = cx.parse("(p == q) & (p == r)", &o).unwrap();
    let r = engine.run(&mut cx, &[e], Run::default().with_assumptions(&a));
    assert!(matches!(r, Err(Error::StaleExpr)), "{r:?}");
    // Another context's set.
    let mut other = Context::new();
    let _ = other.parse("q != r", &o).unwrap();
    let e2 = other.parse("(p == q) & (p == r)", &o).unwrap();
    let mut b = Assumptions::new();
    let mut third = Context::new();
    let ne = third.parse("b != c", &o).unwrap();
    b.assume_true(&mut third, ne).unwrap();
    let r = engine.run(&mut other, &[e2], Run::default().with_assumptions(&b));
    assert!(matches!(r, Err(Error::ForeignExpr)), "{r:?}");
}

#[test]
fn contradictory_constraint_sets_simplify_as_no_constraints() {
    let o = ParseOptions::width(Width::W8);
    let mut cx = Context::new();
    let mut a = Assumptions::new();
    for p in ["x <u 5", "x >u 7"] {
        let p = cx.parse(p, &o).unwrap();
        a.assume_true(&mut cx, p).unwrap();
    }
    assert!(a.is_infeasible());
    let engine = Engine::standard();
    for src in [
        "x + 0",
        "(x & 0xf0) & 0x0f",
        "(y | 1) != 0",
        "zext<16>(y) >>u 8",
        "x & 15",
    ] {
        let e = cx.parse(src, &ParseOptions::width(Width::W8)).unwrap();
        let under = engine
            .run(&mut cx, &[e], Run::default().with_assumptions(&a))
            .unwrap()
            .roots[0];
        let plain = engine.simplify(&mut cx, e).unwrap();
        assert_eq!(under.expr, plain.expr, "{src}");
        assert_eq!(under.end, End::Completed, "{src}");
        assert!(under.relies_on.is_none(), "{src}");
    }
}

/// Fact work of a run over a long DAG, with and without a constraint on a symbol it does not
/// contain: the constraint must not make every query re-walk the DAG (it was quadratic).
#[test]
fn a_constraint_below_a_large_dag_does_not_make_queries_rewalk_it() {
    let work = |n: usize, constrained: bool| -> (u64, u64) {
        let mut cx = Context::new();
        let w = Width::W32;
        let s0 = cx.symbol("s0", w).unwrap();
        let c5 = cx.constant(&BitVec::from_u64(w, 5).unwrap()).unwrap();
        let p = cx.cmp(crate::CmpOpExt::Ult, s0, c5).unwrap();
        let mut acc = cx.symbol("y0", w).unwrap();
        for i in 1..n {
            let y = cx.symbol(format!("y{i}").as_str(), w).unwrap();
            let k = cx
                .constant(&BitVec::from_u64(w, (i as u64 * 2_654_435_761) & 0xffff).unwrap())
                .unwrap();
            let t = cx.xor(y, k).unwrap();
            acc = if i % 2 == 0 {
                cx.add(acc, t).unwrap()
            } else {
                cx.mul(acc, t).unwrap()
            };
        }
        let mut a = Assumptions::new();
        if constrained {
            a.assume_true(&mut cx, p).unwrap();
        }
        let walked = cx.facts.walked;
        let out = Engine::standard()
            .run(&mut cx, &[acc], Run::default().with_assumptions(&a))
            .unwrap();
        (out.stats.fact_work, cx.facts.walked - walked)
    };
    let ((plain, _), (constrained, walked)) = (work(2000, false), work(2000, true));
    assert!(
        constrained <= 3 * plain + 10_000,
        "fact work {constrained} with an unrelated constraint, {plain} without"
    );
    // Each node is walked a bounded number of times, not once per query.
    assert!(
        walked <= 20 * 2000,
        "the overlay walked {walked} nodes for a 2000-link DAG"
    );
}

/// Adding many constraints costs about linear propagation work, not quadratic.
#[test]
fn adding_many_constraints_takes_linear_work() {
    let steps = |n: usize| -> u64 {
        let mut cx = Context::new();
        let w = Width::W32;
        let mut preds = Vec::new();
        for i in 0..n {
            let x = cx.symbol(format!("x{i}").as_str(), w).unwrap();
            let c = cx
                .constant(&BitVec::from_u64(w, 1000 + i as u64).unwrap())
                .unwrap();
            preds.push(cx.cmp(crate::CmpOpExt::Eq, x, c).unwrap());
        }
        let mut a = Assumptions::new();
        let before = cx.facts.work;
        for &p in &preds {
            a.assume_true(&mut cx, p).unwrap();
        }
        assert!(!a.is_truncated());
        cx.facts.work - before
    };
    let (small, large) = (steps(250), steps(1000));
    assert!(
        large <= 6 * small + 1_000,
        "{small} transfers for 250, {large} for 1000"
    );
}
