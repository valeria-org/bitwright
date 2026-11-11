//! Engine properties: results are value-equivalent and normal, the dispatch net is a pure
//! prefilter, runs are idempotent, deterministic and order-independent, the memo is reused and
//! invalidated correctly, and budgets, admission, deadlines, hooks, observers, linking and
//! assumptions behave as documented.

use super::*;
use crate::facts::{Facts, KnownBits, Query, SRange, Truth, URange};
use crate::testutil::{Gen, Rng};
use crate::{BinOp, CmpOpExt, FnEnv, ParseOptions, SymbolKey};

/// The dispatch net of the engine's first `Local` phase.
fn net(engine: &Engine) -> &DispatchNet {
    engine
        .inner
        .phases
        .iter()
        .find_map(|p| match p {
            PhaseImpl::Local(n, _) => Some(&**n),
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
                .program
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
        for rule in engine.inner.rules.iter() {
            if !rule.decreasing || (rule.float_values && !engine.inner.strategy.float_values) {
                continue;
            }
            if let Some(r) = crate::rules::apply::try_apply(cx, rule, id)
                && r != id
            {
                panic!(
                    "{}: `{}` is not normal (rewrites to `{}`)",
                    rule.name,
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
        .filter(|r| r.decreasing && !r.float_values)
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
    // `#[float_values]` rules apply only when a strategy opts in (tested below).
    for rule in engine.inner.rules.iter().filter(|r| !r.float_values) {
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
    for rule in engine.inner.rules.iter().filter(|r| !r.float_values) {
        let c = census.rules.get(&rule.name).copied().unwrap_or_default();
        assert!(
            c.applied > 0,
            "{} never applied inside a larger expression",
            rule.name
        );
    }
}

/// `#[float_values]` rules apply exactly when the strategy opts in, and give their examples;
/// with the option, strict verification accepts their NaN changes.
#[test]
fn float_values_rules_apply_when_enabled() {
    let off = strict_rules();
    let on = Engine::builder()
        .builtin()
        .strategy(rules_only().with_float_values(true))
        .verify(Verify::strict())
        .build()
        .unwrap();
    let values: Vec<&Rule> = on.inner.rules.iter().filter(|r| r.float_values).collect();
    assert!(values.len() >= 6);
    for rule in values {
        for (input, output) in &rule.examples {
            let mut cx = Context::new();
            let o = ParseOptions::width(Width::W8);
            let e = cx.parse(input, &o).unwrap();
            let want = cx.parse(output, &o).unwrap();
            let mut census = RuleCensus::default();
            let out = on
                .run(
                    &mut cx,
                    &[e],
                    Run {
                        observer: Some(&mut census),
                        ..Run::default()
                    },
                )
                .unwrap();
            assert_eq!(out.stats.rejected, 0, "{}", rule.name);
            assert_eq!(out.roots[0].expr, want, "{}: {input}", rule.name);
            assert!(
                census.rules.get(&rule.name).is_some_and(|c| c.applied > 0),
                "{}: {input}",
                rule.name
            );
            // Off: the rule does not apply.
            let mut census = RuleCensus::default();
            off.run(
                &mut cx,
                &[e],
                Run {
                    observer: Some(&mut census),
                    ..Run::default()
                },
            )
            .unwrap();
            assert!(census.rules.get(&rule.name).is_none_or(|c| c.applied == 0));
        }
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
            for (ri, rule) in engine.inner.rules.iter().enumerate() {
                if !rule.decreasing {
                    continue;
                }
                if crate::rules::matcher::match_rule(&cx, rule, id).is_some() {
                    matched += 1;
                    assert!(
                        cands.contains(&(ri as u32)),
                        "{} matches `{}` but was filtered out",
                        rule.name,
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

/// A run its budget stops keeps the work of the phase it stopped in: the nodes that phase
/// finished (and rewrites it had not finished) replace theirs, and their users are rebuilt.
/// Every budget gives a result equal to the input and the same result on every run; here a
/// larger budget never leaves more than a smaller one, and between nothing and the whole
/// strategy some budgets leave a part done.
#[test]
fn budgets_keep_the_stopped_phase_work() {
    let engine = Engine::standard();
    let mut rng = Rng(11);
    let src = (0..40)
        .map(|i| format!("((a{i} ^ b{i}) + ((a{i} & b{i}) << 1) == a{i} + b{i})"))
        .collect::<Vec<_>>()
        .join(" & ");
    let o = ParseOptions::width(Width::W16);
    let size = |cx: &mut Context, e: Expr| match cx.dag_size(&[e], u32::MAX).unwrap() {
        crate::Bounded::Exact(n) => n,
        b => panic!("{b:?}"),
    };
    let mut cx = Context::new();
    let input = cx.parse(&src, &o).unwrap();
    let full = size(&mut cx, input);
    let (mut last, mut partial) = (full, 0);
    for visits in (0..=1200).step_by(40) {
        let budget = Budget::UNLIMITED.with_node_visits(visits);
        let mut sizes = Vec::new();
        for _ in 0..2 {
            let mut cx = Context::new();
            let e = cx.parse(&src, &o).unwrap();
            let out = engine
                .run(&mut cx, &[e], Run::default().with_per_call(budget))
                .unwrap();
            let r = out.roots[0];
            assert!(equivalent(&mut cx, e, r.expr, &mut rng), "{visits} visits");
            sizes.push((size(&mut cx, r.expr), cx.display(r.expr).to_string()));
        }
        assert_eq!(sizes[0], sizes[1], "{visits} visits: not reproducible");
        let n = sizes[0].0;
        assert!(n <= last, "{visits} visits: {n} nodes after {last}");
        if n < full && n > 1 {
            partial += 1;
        }
        last = n;
    }
    assert_eq!(last, 1, "the whole strategy folds the conjunction");
    assert!(partial >= 3, "{partial} budgets left a part done");
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
fn builtin_engines_share_rules_and_nets() {
    let nets = |e: &Engine| -> Vec<Arc<DispatchNet>> {
        e.inner
            .phases
            .iter()
            .filter_map(|p| match p {
                PhaseImpl::Local(n, _) => Some(n.clone()),
                _ => None,
            })
            .collect()
    };
    let build = || {
        Engine::builder()
            .builtin()
            .strategy(Strategy::standard())
            .build()
            .unwrap()
    };
    let (a, b) = (build(), build());
    assert!(Arc::ptr_eq(&a.inner.rules, &b.inner.rules));
    assert!(Arc::ptr_eq(&a.inner.proven, &b.inner.proven));
    assert!(a.inner.proven.iter().all(|&p| p));
    let (na, nb) = (nets(&a), nets(&b));
    assert_eq!(na.len(), 2);
    assert!(na.iter().chain(&nb).all(|n| Arc::ptr_eq(n, &na[0])));
    // A strategy over fewer groups gets a net of its own.
    let bits = Engine::builder()
        .builtin()
        .strategy(Strategy::new(
            "bits",
            vec![Phase::Local {
                groups: vec!["core.bitwise".into()],
            }],
        ))
        .build()
        .unwrap();
    assert!(!Arc::ptr_eq(&nets(&bits)[0], &na[0]));
    assert_eq!(a.inner.id, build().inner.id);
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
    let ledger = Ledger::parse(crate::rules::corpus::CORE_LEDGER).unwrap();
    assert!(Engine::builder().program(q, &ledger).build().is_err());
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

/// A constant mask, or or xor spelled below a shift or above it reaches one form, so equal
/// spellings compare equal and the rules written for one fire on the other.
/// The shift canonicalization moves a mask below a shift only when the shift has no other
/// user (`one_use`): with another user the shift stays, and the move would add a node.
#[test]
fn shared_shifts_keep_their_mask() {
    let engine = Engine::standard();
    let o = ParseOptions::width(Width::W32);
    for (input, want) in [
        ("(x << 3) & 0x7f8", "(x & 255) << 3"),
        ("((x + x) & 0x1fe) * (x + x)", "(x + x) * ((x + x) & 510)"),
        (
            "((x << 3) & 0x7f8) * (x << 3)",
            "(x << 3) * ((x << 3) & 0x7f8)",
        ),
    ] {
        let mut cx = Context::new();
        let e = cx.parse(input, &o).unwrap();
        let got = engine.simplify(&mut cx, e).unwrap().expr;
        let want = cx.parse(want, &o).unwrap();
        assert_eq!(got, want, "{input} gave {}", cx.display(got));
    }
    // Ignoring sharing, `one_use` always holds.
    let alone = Engine::builder()
        .builtin()
        .strategy(Strategy::standard().with_sharing(Sharing::Ignored))
        .build()
        .unwrap();
    let mut cx = Context::new();
    let e = cx.parse("((x << 3) & 0x7f8) * (x << 3)", &o).unwrap();
    let got = alone.simplify(&mut cx, e).unwrap().expr;
    assert!(
        cx.display(got).to_string().contains("x & 255"),
        "{}",
        cx.display(got)
    );
}

#[test]
fn masks_across_shifts_have_one_form() {
    let engine = Engine::standard();
    let o = ParseOptions::width(Width::W32);
    for (input, want) in [
        ("(x & 0xff) << 1 == (x << 1) & 0x1fe", "1:1"),
        ("(x & 0xf0) << 4 == (x << 4) & 0xf00", "1:1"),
        ("(x & 0xff) + (x & 0xff) == (x + x) & 0x1fe", "1:1"),
        ("(x ^ 0xff) + ((x & 0xff) << 1)", "x + 255"),
        ("(x ^ 0xff) + ((x << 1) & 0x1fe)", "x + 255"),
        ("(x + 0xff) - ((x & 0xff) << 1)", "x ^ 255"),
        ("(x + 0xff) - ((x << 1) & 0x1fe)", "x ^ 255"),
        ("(x & 0x7fffffff) << 2", "x << 2"),
        ("(x << 1) & 0xfffffffe", "x + x"),
        ("(x & 0x7fffffff) << 1", "x + x"),
        ("((x << 1) & 0x1fe) >>u 1", "x & 255"),
        ("(x | 3) << 2 == (x << 2) | 12", "1:1"),
        ("(x ^ 3) << 2 == (x << 2) ^ 12", "1:1"),
        ("((x << 1) | 2) - (x + 1)", "x ^ 1"),
        ("((x | 1) << 1) - (x + 1)", "x ^ 1"),
    ] {
        let mut cx = Context::new();
        let e = cx.parse(input, &o).unwrap();
        let got = engine.simplify(&mut cx, e).unwrap().expr;
        let want = cx.parse(want, &o).unwrap();
        assert_eq!(got, want, "{input} gave {}", cx.display(got));
    }
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
    // at the same node. (The linear pass then writes `2·y + 1` as `y − ~y`.)
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
    let applied = |name: &str| census.rules.get(name).map_or(0, |c| c.applied);
    assert_eq!(applied("core.arith::neg_not"), 1, "{census:?}");
    assert_eq!(applied("core.arith::add_disjoint"), 1, "{census:?}");
    assert_eq!(out.stats.rewrites, 3, "{census:?}");
    assert_eq!(cx.parse("y - ~y", &o).unwrap(), out.roots[0].expr);
}

#[test]
fn lifted_flag_conditions_become_comparisons() {
    // The conditions a lifter computes from the flags of `cmp a, b` (x86) or `subs` (AArch64),
    // in the spellings lifters use: sign tests, sign-bit extracts, shifted-down sign words and
    // the builder's own `ssub_overflow`. `$` is the sign bit's index.
    let cases = [
        ("(a - b <s 0) != ssub_overflow(a, b)", "a <s b"),
        ("(a - b <s 0) ^ ssub_overflow(a, b)", "a <s b"),
        ("(a - b <s 0) == ssub_overflow(a, b)", "b <=s a"),
        ("~((a - b <s 0) ^ ssub_overflow(a, b))", "b <=s a"),
        (
            "(a - b == 0) | ((a - b <s 0) != ssub_overflow(a, b))",
            "a <=s b",
        ),
        (
            "(a - b != 0) & ((a - b <s 0) == ssub_overflow(a, b))",
            "b <s a",
        ),
        (
            "(a - b <s 0) != (((a <s 0) != (b <s 0)) & ((a - b <s 0) != (a <s 0)))",
            "a <s b",
        ),
        (
            "extract<$, 1>(a - b) != extract<$, 1>((a ^ b) & (a ^ (a - b)))",
            "a <s b",
        ),
        (
            "extract<$, 1>(a - b) == extract<$, 1>((a ^ b) & (a ^ (a - b)))",
            "b <=s a",
        ),
        (
            "((a - b) >>u $) ^ (((a ^ b) & (a ^ (a - b))) >>u $) == 1",
            "a <s b",
        ),
        ("(a - 5 <s 0) != ssub_overflow(a, 5)", "a <s 5"),
        ("(5 - b <s 0) == ssub_overflow(5, b)", "b <=s 5"),
        ("(a - b != 0) & ~(a <u b)", "b <u a"),
    ];
    let engine = strict();
    for w in [Width::W8, Width::W32, Width::W64] {
        let o = ParseOptions::width(w);
        let sign = (w.bits() - 1).to_string();
        for (input, expected) in cases {
            let mut cx = Context::new();
            let e = cx.parse(&input.replace('$', &sign), &o).unwrap();
            let out = engine.simplify(&mut cx, e).unwrap();
            let want = cx.parse(expected, &o).unwrap();
            assert_eq!(
                out.expr,
                want,
                "at {w:?}: {input} gave {}",
                cx.display(out.expr)
            );
        }
    }
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
            for (ri, rule) in engine.inner.rules.iter().enumerate() {
                if crate::rules::matcher::match_rule(&cx, rule, id).is_some() {
                    matched[ri] += 1;
                    assert!(
                        cands.contains(&(ri as u32)),
                        "{} matches `{}` but was filtered out",
                        rule.name,
                        cx.display(n)
                    );
                }
            }
        }
    }
    for (rule, m) in engine.inner.rules.iter().zip(&matched) {
        if rule.decreasing {
            assert!(*m > 0, "{} never matched", rule.name);
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
        fact_reliance(200, 30_000, 300);
    }

    /// [`fact_reliance_is_sound_where_only_the_relied_on_constraints_hold`] over three times
    /// the seeds.
    #[test]
    #[ignore = "heavy: run with --release -- --ignored"]
    fn fact_reliance_is_sound_where_only_the_relied_on_constraints_hold_heavy() {
        fact_reliance(600, 100_000, 1_000);
    }

    /// `seeds` random assumption sets and probes; at least `min_checked` facts and
    /// `min_partial` partial reliances must have been checked.
    fn fact_reliance(seeds: u64, min_checked: u64, min_partial: u64) {
        let mut checked = 0u64;
        let mut partial = 0u64;
        for seed in 0..seeds {
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
            checked > min_checked && partial > min_partial,
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

/// A function as a compiler holds it: a few random expressions of one width, then values each
/// combining two earlier ones (so later values share earlier ones), every value a root.
fn function(g: &mut Gen, cx: &mut Context, w: u16) -> Vec<Expr> {
    let ops = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Shl,
        BinOp::LShr,
    ];
    let mut vals: Vec<Expr> = (0..3).map(|_| g.expr(cx, w, 2).0).collect();
    for _ in 0..10 {
        let a = vals[vals.len() - 1 - g.rng.below(vals.len().min(4) as u64) as usize];
        let b = vals[g.rng.below(vals.len() as u64) as usize];
        let op = ops[g.rng.below(ops.len() as u64) as usize];
        vals.push(cx.bin(op, a, b).unwrap());
    }
    vals
}

/// The compiler strategy, and passes over a small region: results equal their inputs, pass
/// every postcondition, and are final (a second call over the same roots does no work).
#[test]
fn ignoring_sharing_is_sound_and_every_result_final() {
    let engines = [
        Strategy::compile(),
        Strategy::standard()
            .with_sharing(Sharing::Ignored)
            .with_max_region(4),
        Strategy::standard().with_max_region(4),
    ]
    .map(|s| {
        Engine::builder()
            .builtin()
            .strategy(s)
            .verify(Verify::strict())
            .build()
            .unwrap()
    });
    let mut rng = Rng(11);
    for (k, engine) in engines.iter().enumerate() {
        let mut g = generator(0xc0_0001 + k as u64);
        let mut rewrites = 0;
        for _ in 0..120 {
            let mut cx = Context::new();
            let w = 1 + g.rng.below(6) as u16;
            let roots = function(&mut g, &mut cx, w);
            let out = engine.run(&mut cx, &roots, Run::default()).unwrap();
            assert_eq!(
                out.stats.rejected, 0,
                "a postcondition rejected an application"
            );
            assert_eq!(out.stats.quarantined, 0);
            for (&e, r) in roots.iter().zip(&out.roots) {
                assert_eq!(r.end, End::Completed);
                assert!(
                    equivalent(&mut cx, e, r.expr, &mut rng),
                    "{} vs {}",
                    cx.display(e),
                    cx.display(r.expr)
                );
            }
            rewrites += out.stats.rewrites;
            if engine.strategy().sharing == Sharing::Ignored {
                let again = engine.run(&mut cx, &roots, Run::default()).unwrap();
                assert_eq!(again.roots, out.roots);
                assert_eq!(again.stats.node_visits, 0);
                assert_eq!(again.stats.rewrites, 0);
            }
        }
        assert!(rewrites > 50, "few rewrites ({rewrites})");
    }
}

/// Ignoring sharing, a value's result does not depend on which other values the call has.
#[test]
fn ignoring_sharing_makes_results_independent_of_the_roots() {
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::compile())
        .build()
        .unwrap();
    let mut g1 = generator(0xc0_0002);
    let mut g2 = generator(0xc0_0002);
    for _ in 0..120 {
        let (mut c1, mut c2) = (Context::new(), Context::new());
        let w = 1 + g1.rng.below(6) as u16;
        g2.rng.below(6);
        let all = function(&mut g1, &mut c1, w);
        let each = function(&mut g2, &mut c2, w);
        let together = engine.run(&mut c1, &all, Run::default()).unwrap();
        for (i, &e) in each.iter().enumerate() {
            // Alone, in a context of its own (no memo from the other values either).
            let mut c3 = Context::new();
            let e3 = c3.import(&c2, &[e]).unwrap()[0];
            let alone = engine.simplify(&mut c3, e3).unwrap();
            assert_eq!(
                c1.display(together.roots[i].expr).to_string(),
                c3.display(alone.expr).to_string(),
                "value {i} of {}",
                c1.display(all[i])
            );
        }
    }
}

/// The default commit policy does not enter the engine's id: engines that keep it keep their
/// memos; another policy does.
#[test]
fn the_default_commit_policy_keeps_engine_ids() {
    let id = |s: Strategy| {
        Engine::builder()
            .builtin()
            .strategy(s)
            .build()
            .unwrap()
            .inner
            .id
    };
    let standard = id(Strategy::standard());
    assert_eq!(
        standard,
        id(Strategy::standard()
            .with_sharing(Sharing::Roots)
            .with_max_region(pass::REGION_CAP))
    );
    assert_ne!(
        standard,
        id(Strategy::standard().with_sharing(Sharing::Ignored))
    );
    assert_ne!(standard, id(Strategy::standard().with_max_region(64)));
}

/// Whether `a` and `b` agree on every assignment of their symbols that agrees with the symbols'
/// declared known bits (every such assignment up to 14 bits, else 2048 random ones fitted to
/// the declarations).
fn equivalent_declared(cx: &mut Context, a: Expr, b: Expr, rng: &mut Rng) -> bool {
    let syms = cx.symbols_in(&[a, b]).unwrap();
    let keys: Vec<(SymbolKey, Width, Option<KnownBits>)> = syms
        .iter()
        .map(|&s| {
            let key = cx.symbol_key(s).unwrap().clone();
            let e = cx.find_symbol(&key).unwrap();
            (
                key,
                cx.symbol_width(s).unwrap(),
                cx.declared_known(e).unwrap(),
            )
        })
        .collect();
    let bits: u32 = keys.iter().map(|(_, w, _)| u32::from(w.bits())).sum();
    let exhaustive = bits <= 14;
    let cases: u64 = if exhaustive { 1 << bits } else { 2048 };
    for case in 0..cases {
        let mut rest = case;
        let mut agrees = true;
        let vals: Vec<(SymbolKey, BitVec)> = keys
            .iter()
            .map(|(k, w, known)| {
                let v = if exhaustive {
                    let v = rest & ((1u64 << w.bits()) - 1);
                    rest >>= w.bits();
                    BitVec::wrapping_from_u64(*w, v)
                } else {
                    let limbs: Vec<u64> = (0..8).map(|_| rng.next()).collect();
                    let v = BitVec::wrapping_from_limbs(*w, &limbs);
                    known.map_or(v, |d| d.fit(&v))
                };
                if let Some(d) = known {
                    agrees &= d.fit(&v) == v;
                }
                (k.clone(), v)
            })
            .collect();
        if !agrees {
            continue;
        }
        let env = FnEnv(|k: &SymbolKey, _| vals.iter().find(|(kk, _)| kk == k).map(|(_, v)| *v));
        let r = cx.eval(&[a, b], &env).unwrap();
        if r[0] != r[1] {
            return false;
        }
    }
    true
}

/// Random known bits of width `w`: some bits known, each zero or one.
fn random_known(rng: &mut Rng, w: Width) -> KnownBits {
    let limbs = |rng: &mut Rng| -> Vec<u64> { (0..8).map(|_| rng.next()).collect() };
    let known = BitVec::wrapping_from_limbs(w, &limbs(rng));
    let ones = BitVec::wrapping_from_limbs(w, &limbs(rng));
    let one = crate::facts::known::bv_and(&known, &ones);
    let zero = crate::facts::known::bv_and(&known, &crate::facts::known::bv_not(&ones));
    KnownBits::new(zero, one).unwrap()
}

/// Declared known bits of symbols: every result agrees with its input wherever the symbols
/// agree with their declarations, every rewrite passes strict verification (whose points
/// agree with the declarations too), and the declarations let the simplifier do more.
#[test]
fn declared_known_bits_are_used_soundly() {
    let mut rng = Rng(0xdec1_a4ed);
    for strategy in [Strategy::standard(), Strategy::compile()] {
        let engine = Engine::builder()
            .builtin()
            .strategy(strategy)
            .verify(Verify::strict())
            .build()
            .unwrap();
        let mut g = generator(0xdec1_0001);
        let (mut rewrites, mut more) = (0u64, 0u32);
        for _ in 0..200 {
            let mut cx = Context::new();
            let w = 1 + g.rng.below(6) as u16;
            let roots = function(&mut g, &mut cx, w);
            // The same values without declarations, in a context of their own.
            let mut plain = Context::new();
            let plain_roots = plain.import(&cx, &roots).unwrap();
            let plain_out = engine
                .run(&mut plain, &plain_roots, Run::default())
                .unwrap();
            for s in cx.symbols_in(&roots).unwrap() {
                let key = cx.symbol_key(s).unwrap().clone();
                let e = cx.find_symbol(&key).unwrap();
                let k = random_known(&mut rng, cx.symbol_width(s).unwrap());
                cx.declare_known(e, k).unwrap();
            }
            let out = engine.run(&mut cx, &roots, Run::default()).unwrap();
            assert_eq!(
                out.stats.rejected, 0,
                "a postcondition rejected an application"
            );
            assert_eq!(out.stats.quarantined, 0);
            for (k, (&e, r)) in roots.iter().zip(&out.roots).enumerate() {
                assert!(
                    equivalent_declared(&mut cx, e, r.expr, &mut rng),
                    "{} vs {}",
                    cx.display(e),
                    cx.display(r.expr)
                );
                let size = |cx: &mut Context, e: Expr| match cx.dag_size(&[e], u32::MAX) {
                    Ok(crate::Bounded::Exact(n)) => n,
                    _ => u32::MAX,
                };
                let (with, without) = (
                    size(&mut cx, r.expr),
                    size(&mut plain, plain_out.roots[k].expr),
                );
                more += u32::from(with < without);
            }
            rewrites += out.stats.rewrites;
        }
        assert!(rewrites > 50, "few rewrites ({rewrites})");
        assert!(
            more > 20,
            "declarations rarely helped ({more} smaller results)"
        );
    }
}

/// A declaration made after a run drops the memo that run filled: the next run uses it.
#[test]
fn declaring_known_bits_drops_what_rested_on_their_absence() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let e = cx.parse("(x & 15) + ((x >>u 4) * y)", &o).unwrap();
    let before = engine.simplify(&mut cx, e).unwrap();
    assert_eq!(
        cx.display(before.expr).to_string(),
        "(x >>u 4) * y + (x & 15)"
    );
    let x = cx.find_symbol(&SymbolKey::from("x")).unwrap();
    let high = BitVec::from_u64(Width::W8, 0xf0).unwrap();
    cx.declare_known(x, KnownBits::new(high, BitVec::zero(Width::W8)).unwrap())
        .unwrap();
    let after = engine.simplify(&mut cx, e).unwrap();
    assert_eq!(cx.display(after.expr).to_string(), "x");
    // Withdrawn: back to the first result.
    cx.declare_known(x, KnownBits::unknown(Width::W8)).unwrap();
    assert_eq!(cx.declared_known(x).unwrap(), None);
    let again = engine.simplify(&mut cx, e).unwrap();
    assert_eq!(again.expr, before.expr);
}

/// `run_each` copies declarations into each root's context and back.
#[test]
fn run_each_keeps_declared_known_bits() {
    let engine = Engine::standard();
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let roots = [
        cx.parse("x & 15", &o).unwrap(),
        cx.parse("(x >>u 4) + y", &o).unwrap(),
    ];
    let x = cx.find_symbol(&SymbolKey::from("x")).unwrap();
    let high = BitVec::from_u64(Width::W8, 0xf0).unwrap();
    cx.declare_known(x, KnownBits::new(high, BitVec::zero(Width::W8)).unwrap())
        .unwrap();
    let each = engine
        .run_each(&mut cx, &roots, Each::default().with_threads(2))
        .unwrap();
    let shown: Vec<String> = each
        .roots
        .iter()
        .map(|r| cx.display(r.expr).to_string())
        .collect();
    assert_eq!(shown, ["x", "y"]);
}

mod host_rewrites {
    use super::*;
    use crate::{BinOp, View};
    use std::sync::Arc;

    /// `x + 1 => x`: wrong.
    struct DropIncrement;
    impl Rewrite for DropIncrement {
        fn name(&self) -> &str {
            "t.drop_increment"
        }
        fn group(&self) -> &str {
            "t"
        }
        fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
            let View::Bin(BinOp::Add, x, c) = site.view(e)? else {
                return None;
            };
            (site.as_u64(c)? == 1).then_some(x)
        }
    }

    /// `x << k => x * 2^k`: right, but larger in the termination order.
    struct ShlToMul;
    impl Rewrite for ShlToMul {
        fn name(&self) -> &str {
            "t.shl_to_mul"
        }
        fn group(&self) -> &str {
            "t"
        }
        fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
            let View::Bin(BinOp::Shl, x, k) = site.view(e)? else {
                return None;
            };
            let k = site.as_u64(k)?;
            let w = site.width(e)?;
            let m = site.constant_u64(w, 1u64.checked_shl(u32::try_from(k).ok()?)?)?;
            site.bin(BinOp::Mul, x, m)
        }
    }

    /// `x & c => x` when the facts show `x` has no bit outside `c`.
    struct MaskByFacts;
    impl Rewrite for MaskByFacts {
        fn name(&self) -> &str {
            "t.mask_by_facts"
        }
        fn group(&self) -> &str {
            "t"
        }
        fn revision(&self) -> u32 {
            2
        }
        fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
            let View::Bin(BinOp::And, x, c) = site.view(e)? else {
                return None;
            };
            let c = site.as_const(c)?;
            let maybe = site.known(x)?.maybe_one();
            let outside = crate::facts::known::bv_and(&maybe, &crate::facts::known::bv_not(&c));
            outside.is_zero().then_some(x)
        }
    }

    fn engine(r: Arc<dyn Rewrite>, trusted: bool) -> Engine {
        let b = Engine::builder().strategy(Strategy::new("t", vec![]).with_rule_groups(&["t"]));
        let b = if trusted {
            b.trusted_rewrite(r)
        } else {
            b.rewrite(r).allow_unproven(true)
        };
        b.build().unwrap()
    }

    #[test]
    fn a_wrong_rewrite_is_caught_and_quarantined() {
        let eng = engine(Arc::new(DropIncrement), false);
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let roots = [
            cx.parse("x + 1", &o).unwrap(),
            cx.parse("(y + 1) * 3", &o).unwrap(),
        ];
        let out = eng.run(&mut cx, &roots, Run::default()).unwrap();
        assert_eq!(out.roots[0].expr, roots[0]);
        assert_eq!(out.roots[1].expr, roots[1]);
        assert!(out.stats.quarantined >= 1);
        assert!(out.stats.host.rejected >= 1);
        assert_eq!(out.stats.host.changed, 0);
    }

    #[test]
    fn a_rewrite_that_does_not_decrease_the_order_is_not_committed() {
        let eng = engine(Arc::new(ShlToMul), true);
        let mut cx = Context::new();
        let e = cx.parse("x << 3", &ParseOptions::width(Width::W8)).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(out.roots[0].expr, e);
        assert_eq!(out.stats.host.rejected_cost, 1);
        assert_eq!(out.stats.quarantined, 0);
    }

    #[test]
    fn linking_follows_the_proof_policy_and_the_groups() {
        let r: Arc<dyn Rewrite> = Arc::new(DropIncrement);
        let unproven = Engine::builder()
            .rewrite(r.clone())
            .strategy(Strategy::new("t", vec![]).with_rule_groups(&["t"]))
            .build();
        assert!(matches!(unproven, Err(BuildError::UnprovenRewrite { .. })));
        // A group no program or rewrite defines.
        let unknown = Engine::builder()
            .trusted_rewrite(r.clone())
            .strategy(Strategy::new("t", vec![]).with_rule_groups(&["nope"]))
            .build();
        assert!(matches!(unknown, Err(BuildError::UnknownGroup(_))));
        // A rewrite group named like a rule group.
        struct Clash;
        impl Rewrite for Clash {
            fn name(&self) -> &str {
                "clash"
            }
            fn group(&self) -> &str {
                "core.bitwise"
            }
            fn rewrite(&self, _: &mut Site<'_>, _: Expr) -> Option<Expr> {
                None
            }
        }
        let clash = Engine::builder()
            .builtin()
            .trusted_rewrite(Arc::new(Clash))
            .build();
        assert!(matches!(clash, Err(BuildError::DuplicateGroup(_))));
        // The default strategy runs every linked group, rewrites included.
        let default = Engine::builder()
            .trusted_rewrite(Arc::new(MaskByFacts))
            .build()
            .unwrap();
        let mut cx = Context::new();
        let e = cx
            .parse("(x & 15) & 255", &ParseOptions::width(Width::W8))
            .unwrap();
        let out = default.simplify(&mut cx, e).unwrap();
        assert_eq!(cx.display(out.expr).to_string(), "x & 15");
    }

    /// Facts through the site, under declared known bits: final results, memoized, and keyed by
    /// the rewrite's revision.
    #[test]
    fn rewrites_read_facts_and_their_results_are_final() {
        let eng = engine(Arc::new(MaskByFacts), false);
        let mut cx = Context::new();
        let w = Width::W16;
        let x = cx.symbol("x", w).unwrap();
        let high = BitVec::from_u64(w, 0xff00).unwrap();
        cx.declare_known(x, KnownBits::new(high, BitVec::zero(w)).unwrap())
            .unwrap();
        let e = cx.parse("(x & 0xff) + 1", &ParseOptions::width(w)).unwrap();
        let out = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(cx.display(out.roots[0].expr).to_string(), "x + 1");
        assert_eq!(out.roots[0].end, End::Completed);
        assert_eq!(out.stats.rejected, 0, "sampled verification agrees");
        let again = eng.run(&mut cx, &[e], Run::default()).unwrap();
        assert_eq!(again.stats.node_visits, 0);
        assert_eq!(again.roots[0].expr, out.roots[0].expr);
        // Another revision is another engine.
        struct Rev3;
        impl Rewrite for Rev3 {
            fn name(&self) -> &str {
                "t.mask_by_facts"
            }
            fn group(&self) -> &str {
                "t"
            }
            fn revision(&self) -> u32 {
                3
            }
            fn rewrite(&self, s: &mut Site<'_>, e: Expr) -> Option<Expr> {
                MaskByFacts.rewrite(s, e)
            }
        }
        assert_ne!(eng.inner.id, engine(Arc::new(Rev3), false).inner.id);
        assert_ne!(eng.inner.id, engine(Arc::new(MaskByFacts), true).inner.id);
    }

    /// A rewrite building past the call's node budget stops the call honestly.
    #[test]
    fn budgets_bound_what_a_rewrite_builds() {
        struct Builds;
        impl Rewrite for Builds {
            fn name(&self) -> &str {
                "t.builds"
            }
            fn group(&self) -> &str {
                "t"
            }
            fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
                let w = site.width(e)?;
                let mut acc = site.constant_u64(w, 0)?;
                for k in 1..100u64 {
                    let c = site.constant_u64(w, k)?;
                    acc = site.bin(BinOp::Xor, acc, c)?;
                }
                None
            }
        }
        let eng = engine(Arc::new(Builds), true);
        let mut cx = Context::new();
        let e = cx.parse("x + y", &ParseOptions::width(Width::W16)).unwrap();
        let out = eng
            .run(
                &mut cx,
                &[e],
                Run::default().with_per_call(Budget::default().with_new_nodes(10)),
            )
            .unwrap();
        assert_eq!(out.roots[0].end, End::BudgetTerminated(Exhausted::NewNodes));
        assert!(out.stats.new_nodes <= 10);
    }
}

// ----- structural events and traces ----------------------------------------------------

mod events {
    use super::*;

    /// An event, owned: its kind and the nodes and numbers it carries.
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Ev {
        Root(usize, Expr, bool),
        Stage(Stage, Expr, Expr),
        Begin(u8, usize, Expr),
        End(u8, usize, Expr, Budget, Option<Exhausted>),
        Candidate(String),
        Applied(String, Expr, Expr),
        Relied(Reliance),
        GuardFalse(String),
        GuardFailed(String, &'static str, [Option<Expr>; 2]),
        NotSmaller(String, Expr, Option<Expr>, u32, u32),
        Folded(Expr, Expr),
        Explain(String, Expr, Explanation),
        Other,
    }

    #[derive(Default)]
    struct Log(Vec<Ev>, Detail);

    impl Observer for Log {
        fn detail(&self) -> Detail {
            self.1
        }

        fn event(&mut self, e: Event<'_>) {
            let i = |e: Expr| e;
            self.0.push(match e {
                Event::Root { index, root, again } => Ev::Root(index, i(root), again),
                Event::Stage {
                    stage,
                    before,
                    after,
                } => Ev::Stage(stage, i(before), i(after)),
                Event::PhaseBegin { round, phase, root } => Ev::Begin(round, phase, i(root)),
                Event::PhaseEnd {
                    round,
                    phase,
                    root,
                    spent,
                    stopped,
                } => Ev::End(round, phase, i(root), spent, stopped),
                Event::Candidate { rule, .. } => Ev::Candidate(rule.name.clone()),
                Event::Applied { by, before, after } => {
                    let by = match by {
                        By::Rule(_) => "local".to_string(),
                        other => other.name().to_string(),
                    };
                    Ev::Applied(by, i(before), i(after))
                }
                Event::Relied { on } => Ev::Relied(on),
                Event::GuardFalse { rule } => Ev::GuardFalse(rule.name.clone()),
                Event::GuardFailed { rule, pred, args } => {
                    Ev::GuardFailed(rule.name.clone(), pred, args)
                }
                Event::NotSmaller {
                    by,
                    node,
                    candidate,
                    added,
                    freed,
                    ..
                } => Ev::NotSmaller(by.name().to_string(), node, candidate, added, freed),
                Event::Folded { node, after } => Ev::Folded(node, after),
                Event::Explain { by, node, why } => {
                    Ev::Explain(by.name().to_string(), node, why.clone())
                }
                _ => Ev::Other,
            });
        }
    }

    fn logged(
        engine: &Engine,
        cx: &mut Context,
        roots: &[Expr],
        assumptions: Option<&Assumptions>,
    ) -> (Log, Outcome) {
        logged_with(engine, cx, roots, assumptions, Detail::Events)
    }

    fn logged_with(
        engine: &Engine,
        cx: &mut Context,
        roots: &[Expr],
        assumptions: Option<&Assumptions>,
        detail: Detail,
    ) -> (Log, Outcome) {
        let mut log = Log(Vec::new(), detail);
        let mut run = Run::default().with_observer(&mut log);
        if let Some(a) = assumptions {
            run = run.with_assumptions(a);
        }
        let out = engine.run(cx, roots, run).unwrap();
        (log, out)
    }

    /// Checks the structure of a run's events over one root: the root never changes without an
    /// event saying so (from `Root` through each `Stage` and phase to the result), phases come in
    /// order between their `PhaseBegin` and `PhaseEnd`, and every rewrite happens inside a phase
    /// of its own kind. Returns the number of phases run.
    fn check_structure(engine: &Engine, log: &Log, result: Expr) -> usize {
        let phases = &engine.strategy().phases;
        let mut cur: Option<Expr> = None;
        let mut open: Option<(u8, usize)> = None;
        let mut last: Option<(u8, usize)> = None;
        let mut ran = 0;
        for (k, e) in log.0.iter().enumerate() {
            match e {
                Ev::Root(0, root, false) => {
                    assert_eq!(k, 0, "a root is announced first");
                    cur = Some(*root);
                }
                Ev::Root(..) => panic!("one root, announced once: {e:?}"),
                Ev::Stage(_, before, after) => {
                    assert!(open.is_none(), "a stage runs outside the phases");
                    assert_eq!(Some(*before), cur, "a stage starts from the current root");
                    assert_ne!(
                        before, after,
                        "a stage is reported only when it changes the root"
                    );
                    cur = Some(*after);
                }
                Ev::Begin(round, phase, root) => {
                    assert!(open.is_none(), "phases do not nest");
                    assert_eq!(
                        Some(*root),
                        cur,
                        "phase {phase} starts from the current root"
                    );
                    let expected = match last {
                        None => (0, 0),
                        Some((r, p)) if p + 1 == phases.len() => (r + 1, 0),
                        Some((r, p)) => (r, p + 1),
                    };
                    assert_eq!((*round, *phase), expected, "phases run in order");
                    open = Some((*round, *phase));
                }
                Ev::End(round, phase, root, _, _) => {
                    assert_eq!(open, Some((*round, *phase)), "a phase ends where it began");
                    open = None;
                    last = Some((*round, *phase));
                    cur = Some(*root);
                    ran += 1;
                }
                Ev::Applied(by, ..) => {
                    let (_, phase) = open.expect("a rewrite happens inside a phase");
                    assert_eq!(by, phases[phase].name(), "a rewrite is made by its phase");
                }
                Ev::Candidate(_) => {
                    let (_, phase) = open.expect("a rule is tried inside a phase");
                    assert_eq!(phases[phase].name(), "local");
                }
                Ev::Relied(_) => assert!(
                    matches!(log.0.get(k.wrapping_sub(1)), Some(Ev::Applied(..))),
                    "a reliance follows its rewrite"
                ),
                Ev::GuardFalse(_) | Ev::Folded(..) => {
                    assert!(open.is_some(), "{e:?} happens inside a phase");
                }
                Ev::GuardFailed(rule, ..) => assert!(
                    matches!(log.0.get(k.wrapping_sub(1)), Some(Ev::GuardFalse(r)) if r == rule),
                    "a guard's detail follows its GuardFalse"
                ),
                Ev::NotSmaller(by, ..) => {
                    let (_, phase) = open.expect("a pass drops a candidate inside a phase");
                    assert_eq!(by, phases[phase].name(), "a pass's own phase drops it");
                }
                Ev::Explain(by, node, _) => {
                    // After the rewrite it explains, and its reliance if any.
                    let prev = log.0[..k]
                        .iter()
                        .rev()
                        .find(|e| !matches!(e, Ev::Relied(_)));
                    assert!(
                        matches!(prev, Some(Ev::Applied(b, before, _)) if b == by && before == node),
                        "an explanation follows its own rewrite: {prev:?}"
                    );
                }
                Ev::Other => {}
            }
        }
        assert!(open.is_none(), "every phase ends");
        assert_eq!(cur, Some(result), "the last root reported is the result");
        ran
    }

    fn deobfuscator() -> Engine {
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap()
    }

    #[cfg(feature = "mba")]
    fn with_noise_forms() -> Engine {
        let cfg = crate::mba::MbaConfig::default()
            .with_noise_forms(true)
            .with_known_atoms(true);
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate().with_mba(cfg))
            .build()
            .unwrap()
    }

    const INPUTS: &[(&str, u16)] = &[
        (
            "(((x ^ y) + 2*(x & y)) * 3 + ((x | y) - (x & y))) ^ (~z & z)",
            32,
        ),
        ("((x ^ 0x5a) + 3 - 3) ^ 0x5a", 64),
        ("trunc<8>(zext<32>(b:8) + 256)", 32),
        ("umulhi(x, 0xcccccccccccccccd) >>u 3", 64),
        ("(x <u 10) & (3 <u x)", 32),
        ("((a - b) >>u 31) ^ (((a ^ b) & (a ^ (a - b))) >>u 31)", 32),
        (
            "let m = (x ^ 0xd3220fb78e33751f) * 0xd3220fb78e33751f; \
          (m ^ ((m >>u 32) >>u (m >>u 60))) * 0xd3220fb78e33751f == 0",
            64,
        ),
    ];

    #[test]
    fn the_root_never_changes_without_an_event() {
        #[cfg_attr(not(feature = "mba"), allow(unused_mut))]
        let mut engines = vec![Engine::standard(), deobfuscator()];
        #[cfg(feature = "mba")]
        engines.push(with_noise_forms());
        for engine in &engines {
            for &(text, w) in INPUTS {
                let mut cx = Context::new();
                let e = cx
                    .parse(text, &ParseOptions::width(Width::new(w).unwrap()))
                    .unwrap();
                let (log, out) = logged(engine, &mut cx, &[e], None);
                let ran = check_structure(engine, &log, out.roots[0].expr);
                assert_eq!(
                    ran,
                    engine.strategy().phases.len() * out.stats.rounds as usize,
                    "{text}: every phase of every round is reported"
                );
            }
        }
    }

    #[test]
    fn the_phases_spend_the_run() {
        // Without the MBA service's stages, all of a run's work is done inside its phases.
        let engine = Engine::standard();
        let mut cx = Context::new();
        let e = big(&mut cx);
        let (log, out) = logged(&engine, &mut cx, &[e], None);
        let mut total = Budget::ZERO;
        for ev in &log.0 {
            if let Ev::End(.., spent, None) = ev {
                total = total.saturating_add(spent);
            }
        }
        let s = &out.stats;
        assert_eq!(total.node_visits, s.node_visits);
        assert_eq!(total.candidates, s.candidates);
        assert_eq!(total.match_steps, s.match_steps);
        assert_eq!(total.rewrites, s.rewrites);
        assert_eq!(total.new_nodes, s.new_nodes);
        assert_eq!(total.fact_work, s.fact_work);
        assert_eq!(total.pass_work, s.pass_work);
        assert!(s.rewrites > 0);
    }

    #[test]
    fn a_budget_stop_ends_the_phase_it_stopped() {
        let engine = Engine::standard();
        let mut cx = Context::new();
        let e = big(&mut cx);
        let mut log = Log::default();
        let out = engine
            .run(
                &mut cx,
                &[e],
                Run::default()
                    .with_observer(&mut log)
                    .with_per_call(Budget::default().with_node_visits(40)),
            )
            .unwrap();
        let End::BudgetTerminated(why) = out.roots[0].end else {
            panic!("the budget stops the run: {:?}", out.roots[0].end);
        };
        match log.0.last() {
            Some(Ev::End(_, _, root, _, stopped)) => {
                assert_eq!(*stopped, Some(why));
                assert_eq!(
                    *root, out.roots[0].expr,
                    "the stopped phase leaves the result"
                );
            }
            other => panic!("the run ends with the stopped phase: {other:?}"),
        }
    }

    #[test]
    fn each_distinct_root_is_announced_once() {
        let engine = Engine::standard();
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let a = cx.parse("(x & y) + (x | y)", &o).unwrap();
        let b = cx.parse("x ^ x ^ y", &o).unwrap();
        let (log, _) = logged(&engine, &mut cx, &[a, b, a], None);
        let roots: Vec<_> = log.0.iter().filter(|e| matches!(e, Ev::Root(..))).collect();
        assert_eq!(roots, [&Ev::Root(0, a, false), &Ev::Root(1, b, false)]);
    }

    #[test]
    fn a_rewrite_under_assumptions_says_what_it_relied_on() {
        let engine = Engine::standard();
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let mut a = Assumptions::new();
        for p in ["rsp & 15 == 0", "idx <u n"] {
            let p = cx.parse(p, &o).unwrap();
            a.assume_true(&mut cx, p).unwrap();
        }
        let e = cx
            .parse("((rsp + 32) & 15) + zext<64>(idx <=u n)", &o)
            .unwrap();
        let (log, out) = logged(&engine, &mut cx, &[e], Some(&a));
        let mut all = Reliance::NONE;
        let mut each = 0;
        for (k, ev) in log.0.iter().enumerate() {
            if let Ev::Relied(on) = ev {
                assert!(matches!(log.0[k - 1], Ev::Applied(..)));
                assert!(!on.is_none());
                all = all.union(*on);
                each += 1;
            }
        }
        assert_eq!(each, 2, "both folds rely on a constraint");
        assert!(!out.roots[0].relies_on.is_none());
        assert_eq!(all, out.roots[0].relies_on);
        check_structure(&engine, &log, out.roots[0].expr);
    }

    #[cfg(feature = "mba")]
    #[test]
    fn a_stage_that_rewrites_the_root_is_reported() {
        let engine = with_noise_forms();
        let text = "let %0 = trunc<8>(q) == 0; \
             let %1 = select(%0, 0xe6229ed78bba3a02:64, 0x6917e97be2bd3a02); \
             let %2 = ~x; let %3 = %2 & 0xfffffffebff828d3; \
             let %4 = select(%0, 0x8ceeb0943a22e2ff:64, 0xcb740b420ea162ff); \
             let %5 = ~%3 * %4; let %6 = ~(%2 & 0x14007d72c) * %1; let %7 = %3 * %4; \
             let %8 = ~(x & 0xfffffffebff828d3) * %4; let %9 = %5 * 0xf03a49e91da5aae9; \
             ~(x & 0x14007d72c) * %1 * 0xf03a49e91da5aae9 \
             + select(%0, 0x3196701ba3cc70df:64, 0xb33d0377cd1af0df) \
             + %9 + %6 * 0xf03a49e91da5aae9 + %9 + %7 * 0xf03a49e91da5aae9 \
             + %8 * 0xf03a49e91da5aae9";
        let mut cx = Context::new();
        let e = cx.parse(text, &ParseOptions::width(Width::W64)).unwrap();
        let (log, out) = logged(&engine, &mut cx, &[e], None);
        // (After the root, and the parts the sweep found: see `Event::Part`.)
        let first = (log.0.iter()).find(|ev| !matches!(ev, Ev::Root(..) | Ev::Other));
        assert!(
            matches!(first, Some(Ev::Stage(Stage::Sweep, before, _)) if *before == e),
            "the sweep rewrites the input before the first phase: {first:?}"
        );
        assert!(
            matches!(log.0.get(1), Some(Ev::Other)),
            "its parts come first"
        );
        check_structure(&engine, &log, out.roots[0].expr);
    }

    /// The numbers after `"key":` on a line.
    fn numbers(line: &str, key: &str) -> Vec<u64> {
        let pat = format!("\"{key}\":");
        let mut out = Vec::new();
        let mut rest = line;
        while let Some(at) = rest.find(&pat) {
            rest = &rest[at + pat.len()..];
            let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
            if let Ok(n) = digits.parse() {
                out.push(n);
            }
        }
        out
    }

    /// Whether a line is one JSON object whose brackets balance outside strings.
    fn balanced(line: &str) -> bool {
        let (mut depth, mut in_str, mut esc) = (0i32, false, false);
        for c in line.chars() {
            if in_str {
                match (esc, c) {
                    (true, _) => esc = false,
                    (false, '\\') => esc = true,
                    (false, '"') => in_str = false,
                    _ => {}
                }
                continue;
            }
            match c {
                '"' => in_str = true,
                '{' | '[' => depth += 1,
                '}' | ']' => depth -= 1,
                _ => {}
            }
            if depth < 0 {
                return false;
            }
        }
        depth == 0 && !in_str && line.starts_with('{') && line.ends_with('}')
    }

    fn traced(engine: &Engine, text: &str, w: u16) -> (String, Outcome) {
        let mut cx = Context::new();
        let e = cx
            .parse(text, &ParseOptions::width(Width::new(w).unwrap()))
            .unwrap();
        let mut trace = Trace::new(engine);
        let out = engine
            .run(&mut cx, &[e], Run::default().with_observer(&mut trace))
            .unwrap();
        let text = trace.to_jsonl(&mut cx, &[e], &out).unwrap();
        (text, out)
    }

    #[test]
    fn a_trace_names_every_node_before_it_is_used() {
        for engine in [Engine::standard(), deobfuscator()] {
            for &(input, w) in INPUTS {
                let (text, out) = traced(&engine, input, w);
                let lines: Vec<&str> = text.lines().collect();
                assert!(lines[0].starts_with("{\"trace\":\"bitwright\",\"format\":1,"));
                let mut nodes: IdMap<u32, ()> = IdMap::default();
                let (mut candidates, mut applied, mut results) = (0, 0, 0);
                for l in &lines {
                    assert!(balanced(l), "{l}");
                    if let Some(n) = numbers(l, "node")
                        .first()
                        .filter(|_| l.starts_with("{\"node\":"))
                    {
                        let args = l
                            .split("\"args\":[")
                            .nth(1)
                            .map_or("", |a| a.split(']').next().unwrap_or(""));
                        for a in args.split(',').filter(|a| !a.is_empty()) {
                            let a: u32 = a.parse().unwrap();
                            assert!(nodes.contains_key(&a), "operand {a} before node {n}");
                        }
                        nodes.insert(*n as u32, ());
                        continue;
                    }
                    for key in ["node", "before", "after", "root", "input", "expr"] {
                        for n in numbers(l, key) {
                            assert!(nodes.contains_key(&(n as u32)), "{key} {n} named in {l}");
                        }
                    }
                    candidates += usize::from(l.starts_with("{\"ev\":\"candidate\""));
                    applied += usize::from(l.starts_with("{\"ev\":\"applied\""));
                    results += usize::from(l.starts_with("{\"result\":"));
                }
                assert_eq!(candidates as u64, out.stats.candidates, "{input}");
                assert_eq!(applied as u64, out.stats.rewrites, "{input}");
                assert_eq!(results, 1);
                assert!(lines.last().unwrap().starts_with("{\"stats\":"));
            }
        }
    }

    #[test]
    fn a_trace_is_the_same_on_every_run() {
        let engine = deobfuscator();
        for &(input, w) in INPUTS {
            assert_eq!(
                traced(&engine, input, w).0,
                traced(&engine, input, w).0,
                "{input}"
            );
        }
    }

    fn all_engines() -> Vec<Engine> {
        #[cfg_attr(not(feature = "mba"), allow(unused_mut))]
        let mut engines = vec![Engine::standard(), deobfuscator()];
        #[cfg(feature = "mba")]
        {
            engines.push(
                Engine::builder()
                    .builtin()
                    .strategy(Strategy::deobfuscate().with_mba(crate::mba::MbaConfig::default()))
                    .build()
                    .unwrap(),
            );
            engines.push(with_noise_forms());
        }
        engines
    }

    fn parse(cx: &mut Context, text: &str, w: u16) -> Expr {
        cx.parse(text, &ParseOptions::width(Width::new(w).unwrap()))
            .unwrap()
    }

    #[test]
    fn explanations_follow_their_rewrites_and_only_when_asked() {
        for engine in &all_engines() {
            for &(text, w) in INPUTS {
                let mut cx = Context::new();
                let e = parse(&mut cx, text, w);
                let (log, out) = logged_with(engine, &mut cx, &[e], None, Detail::Explain);
                check_structure(engine, &log, out.roots[0].expr);
                let mut cx = Context::new();
                let e = parse(&mut cx, text, w);
                let (plain, _) = logged(engine, &mut cx, &[e], None);
                assert!(
                    !plain.0.iter().any(|e| matches!(e, Ev::Explain(..))),
                    "{text}: no explanation unless asked"
                );
            }
        }
    }

    #[test]
    fn dropped_candidates_match_the_counters() {
        for engine in &all_engines() {
            for &(text, w) in INPUTS {
                let mut cx = Context::new();
                let e = parse(&mut cx, text, w);
                let (log, out) = logged(engine, &mut cx, &[e], None);
                for (name, c) in &out.stats.passes {
                    let events = log
                        .0
                        .iter()
                        .filter(|e| matches!(e, Ev::NotSmaller(b, ..) if b == name))
                        .count() as u64;
                    assert_eq!(events, c.rejected_cost, "{text}: {name}");
                }
                for ev in &log.0 {
                    if let Ev::NotSmaller(_, _, _, added, freed) = ev {
                        assert!(freed <= added, "dropped only when it does not pay");
                    }
                }
            }
        }
    }

    #[test]
    fn a_guard_says_which_predicate_failed() {
        let engine = deobfuscator();
        let mut cx = Context::new();
        let e = parse(&mut cx, INPUTS[0].0, 32);
        let (log, _) = logged(&engine, &mut cx, &[e], None);
        let three = cx.parse("3:32", &ParseOptions::default()).unwrap();
        let mut disjoint = 0;
        let mut pow2 = 0;
        for ev in &log.0 {
            match ev {
                Ev::GuardFailed(rule, "disjoint", [Some(_), Some(_)])
                    if rule == "core.arith::add_disjoint" =>
                {
                    disjoint += 1
                }
                Ev::GuardFailed(rule, "is_pow2", [Some(c), None])
                    if rule == "core.arith::mul_pow2" =>
                {
                    assert_eq!(*c, three, "is_pow2 of the constant bound to c");
                    pow2 += 1;
                }
                Ev::GuardFailed(rule, pred, _) => panic!("{rule}: {pred}"),
                _ => {}
            }
        }
        assert!(disjoint > 0 && pow2 > 0, "{disjoint} {pow2}");
        let falses = log
            .0
            .iter()
            .filter(|e| matches!(e, Ev::GuardFalse(_)))
            .count();
        let details = log
            .0
            .iter()
            .filter(|e| matches!(e, Ev::GuardFailed(..)))
            .count();
        assert_eq!(falses, details, "every failed guard says why");
    }

    #[test]
    fn a_fold_by_the_constructors_is_reported() {
        // `~z & z` becomes 0, and the root `… ^ 0` folds when it is rebuilt over it.
        let engine = deobfuscator();
        let mut cx = Context::new();
        let e = parse(&mut cx, INPUTS[0].0, 32);
        let (log, _) = logged(&engine, &mut cx, &[e], None);
        let folds: Vec<_> = log
            .0
            .iter()
            .filter(|e| matches!(e, Ev::Folded(..)))
            .collect();
        let rest = parse(&mut cx, "(x + y) * 3 + (x ^ y)", 32);
        assert_eq!(folds, [&Ev::Folded(e, rest)]);
    }

    /// The explanations of one input's rewrites by `engine`.
    fn explanations(engine: &Engine, text: &str, w: u16) -> (Context, Vec<(String, Explanation)>) {
        let mut cx = Context::new();
        let e = parse(&mut cx, text, w);
        let (log, _) = logged_with(engine, &mut cx, &[e], None, Detail::Explain);
        let out = log
            .0
            .into_iter()
            .filter_map(|e| match e {
                Ev::Explain(by, _, why) => Some((by, why)),
                _ => None,
            })
            .collect();
        (cx, out)
    }

    #[test]
    fn pass_explanations_say_what_the_pass_read() {
        let engine = deobfuscator();
        // The keyed mixer: four layers undone, the constant's preimage 0 under the first three.
        let (_, ex) = explanations(&engine, INPUTS[6].0, 64);
        let [(by, Explanation::Invert { layers })] = &ex[..] else {
            panic!("{ex:?}");
        };
        assert_eq!(by, "invert");
        let maps: Vec<_> = layers.iter().map(|l| l.map).collect();
        assert_eq!(maps, ["v * k", "region", "v * k", "v ^ k"]);
        let zero = BitVec::zero(Width::W64);
        let key = BitVec::from_canonical_u64(Width::W64, 0xd322_0fb7_8e33_751f);
        let pre: Vec<_> = layers.iter().map(|l| l.preimage).collect();
        assert_eq!(pre, [Some(zero), Some(zero), Some(zero), Some(key)]);
        assert!(layers.iter().all(|l| l.bijective));
        // A division by 10.
        let (_, ex) = explanations(&engine, INPUTS[3].0, 64);
        assert!(matches!(
            &ex[..],
            [(_, Explanation::Division { divisor, signed: false, .. })]
                if *divisor == BitVec::from_canonical_u64(Width::W64, 10)
        ));
        // Comparisons: one value against constants, and a pair.
        let (_, ex) = explanations(&engine, INPUTS[4].0, 32);
        let iv = |v: u64| BitVec::from_canonical_u64(Width::W32, v);
        assert!(
            matches!(&ex[..], [(_, Explanation::Intervals { set, .. })] if *set == [(iv(4), iv(9))])
        );
        let (_, ex) = explanations(&engine, "(x <=u y) & (x != y) & (x <s y)", 32);
        assert!(
            matches!(&ex[..], [(_, Explanation::Relations { set: 0b110, .. })]),
            "{ex:?}"
        );
        // Linear and xor forms: `(x ^ 90) + 3 - 3` is 1·(x ^ 90), and `x ^ 90 ^ 90` is x.
        let (mut cx, ex) = explanations(&engine, INPUTS[1].0, 64);
        let atom = parse(&mut cx, "x ^ 90", 64);
        let x = parse(&mut cx, "x", 64);
        let one = BitVec::from_canonical_u64(Width::W64, 1);
        match &ex[..] {
            [
                (_, Explanation::Linear { konst, terms }),
                (
                    _,
                    Explanation::Xor {
                        konst: k2,
                        terms: t2,
                    },
                ),
            ] => {
                assert!(konst.is_zero() && k2.is_zero());
                assert_eq!(terms, &[(atom, one)]);
                assert_eq!(t2, &[(x, BitVec::ones(Width::W64))]);
            }
            other => panic!("{other:?}"),
        }
        // Folding under assumptions: the known bits pin the value.
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let mut a = Assumptions::new();
        let p = cx.parse("idx <u n", &o).unwrap();
        a.assume_true(&mut cx, p).unwrap();
        let e = cx.parse("zext<64>(idx <=u n)", &o).unwrap();
        let (log, _) = logged_with(
            &Engine::standard(),
            &mut cx,
            &[e],
            Some(&a),
            Detail::Explain,
        );
        assert!(log.0.iter().any(|e| matches!(
            e,
            Ev::Explain(by, _, Explanation::Fold { value, .. }) if by == "fact_fold" && value.is_ones()
        )));
    }

    #[cfg(feature = "mba")]
    #[test]
    fn the_mba_service_says_what_vouched_for_its_answer() {
        let engine = Engine::builder()
            .builtin()
            .strategy(Strategy::new(
                "mba",
                vec![Phase::Mba(crate::mba::MbaConfig::default())],
            ))
            .build()
            .unwrap();
        // The service alone: in the presets, the linear passes take a linear MBA first.
        let (_, ex) = explanations(&engine, "(x ^ y) + 2 * (x & y)", 32);
        let mba: Vec<_> = ex.iter().filter(|(b, _)| b == "mba").collect();
        assert!(
            matches!(
                &mba[..],
                [(_, Explanation::Mba { atoms, evidence: "certificate", test: Some("signature"), points: 4 })]
                    if atoms.len() == 2
            ),
            "{mba:?}"
        );
    }

    #[test]
    fn a_trace_writes_the_new_events_and_rule_cards() {
        let engine = deobfuscator();
        let mut cx = Context::new();
        let e = parse(&mut cx, INPUTS[0].0, 32);
        let mut trace = Trace::new(&engine).with_explanations(true).with_facts(true);
        let out = engine
            .run(&mut cx, &[e], Run::default().with_observer(&mut trace))
            .unwrap();
        let text = trace.to_jsonl(&mut cx, &[e], &out).unwrap();
        let has = |p: &str| text.lines().any(|l| l.starts_with(p));
        assert!(has(r#"{"ev":"folded","#));
        assert!(has(r#"{"ev":"not_smaller","pass":"linear","#));
        assert!(
            text.lines()
                .any(|l| l.starts_with(r#"{"ev":"guard_false","#)
                    && l.contains(r#""pred":"disjoint","args":["#))
        );
        let card = text
            .lines()
            .find(|l| l.contains(r#""name":"core.arith::add_xor_and""#))
            .unwrap();
        assert!(
            card.contains(r#""source":"identity add_xor_and<W>"#),
            "{card}"
        );
        assert!(card.contains(r#""ledger":"identity exhaustive("#), "{card}");
        assert!(card.contains(r#""proven":true"#));
        assert!(
            text.lines()
                .any(|l| l.starts_with(r#"{"node":"#) && l.contains(r#""facts":{"zero":"#))
        );
        for l in text.lines() {
            assert!(balanced(l), "{l}");
        }
    }
}

/// Results are kept per engine and per assumption set: going back to one used before finds
/// its results, where a single set would be dropped and walked again on every change.
#[test]
fn results_survive_a_change_of_engine_or_assumptions() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let e = cx
        .parse("((x & y) + (x | y)) * 3 + (z ^ z) + (x >>u 4)", &o)
        .unwrap();
    let small = cx.parse("x <u 16", &o).unwrap();
    let mut under = crate::facts::Assumptions::new();
    under.assume_true(&mut cx, small).unwrap();
    let standard = Engine::standard();
    let deobfuscate = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let mut visits = |engine: &Engine, a: Option<&crate::facts::Assumptions>| {
        let run = Run {
            assumptions: a,
            ..Run::default()
        };
        let out = engine.run(&mut cx, &[e], run).unwrap();
        (out.roots[0].expr, out.stats.node_visits)
    };
    let first = [
        visits(&standard, None),
        visits(&deobfuscate, None),
        visits(&standard, Some(&under)),
        visits(&deobfuscate, Some(&under)),
    ];
    assert!(first.iter().all(|&(_, v)| v > 0), "{first:?}");
    // Under `x < 16` the shift is zero: the sets do differ.
    assert_ne!(first[0].0, first[2].0);
    // What a repeat costs with nothing in between (the deobfuscation strategy's whole-root
    // phases look at a root again; the walks are remembered).
    let repeat = [
        visits(&deobfuscate, Some(&under)).1,
        visits(&deobfuscate, None).1,
    ];
    for _ in 0..2 {
        let again = [
            visits(&standard, None),
            visits(&deobfuscate, None),
            visits(&standard, Some(&under)),
            visits(&deobfuscate, Some(&under)),
        ];
        let want = [0, repeat[1], 0, repeat[0]];
        for ((a, f), w) in again.iter().zip(&first).zip(want) {
            assert_eq!((a.0, a.1), (f.0, w), "{again:?} after {first:?}");
            assert!(a.1 < f.1);
        }
    }
}

/// A store of results: a hit is the result, wherever and whenever; what does not fit (another
/// engine, another version, a symbol at another width, a run under assumptions) is no hit and
/// no harm.
#[test]
fn remembered_results_are_found_again_and_only_where_they_hold() {
    let o = ParseOptions::width(Width::W32);
    let standard = Engine::standard();
    let src = "((a & b) + (a | b) - a) * 5 + ((a ^ 0x33) + 9 - 9 ^ 0x33) + (b << 3)";
    let mut memory = Remembered::new();
    let mut cx = Context::new();
    let e = cx.parse(src, &o).unwrap();
    let plain = standard.simplify(&mut cx, e).unwrap().expr;
    let plain_text = cx.display(plain).to_string();
    let first = (standard.run_remembering(&mut cx, &[e], Run::default(), &mut memory)).unwrap();
    assert_eq!(first.roots[0].expr, plain);
    assert!(first.roots[0].changed && !memory.is_empty() && memory.hits() == 0);
    // The same text, whatever order the entries were learned in; and back from it.
    let text = memory.to_text();
    let mut back = Remembered::from_text(&text).unwrap();
    assert_eq!(back.to_text(), text);
    // Another context, the expression inside a larger one: found, nothing left to rewrite.
    let mut other = Context::new();
    other.parse("(q * 3) ^ r", &o).unwrap();
    let again = other.parse(&format!("({src}) - c"), &o).unwrap();
    let out = (standard.run_remembering(&mut other, &[again], Run::default(), &mut back)).unwrap();
    assert_eq!(back.hits(), 1);
    assert_eq!(
        other.display(out.roots[0].expr).to_string(),
        format!("{plain_text} - c")
    );
    assert!(out.roots[0].changed);
    // The result is equal to what was given, at any point.
    let env = FnEnv(|k: &SymbolKey, w| Some(BitVec::wrapping_from_u64(w, k.structural_hash() | 1)));
    let v = other.eval(&[again, out.roots[0].expr], &env).unwrap();
    assert_eq!(v[0], v[1]);
    // A context where a symbol has another width: the entry does not read there.
    let mut narrow = Context::new();
    narrow.symbol("a", Width::W8).unwrap();
    let wide = narrow.parse("zext<32>(a) + 1", &o).unwrap();
    let hits = back.hits();
    standard
        .run_remembering(&mut narrow, &[wide], Run::default(), &mut back)
        .unwrap();
    assert_eq!(back.hits(), hits);
    // Another engine does not read the store, nor write to it.
    let deobfuscate = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let (len, hits) = (back.len(), back.hits());
    let mut cx2 = Context::new();
    let e2 = cx2.parse(src, &o).unwrap();
    deobfuscate
        .run_remembering(&mut cx2, &[e2], Run::default(), &mut back)
        .unwrap();
    assert_eq!((back.len(), back.hits()), (len, hits));
    // Under assumptions nothing is read or kept: a result may hold only under them.
    let small = cx2.parse("a <u 4", &o).unwrap();
    let mut under = crate::facts::Assumptions::new();
    under.assume_true(&mut cx2, small).unwrap();
    let run = Run {
        assumptions: Some(&under),
        ..Run::default()
    };
    let mut fresh = Remembered::new();
    standard
        .run_remembering(&mut cx2, &[e2], run, &mut fresh)
        .unwrap();
    assert!(fresh.is_empty());
    // A store of another version is an empty store; other text is an error.
    let old = text.replacen(env!("CARGO_PKG_VERSION"), "0.0.1", 1);
    assert!(Remembered::from_text(&old).unwrap().is_empty());
    assert!(Remembered::from_text("something else").is_err());
    assert!(Remembered::from_text(&text[..text.len() - 4]).is_err());
}

/// A derivation's steps are equalities another prover can check, its stretches follow one
/// another from the expression to the result, and a step that is not an equality is found.
#[cfg(feature = "prove")]
#[test]
fn a_derivation_is_checked_without_the_engine() {
    let o = ParseOptions::width(Width::W16);
    let cfg = crate::prove::Config::default();
    let deobfuscate = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    for src in [
        "((x & y) + (x | y)) * 3 + (z ^ z)",
        "((x ^ 0x5a) + 3 - 3) ^ 0x5a",
        "(x ^ y) + 2 * (x & y) + (x | z) - (x & z) - (x ^ z)",
        "((x << 8) | (x >>u 8)) & 0xff00 ^ ((x * 3 + y) - x - x - x)",
        "select(x <u 4, x & 3, x) + (y - y)",
    ] {
        for engine in [Engine::standard(), deobfuscate.clone()] {
            let mut cx = Context::new();
            let e = cx.parse(src, &o).unwrap();
            // A result the context already holds is derived afresh, and left as it was.
            let plain = engine.simplify(&mut cx, e).unwrap();
            let (out, d) = engine.derive(&mut cx, e, Run::default()).unwrap();
            assert_eq!(out.expr, plain.expr, "{src}");
            assert_eq!(engine.simplify(&mut cx, e).unwrap().expr, plain.expr);
            assert_eq!(d.steps.is_empty(), !out.changed, "{src}");
            let report = d.check(&cfg).unwrap();
            assert!(report.continuous, "{src}: {report:?}");
            assert_eq!(report.proved + report.unproved.len(), d.steps.len());
            assert_eq!(
                report.explained + report.whole + report.open.len(),
                d.stretches.len()
            );
            // At 16 bits the search proves every step and every stretch one way or another.
            assert!(report.certified(), "{src}: {report:?}\n{d:#?}");
            // The steps as Lean theorems: one each, or a comment saying why not.
            let lean = d.lean("t").unwrap();
            assert_eq!(lean.matches("-- Step ").count(), d.steps.len());
            // A step changed into something that is not an equality is not proved, and
            // its stretch is no longer explained by its steps (the stretch's two ends are
            // still equal, and proved so as wholes).
            if let Some(first) = d.steps.first() {
                let mut forged = d.clone();
                forged.steps[0].after = format!("({}) + 1", first.after);
                let again = forged.check(&cfg).unwrap();
                assert!(again.unproved.contains(&0), "{src}");
                assert!(again.explained < report.explained && again.sound < report.sound);
            }
        }
    }
}

/// What a pass worked out is a rule afterwards: learned from a derivation, checked, and
/// matched by an engine that has no such pass.
#[cfg(feature = "check")]
#[test]
fn a_pass_step_becomes_a_rule() {
    let o = ParseOptions::width(Width::W64);
    // (The pass's step in its phase, on the forms the rules leave: a step of the root read
    // whole is of the input as written, which the rules rewrite before a rule for it matches.)
    let deobfuscate = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_whole_first(false))
        .build()
        .unwrap();
    // A linear MBA over two large subexpressions, which only the linear-MBA pass undoes.
    let (s, t) = ("(a * 0x9e3779b1 >>u 7)", "(b ^ a << 3)");
    let src = format!("({s} | {t}) + ({s} & {t}) - 2 * ({s} & ~{t}) + 3 * ({s} ^ {t})");
    let mut cx = Context::new();
    let e = cx.parse(&src, &o).unwrap();
    let (out, derivation) = deobfuscate.derive(&mut cx, e, Run::default()).unwrap();
    assert!(out.changed);
    let learned = learn(&[&derivation], &LearnConfig::default()).unwrap();
    assert!(learned.kept >= 1 && learned.generic >= 1, "{learned:#?}");
    // The rules are a rule file like any other: they compile, and the checker vouches.
    let program = crate::rules::RuleProgram::compile(&learned.rules).unwrap();
    let checks = crate::check::check_program(&program, &crate::check::CheckConfig::default());
    assert!(checks.iter().all(|c| c.is_sound()), "{}", learned.rules);
    let ledger = learned.ledger.clone();
    // An engine of rules alone (no pass that knows linear MBA), with the learned ones: the
    // same shape over other subexpressions, at another width, is now rewritten.
    let with = Engine::builder()
        .builtin()
        .program(program, &ledger)
        .strategy(Strategy::standard().with_rule_groups(&["learned"]))
        .build()
        .unwrap();
    let narrow = ParseOptions::width(Width::W16);
    let other = "(p * q | r) + (p * q & r) - 2 * (p * q & ~r) + 3 * (p * q ^ r)";
    let mut cx = Context::new();
    let e = cx.parse(other, &narrow).unwrap();
    let plain = Engine::standard().simplify(&mut cx, e).unwrap().expr;
    let better = with.simplify(&mut cx, e).unwrap().expr;
    assert!(
        cx.tree_size(better).unwrap() < cx.tree_size(plain).unwrap(),
        "{} against {}\n{}",
        cx.display(better),
        cx.display(plain),
        learned.rules
    );
    let env = FnEnv(|k: &SymbolKey, w| Some(BitVec::wrapping_from_u64(w, k.structural_hash())));
    let v = cx.eval(&[e, better], &env).unwrap();
    assert_eq!(v[0], v[1]);
}

/// Forgetting the engine's results leaves the context as it was built: the same answer, found
/// again.
#[test]
fn forgotten_results_are_found_again() {
    let o = ParseOptions::width(Width::W64);
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let mut cx = Context::new();
    // (A product: no linear MBA whole, which a stage would read without a rule.)
    let e = (cx.parse("((x ^ y) + 2 * (x & y) - y) * (z + 0 | z)", &o)).unwrap();
    let mut steps = RuleCensus::default();
    let first = (engine.run(&mut cx, &[e], Run::default().with_observer(&mut steps))).unwrap();
    let nodes = cx.len();
    // From memory: nothing is rewritten.
    let mut again = RuleCensus::default();
    engine
        .run(&mut cx, &[e], Run::default().with_observer(&mut again))
        .unwrap();
    cx.forget_results();
    let mut anew = RuleCensus::default();
    let second = (engine.run(&mut cx, &[e], Run::default().with_observer(&mut anew))).unwrap();
    assert_eq!(first.roots[0].expr, second.roots[0].expr);
    assert_eq!(cx.len(), nodes);
    let applied = |c: &RuleCensus| c.rules.values().map(|r| r.applied).sum::<u64>();
    assert!(applied(&steps) > 0 && applied(&again) == 0 && applied(&anew) == applied(&steps));
}

/// A full store makes room by dropping what was used longest ago, and two stores merge.
#[test]
fn a_full_store_forgets_the_oldest_and_stores_merge() {
    let o = ParseOptions::width(Width::W32);
    let engine = Engine::builder().builtin().build().unwrap();
    let question = |k: u32| format!("(x ^ {k}) + 2 * (x & {k}) - {k} + (y * y * {})", k + 7);
    let mut memory = (Remembered::new().with_max_entries(8).with_min_tree(8)).with_per_run(0);
    let mut cx = Context::new();
    for k in 1..=8 {
        let e = cx.parse(&question(k), &o).unwrap();
        (engine.run_remembering(&mut cx, &[e], Run::default(), &mut memory)).unwrap();
    }
    assert_eq!(memory.len(), 8);
    // The first is found again (and so is the newest now); a ninth makes room without it.
    let mut other = Context::new();
    let first = other.parse(&question(1), &o).unwrap();
    (engine.run_remembering(&mut other, &[first], Run::default(), &mut memory)).unwrap();
    assert_eq!(memory.hits(), 1);
    let ninth = other.parse(&question(9), &o).unwrap();
    (engine.run_remembering(&mut other, &[ninth], Run::default(), &mut memory)).unwrap();
    assert_eq!(memory.len(), 8);
    let mut third = Context::new();
    for (k, hit) in [(1, true), (2, false), (9, true)] {
        let before = memory.hits();
        let e = third.parse(&question(k), &o).unwrap();
        let mut probe = memory.clone();
        (engine.run_remembering(&mut third, &[e], Run::default(), &mut probe)).unwrap();
        assert_eq!(probe.hits() > before, hit, "question {k}");
    }
    // Two stores as one; not with a store of another engine.
    let mut a = Remembered::new().with_min_tree(8).with_per_run(0);
    let mut b = Remembered::new().with_min_tree(8).with_per_run(0);
    let (mut c1, mut c2) = (Context::new(), Context::new());
    let (e1, e2) = (
        c1.parse(&question(1), &o).unwrap(),
        c2.parse(&question(2), &o).unwrap(),
    );
    (engine.run_remembering(&mut c1, &[e1], Run::default(), &mut a)).unwrap();
    (engine.run_remembering(&mut c2, &[e2], Run::default(), &mut b)).unwrap();
    assert!(a.merge(&b));
    assert_eq!(a.len(), 2);
    let again = c1.parse(&question(2), &o).unwrap();
    let out = (engine.run_remembering(&mut c1, &[again], Run::default(), &mut a)).unwrap();
    assert_eq!((a.hits(), out.stats.rewrites), (1, 0));
    let deobfuscate = (Engine::builder().builtin())
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    let mut d = Remembered::new().with_min_tree(8).with_per_run(0);
    let e3 = c2.parse(&question(3), &o).unwrap();
    (deobfuscate.run_remembering(&mut c2, &[e3], Run::default(), &mut d)).unwrap();
    assert!(!a.merge(&d) && a.len() == 2);
}

/// The analyses on their own are exact: an expression equals the sum, and the exclusive or,
/// that the engine reads it as, at every value.
#[test]
fn the_forms_of_an_expression_are_the_expression() {
    let engine = Engine::standard();
    let mut g = generator(0xf0_4a55);
    let (mut sums, mut xors, mut tables) = (0, 0, 0);
    for _ in 0..300 {
        let mut cx = Context::new();
        let w = 1 + g.rng.below(6) as u16;
        // Three expressions, joined as a sum or as an exclusive or in turn.
        let (a, b, c) = (
            g.expr(&mut cx, w, 3).0,
            g.expr(&mut cx, w, 3).0,
            g.expr(&mut cx, w, 3).0,
        );
        let width = cx.width(a).unwrap();
        let three = cx.constant(&BitVec::wrapping_from_u64(width, 3)).unwrap();
        let e = if g.rng.below(2) == 0 {
            let b3 = cx.bin(BinOp::Mul, b, three).unwrap();
            let ab = cx.bin(BinOp::Add, a, b3).unwrap();
            cx.bin(BinOp::Sub, ab, c).unwrap()
        } else {
            let bm = cx.bin(BinOp::And, b, three).unwrap();
            let nc = cx.un(crate::UnOp::Not, c).unwrap();
            let ab = cx.bin(BinOp::Xor, a, bm).unwrap();
            cx.bin(BinOp::Xor, ab, nc).unwrap()
        };
        let linear = engine.linear_form(&mut cx, e).unwrap();
        let mut sum = cx.constant(&linear.constant).unwrap();
        for (c, t) in &linear.terms {
            let c = cx.constant(c).unwrap();
            let p = cx.bin(BinOp::Mul, c, *t).unwrap();
            sum = cx.bin(BinOp::Add, sum, p).unwrap();
        }
        assert!(equivalent(&mut cx, e, sum, &mut g.rng), "{}", cx.display(e));
        sums += usize::from(linear.terms.len() > 1);
        let xor = engine.xor_form(&mut cx, e).unwrap();
        let mut acc = cx.constant(&xor.constant).unwrap();
        for (m, t) in &xor.terms {
            let m = cx.constant(m).unwrap();
            let p = cx.bin(BinOp::And, m, *t).unwrap();
            acc = cx.bin(BinOp::Xor, acc, p).unwrap();
        }
        assert!(equivalent(&mut cx, e, acc, &mut g.rng), "{}", cx.display(e));
        xors += usize::from(xor.terms.len() > 1);
        assert_eq!(cx.width(sum).unwrap(), width);
        // A bitwise function of two of the parts and a constant, by its tables: the
        // disjunction, over the classes, of the minterms of the class's table under its mask.
        let m = cx
            .constant(&BitVec::wrapping_from_u64(width, g.rng.below(64)))
            .unwrap();
        let am = cx.bin(BinOp::And, a, m).unwrap();
        let nb = cx.un(crate::UnOp::Not, b).unwrap();
        let bw = cx.bin(BinOp::Xor, am, nb).unwrap();
        let bw = cx.bin(BinOp::Or, bw, a).unwrap();
        if let Some(form) = engine.bitwise_form(&mut cx, bw).unwrap() {
            tables += 1;
            let mut acc = cx.constant(&BitVec::zero(width)).unwrap();
            for (mask, table) in &form.classes {
                let mask = cx.constant(mask).unwrap();
                for p in 0..1u8 << form.terms.len() {
                    if table >> p & 1 == 0 {
                        continue;
                    }
                    let mut minterm = mask;
                    for (k, &t) in form.terms.iter().enumerate() {
                        let lit = if p >> k & 1 == 1 {
                            t
                        } else {
                            cx.un(crate::UnOp::Not, t).unwrap()
                        };
                        minterm = cx.bin(BinOp::And, minterm, lit).unwrap();
                    }
                    acc = cx.bin(BinOp::Or, acc, minterm).unwrap();
                }
            }
            assert!(
                equivalent(&mut cx, bw, acc, &mut g.rng),
                "{}",
                cx.display(bw)
            );
        }
    }
    assert!(tables > 20, "{tables}");
    // Both were exercised on forms of several terms.
    assert!(sums > 20 && xors > 20, "{sums} {xors}");
}

/// The three readings of a linear MBA agree: what the pass makes of one is equal to it by the
/// MBA service's procedures and by the checker's corner evaluation, which share no code with
/// the pass or with each other; and an expression that is not equal is equal by none.
#[cfg(all(feature = "mba", feature = "prove"))]
#[test]
fn the_linear_mba_implementations_agree() {
    use crate::mba::{self, MbaBudget, MbaLimits, Verdict};
    let o = ParseOptions::width(Width::W64);
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::new("t", vec![Phase::LinearMba]))
        .build()
        .unwrap();
    let mut rng = Rng(0x11ea_4b0a);
    let atoms = ["x", "y", "z", "(p * q)"];
    let bitwise = |rng: &mut Rng| {
        let (a, b) = (atoms[rng.below(4) as usize], atoms[rng.below(4) as usize]);
        match rng.below(7) {
            0 => a.to_string(),
            1 => format!("({a} & {b})"),
            2 => format!("({a} | {b})"),
            3 => format!("({a} ^ {b})"),
            4 => format!("~({a} & {b})"),
            5 => format!("({a} & ~{b})"),
            _ => format!("~({a} ^ {b})"),
        }
    };
    let (mut rewritten, mut refused) = (0, 0);
    let (limits, budget) = (MbaLimits::default(), MbaBudget::default());
    for round in 0..200 {
        let mut src = String::from("0");
        for _ in 0..2 + rng.below(6) {
            let c = rng.below(1 << 20) as i64 - (1 << 19);
            src = format!("{src} + {c} * {}", bitwise(&mut rng));
        }
        let mut cx = Context::new();
        let e = cx.parse(&src, &o).unwrap();
        let out = engine.simplify(&mut cx, e).unwrap().expr;
        if out != e {
            rewritten += 1;
            assert_eq!(
                mba::equal(&mut cx, e, out, &limits, &budget).unwrap(),
                Verdict::Proved,
                "round {round}: {src}"
            );
            assert!(
                super::derive::corners_equal(&cx, e, out).unwrap(),
                "round {round}: {src}"
            );
        }
        // One term more: equal by neither.
        let extra = cx
            .parse(&format!("{src} + ({})", bitwise(&mut rng)), &o)
            .unwrap();
        let by_service = mba::equal(&mut cx, e, extra, &limits, &budget).unwrap();
        let by_corners = super::derive::corners_equal(&cx, e, extra).unwrap();
        assert_eq!(
            by_service == Verdict::Proved,
            by_corners,
            "round {round}: {src}"
        );
        refused += usize::from(!by_corners);
    }
    assert!(rewritten > 50 && refused > 100, "{rewritten} {refused}");
}

/// A question asked between a checkpoint and a rollback is answered as in a context of its
/// own, whatever was asked before it in the same context.
#[cfg(feature = "mba")]
#[test]
fn a_rolled_back_context_answers_as_a_fresh_one() {
    let o = ParseOptions::width(Width::W64);
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate())
        .build()
        .unwrap();
    // Questions that share parts: the same sums and conjunctions under other constants.
    let question = |k: u64| {
        format!(
            "((x ^ y) + 2 * (x & y)) * {k} + ((x | z) - (x & ~z)) * (y ^ {}) \
             - (~(x & y) & (x | y)) * {} + ((x + y) ^ z) * ((x & z) + {k})",
            k + 3,
            k * 7 + 1
        )
    };
    let alone: Vec<String> = (1..12)
        .map(|k| {
            let mut cx = Context::new();
            let e = cx.parse(&question(k), &o).unwrap();
            let out = engine.simplify(&mut cx, e).unwrap().expr;
            cx.display(out).to_string()
        })
        .collect();
    let mut shared = Context::new();
    // A symbol and a part every question has, made once and kept.
    let kept = shared.parse("(x ^ y) + 2 * (x & y)", &o).unwrap();
    for (n, k) in (1..12).enumerate() {
        let at = shared.checkpoint();
        let e = shared.parse(&question(k), &o).unwrap();
        let out = engine.simplify(&mut shared, e).unwrap().expr;
        assert_eq!(shared.display(out).to_string(), alone[n], "question {k}");
        shared.rollback(at).unwrap();
    }
    // What was there before the questions is still there.
    assert_eq!(shared.display(kept).to_string(), "(x & y) * 2 + (x ^ y)");
}

/// A predicate is the set of values, or the set of relations, the comparison analysis reads
/// it as.
#[test]
fn the_form_of_a_predicate_is_the_predicate() {
    let engine = Engine::standard();
    let o = ParseOptions::width(Width::new(5).unwrap());
    let mut rng = Rng(0x9e_d1ca);
    let (mut values, mut relations) = (0, 0);
    for round in 0..300 {
        let two = round % 2 == 1;
        let atom = |rng: &mut Rng| {
            let op = ["<u", "<=u", ">u", ">=u", "<s", ">=s", "==", "!="][rng.below(8) as usize];
            let rhs = if two {
                "y".to_string()
            } else {
                rng.below(32).to_string()
            };
            if two && rng.below(2) == 0 {
                format!("(y {op} x)")
            } else {
                format!("(x {op} {rhs})")
            }
        };
        let mut src = atom(&mut rng);
        for _ in 0..1 + rng.below(3) {
            let join = ["&", "|", "^"][rng.below(3) as usize];
            let not = if rng.below(3) == 0 { "~" } else { "" };
            src = format!("({src} {join} {not}{})", atom(&mut rng));
        }
        let mut cx = Context::new();
        let e = cx.parse(&src, &o).unwrap();
        let rebuilt = match engine.predicate_form(&mut cx, e).unwrap() {
            PredicateForm::Constant(b) => cx.bool(b).unwrap(),
            PredicateForm::Values { of, intervals } => {
                values += 1;
                let mut acc = cx.bool(false).unwrap();
                for (lo, hi) in &intervals {
                    let (lo, hi) = (cx.constant(lo).unwrap(), cx.constant(hi).unwrap());
                    let above = cx.cmp(CmpOpExt::Uge, of, lo).unwrap();
                    let below = cx.cmp(CmpOpExt::Ule, of, hi).unwrap();
                    let within = cx.bin(BinOp::And, above, below).unwrap();
                    acc = cx.bin(BinOp::Or, acc, within).unwrap();
                }
                acc
            }
            PredicateForm::Relation {
                left,
                right,
                relations: set,
            } => {
                relations += 1;
                let mut acc = cx.bool(false).unwrap();
                // Equal; then each way of being below or above, unsigned and signed.
                let ways = [
                    (CmpOpExt::Eq, CmpOpExt::Eq),
                    (CmpOpExt::Ult, CmpOpExt::Slt),
                    (CmpOpExt::Ult, CmpOpExt::Sgt),
                    (CmpOpExt::Ugt, CmpOpExt::Slt),
                    (CmpOpExt::Ugt, CmpOpExt::Sgt),
                ];
                for (k, (unsigned, signed)) in ways.into_iter().enumerate() {
                    if set >> k & 1 == 1 {
                        let u = cx.cmp(unsigned, left, right).unwrap();
                        let s = cx.cmp(signed, left, right).unwrap();
                        let both = cx.bin(BinOp::And, u, s).unwrap();
                        acc = cx.bin(BinOp::Or, acc, both).unwrap();
                    }
                }
                acc
            }
            _ => continue,
        };
        assert!(equivalent(&mut cx, e, rebuilt, &mut rng), "{src}");
    }
    assert!(values > 50 && relations > 50, "{values} {relations}");
}

/// What an expression is made into under a mask agrees with it on the mask's bits.
#[test]
fn an_expression_under_a_mask_agrees_on_the_mask() {
    let engine = Engine::standard();
    let mut g = generator(0xde_3a4d);
    let mut changed = 0;
    for _ in 0..400 {
        let mut cx = Context::new();
        let w = 2 + g.rng.below(5) as u16;
        let (a, b) = (g.expr(&mut cx, w, 3).0, g.expr(&mut cx, w, 3).0);
        let width = cx.width(a).unwrap();
        // Parts that reach only some bits: a shift, a mask, a sum.
        let k = cx
            .constant(&BitVec::wrapping_from_u64(width, 1 + g.rng.below(2)))
            .unwrap();
        let hi = cx.bin(BinOp::Shl, b, k).unwrap();
        let e = match g.rng.below(3) {
            0 => cx.bin(BinOp::Add, a, hi).unwrap(),
            1 => cx.bin(BinOp::Xor, a, hi).unwrap(),
            _ => cx.bin(BinOp::Or, hi, a).unwrap(),
        };
        let mask = BitVec::wrapping_from_u64(width, g.rng.below(1 << w));
        let out = engine.under_mask(&mut cx, e, &mask).unwrap();
        changed += usize::from(out != e);
        let m = cx.constant(&mask).unwrap();
        let (x, y) = (
            cx.bin(BinOp::And, e, m).unwrap(),
            cx.bin(BinOp::And, out, m).unwrap(),
        );
        assert!(
            equivalent(&mut cx, x, y, &mut g.rng),
            "{} under {mask:?}",
            cx.display(e)
        );
    }
    assert!(changed > 50, "{changed}");
}
