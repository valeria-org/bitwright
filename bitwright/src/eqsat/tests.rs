//! Equality-saturation tests, by the regression categories the design lists (§10): soundness
//! against the independent reference, expansion before cancellation, repeated variables,
//! cycles, widths, unsupported inputs, admission, budgets and rollback, memo, duplicates,
//! determinism, and contract violations.

use super::*;
use crate::testutil::{Gen, Rng, ref_bin, ref_un};
use crate::{BinOp, ParseOptions, UnOp};
use bitwright_ref as r;

/// Groups that saturate together on the fixtures (`distrib_and` with `distrib_or` does not).
const GROUPS: &[&str] = &[
    "eqsat.assoc",
    "eqsat.distrib",
    "eqsat.distrib_and",
    "eqsat.negation",
    "eqsat.cancel",
];

fn sat() -> Saturator {
    Saturator::builtin_groups(GROUPS, SaturateConfig::default()).0
}

fn parse(cx: &mut Context, src: &str, w: u16) -> Expr {
    cx.parse(src, &ParseOptions::width(Width::new(w).unwrap()))
        .unwrap()
}

/// A random expression in the fragment, with its reference term.
fn frag(g: &mut Gen, cx: &mut Context, w: u16, depth: u32) -> (Expr, r::Term) {
    let width = Width::new(w).unwrap();
    if depth == 0 || g.rng.chance(1, 4) {
        if g.rng.chance(1, 4) {
            let v = g.constant(w);
            return (
                cx.constant(&v).unwrap(),
                r::Term::Const(r::Bits::from_limbs(w, v.limbs())),
            );
        }
        let k = g.rng.below(3) as usize;
        let name = format!("{}{w}", ["x", "y", "z"][k]);
        let e = cx.symbol(name.as_str(), width).unwrap();
        let idx = g.var_index(&name, w);
        return (e, r::Term::Var(idx, w));
    }
    let d = depth - 1;
    if g.rng.chance(1, 5) {
        let op = [UnOp::Neg, UnOp::Not][g.rng.below(2) as usize];
        let (a, ta) = frag(g, cx, w, d);
        return (cx.un(op, a).unwrap(), r::Term::Un(ref_un(op), Box::new(ta)));
    }
    let op = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
    ][g.rng.below(6) as usize];
    let (a, ta) = frag(g, cx, w, d);
    let (b, tb) = frag(g, cx, w, d);
    (
        cx.bin(op, a, b).unwrap(),
        r::Term::Bin(ref_bin(op), Box::new(ta), Box::new(tb)),
    )
}

#[test]
fn candidates_agree_with_the_reference() {
    let s = sat();
    let mut g = Gen {
        rng: Rng(0xe95a),
        max_w: 8,
        vars: Vec::new(),
    };
    let mut found = 0;
    for i in 0..2000 {
        let mut cx = Context::new();
        g.vars.clear();
        let w = if i % 8 == 0 {
            [16, 64, 128][g.rng.below(3) as usize]
        } else {
            1 + g.rng.below(8) as u16
        };
        let (e, t) = frag(&mut g, &mut cx, w, 4);
        let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
        let Some(c) = out.roots[0].candidate else {
            continue;
        };
        found += 1;
        // Against the independent bit-serial evaluator, at random points.
        let vars = g.vars.clone();
        for _ in 0..64 {
            let vals: Vec<r::Bits> = vars
                .iter()
                .map(|&(_, w)| r::Bits::from_limbs(w, &[g.rng.next(), g.rng.next()]))
                .collect();
            let want = t.eval(&vals).unwrap();
            let env: Vec<(crate::SymbolKey, BitVec)> = vars
                .iter()
                .zip(&vals)
                .map(|((name, w), v)| {
                    (
                        crate::SymbolKey::from(name.as_str()),
                        BitVec::from_limbs(Width::new(*w).unwrap(), &v.to_limbs()).unwrap(),
                    )
                })
                .collect();
            let got = cx.eval(&[c], env.as_slice()).unwrap()[0];
            let want = BitVec::from_limbs(got.width(), &want.to_limbs()).unwrap();
            assert_eq!(got, want, "{} vs {}", cx.display(e), cx.display(c));
        }
        // Strictly cheaper as a tree.
        assert!(cx.tree_size(c).unwrap() < cx.tree_size(e).unwrap());
    }
    assert!(found > 20, "{found}");
}

#[test]
fn expansion_before_cancellation() {
    let s = sat();
    let mut cx = Context::new();
    // Needs distributing, then cancelling: a directed simplifier would not expand first.
    let e = parse(&mut cx, "x * (y + 1) - x * y", 32);
    let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out.publication, Publication::Published);
    assert_eq!(out.roots[0].candidate, Some(parse(&mut cx, "x", 32)));
    // Factoring (distributivity backwards).
    let e = parse(&mut cx, "a & b | a & c", 32);
    let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(
        out.roots[0].candidate,
        Some(parse(&mut cx, "a & (b | c)", 32))
    );
}

// Needs the rule checker (feature `check`) to build a ledger.
#[cfg(feature = "check")]
fn program_with_ledger(src: &str) -> (RuleProgram, Ledger) {
    let p = RuleProgram::compile(src).unwrap_or_else(|e| panic!("{}", e.render("t", src)));
    let l = Ledger::from_checks(&crate::check::check_program(
        &p,
        &crate::check::CheckConfig::default(),
    ));
    (p, l)
}

#[cfg(feature = "check")]
#[test]
fn repeated_variables_match_by_class() {
    let (p, l) = program_with_ledger(
        "bitwright 1;
        group t {
            #[allow(BW0407)]
            identity xor_from_or_and<W>(x: W, y: W) { x ^ y <=> (x | y) - (x & y) }
        }",
    );
    let (s, _) = Saturator::new(&[(&p, &l)], &[], SaturateConfig::default()).unwrap();
    let mut cx = Context::new();
    // Read backwards, `(x | y) - (x & y)` repeats both variables.
    let e = parse(&mut cx, "(q | r) - (q & r)", 8);
    let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].candidate, Some(parse(&mut cx, "q ^ r", 8)));
    // Different classes for the two occurrences: no such match (and nothing cheaper).
    let e = parse(&mut cx, "(q | r) - (p & r)", 8);
    let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].candidate, None);
}

#[test]
fn unsupported_inputs_and_admission() {
    let s = sat();
    let mut cx = Context::new();
    for (src, w) in [
        ("(x << 3) + x", 8),
        ("(x <u y) & (y <u x)", 1),
        ("zext<16>(p:8) + q", 16),
    ] {
        let e = parse(&mut cx, src, w);
        let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
        assert_eq!(out.roots[0].end, RootEnd::DeclinedUnsupported, "{src}");
        assert_eq!(
            out.stats.enodes, 0,
            "{src}: built something for a declined root"
        );
    }
    // Atomize: the shift becomes an opaque atom, and the rest is searched.
    let cfg = SaturateConfig {
        unsupported: UnsupportedPolicy::Atomize,
        ..SaturateConfig::default()
    };
    let (atomizing, _) = Saturator::builtin_groups(GROUPS, cfg);
    let e = parse(&mut cx, "(x << 3) * (y + 1) - (x << 3) * y", 8);
    let out = atomizing
        .search(&mut cx, &[e], SearchRun::default())
        .unwrap();
    assert_eq!(out.roots[0].candidate, Some(parse(&mut cx, "x << 3", 8)));
    // Wider than the fragment.
    let e = parse(&mut cx, "u * (v + 1) - u * v", 256);
    assert_eq!(
        s.search(&mut cx, &[e], SearchRun::default()).unwrap().roots[0].end,
        RootEnd::DeclinedUnsupported
    );
    // Oversized: declined by metadata before anything is built.
    let mut big = parse(&mut cx, "x", 8);
    for _ in 0..20_000 {
        let y = parse(&mut cx, "y", 8);
        big = cx.bin(BinOp::Add, big, y).unwrap();
    }
    let out = s.search(&mut cx, &[big], SearchRun::default()).unwrap();
    assert!(matches!(out.roots[0].end, RootEnd::DeclinedAdmission(_)));
    assert_eq!(out.stats.enodes, 0);
}

#[test]
fn budgets_withhold_the_whole_batch() {
    let s = sat();
    let mut cx = Context::new();
    let a = parse(&mut cx, "x * (y + 1) - x * y", 32);
    let b = parse(&mut cx, "(p + q) * (p + q) - p * p", 32);
    let d = parse(&mut cx, "x << 1", 32);
    let mut allowance = Allowance::new(Budget {
        eqsat_nodes: 60,
        ..Budget::UNLIMITED
    });
    let out = s
        .search(
            &mut cx,
            &[d, a, b],
            SearchRun {
                allowance: Some(&mut allowance),
                per_call: Some(Budget::UNLIMITED),
                ..SearchRun::default()
            },
        )
        .unwrap();
    assert!(matches!(out.publication, Publication::Withheld { .. }));
    assert!(out.roots.iter().all(|r| r.candidate.is_none()));
    // Spent is spent.
    assert_eq!(allowance.spent().eqsat_nodes, out.stats.enodes);
    assert!(out.stats.enodes > 0);
    // Not memoized: a later search with a budget publishes.
    let out = s.search(&mut cx, &[a], SearchRun::default()).unwrap();
    assert_eq!(out.publication, Publication::Published);
    assert!(out.roots[0].candidate.is_some());
}

#[test]
fn memo_and_duplicates() {
    let s = sat();
    let mut cx = Context::new();
    let a = parse(&mut cx, "x * (y + 1) - x * y", 32);
    let b = parse(&mut cx, "a & b | a & c", 32);
    let out = s.search(&mut cx, &[b, a, b], SearchRun::default()).unwrap();
    assert_eq!(
        out.roots[0],
        SearchRoot {
            input: b,
            ..out.roots[2]
        }
    );
    assert_eq!(out.roots[0].candidate, out.roots[2].candidate);
    let again = s.search(&mut cx, &[a, b], SearchRun::default()).unwrap();
    assert_eq!(again.stats.enodes, 0);
    assert_eq!(again.stats.memo_hits, 2);
    assert_eq!(again.roots[0].candidate, out.roots[1].candidate);
    // Another configuration is another epoch.
    let (other, _) = Saturator::builtin_groups(
        GROUPS,
        SaturateConfig {
            iterations: 7,
            ..SaturateConfig::default()
        },
    );
    let o = other.search(&mut cx, &[a], SearchRun::default()).unwrap();
    assert_eq!(o.stats.memo_hits, 0);
    // clear() drops the memo.
    cx.clear();
    assert!(cx.eqsat_memo.entries.is_empty());
}

#[test]
fn searches_are_deterministic() {
    let s = sat();
    let mut g1 = Gen {
        rng: Rng(9),
        max_w: 8,
        vars: Vec::new(),
    };
    let mut g2 = Gen {
        rng: Rng(9),
        max_w: 8,
        vars: Vec::new(),
    };
    for _ in 0..100 {
        let (mut c1, mut c2) = (Context::new(), Context::new());
        // Different construction histories.
        for n in ["z8", "y8", "x8"] {
            c2.symbol(n, Width::W8).unwrap();
        }
        let (e1, _) = frag(&mut g1, &mut c1, 8, 3);
        let (e2, _) = frag(&mut g2, &mut c2, 8, 3);
        let r1 = s.search(&mut c1, &[e1], SearchRun::default()).unwrap();
        let r2 = s.search(&mut c2, &[e2], SearchRun::default()).unwrap();
        let show = |cx: &Context, r: &SearchReport| {
            r.roots[0].candidate.map(|c| cx.display(c).to_string())
        };
        assert_eq!(show(&c1, &r1), show(&c2, &r2));
        assert_eq!(r1.stats.enodes, r2.stats.enodes);
    }
}

#[cfg(feature = "check")]
#[test]
fn an_unsound_equation_is_a_contract_violation() {
    // A ledger vouching for an unsound rule (forged: the checker refutes it).
    let src =
        "bitwright 1;\ngroup t {\n#[allow(BW0407)] rule bad<W>(x: W, y: W) { x - y => x }\n}\n";
    let p = RuleProgram::compile(src).unwrap();
    let rule = &p.rules()[0];
    assert!(!crate::check::check_rule(rule, &crate::check::CheckConfig::default()).is_sound());
    let text = format!(
        "# bitwright proof ledger v2. Generated; do not edit.\n{} {} rule forged\n",
        rule.name, rule.id
    );
    let l = Ledger::parse(&text).unwrap();
    let (s, report) = Saturator::new(&[(&p, &l)], &[], SaturateConfig::default()).unwrap();
    assert_eq!(report.admitted, ["t::bad"]);
    let mut cx = Context::new();
    let e = parse(&mut cx, "a - b", 8);
    // The cheaper candidate `a` disagrees with the input: never published, always reported.
    match s.search(&mut cx, &[e], SearchRun::default()) {
        Err(Error::Contract(_)) => {}
        other => panic!("{other:?}"),
    }
}

#[cfg(feature = "check")]
#[test]
fn applied_matches_do_not_starve_later_ones() {
    // One match per rule and iteration: both redexes must still be reached.
    let (p, l) = program_with_ledger(
        "bitwright 1;\ngroup t {\n#[allow(BW0407)] rule add_sub<W>(x: W, y: W) { (x + y) - y => x }\n}\n",
    );
    let cfg = SaturateConfig {
        matches_per_rule_iter: 1,
        ..SaturateConfig::default()
    };
    let (s, _) = Saturator::new(&[(&p, &l)], &[], cfg).unwrap();
    let mut cx = Context::new();
    let e = parse(&mut cx, "((p + q) - q) * ((r + t) - t)", 32);
    let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].end, RootEnd::Saturated);
    assert_eq!(out.roots[0].candidate, Some(parse(&mut cx, "p * r", 32)));
}

#[test]
fn congruence_and_extraction_ties() {
    let mut meter = Meter::new(Budget::UNLIMITED, None);
    let mut eg = EGraph::new();
    let leaf = |eg: &mut EGraph, i: u32, m: &mut Meter<'_>| {
        eg.add(
            ENode {
                op: EOp::Leaf(i),
                kids: [0, 0],
            },
            true,
            m,
        )
        .ok()
        .unwrap()
    };
    let x = leaf(&mut eg, 1, &mut meter);
    let y = leaf(&mut eg, 2, &mut meter);
    let fx = eg
        .add(
            ENode {
                op: EOp::Un(UnOp::Not),
                kids: [x, 0],
            },
            true,
            &mut meter,
        )
        .ok()
        .unwrap();
    let fy = eg
        .add(
            ENode {
                op: EOp::Un(UnOp::Not),
                kids: [y, 0],
            },
            false,
            &mut meter,
        )
        .ok()
        .unwrap();
    assert_ne!(eg.find(fx), eg.find(fy));
    assert!(eg.union(x, y, &mut meter).ok().unwrap());
    assert!(eg.rebuild(&mut meter).is_ok());
    // Congruence: ~x and ~y are now one class.
    assert_eq!(eg.find(fx), eg.find(fy));
    // Extraction prefers the original (imported) e-node on a tie in cost.
    let best = extract::costs(&mut eg, &mut meter).ok().unwrap();
    let c = eg.find(fx);
    let chosen = best[&c].1;
    assert!(eg.imported[chosen as usize]);
    // A union of two different constants is a contract violation.
    let one = eg
        .add(
            ENode {
                op: EOp::Const(BitVec::one(Width::W8)),
                kids: [0, 0],
            },
            true,
            &mut meter,
        )
        .ok()
        .unwrap();
    let two = eg
        .add(
            ENode {
                op: EOp::Const(BitVec::from_u64(Width::W8, 2).unwrap()),
                kids: [0, 0],
            },
            true,
            &mut meter,
        )
        .ok()
        .unwrap();
    assert!(matches!(
        eg.union(one, two, &mut meter),
        Err(Halt::Contract)
    ));
}

#[test]
fn an_iteration_cap_withholds_and_is_not_memoized() {
    // `&` over `|` and `|` over `&` rewrite each other's results without end.
    let (s, _) = Saturator::builtin_groups(
        &["eqsat.distrib_and", "eqsat.distrib_or"],
        SaturateConfig::default(),
    );
    let mut cx = Context::new();
    let a = parse(&mut cx, "a & b | a & c", 32);
    let b = parse(&mut cx, "x & (y ^ z)", 32);
    let c = parse(&mut cx, "p | q & r", 32);
    let out = s.search(&mut cx, &[a, b, c], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].end, RootEnd::IterationCap);
    assert_eq!(
        out.publication,
        Publication::Withheld {
            cause: RootEnd::IterationCap
        }
    );
    // The rest of the batch is not searched once publication is withheld.
    assert_eq!(out.roots[1].end, RootEnd::Skipped);
    assert_eq!(out.roots[2].end, RootEnd::Skipped);
    assert!(out.roots.iter().all(|r| r.candidate.is_none()));
    // Not memoized: searched again.
    let again = s.search(&mut cx, &[a], SearchRun::default()).unwrap();
    assert_eq!(again.stats.memo_hits, 0);
    assert!(again.stats.enodes > 0);
    // Each group alone saturates and publishes.
    for (group, src, want) in [
        ("eqsat.distrib_and", "a & b | a & c", "a & (b | c)"),
        ("eqsat.distrib_or", "(a | b) & (a | c)", "a | b & c"),
    ] {
        let (s, _) = Saturator::builtin_groups(&[group], SaturateConfig::default());
        let e = parse(&mut cx, src, 32);
        let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
        assert_eq!(out.roots[0].end, RootEnd::Saturated, "{group}");
        assert_eq!(out.roots[0].candidate, Some(parse(&mut cx, want, 32)));
    }
}

// ----- regressions from the M7 review ------------------------------------------------------------

struct Late;
impl crate::engine::Clock for Late {
    fn now_ticks(&self) -> u64 {
        u64::MAX
    }
}

#[test]
fn a_deadline_stops_the_search() {
    let s = sat();
    let mut cx = Context::new();
    let e = parse(&mut cx, "x * (y + 1) - x * y", 32);
    let out = s
        .search(
            &mut cx,
            &[e],
            SearchRun {
                deadline: Some(Deadline {
                    clock: &Late,
                    at: 0,
                    check_every: 1,
                }),
                ..SearchRun::default()
            },
        )
        .unwrap();
    assert_eq!(out.roots[0].end, RootEnd::Stopped(Exhausted::Deadline));
    assert!(matches!(out.publication, Publication::Withheld { .. }));
    assert_eq!(out.roots[0].candidate, None);
    // A deadline read late in the search stops it too.
    let e = parse(&mut cx, "(p + q) * (p + q) - p * p", 32);
    let out = s
        .search(
            &mut cx,
            &[e],
            SearchRun {
                deadline: Some(Deadline {
                    clock: &Late,
                    at: 0,
                    check_every: 50,
                }),
                ..SearchRun::default()
            },
        )
        .unwrap();
    assert_eq!(out.roots[0].end, RootEnd::Stopped(Exhausted::Deadline));
    assert!(out.stats.work <= 50);
}

#[test]
fn a_shared_allowance_is_never_overrun() {
    let s = sat();
    let mut allowance = Allowance::new(Budget {
        eqsat_nodes: 10,
        ..Budget::UNLIMITED
    });
    for i in 0..100 {
        let mut cx = Context::new();
        let e = parse(&mut cx, &format!("x * (y + {i}) - x * y"), 32);
        s.search(
            &mut cx,
            &[e],
            SearchRun {
                allowance: Some(&mut allowance),
                per_call: Some(Budget::UNLIMITED),
                ..SearchRun::default()
            },
        )
        .unwrap();
    }
    assert!(
        allowance.spent().eqsat_nodes <= 10,
        "{:?}",
        allowance.spent()
    );
}

#[test]
fn extreme_node_caps_and_the_dag_admission_cap() {
    // No overflow at the largest cap, and candidates are still found.
    let (s, _) = Saturator::builtin_groups(
        GROUPS,
        SaturateConfig {
            max_root_nodes: u32::MAX,
            ..SaturateConfig::default()
        },
    );
    let mut cx = Context::new();
    let e = parse(&mut cx, "x * (y + 1) - x * y", 32);
    let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].candidate, Some(parse(&mut cx, "x", 32)));
    // `Admission::max_root_dag_size` bounds the distinct nodes.
    let (s, _) = Saturator::builtin_groups(
        GROUPS,
        SaturateConfig {
            admission: Admission {
                max_root_dag_size: Some(2),
                ..Admission::default()
            },
            ..SaturateConfig::default()
        },
    );
    let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].end, RootEnd::DeclinedAdmission(Cap::DagSize));
    assert_eq!(out.stats.enodes, 0);
}

#[test]
fn matching_stops_at_its_limit() {
    use super::egraph::{EGraph, ENode, EOp};
    use super::pattern::{PNode, Pattern, ematch};
    // A class holding every sum `a_i + a_j` of 10 leaves (one class: all united), and a root
    // `X + X`: the pattern `(x + y) + (z + t)` has 200 × 200 matches at the root.
    let mut m = Meter::new(Budget::UNLIMITED, None);
    let mut eg = EGraph::new();
    let leaf = |eg: &mut EGraph, m: &mut Meter<'_>, k: u32| {
        let n = ENode {
            op: EOp::Leaf(k),
            kids: [0, 0],
        };
        eg.add(n, true, m).unwrap()
    };
    let leaves: Vec<_> = (0..10).map(|k| leaf(&mut eg, &mut m, k)).collect();
    let mut sums = Vec::new();
    for &a in &leaves {
        for &b in &leaves {
            let n = ENode {
                op: EOp::Bin(BinOp::Add),
                kids: [a, b],
            };
            sums.push(eg.add(n, true, &mut m).unwrap());
        }
    }
    for &c in &sums[1..] {
        eg.union(sums[0], c, &mut m).unwrap();
    }
    eg.rebuild(&mut m).unwrap();
    let x = eg.find(sums[0]);
    let root = eg
        .add(
            ENode {
                op: EOp::Bin(BinOp::Add),
                kids: [x, x],
            },
            true,
            &mut m,
        )
        .unwrap();
    let p = Pattern {
        nodes: vec![
            PNode::Var(0),
            PNode::Var(1),
            PNode::Bin(BinOp::Add, 0, 1),
            PNode::Var(2),
            PNode::Var(3),
            PNode::Bin(BinOp::Add, 3, 4),
            PNode::Bin(BinOp::Add, 2, 5),
        ],
        root: 6,
    };
    let work = |limit: usize| {
        let mut m = Meter::new(Budget::UNLIMITED, None);
        let mut out = Vec::new();
        ematch(
            &mut eg.clone(),
            &p,
            4,
            root,
            Width::W8,
            &mut out,
            limit,
            &mut |_, _| false,
            &mut m,
        )
        .unwrap();
        (out.len(), m.spent.eqsat_work)
    };
    let (n_all, w_all) = work(usize::MAX);
    assert!(n_all >= 10_000, "{n_all}");
    let (n, w) = work(3);
    assert_eq!(n, 3);
    assert!(w * 100 < w_all, "{w} vs {w_all}");
}

#[test]
fn each_root_ends_exactly_once_in_the_statistics() {
    // A small search, so that every budget up to its end is tried (some stop in extraction).
    let (s, _) = Saturator::builtin_groups(
        &["eqsat.distrib", "eqsat.cancel"],
        SaturateConfig::default(),
    );
    for work in 1..1000 {
        let mut cx = Context::new();
        let e = parse(&mut cx, "x * (y + 1) - x * y", 32);
        let out = s
            .search(
                &mut cx,
                &[e],
                SearchRun {
                    per_call: Some(Budget {
                        eqsat_work: work,
                        ..Budget::UNLIMITED
                    }),
                    ..SearchRun::default()
                },
            )
            .unwrap();
        let st = &out.stats;
        let ends = st.saturated
            + st.iteration_capped
            + st.budget_terminated
            + st.declined_admission
            + st.declined_unsupported;
        assert_eq!(ends, 1, "budget {work}: {st:?}");
    }
}

#[test]
fn applied_matches_do_not_fill_the_window() {
    // Associativity over five and six terms saturates; the applied matches of one class used
    // to fill the matcher's window every iteration, so it never looked saturated.
    for (src, per_iter) in [
        ("v0 + v1 + v2 + v3 + v4", 16),
        ("v0 + v1 + v2 + v3 + v4 + v5", 1024),
    ] {
        let (s, _) = Saturator::builtin_groups(
            &["eqsat.assoc"],
            SaturateConfig::default()
                .with_iterations(64)
                .with_matches_per_rule_iter(per_iter),
        );
        let mut cx = Context::new();
        let e = parse(&mut cx, src, 32);
        let out = s
            .search(
                &mut cx,
                &[e],
                SearchRun::default().with_per_call(Budget::UNLIMITED),
            )
            .unwrap();
        assert_eq!(
            out.roots[0].end,
            RootEnd::Saturated,
            "{src}: {:?}",
            out.stats
        );
    }
}

#[test]
fn a_passed_deadline_withholds_memo_answers_too() {
    let s = sat();
    let mut cx = Context::new();
    let e = parse(&mut cx, "x * (y + 1) - x * y", 32);
    let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out.publication, Publication::Published);
    let out = s
        .search(
            &mut cx,
            &[e],
            SearchRun::default().with_deadline(Deadline::new(&Late, 0)),
        )
        .unwrap();
    assert!(matches!(out.publication, Publication::Withheld { .. }));
    assert_eq!(out.roots[0].candidate, None);
    // Nothing was searched: the answer is still in the memo.
    let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out.stats.memo_hits, 1);
    assert!(out.roots[0].candidate.is_some());
}
