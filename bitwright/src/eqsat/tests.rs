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
    let mut eg = EGraph::new(Width::W8);
    let leaf = |eg: &mut EGraph, i: u32, m: &mut Meter<'_>| {
        eg.add(
            ENode {
                op: EOp::Leaf { node: i, width: 8 },
                kids: [0, 0, 0],
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
                kids: [x, 0, 0],
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
                kids: [y, 0, 0],
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
    let one_node = eg.const_node(BitVec::one(Width::W8));
    let one = eg.add(one_node, true, &mut meter).ok().unwrap();
    let two_node = eg.const_node(BitVec::from_u64(Width::W8, 2).unwrap());
    let two = eg.add(two_node, true, &mut meter).ok().unwrap();
    assert!(matches!(
        eg.union(one, two, &mut meter),
        Err(Halt::Contract)
    ));
}

#[test]
fn extraction_propagates_costs_without_changing_selected_nodes() {
    let mut meter = Meter::new(Budget::UNLIMITED, None);
    let mut eg = EGraph::new(Width::W8);
    let add = |eg: &mut EGraph, op, kid, meter: &mut Meter<'_>| {
        eg.add(
            ENode {
                op,
                kids: [kid, 0, 0],
            },
            true,
            meter,
        )
        .ok()
        .unwrap()
    };
    let x = add(&mut eg, EOp::Leaf { node: 0, width: 8 }, 0, &mut meter);
    let mut expensive = x;
    for _ in 0..4 {
        expensive = add(&mut eg, EOp::Un(UnOp::Neg), expensive, &mut meter);
    }
    let parent = add(&mut eg, EOp::Un(UnOp::Not), expensive, &mut meter);
    let root_index = eg.nodes.len() as u32;
    let root = add(&mut eg, EOp::Un(UnOp::Neg), parent, &mut meter);
    // This cheaper representative is visited after the original parents in each scan.
    let late = add(&mut eg, EOp::Leaf { node: 1, width: 8 }, 0, &mut meter);
    let mut alternative = x;
    for op in [UnOp::Not, UnOp::Neg, UnOp::Not] {
        alternative = add(&mut eg, EOp::Un(op), alternative, &mut meter);
    }
    eg.union(expensive, late, &mut meter).ok().unwrap();
    eg.union(root, alternative, &mut meter).ok().unwrap();
    eg.rebuild(&mut meter).ok().unwrap();
    let best = extract::costs(&mut eg, &mut meter).ok().unwrap();
    assert_eq!(best[&eg.find(parent)].0, 2);
    assert_eq!(best[&eg.find(root)], (3, root_index));
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
    use super::pattern::{PNode, POp, Pattern, ematch};
    use crate::rules::WExpr;
    // A class holding every sum `a_i + a_j` of 10 leaves (one class: all united), and a root
    // `X + X`: the pattern `(x + y) + (z + t)` has 200 × 200 matches at the root.
    let mut m = Meter::new(Budget::UNLIMITED, None);
    let mut eg = EGraph::new(Width::W32);
    let leaf = |eg: &mut EGraph, m: &mut Meter<'_>, k: u32| {
        let n = ENode {
            op: EOp::Leaf { node: k, width: 32 },
            kids: [0, 0, 0],
        };
        eg.add(n, true, m).unwrap()
    };
    let leaves: Vec<_> = (0..10).map(|k| leaf(&mut eg, &mut m, k)).collect();
    let mut sums = Vec::new();
    for &a in &leaves {
        for &b in &leaves {
            let n = ENode {
                op: EOp::Bin(BinOp::Add),
                kids: [a, b, 0],
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
                kids: [x, x, 0],
            },
            true,
            &mut m,
        )
        .unwrap();
    let wv = WExpr::var(0);
    let pn = |op: POp| PNode {
        op,
        width: wv.clone(),
    };
    let p = Pattern {
        nodes: vec![
            pn(POp::Var(0)),
            pn(POp::Var(1)),
            pn(POp::Bin(BinOp::Add, 0, 1)),
            pn(POp::Var(2)),
            pn(POp::Var(3)),
            pn(POp::Bin(BinOp::Add, 3, 4)),
            pn(POp::Bin(BinOp::Add, 2, 5)),
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
            Width::W32,
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

#[test]
fn mixed_width_casts_and_wide_vectors_saturate() {
    let cfg = SaturateConfig::extended();
    let (s, report) = Saturator::builtin_groups(
        &[
            "eqsat.casts",
            "eqsat.distrib_and",
            "eqsat.distrib",
            "eqsat.cancel",
        ],
        cfg,
    );
    assert!(report.refused.is_empty(), "{:?}", report.refused);
    let mut cx = Context::new();
    // Mixed-width `zext` + `distrib_and` factoring across widths 8 -> 16 and 31 -> 63.
    let e16 = parse(
        &mut cx,
        "(zext<16>(a:8) & zext<16>(b:8)) | (zext<16>(a:8) & zext<16>(c:8))",
        16,
    );
    let want16 = parse(&mut cx, "zext<16>(a:8 & (b:8 | c:8))", 16);
    let out = s.search(&mut cx, &[e16], SearchRun::default()).unwrap();
    assert_eq!(out.publication, Publication::Published);
    assert_eq!(out.roots[0].candidate, Some(want16));

    let e63 = parse(
        &mut cx,
        "(sext<63>(a31:31) & sext<63>(b31:31)) | (sext<63>(a31:31) & sext<63>(c31:31))",
        63,
    );
    let want63 = parse(&mut cx, "sext<63>(a31:31 & (b31:31 | c31:31))", 63);
    let out = s.search(&mut cx, &[e63], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].candidate, Some(want63));

    // 256-bit `concat` XOR cancellation and 512-bit ring expansion-before-cancellation.
    let e256 = parse(
        &mut cx,
        "concat(a128:128 ^ c128:128, b128:128 ^ d128:128) ^ concat(c128:128, d128:128)",
        256,
    );
    let want256 = parse(&mut cx, "concat(a128:128, b128:128)", 256);
    let out = s.search(&mut cx, &[e256], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].candidate, Some(want256));

    let e512 = parse(&mut cx, "x512 * (y512 + 1) - x512 * y512", 512);
    let want512 = parse(&mut cx, "x512", 512);
    let out = s.search(&mut cx, &[e512], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].candidate, Some(want512));

    // Narrow extract through widened XOR cancels inside the mixed-width e-graph.
    let e_trunc = parse(&mut cx, "trunc<8>(zext<32>(p:8) ^ zext<32>(q:8)) ^ q:8", 8);
    let want_trunc = parse(&mut cx, "p:8", 8);
    let out = s.search(&mut cx, &[e_trunc], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].candidate, Some(want_trunc));
}

#[test]
fn facts_guarded_identities_and_disjoint_detours() {
    let cfg = SaturateConfig::extended();
    let (s, report) =
        Saturator::builtin_groups(&["eqsat.facts", "eqsat.distrib", "eqsat.cancel"], cfg);
    assert!(report.refused.is_empty(), "{:?}", report.refused);

    for w in [8u16, 32, 64, 128, 256, 512] {
        let mut cx = Context::new();
        // Needs `x | y => x + y` under `disjoint(x, y)` (from e-class `Facts`), then `mul_add`,
        // then `add_sub` cancellation.
        let e = parse(&mut cx, "((a & 0xf0) | (b & 0x0f)) * z - (a & 0xf0) * z", w);
        let want = parse(&mut cx, "(b & 0x0f) * z", w);
        let out = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
        assert_eq!(out.roots[0].candidate, Some(want), "W={w}");

        // Structural complement-mask disjointness `(a & m)` vs `(b & ~m)` for symbolic `m`.
        let e_sym = parse(&mut cx, "((a & m) | (b & ~m)) - (b & ~m)", w);
        let want_sym = parse(&mut cx, "a & m", w);
        let out_sym = s.search(&mut cx, &[e_sym], SearchRun::default()).unwrap();
        assert_eq!(out_sym.roots[0].candidate, Some(want_sym), "symbolic W={w}");

        // `nonzero(x)` proved by e-class `Facts` on `x | 1`.
        let e_div = parse(&mut cx, "udiv(x | 1, x | 1)", w);
        let out_div = s.search(&mut cx, &[e_div], SearchRun::default()).unwrap();
        assert_eq!(
            out_div.roots[0].candidate,
            Some(parse(&mut cx, "1", w)),
            "udiv W={w}"
        );
    }

    // Host-declared `KnownBits` on symbols flow into e-class `Facts`.
    let mut cx = Context::new();
    let a = cx.symbol("a", Width::W16).unwrap();
    let b = cx.symbol("b", Width::W16).unwrap();
    cx.declare_known(
        a,
        crate::KnownBits::from_masks(
            BitVec::from_u64(Width::W16, 0xff00).unwrap(),
            BitVec::zero(Width::W16),
        ),
    )
    .unwrap();
    cx.declare_known(
        b,
        crate::KnownBits::from_masks(
            BitVec::from_u64(Width::W16, 0x00ff).unwrap(),
            BitVec::zero(Width::W16),
        ),
    )
    .unwrap();
    let e_decl = parse(&mut cx, "(a | b) - b", 16);
    let out_decl = s.search(&mut cx, &[e_decl], SearchRun::default()).unwrap();
    assert_eq!(out_decl.roots[0].candidate, Some(a));

    // Negative soundness checks: overlapping masks (`0xf0 & 0x1f == 0x10 != 0`) and potentially
    // zero divisors (`udiv(x, x)`) must NOT fire guarded rules.
    let mut cx = Context::new();
    let bad_overlap = parse(&mut cx, "((a & 0xf0) | (b & 0x1f)) - (b & 0x1f)", 8);
    let out_bad = s
        .search(&mut cx, &[bad_overlap], SearchRun::default())
        .unwrap();
    assert_eq!(out_bad.roots[0].candidate, None);

    let bad_div = parse(&mut cx, "udiv(x, x)", 8);
    let out_bad_div = s.search(&mut cx, &[bad_div], SearchRun::default()).unwrap();
    assert_eq!(out_bad_div.roots[0].candidate, None);
}

#[test]
fn select_and_shift_detours_and_publish_policy() {
    let cfg = SaturateConfig::extended();
    let (s_sel, _) = Saturator::builtin_groups(&["eqsat.select", "eqsat.cancel"], cfg);
    let mut cx = Context::new();
    let e = parse(&mut cx, "select(c:1, x + k, y + k) - k", 64);
    let want = parse(&mut cx, "select(c:1, x, y)", 64);
    let out = s_sel.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out.roots[0].candidate, Some(want));

    let (s_sh, _) = Saturator::builtin_groups(&["eqsat.shifts", "eqsat.cancel"], cfg);
    let e_sh = parse(&mut cx, "(x << s) + (y << s)", 128);
    let want_sh = parse(&mut cx, "(x + y) << s", 128);
    let out_sh = s_sh.search(&mut cx, &[e_sh], SearchRun::default()).unwrap();
    assert_eq!(out_sh.roots[0].candidate, Some(want_sh));

    // `PublishPolicy::AtIterationCap` publishes strictly cheaper verified candidates even when
    // mutually-expanding groups hit `RootEnd::IterationCap`, while deadlines still withhold.
    let (s_cap, _) = Saturator::builtin_groups(
        &["eqsat.distrib_and", "eqsat.distrib_or"],
        SaturateConfig::default().with_publish(PublishPolicy::AtIterationCap),
    );
    let a = parse(&mut cx, "a & b | a & c", 32);
    let b = parse(&mut cx, "(p | q) & (p | r)", 32);
    let out_cap = s_cap
        .search(&mut cx, &[a, b], SearchRun::default())
        .unwrap();
    assert_eq!(out_cap.roots[0].end, RootEnd::IterationCap);
    assert_eq!(out_cap.roots[1].end, RootEnd::IterationCap);
    assert_eq!(out_cap.publication, Publication::Published);
    assert_eq!(
        out_cap.roots[0].candidate,
        Some(parse(&mut cx, "a & (b | c)", 32))
    );
    assert_eq!(
        out_cap.roots[1].candidate,
        Some(parse(&mut cx, "p | (q & r)", 32))
    );

    // Passed deadline still withholds under `PublishPolicy::AtIterationCap`.
    let out_late = s_cap
        .search(
            &mut cx,
            &[a],
            SearchRun::default().with_deadline(Deadline::new(&Late, 0)),
        )
        .unwrap();
    assert!(matches!(out_late.publication, Publication::Withheld { .. }));
    assert_eq!(out_late.roots[0].candidate, None);
}

#[test]
fn dag_extraction_exploits_intra_root_and_batch_sharing() {
    // 1. Intra-root shared subterm: for `t = a + b + c` (5 DAG nodes), `t * (t + 1)` has tree size
    //    13 and DAG size 8, whereas `(t * t) + t` has larger tree size (17) but smaller DAG size
    //    (7, reusing `t` three times without `1` or `t + 1`).
    let (s_dist, _) = Saturator::builtin_groups(
        &["eqsat.distrib", "eqsat.cancel"],
        SaturateConfig::default(),
    );
    let mut cx = Context::new();
    let e = parse(&mut cx, "(a + b + c) * ((a + b + c) + 1)", 32);
    let want_dag = parse(&mut cx, "(a + b + c) * (a + b + c) + (a + b + c)", 32);

    // Tree mode keeps `t * (t + 1)`.
    let out_tree = s_dist.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out_tree.roots[0].candidate, None);

    // DAG mode (on the same context — testing memo isolation across cost models too!) extracts
    // `(t * t) + t`, shrinking the DAG from 8 to 7 nodes.
    let out_dag = s_dist
        .search(
            &mut cx,
            &[e],
            SearchRun::default().with_cost_model(CostModel::dag_size()),
        )
        .unwrap();
    assert_eq!(out_dag.publication, Publication::Published);
    assert_eq!(out_dag.roots[0].candidate, Some(want_dag));
    assert_eq!(
        cx.dag_size(&[want_dag], 64).unwrap(),
        crate::Bounded::Exact(7)
    );
    assert_eq!(cx.dag_size(&[e], 64).unwrap(), crate::Bounded::Exact(8));

    // Re-running default tree mode does not read the DAG-mode memo entry.
    let out_tree_again = s_dist.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out_tree_again.roots[0].candidate, None);

    // 2. Coordinate-descent reassociation within one root: `((x + y) + z) * (y + z)` (7 DAG nodes,
    //    tree size 9) reassociates to `(x + (y + z)) * (y + z)` (6 DAG nodes, sharing `y + z`).
    let (s_assoc, _) = Saturator::builtin_groups(&["eqsat.assoc"], SaturateConfig::default());
    let mut cx = Context::new();
    let e_reassoc = parse(&mut cx, "((x + y) + z) * (y + z)", 32);
    let want_reassoc = parse(&mut cx, "(x + (y + z)) * (y + z)", 32);
    assert_eq!(
        s_assoc
            .search(&mut cx, &[e_reassoc], SearchRun::default())
            .unwrap()
            .roots[0]
            .candidate,
        None
    );
    let out_reassoc = s_assoc
        .search(
            &mut cx,
            &[e_reassoc],
            SearchRun::default()
                .with_cost_model(CostModel::ast_size().with_mode(ExtractionMode::Dag)),
        )
        .unwrap();
    assert_eq!(out_reassoc.roots[0].candidate, Some(want_reassoc));

    // 3. Multi-root batch sharing: `[(x + y) + z, y + z]` reassociates the first root to
    //    `x + (y + z)` so `y + z` is shared across the batch (5 total DAG nodes instead of 6).
    let mut cx = Context::new();
    let r0 = parse(&mut cx, "(x + y) + z", 32);
    let r1 = parse(&mut cx, "y + z", 32);
    let want_r0 = parse(&mut cx, "x + (y + z)", 32);
    let out_batch = s_assoc
        .search(
            &mut cx,
            &[r0, r1],
            SearchRun::default().with_cost_model(CostModel::dag_size()),
        )
        .unwrap();
    assert_eq!(out_batch.publication, Publication::Published);
    assert_eq!(out_batch.roots[0].candidate, Some(want_r0));
    assert_eq!(out_batch.roots[1].candidate, None);
}

#[cfg(feature = "check")]
#[test]
fn custom_cost_model_guides_extraction_and_clamps_zero_weights() {
    let (p, l) = program_with_ledger(
        "bitwright 1;
        group host_cost {
            #[allow(BW0407)]
            identity mul_nine<W>(x: W) where W >= 4 { x * 9 <=> (x << 3) + x }
        }",
    );
    let (s, rep) = Saturator::new(&[(&p, &l)], &[], SaturateConfig::extended()).unwrap();
    assert_eq!(rep.admitted, ["host_cost::mul_nine"]);

    let mut cx = Context::new();
    let e = parse(&mut cx, "x * 9", 32);
    let shifted = parse(&mut cx, "(x << 3) + x", 32);

    // Under default `ast_size`, `x * 9` (3 nodes) is smaller than `(x << 3) + x` (5 nodes).
    let out_default = s.search(&mut cx, &[e], SearchRun::default()).unwrap();
    assert_eq!(out_default.roots[0].candidate, None);

    // Host-supplied custom cost model penalizing `Mul` (and returning 0 for constants/symbols to
    // verify `0 -> 1` clamping keeps extraction cycle-safe) selects `(x << 3) + x`.
    let custom = CostModel::custom(|op, _w| match op {
        CostOp::Const | CostOp::Symbol => 0,
        CostOp::Bin(BinOp::Mul) => 10,
        _ => 1,
    });
    assert_eq!(custom.cost(CostOp::Const, Width::W32), 1);
    let s_custom = s.clone().with_cost_model(custom);
    let out_custom = s_custom
        .search(&mut cx, &[e], SearchRun::default())
        .unwrap();
    assert_eq!(out_custom.roots[0].candidate, Some(shifted));
}
