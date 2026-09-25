//! Arena tests: construction soundness against the independent reference evaluator,
//! canonical-form invariants, order independence, deep graphs, text round trips.

use std::collections::HashMap;

use super::*;
use crate::text::{ParseOptions, PrintOptions};
use crate::{BinOp, CmpOpExt, UnOp};
use bitwright_ref as r;

use crate::testutil::{Gen, Rng, ref_bin, ref_cmp, ref_un, width};

/// Checks `e` against the reference term on every assignment (or 256 random ones).
fn check_equivalent(cx: &mut Context, g: &mut Gen, e: Expr, t: &r::Term) {
    let total_bits: u32 = g.vars.iter().map(|(_, w)| u32::from(*w)).sum();
    let exhaustive = total_bits <= 12;
    let rounds = if exhaustive { 1u64 << total_bits } else { 256 };
    for k in 0..rounds {
        let mut env = HashMap::new();
        let mut renv = Vec::new();
        let mut bits = k;
        for (name, w) in g.vars.clone() {
            let v = if exhaustive {
                let v = bits & ((1u64 << w) - 1);
                bits >>= w;
                v
            } else {
                g.rng.next()
            };
            let bv = BitVec::wrapping_from_u64(width(w), v);
            env.insert(SymbolKey::from(name.as_str()), bv);
            renv.push(r::Bits::from_limbs(w, bv.limbs()));
        }
        let got = cx.eval(&[e], &env).unwrap()[0];
        let want = t.eval(&renv).expect("valid term");
        assert_eq!(
            got.limbs(),
            &want.to_limbs()[..],
            "{} (term {t:?}) env {env:?}",
            cx.display(e)
        );
    }
}

// ----- construction soundness -----------------------------------------------------------------

#[test]
fn construction_is_sound_against_the_reference() {
    let mut rng_seed = 0x5eed_1000;
    for round in 0..600 {
        rng_seed += 1;
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(rng_seed),
            max_w: 6,
            vars: Vec::new(),
        };
        let w = 1 + g.rng.below(6) as u16;
        let depth = 1 + (round % 5);
        let (e, t) = g.expr(&mut cx, w, depth);
        check_equivalent(&mut cx, &mut g, e, &t);
    }
}

#[test]
fn construction_is_sound_at_wide_widths() {
    for seed in 0..80 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0xabc0 + seed),
            max_w: 130,
            vars: Vec::new(),
        };
        let w = [1, 8, 63, 64, 65, 127, 128, 129, 130][seed as usize % 9];
        let (e, t) = g.expr(&mut cx, w, 3);
        // Random assignments only; widths are too large to enumerate.
        let mut env = HashMap::new();
        let mut renv = Vec::new();
        for _ in 0..32 {
            env.clear();
            renv.clear();
            for (name, vw) in g.vars.clone() {
                let limbs: Vec<u64> = (0..3).map(|_| g.rng.next()).collect();
                let bv = BitVec::wrapping_from_limbs(width(vw), &limbs);
                env.insert(SymbolKey::from(name.as_str()), bv);
                renv.push(r::Bits::from_limbs(vw, bv.limbs()));
            }
            let got = cx.eval(&[e], &env).unwrap()[0];
            let want = t.eval(&renv).expect("valid term");
            assert_eq!(got.limbs(), &want.to_limbs()[..], "{}", cx.display(e));
        }
    }
}

// ----- canonical-form invariants --------------------------------------------------------------

fn random_arena(seed: u64, trees: usize) -> (Context, Vec<Expr>) {
    let mut cx = Context::new();
    let mut g = Gen {
        rng: Rng(seed),
        max_w: 8,
        vars: Vec::new(),
    };
    let mut roots = Vec::new();
    for k in 0..trees {
        let w = 1 + g.rng.below(8) as u16;
        roots.push(g.expr(&mut cx, w, 1 + (k % 5) as u32).0);
    }
    (cx, roots)
}

#[test]
fn stored_nodes_are_canonical_fixed_points() {
    let (mut cx, _) = random_arena(42, 400);
    let n = cx.len() as u32;
    for i in 0..n {
        let node = cx.node(i);
        for c in node.children() {
            assert!(c < i, "child index must be lower than parent");
        }
        if let Some(op) = node.op.as_bin() {
            if op.is_commutative() {
                assert!(
                    cx.order(node.a, node.b).is_le(),
                    "commutative operands in order"
                );
                assert!(cx.const_val(node.a).is_none(), "constant on the left");
            }
            assert!(
                !(cx.const_val(node.a).is_some() && cx.const_val(node.b).is_some()),
                "unfolded constant operation"
            );
            if op == BinOp::Sub {
                assert!(cx.const_val(node.b).is_none(), "x - c must be x + (-c)");
            }
        }
        // Rebuilding a canonical node from its own children yields the node itself.
        let rebuilt = cx.rebuild(i, [node.a, node.b, node.c]).unwrap();
        assert_eq!(rebuilt, i, "canonical form is a fixed point of the builder");
    }
}

#[test]
fn commutative_order_is_construction_order_independent() {
    for seed in 0..50 {
        // Build the same random tree twice in fresh contexts that first create symbols and
        // unrelated nodes in different orders, then compare the printed forms.
        let build = |pre: u64, hash_seed: u64| {
            let mut cx = Context::with_config(ContextConfig::default().with_hash_seed(hash_seed));
            let mut junk = Gen {
                rng: Rng(pre),
                max_w: 8,
                vars: Vec::new(),
            };
            for _ in 0..20 {
                let w = 1 + junk.rng.below(8) as u16;
                junk.expr(&mut cx, w, 2);
            }
            let mut g = Gen {
                rng: Rng(seed),
                max_w: 8,
                vars: Vec::new(),
            };
            let w = 1 + g.rng.below(8) as u16;
            let (e, _) = g.expr(&mut cx, w, 4);
            cx.display(e).to_string()
        };
        assert_eq!(build(1, 0), build(2, 0xdead_beef), "seed {seed}");
    }
}

#[test]
fn equal_structure_is_one_node() {
    let mut cx = Context::new();
    let w = Width::W32;
    let x = cx.symbol("x", w).unwrap();
    let y = cx.symbol("y", w).unwrap();
    let a = cx.add(x, y).unwrap();
    let b = cx.add(y, x).unwrap();
    assert_eq!(a, b);
    let c = cx.ugt(x, y).unwrap();
    let d = cx.ult(y, x).unwrap();
    assert_eq!(c, d);
    let five = cx.constant_u64(w, 5).unwrap();
    let s = cx.sub(x, five).unwrap();
    let m5 = cx.constant_i128(w, -5).unwrap();
    let t = cx.add(x, m5).unwrap();
    assert_eq!(s, t);
    let n = cx.len();
    let _ = cx.add(y, x).unwrap();
    assert_eq!(cx.len(), n, "a hit does not grow the arena");
}

// ----- deep graphs ----------------------------------------------------------------------------

#[test]
fn deep_chain_needs_no_recursion() {
    let mut cx = Context::new();
    let w = Width::W64;
    let x = cx.symbol("x", w).unwrap();
    let y = cx.symbol("y", w).unwrap();
    let mut e = x;
    for k in 0..100_000u64 {
        e = if k % 2 == 0 {
            cx.xor(e, y)
        } else {
            cx.mul(e, x)
        }
        .unwrap();
    }
    assert!(cx.height(e).unwrap() >= 100_000);
    assert_eq!(
        cx.dag_size(&[e], u32::MAX).unwrap(),
        Bounded::Exact(100_002)
    );
    assert_eq!(cx.dag_size(&[e], 10).unwrap(), Bounded::AtLeast(11));
    assert_eq!(cx.post_order(&[e]).unwrap().len(), 100_002);
    let env: HashMap<SymbolKey, BitVec> = [
        (SymbolKey::from("x"), BitVec::wrapping_from_u64(w, 3)),
        (SymbolKey::from("y"), BitVec::wrapping_from_u64(w, 5)),
    ]
    .into_iter()
    .collect();
    let v = cx.eval(&[e], &env).unwrap()[0];
    assert!(
        cx.display(e).to_string().ends_with('…'),
        "default budget truncates"
    );
    let unbounded = PrintOptions::default()
        .with_max_nodes(usize::MAX)
        .with_max_chars(usize::MAX);
    let text = cx.display_with(e, unbounded).to_string();
    let back = cx.parse(&text, &ParseOptions::default()).unwrap();
    assert_eq!(back, e, "parse(print(e)) == e on a 100k-deep chain");
    assert_eq!(cx.eval(&[back], &env).unwrap()[0], v);
    let replaced = cx.substitute(&[e], &[(y, x)]).unwrap()[0];
    assert_ne!(replaced, e);
}

#[test]
fn heavy_sharing_prints_linearly() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let mut e = x;
    for _ in 0..60 {
        e = cx.mul(e, e).unwrap(); // tree size 2^60
    }
    assert_eq!(cx.tree_size(e).unwrap(), u32::MAX, "saturates");
    let text = cx.display(e).to_string();
    assert!(
        text.len() < 2_000,
        "DAG-aware printing: {} bytes",
        text.len()
    );
    assert_eq!(cx.parse(&text, &ParseOptions::default()).unwrap(), e);
    let bounded = cx
        .display_with(
            e,
            PrintOptions::default().with_lets(false).with_max_nodes(100),
        )
        .to_string();
    assert!(
        bounded.contains('…'),
        "bounded output is marked as truncated"
    );
}

// ----- text round trip ------------------------------------------------------------------------

#[test]
fn print_parse_round_trip_same_context() {
    let (mut cx, roots) = random_arena(7, 500);
    for e in roots {
        let text = cx.display(e).to_string();
        let back = cx
            .parse(
                &text,
                &ParseOptions::default().with_existing_symbols_only(true),
            )
            .unwrap_or_else(|err| panic!("{text}\n{err}"));
        assert_eq!(back, e, "{text}");
    }
}

#[test]
fn print_parse_round_trip_across_contexts() {
    let (cx, roots) = random_arena(8, 300);
    for e in roots {
        let text = cx
            .display_with(e, PrintOptions::default().with_symbol_widths(true))
            .to_string();
        let mut other = Context::new();
        let back = other
            .parse(&text, &ParseOptions::default())
            .unwrap_or_else(|err| panic!("{text}\n{err}"));
        assert_eq!(
            other.display(back).to_string(),
            cx.display(e).to_string(),
            "{text}"
        );
    }
}

#[test]
fn parse_errors_are_reported_not_panics() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    for bad in [
        "a >> b",
        "a < b",
        "a == b == c",
        "x:8 + y:16",
        "zext<4>(x:8)",
        "select(x:2, a, b)",
        "1 +",
        "(((x)",
        "foo(1)",
        "let = 3; x",
        "0x1:0",
        "0x100:8",
        "x ! y",
        "\"unterminated",
        "trunc<600>(x)",
    ] {
        assert!(cx.parse(bad, &o).is_err(), "{bad}");
    }
    assert!(
        cx.parse("1", &ParseOptions::default()).is_err(),
        "no width to infer"
    );
    let deep = format!("{}x{}", "(".repeat(5_000), ")".repeat(5_000));
    assert!(cx.parse(&deep, &o).is_err(), "nesting is limited");
    let deep_neg = format!("{}x", "-".repeat(5_000));
    assert!(cx.parse(&deep_neg, &o).is_err(), "unary nesting is limited");
}

#[test]
fn parse_examples() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let e = cx.parse("x + 1", &o).unwrap();
    assert_eq!(cx.width(e).unwrap(), Width::W8);
    let c = cx.parse("x:16 <u 3", &ParseOptions::default()).unwrap_err();
    assert!(matches!(c, Error::Syntax(_)), "x already has width 8");
    let z = cx.parse("zext<32>(x) >>s 31", &o).unwrap();
    assert_eq!(cx.width(z).unwrap(), Width::W32);
    let s = cx.parse("let t = x ^ 0x5a; t * t", &o).unwrap();
    assert_eq!(cx.display(s).to_string(), "let %0 = x ^ 90;\n%0 * %0");
    let k = cx.parse("#7:64 + $3:64", &ParseOptions::default()).unwrap();
    assert_eq!(cx.display(k).to_string(), "#7 + $3");
    let q = cx
        .parse("\"weird name\":4 - 1", &ParseOptions::default())
        .unwrap();
    assert_eq!(cx.display(q).to_string(), "\"weird name\" - 1");
    let b = cx
        .parse("select(x == 3, 1:8, 2)", &ParseOptions::default())
        .unwrap();
    assert_eq!(cx.display(b).to_string(), "select(x == 3, 1:8, 2)");
}

// ----- handles, symbols, substitution ---------------------------------------------------------

#[test]
fn stale_and_foreign_handles_are_rejected() {
    let mut a = Context::new();
    let mut b = Context::new();
    let x = a.symbol("x", Width::W8).unwrap();
    assert_eq!(b.width(x), Err(Error::ForeignExpr));
    assert_eq!(b.not(x), Err(Error::ForeignExpr));
    a.clear();
    assert_eq!(a.width(x), Err(Error::StaleExpr));
    let x2 = a.symbol("x", Width::W16).unwrap();
    assert_eq!(a.width(x2), Ok(Width::W16));
}

#[test]
fn handle_bits_round_trip_and_forgeries_are_rejected() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let e = cx.not(x).unwrap();
    assert_ne!(e.to_bits(), 0);
    assert_eq!(Expr::from_bits(e.to_bits()), Some(e));
    assert_eq!(Expr::from_bits(0), None);
    // Past the end of the arena, and with another tag.
    let past = Expr::from_bits(e.to_bits() + 1).unwrap();
    assert_eq!(cx.width(past), Err(Error::ForeignExpr));
    let other = Expr::from_bits(e.to_bits() ^ 1 << 40).unwrap();
    assert_eq!(cx.width(other), Err(Error::ForeignExpr));
}

#[test]
fn symbols_have_one_width() {
    let mut cx = Context::new();
    let x = cx.symbol(7u64, Width::W8).unwrap();
    assert_eq!(cx.symbol(7u64, Width::W8).unwrap(), x);
    assert!(matches!(
        cx.symbol(7u64, Width::W16),
        Err(Error::SymbolWidthConflict { .. })
    ));
    let f1 = cx.fresh_symbol(Width::W8).unwrap();
    let f2 = cx.fresh_symbol(Width::W8).unwrap();
    assert_ne!(f1, f2);
    assert_eq!(cx.find_symbol(&SymbolKey::U64(7)), Some(x));
    assert_eq!(cx.find_symbol(&SymbolKey::U64(8)), None);
}

#[test]
fn substitution_matches_evaluation() {
    for seed in 0..100u64 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0x77 + seed),
            max_w: 6,
            vars: Vec::new(),
        };
        let w = 1 + g.rng.below(6) as u16;
        let (e, _) = g.expr(&mut cx, w, 4);
        // Replace one symbol (if any) with a random expression of its width.
        let syms = cx.symbols_in(&[e]).unwrap();
        let Some(&sid) = syms.first() else { continue };
        let key = cx.symbol_key(sid).unwrap().clone();
        let sw = cx.symbol_width(sid).unwrap();
        let from = cx.find_symbol(&key).unwrap();
        let (to, _) = g.expr(&mut cx, sw.bits(), 2);
        let replaced = cx.substitute(&[e], &[(from, to)]).unwrap()[0];
        for _ in 0..32 {
            let mut env: HashMap<SymbolKey, BitVec> = HashMap::new();
            for (name, vw) in g.vars.clone() {
                env.insert(
                    SymbolKey::from(name.as_str()),
                    BitVec::wrapping_from_u64(width(vw), g.rng.next()),
                );
            }
            let tv = cx.eval(&[to], &env).unwrap()[0];
            let mut env2 = env.clone();
            env2.insert(key.clone(), tv);
            assert_eq!(
                cx.eval(&[replaced], &env).unwrap()[0],
                cx.eval(&[e], &env2).unwrap()[0]
            );
        }
    }
}

#[test]
fn eval_reports_unbound_and_badly_sized_symbols() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let env: HashMap<SymbolKey, BitVec> = HashMap::new();
    assert!(matches!(
        cx.eval(&[x], &env),
        Err(Error::UnboundSymbol { .. })
    ));
    let env: HashMap<SymbolKey, BitVec> = [(SymbolKey::from("x"), BitVec::zero(Width::W16))]
        .into_iter()
        .collect();
    assert!(matches!(cx.eval(&[x], &env), Err(Error::EnvWidth { .. })));
}

#[test]
fn counters_and_marks() {
    let mut cx = Context::new();
    let m = cx.mark();
    let x = cx.symbol("x", Width::W8).unwrap();
    let _ = cx.not(x).unwrap();
    assert_eq!(cx.caller_growth_since(m), 2);
    cx.as_engine(|cx| cx.c_un(UnOp::Neg, 0)).unwrap();
    assert_eq!(cx.caller_growth_since(m), 2);
    assert_eq!(cx.counters().engine_nodes, 1);
}

#[test]
fn arena_limit_is_an_error() {
    let mut cx = Context::with_config(ContextConfig::default().with_max_nodes(3));
    let x = cx.symbol("x", Width::W8).unwrap();
    let y = cx.symbol("y", Width::W8).unwrap();
    let _ = cx.add(x, y).unwrap();
    assert!(matches!(cx.sub(x, y), Err(Error::ArenaFull { limit: 3 })));
}

#[test]
fn traps_describe_faults() {
    let mut cx = Context::new();
    let w = Width::W8;
    let a = cx.symbol("a", w).unwrap();
    let b = cx.symbol("b", w).unwrap();
    let t = crate::traps::sdiv(&mut cx, a, b).unwrap();
    for (av, bv, want) in [(0x80u64, 0xffu64, 1u64), (5, 0, 1), (5, 3, 0), (0x80, 1, 0)] {
        let env: HashMap<SymbolKey, BitVec> = [
            (SymbolKey::from("a"), BitVec::wrapping_from_u64(w, av)),
            (SymbolKey::from("b"), BitVec::wrapping_from_u64(w, bv)),
        ]
        .into_iter()
        .collect();
        assert_eq!(cx.eval(&[t], &env).unwrap()[0].to_u64(), Some(want));
    }
}

// ----- the construction table: every rule, every operand shape --------------------------------

/// A built expression paired with its reference term.
#[derive(Clone)]
struct Atom {
    e: Expr,
    t: r::Term,
}

/// Operand shapes at width `w`: symbols, the special constants, and small composites that the
/// canonicalization rules look through (complement, negation, compares, casts, concat, select).
fn atoms(cx: &mut Context, vars: &mut Vec<(String, u16)>, w: u16) -> Vec<Atom> {
    let mut sym = |cx: &mut Context, name: &str, sw: u16| {
        let full = format!("{name}_{sw}");
        let idx = match vars.iter().position(|(n, _)| *n == full) {
            Some(i) => i,
            None => {
                vars.push((full.clone(), sw));
                vars.len() - 1
            }
        };
        Atom {
            e: cx.symbol(full.as_str(), width(sw)).unwrap(),
            t: r::Term::Var(idx, sw),
        }
    };
    let constant = |cx: &mut Context, v: BitVec| Atom {
        e: cx.constant(&v).unwrap(),
        t: r::Term::Const(r::Bits::from_limbs(v.width().bits(), v.limbs())),
    };
    let ww = width(w);
    let x = sym(cx, "x", w);
    let y = sym(cx, "y", w);
    let mut out = vec![x.clone(), y.clone()];
    for v in [
        BitVec::zero(ww),
        BitVec::one(ww),
        BitVec::ones(ww),
        BitVec::smin(ww),
        BitVec::smax(ww),
        BitVec::wrapping_from_u64(ww, 2),
    ] {
        out.push(constant(cx, v));
    }
    out.push(Atom {
        e: cx.not(x.e).unwrap(),
        t: r::Term::Un(r::UnOp::Not, Box::new(x.t.clone())),
    });
    out.push(Atom {
        e: cx.neg(x.e).unwrap(),
        t: r::Term::Un(r::UnOp::Neg, Box::new(x.t.clone())),
    });
    out.push(Atom {
        e: cx.add(x.e, y.e).unwrap(),
        t: r::Term::Bin(r::BinOp::Add, Box::new(x.t.clone()), Box::new(y.t.clone())),
    });
    if w == 1 {
        let (p, q) = (sym(cx, "p", 2), sym(cx, "q", 2));
        out.push(Atom {
            e: cx.ult(p.e, q.e).unwrap(),
            t: r::Term::Cmp(r::CmpOp::Ult, Box::new(p.t.clone()), Box::new(q.t.clone())),
        });
        out.push(Atom {
            e: cx.eq(p.e, q.e).unwrap(),
            t: r::Term::Cmp(r::CmpOp::Eq, Box::new(p.t), Box::new(q.t)),
        });
    } else {
        let n = sym(cx, "n", w - 1);
        out.push(Atom {
            e: cx.zext(n.e, ww).unwrap(),
            t: r::Term::Zext(Box::new(n.t.clone()), w),
        });
        out.push(Atom {
            e: cx.sext(n.e, ww).unwrap(),
            t: r::Term::Sext(Box::new(n.t.clone()), w),
        });
        let h = sym(cx, "h", 1);
        out.push(Atom {
            e: cx.concat(h.e, n.e).unwrap(),
            t: r::Term::Concat(Box::new(h.t), Box::new(n.t)),
        });
    }
    let wide = sym(cx, "u", w + 2);
    out.push(Atom {
        e: cx.extract(wide.e, 1, ww).unwrap(),
        t: r::Term::Extract(Box::new(wide.t), 1, w),
    });
    let c = sym(cx, "c", 1);
    out.push(Atom {
        e: cx.select(c.e, x.e, y.e).unwrap(),
        t: r::Term::Select(Box::new(c.t), Box::new(x.t), Box::new(y.t)),
    });
    out
}

/// Evaluates `e` against `t` on every assignment of the symbols `e` and `t` mention.
fn check_all_assignments(cx: &mut Context, vars: &[(String, u16)], e: Expr, t: &r::Term) {
    let used: Vec<usize> = {
        let mut u = Vec::new();
        let mut stack = vec![t];
        while let Some(t) = stack.pop() {
            match t {
                r::Term::Var(i, _) => {
                    if !u.contains(i) {
                        u.push(*i);
                    }
                }
                r::Term::Const(_) => {}
                r::Term::Un(_, a)
                | r::Term::Zext(a, _)
                | r::Term::Sext(a, _)
                | r::Term::Extract(a, _, _) => stack.push(a),
                r::Term::Bin(_, a, b) | r::Term::Cmp(_, a, b) | r::Term::Concat(a, b) => {
                    stack.push(a);
                    stack.push(b);
                }
                r::Term::Select(a, b, c) => {
                    stack.push(a);
                    stack.push(b);
                    stack.push(c);
                }
            }
        }
        u
    };
    let bits: u32 = used.iter().map(|&i| u32::from(vars[i].1)).sum();
    assert!(bits <= 20, "too many assignment bits: {bits}");
    for k in 0..(1u64 << bits) {
        let mut rest = k;
        let mut renv: Vec<r::Bits> = vars.iter().map(|(_, w)| r::Bits::zero(*w)).collect();
        let mut env: HashMap<SymbolKey, BitVec> = vars
            .iter()
            .map(|(n, w)| (SymbolKey::from(n.as_str()), BitVec::zero(width(*w))))
            .collect();
        for &i in &used {
            let w = vars[i].1;
            let v = rest & ((1 << w) - 1);
            rest >>= w;
            let bv = BitVec::wrapping_from_u64(width(w), v);
            renv[i] = r::Bits::from_limbs(w, bv.limbs());
            env.insert(SymbolKey::from(vars[i].0.as_str()), bv);
        }
        let got = cx.eval(&[e], &env).unwrap()[0];
        let want = t.eval(&renv).expect("valid term");
        assert_eq!(got.limbs(), &want.to_limbs()[..], "{}", cx.display(e));
    }
}

#[test]
fn construction_table_is_sound() {
    for w in 1..=3u16 {
        let mut cx = Context::new();
        let mut vars = Vec::new();
        let here = atoms(&mut cx, &mut vars, w);
        let bits = atoms(&mut cx, &mut vars, 1);
        let wider = atoms(&mut cx, &mut vars, w + 1);
        for a in &here {
            for op in UnOp::ALL {
                if op == UnOp::Bswap && !w.is_multiple_of(8) {
                    continue;
                }
                let e = cx.un(op, a.e).unwrap();
                check_all_assignments(
                    &mut cx,
                    &vars,
                    e,
                    &r::Term::Un(ref_un(op), Box::new(a.t.clone())),
                );
            }
            for b in &here {
                for op in BinOp::ALL {
                    let e = cx.bin(op, a.e, b.e).unwrap();
                    let t = r::Term::Bin(ref_bin(op), Box::new(a.t.clone()), Box::new(b.t.clone()));
                    check_all_assignments(&mut cx, &vars, e, &t);
                }
                for op in CmpOpExt::ALL {
                    let e = cx.cmp(op, a.e, b.e).unwrap();
                    let t = r::Term::Cmp(ref_cmp(op), Box::new(a.t.clone()), Box::new(b.t.clone()));
                    check_all_assignments(&mut cx, &vars, e, &t);
                }
                for c in &bits {
                    let e = cx.select(c.e, a.e, b.e).unwrap();
                    let t = r::Term::Select(
                        Box::new(c.t.clone()),
                        Box::new(a.t.clone()),
                        Box::new(b.t.clone()),
                    );
                    check_all_assignments(&mut cx, &vars, e, &t);
                }
            }
            // Casts from this width.
            for to in (w + 1)..=(w + 2) {
                let e = cx.zext(a.e, width(to)).unwrap();
                check_all_assignments(&mut cx, &vars, e, &r::Term::Zext(Box::new(a.t.clone()), to));
                let e = cx.sext(a.e, width(to)).unwrap();
                check_all_assignments(&mut cx, &vars, e, &r::Term::Sext(Box::new(a.t.clone()), to));
            }
            for b in &bits {
                let e = cx.concat(a.e, b.e).unwrap();
                check_all_assignments(
                    &mut cx,
                    &vars,
                    e,
                    &r::Term::Concat(Box::new(a.t.clone()), Box::new(b.t.clone())),
                );
                let e = cx.concat(b.e, a.e).unwrap();
                check_all_assignments(
                    &mut cx,
                    &vars,
                    e,
                    &r::Term::Concat(Box::new(b.t.clone()), Box::new(a.t.clone())),
                );
            }
        }
        // Extracts of every range from the wider shapes.
        for a in &wider {
            for lo in 0..=w {
                for len in 1..=(w + 1 - lo) {
                    let e = cx.extract(a.e, lo, width(len)).unwrap();
                    check_all_assignments(
                        &mut cx,
                        &vars,
                        e,
                        &r::Term::Extract(Box::new(a.t.clone()), lo, len),
                    );
                }
            }
        }
    }
}

// ----- regressions from the M1 review ---------------------------------------------------------

#[test]
fn stale_handles_stay_rejected_across_many_clears() {
    let mut a = Context::new();
    let x = a.symbol("x", Width::W8).unwrap();
    for _ in 0..5000 {
        a.clear();
    }
    let _ = a.symbol("y", Width::W64).unwrap();
    assert!(
        a.width(x).is_err(),
        "a handle from 5000 generations ago must not alias"
    );
    // The most recent generations are reported as stale.
    let z = a.symbol("z", Width::W8).unwrap();
    a.clear();
    assert_eq!(a.width(z), Err(Error::StaleExpr));
}

#[test]
fn marks_from_other_contexts_do_not_panic() {
    let mut a = Context::new();
    let mut b = Context::new();
    for i in 0..10u64 {
        a.symbol(i, Width::W8).unwrap();
    }
    let m = a.mark();
    b.symbol(1u64, Width::W8).unwrap();
    assert_eq!(
        b.caller_growth_since(m),
        1,
        "a foreign mark counts everything"
    );
}

#[test]
fn odd_symbol_names_round_trip() {
    let mut cx = Context::new();
    for name in [
        "a\rb",
        "nul\0",
        "e\u{301}",
        "\u{200b}",
        "del\u{7f}",
        "q\"uote",
        "back\\slash",
        "tab\t",
        "ones",
        "bit",
        "proves",
        "rule",
        "x.y",
        "_",
    ] {
        let s = cx.symbol(name, Width::W16).unwrap();
        let one = cx.one(Width::W16).unwrap();
        let e = cx.add(s, one).unwrap();
        let text = cx.display(e).to_string();
        let back = cx
            .parse(&text, &ParseOptions::default())
            .unwrap_or_else(|err| panic!("{name:?}: {text}: {err}"));
        assert_eq!(back, e, "{name:?}: {text}");
    }
}

#[test]
fn parsing_many_lets_is_linear() {
    let mut src = String::new();
    for k in 0..20_000 {
        src.push_str(&format!("let %{k} = a{k} + 1;\n"));
    }
    src.push_str("%19999");
    let mut cx = Context::new();
    let e = cx.parse(&src, &ParseOptions::width(Width::W32)).unwrap();
    assert_eq!(cx.width(e).unwrap(), Width::W32);
}

#[test]
fn full_arena_does_not_leak_constant_limbs() {
    let mut cx = Context::with_config(ContextConfig::default().with_max_nodes(1));
    let x = cx.symbol("x", Width::W512).unwrap();
    let _ = x;
    let before = cx.wide_consts.len();
    for k in 0..100u64 {
        let v = BitVec::wrapping_from_limbs(Width::W512, &[k, 1, 2, 3, 4, 5, 6, 7]);
        assert!(matches!(cx.constant(&v), Err(Error::ArenaFull { .. })));
    }
    assert_eq!(cx.wide_consts.len(), before);
}

#[test]
fn failed_parse_leaves_no_symbols() {
    let mut cx = Context::new();
    assert!(
        cx.parse("zext<8>(q)", &ParseOptions::width(Width::W32))
            .is_err()
    );
    assert_eq!(cx.find_symbol(&SymbolKey::from("q")), None);
    assert!(cx.parse("q + 1", &ParseOptions::width(Width::W8)).is_ok());
}

#[test]
fn negative_literals_are_range_checked() {
    let mut cx = Context::new();
    let o = ParseOptions::default();
    assert!(cx.parse("-129:8", &o).is_err());
    assert!(cx.parse("-255:8", &o).is_err());
    let m = cx.parse("-128:8", &o).unwrap();
    assert_eq!(cx.as_const(m).unwrap(), Some(BitVec::smin(Width::W8)));
    let m1 = cx.parse("-1:8", &o).unwrap();
    assert_eq!(cx.as_const(m1).unwrap(), Some(BitVec::ones(Width::W8)));
    assert!(
        cx.parse("let %0 = 1:8; let %0 = 2:8; %0", &o).is_err(),
        "duplicate let"
    );
}

#[test]
fn printing_is_bounded_and_depth_is_clamped() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let mut e = x;
    for k in 0..200_000u64 {
        let c = cx.constant_u64(Width::W64, k | 1).unwrap();
        e = cx.mul(e, c).unwrap();
    }
    let short = cx
        .display_with(e, PrintOptions::default().with_max_nodes(10))
        .to_string();
    assert!(short.len() < 400 && short.contains('…'), "{short}");
    let mut deep = PrintOptions::default()
        .with_max_nodes(usize::MAX)
        .with_max_chars(usize::MAX);
    deep.max_depth = 1000;
    let text = cx.display_with(e, deep).to_string();
    assert_eq!(cx.parse(&text, &ParseOptions::default()).unwrap(), e);
}

#[test]
fn duplicate_substitution_is_an_error() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let y = cx.symbol("y", Width::W8).unwrap();
    let z = cx.symbol("z", Width::W8).unwrap();
    let e = cx.add(x, y).unwrap();
    assert_eq!(
        cx.substitute(&[e], &[(x, y), (x, z)]),
        Err(Error::DuplicateSubstitution)
    );
}

// ----- derived constructors, guards, limits and bounded substitution ----------------------------

/// Every derived constructor against its definition, at every value pair of widths 1 to 5.
#[test]
fn derived_constructors_are_exact() {
    let (s, u) = (
        |v: u64, w: u16| -> i64 { ((v << (64 - w)) as i64) >> (64 - w) },
        |v: i64, w: u16| -> u64 { (v as u64) & ((1u64 << w) - 1) },
    );
    for w in 1..=5u16 {
        let width = width(w);
        let (max, smin, smax) = ((1u64 << w) - 1, -(1i64 << (w - 1)), (1i64 << (w - 1)) - 1);
        let mut cx = Context::new();
        let a = cx.symbol("a", width).unwrap();
        let b = cx.symbol("b", width).unwrap();
        type Ctor = fn(&mut Context, Expr, Expr) -> Result<Expr, Error>;
        type Spec = Box<dyn Fn(u64, u64) -> u64>;
        let cases: Vec<(&str, Ctor, Spec)> = vec![
            ("umin", Context::umin, Box::new(|x, y| x.min(y))),
            ("umax", Context::umax, Box::new(|x, y| x.max(y))),
            (
                "smin",
                Context::smin,
                Box::new(move |x, y| u(s(x, w).min(s(y, w)), w)),
            ),
            (
                "smax",
                Context::smax,
                Box::new(move |x, y| u(s(x, w).max(s(y, w)), w)),
            ),
            ("andn", Context::andn, Box::new(move |x, y| x & !y & max)),
            ("orn", Context::orn, Box::new(move |x, y| (x | !y) & max)),
            ("xnor", Context::xnor, Box::new(move |x, y| !(x ^ y) & max)),
            (
                "add_carry",
                Context::add_carry,
                Box::new(move |x, y| (x + y > max) as u64),
            ),
            (
                "sub_borrow",
                Context::sub_borrow,
                Box::new(|x, y| (x < y) as u64),
            ),
            (
                "sadd_overflow",
                Context::sadd_overflow,
                Box::new(move |x, y| {
                    let r = s(x, w) + s(y, w);
                    (r < smin || r > smax) as u64
                }),
            ),
            (
                "ssub_overflow",
                Context::ssub_overflow,
                Box::new(move |x, y| {
                    let r = s(x, w) - s(y, w);
                    (r < smin || r > smax) as u64
                }),
            ),
            (
                "add_sat_u",
                Context::add_sat_u,
                Box::new(move |x, y| (x + y).min(max)),
            ),
            (
                "sub_sat_u",
                Context::sub_sat_u,
                Box::new(|x, y| x.saturating_sub(y)),
            ),
            (
                "add_sat_s",
                Context::add_sat_s,
                Box::new(move |x, y| u((s(x, w) + s(y, w)).clamp(smin, smax), w)),
            ),
            (
                "sub_sat_s",
                Context::sub_sat_s,
                Box::new(move |x, y| u((s(x, w) - s(y, w)).clamp(smin, smax), w)),
            ),
        ];
        for (name, ctor, spec) in &cases {
            let e = ctor(&mut cx, a, b).unwrap();
            // Parsing the name builds the same node.
            let parsed = cx
                .parse(&format!("{name}(a, b)"), &ParseOptions::width(width))
                .unwrap();
            assert_eq!(parsed, e, "{name} at {w}");
            for x in 0..=max {
                for y in 0..=max {
                    let env: HashMap<SymbolKey, BitVec> = [
                        (SymbolKey::from("a"), BitVec::wrapping_from_u64(width, x)),
                        (SymbolKey::from("b"), BitVec::wrapping_from_u64(width, y)),
                    ]
                    .into_iter()
                    .collect();
                    let got = cx.eval(&[e], &env).unwrap()[0].to_u64().unwrap();
                    assert_eq!(got, spec(x, y), "{name}({x}, {y}) at {w}");
                }
            }
        }
    }
}

#[test]
fn shift_and_rotate_guards_are_count_out_of_range() {
    for w in [1u16, 3, 8, 13, 64, 512] {
        let width = width(w);
        let mut cx = Context::new();
        let c = cx.symbol("c", width).unwrap();
        for t in [
            crate::traps::shift(&mut cx, c).unwrap(),
            crate::traps::rotate(&mut cx, c).unwrap(),
        ] {
            for v in [
                0u64,
                1,
                u64::from(w) - 1,
                u64::from(w),
                u64::from(w) + 1,
                u64::MAX,
            ] {
                let cv = BitVec::wrapping_from_u64(width, v);
                let env: HashMap<SymbolKey, BitVec> =
                    [(SymbolKey::from("c"), cv)].into_iter().collect();
                let want = cv.to_u64().is_none_or(|v| v >= u64::from(w));
                let got = !cx.eval(&[t], &env).unwrap()[0].is_zero();
                assert_eq!(got, want, "count {cv} at {w}");
            }
        }
    }
}

#[test]
fn the_node_limit_can_change_at_run_time() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let y = cx.symbol("y", Width::W8).unwrap();
    let s = cx.add(x, y).unwrap();
    cx.set_max_nodes(1);
    // Existing structure is found without creating anything.
    assert_eq!(cx.add(y, x).unwrap(), s);
    assert!(matches!(cx.sub(x, y), Err(Error::ArenaFull { limit: 1 })));
    cx.set_max_nodes(100);
    assert!(cx.sub(x, y).is_ok());
}

#[test]
fn bounded_substitution_matches_substitution_and_resumes() {
    for seed in 0..200u64 {
        let (mut cx, roots) = random_arena(0x5b57_0000 + seed, 3);
        let all = cx.post_order(&roots).unwrap();
        // Replace a few inner nodes by fresh symbols of their widths.
        let mut s = Substitution::new();
        let mut map = Vec::new();
        for (k, &e) in all.iter().enumerate().filter(|(k, _)| k % 7 == 3) {
            let w = cx.width(e).unwrap();
            let t = cx.symbol(format!("fresh{k}").as_str(), w).unwrap();
            s.replace(&cx, e, t).unwrap();
            map.push((e, t));
        }
        let want = cx.substitute(&roots, &map).unwrap();
        // In small steps: each call continues where the last stopped.
        let mut calls = 0;
        let got = loop {
            calls += 1;
            if let Some(v) = cx.substitute_bounded(&roots, &mut s, 3).unwrap() {
                break v;
            }
            assert!(calls < 10_000);
        };
        assert_eq!(got, want, "seed {seed}");
        for (old, new) in s.changed(&cx) {
            assert_ne!(old, new);
            assert_eq!(s.image(&cx, old).unwrap(), Some(new));
        }
        // Asking again costs nothing.
        assert_eq!(
            cx.substitute_bounded(&roots, &mut s, 0).unwrap(),
            Some(want)
        );
    }
}

#[test]
fn bounded_substitution_never_walks_below_what_it_replaces() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W32);
    let big = cx
        .parse("((a * b + c) ^ (d - e)) * ((a | c) + (b & e))", &o)
        .unwrap();
    let root = cx
        .parse("((((a * b + c) ^ (d - e)) * ((a | c) + (b & e))) + z)", &o)
        .unwrap();
    let t = cx.symbol("t", Width::W32).unwrap();
    let mut s = Substitution::new();
    s.replace(&cx, big, t).unwrap();
    // The root and `z` only: two visits.
    let out = cx.substitute_bounded(&[root], &mut s, 2).unwrap().unwrap();
    assert_eq!(out[0], cx.parse("t + z", &o).unwrap());
    // Replacements are fixed once applied.
    let u = cx.symbol("u", Width::W32).unwrap();
    assert!(s.replace(&cx, u, t).is_err());
    let mut fresh = Substitution::new();
    fresh.replace(&cx, u, t).unwrap();
    assert!(matches!(
        fresh.replace(&cx, u, t),
        Err(Error::DuplicateSubstitution)
    ));
    let narrow = cx.symbol("n", Width::W8).unwrap();
    assert!(Substitution::new().replace(&cx, u, narrow).is_err());
    // Another context's substitution is rejected.
    let mut other = Context::new();
    let q = other.symbol("q", Width::W32).unwrap();
    assert!(other.substitute_bounded(&[q], &mut s, 10).is_err());
}

#[test]
fn bounded_substitution_of_a_deep_chain_takes_linear_total_work() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W64).unwrap();
    let mut e = x;
    for k in 0..20_000u64 {
        let c = cx
            .constant(&BitVec::wrapping_from_u64(Width::W64, k * 2 + 1))
            .unwrap();
        let m = cx.mul(e, c).unwrap();
        e = cx.xor(m, c).unwrap();
    }
    let y = cx.symbol("y", Width::W64).unwrap();
    let mut s = Substitution::new();
    s.replace(&cx, x, y).unwrap();
    let mut calls = 0u64;
    let out = loop {
        calls += 1;
        if let Some(v) = cx.substitute_bounded(&[e], &mut s, 1000).unwrap() {
            break v;
        }
    };
    // 60,001 nodes: about 61 calls of 1000 visits each, however deep the chain.
    assert!(calls <= 62, "{calls} calls");
    assert_eq!(out, cx.substitute(&[e], &[(x, y)]).unwrap());
}

/// Constants of at most 64 bits built from a word are the nodes built from a `BitVec`: the same
/// node, structural hash and printed form, whichever path makes them first.
#[test]
fn word_constants_are_the_bitvec_constants() {
    let mut rng = Rng(0x5eed_c0de);
    for word_first in [true, false] {
        let mut cx = Context::new();
        for w in 1..=64u16 {
            let width = Width::new(w).unwrap();
            let mask = u64::MAX >> (64 - w);
            for v in [0, 1, mask, mask >> 1, rng.next() & mask, rng.next() & mask] {
                let bv = BitVec::from_u64(width, v).unwrap();
                let (a, b) = if word_first {
                    let a = cx.constant_u64(width, v).unwrap();
                    (a, cx.constant(&bv).unwrap())
                } else {
                    let b = cx.constant(&bv).unwrap();
                    (cx.constant_u64(width, v).unwrap(), b)
                };
                assert_eq!(a, b, "{v:#x} at {w} bits");
                let i = cx.id(a).unwrap();
                assert_eq!(cx.meta[i as usize].shash, Context::const_hash(&bv));
                assert_eq!(cx.as_const(a).unwrap(), Some(bv));
            }
            // A value that does not fit is refused as before.
            if w < 64 {
                assert!(cx.constant_u64(width, mask + 1).is_err());
            }
        }
    }
}

/// Reserving room changes nothing but capacity.
#[test]
fn reserving_room_builds_the_same_nodes() {
    let (mut a, mut b) = (Context::new(), Context::new());
    b.reserve(10_000);
    let o = ParseOptions::width(Width::W32);
    for src in ["(x & y) + (x | y)", "x - 5 + 5", "(x ^ 0x5a) * 3 == y"] {
        let (ea, eb) = (a.parse(src, &o).unwrap(), b.parse(src, &o).unwrap());
        assert_eq!(a.display(ea).to_string(), b.display(eb).to_string());
        assert_eq!(ea.index(), eb.index());
    }
}
