//! The benchmarks. Names are `group/case/width`; every workload is deterministic.

use std::hint::black_box;
use std::sync::Arc;

use bitwright::engine::{Engine, Strategy};
use bitwright::eqsat::{SaturateConfig, Saturator, SearchRun};
use bitwright::mba::{MbaConfig, MbaTrust, SignatureSolver};
use bitwright::{
    Assumptions, BinOp, BitVec, CmpOpExt, Context, Expr, ParseOptions, Query, SymbolKey, Width,
};

use crate::bench::Bench;
use crate::workload::{self, Dag, Rng};

/// Every benchmark, in report order.
pub fn all() -> Vec<Bench> {
    let mut v = Vec::new();
    values(&mut v);
    exprs(&mut v);
    facts(&mut v);
    constraints(&mut v);
    simplify(&mut v);
    services(&mut v);
    v
}

const WIDTHS: [u16; 4] = [8, 64, 128, 512];

/// Exact arithmetic on values: 1024 operations per iteration.
fn values(v: &mut Vec<Bench>) {
    for &bits in &WIDTHS {
        for op in [BinOp::Add, BinOp::Mul, BinOp::UDiv, BinOp::Shl] {
            let w = workload::width(bits);
            let name = format!("value/{}/{bits}", format!("{op:?}").to_lowercase());
            v.push(Bench::new(name, 200, "1024 ops", move |b| {
                let pairs = workload::value_pairs(u64::from(bits), w, 1024);
                b.iter(|| {
                    let mut acc = 0u64;
                    for (x, y) in &pairs {
                        let r =
                            BitVec::apply_bin(op, black_box(x), black_box(y)).expect("same widths");
                        acc ^= r.limbs()[0];
                    }
                    acc
                });
            }));
        }
    }
}

fn dag_shape(bits: u16, nodes: usize) -> Dag {
    Dag {
        width: workload::width(bits),
        symbols: 6,
        nodes,
        heavy_ops: true,
    }
}

/// Building (hash-consing and canonicalization), evaluation, substitution and the text syntax.
fn exprs(v: &mut Vec<Bench>) {
    for &bits in &[8u16, 64, 512] {
        v.push(Bench::new(
            format!("expr/build/{bits}"),
            40,
            "1000 nodes",
            move |b| {
                b.iter(|| {
                    let mut cx = Context::new();
                    workload::dag(&mut cx, 7, dag_shape(bits, 1000))
                });
            },
        ));
        v.push(Bench::new(
            format!("expr/eval/{bits}"),
            100,
            "1000 nodes",
            move |b| {
                let mut cx = Context::new();
                let root = workload::dag(&mut cx, 7, dag_shape(bits, 1000));
                let mut rng = Rng::new(3);
                let env: Vec<(SymbolKey, BitVec)> = (0..6)
                    .map(|i| {
                        (
                            SymbolKey::U64(i),
                            workload::value(&mut rng, workload::width(bits)),
                        )
                    })
                    .collect();
                b.iter(|| cx.eval(&[root], env.as_slice()).expect("eval"));
            },
        ));
    }
    v.push(Bench::new("expr/context-new", 20_000, "context", |b| {
        b.iter(Context::new);
    }));
    v.push(Bench::new("expr/substitute/64", 40, "1000 nodes", |b| {
        b.iter_batched(
            || {
                let mut cx = Context::new();
                let root = workload::dag(&mut cx, 7, dag_shape(64, 1000));
                let x = cx.symbol(SymbolKey::U64(0), Width::W64).expect("symbol");
                let y = cx.symbol(SymbolKey::U64(1), Width::W64).expect("symbol");
                let k = cx.constant_u64(Width::W64, 0x1234).expect("constant");
                let yk = cx.bin(BinOp::Add, y, k).expect("add");
                (cx, root, x, yk)
            },
            |(mut cx, root, x, yk)| cx.substitute(&[root], &[(x, yk)]).expect("substitute"),
        );
    }));
    let texts = |bits: u16| -> Vec<String> {
        let mut cx = Context::new();
        (0..20)
            .map(|i| {
                let e = workload::dag(&mut cx, 100 + i, dag_shape(bits, 60));
                cx.display(e).to_string()
            })
            .collect()
    };
    v.push(Bench::new("expr/parse/64", 40, "20 exprs", move |b| {
        let texts = texts(64);
        let o = ParseOptions::width(Width::W64);
        b.iter(|| {
            let mut cx = Context::new();
            for t in &texts {
                black_box(cx.parse(t, &o).expect("parse"));
            }
        });
    }));
    v.push(Bench::new("expr/display/64", 100, "20 exprs", |b| {
        let mut cx = Context::new();
        let roots: Vec<Expr> = (0..20)
            .map(|i| workload::dag(&mut cx, 100 + i, dag_shape(64, 60)))
            .collect();
        b.iter(|| {
            let mut n = 0;
            for &e in &roots {
                n += cx.display(e).to_string().len();
            }
            n
        });
    }));
}

/// Facts: cold (every node's facts computed once), warm (cached), proofs, and a fresh tiny
/// context per query (the shape of a per-instruction consumer).
fn facts(v: &mut Vec<Bench>) {
    for &bits in &[8u16, 64, 128, 512] {
        v.push(Bench::new(
            format!("facts/cold/{bits}"),
            40,
            "1000 nodes",
            move |b| {
                b.iter_batched(
                    || {
                        let mut cx = Context::new();
                        let root = workload::dag(&mut cx, 7, dag_shape(bits, 1000));
                        (cx, root)
                    },
                    |(mut cx, root)| cx.facts(root).expect("facts"),
                );
            },
        ));
    }
    v.push(Bench::new("facts/warm/64", 20_000, "query", |b| {
        let mut cx = Context::new();
        let root = workload::dag(&mut cx, 7, dag_shape(64, 1000));
        cx.facts(root).expect("facts");
        b.iter(|| cx.facts(root).expect("facts"));
    }));
    v.push(Bench::new("facts/prove/64", 40, "50 queries", |b| {
        b.iter_batched(
            || {
                let mut cx = Context::new();
                let roots: Vec<Expr> = (0..50)
                    .map(|i| workload::dag(&mut cx, 200 + i, dag_shape(64, 30)))
                    .collect();
                let bound = cx.constant_u64(Width::W64, 1 << 40).expect("constant");
                (cx, roots, bound)
            },
            |(mut cx, roots, bound)| {
                roots
                    .iter()
                    .map(|&e| {
                        cx.prove(Query::Cmp(CmpOpExt::Ult, e, bound))
                            .expect("prove")
                    })
                    .count()
            },
        );
    }));
    for &bits in &[8u16, 64] {
        v.push(Bench::new(
            format!("facts/tiny-context/{bits}"),
            20_000,
            "context",
            move |b| {
                let w = workload::width(bits);
                b.iter(|| {
                    let mut cx = Context::new();
                    let x = cx.symbol(SymbolKey::U64(0), w).expect("symbol");
                    let k = cx.constant_u64(w, 0x0f).expect("constant");
                    let m = cx.bin(BinOp::And, x, k).expect("and");
                    let four = cx.constant_u64(w, 4).expect("constant");
                    let e = cx.bin(BinOp::Shl, m, four).expect("shl");
                    cx.facts(e).expect("facts")
                });
            },
        ));
    }
}

/// Constraints: assuming predicates (propagated to operands) and facts under them.
fn constraints(v: &mut Vec<Bench>) {
    v.push(Bench::new(
        "constraints/assume/64",
        40,
        "40 predicates",
        |b| {
            b.iter_batched(
                || {
                    let mut cx = Context::new();
                    let o = ParseOptions::width(Width::W64);
                    let mut preds = Vec::new();
                    for i in 0..20 {
                        preds.push(
                            cx.parse(&format!("v{i} <u v{}", i + 1), &o)
                                .expect("ordering"),
                        );
                        preds.push(
                            cx.parse(&format!("(v{i} & {}) == 0", (1u64 << (i % 8)) - 1), &o)
                                .expect("mask"),
                        );
                    }
                    (cx, preds)
                },
                |(mut cx, preds)| {
                    let mut a = Assumptions::new();
                    for p in preds {
                        a.assume_true(&mut cx, p).expect("assume");
                    }
                    a
                },
            );
        },
    ));
    v.push(Bench::new(
        "constraints/facts-under/64",
        40,
        "40 queries",
        |b| {
            b.iter_batched(
                || {
                    let mut cx = Context::new();
                    let o = ParseOptions::width(Width::W64);
                    let mut a = Assumptions::new();
                    for i in 0..20 {
                        let p = cx
                            .parse(&format!("v{i} <u v{}", i + 1), &o)
                            .expect("ordering");
                        a.assume_true(&mut cx, p).expect("assume");
                        let m = cx
                            .parse(&format!("(v{i} & 7) == {}", i % 8), &o)
                            .expect("mask");
                        a.assume_true(&mut cx, m).expect("assume");
                    }
                    let queries: Vec<Expr> = (0..40)
                        .map(|i| {
                            cx.parse(&format!("(v{} + v{}) & 0xff", i % 21, (i + 3) % 21), &o)
                                .expect("query")
                        })
                        .collect();
                    (cx, a, queries)
                },
                |(mut cx, a, queries)| {
                    queries
                        .iter()
                        .filter_map(|&q| cx.facts_under(q, &a).expect("facts under"))
                        .count()
                },
            );
        },
    ));
}

/// The simplifier: the standard strategy on random DAGs, the deobfuscation strategy with the
/// native MBA solver on linear MBA, and a fresh tiny context per call.
fn simplify(v: &mut Vec<Bench>) {
    for &bits in &[8u16, 32, 64] {
        v.push(Bench::new(
            format!("simplify/standard/{bits}"),
            10,
            "20 exprs",
            move |b| {
                let engine = Engine::standard();
                b.iter_batched(
                    || {
                        let mut cx = Context::new();
                        let roots: Vec<Expr> = (0..20)
                            .map(|i| {
                                workload::dag(
                                    &mut cx,
                                    300 + i,
                                    Dag {
                                        heavy_ops: false,
                                        ..dag_shape(bits, 40)
                                    },
                                )
                            })
                            .collect();
                        (cx, roots)
                    },
                    |(mut cx, roots)| {
                        engine
                            .run(&mut cx, &roots, Default::default())
                            .expect("simplify")
                    },
                );
            },
        ));
    }
    for &bits in &[8u16, 64] {
        v.push(Bench::new(
            format!("simplify/mba/{bits}"),
            10,
            "20 exprs",
            move |b| {
                let config = MbaConfig::default()
                    .with_trust(MbaTrust::default().with_backend_certificates(false));
                let engine = Engine::builder()
                    .builtin()
                    .strategy(Strategy::deobfuscate().with_mba(config))
                    .mba_solver(Arc::new(SignatureSolver))
                    .build()
                    .expect("engine");
                let texts = workload::mba_corpus(11, 20);
                let o = ParseOptions::width(workload::width(bits));
                b.iter_batched(
                    || {
                        let mut cx = Context::new();
                        let roots: Vec<Expr> = texts
                            .iter()
                            .map(|t| cx.parse(t, &o).expect("MBA parses"))
                            .collect();
                        (cx, roots)
                    },
                    |(mut cx, roots)| {
                        engine
                            .run(&mut cx, &roots, Default::default())
                            .expect("simplify")
                    },
                );
            },
        ));
    }
    v.push(Bench::new(
        "simplify/tiny-context/64",
        2_000,
        "context",
        |b| {
            let engine = Engine::standard();
            let o = ParseOptions::width(Width::W64);
            b.iter(|| {
                let mut cx = Context::new();
                let e = cx.parse("(x | y) & x", &o).expect("parse");
                engine.simplify(&mut cx, e).expect("simplify")
            });
        },
    ));
}

/// Engine construction (rule compilation), equality saturation, SMT-LIB.
fn services(v: &mut Vec<Bench>) {
    v.push(Bench::new("service/engine-build", 20, "engine", |b| {
        b.iter(|| {
            Engine::builder()
                .builtin()
                .strategy(Strategy::standard())
                .build()
                .expect("engine")
        });
    }));
    v.push(Bench::new("service/eqsat/32", 20, "4 exprs", |b| {
        let (sat, _) = Saturator::builtin_groups(
            &["eqsat.distrib", "eqsat.cancel"],
            SaturateConfig::default(),
        );
        let o = ParseOptions::width(Width::W32);
        b.iter_batched(
            || {
                let mut cx = Context::new();
                let roots: Vec<Expr> = [
                    "x * y + x * z",
                    "x * (y + 1) - x * y",
                    "(a + b) * (c + d) - a * c",
                    "x * y + x * z + x * w - x * (y + z)",
                ]
                .iter()
                .map(|t| cx.parse(t, &o).expect("parse"))
                .collect();
                (cx, roots)
            },
            |(mut cx, roots)| {
                sat.search(&mut cx, &roots, SearchRun::default())
                    .expect("search")
            },
        );
    }));
    v.push(Bench::new("service/smt-export/64", 40, "1000 nodes", |b| {
        let mut cx = Context::new();
        let root = workload::dag(&mut cx, 7, dag_shape(64, 1000));
        b.iter(|| bitwright::smtlib::export(&mut cx, &[root]).expect("export"));
    }));
    v.push(Bench::new("service/smt-import/64", 40, "1000 nodes", |b| {
        let mut cx = Context::new();
        let root = workload::dag(&mut cx, 7, dag_shape(64, 1000));
        let script = bitwright::smtlib::export(&mut cx, &[root]).expect("export");
        b.iter(|| {
            let mut cx = Context::new();
            bitwright::smtlib::import(&mut cx, &script).expect("import")
        });
    }));
}
