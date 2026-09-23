//! Facts soundness: every value an expression can take lies inside its known bits and its
//! unsigned and signed ranges, `exact` and `enumerate_values` never exclude a value, and
//! `prove` never proves something false, for every query kind and at the edges of its
//! parameters (bit 0 and W − 1, empty and full ranges, alignment and fit sizes around W). Checked
//! on every node of random DAGs, exhaustively over all assignments at small widths and at
//! boundary environments up to 512 bits, and again under tiny `fact_work` caps, where every
//! answer must degrade to `top`/`Unknown`, never to a wrong one.
//!
//! The library's unit tests check the transfer functions exhaustively on abstract states, and
//! context facts at random environments up to 70 bits; this suite checks context facts at every
//! assignment and at the boundaries, and every query kind (not only comparisons) exhaustively.

mod common;

use bitwright::{BitVec, CmpOpExt, Context, ContextConfig, Expr, Facts, Query, Truth, Width};
use bitwright_ref as r;
use common::{
    Dag, GenConfig, Rng, SMOKE_WIDTHS, Size, WIDTHS, boundary_values, envs_for, test_context,
    to_ref,
};

/// A DAG, its roots' canonical post-order, and the value of every node at every environment.
struct Sampled {
    dag: Dag,
    nodes: Vec<Expr>,
    envs: Vec<Vec<BitVec>>,
    /// `values[k][i]`: node `i` at environment `k`.
    values: Vec<Vec<BitVec>>,
    exhaustive: bool,
}

fn sample(cx: &mut Context, rng: &mut Rng, cfg: GenConfig, roots: usize, size: Size) -> Sampled {
    let widths = cfg.widths.clone();
    let mut dag = Dag::new(cx, cfg);
    let root_exprs: Vec<Expr> = (0..roots)
        .map(|_| {
            let rw = rng.pick(&widths);
            let i = dag.random(cx, rng, rw);
            dag.expr(i)
        })
        .collect();
    let nodes = cx.post_order(&root_exprs).unwrap();
    let max_bits = size.pick(8, 12);
    let exhaustive = dag.every_env(max_bits).is_some();
    let envs = envs_for(&dag, rng, max_bits, size.pick(8, 32));
    let values = envs
        .iter()
        .map(|env| cx.eval(&nodes, &dag.binding(env)[..]).unwrap())
        .collect();
    Sampled {
        dag,
        nodes,
        envs,
        values,
        exhaustive,
    }
}

/// Every value of every node lies in its facts; `exact` and `enumerate_values` agree.
fn check_facts(cx: &mut Context, s: &Sampled, what: &str) {
    for (i, &e) in s.nodes.iter().enumerate() {
        let f = cx.facts(e).unwrap();
        assert_eq!(f.width(), cx.width(e).unwrap(), "{what}: facts width");
        let exact = cx.exact(e).unwrap();
        let listed = cx.enumerate_values(e, 64).unwrap();
        for (k, vals) in s.values.iter().enumerate() {
            let v = &vals[i];
            let fail = |part: &str| -> String {
                format!(
                    "{what}: `{}` = {v} at {} is outside its {part}: {f:?}",
                    cx.display(e),
                    s.dag.show_env(&s.envs[k])
                )
            };
            assert!(f.known().contains(v), "{}", fail("known bits"));
            assert!(f.urange().contains(v), "{}", fail("unsigned range"));
            assert!(f.srange().contains(v), "{}", fail("signed range"));
            if let Some(x) = exact {
                assert_eq!(x, *v, "{}", fail("exact value"));
            }
            if let Some(l) = &listed {
                assert!(l.contains(v), "{}", fail("enumerated values"));
            }
        }
    }
}

// ----- queries and their concrete meaning -----------------------------------------------------

/// An owned query, so its bounds can be generated per node.
#[derive(Clone, Debug)]
enum Q {
    IsZero(Expr),
    IsNonZero(Expr),
    Bit(Expr, u16, bool),
    Eq(Expr, Expr),
    Cmp(CmpOpExt, Expr, Expr),
    InU(Expr, BitVec, BitVec),
    InS(Expr, BitVec, BitVec),
    Aligned(Expr, u16),
    Mask(Expr, BitVec),
    FitsU(Expr, u16),
    FitsS(Expr, u16),
    IsConstant(Expr),
}

impl Q {
    fn query(&self) -> Query<'_> {
        match self {
            Q::IsZero(e) => Query::IsZero(*e),
            Q::IsNonZero(e) => Query::IsNonZero(*e),
            Q::Bit(e, bit, value) => Query::Bit {
                e: *e,
                bit: *bit,
                value: *value,
            },
            Q::Eq(a, b) => Query::Eq(*a, *b),
            Q::Cmp(op, a, b) => Query::Cmp(*op, *a, *b),
            Q::InU(e, lo, hi) => Query::InURange { e: *e, lo, hi },
            Q::InS(e, lo, hi) => Query::InSRange { e: *e, lo, hi },
            Q::Aligned(e, log2) => Query::Aligned { e: *e, log2: *log2 },
            Q::Mask(e, mask) => Query::MaskRedundant { e: *e, mask },
            Q::FitsU(e, bits) => Query::FitsUnsigned { e: *e, bits: *bits },
            Q::FitsS(e, bits) => Query::FitsSigned { e: *e, bits: *bits },
            Q::IsConstant(e) => Query::IsConstant(*e),
        }
    }

    fn operands(&self) -> (Expr, Option<Expr>) {
        match self {
            Q::Eq(a, b) | Q::Cmp(_, a, b) => (*a, Some(*b)),
            Q::IsZero(e)
            | Q::IsNonZero(e)
            | Q::Bit(e, ..)
            | Q::InU(e, ..)
            | Q::InS(e, ..)
            | Q::Aligned(e, _)
            | Q::Mask(e, _)
            | Q::FitsU(e, _)
            | Q::FitsS(e, _)
            | Q::IsConstant(e) => (*e, None),
        }
    }

    /// Whether the query holds at one point, computed with the reference (`IsConstant` is a
    /// property of all points and is checked separately).
    fn holds(&self, a: &BitVec, b: Option<&BitVec>) -> bool {
        let ra = to_ref(a);
        let n = ra.width();
        let zero = r::Bits::zero(n);
        // Bits [from, n) all equal `bit`.
        let high_all = |from: u16, bit: bool| (from..n).all(|i| ra.bit(i) == bit);
        match self {
            Q::IsZero(_) => ra == zero,
            Q::IsNonZero(_) => ra != zero,
            Q::Bit(_, bit, value) => ra.bit(*bit) == *value,
            Q::Eq(..) => ra == to_ref(b.unwrap()),
            Q::Cmp(op, ..) => r::cmp(common::ref_cmp(*op), &ra, &to_ref(b.unwrap())),
            Q::InU(_, lo, hi) => {
                r::cmp(r::CmpOp::Ule, &to_ref(lo), &ra) && r::cmp(r::CmpOp::Ule, &ra, &to_ref(hi))
            }
            Q::InS(_, lo, hi) => {
                r::cmp(r::CmpOp::Sle, &to_ref(lo), &ra) && r::cmp(r::CmpOp::Sle, &ra, &to_ref(hi))
            }
            // A multiple of 2^log2 (zero is a multiple of everything).
            Q::Aligned(_, log2) => {
                (0..(*log2).min(n)).all(|i| !ra.bit(i)) && (*log2 <= n || ra == zero)
            }
            Q::Mask(_, m) => {
                let rm = to_ref(m);
                (0..n).all(|i| !ra.bit(i) || rm.bit(i))
            }
            Q::FitsU(_, bits) => *bits >= n || high_all(*bits, false),
            Q::FitsS(_, bits) => *bits != 0 && (*bits >= n || high_all(bits - 1, ra.bit(n - 1))),
            Q::IsConstant(_) => unreachable!("checked across points"),
        }
    }
}

/// Queries about node `a` (and `b`, of the same width), with parameters at their edges.
fn queries(rng: &mut Rng, a: Expr, b: Expr, width: Width) -> Vec<Q> {
    let n = width.bits();
    let bv = boundary_values(width);
    let mut q = vec![
        Q::IsZero(a),
        Q::IsNonZero(a),
        Q::IsConstant(a),
        Q::Eq(a, b),
        Q::Bit(a, 0, rng.chance(1, 2)),
        Q::Bit(a, n - 1, rng.chance(1, 2)),
        Q::Bit(a, rng.below(u64::from(n)) as u16, rng.chance(1, 2)),
    ];
    for op in CmpOpExt::ALL {
        q.push(Q::Cmp(op, a, b));
    }
    for log2 in [0, 1, n / 2, n - 1, n, n + 1, u16::MAX] {
        q.push(Q::Aligned(a, log2));
    }
    for bits in [0, 1, n / 2, n - 1, n, n + 1, u16::MAX] {
        q.push(Q::FitsU(a, bits));
        q.push(Q::FitsS(a, bits));
    }
    for _ in 0..3 {
        let (lo, hi) = (rng.pick(&bv), rng.pick(&bv));
        // Both orders: one of them is an empty range unless lo == hi.
        q.push(Q::InU(a, lo, hi));
        q.push(Q::InU(a, hi, lo));
        q.push(Q::InS(a, lo, hi));
        q.push(Q::InS(a, hi, lo));
        q.push(Q::Mask(a, rng.pick(&bv)));
    }
    q.push(Q::InU(a, BitVec::zero(width), BitVec::ones(width)));
    q.push(Q::InS(a, BitVec::smin(width), BitVec::smax(width)));
    q
}

/// Every `True`/`False` answer holds at every sampled point (for `IsConstant`, across them).
/// Returns the number of decided queries.
fn check_proofs(cx: &mut Context, rng: &mut Rng, s: &Sampled, what: &str) -> usize {
    let pos = |e: Expr| s.nodes.iter().position(|&x| x == e).unwrap();
    let mut decided = 0;
    for (i, &a) in s.nodes.iter().enumerate() {
        let width = cx.width(a).unwrap();
        let same: Vec<Expr> = s
            .nodes
            .iter()
            .copied()
            .filter(|&x| cx.width(x).unwrap() == width)
            .collect();
        let b = rng.pick(&same);
        for q in queries(rng, a, b, width) {
            let truth = cx.prove(q.query()).unwrap();
            if truth == Truth::Unknown {
                continue;
            }
            decided += 1;
            let (qa, qb) = q.operands();
            let (ia, ib) = (pos(qa), qb.map(pos));
            if let Q::IsConstant(_) = q {
                let first = &s.values[0][i];
                let constant = s.values.iter().all(|v| v[i] == *first);
                if truth == Truth::True {
                    assert!(constant, "{what}: `{}` proved constant", cx.display(a));
                } else if s.exhaustive {
                    assert!(!constant, "{what}: `{}` proved not constant", cx.display(a));
                }
                continue;
            }
            for (k, vals) in s.values.iter().enumerate() {
                let holds = q.holds(&vals[ia], ib.map(|j| &vals[j]));
                assert_eq!(
                    holds,
                    truth == Truth::True,
                    "{what}: {q:?} on `{}` / `{}` proved {truth:?}, but at {} the values are {} / {}",
                    cx.display(qa),
                    qb.map(|b| cx.display(b).to_string()).unwrap_or_default(),
                    s.dag.show_env(&s.envs[k]),
                    vals[ia],
                    ib.map(|j| vals[j].to_string()).unwrap_or_default()
                );
            }
        }
    }
    decided
}

// ----- the properties ---------------------------------------------------------------------------

fn small(size: Size, rounds: u64, config: ContextConfig, seed0: u64) -> (usize, usize) {
    let (mut nodes, mut decided) = (0, 0);
    for seed in 0..rounds {
        let mut rng = Rng(seed0 + seed);
        let mut cx = test_context(config.clone());
        let cfg = GenConfig::small(&mut rng, 4, 2 + (seed % 4) as u32).with_ext(seed % 3 == 2);
        let s = sample(&mut cx, &mut rng, cfg, 2, size);
        let what = format!("seed {:#x} (fact_work {})", seed0 + seed, config.fact_work);
        check_facts(&mut cx, &s, &what);
        decided += check_proofs(&mut cx, &mut rng, &s, &what);
        nodes += s.nodes.len();
    }
    (nodes, decided)
}

fn wide(size: Size, rounds: u64, config: ContextConfig, seed0: u64) -> (usize, usize) {
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    let (mut nodes, mut decided) = (0, 0);
    for seed in 0..rounds {
        let mut rng = Rng(seed0 + seed);
        let mut cx = test_context(config.clone());
        let cfg = GenConfig::wide(&mut rng, &widths, 2 + (seed % 3) as u32).with_ext(seed % 3 == 2);
        let s = sample(&mut cx, &mut rng, cfg, 2, size);
        let what = format!("seed {:#x} (fact_work {})", seed0 + seed, config.fact_work);
        check_facts(&mut cx, &s, &what);
        decided += check_proofs(&mut cx, &mut rng, &s, &what);
        nodes += s.nodes.len();
    }
    (nodes, decided)
}

fn facts_and_proofs(size: Size) {
    let (n, d) = small(
        size,
        size.pick(40, 8000),
        ContextConfig::default(),
        0xfac_0000,
    );
    eprintln!("small: {n} nodes, {d} decided queries");
    assert!(
        d > n * 5,
        "the facts should decide many queries ({d} of {n} nodes)"
    );
    let (n, d) = wide(
        size,
        size.pick(10, 3000),
        ContextConfig::default(),
        0xfac_8000,
    );
    eprintln!("wide: {n} nodes, {d} decided queries");
    assert!(
        d > n * 5,
        "the facts should decide many queries ({d} of {n} nodes)"
    );
}

#[test]
fn facts_contain_every_value_and_proofs_hold_smoke() {
    facts_and_proofs(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn facts_contain_every_value_and_proofs_hold_heavy() {
    facts_and_proofs(Size::Heavy);
}

/// A work cap of a handful of transfers makes most answers `top`/`Unknown`; none may be wrong.
fn tiny_work(size: Size) {
    for work in [0, 1, 2, 3, 5, 8, 13] {
        let config = ContextConfig::default().with_fact_work(work);
        let seed = u64::from(work) * 0x1_0000;
        small(size, size.pick(10, 500), config.clone(), 0x71_0000 + seed);
        wide(size, size.pick(4, 250), config, 0x71_8000 + seed);
    }
}

#[test]
fn tiny_fact_work_stays_sound_smoke() {
    tiny_work(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn tiny_fact_work_stays_sound_heavy() {
    tiny_work(Size::Heavy);
}

/// A capped query resumes where it stopped: repeating `try_facts` until it answers gives the
/// facts an uncapped context computes for the same DAG, and `facts` is `top` or those facts.
/// Nodes are asked root first, so the caps bite.
fn resumed(size: Size) {
    let rounds = size.pick(30, 30_000);
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    let (mut capped_answers, mut nodes) = (0, 0);
    for seed in 0..rounds {
        let work = 1 + (seed % 7) as u32;
        let build = |cx: &mut Context| {
            let mut rng = Rng(0x2e5_0000 + seed);
            let cfg =
                GenConfig::wide(&mut rng, &widths, 5 + (seed % 4) as u32).with_ext(seed % 3 == 2);
            let mut dag = Dag::new(cx, cfg);
            let rw = rng.pick(&widths);
            let i = dag.random(cx, &mut rng, rw);
            dag.expr(i)
        };
        let mut full = test_context(ContextConfig::default());
        let e_full = build(&mut full);
        let mut capped = test_context(ContextConfig::default().with_fact_work(work));
        let e = build(&mut capped);
        let order_full = full.post_order(&[e_full]).unwrap();
        let order = capped.post_order(&[e]).unwrap();
        assert_eq!(order.len(), order_full.len(), "seed {seed:#x}: same DAG");
        nodes += order.len();
        for (&x, &xf) in order.iter().zip(&order_full).rev() {
            let want = full.facts(xf).unwrap();
            let top = Facts::top(capped.width(x).unwrap());
            let once = capped.facts(x).unwrap();
            assert!(
                once == want || once == top,
                "seed {seed:#x}: capped facts of `{}` are neither top nor the full facts",
                capped.display(x)
            );
            let mut tries = 0;
            let got = loop {
                tries += 1;
                assert!(tries < 100_000, "seed {seed:#x}: capped facts never finish");
                match capped.try_facts(x).unwrap() {
                    Some(f) => break f,
                    None => capped_answers += 1,
                }
            };
            assert_eq!(
                got,
                want,
                "seed {seed:#x}: resumed facts of `{}` (work {work})",
                capped.display(x)
            );
        }
    }
    eprintln!("{nodes} nodes, {capped_answers} capped answers");
    assert!(
        capped_answers > rounds as usize,
        "the caps should bite ({capped_answers})"
    );
}

#[test]
fn capped_facts_resume_to_the_uncapped_answer_smoke() {
    resumed(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn capped_facts_resume_to_the_uncapped_answer_heavy() {
    resumed(Size::Heavy);
}
