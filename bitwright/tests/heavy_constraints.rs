//! Constraints (`Assumptions`): random sets mixing predicates (assumed true or false) and
//! assumed facts (known bits and ranges) over random DAGs. Checked exhaustively at small widths:
//!
//! - every value a node takes where the constraints its facts rely on hold lies inside
//!   `facts_under` (reliance is sufficient, not just the full set);
//! - `prove_under` is sound for every query kind where its reliance holds;
//! - an infeasible set really has no solution, and its reported conflict alone has none;
//! - re-deriving facts and re-proving with only the relied-on constraints gives the same answer;
//! - sets of more than 64 constraints (where reliance lumps the later ones together) stay sound;
//! - the simplifier's results under the set hold wherever the constraints they rely on hold.
//!
//! At wide widths the constraints are built to hold at a witness assignment, so the set is
//! feasible by construction: it must not be called infeasible, and every fact and proof must
//! agree with the witness.
//!
//! The library's unit tests check predicate constraints and `Cmp` proofs at up to 3 bits; this
//! suite adds assumed facts, every query kind, reliance-restricted checking of facts, re-proof
//! from the reliance, more than 64 constraints, and wide widths.

mod common;

use bitwright::engine::{Engine, Run, Strategy};
use bitwright::{
    Assumptions, BitVec, CmpOpExt, ConstraintId, Context, ContextConfig, Expr, Facts, KnownBits,
    Proof, Query, Reliance, SRange, Truth, URange, Width,
};
use common::{Dag, GenConfig, Rng, SMOKE_WIDTHS, Size, WIDTHS, boundary_values, test_context, w};

// ----- building constraints ------------------------------------------------------------------

fn ule(a: &BitVec, b: &BitVec) -> bool {
    BitVec::apply_cmp(CmpOpExt::Ule, a, b).unwrap()
}

fn sle(a: &BitVec, b: &BitVec) -> bool {
    BitVec::apply_cmp(CmpOpExt::Sle, a, b).unwrap()
}

/// A random mask: none, all, low bits, high bits, or random bits.
fn mask(rng: &mut Rng, width: Width) -> BitVec {
    let n = width.bits();
    match rng.below(5) {
        0 => BitVec::zero(width),
        1 => BitVec::ones(width),
        2 => common::ones_range(width, 0, 1 + rng.below(u64::from(n)) as u16),
        3 => {
            let k = rng.below(u64::from(n)) as u16;
            common::ones_range(width, k, n - k)
        }
        _ => rng.bitvec(width),
    }
}

fn and(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::apply_bin(bitwright::BinOp::And, a, b).unwrap()
}

fn not(a: &BitVec) -> BitVec {
    BitVec::apply_un(bitwright::UnOp::Not, a).unwrap()
}

/// Facts that contain `v`: some of its bits known, and ranges around it.
fn facts_around(rng: &mut Rng, v: &BitVec) -> Facts {
    let width = v.width();
    let m = mask(rng, width);
    let known = KnownBits::new(and(&not(v), &m), and(v, &m)).unwrap();
    let (a, b) = (rng.biased(width), rng.biased(width));
    let ulo = if ule(&a, v) { a } else { *v };
    let uhi = if ule(v, &b) { b } else { *v };
    let (c, d) = (rng.biased(width), rng.biased(width));
    let slo = if sle(&c, v) { c } else { *v };
    let shi = if sle(v, &d) { d } else { *v };
    let u = if rng.chance(1, 2) {
        URange::new(ulo, uhi).unwrap()
    } else {
        URange::full(width)
    };
    let s = if rng.chance(1, 2) {
        SRange::new(slo, shi).unwrap()
    } else {
        SRange::full(width)
    };
    let f = Facts::new(known, u, s).expect("facts containing a value are consistent");
    assert!(f.contains(v), "facts_around must contain {v}: {f:?}");
    f
}

/// Arbitrary facts (which may exclude every value the expression takes), if consistent.
fn random_facts(rng: &mut Rng, width: Width) -> Option<Facts> {
    let v = rng.biased(width);
    let m = mask(rng, width);
    let known = KnownBits::new(and(&not(&v), &m), and(&v, &m)).unwrap();
    let (a, b) = (rng.biased(width), rng.biased(width));
    let (lo, hi) = if ule(&a, &b) { (a, b) } else { (b, a) };
    let (c, d) = (rng.biased(width), rng.biased(width));
    let (slo, shi) = if sle(&c, &d) { (c, d) } else { (d, c) };
    Facts::new(known, URange::new(lo, hi)?, SRange::new(slo, shi)?)
}

/// How constraints are drawn.
#[derive(Copy, Clone, PartialEq, Eq)]
enum Mode {
    /// Anything: predicates assumed either way, arbitrary facts (often infeasible).
    Arbitrary,
    /// Every constraint holds at the witness assignment.
    Witness,
}

/// A constraint: a random 1-bit DAG node or comparison assumed true or false, or facts about a
/// random DAG node. `witness` holds every node's value at the witness assignment.
fn add_constraint(
    cx: &mut Context,
    rng: &mut Rng,
    dag: &mut Dag,
    a: &mut Assumptions,
    mode: Mode,
    witness: &[BitVec],
) -> ConstraintId {
    let value_of = |dag: &Dag, cx: &mut Context, e: Expr| -> BitVec {
        cx.eval(&[e], &dag.binding(witness)[..]).unwrap()[0]
    };
    let widths = dag.cfg.widths.clone();
    match rng.below(3) {
        0 | 1 => {
            let p = if rng.chance(1, 2) {
                let i = dag.random(cx, rng, 1);
                dag.expr(i)
            } else {
                // A comparison against a boundary constant or another node.
                let ow = rng.pick(&widths);
                let i = dag.random(cx, rng, ow);
                let x = dag.expr(i);
                let y = if rng.chance(1, 2) {
                    let c = rng.pick(&boundary_values(w(ow)));
                    cx.constant(&c).unwrap()
                } else {
                    let j = dag.random(cx, rng, ow);
                    dag.expr(j)
                };
                cx.cmp(rng.pick(&CmpOpExt::ALL), x, y).unwrap()
            };
            let truth = match mode {
                Mode::Witness => !value_of(dag, cx, p).is_zero(),
                Mode::Arbitrary => rng.chance(2, 3),
            };
            if truth {
                a.assume_true(cx, p).unwrap()
            } else {
                a.assume_false(cx, p).unwrap()
            }
        }
        _ => {
            let ow = rng.pick(&widths);
            let i = dag.random(cx, rng, ow);
            let e = dag.expr(i);
            let f = match mode {
                Mode::Witness => facts_around(rng, &value_of(dag, cx, e)),
                Mode::Arbitrary => match random_facts(rng, w(ow)) {
                    Some(f) if rng.chance(1, 2) => f,
                    _ => facts_around(rng, &value_of(dag, cx, e)),
                },
            };
            a.assume(cx, e, f).unwrap()
        }
    }
}

// ----- the checks ----------------------------------------------------------------------------

/// A constraint set over a DAG and, at each environment, which constraints hold.
struct World {
    dag: Dag,
    a: Assumptions,
    /// Every node under the constraints and the probes, in post-order.
    nodes: Vec<Expr>,
    /// Expressions over the same symbols that are not constrained themselves.
    probes: Vec<Expr>,
    envs: Vec<Vec<BitVec>>,
    values: Vec<Vec<BitVec>>,
    /// The constraints' ids, in order.
    ids: Vec<ConstraintId>,
    /// `holds[k][c]`: constraint `c` holds at environment `k`.
    holds: Vec<Vec<bool>>,
    exhaustive: bool,
}

impl World {
    fn new(
        cx: &mut Context,
        rng: &mut Rng,
        cfg: GenConfig,
        constraints: usize,
        mode: Mode,
        size: Size,
    ) -> World {
        let mut dag = Dag::new(cx, cfg);
        let witness = dag.boundary_env(rng);
        let mut a = Assumptions::new();
        for _ in 0..constraints {
            add_constraint(cx, rng, &mut dag, &mut a, mode, &witness);
        }
        // Probes: a few more expressions over the same symbols.
        let widths = dag.cfg.widths.clone();
        let mut roots: Vec<Expr> = a.constraints().map(|(_, e, _)| e).collect();
        let mut probes = Vec::new();
        for _ in 0..3 {
            let pw = rng.pick(&widths);
            let i = dag.random(cx, rng, pw);
            probes.push(dag.expr(i));
        }
        roots.extend(&probes);
        let nodes = cx.post_order(&roots).unwrap();
        let max_bits = size.pick(8, 12);
        let exhaustive = dag.every_env(max_bits).is_some();
        let mut envs = common::envs_for(&dag, rng, max_bits, size.pick(8, 32));
        if mode == Mode::Witness {
            envs.push(witness);
        }
        let seeds: Vec<(Expr, Facts)> = a.constraints().map(|(_, e, f)| (e, f)).collect();
        let mut values = Vec::with_capacity(envs.len());
        let mut holds = Vec::with_capacity(envs.len());
        for env in &envs {
            let b = dag.binding(env);
            values.push(cx.eval(&nodes, &b[..]).unwrap());
            let cv = cx
                .eval(&seeds.iter().map(|s| s.0).collect::<Vec<_>>(), &b[..])
                .unwrap();
            holds.push(
                seeds
                    .iter()
                    .zip(&cv)
                    .map(|((_, f), v)| f.contains(v))
                    .collect(),
            );
        }
        let ids = a.constraints().map(|(id, _, _)| id).collect();
        World {
            dag,
            a,
            nodes,
            probes,
            envs,
            values,
            ids,
            holds,
            exhaustive,
        }
    }

    /// Whether every constraint `rel` names holds at environment `k`.
    fn relied_hold(&self, k: usize, rel: Reliance) -> bool {
        self.holds[k]
            .iter()
            .enumerate()
            .all(|(c, &h)| h || !rel.may_use(self.ids[c]))
    }

    fn all_hold(&self, k: usize) -> bool {
        self.holds[k].iter().all(|&h| h)
    }

    fn satisfiable(&self) -> bool {
        (0..self.envs.len()).any(|k| self.all_hold(k))
    }
}

/// Facts under the constraints contain every value wherever the constraints they rely on
/// hold; `None` (infeasible) only when no assignment satisfies the set.
fn check_facts_under(cx: &mut Context, wd: &World, what: &str) -> usize {
    let mut refined = 0;
    for (i, &e) in wd.nodes.iter().enumerate() {
        match cx.facts_under(e, &wd.a).unwrap() {
            // Infeasible for the part `e` depends on (the overlay can find a contradiction the
            // set's own propagation did not): no assignment may satisfy the set.
            None => {
                assert!(
                    !wd.exhaustive || !wd.satisfiable(),
                    "{what}: `{}` has no facts (infeasible), but the set is satisfiable",
                    cx.display(e)
                );
            }
            Some((f, rel)) => {
                if f != cx.facts(e).unwrap() {
                    refined += 1;
                }
                for (k, vals) in wd.values.iter().enumerate() {
                    if !wd.relied_hold(k, rel) {
                        continue;
                    }
                    assert!(
                        f.contains(&vals[i]),
                        "{what}: `{}` = {} at {} where its relied-on constraints {rel:?} hold, \
                         but its facts under {:?} are {f:?}",
                        cx.display(e),
                        vals[i],
                        wd.dag.show_env(&wd.envs[k]),
                        wd.a
                    );
                }
                // The relied-on constraints alone give the same facts, unless they have no
                // solution at all.
                if !rel.is_none() {
                    let mut sub = Assumptions::new();
                    for (id, x, g) in wd.a.constraints() {
                        if rel.may_use(id) {
                            sub.assume(cx, x, g).unwrap();
                        }
                    }
                    let again = cx.facts_under(e, &sub).unwrap().map(|(g, _)| g);
                    let sub_satisfiable = (0..wd.envs.len()).any(|k| wd.relied_hold(k, rel));
                    assert!(
                        again == Some(f) || (wd.exhaustive && !sub_satisfiable),
                        "{what}: `{}` has {f:?} under {:?} but {again:?} under its reliance {sub:?}",
                        cx.display(e),
                        wd.a
                    );
                }
            }
        }
    }
    refined
}

/// Whether a query holds at the values of its operands (via the context's own kernels, which
/// the value suites check against the reference).
fn holds(q: &Query<'_>, a: &BitVec, b: Option<&BitVec>) -> bool {
    let n = a.width().bits();
    let bits_from = |from: u16, bit: bool| (from..n).all(|i| a.bit(i) == Some(bit));
    match *q {
        Query::IsZero(_) => a.is_zero(),
        Query::IsNonZero(_) => !a.is_zero(),
        Query::Bit { bit, value, .. } => a.bit(bit) == Some(value),
        Query::Eq(..) => Some(a) == b,
        Query::Cmp(op, ..) => BitVec::apply_cmp(op, a, b.unwrap()).unwrap(),
        Query::InURange { lo, hi, .. } => ule(lo, a) && ule(a, hi),
        Query::InSRange { lo, hi, .. } => sle(lo, a) && sle(a, hi),
        Query::Aligned { log2, .. } => {
            (0..log2.min(n)).all(|i| a.bit(i) == Some(false)) && (log2 <= n || a.is_zero())
        }
        Query::MaskRedundant { mask, .. } => and(a, mask) == *a,
        Query::FitsUnsigned { bits, .. } => bits >= n || bits_from(bits, false),
        Query::FitsSigned { bits, .. } => bits != 0 && (bits >= n || bits_from(bits - 1, a.msb())),
        _ => unreachable!(),
    }
}

/// `prove_under` is sound where its reliance holds, and re-proving under only the relied-on
/// constraints gives the same answer. Returns (decided, re-proved identically, re-proved).
fn check_proofs_under(
    cx: &mut Context,
    rng: &mut Rng,
    wd: &World,
    what: &str,
) -> (usize, usize, usize) {
    let (mut decided, mut same, mut reproved) = (0, 0, 0);
    let pos = |e: Expr| wd.nodes.iter().position(|&x| x == e).unwrap();
    for _ in 0..12 {
        let x = rng.pick(&wd.nodes);
        let width = cx.width(x).unwrap();
        let same_w: Vec<Expr> = wd
            .nodes
            .iter()
            .copied()
            .filter(|&y| cx.width(y).unwrap() == width)
            .collect();
        let y = rng.pick(&same_w);
        let n = width.bits();
        let bv = boundary_values(width);
        let (lo, hi, m) = (rng.pick(&bv), rng.pick(&bv), rng.pick(&bv));
        let bit = rng.below(u64::from(n)) as u16;
        let mut qs = vec![
            Query::IsZero(x),
            Query::IsNonZero(x),
            Query::Eq(x, y),
            Query::Bit {
                e: x,
                bit,
                value: rng.chance(1, 2),
            },
            Query::InURange {
                e: x,
                lo: &lo,
                hi: &hi,
            },
            Query::InSRange {
                e: x,
                lo: &lo,
                hi: &hi,
            },
            Query::Aligned {
                e: x,
                log2: rng.below(u64::from(n) + 2) as u16,
            },
            Query::MaskRedundant { e: x, mask: &m },
            Query::FitsUnsigned {
                e: x,
                bits: rng.below(u64::from(n) + 2) as u16,
            },
            Query::FitsSigned {
                e: x,
                bits: rng.below(u64::from(n) + 2) as u16,
            },
        ];
        for op in CmpOpExt::ALL {
            qs.push(Query::Cmp(op, x, y));
        }
        for q in qs {
            let p: Proof = cx.prove_under(q, &wd.a).unwrap();
            if p.truth == Truth::Unknown {
                assert!(p.relies_on.is_none(), "{what}: Unknown relies on nothing");
                continue;
            }
            decided += 1;
            let (ix, iy) = (pos(x), pos(y));
            for (k, vals) in wd.values.iter().enumerate() {
                if !wd.relied_hold(k, p.relies_on) {
                    continue;
                }
                let got = holds(&q, &vals[ix], Some(&vals[iy]));
                assert_eq!(
                    got,
                    p.truth == Truth::True,
                    "{what}: {q:?} (`{}`, `{}`) proved {:?} relying on {:?}, but at {} it is {got} \
                     ({} / {}) under {:?}",
                    cx.display(x),
                    cx.display(y),
                    p.truth,
                    p.relies_on,
                    wd.dag.show_env(&wd.envs[k]),
                    vals[ix],
                    vals[iy],
                    wd.a
                );
            }
            // Re-prove from the relied-on constraints alone, in their order.
            let mut sub = Assumptions::new();
            for (id, e, f) in wd.a.constraints() {
                if p.relies_on.may_use(id) {
                    sub.assume(cx, e, f).unwrap();
                }
            }
            let again = cx.prove_under(q, &sub).unwrap();
            reproved += 1;
            if again.truth == p.truth {
                same += 1;
            } else {
                // The relied-on constraints are sufficient: they alone give the same answer,
                // unless they have no solution at all (then any answer is vacuously true).
                let sub_satisfiable = (0..wd.envs.len()).any(|k| wd.relied_hold(k, p.relies_on));
                assert!(
                    wd.exhaustive && !sub_satisfiable,
                    "{what}: {q:?} is {:?} under {:?} but {:?} under its reliance {:?} alone",
                    p.truth,
                    wd.a,
                    again.truth,
                    sub
                );
            }
        }
    }
    (decided, same, reproved)
}

/// The simplifier under the constraints: each result equals its input wherever the constraints
/// it relies on hold (everywhere, when it relies on none). Returns how many results changed.
fn check_engine_under(cx: &mut Context, wd: &World, what: &str) -> usize {
    let mut changed = 0;
    for engine in [
        Engine::standard(),
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build()
            .unwrap(),
    ] {
        let out = engine
            .run(cx, &wd.probes, Run::default().with_assumptions(&wd.a))
            .unwrap();
        for (&e, r) in wd.probes.iter().zip(&out.roots) {
            changed += usize::from(r.changed);
            if wd.a.is_infeasible() {
                assert!(
                    r.relies_on.is_none(),
                    "{what}: an infeasible set is relied on"
                );
            }
            for (k, env) in wd.envs.iter().enumerate() {
                if !wd.relied_hold(k, r.relies_on) {
                    continue;
                }
                let v = cx.eval(&[e, r.expr], &wd.dag.binding(env)[..]).unwrap();
                assert_eq!(
                    v[0],
                    v[1],
                    "{what}: `{}` became `{}` relying on {:?} under {:?}, but differs at {}",
                    cx.display(e),
                    cx.display(r.expr),
                    r.relies_on,
                    wd.a,
                    wd.dag.show_env(env)
                );
            }
        }
    }
    changed
}

/// An infeasible set has no solution, and neither has its conflict alone.
fn check_infeasible(wd: &World, what: &str) -> bool {
    let Some(conflict) = wd.a.conflict() else {
        return false;
    };
    if wd.exhaustive {
        for k in 0..wd.envs.len() {
            assert!(
                !wd.relied_hold(k, conflict),
                "{what}: {} satisfies the conflict {conflict:?} of {:?}",
                wd.dag.show_env(&wd.envs[k]),
                wd.a
            );
        }
    }
    true
}

// ----- the properties -------------------------------------------------------------------------

/// Runs every check on `rounds` random sets of up to `max_constraints` constraints; a third of
/// them (or all, with `witness`) hold at a witness. Returns the counts `[infeasible sets,
/// refined facts, decided proofs, identical re-proofs, re-proofs, sets]`.
fn small_sets(
    size: Size,
    max_constraints: u64,
    witness: bool,
    seed0: u64,
    rounds: u64,
) -> [usize; 6] {
    let mut t = [0usize; 6];
    for seed in 0..rounds {
        let mut rng = Rng(seed0 + seed);
        let mut cx = test_context(ContextConfig::default());
        let cfg = GenConfig::small(&mut rng, size.pick(3, 4), 2 + (seed % 3) as u32)
            .with_ext(seed % 3 == 2);
        let n = 1 + rng.below(max_constraints) as usize;
        let mode = if witness || rng.chance(1, 3) {
            Mode::Witness
        } else {
            Mode::Arbitrary
        };
        let wd = World::new(&mut cx, &mut rng, cfg, n, mode, size);
        let what = format!("seed {:#x} ({n} constraints)", seed0 + seed);
        if mode == Mode::Witness {
            assert!(
                !wd.a.is_infeasible(),
                "{what}: a set with a witness is infeasible"
            );
        }
        if wd.exhaustive && wd.satisfiable() {
            assert!(
                !wd.a.is_infeasible(),
                "{what}: satisfiable, called infeasible"
            );
        }
        t[0] += usize::from(check_infeasible(&wd, &what));
        t[1] += check_facts_under(&mut cx, &wd, &what);
        check_engine_under(&mut cx, &wd, &what);
        let (d, s, r) = check_proofs_under(&mut cx, &mut rng, &wd, &what);
        t[2] += d;
        t[3] += s;
        t[4] += r;
        t[5] += 1;
    }
    t
}

fn constraints_small(size: Size) {
    let t = small_sets(size, 4, false, 0xc0_0000, size.pick(40, 15_000));
    eprintln!(
        "{} sets: {} infeasible, {} refined facts, {} decided proofs, {}/{} re-proved identically",
        t[5], t[0], t[1], t[2], t[3], t[4]
    );
    assert!(
        t[0] > 0 && t[1] > t[5] && t[2] > t[5],
        "the sets should decide things: {t:?}"
    );
}

#[test]
fn constraints_are_sound_where_their_reliance_holds_smoke() {
    constraints_small(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn constraints_are_sound_where_their_reliance_holds_heavy() {
    constraints_small(Size::Heavy);
}

/// More than 64 constraints: reliance tracks the 64th on together, and must stay sufficient.
/// The sets hold at a witness, so they stay feasible however many there are.
fn many_constraints(size: Size) {
    let t = small_sets(size, 90, true, 0xc1_0000, size.pick(4, 600));
    eprintln!("{t:?}");
    assert!(t[2] > t[5], "the sets should decide things: {t:?}");
}

#[test]
fn more_than_64_constraints_stay_sound_smoke() {
    many_constraints(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn more_than_64_constraints_stay_sound_heavy() {
    many_constraints(Size::Heavy);
}

/// Wide widths: constraints hold at a witness, so the set is feasible, every fact contains the
/// witness's values, and every proof agrees with it.
fn constraints_wide(size: Size) {
    let widths: Vec<u16> = size.pick(SMOKE_WIDTHS.to_vec(), WIDTHS.to_vec());
    let mut decided = 0;
    for seed in 0..size.pick(10, 8000u64) {
        let mut rng = Rng(0xc2_0000 + seed);
        let mut cx = test_context(ContextConfig::default());
        let cfg = GenConfig::wide(&mut rng, &widths, 2 + (seed % 3) as u32).with_ext(seed % 3 == 2);
        let n = 1 + rng.below(6) as usize;
        let wd = World::new(&mut cx, &mut rng, cfg, n, Mode::Witness, size);
        let what = format!("seed {:#x} ({n} constraints)", 0xc2_0000 + seed);
        assert!(
            !wd.a.is_infeasible(),
            "{what}: a set with a witness is infeasible"
        );
        check_facts_under(&mut cx, &wd, &what);
        check_engine_under(&mut cx, &wd, &what);
        decided += check_proofs_under(&mut cx, &mut rng, &wd, &what).0;
    }
    assert!(decided > 0);
}

#[test]
fn wide_constraints_agree_with_their_witness_smoke() {
    constraints_wide(Size::Smoke);
}

#[test]
#[ignore = "heavy: run with --release -- --ignored"]
fn wide_constraints_agree_with_their_witness_heavy() {
    constraints_wide(Size::Heavy);
}
