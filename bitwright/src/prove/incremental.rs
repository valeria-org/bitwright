//! One circuit and one search for many questions.

use super::aig::{Aig, Cnf};
use super::blast::Bits;
use super::sat::{self, Backend, Limits, Lit, Solver};
use super::{Blaster, Model, Unknown};
use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::hash::IdMap;
use crate::{BitVec, Checkpoint};

/// What an [`Incremental`] answers.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Answer {
    /// The predicates hold together at these values of their symbols.
    Sat(Model),
    /// They do not: the positions (in the slice asked about) of predicates that conflict,
    /// in order. Not a smallest such set: the ones the last conflict went through.
    Unsat(Vec<usize>),
    /// Not decided: why.
    Unknown(Unknown),
}

/// A circuit and a SAT search that outlive a question: each predicate asked about is added to
/// the circuit once, its clauses to the search once, and what the search learns stays, so a
/// sequence of related questions (a path condition that grows, a query against one) costs
/// what is new in each.
///
/// Predicates are assumed for the question that names them, never asserted for good: the
/// same `Incremental` answers any subset of what it has seen, in any order.
///
/// ```
/// use bitwright::prove::{Incremental, IncrementalAnswer as Answer, Limits};
/// use bitwright::{Context, ParseOptions, Width};
///
/// let mut cx = Context::new();
/// let o = ParseOptions::width(Width::W16);
/// let mut p = |s: &str| cx.parse(s, &o);
/// let (a, b, c) = (p("x * 3 == y")?, p("y <u 10")?, p("x >u 0x8000")?);
/// let mut inc = Incremental::new(1 << 20);
/// let limits = Limits::conflicts(10_000);
/// assert!(matches!(inc.solve(&mut cx, &[a, b], limits)?, Answer::Sat(_)));
/// // 3x < 10 leaves x = 0..3 and the x whose triple wraps: 0xaaab is one (y = 1).
/// assert!(matches!(inc.solve(&mut cx, &[a, b, c], limits)?, Answer::Sat(_)));
/// // y = 0 only for x = 0 (3 is odd), which is not above 0x8000.
/// let d = cx.parse("y == 0", &o)?;
/// let Answer::Unsat(core) = inc.solve(&mut cx, &[a, c, b, d], limits)? else {
///     panic!("x * 3 == 0 has one solution");
/// };
/// assert!([0, 1, 3].iter().all(|k| core.contains(k)));
/// // What it has seen it answers again in any combination, without building anything.
/// let gates = inc.nodes();
/// assert!(matches!(inc.solve(&mut cx, &[d, a], limits)?, Answer::Sat(_)));
/// assert_eq!(inc.nodes(), gates);
/// # Ok::<(), bitwright::Error>(())
/// ```
///
/// The search is bitwright's own ([`Incremental::new`]) or any other [`Backend`]
/// ([`Incremental::on`]).
#[derive(Debug)]
pub struct Incremental<B = Solver> {
    g: Aig,
    bits: IdMap<u32, Bits>,
    symbols: Vec<(u32, Bits)>,
    /// The gates each predicate added when it was first asked.
    added: IdMap<u32, u32>,
    cnf: Cnf,
    solver: B,
    max_nodes: usize,
    question_nodes: usize,
}

impl Incremental {
    /// An empty one, whose circuit may grow to `max_nodes` gates (then it answers
    /// [`Unknown::TooLarge`] for a question that needs more).
    pub fn new(max_nodes: usize) -> Self {
        Incremental::on(Solver::new(), max_nodes)
    }
}

impl<B: Backend> Incremental<B> {
    /// An empty one searched by `backend` (which must be empty too).
    pub fn on(backend: B, max_nodes: usize) -> Self {
        Incremental {
            g: Aig::new(),
            bits: IdMap::default(),
            symbols: Vec::new(),
            added: IdMap::default(),
            cnf: Cnf::empty(false),
            solver: backend,
            max_nodes,
            question_nodes: usize::MAX,
        }
    }

    /// The gates a question may add to the circuit for each predicate it has not seen (any
    /// number by default): one that needs more is answered [`Unknown::TooLarge`], and what
    /// it added stays for the next. A bound on what one new predicate may cost, which a
    /// question of many new ones (the first after the circuit was started again) is not
    /// held to as one.
    #[must_use]
    pub fn with_question_nodes(mut self, nodes: usize) -> Self {
        self.question_nodes = nodes;
        self
    }

    /// The gates of the circuit so far.
    pub fn nodes(&self) -> usize {
        self.g.len()
    }

    /// The gates that `predicates` added to the circuit, each when it was first asked (what
    /// it shares with an earlier one is the earlier one's). The rest of
    /// [`nodes`](Self::nodes) was added for predicates that are not among these: a circuit
    /// that is mostly that is better started again.
    pub fn nodes_of(&self, cx: &Context, predicates: &[Expr]) -> Result<usize, Error> {
        let mut n = 0usize;
        let mut ids = cx.ids(predicates)?;
        ids.sort_unstable();
        ids.dedup();
        for i in ids {
            n += self.added.get(&i).map_or(0, |&a| a as usize);
        }
        Ok(n)
    }

    /// The conflicts of every search so far.
    pub fn conflicts(&self) -> u64 {
        self.solver.conflicts()
    }

    /// Whether the 1-bit `predicates` hold together, within `limits` of search (counted from
    /// this call). A symbol's declared bits ([`Context::declare_known`]) are read when the
    /// symbol is first met.
    pub fn solve(
        &mut self,
        cx: &mut Context,
        predicates: &[Expr],
        limits: Limits,
    ) -> Result<Answer, Error> {
        let ids = cx.ids(predicates)?;
        let mut roots = Vec::with_capacity(ids.len());
        let unseen = ids.iter().filter(|i| !self.bits.contains_key(i)).count();
        let growth = self.question_nodes.saturating_mul(unseen.max(1));
        // (Read before the circuit is handed over: its size is part of the allowance.)
        let allowed = (self.max_nodes).min(self.g.len().saturating_add(growth));
        {
            let mut b = Blaster::resume(
                cx,
                core::mem::take(&mut self.g),
                core::mem::take(&mut self.bits),
                core::mem::take(&mut self.symbols),
                allowed,
            );
            let mut failure = None;
            for &i in &ids {
                if b.cx.width_of(i) != crate::Width::W1 {
                    failure = Some(Err(Error::Unsupported("a predicate must be 1 bit".into())));
                    break;
                }
                let before = b.g.len();
                match b.blast(i) {
                    Ok(bits) => {
                        let grew = (b.g.len() - before).min(u32::MAX as usize) as u32;
                        if grew > 0 {
                            *self.added.entry(i).or_insert(0) += grew;
                        }
                        roots.push(bits[0]);
                    }
                    Err(e) => {
                        failure = Some(b.unknown(e).map(Answer::Unknown));
                        break;
                    }
                }
            }
            (self.g, self.bits, self.symbols) = b.into_parts();
            if let Some(f) = failure {
                return f;
            }
        }
        self.cnf.extend(&self.g, &roots, &mut self.solver, false);
        let lits: Vec<Lit> = roots.iter().map(|&r| self.cnf.lit(r)).collect();
        Ok(match self.solver.solve_assuming(&lits, limits) {
            sat::Answer::Sat(model) => {
                let mut out = Vec::with_capacity(self.symbols.len());
                for (node, bits) in &self.symbols {
                    let e = cx.handle(*node);
                    let Some(key) = cx.symbol_id(e)?.and_then(|id| cx.symbol_key(id)).cloned()
                    else {
                        continue;
                    };
                    let w = cx.width_of(*node);
                    let mut limbs = vec![0u64; usize::from(w.bits()).div_ceil(64)];
                    for (j, &b) in bits.iter().enumerate() {
                        if self.cnf.value(b, &model) {
                            limbs[j / 64] |= 1 << (j % 64);
                        }
                    }
                    out.push((key, BitVec::wrapping_from_limbs(w, &limbs)));
                }
                Answer::Sat(out)
            }
            sat::Answer::Unsat => {
                let failed = self.solver.failed_assumptions();
                Answer::Unsat(
                    (0..lits.len())
                        .filter(|&k| failed.contains(&lits[k]))
                        .collect(),
                )
            }
            sat::Answer::Unknown => Answer::Unknown(Unknown::Budget {
                conflicts: self.solver.conflicts(),
                propagations: self.solver.propagations(),
            }),
        })
    }

    /// Makes it safe across a [`Context::rollback`] to `at`, to be called before it: forgets
    /// which gates stand for the expressions created since the checkpoint. (Their gates and
    /// clauses stay, harmless and unused; a long session starts a new `Incremental` now and
    /// then.)
    pub fn forget_since(&mut self, at: Checkpoint) {
        self.bits.retain(|&i, _| i < at.nodes());
        self.symbols.retain(|&(i, _)| i < at.nodes());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testutil::Rng;
    use crate::{ParseOptions, Width};

    /// A circuit that grows by related predicates (sums, products, selections sharing
    /// operands, so that a later predicate's gates look into an earlier one's) answers each
    /// subset as a circuit built for that subset alone does; a model satisfies what was asked
    /// and a core is unsatisfiable alone.
    /// A question's allowance of nodes is on top of the circuit as it is: a circuit that has
    /// grown past one allowance still takes the next question.
    #[test]
    fn a_question_is_allowed_its_nodes_on_top_of_the_circuit() {
        let o = ParseOptions::width(Width::W64);
        let mut cx = Context::new();
        let mut inc = Incremental::new(1 << 20).with_question_nodes(2_000);
        let sum = cx.parse("x + y == 12345", &o).unwrap();
        for i in 0..40u64 {
            let e = cx.parse(&format!("x * {} == {i}", 2 * i + 1), &o).unwrap();
            let a = inc
                .solve(&mut cx, &[sum, e], Limits::conflicts(10_000))
                .unwrap();
            assert!(matches!(a, Answer::Sat(_)), "question {i}: {a:?}");
        }
        assert!(inc.nodes() > 2_000);
    }

    #[test]
    fn a_grown_circuit_answers_as_a_fresh_one() {
        let o = ParseOptions::width(Width::W8);
        // First, predicates whose gates share inner conjunctions with gates encoded before
        // them. (The encoder once read a new gate through one encoded earlier, down to
        // operands that had no variable; the floating-point cases of the transformation
        // verifier's tests, which ask their questions of one solver, are what found it.)
        {
            let mut cx = Context::new();
            let mut inc = Incremental::new(1 << 20);
            let p1 = cx.parse("((a & b) & c) == 0x41", &o).unwrap();
            let p2 = cx.parse("((a & b) ^ c) == 0x3e", &o).unwrap();
            let p3 = cx
                .parse("select((a & b) == c, a, b) + ((a & b) & c) == 0x40", &o)
                .unwrap();
            let limits = Limits::conflicts(100_000);
            for subset in [vec![p1], vec![p1, p2], vec![p2, p3], vec![p1, p2, p3]] {
                let mut all = cx.bool(true).unwrap();
                for &e in &subset {
                    all = cx.bin(crate::BinOp::And, all, e).unwrap();
                }
                let cfg = crate::prove::Config::default().with_simplify(false);
                let fresh = crate::prove::satisfy(&mut cx, all, &cfg).unwrap().unwrap();
                match inc.solve(&mut cx, &subset, limits).unwrap() {
                    Answer::Sat(m) => {
                        assert!(fresh.is_some());
                        for v in cx.eval(&subset, m.as_slice()).unwrap() {
                            assert!(!v.is_zero());
                        }
                    }
                    Answer::Unsat(_) => assert!(fresh.is_none()),
                    Answer::Unknown(why) => panic!("{why:?}"),
                }
            }
        }
        let mut rng = Rng(0x1c);
        let (mut sat, mut unsat) = (0, 0);
        for round in 0..150 {
            let mut cx = Context::new();
            let mut inc = Incremental::new(1 << 20);
            let limits = Limits::conflicts(200_000);
            let mut pick = |n: u64| rng.below(n);
            let names = ["a", "b", "c"];
            let mut terms: Vec<String> = names.iter().map(|s| s.to_string()).collect();
            let mut asked: Vec<Expr> = Vec::new();
            for step in 0..6 {
                // A new term over earlier ones, then a predicate about it.
                let (x, y) = (
                    terms[pick(terms.len() as u64) as usize].clone(),
                    terms[pick(terms.len() as u64) as usize].clone(),
                );
                let k = pick(256);
                let t = match pick(7) {
                    0 => format!("({x} + {y})"),
                    1 => format!("({x} - {y} + {k})"),
                    2 => format!("({x} * {y})"),
                    3 => format!("({x} ^ {y} ^ {k})"),
                    4 => format!("select({x} <u {y}, {x}, {y} + 1)"),
                    5 => format!("(({x} & {y}) | ({x} & {k}) | ({y} & {k}))"),
                    _ => format!("({x} >>u 1) + ({y} << 1)"),
                };
                terms.push(t.clone());
                let p = match pick(4) {
                    0 => format!("{t} == {k}"),
                    1 => format!("{t} <u {}", k | 1),
                    2 => format!("{t} != {x}"),
                    _ => format!("({t} & 1) == {}", k & 1),
                };
                asked.push(cx.parse(&p, &o).unwrap());
                // The whole set, and a subset that leaves earlier predicates out.
                for subset in [asked.clone(), asked[step / 2..].to_vec()] {
                    let fresh = {
                        let mut all = cx.bool(true).unwrap();
                        for &e in &subset {
                            all = cx.bin(crate::BinOp::And, all, e).unwrap();
                        }
                        let cfg = crate::prove::Config::default().with_simplify(false);
                        crate::prove::satisfy(&mut cx, all, &cfg).unwrap().unwrap()
                    };
                    match inc.solve(&mut cx, &subset, limits).unwrap() {
                        Answer::Sat(m) => {
                            sat += 1;
                            assert!(fresh.is_some(), "round {round}: sat, fresh says unsat");
                            for v in cx.eval(&subset, m.as_slice()).unwrap() {
                                assert!(!v.is_zero(), "round {round}: the model fails");
                            }
                        }
                        Answer::Unsat(core) => {
                            unsat += 1;
                            assert!(fresh.is_none(), "round {round}: unsat, fresh says sat");
                            let mut all = cx.bool(true).unwrap();
                            for &k in &core {
                                all = cx.bin(crate::BinOp::And, all, subset[k]).unwrap();
                            }
                            let cfg = crate::prove::Config::default();
                            let alone = crate::prove::satisfy(&mut cx, all, &cfg).unwrap();
                            assert_eq!(alone, Ok(None), "round {round}: the core is satisfiable");
                        }
                        Answer::Unknown(why) => panic!("round {round}: {why:?}"),
                    }
                }
            }
        }
        assert!(sat > 300 && unsat > 100, "{sat} {unsat}");
    }
}
