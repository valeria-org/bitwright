//! One circuit and one search for many questions.

use super::aig::{Aig, Cnf};
use super::blast::Bits;
use super::sat::{self, Backend, Limits, Lit, Solver};
use super::{Blaster, Config, Model, Question, SampleMode, Simplifiers, Unknown};
use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::hash::IdMap;
use crate::{BitVec, Checkpoint, SymbolKey, Width};

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
    /// this call). A symbol's declared bits ([`Context::declare_known`]) are assumed as they
    /// stand in `cx` at this call, so changing or withdrawing a declaration stays sound.
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
        let pred_count = roots.len();
        let mut lits: Vec<Lit> = roots.iter().map(|&r| self.cnf.lit(r)).collect();
        for (node, bits) in &self.symbols {
            let Some(kb) = cx.declared_at(*node) else {
                continue;
            };
            for (j, &b) in bits.iter().enumerate() {
                let Some(lit) = self.cnf.mapped_lit(b) else {
                    continue;
                };
                if kb.known_one().bit(j as u16) == Some(true) {
                    lits.push(lit);
                } else if kb.known_zero().bit(j as u16) == Some(true) {
                    lits.push(!lit);
                }
            }
        }
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
                    let mut v = BitVec::wrapping_from_limbs(w, &limbs);
                    if let Some(kb) = cx.declared_at(*node) {
                        let keep = crate::facts::known::bv_not(&kb.known_zero());
                        v = crate::facts::known::bv_or(
                            &crate::facts::known::bv_and(&v, &keep),
                            &kb.known_one(),
                        );
                    }
                    out.push((key, v));
                }
                Answer::Sat(out)
            }
            sat::Answer::Unsat => {
                let failed = self.solver.failed_assumptions();
                let mut core: Vec<usize> = (0..pred_count)
                    .filter(|&k| failed.contains(&lits[k]))
                    .collect();
                if core.is_empty() && pred_count > 0 {
                    core = (0..pred_count).collect();
                }
                Answer::Unsat(core)
            }
            sat::Answer::Unknown => Answer::Unknown(Unknown::Budget {
                conflicts: self.solver.conflicts(),
                propagations: self.solver.propagations(),
            }),
        })
    }

    /// Does this backend report exact conflict counts (see [`Backend::exact_conflicts`])?
    pub(crate) fn exact_conflicts(&self) -> bool {
        self.solver.exact_conflicts()
    }

    /// Makes it safe across a [`Context::rollback`] to `at`, to be called before it: forgets
    /// which gates stand for the expressions created since the checkpoint. (Their gates and
    /// clauses stay, harmless and unused; a long session starts a new `Incremental` now and
    /// then.)
    pub fn forget_since(&mut self, at: Checkpoint) {
        self.bits.retain(|&i, _| i < at.nodes());
        self.symbols.retain(|&(i, _)| i < at.nodes());
        self.added.retain(|&i, _| i < at.nodes());
    }
}

/// A fixed family of feasibility questions. Every check requires the same Boolean `facts`
/// and binds any subset of the `observations` (words or predicates) to concrete values.
/// The family is simplified without target assumptions, blasted and encoded **once**.
/// The mutable context borrow freezes declarations and prevents rollback until the family
/// is dropped. A returned model is checked on the original facts and requested observations.
///
/// Unlike [`Incremental`], each search starts with a private copy of the unsearched SAT
/// state: no learned clause, phase or spent budget leaks from another target. This trades
/// copying the clause database for target-order independent answers, even at small limits.
/// Preparation uses one simplify budget and one circuit cap for the **whole catalog**;
/// each target gets the configured search limits. This is not the same circuit or search
/// as a standalone question. If preparation returns [`Unknown::TooLarge`], prepare a smaller
/// family or ask each original question separately: it says nothing about feasibility.
///
/// ```
/// use bitwright::{BitVec, Context, ParseOptions, Width};
/// use bitwright::prove::{Config, Prepared, Simplifiers};
///
/// let mut cx = Context::new();
/// let o = ParseOptions::width(Width::W8);
/// let fact = cx.parse("x + y == 7", &o)?;
/// let x = cx.parse("x", &o)?;
/// let goal = cx.parse("y == 4", &o)?;
/// let cfg = Config::default().with_sweeping(false);
/// let mut family = Prepared::new(&mut cx, &[fact], &[x, goal], &cfg, &Simplifiers::new())?
///     .expect("supported family within its circuit cap");
/// let three = BitVec::from_u64(Width::W8, 3).unwrap();
/// // Is there a counterexample to `goal` under `fact` and `x == 3`?
/// assert_eq!(family.check(&[(0, three), (1, BitVec::from_bool(false))])?, Ok(None));
/// assert!(family.check(&[(0, three)])?.unwrap().is_some());
/// # Ok::<(), bitwright::Error>(())
/// ```
#[derive(Debug)]
pub struct Prepared<'c> {
    cx: &'c mut Context,
    original: Vec<Expr>,
    facts: usize,
    outputs: Vec<Bits>,
    symbols: Vec<(SymbolKey, Width, Bits)>,
    sampling: Option<(Aig, SampleMode, u32)>,
    cnf: Cnf,
    template: Solver,
    limits: Limits,
}

impl<'c> Prepared<'c> {
    /// Prepare exact shared predicates (use `Assumptions::predicates` for scoped facts)
    /// and observed outputs, in the order used by [`check`](Self::check). Sampling, if
    /// enabled, only finds witnesses. Certificate requests, sweeping, word sampling,
    /// exhaustive enumeration, shared-sum rewriting and root-conditioned relational lemmas
    /// require the ordinary [`Question`] pipeline and return [`Unknown::Unsupported`] here.
    pub fn new(
        cx: &'c mut Context,
        facts: &[Expr],
        observations: &[Expr],
        cfg: &Config,
        simplifiers: &Simplifiers,
    ) -> Result<Result<Self, Unknown>, Error> {
        if cfg.certificate
            || cfg.sweeping
            || cfg.word_sampling
            || cfg.sample_mode == SampleMode::Words
            || cfg.exhaustive_inputs != 0
            || cfg.shared_sums
            || cfg.relational_lemmas
        {
            return Ok(Err(Unknown::Unsupported(
                "requested proof mode needs a standalone Question".into(),
            )));
        }
        for &fact in facts {
            let w = cx.width(fact)?;
            if w != Width::W1 {
                return Err(crate::WidthError::Mismatch {
                    left: 1,
                    right: w.bits(),
                }
                .into());
            }
        }
        let original: Vec<_> = facts.iter().chain(observations).copied().collect();
        let roots = if cfg.simplify || cfg.divisions {
            let engine = if cfg.simplify {
                simplifiers.engine(cfg.strict, cfg.proved_words)
            } else {
                simplifiers.divisions_only()
            };
            let run = crate::engine::Run::default().with_per_call(cfg.simplify_budget);
            engine
                .run(cx, &original, run)?
                .roots
                .iter()
                .map(|out| cx.id(out.expr))
                .collect::<Result<_, _>>()?
        } else {
            cx.ids(&original)?
        };
        let mut b = Blaster::new(cx, cfg.max_nodes);
        b.selector_hints = cfg.selector_branching;
        b.join_factoring = cfg.join_factoring;
        b.input_cancellation = cfg.input_cancellation;
        b.carry_save_multiplication = cfg.carry_save_multiplication;
        let mut outputs = Vec::with_capacity(roots.len());
        for root in roots {
            match b.blast(root) {
                Ok(bits) => outputs.push(bits),
                Err(e) => return Ok(Err(b.unknown(e)?)),
            }
        }
        if b.g.len() > cfg.max_nodes {
            return Ok(Err(Unknown::TooLarge { nodes: b.g.len() }));
        }
        // Include symbols erased by simplification, with their declared bits (or zero).
        let ids = b.cx.symbols_in(&original)?;
        let mut symbols = Vec::with_capacity(ids.len());
        for id in ids {
            let key = b.cx.symbol_key(id).unwrap();
            let node = b.cx.find_symbol(key).unwrap().index();
            let bits = b.bits.remove(&node).unwrap_or_else(|| {
                b.cx.declared_at(node)
                    .map(|known| super::blast::konst(&known.known_one()))
                    .unwrap_or_default()
            });
            symbols.push((key.clone(), b.cx.width_of(node), bits));
        }
        symbols.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        let mut template = Solver::new();
        let all: Vec<_> = outputs.iter().flatten().copied().collect();
        let cnf = Cnf::encode_with_xor3(&b.g, &all, &mut template, false, cfg.xor3_encoding);
        for selector in b.selectors {
            if let Some(l) = cnf.mapped_lit(selector) {
                template.prefer_selector(l);
            }
        }
        Ok(Ok(Self {
            cx: b.cx,
            original,
            facts: facts.len(),
            outputs,
            symbols,
            sampling: (cfg.samples != 0).then_some((b.g, cfg.sample_mode, cfg.samples.div_ceil(64))),
            cnf,
            template,
            limits: cfg.limits(),
        }))
    }

    /// Whether the facts hold with `observations[i] == value` for every `(i, value)`.
    /// `Ok(Some(model))` is a replayed witness; `Ok(None)` is unsatisfiable. An unknown
    /// (including budget exhaustion) is not a negative answer. Indices and widths are
    /// checked even if another binding is contradictory.
    pub fn check(
        &mut self,
        bindings: &[(usize, BitVec)],
    ) -> Result<Result<Option<Model>, Unknown>, Error> {
        let mut required: Vec<_> = self.outputs[..self.facts]
            .iter()
            .map(|bits| bits[0])
            .collect();
        for &(i, value) in bindings {
            let bits = self.outputs[self.facts..]
                .get(i)
                .ok_or_else(|| Error::Unsupported("unknown observation index".into()))?;
            if usize::from(value.width().bits()) != bits.len() {
                return Err(crate::WidthError::Mismatch {
                    left: bits.len() as u16,
                    right: value.width().bits(),
                }
                .into());
            }
            for (j, &bit) in bits.iter().enumerate() {
                required.push(bit ^ u32::from(value.bit(j as u16) != Some(true)));
            }
        }
        required.sort_unstable();
        required.dedup();
        if required.first() == Some(&super::aig::FALSE)
            || required.windows(2).any(|p| p[0] ^ 1 == p[1])
        {
            return Ok(Ok(None));
        }
        let required = required
            .strip_prefix(&[super::aig::TRUE])
            .unwrap_or(&required);
        if required.is_empty() {
            let model = Question::counterexample(&self.symbols, |l| l == super::aig::TRUE);
            return self.replay(bindings, model);
        }
        if let Some((g, mode, batches)) = &self.sampling {
            for batch in 0..*batches {
                let vals = g.eval_words(|k| match mode {
                    SampleMode::Random => super::sample(batch, k),
                    _ => super::small_sample(batch, k),
                });
                let lanes = required
                    .iter()
                    .fold(u64::MAX, |a, &l| a & Aig::word(&vals, l));
                if lanes != 0 {
                    let lane = lanes.trailing_zeros();
                    let model = Question::counterexample(&self.symbols, |l| {
                        Aig::word(&vals, l) >> lane & 1 != 0
                    });
                    return self.replay(bindings, model);
                }
            }
        }
        if self.limits.conflicts == 0 || self.limits.propagations == 0 {
            return Ok(Err(Unknown::Budget {
                conflicts: 0,
                propagations: 0,
            }));
        }
        // This search is disposable. Bind all selected bits at level zero, before
        // propagation, rather than paying a separate assumption level per output bit.
        let mut solver = self.template.clone();
        for &l in required {
            if !solver.bind_root(self.cnf.lit(l)) {
                return Ok(Ok(None));
            }
        }
        match solver.solve_within(self.limits) {
            sat::Answer::Unsat => Ok(Ok(None)),
            sat::Answer::Unknown => Ok(Err(Unknown::Budget {
                conflicts: solver.conflicts - self.template.conflicts,
                propagations: solver.propagations - self.template.propagations,
            })),
            sat::Answer::Sat(values) => {
                let model = Question::counterexample(&self.symbols, |l| self.cnf.value(l, &values));
                self.replay(bindings, model)
            }
        }
    }

    fn replay(
        &mut self,
        bindings: &[(usize, BitVec)],
        model: Model,
    ) -> Result<Result<Option<Model>, Unknown>, Error> {
        let roots: Vec<_> = self.original[..self.facts]
            .iter()
            .copied()
            .chain(bindings.iter().map(|&(i, _)| self.original[self.facts + i]))
            .collect();
        let env = crate::FnEnv(|key: &SymbolKey, _| {
            model.binary_search_by(|(k, _)| k.cmp(key)).ok().map(|i| model[i].1)
        });
        let values = self.cx.eval(&roots, &env)?;
        if values[..self.facts].iter().any(BitVec::is_zero)
            || bindings
                .iter()
                .zip(&values[self.facts..])
                .any(|((_, want), got)| want != got)
        {
            return Err(Error::Contract(
                "prepared model fails the original constraints".into(),
            ));
        }
        Ok(Ok(Some(model)))
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
