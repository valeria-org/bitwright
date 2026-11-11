//! A solver session: an assertion stack with `push` and `pop`, satisfiability checks with
//! models, checks under assumptions, and unsatisfiable cores.
//!
//! ```
//! use bitwright::solve::{Solver, Status};
//! use bitwright::{Context, ParseOptions, Width};
//!
//! let mut cx = Context::new();
//! let o = ParseOptions::width(Width::W32);
//! let mut s = Solver::default();
//! let hash = cx.parse("(x ^ 0x5bd1e995) * 0x9e3779b1 == 0x1234", &o)?;
//! s.assert(&cx, hash)?;
//! assert_eq!(s.check(&mut cx)?, Status::Sat);
//! let x = cx.parse("x", &o)?;
//! let v = s.value(&mut cx, x)?.unwrap();
//! s.push();
//! let other = cx.parse("x != 0", &o)?;
//! let pinned = cx.constant(&v)?;
//! let differs = cx.cmp(bitwright::CmpOp::Ne, x, pinned)?;
//! s.assert(&cx, other)?;
//! s.assert(&cx, differs)?;
//! // An odd multiplier is a bijection: no other preimage.
//! assert_eq!(s.check(&mut cx)?, Status::Unsat);
//! s.pop(1)?;
//! assert_eq!(s.check(&mut cx)?, Status::Sat);
//! # Ok::<(), bitwright::Error>(())
//! ```
//!
//! **What a check does.** Constant assertions first (construction folds many). An assertion
//! The others are
//! split into independent slices, the assertions that share no symbol with the rest
//! ([`Config::slice`]), and each slice is answered by the first of: the last model, evaluated
//! on it (a path condition that grows usually keeps its model); the answers remembered for
//! slices seen before, and for unsatisfiable subsets of this one ([`Config::cache_entries`]);
//! a quick attempt under a small budget ([`Config::quick`]), on a circuit and a search the
//! solver keeps from check to check ([`Config::incremental`]: each assertion is built once,
//! and what one search learns the next ones use); the whole prover ([`Config::prove`]: the
//! simplifier, then a circuit of its own), which is asked what is left of the slice once
//! each assertion that defines a symbol (`x == t`, `t` without `x`) is solved for it and `t`
//! put in its place ([`Config::solve_equations`]): the same question of fewer symbols, whose
//! model gives the symbol its value back. [`Solver::decided_by`] says which was the last
//! needed.
//!
//! **Cores.** After `Unsat`, [`Solver::unsat_core`] names assertions and assumptions that are
//! unsatisfiable together: the slice that is, less each member the quick attempt shows is
//! not needed ([`Config::minimize_cores`]). A core is sound, not minimal.

use std::collections::HashMap;

use crate::engine::Deadline;
use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::ops::{BinOp, UnOp};
use crate::prove::{self, Limits, Model, Outcome, Question, Unknown};
use crate::{BitVec, FnEnv, SymbolId, Width};

/// How a [`Solver`] checks.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct Config {
    /// The prover's configuration for the deciding attempt.
    pub prove: prove::Config,
    /// The quick attempt before it, if any: by default the circuit alone (no simplifier, no
    /// sweeping) under 1,000 conflicts and 50,000 circuit nodes, which settles most
    /// satisfiable path conditions for a fraction of what simplifying them first costs.
    pub quick: Option<prove::Config>,
    /// How many assignments a question is evaluated at before any search (none: no such
    /// stage). First the last model repaired at the level of words: a predicate that is
    /// false there is made true by solving it for one symbol through the operators that can
    /// be undone, which answers a question that is a chain of definitions without a
    /// circuit. Then every symbol all ones, then values drawn from zero, one, small numbers
    /// and any number. A hit is a model for the cost of evaluations; a miss costs them.
    pub probes: u32,
    /// The rounds of a local search after those assignments (none: no such stage): from
    /// the best of them, a predicate that is false is made true by a repair or a symbol of
    /// it is changed at random, and the change is kept when no more predicates are false
    /// than before (and now and then when more are). A model it reaches is evaluated.
    pub local_search: u32,
    /// Whether, with [`Answers`], the quick search of a shape of question it has decided
    /// before is given a few times the most conflicts it took there, where a later stage
    /// has decided that shape too: the questions it will not decide go on sooner.
    pub learn_budgets: bool,
    /// Whether, on the way to the prover, a symbol that occurs once under an operator that
    /// reaches every value by it (a sum, an exclusive or, a product by an odd constant, an
    /// equality) is taken out with the term it frees, and given its value back in the model.
    /// Off by default: the simplifier that follows reads the terms as they were written, and
    /// a question it decides by their form can be one it no longer decides.
    pub unconstrained: bool,
    /// Whether a question the quick search leaves open is asked again with its products,
    /// quotients and remainders of two unknowns as unknowns of their own, each defined only
    /// when a model gets it wrong: unsatisfiable so is unsatisfiable, and a model that
    /// satisfies what was asked is a model.
    pub abstraction: bool,
    /// Whether [`Solver::unsat_core`] drops what the quick attempt shows is not needed.
    pub minimize_cores: bool,
    /// The most members a core may have for that (each costs one quick attempt).
    pub minimize_cores_up_to: usize,
    /// Whether a check answers the assertions that share no symbol with the others on their
    /// own: smaller questions, answers that are remembered apart, and a core within one.
    pub slice: bool,
    /// The most slices whose answers are remembered (0: none); when full, all are forgotten.
    pub cache_entries: usize,
    /// Whether the quick attempt is made on one circuit and one search kept for the solver's
    /// life ([`prove::Incremental`]), not on new ones for each check.
    pub incremental: bool,
    /// The gates that circuit may hold before the solver starts another.
    pub incremental_nodes: usize,
    /// Whether an assertion `x == t` (`t` without `x`; also a Boolean symbol asserted or
    /// denied) is solved for `x` and substituted into the others before the prover is asked
    /// (the cheaper stages before it see the assertions as given). A model then has `x` at
    /// the value of `t`.
    pub solve_equations: bool,
    /// A simplifier of the host's, if any, run on what is left of a slice before the prover
    /// is asked: an engine linked with the host's rules (its own, or theorems imported from
    /// Lean with [`rules::lean_import`](crate::rules::lean_import)) makes them take part in
    /// solving. Each conjunct is simplified under the ones before it (so a rule guarded by
    /// a fact fires where an earlier conjunct states the fact), which leaves the
    /// conjunction what it was: answers and models are of the assertions as given.
    pub simplifier: Option<crate::engine::Engine>,
    /// Another SAT search than bitwright's own, if any ([`Backend`]): it searches the kept
    /// circuit, and after the prover it searches what the prover's simplifier left of a
    /// slice, with the rest of the prover's budget. With one, the prover's own search stops
    /// at [`backend_after`](Self::backend_after) conflicts: the simplifier and the cheap
    /// refutations run as ever, and the long searches go to the other solver.
    pub backend: Option<Backend>,
    /// The conflicts the prover's own search gets before [`backend`](Self::backend) takes
    /// over.
    pub backend_after: u64,
}

/// A maker of SAT searches for a [`Solver`]: each call returns a new, empty one.
#[derive(Clone)]
pub struct Backend(std::sync::Arc<dyn Fn() -> Box<dyn prove::Backend> + Send + Sync>);

impl Backend {
    /// `make` returns a new, empty search each time it is called.
    pub fn new(make: impl Fn() -> Box<dyn prove::Backend> + Send + Sync + 'static) -> Self {
        Backend(std::sync::Arc::new(make))
    }
}

impl core::fmt::Debug for Backend {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Backend(..)")
    }
}

impl Default for Config {
    fn default() -> Self {
        Config {
            prove: prove::Config::default(),
            quick: Some(Self::quick_default()),
            probes: 4,
            local_search: 0,
            learn_budgets: false,
            unconstrained: false,
            abstraction: false,
            minimize_cores: true,
            minimize_cores_up_to: 64,
            slice: true,
            cache_entries: 4096,
            incremental: true,
            incremental_nodes: 1 << 21,
            solve_equations: true,
            simplifier: None,
            backend: None,
            backend_after: 2_000,
        }
    }
}

setters!(Config {
    with_prove: prove: prove::Config,
    with_quick: quick: Option<prove::Config>,
    with_probes: probes: u32,
    with_local_search: local_search: u32,
    with_learn_budgets: learn_budgets: bool,
    with_abstraction: abstraction: bool,
    with_unconstrained: unconstrained: bool,
    with_minimize_cores: minimize_cores: bool,
    with_minimize_cores_up_to: minimize_cores_up_to: usize,
    with_slice: slice: bool,
    with_cache_entries: cache_entries: usize,
    with_incremental: incremental: bool,
    with_incremental_nodes: incremental_nodes: usize,
    with_solve_equations: solve_equations: bool,
    with_simplifier: simplifier: Option<crate::engine::Engine>,
    with_backend: backend: Option<Backend>,
    with_backend_after: backend_after: u64,
});

impl Config {
    /// The default [`quick`](Self::quick) attempt.
    pub fn quick_default() -> prove::Config {
        prove::Config::default()
            .with_simplify(false)
            .with_sweeping(false)
            .with_max_conflicts(1_000)
            .with_max_nodes(50_000)
    }
}

/// What an answer rests on: how far it can be checked without trusting what found it.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub enum Tier {
    /// A model, evaluated: the assertions are true at it, whatever stage found it.
    Model,
    /// Unsatisfiable by construction: an assertion folded to false as it was built.
    Folding,
    /// Unsatisfiable by a circuit of the assertions and a search, with nothing rewritten
    /// before: [`Solver::lean_theorem`] states it for an independent check.
    Search,
    /// Unsatisfiable after the simplifier: proved rules, the passes that are decision
    /// procedures, and (unless [`prove::Config::strict`] or
    /// [`proved_words`](prove::Config::proved_words) is set) the limb-arithmetic pass's
    /// derivations, which are not proved; then a circuit and a search of what was left.
    Simplifier,
    /// Unsatisfiable because the same assertions were answered so before by this solver:
    /// as good as that answer was.
    Earlier,
    /// Unsatisfiable by [`Answers`] from elsewhere: taken on the hashes of the assertions.
    Remembered,
}

impl core::fmt::Display for Tier {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Tier::Model => "model",
            Tier::Folding => "folding",
            Tier::Search => "search",
            Tier::Simplifier => "simplifier",
            Tier::Earlier => "earlier",
            Tier::Remembered => "remembered",
        })
    }
}

/// The answer of a check.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Status {
    /// The assertions hold together at [`Solver::model`].
    Sat,
    /// They hold at no value of the symbols.
    Unsat,
    /// Not decided: why.
    Unknown(Unknown),
}

/// What decided a check: of what its slices needed, the last in this order.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum DecidedBy {
    /// The assertions were constants.
    Constants,
    /// The model of the check before satisfies them.
    LastModel,
    /// An answer remembered from an earlier check.
    Cache,
    /// An answer from the solver's [`Answers`]: of another solver, context or run.
    Remembered,
    /// [`Config::probes`]: an assignment tried before any search.
    Probe,
    /// [`Config::quick`], on the circuit the solver keeps ([`Config::incremental`]).
    Incremental,
    /// [`Config::abstraction`]: products and divisions as unknowns, defined where a model
    /// needed it.
    Abstraction,
    /// [`Config::quick`].
    Quick,
    /// [`Config::prove`].
    Prover,
    /// [`Config::backend`], on what the prover's simplifier left.
    Backend,
}

/// A member of an unsatisfiable core.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum CoreItem {
    /// The assertion with this index (in assertion order, over the whole stack).
    Assertion(usize),
    /// The assumption with this index in the slice [`Solver::check_assuming`] was given.
    Assumption(usize),
}

/// A check's answer, what decided it, its core when deciding it gave one, and, of an
/// unsatisfiable one, the slice that is.
struct Decision {
    status: Status,
    by: Option<DecidedBy>,
    core: Option<Vec<CoreItem>>,
    scope: Option<Vec<(CoreItem, Expr)>>,
}

impl Decision {
    fn of(status: Status, by: Option<DecidedBy>) -> Self {
        Decision {
            status,
            by,
            core: None,
            scope: None,
        }
    }
}

/// A slice's answer: a model, complete over the slice's symbols, or none.
type Answer = Result<Option<Model>, Unknown>;

/// A slice's answer, what decided it, and, of an unsatisfiable one, positions in the slice
/// of members that conflict when the search named them.
type SliceAnswer = (Answer, DecidedBy, Option<Vec<usize>>);

/// Answers of slices, by their assertions in index order.
#[derive(Clone, Debug, Default)]
struct Cache {
    exact: HashMap<Vec<Expr>, Option<Model>>,
    /// The unsatisfiable ones, newest last: a slice that contains one is unsatisfiable too.
    unsat: Vec<Vec<Expr>>,
}

/// The decisions of the kept circuit on a shape after which its budget there is learned
/// ([`Config::learn_budgets`]).
const LEARNED_AFTER: u32 = 4;

/// A kept circuit is started again when it has more gates than this many times those of
/// the predicates being asked, and [`KEPT_SLACK`] more.
const KEPT_DEAD: usize = 4;
/// See [`KEPT_DEAD`].
const KEPT_SLACK: usize = 1 << 14;

/// The unsatisfiable slices a larger one is compared with, newest first.
const SUBSET_TESTS: usize = 256;

/// The check an answer is of: what was asked, and what came of it.
#[derive(Clone, Debug)]
struct Checked {
    /// The assertions and assumptions of the check, with what each is: all of them, or after
    /// `Unsat` the slice that is unsatisfiable.
    asked: Vec<(CoreItem, Expr)>,
    status: Status,
    by: Option<DecidedBy>,
    /// After `Unsat`: the core, once computed.
    core: Option<Vec<CoreItem>>,
}

/// An assertion stack and its checks. See the [module](self).
///
/// A solver holds expressions of one [`Context`], the one every method is given; it is
/// independent of the context otherwise, so several solvers may share one.
#[derive(Debug, Default)]
pub struct Solver {
    cfg: Config,
    assertions: Vec<Expr>,
    /// The number of assertions at each `push`.
    frames: Vec<usize>,
    /// The model of the last `Sat`, kept across checks (and pops) as a first guess.
    model: Option<Model>,
    last: Option<Checked>,
    cache: Cache,
    /// Answers from elsewhere and for elsewhere, when the solver was given any.
    answers: Option<Answers>,
    /// The circuit and search of the quick attempts, once one was made.
    circuit: Option<prove::Incremental<Box<dyn prove::Backend>>>,
    /// The conflicts of the last quick attempt on it.
    kept_conflicts: u64,
}

impl Solver {
    /// A solver with this configuration.
    pub fn new(cfg: Config) -> Self {
        Solver {
            cfg,
            ..Solver::default()
        }
    }

    /// The configuration.
    pub fn config(&self) -> &Config {
        &self.cfg
    }

    /// Gives the solver answers found elsewhere (by another solver, in another context, in
    /// an earlier run) to answer from, and to add its own to: see [`Answers`].
    #[must_use]
    pub fn with_answers(mut self, answers: Answers) -> Self {
        self.answers = Some(answers);
        self
    }

    /// The solver's [`Answers`], if it has any: those it was given and those it found since.
    pub fn answers(&self) -> Option<&Answers> {
        self.answers.as_ref()
    }

    /// Asserts the 1-bit `p`: its index among the assertions.
    pub fn assert(&mut self, cx: &Context, p: Expr) -> Result<usize, Error> {
        if cx.width(p)? != Width::W1 {
            return Err(Error::Unsupported("an assertion must be 1 bit".into()));
        }
        self.assertions.push(p);
        self.last = None;
        Ok(self.assertions.len() - 1)
    }

    /// The assertions, in order.
    pub fn assertions(&self) -> &[Expr] {
        &self.assertions
    }

    /// Opens a scope: a later [`pop`](Self::pop) drops the assertions made in it.
    pub fn push(&mut self) {
        self.frames.push(self.assertions.len());
    }

    /// Closes the `n` innermost scopes. An error, and nothing changes, when fewer are open.
    pub fn pop(&mut self, n: usize) -> Result<(), Error> {
        if n > self.frames.len() {
            return Err(Error::Unsupported(format!(
                "pop {n} with {} scopes open",
                self.frames.len()
            )));
        }
        if n > 0 {
            let keep = self.frames[self.frames.len() - n];
            self.frames.truncate(self.frames.len() - n);
            self.assertions.truncate(keep);
            self.last = None;
        }
        Ok(())
    }

    /// The number of open scopes.
    pub fn depth(&self) -> usize {
        self.frames.len()
    }

    /// Drops every assertion and scope, and the last model. Remembered answers stay: they
    /// are of the assertions, whichever scope those were in.
    pub fn reset(&mut self) {
        self.assertions.clear();
        self.frames.clear();
        self.model = None;
        self.last = None;
    }

    /// After a check answered [`Status::Unsat`]: its core as a Lean 4 theorem named `name`
    /// ([`prove::lean_theorem`]), which `lean` proves again by itself or does not, with a
    /// comment saying which stage decided it here. `None` after any other answer; an error
    /// when the core has an operation Lean's `BitVec` lacks.
    pub fn lean_theorem(&mut self, cx: &mut Context, name: &str) -> Result<Option<String>, Error> {
        let Some(core) = self.unsat_core(cx)? else {
            return Ok(None);
        };
        let Some(last) = &self.last else {
            return Ok(None);
        };
        let predicates: Vec<Expr> = (last.asked.iter())
            .filter(|(item, _)| core.contains(item))
            .map(|&(_, e)| e)
            .collect();
        let how = match last.by {
            Some(by) => format!("{by:?}"),
            None => "nothing".into(),
        };
        let comment = format!(
            "bitwright {}: unsatisfiable (decided by: {how}).\n\
             The statement is the conflicting assertions as given; the proof is Lean's own.",
            env!("CARGO_PKG_VERSION")
        );
        prove::lean_theorem(cx, name, &predicates, &comment).map(Some)
    }

    /// Makes the solver safe across a [`Context::rollback`] to `at`, to be called before it:
    /// forgets the last check and every remembered answer about an expression created since
    /// the checkpoint. An error, and nothing changes, when an assertion is one of those:
    /// pop the scopes that hold them first.
    ///
    /// ```
    /// use bitwright::solve::{Solver, Status};
    /// use bitwright::{Context, ParseOptions, Width};
    ///
    /// let (mut cx, mut s) = (Context::new(), Solver::default());
    /// let o = ParseOptions::width(Width::W32);
    /// let path = cx.parse("x * 3 <u 100", &o)?;
    /// s.assert(&cx, path)?;
    /// let (base, size) = (cx.checkpoint(), cx.len());
    /// for k in 0..1000u32 {
    ///     s.push();
    ///     let q = cx.parse(&format!("(x ^ {k}) + {k} == 77"), &o)?;
    ///     s.assert(&cx, q)?;
    ///     assert!(!matches!(s.check(&mut cx)?, Status::Unknown(_)));
    ///     s.pop(1)?;
    ///     s.forget_since(base)?;
    ///     cx.rollback(base)?;
    /// }
    /// // A thousand queries later the context holds what it held.
    /// assert_eq!(cx.len(), size);
    /// # Ok::<(), bitwright::Error>(())
    /// ```
    pub fn forget_since(&mut self, at: crate::Checkpoint) -> Result<(), Error> {
        let since = |e: &Expr| e.index() >= at.nodes();
        if self.assertions.iter().any(since) {
            return Err(Error::Unsupported(
                "an assertion was created after the checkpoint".into(),
            ));
        }
        self.last = None;
        self.cache.exact.retain(|key, _| !key.iter().any(since));
        self.cache.unsat.retain(|key| !key.iter().any(since));
        if let Some(c) = &mut self.circuit {
            c.forget_since(at);
        }
        Ok(())
    }

    /// Whether the assertions hold together.
    pub fn check(&mut self, cx: &mut Context) -> Result<Status, Error> {
        self.check_assuming(cx, &[])
    }

    /// Whether the assertions and the 1-bit `assumptions` hold together. The assumptions are
    /// of this check only.
    pub fn check_assuming(
        &mut self,
        cx: &mut Context,
        assumptions: &[Expr],
    ) -> Result<Status, Error> {
        self.check_within(cx, assumptions, None)
    }

    /// [`check_assuming`](Self::check_assuming), stopping once the deadline passes with
    /// [`Unknown::Deadline`]. The clock is read between attempts and every few thousand
    /// conflicts of a search; building a question (simplifying it, its circuit) is not
    /// interrupted, so a check may run past the deadline by that much: bound it with
    /// [`prove::Config::simplify_budget`] and [`prove::Config::max_nodes`].
    pub fn check_within(
        &mut self,
        cx: &mut Context,
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Status, Error> {
        for &a in assumptions {
            if cx.width(a)? != Width::W1 {
                return Err(Error::Unsupported("an assumption must be 1 bit".into()));
            }
        }
        let asked: Vec<(CoreItem, Expr)> = (self.assertions.iter().copied().enumerate())
            .map(|(i, e)| (CoreItem::Assertion(i), e))
            .chain(
                (assumptions.iter().copied().enumerate())
                    .map(|(i, e)| (CoreItem::Assumption(i), e)),
            )
            .collect();
        let d = self.decide(cx, &asked, deadline)?;
        self.last = Some(Checked {
            asked: d.scope.unwrap_or(asked),
            status: d.status.clone(),
            by: d.by,
            core: d.core,
        });
        Ok(d.status)
    }

    fn decide(
        &mut self,
        cx: &mut Context,
        asked: &[(CoreItem, Expr)],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Decision, Error> {
        // Constants: one false assertion is a core by itself.
        let mut open: Vec<(CoreItem, Expr)> = Vec::with_capacity(asked.len());
        for &(item, e) in asked {
            match cx.as_const(e)? {
                Some(v) if v.is_zero() => {
                    let mut d = Decision::of(Status::Unsat, Some(DecidedBy::Constants));
                    d.core = Some(vec![item]);
                    return Ok(d);
                }
                Some(_) => {}
                None => open.push((item, e)),
            }
        }
        // A kept circuit that is mostly of predicates no longer asked (popped, or assumed
        // once) is started again: every search pays for the gates that are there.
        if let Some(circuit) = &self.circuit {
            let es: Vec<Expr> = open.iter().map(|&(_, e)| e).collect();
            let live = circuit.nodes_of(cx, &es)?;
            if circuit.nodes() > live.saturating_mul(KEPT_DEAD).saturating_add(KEPT_SLACK) {
                self.circuit = None;
            }
        }
        let old = self.model.clone().unwrap_or_default();
        let mut model = old.clone();
        let mut by = DecidedBy::Constants;
        let mut unknown = None;
        for part in self.slices(cx, &open)? {
            let es: Vec<Expr> = part.iter().map(|&i| open[i].1).collect();
            let (answer, how, conflicting) = self.answer(cx, &es, &old, deadline)?;
            by = by.max(how);
            match answer {
                Ok(Some(m)) => {
                    for (key, v) in m {
                        match model.iter_mut().find(|(k, _)| *k == key) {
                            Some(slot) => slot.1 = v,
                            None => model.push((key, v)),
                        }
                    }
                }
                Ok(None) => {
                    let mut d = Decision::of(Status::Unsat, Some(how));
                    d.scope = Some(match conflicting {
                        Some(ks) => ks.iter().map(|&k| open[part[k]]).collect(),
                        None => part.iter().map(|&i| open[i]).collect(),
                    });
                    return Ok(d);
                }
                Err(Unknown::Deadline) => {
                    return Ok(Decision::of(Status::Unknown(Unknown::Deadline), None));
                }
                // Another slice may still be unsatisfiable.
                Err(why) => unknown = Some(why),
            }
        }
        if let Some(why) = unknown {
            return Ok(Decision::of(Status::Unknown(why), None));
        }
        self.model = Some(model);
        Ok(Decision::of(Status::Sat, Some(by)))
    }

    /// The assertions in independent groups: two are in one when a chain of shared symbols
    /// links them. Each group in order, the groups by their first member.
    fn slices(
        &mut self,
        cx: &mut Context,
        open: &[(CoreItem, Expr)],
    ) -> Result<Vec<Vec<usize>>, Error> {
        if open.is_empty() {
            return Ok(Vec::new());
        }
        if !self.cfg.slice || open.len() == 1 {
            return Ok(vec![(0..open.len()).collect()]);
        }
        fn root(parent: &mut [usize], mut i: usize) -> usize {
            while parent[i] != i {
                parent[i] = parent[parent[i]];
                i = parent[i];
            }
            i
        }
        let mut parent: Vec<usize> = (0..open.len()).collect();
        let mut first: HashMap<SymbolId, usize> = HashMap::new();
        for (i, &(_, e)) in open.iter().enumerate() {
            for sym in cx.symbols_in(&[e])? {
                match first.get(&sym) {
                    Some(&j) => {
                        let (a, b) = (root(&mut parent, i), root(&mut parent, j));
                        // The smaller index stays the root, so groups keep their order.
                        parent[a.max(b)] = a.min(b);
                    }
                    None => {
                        first.insert(sym, i);
                    }
                }
            }
        }
        let mut groups: Vec<Vec<usize>> = Vec::new();
        let mut group_of: HashMap<usize, usize> = HashMap::new();
        for i in 0..open.len() {
            let r = root(&mut parent, i);
            let g = *group_of.entry(r).or_insert_with(|| {
                groups.push(Vec::new());
                groups.len() - 1
            });
            groups[g].push(i);
        }
        Ok(groups)
    }

    /// Whether one slice's assertions hold together, and what decided it. A model changes
    /// only what it lists: with the last model, nothing.
    fn answer(
        &mut self,
        cx: &mut Context,
        es: &[Expr],
        old: &Model,
        deadline: Option<Deadline<'_>>,
    ) -> Result<SliceAnswer, Error> {
        if holds(cx, es, old)? {
            return Ok((Ok(Some(Vec::new())), DecidedBy::LastModel, None));
        }
        let mut key = es.to_vec();
        key.sort_by_key(|e| e.index());
        key.dedup();
        let caching = self.cfg.cache_entries > 0;
        if caching {
            match self.cache.exact.get(&key) {
                Some(Some(m)) => return Ok((Ok(Some(m.clone())), DecidedBy::Cache, None)),
                Some(None) => return Ok((Ok(None), DecidedBy::Cache, None)),
                None => {}
            }
            let contains = |sub: &Vec<Expr>| {
                sub.len() < key.len()
                    && sub
                        .iter()
                        .all(|e| key.binary_search_by_key(&e.index(), |k| k.index()).is_ok())
            };
            if (self.cache.unsat.iter().rev().take(SUBSET_TESTS)).any(contains) {
                return Ok((Ok(None), DecidedBy::Cache, None));
            }
        }
        // Answers from elsewhere, by what the slice is (not where it is): a model is
        // checked, an "unsatisfiable" is taken on the slice's hashes.
        let named = match &self.answers {
            Some(_) => Some(Answers::key(cx, es)?),
            None => None,
        };
        let mut skip_kept = false;
        let mut kept_budget: Option<u64> = None;
        if let (Some(answers), Some(name)) = (&self.answers, &named) {
            match answers.exact.get(&name.0) {
                Some(Some(m)) if holds(cx, es, m)? => {
                    let m = complete(cx, es, m)?;
                    if caching {
                        self.cache.exact.insert(key, Some(m.clone()));
                    }
                    return Ok((Ok(Some(m)), DecidedBy::Remembered, None));
                }
                Some(None) => {
                    if caching {
                        self.cache.unsat.push(key.clone());
                        self.cache.exact.insert(key, None);
                    }
                    return Ok((Ok(None), DecidedBy::Remembered, None));
                }
                _ => {}
            }
            // A shape the kept circuit has never decided, and something later has: not
            // tried again.
            let seen = answers.strategy.get(&name.1);
            skip_kept = seen.is_some_and(|s| s.kept == 0 && s.later > 0);
            // A shape the kept circuit has decided several times, and other stages too: it
            // is given a few times the most conflicts it ever took there, not the whole
            // quick budget, before the question goes on.
            if self.cfg.learn_budgets
                && let Some(s) = seen.filter(|s| s.kept >= LEARNED_AFTER && s.later > 0)
            {
                kept_budget = Some(s.conflicts.saturating_mul(4).max(32));
            }
        }
        if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
            return Ok((Err(Unknown::Deadline), DecidedBy::Cache, None));
        }
        if self.cfg.probes > 0
            && let Some(m) = match repair(cx, es, old)? {
                Some(m) => Some(m),
                None => match probe(cx, es, self.cfg.probes)? {
                    Some(m) => Some(m),
                    None if self.cfg.local_search > 0 => {
                        local_search(cx, es, old, self.cfg.local_search)?
                    }
                    None => None,
                },
            }
        {
            let answer = Some(m);
            if caching {
                self.cache.exact.insert(key, answer.clone());
            }
            if let (Some(answers), Some(name)) = (&mut self.answers, named) {
                answers.learn(name, &answer, DecidedBy::Probe, 0);
            }
            return Ok((Ok(answer), DecidedBy::Probe, None));
        }
        let mut unknown = None;
        let mut conflicting = None;
        // The quick attempt on the kept circuit stands in for the one on a new circuit.
        let kept = match self.cfg.quick {
            Some(quick) if self.cfg.incremental && !skip_kept => {
                let quick = match kept_budget {
                    Some(b) => quick.with_max_conflicts(quick.max_conflicts.min(b)),
                    None => quick,
                };
                self.kept_attempt(cx, es, &quick)?
            }
            _ => None,
        };
        // On the way to the prover (not before: rewriting an assertion each time a new
        // definition arrives would cost the kept circuit what it kept), the definitions are
        // solved and what is left is asked.
        let (mut left, mut trail) = if self.cfg.solve_equations && es.len() > 1 {
            solve_equations(cx, es)?
        } else {
            (es.to_vec(), Vec::new())
        };
        if self.cfg.unconstrained {
            let (rest, taken) = eliminate_unconstrained(cx, &left, &mut trail)?;
            left = rest;
            trail.extend(taken);
        }
        let left = match self.cfg.simplifier.clone() {
            Some(engine) => {
                // Each conjunct under the ones before it, as given: a rule whose guard is
                // a fact (`proves(y != 0)`) fires where an earlier conjunct states it, and
                // the conjunction of the results is the conjunction of what was given.
                let mut parts = Vec::new();
                let mut stack: Vec<Expr> = left.into_iter().rev().collect();
                while let Some(e) = stack.pop() {
                    match cx.view(e)? {
                        crate::View::Bin(BinOp::And, a, b) => stack.extend([b, a]),
                        _ => parts.push(e),
                    }
                }
                let mut under = crate::facts::Assumptions::new();
                let mut out = Vec::with_capacity(parts.len());
                for part in parts {
                    let run = crate::engine::Run {
                        assumptions: Some(&under),
                        ..Default::default()
                    };
                    out.push(engine.run(cx, &[part], run)?.roots[0].expr);
                    under.assume_true(cx, part)?;
                    if under.is_infeasible() {
                        // The facts of the conjuncts so far contradict each other.
                        out.push(cx.bool(false)?);
                        break;
                    }
                }
                out
            }
            None => left,
        };
        let all = conjunction(cx, &left)?;
        // With another search to follow, the prover's own stops early.
        let own = match &self.cfg.backend {
            Some(_) => {
                let cap = self.cfg.prove.max_conflicts.min(self.cfg.backend_after);
                self.cfg.prove.with_max_conflicts(cap)
            }
            None => self.cfg.prove,
        };
        let attempts = [
            (
                self.cfg.quick.filter(|_| !self.cfg.incremental),
                DecidedBy::Quick,
            ),
            (Some(own), DecidedBy::Prover),
            (
                self.cfg.backend.as_ref().map(|_| self.cfg.prove),
                DecidedBy::Backend,
            ),
        ];
        let abstract_ = match self.cfg.quick {
            Some(quick) if self.cfg.abstraction && kept.is_none() => {
                abstracted(cx, es, quick.limits())?
            }
            _ => None,
        };
        let attempts = (kept
            .into_iter()
            .map(|a| (None, DecidedBy::Incremental, Some(a))))
        .chain(
            abstract_
                .into_iter()
                .map(|a| (None, DecidedBy::Abstraction, Some(a))),
        )
        .chain(attempts.into_iter().map(|(cfg, by)| (cfg, by, None)));
        for (cfg, by, ready) in attempts {
            // (The kept circuit answered of the slice as given: its model is whole.)
            let ready_is_none = ready.is_none();
            let outcome = match (ready, cfg) {
                (Some(prove::IncrementalAnswer::Sat(m)), _) => Ok(Some(m)),
                (Some(prove::IncrementalAnswer::Unsat(ks)), _) => {
                    conflicting = Some(ks);
                    Ok(None)
                }
                (Some(prove::IncrementalAnswer::Unknown(why)), _) => Err(why),
                (None, Some(cfg)) if by == DecidedBy::Backend => {
                    self.backend_attempt(cx, all, &cfg, deadline)?
                }
                (None, Some(cfg)) => satisfy_within(cx, all, &cfg, deadline)?,
                (None, None) => continue,
            };
            let answer = match outcome {
                Ok(Some(mut found)) => {
                    // The symbols solved for, at the values of what they equal.
                    #[allow(clippy::collapsible_if)]
                    if !trail.is_empty() && ready_is_none {
                        let ts: Vec<Expr> = trail.iter().map(|&(_, t)| t).collect();
                        let values = eval_in(cx, &ts, &found)?;
                        for ((key, _), v) in trail.iter().zip(values) {
                            found.retain(|(k, _)| k != key);
                            found.push((key.clone(), v));
                        }
                    }
                    // Complete over the slice's symbols: one the prover left open is zero.
                    let mut m = Vec::new();
                    for sym in cx.symbols_in(es)? {
                        let (Some(k), Some(w)) =
                            (cx.symbol_key(sym).cloned(), cx.symbol_width(sym))
                        else {
                            continue;
                        };
                        let v = (found.iter().find(|(f, _)| *f == k))
                            .map_or_else(|| BitVec::zero(w), |&(_, v)| v);
                        m.push((k, v));
                    }
                    Some(m)
                }
                Ok(None) => None,
                Err(Unknown::Deadline) => return Ok((Err(Unknown::Deadline), by, None)),
                Err(why) => {
                    unknown = Some(why);
                    continue;
                }
            };
            if caching {
                if self.cache.exact.len() >= self.cfg.cache_entries {
                    self.cache = Cache::default();
                }
                if answer.is_none() {
                    self.cache.unsat.push(key.clone());
                }
                self.cache.exact.insert(key, answer.clone());
            }
            if let (Some(answers), Some(name)) = (&mut self.answers, named) {
                let used = self.kept_conflicts;
                answers.learn(name, &answer, by, used);
            }
            return Ok((Ok(answer), by, conflicting));
        }
        let why = unknown.unwrap_or_else(|| Unknown::Unsupported("no attempt configured".into()));
        Ok((Err(why), DecidedBy::Prover, None))
    }

    /// [`Config::backend`] on what the prover's simplifier left of `all`, within the
    /// prover's budget. (Its search is not interrupted: a deadline is read before it.)
    fn backend_attempt(
        &mut self,
        cx: &mut Context,
        all: Expr,
        cfg: &prove::Config,
        deadline: Option<Deadline<'_>>,
    ) -> Result<Answer, Error> {
        let Some(make) = &self.cfg.backend else {
            return Ok(Err(Unknown::Unsupported("no backend".into())));
        };
        if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
            return Ok(Err(Unknown::Deadline));
        }
        // The goal the prover posed (and simplified): the negation.
        let goal = cx.un(UnOp::Not, all)?;
        let left = if cfg.simplify {
            prove::simplified(cx, goal, cfg)?
        } else {
            goal
        };
        let predicate = cx.un(UnOp::Not, left)?;
        let mut circuit = prove::Incremental::on((make.0)(), cfg.max_nodes);
        Ok(match circuit.solve(cx, &[predicate], cfg.limits())? {
            // Equal to `all` everywhere: a model of one is a model of the other.
            prove::IncrementalAnswer::Sat(m) if holds(cx, &[all], &m)? => Ok(Some(m)),
            prove::IncrementalAnswer::Sat(_) => Err(Unknown::Unsupported(
                "the backend's model does not hold".into(),
            )),
            prove::IncrementalAnswer::Unsat(_) => Ok(None),
            prove::IncrementalAnswer::Unknown(why) => Err(why),
        })
    }

    /// The quick attempt on the kept circuit: its answer when it has one worth having (a
    /// model it gives is checked by evaluation; one that fails the check is no answer).
    fn kept_attempt(
        &mut self,
        cx: &mut Context,
        es: &[Expr],
        quick: &prove::Config,
    ) -> Result<Option<prove::IncrementalAnswer>, Error> {
        if (self.circuit.as_ref()).is_some_and(|c| c.nodes() > self.cfg.incremental_nodes) {
            self.circuit = None;
        }
        let circuit = (self.circuit).get_or_insert_with(|| {
            let search: Box<dyn prove::Backend> = match &self.cfg.backend {
                Some(make) => (make.0)(),
                None => Box::new(prove::sat::Solver::new()),
            };
            prove::Incremental::on(search, self.cfg.incremental_nodes.max(1) * 2)
                .with_question_nodes(quick.max_nodes)
        });
        let before = circuit.conflicts();
        let answer = circuit.solve(cx, es, quick.limits())?;
        self.kept_conflicts = circuit.conflicts().saturating_sub(before);
        Ok(match answer {
            prove::IncrementalAnswer::Sat(ref m) if !holds(cx, es, m)? => None,
            prove::IncrementalAnswer::Unknown(_) => None,
            decided => Some(decided),
        })
    }

    /// The answer of the last check, unless the assertions changed since.
    pub fn status(&self) -> Option<&Status> {
        self.last.as_ref().map(|c| &c.status)
    }

    /// What decided the last check, when it was decided.
    pub fn decided_by(&self) -> Option<DecidedBy> {
        self.last.as_ref().and_then(|c| c.by)
    }

    /// What the last check's answer rests on (`None` when it was not decided): a model is a
    /// model wherever it came from, and "unsatisfiable" is as strong as the weakest stage
    /// that said so of a slice.
    pub fn tier(&self) -> Option<Tier> {
        let last = self.last.as_ref()?;
        Some(match (&last.status, last.by?) {
            (Status::Sat, _) => Tier::Model,
            (Status::Unknown(_), _) => return None,
            (_, DecidedBy::Constants) => Tier::Folding,
            (_, DecidedBy::Remembered) => Tier::Remembered,
            (_, DecidedBy::Cache | DecidedBy::LastModel | DecidedBy::Probe) => Tier::Earlier,
            (_, DecidedBy::Incremental | DecidedBy::Quick | DecidedBy::Abstraction) => Tier::Search,
            (_, DecidedBy::Prover | DecidedBy::Backend) => Tier::Simplifier,
        })
    }

    /// After a check answered [`Status::Sat`]: values of the symbols at which the assertions
    /// hold. A symbol it does not list may take any value ([`value`](Self::value) reads it as
    /// zero).
    pub fn model(&self) -> Option<&Model> {
        match self.last.as_ref()?.status {
            Status::Sat => self.model.as_ref(),
            _ => None,
        }
    }

    /// After [`Status::Sat`]: the value of `e` in the model (`None` otherwise).
    pub fn value(&self, cx: &mut Context, e: Expr) -> Result<Option<BitVec>, Error> {
        let Some(m) = self.model() else {
            return Ok(None);
        };
        Ok(Some(eval_in(cx, &[e], m)?.remove(0)))
    }

    /// After a check answered [`Status::Unsat`]: assertions and assumptions of that check that
    /// are unsatisfiable together, in order (`None` otherwise). See the [module](self) on how
    /// small.
    pub fn unsat_core(&mut self, cx: &mut Context) -> Result<Option<Vec<CoreItem>>, Error> {
        let Some(last) = &self.last else {
            return Ok(None);
        };
        if last.status != Status::Unsat {
            return Ok(None);
        }
        if let Some(core) = &last.core {
            return Ok(Some(core.clone()));
        }
        // Constant-true members are never needed.
        let mut core: Vec<(CoreItem, Expr)> = Vec::new();
        for &(item, e) in &last.asked {
            if cx.as_const(e)?.is_none() {
                core.push((item, e));
            }
        }
        if let Some(quick) = self.cfg.quick
            && self.cfg.minimize_cores
            && core.len() <= self.cfg.minimize_cores_up_to
        {
            let mut i = 0;
            while i < core.len() && core.len() > 1 {
                let rest: Vec<Expr> = (core.iter().enumerate())
                    .filter(|&(k, _)| k != i)
                    .map(|(_, &(_, e))| e)
                    .collect();
                let all = conjunction(cx, &rest)?;
                if matches!(prove::satisfy(cx, all, &quick)?, Ok(None)) {
                    core.remove(i);
                } else {
                    i += 1;
                }
            }
        }
        let core: Vec<CoreItem> = core.into_iter().map(|(item, _)| item).collect();
        if let Some(last) = &mut self.last {
            last.core = Some(core.clone());
        }
        Ok(Some(core))
    }
}

/// `model` over exactly the symbols `es` read: one it does not list is zero.
fn complete(cx: &mut Context, es: &[Expr], model: &Model) -> Result<Model, Error> {
    let mut m = Vec::new();
    for sym in cx.symbols_in(es)? {
        let (Some(k), Some(w)) = (cx.symbol_key(sym).cloned(), cx.symbol_width(sym)) else {
            continue;
        };
        let v = (model.iter().find(|(f, _)| *f == k)).map_or_else(|| BitVec::zero(w), |&(_, v)| v);
        m.push((k, v));
    }
    Ok(m)
}

/// Answers kept outside any solver or context: whether sets of assertions hold together,
/// with a model when they do, by what the assertions are (their
/// [structural hashes](Context::structural_hash)), so that a question answered once is
/// answered from memory by any solver that is given them, in this process or a later one.
/// And, by the [shape](Context::shape_hashes) of a question, which stage decided ones like
/// it, so that a stage that never decides a shape is not tried on it again.
///
/// A solver given some ([`Solver::with_answers`]) reads them after its own memory and adds
/// what it finds ([`Solver::answers`]). The host keeps the value, merges it and writes it
/// where it likes ([`to_text`](Self::to_text), [`from_text`](Self::from_text)); bitwright
/// does no IO, and a solver's answers depend on its `Answers` only through what the host
/// gave it.
///
/// A remembered model is checked by evaluation before it is used. A remembered
/// "unsatisfiable" is taken on trust in two 64-bit hashes of every assertion of the slice:
/// [`DecidedBy::Remembered`] says an answer came this way.
///
/// ```
/// use bitwright::solve::{Answers, DecidedBy, Solver, Status};
/// use bitwright::{Context, ParseOptions, Width};
///
/// let o = ParseOptions::width(Width::W64);
/// let hard = "(x ^ y) + 2 * (x & y) + (x | z) - (x & z) - (x ^ z) != x + y";
/// let answers = {
///     let (mut cx, mut s) = (Context::new(), Solver::default().with_answers(Answers::new()));
///     let e = cx.parse(hard, &o)?;
///     s.assert(&cx, e)?;
///     assert_eq!(s.check(&mut cx)?, Status::Unsat);
///     assert_eq!(s.decided_by(), Some(DecidedBy::Prover));
///     s.answers().unwrap().to_text()
/// };
/// // Another process, another context:
/// let answers = Answers::from_text(&answers)?;
/// let (mut cx, mut s) = (Context::new(), Solver::default().with_answers(answers));
/// let e = cx.parse(hard, &o)?;
/// s.assert(&cx, e)?;
/// assert_eq!(s.check(&mut cx)?, Status::Unsat);
/// assert_eq!(s.decided_by(), Some(DecidedBy::Remembered));
/// # Ok::<(), bitwright::Error>(())
/// ```
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Answers {
    /// By the slice's assertions, each as its structural and shape hashes, sorted.
    exact: HashMap<Vec<(u64, u64)>, Option<Model>>,
    /// By the slice's shape: how often each kind of stage decided one.
    strategy: HashMap<u64, Decided>,
}

/// How often the kept circuit decided slices of a shape, and how often a later stage did.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
struct Decided {
    kept: u32,
    later: u32,
    /// The most conflicts a decision of the kept circuit took.
    conflicts: u64,
}

impl Answers {
    /// No answers yet.
    pub fn new() -> Self {
        Self::default()
    }

    /// The number of slices with an answer.
    pub fn len(&self) -> usize {
        self.exact.len()
    }

    /// Whether there is no answer.
    pub fn is_empty(&self) -> bool {
        self.exact.is_empty()
    }

    /// Adds the answers of `other` (where both have one, this one's stays: answers of one
    /// slice agree, and a model is checked where it is used).
    pub fn merge(&mut self, other: &Answers) {
        for (k, v) in &other.exact {
            self.exact.entry(k.clone()).or_insert_with(|| v.clone());
        }
        for (k, v) in &other.strategy {
            let d = self.strategy.entry(*k).or_default();
            d.kept = d.kept.saturating_add(v.kept);
            d.later = d.later.saturating_add(v.later);
            d.conflicts = d.conflicts.max(v.conflicts);
        }
    }

    /// The names of a slice: its assertions' hashes, and its shape.
    fn key(cx: &mut Context, es: &[Expr]) -> Result<(Vec<(u64, u64)>, u64), Error> {
        let shapes = cx.shape_hashes(es)?;
        let mut name = Vec::with_capacity(es.len());
        for (&e, &shape) in es.iter().zip(&shapes) {
            name.push((cx.structural_hash(e)?, shape));
        }
        name.sort_unstable();
        name.dedup();
        let mut shape = 0x736c_6963_6521u64;
        for &(_, s) in &name {
            shape = crate::hash::combine(shape, s);
        }
        Ok((name, shape))
    }

    fn learn(
        &mut self,
        (name, shape): (Vec<(u64, u64)>, u64),
        answer: &Option<Model>,
        by: DecidedBy,
        conflicts: u64,
    ) {
        // (An assignment that happened to satisfy says nothing of the searches.)
        if by != DecidedBy::Probe {
            let d = self.strategy.entry(shape).or_default();
            match by {
                DecidedBy::Incremental => {
                    d.kept = d.kept.saturating_add(1);
                    d.conflicts = d.conflicts.max(conflicts);
                }
                _ => d.later = d.later.saturating_add(1),
            }
        }
        // A model with a symbol that is of its context is of no use in another.
        let portable =
            (answer.iter().flatten()).all(|(k, _)| !matches!(k, crate::SymbolKey::Fresh(_)));
        if portable {
            self.exact.insert(name, answer.clone());
        }
    }

    /// The answers as text: a header naming the versions they are of, then a line each, in
    /// an order that is the same for the same answers.
    pub fn to_text(&self) -> String {
        use core::fmt::Write;
        let mut out = format!(
            "bitwright-answers 1 hash {} crate {}\n",
            crate::HASH_VERSION,
            env!("CARGO_PKG_VERSION")
        );
        let mut names: Vec<&Vec<(u64, u64)>> = self.exact.keys().collect();
        names.sort();
        for name in names {
            let answer = &self.exact[name];
            out.push_str(if answer.is_some() { "s" } else { "u" });
            for (h, s) in name {
                let _ = write!(out, " {h:016x}:{s:016x}");
            }
            for (k, v) in answer.iter().flatten() {
                let _ = match k {
                    crate::SymbolKey::U64(n) => write!(out, " | #{n} {v}"),
                    crate::SymbolKey::Str(name) => {
                        out.push_str(" | $");
                        name.bytes().for_each(|b| {
                            let _ = write!(out, "{b:02x}");
                        });
                        write!(out, " {v}")
                    }
                    crate::SymbolKey::Fresh(_) => Ok(()),
                };
            }
            out.push('\n');
        }
        let mut shapes: Vec<(&u64, &Decided)> = self.strategy.iter().collect();
        shapes.sort_by_key(|&(shape, _)| *shape);
        for (shape, d) in shapes {
            let _ = writeln!(out, "t {shape:016x} {} {} {}", d.kept, d.later, d.conflicts);
        }
        out
    }

    /// Answers from [`to_text`](Self::to_text). Text written under another hash or crate
    /// version reads as no answers; text that is not answers is an error.
    pub fn from_text(text: &str) -> Result<Self, Error> {
        let bad = |what: &str| Error::Unsupported(format!("not a store of answers: {what}"));
        let mut lines = text.lines();
        let header: Vec<&str> = lines.next().unwrap_or_default().split(' ').collect();
        let &["bitwright-answers", "1", "hash", hash, "crate", version] = header.as_slice() else {
            return Err(bad("the header"));
        };
        let mut out = Answers::new();
        if hash.parse() != Ok(crate::HASH_VERSION) || version != env!("CARGO_PKG_VERSION") {
            return Ok(out);
        }
        let hex = |s: &str| u64::from_str_radix(s, 16).map_err(|_| bad("a hash"));
        for line in lines {
            let mut parts = line.split(" | ");
            let mut head = parts.next().unwrap_or_default().split(' ');
            match head.next() {
                Some("t") => {
                    let (Some(shape), Some(kept), Some(later)) =
                        (head.next(), head.next(), head.next())
                    else {
                        return Err(bad("a shape's line"));
                    };
                    let d = Decided {
                        kept: kept.parse().map_err(|_| bad("a count"))?,
                        later: later.parse().map_err(|_| bad("a count"))?,
                        // (Absent from stores written before it was kept.)
                        conflicts: match head.next() {
                            Some(c) => c.parse().map_err(|_| bad("a count"))?,
                            None => 0,
                        },
                    };
                    out.strategy.insert(hex(shape)?, d);
                }
                Some(kind @ ("s" | "u")) => {
                    let mut name = Vec::new();
                    for pair in head {
                        let (h, s) = pair.split_once(':').ok_or_else(|| bad("an assertion"))?;
                        name.push((hex(h)?, hex(s)?));
                    }
                    let mut model = Vec::new();
                    for binding in parts {
                        let (k, v) = binding.split_once(' ').ok_or_else(|| bad("a binding"))?;
                        let key = if let Some(n) = k.strip_prefix('#') {
                            crate::SymbolKey::U64(n.parse().map_err(|_| bad("a symbol"))?)
                        } else if let Some(h) = k.strip_prefix('$') {
                            let bytes: Option<Vec<u8>> = (0..h.len() / 2)
                                .map(|i| u8::from_str_radix(h.get(2 * i..2 * i + 2)?, 16).ok())
                                .collect();
                            let name = bytes.and_then(|b| String::from_utf8(b).ok());
                            crate::SymbolKey::from(name.ok_or_else(|| bad("a symbol"))?)
                        } else {
                            return Err(bad("a symbol"));
                        };
                        model.push((key, BitVec::parse(v).map_err(|_| bad("a value"))?));
                    }
                    out.exact.insert(name, (kind == "s").then_some(model));
                }
                _ => return Err(bad("a line")),
            }
        }
        Ok(out)
    }
}

/// The most symbols one check solves for.
const SOLVED_SYMBOLS: usize = 4096;

/// The rounds of [`eliminate_unconstrained`]: each takes out the symbols used once, and what
/// stands for the terms they were in may be used once in turn.
const UNCONSTRAINED_ROUNDS: usize = 16;

/// The inverse of an odd number modulo two to its width.
fn odd_inverse(c: &BitVec) -> Option<BitVec> {
    if c.bit(0) != Some(true) {
        return None;
    }
    let two = BitVec::wrapping_from_u64(c.width(), 2);
    let mut inv = *c;
    // Each round doubles the bits that are right, from three.
    for _ in 0..10 {
        let ci = BitVec::apply_bin(BinOp::Mul, c, &inv).ok()?;
        let f = BitVec::apply_bin(BinOp::Sub, &two, &ci).ok()?;
        inv = BitVec::apply_bin(BinOp::Mul, &inv, &f).ok()?;
    }
    Some(inv)
}

/// Takes out what is not constrained: a symbol that occurs once, under an operator that
/// reaches every value by it (a sum, a difference, an exclusive or, a complement, a negation,
/// a product by an odd constant, an equality), leaves the operator's result free, so a new
/// symbol stands for the result, and so on upward. What is left holds together exactly when
/// what was given does, and each symbol taken out comes with what it equals over the symbols
/// left, for the model.
///
/// `prior` is a trail made before (symbols solved for, with what they equal): what it reads
/// is kept right as symbols are taken out.
fn eliminate_unconstrained(
    cx: &mut Context,
    es: &[Expr],
    prior: &mut [(crate::SymbolKey, Expr)],
) -> Result<Solved, Error> {
    use crate::View;
    use crate::ops::CmpOp;
    let mut now = es.to_vec();
    let mut trail: Vec<(Expr, Expr)> = Vec::new();
    for _ in 0..UNCONSTRAINED_ROUNDS {
        let order = cx.post_order(&now)?;
        let mut uses: HashMap<Expr, u32> = HashMap::with_capacity(order.len());
        for &r in &now {
            *uses.entry(r).or_insert(0) += 1;
        }
        for &n in &order {
            let children: Vec<Expr> = cx.children(n)?.collect();
            for c in children {
                *uses.entry(c).or_insert(0) += 1;
            }
        }
        let free = |cx: &Context, e: Expr| -> Result<bool, Error> {
            Ok(uses.get(&e) == Some(&1)
                && cx.symbol_id(e)?.is_some()
                && cx.declared_known(e)?.is_none())
        };
        // The terms that are free, each with its new symbol, and the symbol taken out with
        // what it equals.
        let mut nodes: Vec<(Expr, Expr)> = Vec::new();
        let mut symbols: Vec<(Expr, Expr)> = Vec::new();
        for &n in &order {
            let w = cx.width(n)?;
            let taken = |symbols: &[(Expr, Expr)], e: Expr| symbols.iter().any(|&(s, _)| s == e);
            match cx.view(n)? {
                View::Un(op @ (UnOp::Not | UnOp::Neg), a) if free(cx, a)? => {
                    let v = cx.fresh_symbol(w)?;
                    let d = cx.un(op, v)?;
                    nodes.push((n, v));
                    symbols.push((a, d));
                }
                View::Bin(op @ (BinOp::Add | BinOp::Sub | BinOp::Xor), a, b) => {
                    let (x, other, left) = if free(cx, a)? && !taken(&symbols, a) {
                        (a, b, true)
                    } else if free(cx, b)? && !taken(&symbols, b) {
                        (b, a, false)
                    } else {
                        continue;
                    };
                    let v = cx.fresh_symbol(w)?;
                    let d = match (op, left) {
                        (BinOp::Add, _) => cx.bin(BinOp::Sub, v, other)?,
                        (BinOp::Sub, true) => cx.bin(BinOp::Add, v, other)?,
                        (BinOp::Sub, false) => cx.bin(BinOp::Sub, other, v)?,
                        _ => cx.bin(BinOp::Xor, v, other)?,
                    };
                    nodes.push((n, v));
                    symbols.push((x, d));
                }
                View::Bin(BinOp::Mul, a, b) => {
                    let (x, c) = match (cx.as_const(a)?, cx.as_const(b)?) {
                        (Some(c), None) => (b, c),
                        (None, Some(c)) => (a, c),
                        _ => continue,
                    };
                    let Some(inv) = odd_inverse(&c) else { continue };
                    if !free(cx, x)? {
                        continue;
                    }
                    let v = cx.fresh_symbol(w)?;
                    let inv = cx.constant(&inv)?;
                    let d = cx.bin(BinOp::Mul, v, inv)?;
                    nodes.push((n, v));
                    symbols.push((x, d));
                }
                View::Cmp(op @ (CmpOp::Eq | CmpOp::Ne), a, b) => {
                    let (x, other) = if free(cx, a)? && !taken(&symbols, a) {
                        (a, b)
                    } else if free(cx, b)? && !taken(&symbols, b) {
                        (b, a)
                    } else {
                        continue;
                    };
                    // Equal to the other side, or one more: whichever the result says.
                    let v = cx.fresh_symbol(Width::W1)?;
                    let one = cx.constant(&BitVec::wrapping_from_u64(cx.width(x)?, 1))?;
                    let next = cx.bin(BinOp::Add, other, one)?;
                    let d = if op == CmpOp::Eq {
                        cx.select(v, other, next)?
                    } else {
                        cx.select(v, next, other)?
                    };
                    nodes.push((n, v));
                    symbols.push((x, d));
                }
                _ => {}
            }
        }
        if nodes.is_empty() {
            break;
        }
        // A term under a term taken out goes with it: its symbol is not constrained either,
        // and what it equals is not needed (any value will do), but is kept right.
        now = cx.substitute(&now, &nodes)?;
        let mut all = nodes.clone();
        let written: Vec<Expr> = symbols.iter().map(|&(_, d)| d).collect();
        let written = cx.substitute(&written, &nodes)?;
        for (k, d) in written.into_iter().enumerate() {
            symbols[k].1 = d;
        }
        all.extend(symbols.iter().copied());
        // The earlier ones may read a symbol taken out now, or a term replaced now.
        let earlier: Vec<Expr> = trail.iter().map(|&(_, d)| d).collect();
        let earlier = cx.substitute(&earlier, &all)?;
        for (k, d) in earlier.into_iter().enumerate() {
            trail[k].1 = d;
        }
        let before: Vec<Expr> = prior.iter().map(|&(_, d)| d).collect();
        let before = cx.substitute(&before, &all)?;
        for (k, d) in before.into_iter().enumerate() {
            prior[k].1 = d;
        }
        trail.extend(symbols);
    }
    let mut keyed = Vec::with_capacity(trail.len());
    for (sym, d) in trail {
        if let Some(key) = cx.symbol_id(sym)?.and_then(|id| cx.symbol_key(id)).cloned() {
            keyed.push((key, d));
        }
    }
    Ok((now, keyed))
}

/// What is left of a slice once its definitions are solved, and the model trail: each symbol
/// solved for with what it equals.
type Solved = (Vec<Expr>, Vec<(crate::SymbolKey, Expr)>);

/// Solves the assertions that define a symbol and substitutes the solutions into the others:
/// what is left of them (in order), and each symbol solved for with what it equals (over
/// symbols not solved for). The assertions given hold together exactly when those left do,
/// and a model of those extends to one of all by giving each solved symbol the value of what
/// it equals.
fn solve_equations(cx: &mut Context, es: &[Expr]) -> Result<Solved, Error> {
    struct Solution {
        key: crate::SymbolKey,
        equals: Expr,
        /// The symbols `equals` reads.
        reads: Vec<SymbolId>,
    }
    let mut solutions: Vec<Solution> = Vec::new();
    let mut map: Vec<(Expr, Expr)> = Vec::new();
    let mut kept: Vec<Expr> = Vec::new();
    for &e in es {
        // Under the solutions so far, which read no solved symbol: neither does `now`.
        let now = if map.is_empty() {
            e
        } else {
            cx.substitute(&[e], &map)?[0]
        };
        let definition = if solutions.len() < SOLVED_SYMBOLS {
            definition(cx, now)?
        } else {
            None
        };
        let Some((symbol, id, equals, reads)) = definition else {
            kept.push(e);
            continue;
        };
        let Some(key) = cx.symbol_key(id).cloned() else {
            kept.push(e);
            continue;
        };
        // The earlier solutions that read the symbol now read what it equals.
        for (k, s) in solutions.iter_mut().enumerate() {
            if s.reads.contains(&id) {
                s.equals = cx.substitute(&[s.equals], &[(symbol, equals)])?[0];
                s.reads = cx.symbols_in(&[s.equals])?;
                map[k].1 = s.equals;
            }
        }
        map.push((symbol, equals));
        solutions.push(Solution { key, equals, reads });
    }
    if !map.is_empty() {
        kept = cx.substitute(&kept, &map)?;
    }
    Ok((
        kept,
        solutions.into_iter().map(|s| (s.key, s.equals)).collect(),
    ))
}

/// A symbol `p` defines and what it defines it as: `x == t` with `x` a symbol `t` does not
/// read and nothing was declared of ([`Context::declare_known`]), or a 1-bit symbol asserted
/// or denied. With the symbol's id and the symbols `t` reads.
#[allow(clippy::type_complexity)]
fn definition(
    cx: &mut Context,
    p: Expr,
) -> Result<Option<(Expr, SymbolId, Expr, Vec<SymbolId>)>, Error> {
    use crate::View;
    let free = |cx: &Context, e: Expr| -> Result<Option<SymbolId>, Error> {
        Ok(match cx.view(e)? {
            View::Sym(id) if cx.declared_known(e)?.is_none() => Some(id),
            _ => None,
        })
    };
    let candidates: Vec<(Expr, Expr)> = match cx.view(p)? {
        View::Cmp(crate::CmpOp::Eq, a, b) => vec![(a, b), (b, a)],
        View::Sym(_) => vec![(p, cx.bool(true)?)],
        View::Un(UnOp::Not, a) => vec![(a, cx.bool(false)?)],
        _ => Vec::new(),
    };
    for (x, t) in candidates {
        let Some(id) = free(cx, x)? else { continue };
        let reads = cx.symbols_in(&[t])?;
        if !reads.contains(&id) {
            return Ok(Some((x, id, t, reads)));
        }
    }
    Ok(None)
}

/// [`prove::satisfy`] that also stops at a deadline: the search runs in slices, the clock
/// read between them.
fn satisfy_within(
    cx: &mut Context,
    p: Expr,
    cfg: &prove::Config,
    deadline: Option<Deadline<'_>>,
) -> Result<Result<Option<Model>, Unknown>, Error> {
    let Some(deadline) = deadline else {
        return prove::satisfy(cx, p, cfg);
    };
    let passed = || deadline.clock.now_ticks() >= deadline.at;
    if passed() {
        return Ok(Err(Unknown::Deadline));
    }
    let np = cx.un(UnOp::Not, p)?;
    let mut q = Question::valid(cx, np, cfg)?;
    let total = cfg.limits();
    loop {
        let done = q.stats();
        let slice = Limits {
            conflicts: (total.conflicts.saturating_sub(done.conflicts)).min(SLICE_CONFLICTS),
            propagations: (total.propagations.saturating_sub(done.propagations))
                .min(SLICE_PROPAGATIONS),
        };
        match q.solve(cx, slice)? {
            Outcome::Proved(_) => return Ok(Ok(None)),
            Outcome::Refuted(m) => return Ok(Ok(Some(m))),
            Outcome::Unknown(Unknown::Budget { .. }) => {
                let done = q.stats();
                if done.conflicts >= total.conflicts || done.propagations >= total.propagations {
                    return Ok(Err(Unknown::Budget {
                        conflicts: done.conflicts,
                        propagations: done.propagations,
                    }));
                }
                if passed() {
                    return Ok(Err(Unknown::Deadline));
                }
            }
            Outcome::Unknown(why) => return Ok(Err(why)),
        }
    }
}

/// The search between two readings of a deadline's clock: a few milliseconds.
const SLICE_CONFLICTS: u64 = 2_000;
const SLICE_PROPAGATIONS: u64 = 2_000_000;

/// The conjunction of 1-bit expressions (true of none).
fn conjunction(cx: &mut Context, ps: &[Expr]) -> Result<Expr, Error> {
    let mut all = cx.bool(true)?;
    for &p in ps {
        all = cx.bin(BinOp::And, all, p)?;
    }
    Ok(all)
}

/// The expressions at `model`, a symbol it does not list as zero.
fn eval_in(cx: &mut Context, es: &[Expr], model: &Model) -> Result<Vec<BitVec>, Error> {
    let env = FnEnv(|key: &crate::SymbolKey, w: Width| {
        Some((model.iter().find(|(k, _)| k == key)).map_or_else(|| BitVec::zero(w), |&(_, v)| v))
    });
    cx.eval(es, &env)
}

/// A model of `es` among `tries` assignments: every symbol all ones, then each symbol a
/// value drawn from its name's place and the try's number (zero, all ones, one, a small
/// number or any value), the same for the same question.
fn probe(cx: &mut Context, es: &[Expr], tries: u32) -> Result<Option<Model>, Error> {
    let mut symbols = Vec::new();
    for sym in cx.symbols_in(es)? {
        if let (Some(k), Some(w)) = (cx.symbol_key(sym).cloned(), cx.symbol_width(sym)) {
            symbols.push((k, w));
        }
    }
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    for t in 0..tries {
        let model: Model = (symbols.iter())
            .map(|(k, w)| {
                let r = next();
                let v = match if t == 0 { 1 } else { r % 6 } {
                    0 => BitVec::zero(*w),
                    1 => BitVec::ones(*w),
                    2 => BitVec::wrapping_from_u64(*w, 1),
                    3 => BitVec::wrapping_from_u64(*w, next() % 256),
                    _ => BitVec::wrapping_from_u64(*w, next()),
                };
                (k.clone(), v)
            })
            .collect();
        if holds(cx, es, &model)? {
            return Ok(Some(model));
        }
    }
    Ok(None)
}

/// The rounds of [`abstracted`], and the definitions a round may add.
const ABSTRACTION_ROUNDS: usize = 12;
/// See [`ABSTRACTION_ROUNDS`].
const ABSTRACTION_LEMMAS: usize = 4;

/// `es` with every product, quotient and remainder of two unknowns (16 bits or more) as an
/// unknown of its own: whether they hold together, a definition added for each unknown a
/// model gave another value than its operands make. `None` when there is none to take out,
/// or the rounds or `limits` end first.
fn abstracted(
    cx: &mut Context,
    es: &[Expr],
    limits: prove::Limits,
) -> Result<Option<prove::IncrementalAnswer>, Error> {
    use crate::View;
    let mut hard: Vec<(Expr, BinOp, Expr, Expr)> = Vec::new();
    for e in cx.post_order(es)? {
        if let View::Bin(
            op @ (BinOp::Mul
            | BinOp::UMulHi
            | BinOp::SMulHi
            | BinOp::UDiv
            | BinOp::URem
            | BinOp::SDiv
            | BinOp::SRem),
            a,
            b,
        ) = cx.view(e)?
            && cx.width(e)?.bits() >= 16
            && cx.as_const(a)?.is_none()
            && cx.as_const(b)?.is_none()
        {
            hard.push((e, op, a, b));
        }
    }
    if hard.is_empty() {
        return Ok(None);
    }
    let mut map = Vec::with_capacity(hard.len());
    for &(e, ..) in &hard {
        let w = cx.width(e)?;
        map.push((e, cx.fresh_symbol(w)?));
    }
    let asked = cx.substitute(es, &map)?;
    // Each unknown is what its operator makes of its operands, as abstracted.
    let mut definitions = Vec::with_capacity(hard.len());
    for (k, &(_, op, a, b)) in hard.iter().enumerate() {
        let ab = cx.substitute(&[a, b], &map)?;
        let made = cx.bin(op, ab[0], ab[1])?;
        definitions.push(cx.cmp(crate::CmpOpExt::Eq, map[k].1, made)?);
    }
    let mut circuit = prove::Incremental::new(1 << 22);
    let mut question = asked;
    for _ in 0..ABSTRACTION_ROUNDS {
        match circuit.solve(cx, &question, limits)? {
            prove::IncrementalAnswer::Sat(m) => {
                if holds(cx, es, &m)? {
                    return Ok(Some(prove::IncrementalAnswer::Sat(m)));
                }
                let values = eval_in(cx, &definitions, &m)?;
                let wrong: Vec<Expr> = (definitions.iter().zip(&values))
                    .filter(|&(d, v)| v.is_zero() && !question.contains(d))
                    .map(|(&d, _)| d)
                    .take(ABSTRACTION_LEMMAS)
                    .collect();
                if wrong.is_empty() {
                    return Ok(None);
                }
                question.extend(wrong);
            }
            prove::IncrementalAnswer::Unsat(_) => {
                // (Which of the assertions conflict is not read off the abstraction.)
                return Ok(Some(prove::IncrementalAnswer::Unsat(
                    (0..es.len()).collect(),
                )));
            }
            _ => return Ok(None),
        }
    }
    Ok(None)
}

/// The predicates a repair makes true one after another, and the operators it looks through
/// for all of them, before it gives up.
const REPAIRS: usize = 8;
/// See [`REPAIRS`].
const REPAIR_STEPS: u32 = 256;
/// The nodes a repair's steps may evaluate together, about: a question of more nodes than
/// this has the fewest steps.
const REPAIR_WORK: u32 = 1 << 19;

/// A model of `es` made from `start` at the level of words: while a predicate is false, it
/// is made true by giving one symbol the value that does it, found by going down through the
/// operators that can be undone (an equality to either side, sums, differences, exclusive
/// ors, complements, products by an odd constant, masks, shifts, extensions, extracts,
/// concatenations and selections, and for an order the value beside the bound). A symbol is
/// given a value at most twice. `None` when that does not end in a model: nothing is taken on trust,
/// the result is evaluated.
fn repair(cx: &mut Context, es: &[Expr], start: &Model) -> Result<Option<Model>, Error> {
    // Each step evaluates part of the question: fewer of them for a large one.
    let size = match cx.dag_size(es, REPAIR_WORK)? {
        crate::Bounded::Exact(n) => n.max(1),
        _ => REPAIR_WORK,
    };
    let mut r = Repair {
        model: complete(cx, es, start)?,
        fixed: Vec::new(),
        partial: false,
        steps: (REPAIR_WORK / size).clamp(8, REPAIR_STEPS),
    };
    // The symbols of each predicate looked at, once.
    let mut symbols: Vec<Option<Vec<crate::SymbolKey>>> = vec![None; es.len()];
    for _ in 0..REPAIRS {
        let values = eval_in(cx, es, &r.model)?;
        // Of the false ones, the one with the fewest symbols still open: a definition
        // before what uses it.
        let mut best: Option<(usize, usize)> = None;
        for k in (0..es.len()).filter(|&k| values[k].is_zero()) {
            if symbols[k].is_none() {
                let ids = cx.symbols_in(&[es[k]])?;
                symbols[k] = Some(
                    ids.iter()
                        .filter_map(|&id| cx.symbol_key(id).cloned())
                        .collect(),
                );
            }
            let open = (symbols[k].iter().flatten())
                .filter(|key| !r.fixed.contains(key))
                .count();
            if best.is_none_or(|(_, n)| open < n) {
                best = Some((k, open));
            }
        }
        let Some((k, _)) = best else {
            return Ok(Some(r.model));
        };
        if !r.make(cx, es[k], true)? {
            return Ok(None);
        }
    }
    Ok(holds(cx, es, &r.model)?.then_some(r.model))
}

/// A model of `es` by a walk from `start`: each round takes a predicate that is false and
/// makes it true by a repair, or changes one of its symbols at random (a bit, or the whole
/// value), and keeps the change when no more predicates are false than before, or one time
/// in eight anyway. `None` when `rounds` end first; a model returned is evaluated.
fn local_search(
    cx: &mut Context,
    es: &[Expr],
    start: &Model,
    rounds: u32,
) -> Result<Option<Model>, Error> {
    let mut model = complete(cx, es, start)?;
    if model.is_empty() {
        return Ok(None);
    }
    let mut state = 0x243f_6a88_85a3_08d3u64;
    let mut next = move || {
        state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    let falses = |cx: &mut Context, m: &Model| -> Result<Vec<usize>, Error> {
        let values = eval_in(cx, es, m)?;
        Ok((0..es.len()).filter(|&k| values[k].is_zero()).collect())
    };
    let mut wrong = falses(cx, &model)?;
    for _ in 0..rounds {
        if wrong.is_empty() {
            return Ok(Some(model));
        }
        let k = wrong[(next() % wrong.len() as u64) as usize];
        let mut candidate = model.clone();
        let mut moved = false;
        if next() % 4 != 0 {
            let mut r = Repair {
                model: candidate,
                fixed: Vec::new(),
                partial: false,
                steps: 32,
            };
            moved = r.make(cx, es[k], true)?;
            candidate = r.model;
        }
        if !moved {
            // A symbol of the predicate: one bit of it, or all of it.
            let ids = cx.symbols_in(&[es[k]])?;
            if ids.is_empty() {
                return Ok(None);
            }
            let id = ids[(next() % ids.len() as u64) as usize];
            let Some(key) = cx.symbol_key(id).cloned() else {
                continue;
            };
            if let Some(slot) = candidate.iter_mut().find(|(f, _)| *f == key) {
                let w = slot.1.width();
                let change = if next() % 2 == 0 {
                    let one = BitVec::wrapping_from_u64(w, 1);
                    let by = BitVec::wrapping_from_u64(w, next() % u64::from(w.bits()));
                    BitVec::apply_bin(BinOp::Shl, &one, &by).unwrap_or(one)
                } else {
                    BitVec::wrapping_from_limbs(w, &[next(), next(), next(), next()])
                };
                slot.1 = BitVec::apply_bin(BinOp::Xor, &slot.1, &change).unwrap_or(slot.1);
            }
        }
        let after = falses(cx, &candidate)?;
        if after.len() <= wrong.len() || next() % 8 == 0 {
            model = candidate;
            wrong = after;
        }
    }
    Ok(wrong.is_empty().then_some(model))
}

struct Repair {
    model: Model,
    /// The symbols given a value, once for each time.
    fixed: Vec<crate::SymbolKey>,
    /// Whether the value being given keeps some bits of the operand as they are.
    partial: bool,
    steps: u32,
}

impl Repair {
    fn value(&self, cx: &mut Context, e: Expr) -> Result<BitVec, Error> {
        Ok(eval_in(cx, &[e], &self.model)?.remove(0))
    }

    /// Makes the 1-bit `e` true (or false).
    fn make(&mut self, cx: &mut Context, e: Expr, want: bool) -> Result<bool, Error> {
        use crate::View;
        use crate::ops::{CmpOp, UnOp};
        if self.steps == 0 {
            return Ok(false);
        }
        self.steps -= 1;
        let one = |w: Width| BitVec::wrapping_from_u64(w, 1);
        let bin = |op: BinOp, a: &BitVec, b: &BitVec| BitVec::apply_bin(op, a, b).ok();
        match cx.view(e)? {
            View::Un(UnOp::Not, a) if cx.width(a)? == Width::W1 => self.make(cx, a, !want),
            View::Bin(BinOp::And, a, b) if want => {
                Ok(self.make(cx, a, true)? && self.make(cx, b, true)?)
            }
            View::Bin(BinOp::Or, a, b) if !want => {
                Ok(self.make(cx, a, false)? && self.make(cx, b, false)?)
            }
            View::Bin(BinOp::Or, a, b) if want => {
                if !self.value(cx, a)?.is_zero() || !self.value(cx, b)?.is_zero() {
                    return Ok(true);
                }
                Ok(self.make(cx, a, true)? || self.make(cx, b, true)?)
            }
            View::Cmp(op, l, r) => {
                let w = cx.width(l)?;
                // The value `l` is to have beside `r`'s (or `r` beside `l`'s): `None` when
                // there is none on that side of the bound.
                let (equal, signed, swap) = match (op, want) {
                    (CmpOp::Eq, true) | (CmpOp::Ne, false) => (true, false, false),
                    (CmpOp::Eq, false) | (CmpOp::Ne, true) => (false, false, false),
                    (CmpOp::Ult, true) => (false, false, false),
                    (CmpOp::Ule, true) => (true, false, false),
                    (CmpOp::Slt, true) => (false, true, false),
                    (CmpOp::Sle, true) => (true, true, false),
                    // `!(l < r)` is `r <= l`, and `!(l <= r)` is `r < l`.
                    (CmpOp::Ult, false) => (true, false, true),
                    (CmpOp::Ule, false) => (false, false, true),
                    (CmpOp::Slt, false) => (true, true, true),
                    (CmpOp::Sle, false) => (false, true, true),
                };
                let (l, r) = if swap { (r, l) } else { (l, r) };
                // Now: `l == r` (equal) will do, or `l` is to differ from or be below `r`, in the
                // order `signed`.
                let (lowest, highest) = if signed {
                    (BitVec::smin(w), BitVec::smax(w))
                } else {
                    (BitVec::zero(w), BitVec::ones(w))
                };
                let rv = self.value(cx, r)?;
                let below = if equal {
                    Some(rv)
                } else if matches!(op, CmpOp::Eq | CmpOp::Ne) {
                    bin(BinOp::Add, &rv, &one(w))
                } else if rv != lowest {
                    bin(BinOp::Sub, &rv, &one(w))
                } else {
                    None
                };
                if let Some(t) = below
                    && self.set(cx, l, t)?
                {
                    return Ok(true);
                }
                let lv = self.value(cx, l)?;
                let above = if equal {
                    Some(lv)
                } else if matches!(op, CmpOp::Eq | CmpOp::Ne) || lv != highest {
                    bin(BinOp::Add, &lv, &one(w))
                } else {
                    None
                };
                match above {
                    Some(t) => self.set(cx, r, t),
                    None => Ok(false),
                }
            }
            _ => self.set(cx, e, BitVec::from_bool(want)),
        }
    }

    /// [`set`](Self::set) where `target` keeps some bits of `e` as they are.
    fn set_part(&mut self, cx: &mut Context, e: Expr, target: BitVec) -> Result<bool, Error> {
        let outer = core::mem::replace(&mut self.partial, true);
        let r = self.set(cx, e, target);
        self.partial = outer;
        r
    }

    /// Gives `e` the value `target` by giving one symbol under it a value.
    fn set(&mut self, cx: &mut Context, e: Expr, target: BitVec) -> Result<bool, Error> {
        use crate::View;
        use crate::ops::UnOp;
        if self.steps == 0 {
            return Ok(false);
        }
        self.steps -= 1;
        let w = target.width();
        let bin = |op: BinOp, a: &BitVec, b: &BitVec| BitVec::apply_bin(op, a, b).ok();
        // (Of one width: the operands of one operator.)
        let and = |a: &BitVec, b: &BitVec| BitVec::apply_bin(BinOp::And, a, b).unwrap_or(*a);
        let or = |a: &BitVec, b: &BitVec| BitVec::apply_bin(BinOp::Or, a, b).unwrap_or(*a);
        let not = |a: &BitVec| BitVec::apply_un(UnOp::Not, a).unwrap_or(*a);
        match cx.view(e)? {
            View::Const(v) => Ok(v == target),
            View::Sym(id) => {
                let Some(key) = cx.symbol_key(id).cloned() else {
                    return Ok(false);
                };
                let Some(slot) = self.model.iter_mut().find(|(k, _)| *k == key) else {
                    return Ok(false);
                };
                // A second value is one that keeps what the first was given for (a mask, an
                // extract and a shift change the bits they read and leave the others); a
                // third is not tried.
                let given = self.fixed.iter().filter(|k| **k == key).count();
                if given >= 2 || (given == 1 && !self.partial) {
                    return Ok(slot.1 == target);
                }
                slot.1 = target;
                self.fixed.push(key);
                Ok(true)
            }
            View::Un(op @ (UnOp::Not | UnOp::Neg), a) => match BitVec::apply_un(op, &target) {
                Ok(t) => self.set(cx, a, t),
                Err(_) => Ok(false),
            },
            View::Bin(op @ (BinOp::Add | BinOp::Sub | BinOp::Xor), a, b) => {
                // Through either operand, the other as it is now.
                let bv = self.value(cx, b)?;
                let through_a = match op {
                    BinOp::Add => bin(BinOp::Sub, &target, &bv),
                    BinOp::Sub => bin(BinOp::Add, &target, &bv),
                    _ => bin(BinOp::Xor, &target, &bv),
                };
                if let Some(t) = through_a
                    && cx.as_const(a)?.is_none()
                    && self.set(cx, a, t)?
                {
                    return Ok(true);
                }
                let av = self.value(cx, a)?;
                let through_b = match op {
                    BinOp::Add => bin(BinOp::Sub, &target, &av),
                    BinOp::Sub => bin(BinOp::Sub, &av, &target),
                    _ => bin(BinOp::Xor, &target, &av),
                };
                match through_b {
                    Some(t) => self.set(cx, b, t),
                    None => Ok(false),
                }
            }
            View::Bin(BinOp::Mul, a, b) => {
                let (c, x) = match (cx.as_const(a)?, cx.as_const(b)?) {
                    (Some(c), None) => (c, b),
                    (None, Some(c)) => (c, a),
                    _ => return Ok(false),
                };
                if c.bit(0) != Some(true) {
                    return Ok(false);
                }
                // The inverse of an odd number: each round doubles the bits that are right.
                let two = BitVec::wrapping_from_u64(w, 2);
                let mut inv = c;
                for _ in 0..10 {
                    let Some(next) = bin(BinOp::Mul, &c, &inv)
                        .and_then(|ci| bin(BinOp::Sub, &two, &ci))
                        .and_then(|f| bin(BinOp::Mul, &inv, &f))
                    else {
                        return Ok(false);
                    };
                    inv = next;
                }
                match bin(BinOp::Mul, &target, &inv) {
                    Some(t) => self.set(cx, x, t),
                    None => Ok(false),
                }
            }
            View::Bin(op @ (BinOp::And | BinOp::Or), a, b) => {
                // A mask: the bits it lets through as asked, the others as they are.
                let (m, x) = match (cx.as_const(a)?, cx.as_const(b)?) {
                    (Some(m), None) => (m, b),
                    (None, Some(m)) => (m, a),
                    _ => return Ok(false),
                };
                let through = if op == BinOp::And { m } else { not(&m) };
                let fits = if op == BinOp::And {
                    and(&target, &not(&m)).is_zero()
                } else {
                    and(&target, &m) == m
                };
                if !fits {
                    return Ok(false);
                }
                let xv = self.value(cx, x)?;
                let t = or(&and(&target, &through), &and(&xv, &not(&through)));
                self.set_part(cx, x, t)
            }
            View::Bin(op @ (BinOp::Shl | BinOp::LShr), a, k) => {
                let Some(k) = cx.as_const(k)? else {
                    return Ok(false);
                };
                // The bits shifted in are zero in the target, or there is no such operand;
                // the bits shifted out stay as they are.
                let back = if op == BinOp::Shl {
                    BinOp::LShr
                } else {
                    BinOp::Shl
                };
                let Some(t) = bin(back, &target, &k) else {
                    return Ok(false);
                };
                if bin(op, &t, &k) != Some(target) {
                    return Ok(false);
                }
                let av = self.value(cx, a)?;
                let Some(kept) = bin(op, &BitVec::ones(w), &k).and_then(|m| bin(back, &m, &k))
                else {
                    return Ok(false);
                };
                self.set_part(cx, a, or(&and(&t, &kept), &and(&av, &not(&kept))))
            }
            View::Zext(a) | View::Sext(a) => {
                let narrow = cx.width(a)?;
                let Ok(t) = target.trunc(narrow) else {
                    return Ok(false);
                };
                let back = if matches!(cx.view(e)?, View::Zext(_)) {
                    t.zext(w)
                } else {
                    t.sext(w)
                };
                if back.ok() != Some(target) {
                    return Ok(false);
                }
                self.set(cx, a, t)
            }
            View::Extract { lo, src } => {
                // The source as it is, with these bits as asked.
                let sv = self.value(cx, src)?;
                let sw = sv.width();
                let (Ok(wide), Ok(ones)) = (target.zext(sw), BitVec::ones(w).zext(sw)) else {
                    return Ok(false);
                };
                let by = BitVec::wrapping_from_u64(sw, u64::from(lo));
                let (Some(field), Some(place)) =
                    (bin(BinOp::Shl, &wide, &by), bin(BinOp::Shl, &ones, &by))
                else {
                    return Ok(false);
                };
                self.set_part(cx, src, or(&and(&sv, &not(&place)), &field))
            }
            View::Concat { hi, lo } => {
                let (hw, lw) = (cx.width(hi)?, cx.width(lo)?);
                let (Ok(h), Ok(l)) = (target.extract(lw.bits(), hw), target.extract(0, lw)) else {
                    return Ok(false);
                };
                Ok(self.set(cx, hi, h)? && self.set(cx, lo, l)?)
            }
            View::Select { cond, then, els } => {
                let c = self.value(cx, cond)?;
                self.set(cx, if c.is_zero() { els } else { then }, target)
            }
            _ if w == Width::W1 && !matches!(cx.view(e)?, View::Bin(..) | View::Un(..)) => {
                self.make(cx, e, !target.is_zero())
            }
            _ => Ok(false),
        }
    }
}

/// Whether every 1-bit expression is true at `model`.
fn holds(cx: &mut Context, ps: &[Expr], model: &Model) -> Result<bool, Error> {
    Ok(eval_in(cx, ps, model)?.iter().all(|v| !v.is_zero()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParseOptions;

    fn p(cx: &mut Context, s: &str) -> Expr {
        cx.parse(s, &ParseOptions::width(Width::W16)).unwrap()
    }

    /// A symbol used once frees the term it is in, and the terms that one is in; the model
    /// gives it the value that makes the terms what the model of the rest says.
    #[test]
    fn unconstrained_symbols_are_taken_out() {
        let o = ParseOptions::width(Width::W64);
        let mut cx = Context::new();
        let srcs = [
            "(x + a * b ^ 0x55) * 3 == c - (a & b)",
            "a >u 3",
            "~y - b != a",
            "c <u 100",
        ];
        let es: Vec<Expr> = srcs.iter().map(|t| cx.parse(t, &o).unwrap()).collect();
        let (left, trail) = eliminate_unconstrained(&mut cx, &es, &mut []).unwrap();
        // The first and the third are a free Boolean each; the others are as they were.
        assert!(cx.symbol_id(left[0]).unwrap().is_some());
        assert!(cx.symbol_id(left[2]).unwrap().is_some());
        assert_eq!((left[1], left[3]), (es[1], es[3]));
        let keys: Vec<String> = trail.iter().map(|(k, _)| k.to_string()).collect();
        assert!(keys.contains(&"x".to_string()) && keys.contains(&"y".to_string()));
        // Through the solver: the prover is asked the little that is left, and the model is
        // of what was asserted.
        let cfg = Config::default()
            .with_probes(0)
            .with_incremental(false)
            .with_unconstrained(true)
            .with_quick(None);
        let mut s = Solver::new(cfg);
        for &e in &es {
            s.assert(&cx, e).unwrap();
        }
        assert_eq!(s.check(&mut cx).unwrap(), Status::Sat);
        for &e in &es {
            assert!(!s.value(&mut cx, e).unwrap().unwrap().is_zero());
        }
        // A symbol with declared bits is not free.
        let z = cx.parse("z", &o).unwrap();
        let known = crate::KnownBits::new(
            BitVec::wrapping_from_u64(Width::W64, 0xff),
            BitVec::zero(Width::W64),
        );
        cx.declare_known(z, known.unwrap()).unwrap();
        let e = cx.parse("z + a == 7", &o).unwrap();
        let (left, trail) = eliminate_unconstrained(&mut cx, &[e, es[1]], &mut []).unwrap();
        assert!(left[0] == e && trail.is_empty());
    }

    /// Products as unknowns: unsatisfiable without them is unsatisfiable, and a model is one
    /// of what was asked, by definitions added where a model got a product wrong.
    #[test]
    fn products_are_abstracted_and_refined() {
        let o = ParseOptions::width(Width::W64);
        let mut cx = Context::new();
        // Whatever `a * b` is, it is not above and below `c` at once. (No circuit is kept,
        // and the search has 50 conflicts: only the abstraction can answer.)
        let cfg = Config::default()
            .with_probes(0)
            .with_incremental(false)
            .with_quick(Some(Config::quick_default().with_max_conflicts(50)))
            .with_abstraction(true);
        let mut s = Solver::new(cfg);
        for t in [
            "a * b * a >u c + (b * a)",
            "c + (a * b) >=u (a * b) * a",
            "a >u 0x10000",
        ] {
            let e = cx.parse(t, &o).unwrap();
            s.assert(&cx, e).unwrap();
        }
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
        assert_eq!(s.decided_by(), Some(DecidedBy::Abstraction));
        // A model needs the product to be the product: found after refinement, and checked.
        let direct = |cx: &mut Context, ts: &[&str]| {
            let es: Vec<Expr> = ts.iter().map(|t| cx.parse(t, &o).unwrap()).collect();
            let a = abstracted(cx, &es, Limits::conflicts(100_000)).unwrap();
            (es, a)
        };
        let (es, a) = direct(
            &mut cx,
            &["x * y == 35", "x >u 1", "y >u 1", "x <u 16", "y <u 16"],
        );
        let Some(prove::IncrementalAnswer::Sat(m)) = a else {
            panic!("{a:?}")
        };
        assert!(holds(&mut cx, &es, &m).unwrap());
        // Unsatisfiable only by what a product is: every definition is asked for, or the
        // rounds end; never a wrong answer.
        let (_, a) = direct(&mut cx, &["x * y == 35", "x == 2"]);
        assert!(
            !matches!(a, Some(prove::IncrementalAnswer::Sat(_))),
            "{a:?}"
        );
        // Nothing to take out.
        assert!(direct(&mut cx, &["x + 3 == y"]).1.is_none());
    }

    /// The local search returns only models, and finds some the repair alone does not.
    #[test]
    fn a_local_search_returns_models() {
        let o = ParseOptions::width(Width::W16);
        let mut cx = Context::new();
        let mut found = 0;
        for srcs in [
            vec!["(x & 0xf0) == 0x30", "(x ^ y) <u 4", "y >u 0x1000"],
            vec!["x * y == 77", "x >u 1", "y >u 1"],
            vec!["(x | y) == 0xffff", "(x & y) == 0", "x <u y"],
            vec!["x + y == 7", "x == 3", "y == 9"],
        ] {
            let es: Vec<Expr> = srcs.iter().map(|t| cx.parse(t, &o).unwrap()).collect();
            if let Some(m) = local_search(&mut cx, &es, &Vec::new(), 2_000).unwrap() {
                assert!(holds(&mut cx, &es, &m).unwrap(), "{srcs:?}");
                found += 1;
            }
        }
        // The last has no model; of the others at least one is reached.
        assert!((1..=3).contains(&found), "{found}");
    }

    /// The store keeps, per shape, the most conflicts the kept circuit took, and reads a
    /// store written before it did.
    #[test]
    fn the_store_keeps_conflicts_per_shape() {
        let o = ParseOptions::width(Width::W16);
        let mut cx = Context::new();
        let cfg = Config::default().with_probes(0).with_learn_budgets(true);
        let mut s = Solver::new(cfg).with_answers(Answers::new());
        for k in 0..6u32 {
            s.push();
            for t in [format!("x * x == {}", 4 * k + 1), "x >u 2".to_string()] {
                let e = cx.parse(&t, &o).unwrap();
                s.assert(&cx, e).unwrap();
            }
            assert!(!matches!(s.check(&mut cx).unwrap(), Status::Unknown(_)));
            s.pop(1).unwrap();
        }
        let text = s.answers().unwrap().to_text();
        let lines: Vec<&str> = text.lines().filter(|l| l.starts_with("t ")).collect();
        assert!(
            !lines.is_empty() && lines.iter().all(|l| l.split(' ').count() == 5),
            "{text}"
        );
        assert_eq!(&Answers::from_text(&text).unwrap(), s.answers().unwrap());
        // Without the count: zero.
        let old: String = text
            .lines()
            .map(|l| match l.strip_prefix("t ") {
                Some(rest) => format!("t {}\n", rest.rsplit_once(' ').unwrap().0),
                None => format!("{l}\n"),
            })
            .collect();
        assert!(Answers::from_text(&old).is_ok());
    }

    /// Every decided answer says what it rests on.
    #[test]
    fn an_answer_names_its_tier() {
        let o = ParseOptions::width(Width::W64);
        let mut cx = Context::new();
        let tier = |cx: &mut Context, cfg: Config, srcs: &[&str]| {
            let mut s = Solver::new(cfg);
            for t in srcs {
                let e = cx.parse(t, &o).unwrap();
                s.assert(cx, e).unwrap();
            }
            (s.check(cx).unwrap(), s.tier())
        };
        let d = Config::default;
        assert_eq!(
            tier(&mut cx, d(), &["x + 1 == y"]),
            (Status::Sat, Some(Tier::Model))
        );
        assert_eq!(
            tier(&mut cx, d(), &["x != x"]),
            (Status::Unsat, Some(Tier::Folding))
        );
        assert_eq!(
            tier(&mut cx, d(), &["x <u 4", "x >u 9"]),
            (Status::Unsat, Some(Tier::Search))
        );
        // A linear MBA identity denied: past the quick search, the simplifier's.
        let mba = "(x ^ y) + 2 * (x & y) + (x | z) - (x & z) - (x ^ z) != x + y";
        assert_eq!(
            tier(&mut cx, d().with_quick(None), &[mba]),
            (Status::Unsat, Some(Tier::Simplifier))
        );
        // Nothing decided: no tier.
        let none = d().with_quick(None).with_prove(
            Config::quick_default()
                .with_max_conflicts(0)
                .with_samples(0),
        );
        let (status, t) = tier(&mut cx, none, &["x * x * x == 0x1234567"]);
        assert!(
            matches!(status, Status::Unknown(_)) && t.is_none(),
            "{status:?}"
        );
    }

    /// A chain of definitions is answered at the level of words: no circuit.
    #[test]
    fn definitions_are_solved_by_repair() {
        let o = ParseOptions::width(Width::W64);
        for (src, by) in [
            // An equation solved for one symbol through sums and exclusive ors.
            (
                vec!["(x ^ y) + ((x & y) << 1) + 77 == 0x1234"],
                DecidedBy::Probe,
            ),
            // The symbol with one use first, then what depends on it.
            (vec!["x + y == 12345", "x == 99"], DecidedBy::Probe),
            (
                vec!["a * 7 - b == 3", "b == c ^ 0xff", "c == 5", "d >u a"],
                DecidedBy::Probe,
            ),
            (
                vec!["zext<64>(trunc<16>(x) + 1:16) == 0x8000", "(x >>u 16) == 3"],
                DecidedBy::Probe,
            ),
            (
                vec!["~x <u 16", "x != -1", "select(x <u 5, y, z) == 7"],
                DecidedBy::Probe,
            ),
        ] {
            let mut cx = Context::new();
            let mut s = Solver::default();
            let es: Vec<Expr> = src.iter().map(|t| cx.parse(t, &o).unwrap()).collect();
            for &e in &es {
                s.assert(&cx, e).unwrap();
            }
            assert_eq!(s.check(&mut cx).unwrap(), Status::Sat, "{src:?}");
            assert_eq!(s.decided_by(), Some(by), "{src:?}");
            for &e in &es {
                assert!(!s.value(&mut cx, e).unwrap().unwrap().is_zero(), "{src:?}");
            }
        }
        // What cannot be repaired is still answered, and what has no model is not given one.
        let mut cx = Context::new();
        let mut s = Solver::default();
        for t in ["x * x == 49", "x >u 5", "x <u 0x1000"] {
            let e = cx.parse(t, &o).unwrap();
            s.assert(&cx, e).unwrap();
        }
        assert_eq!(s.check(&mut cx).unwrap(), Status::Sat);
        let mut s = Solver::default();
        for t in ["x + y == 5", "x == 2", "y == 4"] {
            let e = cx.parse(t, &o).unwrap();
            s.assert(&cx, e).unwrap();
        }
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
    }

    #[test]
    fn the_stack_scopes_assertions() {
        let mut cx = Context::new();
        let mut s = Solver::default();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Sat);
        assert_eq!(s.decided_by(), Some(DecidedBy::Constants));
        let a = p(&mut cx, "x * 3 == 9");
        s.assert(&cx, a).unwrap();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Sat);
        let x = p(&mut cx, "x");
        // 3 is odd: one solution.
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_u64(), Some(3));
        s.push();
        let b = p(&mut cx, "x >u 3");
        s.assert(&cx, b).unwrap();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
        assert!(s.model().is_none());
        assert!(s.pop(2).is_err());
        s.pop(1).unwrap();
        assert_eq!(s.depth(), 0);
        // The model from before the scope still holds.
        assert_eq!(s.check(&mut cx).unwrap(), Status::Sat);
        assert_eq!(s.decided_by(), Some(DecidedBy::LastModel));
        // A wide assertion is refused.
        assert!(s.assert(&cx, x).is_err());
    }

    #[test]
    fn a_model_satisfies_every_assertion() {
        let mut cx = Context::new();
        let mut s = Solver::default();
        for src in [
            "(x ^ y) + 2 * (x & y) == 0x1234",
            "x >u 0x100",
            "y & 0xff == 0x34",
            "x != y",
        ] {
            let e = p(&mut cx, src);
            s.assert(&cx, e).unwrap();
            assert_eq!(s.check(&mut cx).unwrap(), Status::Sat, "{src}");
            for &a in s.assertions().to_vec().iter() {
                assert_eq!(s.value(&mut cx, a).unwrap().unwrap().to_u64(), Some(1));
            }
        }
    }

    #[test]
    fn assumptions_are_of_one_check_and_cores_name_what_conflicts() {
        let mut cx = Context::new();
        let mut s = Solver::default();
        let a0 = p(&mut cx, "x <u 10");
        let a1 = p(&mut cx, "y == x + 1");
        let a2 = p(&mut cx, "z == 7");
        for a in [a0, a1, a2] {
            s.assert(&cx, a).unwrap();
        }
        let (q0, q1) = (p(&mut cx, "y >u 20"), p(&mut cx, "z != 0"));
        assert_eq!(s.check_assuming(&mut cx, &[q1, q0]).unwrap(), Status::Unsat);
        // x < 10, y = x + 1 and y > 20 conflict; z has no part in it.
        assert_eq!(
            s.unsat_core(&mut cx).unwrap().unwrap(),
            vec![
                CoreItem::Assertion(0),
                CoreItem::Assertion(1),
                CoreItem::Assumption(1)
            ]
        );
        assert_eq!(s.check(&mut cx).unwrap(), Status::Sat);
        assert!(s.unsat_core(&mut cx).unwrap().is_none());
        // Without minimization: the whole slice; without slicing either, everything that
        // is not a constant.
        let mut whole = Solver::new(Config::default().with_minimize_cores(false));
        for a in [a0, a1, a2] {
            whole.assert(&cx, a).unwrap();
        }
        assert_eq!(whole.check_assuming(&mut cx, &[q0]).unwrap(), Status::Unsat);
        assert_eq!(whole.unsat_core(&mut cx).unwrap().unwrap().len(), 3);
        let unsliced = Config::default()
            .with_minimize_cores(false)
            .with_incremental(false)
            .with_solve_equations(false)
            .with_slice(false);
        let mut all = Solver::new(unsliced);
        for a in [a0, a1, a2] {
            all.assert(&cx, a).unwrap();
        }
        assert_eq!(all.check_assuming(&mut cx, &[q0]).unwrap(), Status::Unsat);
        assert_eq!(all.unsat_core(&mut cx).unwrap().unwrap().len(), 4);
        // A false assertion is its own core.
        let f = cx.bool(false).unwrap();
        s.assert(&cx, f).unwrap();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
        assert_eq!(s.decided_by(), Some(DecidedBy::Constants));
        assert_eq!(
            s.unsat_core(&mut cx).unwrap().unwrap(),
            vec![CoreItem::Assertion(3)]
        );
    }

    #[test]
    fn independent_assertions_are_answered_apart_and_remembered() {
        let mut cx = Context::new();
        let mut s = Solver::default();
        let (a, b) = (p(&mut cx, "x * 5 == 35"), p(&mut cx, "y + z == 9"));
        let (c, d) = (p(&mut cx, "y >u 20"), p(&mut cx, "z >u 20"));
        s.assert(&cx, a).unwrap();
        s.assert(&cx, b).unwrap();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Sat);
        let model = s.model().unwrap().clone();
        assert_eq!(model.len(), 3, "{model:?}");
        s.push();
        s.assert(&cx, c).unwrap();
        s.assert(&cx, d).unwrap();
        // y + z = 9 with both above 20 wraps; possible at 16 bits.
        assert_eq!(s.check(&mut cx).unwrap(), Status::Sat);
        let e = p(&mut cx, "y + z <u y");
        let not_wrapping = cx.un(UnOp::Not, e).unwrap();
        s.assert(&cx, not_wrapping).unwrap();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
        // The core is within the slice of y and z: x has no part in it.
        let core = s.unsat_core(&mut cx).unwrap().unwrap();
        assert!(!core.contains(&CoreItem::Assertion(0)), "{core:?}");
        assert!(core.contains(&CoreItem::Assertion(1)), "{core:?}");
        // Asked again, and as part of a larger slice: remembered.
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
        assert_eq!(s.decided_by(), Some(DecidedBy::Cache));
        let more = p(&mut cx, "y != 77");
        s.assert(&cx, more).unwrap();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
        assert_eq!(s.decided_by(), Some(DecidedBy::Cache));
        s.pop(1).unwrap();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Sat);
        // Every assertion holds in the model, whichever slice gave its part.
        for a in s.assertions().to_vec() {
            assert_eq!(s.value(&mut cx, a).unwrap().unwrap().to_u64(), Some(1));
        }
        // Without slicing or memory the answers are the same.
        let plain = Config::default().with_slice(false).with_cache_entries(0);
        let mut t = Solver::new(plain);
        for a in [a, b, c, d, not_wrapping] {
            t.assert(&cx, a).unwrap();
        }
        assert_eq!(t.check(&mut cx).unwrap(), Status::Unsat);
        assert_eq!(t.check(&mut cx).unwrap(), Status::Unsat);
        assert_ne!(t.decided_by(), Some(DecidedBy::Cache));
    }

    /// Every way a check has of answering, against the plainest one: random small sets of
    /// assertions, many of them definitions, answered alike; a model satisfies what was
    /// asserted (not what was left of it); and a core is unsatisfiable by itself.
    #[test]
    fn every_schedule_answers_as_the_plain_one() {
        use crate::testutil::Rng;
        let plain = Config::default()
            .with_solve_equations(false)
            .with_slice(false)
            .with_cache_entries(0)
            .with_incremental(false)
            .with_probes(0)
            .with_unconstrained(false)
            .with_quick(None);
        // Straight to the prover, through what takes symbols out on the way.
        let taken = plain
            .clone()
            .with_solve_equations(true)
            .with_unconstrained(true);
        let names = ["a", "b", "c", "d", "e"];
        let mut rng = Rng(0x5eed);
        let (mut sat, mut unsat, mut solved_cores) = (0, 0, 0);
        for round in 0..400 {
            let mut cx = Context::new();
            let mut pick = |n: usize| rng.below(n as u64) as usize;
            let term = |pick: &mut dyn FnMut(usize) -> usize| {
                let (x, y) = (names[pick(5)], names[pick(5)]);
                let k = pick(256);
                match pick(7) {
                    0 => x.to_string(),
                    1 => format!("{k}"),
                    2 => format!("({x} + {y})"),
                    3 => format!("({x} ^ {k})"),
                    4 => format!("({x} * {})", k | 1),
                    5 => format!("({x} & {y})"),
                    _ => format!("({x} - {k})"),
                }
            };
            let mut srcs = Vec::new();
            for _ in 0..3 + pick(5) {
                let (l, r) = (term(&mut pick), term(&mut pick));
                srcs.push(match pick(6) {
                    // A definition, either way round.
                    0 | 1 => format!("{} == {r}", names[pick(5)]),
                    2 => format!("{l} == {}", names[pick(5)]),
                    3 => format!("{l} <u {r}"),
                    4 => format!("{l} != {r}"),
                    _ => format!("{l} == {r}"),
                });
            }
            let o = ParseOptions::width(Width::W8);
            let es: Vec<Expr> = srcs.iter().map(|s| cx.parse(s, &o).unwrap()).collect();
            let mut full = Solver::default();
            let mut base = Solver::new(plain.clone());
            let mut out = Solver::new(taken.clone());
            for &e in &es {
                full.assert(&cx, e).unwrap();
                base.assert(&cx, e).unwrap();
                out.assert(&cx, e).unwrap();
                let through = out.check(&mut cx).unwrap();
                if through == Status::Sat {
                    for &a in out.assertions().to_vec().iter() {
                        let v = out.value(&mut cx, a).unwrap().unwrap();
                        assert!(!v.is_zero(), "round {round}: {srcs:?} (taken out)");
                    }
                }
                // After every assertion: the kept circuit, the cache and the last model
                // all have a history by the end.
                let got = full.check(&mut cx).unwrap();
                assert_eq!(got, base.check(&mut cx).unwrap(), "round {round}: {srcs:?}");
                assert_eq!(got, through, "round {round}: {srcs:?} (taken out)");
                match got {
                    Status::Sat => {
                        sat += 1;
                        for &a in full.assertions().to_vec().iter() {
                            let v = full.value(&mut cx, a).unwrap().unwrap();
                            assert!(!v.is_zero(), "round {round}: {srcs:?}");
                        }
                    }
                    Status::Unsat => {
                        unsat += 1;
                        let core = full.unsat_core(&mut cx).unwrap().unwrap();
                        let mut alone = Solver::new(plain.clone());
                        for item in &core {
                            let CoreItem::Assertion(i) = *item else {
                                panic!("no assumption was made")
                            };
                            alone.assert(&cx, full.assertions()[i]).unwrap();
                        }
                        assert_eq!(
                            alone.check(&mut cx).unwrap(),
                            Status::Unsat,
                            "round {round}: {core:?} of {srcs:?}"
                        );
                        solved_cores += usize::from(core.len() < full.assertions().len());
                    }
                    Status::Unknown(why) => panic!("round {round}: {why:?}"),
                }
            }
        }
        // Both answers, and cores that leave something out, were exercised.
        assert!(
            sat > 200 && unsat > 200 && solved_cores > 20,
            "{sat} {unsat} {solved_cores}"
        );
    }

    #[test]
    fn answers_travel_between_solvers_as_text() {
        let o = ParseOptions::width(Width::W16);
        let srcs = [
            "(x * 3 == 0x21) & (\"odd name\" >u x)",
            "(y ^ 0x5a5a) + 1 == 0",
            "(z * z == 3)",
        ];
        let mut first = Solver::default().with_answers(Answers::new());
        let mut cx = Context::new();
        let mut statuses = Vec::new();
        for src in srcs {
            let e = cx.parse(src, &o).unwrap();
            first.push();
            first.assert(&cx, e).unwrap();
            statuses.push(first.check(&mut cx).unwrap());
            assert_ne!(first.decided_by(), Some(DecidedBy::Remembered));
            first.pop(1).unwrap();
        }
        assert_eq!(statuses, [Status::Sat, Status::Sat, Status::Unsat]);
        let text = first.answers().unwrap().to_text();
        let back = Answers::from_text(&text).unwrap();
        assert_eq!(&back, first.answers().unwrap());
        assert_eq!((back.len(), back.to_text() == text), (3, true));
        // Another context (other symbols first, so nothing is where it was): every answer
        // is found, and a remembered model holds.
        let mut cx = Context::new();
        cx.parse("unrelated * 7", &o).unwrap();
        let mut second = Solver::default().with_answers(back);
        for (src, want) in srcs.iter().zip(&statuses) {
            let e = cx.parse(src, &o).unwrap();
            second.push();
            second.assert(&cx, e).unwrap();
            assert_eq!(&second.check(&mut cx).unwrap(), want, "{src}");
            assert_eq!(second.decided_by(), Some(DecidedBy::Remembered), "{src}");
            if *want == Status::Sat {
                assert_eq!(second.value(&mut cx, e).unwrap().unwrap().to_u64(), Some(1));
            }
            second.pop(1).unwrap();
        }
        // A model that does not hold of the slice it is filed under is not used.
        let forged = text.replace(" 0xb:16", " 0xc:16");
        assert_ne!(forged, text);
        let mut third = Solver::default().with_answers(Answers::from_text(&forged).unwrap());
        let e = cx.parse(srcs[0], &o).unwrap();
        third.assert(&cx, e).unwrap();
        assert_eq!(third.check(&mut cx).unwrap(), Status::Sat);
        assert_ne!(third.decided_by(), Some(DecidedBy::Remembered));
        // Merging keeps both sides; another version's text is no answers; other text is an
        // error.
        let mut merged = Answers::new();
        merged.merge(first.answers().unwrap());
        merged.merge(third.answers().unwrap());
        assert_eq!(merged.len(), 3);
        let old = text.replacen(env!("CARGO_PKG_VERSION"), "0.0.1", 1);
        assert!(Answers::from_text(&old).unwrap().is_empty());
        assert!(Answers::from_text("x").is_err());
    }

    #[test]
    fn a_deadline_stops_a_search() {
        use core::cell::Cell;
        /// A clock that advances one tick each time it is read.
        struct Ticks(Cell<u64>);
        impl crate::engine::Clock for Ticks {
            fn now_ticks(&self) -> u64 {
                self.0.set(self.0.get() + 1);
                self.0.get()
            }
        }
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        // Factoring a product of two primes: beyond any small budget.
        let hard = cx
            .parse(
                "(zext<128>(x) * zext<128>(y) == 0x7fffffffffffffc980000000000005c3:128) & (x >u 1) & (y >u 1)",
                &o,
            )
            .unwrap();
        let cfg = Config::default()
            .with_quick(None)
            .with_prove(prove::Config::default().with_simplify(false));
        let mut s = Solver::new(cfg);
        s.assert(&cx, hard).unwrap();
        let clock = Ticks(Cell::new(0));
        let status = s
            .check_within(&mut cx, &[], Some(Deadline::new(&clock, 6)))
            .unwrap();
        assert_eq!(status, Status::Unknown(Unknown::Deadline));
        // A few slices ran, not the whole search.
        assert!((6..12).contains(&clock.0.get()), "{}", clock.0.get());
        // An easy question is answered whatever the deadline, short of one already past.
        let mut s = Solver::default();
        let easy = cx.parse("x + 1 == 5", &o).unwrap();
        s.assert(&cx, easy).unwrap();
        let clock = Ticks(Cell::new(0));
        let d = Some(Deadline::new(&clock, 1_000));
        assert_eq!(s.check_within(&mut cx, &[], d).unwrap(), Status::Sat);
        // (A solver that remembers the answer gives it again at no cost, deadline or not.)
        let past = Some(Deadline::new(&clock, 0));
        let mut s = Solver::default();
        s.assert(&cx, easy).unwrap();
        assert_eq!(
            s.check_within(&mut cx, &[], past).unwrap(),
            Status::Unknown(Unknown::Deadline)
        );
    }

    #[test]
    fn what_the_quick_attempt_leaves_the_prover_decides() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        // A linear MBA identity: hopeless for the circuit under 1,000 conflicts.
        let e = cx
            .parse(
                "(x ^ y) + 2 * (x & y) + (x | z) - (x & z) - (x ^ z) != x + y",
                &o,
            )
            .unwrap();
        let mut s = Solver::default();
        s.assert(&cx, e).unwrap();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
        // No attempt at all: unknown, with the reason.
        let none = Config::default().with_quick(None).with_prove(
            Config::quick_default()
                .with_max_conflicts(1)
                .with_samples(0),
        );
        let mut s = Solver::new(none);
        let hard = cx.parse("(x * y == 0x123456789abcdef1) & (x >u 1) & (y >u 1)", &o);
        s.assert(&cx, hard.unwrap()).unwrap();
        assert!(matches!(s.check(&mut cx).unwrap(), Status::Unknown(_)));
        assert!(s.model().is_none() && s.decided_by().is_none());
    }
}
