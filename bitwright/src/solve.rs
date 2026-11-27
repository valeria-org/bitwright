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

use std::collections::{HashMap, HashSet};

use crate::engine::Deadline;
use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::prove::{self, Limits, Model, Outcome, Question, Unknown};
use crate::{BitVec, Facts, FnEnv, KnownBits, SRange, SymbolId, Truth, URange, Width};

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
    /// Whether causal 2-adic T-function equations are solved by Hensel root-lifting before
    /// bit-blasting.
    pub hensel: bool,
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
            hensel: true,
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
    with_hensel: hensel: bool,
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

/// Distinct values an expression can take under a [`Solver`]'s assertions
/// ([`Solver::enumerate_values`]).
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Values {
    /// Every value the expression can take under the assertions, in ascending unsigned order
    /// (empty when the assertions are [`Status::Unsat`]).
    Exact(Vec<BitVec>),
    /// At least these `limit` distinct values exist (in ascending unsigned order); at least one
    /// further value was still possible or undecided when the count limit was reached.
    AtLeast(Vec<BitVec>),
    /// Fewer than `limit` values had been found when a search stopped undecided.
    Unknown(Unknown),
}

/// Result of optimizing an expression under a [`Solver`]'s assertions.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Optimum {
    /// Exact optimal value achieved by at least one satisfying model (which [`Solver::value`]
    /// and [`Solver::model`] now hold).
    Found(BitVec),
    /// The assertions (and assumptions) are unsatisfiable.
    Unsat,
    /// Optimization stopped before proving optimality.
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
    /// 2-adic Hensel root-lifting on causal T-function equations.
    Hensel,
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
    /// The conflicts of the last quick attempt on it, when the backend counts them.
    kept_conflicts: Option<u64>,
    /// The context's `declaration_revision` when `model` and `cache` were recorded.
    declaration_revision: u64,
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
        if self.declaration_revision != cx.declaration_revision {
            self.declaration_revision = cx.declaration_revision;
            self.model = None;
            self.cache = Cache::default();
        }
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
                && let Some(s) =
                    seen.filter(|s| s.kept >= LEARNED_AFTER && s.later > 0 && s.conflicts > 0)
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
                answers.learn(name, &answer, DecidedBy::Probe, None);
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
        let has_conjuncts = es.len() > 1
            || (es.len() == 1 && matches!(cx.view(es[0])?, crate::View::Bin(BinOp::And, ..)));
        let (mut left, mut trail) = if self.cfg.solve_equations && has_conjuncts {
            solve_equations(cx, es)?
        } else {
            (es.to_vec(), Vec::new())
        };
        if self.cfg.unconstrained {
            let (rest, taken) = eliminate_unconstrained(cx, &left, &mut trail)?;
            left = rest;
            trail.extend(taken);
        }
        let abstract_ = match self.cfg.quick {
            Some(quick) if self.cfg.abstraction && kept.is_none() => {
                abstracted(cx, es, quick.limits())?
            }
            _ => None,
        };
        let can_search = self.cfg.quick.is_some() || self.cfg.prove.max_conflicts > 0;
        if self.cfg.hensel
            && can_search
            && kept.is_none()
            && abstract_.is_none()
            && !left.is_empty()
        {
            use crate::invert::hensel::{HenselLimits, HenselOutcome, solve as hensel_solve};
            match hensel_solve(cx, &left, &HenselLimits::default())? {
                HenselOutcome::Sat(mut found) => {
                    if !trail.is_empty() {
                        let ts: Vec<Expr> = trail.iter().map(|&(_, t)| t).collect();
                        let values = eval_in(cx, &ts, &found)?;
                        for ((k_sym, _), v) in trail.iter().zip(values) {
                            found.retain(|(k, _)| k != k_sym);
                            found.push((k_sym.clone(), v));
                        }
                    }
                    let m = complete(cx, es, &found)?;
                    if holds(cx, es, &m)? {
                        let answer = Some(m);
                        if caching {
                            if self.cache.exact.len() >= self.cfg.cache_entries {
                                self.cache = Cache::default();
                            }
                            self.cache.exact.insert(key, answer.clone());
                        }
                        if let (Some(answers), Some(name)) = (&mut self.answers, named) {
                            answers.learn(name, &answer, DecidedBy::Hensel, None);
                        }
                        return Ok((Ok(answer), DecidedBy::Hensel, None));
                    }
                }
                HenselOutcome::Unsat => {
                    if caching {
                        if self.cache.exact.len() >= self.cfg.cache_entries {
                            self.cache = Cache::default();
                        }
                        self.cache.unsat.push(key.clone());
                        self.cache.exact.insert(key, None);
                    }
                    if let (Some(answers), Some(name)) = (&mut self.answers, named) {
                        answers.learn(name, &None, DecidedBy::Hensel, None);
                    }
                    return Ok((Ok(None), DecidedBy::Hensel, None));
                }
                HenselOutcome::Unknown => {}
            }
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
                    // Complete over the slice's symbols: one the prover left open takes its
                    // declared known-one bits (zero when unconstrained).
                    let m = complete(cx, es, &found)?;
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
        self.kept_conflicts = circuit
            .exact_conflicts()
            .then(|| circuit.conflicts().saturating_sub(before));
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
            (
                _,
                DecidedBy::Incremental
                | DecidedBy::Quick
                | DecidedBy::Abstraction
                | DecidedBy::Hensel,
            ) => Tier::Search,
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

    /// Enumerates up to `limit` distinct values `expr` can take under the current assertions
    /// (for recovering indirect jump targets, dispatch tables, or state-machine transitions).
    ///
    /// Returns [`Values::Exact`] (sorted ascending) when all reachable values are exhausted within
    /// `limit`, [`Values::AtLeast`] when `limit` distinct values are confirmed and more may exist,
    /// or [`Values::Unknown`] if a check stops undecided before reaching `limit`. Leaves the
    /// assertion stack unchanged.
    pub fn enumerate_values(
        &mut self,
        cx: &mut Context,
        expr: Expr,
        limit: usize,
    ) -> Result<Values, Error> {
        self.enumerate_values_within(cx, expr, limit, &[], None)
    }

    /// [`enumerate_values`](Self::enumerate_values) under temporary 1-bit `assumptions` and an
    /// optional `deadline`.
    pub fn enumerate_values_within(
        &mut self,
        cx: &mut Context,
        expr: Expr,
        limit: usize,
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Values, Error> {
        let _w = cx.width(expr)?;
        for &a in assumptions {
            if cx.width(a)? != Width::W1 {
                return Err(Error::Unsupported("an assumption must be 1 bit".into()));
            }
        }
        if limit == 0 {
            return Ok(match self.check_within(cx, assumptions, deadline)? {
                Status::Unsat => Values::Exact(Vec::new()),
                Status::Sat => Values::AtLeast(Vec::new()),
                Status::Unknown(why) => Values::Unknown(why),
            });
        }
        if let Some(c) = cx.as_const(expr)? {
            return Ok(match self.check_within(cx, assumptions, deadline)? {
                Status::Unsat => Values::Exact(Vec::new()),
                Status::Sat => Values::Exact(vec![c]),
                Status::Unknown(why) => Values::Unknown(why),
            });
        }
        if self.cfg.hensel && deadline.is_none_or(|d| d.clock.now_ticks() < d.at) {
            let mut all_preds = Vec::with_capacity(self.assertions.len() + assumptions.len());
            all_preds.extend_from_slice(&self.assertions);
            all_preds.extend_from_slice(assumptions);
            if !all_preds.is_empty()
                && let Some(exact) = crate::invert::hensel::enumerate(
                    cx,
                    &all_preds,
                    expr,
                    limit,
                    &crate::invert::hensel::HenselLimits::default(),
                )?
            {
                return Ok(Values::Exact(exact));
            }
        }
        self.push();
        let res = (|| -> Result<Values, Error> {
            for &a in assumptions {
                self.assert(cx, a)?;
            }
            let mut found: Vec<BitVec> = Vec::new();
            loop {
                match self.check_within(cx, &[], deadline)? {
                    Status::Unsat => {
                        found.sort();
                        return Ok(Values::Exact(found));
                    }
                    Status::Unknown(why) => {
                        if found.len() >= limit {
                            found.sort();
                            return Ok(Values::AtLeast(found));
                        }
                        return Ok(Values::Unknown(why));
                    }
                    Status::Sat => {
                        if found.len() >= limit {
                            found.sort();
                            return Ok(Values::AtLeast(found));
                        }
                        let Some(v) = self.value(cx, expr)? else {
                            return Ok(Values::Unknown(Unknown::Unsupported(
                                "missing model value".into(),
                            )));
                        };
                        found.push(v);
                        let k = cx.constant(&v)?;
                        let ne = cx.cmp(crate::CmpOpExt::Ne, expr, k)?;
                        self.assert(cx, ne)?;
                    }
                }
            }
        })();
        let _ = self.pop(1);
        res
    }

    /// Finds the minimum unsigned value `expr` can take under the current assertions.
    ///
    /// When [`Optimum::Found`] is returned, [`Solver::model`] and [`Solver::value`] hold a
    /// satisfying assignment achieving that exact minimum.
    pub fn minimize(&mut self, cx: &mut Context, expr: Expr) -> Result<Optimum, Error> {
        self.minimize_within(cx, expr, &[], None)
    }

    /// [`minimize`](Self::minimize) under temporary 1-bit `assumptions` and an optional
    /// `deadline`.
    pub fn minimize_within(
        &mut self,
        cx: &mut Context,
        expr: Expr,
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Optimum, Error> {
        self.optimize_unsigned(cx, expr, false, assumptions, deadline, None)
    }

    /// Finds the maximum unsigned value `expr` can take under the current assertions.
    ///
    /// When [`Optimum::Found`] is returned, [`Solver::model`] and [`Solver::value`] hold a
    /// satisfying assignment achieving that exact maximum.
    pub fn maximize(&mut self, cx: &mut Context, expr: Expr) -> Result<Optimum, Error> {
        self.maximize_within(cx, expr, &[], None)
    }

    /// [`maximize`](Self::maximize) under temporary 1-bit `assumptions` and an optional
    /// `deadline`.
    pub fn maximize_within(
        &mut self,
        cx: &mut Context,
        expr: Expr,
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Optimum, Error> {
        self.optimize_unsigned(cx, expr, true, assumptions, deadline, None)
    }

    /// Finds the minimum two's-complement signed value `expr` can take under the current
    /// assertions.
    ///
    /// When [`Optimum::Found`] is returned, [`Solver::model`] and [`Solver::value`] hold a
    /// satisfying assignment achieving that exact signed minimum.
    pub fn minimize_signed(&mut self, cx: &mut Context, expr: Expr) -> Result<Optimum, Error> {
        self.minimize_signed_within(cx, expr, &[], None)
    }

    /// [`minimize_signed`](Self::minimize_signed) under temporary 1-bit `assumptions` and an
    /// optional `deadline`.
    pub fn minimize_signed_within(
        &mut self,
        cx: &mut Context,
        expr: Expr,
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Optimum, Error> {
        self.optimize_signed(cx, expr, false, assumptions, deadline, None)
    }

    /// Finds the maximum two's-complement signed value `expr` can take under the current
    /// assertions.
    ///
    /// When [`Optimum::Found`] is returned, [`Solver::model`] and [`Solver::value`] hold a
    /// satisfying assignment achieving that exact signed maximum.
    pub fn maximize_signed(&mut self, cx: &mut Context, expr: Expr) -> Result<Optimum, Error> {
        self.maximize_signed_within(cx, expr, &[], None)
    }

    /// [`maximize_signed`](Self::maximize_signed) under temporary 1-bit `assumptions` and an
    /// optional `deadline`.
    pub fn maximize_signed_within(
        &mut self,
        cx: &mut Context,
        expr: Expr,
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Optimum, Error> {
        self.optimize_signed(cx, expr, true, assumptions, deadline, None)
    }

    fn optimize_unsigned(
        &mut self,
        cx: &mut Context,
        expr: Expr,
        maximize: bool,
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
        mut on_witness: Option<&mut dyn FnMut(&BitVec)>,
    ) -> Result<Optimum, Error> {
        let w = cx.width(expr)?;
        for &a in assumptions {
            if cx.width(a)? != Width::W1 {
                return Err(Error::Unsupported("an assumption must be 1 bit".into()));
            }
        }
        if let Some(c) = cx.as_const(expr)? {
            return Ok(match self.check_within(cx, assumptions, deadline)? {
                Status::Sat => {
                    if let Some(cb) = on_witness.as_deref_mut() {
                        cb(&c);
                    }
                    Optimum::Found(c)
                }
                Status::Unsat => Optimum::Unsat,
                Status::Unknown(why) => Optimum::Unknown(why),
            });
        }
        match self.check_within(cx, assumptions, deadline)? {
            Status::Unsat => return Ok(Optimum::Unsat),
            Status::Unknown(why) => return Ok(Optimum::Unknown(why)),
            Status::Sat => {}
        }
        let Some(mut best_val) = self.value(cx, expr)? else {
            return Ok(Optimum::Unknown(Unknown::Unsupported(
                "missing model value".into(),
            )));
        };
        if let Some(cb) = on_witness.as_deref_mut() {
            cb(&best_val);
        }
        let mut best_model = self.model.clone();
        let mut best_last = self.last.clone();

        let facts = cx.facts(expr)?;
        let bound = if maximize {
            facts.urange().hi()
        } else {
            facts.urange().lo()
        };
        if best_val == bound {
            return Ok(Optimum::Found(best_val));
        }
        let kb = facts.known();

        let mut active: Vec<Expr> = Vec::with_capacity(assumptions.len() + usize::from(w.bits()));
        active.extend_from_slice(assumptions);

        for bit in (0..w.bits()).rev() {
            let bit_one = cx.extract(expr, bit, Width::W1)?;
            let bit_zero = cx.un(UnOp::Not, bit_one)?;
            let (prefer, fallback) = if maximize {
                (bit_one, bit_zero)
            } else {
                (bit_zero, bit_one)
            };
            if (best_val.bit(bit) == Some(true)) == maximize {
                active.push(prefer);
                continue;
            }
            let impossible = if maximize {
                kb.known_zero().bit(bit) == Some(true)
            } else {
                kb.known_one().bit(bit) == Some(true)
            };
            if impossible {
                active.push(fallback);
                continue;
            }
            active.push(prefer);
            match self.check_within(cx, &active, deadline)? {
                Status::Sat => {
                    let Some(v) = self.value(cx, expr)? else {
                        self.model = best_model;
                        return Ok(Optimum::Unknown(Unknown::Unsupported(
                            "missing model value".into(),
                        )));
                    };
                    if let Some(cb) = on_witness.as_deref_mut() {
                        cb(&v);
                    }
                    best_val = v;
                    best_model = self.model.clone();
                    if let (Some(bl), Some(nl)) = (&mut best_last, &self.last) {
                        bl.by = bl.by.max(nl.by);
                    }
                    if best_val == bound {
                        break;
                    }
                }
                Status::Unsat => {
                    if let Some(slot) = active.last_mut() {
                        *slot = fallback;
                    }
                }
                Status::Unknown(why) => {
                    self.model = best_model;
                    return Ok(Optimum::Unknown(why));
                }
            }
        }
        self.model = best_model;
        self.last = best_last;
        Ok(Optimum::Found(best_val))
    }

    fn optimize_signed(
        &mut self,
        cx: &mut Context,
        expr: Expr,
        maximize: bool,
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
        on_witness: Option<&mut dyn FnMut(&BitVec)>,
    ) -> Result<Optimum, Error> {
        let w = cx.width(expr)?;
        let smin = BitVec::smin(w);
        let smin_e = cx.constant(&smin)?;
        let shifted = cx.bin(BinOp::Xor, expr, smin_e)?;
        let opt = match on_witness {
            Some(cb) => {
                let mut unshift = |sv: &BitVec| {
                    cb(&crate::facts::known::bv_xor(sv, &smin));
                };
                self.optimize_unsigned(
                    cx,
                    shifted,
                    maximize,
                    assumptions,
                    deadline,
                    Some(&mut unshift),
                )?
            }
            None => self.optimize_unsigned(cx, shifted, maximize, assumptions, deadline, None)?,
        };
        Ok(match opt {
            Optimum::Found(sv) => Optimum::Found(crate::facts::known::bv_xor(&sv, &smin)),
            Optimum::Unsat => Optimum::Unsat,
            Optimum::Unknown(why) => Optimum::Unknown(why),
        })
    }

    /// Computes solver-tightened [`Facts`] for `expr` under the current assertions, or `None` when
    /// the assertions are unsatisfiable.
    pub fn tighten_facts(&mut self, cx: &mut Context, expr: Expr) -> Result<Option<Facts>, Error> {
        self.tighten_facts_within(cx, expr, &[], None)
    }

    /// [`tighten_facts`](Self::tighten_facts) under temporary 1-bit `assumptions` and an optional
    /// `deadline`.
    pub fn tighten_facts_within(
        &mut self,
        cx: &mut Context,
        expr: Expr,
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Option<Facts>, Error> {
        let w = cx.width(expr)?;
        for &a in assumptions {
            if cx.width(a)? != Width::W1 {
                return Err(Error::Unsupported("an assumption must be 1 bit".into()));
            }
        }
        let base = cx.facts(expr)?;
        if base.as_constant().is_some() || cx.as_const(expr)?.is_some() {
            return Ok(match self.check_within(cx, assumptions, deadline)? {
                Status::Unsat => None,
                Status::Sat | Status::Unknown(_) => Some(base),
            });
        }

        let mut seen_zero = BitVec::zero(w);
        let mut seen_one = BitVec::zero(w);
        let mut any_witness = false;
        let record_into = |v: &BitVec, sz: &mut BitVec, so: &mut BitVec, seen_any: &mut bool| {
            *seen_any = true;
            *so = crate::facts::known::bv_or(so, v);
            *sz = crate::facts::known::bv_or(sz, &crate::facts::known::bv_not(v));
        };

        let (umin, umin_exact) = {
            let mut rec =
                |v: &BitVec| record_into(v, &mut seen_zero, &mut seen_one, &mut any_witness);
            match self.optimize_unsigned(cx, expr, false, assumptions, deadline, Some(&mut rec))? {
                Optimum::Unsat => return Ok(None),
                Optimum::Unknown(_) if !any_witness => return Ok(Some(base)),
                Optimum::Unknown(_) => (base.urange().lo(), false),
                Optimum::Found(v) => (v, true),
            }
        };
        let saved_model = self.model.clone();
        let saved_last = self.last.clone();

        if umin_exact && umin == base.urange().hi() {
            return Ok(Some(Facts::constant(&umin)));
        }

        let (umax, umax_exact) = {
            let mut rec =
                |v: &BitVec| record_into(v, &mut seen_zero, &mut seen_one, &mut any_witness);
            match self.optimize_unsigned(cx, expr, true, assumptions, deadline, Some(&mut rec))? {
                Optimum::Unsat => return Ok(None),
                Optimum::Unknown(_) => (base.urange().hi(), false),
                Optimum::Found(v) => (v, true),
            }
        };
        if umin == umax {
            return Ok(Some(Facts::constant(&umin)));
        }

        let (smin, smax) = if umin_exact && umax_exact && umin.msb() == umax.msb() {
            (umin, umax)
        } else {
            let s_lo = {
                let mut rec =
                    |v: &BitVec| record_into(v, &mut seen_zero, &mut seen_one, &mut any_witness);
                match self.optimize_signed(
                    cx,
                    expr,
                    false,
                    assumptions,
                    deadline,
                    Some(&mut rec),
                )? {
                    Optimum::Unsat => return Ok(None),
                    Optimum::Unknown(_) => base.srange().lo(),
                    Optimum::Found(v) => v,
                }
            };
            let s_hi = {
                let mut rec =
                    |v: &BitVec| record_into(v, &mut seen_zero, &mut seen_one, &mut any_witness);
                match self.optimize_signed(cx, expr, true, assumptions, deadline, Some(&mut rec))? {
                    Optimum::Unsat => return Ok(None),
                    Optimum::Unknown(_) => base.srange().hi(),
                    Optimum::Found(v) => v,
                }
            };
            (s_lo, s_hi)
        };

        let ur = URange::new(umin, umax).unwrap_or_else(|| base.urange());
        let sr = SRange::new(smin, smax).unwrap_or_else(|| base.srange());
        let prelim = Facts::new(base.known(), ur, sr)
            .and_then(|f| f.meet(&base))
            .unwrap_or(base);

        let mut kz = prelim.known().known_zero();
        let mut ko = prelim.known().known_one();
        let mut probe_assumptions: Vec<Expr> = Vec::with_capacity(assumptions.len() + 1);
        probe_assumptions.extend_from_slice(assumptions);

        let mut probed = 0u32;
        for k in 0..w.bits() {
            if prelim.known().known().bit(k) == Some(true) {
                continue;
            }
            let s0 = seen_zero.bit(k) == Some(true);
            let s1 = seen_one.bit(k) == Some(true);
            if s0 && s1 {
                continue;
            }
            if probed >= 64 {
                break;
            }
            probed += 1;

            let bit_one = cx.extract(expr, k, Width::W1)?;
            let test_lit = if s0 {
                bit_one
            } else {
                cx.un(UnOp::Not, bit_one)?
            };
            probe_assumptions.truncate(assumptions.len());
            probe_assumptions.push(test_lit);

            match self.check_within(cx, &probe_assumptions, deadline)? {
                Status::Unsat => {
                    let mask = crate::facts::known::bv_shl(&BitVec::one(w), u32::from(k));
                    if s0 {
                        kz = crate::facts::known::bv_or(&kz, &mask);
                    } else {
                        ko = crate::facts::known::bv_or(&ko, &mask);
                    }
                }
                Status::Sat => {
                    if let Some(v) = self.value(cx, expr)? {
                        record_into(&v, &mut seen_zero, &mut seen_one, &mut any_witness);
                    }
                }
                Status::Unknown(Unknown::Deadline) => break,
                Status::Unknown(_) => {}
            }
        }

        if saved_model.is_some() {
            self.model = saved_model;
            self.last = saved_last;
        }

        let kb = KnownBits::new(kz, ko).unwrap_or_else(|| prelim.known());
        let tightened = Facts::new(kb, ur, sr)
            .and_then(|f| f.meet(&prelim))
            .unwrap_or(prelim);
        Ok(Some(tightened))
    }

    /// Checks whether `target` is uniquely determined by `inputs` under the current assertions:
    /// whether every pair of satisfying models that agree on all `inputs` also agree on `target`.
    pub fn is_determined_by(
        &mut self,
        cx: &mut Context,
        target: Expr,
        inputs: &[Expr],
    ) -> Result<Truth, Error> {
        self.is_determined_by_within(cx, target, inputs, &[], None)
    }

    /// [`is_determined_by`](Self::is_determined_by) under temporary 1-bit `assumptions` and an
    /// optional `deadline`.
    pub fn is_determined_by_within(
        &mut self,
        cx: &mut Context,
        target: Expr,
        inputs: &[Expr],
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Truth, Error> {
        let _tw = cx.width(target)?;
        for &inp in inputs {
            let _ = cx.width(inp)?;
        }
        for &a in assumptions {
            if cx.width(a)? != Width::W1 {
                return Err(Error::Unsupported("an assumption must be 1 bit".into()));
            }
        }
        if cx.as_const(target)?.is_some() || inputs.contains(&target) {
            return Ok(Truth::True);
        }
        let target_syms = cx.symbols_in(&[target])?;
        if target_syms.is_empty() {
            return Ok(Truth::True);
        }
        let mut direct_input_syms = HashSet::new();
        for &inp in inputs {
            if let Some(id) = cx.symbol_id(inp)? {
                direct_input_syms.insert(id);
            }
        }
        if target_syms.iter().all(|s| direct_input_syms.contains(s)) {
            return Ok(Truth::True);
        }

        let cp = cx.checkpoint();
        let res = (|| -> Result<Truth, Error> {
            let mut all_roots: Vec<Expr> =
                Vec::with_capacity(self.assertions.len() + assumptions.len() + inputs.len() + 1);
            all_roots.extend_from_slice(&self.assertions);
            all_roots.extend_from_slice(assumptions);
            all_roots.extend_from_slice(inputs);
            all_roots.push(target);

            let syms = cx.symbols_in(&all_roots)?;
            let mut subst_map: Vec<(Expr, Expr)> = Vec::with_capacity(syms.len());
            let mut kb_preds: Vec<Expr> = Vec::new();
            let mut seen = HashSet::with_capacity(syms.len());
            for sym in syms {
                if !seen.insert(sym) {
                    continue;
                }
                let (Some(key), Some(sw)) = (cx.symbol_key(sym).cloned(), cx.symbol_width(sym))
                else {
                    continue;
                };
                let Some(sym1) = cx.find_symbol(&key) else {
                    continue;
                };
                let sym2 = cx.fresh_symbol(sw)?;
                if let Some(kb) = cx.declared_known(sym1)? {
                    let mask = cx.constant(&kb.known())?;
                    let ones = cx.constant(&kb.known_one())?;
                    let m1 = cx.bin(BinOp::And, sym1, mask)?;
                    let m2 = cx.bin(BinOp::And, sym2, mask)?;
                    kb_preds.push(cx.cmp(crate::CmpOpExt::Eq, m1, ones)?);
                    kb_preds.push(cx.cmp(crate::CmpOpExt::Eq, m2, ones)?);
                }
                subst_map.push((sym1, sym2));
            }

            let copy2 = if subst_map.is_empty() {
                all_roots.clone()
            } else {
                cx.substitute(&all_roots, &subst_map)?
            };
            let n_assert = self.assertions.len();
            let n_assume = assumptions.len();
            let n_in = inputs.len();
            let assertions_2 = &copy2[..n_assert];
            let assumptions_2 = &copy2[n_assert..n_assert + n_assume];
            let inputs_2 = &copy2[n_assert + n_assume..n_assert + n_assume + n_in];
            let target_2 = copy2[n_assert + n_assume + n_in];

            let mut miter = Solver::new(self.cfg.clone());
            for &p in &self.assertions {
                miter.assert(cx, p)?;
            }
            for &p in assumptions {
                miter.assert(cx, p)?;
            }
            for &p in assertions_2 {
                miter.assert(cx, p)?;
            }
            for &p in assumptions_2 {
                miter.assert(cx, p)?;
            }
            for p in kb_preds {
                miter.assert(cx, p)?;
            }
            for (&i1, &i2) in inputs.iter().zip(inputs_2) {
                let eq = cx.cmp(crate::CmpOpExt::Eq, i1, i2)?;
                miter.assert(cx, eq)?;
            }
            let diff = cx.cmp(crate::CmpOpExt::Ne, target, target_2)?;
            miter.assert(cx, diff)?;

            Ok(match miter.check_within(cx, &[], deadline)? {
                Status::Unsat => Truth::True,
                Status::Sat => Truth::False,
                Status::Unknown(_) => Truth::Unknown,
            })
        })();
        let _ = cx.rollback(cp);
        res
    }

    /// Synthesizes a closed-form expression built solely from `inputs` and constants that equals
    /// `target` under every model of the current assertions.
    ///
    /// Returns `Ok(None)` when the assertions are unsatisfiable, when `target` is not uniquely
    /// determined by `inputs`, or when no closed-form expression is found within the solver's
    /// budgets. Every returned `Some(expr)` is solver-verified (`target != expr` is
    /// [`Status::Unsat`]).
    pub fn functional_def(
        &mut self,
        cx: &mut Context,
        target: Expr,
        inputs: &[Expr],
    ) -> Result<Option<Expr>, Error> {
        self.functional_def_within(cx, target, inputs, &[], None)
    }

    /// [`functional_def`](Self::functional_def) under temporary 1-bit `assumptions` and an
    /// optional `deadline`.
    pub fn functional_def_within(
        &mut self,
        cx: &mut Context,
        target: Expr,
        inputs: &[Expr],
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Option<Expr>, Error> {
        let tw = cx.width(target)?;
        for &inp in inputs {
            let _ = cx.width(inp)?;
        }
        for &a in assumptions {
            if cx.width(a)? != Width::W1 {
                return Err(Error::Unsupported("an assumption must be 1 bit".into()));
            }
        }

        // 1. Constant target fast-path and satisfiability + singleton-value check.
        if let Some(c) = cx.as_const(target)? {
            return Ok(match self.check_within(cx, assumptions, deadline)? {
                Status::Sat => Some(cx.constant(&c)?),
                Status::Unsat | Status::Unknown(_) => None,
            });
        }

        let mut samples: Vec<(Vec<BitVec>, BitVec)> = Vec::new();
        match self.check_within(cx, assumptions, deadline)? {
            Status::Unsat | Status::Unknown(_) => return Ok(None),
            Status::Sat => {
                if let Some(sample) = self.read_io_sample(cx, inputs, target)? {
                    samples.push(sample);
                }
            }
        }
        let saved_model = self.model.clone();
        let saved_last = self.last.clone();

        // Check whether `target` is constant under `self.assertions` + `assumptions`.
        if let Some((_, v0)) = samples.first().cloned() {
            let c0 = cx.constant(&v0)?;
            let ne0 = cx.cmp(crate::CmpOpExt::Ne, target, c0)?;
            let mut probe_a = assumptions.to_vec();
            probe_a.push(ne0);
            match self.check_within(cx, &probe_a, deadline)? {
                Status::Unsat => {
                    self.model = saved_model;
                    self.last = saved_last;
                    return Ok(Some(c0));
                }
                Status::Sat => {
                    if let Some(s1) = self.read_io_sample(cx, inputs, target)?
                        && !samples.iter().any(|(ins, _)| *ins == s1.0)
                    {
                        samples.push(s1);
                    }
                }
                Status::Unknown(_) => {
                    if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
                        self.model = saved_model;
                        self.last = saved_last;
                        return Ok(None);
                    }
                }
            }
        }

        // 2. Empty `inputs`: since `target` takes >= 2 values, it cannot be a function of `[]`.
        if inputs.is_empty() {
            self.model = saved_model;
            self.last = saved_last;
            return Ok(None);
        }

        // 3. Direct syntactic membership or symbol subset check.
        if inputs.contains(&target) {
            self.model = saved_model;
            self.last = saved_last;
            return Ok(Some(target));
        }
        let target_syms = cx.symbols_in(&[target])?;
        let mut direct_in_syms = HashSet::new();
        for &inp in inputs {
            if let Some(id) = cx.symbol_id(inp)? {
                direct_in_syms.insert(id);
            }
        }
        if !target_syms.is_empty() && target_syms.iter().all(|s| direct_in_syms.contains(s)) {
            let simp = crate::engine::Engine::standard().simplify(cx, target)?.expr;
            if let CheckCand::Verified(out) =
                self.verify_functional_cand(cx, target, simp, inputs, assumptions, deadline)?
            {
                self.model = saved_model;
                self.last = saved_last;
                return Ok(Some(out));
            }
        }

        // 4. Implicit functional dependency gate.
        let det = self.is_determined_by_within(cx, target, inputs, assumptions, deadline)?;
        if det == Truth::False {
            self.model = saved_model;
            self.last = saved_last;
            return Ok(None);
        }
        if det == Truth::Unknown && deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
            self.model = saved_model;
            self.last = saved_last;
            return Ok(None);
        }

        // Fresh proxy symbols `p_i` representing `inputs[i]` so candidates are guaranteed by
        // construction to depend solely on `inputs`.
        let mut proxies: Vec<Expr> = Vec::with_capacity(inputs.len());
        let mut keep_ids: HashSet<SymbolId> = HashSet::with_capacity(inputs.len());
        let mut proxy_to_input: Vec<(Expr, Expr)> = Vec::with_capacity(inputs.len());
        for &inp in inputs {
            let p = cx.fresh_symbol(cx.width(inp)?)?;
            if let Some(pid) = cx.symbol_id(p)? {
                keep_ids.insert(pid);
            }
            proxies.push(p);
            proxy_to_input.push((p, inp));
        }

        // 5. Tier A: Equation isolation in terms of `proxies`.
        if let Some(cand_p) = try_algebraic_isolation(
            cx,
            &self.assertions,
            assumptions,
            target,
            inputs,
            &proxies,
            &keep_ids,
        )? {
            let cand_p = crate::engine::Engine::standard().simplify(cx, cand_p)?.expr;
            let cand = cx.substitute(&[cand_p], &proxy_to_input)?[0];
            match self.verify_functional_cand(cx, target, cand, inputs, assumptions, deadline)? {
                CheckCand::Verified(out) => {
                    self.model = saved_model;
                    self.last = saved_last;
                    return Ok(Some(out));
                }
                CheckCand::Counterexample(cex) => {
                    if !samples.iter().any(|(ins, _)| *ins == cex.0) {
                        samples.push(cex);
                    }
                }
                CheckCand::Undecided => {}
            }
        }

        if det != Truth::True {
            self.model = saved_model;
            self.last = saved_last;
            return Ok(None);
        }

        // 6. Tier B.0: Modular-affine interpolation `c_0 + sum_i c_i * cast(inputs[i]) (mod 2^tw)`
        // with CEGIS counterexample refinement.
        if let Some(out) = self.try_modular_affine_def(
            cx,
            target,
            tw,
            inputs,
            &proxies,
            &proxy_to_input,
            assumptions,
            deadline,
            &mut samples,
        )? {
            self.model = saved_model;
            self.last = saved_last;
            return Ok(Some(out));
        }

        // 7. Tier B.1: GF(2)-affine interpolation with diagonal shift-mask-XOR emission + CEGIS.
        if let Some(out) = self.try_gf2_affine_def(
            cx,
            target,
            tw,
            inputs,
            &proxies,
            &proxy_to_input,
            assumptions,
            deadline,
            &mut samples,
        )? {
            self.model = saved_model;
            self.last = saved_last;
            return Ok(Some(out));
        }

        // 8. Tier B.2: Finite-domain `select` tree + observational synthesis CEGIS.
        if let Some(out) = self.try_observational_def(
            cx,
            target,
            tw,
            inputs,
            &proxies,
            &proxy_to_input,
            assumptions,
            deadline,
            &mut samples,
        )? {
            self.model = saved_model;
            self.last = saved_last;
            return Ok(Some(out));
        }

        self.model = saved_model;
        self.last = saved_last;
        Ok(None)
    }

    fn read_io_sample(
        &self,
        cx: &mut Context,
        inputs: &[Expr],
        target: Expr,
    ) -> Result<Option<(Vec<BitVec>, BitVec)>, Error> {
        let Some(m) = self.model() else {
            return Ok(None);
        };
        let mut all = Vec::with_capacity(inputs.len() + 1);
        all.extend_from_slice(inputs);
        all.push(target);
        let mut vals = eval_in(cx, &all, m)?;
        let out_v = vals.pop().expect("target appended");
        Ok(Some((vals, out_v)))
    }

    fn probe_input_point(
        &mut self,
        cx: &mut Context,
        inputs: &[Expr],
        target: Expr,
        point: &[BitVec],
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<Option<(Vec<BitVec>, BitVec)>, Error> {
        if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
            return Ok(None);
        }
        let mut probe_a: Vec<Expr> = Vec::with_capacity(assumptions.len() + inputs.len());
        probe_a.extend_from_slice(assumptions);
        for (&inp, val) in inputs.iter().zip(point) {
            let k = cx.constant(val)?;
            probe_a.push(cx.cmp(crate::CmpOpExt::Eq, inp, k)?);
        }
        if self.check_within(cx, &probe_a, deadline)? == Status::Sat {
            self.read_io_sample(cx, inputs, target)
        } else {
            Ok(None)
        }
    }

    fn verify_functional_cand(
        &mut self,
        cx: &mut Context,
        target: Expr,
        cand: Expr,
        inputs: &[Expr],
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
    ) -> Result<CheckCand, Error> {
        let simp = crate::engine::Engine::standard().simplify(cx, cand)?.expr;
        let ne = cx.cmp(crate::CmpOpExt::Ne, target, simp)?;
        let mut check_a = Vec::with_capacity(assumptions.len() + 1);
        check_a.extend_from_slice(assumptions);
        check_a.push(ne);
        match self.check_within(cx, &check_a, deadline)? {
            Status::Unsat => Ok(CheckCand::Verified(simp)),
            Status::Sat => match self.read_io_sample(cx, inputs, target)? {
                Some(cex) => Ok(CheckCand::Counterexample(cex)),
                None => Ok(CheckCand::Undecided),
            },
            Status::Unknown(_) => Ok(CheckCand::Undecided),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn try_modular_affine_def(
        &mut self,
        cx: &mut Context,
        target: Expr,
        tw: Width,
        inputs: &[Expr],
        proxies: &[Expr],
        proxy_to_input: &[(Expr, Expr)],
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
        samples: &mut Vec<(Vec<BitVec>, BitVec)>,
    ) -> Result<Option<Expr>, Error> {
        let m = inputs.len();
        if m > 8 {
            return Ok(None);
        }
        let widths: Vec<Width> = inputs
            .iter()
            .map(|&e| cx.width(e))
            .collect::<Result<_, _>>()?;

        // Probe `(0, ..., 0)` and unit vectors `(0, ..., 1, ..., 0)` when not yet sampled.
        let zeros: Vec<BitVec> = widths.iter().map(|&w| BitVec::zero(w)).collect();
        if !samples.iter().any(|(ins, _)| *ins == zeros)
            && let Some(s) =
                self.probe_input_point(cx, inputs, target, &zeros, assumptions, deadline)?
        {
            samples.push(s);
        }
        for i in 0..m {
            let mut unit = zeros.clone();
            unit[i] = BitVec::one(widths[i]);
            if !samples.iter().any(|(ins, _)| *ins == unit)
                && let Some(s) =
                    self.probe_input_point(cx, inputs, target, &unit, assumptions, deadline)?
            {
                samples.push(s);
            }
        }

        let max_rounds = m + 4;
        for _ in 0..max_rounds {
            if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
                return Ok(None);
            }
            let Some(coeffs) = fit_modular_affine(tw, samples) else {
                return Ok(None);
            };
            let cand_p = build_modular_affine_expr(cx, tw, proxies, &coeffs)?;
            let cand_p = crate::engine::Engine::standard().simplify(cx, cand_p)?.expr;
            let cand = cx.substitute(&[cand_p], proxy_to_input)?[0];
            match self.verify_functional_cand(cx, target, cand, inputs, assumptions, deadline)? {
                CheckCand::Verified(out) => return Ok(Some(out)),
                CheckCand::Counterexample(cex) => {
                    if samples.iter().any(|(ins, _)| *ins == cex.0) {
                        return Ok(None);
                    }
                    samples.push(cex);
                }
                CheckCand::Undecided => return Ok(None),
            }
        }
        Ok(None)
    }

    #[allow(clippy::too_many_arguments)]
    fn try_gf2_affine_def(
        &mut self,
        cx: &mut Context,
        target: Expr,
        tw: Width,
        inputs: &[Expr],
        proxies: &[Expr],
        proxy_to_input: &[(Expr, Expr)],
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
        samples: &mut Vec<(Vec<BitVec>, BitVec)>,
    ) -> Result<Option<Expr>, Error> {
        if tw.bits() > 128 {
            return Ok(None);
        }
        let widths: Vec<Width> = inputs
            .iter()
            .map(|&e| cx.width(e))
            .collect::<Result<_, _>>()?;
        let total_in_bits: usize = widths.iter().map(|w| usize::from(w.bits())).sum();
        if total_in_bits == 0 || total_in_bits > 128 {
            return Ok(None);
        }

        // Fast GF(2)-affine quartet filter: for any GF(2)-affine `f`,
        // `f(a) ^ f(b) ^ f(c) ^ f(a ^ b ^ c) == 0`.
        if samples.len() < 3 {
            let alt: Vec<BitVec> = widths
                .iter()
                .enumerate()
                .map(|(i, &w)| {
                    BitVec::wrapping_from_u64(
                        w,
                        0x5555_5555_5555_5555u64.wrapping_add(i as u64 * 3),
                    )
                })
                .collect();
            if !samples.iter().any(|(ins, _)| *ins == alt)
                && let Some(s) =
                    self.probe_input_point(cx, inputs, target, &alt, assumptions, deadline)?
            {
                samples.push(s);
            }
        }
        if samples.len() >= 3 {
            let fourth: Vec<BitVec> = (0..inputs.len())
                .map(|i| {
                    let ab = crate::facts::known::bv_xor(&samples[0].0[i], &samples[1].0[i]);
                    crate::facts::known::bv_xor(&ab, &samples[2].0[i])
                })
                .collect();
            if !samples.iter().any(|(ins, _)| *ins == fourth)
                && let Some(s) =
                    self.probe_input_point(cx, inputs, target, &fourth, assumptions, deadline)?
            {
                samples.push(s);
            }
        }

        // Check consistency on initial samples before probing bit columns.
        if fit_gf2_affine(tw, &widths, samples).is_none() {
            return Ok(None);
        }

        // Passed quartet check: probe single-bit flips from `samples[0]` if `total_in_bits <= 64`.
        if total_in_bits <= 64
            && let Some(base) = samples.first().map(|(ins, _)| ins.clone())
        {
            for (i, &w) in widths.iter().enumerate() {
                for b in 0..w.bits() {
                    if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
                        return Ok(None);
                    }
                    let mut pt = base.clone();
                    let mask = crate::facts::known::bv_shl(&BitVec::one(w), u32::from(b));
                    pt[i] = crate::facts::known::bv_xor(&pt[i], &mask);
                    if !samples.iter().any(|(ins, _)| *ins == pt)
                        && let Some(s) =
                            self.probe_input_point(cx, inputs, target, &pt, assumptions, deadline)?
                    {
                        samples.push(s);
                    }
                }
            }
        }

        let max_cegis = total_in_bits.min(64) + 2;
        for _ in 0..max_cegis {
            if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
                return Ok(None);
            }
            let Some((c0, cols)) = fit_gf2_affine(tw, &widths, samples) else {
                return Ok(None);
            };
            let cand_p = build_gf2_affine_expr(cx, tw, proxies, &widths, &c0, &cols)?;
            let cand_p = crate::engine::Engine::standard().simplify(cx, cand_p)?.expr;
            let cand = cx.substitute(&[cand_p], proxy_to_input)?[0];
            match self.verify_functional_cand(cx, target, cand, inputs, assumptions, deadline)? {
                CheckCand::Verified(out) => return Ok(Some(out)),
                CheckCand::Counterexample(cex) => {
                    if samples.iter().any(|(ins, _)| *ins == cex.0) {
                        return Ok(None);
                    }
                    samples.push(cex);
                }
                CheckCand::Undecided => return Ok(None),
            }
        }
        Ok(None)
    }

    #[allow(clippy::too_many_arguments)]
    fn try_observational_def(
        &mut self,
        cx: &mut Context,
        target: Expr,
        tw: Width,
        inputs: &[Expr],
        proxies: &[Expr],
        proxy_to_input: &[(Expr, Expr)],
        assumptions: &[Expr],
        deadline: Option<Deadline<'_>>,
        samples: &mut Vec<(Vec<BitVec>, BitVec)>,
    ) -> Result<Option<Expr>, Error> {
        let m = inputs.len();
        let widths: Vec<Width> = inputs
            .iter()
            .map(|&e| cx.width(e))
            .collect::<Result<_, _>>()?;

        // Try to exhaust up to 9 distinct input tuples to detect small finite domains (`<= 8`).
        let mut exhausted_domain = false;
        if samples.len() <= 8 {
            let mut block_a = assumptions.to_vec();
            for (ins, _) in samples.iter() {
                block_a.push(neq_tuple(cx, inputs, ins)?);
            }
            while samples.len() < 9 {
                if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
                    return Ok(None);
                }
                match self.check_within(cx, &block_a, deadline)? {
                    Status::Unsat => {
                        exhausted_domain = true;
                        break;
                    }
                    Status::Sat => {
                        let Some(s) = self.read_io_sample(cx, inputs, target)? else {
                            break;
                        };
                        block_a.push(neq_tuple(cx, inputs, &s.0)?);
                        samples.push(s);
                    }
                    Status::Unknown(_) => break,
                }
            }
        }

        // Seed a handful of diverse boundary/random probes when domain is larger.
        if !exhausted_domain && samples.len() < 12 && m <= 4 {
            let mut rng = 0x9e37_79b9_7f4a_7c15u64 ^ u64::from(tw.bits());
            for step in 0..8u64 {
                if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
                    break;
                }
                let pt: Vec<BitVec> = widths
                    .iter()
                    .enumerate()
                    .map(|(i, &w)| {
                        rng ^= rng << 13;
                        rng ^= rng >> 7;
                        rng ^= rng << 17;
                        let v = match step {
                            0 => 2,
                            1 => 3,
                            2 => 7,
                            3 => u64::MAX,
                            _ => rng.wrapping_add(i as u64 * 17),
                        };
                        BitVec::wrapping_from_u64(w, v)
                    })
                    .collect();
                if !samples.iter().any(|(ins, _)| *ins == pt)
                    && let Some(s) =
                        self.probe_input_point(cx, inputs, target, &pt, assumptions, deadline)?
                {
                    samples.push(s);
                }
            }
        }

        // Bottom-up observational synthesis + CEGIS when `tw <= 64` and `m <= 4`.
        if tw.bits() <= 64 && m <= 4 && !samples.is_empty() {
            let extra_consts =
                problem_constants_u64(cx, &self.assertions, assumptions, target, tw)?;
            for _round in 0..5 {
                if deadline.is_some_and(|d| d.clock.now_ticks() >= d.at) {
                    break;
                }
                let Some(cand_p) =
                    observational_enumerate(cx, tw, proxies, &widths, samples, &extra_consts)?
                else {
                    break;
                };
                let cand_p = crate::engine::Engine::standard().simplify(cx, cand_p)?.expr;
                let cand = cx.substitute(&[cand_p], proxy_to_input)?[0];
                match self.verify_functional_cand(
                    cx,
                    target,
                    cand,
                    inputs,
                    assumptions,
                    deadline,
                )? {
                    CheckCand::Verified(out) => return Ok(Some(out)),
                    CheckCand::Counterexample(cex) => {
                        if samples.iter().any(|(ins, _)| *ins == cex.0) {
                            break;
                        }
                        samples.push(cex);
                    }
                    CheckCand::Undecided => break,
                }
            }
        }

        // Exact finite-domain `select` tree when total distinct reachable input tuples `<= 8`
        // (and `synth::synthesize` shrinkage when all inputs match `tw`).
        if exhausted_domain && !samples.is_empty() && samples.len() <= 8 {
            let sel_p = build_select_lut(cx, proxies, samples)?;
            let mut best_p = crate::engine::Engine::standard().simplify(cx, sel_p)?.expr;
            if m <= 4
                && widths.iter().all(|&w| w == tw)
                && let Some(shrunk) =
                    crate::synth::synthesize(cx, best_p, &crate::synth::Config::extended())?
            {
                best_p = shrunk;
            }
            let cand = cx.substitute(&[best_p], proxy_to_input)?[0];
            if let CheckCand::Verified(out) =
                self.verify_functional_cand(cx, target, cand, inputs, assumptions, deadline)?
            {
                return Ok(Some(out));
            }
        }

        Ok(None)
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
            && core.len() > 1
        {
            let search: Box<dyn prove::Backend> = match &self.cfg.backend {
                Some(make) => (make.0)(),
                None => Box::new(prove::sat::Solver::new()),
            };
            let mut inc = prove::Incremental::on(
                search,
                quick.max_nodes.saturating_mul(core.len().max(1)).max(1),
            )
            .with_question_nodes(quick.max_nodes);
            let mut i = 0;
            while i < core.len() && core.len() > 1 {
                let rest_items: Vec<(CoreItem, Expr)> = (core.iter().enumerate())
                    .filter(|&(k, _)| k != i)
                    .map(|(_, &pair)| pair)
                    .collect();
                let rest: Vec<Expr> = rest_items.iter().map(|&(_, e)| e).collect();
                match inc.solve(cx, &rest, quick.limits())? {
                    prove::IncrementalAnswer::Unsat(sub) => {
                        let prev_before = core[..i].to_vec();
                        core = sub.into_iter().map(|k| rest_items[k]).collect();
                        i = core
                            .iter()
                            .position(|item| !prev_before.contains(item))
                            .unwrap_or(core.len());
                    }
                    prove::IncrementalAnswer::Unknown(Unknown::TooLarge { .. }) => {
                        let all = conjunction(cx, &rest)?;
                        if matches!(prove::satisfy(cx, all, &quick)?, Ok(None)) {
                            core.remove(i);
                        } else {
                            i += 1;
                        }
                    }
                    _ => {
                        i += 1;
                    }
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

/// Default value of a symbol not listed in a model: its declared known-one bits (zero when none).
fn default_for_symbol(cx: &Context, key: &crate::SymbolKey, w: Width) -> BitVec {
    cx.find_symbol(key)
        .and_then(|s| cx.declared_known(s).ok().flatten())
        .map_or_else(|| BitVec::zero(w), |kb| kb.known_one())
}

/// Projects `v` onto the bits declared for `key` (`(v & !known_zero) | known_one`).
fn fit_declared(cx: &Context, key: &crate::SymbolKey, v: BitVec) -> BitVec {
    let Some(kb) = cx
        .find_symbol(key)
        .and_then(|s| cx.declared_known(s).ok().flatten())
    else {
        return v;
    };
    let keep = crate::facts::known::bv_not(&kb.known_zero());
    crate::facts::known::bv_or(&crate::facts::known::bv_and(&v, &keep), &kb.known_one())
}

/// Whether `v` satisfies the bits declared for `key`.
fn satisfies_declared(cx: &Context, key: &crate::SymbolKey, v: &BitVec) -> bool {
    let Some(kb) = cx
        .find_symbol(key)
        .and_then(|s| cx.declared_known(s).ok().flatten())
    else {
        return true;
    };
    crate::facts::known::bv_and(v, &kb.known()) == kb.known_one()
}

/// `model` over exactly the symbols `es` read: one it does not list takes its declared known-one
/// bits (zero when unconstrained).
fn complete(cx: &mut Context, es: &[Expr], model: &Model) -> Result<Model, Error> {
    let mut m = Vec::new();
    for sym in cx.symbols_in(es)? {
        let (Some(k), Some(w)) = (cx.symbol_key(sym).cloned(), cx.symbol_width(sym)) else {
            continue;
        };
        let v = (model.iter().find(|(f, _)| *f == k)).map_or_else(
            || default_for_symbol(cx, &k, w),
            |&(_, v)| fit_declared(cx, &k, v),
        );
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

    /// The names of a slice: its assertions' hashes (plus any declared known-bit axioms on its
    /// symbols), and its shape.
    fn key(cx: &mut Context, es: &[Expr]) -> Result<(Vec<(u64, u64)>, u64), Error> {
        let shapes = cx.shape_hashes(es)?;
        let mut name = Vec::with_capacity(es.len());
        for (&e, &shape) in es.iter().zip(&shapes) {
            name.push((cx.structural_hash(e)?, shape));
        }
        for sym in cx.symbols_in(es)? {
            let Some(key) = cx.symbol_key(sym).cloned() else {
                continue;
            };
            let Some(s_expr) = cx.find_symbol(&key) else {
                continue;
            };
            let Some(kb) = cx.declared_known(s_expr)? else {
                continue;
            };
            let mut dh = crate::hash::combine(0x6465_636c_6b6e_776e, key.structural_hash());
            let mut ds = crate::hash::combine(0x6465_636c_7368_6170, u64::from(kb.width().bits()));
            for &l in kb.known_zero().limbs() {
                dh = crate::hash::combine(dh, l);
                ds = crate::hash::combine(ds, u64::from(l.count_ones()));
            }
            for &l in kb.known_one().limbs() {
                dh = crate::hash::combine(dh, l);
                ds = crate::hash::combine(ds, u64::from(l.count_ones()));
            }
            name.push((dh, ds));
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
        conflicts: Option<u64>,
    ) {
        // (An assignment that happened to satisfy says nothing of the searches.)
        if by != DecidedBy::Probe {
            let d = self.strategy.entry(shape).or_default();
            match by {
                DecidedBy::Incremental => {
                    d.kept = d.kept.saturating_add(1);
                    if let Some(c) = conflicts {
                        d.conflicts = d.conflicts.max(c);
                    }
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

/// Solves the assertions that define a symbol (including through bijective arithmetic/bitwise
/// spines, xorshifts, extensions, and split-register concatenations) and substitutes the
/// solutions into the others: what is left of them (in order), and each symbol solved for with
/// what it equals (over symbols not solved for).
fn solve_equations(cx: &mut Context, es: &[Expr]) -> Result<Solved, Error> {
    struct Solution {
        key: crate::SymbolKey,
        equals: Expr,
        /// The symbols `equals` reads.
        reads: Vec<SymbolId>,
    }
    let mut flat: Vec<Expr> = Vec::with_capacity(es.len());
    let mut stack: Vec<Expr> = es.iter().rev().copied().collect();
    while let Some(e) = stack.pop() {
        match cx.view(e)? {
            crate::View::Bin(BinOp::And, a, b) => stack.extend([b, a]),
            _ => flat.push(e),
        }
    }

    let mut solutions: Vec<Solution> = Vec::new();
    let mut map: Vec<(Expr, Expr)> = Vec::new();
    let mut current = flat;

    for _round in 0..4 {
        if solutions.len() >= SOLVED_SYMBOLS || current.is_empty() {
            break;
        }
        let prev_solved = solutions.len();
        let mut kept: Vec<Expr> = Vec::with_capacity(current.len());
        let mut queue: std::collections::VecDeque<Expr> = current.into_iter().collect();

        while let Some(e) = queue.pop_front() {
            let now = if map.is_empty() {
                e
            } else {
                cx.substitute(&[e], &map)?[0]
            };
            if cx.as_const(now)? == Some(BitVec::from_bool(true)) {
                continue;
            }
            if solutions.len() >= SOLVED_SYMBOLS {
                kept.push(now);
                continue;
            }
            // Split `concat(hi, lo) == rhs` into two slice equations so split-register pairs
            // (`edx:eax`, `x0_hi:w0`) expose both halves to isolation.
            if let Some((eq_hi, eq_lo)) = split_concat_eq(cx, now)? {
                queue.push_front(eq_lo);
                queue.push_front(eq_hi);
                continue;
            }
            let Some((symbol, id, equals, reads, guard)) = definition(cx, now)? else {
                kept.push(now);
                continue;
            };
            let Some(key) = cx.symbol_key(id).cloned() else {
                kept.push(now);
                continue;
            };
            if let Some(g) = guard {
                queue.push_front(g);
            }
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
        current = if map.is_empty() {
            kept
        } else {
            cx.substitute(&kept, &map)?
        };
        if solutions.len() == prev_solved {
            break;
        }
    }
    Ok((
        current,
        solutions.into_iter().map(|s| (s.key, s.equals)).collect(),
    ))
}

fn split_concat_eq(cx: &mut Context, p: Expr) -> Result<Option<(Expr, Expr)>, Error> {
    use crate::View;
    let View::Cmp(crate::CmpOp::Eq, a, b) = cx.view(p)? else {
        return Ok(None);
    };
    for (lhs, rhs) in [(a, b), (b, a)] {
        if let View::Concat { hi, lo } = cx.view(lhs)? {
            let (whi, wlo) = (cx.width(hi)?, cx.width(lo)?);
            let rhs_lo = cx.extract(rhs, 0, wlo)?;
            let rhs_hi = cx.extract(rhs, wlo.bits(), whi)?;
            return Ok(Some((
                cx.cmp(crate::CmpOpExt::Eq, hi, rhs_hi)?,
                cx.cmp(crate::CmpOpExt::Eq, lo, rhs_lo)?,
            )));
        }
    }
    Ok(None)
}

/// If `e` is a self-xorshift `u ^ (u >>u s)` or `u ^ (u << s)` (`1 <= s < W`), returns
/// `(u, is_left, s)`.
fn peel_xorshift(cx: &Context, e: Expr) -> Result<Option<(Expr, bool, u32)>, Error> {
    use crate::View;
    let w = u32::from(cx.width(e)?.bits());
    let View::Bin(BinOp::Xor, a, b) = cx.view(e)? else {
        return Ok(None);
    };
    for (u, shifted) in [(a, b), (b, a)] {
        match cx.view(shifted)? {
            View::Bin(op @ (BinOp::LShr | BinOp::Shl), src, cnt) if src == u => {
                if let Some(cv) = cx.as_const(cnt)?
                    && let Some(s) = cv.to_u64()
                    && s > 0
                    && s < u64::from(w)
                {
                    return Ok(Some((u, op == BinOp::Shl, s as u32)));
                }
            }
            _ => {}
        }
    }
    Ok(None)
}

fn invert_xorshift_expr(
    cx: &mut Context,
    mut v: Expr,
    is_left: bool,
    mut step: u32,
) -> Result<Expr, Error> {
    let w = cx.width(v)?;
    let wb = u32::from(w.bits());
    let op = if is_left { BinOp::Shl } else { BinOp::LShr };
    while step < wb {
        let c = cx.constant_u64(w, u64::from(step))?;
        let sh = cx.bin(op, v, c)?;
        v = cx.bin(BinOp::Xor, v, sh)?;
        step = step.saturating_mul(2);
    }
    Ok(v)
}

/// Attempts to isolate a free unconstrained symbol `x` from `lhs == rhs` by peeling bijective
/// layers (and at most one outer `Zext`/`Sext`, emitting the corresponding range guard) around a
/// single occurrence of `x`.
#[allow(clippy::type_complexity)]
fn isolate_from_eq(
    cx: &mut Context,
    mut lhs: Expr,
    mut rhs: Expr,
) -> Result<Option<(Expr, SymbolId, Expr, Vec<SymbolId>, Option<Expr>)>, Error> {
    use crate::View;
    let free = |cx: &Context, e: Expr| -> Result<Option<SymbolId>, Error> {
        Ok(match cx.view(e)? {
            View::Sym(id) if cx.declared_known(e)?.is_none() => Some(id),
            _ => None,
        })
    };
    let mut guard: Option<Expr> = None;
    for _depth in 0..24 {
        if let Some(id) = free(cx, lhs)? {
            let mut reads = cx.symbols_in(&[rhs])?;
            if let Some(g) = guard {
                for gs in cx.symbols_in(&[g])? {
                    if !reads.contains(&gs) {
                        reads.push(gs);
                    }
                }
            }
            if !reads.contains(&id) {
                return Ok(Some((lhs, id, rhs, reads, guard)));
            }
            return Ok(None);
        }
        if let Some((u, is_left, step)) = peel_xorshift(cx, lhs)? {
            rhs = invert_xorshift_expr(cx, rhs, is_left, step)?;
            lhs = u;
            continue;
        }
        match cx.view(lhs)? {
            View::Un(op @ (UnOp::Not | UnOp::Neg | UnOp::Bswap | UnOp::BitRev), u) => {
                rhs = cx.un(op, rhs)?;
                lhs = u;
            }
            View::Bin(BinOp::Add, a, b) => {
                // Pick the side that still contains a free symbol; try `a` first unless `a` has
                // no symbols or `b` is a direct free symbol.
                let prefer_b = free(cx, b)?.is_some() || cx.symbols_in(&[a])?.is_empty();
                let (u, other) = if prefer_b { (b, a) } else { (a, b) };
                rhs = cx.bin(BinOp::Sub, rhs, other)?;
                lhs = u;
            }
            View::Bin(BinOp::Sub, a, b) => {
                let prefer_b = free(cx, b)?.is_some() || cx.symbols_in(&[a])?.is_empty();
                if prefer_b {
                    rhs = cx.bin(BinOp::Sub, a, rhs)?;
                    lhs = b;
                } else {
                    rhs = cx.bin(BinOp::Add, rhs, b)?;
                    lhs = a;
                }
            }
            View::Bin(BinOp::Xor, a, b) => {
                let prefer_b = free(cx, b)?.is_some() || cx.symbols_in(&[a])?.is_empty();
                let (u, other) = if prefer_b { (b, a) } else { (a, b) };
                rhs = cx.bin(BinOp::Xor, rhs, other)?;
                lhs = u;
            }
            View::Bin(BinOp::Mul, a, b) => {
                let (u, c) = match (cx.as_const(a)?, cx.as_const(b)?) {
                    (None, Some(c)) => (a, c),
                    (Some(c), None) => (b, c),
                    _ => return Ok(None),
                };
                let Some(inv) = odd_inverse(&c) else {
                    return Ok(None);
                };
                let inv_e = cx.constant(&inv)?;
                rhs = cx.bin(BinOp::Mul, rhs, inv_e)?;
                lhs = u;
            }
            View::Bin(BinOp::RotL, u, cnt) => {
                rhs = cx.bin(BinOp::RotR, rhs, cnt)?;
                lhs = u;
            }
            View::Bin(BinOp::RotR, u, cnt) => {
                rhs = cx.bin(BinOp::RotL, rhs, cnt)?;
                lhs = u;
            }
            View::Zext(u) if guard.is_none() => {
                let (w_out, w_in) = (cx.width(lhs)?, cx.width(u)?);
                let hi_w = Width::new(w_out.bits() - w_in.bits())?;
                let hi = cx.extract(rhs, w_in.bits(), hi_w)?;
                let zero = cx.zero(hi_w)?;
                guard = Some(cx.cmp(crate::CmpOpExt::Eq, hi, zero)?);
                rhs = cx.extract(rhs, 0, w_in)?;
                lhs = u;
            }
            View::Sext(u) if guard.is_none() => {
                let (w_out, w_in) = (cx.width(lhs)?, cx.width(u)?);
                let lo = cx.extract(rhs, 0, w_in)?;
                let back = cx.sext(lo, w_out)?;
                guard = Some(cx.cmp(crate::CmpOpExt::Eq, back, rhs)?);
                rhs = lo;
                lhs = u;
            }
            View::Ext { op, output, args } => {
                let Some(reg) = cx.registry.clone() else {
                    return Ok(None);
                };
                let Some(ext_op) = reg.op_at(op.raw()) else {
                    return Ok(None);
                };
                let slice = args.as_slice();
                // Choose the single argument holding symbols (preferring a direct free symbol).
                let mut target_arg: Option<usize> = None;
                for (idx, &arg_e) in slice.iter().enumerate() {
                    if free(cx, arg_e)?.is_some() {
                        target_arg = Some(idx);
                        break;
                    }
                }
                if target_arg.is_none() {
                    let non_const: Vec<usize> = (0..slice.len())
                        .filter(|&idx| cx.symbols_in(&[slice[idx]]).is_ok_and(|s| !s.is_empty()))
                        .collect();
                    if let [only] = non_const[..] {
                        target_arg = Some(only);
                    }
                }
                let Some(arg_idx) = target_arg else {
                    return Ok(None);
                };
                if let Some(inv_decl) = ext_op.inverse(output, arg_idx as u8)
                    && let Some(inv_id) = reg.id(inv_decl.op.as_ref())
                {
                    let mut inv_args = Vec::with_capacity(inv_decl.args.len());
                    let mut ok = true;
                    for &ia in &inv_decl.args {
                        match ia {
                            crate::ext::InverseArg::Output => inv_args.push(rhs),
                            crate::ext::InverseArg::Arg(pos) => {
                                if let Some(&ae) = slice.get(usize::from(pos)) {
                                    inv_args.push(ae);
                                } else {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                    }
                    if ok
                        && cx.width(slice[arg_idx])? == cx.width(lhs)?
                        && let Ok(undone) =
                            cx.ext_output(inv_id, usize::from(inv_decl.output), &inv_args)
                    {
                        rhs = undone;
                        lhs = slice[arg_idx];
                        continue;
                    }
                }
                // Constant-RHS preimage via `ExtOp::invert` when `Bijective`.
                if let Some(rhs_bv) = cx.as_const(rhs)? {
                    let mut const_args = Vec::with_capacity(slice.len());
                    let mut kbs = Vec::with_capacity(slice.len());
                    let mut all_other_const = true;
                    for (idx, &arg_e) in slice.iter().enumerate() {
                        let aw = cx.width(arg_e)?;
                        if idx == arg_idx {
                            const_args.push(BitVec::zero(aw));
                            kbs.push(crate::facts::KnownBits::unknown(aw));
                        } else if let Some(cv) = cx.as_const(arg_e)? {
                            const_args.push(cv);
                            kbs.push(crate::facts::KnownBits::constant(&cv));
                        } else {
                            all_other_const = false;
                            break;
                        }
                    }
                    if all_other_const
                        && ext_op.invertible(output, arg_idx as u8, &kbs)
                            == crate::ext::Invertible::Bijective
                        && let Some(pre) =
                            ext_op.invert(output, arg_idx as u8, &const_args, &rhs_bv)
                    {
                        const_args[arg_idx] = pre;
                        if let Ok(sig) = ext_op
                            .signature(&const_args.iter().map(BitVec::width).collect::<Vec<_>>())
                        {
                            let mut check_out: Vec<BitVec> =
                                sig.outputs().map(|(_, w)| BitVec::zero(w)).collect();
                            ext_op.eval(&const_args, &mut check_out);
                            if check_out.get(usize::from(output)) == Some(&rhs_bv) {
                                rhs = cx.constant(&pre)?;
                                lhs = slice[arg_idx];
                                continue;
                            }
                        }
                    }
                }
                return Ok(None);
            }
            _ => return Ok(None),
        }
    }
    Ok(None)
}

/// A symbol `p` defines and what it defines it as, with any side guard required by narrowing an
/// injective extension (`zext`/`sext`).
#[allow(clippy::type_complexity)]
fn definition(
    cx: &mut Context,
    p: Expr,
) -> Result<Option<(Expr, SymbolId, Expr, Vec<SymbolId>, Option<Expr>)>, Error> {
    use crate::View;
    let free = |cx: &Context, e: Expr| -> Result<Option<SymbolId>, Error> {
        Ok(match cx.view(e)? {
            View::Sym(id) if cx.declared_known(e)?.is_none() => Some(id),
            _ => None,
        })
    };
    match cx.view(p)? {
        View::Sym(_) => {
            if let Some(id) = free(cx, p)? {
                return Ok(Some((p, id, cx.bool(true)?, Vec::new(), None)));
            }
        }
        View::Un(UnOp::Not, a) => {
            if let Some(id) = free(cx, a)? {
                return Ok(Some((a, id, cx.bool(false)?, Vec::new(), None)));
            }
            if let View::Cmp(crate::CmpOp::Ne, l, r) = cx.view(a)? {
                for (lhs, rhs) in [(l, r), (r, l)] {
                    if let Some(sol) = isolate_from_eq(cx, lhs, rhs)? {
                        return Ok(Some(sol));
                    }
                }
            }
        }
        View::Cmp(crate::CmpOp::Eq, a, b) => {
            for (lhs, rhs) in [(a, b), (b, a)] {
                if let Some(sol) = isolate_from_eq(cx, lhs, rhs)? {
                    return Ok(Some(sol));
                }
            }
        }
        _ => {}
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

/// The expressions at `model`, a symbol it does not list at its declared known-one bits (zero
/// when unconstrained).
fn eval_in(cx: &mut Context, es: &[Expr], model: &Model) -> Result<Vec<BitVec>, Error> {
    let mut defaults: Vec<(crate::SymbolKey, BitVec)> = Vec::new();
    // (With nothing declared every default is zero: the symbols are not looked up.)
    let symbols = match cx.any_declared() {
        true => cx.symbols_in(es)?,
        false => Vec::new(),
    };
    for sym in symbols {
        let (Some(k), Some(w)) = (cx.symbol_key(sym).cloned(), cx.symbol_width(sym)) else {
            continue;
        };
        if !model.iter().any(|(mk, _)| *mk == k) {
            defaults.push((k.clone(), default_for_symbol(cx, &k, w)));
        }
    }
    let env = FnEnv(|key: &crate::SymbolKey, w: Width| {
        Some(
            (model.iter().find(|(k, _)| k == key))
                .or_else(|| defaults.iter().find(|(k, _)| k == key))
                .map_or_else(|| BitVec::zero(w), |&(_, v)| v),
        )
    });
    cx.eval(es, &env)
}

/// A model of `es` among `tries` assignments: every symbol all ones, then each symbol a
/// value drawn from its name's place and the try's number (zero, all ones, one, a small
/// number or any value), projected onto any declared known bits, the same for the same question.
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
                    _ => {
                        let limbs: [u64; 8] = core::array::from_fn(|_| next());
                        BitVec::wrapping_from_limbs(*w, &limbs)
                    }
                };
                (k.clone(), fit_declared(cx, k, v))
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
                    let limbs: [u64; 8] = core::array::from_fn(|_| next());
                    BitVec::wrapping_from_limbs(w, &limbs)
                };
                let xored = BitVec::apply_bin(BinOp::Xor, &slot.1, &change).unwrap_or(slot.1);
                slot.1 = fit_declared(cx, &key, xored);
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
                if !satisfies_declared(cx, &key, &target) {
                    return Ok(false);
                }
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

/// Whether `model` respects declared known bits on every symbol of `ps` and makes every 1-bit
/// expression of `ps` true.
fn holds(cx: &mut Context, ps: &[Expr], model: &Model) -> Result<bool, Error> {
    if !cx.any_declared() {
        return Ok(eval_in(cx, ps, model)?.iter().all(|v| !v.is_zero()));
    }
    for sym in cx.symbols_in(ps)? {
        let (Some(k), Some(w)) = (cx.symbol_key(sym).cloned(), cx.symbol_width(sym)) else {
            continue;
        };
        let v = (model.iter().find(|(mk, _)| *mk == k))
            .map_or_else(|| default_for_symbol(cx, &k, w), |&(_, v)| v);
        if !satisfies_declared(cx, &k, &v) {
            return Ok(false);
        }
    }
    Ok(eval_in(cx, ps, model)?.iter().all(|v| !v.is_zero()))
}

enum CheckCand {
    Verified(Expr),
    Counterexample((Vec<BitVec>, BitVec)),
    Undecided,
}

fn neq_tuple(cx: &mut Context, inputs: &[Expr], vals: &[BitVec]) -> Result<Expr, Error> {
    let mut disj = cx.bool(false)?;
    for (&inp, val) in inputs.iter().zip(vals) {
        let k = cx.constant(val)?;
        let ne = cx.cmp(crate::CmpOpExt::Ne, inp, k)?;
        disj = cx.bin(BinOp::Or, disj, ne)?;
    }
    Ok(disj)
}

fn cast_expr_to(cx: &mut Context, e: Expr, tw: Width) -> Result<Expr, Error> {
    let w = cx.width(e)?;
    if w == tw {
        Ok(e)
    } else if w < tw {
        cx.zext(e, tw)
    } else {
        cx.trunc(e, tw)
    }
}

fn cast_bv_to(v: &BitVec, tw: Width) -> BitVec {
    let w = v.width();
    if w == tw {
        *v
    } else if w < tw {
        v.zext(tw).unwrap_or_else(|_| BitVec::zero(tw))
    } else {
        v.trunc(tw).unwrap_or_else(|_| BitVec::zero(tw))
    }
}

/// Tier A: Isolates `target` in terms of `proxies` (`keep_ids`) across assertions + assumptions.
fn try_algebraic_isolation(
    cx: &mut Context,
    assertions: &[Expr],
    assumptions: &[Expr],
    target: Expr,
    inputs: &[Expr],
    proxies: &[Expr],
    keep_ids: &HashSet<SymbolId>,
) -> Result<Option<Expr>, Error> {
    let tw = cx.width(target)?;
    let t_out = cx.fresh_symbol(tw)?;
    let Some(t_out_id) = cx.symbol_id(t_out)? else {
        return Ok(None);
    };

    // Map bare-symbol inputs directly to their proxy symbols (deduplicated).
    let mut sym_in_map: Vec<(Expr, Expr)> = Vec::new();
    let mut non_sym_eqs: Vec<Expr> = Vec::new();
    for (&inp, &p) in inputs.iter().zip(proxies) {
        if cx.symbol_id(inp)?.is_some() {
            if !sym_in_map.iter().any(|&(from, _)| from == inp) {
                sym_in_map.push((inp, p));
            } else if let Some(&(_, first_p)) = sym_in_map.iter().find(|&&(from, _)| from == inp) {
                non_sym_eqs.push(cx.cmp(crate::CmpOpExt::Eq, p, first_p)?);
            }
        }
    }

    let mut raw_preds: Vec<Expr> = Vec::with_capacity(assertions.len() + assumptions.len() + 2);
    raw_preds.extend_from_slice(assertions);
    raw_preds.extend_from_slice(assumptions);
    if !sym_in_map.is_empty() {
        raw_preds = cx.substitute(&raw_preds, &sym_in_map)?;
    }
    let target_sub = if sym_in_map.is_empty() {
        target
    } else {
        cx.substitute(&[target], &sym_in_map)?[0]
    };
    raw_preds.push(cx.cmp(crate::CmpOpExt::Eq, t_out, target_sub)?);
    raw_preds.extend(non_sym_eqs);
    for (&inp, &p) in inputs.iter().zip(proxies) {
        if cx.symbol_id(inp)?.is_none() {
            let inp_sub = if sym_in_map.is_empty() {
                inp
            } else {
                cx.substitute(&[inp], &sym_in_map)?[0]
            };
            raw_preds.push(cx.cmp(crate::CmpOpExt::Eq, p, inp_sub)?);
        }
    }

    // Flatten top-level `And` conjuncts.
    let mut current: Vec<Expr> = Vec::with_capacity(raw_preds.len());
    let mut stack: Vec<Expr> = raw_preds.into_iter().rev().collect();
    while let Some(e) = stack.pop() {
        match cx.view(e)? {
            crate::View::Bin(BinOp::And, a, b) => stack.extend([b, a]),
            _ => current.push(e),
        }
    }

    struct Sol {
        id: SymbolId,
        equals: Expr,
        reads: Vec<SymbolId>,
    }
    let mut solutions: Vec<Sol> = Vec::new();
    let mut map: Vec<(Expr, Expr)> = Vec::new();
    let mut simplified_once = false;

    for round in 0..8 {
        if current.is_empty() || solutions.len() >= SOLVED_SYMBOLS {
            break;
        }
        // Eliminate intermediate non-keep, non-`t_out` symbols first; allow `t_out` once no
        // intermediate symbol made progress or after round 2.
        let allow_target = round >= 2;
        let prev_len = solutions.len();
        let mut kept: Vec<Expr> = Vec::with_capacity(current.len());
        let mut queue: std::collections::VecDeque<Expr> = current.into_iter().collect();

        while let Some(e) = queue.pop_front() {
            let now = if map.is_empty() {
                e
            } else {
                cx.substitute(&[e], &map)?[0]
            };
            if cx.as_const(now)? == Some(BitVec::from_bool(true)) {
                continue;
            }
            if let Some((eq_hi, eq_lo)) = split_concat_eq(cx, now)? {
                queue.push_front(eq_lo);
                queue.push_front(eq_hi);
                continue;
            }
            let mut forbid = keep_ids.clone();
            if !allow_target {
                forbid.insert(t_out_id);
            }
            let Some((sym_expr, id, equals, reads)) = definition_keeping(cx, now, &forbid)? else {
                kept.push(now);
                continue;
            };
            if map.iter().any(|&(f, _)| f == sym_expr) {
                kept.push(now);
                continue;
            }
            for (k, s) in solutions.iter_mut().enumerate() {
                if s.reads.contains(&id) {
                    s.equals = cx.substitute(&[s.equals], &[(sym_expr, equals)])?[0];
                    s.reads = cx.symbols_in(&[s.equals])?;
                    map[k].1 = s.equals;
                }
            }
            map.push((sym_expr, equals));
            solutions.push(Sol { id, equals, reads });
        }

        current = if map.is_empty() {
            kept
        } else {
            cx.substitute(&kept, &map)?
        };

        if solutions.len() == prev_len && allow_target {
            if !simplified_once {
                simplified_once = true;
                let eng = crate::engine::Engine::standard();
                let mut next_cur = Vec::with_capacity(current.len());
                for c in current {
                    next_cur.push(eng.simplify(cx, c)?.expr);
                }
                current = next_cur;
                continue;
            }
            break;
        }
    }

    if let Some(sol) = solutions.iter().find(|s| s.id == t_out_id) {
        let mut cand = sol.equals;
        if !sol.reads.iter().all(|r| keep_ids.contains(r)) {
            cand = crate::engine::Engine::standard().simplify(cx, cand)?.expr;
        }
        let reads = cx.symbols_in(&[cand])?;
        if reads.iter().all(|r| keep_ids.contains(r)) {
            return Ok(Some(cand));
        }
    }
    Ok(None)
}

#[allow(clippy::type_complexity)]
fn definition_keeping(
    cx: &mut Context,
    p: Expr,
    forbid: &HashSet<SymbolId>,
) -> Result<Option<(Expr, SymbolId, Expr, Vec<SymbolId>)>, Error> {
    use crate::View;
    let free = |cx: &Context, e: Expr| -> Result<Option<SymbolId>, Error> {
        Ok(match cx.view(e)? {
            View::Sym(id) if !forbid.contains(&id) => Some(id),
            _ => None,
        })
    };
    match cx.view(p)? {
        View::Sym(_) => {
            if let Some(id) = free(cx, p)? {
                return Ok(Some((p, id, cx.bool(true)?, Vec::new())));
            }
        }
        View::Un(UnOp::Not, a) => {
            if let Some(id) = free(cx, a)? {
                return Ok(Some((a, id, cx.bool(false)?, Vec::new())));
            }
            if let View::Cmp(CmpOp::Ne, l, r) = cx.view(a)? {
                for (lhs, rhs) in [(l, r), (r, l)] {
                    if let Some(sol) = isolate_from_eq_keeping(cx, lhs, rhs, forbid)? {
                        return Ok(Some(sol));
                    }
                }
            }
        }
        View::Cmp(CmpOp::Eq, a, b) => {
            for (lhs, rhs) in [(a, b), (b, a)] {
                if let Some(sol) = isolate_from_eq_keeping(cx, lhs, rhs, forbid)? {
                    return Ok(Some(sol));
                }
            }
        }
        _ => {}
    }
    Ok(None)
}

#[allow(clippy::type_complexity)]
fn isolate_from_eq_keeping(
    cx: &mut Context,
    mut lhs: Expr,
    mut rhs: Expr,
    forbid: &HashSet<SymbolId>,
) -> Result<Option<(Expr, SymbolId, Expr, Vec<SymbolId>)>, Error> {
    use crate::View;
    let free = |cx: &Context, e: Expr| -> Result<Option<SymbolId>, Error> {
        Ok(match cx.view(e)? {
            View::Sym(id) if !forbid.contains(&id) => Some(id),
            _ => None,
        })
    };
    let only_forbidden = |cx: &mut Context, e: Expr| -> Result<bool, Error> {
        Ok(cx.symbols_in(&[e])?.iter().all(|s| forbid.contains(s)))
    };
    for _depth in 0..24 {
        if let Some(id) = free(cx, lhs)? {
            let reads = cx.symbols_in(&[rhs])?;
            if !reads.contains(&id) {
                return Ok(Some((lhs, id, rhs, reads)));
            }
            return Ok(None);
        }
        if only_forbidden(cx, lhs)? {
            return Ok(None);
        }
        if let Some((u, is_left, step)) = peel_xorshift(cx, lhs)? {
            rhs = invert_xorshift_expr(cx, rhs, is_left, step)?;
            lhs = u;
            continue;
        }
        match cx.view(lhs)? {
            View::Un(op @ (UnOp::Not | UnOp::Neg | UnOp::Bswap | UnOp::BitRev), u) => {
                rhs = cx.un(op, rhs)?;
                lhs = u;
            }
            View::Bin(BinOp::Add, a, b) => {
                let prefer_b = free(cx, b)?.is_some() || only_forbidden(cx, a)?;
                let (u, other) = if prefer_b { (b, a) } else { (a, b) };
                rhs = cx.bin(BinOp::Sub, rhs, other)?;
                lhs = u;
            }
            View::Bin(BinOp::Sub, a, b) => {
                let prefer_b = free(cx, b)?.is_some() || only_forbidden(cx, a)?;
                if prefer_b {
                    rhs = cx.bin(BinOp::Sub, a, rhs)?;
                    lhs = b;
                } else {
                    rhs = cx.bin(BinOp::Add, rhs, b)?;
                    lhs = a;
                }
            }
            View::Bin(BinOp::Xor, a, b) => {
                let prefer_b = free(cx, b)?.is_some() || only_forbidden(cx, a)?;
                let (u, other) = if prefer_b { (b, a) } else { (a, b) };
                rhs = cx.bin(BinOp::Xor, rhs, other)?;
                lhs = u;
            }
            View::Bin(BinOp::Mul, a, b) => {
                let (u, c) = match (cx.as_const(a)?, cx.as_const(b)?) {
                    (None, Some(c)) => (a, c),
                    (Some(c), None) => (b, c),
                    _ => return Ok(None),
                };
                let Some(inv) = odd_inverse(&c) else {
                    return Ok(None);
                };
                let inv_e = cx.constant(&inv)?;
                rhs = cx.bin(BinOp::Mul, rhs, inv_e)?;
                lhs = u;
            }
            View::Bin(BinOp::RotL, u, cnt) if only_forbidden(cx, cnt)? => {
                rhs = cx.bin(BinOp::RotR, rhs, cnt)?;
                lhs = u;
            }
            View::Bin(BinOp::RotR, u, cnt) if only_forbidden(cx, cnt)? => {
                rhs = cx.bin(BinOp::RotL, rhs, cnt)?;
                lhs = u;
            }
            View::Zext(u) => {
                let w_in = cx.width(u)?;
                rhs = cx.extract(rhs, 0, w_in)?;
                lhs = u;
            }
            View::Sext(u) => {
                let w_in = cx.width(u)?;
                rhs = cx.extract(rhs, 0, w_in)?;
                lhs = u;
            }
            _ => return Ok(None),
        }
    }
    Ok(None)
}

/// Solves `c_0 + sum_{i=1}^m c_i * cast(x_i) == y (mod 2^tw)` across all `samples` via `ctz`-pivot
/// elimination over `Z / 2^tw Z`. Returns `None` if no modular-affine tuple fits all `samples`.
fn fit_modular_affine(tw: Width, samples: &[(Vec<BitVec>, BitVec)]) -> Option<Vec<BitVec>> {
    let first = samples.first()?;
    let m = first.0.len();
    let cols = m + 1;
    let wb = u32::from(tw.bits());

    // Build augmented rows `[1, x_1, ..., x_m, y]`.
    let mut rows: Vec<Vec<BitVec>> = Vec::with_capacity(samples.len());
    for (ins, out) in samples {
        let mut row = Vec::with_capacity(cols + 1);
        row.push(BitVec::one(tw));
        for v in ins {
            row.push(cast_bv_to(v, tw));
        }
        row.push(*out);
        rows.push(row);
    }

    let mut pivots: Vec<(usize, u32, BitVec)> = Vec::new();
    let mut rank = 0usize;
    for col in 0..cols {
        let mut best: Option<(usize, u32)> = None;
        for (r, row) in rows.iter().enumerate().skip(rank) {
            if !row[col].is_zero() {
                let tz = crate::facts::known::trailing_zeros(&row[col]);
                if best.is_none_or(|(_, btz)| tz < btz) {
                    best = Some((r, tz));
                    if tz == 0 {
                        break;
                    }
                }
            }
        }
        let Some((piv_r, p_tz)) = best else {
            continue;
        };
        rows.swap(rank, piv_r);
        let p_odd = crate::facts::known::bv_lshr(&rows[rank][col], p_tz);
        let p_inv = odd_inverse(&p_odd)?;

        let piv_row = rows[rank].clone();
        for row in rows.iter_mut().skip(rank + 1) {
            if row[col].is_zero() {
                continue;
            }
            let r_tz = crate::facts::known::trailing_zeros(&row[col]);
            if r_tz < p_tz {
                return None;
            }
            let r_shifted = crate::facts::known::bv_lshr(&row[col], p_tz);
            let factor = BitVec::apply_bin(BinOp::Mul, &r_shifted, &p_inv).ok()?;
            for (cell, pv) in row.iter_mut().zip(&piv_row).skip(col) {
                let prod = BitVec::apply_bin(BinOp::Mul, &factor, pv).ok()?;
                *cell = BitVec::apply_bin(BinOp::Sub, cell, &prod).ok()?;
            }
        }
        pivots.push((col, p_tz, p_inv));
        rank += 1;
        if rank == rows.len() {
            break;
        }
    }

    let mut coeffs = vec![BitVec::zero(tw); cols];
    for (r, &(col, p_tz, ref p_inv)) in pivots.iter().enumerate().rev() {
        let mut rhs = rows[r][cols];
        for j in (col + 1)..cols {
            if !rows[r][j].is_zero() && !coeffs[j].is_zero() {
                let prod = BitVec::apply_bin(BinOp::Mul, &rows[r][j], &coeffs[j]).ok()?;
                rhs = BitVec::apply_bin(BinOp::Sub, &rhs, &prod).ok()?;
            }
        }
        if rhs.is_zero() {
            coeffs[col] = BitVec::zero(tw);
        } else {
            let r_tz = crate::facts::known::trailing_zeros(&rhs);
            if r_tz < p_tz || p_tz >= wb {
                return None;
            }
            let r_shifted = crate::facts::known::bv_lshr(&rhs, p_tz);
            coeffs[col] = BitVec::apply_bin(BinOp::Mul, &r_shifted, p_inv).ok()?;
        }
    }

    // Verify `[c_0, ..., c_m]` matches every sample exactly.
    for (ins, out) in samples {
        let mut acc = coeffs[0];
        for (i, v) in ins.iter().enumerate() {
            let xv = cast_bv_to(v, tw);
            let prod = BitVec::apply_bin(BinOp::Mul, &coeffs[i + 1], &xv).ok()?;
            acc = BitVec::apply_bin(BinOp::Add, &acc, &prod).ok()?;
        }
        if acc != *out {
            return None;
        }
    }
    Some(coeffs)
}

fn build_modular_affine_expr(
    cx: &mut Context,
    tw: Width,
    proxies: &[Expr],
    coeffs: &[BitVec],
) -> Result<Expr, Error> {
    let mut acc = cx.constant(&coeffs[0])?;
    let one = BitVec::one(tw);
    let ones = BitVec::ones(tw);
    for (i, &p) in proxies.iter().enumerate() {
        let c = &coeffs[i + 1];
        if c.is_zero() {
            continue;
        }
        let xp = cast_expr_to(cx, p, tw)?;
        if *c == one {
            acc = cx.bin(BinOp::Add, acc, xp)?;
        } else if *c == ones {
            acc = cx.bin(BinOp::Sub, acc, xp)?;
        } else {
            let ce = cx.constant(c)?;
            let term = cx.bin(BinOp::Mul, ce, xp)?;
            acc = cx.bin(BinOp::Add, acc, term)?;
        }
    }
    Ok(acc)
}

/// Solves `y = c_0 ^ XOR_j (col_j * in_bit_j)` over GF(2) for `tw <= 128` and `N <= 128` input
/// bits. Returns `(c_0, cols)` where `cols[j]` is the `u128` output-bit column for input bit `j`.
fn fit_gf2_affine(
    tw: Width,
    widths: &[Width],
    samples: &[(Vec<BitVec>, BitVec)],
) -> Option<(u128, Vec<u128>)> {
    let n_bits: usize = widths.iter().map(|w| usize::from(w.bits())).sum();
    let n_cols = n_bits + 1;
    if n_cols > 192 || samples.is_empty() {
        return None;
    }

    let get_bit = |row: &[u64; 3], c: usize| -> bool { (row[c / 64] >> (c % 64)) & 1 != 0 };
    let set_bit = |row: &mut [u64; 3], c: usize| {
        row[c / 64] |= 1u64 << (c % 64);
    };

    let mut mat: Vec<([u64; 3], u128)> = Vec::with_capacity(samples.len());
    for (ins, out) in samples {
        let mut lhs = [0u64; 3];
        set_bit(&mut lhs, 0);
        let mut col = 1usize;
        for (v, &w) in ins.iter().zip(widths) {
            let u = v.to_u128().unwrap_or(0);
            for b in 0..usize::from(w.bits()) {
                if (u >> b) & 1 != 0 {
                    set_bit(&mut lhs, col);
                }
                col += 1;
            }
        }
        mat.push((lhs, out.to_u128()?));
    }

    let mut piv_cols: Vec<usize> = Vec::new();
    let mut rank = 0usize;
    for col in 0..n_cols {
        let Some(piv) = (rank..mat.len()).find(|&r| get_bit(&mat[r].0, col)) else {
            continue;
        };
        mat.swap(rank, piv);
        let (piv_lhs, piv_rhs) = mat[rank];
        for (r, (lhs, rhs)) in mat.iter_mut().enumerate() {
            if r != rank && get_bit(lhs, col) {
                lhs[0] ^= piv_lhs[0];
                lhs[1] ^= piv_lhs[1];
                lhs[2] ^= piv_lhs[2];
                *rhs ^= piv_rhs;
            }
        }
        piv_cols.push(col);
        rank += 1;
        if rank == mat.len() {
            break;
        }
    }

    // Any remaining row with zero LHS and non-zero RHS proves GF(2) inconsistency.
    for &(lhs, rhs) in mat.iter().skip(rank) {
        if lhs == [0, 0, 0] && rhs != 0 {
            return None;
        }
    }

    let mut sol = vec![0u128; n_cols];
    for (r, &col) in piv_cols.iter().enumerate() {
        sol[col] = mat[r].1;
    }
    debug_assert!(tw.bits() <= 128);
    Some((sol[0], sol[1..].to_vec()))
}

/// Emits a compact word-level shift-mask-XOR expression for a GF(2)-affine map `c0 ^ M(proxies)`
/// via diagonal decomposition of each input's binary matrix block.
fn build_gf2_affine_expr(
    cx: &mut Context,
    tw: Width,
    proxies: &[Expr],
    widths: &[Width],
    c0: &u128,
    cols: &[u128],
) -> Result<Expr, Error> {
    let out_bits = usize::from(tw.bits());
    let full_mask: u128 = if out_bits == 128 {
        u128::MAX
    } else {
        (1u128 << out_bits) - 1
    };
    let mut acc = cx.constant(&BitVec::wrapping_from_u128(tw, *c0 & full_mask))?;

    let mut offset = 0usize;
    for (&p, &pw) in proxies.iter().zip(widths) {
        let in_bits = usize::from(pw.bits());
        let p_cols = &cols[offset..offset + in_bits];
        offset += in_bits;
        if p_cols.iter().all(|&c| c == 0) {
            continue;
        }

        // Split wide inputs (`in_bits > out_bits`) into `<= out_bits` slices so each slice is at
        // most `tw` wide before `zext` to `tw`.
        let mut slice_lo = 0usize;
        while slice_lo < in_bits {
            let chunk_len = (in_bits - slice_lo).min(out_bits);
            let chunk_cols = &p_cols[slice_lo..slice_lo + chunk_len];
            if chunk_cols.iter().any(|&c| c != 0) {
                let slice_e = if slice_lo == 0 && chunk_len == in_bits {
                    cast_expr_to(cx, p, tw)?
                } else {
                    let cw = Width::new(chunk_len as u16)?;
                    let ex = cx.extract(p, slice_lo as u16, cw)?;
                    cast_expr_to(cx, ex, tw)?
                };
                // Natural non-zero bit mask of `slice_e`: bits `0..chunk_len`.
                let src_mask: u128 = if chunk_len == 128 {
                    u128::MAX
                } else {
                    (1u128 << chunk_len) - 1
                };

                // Main diagonal (`s == 0`): output bit `r` reads chunk bit `r`.
                let mut m0 = 0u128;
                for (c, &col_bits) in chunk_cols.iter().enumerate() {
                    if (col_bits >> c) & 1 != 0 {
                        m0 |= 1u128 << c;
                    }
                }
                if m0 != 0 {
                    let term = if m0 == src_mask {
                        slice_e
                    } else {
                        let me = cx.constant(&BitVec::wrapping_from_u128(tw, m0))?;
                        cx.bin(BinOp::And, slice_e, me)?
                    };
                    acc = cx.bin(BinOp::Xor, acc, term)?;
                }

                // Sub-diagonals (`slice_e << s`, `1 <= s < out_bits`): output bit `r` reads `r - s`.
                for s in 1..out_bits {
                    let mut ms = 0u128;
                    for (c, &col_bits) in chunk_cols.iter().enumerate() {
                        let r = c + s;
                        if r < out_bits && (col_bits >> r) & 1 != 0 {
                            ms |= 1u128 << r;
                        }
                    }
                    if ms != 0 {
                        let sc = cx.constant_u64(tw, s as u64)?;
                        let sh = cx.bin(BinOp::Shl, slice_e, sc)?;
                        let natural = (src_mask << s) & full_mask;
                        let term = if ms == natural {
                            sh
                        } else {
                            let me = cx.constant(&BitVec::wrapping_from_u128(tw, ms))?;
                            cx.bin(BinOp::And, sh, me)?
                        };
                        acc = cx.bin(BinOp::Xor, acc, term)?;
                    }
                }

                // Super-diagonals (`slice_e >>u s`, `1 <= s < chunk_len`): output bit `r` reads `r + s`.
                for s in 1..chunk_len {
                    let mut ms = 0u128;
                    for r in 0..(chunk_len - s) {
                        if (chunk_cols[r + s] >> r) & 1 != 0 {
                            ms |= 1u128 << r;
                        }
                    }
                    if ms != 0 {
                        let sc = cx.constant_u64(tw, s as u64)?;
                        let sh = cx.bin(BinOp::LShr, slice_e, sc)?;
                        let natural = src_mask >> s;
                        let term = if ms == natural {
                            sh
                        } else {
                            let me = cx.constant(&BitVec::wrapping_from_u128(tw, ms))?;
                            cx.bin(BinOp::And, sh, me)?
                        };
                        acc = cx.bin(BinOp::Xor, acc, term)?;
                    }
                }
            }
            slice_lo += chunk_len;
        }
    }
    Ok(acc)
}

fn problem_constants_u64(
    cx: &mut Context,
    assertions: &[Expr],
    assumptions: &[Expr],
    target: Expr,
    tw: Width,
) -> Result<Vec<u64>, Error> {
    let mut roots = Vec::with_capacity(assertions.len() + assumptions.len() + 1);
    roots.extend_from_slice(assertions);
    roots.extend_from_slice(assumptions);
    roots.push(target);
    let mask = if tw.bits() == 64 {
        u64::MAX
    } else {
        (1u64 << tw.bits()) - 1
    };
    let mut out = Vec::new();
    for e in cx.post_order(&roots)? {
        if let Some(bv) = cx.as_const(e)?
            && cx.width(e)? != Width::W1
            && let Some(v) = bv.to_u64()
        {
            let vm = v & mask;
            if vm != 0 && !out.contains(&vm) {
                out.push(vm);
                if out.len() >= 10 {
                    break;
                }
            }
        }
    }
    Ok(out)
}

#[derive(Copy, Clone)]
enum ObsTerm {
    Var(usize),
    Const(u64),
    Un(UnOp, u32),
    Bin(BinOp, u32, u32),
    Cmp(CmpOp, u32, u32),
    Sel(u32, u32, u32),
}

struct ObsLanes {
    w: u32,
    mask: u64,
}

impl ObsLanes {
    fn sx(&self, a: u64) -> i64 {
        let s = 64 - self.w;
        ((a << s) as i64) >> s
    }

    fn un(&self, op: UnOp, a: u64) -> u64 {
        match op {
            UnOp::Not => !a & self.mask,
            UnOp::Neg => a.wrapping_neg() & self.mask,
            UnOp::Popcnt => u64::from(a.count_ones()) & self.mask,
            UnOp::Clz => u64::from(a.leading_zeros() - (64 - self.w)) & self.mask,
            UnOp::Ctz => {
                (if a == 0 {
                    u64::from(self.w)
                } else {
                    u64::from(a.trailing_zeros())
                }) & self.mask
            }
            UnOp::Bswap => a.swap_bytes() >> (64 - self.w),
            UnOp::BitRev => a.reverse_bits() >> (64 - self.w),
        }
    }

    fn cmp(&self, op: CmpOp, a: u64, b: u64) -> u64 {
        u64::from(match op {
            CmpOp::Eq => a == b,
            CmpOp::Ne => a != b,
            CmpOp::Ult => a < b,
            CmpOp::Ule => a <= b,
            CmpOp::Slt => self.sx(a) < self.sx(b),
            CmpOp::Sle => self.sx(a) <= self.sx(b),
        })
    }

    fn bin(&self, op: BinOp, a: u64, b: u64) -> u64 {
        let w = u64::from(self.w);
        let m = self.mask;
        match op {
            BinOp::Add => a.wrapping_add(b) & m,
            BinOp::Sub => a.wrapping_sub(b) & m,
            BinOp::Mul => a.wrapping_mul(b) & m,
            BinOp::And => a & b,
            BinOp::Or => a | b,
            BinOp::Xor => a ^ b,
            BinOp::Shl => {
                if b >= w {
                    0
                } else {
                    (a << b) & m
                }
            }
            BinOp::LShr => {
                if b >= w {
                    0
                } else {
                    a >> b
                }
            }
            BinOp::AShr => {
                let s = self.sx(a);
                (if b >= w { s >> 63 } else { s >> b }) as u64 & m
            }
            BinOp::UDiv => a.checked_div(b).unwrap_or(m),
            BinOp::URem => a.checked_rem(b).unwrap_or(a),
            BinOp::RotL => {
                let r = (b % w) as u32;
                if r == 0 {
                    a
                } else {
                    ((a << r) | (a >> (self.w - r))) & m
                }
            }
            BinOp::RotR => {
                let r = (b % w) as u32;
                let l = (self.w - r) % self.w;
                if l == 0 {
                    a
                } else {
                    ((a << l) | (a >> (self.w - l))) & m
                }
            }
            _ => 0,
        }
    }
}

fn obs_hash(v: &[u64]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &x in v {
        h ^= x;
        h = h.wrapping_mul(0x0000_0100_0000_01b3).rotate_left(17);
    }
    h
}

/// Bottom-up observational enumerator over collected `(inputs, target)` samples (`tw <= 64`).
fn observational_enumerate(
    cx: &mut Context,
    tw: Width,
    proxies: &[Expr],
    widths: &[Width],
    samples: &[(Vec<BitVec>, BitVec)],
    extra_consts: &[u64],
) -> Result<Option<Expr>, Error> {
    let w = u32::from(tw.bits());
    let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
    let lanes = ObsLanes { w, mask };
    let n = samples.len();

    let mut leaf_exprs: Vec<Expr> = Vec::with_capacity(proxies.len() + 1);
    let mut var_rows: Vec<Vec<u64>> = Vec::with_capacity(proxies.len() + 1);
    for (i, (&p, &pw)) in proxies.iter().zip(widths).enumerate() {
        leaf_exprs.push(cast_expr_to(cx, p, tw)?);
        var_rows.push(
            samples
                .iter()
                .map(|(ins, _)| cast_bv_to(&ins[i], tw).to_u64().unwrap_or(0) & mask)
                .collect(),
        );
        if proxies.len() == 1 && pw.bits() > tw.bits() {
            let hi_w = Width::new((pw.bits() - tw.bits()).min(tw.bits()))?;
            let hi_e = cx.extract(p, tw.bits(), hi_w)?;
            leaf_exprs.push(cast_expr_to(cx, hi_e, tw)?);
            var_rows.push(
                samples
                    .iter()
                    .map(|(ins, _)| {
                        ins[i]
                            .extract(tw.bits(), hi_w)
                            .ok()
                            .and_then(|b| cast_bv_to(&b, tw).to_u64())
                            .unwrap_or(0)
                            & mask
                    })
                    .collect(),
            );
        }
    }

    let want: Vec<u64> = samples
        .iter()
        .map(|(_, out)| out.to_u64().unwrap_or(0) & mask)
        .collect();

    let mut consts = vec![
        0u64,
        1 & mask,
        mask,
        u64::from(w - 1) & mask,
        (1u64 << (w - 1)) & mask,
        2 & mask,
    ];
    for &c in extra_consts {
        if !consts.contains(&c) {
            consts.push(c);
        }
    }
    consts.dedup();
    consts.truncate(12);

    let max_size: usize = if leaf_exprs.len() <= 2 { 6 } else { 5 };
    let max_terms: usize = 25_000;

    let mut terms: Vec<ObsTerm> = Vec::new();
    let mut values: Vec<u64> = Vec::new();
    let mut seen: HashMap<u64, Vec<u32>> = HashMap::new();
    let mut by_size: Vec<Vec<u32>> = vec![Vec::new(); max_size + 1];

    fn row_at(vals: &[u64], n: usize, k: u32) -> &[u64] {
        &vals[k as usize * n..(k as usize + 1) * n]
    }
    let add_term = |t: ObsTerm,
                    sz: usize,
                    row: Vec<u64>,
                    terms: &mut Vec<ObsTerm>,
                    values: &mut Vec<u64>,
                    seen: &mut HashMap<u64, Vec<u32>>,
                    by_size: &mut [Vec<u32>]|
     -> Option<u32> {
        let matched = row == want;
        let h = obs_hash(&row);
        if let Some(bucket) = seen.get(&h)
            && bucket
                .iter()
                .any(|&k| row_at(values, n, k) == row.as_slice())
        {
            return None;
        }
        let k = terms.len() as u32;
        terms.push(t);
        values.extend_from_slice(&row);
        seen.entry(h).or_default().push(k);
        by_size[sz].push(k);
        matched.then_some(k)
    };

    for (v, r) in var_rows.into_iter().enumerate() {
        if let Some(hit) = add_term(
            ObsTerm::Var(v),
            1,
            r,
            &mut terms,
            &mut values,
            &mut seen,
            &mut by_size,
        ) {
            return build_obs_term(cx, tw, &leaf_exprs, &terms, hit).map(Some);
        }
    }
    for &c in &consts {
        if let Some(hit) = add_term(
            ObsTerm::Const(c),
            1,
            vec![c; n],
            &mut terms,
            &mut values,
            &mut seen,
            &mut by_size,
        ) {
            return build_obs_term(cx, tw, &leaf_exprs, &terms, hit).map(Some);
        }
    }

    let mut un_ops = vec![
        UnOp::Not,
        UnOp::Neg,
        UnOp::Popcnt,
        UnOp::Clz,
        UnOp::Ctz,
        UnOp::BitRev,
    ];
    if tw.bits().is_multiple_of(8) {
        un_ops.push(UnOp::Bswap);
    }
    let bin_ops = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
        BinOp::UDiv,
        BinOp::URem,
        BinOp::RotL,
        BinOp::RotR,
    ];
    let cmp_ops = [CmpOp::Eq, CmpOp::Ne, CmpOp::Ult, CmpOp::Slt];

    'outer: for sz in 2..=max_size {
        let prev = by_size[sz - 1].clone();
        for &op in &un_ops {
            for &a in &prev {
                let row: Vec<u64> = row_at(&values, n, a)
                    .iter()
                    .map(|&x| lanes.un(op, x))
                    .collect();
                if let Some(hit) = add_term(
                    ObsTerm::Un(op, a),
                    sz,
                    row,
                    &mut terms,
                    &mut values,
                    &mut seen,
                    &mut by_size,
                ) {
                    return build_obs_term(cx, tw, &leaf_exprs, &terms, hit).map(Some);
                }
                if terms.len() >= max_terms {
                    break 'outer;
                }
            }
        }

        for i in 1..sz - 1 {
            let j = sz - 1 - i;
            let left = by_size[i].clone();
            let right = by_size[j].clone();
            for &op in &bin_ops {
                let comm = matches!(
                    op,
                    BinOp::Add | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor
                );
                if comm && i > j {
                    continue;
                }
                for &a in &left {
                    for &b in &right {
                        if comm && i == j && b < a {
                            continue;
                        }
                        let row: Vec<u64> = row_at(&values, n, a)
                            .iter()
                            .zip(row_at(&values, n, b))
                            .map(|(&x, &y)| lanes.bin(op, x, y))
                            .collect();
                        if let Some(hit) = add_term(
                            ObsTerm::Bin(op, a, b),
                            sz,
                            row,
                            &mut terms,
                            &mut values,
                            &mut seen,
                            &mut by_size,
                        ) {
                            return build_obs_term(cx, tw, &leaf_exprs, &terms, hit).map(Some);
                        }
                        if terms.len() >= max_terms {
                            break 'outer;
                        }
                    }
                }
            }
            for &op in &cmp_ops {
                let sym = matches!(op, CmpOp::Eq | CmpOp::Ne);
                if sym && i > j {
                    continue;
                }
                for &a in &left {
                    for &b in &right {
                        if sym && i == j && b < a {
                            continue;
                        }
                        let row: Vec<u64> = row_at(&values, n, a)
                            .iter()
                            .zip(row_at(&values, n, b))
                            .map(|(&x, &y)| lanes.cmp(op, x, y))
                            .collect();
                        if let Some(hit) = add_term(
                            ObsTerm::Cmp(op, a, b),
                            sz,
                            row,
                            &mut terms,
                            &mut values,
                            &mut seen,
                            &mut by_size,
                        ) {
                            return build_obs_term(cx, tw, &leaf_exprs, &terms, hit).map(Some);
                        }
                        if terms.len() >= max_terms {
                            break 'outer;
                        }
                    }
                }
            }
        }

        for ci in 2..sz.saturating_sub(2) {
            let conds: Vec<u32> = by_size[ci]
                .iter()
                .copied()
                .filter(|&c| {
                    let r = row_at(&values, n, c);
                    r.iter().all(|&v| v <= 1) && r.iter().any(|&v| v != r[0])
                })
                .collect();
            if conds.is_empty() {
                continue;
            }
            let rest = sz - 1 - ci;
            for j in 1..rest {
                let left = by_size[j].clone();
                let right = by_size[rest - j].clone();
                for &c in &conds {
                    for &a in &left {
                        for &b in &right {
                            if a == b {
                                continue;
                            }
                            let (rc, ra, rb) = (
                                row_at(&values, n, c),
                                row_at(&values, n, a),
                                row_at(&values, n, b),
                            );
                            let row: Vec<u64> = (0..n)
                                .map(|p| if rc[p] != 0 { ra[p] } else { rb[p] })
                                .collect();
                            if let Some(hit) = add_term(
                                ObsTerm::Sel(c, a, b),
                                sz,
                                row,
                                &mut terms,
                                &mut values,
                                &mut seen,
                                &mut by_size,
                            ) {
                                return build_obs_term(cx, tw, &leaf_exprs, &terms, hit).map(Some);
                            }
                            if terms.len() >= max_terms {
                                break 'outer;
                            }
                        }
                    }
                }
            }
        }
    }

    // Meet-in-the-middle pair join (`t + c`, `t - c`, `c - t`, `t ^ c`) for effective depth 2x.
    let count = terms.len() as u32;
    let mut need = vec![0u64; n];
    for t in 0..count {
        for (op, flip) in [
            (BinOp::Add, false),
            (BinOp::Sub, false),
            (BinOp::Sub, true),
            (BinOp::Xor, false),
        ] {
            let rt = row_at(&values, n, t);
            for (p, slot) in need.iter_mut().enumerate() {
                *slot = match (op, flip) {
                    (BinOp::Add, _) => lanes.bin(BinOp::Sub, want[p], rt[p]),
                    (BinOp::Sub, false) => lanes.bin(BinOp::Sub, rt[p], want[p]),
                    (BinOp::Sub, true) => lanes.bin(BinOp::Add, want[p], rt[p]),
                    _ => want[p] ^ rt[p],
                };
            }
            if let Some(bucket) = seen.get(&obs_hash(&need))
                && let Some(&c) = bucket
                    .iter()
                    .find(|&&k| row_at(&values, n, k) == need.as_slice())
            {
                let (lhs, rhs) = if flip { (c, t) } else { (t, c) };
                let e_lhs = build_obs_term(cx, tw, &leaf_exprs, &terms, lhs)?;
                let e_rhs = build_obs_term(cx, tw, &leaf_exprs, &terms, rhs)?;
                return cx.bin(op, e_lhs, e_rhs).map(Some);
            }
        }
    }

    // Meet-in-the-middle `select(c, a, b)` join over `{0, 1}` conditions and arms of size `<= 4`.
    let arm_cap = 4.min(max_size);
    let mut small_arms: Vec<u32> = Vec::new();
    for slot in by_size.iter().take(arm_cap + 1).skip(1) {
        small_arms.extend_from_slice(slot);
        if small_arms.len() >= 2_048 {
            small_arms.truncate(2_048);
            break;
        }
    }
    let mut small_conds: Vec<u32> = Vec::new();
    for slot in by_size.iter().take(arm_cap + 1).skip(2) {
        for &c in slot {
            let r = row_at(&values, n, c);
            if r.iter().all(|&v| v <= 1) && r.iter().any(|&v| v != r[0]) {
                small_conds.push(c);
            }
        }
    }
    for c in small_conds {
        let rc = row_at(&values, n, c);
        let then_hit = small_arms.iter().copied().find(|&a| {
            let ra = row_at(&values, n, a);
            (0..n).all(|p| rc[p] == 0 || ra[p] == want[p])
        });
        let Some(a) = then_hit else { continue };
        let else_hit = small_arms.iter().copied().find(|&b| {
            let rb = row_at(&values, n, b);
            (0..n).all(|p| rc[p] != 0 || rb[p] == want[p])
        });
        let Some(b) = else_hit else { continue };
        let k = terms.len() as u32;
        terms.push(ObsTerm::Sel(c, a, b));
        return build_obs_term(cx, tw, &leaf_exprs, &terms, k).map(Some);
    }
    Ok(None)
}

fn build_obs_term(
    cx: &mut Context,
    tw: Width,
    leaves: &[Expr],
    terms: &[ObsTerm],
    k: u32,
) -> Result<Expr, Error> {
    Ok(match terms[k as usize] {
        ObsTerm::Var(v) => leaves[v],
        ObsTerm::Const(c) => cx.constant(&BitVec::wrapping_from_u64(tw, c))?,
        ObsTerm::Un(op, a) => {
            let ea = build_obs_term(cx, tw, leaves, terms, a)?;
            cx.un(op, ea)?
        }
        ObsTerm::Bin(op, a, b) => {
            let ea = build_obs_term(cx, tw, leaves, terms, a)?;
            let eb = build_obs_term(cx, tw, leaves, terms, b)?;
            cx.bin(op, ea, eb)?
        }
        ObsTerm::Cmp(op, a, b) => {
            let ea = build_obs_term(cx, tw, leaves, terms, a)?;
            let eb = build_obs_term(cx, tw, leaves, terms, b)?;
            let c = cx.cmp(op, ea, eb)?;
            cx.zext(c, tw)?
        }
        ObsTerm::Sel(c, a, b) => {
            let cond = match terms[c as usize] {
                ObsTerm::Cmp(op, x, y) => {
                    let ex = build_obs_term(cx, tw, leaves, terms, x)?;
                    let ey = build_obs_term(cx, tw, leaves, terms, y)?;
                    cx.cmp(op, ex, ey)?
                }
                _ => {
                    let ec = build_obs_term(cx, tw, leaves, terms, c)?;
                    let zero = cx.zero(tw)?;
                    cx.cmp(CmpOp::Ne, ec, zero)?
                }
            };
            let ea = build_obs_term(cx, tw, leaves, terms, a)?;
            let eb = build_obs_term(cx, tw, leaves, terms, b)?;
            cx.select(cond, ea, eb)?
        }
    })
}

fn build_select_lut(
    cx: &mut Context,
    proxies: &[Expr],
    samples: &[(Vec<BitVec>, BitVec)],
) -> Result<Expr, Error> {
    // Pick the most frequent output value as the fallback `els` arm to minimize `select` nodes.
    let mut best_default = &samples[0].1;
    let mut best_count = 0usize;
    for (_, out) in samples {
        let count = samples.iter().filter(|(_, o)| o == out).count();
        if count > best_count {
            best_count = count;
            best_default = out;
        }
    }
    let mut acc = cx.constant(best_default)?;
    for (ins, out) in samples.iter().rev() {
        if out == best_default {
            continue;
        }
        let mut cond = cx.bool(true)?;
        for (&p, v) in proxies.iter().zip(ins) {
            let kv = cx.constant(v)?;
            let eq = cx.cmp(crate::CmpOpExt::Eq, p, kv)?;
            cond = cx.bin(BinOp::And, cond, eq)?;
        }
        let then_e = cx.constant(out)?;
        acc = cx.select(cond, then_e, acc)?;
    }
    Ok(acc)
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

    #[test]
    fn bijective_and_split_register_equation_isolation() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        // Zero SAT conflicts allowed: `solve_equations` + word-level simplifier must eliminate
        // the entire CFF / handler chain before any SAT branching.
        let zero_sat = Config::default()
            .with_probes(0)
            .with_quick(None)
            .with_prove(
                prove::Config::default()
                    .with_max_conflicts(0)
                    .with_samples(0),
            );

        // 1. Unsatisfiable 5-step obfuscated state chain ending in an MBA contradiction.
        let mut s = Solver::new(zero_sat.clone());
        let assertions = [
            cx.parse("s1 ^ 0x5bd1e995 == s0 + 0x100", &o).unwrap(),
            cx.parse("(s2 + 0x1337) * 0x9e3779b97f4a7c15 == rotl(s1, 13)", &o)
                .unwrap(),
            cx.parse("s3 ^ (s3 >>u 29) == bswap(s2)", &o).unwrap(),
            cx.parse("rotl(s4, 19) == s3 - 77", &o).unwrap(),
            cx.parse("(s4 ^ y) + 2 * (s4 & y) != s4 + y", &o).unwrap(),
        ];
        for &a in &assertions {
            s.assert(&cx, a).unwrap();
        }
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);

        // 2. Satisfiable chain reconstructs exact model values for every eliminated state symbol.
        let mut s_sat = Solver::new(
            Config::default()
                .with_probes(0)
                .with_quick(None)
                .with_prove(prove::Config::default().with_max_conflicts(64)),
        );
        let sat_assertions = [
            cx.parse("s0 == 0x123456789abcdef0", &o).unwrap(),
            assertions[0],
            assertions[1],
            assertions[2],
            assertions[3],
        ];
        for &a in &sat_assertions {
            s_sat.assert(&cx, a).unwrap();
        }
        assert_eq!(s_sat.check(&mut cx).unwrap(), Status::Sat);
        assert!(holds(&mut cx, &sat_assertions, s_sat.model().unwrap()).unwrap());

        // 3. Split-register `concat(edx, eax) == prod` and `zext<64>(w0) == val`.
        let edx = cx.symbol("edx", Width::W32).unwrap();
        let eax = cx.symbol("eax", Width::W32).unwrap();
        let w0 = cx.symbol("w0", Width::W32).unwrap();
        let pair = cx.concat(edx, eax).unwrap();
        let full = cx.constant_u64(Width::W64, 0xdead_beef_cafe_babe).unwrap();
        let eq_pair = cx.cmp(crate::CmpOpExt::Eq, pair, full).unwrap();
        let zw0 = cx.zext(w0, Width::W64).unwrap();
        let small_64 = cx.constant_u64(Width::W64, 0x0000_0000_1122_3344).unwrap();
        let eq_zext_ok = cx.cmp(crate::CmpOpExt::Eq, zw0, small_64).unwrap();

        let mut s_split = Solver::new(
            Config::default()
                .with_probes(0)
                .with_quick(None)
                .with_prove(prove::Config::default().with_max_conflicts(16)),
        );
        s_split.assert(&cx, eq_pair).unwrap();
        s_split.assert(&cx, eq_zext_ok).unwrap();
        assert_eq!(s_split.check(&mut cx).unwrap(), Status::Sat);
        assert_eq!(
            s_split.value(&mut cx, edx).unwrap().unwrap().to_u64(),
            Some(0xdead_beef)
        );
        assert_eq!(
            s_split.value(&mut cx, eax).unwrap().unwrap().to_u64(),
            Some(0xcafe_babe)
        );
        assert_eq!(
            s_split.value(&mut cx, w0).unwrap().unwrap().to_u64(),
            Some(0x1122_3344)
        );

        // `zext<64>(w0) == 0x1_0000_0005` has non-zero upper 32 bits -> `Unsat` at 0 conflicts.
        let bad_64 = cx.constant_u64(Width::W64, 0x0000_0001_0000_0005).unwrap();
        let eq_zext_bad = cx.cmp(crate::CmpOpExt::Eq, zw0, bad_64).unwrap();
        let c1 = cx
            .parse("w0 != 0", &ParseOptions::width(Width::W32))
            .unwrap();
        let mut s_bad = Solver::new(zero_sat);
        s_bad.assert(&cx, eq_zext_bad).unwrap();
        s_bad.assert(&cx, c1).unwrap();
        assert_eq!(s_bad.check(&mut cx).unwrap(), Status::Unsat);
    }

    #[test]
    fn enumerate_values_recovers_jump_tables_and_handles_limits() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        // Obfuscated 4-way jump table: `0x401000 + ((idx + 2) * 16)` with `idx = tag & 3`
        // disguised via MBA `(idx ^ 2) + 2 * (idx & 2)`.
        let target = cx
            .parse(
                "let idx = tag & 3; 0x401000 + ((idx ^ 2) + 2 * (idx & 2)) * 16",
                &o,
            )
            .unwrap();
        let expected: Vec<BitVec> = [0x401020u64, 0x401030, 0x401040, 0x401050]
            .into_iter()
            .map(|v| BitVec::wrapping_from_u64(Width::W64, v))
            .collect();

        let mut s = Solver::default();
        assert_eq!(
            s.enumerate_values(&mut cx, target, 8).unwrap(),
            Values::Exact(expected.clone())
        );
        // Exact boundary `limit == 4` still proves exhaustion (`Exact`) on the 5th check.
        assert_eq!(
            s.enumerate_values(&mut cx, target, 4).unwrap(),
            Values::Exact(expected.clone())
        );
        // Below cardinality (`limit == 3`) reports `AtLeast` of 3 distinct values.
        match s.enumerate_values(&mut cx, target, 3).unwrap() {
            Values::AtLeast(vs) => {
                assert_eq!(vs.len(), 3);
                assert!(vs.iter().all(|v| expected.contains(v)));
            }
            other => panic!("expected AtLeast(3), got {other:?}"),
        }

        // Scoped path assumption `(tag & 3) <u 2` narrows to 2 targets and leaves stack clean.
        let guard = cx.parse("(tag & 3) <u 2", &o).unwrap();
        assert_eq!(
            s.enumerate_values_within(&mut cx, target, 8, &[guard], None)
                .unwrap(),
            Values::Exact(expected[..2].to_vec())
        );
        assert!(s.assertions().is_empty() && s.depth() == 0);

        // Infeasible assumption -> `Exact([])`.
        let unsat_guard = cx.parse("(tag & 3) == 7", &o).unwrap();
        assert_eq!(
            s.enumerate_values_within(&mut cx, target, 8, &[unsat_guard], None)
                .unwrap(),
            Values::Exact(Vec::new())
        );
    }

    #[test]
    fn optimize_and_tighten_facts_unit() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W16);
        let x = cx.parse("x", &o).unwrap();
        let c = cx
            .parse("(x >=u 12) & (x <=u 40) & ((x & 3) == 2)", &o)
            .unwrap();
        let mut s = Solver::default();
        s.assert(&cx, c).unwrap();

        assert_eq!(
            s.minimize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::wrapping_from_u64(Width::W16, 14))
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_u64(), Some(14));

        assert_eq!(
            s.maximize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::wrapping_from_u64(Width::W16, 38))
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_u64(), Some(38));

        let f = s.tighten_facts(&mut cx, x).unwrap().unwrap();
        assert_eq!(f.urange().lo().to_u64(), Some(14));
        assert_eq!(f.urange().hi().to_u64(), Some(38));
        assert_eq!(f.known().known_zero().bit(0), Some(true));
        assert_eq!(f.known().known_one().bit(1), Some(true));
    }

    #[test]
    fn functional_dependency_and_synthesis_unit() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let x = cx.parse("x", &o).unwrap();
        let k = cx.parse("k", &o).unwrap();
        let y = cx.parse("y", &o).unwrap();
        let eq1 = cx.parse("t == (x ^ k)", &o).unwrap();
        let eq2 = cx.parse("y + t == (x & k) * 2 + (x ^ k)", &o).unwrap();

        let mut s = Solver::default();
        s.assert(&cx, eq1).unwrap();
        s.assert(&cx, eq2).unwrap();

        assert_eq!(
            s.is_determined_by(&mut cx, y, &[x, k]).unwrap(),
            Truth::True
        );
        assert_eq!(s.is_determined_by(&mut cx, y, &[x]).unwrap(), Truth::False);

        let def = s.functional_def(&mut cx, y, &[x, k]).unwrap().unwrap();
        let allowed: HashSet<SymbolId> = cx.symbols_in(&[x, k]).unwrap().into_iter().collect();
        for sym in cx.symbols_in(&[def]).unwrap() {
            assert!(allowed.contains(&sym));
        }
        let ne = cx.cmp(crate::CmpOpExt::Ne, y, def).unwrap();
        assert_eq!(s.check_assuming(&mut cx, &[ne]).unwrap(), Status::Unsat);
    }
}
