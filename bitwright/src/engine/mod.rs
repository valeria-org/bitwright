//! The simplifier: an [`Engine`] applies linked rule programs to expressions under a
//! [`Strategy`], within caller-owned budgets. See `docs/design.md` §6.
//!
//! ```
//! use bitwright::engine::Engine;
//! use bitwright::{Context, ParseOptions, Width};
//!
//! let engine = Engine::standard();
//! let mut cx = Context::new();
//! let e = cx.parse("(x & y) + (x | y)", &ParseOptions::width(Width::W32))?;
//! let out = engine.simplify(&mut cx, e)?;
//! assert_eq!(cx.display(out.expr).to_string(), "x + y");
//! # Ok::<(), bitwright::Error>(())
//! ```

pub(crate) mod budget;
mod dispatch;
mod pass;
mod stats;
#[cfg(test)]
pub(crate) mod tests;

use std::borrow::Cow;
use std::sync::{Arc, OnceLock};

use core::fmt;

pub use budget::{Admission, Allowance, Budget, Cap, Clock, Deadline, Exhausted};
pub use stats::{
    By, Event, Hooks, MbaStats, Observer, PassCounts, Reject, RuleCensus, RuleCounts, Stats,
};

use budget::{Counter, Meter};
use dispatch::DispatchNet;

use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::facts::{Assumptions, Reliance};
use crate::hash::{IdMap, combine};
use crate::rules::apply::{ApplyEnv, try_apply_with};
use crate::rules::matcher::MATCH_STEPS;
use crate::rules::{Ledger, Rule, RuleProgram};
use crate::{BitVec, Width};

/// One step of a [`Strategy`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Phase {
    /// Directed rules of the named groups (in this order), applied bottom-up to a fixpoint.
    /// Every rule strictly decreases the termination order, so the phase terminates.
    Local {
        /// Group names, e.g. `core.bitwise`.
        groups: Vec<String>,
    },
    /// Nodes whose facts pin one value become that constant (subject to
    /// [`Hooks::fold_known`]).
    FactFold,
    /// Linear sums `c + Σ kᵢ·aᵢ` over Z/2^W are collected and re-emitted in canonical form when
    /// that is smaller: cancels additive masking.
    Linear,
    /// Pure bitwise functions of at most three atoms become a minimum-size form of their truth
    /// table when that is smaller.
    Bitwise,
    /// Xor sums `k ⊕ ⊕ᵢ (aᵢ & mᵢ)` over GF(2)^W are collected and re-emitted canonically when
    /// that is smaller: cancels boolean masking.
    Xor,
    /// Boolean combinations of comparisons of one operand pair, or of one operand against
    /// constants, become a single comparison, a range check, or a constant when that is smaller.
    Compares,
    /// Extracts and truncations are pushed through arithmetic, bitwise operations, constant
    /// shifts, extensions and `concat` when the result is smaller.
    Casts,
    /// Operands observed only through some bits (a mask, an extract, a constant shift) are
    /// simplified under those bits when the result is smaller.
    Demanded,
    /// Linear combinations of bitwise functions of at most six atoms (linear MBA) become an
    /// affine form or a small combination of minimum-form bitwise functions when that is
    /// smaller; the form is determined by the values at the 2^t all-zero/all-ones corners.
    LinearMba,
    /// Values assembled from bit slices of other values (masks, shifts, rotations, extensions,
    /// extracts, `concat`, `bswap`, and disjoint `| ^ +`) become the source, a rotation, a byte
    /// swap, or a `concat` of slices when that is smaller.
    Shuffle,
    /// Equalities through invertible maps: `f(x) == f(y)` becomes `x == y` and `f(x) == c`
    /// becomes `x == f⁻¹(c)` (or a constant, when `c` has no preimage) for every layer `f`
    /// proved injective with its other operands fixed, and `a | b == 0` is solved leaf by leaf.
    /// Orderings are left alone. Like a rule, it commits whether or not the operands are
    /// shared (see `bitwright::Query::Injective` for what counts as a layer).
    Invert,
    /// The MBA service: mixed Boolean-arithmetic fragments are lowered, simplified by the
    /// engine's MBA solver, checked by the evidence gate, and lifted back (see [`crate::mba`]).
    #[cfg(feature = "mba")]
    Mba(crate::mba::MbaConfig),
}

/// Named, hashable policy: phases run in order within a round, and rounds repeat until nothing
/// changes or `max_rounds` is reached.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Strategy {
    /// A name for diagnostics.
    pub name: Cow<'static, str>,
    /// The phases of a round.
    pub phases: Vec<Phase>,
    /// The most rounds (at least 1).
    pub max_rounds: u8,
}

impl Strategy {
    /// A strategy with the given phases and at most 4 rounds.
    pub fn new(name: impl Into<Cow<'static, str>>, phases: Vec<Phase>) -> Strategy {
        Strategy {
            name: name.into(),
            phases,
            max_rounds: 4,
        }
    }

    /// The built-in strategy: fact folding, the built-in rules, the normal-form passes, and the
    /// rules again, for up to 4 rounds: `[FactFold, Local(core), Linear, Xor, Casts, Invert,
    /// Compares, Bitwise, Demanded, Local(core)]`.
    pub fn standard() -> Strategy {
        let core = || Phase::Local {
            groups: builtin()
                .0
                .groups()
                .iter()
                .map(|g| g.name.clone())
                .collect(),
        };
        Strategy::new(
            "standard",
            vec![
                Phase::FactFold,
                core(),
                Phase::Linear,
                Phase::Xor,
                Phase::Casts,
                Phase::Invert,
                Phase::Compares,
                Phase::Bitwise,
                Phase::Demanded,
                core(),
            ],
        )
    }

    /// The standard strategy plus the deobfuscation passes (linear MBA and bit shuffles):
    /// `[FactFold, Local(core), Linear, Xor, Casts, Invert, Compares, Bitwise, LinearMba,
    /// Shuffle, Demanded, Local(core)]`, up to 4 rounds.
    pub fn deobfuscate() -> Strategy {
        let core = || Phase::Local {
            groups: builtin()
                .0
                .groups()
                .iter()
                .map(|g| g.name.clone())
                .collect(),
        };
        Strategy::new(
            "deobfuscate",
            vec![
                Phase::FactFold,
                core(),
                Phase::Linear,
                Phase::Xor,
                Phase::Casts,
                Phase::Invert,
                Phase::Compares,
                Phase::Bitwise,
                Phase::LinearMba,
                Phase::Shuffle,
                Phase::Demanded,
                core(),
            ],
        )
    }

    /// Adds the MBA service before the strategy's last phase (after the passes, before the
    /// final rules).
    #[cfg(feature = "mba")]
    pub fn with_mba(mut self, config: crate::mba::MbaConfig) -> Strategy {
        let at = self.phases.len().saturating_sub(1);
        self.phases.insert(at, Phase::Mba(config));
        self
    }

    /// Adds rule groups (of programs linked with [`EngineBuilder::program`]) to every rule
    /// phase, after the groups already there. A strategy with no rule phase gets one at the
    /// end.
    pub fn with_rule_groups(mut self, groups: &[&str]) -> Strategy {
        let mut found = false;
        for p in &mut self.phases {
            if let Phase::Local { groups: g } = p {
                found = true;
                g.extend(groups.iter().map(|s| s.to_string()));
            }
        }
        if !found {
            self.phases.push(Phase::Local {
                groups: groups.iter().map(|s| s.to_string()).collect(),
            });
        }
        self
    }

    /// Sets [`max_rounds`](Self::max_rounds).
    pub fn with_max_rounds(mut self, n: u8) -> Strategy {
        self.max_rounds = n.max(1);
        self
    }
}

/// Checks on every application beyond the ones that always run (result width, host veto).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Verify {
    /// Evaluate both sides at this many seeded points for every application (0 = off).
    pub sampled_points: u32,
    /// ... and at this many for rules linked without a proof (0 = off).
    pub unproven_points: u32,
    /// Reject an application whose sides have incompatible facts.
    pub tripwire: bool,
    /// Reject an application that does not decrease the ground termination order.
    pub termination: bool,
}

impl Default for Verify {
    /// Sampled verification (16 points) for unproven rules only.
    fn default() -> Self {
        Verify {
            sampled_points: 0,
            unproven_points: 16,
            tripwire: false,
            termination: false,
        }
    }
}

setters!(Verify {
    with_sampled_points: sampled_points: u32,
    with_unproven_points: unproven_points: u32,
    with_tripwire: tripwire: bool,
    with_termination: termination: bool,
});

impl Verify {
    /// Every check, with 8 points for every application (for tests and debugging).
    pub fn strict() -> Verify {
        Verify {
            sampled_points: 8,
            unproven_points: 16,
            tripwire: true,
            termination: true,
        }
    }
}

/// Why an engine could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum BuildError {
    /// A rule is not vouched for by its program's ledger, and unproven rules are not allowed.
    Unproven {
        /// `group::rule`.
        rule: String,
    },
    /// Two linked programs define the same group.
    DuplicateGroup(String),
    /// The strategy names a group no linked program defines.
    UnknownGroup(String),
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BuildError::Unproven { rule } => write!(
                f,
                "rule `{rule}` is not vouched for by its ledger (allow unproven rules to link it)"
            ),
            BuildError::DuplicateGroup(g) => write!(f, "group `{g}` is defined twice"),
            BuildError::UnknownGroup(g) => write!(f, "the strategy names unknown group `{g}`"),
        }
    }
}

impl std::error::Error for BuildError {}

/// A linked rule.
struct Linked {
    rule: Rule,
    proven: bool,
}

/// A phase as the engine runs it.
enum PhaseImpl {
    Local(DispatchNet),
    Pass(pass::PassKind),
    #[cfg(feature = "mba")]
    Mba(crate::mba::MbaConfig),
}

/// The MBA service's backends.
#[cfg(feature = "mba")]
#[derive(Clone)]
struct MbaService {
    solver: Arc<dyn crate::mba::MbaSolver>,
    prover: Option<Arc<dyn crate::mba::EquivalenceProver>>,
    cache: Arc<dyn crate::mba::MbaCacheStore>,
}

#[cfg(feature = "mba")]
impl Default for MbaService {
    fn default() -> Self {
        MbaService {
            solver: Arc::new(crate::mba::SignatureSolver),
            prover: None,
            cache: Arc::new(crate::mba::NoCache),
        }
    }
}

struct Inner {
    rules: Vec<Linked>,
    strategy: Strategy,
    phases: Vec<PhaseImpl>,
    #[cfg(feature = "mba")]
    mba: MbaService,
    verify: Verify,
    id: u128,
}

/// Linked rule programs, a strategy and verification settings. Cheap to clone; `Send + Sync`.
#[derive(Clone)]
pub struct Engine {
    inner: Arc<Inner>,
}

impl fmt::Debug for Engine {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Engine")
            .field("strategy", &self.inner.strategy.name)
            .field("rules", &self.inner.rules.len())
            .finish_non_exhaustive()
    }
}

/// Builds an [`Engine`].
#[derive(Default)]
pub struct EngineBuilder {
    programs: Vec<(RuleProgram, Option<Ledger>)>,
    strategy: Option<Strategy>,
    verify: Verify,
    allow_unproven: bool,
    #[cfg(feature = "mba")]
    mba: MbaService,
}

impl fmt::Debug for EngineBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EngineBuilder")
            .field("programs", &self.programs.len())
            .finish_non_exhaustive()
    }
}

/// The built-in corpus, compiled once. An immutable cache: it never influences a result.
fn builtin() -> &'static (RuleProgram, Ledger) {
    static BUILTIN: OnceLock<(RuleProgram, Ledger)> = OnceLock::new();
    BUILTIN.get_or_init(|| {
        let program = RuleProgram::compile(crate::rules::corpus::CORE)
            .unwrap_or_else(|e| panic!("the built-in corpus does not compile: {e}"));
        let ledger = Ledger::parse(crate::rules::corpus::CORE_LEDGER)
            .unwrap_or_else(|e| panic!("the built-in ledger does not parse: {e}"));
        (program, ledger)
    })
}

impl EngineBuilder {
    /// Links the built-in corpus.
    pub fn builtin(mut self) -> Self {
        let (p, l) = builtin();
        self.programs.push((p.clone(), Some(l.clone())));
        self
    }

    /// Links a program; each rule must be vouched for by `ledger` (see
    /// [`allow_unproven`](Self::allow_unproven)).
    pub fn program(mut self, program: RuleProgram, ledger: &Ledger) -> Self {
        self.programs.push((program, Some(ledger.clone())));
        self
    }

    /// Links a program without a ledger. Requires [`allow_unproven`](Self::allow_unproven);
    /// its rules get sampled verification ([`Verify::unproven_points`]).
    pub fn unproven_program(mut self, program: RuleProgram) -> Self {
        self.programs.push((program, None));
        self
    }

    /// Whether rules without a proof may be linked (for experiments; counted per rule).
    pub fn allow_unproven(mut self, yes: bool) -> Self {
        self.allow_unproven = yes;
        self
    }

    /// The strategy (default: one `Local` phase over every linked group, in link order).
    pub fn strategy(mut self, s: Strategy) -> Self {
        self.strategy = Some(s);
        self
    }

    /// Verification settings.
    pub fn verify(mut self, v: Verify) -> Self {
        self.verify = v;
        self
    }

    /// The MBA solver (default: [`SignatureSolver`](crate::mba::SignatureSolver)).
    #[cfg(feature = "mba")]
    pub fn mba_solver(mut self, s: Arc<dyn crate::mba::MbaSolver>) -> Self {
        self.mba.solver = s;
        self
    }

    /// An equivalence prover for the MBA gate (default: none).
    #[cfg(feature = "mba")]
    pub fn mba_prover(mut self, p: Arc<dyn crate::mba::EquivalenceProver>) -> Self {
        self.mba.prover = Some(p);
        self
    }

    /// The MBA answer cache (default: [`NoCache`](crate::mba::NoCache)).
    #[cfg(feature = "mba")]
    pub fn mba_cache(mut self, c: Arc<dyn crate::mba::MbaCacheStore>) -> Self {
        self.mba.cache = c;
        self
    }

    /// Links everything.
    pub fn build(self) -> Result<Engine, BuildError> {
        let mut rules: Vec<Linked> = Vec::new();
        let mut groups: Vec<(String, Vec<u32>)> = Vec::new();
        for (program, ledger) in &self.programs {
            let base = rules.len() as u32;
            for rule in program.rules() {
                let proven = ledger
                    .as_ref()
                    .is_some_and(|l| l.vouches_for(&rule.name, rule.id));
                if !proven && !self.allow_unproven {
                    return Err(BuildError::Unproven {
                        rule: rule.name.clone(),
                    });
                }
                rules.push(Linked {
                    rule: rule.clone(),
                    proven,
                });
            }
            for g in program.groups() {
                if groups.iter().any(|(n, _)| *n == g.name) {
                    return Err(BuildError::DuplicateGroup(g.name.clone()));
                }
                groups.push((
                    g.name.clone(),
                    g.rules.iter().map(|&i| base + i as u32).collect(),
                ));
            }
        }
        let strategy = self.strategy.unwrap_or_else(|| {
            Strategy::new(
                "default",
                vec![Phase::Local {
                    groups: groups.iter().map(|(n, _)| n.clone()).collect(),
                }],
            )
        });
        let plain: Vec<Rule> = rules.iter().map(|l| l.rule.clone()).collect();
        let mut phases = Vec::new();
        let mut id = combine(0x656e_6769_6e65, u64::from(strategy.max_rounds));
        for phase in &strategy.phases {
            match phase {
                Phase::Local { groups: names } => {
                    let mut order = Vec::new();
                    for name in names {
                        let Some((_, rs)) = groups.iter().find(|(n, _)| n == name) else {
                            return Err(BuildError::UnknownGroup(name.clone()));
                        };
                        // Only directed rules: an identity that does not decrease the order
                        // belongs to the search service.
                        order.extend(rs.iter().copied().filter(|&r| plain[r as usize].decreasing));
                    }
                    id = combine(id, 1);
                    for &r in &order {
                        let rid = plain[r as usize].id.0;
                        id = combine(combine(id, rid[0]), rid[1]);
                        id = combine(id, u64::from(rules[r as usize].proven));
                    }
                    phases.push(PhaseImpl::Local(DispatchNet::new(&plain, &order)));
                }
                Phase::FactFold => {
                    id = combine(id, 2);
                    phases.push(PhaseImpl::Pass(pass::PassKind::FactFold));
                }
                Phase::Linear => {
                    id = combine(id, 3);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Linear));
                }
                Phase::Bitwise => {
                    id = combine(id, 4);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Bitwise));
                }
                Phase::Xor => {
                    id = combine(id, 5);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Xor));
                }
                Phase::Compares => {
                    id = combine(id, 6);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Compares));
                }
                Phase::Casts => {
                    id = combine(id, 7);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Casts));
                }
                Phase::Demanded => {
                    id = combine(id, 8);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Demanded));
                }
                Phase::LinearMba => {
                    id = combine(id, 9);
                    phases.push(PhaseImpl::Pass(pass::PassKind::LinearMba));
                }
                Phase::Shuffle => {
                    id = combine(id, 10);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Shuffle));
                }
                Phase::Invert => {
                    id = combine(id, 12);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Invert));
                }
                #[cfg(feature = "mba")]
                Phase::Mba(cfg) => {
                    use core::hash::{Hash, Hasher};
                    let mut h = std::collections::hash_map::DefaultHasher::new();
                    cfg.hash(&mut h);
                    id = combine(combine(id, 11), h.finish());
                    let prover = self.mba.prover.as_ref().map_or("", |p| p.id());
                    for b in self
                        .mba
                        .solver
                        .id()
                        .bytes()
                        .chain([0])
                        .chain(prover.bytes())
                    {
                        id = combine(id, u64::from(b));
                    }
                    phases.push(PhaseImpl::Mba(*cfg));
                }
            }
        }
        let v = &self.verify;
        for x in [
            u64::from(v.sampled_points),
            u64::from(v.unproven_points),
            u64::from(v.tripwire),
            u64::from(v.termination),
        ] {
            id = combine(id, x);
        }
        Ok(Engine {
            inner: Arc::new(Inner {
                rules,
                strategy,
                phases,
                #[cfg(feature = "mba")]
                mba: self.mba.clone(),
                verify: self.verify,
                id: (u128::from(id) << 64) | u128::from(combine(id, 0x9e37)),
            }),
        })
    }
}

/// Options of one call.
#[derive(Default)]
#[non_exhaustive]
pub struct Run<'a> {
    /// A caller-owned account shared across calls; charged with everything this call spends.
    pub allowance: Option<&'a mut Allowance>,
    /// Caps on this call (applied inside the allowance).
    pub per_call: Budget,
    /// Per-root caps, checked before any work.
    pub admission: Admission,
    /// Receives per-rule events.
    pub observer: Option<&'a mut dyn Observer>,
    /// Host policy.
    pub hooks: Option<&'a dyn Hooks>,
    /// Facts in guards are read under these assumptions (part of the memo key).
    pub assumptions: Option<&'a Assumptions>,
    /// Stop at a host-supplied time.
    pub deadline: Option<Deadline<'a>>,
}

setters!(Run<'a> {
    with_allowance: allowance ? &'a mut Allowance,
    with_per_call: per_call: Budget,
    with_admission: admission: Admission,
    with_observer: observer ? &'a mut dyn Observer,
    with_hooks: hooks ? &'a dyn Hooks,
    with_assumptions: assumptions ? &'a Assumptions,
    with_deadline: deadline ? Deadline<'a>,
});

impl fmt::Debug for Run<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Run")
            .field("per_call", &self.per_call)
            .field("admission", &self.admission)
            .finish_non_exhaustive()
    }
}

/// How a root's processing ended.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum End {
    /// The strategy ran to its end.
    Completed,
    /// A budget or deadline stopped it; the result is as valid as a completed one (see
    /// [`RootOutcome::relies_on`]) but not final.
    BudgetTerminated(Exhausted),
    /// Not processed.
    Declined(Decline),
}

/// Why a root was not processed.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Decline {
    /// An admission cap.
    AdmissionCap(Cap),
}

/// The result for one root.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct RootOutcome {
    /// The result: equal to the input wherever the constraints in
    /// [`relies_on`](Self::relies_on) hold (everywhere when it is empty).
    pub expr: Expr,
    /// Whether it differs from the input.
    pub changed: bool,
    /// How processing ended.
    pub end: End,
    /// The constraints of the run's [assumptions](Run::assumptions) the result relies on (none
    /// when it holds everywhere).
    pub relies_on: Reliance,
}

/// The result of a call: `roots[i]` answers input `i`.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Outcome {
    /// Per input root.
    pub roots: Vec<RootOutcome>,
    /// Counters.
    pub stats: Stats,
}

/// Completed per-phase results (with the constraints each relied on), kept in the context across
/// calls and dropped whenever anything that can change a result changes (the engine, host hooks,
/// assumptions).
#[derive(Clone, Debug, Default)]
pub(crate) struct Memo {
    epoch: u128,
    assumptions: Option<Assumptions>,
    phases: Vec<IdMap<u32, (u32, Reliance)>>,
}

impl Memo {
    pub(crate) fn clear(&mut self) {
        *self = Memo::default();
    }

    fn prepare(&mut self, epoch: u128, assumptions: Option<&Assumptions>, phases: usize) {
        let same = self.epoch == epoch
            && self.assumptions.as_ref() == assumptions
            && self.phases.len() == phases;
        if !same {
            self.epoch = epoch;
            self.assumptions = assumptions.cloned();
            self.phases = (0..phases).map(|_| IdMap::default()).collect();
        }
    }
}

/// Stops a phase.
enum Stop {
    Exhausted(Exhausted),
    Error(Error),
}

impl From<Exhausted> for Stop {
    fn from(e: Exhausted) -> Self {
        Stop::Exhausted(e)
    }
}

/// Whether a result is final (memoizable), and if it is not because a cap declined some rule,
/// which one (a root with such a result ends `BudgetTerminated`); and the constraints the
/// rewrites that produced it relied on.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct Fin {
    done: bool,
    why: Option<Exhausted>,
    rel: Reliance,
}

impl Fin {
    const FINAL: Fin = Fin {
        done: true,
        why: None,
        rel: Reliance::NONE,
    };

    /// Not final, for a reason that is not a cap (a rule quarantined for this call).
    const PROVISIONAL: Fin = Fin {
        done: false,
        why: None,
        rel: Reliance::NONE,
    };

    fn capped(why: Exhausted) -> Fin {
        Fin {
            done: false,
            why: Some(why),
            rel: Reliance::NONE,
        }
    }

    /// Final, relying on `rel`.
    fn relying(rel: Reliance) -> Fin {
        Fin { rel, ..Fin::FINAL }
    }

    /// The same, relying on nothing (for a node left unchanged: it equals itself everywhere).
    fn unchanged(self) -> Fin {
        Fin {
            rel: Reliance::NONE,
            ..self
        }
    }

    fn and(self, o: Fin) -> Fin {
        Fin {
            done: self.done && o.done,
            why: self.why.or(o.why),
            rel: self.rel | o.rel,
        }
    }
}

enum Frame {
    Visit(u32),
    /// The result of the first node is the result of the second; the flag says what the first
    /// node's own step (its operands and its declined candidates) contributes.
    Finish(u32, u32, Fin),
}

/// The outcome of the checks on one application.
enum Accept {
    Yes,
    Vetoed,
    Rejected(Reject),
}

/// A node's fate at the rule step, with what its declined candidates contribute.
enum Step {
    To(u32, Fin),
    Normal(Fin),
}

/// The state of one call.
struct Runner<'r, 'a> {
    inner: &'r Inner,
    meter: Meter<'a>,
    stats: Stats,
    observer: Option<&'a mut dyn Observer>,
    hooks: Option<&'a dyn Hooks>,
    assumptions: Option<&'a Assumptions>,
    quarantined: Vec<bool>,
    /// Results of this call that are not final (not memoized), per phase.
    partial: Vec<IdMap<u32, (u32, Fin)>>,
    /// Candidate buffer, reused.
    cands: Vec<u32>,
    /// Sampled verification: the values of every node evaluated so far at each point.
    samples: IdMap<u32, Box<[BitVec]>>,
    /// The linear pass's forms, per node.
    linear: IdMap<u32, pass::linear::Form>,
    /// The bitwise pass's truth tables, per node.
    bitwise: IdMap<u32, pass::bitwise::Info>,
    /// The xor pass's forms, per node.
    xor: IdMap<u32, pass::xor::Form>,
    /// The compares pass's descriptions, per node.
    compares: IdMap<u32, pass::compares::Info>,
    /// The shuffle pass's bit provenance, per node.
    shuffle: IdMap<u32, pass::shuffle::Bits>,
    /// Passes quarantined for the call after a postcondition failure.
    quarantined_passes: Vec<pass::PassKind>,
    /// Use counts (parent edges of live nodes) for the passes' commit rule, per phase run,
    /// computed on first need.
    uses: Option<IdMap<u32, u32>>,
    /// Arena nodes whose edges `uses` already counts.
    uses_upto: u32,
    /// The arena length when the current phase run began.
    phase_start: u32,
    /// Nodes replaced (or built and discarded) in the current phase run: not parents.
    dead: IdMap<u32, ()>,
    /// The current version of every distinct root of the call (for use counts).
    live_roots: Vec<u32>,
    /// Which entry of `live_roots` is being processed.
    active: usize,
    /// Nodes whose edges `uses` currently counts.
    counted: IdMap<u32, ()>,
}

impl Runner<'_, '_> {
    fn emit(&mut self, e: Event<'_>) {
        if let Some(o) = self.observer.as_deref_mut() {
            o.event(e);
        }
    }

    /// The result for `n` in `phase`, and whether it is final.
    fn lookup(&self, cx: &Context, phase: usize, n: u32) -> Option<(u32, Fin)> {
        if let Some(&(r, rel)) = cx.memo.phases[phase].get(&n) {
            return Some((r, Fin::relying(rel)));
        }
        self.partial[phase].get(&n).copied()
    }

    fn set(&mut self, cx: &mut Context, phase: usize, n: u32, r: u32, fin: Fin) {
        if fin.done {
            cx.memo.phases[phase].insert(n, (r, fin.rel));
        } else {
            self.partial[phase].insert(n, (r, fin));
        }
    }

    /// Records that node `n` is no longer used in this phase run (it was replaced): its edges
    /// stop counting as uses of its operands.
    fn retire(&mut self, cx: &Context, n: u32) {
        if self.dead.insert(n, ()).is_some() {
            return;
        }
        if self.counted.remove(&n).is_some()
            && let Some(uses) = self.uses.as_mut()
        {
            for c in cx.node(n).children() {
                if let Some(u) = uses.get_mut(&c) {
                    *u = u.saturating_sub(1);
                }
            }
        }
    }

    /// Runs `f` as engine work, charging the nodes it creates.
    fn build<T>(
        &mut self,
        cx: &mut Context,
        f: impl FnOnce(&mut Context) -> Result<T, Error>,
    ) -> Result<T, Stop> {
        // Nodes are refused before they would exceed the budget, so it is never overspent.
        let left = self.meter.left().new_nodes;
        let before = cx.counters().engine_nodes;
        let (r, refused) = cx.as_engine_limited(left, f);
        let made = cx.counters().engine_nodes - before;
        self.meter.spent.new_nodes += made;
        if refused {
            return Err(Stop::Exhausted(Exhausted::NewNodes));
        }
        match r {
            Ok(v) => {
                self.meter.check()?;
                Ok(v)
            }
            Err(Error::ArenaFull { .. }) => Err(Stop::Exhausted(Exhausted::ArenaCapacity)),
            Err(e) => Err(Stop::Error(e)),
        }
    }

    /// Normalizes `root` under a `Local` phase.
    fn local(&mut self, cx: &mut Context, phase: usize, root: u32) -> Result<(u32, Fin), Stop> {
        if !matches!(self.inner.phases[phase], PhaseImpl::Local(_)) {
            // A pass's decisions depend on sharing, which the previous phase or round may have
            // changed: start afresh (final results stay memoized).
            self.uses = None;
            self.counted.clear();
            self.dead.clear();
            self.partial[phase].clear();
            self.phase_start = cx.len() as u32;
            if let Some(slot) = self.live_roots.get_mut(self.active) {
                *slot = root;
            }
        }
        let mut stack = vec![Frame::Visit(root)];
        while let Some(top) = stack.last() {
            match *top {
                Frame::Finish(n, t, own) => {
                    stack.pop();
                    let (r, fin) = self.lookup(cx, phase, t).unwrap_or((t, Fin::PROVISIONAL));
                    if r != n {
                        self.retire(cx, n);
                    }
                    self.set(cx, phase, n, r, own.and(fin));
                }
                Frame::Visit(n) => {
                    if self.lookup(cx, phase, n).is_some() {
                        if cx.memo.phases[phase].contains_key(&n) {
                            self.stats.memo_hits += 1;
                        }
                        stack.pop();
                        continue;
                    }
                    self.meter.visit()?;
                    let node = cx.node(n);
                    // An opaque extension call is an atom, arguments included.
                    if node.op.as_ext().is_some()
                        && cx
                            .registry
                            .as_deref()
                            .and_then(|r| r.op_at(node.aux))
                            .is_some_and(|o| o.traits().opaque)
                    {
                        stack.pop();
                        self.set(cx, phase, n, n, Fin::FINAL);
                        continue;
                    }
                    let mut waiting = false;
                    for c in node.children() {
                        if self.lookup(cx, phase, c).is_none() {
                            stack.push(Frame::Visit(c));
                            waiting = true;
                        }
                    }
                    if waiting {
                        continue;
                    }
                    stack.pop();
                    let mut kids = [0u32; 3];
                    let mut own = Fin::FINAL;
                    let mut changed = false;
                    for (k, c) in node.children().enumerate() {
                        let (r, fin) = self.lookup(cx, phase, c).unwrap_or((c, Fin::PROVISIONAL));
                        kids[k] = r;
                        own = own.and(fin);
                        changed |= r != c;
                    }
                    if changed {
                        let n1 = self.build(cx, |cx| cx.rebuild(n, kids))?;
                        if n1 != n {
                            stack.push(Frame::Finish(n, n1, own));
                            stack.push(Frame::Visit(n1));
                            continue;
                        }
                    }
                    let step = match &self.inner.phases[phase] {
                        PhaseImpl::Local(_) => self.rewrite(cx, phase, n)?,
                        PhaseImpl::Pass(k) => pass::step(self, cx, *k, n)?,
                        #[cfg(feature = "mba")]
                        PhaseImpl::Mba(cfg) => pass::mba_step(self, cx, cfg, n)?,
                    };
                    match step {
                        Step::To(r, fin) => {
                            stack.push(Frame::Finish(n, r, own.and(fin)));
                            stack.push(Frame::Visit(r));
                        }
                        Step::Normal(fin) => self.set(cx, phase, n, n, own.and(fin.unchanged())),
                    }
                }
            }
        }
        Ok(self
            .lookup(cx, phase, root)
            .unwrap_or((root, Fin::PROVISIONAL)))
    }

    /// Tries the phase's candidate rules at `n`, whose operands are normal.
    fn rewrite(&mut self, cx: &mut Context, phase: usize, n: u32) -> Result<Step, Stop> {
        let inner = self.inner;
        let PhaseImpl::Local(net) = &inner.phases[phase] else {
            return Ok(Step::Normal(Fin::FINAL));
        };
        let mut cands = core::mem::take(&mut self.cands);
        cands.clear();
        cands.extend(net.candidates(cx, n));
        let r = self.try_candidates(cx, n, &cands);
        self.cands = cands;
        r
    }

    fn try_candidates(&mut self, cx: &mut Context, n: u32, cands: &[u32]) -> Result<Step, Stop> {
        let inner = self.inner;
        let mut fin = Fin::FINAL;
        for &ri in cands {
            let linked = &inner.rules[ri as usize];
            let rule = &linked.rule;
            if self.quarantined[ri as usize] {
                // Skipped only for this call: the result is not final.
                fin = fin.and(Fin::PROVISIONAL);
                continue;
            }
            self.meter.charge(Counter::Candidates, 1)?;
            self.emit(Event::Candidate {
                rule,
                node: cx.handle(n),
            });
            let left = self.meter.left();
            let steps = u32::try_from(left.match_steps)
                .unwrap_or(u32::MAX)
                .min(MATCH_STEPS);
            let fact_cap = u32::try_from(left.fact_work).unwrap_or(u32::MAX);
            let mut env = ApplyEnv {
                assumptions: self.assumptions,
                fact_cap: Some(fact_cap),
                steps,
                ..ApplyEnv::default()
            };
            let (work0, capped0) = (cx.facts.work, cx.facts.capped);
            let r = self.build(cx, |cx| Ok(try_apply_with(&mut env, cx, rule, n)))?;
            self.meter.spent.match_steps += u64::from(steps - env.steps);
            self.meter.spent.fact_work += cx.facts.work - work0;
            // A cap that was the call's budget stops the call; the context's own per-query
            // cap or the matcher's per-application cap only makes this node not final.
            let fact_capped = cx.facts.capped != capped0 || env.out_of_facts;
            if fact_capped && fact_cap < cx.config().fact_work {
                return Err(Stop::Exhausted(Exhausted::FactWork));
            }
            let out_of_steps = env.degraded && env.steps == 0 && !fact_capped;
            if out_of_steps && steps < MATCH_STEPS {
                return Err(Stop::Exhausted(Exhausted::MatchSteps));
            }
            self.meter.check()?;
            let Some(r) = r else {
                if env.instantiating && cx.len() as u64 >= u64::from(cx.config().max_nodes) {
                    return Err(Stop::Exhausted(Exhausted::ArenaCapacity));
                }
                if env.degraded {
                    let why = if fact_capped {
                        Exhausted::FactWork
                    } else {
                        Exhausted::MatchSteps
                    };
                    fin = fin.and(Fin::capped(why));
                    self.stats.degraded += 1;
                    self.emit(Event::Degraded { rule });
                } else if env.matched {
                    self.stats.guard_false += 1;
                    self.emit(Event::GuardFalse { rule });
                } else {
                    self.stats.no_match += 1;
                    self.emit(Event::NoMatch { rule });
                }
                continue;
            };
            if r == n {
                self.stats.no_change += 1;
                self.emit(Event::NoChange { rule });
                continue;
            }
            match self.accept(cx, By::Rule(rule), linked.proven, n, r, env.rel)? {
                Accept::Yes => return Ok(Step::To(r, fin.and(Fin::relying(env.rel)))),
                Accept::Vetoed => continue,
                Accept::Rejected(reason) => {
                    if matches!(reason, Reject::Width | Reject::Verify | Reject::Tripwire) {
                        self.quarantined[ri as usize] = true;
                        self.stats.quarantined += 1;
                    }
                    continue;
                }
            }
        }
        Ok(Step::Normal(fin))
    }

    /// Runs the postconditions and the host veto on rewriting `n` to `r`, and records the
    /// outcome (events, counters, the rewrite budget).
    fn accept(
        &mut self,
        cx: &mut Context,
        by: By<'_>,
        proven: bool,
        n: u32,
        r: u32,
        rel: Reliance,
    ) -> Result<Accept, Stop> {
        if let Some(reason) = self.postcondition(cx, by, proven, n, r, rel)? {
            self.stats.rejected += 1;
            self.emit(Event::Rejected { by, reason });
            return Ok(Accept::Rejected(reason));
        }
        let (before, after) = (cx.handle(n), cx.handle(r));
        if let Some(h) = self.hooks
            && !h.admit(cx, before, after, by)
        {
            self.stats.hook_vetoes += 1;
            self.emit(Event::Vetoed { by });
            return Ok(Accept::Vetoed);
        }
        self.meter.charge(Counter::Rewrites, 1)?;
        self.emit(Event::Applied { by, before, after });
        Ok(Accept::Yes)
    }

    /// Checks an application; the reason to reject it, if any. Rules are checked against the
    /// ground termination order; passes decrease DAG size instead, which they check themselves.
    /// A rewrite relying on constraints is compared only at the points where they hold.
    fn postcondition(
        &mut self,
        cx: &mut Context,
        by: By<'_>,
        proven: bool,
        n: u32,
        r: u32,
        rel: Reliance,
    ) -> Result<Option<Reject>, Stop> {
        let v = self.inner.verify;
        if cx.wid(r) != cx.wid(n) {
            return Ok(Some(Reject::Width));
        }
        // An undecided comparison (saturated tree sizes) is no evidence against the compiler's
        // static proof, so only a definite "not smaller" rejects.
        if v.termination
            && matches!(by, By::Rule(_))
            && crate::rules::order::ground_greater(cx, n, r) == Some(false)
        {
            return Ok(Some(Reject::Termination));
        }
        let points = if proven {
            v.sampled_points
        } else {
            v.sampled_points.max(v.unproven_points)
        };
        if points > 0 {
            self.sample(cx, n)?;
            self.sample(cx, r)?;
            let k = points as usize;
            let held = self.constraints_hold(cx, rel, k)?;
            let (a, b) = (&self.samples[&n], &self.samples[&r]);
            if (0..k).any(|j| held[j] && a[j] != b[j]) {
                return Ok(Some(Reject::Verify));
            }
        }
        if v.tripwire {
            // Capped by what remains of the fact budget, both queries together.
            let cap = u32::try_from(self.meter.left().fact_work).unwrap_or(u32::MAX);
            let work0 = cx.facts.work;
            let (a, b) = (cx.handle(n), cx.handle(r));
            let fa = cx.try_facts_cap(a, cap).map_err(Stop::Error)?;
            let used = u32::try_from(cx.facts.work - work0).unwrap_or(u32::MAX);
            let fb = cx
                .try_facts_cap(b, cap.saturating_sub(used))
                .map_err(Stop::Error)?;
            self.meter.spent.fact_work += cx.facts.work - work0;
            match (fa, fb) {
                (Some(fa), Some(fb)) => {
                    if fa.meet(&fb).is_none() {
                        return Ok(Some(Reject::Tripwire));
                    }
                }
                // Out of fact budget: the rewrite is not checked, so not made.
                _ if cap < cx.config().fact_work => {
                    return Err(Stop::Exhausted(Exhausted::FactWork));
                }
                // The context's own per-query cap: the facts are unknown, nothing to compare.
                _ => {}
            }
            self.meter.check()?;
        }
        Ok(None)
    }

    /// Whether the constraints in `rel` hold at each of the first `k` verification points.
    fn constraints_hold(
        &mut self,
        cx: &Context,
        rel: Reliance,
        k: usize,
    ) -> Result<Vec<bool>, Stop> {
        let mut held = vec![true; k];
        let Some(a) = self.assumptions else {
            return Ok(held);
        };
        if rel.is_none() {
            return Ok(held);
        }
        for (id, e, f) in a.constraints() {
            if !rel.may_use(id) {
                continue;
            }
            let i = cx.id(e).map_err(Stop::Error)?;
            self.sample(cx, i)?;
            let vals = &self.samples[&i];
            for (j, h) in held.iter_mut().enumerate() {
                *h &= f.contains(&vals[j]);
            }
        }
        Ok(held)
    }

    /// Evaluates `root` and every node below it not yet sampled at every verification point
    /// (each node once per call; charged as node visits).
    fn sample(&mut self, cx: &Context, root: u32) -> Result<(), Stop> {
        let v = self.inner.verify;
        // At least 16: the MBA gate compares lifted results with the original through these.
        let points = v.sampled_points.max(v.unproven_points).max(16) as usize;
        if self.samples.contains_key(&root) {
            return Ok(());
        }
        let mut samples = core::mem::take(&mut self.samples);
        let mut stack: Vec<(u32, bool)> = vec![(root, false)];
        let mut out = Ok(());
        while let Some((i, expanded)) = stack.pop() {
            if samples.contains_key(&i) {
                continue;
            }
            if !expanded {
                stack.push((i, true));
                for c in cx.node(i).children() {
                    if !samples.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
                continue;
            }
            if let Err(e) = self.meter.visit() {
                out = Err(Stop::Exhausted(e));
                break;
            }
            let seed = cx.meta[i as usize].shash;
            let vals: Result<Vec<BitVec>, Error> = (0..points)
                .map(|k| cx.eval_node(i, |j| samples[&j][k], |_, w| Some(point_value(seed, w, k))))
                .collect();
            match vals {
                Ok(v) => {
                    samples.insert(i, v.into_boxed_slice());
                }
                Err(e) => {
                    out = Err(Stop::Error(e));
                    break;
                }
            }
        }
        self.samples = samples;
        out
    }
}

/// The value of a symbol (identified by its structural hash) at verification point `k`: zero,
/// all ones, then seeded random values. Deterministic.
fn point_value(seed: u64, w: Width, k: usize) -> BitVec {
    match k {
        0 => BitVec::zero(w),
        1 => BitVec::ones(w),
        _ => {
            let mut x = seed ^ (k as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let limbs: Vec<u64> = (0..8)
                .map(|_| {
                    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
                    let mut z = x;
                    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                    z ^ (z >> 31)
                })
                .collect();
            BitVec::wrapping_from_limbs(w, &limbs)
        }
    }
}

impl Engine {
    /// The built-in corpus under [`Strategy::standard`], with default verification.
    pub fn standard() -> Engine {
        static STANDARD: OnceLock<Engine> = OnceLock::new();
        STANDARD
            .get_or_init(|| {
                Engine::builder()
                    .builtin()
                    .strategy(Strategy::standard())
                    .build()
                    .unwrap_or_else(|e| panic!("the built-in engine does not link: {e}"))
            })
            .clone()
    }

    /// A builder.
    pub fn builder() -> EngineBuilder {
        EngineBuilder::default()
    }

    /// The strategy.
    pub fn strategy(&self) -> &Strategy {
        &self.inner.strategy
    }

    /// Simplifies one expression with default options.
    pub fn simplify(&self, cx: &mut Context, e: Expr) -> Result<RootOutcome, Error> {
        Ok(self.run(cx, &[e], Run::default())?.roots[0])
    }

    /// Simplifies `roots` under `run`. Each distinct root is processed once; `roots[i]` of the
    /// outcome answers `roots[i]` of the input.
    pub fn run(&self, cx: &mut Context, roots: &[Expr], run: Run<'_>) -> Result<Outcome, Error> {
        let ids = cx.ids(roots)?;
        let inner = &*self.inner;
        let Run {
            allowance,
            per_call,
            admission,
            observer,
            hooks,
            assumptions,
            deadline,
        } = run;
        if let Some(a) = assumptions {
            a.check_context(cx)?;
        }
        // Contradictory constraints prove anything, so the engine simplifies as without them
        // (they would justify any rewrite; none is made from them).
        let assumptions = assumptions.filter(|a| !a.is_infeasible());
        // Hooks enter the epoch by presence and revision: a host veto must never be bypassed
        // by a memo filled without it, nor leak into runs without it.
        let epoch =
            inner.id ^ u128::from(hooks.map_or(0, |h| combine(0x686f_6f6b_7321, h.revision())));
        cx.memo.prepare(epoch, assumptions, inner.phases.len());
        let limit = match &allowance {
            Some(a) => per_call.min(&a.remaining()),
            None => per_call,
        };
        let mut runner = Runner {
            inner,
            meter: Meter::new(limit, deadline),
            stats: Stats::default(),
            observer,
            hooks,
            assumptions,
            quarantined: vec![false; inner.rules.len()],
            partial: (0..inner.phases.len()).map(|_| IdMap::default()).collect(),
            cands: Vec::new(),
            samples: IdMap::default(),
            linear: IdMap::default(),
            bitwise: IdMap::default(),
            xor: IdMap::default(),
            compares: IdMap::default(),
            shuffle: IdMap::default(),
            quarantined_passes: Vec::new(),
            uses: None,
            uses_upto: 0,
            phase_start: 0,
            dead: IdMap::default(),
            live_roots: {
                let mut seen: IdMap<u32, ()> = IdMap::default();
                ids.iter()
                    .copied()
                    .filter(|&i| seen.insert(i, ()).is_none())
                    .collect()
            },
            active: 0,
            counted: IdMap::default(),
        };
        let mut done: IdMap<u32, (u32, End, Reliance)> = IdMap::default();
        let mut failure: Option<Error> = None;
        for &root in &ids {
            if done.contains_key(&root) {
                continue;
            }
            let out = match admit(cx, root, &admission) {
                Some(cap) => {
                    runner.stats.declined += 1;
                    (
                        root,
                        End::Declined(Decline::AdmissionCap(cap)),
                        Reliance::NONE,
                    )
                }
                None => {
                    let (r, end, rel) = match runner.strategy(cx, root) {
                        Ok((r, fin)) => match fin.why {
                            Some(why) if !fin.done => (r, End::BudgetTerminated(why), fin.rel),
                            _ => (r, End::Completed, fin.rel),
                        },
                        Err((r, fin, Stop::Exhausted(e))) => (r, End::BudgetTerminated(e), fin.rel),
                        Err((_, _, Stop::Error(e))) => {
                            failure = Some(e);
                            break;
                        }
                    };
                    let slot = match end {
                        End::Completed => &mut runner.stats.completed,
                        _ => &mut runner.stats.budget_terminated,
                    };
                    slot[usize::from(r != root)] += 1;
                    (r, end, rel)
                }
            };
            if let Some(slot) = runner.live_roots.get_mut(runner.active) {
                *slot = out.0;
            }
            runner.active += 1;
            done.insert(root, out);
        }
        let spent = runner.meter.spent;
        if let Some(a) = allowance {
            a.spend(&spent);
        }
        if let Some(e) = failure {
            return Err(e);
        }
        let mut stats = runner.stats;
        stats.node_visits = spent.node_visits;
        stats.candidates = spent.candidates;
        stats.match_steps = spent.match_steps;
        stats.rewrites = spent.rewrites;
        stats.new_nodes = spent.new_nodes;
        stats.fact_work = spent.fact_work;
        stats.pass_work = spent.pass_work;
        stats.mba.calls = spent.mba_calls;
        Ok(Outcome {
            roots: ids
                .iter()
                .map(|&i| {
                    let (r, end, rel) = done[&i];
                    RootOutcome {
                        expr: cx.handle(r),
                        changed: r != i,
                        end,
                        relies_on: if r == i { Reliance::NONE } else { rel },
                    }
                })
                .collect(),
            stats,
        })
    }
}

/// The admission cap `root` exceeds, if any.
fn admit(cx: &mut Context, root: u32, a: &Admission) -> Option<Cap> {
    let meta = cx.meta[root as usize];
    if meta.height > a.max_root_height {
        return Some(Cap::Height);
    }
    if meta.tree > a.max_root_tree_size {
        return Some(Cap::TreeSize);
    }
    if let Some(cap) = a.max_root_dag_size {
        let e = cx.handle(root);
        match cx.dag_size(&[e], cap) {
            Ok(crate::Bounded::Exact(_)) => {}
            _ => return Some(Cap::DagSize),
        }
    }
    None
}

impl Runner<'_, '_> {
    /// Runs the strategy on one root: the result, or the best value-equivalent result so far
    /// with the reason it stopped.
    fn strategy(&mut self, cx: &mut Context, root: u32) -> Result<(u32, Fin), (u32, Fin, Stop)> {
        let inner = self.inner;
        let mut cur = root;
        let mut fin = Fin::FINAL;
        for round in 0..inner.strategy.max_rounds.max(1) {
            self.stats.rounds = self.stats.rounds.max(u32::from(round) + 1);
            let start = cur;
            for (phase, p) in inner.strategy.phases.iter().enumerate() {
                let _ = p;
                match self.local(cx, phase, cur) {
                    Ok((r, f)) => {
                        cur = r;
                        fin = fin.and(f);
                    }
                    Err(stop) => return Err((cur, fin, stop)),
                }
            }
            if cur == start {
                break;
            }
        }
        Ok((cur, fin))
    }
}
