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
mod explain;
pub(crate) mod host;
pub(crate) mod pass;
mod stats;
#[cfg(test)]
pub(crate) mod tests;
pub(crate) mod trace;

use std::borrow::Cow;
use std::sync::{Arc, OnceLock};

use core::fmt;

pub use budget::{Admission, Allowance, Budget, Cap, Clock, Deadline, Exhausted};
pub use explain::{Explanation, Peel, Source};
pub use host::{Rewrite, Site};
pub use stats::{
    By, CertStats, Detail, Event, Hooks, MbaStats, Observer, PassCounts, Reject, RuleCensus,
    RuleCounts, Stage, Stats,
};
pub use trace::Trace;

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
    /// table when that is smaller; constants (masks) are read per class of bit positions, not
    /// as atoms; and, failing those, a function of up to six atoms (constants among them) that
    /// depends on three or fewer becomes their minimum form.
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
    /// Divisions by a constant that a compiler wrote as a multiplication by a magic number
    /// become `udiv`/`sdiv` again: `umulhi(x, M) >>u s`, its add-and-halve form for a
    /// multiplier of `W + 1` bits, the same in a register twice as wide
    /// (`trunc((zext(x) * M) >>u k)`), and the signed forms with an arithmetic shift and a
    /// sign correction. A sequence is replaced only when an exact check proves it equal to the
    /// quotient for every value the input can take (with the facts' bounds on it), and only
    /// when that is not larger (a bare `umulhi(x, M)` is the size of its `udiv`). In a linear
    /// sum, `c·x − c·d·q` for such a quotient `q = udiv(x, d)` (or `sdiv`) becomes
    /// `c·urem(x, d)` (or `srem`), and `c·x − c·(udiv(x, y)·y)` becomes `c·urem(x, y)`.
    ///
    /// It undoes a compiler's strength reduction, which a compiler wants kept: only
    /// [`Strategy::deobfuscate`] runs it among the built-in strategies.
    Division,
    /// Carry and borrow networks: `& | ^ ~` and left shifts by constants over at most three
    /// atoms (a parallel-prefix adder or subtractor, a ripple chain written out of up to about
    /// 40 bits) become the affine form `c + Σ aᵢ·xᵢ` they compute (`x + y`, `x − y`) when that
    /// is smaller. The form is read off the network's values at 0 and at each atom alone,
    /// checked at a fixed set of points, and committed only when the native prover proves it
    /// equal, within the pass's own caps on the proof and what is left of the pass work; a
    /// network the prover refutes or does not decide within its caps stays as it is (shifts of
    /// one atom alone are `2^k·a` exactly, unproved). Only [`Strategy::deobfuscate`] runs it
    /// among the built-in strategies.
    #[cfg(feature = "prove")]
    Carries,
    /// Limb arithmetic read as arithmetic on the words: digits of wide values computed apart,
    /// with the carries and borrows between them written as comparisons of the digits below
    /// (`(a >>u k) + (b >>u k) + zext(trunc<k>(a + b) <u trunc<k>(a))`), products by constants
    /// and XORs done digit by digit, and constants added limb by limb become slices of the
    /// word-level operation (`(a + b) >>u k`). Every node is read as an integer form over
    /// floors `floor(x / 2^k)` kept in one shape, in which the digits' terms cancel; each step
    /// is an identity of the integers, and nothing is proved or matched. The forms are written
    /// back from the root down, each node for all its users at once and at the bits of it
    /// that are read, wherever the root's DAG gets smaller (see the pass's module). Only
    /// [`Strategy::deobfuscate`] runs it among the built-in strategies.
    Words,
    /// The MBA service: mixed Boolean-arithmetic fragments are lowered, simplified by the
    /// engine's MBA solver, checked by the evidence gate, and lifted back (see [`crate::mba`]).
    #[cfg(feature = "mba")]
    Mba(crate::mba::MbaConfig),
}

impl Phase {
    /// A short name: `local` for rules, else the pass's name as [`By::Pass`] and
    /// [`Stats::passes`] give it (`fact_fold`, `linear`, `linear_mba`, `mba`, …).
    pub fn name(&self) -> &'static str {
        match self {
            Phase::Local { .. } => "local",
            Phase::FactFold => "fact_fold",
            Phase::Linear => "linear",
            Phase::Bitwise => "bitwise",
            Phase::Xor => "xor",
            Phase::Compares => "compares",
            Phase::Casts => "casts",
            Phase::Demanded => "demanded",
            Phase::LinearMba => "linear_mba",
            Phase::Shuffle => "shuffle",
            Phase::Invert => "invert",
            Phase::Division => "division",
            #[cfg(feature = "prove")]
            Phase::Carries => "carries",
            Phase::Words => "words",
            #[cfg(feature = "mba")]
            Phase::Mba(_) => "mba",
        }
    }
}

/// How the normal-form passes weigh sharing when they decide whether a rewrite makes the DAG
/// smaller (see [`Strategy::sharing`]).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Sharing {
    /// Against the DAG of every root of the call: a node another root still uses is not
    /// freed by rewriting its user. Results are the smallest, but a decision depends on which
    /// roots a call has, so one that sharing made is decided again for every root, and not
    /// memoized; a call over every value of a function costs time growing with its size.
    #[default]
    Roots,
    /// As if the region below each node were used by that node alone: decisions depend on the
    /// node only, so every result is final and memoized, and each node is decided once per
    /// context. A rewrite may then keep a subterm alive that another root still uses. For hosts
    /// that simplify every value of a function (a compiler) and keep their own use counts.
    Ignored,
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
    /// The most rounds that change a root (at least 1). A round that changed nothing may be
    /// followed by rounds over the same root in which the MBA phase asks the questions it had
    /// cut short, and one such round may follow the last (see the solver's steps in
    /// `docs/design.md`).
    pub max_rounds: u8,
    /// Whether rules marked `#[float_values]` apply: identities that hold for floats as
    /// values, every NaN one value (`x · 1 = x` for every `x`, where the product of a NaN with
    /// a payload is the canonical NaN). A result then equals its input as a float of each
    /// rewritten operation's format, not necessarily bit for bit: a NaN may change payload or
    /// sign. Off by default; for hosts that observe floats only as values (a compiler's
    /// fast-math, most deobfuscation).
    pub float_values: bool,
    /// How the passes weigh sharing in their commit rule. [`Sharing::Roots`] by default.
    pub sharing: Sharing,
    /// The most nodes the passes' commit rule examines below a node and in a candidate, and
    /// (up to 256) the demanded-bits pass visits for one operand: the per-node work of the
    /// passes. A region cut short counts fewer nodes freed, so fewer rewrites commit; never a
    /// wrong one. 1024 by default.
    pub max_region: u32,
}

impl Strategy {
    /// A strategy with the given phases and at most 4 rounds.
    pub fn new(name: impl Into<Cow<'static, str>>, phases: Vec<Phase>) -> Strategy {
        Strategy {
            name: name.into(),
            phases,
            max_rounds: 4,
            float_values: false,
            sharing: Sharing::Roots,
            max_region: pass::REGION_CAP,
        }
    }

    /// Sets [`float_values`](Self::float_values).
    pub fn with_float_values(mut self, yes: bool) -> Strategy {
        self.float_values = yes;
        self
    }

    /// The built-in strategy: fact folding, the built-in rules, the normal-form passes, and the
    /// rules again, for up to 4 rounds: `[FactFold, Local(core), Linear, Xor, Casts, Invert,
    /// Compares, Bitwise, Demanded, Local(core)]`.
    pub fn standard() -> Strategy {
        let core = || Phase::Local {
            groups: builtin()
                .program
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

    /// The standard strategy plus the deobfuscation passes (divisions by constants, carry
    /// networks with feature `prove`, linear MBA, bit shuffles and limb arithmetic):
    /// `[FactFold, Local(core), Linear, Xor, Casts, Division, Invert, Compares, Bitwise,
    /// Carries, LinearMba, Shuffle, Demanded, Words, Local(core)]`, up to 4 rounds.
    pub fn deobfuscate() -> Strategy {
        let core = || Phase::Local {
            groups: builtin()
                .program
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
                Phase::Division,
                Phase::Invert,
                Phase::Compares,
                Phase::Bitwise,
                #[cfg(feature = "prove")]
                Phase::Carries,
                Phase::LinearMba,
                Phase::Shuffle,
                Phase::Demanded,
                Phase::Words,
                core(),
            ],
        )
    }

    /// For a decompiler or a lifter's everyday output, not obfuscated code: the standard
    /// strategy plus the passes that recover what compilers emit, divisions by constants
    /// (multiply-high sequences), byte swaps, rotations and bit-field moves (shuffles), and
    /// with feature `prove` carry networks and bit counts spelled out (the SWAR population
    /// count), but not the MBA passes: `[FactFold, Local(core), Linear, Xor, Casts, Division,
    /// Invert, Compares, Bitwise, Carries, Shuffle, Demanded, Local(core)]`, up to 4 rounds.
    pub fn decompile() -> Strategy {
        let core = || Phase::Local {
            groups: builtin()
                .program
                .groups()
                .iter()
                .map(|g| g.name.clone())
                .collect(),
        };
        Strategy::new(
            "decompile",
            vec![
                Phase::FactFold,
                core(),
                Phase::Linear,
                Phase::Xor,
                Phase::Casts,
                Phase::Division,
                Phase::Invert,
                Phase::Compares,
                Phase::Bitwise,
                #[cfg(feature = "prove")]
                Phase::Carries,
                Phase::Shuffle,
                Phase::Demanded,
                core(),
            ],
        )
    }

    /// For a compiler, which simplifies every value of every function: the standard phases
    /// without the demanded-bits pass, `[FactFold, Local(core), Linear, Xor, Casts, Invert,
    /// Compares, Bitwise, Local(core)]`, one round, with the passes deciding as if each node
    /// were alone ([`Sharing::Ignored`]) over at most 64 nodes ([`max_region`](Self::max_region)).
    ///
    /// Every result is final and memoized, so a call over every value of a function costs time
    /// in proportion to its size, and a later call over the same values is answered by the
    /// memo. Results can be larger than [`Strategy::standard`]'s where values share subterms.
    pub fn compile() -> Strategy {
        let core = || Phase::Local {
            groups: builtin()
                .program
                .groups()
                .iter()
                .map(|g| g.name.clone())
                .collect(),
        };
        Strategy::new(
            "compile",
            vec![
                Phase::FactFold,
                core(),
                Phase::Linear,
                Phase::Xor,
                Phase::Casts,
                Phase::Invert,
                Phase::Compares,
                Phase::Bitwise,
                core(),
            ],
        )
        .with_max_rounds(1)
        .with_sharing(Sharing::Ignored)
        .with_max_region(64)
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

    /// Sets [`sharing`](Self::sharing).
    pub fn with_sharing(mut self, sharing: Sharing) -> Strategy {
        self.sharing = sharing;
        self
    }

    /// Sets [`max_region`](Self::max_region) (at least 1).
    pub fn with_max_region(mut self, n: u32) -> Strategy {
        self.max_region = n.max(1);
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
    /// A host rewrite linked with [`EngineBuilder::rewrite`] (sampled at every application)
    /// while unproven rules are not allowed.
    UnprovenRewrite {
        /// Its name.
        rewrite: String,
    },
}

impl fmt::Display for BuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BuildError::Unproven { rule } => write!(
                f,
                "rule `{rule}` is not vouched for by its ledger (allow unproven rules to link it)"
            ),
            BuildError::UnprovenRewrite { rewrite } => write!(
                f,
                "host rewrite `{rewrite}` has no proof (allow unproven rules to link it with \
                 sampled verification, or link it as trusted)"
            ),
            BuildError::DuplicateGroup(g) => write!(f, "group `{g}` is defined twice"),
            BuildError::UnknownGroup(g) => write!(f, "the strategy names unknown group `{g}`"),
        }
    }
}

impl std::error::Error for BuildError {}

/// A phase as the engine runs it.
enum PhaseImpl {
    /// The rules' dispatch net and the host rewrites, by index, tried after the rules.
    Local(Arc<DispatchNet>, Arc<[u32]>),
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
            solver: Arc::new(crate::mba::NormalFormSolver::default()),
            prover: None,
            cache: Arc::new(crate::mba::NoCache),
        }
    }
}

struct Inner {
    /// Every linked rule, in link order.
    rules: Arc<[Rule]>,
    /// Every linked host rewrite, in link order.
    host: Arc<[host::Linked]>,
    /// Whether each rule is vouched for by its program's ledger.
    proven: Arc<[bool]>,
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
    /// Each program with the rules its ledger vouches for (`None`: linked without a ledger).
    programs: Vec<(RuleProgram, Option<Arc<[bool]>>)>,
    strategy: Option<Strategy>,
    verify: Verify,
    allow_unproven: bool,
    /// Host rewrites, in link order.
    host: Vec<host::Linked>,
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

/// The built-in corpus, compiled, checked against its ledger and indexed once. An immutable
/// cache: it never influences a result.
struct Builtin {
    program: RuleProgram,
    /// The rules the ledger vouches for.
    proven: Arc<[bool]>,
    /// The rule order and dispatch net of a `Local` phase over every group in source order (the
    /// rule phases of the built-in strategies).
    core: (Vec<u32>, Arc<DispatchNet>),
}

static BUILTIN: OnceLock<Builtin> = OnceLock::new();

fn builtin() -> &'static Builtin {
    BUILTIN.get_or_init(|| {
        let program = RuleProgram::compile_trusted(crate::rules::corpus::CORE)
            .unwrap_or_else(|e| panic!("the built-in corpus does not compile: {e}"));
        let ledger = Ledger::parse(crate::rules::corpus::CORE_LEDGER)
            .unwrap_or_else(|e| panic!("the built-in ledger does not parse: {e}"));
        let proven = vouched(&program, &ledger);
        let rules = program.rules();
        let order: Vec<u32> = program
            .groups()
            .iter()
            .flat_map(|g| g.rules.iter().map(|&r| r as u32))
            .filter(|&r| rules[r as usize].decreasing && !rules[r as usize].float_values)
            .collect();
        let net = Arc::new(DispatchNet::new(rules, &order));
        Builtin {
            program,
            proven,
            core: (order, net),
        }
    })
}

/// The rules of `program` that `ledger` vouches for.
fn vouched(program: &RuleProgram, ledger: &Ledger) -> Arc<[bool]> {
    program
        .rules()
        .iter()
        .map(|r| ledger.vouches_for(&r.name, r.id))
        .collect()
}

impl EngineBuilder {
    /// Links the built-in corpus.
    pub fn builtin(mut self) -> Self {
        let b = builtin();
        self.programs
            .push((b.program.clone(), Some(b.proven.clone())));
        self
    }

    /// Links a program; each rule must be vouched for by `ledger` (see
    /// [`allow_unproven`](Self::allow_unproven)).
    pub fn program(mut self, program: RuleProgram, ledger: &Ledger) -> Self {
        let proven = vouched(&program, ledger);
        self.programs.push((program, Some(proven)));
        self
    }

    /// Links a program without a ledger. Requires [`allow_unproven`](Self::allow_unproven);
    /// its rules get sampled verification ([`Verify::unproven_points`]).
    pub fn unproven_program(mut self, program: RuleProgram) -> Self {
        self.programs.push((program, None));
        self
    }

    /// Links a host rewrite ([`Rewrite`]), run in the rule phases whose strategy names its
    /// group. Requires [`allow_unproven`](Self::allow_unproven): each application is checked
    /// at sampled points ([`Verify::unproven_points`]), and a rewrite found wrong is quarantined
    /// for the rest of the call.
    pub fn rewrite(mut self, r: Arc<dyn Rewrite>) -> Self {
        self.host.push(host::Linked {
            op: r,
            trusted: false,
        });
        self
    }

    /// Links a host rewrite the host vouches for: its applications are not sampled, like a
    /// proven rule's. Vouch only for a rewrite that
    /// [`check::rewrite`](crate::check::rewrite) (or a proof of your own) establishes; a wrong
    /// trusted rewrite makes wrong results.
    pub fn trusted_rewrite(mut self, r: Arc<dyn Rewrite>) -> Self {
        self.host.push(host::Linked {
            op: r,
            trusted: true,
        });
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

    /// The MBA solver (default: [`NormalFormSolver`](crate::mba::NormalFormSolver); the
    /// [`SignatureSolver`](crate::mba::SignatureSolver) answers linear MBA only, faster).
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
        if !self.allow_unproven
            && let Some(h) = self.host.iter().find(|h| !h.trusted)
        {
            return Err(BuildError::UnprovenRewrite {
                rewrite: h.op.name().to_string(),
            });
        }
        let mut groups: Vec<(String, Vec<u32>)> = Vec::new();
        let mut base = 0u32;
        for (program, proven) in &self.programs {
            if !self.allow_unproven {
                let unproven = match proven {
                    Some(p) => p.iter().position(|&x| !x),
                    None => (!program.rules().is_empty()).then_some(0),
                };
                if let Some(i) = unproven {
                    return Err(BuildError::Unproven {
                        rule: program.rules()[i].name.clone(),
                    });
                }
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
            base += program.rules().len() as u32;
        }
        // A single program's rules are shared, not copied.
        let (rules, proven): (Arc<[Rule]>, Arc<[bool]>) = match &self.programs[..] {
            [(p, proven)] => (
                p.shared_rules().clone(),
                proven
                    .clone()
                    .unwrap_or_else(|| vec![false; p.rules().len()].into()),
            ),
            ps => (
                ps.iter()
                    .flat_map(|(p, _)| p.rules().iter().cloned())
                    .collect(),
                ps.iter()
                    .flat_map(|(p, proven)| match proven {
                        Some(v) => v.to_vec(),
                        None => vec![false; p.rules().len()],
                    })
                    .collect(),
            ),
        };
        // Phases over the same rules in the same order share one dispatch net, and so do engines
        // that link only the built-in corpus.
        let mut nets: Vec<(Vec<u32>, Arc<DispatchNet>)> = Vec::new();
        if let Some(b) = BUILTIN.get()
            && Arc::ptr_eq(&rules, b.program.shared_rules())
        {
            nets.push(b.core.clone());
        }
        // The host rewrites' groups, in the order their first rewrite was linked.
        let mut host_groups: Vec<(String, Vec<u32>)> = Vec::new();
        for (k, h) in self.host.iter().enumerate() {
            let g = h.op.group();
            if groups.iter().any(|(n, _)| n == g) {
                return Err(BuildError::DuplicateGroup(g.to_string()));
            }
            match host_groups.iter_mut().find(|(n, _)| n == g) {
                Some((_, list)) => list.push(k as u32),
                None => host_groups.push((g.to_string(), vec![k as u32])),
            }
        }
        let strategy = self.strategy.unwrap_or_else(|| {
            Strategy::new(
                "default",
                vec![Phase::Local {
                    groups: groups
                        .iter()
                        .chain(&host_groups)
                        .map(|(n, _)| n.clone())
                        .collect(),
                }],
            )
        });
        let mut phases = Vec::new();
        let mut id = combine(0x656e_6769_6e65, u64::from(strategy.max_rounds));
        // The commit policy enters only when it is not the default, so engines that keep it
        // keep their ids (and contexts their memos).
        if strategy.sharing != Sharing::Roots || strategy.max_region != pass::REGION_CAP {
            let sharing = match strategy.sharing {
                Sharing::Roots => 0,
                Sharing::Ignored => 1,
            };
            id = combine(
                combine(combine(id, 0x7368_6172), sharing),
                u64::from(strategy.max_region),
            );
        }
        for phase in &strategy.phases {
            match phase {
                Phase::Local { groups: names } => {
                    let mut order = Vec::new();
                    let mut host_order: Vec<u32> = Vec::new();
                    for name in names {
                        if let Some((_, hs)) = host_groups.iter().find(|(n, _)| n == name) {
                            host_order.extend(hs);
                            continue;
                        }
                        let Some((_, rs)) = groups.iter().find(|(n, _)| n == name) else {
                            return Err(BuildError::UnknownGroup(name.clone()));
                        };
                        // Only directed rules: an identity that does not decrease the order
                        // belongs to the search service.
                        // `#[float_values]` rules only when the strategy opts in.
                        order.extend(rs.iter().copied().filter(|&r| {
                            let rule = &rules[r as usize];
                            rule.decreasing && (!rule.float_values || strategy.float_values)
                        }));
                    }
                    id = combine(id, 1);
                    for &r in &order {
                        let rid = rules[r as usize].id.0;
                        id = combine(combine(id, rid[0]), rid[1]);
                        id = combine(id, u64::from(proven[r as usize]));
                    }
                    let net = match nets.iter().find(|(o, _)| *o == order) {
                        Some((_, net)) => net.clone(),
                        None => {
                            let net = Arc::new(DispatchNet::new(&rules, &order));
                            nets.push((order, net.clone()));
                            net
                        }
                    };
                    // Host rewrites by name, revision and trust (never by address).
                    for &h in &host_order {
                        let l = &self.host[h as usize];
                        id = combine(id, 0x686f_7374);
                        for b in l.op.name().bytes() {
                            id = combine(id, u64::from(b));
                        }
                        id = combine(
                            combine(id, u64::from(l.op.revision())),
                            u64::from(l.trusted),
                        );
                    }
                    phases.push(PhaseImpl::Local(net, host_order.into()));
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
                Phase::Division => {
                    id = combine(id, 13);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Division));
                }
                #[cfg(feature = "prove")]
                Phase::Carries => {
                    id = combine(id, 14);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Carries));
                }
                Phase::Words => {
                    id = combine(id, 15);
                    phases.push(PhaseImpl::Pass(pass::PassKind::Words));
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
                host: self.host.into(),
                proven,
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

/// Options of [`Engine::run_each`].
#[derive(Clone, Copy, Default)]
#[non_exhaustive]
pub struct Each<'a> {
    /// Threads to use at most (0: as many as the machine runs at once).
    pub threads: usize,
    /// Caps on each root (as [`Run::per_call`] on a call with that root alone).
    pub per_root: Budget,
    /// Per-root caps, checked before any work.
    pub admission: Admission,
    /// Facts in guards are read under these assumptions.
    pub assumptions: Option<&'a Assumptions>,
    /// Host policy, shared by the threads; it sees each root in the root's own context.
    pub hooks: Option<&'a (dyn Hooks + Sync)>,
}

setters!(Each<'a> {
    with_threads: threads: usize,
    with_per_root: per_root: Budget,
    with_admission: admission: Admission,
    with_assumptions: assumptions ? &'a Assumptions,
    with_hooks: hooks ? &'a (dyn Hooks + Sync),
});

impl fmt::Debug for Each<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Each")
            .field("threads", &self.threads)
            .field("per_root", &self.per_root)
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
    phases: Vec<PhaseMemo>,
}

/// One phase's final results: the result node of every node visited, and the constraints a
/// result relied on, where it relied on any (only under assumptions).
#[derive(Clone, Debug, Default)]
struct PhaseMemo {
    result: NodeTable,
    rel: IdMap<u32, Reliance>,
}

impl PhaseMemo {
    fn get(&self, n: u32) -> Option<(u32, Reliance)> {
        let r = self.result.get(n)?;
        Some((r, self.rel.get(&n).copied().unwrap_or(Reliance::NONE)))
    }

    fn contains(&self, n: u32) -> bool {
        self.result.get(n).is_some()
    }

    fn insert(&mut self, n: u32, r: u32, rel: Reliance) {
        self.result.insert(n, r);
        if rel.is_none() {
            self.rel.remove(&n);
        } else {
            self.rel.insert(n, rel);
        }
    }
}

/// A node index per node index, in pages of consecutive indices allocated on first write:
/// a lookup is two array reads, nodes built together share a page, and nodes never written cost
/// nothing beyond their page's pointer.
#[derive(Clone, Default)]
struct NodeTable {
    /// Page `p` holds the values of nodes `p * PAGE ..`, each plus one (0: none).
    pages: Vec<Option<Box<[u32; PAGE]>>>,
}

const PAGE: usize = 512;

impl NodeTable {
    fn get(&self, n: u32) -> Option<u32> {
        let n = n as usize;
        let page = self.pages.get(n / PAGE)?.as_ref()?;
        page[n % PAGE].checked_sub(1)
    }

    fn insert(&mut self, n: u32, v: u32) {
        let n = n as usize;
        if n / PAGE >= self.pages.len() {
            self.pages.resize_with(n / PAGE + 1, || None);
        }
        let page = self.pages[n / PAGE].get_or_insert_with(|| Box::new([0; PAGE]));
        // Node indices are below `u32::MAX` (the arena holds at most `u32::MAX` nodes).
        page[n % PAGE] = v + 1;
    }
}

impl fmt::Debug for NodeTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pages = self.pages.iter().filter(|p| p.is_some()).count();
        write!(f, "NodeTable({pages} pages)")
    }
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
            self.phases = (0..phases).map(|_| PhaseMemo::default()).collect();
        }
    }
}

/// The most times the demanded-bits pass's step at the root is taken in one phase run (see
/// `Runner::at_root`): each rewrites the root into a smaller one, which is asked again.
#[cfg(feature = "prove")]
const ROOT_STEPS: u32 = 4;

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

/// What a slice pushed into its operand comes to (`casts::narrowed_from`): the node, what the
/// pushes relied on, and the nodes they stopped at. `None` when the pushes were capped.
type Narrowing = Option<(u32, Fin, Vec<u32>)>;

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
    assumptions: Option<&'r Assumptions>,
    /// Rules quarantined for the call, by index (sized on the first quarantine).
    quarantined: Vec<bool>,
    /// Host rewrites quarantined for the call, likewise.
    host_quarantined: Vec<bool>,
    /// Results of this call that are not final (not memoized), per phase.
    partial: Vec<IdMap<u32, (u32, Fin)>>,
    /// Candidate buffer, reused.
    cands: Vec<u32>,
    /// The walk's stack, reused across phases.
    stack: Vec<Frame>,
    /// Sampled verification: the values of every node evaluated so far at each point.
    samples: IdMap<u32, Box<[BitVec]>>,
    /// The linear pass's forms, per node.
    linear: pass::forms::FormCache<pass::linear::Form>,
    /// The linear pass's sums over its cap on terms, whole (see `pass::forms::Whole`).
    linear_whole: pass::forms::Whole<pass::linear::Form>,
    /// The bitwise pass's truth tables, per node.
    bitwise: IdMap<u32, pass::bitwise::Info>,
    /// The bitwise pass's tables over up to six atoms, per node (read where three hide some).
    bitwise_wide: IdMap<u32, pass::bitwise::Wide>,
    /// Nodes whose bitwise region is beyond the bitwise pass's reading with constants (see
    /// `pass::bitwise`): so is every region above them.
    bitwise_beyond: IdMap<u32, ()>,
    /// The xor pass's forms, per node.
    xor: pass::forms::FormCache<pass::xor::Form>,
    /// The xor pass's xors over its cap on terms, whole.
    xor_whole: pass::forms::Whole<pass::xor::Form>,
    /// The compares pass's descriptions, per node.
    compares: IdMap<u32, pass::compares::Info>,
    /// The shuffle pass's bit provenance, per node.
    shuffle: IdMap<u32, pass::shuffle::Bits>,
    /// The single atom the linear map below each node reads, if one (see `pass::gf2`).
    gf2_atoms: Vec<u32>,
    gf2_stack: Vec<(u32, bool)>,
    /// Residue tables, per node and number of low bits (see `pass::residue`).
    residues: IdMap<(u32, u32), Option<std::rc::Rc<pass::residue::Residues>>>,
    /// The chains of `·`, `&` or `|` found in order, or of more operands than are put in
    /// order (see `pass::sort_chain`).
    chains: IdMap<u32, pass::Chain>,
    /// Passes quarantined for the call after a postcondition failure.
    quarantined_passes: Vec<pass::PassKind>,
    /// The passes' commit rule's scratch.
    scratch: pass::Scratch,
    /// The linear-MBA pass's scratch.
    linear_mba: pass::linear_mba::Scratch,
    /// The carries pass's scratch.
    #[cfg(feature = "prove")]
    carries: pass::carries::Scratch,
    /// The demanded-bits pass's memo, empty between calls.
    demanded: pass::demanded::Memo,
    /// The operands the demanded-bits pass found nothing to simplify under a mask, for the
    /// phase run (a node's value is fixed, so neither is the answer; see `demanded::step`).
    demanded_same: pass::demanded::Same,
    /// What the opaque-constant sweep's reductions of its candidates found, per node and
    /// demanded mask, for the call (see `pass::demanded::reduced`).
    #[cfg(feature = "mba")]
    reduced: [pass::demanded::Memo; 2],
    /// The constants those reductions added to each operand (see `pass::demanded::same_on`).
    sum_constants: IdMap<(u32, u8), Vec<u32>>,
    /// The words pass's forms and marks.
    words: pass::words::State,
    /// The MBA solver's answers in this call, by question.
    #[cfg(feature = "mba")]
    mba_answers: IdMap<crate::mba::CacheKey, crate::mba::MbaAnswer>,
    /// Questions whose answers the evidence gate could not prove in this call (see `pass::mba::ask`).
    #[cfg(feature = "mba")]
    mba_unproved: IdMap<crate::mba::CacheKey, ()>,
    /// Questions the solver ran out of steps on in this call, each with the steps it had (see
    /// `pass::mba::ask`).
    #[cfg(feature = "mba")]
    mba_exhausted: IdMap<crate::mba::CacheKey, u64>,
    /// The pass work the evidence gate's certificates that proved nothing have taken in this
    /// call (see `pass::mba::exact`).
    #[cfg(feature = "mba")]
    mba_missed: u64,
    /// The roots of fragments the MBA phase asked about in this call and kept as they are:
    /// declined by the solver for their size, answered with nothing that would make the DAG
    /// smaller, or with an answer the gate could not prove (see `pass::mba::holds_kept`).
    #[cfg(feature = "mba")]
    mba_kept: IdMap<u32, ()>,
    /// How deep the MBA phase's own questions go in this round (see `pass::mba::depth`): the
    /// rounds ask within a few steps each until one changes nothing, and only then deeper.
    #[cfg(feature = "mba")]
    mba_depth: u8,
    /// Whether a question of this round ran out of steps at that depth (or was not asked for
    /// holding one that did), so a deeper round has something to ask.
    #[cfg(feature = "mba")]
    mba_deeper: bool,
    /// The roots of the fragments whose questions ran out of steps at this round's depth:
    /// a fragment holding one is not asked at this depth either (see `pass::mba::ask`).
    #[cfg(feature = "mba")]
    mba_shallow: IdMap<u32, ()>,
    /// The opaque-constant candidates whose readings were asked in this call and decided
    /// nothing: atoms to the readings of every candidate above them (see
    /// `pass::mba::readings_prove`).
    #[cfg(feature = "mba")]
    mba_undecided: IdMap<u32, ()>,
    /// The opaque-constant sweep's result for every node it examined in this call (the node
    /// itself where it found nothing), so a sweep of another root or of one side of a case
    /// reads the nodes it shares with an earlier sweep instead of asking about them again (see
    /// `pass::mba::sweep`).
    #[cfg(feature = "mba")]
    swept: IdMap<u32, u32>,
    /// The pass work the sweep's certificates took once the call's MBA solver steps were
    /// gone (see `pass::mba::readings_prove`).
    #[cfg(feature = "mba")]
    sweep_borrowed: u64,
    /// Inputs at which a candidate of the opaque-constant sweep was found to differ from what
    /// its samples showed (see `pass::mba::Witness`).
    #[cfg(feature = "mba")]
    witnesses: Vec<pass::mba::Witness>,
    /// The blocks the opaque-constant sweep asked the solver about in this call with a node
    /// cut off and got no answer to within its steps: the blocks' roots, by the cut (see
    /// `pass::mba::sweep_cut_at`).
    #[cfg(feature = "mba")]
    cut_declined: IdMap<u32, IdMap<u32, ()>>,
    /// The opaque-constant sweep's enumerations' buffers (see `pass::mba::Exhaust`).
    #[cfg(feature = "mba")]
    exhaust: pass::mba::Exhaust,
    /// Use counts (parent edges of live nodes) for the passes' commit rule, and the nodes whose
    /// edges they count, per phase run, computed on first need (`uses_on`).
    live: pass::Live,
    uses_on: bool,
    /// Arena nodes whose edges `live` already counts.
    uses_upto: u32,
    /// The arena length when the current phase run began.
    phase_start: u32,
    /// Nodes replaced (or built and discarded) in the current phase run: not parents.
    dead: pass::Marks,
    /// The nodes `dead` took in the current phase run, in order.
    dead_log: Vec<u32>,
    /// The current version of every distinct root of the call (for use counts).
    live_roots: Vec<u32>,
    /// Which entry of `live_roots` is being processed.
    active: usize,
    /// The rewrites passes made in this call, from and to: in a pass's phase a node is not
    /// rebuilt, over its operands' results, into one a pass rewrote it from (see `local`).
    rewritten: IdMap<(u32, u32), ()>,
    /// The roots at which the demanded-bits pass's step at the root found nothing in this
    /// call, with what that decision contributes (see `at_root`).
    #[cfg(feature = "prove")]
    rooted: IdMap<u32, Fin>,
    /// Whether the rounds are in their late stage (see `rounds`): a pass asks it before a
    /// reading that may stand in the way of what the rounds read better (the step at the
    /// root, for the readings that leave a sum no fewer terms).
    late: bool,
    /// Whether a pass left a reading to the late stage in the round under way (see `hold`).
    held: bool,
    /// The root, and what was known of it, when the late stage began.
    turned: Option<(u32, Fin)>,
    /// The roots at which the step at the root found nothing and said the readings it
    /// leaves to the late stage would rewrite the root.
    #[cfg(feature = "prove")]
    latent: IdMap<u32, ()>,
    /// Slices pushed into their operands, by node, low bit, length and whether a slice met
    /// whole was pushed too (`casts::narrowed_from`, `casts::spelled`), kept for the call:
    /// the answer is a function of the nodes and their facts, and the readings of limb
    /// arithmetic ask for the same slices in every round.
    narrows: IdMap<(u32, u16, u16, bool), Narrowing>,
    /// Whether the phases of the round under way have left the root as the round found it,
    /// up to the phase being run.
    #[cfg_attr(not(feature = "prove"), allow(dead_code))]
    settled: bool,
    /// In the MBA phase: the user through which the walk first reached each node (see
    /// `pass::mba_step`).
    chain_parent: IdMap<u32, u32>,
    /// In the MBA phase: whether the question at a node is asked (see `pass::mba::asks`).
    asks: IdMap<u32, bool>,
    /// In the MBA phase: the nodes whose question was considered before their operands were
    /// walked, with its finality when it was asked and not taken (see `pass::mba_first`).
    first: IdMap<u32, Option<Fin>>,
    /// What the observer asks for ([`Detail::Events`] without one).
    detail: Detail,
    /// The name of the phase being run (`local`, or the pass's), for the events of the
    /// passes' commit rule.
    phase_name: &'static str,
    /// The reasoning of the pass step under way, for the `Explain` event after its rewrite
    /// (recorded only under [`Detail::Explain`]).
    explain: Option<Explanation>,
}

impl Runner<'_, '_> {
    fn emit(&mut self, e: Event<'_>) {
        if let Some(o) = self.observer.as_deref_mut() {
            o.event(e);
        }
    }

    /// Whether an observer receives events (the structural events are built only then).
    fn observing(&self) -> bool {
        self.observer.is_some()
    }

    /// Reports a stage's rewrite of the root, when it changed it.
    #[cfg_attr(not(feature = "mba"), allow(dead_code))]
    fn emit_stage(&mut self, cx: &Context, stage: Stage, before: u32, after: u32) {
        if before != after && self.observing() {
            self.emit(Event::Stage {
                stage,
                before: cx.handle(before),
                after: cx.handle(after),
            });
        }
    }

    /// Reports a candidate the commit rule dropped (see [`Event::NotSmaller`]).
    pub(crate) fn not_smaller(
        &mut self,
        cx: &Context,
        n: u32,
        candidate: Option<u32>,
        added: u32,
        freed: u32,
        shared: bool,
    ) {
        if self.observing() {
            self.emit(Event::NotSmaller {
                by: By::Pass(self.phase_name),
                node: cx.handle(n),
                candidate: candidate.map(|c| cx.handle(c)),
                added,
                freed,
                shared,
            });
        }
    }

    /// Whether the passes record their reasoning for an `Explain` event.
    pub(crate) fn explaining(&self) -> bool {
        self.detail >= Detail::Explain
    }

    /// Records the reasoning of the step under way (when explaining), for the `Explain` event
    /// that follows its rewrite.
    pub(crate) fn explain_with(&mut self, f: impl FnOnce() -> Explanation) {
        if self.explaining() {
            self.explain = Some(f());
        }
    }

    /// The result for `n` in `phase`, and whether it is final.
    fn lookup(&self, cx: &Context, phase: usize, n: u32) -> Option<(u32, Fin)> {
        if let Some((r, rel)) = cx.memo.phases[phase].get(n) {
            return Some((r, Fin::relying(rel)));
        }
        self.partial[phase].get(&n).copied()
    }

    fn set(&mut self, cx: &mut Context, phase: usize, n: u32, r: u32, fin: Fin) {
        // (In the late stage of the rounds nothing is kept beyond the call: a stage that is
        // given up leaves the memo as it found it.)
        if fin.done && !self.late {
            cx.memo.phases[phase].insert(n, r, fin.rel);
        } else {
            self.partial[phase].insert(n, (r, fin));
        }
    }

    /// For a pass that leaves a reading to the late stage of the rounds (see `rounds`):
    /// notes that there is one, and gives what that contributes to the node's finality. The
    /// node is not final, so its phase asks it again in every round, and so once the stage
    /// has begun (`late` is set then, and the reading is taken): nothing a phase found
    /// final before the stage is asked again. The pass should find out cheaply that it
    /// holds a reading back.
    #[cfg_attr(not(feature = "prove"), allow(dead_code))]
    pub(crate) fn hold(&mut self) -> Fin {
        self.held = true;
        Fin::PROVISIONAL
    }

    /// Whether `phase` is the MBA service.
    fn is_mba(&self, phase: usize) -> bool {
        #[cfg(feature = "mba")]
        {
            matches!(self.inner.phases[phase], PhaseImpl::Mba(_))
        }
        #[cfg(not(feature = "mba"))]
        {
            let _ = phase;
            false
        }
    }

    /// `r` replaces `n`: it is reached through `n`'s user.
    fn inherit_parent(&mut self, n: u32, r: u32) {
        if let Some(&p) = self.chain_parent.get(&n) {
            self.chain_parent.entry(r).or_insert(p);
        }
    }

    /// Records that node `n` is no longer used in this phase run (it was replaced): its edges
    /// stop counting as uses of its operands, and an operand that no counted node uses any
    /// more (and that is no root of the call) goes the same way. A node used again later is
    /// counted again (see `pass::refresh_uses`).
    fn retire(&mut self, cx: &Context, n: u32) {
        let mut stack = vec![n];
        let mut orphans: Vec<u32> = Vec::new();
        while let Some(n) = stack.pop() {
            if !self.dead.insert(n) {
                continue;
            }
            self.dead_log.push(n);
            if !self.live.uncount(n) {
                continue;
            }
            if !self.uses_on {
                continue;
            }
            orphans.clear();
            for c in cx.node(n).children() {
                if self.live.dec(c) == Some(0) {
                    orphans.push(c);
                }
            }
            for &c in &orphans {
                if self.live.counted(c) && !self.live_roots.contains(&c) {
                    stack.push(c);
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
        let left = self.meter.left_in(|b| b.new_nodes);
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

    /// `root` with what an interrupted walk of `phase` did kept: a node the walk finished is
    /// its result, a node it rewrote but did not finish (a `Finish` on the stack) is what the
    /// rewrite has become so far, and the nodes above are rebuilt over them. No rule or pass
    /// runs. The nodes the walk had reached (the ones on its stack) are read for nothing: their
    /// visits are charged already. Each node below them is a node visit, as in the walk, and
    /// one the budget does not cover stays as it was, operands included: so does a node the
    /// budget's new nodes cannot rebuild. `None` when nothing changes.
    fn salvage(&mut self, cx: &mut Context, phase: usize, root: u32) -> Option<(u32, Fin)> {
        self.stats.salvaged += 1;
        let mut rewrote: IdMap<u32, (u32, Fin)> = IdMap::default();
        let mut reached: IdMap<u32, ()> = IdMap::default();
        for f in &self.stack {
            match *f {
                Frame::Visit(n) => {
                    reached.insert(n, ());
                }
                Frame::Finish(n, t, own) => {
                    rewrote.entry(n).or_insert((t, own));
                    reached.insert(t, ());
                }
            }
        }
        // Each node's salvaged value, and the nodes whose value is being worked out (a node
        // met again below itself keeps its own value, which is always sound).
        let mut done: IdMap<u32, (u32, Fin)> = IdMap::default();
        let mut open: IdMap<u32, ()> = IdMap::default();
        let mut work: Vec<(u32, bool)> = vec![(root, false)];
        while let Some((n, expanded)) = work.pop() {
            if done.contains_key(&n) {
                continue;
            }
            if let Some(r) = self.lookup(cx, phase, n) {
                done.insert(n, r);
                continue;
            }
            if let Some(&(t, own)) = rewrote.get(&n) {
                if !expanded && open.insert(n, ()).is_none() {
                    work.push((n, true));
                    if !done.contains_key(&t) && !open.contains_key(&t) {
                        work.push((t, false));
                    }
                    continue;
                }
                open.remove(&n);
                let (r, f) = done.get(&t).copied().unwrap_or((t, Fin::FINAL));
                done.insert(n, (r, own.and(f)));
                continue;
            }
            let node = cx.node(n);
            if !expanded && open.insert(n, ()).is_none() {
                if !reached.contains_key(&n) && self.meter.visit().is_err() {
                    open.remove(&n);
                    done.insert(n, (n, Fin::FINAL));
                    continue;
                }
                work.push((n, true));
                for c in node.children() {
                    if !done.contains_key(&c) && !open.contains_key(&c) {
                        work.push((c, false));
                    }
                }
                continue;
            }
            open.remove(&n);
            let mut kids = [0u32; 3];
            let mut fin = Fin::FINAL;
            let mut changed = false;
            for (k, c) in node.children().enumerate() {
                let (r, f) = done.get(&c).copied().unwrap_or((c, Fin::FINAL));
                kids[k] = r;
                changed |= r != c;
                fin = fin.and(f);
            }
            let value = if changed {
                let left = self.meter.left_in(|b| b.new_nodes);
                let before = cx.counters().engine_nodes;
                let (r, refused) = cx.as_engine_limited(left, |cx| cx.rebuild(n, kids));
                self.meter.spent.new_nodes += cx.counters().engine_nodes - before;
                match r {
                    Ok(n1) if !refused => (n1, fin),
                    _ => (n, Fin::FINAL),
                }
            } else {
                (n, Fin::FINAL)
            };
            done.insert(n, value);
        }
        let (r, f) = done.get(&root).copied()?;
        (r != root).then_some((r, f.and(Fin::PROVISIONAL)))
    }

    /// Normalizes `root` under a `Local` phase.
    fn local(&mut self, cx: &mut Context, phase: usize, root: u32) -> Result<(u32, Fin), Stop> {
        let out = self.walked(cx, phase, root)?;
        // The step at the root, once the phases before this one and its own walk leave the
        // root as the round found it: what the step reads (a limb's carries as the high
        // digit of its word) the passes may still be about to read otherwise, or to show
        // never reaches the root; it is taken where they have nothing left to do.
        #[cfg(feature = "prove")]
        if matches!(
            self.inner.phases[phase],
            PhaseImpl::Pass(pass::PassKind::Demanded)
        ) && self.settled
            && out.0 == root
        {
            return self.at_root(cx, phase, out);
        }
        Ok(out)
    }

    /// The demanded-bits pass's step at the root of its walk (`pass::demanded::whole`), on the
    /// walk's result `out`: what it rewrites the root into is walked as a root in its turn,
    /// and asked again, at most [`ROOT_STEPS`] times.
    ///
    /// What the step does depends on the node being the root (the bits that reach the root
    /// are read below it), so its result is no result of the phase for that node: it is not
    /// memoized, and a root the phase has a final result for is asked all the same. A root
    /// the step found nothing at is remembered for the call (for the stage of the rounds it
    /// was asked in, see `rounds`).
    #[cfg(feature = "prove")]
    fn at_root(
        &mut self,
        cx: &mut Context,
        phase: usize,
        out: (u32, Fin),
    ) -> Result<(u32, Fin), Stop> {
        let (mut cur, mut fin) = out;
        for _ in 0..ROOT_STEPS {
            if let Some(&f) = self.rooted.get(&cur) {
                return Ok((cur, fin.and(f)));
            }
            // (The walk may have been answered by the memo, or have left the root's uses as
            // of another node's: counted afresh.)
            self.begin(cx, phase, cur);
            match pass::demanded::whole(self, cx, cur, self.late)? {
                Step::Normal(f) => {
                    let f = f.unchanged();
                    self.rooted.insert(cur, f);
                    // Whether the readings left to the late stage would rewrite this root:
                    // asked here, in the phase, once for a root (see `rounds`).
                    if !self.late {
                        self.begin(cx, phase, cur);
                        if pass::demanded::late(self, cx, cur)? {
                            self.latent.insert(cur, ());
                        }
                    }
                    return Ok((cur, fin.and(f)));
                }
                Step::To(e, f) => {
                    self.rewritten.insert((cur, e), ());
                    let (r, f2) = self.walked(cx, phase, e)?;
                    fin = fin.and(f).and(f2);
                    cur = r;
                }
            }
        }
        Ok((cur, fin))
    }

    /// Prepares a phase run on `root`.
    fn begin(&mut self, cx: &Context, phase: usize, root: u32) {
        // Use counts are counted afresh in each phase run, on first need (a pass's commit rule,
        // a rule's `one_use`).
        self.uses_on = false;
        self.live.begin();
        self.dead.clear();
        self.dead_log.clear();
        self.phase_start = cx.len() as u32;
        if let Some(slot) = self.live_roots.get_mut(self.active) {
            *slot = root;
        }
        if !matches!(self.inner.phases[phase], PhaseImpl::Local(..)) {
            // A pass's decisions depend on sharing, which the previous phase or round may have
            // changed: start afresh (final results stay memoized).
            self.partial[phase].clear();
            self.chain_parent.clear();
            self.asks.clear();
            self.first.clear();
            self.demanded_same.clear();
            self.words.begin();
        } else {
            // A rule's "no" from sharing (`one_use`) may be a "yes" once a phase since has
            // dropped the other use: those results are decided again. What a cap declined
            // stays declined for the call.
            self.partial[phase].retain(|_, (_, fin)| fin.why.is_some());
        }
    }

    /// [`local`](Self::local)'s walk of `root`, prepared.
    fn walked(&mut self, cx: &mut Context, phase: usize, root: u32) -> Result<(u32, Fin), Stop> {
        // A root with a final result: what the walk would find at its first step, without
        // preparing one (the preparation only matters to a walk that does work).
        if let Some((r, rel)) = cx.memo.phases[phase].get(root) {
            self.stats.memo_hits += 1;
            return Ok((r, Fin::relying(rel)));
        }
        self.begin(cx, phase, root);
        let mut stack = core::mem::take(&mut self.stack);
        stack.clear();
        stack.push(Frame::Visit(root));
        let out = self.walk(cx, phase, root, &mut stack);
        self.stack = stack;
        out
    }

    /// The walk of [`local`](Self::local), from `stack` (holding the root).
    fn walk(
        &mut self,
        cx: &mut Context,
        phase: usize,
        root: u32,
        stack: &mut Vec<Frame>,
    ) -> Result<(u32, Fin), Stop> {
        // Rewrites are accepted where they are made, but results are remembered and reused
        // anywhere: a pass's decision depends on sharing, so an operand's remembered result can
        // rebuild the very node its parent was rewritten from, which the pass rewrites again,
        // and so on. Such cycles are cut in favor of the rewrite, not final: a node is not
        // rebuilt into one a pass rewrote it from in this call (`rewritten`), nor into one whose
        // result waits on it (`pending`: a `Finish` on the stack); a node rewritten into a
        // waiting one takes it. Rules strictly decrease an order, so their phases never cycle
        // and keep no such records.
        let mut pending: IdMap<u32, u32> = IdMap::default();
        let local = matches!(self.inner.phases[phase], PhaseImpl::Local(..));
        while let Some(top) = stack.last() {
            match *top {
                Frame::Finish(n, t, own) => {
                    stack.pop();
                    if let Some(k) = pending.get_mut(&n) {
                        *k -= 1;
                        if *k == 0 {
                            pending.remove(&n);
                        }
                    }
                    let (r, fin) = self.lookup(cx, phase, t).unwrap_or((t, Fin::PROVISIONAL));
                    if r != n {
                        self.retire(cx, n);
                    }
                    self.set(cx, phase, n, r, own.and(fin));
                }
                Frame::Visit(n) => {
                    if self.lookup(cx, phase, n).is_some() {
                        if cx.memo.phases[phase].contains(n) {
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
                    let mba = !local && self.is_mba(phase);
                    // A question asked before the operands are walked, over the node as it is.
                    // In the MBA phase, the one at the top of a fragment (see
                    // `pass::mba_first`); in the demanded-bits phase, the one of a tall node
                    // that observes an operand (see `pass::demanded::first`). A rewrite is
                    // taken as a pass's is below, with nothing to wait on.
                    let mut first: Option<(u32, Fin)> = None;
                    #[cfg(feature = "mba")]
                    if mba && !self.first.contains_key(&n) {
                        self.explain = None;
                        let inner = self.inner;
                        if let PhaseImpl::Mba(cfg) = &inner.phases[phase] {
                            first = pass::mba_first(self, cx, cfg, n)?;
                        }
                    }
                    if matches!(
                        self.inner.phases[phase],
                        PhaseImpl::Pass(pass::PassKind::Demanded)
                    ) && pass::demanded::asks_first(self, cx, n)
                    {
                        self.explain = None;
                        first = pass::demanded::first(self, cx, n)?;
                    }
                    if matches!(
                        self.inner.phases[phase],
                        PhaseImpl::Pass(pass::PassKind::Words)
                    ) && pass::words::asks_first(self, cx, n)
                    {
                        self.explain = None;
                        first = pass::words::first(self, cx, n)?;
                    }
                    if let Some((r, fin)) = first {
                        stack.pop();
                        if pending.contains_key(&r) {
                            self.stats.cycles_cut += 1;
                            self.retire(cx, n);
                            self.set(cx, phase, n, r, fin.and(Fin::PROVISIONAL));
                        } else {
                            self.rewritten.insert((n, r), ());
                            *pending.entry(n).or_default() += 1;
                            self.live.replace(n, r);
                            self.retire(cx, n);
                            self.inherit_parent(n, r);
                            stack.push(Frame::Finish(n, r, fin));
                            stack.push(Frame::Visit(r));
                        }
                        continue;
                    }
                    let mut waiting = false;
                    for c in node.children() {
                        if mba {
                            self.chain_parent.entry(c).or_insert(n);
                        }
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
                        if n1 != n && self.observing() && !same_operator(cx, n, n1, &kids) {
                            self.emit(Event::Folded {
                                node: cx.handle(n),
                                after: cx.handle(n1),
                            });
                        }
                        if n1 != n
                            && (pending.contains_key(&n1)
                                || (!local && self.rewritten.contains_key(&(n1, n))))
                        {
                            self.stats.cycles_cut += 1;
                            self.set(cx, phase, n, n, own.and(Fin::PROVISIONAL));
                            continue;
                        }
                        if n1 != n {
                            if !local {
                                *pending.entry(n).or_default() += 1;
                            }
                            // `n1` replaces `n`: `n` no longer counts as a user, and its
                            // users will use `n1`.
                            self.live.replace(n, n1);
                            self.retire(cx, n);
                            self.inherit_parent(n, n1);
                            stack.push(Frame::Finish(n, n1, own));
                            stack.push(Frame::Visit(n1));
                            continue;
                        }
                    }
                    // An explanation belongs to the step that records it.
                    self.explain = None;
                    let step = match &self.inner.phases[phase] {
                        PhaseImpl::Local(..) => self.rewrite(cx, phase, n)?,
                        PhaseImpl::Pass(k) => pass::step(self, cx, *k, n)?,
                        #[cfg(feature = "mba")]
                        PhaseImpl::Mba(cfg) => pass::mba_step(self, cx, cfg, n)?,
                    };
                    match step {
                        Step::To(r, fin) if pending.contains_key(&r) => {
                            // `r` waits on `n`: take the rewrite (accepted as smaller where it
                            // was made) without visiting `r` again, so both settle on `r`.
                            self.stats.cycles_cut += 1;
                            self.retire(cx, n);
                            self.set(cx, phase, n, r, own.and(fin).and(Fin::PROVISIONAL));
                        }
                        Step::To(r, fin) => {
                            if !local {
                                self.rewritten.insert((n, r), ());
                                *pending.entry(n).or_default() += 1;
                            }
                            self.live.replace(n, r);
                            self.retire(cx, n);
                            self.inherit_parent(n, r);
                            stack.push(Frame::Finish(n, r, own.and(fin)));
                            stack.push(Frame::Visit(r));
                        }
                        Step::Normal(fin) => self.set(cx, phase, n, n, own.and(fin.unchanged())),
                    }
                }
            }
        }
        debug_assert!(pending.is_empty(), "a walk ended with results pending");
        Ok(self
            .lookup(cx, phase, root)
            .unwrap_or((root, Fin::PROVISIONAL)))
    }

    /// Tries the phase's candidate rules at `n`, whose operands are normal.
    fn rewrite(&mut self, cx: &mut Context, phase: usize, n: u32) -> Result<Step, Stop> {
        let inner = self.inner;
        let PhaseImpl::Local(net, host) = &inner.phases[phase] else {
            return Ok(Step::Normal(Fin::FINAL));
        };
        let mut cands = core::mem::take(&mut self.cands);
        cands.clear();
        cands.extend(net.candidates(cx, n));
        let r = self.try_candidates(cx, n, &cands);
        self.cands = cands;
        // The host rewrites, where no rule applied.
        match r? {
            Step::Normal(fin) if !host.is_empty() => Ok(match self.try_host(cx, n, host)? {
                Step::To(t, f) => Step::To(t, fin.and(f)),
                Step::Normal(f) => Step::Normal(fin.and(f)),
            }),
            step => Ok(step),
        }
    }

    fn try_candidates(&mut self, cx: &mut Context, n: u32, cands: &[u32]) -> Result<Step, Stop> {
        let inner = self.inner;
        let mut fin = Fin::FINAL;
        for &ri in cands {
            let rule = &inner.rules[ri as usize];
            if self.quarantined.get(ri as usize).copied().unwrap_or(false) {
                // Skipped only for this call: the result is not final.
                fin = fin.and(Fin::PROVISIONAL);
                continue;
            }
            self.meter.charge(Counter::Candidates, 1)?;
            self.emit(Event::Candidate {
                rule,
                node: cx.handle(n),
            });
            let steps = u32::try_from(self.meter.left_in(|b| b.match_steps))
                .unwrap_or(u32::MAX)
                .min(MATCH_STEPS);
            let fact_cap = u32::try_from(self.meter.left_in(|b| b.fact_work)).unwrap_or(u32::MAX);
            // `one_use` is answered from the use counts of the live DAG (under
            // `Sharing::Ignored`, as if each node were used by its user alone: always).
            let one_use = uses_one_use(rule) && !pass::alone(self);
            if one_use {
                pass::refresh_uses(self, cx)?;
            }
            let live = core::mem::take(&mut self.live);
            let roots = core::mem::take(&mut self.live_roots);
            let mut once = |_: &Context, i: u32| live.uses(i) == Some(1) && !roots.contains(&i);
            let mut env = ApplyEnv {
                assumptions: self.assumptions,
                fact_cap: Some(fact_cap),
                steps,
                one_use: one_use.then_some(&mut once as crate::rules::apply::OneUse<'_>),
                ..ApplyEnv::default()
            };
            let (work0, capped0) = (cx.facts.work, cx.facts.capped);
            let r = self.build(cx, |cx| Ok(try_apply_with(&mut env, cx, rule, n)));
            let shared = env.shared;
            // What the application reports, without its borrow of the use counts.
            let env = ApplyEnv {
                assumptions: self.assumptions,
                fact_cap: env.fact_cap,
                out_of_facts: env.out_of_facts,
                degraded: env.degraded,
                steps: env.steps,
                matched: env.matched,
                instantiating: env.instantiating,
                rel: env.rel,
                one_use: None,
                shared,
                failed: env.failed,
            };
            self.live = live;
            self.live_roots = roots;
            let r = r?;
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
                // A "no" from sharing may be a "yes" once the sharing changes.
                if shared {
                    fin = fin.and(Fin::PROVISIONAL);
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
                    if let Some((pred, [a, b])) = env.failed
                        && self.observing()
                    {
                        let h = |i: Option<u32>| i.map(|i| cx.handle(i));
                        self.emit(Event::GuardFailed {
                            rule,
                            pred,
                            args: [h(a), h(b)],
                        });
                    }
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
            match self.accept(cx, By::Rule(rule), inner.proven[ri as usize], n, r, env.rel)? {
                Accept::Yes => return Ok(Step::To(r, fin.and(Fin::relying(env.rel)))),
                Accept::Vetoed => continue,
                Accept::Rejected(reason) => {
                    if matches!(reason, Reject::Width | Reject::Verify | Reject::Tripwire) {
                        if self.quarantined.len() <= ri as usize {
                            self.quarantined.resize(ri as usize + 1, false);
                        }
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
        // The step's explanation goes with this application, taken or not.
        let why = self.explain.take();
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
        if !rel.is_none() {
            self.emit(Event::Relied { on: rel });
        }
        if let Some(why) = why {
            self.emit(Event::Explain {
                by,
                node: before,
                why: &why,
            });
        }
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
            // A `#[float_values]` rule may change a NaN into another NaN.
            let values = match by {
                By::Rule(rule) if rule.float_values => cx.fp_desc(n).map(|d| match d.op {
                    crate::fp::FpOp::Convert { to, .. } => to,
                    _ => d.format,
                }),
                _ => None,
            };
            let nan =
                |f: crate::FpFormat, x: &BitVec| f.test(crate::fp::FpTest::Nan, x) == Ok(true);
            if (0..k).any(|j| {
                held[j] && a[j] != b[j] && !values.is_some_and(|f| nan(f, &a[j]) && nan(f, &b[j]))
            }) {
                return Ok(Some(Reject::Verify));
            }
        }
        // The facts of two NaNs may be disjoint; a `#[float_values]` rewrite is not compared.
        let values_rule = matches!(by, By::Rule(rule) if rule.float_values);
        if v.tripwire && !values_rule {
            // Capped by what remains of the fact budget, both queries together.
            let cap = u32::try_from(self.meter.left_in(|b| b.fact_work)).unwrap_or(u32::MAX);
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
            // A symbol's points agree with what the host declared of it.
            let declared = cx.declared_at(i);
            let point = |w: Width, k: usize| {
                let v = point_value(seed, w, k);
                declared.map_or(v, |d| d.fit(&v))
            };
            // The operands' samples, looked up once for the node (not once per point), and
            // the node's in a vector of its final size.
            let mut kids: [(u32, &[BitVec]); 3] = [(u32::MAX, &[]); 3];
            for (slot, c) in cx.node(i).children().enumerate() {
                kids[slot] = (c, &samples[&c]);
            }
            let at = |j: u32, k: usize| match kids.iter().find(|(c, _)| *c == j) {
                Some((_, vals)) => vals[k],
                None => samples[&j][k],
            };
            let mut vals: Vec<BitVec> = Vec::with_capacity(points);
            let mut failed = None;
            for k in 0..points {
                match cx.eval_node(i, |j| at(j, k), |_, w| Some(point(w, k))) {
                    Ok(v) => vals.push(v),
                    Err(e) => {
                        failed = Some(e);
                        break;
                    }
                }
            }
            if let Some(e) = failed {
                out = Err(Stop::Error(e));
                break;
            }
            samples.insert(i, vals.into_boxed_slice());
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

    /// Simplifies each root as a call of [`run`](Self::run) with that root alone would, on up
    /// to [`Each::threads`] threads at once. Each distinct root is copied into a context of its
    /// own (with `cx`'s configuration and registry, and the assumptions copied too), simplified
    /// there, and its result copied back into `cx` ([`Context::import`]); `roots[i]` of the
    /// outcome answers `roots[i]` of the input, and the statistics are the sums over the roots.
    ///
    /// A root's work does not depend on the other roots or on the number of threads, so neither
    /// do the results. Unlike [`run`](Self::run) over several roots, sharing between roots is not
    /// weighed: a node two roots share counts as used by each alone. Observers, allowances and
    /// deadlines are [`run`](Self::run)'s.
    pub fn run_each(
        &self,
        cx: &mut Context,
        roots: &[Expr],
        each: Each<'_>,
    ) -> Result<Outcome, Error> {
        let ids = cx.ids(roots)?;
        if let Some(a) = each.assumptions {
            a.check_context(cx)?;
        }
        let mut distinct: Vec<Expr> = Vec::new();
        let mut slot: IdMap<u32, usize> = IdMap::default();
        for (&i, &e) in ids.iter().zip(roots) {
            slot.entry(i).or_insert_with(|| {
                distinct.push(e);
                distinct.len() - 1
            });
        }
        let threads = match each.threads {
            0 => std::thread::available_parallelism().map_or(1, |n| n.get()),
            n => n,
        }
        .clamp(1, distinct.len().max(1));
        // Each worker takes the next root; its result is kept alone in a small context.
        type Done = Result<(Context, RootOutcome, Stats), Error>;
        let next = std::sync::atomic::AtomicUsize::new(0);
        let results: Vec<std::sync::Mutex<Option<Done>>> = distinct
            .iter()
            .map(|_| std::sync::Mutex::new(None))
            .collect();
        let src: &Context = cx;
        let work = || {
            loop {
                let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(&root) = distinct.get(k) else {
                    break;
                };
                let done = self.run_alone(src, root, &each);
                if let Ok(mut r) = results[k].lock() {
                    *r = Some(done);
                }
            }
        };
        // The calling thread works too; where no thread can be started (WebAssembly without
        // threads, say), it does everything.
        std::thread::scope(|s| {
            for _ in 1..threads {
                if std::thread::Builder::new().spawn_scoped(s, work).is_err() {
                    break;
                }
            }
            work();
        });
        let mut outcome = Outcome {
            roots: Vec::with_capacity(roots.len()),
            stats: Stats::default(),
        };
        let mut answers: Vec<RootOutcome> = Vec::with_capacity(distinct.len());
        for (r, &root) in results.into_iter().zip(&distinct) {
            let done = r.into_inner().ok().flatten().ok_or_else(|| {
                Error::Contract("a root's worker stopped without a result".into())
            })?;
            let (small, mut out, stats) = done?;
            out.expr = cx.import(&small, &[out.expr])?[0];
            out.changed = out.expr != root;
            outcome.stats.absorb(&stats);
            answers.push(out);
        }
        for i in &ids {
            outcome.roots.push(answers[slot[i]]);
        }
        Ok(outcome)
    }

    /// [`run_each`](Self::run_each) for one root of `src`: the outcome, its result alone in a
    /// context of its own, and the statistics.
    fn run_alone(
        &self,
        src: &Context,
        root: Expr,
        each: &Each<'_>,
    ) -> Result<(Context, RootOutcome, Stats), Error> {
        let fresh = || {
            let mut cx = Context::with_config(src.config().clone());
            cx.registry = src.registry.clone();
            cx
        };
        let mut cx = fresh();
        let x = cx.import(src, &[root])?[0];
        let mut assumptions = Assumptions::new();
        if let Some(a) = each.assumptions {
            for (_, e, facts) in a.constraints() {
                let e = cx.import(src, &[e])?[0];
                assumptions.assume(&mut cx, e, facts)?;
            }
        }
        let mut run = Run::default()
            .with_per_call(each.per_root)
            .with_admission(each.admission);
        if each.assumptions.is_some() {
            run = run.with_assumptions(&assumptions);
        }
        if let Some(h) = each.hooks {
            run = run.with_hooks(h);
        }
        let out = self.run(&mut cx, &[x], run)?;
        let mut small = fresh();
        let mut root_out = out.roots[0];
        root_out.expr = small.import(&cx, &[root_out.expr])?[0];
        Ok((small, root_out, out.stats))
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
        let current = assumptions.map(|a| a.refreshed(cx)).transpose()?;
        let assumptions = current.as_deref();
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
            quarantined: Vec::new(),
            host_quarantined: Vec::new(),
            partial: (0..inner.phases.len()).map(|_| IdMap::default()).collect(),
            cands: Vec::new(),
            stack: Vec::new(),
            samples: IdMap::default(),
            linear: Default::default(),
            bitwise: IdMap::default(),
            bitwise_wide: IdMap::default(),
            bitwise_beyond: IdMap::default(),
            xor: Default::default(),
            linear_whole: Default::default(),
            xor_whole: Default::default(),
            compares: IdMap::default(),
            shuffle: IdMap::default(),
            residues: IdMap::default(),
            gf2_atoms: Vec::new(),
            gf2_stack: Vec::new(),
            chains: IdMap::default(),
            quarantined_passes: Vec::new(),
            scratch: pass::Scratch::default(),
            linear_mba: Default::default(),
            #[cfg(feature = "prove")]
            carries: Default::default(),
            demanded: Default::default(),
            demanded_same: Default::default(),
            words: Default::default(),
            #[cfg(feature = "mba")]
            reduced: Default::default(),
            sum_constants: IdMap::default(),
            #[cfg(feature = "mba")]
            mba_answers: IdMap::default(),
            #[cfg(feature = "mba")]
            mba_unproved: IdMap::default(),
            #[cfg(feature = "mba")]
            mba_exhausted: IdMap::default(),
            #[cfg(feature = "mba")]
            mba_missed: 0,
            #[cfg(feature = "mba")]
            mba_kept: IdMap::default(),
            #[cfg(feature = "mba")]
            mba_depth: 0,
            #[cfg(feature = "mba")]
            mba_deeper: false,
            #[cfg(feature = "mba")]
            mba_shallow: IdMap::default(),
            #[cfg(feature = "mba")]
            mba_undecided: IdMap::default(),
            #[cfg(feature = "mba")]
            swept: IdMap::default(),
            #[cfg(feature = "mba")]
            sweep_borrowed: 0,
            #[cfg(feature = "mba")]
            witnesses: Vec::new(),
            #[cfg(feature = "mba")]
            cut_declined: IdMap::default(),
            #[cfg(feature = "mba")]
            exhaust: Default::default(),
            live: pass::Live::default(),
            uses_on: false,
            uses_upto: 0,
            phase_start: 0,
            dead: pass::Marks::default(),
            dead_log: Vec::new(),
            live_roots: {
                let mut seen: IdMap<u32, ()> = IdMap::default();
                ids.iter()
                    .copied()
                    .filter(|&i| seen.insert(i, ()).is_none())
                    .collect()
            },
            active: 0,
            rewritten: IdMap::default(),
            #[cfg(feature = "prove")]
            rooted: IdMap::default(),
            late: false,
            held: false,
            turned: None,
            #[cfg(feature = "prove")]
            latent: IdMap::default(),
            narrows: IdMap::default(),
            settled: false,
            chain_parent: IdMap::default(),
            asks: IdMap::default(),
            first: IdMap::default(),
            detail: Detail::Events,
            phase_name: "",
            explain: None,
        };
        if let Some(o) = runner.observer.as_deref() {
            runner.detail = o.detail();
        }
        let mut done: IdMap<u32, (u32, End, Reliance)> = IdMap::default();
        let mut failure: Option<Error> = None;
        // Roots whose result is not final only because of what other roots share, with their
        // entry of `live_roots` and the version of the live roots their result was reached at
        // (the count of roots rewritten so far).
        let mut provisional: Vec<(u32, usize, u64)> = Vec::new();
        let mut version = 0u64;
        for (index, &root) in ids.iter().enumerate() {
            if done.contains_key(&root) {
                continue;
            }
            // Once the deadline has passed, no root is started: the call returns
            // what it has, and the rest say why they did not run. (A budget stop
            // goes on to the next root, whose own work is still worth keeping.)
            if runner.meter.deadline_passed() {
                done.insert(
                    root,
                    (
                        root,
                        End::BudgetTerminated(Exhausted::Deadline),
                        Reliance::NONE,
                    ),
                );
                runner.stats.budget_terminated[0] += 1;
                runner.stats.not_started += 1;
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
                    if runner.observing() {
                        runner.emit(Event::Root {
                            index,
                            root: cx.handle(root),
                            again: false,
                        });
                    }
                    let (r, end, rel) = match runner.strategy(cx, root) {
                        Ok((r, fin)) => match fin.why {
                            Some(why) if !fin.done => (r, End::BudgetTerminated(why), fin.rel),
                            _ => {
                                if !fin.done {
                                    provisional.push((
                                        root,
                                        runner.active,
                                        version + u64::from(r != root),
                                    ));
                                }
                                (r, End::Completed, fin.rel)
                            }
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
            version += u64::from(out.0 != root);
            runner.active += 1;
            done.insert(root, out);
        }
        // Once every root is done, sharing that kept a rewrite back may be gone (a subterm
        // only other roots' parts used, simplified away since): those roots again, while that
        // changes something.
        if runner.live_roots.len() > 1 {
            let mut settled = false;
            for _ in 0..3 {
                if failure.is_some() || provisional.is_empty() {
                    settled = true;
                    break;
                }
                runner.live.forget_others();
                let mut changed = false;
                for (root, k, seen) in std::mem::take(&mut provisional) {
                    // Nothing rewritten since this root's result was reached: the live roots
                    // are as they were then, and the result a fixed point of them.
                    if seen == version {
                        provisional.push((root, k, seen));
                        continue;
                    }
                    let (r0, _, rel0) = done[&root];
                    runner.active = k;
                    if runner.observing() {
                        let index = ids.iter().position(|&i| i == root).unwrap_or(0);
                        runner.emit(Event::Root {
                            index,
                            root: cx.handle(r0),
                            again: true,
                        });
                    }
                    let (r, end, rel, again) = match runner.strategy(cx, r0) {
                        Ok((r, fin)) => match fin.why {
                            Some(why) if !fin.done => {
                                (r, End::BudgetTerminated(why), fin.rel, false)
                            }
                            _ => (r, End::Completed, fin.rel, !fin.done),
                        },
                        Err((r, fin, Stop::Exhausted(e))) => {
                            (r, End::BudgetTerminated(e), fin.rel, false)
                        }
                        Err((_, _, Stop::Error(e))) => {
                            failure = Some(e);
                            break;
                        }
                    };
                    if r != r0 {
                        changed = true;
                        version += 1;
                        runner.stats.completed[usize::from(r0 != root)] -= 1;
                        let slot = match end {
                            End::Completed => &mut runner.stats.completed,
                            _ => &mut runner.stats.budget_terminated,
                        };
                        slot[usize::from(r != root)] += 1;
                        if let Some(slot) = runner.live_roots.get_mut(k) {
                            *slot = r;
                        }
                    } else if end != End::Completed {
                        runner.stats.completed[usize::from(r0 != root)] -= 1;
                        runner.stats.budget_terminated[usize::from(r != root)] += 1;
                    }
                    done.insert(root, (r, end, rel0 | rel));
                    if again {
                        provisional.push((root, k, version));
                    }
                }
                if !changed {
                    settled = true;
                    break;
                }
            }
            // The cap, with a root rewritten since another's result was reached.
            if !settled && failure.is_none() && provisional.iter().any(|p| p.2 != version) {
                runner.stats.reruns_capped += 1;
            }
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
        stats.mba.steps = spent.mba_steps;
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
        #[cfg(feature = "mba")]
        let inner = self.inner;
        let mut cur = root;
        let mut fin = Fin::FINAL;
        // with the MBA phase's noise forms, the root is read with what its
        // conditions fix put into the operands they guard first (see `pass::push_context`):
        // a case table's noise folds once its selector's bits are constants, and the budget is
        // spent on what is left. At most doubling the root; a budget keeps the root as it is.
        #[cfg(feature = "mba")]
        if inner
            .phases
            .iter()
            .any(|p| matches!(p, PhaseImpl::Mba(c) if c.noise_forms))
        {
            let own = match cx.dag_size(&[cx.handle(cur)], 1 << 22) {
                Ok(crate::expr::Bounded::Exact(n)) => n,
                _ => 0,
            };
            match pass::push_context(self, cx, cur, own) {
                Ok(Some(p)) => {
                    self.emit_stage(cx, Stage::Context, cur, p);
                    cur = p;
                }
                Ok(None) | Err(Stop::Exhausted(_)) => {}
                Err(stop) => return Err((cur, fin, stop)),
            }
        }
        let swept = self.sweep(cx, cur).map_err(|stop| (cur, fin, stop))?;
        if swept != cur {
            fin = fin.and(Fin::relying(self.assumed()));
            cur = swept;
        }
        cur = self.cases(cx, cur).map_err(|stop| (cur, fin, stop))?;
        let settled = self.rounds(cx, cur, fin);
        #[cfg(feature = "mba")]
        if let Ok((u, ufin)) = settled
            && inner
                .phases
                .iter()
                .any(|p| matches!(p, PhaseImpl::Mba(c) if c.noise_forms))
        {
            return self.split(cx, u, ufin);
        }
        settled
    }

    /// With the MBA phase's noise forms, the root `u` the rounds settled on, read once more on
    /// either side of the condition its selects test most (see `pass::split_cases`): each side
    /// with what that case fixes put in, swept and simplified by the rounds as a root is, and
    /// the two written as one expression again with the choice as far down as they agree
    /// (`pass::join_cases`). The smallest of the three is the result: `u`, the select of the
    /// sides, or the sides joined.
    ///
    /// An obfuscator picks between two masked values by a flag and computes with the one
    /// picked: with the flag fixed one of them is a constant, and everything computed from it
    /// folds, where the root as a whole is a function of both. In 140 measured calls every one
    /// of 41 such roots was a constant or a fraction of its size on one side. Asked of the
    /// root before the rounds, the sides came out larger than the settled root's sides in
    /// every one of them: the rounds fold what the two sides share once.
    ///
    /// The sides take one round that changes them (and the deeper one it may ask for): what
    /// the condition fixed folds in it, and the rounds after it changed nothing measured and
    /// took as long again. A budget that runs out on the sides keeps the smallest so far, and
    /// is the reason the run ended.
    #[cfg(feature = "mba")]
    fn split(
        &mut self,
        cx: &mut Context,
        u: u32,
        ufin: Fin,
    ) -> Result<(u32, Fin), (u32, Fin, Stop)> {
        let e = match pass::split_cases(self, cx, u, true) {
            Ok(Some(e)) => e,
            Ok(None) | Err(Stop::Exhausted(_)) => return Ok((u, ufin)),
            Err(stop) => return Err((u, ufin, stop)),
        };
        self.emit_stage(cx, Stage::Cases, u, e);
        let sides = |me: &mut Self, cx: &mut Context| {
            let (mut cur, mut fin) = (e, ufin);
            let swept = me.sweep(cx, cur).map_err(|stop| (cur, fin, stop))?;
            if swept != cur {
                fin = fin.and(Fin::relying(me.assumed()));
                cur = swept;
            }
            cur = me.cases(cx, cur).map_err(|stop| (cur, fin, stop))?;
            me.rounds_within(cx, cur, fin, SIDE_ROUNDS, false)
        };
        let (s, sfin, stop) = match sides(self, cx) {
            Ok((s, f)) => (s, f, None),
            Err((s, f, stop)) => (s, f, Some(stop)),
        };
        let joined = match pass::join_cases(self, cx, s) {
            Ok(joined) => joined,
            Err(Stop::Exhausted(_)) => None,
            Err(stop) => return Err((u, ufin, stop)),
        };
        let size = |cx: &mut Context, i: u32| match cx.dag_size(&[cx.handle(i)], 1 << 22) {
            Ok(crate::expr::Bounded::Exact(n)) => n,
            _ => u32::MAX,
        };
        let mut best = (u, ufin, size(cx, u));
        for cand in [Some(s), joined].into_iter().flatten() {
            let n = size(cx, cand);
            if n < best.2 {
                best = (cand, sfin, n);
            }
        }
        // (The last root an observer was told of is the sides': it is told of the result.)
        if best.0 != s {
            self.emit_stage(cx, Stage::Cases, s, best.0);
        }
        match stop {
            None => Ok((best.0, best.1)),
            Some(stop) => Err((best.0, best.1, stop)),
        }
    }

    /// Every constraint of the run's assumptions: what a result of the opaque-constant sweep
    /// is taken to rely on. The sweep reads the facts of the nodes it folds (known bits, the
    /// values a bottleneck can take) without recording which constraints they came from, so a
    /// root it changed is reported as relying on all of them (an over-approximation, as
    /// [`Reliance`] allows; none where the run has no assumptions).
    fn assumed(&self) -> Reliance {
        self.assumptions.map_or(Reliance::NONE, |a| {
            a.constraints()
                .fold(Reliance::NONE, |r, (id, _, _)| r | Reliance::of(id))
        })
    }

    /// `cur` after the opaque-constant sweep (see `pass::mba::sweep`), where the MBA phase asks
    /// for it. The sweep is opt-in: it can spend work on failed candidate proofs before the
    /// ordinary phases reach their root. Run before the first round, and before each later one
    /// on what the round before left: the phases expose constants the first sweep could not
    /// prove (a fragment over fewer atoms once its operands are simplified), and a node an
    /// earlier sweep examined is read from it, so only what a round made is asked about. A
    /// budget keeps the root as it is.
    fn sweep(&mut self, cx: &mut Context, cur: u32) -> Result<u32, Stop> {
        #[cfg(feature = "mba")]
        if let Some(cfg) = self.inner.phases.iter().find_map(|p| match p {
            PhaseImpl::Mba(c) if c.opaque_sweep || c.noise_forms || c.known_atoms => Some(c),
            _ => None,
        }) {
            return match pass::mba_sweep(self, cx, cfg, cur) {
                Ok(r) => {
                    self.emit_stage(cx, Stage::Sweep, cur, r);
                    Ok(r)
                }
                Err(Stop::Exhausted(_)) => Ok(cur),
                Err(stop) => Err(stop),
            };
        }
        let _ = cx;
        Ok(cur)
    }

    /// with the MBA phase's noise forms, `cur` with its pieces that depend only on
    /// a few conditions written as tables of their values (see `pass::cut_cases`): what the
    /// rounds leave of a noise term is often a constant on either side of one condition. The
    /// evaluations walk at most 4 times the root's nodes; a budget keeps the root as it is.
    fn cases(&mut self, cx: &mut Context, cur: u32) -> Result<u32, Stop> {
        #[cfg(feature = "mba")]
        if self
            .inner
            .phases
            .iter()
            .any(|p| matches!(p, PhaseImpl::Mba(c) if c.noise_forms))
        {
            let own = match cx.dag_size(&[cx.handle(cur)], 1 << 22) {
                Ok(crate::expr::Bounded::Exact(n)) => n,
                _ => return Ok(cur),
            };
            let cur = match pass::cut_cases(self, cx, cur, 4 * u64::from(own)) {
                Ok(Some(p)) => {
                    self.emit_stage(cx, Stage::Cases, cur, p);
                    p
                }
                Ok(None) | Err(Stop::Exhausted(_)) => cur,
                Err(stop) => return Err(stop),
            };
            // And the root itself, where it is one value on either side of the condition
            // its selects test most (see `pass::split_cases`).
            return match pass::split_cases(self, cx, cur, false) {
                Ok(Some(p)) => {
                    self.emit_stage(cx, Stage::Cases, cur, p);
                    Ok(p)
                }
                Ok(None) | Err(Stop::Exhausted(_)) => Ok(cur),
                Err(stop) => Err(stop),
            };
        }
        let _ = cx;
        Ok(cur)
    }

    /// Reports the end of a phase that began when the meter had spent `spent0`.
    fn emit_phase_end(
        &mut self,
        cx: &Context,
        round: u8,
        phase: usize,
        root: u32,
        spent0: Budget,
        stopped: Option<Exhausted>,
    ) {
        if self.observing() {
            self.emit(Event::PhaseEnd {
                round,
                phase,
                root: cx.handle(root),
                spent: self.meter.spent.saturating_sub(&spent0),
                stopped,
            });
        }
    }

    /// Whether questions of the MBA phase wait for a deeper round (see `pass::mba::depth`),
    /// which the next round then is: one step deeper, or at the full depth (`full`).
    fn deepen(&mut self, full: bool) -> bool {
        #[cfg(feature = "mba")]
        if self.mba_deeper {
            self.mba_deeper = false;
            self.mba_shallow.clear();
            self.mba_depth = match full {
                true => u8::MAX,
                false => self.mba_depth.saturating_add(1),
            };
            return true;
        }
        let _ = full;
        false
    }

    /// [`strategy`](Self::strategy)'s rounds of its phases from `cur`, until a round changes
    /// nothing or the strategy allows no more (`Stats::rounds_capped` counts those).
    ///
    /// The rounds have a late stage, for readings that pay by the commit rule and yet stand
    /// in the way of what the passes read better when they are taken first (a carry read as
    /// digits that meet nothing, before the slice of its word is proved). A pass leaves
    /// such a reading alone until `late` is set, and says so ([`hold`](Self::hold); the step
    /// at the root says whether its own would rewrite the root, `at_root`). Where a round
    /// has changed nothing, the deeper questions and the words pass have had their turn
    /// (see `rounds_within`) and a reading was so left in it, the flag is set and the
    /// rounds go on: once for a root. Every rewrite of the stage is a rewrite as any other,
    /// under the commit rule, so the rounds end as they do without it.
    ///
    /// What is asked again when the flag turns is what was not final: the nodes at which a
    /// reading was held back, and those above them. Results made under the flag are kept
    /// for the call only (see `set`).
    fn rounds(
        &mut self,
        cx: &mut Context,
        cur: u32,
        fin: Fin,
    ) -> Result<(u32, Fin), (u32, Fin, Stop)> {
        self.late = false;
        self.turned = None;
        let max = self.inner.strategy.max_rounds.max(1);
        let out = self.rounds_within(cx, cur, fin, max, true);
        self.late = false;
        // The stage's guard: its root is kept where it has fewer nodes than the root the
        // stage began from, or as many and fewer comparisons, and no cap declined in the
        // stage what none had declined before it (a question the stage's readings pose and
        // a limit leaves open would end a run that was complete as one cut short).
        // Otherwise that root is the result, with what was known of it then: the outcome is
        // what it would have been without the stage, but for the work charged (and
        // reported, see `Stage::Late`).
        let Some((start, known)) = self.turned.take() else {
            return out;
        };
        let end = match &out {
            Ok((r, _)) | Err((r, _, _)) => *r,
        };
        let capped = matches!(&out, Ok((_, f)) if f.why.is_some() && known.why.is_none());
        if !capped && (end == start || smaller(cx, end, start)) {
            return out;
        }
        if end != start {
            self.emit_stage(cx, Stage::Late, end, start);
        }
        match out {
            Ok(_) => Ok((start, known)),
            Err((_, _, stop)) => Err((start, known, stop)),
        }
    }

    /// [`rounds`](Self::rounds), at most `max` of them that change the root; with `late`,
    /// the late stage among them.
    fn rounds_within(
        &mut self,
        cx: &mut Context,
        mut cur: u32,
        mut fin: Fin,
        max: u8,
        late: bool,
    ) -> Result<(u32, Fin), (u32, Fin, Stop)> {
        let inner = self.inner;
        #[cfg(feature = "mba")]
        {
            self.mba_depth = 0;
            self.mba_deeper = false;
            self.mba_shallow.clear();
        }
        self.words.turn = false;
        // The rounds that changed the root, and every round (the number an observer sees).
        let (mut changed, mut round) = (0u8, 0u8);
        // Whether this round is over the root the one before it left as it was, with deeper
        // questions; and whether it is the one round past the strategy's last, with the
        // deepest (see below).
        let (mut again, mut extra) = (false, false);
        loop {
            self.stats.rounds = self.stats.rounds.max(u32::from(round) + 1);
            self.held = false;
            if round > 0 && !again {
                let swept = self.sweep(cx, cur).map_err(|stop| (cur, fin, stop))?;
                if swept != cur {
                    fin = fin.and(Fin::relying(self.assumed()));
                    cur = swept;
                }
                cur = self.cases(cx, cur).map_err(|stop| (cur, fin, stop))?;
            }
            let (start, before) = (cur, fin);
            for (phase, p) in inner.strategy.phases.iter().enumerate() {
                let spent0 = self.meter.spent;
                self.settled = cur == start;
                self.phase_name = p.name();
                if self.observing() {
                    self.emit(Event::PhaseBegin {
                        round,
                        phase,
                        root: cx.handle(cur),
                    });
                }
                match self.local(cx, phase, cur) {
                    Ok((r, f)) => {
                        // The demanded-bits pass commits a reader at a time, each counted
                        // against the nodes it frees with the rest of the root as it was;
                        // what several readers of one word are rewritten to can leave the
                        // root larger than the phase found it (the limbs written twice, once
                        // for the readers rewritten and once for those that were not). Such
                        // a phase is given up: what the later phases read (the words pass,
                        // whole) is the root as it was.
                        let grew = r != cur
                            && matches!(
                                inner.phases[phase],
                                PhaseImpl::Pass(pass::PassKind::Demanded)
                            )
                            && census(cx, r).0 > census(cx, cur).0;
                        if grew {
                            fin = fin.and(Fin::PROVISIONAL);
                        } else {
                            cur = r;
                            fin = fin.and(f);
                        }
                        self.emit_phase_end(cx, round, phase, cur, spent0, None);
                    }
                    // A budget keeps what the stopped phase did (see `salvage`). A
                    // deadline does not: it means stop now, the caller is waiting, and
                    // salvaging walks the whole DAG below the root once more — work the
                    // run was just told to stop doing.
                    Err(stop @ Stop::Exhausted(Exhausted::Deadline)) => {
                        self.emit_phase_end(
                            cx,
                            round,
                            phase,
                            cur,
                            spent0,
                            Some(Exhausted::Deadline),
                        );
                        return Err((cur, fin, stop));
                    }
                    Err(Stop::Exhausted(why)) => {
                        let out = match self.salvage(cx, phase, cur) {
                            Some((r, f)) => (r, fin.and(f), Stop::Exhausted(why)),
                            None => (cur, fin, Stop::Exhausted(why)),
                        };
                        self.emit_phase_end(cx, round, phase, out.0, spent0, Some(why));
                        return Err(out);
                    }
                    Err(stop) => return Err((cur, fin, stop)),
                }
            }
            round = round.saturating_add(1);
            let same = cur == start;
            changed += u8::from(!same);
            let last = extra || changed >= max;
            // The MBA phase's questions that ran out of steps at the depth this round asked
            // them (see `pass::mba::depth`) are asked deeper once the rounds have nothing left
            // to do at this one: in a round over the same root where this one changed nothing
            // (without the sweeps, and with that round's word on the root in place of this
            // one's), and in one round past the strategy's last, at the full depth, where the
            // rounds were still changing it.
            //
            // The words pass asks the same way, after them: in a round over a root the other
            // phases left as it was (see `pass::words::State::turn`), and in that one round
            // past the last.
            let words = !self.words.turn
                && inner
                    .phases
                    .iter()
                    .any(|p| matches!(p, PhaseImpl::Pass(pass::PassKind::Words)));
            self.words.turn = false;
            if same {
                if self.deepen(false) {
                    (fin, again) = (before, true);
                    continue;
                }
                if words {
                    self.words.turn = true;
                    (fin, again) = (before, true);
                    continue;
                }
                // The late stage, once and last: where a reading was left to it in this
                // round, or the step at the root has said the readings it takes last would
                // rewrite this root, the rounds go on with the flag set.
                #[cfg(feature = "prove")]
                let latent = self.latent.contains_key(&cur);
                #[cfg(not(feature = "prove"))]
                let latent = false;
                if late && !self.late && (self.held || latent) {
                    self.late = true;
                    self.turned = Some((cur, fin));
                    #[cfg(feature = "prove")]
                    self.rooted.clear();
                    again = true;
                    continue;
                }
                return Ok((cur, fin));
            }
            if last {
                // (Both are asked for: neither short-circuits the other.)
                let deeper = !extra && self.deepen(true);
                if !extra && (deeper || words) {
                    self.words.turn = words;
                    (extra, again) = (true, false);
                    continue;
                }
                break;
            }
            again = false;
        }
        self.stats.rounds_capped += 1;
        Ok((cur, fin))
    }
}

/// The nodes of the DAG of `root`, and the comparisons among them.
fn census(cx: &Context, root: u32) -> (usize, u32) {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack = vec![root];
    let mut compares = 0u32;
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        let node = cx.node(i);
        compares += u32::from(matches!(
            node.op,
            crate::expr::OpCode::Eq
                | crate::expr::OpCode::Ne
                | crate::expr::OpCode::Ult
                | crate::expr::OpCode::Ule
                | crate::expr::OpCode::Slt
                | crate::expr::OpCode::Sle
        ));
        stack.extend(node.children());
    }
    (seen.len(), compares)
}

/// Whether the DAG of `a` has fewer nodes than that of `b`, or as many and fewer comparisons.
fn smaller(cx: &Context, a: u32, b: u32) -> bool {
    census(cx, a) < census(cx, b)
}

/// The rounds that change them the sides of a split root take (see `Runner::split`).
#[cfg(feature = "mba")]
const SIDE_ROUNDS: u8 = 1;

/// Whether `n1`, the rebuild of `n` over new operands `kids`, is `n`'s operator over them (in
/// any order: the constructors sort commutative operands), not a fold the constructors made.
fn same_operator(cx: &Context, n: u32, n1: u32, kids: &[u32; 3]) -> bool {
    let (a, b) = (cx.node(n), cx.node(n1));
    if a.op != b.op {
        return false;
    }
    let mut want: Vec<u32> = kids[..a.children().count()].to_vec();
    let mut got: Vec<u32> = b.children().collect();
    want.sort_unstable();
    got.sort_unstable();
    want == got
}

/// Whether the rule's guard asks `one_use`.
fn uses_one_use(rule: &Rule) -> bool {
    use crate::rules::{FactPred, RNode};
    rule.guard.is_some()
        && rule
            .nodes
            .iter()
            .any(|n| matches!(n, RNode::Fact(FactPred::OneUse, ..)))
}
