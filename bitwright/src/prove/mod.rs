//! A native prover (feature `prove`): expressions are bit-blasted into an and-inverter graph,
//! encoded as clauses, and decided by bitwright's own CDCL SAT solver. A proof of validity comes
//! with a certificate, the clauses and a DRUP proof of their unsatisfiability, that an
//! independent checker ([`Certificate::check`]) verifies, and that any DRAT checker can read
//! ([`Certificate::dimacs`], [`Certificate::drat`]). A refutation comes with a counterexample:
//! a value for every symbol, checked by bitwright's evaluator before it is returned. A question
//! the search does not settle within its budget says why ([`Unknown`]), and a [`Question`]
//! goes on from where the search stopped, under a larger budget, without starting over.
//! For a small joint output superset above unresolved predicates, [`domain::analyze`]
//! preserves shared Boolean structure under explicit premises without solving reachability.
//!
//! No other solver is involved. Bit-vector operators are blasted with bitwright's total
//! semantics (SMT-LIB's); floating-point operators with IEEE 754's and bitwright's canonical
//! NaN ([`crate::fp`]); extension operations through their [`expand`](crate::ext::ExtOp::expand)
//! definition, if they have one (otherwise the question is not decided).
//!
//! ```
//! use bitwright::prove::{Config, Outcome, equal};
//! use bitwright::{Context, ParseOptions, Width};
//!
//! let mut cx = Context::new();
//! let o = ParseOptions::width(Width::W32);
//! let (a, b) = (cx.parse("(x ^ y) + 2 * (x & y)", &o)?, cx.parse("x + y", &o)?);
//! let Outcome::Proved(Some(cert)) = equal(&mut cx, a, b, &Config::default().with_certificate(true))? else {
//!     panic!("not proved")
//! };
//! assert!(cert.check().is_ok());
//! let c = cx.parse("x | y", &o)?;
//! assert!(matches!(equal(&mut cx, a, c, &Config::default())?, Outcome::Refuted(_)));
//! # Ok::<(), bitwright::Error>(())
//! ```

pub mod aig;
pub mod blast;
mod cuts;
pub mod domain;
pub mod drup;
mod exhaustion;
pub mod finite;
mod fp;
mod incremental;
mod lean;
pub mod lrat;
mod relations;
mod rule;
mod sample_words;
pub mod sat;
mod sums;
mod sweep;
#[cfg(test)]
mod tests;

use crate::error::Error;
use crate::expr::{Context, Expr, OpCode};
use crate::facts::Assumptions;
use crate::hash::IdMap;
use crate::{BitVec, SymbolKey, Width};

pub use exhaustion::Exhaustion;
/// What an [`Incremental`] answers.
pub use incremental::Answer as IncrementalAnswer;
pub use incremental::Incremental;
pub(crate) use lean::lean_equation;
pub use lean::lean_theorem;
pub use rule::{RuleOutcome, WidthReport, rule, rule_all_widths};

use aig::{Aig, Cnf, L};
use blast::Bits;
use sat::{Answer, Lit, Solver, Step};
pub use sat::{Backend, Limits};

/// How assignments are selected before SAT search. Sampling can find a concrete
/// counterexample. Complete ordered enumeration on the word path can also prove validity;
/// partial coverage and pseudorandom samples cannot.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub enum SampleMode {
    /// Seeded pseudorandom assignments, with all-zero and all-one unknown bits first.
    #[default]
    Random,
    /// Enumerate assignments from zero upwards over the circuit's unknown input bits,
    /// least significant input first. Useful for small integer witnesses in wide domains.
    /// Multiple symbols' unknown bits are concatenated in circuit input order; declared
    /// fixed bits retain their values. Higher unknown bits stay zero until reached.
    Small,
    /// Enumerate small values of reconstructed words: unknown bits of larger pure
    /// concatenations and standalone symbols are visited from low to high. A bounded
    /// portfolio varies words separately and together within the shared sample allowance.
    /// Shared bits keep one assignment. Uses the bounded word sampler when supported, falling
    /// back to [`Small`](Self::Small) circuit ordering for other graphs.
    Words,
}

/// How hard to try, and what to keep.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Config {
    /// The most conflicts the SAT solver may meet (then [`Unknown::Budget`]).
    pub max_conflicts: u64,
    /// The most propagations the SAT solver may do (then [`Unknown::Budget`]; `u64::MAX`, the
    /// default: no limit). A conflict costs more propagation on a larger circuit, so this bounds
    /// the time a question takes more closely than conflicts do, and as deterministically.
    pub max_propagations: u64,
    /// The most AIG nodes the question may take (then [`Unknown::TooLarge`]).
    pub max_nodes: usize,
    /// Keep a [`Certificate`] for a proof.
    pub certificate: bool,
    /// Simplify the question with bitwright's own engine before blasting it (the
    /// deobfuscation strategy, with the MBA service and its opaque-constant sweep when the `mba`
    /// feature is on): identities the engine settles at the word level (products of MBA, say,
    /// which bit-level SAT finds hard) are answered at once, and the rest is blasted smaller.
    /// Not with a certificate: a certificate is of the question as asked, with its symbols'
    /// declared known bits.
    pub simplify: bool,
    /// Simplify without the one pass of the engine that commits rewrites it has derived but
    /// neither proved nor matched against a proved rule: the limb-arithmetic pass
    /// ([`Phase::Words`](crate::engine::Phase), integer identities checked at sample points).
    /// An answer then rests only on proved rules, passes that are decision procedures or
    /// prove what they commit, and the search. Off by default: that pass is what decides
    /// limb multiplications no search finishes.
    pub strict: bool,
    /// Whether the simplifier's limb-arithmetic pass writes a result only once a circuit and
    /// a search have proved it ([`Strategy::words_proved`](crate::engine::Strategy)): between
    /// the default, which takes the pass's derivations as they are, and
    /// [`strict`](Self::strict), which leaves the pass out.
    pub proved_words: bool,
    /// The engine's budget for [`simplify`](Self::simplify): caps in the units of
    /// [`Budget`](crate::engine::Budget), counts of work and never time, so a question stops at
    /// the same place on every run. [`Budget::default`](crate::engine::Budget::default) (the
    /// default) is generous; [`with_simplify_fuel`](Self::with_simplify_fuel) scales every cap
    /// by one number. A simplification its budget stops keeps the rewrites it made, and the
    /// rest of the question is blasted as it stands; [`Stats::simplification`] says what was
    /// spent and which cap stopped it.
    pub simplify_budget: crate::engine::Budget,
    /// Assignments of the symbols to evaluate before the search, 64 at a time
    /// (in batches of 64, selected by [`sample_mode`](Self::sample_mode)): a refutation that a fraction of
    /// the values give is found without the search, which needs many conflicts for it on a
    /// large circuit. With [`word_sampling`](Self::word_sampling), supported samples precede
    /// bit-blasting. 0: none.
    pub samples: u32,
    /// Assignment selection for [`samples`](Self::samples). Default: [`SampleMode::Random`].
    pub sample_mode: SampleMode,
    /// Add certified transitive bit-equality lemmas exposed by the asserted query. Cycle
    /// contradictions are detected regardless; additional lemmas are opt-in because their
    /// effect on arithmetic search depends on the workload.
    pub relational_lemmas: bool,
    /// Initially prefer the unknown bits of small shift counts as decisions. This specializes
    /// variable shifts during search without restricting which selector values are allowed.
    pub selector_branching: bool,
    /// Cancel a shared input through bounded XOR paths at every bitwise boundary. This can
    /// remove direct input dependencies through odd products, but changes arithmetic search
    /// behavior; opt-in pending workload-specific measurement.
    pub input_cancellation: bool,
    /// Factor ORs of XORs with a shared operand at one-valued equality target bits.
    /// Opt-in because the smaller encoding can alter longer arithmetic searches adversely.
    pub join_factoring: bool,
    /// Inline private intermediate XORs into three-input parity gates. This reduces encoding
    /// variables without changing the clause count, but its search performance is workload-dependent.
    pub xor3_encoding: bool,
    /// Compress modular multiplication columns before one final carry-propagating addition.
    /// Opt-in pending measurements on arithmetic search workloads.
    pub carry_save_multiplication: bool,
    /// Try samples directly on a bounded integer DAG of at most 64-bit words before
    /// bit-blasting. Ordered modes can prove after enumerating every legal input assignment;
    /// partial samples and unsupported DAGs use the circuit path. Certificates use that path
    /// even after complete enumeration.
    /// [`SampleMode::Words`] also enables this path.
    pub word_sampling: bool,
    /// Decide a question by evaluating it at every legal assignment when it has at most this
    /// many unknown input bits, before bit-blasting. It applies to bounded integer DAGs of at
    /// most 64-bit words, the same as [`word_sampling`](Self::word_sampling), and costs
    /// `2^bits` evaluations, in parallel across threads; it is not bounded by the search
    /// limits. A failing assignment is replayed on the original question. A proof asked for
    /// with a [`certificate`](Self::certificate) comes with an [`Exhaustion`], which checks the
    /// question's bit-blasted circuit at every assignment of its inputs, independently of the
    /// word-level decision. If that circuit has more inputs than this bound (it may keep bits
    /// the word program fixes from scoped assumptions as constrained inputs), the search
    /// decides the question instead. 0 (the default): never.
    pub exhaustive_inputs: u8,
    /// Write the sums of the question one way before blasting it: both sides read as linear
    /// forms over slices of their values (carries of limbs as the high digits they stand
    /// for), and built again in one order, so that what the two sides add up the same way is
    /// one circuit and what cancels is gone. An equality at every input; not for a
    /// [`certificate`](Self::certificate), which is of the question as asked. Opt-in: it
    /// helps where the two sides are one arithmetic written twice (a limb against its word),
    /// and changes the search elsewhere.
    pub shared_sums: bool,
    /// Read the divisions by constants that a compiler wrote as products by magic numbers
    /// (`trunc((zext(x) · M) >>u k)`, a multiply-high and a shift, the signed forms) as the
    /// divisions they are, before the question is blasted: the simplifier's division pass
    /// alone, for a question asked without the simplifier ([`simplify`](Self::simplify)
    /// reads them already). A multiplier's circuit against a divider's is beyond a search
    /// (the 32-bit quotient by 10 is undecided after 200,000 conflicts); read, both sides
    /// are one division. An equality at every input; not for a
    /// [`certificate`](Self::certificate). Opt-in.
    pub divisions: bool,
    /// Sweep the circuit before the first search: nodes that simulation shows equal (or
    /// complementary) are proved so one pair at a time, from the inputs up, by a solver of
    /// the circuit's clauses alone, and each equivalence is given to the search as clauses.
    /// Two circuits for one function often share most of their inner nodes (a prefix adder
    /// and `x + y` have the same carries), and a search over their miter alone rediscovers
    /// each of them inside one refutation: swept, the 64-bit prefix adder against `x + y`
    /// takes 0.29 M propagations instead of 0.54 M, the 32-bit SWAR population count against
    /// `popcnt` 24 k instead of 148 k, and a 64-bit MBA rewriting of `x - y` 0.56 M instead of
    /// 7.6 M.
    ///
    /// The circuit is simulated first, and only swept when the simulation shows enough of
    /// that sharing: classes of nodes that agree joining the two sides of an equality, at
    /// least 4 and one per 10 nodes private to a side (a question that is no equality: classes
    /// of two nodes or more, against all its nodes). Products, or the shift-and-xor addition
    /// loop against `x + y`, show little and are not swept; the simulation is all they cost.
    /// A sweep is part of preparing the question: it takes at most half of the configured
    /// limits ([`max_conflicts`](Self::max_conflicts), [`max_propagations`](Self::max_propagations))
    /// before any search, whatever the searches' own, so a question resumed in steps is swept
    /// as one asked at once; its work counts in the question's totals as work done before the
    /// first search; and with a [`certificate`](Self::certificate) its lemmas are logged so the
    /// certificate still checks. See [`Stats::sweeping`]. On by default.
    pub sweeping: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            max_conflicts: 1_000_000,
            max_propagations: u64::MAX,
            max_nodes: 4_000_000,
            certificate: false,
            simplify: true,
            strict: false,
            proved_words: false,
            simplify_budget: crate::engine::Budget::default(),
            samples: 256,
            sample_mode: SampleMode::Random,
            relational_lemmas: false,
            selector_branching: false,
            input_cancellation: false,
            join_factoring: false,
            xor3_encoding: false,
            carry_save_multiplication: false,
            word_sampling: false,
            exhaustive_inputs: 0,
            shared_sums: false,
            divisions: false,
            sweeping: true,
        }
    }
}

setters!(Config {
    with_max_conflicts: max_conflicts: u64,
    with_max_propagations: max_propagations: u64,
    with_max_nodes: max_nodes: usize,
    with_certificate: certificate: bool,
    with_simplify: simplify: bool,
    with_strict: strict: bool,
    with_proved_words: proved_words: bool,
    with_simplify_budget: simplify_budget: crate::engine::Budget,
    with_samples: samples: u32,
    with_sample_mode: sample_mode: SampleMode,
    with_relational_lemmas: relational_lemmas: bool,
    with_selector_branching: selector_branching: bool,
    with_input_cancellation: input_cancellation: bool,
    with_join_factoring: join_factoring: bool,
    with_xor3_encoding: xor3_encoding: bool,
    with_carry_save_multiplication: carry_save_multiplication: bool,
    with_word_sampling: word_sampling: bool,
    with_exhaustive_inputs: exhaustive_inputs: u8,
    with_shared_sums: shared_sums: bool,
    with_divisions: divisions: bool,
    with_sweeping: sweeping: bool,
});

impl Config {
    /// Sets [`simplify_budget`](Self::simplify_budget) to
    /// [`Budget::fuel`](crate::engine::Budget::fuel)`(fuel)`: `fuel` node visits of the engine
    /// and every other cap in proportion (the default is `1 << 22`).
    pub fn with_simplify_fuel(self, fuel: u64) -> Self {
        self.with_simplify_budget(crate::engine::Budget::fuel(fuel))
    }

    /// The search's limits: [`max_conflicts`](Self::max_conflicts) and
    /// [`max_propagations`](Self::max_propagations).
    pub fn limits(&self) -> Limits {
        Limits {
            conflicts: self.max_conflicts,
            propagations: self.max_propagations,
        }
    }
}

/// The engine that simplifies questions (see [`Config::simplify`]): the deobfuscation
/// strategy, and with `strict` without the pass that commits rewrites it has derived but
/// neither proved nor matched against a proved rule ([`Phase::Words`](crate::engine::Phase)),
/// or with `proved` with that pass writing only what a circuit and a search prove
/// ([`Config::proved_words`]).
fn simplifier_of(strict: bool, proved: bool) -> &'static crate::engine::Engine {
    static ENGINES: [std::sync::OnceLock<crate::engine::Engine>; 3] = [
        std::sync::OnceLock::new(),
        std::sync::OnceLock::new(),
        std::sync::OnceLock::new(),
    ];
    let which = if strict { 1 } else { 2 * usize::from(proved) };
    ENGINES[which].get_or_init(|| {
        #[cfg(feature = "mba")]
        let mut strategy = crate::engine::Strategy::deobfuscate()
            .with_mba(crate::mba::MbaConfig::default().with_opaque_sweep(true));
        #[cfg(not(feature = "mba"))]
        let mut strategy = crate::engine::Strategy::deobfuscate();
        if strict {
            (strategy.phases).retain(|p| !matches!(p, crate::engine::Phase::Words));
        }
        strategy.words_proved = proved;
        crate::engine::Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap_or_else(|_| crate::engine::Engine::standard())
    })
}

/// The division pass alone ([`Config::divisions`]).
fn divisions_only() -> &'static crate::engine::Engine {
    static ENGINE: std::sync::OnceLock<crate::engine::Engine> = std::sync::OnceLock::new();
    ENGINE.get_or_init(|| {
        let strategy =
            crate::engine::Strategy::new("divisions", vec![crate::engine::Phase::Division]);
        crate::engine::Engine::builder()
            .builtin()
            .strategy(strategy)
            .build()
            .unwrap_or_else(|_| crate::engine::Engine::standard())
    })
}

/// `p` as the prover's simplifier leaves it within [`Config::simplify_budget`]: an expression
/// equal to `p` at every value of the symbols, which is what the prover builds its circuit
/// of. Asked again of an expression a question was posed about, it costs a lookup.
pub fn simplified(cx: &mut Context, p: Expr, cfg: &Config) -> Result<Expr, Error> {
    let run = crate::engine::Run::default().with_per_call(cfg.simplify_budget);
    Ok(simplifier_of(cfg.strict, cfg.proved_words)
        .run(cx, &[p], run)?
        .roots[0]
        .expr)
}

/// Clauses and a DRUP proof that they are unsatisfiable, or, for a proof by complete
/// enumeration ([`Config::exhaustive_inputs`]), the circuit to enumerate.
#[derive(Clone, Debug)]
pub struct Certificate {
    /// The number of variables.
    pub vars: u32,
    /// The clauses.
    pub clauses: Vec<Vec<Lit>>,
    /// The proof.
    pub proof: Vec<Step>,
    /// The circuit of a proof by complete enumeration. Such a certificate has no clauses or
    /// DRUP proof, so its [`dimacs`](Self::dimacs) and [`drat`](Self::drat) export nothing a
    /// DRAT checker would accept.
    pub exhaustion: Option<Exhaustion>,
}

impl Certificate {
    /// Checks the proof with the independent checker: the DRUP proof against the clauses, or
    /// the circuit of an [`Exhaustion`] at every assignment of its inputs.
    pub fn check(&self) -> Result<(), String> {
        match &self.exhaustion {
            Some(exhaustion) => exhaustion.check(),
            None => {
                drup::check(&self.clauses, &self.proof)?;
                // In the tests, every proof checked is checked as LRAT too.
                #[cfg(test)]
                lrat::check(&self.clauses, &self.lrat()?)?;
                Ok(())
            }
        }
    }

    /// The clauses in DIMACS CNF.
    pub fn dimacs(&self) -> String {
        let mut s = format!("p cnf {} {}\n", self.vars, self.clauses.len());
        for c in &self.clauses {
            for l in c {
                s.push_str(&l.dimacs().to_string());
                s.push(' ');
            }
            s.push_str("0\n");
        }
        s
    }

    /// The proof as LRAT ([`lrat`]): every learned clause with the clauses it follows from,
    /// found by checking the DRUP proof, for a checker that does no search (the text is
    /// [`lrat::to_text`], beside [`dimacs`](Self::dimacs)). An error when the proof does not
    /// check, or is one by enumeration.
    pub fn lrat(&self) -> Result<Vec<lrat::Step>, String> {
        match &self.exhaustion {
            Some(_) => Err("a proof by enumeration has no clauses".into()),
            None => lrat::from_drup(&self.clauses, &self.proof),
        }
    }

    /// The proof in DRAT's text format (additions, and deletions prefixed `d`).
    pub fn drat(&self) -> String {
        let mut s = String::new();
        for step in &self.proof {
            let (pre, c) = match step {
                Step::Add(c) => ("", c),
                Step::Delete(c) => ("d ", c),
            };
            s.push_str(pre);
            for l in c {
                s.push_str(&l.dimacs().to_string());
                s.push(' ');
            }
            s.push_str("0\n");
        }
        s
    }
}

/// The answer to a question.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Outcome {
    /// It holds for every value of the symbols (with a certificate, if asked for).
    Proved(Option<Certificate>),
    /// It fails at these values of the symbols (checked by evaluation).
    Refuted(Vec<(SymbolKey, BitVec)>),
    /// Not decided: why.
    Unknown(Unknown),
}

/// Why a question is not decided.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Unknown {
    /// The search reached a limit ([`Config::max_conflicts`] or
    /// [`Config::max_propagations`]) after this much work on the question: more may decide
    /// it, and a [`Question`] goes on from where it stopped.
    Budget {
        /// Conflicts met on the question.
        conflicts: u64,
        /// Propagations done on the question.
        propagations: u64,
    },
    /// The circuit passed [`Config::max_nodes`]: `nodes` had been built when blasting stopped.
    /// The same under any search budget with that cap.
    TooLarge {
        /// AIG nodes built.
        nodes: usize,
    },
    /// Something the prover does not reason about (an extension operation without an
    /// expansion, say). The same under any budget.
    Unsupported(String),
    /// A caller's deadline passed ([`crate::solve::Solver::check_within`]): more time may
    /// decide it. Unlike the budgets, this depends on timing.
    Deadline,
}

impl Unknown {
    /// Whether a larger search budget may decide the question ([`Unknown::Budget`]).
    pub fn is_budget(&self) -> bool {
        matches!(self, Unknown::Budget { .. })
    }
}

impl core::fmt::Display for Unknown {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Unknown::Budget {
                conflicts,
                propagations,
            } => write!(
                f,
                "no answer within {conflicts} conflicts ({propagations} propagations)"
            ),
            Unknown::Deadline => write!(f, "the deadline passed"),
            Unknown::TooLarge { nodes } => {
                write!(f, "the circuit is too large ({nodes} nodes built)")
            }
            Unknown::Unsupported(why) => f.write_str(why),
        }
    }
}

/// The work a question took, so far. Every count is of work done, not of time, and the same on
/// every run: a question asked the same way (in a context with the same history) reports the
/// same numbers, and the totals of one resumed in steps are those of one asked at once.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Stats {
    /// What simplifying the question took ([`Config::simplify`]).
    pub simplification: Simplification,
    /// What sweeping the circuit did ([`Config::sweeping`]); its conflicts, decisions,
    /// propagations and lemmas are also counted in the totals below.
    pub sweeping: Sweeping,
    /// AIG nodes of the circuit (inputs and gates).
    pub nodes: usize,
    /// Whether the circuit is of the question with its sums written again
    /// ([`Config::shared_sums`]), and not of the question as asked (where that changed
    /// nothing, or made a circuit past [`Config::max_nodes`]).
    pub rewritten: bool,
    /// Assignments evaluated before search, on words or the circuit ([`Config::samples`]).
    pub samples: u64,
    /// Variables of the clauses.
    pub vars: u32,
    /// Clauses of the question (not learned ones).
    pub clauses: usize,
    /// Learned clauses kept.
    pub learned: usize,
    /// Clauses learned in all, units included, whether kept or since deleted.
    pub lemmas: u64,
    /// Variables fixed for good: assigned with no decision made, by the clauses and the units
    /// learned so far. Of [`vars`](Self::vars), the part of the circuit the search has settled.
    pub fixed: usize,
    /// Conflicts.
    pub conflicts: u64,
    /// Decisions.
    pub decisions: u64,
    /// Propagations.
    pub propagations: u64,
    /// Searches run: [`Question::solve`] calls that searched (one that finds the question
    /// already decided, or that has a zero allowance, does not).
    pub searches: u32,
    /// The last search's conflicts: the marginal cost of its call. A search goes on from where
    /// the one before stopped, so these add up to [`conflicts`](Self::conflicts) and nothing
    /// is searched twice.
    pub last_conflicts: u64,
    /// The last search's decisions.
    pub last_decisions: u64,
    /// The last search's propagations (they add up to [`propagations`](Self::propagations)
    /// with the propagation of the clauses before any search).
    pub last_propagations: u64,
    /// Clauses the last search learned.
    pub last_lemmas: u64,
}

impl Stats {
    /// These counts without the last search's own ([`searches`](Self::searches) and the
    /// `last_*` fields cleared): the work done in all, which is the same for a question
    /// resumed in steps and one asked at once under their combined limits.
    pub fn totals(self) -> Stats {
        Stats {
            searches: 0,
            last_conflicts: 0,
            last_decisions: 0,
            last_propagations: 0,
            last_lemmas: 0,
            ..self
        }
    }
}

/// What sweeping a question's circuit did ([`Config::sweeping`]).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Sweeping {
    /// Whether the circuit was swept: simulated, and its candidate pairs proved.
    pub ran: bool,
    /// Whether the circuit was simulated and judged not worth sweeping: too few classes of
    /// nodes that agree join the two sides of an equality (see [`Config::sweeping`]).
    pub skipped: bool,
    /// Classes of the first simulation that join the two sides of an equality (of a question
    /// that is not one: classes of two nodes or more).
    pub crossings: u64,
    /// Nodes proved equal to an earlier node, or its complement, or to a constant.
    pub merged: u64,
    /// Candidate pairs a counterexample told apart.
    pub separated: u64,
    /// Candidate pairs left undecided within their own conflict cap.
    pub undecided: u64,
    /// The sweep's conflicts.
    pub conflicts: u64,
    /// The sweep's propagations.
    pub propagations: u64,
}

/// What simplifying a question with bitwright's own engine took ([`Config::simplify`]).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Simplification {
    /// Whether the engine ran on the question.
    pub ran: bool,
    /// The work it did, in the units of its budget ([`Config::simplify_budget`]): every
    /// field counted, capped or not. Work the engine finished on the same nodes earlier in the
    /// same context is remembered there and not done again.
    pub spent: crate::engine::Budget,
    /// The cap that stopped it, if one did. The rewrites it made until then are kept, and the
    /// rest of the question is blasted as it stands; a larger budget may settle more.
    pub stopped: Option<crate::engine::Exhausted>,
    /// Whether it decided the question (the simplified question is true).
    pub decided: bool,
}

impl Default for Simplification {
    /// The engine did not run.
    fn default() -> Self {
        Simplification {
            ran: false,
            spent: crate::engine::Budget::ZERO,
            stopped: None,
            decided: false,
        }
    }
}

/// The bits of expressions, blasted on demand.
pub(crate) struct Blaster<'c> {
    pub(crate) cx: &'c mut Context,
    pub(crate) g: Aig,
    bits: IdMap<u32, Bits>,
    /// Each symbol met, with its bits.
    pub(crate) symbols: Vec<(u32, Bits)>,
    selectors: Vec<L>,
    selector_hints: bool,
    input_cancellation: bool,
    join_factoring: bool,
    carry_save_multiplication: bool,
    max_nodes: usize,
    /// Blasting stopped at `max_nodes`.
    too_large: bool,
}

impl<'c> Blaster<'c> {
    pub(crate) fn new(cx: &'c mut Context, max_nodes: usize) -> Blaster<'c> {
        Blaster {
            cx,
            g: Aig::new(),
            bits: IdMap::default(),
            symbols: Vec::new(),
            selectors: Vec::new(),
            selector_hints: false,
            input_cancellation: false,
            join_factoring: false,
            carry_save_multiplication: false,
            max_nodes,
            too_large: false,
        }
    }

    /// A blaster that goes on from a circuit built before: its graph, the bits of the nodes
    /// blasted and the symbols met ([`into_parts`](Self::into_parts)).
    pub(crate) fn resume(
        cx: &'c mut Context,
        g: Aig,
        bits: IdMap<u32, Bits>,
        symbols: Vec<(u32, Bits)>,
        max_nodes: usize,
    ) -> Blaster<'c> {
        Blaster {
            g,
            bits,
            symbols,
            ..Blaster::new(cx, max_nodes)
        }
    }

    /// The circuit, to [`resume`](Self::resume) from.
    pub(crate) fn into_parts(self) -> (Aig, IdMap<u32, Bits>, Vec<(u32, Bits)>) {
        (self.g, self.bits, self.symbols)
    }

    /// The bits of node `root`.
    pub(crate) fn blast(&mut self, root: u32) -> Result<Bits, Error> {
        let bits = &self.bits;
        let order = self
            .cx
            .post_order_ids_pruned(&[root], |e| bits.contains_key(&e.index()));
        for i in order {
            if self.bits.contains_key(&i) {
                continue;
            }
            if self.g.len() > self.max_nodes {
                self.too_large = true;
                return Err(Error::Unsupported("the circuit is too large".into()));
            }
            let b = self.node(i)?;
            self.bits.insert(i, b);
        }
        Ok(self.bits[&root].clone())
    }

    fn node(&mut self, i: u32) -> Result<Bits, Error> {
        use blast::*;
        let n = self.cx.node(i);
        let w = usize::from(n.width);
        let get = |s: &Self, j: u32| s.bits[&j].clone();
        let g = &mut self.g;
        Ok(match n.op {
            OpCode::Const => konst(&self.cx.const_val(i).unwrap_or(BitVec::zero(Width::W1))),
            OpCode::Sym => {
                // Declarations are part of a symbol's meaning, including in certificate
                // mode. Only its unknown bits are inputs of the circuit.
                let known = self.cx.declared_at(i);
                let b: Bits = (0..w)
                    .map(|j| match known {
                        Some(k) if k.known_one().bit(j as u16) == Some(true) => aig::TRUE,
                        Some(k) if k.known_zero().bit(j as u16) == Some(true) => aig::FALSE,
                        _ => g.input(),
                    })
                    .collect();
                self.symbols.push((i, b.clone()));
                b
            }
            OpCode::Not => not(g, &self.bits[&n.a]),
            OpCode::Neg => {
                let a = get(self, n.a);
                neg(&mut self.g, &a)
            }
            OpCode::Popcnt => popcnt(g, &self.bits[&n.a]),
            OpCode::Clz => clz(g, &self.bits[&n.a]),
            OpCode::Ctz => ctz(g, &self.bits[&n.a]),
            OpCode::Bswap => bswap(&self.bits[&n.a]),
            OpCode::BitRev => bitrev(&self.bits[&n.a]),
            OpCode::Zext => {
                let mut a = get(self, n.a);
                a.resize(w, aig::FALSE);
                a
            }
            OpCode::Sext => {
                let mut a = get(self, n.a);
                let top = *a.last().unwrap_or(&aig::FALSE);
                a.resize(w, top);
                a
            }
            OpCode::Extract => {
                let a = get(self, n.a);
                let lo = n.b as usize;
                a[lo..lo + w].to_vec()
            }
            OpCode::Concat => {
                let (hi, mut lo) = (get(self, n.a), get(self, n.b));
                lo.extend(hi);
                lo
            }
            OpCode::Select => {
                let (c, t, e) = (get(self, n.a)[0], get(self, n.b), get(self, n.c));
                mux(&mut self.g, c, &t, &e)
            }
            OpCode::Eq | OpCode::Ne | OpCode::Ult | OpCode::Ule | OpCode::Slt | OpCode::Sle => {
                let (a, b) = (get(self, n.a), get(self, n.b));
                let g = &mut self.g;
                let r = match n.op {
                    OpCode::Eq if self.join_factoring => eq_factored(g, &a, &b),
                    OpCode::Ne if self.join_factoring => eq_factored(g, &a, &b) ^ 1,
                    OpCode::Eq => eq(g, &a, &b),
                    OpCode::Ne => eq(g, &a, &b) ^ 1,
                    OpCode::Ult => ult(g, &a, &b),
                    OpCode::Ule => ule(g, &a, &b),
                    OpCode::Slt => slt(g, &a, &b),
                    _ => sle(g, &a, &b),
                };
                vec![r]
            }
            op if op.as_bin().is_some() => {
                let (a, b) = (get(self, n.a), get(self, n.b));
                if self.selector_hints && matches!(op, OpCode::Shl | OpCode::LShr | OpCode::AShr) {
                    let unknown: Vec<_> = b
                        .iter()
                        .copied()
                        .filter(|&l| l > aig::TRUE)
                        .take(5)
                        .collect();
                    if !unknown.is_empty() && unknown.len() <= 4 {
                        self.selectors.extend(unknown);
                    }
                }
                let g = &mut self.g;
                match op {
                    OpCode::Add => add(g, &a, &b),
                    OpCode::Sub => sub(g, &a, &b),
                    OpCode::Mul if self.carry_save_multiplication => mul_carry_save(g, &a, &b),
                    OpCode::Mul => mul(g, &a, &b),
                    OpCode::UMulHi => mulhi(g, &a, &b, false),
                    OpCode::SMulHi => mulhi(g, &a, &b, true),
                    OpCode::UDiv => udivrem(g, &a, &b).0,
                    OpCode::URem => udivrem(g, &a, &b).1,
                    OpCode::SDiv => sdiv(g, &a, &b),
                    OpCode::SRem => srem(g, &a, &b),
                    OpCode::And => and(g, &a, &b),
                    OpCode::Or => or(g, &a, &b),
                    OpCode::Xor if self.input_cancellation => xor_cancel_input(g, &a, &b),
                    OpCode::Xor => xor(g, &a, &b),
                    OpCode::Shl => shift(g, &a, &b, true, aig::FALSE),
                    OpCode::LShr => shift(g, &a, &b, false, aig::FALSE),
                    OpCode::AShr => {
                        let s = *a.last().unwrap_or(&aig::FALSE);
                        shift(g, &a, &b, false, s)
                    }
                    OpCode::RotL => rotate(g, &a, &b, true),
                    OpCode::RotR => rotate(g, &a, &b, false),
                    OpCode::Pdep => pdep(g, &a, &b),
                    _ => pext(g, &a, &b),
                }
            }
            op if op.as_ext().is_some() => self.ext(i)?,
            _ => {
                let kids: Vec<Bits> = n.children().map(|c| self.bits[&c].clone()).collect();
                fp::blast(self, i, &kids)?
            }
        })
    }

    /// An extension output, through the operation's expansion.
    fn ext(&mut self, i: u32) -> Result<Bits, Error> {
        let n = self.cx.node(i);
        let Some((_, k)) = n.op.as_ext() else {
            return Err(Error::Unsupported("not an extension output".into()));
        };
        let args: Vec<Expr> = n.children().map(|c| self.cx.handle(c)).collect();
        let reg = self
            .cx
            .registry
            .clone()
            .ok_or_else(|| Error::Unsupported("an extension without its registry".into()))?;
        let op = reg
            .op_at(n.aux)
            .ok_or_else(|| Error::Unsupported("an extension without its operation".into()))?;
        let Some(ex) = op.expand(self.cx, &args) else {
            return Err(Error::Unsupported(format!(
                "`{}` has no expansion to reason about",
                op.name()
            )));
        };
        let outs = ex?;
        let e = self.cx.id(outs[k])?;
        self.blast(e)
    }

    /// Why blasting failed with `e`: [`Unknown::TooLarge`] past `max_nodes`, else the reason
    /// of an unsupported operation. Other errors are errors.
    fn unknown(&self, e: Error) -> Result<Unknown, Error> {
        match e {
            _ if self.too_large => Ok(Unknown::TooLarge {
                nodes: self.g.len(),
            }),
            Error::Unsupported(why) => Ok(Unknown::Unsupported(why)),
            e => Err(e),
        }
    }
}

/// Where a SAT-solved question stands.
struct Search {
    solver: Solver,
    cnf: Cnf,
    /// What the sweep cost ([`Config::sweeping`]), counted in the totals.
    swept: sweep::Work,
}

/// A question, blasted and encoded once, then decided in as many steps as its caller likes: a
/// search that ends on its limits stops where it is, keeping what it learned, and the next
/// [`solve`](Self::solve) goes on from there. Asking under 5,000 conflicts, then 15,000 more,
/// costs what asking under 20,000 once does, and answers the same.
///
/// ```
/// use bitwright::prove::{Config, Limits, Outcome, Question};
/// use bitwright::{Context, ParseOptions, Width};
///
/// let mut cx = Context::new();
/// let o = ParseOptions::width(Width::W16);
/// let p = cx.parse("x * x != 0x1234", &o)?;
/// // Without the engine's simplification first, which decides it by residues.
/// let cfg = Config::default().with_samples(0).with_simplify(false);
/// let mut q = Question::valid(&mut cx, p, &cfg)?;
/// let mut out = q.solve(&mut cx, Limits::conflicts(10))?;
/// while let Outcome::Unknown(why) = &out {
///     assert!(why.is_budget());
///     out = q.solve(&mut cx, Limits::conflicts(10))?;
/// }
/// assert!(matches!(out, Outcome::Proved(_))); // 0x1234 is not a square mod 2^16
/// assert!(q.stats().conflicts > 0);
/// # Ok::<(), bitwright::Error>(())
/// ```
pub struct Question {
    /// The question as asked (with the constraints, as `¬(c1 ∧ …) ∨ p`), checked by evaluation.
    root: Expr,
    /// Each symbol of the question with its bits (one the circuit does not read takes its
    /// declared ones, or 0 without a declaration).
    symbols: Vec<(SymbolKey, Width, Bits)>,
    search: Option<Box<Search>>,
    outcome: Option<Outcome>,
    stats: Stats,
}

impl core::fmt::Debug for Question {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Question")
            .field("outcome", &self.outcome)
            .field("stats", &self.stats)
            .finish_non_exhaustive()
    }
}

impl Question {
    /// Whether the 1-bit `p` is true for every value of its symbols agreeing with their
    /// declared known bits.
    pub fn valid(cx: &mut Context, p: Expr, cfg: &Config) -> Result<Question, Error> {
        Question::valid_under(cx, p, None, cfg)
    }

    /// Whether `a` and `b` (of one width) are equal for every value of their symbols agreeing
    /// with their declared known bits.
    pub fn equal(cx: &mut Context, a: Expr, b: Expr, cfg: &Config) -> Result<Question, Error> {
        let (ai, bi) = (cx.id(a)?, cx.id(b)?);
        if cx.wid(ai) != cx.wid(bi) {
            return Err(crate::WidthError::Mismatch {
                left: cx.wid(ai),
                right: cx.wid(bi),
            }
            .into());
        }
        let p = cx.c_cmp(crate::CmpOp::Eq, ai, bi)?;
        let p = cx.handle(p);
        Question::valid(cx, p, cfg)
    }

    /// Whether `p` is true wherever the constraints of `assumptions` hold. Complete original
    /// facts are retained, including partial masks, signed/unsigned
    /// intervals and unsigned strides; they remain in certificates and counterexample replay.
    /// The question is simplified (see [`Config::simplify`]), optionally sampled at the word level, then
    /// blasted, sampled (see [`Config::samples`]) and encoded here; each stage may decide it.
    pub fn valid_under(
        cx: &mut Context,
        p: Expr,
        assumptions: Option<&Assumptions>,
        cfg: &Config,
    ) -> Result<Question, Error> {
        Self::valid_under_with_pairs(cx, p, assumptions, &[], cfg)
    }

    /// Ask the original question after applying explicitly supplied, exhaustively checked
    /// finite-domain pair facts. Verification costs are separate from this query's budget.
    /// Models are replayed on the original predicate. Certificate requests retain the
    /// original bit-blast path and do not use these word-level facts.
    pub fn valid_with_pairs(
        cx: &mut Context,
        p: Expr,
        pairs: &[finite::CheckedPair],
        cfg: &Config,
    ) -> Result<Question, Error> {
        Self::valid_under_with_pairs(cx, p, None, pairs, cfg)
    }

    /// [`valid_with_pairs`](Self::valid_with_pairs) under explicit assumptions.
    pub fn valid_under_with_pairs(
        cx: &mut Context,
        p: Expr,
        assumptions: Option<&Assumptions>,
        pairs: &[finite::CheckedPair],
        cfg: &Config,
    ) -> Result<Question, Error> {
        let pi = cx.id(p)?;
        if cx.wid(pi) != 1 {
            return Err(crate::WidthError::Mismatch {
                left: 1,
                right: cx.wid(pi),
            }
            .into());
        }
        let mut q = Question {
            root: p,
            symbols: Vec::new(),
            search: None,
            outcome: None,
            stats: Stats::default(),
        };
        let decided = |mut q: Question, o: Outcome| {
            q.outcome = Some(o);
            Ok(q)
        };
        // Exact original constraints, including masks, signed/unsigned bounds and strides.
        let mut cons: Vec<u32> = Vec::new();
        if let Some(a) = assumptions {
            for predicate in a.predicates(cx)? {
                cons.push(cx.id(predicate)?);
            }
        }
        // The root checked by evaluation: `p` where the constraints hold, as `¬(c1 ∧ …) ∨ p`.
        let mut root = pi;
        for &c in &cons {
            let nc = cx.c_un(crate::UnOp::Not, c)?;
            root = cx.c_bin(crate::BinOp::Or, nc, root)?;
        }
        q.root = cx.handle(root);
        // The question simplified (not for a certificate, which must be of the question itself).
        let mut goal_node = pi;
        if !cfg.certificate {
            for pair in pairs {
                let rewritten = pair.simplify(cx, cx.handle(goal_node))?;
                goal_node = cx.id(rewritten)?;
            }
            if cx
                .const_val(goal_node)
                .is_some_and(|value| !value.is_zero())
            {
                return decided(q, Outcome::Proved(None));
            }
        }
        if cfg.simplify && !cfg.certificate {
            let mut spent = crate::engine::Allowance::new(crate::engine::Budget::UNLIMITED);
            let run = crate::engine::Run::default()
                .with_per_call(cfg.simplify_budget)
                .with_allowance(&mut spent);
            let run = match assumptions {
                Some(a) => run.with_assumptions(a),
                None => run,
            };
            let goal = cx.handle(goal_node);
            let out = simplifier_of(cfg.strict, cfg.proved_words)
                .run(cx, &[goal], run)?
                .roots[0];
            let s = cx.id(out.expr)?;
            let proved = cx.const_val(s).is_some_and(|v| !v.is_zero());
            q.stats.simplification = Simplification {
                ran: true,
                spent: spent.spent(),
                stopped: match out.end {
                    crate::engine::End::BudgetTerminated(why) => Some(why),
                    _ => None,
                },
                decided: proved,
            };
            if proved {
                return decided(q, Outcome::Proved(None));
            }
            // A result that relies on constraints holds where they do, which is all a proof
            // under them needs.
            goal_node = s;
        }
        if cfg.divisions && !cfg.simplify && !cfg.certificate {
            let run = crate::engine::Run::default().with_per_call(cfg.simplify_budget);
            let run = match assumptions {
                Some(a) => run.with_assumptions(a),
                None => run,
            };
            let goal = cx.handle(goal_node);
            let out = divisions_only().run(cx, &[goal], run)?.roots[0];
            goal_node = cx.id(out.expr)?;
            if cx.const_val(goal_node).is_some_and(|v| !v.is_zero()) {
                q.stats.rewritten = true;
                return decided(q, Outcome::Proved(None));
            }
        }
        let mut word_sampled = false;
        if (cfg.word_sampling || cfg.sample_mode == SampleMode::Words)
            && cfg.samples != 0
            && let Some(trial) = sample_words::try_sample(cx, goal_node, &cons, assumptions, cfg)
        {
            q.stats.samples = trial.samples;
            word_sampled = true;
            if let Some(mut model) = trial.model {
                complete_model(cx, q.root, &mut model)?;
                let outcome = q.refuted(cx, model)?;
                return decided(q, outcome);
            }
            if trial.complete && !cfg.certificate {
                return decided(q, Outcome::Proved(None));
            }
        }
        // Every legal assignment, when there are few enough. A proof that asks for a
        // certificate takes it from the circuit below, which is checked independently.
        let mut exhausted = false;
        if cfg.exhaustive_inputs != 0
            && let Some((failure, evaluated)) =
                sample_words::try_exhaust(cx, goal_node, &cons, assumptions, cfg.exhaustive_inputs)
        {
            q.stats.samples += evaluated;
            match failure {
                Some(mut model) => {
                    complete_model(cx, q.root, &mut model)?;
                    let outcome = q.refuted(cx, model)?;
                    return decided(q, outcome);
                }
                None if !cfg.certificate => return decided(q, Outcome::Proved(None)),
                None => exhausted = true,
            }
        }
        // The question as asked, where writing its sums again changes it.
        let asked = goal_node;
        if cfg.shared_sums && !cfg.certificate {
            goal_node = sums::shared(cx, goal_node)?;
            if cx
                .const_val(goal_node)
                .is_some_and(|value| !value.is_zero())
            {
                q.stats.rewritten = true;
                return decided(q, Outcome::Proved(None));
            }
        }
        let (mut b, goal, extra) = loop {
            let constant_goal = cuts::constant_true(cx, goal_node);
            let mut b = Blaster::new(cx, cfg.max_nodes);
            b.selector_hints = cfg.selector_branching;
            b.input_cancellation = cfg.input_cancellation;
            b.join_factoring = cfg.join_factoring;
            b.carry_save_multiplication = cfg.carry_save_multiplication;
            if constant_goal {
                b.bits.insert(goal_node, vec![aig::TRUE]);
            }
            let mut blasted = || -> Result<(L, Vec<L>), Error> {
                let goal = b.blast(goal_node)?[0];
                let mut extra = Vec::new();
                for &c in &cons {
                    extra.push(b.blast(c)?[0]);
                }
                Ok((goal, extra))
            };
            match blasted() {
                Ok((goal, extra)) if b.g.len() <= cfg.max_nodes => break (b, goal, extra),
                // (Written again the circuit is too large: the question as asked, then.)
                _ if goal_node != asked => goal_node = asked,
                Ok(_) => {
                    let why = Unknown::TooLarge { nodes: b.g.len() };
                    return decided(q, Outcome::Unknown(why));
                }
                Err(e) => {
                    let why = b.unknown(e)?;
                    return decided(q, Outcome::Unknown(why));
                }
            }
        };
        q.stats.nodes = b.g.len();
        q.stats.rewritten = goal_node != asked;
        // Every symbol of the question, with its bits if the circuit reads it. (Marked by
        // symbol index: a search of the list per symbol took 12 s on a question of 64 000
        // symbols that simplification had already decided.)
        let mut listed = vec![false; b.cx.symbol_count()];
        for (s, bits) in &b.symbols {
            let h = b.cx.handle(*s);
            let id =
                b.cx.symbol_id(h)?
                    .ok_or_else(|| Error::Contract("a symbol without its key".into()))?;
            let key =
                b.cx.symbol_key(id)
                    .cloned()
                    .ok_or_else(|| Error::Contract("a symbol without its key".into()))?;
            listed[id.index() as usize] = true;
            q.symbols.push((key, b.cx.width_of(*s), bits.clone()));
        }
        for id in b.cx.symbols_in(&[q.root])? {
            if !core::mem::replace(&mut listed[id.index() as usize], true)
                && let (Some(k), Some(w)) = (b.cx.symbol_key(id).cloned(), b.cx.symbol_width(id))
            {
                let bits =
                    b.cx.find_symbol(&k)
                        .and_then(|e| b.cx.declared_at(e.index()))
                        .map(|known| blast::konst(&known.known_one()))
                        .unwrap_or_default();
                q.symbols.push((k, w, bits));
            }
        }
        if exhausted {
            let exhaustion = Exhaustion::of(&b.g, goal, &extra);
            if exhaustion.inputs() <= u32::from(cfg.exhaustive_inputs.min(63)) {
                let cert = Certificate {
                    vars: 0,
                    clauses: Vec::new(),
                    proof: Vec::new(),
                    exhaustion: Some(exhaustion),
                };
                return decided(q, Outcome::Proved(Some(cert)));
            }
        }
        // Sampled: a lane where the constraints hold and the goal does not refutes it.
        let batches = if word_sampled {
            0
        } else {
            cfg.samples.div_ceil(64)
        };
        for batch in 0..batches {
            let vals = b.g.eval_words(|k| match cfg.sample_mode {
                SampleMode::Random => sample(batch, k),
                SampleMode::Small | SampleMode::Words => small_sample(batch, k),
            });
            q.stats.samples += 64;
            let mut bad = !Aig::word(&vals, goal);
            for &e in &extra {
                bad &= Aig::word(&vals, e);
            }
            if bad != 0 {
                let lane = bad.trailing_zeros();
                let ce = Question::counterexample(&q.symbols, |l| {
                    (Aig::word(&vals, l) >> lane) & 1 == 1
                });
                let o = q.refuted(b.cx, ce)?;
                return decided(q, o);
            }
        }
        let mut solver = Solver::new();
        if cfg.certificate {
            solver.log_proof();
        }
        let mut roots = vec![goal];
        roots.extend_from_slice(&extra);
        let mut cnf = Cnf::encode_with_xor3(
            &b.g,
            &roots,
            &mut solver,
            cfg.certificate,
            cfg.xor3_encoding,
        );
        for &e in &extra {
            cnf.assert(e, &mut solver);
        }
        cnf.assert(goal ^ 1, &mut solver);
        let mut asserted = vec![goal ^ 1];
        asserted.extend_from_slice(&extra);
        relations::strengthen(&b.g, &asserted, &cnf, &mut solver, cfg.relational_lemmas);
        if cfg.selector_branching {
            for &l in &b.selectors {
                if let Some(l) = cnf.mapped_lit(l) {
                    solver.prefer_selector(l);
                }
            }
        }
        // Swept once, as part of preparing the question: within half of the configured limits,
        // whatever the searches' own, so a question resumed in steps is swept as one asked at
        // once.
        let mut swept = sweep::Work::default();
        if cfg.sweeping {
            // The two sides of an equality, whose inner nodes a sweep can merge across.
            let sides = match b.cx.node(goal_node) {
                n if n.op == OpCode::Eq => match (b.bits.get(&n.a), b.bits.get(&n.b)) {
                    (Some(x), Some(y)) => Some((x.clone(), y.clone())),
                    _ => None,
                },
                _ => None,
            };
            let pending = sweep::Pending {
                sides,
                words: b.symbols.iter().map(|(_, bits)| bits.clone()).collect(),
                aig: core::mem::take(&mut b.g),
                roots,
                xor3: cfg.xor3_encoding,
                certificate: cfg.certificate,
            };
            let share = Limits {
                conflicts: cfg.max_conflicts / 2,
                propagations: cfg.max_propagations / 2,
            };
            swept = sweep::sweep(&pending, &cnf, &mut solver, share);
            q.stats.sweeping = Sweeping {
                ran: swept.ran,
                skipped: swept.skipped,
                crossings: swept.crossings,
                merged: swept.merged,
                separated: swept.separated,
                undecided: swept.undecided,
                conflicts: swept.conflicts,
                propagations: swept.propagations,
            };
        }
        q.stats.vars = solver.num_vars();
        q.stats.clauses = cnf.emitted();
        q.stats.learned = solver.num_learnts();
        q.stats.lemmas = solver.lemmas + swept.lemmas;
        q.stats.fixed = solver.num_fixed();
        q.stats.conflicts = swept.conflicts;
        q.stats.decisions = swept.decisions;
        q.stats.propagations = solver.propagations + swept.propagations;
        q.search = Some(Box::new(Search { solver, cnf, swept }));
        Ok(q)
    }

    /// Searches within `limits` more work (counted from this call): the answer, or
    /// [`Unknown::Budget`] with the work done on the question so far, and the next call goes on
    /// from there. Once decided (here or when built), the answer is kept and returned again.
    /// `cx` is the context the question was built in.
    pub fn solve(&mut self, cx: &mut Context, limits: Limits) -> Result<Outcome, Error> {
        if let Some(o) = &self.outcome {
            return Ok(o.clone());
        }
        let Some(s) = self.search.as_mut() else {
            return Err(Error::Contract(
                "a question neither decided nor open".into(),
            ));
        };
        // The question's totals: its solver's and its sweep's.
        let totals = |s: &Search| {
            (
                s.solver.conflicts + s.swept.conflicts,
                s.solver.decisions + s.swept.decisions,
                s.solver.propagations + s.swept.propagations,
                s.solver.lemmas + s.swept.lemmas,
            )
        };
        let before = totals(s);
        // A zero allowance pauses the question without searching.
        let searching = limits.conflicts != 0 && limits.propagations != 0;
        let answer = s.solver.solve_within(limits);
        let after = totals(s);
        self.stats.learned = s.solver.num_learnts();
        self.stats.lemmas = after.3;
        self.stats.fixed = s.solver.num_fixed();
        self.stats.conflicts = after.0;
        self.stats.decisions = after.1;
        self.stats.propagations = after.2;
        if searching {
            self.stats.searches += 1;
            self.stats.last_conflicts = after.0 - before.0;
            self.stats.last_decisions = after.1 - before.1;
            self.stats.last_propagations = after.2 - before.2;
            self.stats.last_lemmas = after.3 - before.3;
        }
        let o = match answer {
            Answer::Unknown => {
                return Ok(Outcome::Unknown(Unknown::Budget {
                    conflicts: after.0,
                    propagations: after.2,
                }));
            }
            Answer::Unsat => {
                let cert = s.solver.take_proof().map(|proof| Certificate {
                    vars: s.solver.num_vars(),
                    clauses: core::mem::take(&mut s.cnf.clauses),
                    proof,
                    exhaustion: None,
                });
                Outcome::Proved(cert)
            }
            Answer::Sat(model) => {
                let cnf = &s.cnf;
                let ce = Question::counterexample(&self.symbols, |l| cnf.value(l, &model));
                self.refuted(cx, ce)?
            }
        };
        self.search = None;
        self.outcome = Some(o.clone());
        Ok(o)
    }

    /// The answer, once decided.
    pub fn outcome(&self) -> Option<&Outcome> {
        self.outcome.as_ref()
    }

    /// The work done on the question so far.
    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// The counterexample an assignment of the circuit's inputs gives.
    fn counterexample(symbols: &[(SymbolKey, Width, Bits)], bit: impl Fn(L) -> bool) -> Model {
        symbols
            .iter()
            .map(|(k, w, bits)| {
                let mut limbs = [0u64; 8];
                for (j, &b) in bits.iter().enumerate() {
                    if bit(b) {
                        limbs[j / 64] |= 1 << (j % 64);
                    }
                }
                (k.clone(), BitVec::wrapping_from_limbs(*w, &limbs))
            })
            .collect()
    }

    /// `Refuted(ce)`, checked by bitwright's evaluator: a solver or blaster bug cannot produce a
    /// false refutation unnoticed.
    fn refuted(&self, cx: &mut Context, ce: Model) -> Result<Outcome, Error> {
        // (By key, the first value given for one: a model lists every symbol of the question.)
        let mut env: std::collections::HashMap<SymbolKey, BitVec> =
            std::collections::HashMap::with_capacity(ce.len());
        for (k, v) in &ce {
            env.entry(k.clone()).or_insert(*v);
        }
        let v = cx.eval(&[self.root], &env)?[0];
        if v.is_zero() {
            Ok(Outcome::Refuted(ce))
        } else {
            Err(Error::Contract(format!(
                "the prover's counterexample does not refute {}",
                cx.display(self.root)
            )))
        }
    }
}

/// Simplification can omit original symbols: supply values consistent with their declarations
/// before replaying the original constrained predicate.
fn complete_model(cx: &mut Context, root: Expr, model: &mut Model) -> Result<(), Error> {
    let mut given: std::collections::HashSet<SymbolKey> =
        model.iter().map(|(k, _)| k.clone()).collect();
    for id in cx.symbols_in(&[root])? {
        let key = cx.symbol_key(id).unwrap().clone();
        if given.insert(key.clone()) {
            let symbol = cx.find_symbol(&key).unwrap();
            let value = cx.declared_known(symbol)?.map_or_else(
                || BitVec::zero(cx.symbol_width(id).unwrap()),
                |k| k.known_one(),
            );
            model.push((key, value));
        }
    }
    Ok(())
}

/// The 64 consecutive assignments `64*batch .. 64*batch+64`, transposed into input words.
fn small_sample(batch: u32, k: u32) -> u64 {
    const LOW: [u64; 6] = [
        0xaaaa_aaaa_aaaa_aaaa,
        0xcccc_cccc_cccc_cccc,
        0xf0f0_f0f0_f0f0_f0f0,
        0xff00_ff00_ff00_ff00,
        0xffff_0000_ffff_0000,
        0xffff_ffff_0000_0000,
    ];
    if k < 6 {
        LOW[k as usize]
    } else if k - 6 < 32 && (batch >> (k - 6)) & 1 == 1 {
        u64::MAX
    } else {
        0
    }
}

/// Input `k`'s word in sample batch `batch` (splitmix64 of the pair); batch 0's lanes 0 and 1
/// are all zeros and all ones.
fn sample(batch: u32, k: u32) -> u64 {
    let mut z = (u64::from(batch) << 32 | u64::from(k)).wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^= z >> 31;
    if batch == 0 { (z & !0b11) | 0b10 } else { z }
}

/// Whether the 1-bit `p` is true for every value of its symbols agreeing with their declared
/// known bits.
pub fn valid(cx: &mut Context, p: Expr, cfg: &Config) -> Result<Outcome, Error> {
    valid_under(cx, p, None, cfg)
}

/// Whether `p` is true wherever the constraints of `assumptions` and the symbols' declared
/// known bits hold.
pub fn valid_under(
    cx: &mut Context,
    p: Expr,
    assumptions: Option<&Assumptions>,
    cfg: &Config,
) -> Result<Outcome, Error> {
    Question::valid_under(cx, p, assumptions, cfg)?.solve(cx, cfg.limits())
}

/// Whether `a` and `b` (of one width) are equal for every value of their symbols agreeing with
/// their declared known bits.
pub fn equal(cx: &mut Context, a: Expr, b: Expr, cfg: &Config) -> Result<Outcome, Error> {
    Question::equal(cx, a, b, cfg)?.solve(cx, cfg.limits())
}

/// Values of symbols, as a counterexample or a model gives them.
pub type Model = Vec<(SymbolKey, BitVec)>;

/// A value of the symbols that makes the 1-bit `p` true, if there is one: `Refuted` of `¬p`
/// read back as a model (`Ok(Some)`), `Ok(None)` when `p` is unsatisfiable, and `Err` with the
/// reason when not decided.
pub fn satisfy(
    cx: &mut Context,
    p: Expr,
    cfg: &Config,
) -> Result<Result<Option<Model>, Unknown>, Error> {
    let np = cx.un(crate::UnOp::Not, p)?;
    Ok(match valid(cx, np, cfg)? {
        Outcome::Proved(_) => Ok(None),
        Outcome::Refuted(m) => Ok(Some(m)),
        Outcome::Unknown(why) => Err(why),
    })
}

/// The prover the engine's passes are given ([`crate::engine::oracle`]): the circuit and the
/// search alone, without the simplifier (which is the engine that asks).
pub(crate) fn circuit_equality(
    cx: &mut Context,
    a: Expr,
    b: Expr,
    caps: &crate::engine::oracle::EqualityCaps,
) -> Result<crate::engine::oracle::EqualityAnswer, Error> {
    use crate::engine::oracle::{EqualityAnswer, EqualityVerdict};
    let cfg = Config::default()
        .with_simplify(false)
        .with_certificate(false)
        .with_samples(caps.samples)
        .with_max_nodes(caps.max_nodes)
        .with_max_conflicts(u64::MAX)
        .with_max_propagations(caps.max_propagations);
    let mut q = Question::equal(cx, a, b, &cfg)?;
    let out = q.solve(cx, cfg.limits())?;
    let stats = q.stats();
    let (verdict, nodes) = match out {
        Outcome::Proved(_) => (EqualityVerdict::Proved, stats.nodes),
        Outcome::Refuted(_) => (EqualityVerdict::Refuted, stats.nodes),
        Outcome::Unknown(Unknown::Budget { .. }) => (EqualityVerdict::Budget, stats.nodes),
        Outcome::Unknown(Unknown::TooLarge { nodes }) => (EqualityVerdict::Unknown, nodes),
        Outcome::Unknown(_) => (EqualityVerdict::Unknown, stats.nodes),
    };
    Ok(EqualityAnswer {
        verdict,
        nodes,
        propagations: stats.propagations,
    })
}
