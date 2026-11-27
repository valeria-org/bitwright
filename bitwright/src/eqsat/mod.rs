//! The equality-saturation search service (feature `eqsat`, default off). See `docs/design.md`
//! §10.
//!
//! A bounded *alternative-expression search* over immutable graphs, not a phase: the host
//! decides when (output or checkpoint boundaries, never routine maintenance), which roots, and
//! which allowance. By default ([`Fragment::conservative`]), admitted equations are proven,
//! unconditional, of one width, and in the conservative fragment `+ − * & | ^ neg ~`; opting into
//! [`Fragment::extended`] admits widths `1..=512`, mixed-width casts (`extract`, `zext`, `sext`,
//! `concat`), shifts, rotates, bit-ops, comparisons, `select`, and [`Facts`]-guarded
//! rules. An extracted expression is a **candidate** the host's own profitability and verification
//! gates decide to use.
//!
//! ```
//! use bitwright::eqsat::{SaturateConfig, Saturator, SearchRun};
//! use bitwright::{Context, ParseOptions, Width};
//!
//! let (sat, _report) = Saturator::builtin_groups(&["eqsat.distrib"], SaturateConfig::default());
//! let mut cx = Context::new();
//! // Factoring needs distributivity backwards, which a directed simplifier never does. The
//! // search saturates, so the candidate is published.
//! let e = cx.parse("x * y + x * z", &ParseOptions::width(Width::W32))?;
//! let out = sat.search(&mut cx, &[e], SearchRun::default())?;
//! let want = cx.parse("x * (y + z)", &ParseOptions::width(Width::W32))?;
//! assert_eq!(out.roots[0].candidate, Some(want));
//! # Ok::<(), bitwright::Error>(())
//! ```

mod egraph;
mod extract;
mod pattern;
#[cfg(test)]
mod tests;

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use egraph::{ClassId, EGraph, ENode, EOp, Halt};
use pattern::{Identity, MatchOut};

use crate::engine::budget::Meter;
use crate::engine::{Admission, Allowance, Budget, BuildError, Cap, Deadline, Exhausted};
use crate::error::Error;
use crate::expr::{Context, Expr, FnEnv, OpCode};
use crate::facts::Facts;
use crate::hash::{IdMap, combine};
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::rules::{Ledger, RuleProgram};
use crate::{BitVec, SymbolKey, Width};

/// An operator shape scored by a [`CostModel`].
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum CostOp {
    /// A bit-vector constant.
    Const,
    /// A symbol (or an opaque atomized subterm).
    Symbol,
    /// A unary operator.
    Un(UnOp),
    /// A binary operator.
    Bin(BinOp),
    /// A 1-bit comparison.
    Cmp(CmpOp),
    /// Zero extension from `from` bits to `to` bits.
    Zext {
        /// Source width.
        from: Width,
        /// Target width.
        to: Width,
    },
    /// Sign extension from `from` bits to `to` bits.
    Sext {
        /// Source width.
        from: Width,
        /// Target width.
        to: Width,
    },
    /// Bit slice `[lo, lo + width)` extracted from a `from`-bit value.
    Extract {
        /// Source width.
        from: Width,
        /// Lowest extracted bit.
        lo: u16,
        /// Extracted slice width.
        width: Width,
    },
    /// Concatenation of a `hi`-bit value above a `lo`-bit value.
    Concat {
        /// High operand width.
        hi: Width,
        /// Low operand width.
        lo: Width,
    },
    /// Conditional `select(cond, then, els)` producing a `Width`-bit value.
    Select(Width),
}

/// How extraction accounts for subterms used more than once.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, Hash)]
pub enum ExtractionMode {
    /// Sum every subterm occurrence independently (tree cost).
    #[default]
    Tree,
    /// Count shared equivalence classes once across the extracted DAG (and across roots of the
    /// search batch).
    Dag,
}

type CustomCostFn = Arc<dyn Fn(CostOp, Width) -> u64 + Send + Sync>;

#[derive(Clone)]
enum CostKind {
    AstSize,
    Custom { id: u64, f: CustomCostFn },
}

/// Structural or host-supplied operator cost model and [`ExtractionMode`] for equality-saturation
/// extraction.
///
/// Every operator weight is positive (`>= 1`; `0` returned by a custom callback is clamped to
/// `1`), guaranteeing acyclic extraction even when the e-graph contains cyclic equivalences.
#[derive(Clone)]
pub struct CostModel {
    kind: CostKind,
    mode: ExtractionMode,
}

impl Default for CostModel {
    fn default() -> Self {
        Self::ast_size()
    }
}

impl core::fmt::Debug for CostModel {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let kind = match &self.kind {
            CostKind::AstSize => "ast_size",
            CostKind::Custom { .. } => "custom",
        };
        f.debug_struct("CostModel")
            .field("kind", &kind)
            .field("mode", &self.mode)
            .finish()
    }
}

impl CostModel {
    /// Unit node weight (`1` per node) under [`ExtractionMode::Tree`] (the default).
    pub fn ast_size() -> CostModel {
        CostModel {
            kind: CostKind::AstSize,
            mode: ExtractionMode::Tree,
        }
    }

    /// Unit node weight (`1` per unique node) under [`ExtractionMode::Dag`].
    pub fn dag_size() -> CostModel {
        CostModel {
            kind: CostKind::AstSize,
            mode: ExtractionMode::Dag,
        }
    }

    /// Host-supplied operator weights (`width` is the node's result width). Any weight of `0` is
    /// clamped to `1` so cyclic equivalence classes always extract to acyclic expressions.
    pub fn custom(f: impl Fn(CostOp, Width) -> u64 + Send + Sync + 'static) -> CostModel {
        static NEXT_ID: AtomicU64 = AtomicU64::new(1);
        CostModel {
            kind: CostKind::Custom {
                id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
                f: Arc::new(f),
            },
            mode: ExtractionMode::Tree,
        }
    }

    /// Sets the [`ExtractionMode`] (`Tree` or `Dag`).
    #[must_use]
    pub fn with_mode(mut self, mode: ExtractionMode) -> CostModel {
        self.mode = mode;
        self
    }

    /// The active [`ExtractionMode`].
    pub fn mode(&self) -> ExtractionMode {
        self.mode
    }

    /// The positive weight (`>= 1`) assigned to `(op, width)`.
    pub fn cost(&self, op: CostOp, width: Width) -> u64 {
        match &self.kind {
            CostKind::AstSize => 1,
            CostKind::Custom { f, .. } => f(op, width).max(1),
        }
    }

    pub(crate) fn is_default_ast_tree(&self) -> bool {
        matches!(self.kind, CostKind::AstSize) && self.mode == ExtractionMode::Tree
    }

    fn epoch_mix(&self, base: u64) -> u64 {
        if self.is_default_ast_tree() {
            return base;
        }
        let mode_tag = match self.mode {
            ExtractionMode::Tree => 1u64,
            ExtractionMode::Dag => 2u64,
        };
        let kind_tag = match &self.kind {
            CostKind::AstSize => 0u64,
            CostKind::Custom { id, .. } => *id,
        };
        combine(combine(base, mode_tag), kind_tag)
    }
}

/// The operators and widths the search accepts.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Fragment {
    /// The widest expression node admitted.
    pub max_width: u16,
    /// Whether mixed-width casts, shifts/rotates, bit-ops, comparisons, `select`, multi-width
    /// equations, and [`Facts`]-guarded rules are admitted.
    pub extended_ops: bool,
}

impl Fragment {
    /// Widths 1..=128, one width per root, `+ − * & | ^`, unary `−` and `~`, constants and
    /// symbols.
    pub fn conservative() -> Fragment {
        Fragment {
            max_width: 128,
            extended_ops: false,
        }
    }

    /// Widths 1..=512, mixed-width casts (`extract`, `zext`, `sext`, `concat`), shifts, rotates,
    /// bit-ops, comparisons, `select`, multi-width equations, and [`Facts`]-guarded rules.
    pub fn extended() -> Fragment {
        Fragment {
            max_width: Width::MAX_BITS,
            extended_ops: true,
        }
    }
}

setters!(Fragment {
    with_max_width: max_width: u16,
    with_extended_ops: extended_ops: bool,
});

/// What to do with subterms outside the fragment.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UnsupportedPolicy {
    /// Decline the root (the default).
    Decline,
    /// Treat maximal outside subterms as opaque atoms (sound under total semantics; opt-in).
    Atomize,
}

/// When a batch's extracted candidates are published.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum PublishPolicy {
    /// Publish only when every searched root saturated within its bounds (the default).
    SaturatedOnly,
    /// Publish strictly cheaper verified candidates even when a root stopped at its iteration cap
    /// ([`RootEnd::IterationCap`]). Budget and deadline stops still withhold the batch.
    AtIterationCap,
}

/// Search configuration.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct SaturateConfig {
    /// The accepted fragment.
    pub fragment: Fragment,
    /// The most iterations per root.
    pub iterations: u8,
    /// The most matches applied per identity and direction per iteration.
    pub matches_per_rule_iter: u32,
    /// Per-root caps checked before anything is built.
    pub admission: Admission,
    /// Outside subterms.
    pub unsupported: UnsupportedPolicy,
    /// When candidates are published.
    pub publish: PublishPolicy,
    /// The most distinct nodes a root may have.
    pub max_root_nodes: u32,
}

impl Default for SaturateConfig {
    /// The conservative defaults: 8 iterations, 16 matches per equation and direction per
    /// iteration, and nothing published unless every searched root saturated.
    fn default() -> Self {
        SaturateConfig {
            fragment: Fragment::conservative(),
            iterations: 8,
            matches_per_rule_iter: 16,
            admission: Admission::default(),
            unsupported: UnsupportedPolicy::Decline,
            publish: PublishPolicy::SaturatedOnly,
            max_root_nodes: 4096,
        }
    }
}

setters!(SaturateConfig {
    with_fragment: fragment: Fragment,
    with_iterations: iterations: u8,
    with_matches_per_rule_iter: matches_per_rule_iter: u32,
    with_admission: admission: Admission,
    with_unsupported: unsupported: UnsupportedPolicy,
    with_publish: publish: PublishPolicy,
    with_max_root_nodes: max_root_nodes: u32,
});

impl SaturateConfig {
    /// A larger search: 16 iterations of at most 64 new matches per equation and direction.
    /// Pair it with a larger budget ([`SearchRun::per_call`]). Like the default configuration, it
    /// publishes only searches that saturate: an iteration cap, a budget or a deadline
    /// withholds the batch. Associativity and distributivity together rarely saturate, so
    /// choose the equation groups per search ([`Saturator::new`]).
    pub fn exploratory() -> SaturateConfig {
        SaturateConfig {
            iterations: 16,
            matches_per_rule_iter: 64,
            ..SaturateConfig::default()
        }
    }

    /// Extended multi-width search (`1..=512` bits, casts, shifts, rotates, comparisons, `select`,
    /// and [`Facts`]-guarded rules) that also publishes strictly cheaper verified candidates when
    /// a search stops at [`RootEnd::IterationCap`].
    pub fn extended() -> SaturateConfig {
        SaturateConfig {
            fragment: Fragment::extended(),
            iterations: 12,
            matches_per_rule_iter: 32,
            publish: PublishPolicy::AtIterationCap,
            ..SaturateConfig::default()
        }
    }
}

/// Which rules were admitted, and why others were not.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct AdmissionReport {
    /// Admitted identities.
    pub admitted: Vec<String>,
    /// Refused rules and the reason.
    pub refused: Vec<(String, String)>,
}

/// Options of one search.
#[derive(Default)]
#[non_exhaustive]
pub struct SearchRun<'a> {
    /// A caller-owned account shared across searches (and with other work).
    pub allowance: Option<&'a mut Allowance>,
    /// Caps on this search (default: [`SearchRun::DEFAULT_BUDGET`] when left at the default).
    pub per_call: Option<Budget>,
    /// Stop at a host-supplied time.
    pub deadline: Option<Deadline<'a>>,
    /// Cost model and extraction mode for this search (overrides the saturator's model when set).
    pub cost_model: Option<CostModel>,
}

setters!(SearchRun<'a> {
    with_allowance: allowance ? &'a mut Allowance,
    with_per_call: per_call ? Budget,
    with_deadline: deadline ? Deadline<'a>,
    with_cost_model: cost_model ? CostModel,
});

impl SearchRun<'_> {
    /// The default caps: 2048 e-nodes and 100 000 work units per search.
    pub const DEFAULT_BUDGET: Budget = {
        let mut b = Budget::UNLIMITED;
        b.eqsat_nodes = 2048;
        b.eqsat_work = 100_000;
        b
    };
}

impl core::fmt::Debug for SearchRun<'_> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SearchRun")
            .field("per_call", &self.per_call)
            .finish_non_exhaustive()
    }
}

/// How one root's search ended.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum RootEnd {
    /// No rule application added anything: the graph is saturated.
    Saturated,
    /// The iteration cap was reached first.
    IterationCap,
    /// A budget or deadline stopped it.
    Stopped(Exhausted),
    /// Outside the fragment (with `UnsupportedPolicy::Decline`).
    DeclinedUnsupported,
    /// Over an admission cap.
    DeclinedAdmission(Cap),
    /// Answered from the context's memo.
    Memo,
    /// Not searched: an earlier root already withheld the batch's publication.
    Skipped,
}

/// The result for one root.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct SearchRoot {
    /// The input.
    pub input: Expr,
    /// A strictly cheaper equivalent expression, if the batch was published and one was found.
    pub candidate: Option<Expr>,
    /// How its search ended.
    pub end: RootEnd,
}

/// Whether a batch's candidates are published.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Publication {
    /// Every searched root finished: candidates are published.
    Published,
    /// Some root stopped: no candidate of the batch is published.
    Withheld {
        /// The first stop: [`RootEnd::Stopped`], or [`RootEnd::IterationCap`] when the
        /// configuration does not publish at the cap.
        cause: RootEnd,
    },
}

/// Counters for one search; unproductive search is counted, not hidden.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct EqsatStats {
    /// Roots declined as unsupported.
    pub declined_unsupported: u64,
    /// Roots declined by an admission cap.
    pub declined_admission: u64,
    /// Roots saturated.
    pub saturated: u64,
    /// Roots stopped at the iteration cap.
    pub iteration_capped: u64,
    /// Roots stopped by a budget or deadline.
    pub budget_terminated: u64,
    /// Roots answered from the memo.
    pub memo_hits: u64,
    /// Roots with a candidate found (before publication).
    pub changed: u64,
    /// E-nodes inserted.
    pub enodes: u64,
    /// Work charged.
    pub work: u64,
    /// Unions.
    pub unions: u64,
    /// Iterations run.
    pub iterations: u64,
    /// Batches withheld.
    pub withheld: u64,
}

/// The result of a search.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct SearchReport {
    /// Per input root.
    pub roots: Vec<SearchRoot>,
    /// Whether the batch's candidates are published.
    pub publication: Publication,
    /// Counters.
    pub stats: EqsatStats,
}

struct Inner {
    rules: Vec<Identity>,
    cfg: SaturateConfig,
    epoch: u64,
    cost_model: CostModel,
}

/// A compiled set of admitted identities and a configuration. Cheap to clone; `Send + Sync`.
#[derive(Clone)]
pub struct Saturator {
    inner: Arc<Inner>,
}

impl core::fmt::Debug for Saturator {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Saturator")
            .field("identities", &self.inner.rules.len())
            .field("config", &self.inner.cfg)
            .field("cost_model", &self.inner.cost_model)
            .finish()
    }
}

/// The per-context memo: completed candidates and stable declines, per saturator epoch.
#[derive(Clone, Debug, Default)]
pub(crate) struct Memo {
    epoch: u64,
    entries: IdMap<u32, (Option<u32>, RootEnd)>,
}

impl Memo {
    pub(crate) fn clear(&mut self) {
        *self = Memo::default();
    }
}

fn builtin_program() -> &'static (RuleProgram, Ledger) {
    static B: OnceLock<(RuleProgram, Ledger)> = OnceLock::new();
    B.get_or_init(|| {
        let p = RuleProgram::compile_trusted(crate::rules::corpus::EQSAT)
            .unwrap_or_else(|e| panic!("the built-in identities do not compile: {e}"));
        let l = Ledger::parse(crate::rules::corpus::EQSAT_LEDGER)
            .unwrap_or_else(|e| panic!("the built-in identity ledger does not parse: {e}"));
        (p, l)
    })
}

fn node_in_fragment(op: OpCode, extended: bool) -> bool {
    match op {
        OpCode::Const | OpCode::Sym => true,
        _ if extended => {
            op.as_un().is_some()
                || op.as_bin().is_some()
                || op.as_cmp().is_some()
                || matches!(
                    op,
                    OpCode::Zext | OpCode::Sext | OpCode::Extract | OpCode::Concat | OpCode::Select
                )
        }
        _ => {
            op.as_bin().is_some_and(pattern::admitted_bin_conservative)
                || op.as_un().is_some_and(pattern::admitted_un_conservative)
        }
    }
}

impl Saturator {
    /// A saturator over the admitted identities of `programs` (each with the ledger that
    /// vouches for it), restricted to `groups` (all groups when empty).
    pub fn new(
        programs: &[(&RuleProgram, &Ledger)],
        groups: &[&str],
        cfg: SaturateConfig,
    ) -> Result<(Saturator, AdmissionReport), BuildError> {
        let mut report = AdmissionReport::default();
        let mut rules = Vec::new();
        let mut epoch = combine(0x65_7173_6174, u64::from(cfg.iterations));
        let extended = cfg.fragment.extended_ops;
        for (p, ledger) in programs {
            for g in p.groups() {
                if !groups.is_empty() && !groups.contains(&g.name.as_str()) {
                    continue;
                }
                for &ri in &g.rules {
                    let rule = &p.rules()[ri];
                    match pattern::admit(rule, ledger.vouches_for(&rule.name, rule.id), extended) {
                        Ok(id) => {
                            epoch = combine(combine(epoch, rule.id.0[0]), rule.id.0[1]);
                            report.admitted.push(rule.name.clone());
                            rules.push(id);
                        }
                        Err(why) => report.refused.push((rule.name.clone(), why)),
                    }
                }
            }
        }
        for g in groups {
            if !programs
                .iter()
                .any(|(p, _)| p.groups().iter().any(|x| x.name == *g))
            {
                return Err(BuildError::UnknownGroup((*g).to_string()));
            }
        }
        {
            use core::hash::{Hash, Hasher};
            let mut h = std::collections::hash_map::DefaultHasher::new();
            cfg.hash(&mut h);
            epoch = combine(epoch, h.finish());
        }
        Ok((
            Saturator {
                inner: Arc::new(Inner {
                    rules,
                    cfg,
                    epoch,
                    cost_model: CostModel::ast_size(),
                }),
            },
            report,
        ))
    }

    /// Returns a saturator sharing the compiled identities and configuration, with `model` as its
    /// default [`CostModel`] (overridable per call via [`SearchRun::with_cost_model`]).
    #[must_use]
    pub fn with_cost_model(self, model: CostModel) -> Saturator {
        let prev = &*self.inner;
        Saturator {
            inner: Arc::new(Inner {
                rules: prev.rules.clone(),
                cfg: prev.cfg,
                epoch: prev.epoch,
                cost_model: model,
            }),
        }
    }

    /// A saturator over every built-in group (`eqsat.*`). Associativity and each
    /// distributivity group saturate on their own, but not all together on most inputs; prefer
    /// [`builtin_groups`](Saturator::builtin_groups) with the groups a search needs.
    pub fn builtin(cfg: SaturateConfig) -> (Saturator, AdmissionReport) {
        Saturator::builtin_groups(&[], cfg)
    }

    /// A saturator over the named built-in groups (every group when `groups` is empty):
    /// `eqsat.assoc`, `eqsat.distrib` (`*` over `+`), `eqsat.distrib_and` (`&` over `|` and
    /// `^`), `eqsat.distrib_or` (`|` over `&`), `eqsat.negation`, `eqsat.cancel`, and (under
    /// [`Fragment::extended`]) `eqsat.casts`, `eqsat.shifts`, `eqsat.select`, and `eqsat.facts`.
    pub fn builtin_groups(groups: &[&str], cfg: SaturateConfig) -> (Saturator, AdmissionReport) {
        let (p, l) = builtin_program();
        Saturator::new(&[(p, l)], groups, cfg)
            .unwrap_or_else(|e| panic!("the built-in identities do not link: {e}"))
    }

    /// Searches each root of `batch` in its own e-graph (sharing only the allowance) and
    /// extracts strictly cheaper candidates. Publication is transactional per batch.
    pub fn search(
        &self,
        cx: &mut Context,
        batch: &[Expr],
        run: SearchRun<'_>,
    ) -> Result<SearchReport, Error> {
        let ids = cx.ids(batch)?;
        let inner = &*self.inner;
        let SearchRun {
            allowance,
            per_call,
            deadline,
            cost_model,
        } = run;
        let active_model = cost_model.unwrap_or_else(|| inner.cost_model.clone());
        let effective_epoch = active_model.epoch_mix(inner.epoch);
        let per_call = per_call.unwrap_or(SearchRun::DEFAULT_BUDGET);
        let limit = match &allowance {
            Some(a) => per_call.min(&a.remaining()),
            None => per_call,
        };
        let mut meter = Meter::new(limit, deadline);
        let mut stats = EqsatStats::default();
        let mut distinct_roots: Vec<u32> = Vec::with_capacity(ids.len());
        for &r in &ids {
            if !distinct_roots.contains(&r) {
                distinct_roots.push(r);
            }
        }
        // In multi-root DAG mode, extraction and profitability weigh subterms shared across the
        // batch's roots, so single-root context memoization is bypassed.
        let use_memo = !(active_model.mode() == ExtractionMode::Dag && distinct_roots.len() > 1);
        if use_memo && cx.eqsat_memo.epoch != effective_epoch {
            cx.eqsat_memo.clear();
            cx.eqsat_memo.epoch = effective_epoch;
        }
        let mut current_roots = distinct_roots.clone();
        let mut done: IdMap<u32, (Option<u32>, RootEnd)> = IdMap::default();
        // A deadline already passed withholds the batch, memo answers included.
        let mut cause: Option<RootEnd> = meter.deadline_now().err().map(RootEnd::Stopped);
        let mut failure: Option<Error> = None;
        for (pos, &root) in distinct_roots.iter().enumerate() {
            if use_memo && let Some(&(c, _)) = cx.eqsat_memo.entries.get(&root) {
                stats.memo_hits += 1;
                done.insert(root, (c, RootEnd::Memo));
                if let Some(cand) = c {
                    current_roots[pos] = cand;
                }
                continue;
            }
            match cause {
                // A budget stop earlier in the batch: nothing more is searched.
                Some(RootEnd::Stopped(e)) => {
                    done.insert(root, (None, RootEnd::Stopped(e)));
                    continue;
                }
                // Publication is already withheld: searching on would only spend the budget.
                Some(_) => {
                    done.insert(root, (None, RootEnd::Skipped));
                    continue;
                }
                None => {}
            }
            let other_roots: Vec<u32> =
                if active_model.mode() == ExtractionMode::Dag && current_roots.len() > 1 {
                    current_roots
                        .iter()
                        .enumerate()
                        .filter(|&(k, _)| k != pos)
                        .map(|(_, &r)| r)
                        .collect()
                } else {
                    Vec::new()
                };
            let (cand, end) = match self.search_root(
                cx,
                root,
                &other_roots,
                &active_model,
                &mut meter,
                &mut stats,
            ) {
                Ok(x) => x,
                Err(e) => {
                    failure = Some(e);
                    break;
                }
            };
            match end {
                RootEnd::Stopped(_) => cause = Some(end),
                RootEnd::IterationCap if inner.cfg.publish == PublishPolicy::SaturatedOnly => {
                    cause.get_or_insert(end);
                }
                _ => {}
            }
            // Stable outcomes are memoized: saturated searches and admission declines. Never an
            // incomplete search (an iteration cap, a budget or a deadline stop).
            let stable = matches!(
                end,
                RootEnd::Saturated | RootEnd::DeclinedUnsupported | RootEnd::DeclinedAdmission(_)
            );
            if use_memo && stable {
                cx.eqsat_memo.entries.insert(root, (cand, end));
            }
            if let Some(c) = cand {
                current_roots[pos] = c;
            }
            done.insert(root, (cand, end));
        }
        let spent = meter.spent;
        if let Some(a) = allowance {
            a.spend(&spent);
        }
        if let Some(e) = failure {
            return Err(e);
        }
        stats.enodes = spent.eqsat_nodes;
        stats.work = spent.eqsat_work;
        let publication = match cause {
            None => Publication::Published,
            Some(c) => {
                stats.withheld += 1;
                Publication::Withheld { cause: c }
            }
        };
        let published = publication == Publication::Published;
        Ok(SearchReport {
            roots: ids
                .iter()
                .map(|&i| {
                    let (c, end) = done[&i];
                    SearchRoot {
                        input: cx.handle(i),
                        candidate: c.filter(|_| published).map(|c| cx.handle(c)),
                        end,
                    }
                })
                .collect(),
            publication,
            stats,
        })
    }

    fn search_root(
        &self,
        cx: &mut Context,
        root: u32,
        other_roots: &[u32],
        model: &CostModel,
        meter: &mut Meter<'_>,
        stats: &mut EqsatStats,
    ) -> Result<(Option<u32>, RootEnd), Error> {
        let cfg = &self.inner.cfg;
        // Admission from O(1) metadata first.
        let meta = cx.meta[root as usize];
        if meta.height > cfg.admission.max_root_height {
            stats.declined_admission += 1;
            return Ok((None, RootEnd::DeclinedAdmission(Cap::Height)));
        }
        if meta.tree > cfg.admission.max_root_tree_size {
            stats.declined_admission += 1;
            return Ok((None, RootEnd::DeclinedAdmission(Cap::TreeSize)));
        }
        let w = cx.width_of(root);
        // The bounded fragment and homogeneity check, then the import.
        let order = match self.fragment(cx, root, w) {
            Ok(o) => o,
            Err(end) => {
                match end {
                    RootEnd::DeclinedAdmission(_) => stats.declined_admission += 1,
                    _ => stats.declined_unsupported += 1,
                }
                return Ok((None, end));
            }
        };
        let mut eg = EGraph::new(w);
        let rootc = match self.import(cx, &mut eg, &order, meter) {
            Ok(c) => c,
            Err(Halt::Budget(e)) => {
                stats.budget_terminated += 1;
                return Ok((None, RootEnd::Stopped(e)));
            }
            Err(Halt::Contract) => {
                return Err(Error::Contract(
                    "constant folding disagreed on import".into(),
                ));
            }
        };
        let end = match self.saturate(&mut eg, meter, stats) {
            Ok(end) => end,
            Err(Halt::Budget(e)) => {
                stats.budget_terminated += 1;
                stats.unions += eg.unions;
                return Ok((None, RootEnd::Stopped(e)));
            }
            Err(Halt::Contract) => {
                return Err(Error::Contract(
                    "an admitted identity united two different constants".into(),
                ));
            }
        };
        stats.unions += eg.unions;
        let external_shared = if model.mode() == ExtractionMode::Dag && !other_roots.is_empty() {
            self.shared_classes(cx, &mut eg, other_roots, w)
        } else {
            IdMap::default()
        };
        let best = match extract::costs_for(&mut eg, rootc, model, &external_shared, meter) {
            Ok(b) => b,
            Err(e) => {
                stats.budget_terminated += 1;
                return Ok((None, RootEnd::Stopped(e)));
            }
        };
        match end {
            RootEnd::Saturated => stats.saturated += 1,
            RootEnd::IterationCap => stats.iteration_capped += 1,
            _ => {}
        }
        let Some(e) = cx.as_engine(|cx| extract::build(&mut eg, &best, rootc, cx))? else {
            return Ok((None, end));
        };
        if e == root {
            return Ok((None, end));
        }
        let cheaper = if model.is_default_ast_tree() {
            // Strictly cheaper as a tree (and no larger as a DAG), or strictly smaller as a DAG
            // (and no larger as a tree).
            let (te, tr) = (cx.meta[e as usize].tree, cx.meta[root as usize].tree);
            let dag = |cx: &mut Context, i: u32| match cx
                .dag_size(&[cx.handle(i)], cfg.max_root_nodes.saturating_mul(4))
            {
                Ok(crate::Bounded::Exact(n)) => Some(n),
                _ => None,
            };
            let (de, dr) = (dag(cx, e), dag(cx, root));
            (te < tr && matches!((de, dr), (Some(a), Some(b)) if a <= b))
                || (te <= tr && matches!((de, dr), (Some(a), Some(b)) if a < b))
        } else {
            self.is_cheaper_under(cx, root, e, other_roots, w, model)
        };
        if !cheaper {
            return Ok((None, end));
        }
        if !agrees(cx, root, e)? {
            return Err(Error::Contract(
                "an extracted candidate differs from its input at a sampled point".into(),
            ));
        }
        stats.changed += 1;
        Ok((Some(e), end))
    }

    /// Maps nodes already live in `other_roots` to canonical `ClassId`s present in `eg` without
    /// inserting new e-nodes.
    fn shared_classes(
        &self,
        cx: &Context,
        eg: &mut EGraph,
        other_roots: &[u32],
        root_w: Width,
    ) -> IdMap<ClassId, ()> {
        let cfg = &self.inner.cfg;
        let max_nodes = cfg.max_root_nodes.saturating_mul(4) as usize;
        let extended = cfg.fragment.extended_ops;
        let max_w = cfg.fragment.max_width.min(Width::MAX_BITS);
        let mut order = Vec::new();
        let mut seen: IdMap<u32, ()> = IdMap::default();
        let mut stack: Vec<(u32, bool)> = other_roots.iter().map(|&r| (r, false)).collect();
        while let Some((i, expanded)) = stack.pop() {
            if expanded {
                order.push(i);
                continue;
            }
            if seen.insert(i, ()).is_some() {
                continue;
            }
            if seen.len() > max_nodes {
                return IdMap::default();
            }
            let n = cx.node(i);
            let width_ok = if extended {
                n.width <= max_w
            } else {
                n.width == root_w.bits()
            };
            if !width_ok || !node_in_fragment(n.op, extended) {
                order.push(i);
                continue;
            }
            stack.push((i, true));
            for c in n.children() {
                stack.push((c, false));
            }
        }
        let mut node_to_class: IdMap<u32, ClassId> = IdMap::default();
        let mut shared: IdMap<ClassId, ()> = IdMap::default();
        for i in order {
            let n = cx.node(i);
            let inside = if extended {
                n.width <= max_w && node_in_fragment(n.op, true)
            } else {
                n.width == root_w.bits() && node_in_fragment(n.op, false)
            };
            let enode = if let Some(v) = cx.const_val(i) {
                eg.lookup_const_node(&v)
            } else if !inside || n.op == OpCode::Sym {
                Some(ENode {
                    op: EOp::Leaf {
                        node: i,
                        width: n.width,
                    },
                    kids: [0, 0, 0],
                })
            } else if let Some(u) = n.op.as_un() {
                node_to_class.get(&n.a).map(|&ca| ENode {
                    op: EOp::Un(u),
                    kids: [ca, 0, 0],
                })
            } else if let Some(b) = n.op.as_bin() {
                match (node_to_class.get(&n.a), node_to_class.get(&n.b)) {
                    (Some(&ca), Some(&cb)) => Some(ENode {
                        op: EOp::Bin(b),
                        kids: [ca, cb, 0],
                    }),
                    _ => None,
                }
            } else if let Some(c) = n.op.as_cmp() {
                match (node_to_class.get(&n.a), node_to_class.get(&n.b)) {
                    (Some(&ca), Some(&cb)) => Some(ENode {
                        op: EOp::Cmp(c),
                        kids: [ca, cb, 0],
                    }),
                    _ => None,
                }
            } else {
                match n.op {
                    OpCode::Zext => node_to_class.get(&n.a).map(|&ca| ENode {
                        op: EOp::Zext(n.width),
                        kids: [ca, 0, 0],
                    }),
                    OpCode::Sext => node_to_class.get(&n.a).map(|&ca| ENode {
                        op: EOp::Sext(n.width),
                        kids: [ca, 0, 0],
                    }),
                    OpCode::Extract => node_to_class.get(&n.a).map(|&ca| ENode {
                        op: EOp::Extract {
                            lo: n.b as u16,
                            width: n.width,
                        },
                        kids: [ca, 0, 0],
                    }),
                    OpCode::Concat => match (node_to_class.get(&n.a), node_to_class.get(&n.b)) {
                        (Some(&ca), Some(&cb)) => Some(ENode {
                            op: EOp::Concat,
                            kids: [ca, cb, 0],
                        }),
                        _ => None,
                    },
                    OpCode::Select => match (
                        node_to_class.get(&n.a),
                        node_to_class.get(&n.b),
                        node_to_class.get(&n.c),
                    ) {
                        (Some(&ca), Some(&cb), Some(&cc)) => Some(ENode {
                            op: EOp::Select,
                            kids: [ca, cb, cc],
                        }),
                        _ => None,
                    },
                    _ => None,
                }
            };
            if let Some(en) = enode
                && let Some(cid) = eg.find_enode(en)
            {
                node_to_class.insert(i, cid);
                shared.insert(cid, ());
            }
        }
        shared
    }

    fn expr_node_cost(
        &self,
        cx: &Context,
        i: u32,
        root_w: Width,
        model: &CostModel,
    ) -> (u64, bool) {
        let cfg = &self.inner.cfg;
        let extended = cfg.fragment.extended_ops;
        let max_w = cfg.fragment.max_width.min(Width::MAX_BITS);
        let n = cx.node(i);
        let w = cx.width_of(i);
        let width_ok = if extended {
            n.width <= max_w
        } else {
            n.width == root_w.bits()
        };
        if n.op == OpCode::Const {
            return (model.cost(CostOp::Const, w), true);
        }
        if n.op == OpCode::Sym || !width_ok || !node_in_fragment(n.op, extended) {
            return (model.cost(CostOp::Symbol, w), true);
        }
        let op = if let Some(u) = n.op.as_un() {
            CostOp::Un(u)
        } else if let Some(b) = n.op.as_bin() {
            CostOp::Bin(b)
        } else if let Some(c) = n.op.as_cmp() {
            CostOp::Cmp(c)
        } else {
            match n.op {
                OpCode::Zext => CostOp::Zext {
                    from: cx.width_of(n.a),
                    to: w,
                },
                OpCode::Sext => CostOp::Sext {
                    from: cx.width_of(n.a),
                    to: w,
                },
                OpCode::Extract => CostOp::Extract {
                    from: cx.width_of(n.a),
                    lo: n.b as u16,
                    width: w,
                },
                OpCode::Concat => CostOp::Concat {
                    hi: cx.width_of(n.a),
                    lo: cx.width_of(n.b),
                },
                OpCode::Select => CostOp::Select(w),
                _ => return (model.cost(CostOp::Symbol, w), true),
            }
        };
        (model.cost(op, w), false)
    }

    fn eval_tree_cost(
        &self,
        cx: &Context,
        root: u32,
        root_w: Width,
        model: &CostModel,
    ) -> Option<u64> {
        let cap = self.inner.cfg.max_root_nodes.saturating_mul(4) as usize;
        let mut memo: IdMap<u32, u64> = IdMap::default();
        let mut stack: Vec<(u32, bool)> = vec![(root, false)];
        while let Some((i, expanded)) = stack.pop() {
            if memo.contains_key(&i) {
                continue;
            }
            if memo.len() > cap {
                return None;
            }
            let (own, is_leaf) = self.expr_node_cost(cx, i, root_w, model);
            if is_leaf {
                memo.insert(i, own);
                continue;
            }
            let n = cx.node(i);
            if !expanded {
                stack.push((i, true));
                for c in n.children() {
                    if !memo.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
                continue;
            }
            let mut sum = own;
            for c in n.children() {
                sum = sum.saturating_add(*memo.get(&c)?);
            }
            memo.insert(i, sum);
        }
        memo.get(&root).copied()
    }

    fn eval_dag_cost(
        &self,
        cx: &Context,
        roots: &[u32],
        root_w: Width,
        model: &CostModel,
    ) -> Option<u64> {
        let cap = self.inner.cfg.max_root_nodes.saturating_mul(8) as usize;
        let mut seen: IdMap<u32, ()> = IdMap::default();
        let mut stack: Vec<u32> = roots.to_vec();
        let mut total = 0u64;
        while let Some(i) = stack.pop() {
            if seen.insert(i, ()).is_some() {
                continue;
            }
            if seen.len() > cap {
                return None;
            }
            let (own, is_leaf) = self.expr_node_cost(cx, i, root_w, model);
            total = total.saturating_add(own);
            if !is_leaf {
                for c in cx.node(i).children() {
                    if !seen.contains_key(&c) {
                        stack.push(c);
                    }
                }
            }
        }
        Some(total)
    }

    fn is_cheaper_under(
        &self,
        cx: &Context,
        root: u32,
        cand: u32,
        other_roots: &[u32],
        root_w: Width,
        model: &CostModel,
    ) -> bool {
        match model.mode() {
            ExtractionMode::Tree => {
                let (Some(ce), Some(cr)) = (
                    self.eval_tree_cost(cx, cand, root_w, model),
                    self.eval_tree_cost(cx, root, root_w, model),
                ) else {
                    return false;
                };
                if ce != cr {
                    return ce < cr;
                }
                matches!(
                    (
                        self.eval_dag_cost(cx, &[cand], root_w, model),
                        self.eval_dag_cost(cx, &[root], root_w, model),
                    ),
                    (Some(de), Some(dr)) if de < dr
                )
            }
            ExtractionMode::Dag => {
                let mut before = Vec::with_capacity(other_roots.len() + 1);
                before.extend_from_slice(other_roots);
                before.push(root);
                let mut after = Vec::with_capacity(other_roots.len() + 1);
                after.extend_from_slice(other_roots);
                after.push(cand);
                matches!(
                    (
                        self.eval_dag_cost(cx, &after, root_w, model),
                        self.eval_dag_cost(cx, &before, root_w, model),
                    ),
                    (Some(de), Some(dr)) if de < dr
                )
            }
        }
    }

    /// The fragment nodes below `root` in post-order (atoms included as leaves), or why the
    /// root is declined.
    fn fragment(&self, cx: &Context, root: u32, w: Width) -> Result<Vec<u32>, RootEnd> {
        let cfg = &self.inner.cfg;
        let max_w = cfg.fragment.max_width.min(Width::MAX_BITS);
        let extended = cfg.fragment.extended_ops;
        if w.bits() > max_w {
            return Err(RootEnd::DeclinedUnsupported);
        }
        // `Admission::max_root_dag_size` and `max_root_nodes` both bound the distinct nodes.
        let max_nodes = cfg
            .admission
            .max_root_dag_size
            .map_or(cfg.max_root_nodes, |d| d.min(cfg.max_root_nodes));
        let mut order = Vec::new();
        let mut seen: IdMap<u32, ()> = IdMap::default();
        let mut stack: Vec<(u32, bool)> = vec![(root, false)];
        while let Some((i, expanded)) = stack.pop() {
            if expanded {
                order.push(i);
                continue;
            }
            if seen.insert(i, ()).is_some() {
                continue;
            }
            if seen.len() as u32 > max_nodes {
                return Err(RootEnd::DeclinedAdmission(Cap::DagSize));
            }
            let n = cx.node(i);
            let width_ok = if extended {
                n.width <= max_w
            } else {
                n.width == w.bits()
            };
            if !width_ok || !node_in_fragment(n.op, extended) {
                if cfg.unsupported == UnsupportedPolicy::Atomize && i != root && n.width <= max_w {
                    order.push(i);
                    continue;
                }
                return Err(RootEnd::DeclinedUnsupported);
            }
            stack.push((i, true));
            for c in n.children() {
                stack.push((c, false));
            }
        }
        Ok(order)
    }

    fn import(
        &self,
        cx: &mut Context,
        eg: &mut EGraph,
        order: &[u32],
        m: &mut Meter<'_>,
    ) -> Result<ClassId, Halt> {
        let extended = self.inner.cfg.fragment.extended_ops;
        let mut at: IdMap<u32, ClassId> = IdMap::default();
        for &i in order {
            let n = cx.node(i);
            let inside = node_in_fragment(n.op, extended);
            let mut leaf_facts: Option<Facts> = None;
            let e = if let Some(v) = cx.const_val(i) {
                eg.const_node(v)
            } else if !inside || n.op == OpCode::Sym || !n.children().all(|c| at.contains_key(&c)) {
                leaf_facts = if n.op == OpCode::Sym {
                    cx.declared_at(i).map(Facts::from_known)
                } else {
                    cx.try_facts_cap(cx.handle(i), 64).ok().flatten()
                };
                ENode {
                    op: EOp::Leaf {
                        node: i,
                        width: n.width,
                    },
                    kids: [0, 0, 0],
                }
            } else if let Some(u) = n.op.as_un() {
                ENode {
                    op: EOp::Un(u),
                    kids: [at[&n.a], 0, 0],
                }
            } else if let Some(b) = n.op.as_bin() {
                ENode {
                    op: EOp::Bin(b),
                    kids: [at[&n.a], at[&n.b], 0],
                }
            } else if let Some(c) = n.op.as_cmp() {
                ENode {
                    op: EOp::Cmp(c),
                    kids: [at[&n.a], at[&n.b], 0],
                }
            } else {
                match n.op {
                    OpCode::Zext => ENode {
                        op: EOp::Zext(n.width),
                        kids: [at[&n.a], 0, 0],
                    },
                    OpCode::Sext => ENode {
                        op: EOp::Sext(n.width),
                        kids: [at[&n.a], 0, 0],
                    },
                    OpCode::Extract => ENode {
                        op: EOp::Extract {
                            lo: n.b as u16,
                            width: n.width,
                        },
                        kids: [at[&n.a], 0, 0],
                    },
                    OpCode::Concat => ENode {
                        op: EOp::Concat,
                        kids: [at[&n.a], at[&n.b], 0],
                    },
                    OpCode::Select => ENode {
                        op: EOp::Select,
                        kids: [at[&n.a], at[&n.b], at[&n.c]],
                    },
                    _ => ENode {
                        op: EOp::Leaf {
                            node: i,
                            width: n.width,
                        },
                        kids: [0, 0, 0],
                    },
                }
            };
            let c = eg.add_with_facts(e, true, leaf_facts, m)?;
            at.insert(i, c);
        }
        order
            .last()
            .and_then(|r| at.get(r).copied())
            .ok_or(Halt::Contract)
    }

    fn saturate(
        &self,
        eg: &mut EGraph,
        m: &mut Meter<'_>,
        stats: &mut EqsatStats,
    ) -> Result<RootEnd, Halt> {
        let cfg = &self.inner.cfg;
        let max_w = cfg.fragment.max_width.min(Width::MAX_BITS);
        let extended = cfg.fragment.extended_ops;
        if extended {
            eg.materialize_constants(m)?;
        }
        type AppliedKey = (usize, usize, ClassId, MatchOut);
        // Matches already applied (canonicalized when checked): they do not count toward the
        // per-equation cap, or an early redex could starve every later one.
        let mut applied: std::collections::HashSet<AppliedKey, crate::hash::IdBuild> =
            std::collections::HashSet::default();
        for _ in 0..cfg.iterations {
            stats.iterations += 1;
            let (n0, u0) = (eg.nodes.len(), eg.unions);
            // Collect every identity's matches in both directions over the canonical classes,
            // then apply them in collection order.
            let mut apps: Vec<AppliedKey> = Vec::new();
            let classes = eg.canonical_classes();
            // Saturation can only be claimed when no equation had more matches than it took.
            let mut capped = false;
            for (ri, rule) in self.inner.rules.iter().enumerate() {
                for dir in 0..if rule.bidirectional { 2 } else { 1 } {
                    let mut left = cfg.matches_per_rule_iter as usize;
                    for &c in &classes {
                        if left == 0 && capped {
                            // Nothing more can be taken, and saturation is already ruled out.
                            break;
                        }
                        let mut found: Vec<MatchOut> = Vec::new();
                        // One more than can be taken shows whether matches were left over.
                        // Matches already applied are skipped before they count.
                        let window = left + 1;
                        let mut skip = |eg: &mut EGraph, ws: &[u16], b: &[ClassId]| {
                            let key = (
                                ri,
                                dir,
                                eg.find(c),
                                MatchOut {
                                    widths: ws.to_vec(),
                                    vars: b.iter().map(|&x| eg.find(x)).collect(),
                                },
                            );
                            applied.contains(&key)
                        };
                        pattern::ematch_identity(
                            eg, rule, dir, c, max_w, &mut found, window, &mut skip, m,
                        )?;
                        if found.len() >= window {
                            capped = true;
                        }
                        for mo in found {
                            let canon_mo = MatchOut {
                                widths: mo.widths.clone(),
                                vars: mo.vars.iter().map(|&x| eg.find(x)).collect(),
                            };
                            let key = (ri, dir, eg.find(c), canon_mo);
                            if applied.contains(&key) {
                                continue;
                            }
                            if left == 0 {
                                capped = true;
                                break;
                            }
                            left -= 1;
                            applied.insert(key);
                            apps.push((ri, dir, c, mo));
                        }
                    }
                }
            }
            for (ri, dir, c, mo) in apps {
                let rule = &self.inner.rules[ri];
                if let Some(r) =
                    pattern::instantiate(eg, rule, 1 - dir, &mo.widths, &mo.vars, max_w, m)?
                {
                    eg.union(c, r, m)?;
                }
            }
            eg.rebuild(m)?;
            if extended {
                eg.materialize_constants(m)?;
            }
            if eg.nodes.len() == n0 && eg.unions == u0 && !capped {
                return Ok(RootEnd::Saturated);
            }
        }
        Ok(RootEnd::IterationCap)
    }
}

/// Whether `a` and `b` agree at seeded values of their symbols.
fn agrees(cx: &mut Context, a: u32, b: u32) -> Result<bool, Error> {
    let (ea, eb) = (cx.handle(a), cx.handle(b));
    let syms = cx.symbols_in(&[ea, eb])?;
    // With what the host declared of each (the points agree with it).
    let keys: Vec<(SymbolKey, Width, Option<crate::KnownBits>)> = syms
        .iter()
        .filter_map(|&s| {
            let key = cx.symbol_key(s)?.clone();
            let known = cx
                .find_symbol(&key)
                .and_then(|e| cx.declared_known(e).ok().flatten());
            Some((key, cx.symbol_width(s)?, known))
        })
        .collect();
    let mut x = cx.meta[a as usize].shash;
    for k in 0..32u32 {
        let vals: Vec<(SymbolKey, BitVec)> = keys
            .iter()
            .map(|(key, w, known)| {
                let v = match k {
                    0 => BitVec::zero(*w),
                    1 => BitVec::ones(*w),
                    _ => {
                        let limbs: Vec<u64> = (0..8)
                            .map(|_| {
                                x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
                                let mut z = x;
                                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                                z ^ (z >> 31)
                            })
                            .collect();
                        BitVec::wrapping_from_limbs(*w, &limbs)
                    }
                };
                (key.clone(), known.map_or(v, |d| d.fit(&v)))
            })
            .collect();
        let env =
            FnEnv(|key: &SymbolKey, _| vals.iter().find(|(k2, _)| k2 == key).map(|(_, v)| *v));
        let r = cx.eval(&[ea, eb], &env)?;
        if r[0] != r[1] {
            return Ok(false);
        }
    }
    Ok(true)
}
