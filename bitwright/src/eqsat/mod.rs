//! The equality-saturation search service (feature `eqsat`, default off). See `docs/design.md`
//! §10.
//!
//! A bounded *alternative-expression search* over immutable graphs, not a phase: the host
//! decides when (output or checkpoint boundaries, never routine maintenance), which roots, and
//! which allowance. Admitted equations are proven, unconditional, of one width, and in the
//! conservative fragment `+ − * & | ^ neg ~`: identities are used in both directions, guard-free
//! rules in their authored direction. An extracted expression is a **candidate** the host's own
//! profitability and verification gates decide to use.
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

use std::sync::{Arc, OnceLock};

use egraph::{ClassId, EGraph, ENode, EOp, Halt};
use pattern::Identity;

use crate::engine::budget::Meter;
use crate::engine::{Admission, Allowance, Budget, BuildError, Cap, Deadline, Exhausted};
use crate::error::Error;
use crate::expr::{Context, Expr, FnEnv, OpCode};
use crate::hash::{IdMap, combine};
use crate::rules::{Ledger, RuleProgram};
use crate::{BitVec, SymbolKey, Width};

/// The operators and widths the search accepts.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Fragment {
    /// The widest root.
    pub max_width: u16,
}

impl Fragment {
    /// Widths 1..=128, one width per root, `+ − * & | ^`, unary `−` and `~`, constants and
    /// symbols.
    pub fn conservative() -> Fragment {
        Fragment { max_width: 128 }
    }
}

setters!(Fragment {
    with_max_width: max_width: u16,
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
    with_max_root_nodes: max_root_nodes: u32,
});

impl SaturateConfig {
    /// A larger search: 16 iterations of at most 64 new matches per equation and direction.
    /// Pair it with a larger budget ([`SearchRun::per_call`]). Like every configuration, it
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
}

setters!(SearchRun<'a> {
    with_allowance: allowance ? &'a mut Allowance,
    with_per_call: per_call ? Budget,
    with_deadline: deadline ? Deadline<'a>,
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
        let p = RuleProgram::compile(crate::rules::corpus::EQSAT)
            .unwrap_or_else(|e| panic!("the built-in identities do not compile: {e}"));
        let l = Ledger::parse(crate::rules::corpus::EQSAT_LEDGER)
            .unwrap_or_else(|e| panic!("the built-in identity ledger does not parse: {e}"));
        (p, l)
    })
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
        for (p, ledger) in programs {
            for g in p.groups() {
                if !groups.is_empty() && !groups.contains(&g.name.as_str()) {
                    continue;
                }
                for &ri in &g.rules {
                    let rule = &p.rules()[ri];
                    match pattern::admit(rule, ledger.vouches_for(&rule.name, rule.id)) {
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
                inner: Arc::new(Inner { rules, cfg, epoch }),
            },
            report,
        ))
    }

    /// A saturator over every built-in group (`eqsat.*`). Associativity and each
    /// distributivity group saturate on their own, but not all together on most inputs; prefer
    /// [`builtin_groups`](Saturator::builtin_groups) with the groups a search needs.
    pub fn builtin(cfg: SaturateConfig) -> (Saturator, AdmissionReport) {
        Saturator::builtin_groups(&[], cfg)
    }

    /// A saturator over the named built-in groups (every group when `groups` is empty):
    /// `eqsat.assoc`, `eqsat.distrib` (`*` over `+`), `eqsat.distrib_and` (`&` over `|` and
    /// `^`), `eqsat.distrib_or` (`|` over `&`), `eqsat.negation` and `eqsat.cancel`.
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
        } = run;
        let per_call = per_call.unwrap_or(SearchRun::DEFAULT_BUDGET);
        let limit = match &allowance {
            Some(a) => per_call.min(&a.remaining()),
            None => per_call,
        };
        let mut meter = Meter::new(limit, deadline);
        let mut stats = EqsatStats::default();
        if cx.eqsat_memo.epoch != inner.epoch {
            cx.eqsat_memo.clear();
            cx.eqsat_memo.epoch = inner.epoch;
        }
        let mut done: IdMap<u32, (Option<u32>, RootEnd)> = IdMap::default();
        // A deadline already passed withholds the batch, memo answers included.
        let mut cause: Option<RootEnd> = meter.deadline_now().err().map(RootEnd::Stopped);
        let mut failure: Option<Error> = None;
        for &root in &ids {
            if done.contains_key(&root) {
                continue;
            }
            if let Some(&(c, _)) = cx.eqsat_memo.entries.get(&root) {
                stats.memo_hits += 1;
                done.insert(root, (c, RootEnd::Memo));
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
            let (cand, end) = match self.search_root(cx, root, &mut meter, &mut stats) {
                Ok(x) => x,
                Err(e) => {
                    failure = Some(e);
                    break;
                }
            };
            match end {
                RootEnd::Stopped(_) => cause = Some(end),
                RootEnd::IterationCap => {
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
            if stable {
                cx.eqsat_memo.entries.insert(root, (cand, end));
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
        let mut eg = EGraph::new();
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
        let end = match self.saturate(&mut eg, w, meter, stats) {
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
        let best = match extract::costs(&mut eg, meter) {
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
        let Some(e) = cx.as_engine(|cx| extract::build(&mut eg, &best, rootc, cx, w))? else {
            return Ok((None, end));
        };
        if e == root {
            return Ok((None, end));
        }
        // Strictly cheaper as a tree, no larger as a DAG.
        let (te, tr) = (cx.meta[e as usize].tree, cx.meta[root as usize].tree);
        let dag = |cx: &mut Context, i: u32| match cx
            .dag_size(&[cx.handle(i)], cfg.max_root_nodes.saturating_mul(4))
        {
            Ok(crate::Bounded::Exact(n)) => Some(n),
            _ => None,
        };
        let (de, dr) = (dag(cx, e), dag(cx, root));
        let cheaper = te < tr && matches!((de, dr), (Some(a), Some(b)) if a <= b);
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

    /// The fragment nodes below `root` in post-order (atoms included as leaves), or why the
    /// root is declined.
    fn fragment(&self, cx: &Context, root: u32, w: Width) -> Result<Vec<u32>, RootEnd> {
        let cfg = &self.inner.cfg;
        if w.bits() > cfg.fragment.max_width {
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
            if n.width != w.bits() {
                if cfg.unsupported == UnsupportedPolicy::Atomize && i != root {
                    order.push(i);
                    continue;
                }
                return Err(RootEnd::DeclinedUnsupported);
            }
            let inside = match n.op {
                OpCode::Const | OpCode::Sym => true,
                op => {
                    op.as_bin().is_some_and(pattern::admitted_bin)
                        || op.as_un().is_some_and(pattern::admitted_un)
                }
            };
            if !inside {
                if cfg.unsupported == UnsupportedPolicy::Atomize && i != root {
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
        cx: &Context,
        eg: &mut EGraph,
        order: &[u32],
        m: &mut Meter<'_>,
    ) -> Result<ClassId, Halt> {
        let mut at: IdMap<u32, ClassId> = IdMap::default();
        for &i in order {
            let n = cx.node(i);
            let inside = n.op == OpCode::Const
                || n.op.as_bin().is_some_and(pattern::admitted_bin)
                || n.op.as_un().is_some_and(pattern::admitted_un);
            let e = if let Some(v) = cx.const_val(i) {
                ENode {
                    op: EOp::Const(v),
                    kids: [0, 0],
                }
            } else if !inside || n.op == OpCode::Sym || !n.children().all(|c| at.contains_key(&c)) {
                ENode {
                    op: EOp::Leaf(i),
                    kids: [0, 0],
                }
            } else if let Some(u) = n.op.as_un() {
                ENode {
                    op: EOp::Un(u),
                    kids: [at[&n.a], 0],
                }
            } else {
                let b = n.op.as_bin().unwrap_or(crate::BinOp::Add);
                ENode {
                    op: EOp::Bin(b),
                    kids: [at[&n.a], at[&n.b]],
                }
            };
            let c = eg.add(e, true, m)?;
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
        w: Width,
        m: &mut Meter<'_>,
        stats: &mut EqsatStats,
    ) -> Result<RootEnd, Halt> {
        let cfg = &self.inner.cfg;
        // Matches already applied (canonicalized when checked): they do not count toward the
        // per-equation cap, or an early redex could starve every later one.
        let mut applied: std::collections::HashSet<
            (usize, usize, ClassId, Vec<ClassId>),
            crate::hash::IdBuild,
        > = std::collections::HashSet::default();
        for _ in 0..cfg.iterations {
            stats.iterations += 1;
            let (n0, u0) = (eg.nodes.len(), eg.unions);
            // Collect every identity's matches in both directions over the canonical classes,
            // then apply them in collection order.
            let mut apps: Vec<(usize, usize, ClassId, Vec<ClassId>)> = Vec::new();
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
                        let mut found: Vec<Vec<ClassId>> = Vec::new();
                        // One more than can be taken shows whether matches were left over.
                        // Matches already applied are skipped before they count.
                        let window = left + 1;
                        let mut skip = |eg: &mut EGraph, b: &[ClassId]| {
                            let key = (
                                ri,
                                dir,
                                eg.find(c),
                                b.iter().map(|&x| eg.find(x)).collect::<Vec<_>>(),
                            );
                            applied.contains(&key)
                        };
                        pattern::ematch(
                            eg,
                            &rule.sides[dir],
                            rule.vars,
                            c,
                            w,
                            &mut found,
                            window,
                            &mut skip,
                            m,
                        )?;
                        if found.len() >= window {
                            capped = true;
                        }
                        for b in found {
                            let key = (
                                ri,
                                dir,
                                eg.find(c),
                                b.iter().map(|&x| eg.find(x)).collect::<Vec<_>>(),
                            );
                            if applied.contains(&key) {
                                continue;
                            }
                            if left == 0 {
                                capped = true;
                                break;
                            }
                            left -= 1;
                            applied.insert(key);
                            apps.push((ri, dir, c, b));
                        }
                    }
                }
            }
            for (ri, dir, c, b) in apps {
                let rule = &self.inner.rules[ri];
                if let Some(r) = pattern::instantiate(eg, &rule.sides[1 - dir], &b, w, m)? {
                    eg.union(c, r, m)?;
                }
            }
            eg.rebuild(m)?;
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
    let keys: Vec<(SymbolKey, Width)> = syms
        .iter()
        .filter_map(|&s| Some((cx.symbol_key(s)?.clone(), cx.symbol_width(s)?)))
        .collect();
    let mut x = cx.meta[a as usize].shash;
    for k in 0..32u32 {
        let vals: Vec<(SymbolKey, BitVec)> = keys
            .iter()
            .map(|(key, w)| {
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
                (key.clone(), v)
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
