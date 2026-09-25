//! Telemetry: counters that are always collected, and per-rule events for an observer.

use std::collections::BTreeMap;

use crate::expr::{Context, Expr};
use crate::rules::Rule;

/// Counters for one call. Always collected; no-op work is counted like useful work.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Stats {
    /// Node visits.
    pub node_visits: u64,
    /// Nodes answered from the context's memo (a completed earlier result).
    pub memo_hits: u64,
    /// Candidate rules tried after the dispatch prefilter.
    pub candidates: u64,
    /// Matcher steps.
    pub match_steps: u64,
    /// Candidates whose pattern did not match.
    pub no_match: u64,
    /// Candidates that matched but whose guard did not hold.
    pub guard_false: u64,
    /// Candidates and pass steps declined only for lack of work or facts (the node may not be
    /// normal, so it is not memoized as such).
    pub degraded: u64,
    /// Candidates that applied but produced the node itself.
    pub no_change: u64,
    /// Rewrites committed.
    pub rewrites: u64,
    /// Applications vetoed by [`Hooks::admit`].
    pub hook_vetoes: u64,
    /// Applications rejected by a postcondition (width, verification, tripwire, termination).
    pub rejected: u64,
    /// Rewrite cycles cut, in favor of the rewrite: a node not rebuilt over its operands'
    /// results into one a pass rewrote it from in this call (in a pass's phase), or into one
    /// whose result was still being worked out; or rewritten into the latter without visiting
    /// it again.
    pub cycles_cut: u64,
    /// Rules quarantined for the rest of the call after a postcondition failure.
    pub quarantined: u64,
    /// Nodes created.
    pub new_nodes: u64,
    /// Fact transfer functions run for guards and passes.
    pub fact_work: u64,
    /// Normal-form pass work.
    pub pass_work: u64,
    /// Rounds run.
    pub rounds: u32,
    /// Per normal-form pass, by name.
    pub passes: BTreeMap<&'static str, PassCounts>,
    /// The MBA service.
    pub mba: MbaStats,
    /// Distinct roots by outcome: `[unchanged, changed]` for each end.
    pub completed: [u64; 2],
    /// Distinct roots stopped by a budget: `[unchanged, changed]`.
    pub budget_terminated: [u64; 2],
    /// Distinct roots declined by an admission cap.
    pub declined: u64,
}

impl Stats {
    /// Adds another call's counters (`rounds` is the larger of the two).
    pub fn absorb(&mut self, o: &Stats) {
        // Every field by name, so a new one cannot be forgotten.
        let Stats {
            node_visits,
            memo_hits,
            candidates,
            match_steps,
            no_match,
            guard_false,
            degraded,
            no_change,
            rewrites,
            hook_vetoes,
            rejected,
            cycles_cut,
            quarantined,
            new_nodes,
            fact_work,
            pass_work,
            rounds,
            passes,
            mba,
            completed,
            budget_terminated,
            declined,
        } = o;
        self.node_visits += node_visits;
        self.memo_hits += memo_hits;
        self.candidates += candidates;
        self.match_steps += match_steps;
        self.no_match += no_match;
        self.guard_false += guard_false;
        self.degraded += degraded;
        self.no_change += no_change;
        self.rewrites += rewrites;
        self.hook_vetoes += hook_vetoes;
        self.rejected += rejected;
        self.cycles_cut += cycles_cut;
        self.quarantined += quarantined;
        self.new_nodes += new_nodes;
        self.fact_work += fact_work;
        self.pass_work += pass_work;
        self.rounds = self.rounds.max(*rounds);
        for (name, c) in passes {
            self.passes.entry(name).or_default().absorb(c);
        }
        self.mba.absorb(mba);
        for k in 0..2 {
            self.completed[k] += completed[k];
            self.budget_terminated[k] += budget_terminated[k];
        }
        self.declined += declined;
    }
}

/// Counters for the MBA service: calls, outcomes, and the refusal taxonomy.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct MbaStats {
    /// Solver calls.
    pub calls: u64,
    /// Answers taken from the cache.
    pub cache_hits: u64,
    /// Nodes replaced.
    pub simplified: u64,
    /// "No simpler" answers.
    pub no_simpler: u64,
    /// Inputs the solver does not handle.
    pub unsupported: u64,
    /// Calls that ran out of the solver's budget.
    pub exhausted: u64,
    /// Answers found wrong (at a sampled point, or after lifting).
    pub refuted: u64,
    /// Answers without accepted evidence.
    pub proof_unknown: u64,
    /// Answers that would not make the DAG smaller (checked before they are proved, and again
    /// when committing).
    pub not_smaller: u64,
    /// Inputs refused before asking: too many variables, too large, too wide, too small.
    pub too_many_vars: u64,
    /// See `too_many_vars`.
    pub too_large: u64,
    /// See `too_many_vars`.
    pub too_wide: u64,
    /// See `too_many_vars`.
    pub too_small: u64,
    /// bitwright's own certificates, run on every answer (see [`CertStats`]).
    pub certificates: CertStats,
}

impl MbaStats {
    /// Adds another call's counters.
    pub fn absorb(&mut self, o: &MbaStats) {
        let MbaStats {
            calls,
            cache_hits,
            simplified,
            no_simpler,
            unsupported,
            exhausted,
            refuted,
            proof_unknown,
            not_smaller,
            too_many_vars,
            too_large,
            too_wide,
            too_small,
            certificates,
        } = o;
        self.calls += calls;
        self.cache_hits += cache_hits;
        self.simplified += simplified;
        self.no_simpler += no_simpler;
        self.unsupported += unsupported;
        self.exhausted += exhausted;
        self.refuted += refuted;
        self.proof_unknown += proof_unknown;
        self.not_smaller += not_smaller;
        self.too_many_vars += too_many_vars;
        self.too_large += too_large;
        self.too_wide += too_wide;
        self.too_small += too_small;
        self.certificates.absorb(certificates);
    }

    #[cfg(feature = "mba")]
    pub(crate) fn refused(&mut self, why: &crate::mba::Refusal) {
        use crate::mba::Refusal;
        match why {
            Refusal::TooManyVars => self.too_many_vars += 1,
            Refusal::TooLarge => self.too_large += 1,
            Refusal::TooWide => self.too_wide += 1,
            Refusal::TooSmall => self.too_small += 1,
            _ => self.unsupported += 1,
        }
    }
}

/// Counters of the native certificates, by the test that decided.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct CertStats {
    /// Questions asked.
    pub calls: u64,
    /// Proved.
    pub proved: u64,
    /// Refuted (with a concrete counterexample).
    pub refuted: u64,
    /// Not decided.
    pub unknown: u64,
    /// Decided by the corner signature.
    pub signature: u64,
    /// Decided at single bit positions.
    pub single_bit: u64,
    /// Decided at points with at most `d` set positions.
    pub sparse: u64,
    /// Decided on the pure-polynomial grid.
    pub grid: u64,
    /// Decided exhaustively.
    pub exhaustive: u64,
    /// Decided as equal polynomials over symbols (variables, conjunctions of the leaves of a
    /// bitwise function, other bitwise subterms).
    pub symbolic: u64,
    /// Decided bit-serially over every reachable carry state (`+ − ~ & | ^`, small left shifts
    /// and products by small constants).
    pub carries: u64,
    /// Decided over abstracted atoms.
    pub compositional: u64,
    /// Decided case by case over a few bits of one variable: bits it is read through a narrow
    /// mask at (`x & 1`), or low bits that bitwise operations with constants read (`x ^ 1`).
    pub split: u64,
    /// Decided after bitwise operations with constants that read only known bits were read as
    /// arithmetic (`−2·(x & 1) | 1` as `−2·(x & 1) + 1`).
    pub known_bits: u64,
    /// Points evaluated.
    pub points: u64,
    /// Tests skipped for lack of budget.
    pub over_budget: u64,
    /// Internal inconsistencies (never expected).
    pub internal: u64,
}

impl CertStats {
    /// Adds another call's counters.
    pub fn absorb(&mut self, o: &CertStats) {
        let CertStats {
            calls,
            proved,
            refuted,
            unknown,
            signature,
            single_bit,
            sparse,
            grid,
            exhaustive,
            symbolic,
            carries,
            compositional,
            split,
            known_bits,
            points,
            over_budget,
            internal,
        } = o;
        self.calls += calls;
        self.proved += proved;
        self.refuted += refuted;
        self.unknown += unknown;
        self.signature += signature;
        self.single_bit += single_bit;
        self.sparse += sparse;
        self.grid += grid;
        self.exhaustive += exhaustive;
        self.symbolic += symbolic;
        self.carries += carries;
        self.compositional += compositional;
        self.split += split;
        self.known_bits += known_bits;
        self.points += points;
        self.over_budget += over_budget;
        self.internal += internal;
    }

    /// Adds a report.
    #[cfg(feature = "mba")]
    pub(crate) fn record(&mut self, r: &crate::mba::certify::Report) {
        use crate::mba::Verdict;
        use crate::mba::certify::Cert;
        self.calls += 1;
        match r.verdict {
            Verdict::Proved => self.proved += 1,
            Verdict::Refuted => self.refuted += 1,
            Verdict::Unknown => self.unknown += 1,
        }
        if r.verdict != Verdict::Unknown {
            match r.cert {
                Some(Cert::Signature) => self.signature += 1,
                Some(Cert::SingleBit) => self.single_bit += 1,
                Some(Cert::Sparse) => self.sparse += 1,
                Some(Cert::Grid) => self.grid += 1,
                Some(Cert::Exhaustive) => self.exhaustive += 1,
                Some(Cert::Symbolic) => self.symbolic += 1,
                Some(Cert::Carries) => self.carries += 1,
                None => {}
            }
            if r.compositional {
                self.compositional += 1;
            }
            if r.split {
                self.split += 1;
            }
            if r.known_bits {
                self.known_bits += 1;
            }
        }
        self.points += r.points;
        self.over_budget += u64::from(r.over_budget);
        self.internal += r.internal;
    }
}

/// Counters for one normal-form pass.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct PassCounts {
    /// Nodes the pass considered.
    pub calls: u64,
    /// Nodes where it produced the node itself.
    pub noop: u64,
    /// Nodes it replaced.
    pub changed: u64,
    /// Candidates rejected because they would not make the DAG smaller.
    pub rejected_cost: u64,
    /// Candidates rejected by a postcondition or vetoed by the host.
    pub rejected: u64,
    /// Regions over the pass's size cap, treated as opaque atoms.
    pub atomized: u64,
}

impl PassCounts {
    /// Adds another call's counters.
    pub fn absorb(&mut self, o: &PassCounts) {
        let PassCounts {
            calls,
            noop,
            changed,
            rejected_cost,
            rejected,
            atomized,
        } = o;
        self.calls += calls;
        self.noop += noop;
        self.changed += changed;
        self.rejected_cost += rejected_cost;
        self.rejected += rejected;
        self.atomized += atomized;
    }
}

/// Why an application was rejected after its rule applied.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Reject {
    /// The result's width differs from the node's (a compiler or program defect).
    Width,
    /// Sampled verification found a point where the two sides differ.
    Verify,
    /// The fact tripwire found incompatible facts.
    Tripwire,
    /// The result is not smaller in the ground termination order.
    Termination,
}

/// What made a rewrite: a rule, or a normal-form pass (by name).
#[derive(Copy, Clone, Debug)]
#[non_exhaustive]
pub enum By<'a> {
    /// A linked rule.
    Rule(&'a Rule),
    /// A normal-form pass, e.g. `"linear"`.
    Pass(&'static str),
}

impl By<'_> {
    /// `group::rule`, or the pass's name.
    pub fn name(&self) -> &str {
        match self {
            By::Rule(r) => &r.name,
            By::Pass(p) => p,
        }
    }
}

/// A per-rule event.
#[derive(Copy, Clone, Debug)]
#[non_exhaustive]
pub enum Event<'a> {
    /// `rule` is a candidate at `node` (after the dispatch prefilter).
    Candidate {
        /// The rule.
        rule: &'a Rule,
        /// The node.
        node: Expr,
    },
    /// The pattern did not match.
    NoMatch {
        /// The rule.
        rule: &'a Rule,
    },
    /// The pattern matched but the guard did not hold.
    GuardFalse {
        /// The rule.
        rule: &'a Rule,
    },
    /// Declined for lack of work or facts.
    Degraded {
        /// The rule.
        rule: &'a Rule,
    },
    /// Applied, but produced the node itself.
    NoChange {
        /// The rule.
        rule: &'a Rule,
    },
    /// A rule or pass rewrote `before` to `after`.
    Applied {
        /// What rewrote it.
        by: By<'a>,
        /// The node rewritten.
        before: Expr,
        /// Its replacement.
        after: Expr,
    },
    /// The host vetoed the application.
    Vetoed {
        /// What proposed it.
        by: By<'a>,
    },
    /// A postcondition rejected the application.
    Rejected {
        /// What proposed it.
        by: By<'a>,
        /// Which one.
        reason: Reject,
    },
}

/// Receives per-rule and per-pass events. With no observer the cost is one predictable branch per event.
pub trait Observer {
    /// Called for every event, in order.
    fn event(&mut self, event: Event<'_>);
}

/// Per-rule counts, keyed by `group::rule`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct RuleCensus {
    /// The counts.
    pub rules: BTreeMap<String, RuleCounts>,
}

/// Counts for one rule.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct RuleCounts {
    /// Times it was a candidate.
    pub candidates: u64,
    /// Times its pattern did not match.
    pub no_match: u64,
    /// Times its guard did not hold.
    pub guard_false: u64,
    /// Times it was declined for lack of work or facts.
    pub degraded: u64,
    /// Times it applied but produced the node itself.
    pub no_change: u64,
    /// Times it applied.
    pub applied: u64,
    /// Times it was vetoed or rejected.
    pub rejected: u64,
}

impl Observer for RuleCensus {
    fn event(&mut self, event: Event<'_>) {
        let (rule, f): (&Rule, fn(&mut RuleCounts)) = match event {
            Event::Candidate { rule, .. } => (rule, |c| c.candidates += 1),
            Event::NoMatch { rule } => (rule, |c| c.no_match += 1),
            Event::GuardFalse { rule } => (rule, |c| c.guard_false += 1),
            Event::Degraded { rule } => (rule, |c| c.degraded += 1),
            Event::NoChange { rule } => (rule, |c| c.no_change += 1),
            Event::Applied {
                by: By::Rule(rule), ..
            } => (rule, |c| c.applied += 1),
            Event::Vetoed { by: By::Rule(rule) }
            | Event::Rejected {
                by: By::Rule(rule), ..
            } => (rule, |c| c.rejected += 1),
            // Pass events are not per-rule.
            _ => return,
        };
        f(self.rules.entry(rule.name.clone()).or_default());
    }
}

/// Deterministic host policy. Its [`revision`](Hooks::revision) is part of the memo epoch, so
/// change it whenever the policy changes.
pub trait Hooks {
    /// Whether to accept rewriting `before` to `after` by a rule or a pass.
    fn admit(&self, cx: &Context, before: Expr, after: Expr, by: By<'_>) -> bool {
        let _ = (cx, before, after, by);
        true
    }

    /// Whether a pass may replace `e`, whose facts pin its value (or, for the demanded-bits
    /// pass, the bits of it that are observed), by a constant.
    fn fold_known(&self, cx: &Context, e: Expr) -> bool {
        let _ = (cx, e);
        true
    }

    /// A number that changes whenever the policy does.
    fn revision(&self) -> u64 {
        0
    }
}
