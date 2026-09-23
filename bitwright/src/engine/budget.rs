//! Budgets, allowances, admission caps and deadlines.

use core::fmt;

/// Caps on the work of one call, or what remains of an [`Allowance`]. Every field counts a unit
/// of the fixed charging schedule (see each field); `u64::MAX` is unlimited.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Budget {
    /// Nodes visited by a phase (one per node per visit; a node answered from the memo is
    /// free), and nodes evaluated by sampled verification.
    pub node_visits: u64,
    /// Candidate rules tried (one per candidate after the dispatch prefilter).
    pub candidates: u64,
    /// Matcher steps (one per pattern/node pair).
    pub match_steps: u64,
    /// Rewrites committed.
    pub rewrites: u64,
    /// Nodes created.
    pub new_nodes: u64,
    /// Fact transfer functions run for guards and passes.
    pub fact_work: u64,
    /// Normal-form pass work (one per node a pass reads or emits).
    pub pass_work: u64,
    /// Calls to the MBA solver.
    pub mba_calls: u64,
    /// E-nodes inserted by the equality-saturation search.
    pub eqsat_nodes: u64,
    /// Equality-saturation work (matching, unions, repairs, extraction).
    pub eqsat_work: u64,
}

impl Budget {
    /// No limits.
    pub const UNLIMITED: Budget = Budget {
        node_visits: u64::MAX,
        candidates: u64::MAX,
        match_steps: u64::MAX,
        rewrites: u64::MAX,
        new_nodes: u64::MAX,
        fact_work: u64::MAX,
        pass_work: u64::MAX,
        mba_calls: u64::MAX,
        eqsat_nodes: u64::MAX,
        eqsat_work: u64::MAX,
    };

    /// Nothing spent.
    pub const ZERO: Budget = Budget {
        node_visits: 0,
        candidates: 0,
        match_steps: 0,
        rewrites: 0,
        new_nodes: 0,
        fact_work: 0,
        pass_work: 0,
        mba_calls: 0,
        eqsat_nodes: 0,
        eqsat_work: 0,
    };

    /// Field-wise minimum.
    pub fn min(&self, o: &Budget) -> Budget {
        self.zip(o, u64::min)
    }

    fn zip(&self, o: &Budget, f: impl Fn(u64, u64) -> u64) -> Budget {
        Budget {
            node_visits: f(self.node_visits, o.node_visits),
            candidates: f(self.candidates, o.candidates),
            match_steps: f(self.match_steps, o.match_steps),
            rewrites: f(self.rewrites, o.rewrites),
            new_nodes: f(self.new_nodes, o.new_nodes),
            fact_work: f(self.fact_work, o.fact_work),
            pass_work: f(self.pass_work, o.pass_work),
            mba_calls: f(self.mba_calls, o.mba_calls),
            eqsat_nodes: f(self.eqsat_nodes, o.eqsat_nodes),
            eqsat_work: f(self.eqsat_work, o.eqsat_work),
        }
    }

    pub(crate) fn saturating_sub(&self, o: &Budget) -> Budget {
        self.zip(o, u64::saturating_sub)
    }

    pub(crate) fn saturating_add(&self, o: &Budget) -> Budget {
        self.zip(o, u64::saturating_add)
    }
}

impl Default for Budget {
    /// Generous caps for one call: 2^22 visits, candidates, rewrites and new nodes, 2^26
    /// matcher steps, fact transfers and pass work, 4096 MBA solver calls.
    fn default() -> Self {
        Budget {
            node_visits: 1 << 22,
            candidates: 1 << 22,
            match_steps: 1 << 26,
            rewrites: 1 << 22,
            new_nodes: 1 << 22,
            fact_work: 1 << 26,
            pass_work: 1 << 26,
            mba_calls: 1 << 12,
            eqsat_nodes: 1 << 22,
            eqsat_work: 1 << 26,
        }
    }
}

setters!(Budget {
    with_node_visits: node_visits: u64,
    with_candidates: candidates: u64,
    with_match_steps: match_steps: u64,
    with_rewrites: rewrites: u64,
    with_new_nodes: new_nodes: u64,
    with_fact_work: fact_work: u64,
    with_pass_work: pass_work: u64,
    with_mba_calls: mba_calls: u64,
    with_eqsat_nodes: eqsat_nodes: u64,
    with_eqsat_work: eqsat_work: u64,
});

/// Which limit stopped a run.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Exhausted {
    /// [`Budget::node_visits`].
    NodeVisits,
    /// [`Budget::candidates`].
    Candidates,
    /// [`Budget::match_steps`].
    MatchSteps,
    /// [`Budget::rewrites`].
    Rewrites,
    /// [`Budget::new_nodes`].
    NewNodes,
    /// [`Budget::fact_work`].
    FactWork,
    /// [`Budget::pass_work`].
    PassWork,
    /// [`Budget::mba_calls`].
    MbaCalls,
    /// [`Budget::eqsat_nodes`].
    EqsatNodes,
    /// [`Budget::eqsat_work`].
    EqsatWork,
    /// The [`Deadline`] passed.
    Deadline,
    /// The context's node capacity ([`ContextConfig::max_nodes`](crate::ContextConfig)).
    ArenaCapacity,
}

impl fmt::Display for Exhausted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Exhausted::NodeVisits => "node visits",
            Exhausted::Candidates => "candidates",
            Exhausted::MatchSteps => "matcher steps",
            Exhausted::Rewrites => "rewrites",
            Exhausted::NewNodes => "new nodes",
            Exhausted::FactWork => "fact work",
            Exhausted::PassWork => "pass work",
            Exhausted::MbaCalls => "MBA solver calls",
            Exhausted::EqsatNodes => "e-nodes",
            Exhausted::EqsatWork => "equality-saturation work",
            Exhausted::Deadline => "deadline",
            Exhausted::ArenaCapacity => "arena capacity",
        })
    }
}

/// A spendable account shared by any number of calls (for example every block of one pass).
/// Spent work is never refunded.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Allowance {
    remaining: Budget,
    spent: Budget,
}

impl Allowance {
    /// An account holding `budget`.
    pub fn new(budget: Budget) -> Self {
        Allowance {
            remaining: budget,
            spent: Budget::ZERO,
        }
    }

    /// What is left.
    pub fn remaining(&self) -> Budget {
        self.remaining
    }

    /// What has been spent.
    pub fn spent(&self) -> Budget {
        self.spent
    }

    pub(crate) fn spend(&mut self, b: &Budget) {
        self.remaining = self.remaining.saturating_sub(b);
        self.spent = self.spent.saturating_add(b);
    }
}

/// Per-root caps checked before any work, from O(1) node metadata (and, if set, a bounded DAG
/// size). A root over a cap is declined unchanged.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Admission {
    /// Maximum height of a root.
    pub max_root_height: u32,
    /// Maximum size of a root unfolded as a tree (saturating; see [`Context::tree_size`](crate::Context::tree_size)).
    pub max_root_tree_size: u32,
    /// Maximum number of distinct nodes under a root, if checked (a walk of up to that many
    /// nodes, not charged to the budget).
    pub max_root_dag_size: Option<u32>,
}

impl Default for Admission {
    /// No caps.
    fn default() -> Self {
        Admission {
            max_root_height: u32::MAX,
            max_root_tree_size: u32::MAX,
            max_root_dag_size: None,
        }
    }
}

setters!(Admission {
    with_max_root_height: max_root_height: u32,
    with_max_root_tree_size: max_root_tree_size: u32,
    with_max_root_dag_size: max_root_dag_size ? u32,
});

/// Which admission cap declined a root.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Cap {
    /// [`Admission::max_root_height`].
    Height,
    /// [`Admission::max_root_tree_size`].
    TreeSize,
    /// [`Admission::max_root_dag_size`].
    DagSize,
}

/// A monotone tick source supplied by the host (the library never reads a clock itself).
pub trait Clock {
    /// The current time, in any unit.
    fn now_ticks(&self) -> u64;
}

/// Stop once `clock` reaches `at`, checking every `check_every` node visits. Deadlines make
/// results depend on timing; budgets are the deterministic alternative.
#[derive(Copy, Clone)]
#[non_exhaustive]
pub struct Deadline<'a> {
    /// The clock.
    pub clock: &'a dyn Clock,
    /// The tick at which to stop.
    pub at: u64,
    /// Visits between clock reads (at least 1).
    pub check_every: u32,
}

impl<'a> Deadline<'a> {
    /// Stop once `clock` reaches `at`, reading it every 64 charges.
    pub fn new(clock: &'a dyn Clock, at: u64) -> Self {
        Deadline {
            clock,
            at,
            check_every: 64,
        }
    }
}

setters!(Deadline<'a> {
    with_check_every: check_every: u32,
});

impl fmt::Debug for Deadline<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Deadline")
            .field("at", &self.at)
            .field("check_every", &self.check_every)
            .finish_non_exhaustive()
    }
}

/// A field of [`Budget`] charged before its work, for [`Meter::charge`]. (Matcher steps, fact
/// work and new nodes are capped beforehand and recorded when done; see [`Meter`].)
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[cfg_attr(not(all(feature = "mba", feature = "eqsat")), allow(dead_code))] // per feature
pub(crate) enum Counter {
    NodeVisits,
    Candidates,
    Rewrites,
    PassWork,
    MbaCalls,
    EqsatNodes,
    EqsatWork,
}

impl Counter {
    fn of(self, b: &Budget) -> u64 {
        match self {
            Counter::NodeVisits => b.node_visits,
            Counter::Candidates => b.candidates,
            Counter::Rewrites => b.rewrites,
            Counter::PassWork => b.pass_work,
            Counter::MbaCalls => b.mba_calls,
            Counter::EqsatNodes => b.eqsat_nodes,
            Counter::EqsatWork => b.eqsat_work,
        }
    }

    fn slot(self, b: &mut Budget) -> &mut u64 {
        match self {
            Counter::NodeVisits => &mut b.node_visits,
            Counter::Candidates => &mut b.candidates,
            Counter::Rewrites => &mut b.rewrites,
            Counter::PassWork => &mut b.pass_work,
            Counter::MbaCalls => &mut b.mba_calls,
            Counter::EqsatNodes => &mut b.eqsat_nodes,
            Counter::EqsatWork => &mut b.eqsat_work,
        }
    }

    fn exhausted(self) -> Exhausted {
        match self {
            Counter::NodeVisits => Exhausted::NodeVisits,
            Counter::Candidates => Exhausted::Candidates,
            Counter::Rewrites => Exhausted::Rewrites,
            Counter::PassWork => Exhausted::PassWork,
            Counter::MbaCalls => Exhausted::MbaCalls,
            Counter::EqsatNodes => Exhausted::EqsatNodes,
            Counter::EqsatWork => Exhausted::EqsatWork,
        }
    }
}

/// Charges work against the effective limits of one call.
///
/// Work about to be done is charged with [`charge`](Meter::charge), which refuses it (charging
/// nothing) when the limit cannot cover it, and a call against an exhausted allowance does no
/// such work at all. Work whose amount is known only afterwards is bounded beforehand and
/// recorded when done: a fact query runs under a cap of what remains of `fact_work` (a rule
/// application's queries share one), the matcher under what remains of `match_steps`, and
/// building under an arena allowance of what remains of `new_nodes`. So a call never spends past
/// its limit. Every charge also counts toward the deadline's clock reads.
pub(crate) struct Meter<'a> {
    pub(crate) limit: Budget,
    pub(crate) spent: Budget,
    deadline: Option<Deadline<'a>>,
    until_check: u32,
    /// Latched once the deadline has passed: every later visit fails at once.
    expired: bool,
}

impl<'a> Meter<'a> {
    pub(crate) fn new(limit: Budget, deadline: Option<Deadline<'a>>) -> Self {
        Meter {
            limit,
            spent: Budget::ZERO,
            deadline,
            until_check: 0,
            expired: false,
        }
    }

    fn over(&self) -> Option<Exhausted> {
        let (s, l) = (&self.spent, &self.limit);
        if s.node_visits > l.node_visits {
            Some(Exhausted::NodeVisits)
        } else if s.candidates > l.candidates {
            Some(Exhausted::Candidates)
        } else if s.match_steps > l.match_steps {
            Some(Exhausted::MatchSteps)
        } else if s.rewrites > l.rewrites {
            Some(Exhausted::Rewrites)
        } else if s.new_nodes > l.new_nodes {
            Some(Exhausted::NewNodes)
        } else if s.fact_work > l.fact_work {
            Some(Exhausted::FactWork)
        } else if s.pass_work > l.pass_work {
            Some(Exhausted::PassWork)
        } else if s.mba_calls > l.mba_calls {
            Some(Exhausted::MbaCalls)
        } else if s.eqsat_nodes > l.eqsat_nodes {
            Some(Exhausted::EqsatNodes)
        } else if s.eqsat_work > l.eqsat_work {
            Some(Exhausted::EqsatWork)
        } else {
            None
        }
    }

    /// Reads the deadline's clock when due; latched once it has passed.
    fn tick(&mut self) -> Result<(), Exhausted> {
        if self.expired {
            return Err(Exhausted::Deadline);
        }
        if let Some(d) = self.deadline {
            if self.until_check == 0 {
                self.until_check = d.check_every.max(1);
                if d.clock.now_ticks() >= d.at {
                    self.expired = true;
                    return Err(Exhausted::Deadline);
                }
            }
            self.until_check -= 1;
        }
        Ok(())
    }

    /// Reads the deadline's clock now (not when due); latched once it has passed.
    #[cfg_attr(not(feature = "eqsat"), allow(dead_code))]
    pub(crate) fn deadline_now(&mut self) -> Result<(), Exhausted> {
        if self.expired {
            return Err(Exhausted::Deadline);
        }
        if let Some(d) = self.deadline
            && d.clock.now_ticks() >= d.at
        {
            self.expired = true;
            return Err(Exhausted::Deadline);
        }
        Ok(())
    }

    /// Charges `n` units of `c` for work about to be done, or refuses (charging nothing) when
    /// the limit cannot cover them. Reads the deadline when due.
    pub(crate) fn charge(&mut self, c: Counter, n: u64) -> Result<(), Exhausted> {
        self.tick()?;
        // A counter recorded after the fact may already be over: then nothing is charged.
        self.check()?;
        let spent = c.slot(&mut self.spent);
        let after = spent.saturating_add(n);
        if after > c.of(&self.limit) {
            return Err(c.exhausted());
        }
        *spent = after;
        self.check()
    }

    /// Charges one node visit.
    pub(crate) fn visit(&mut self) -> Result<(), Exhausted> {
        self.charge(Counter::NodeVisits, 1)
    }

    /// Whether every limit still holds (and the deadline has not been seen to pass).
    pub(crate) fn check(&self) -> Result<(), Exhausted> {
        if self.expired {
            return Err(Exhausted::Deadline);
        }
        match self.over() {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    pub(crate) fn left(&self) -> Budget {
        self.limit.saturating_sub(&self.spent)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Ticks(core::cell::Cell<u64>);
    impl Clock for Ticks {
        fn now_ticks(&self) -> u64 {
            let t = self.0.get();
            self.0.set(t + 1);
            t
        }
    }

    #[test]
    fn a_charge_the_limit_cannot_cover_is_refused_and_not_charged() {
        let mut limit = Budget::UNLIMITED;
        limit.pass_work = 10;
        let mut m = Meter::new(limit, None);
        assert_eq!(m.charge(Counter::PassWork, 7), Ok(()));
        assert_eq!(m.charge(Counter::PassWork, 4), Err(Exhausted::PassWork));
        assert_eq!(m.spent.pass_work, 7);
        assert_eq!(m.charge(Counter::PassWork, 3), Ok(()));
        assert_eq!(m.charge(Counter::PassWork, 1), Err(Exhausted::PassWork));
        assert_eq!(m.spent.pass_work, 10);
        // A zero limit refuses everything and charges nothing.
        let mut limit = Budget::UNLIMITED;
        limit.eqsat_nodes = 0;
        let mut m = Meter::new(limit, None);
        assert_eq!(m.charge(Counter::EqsatNodes, 1), Err(Exhausted::EqsatNodes));
        assert_eq!(m.spent, Budget::ZERO);
        // Another counter already over (recorded after the fact): refused, nothing charged.
        let mut limit = Budget::UNLIMITED;
        limit.fact_work = 5;
        let mut m = Meter::new(limit, None);
        m.spent.fact_work = 10;
        assert_eq!(m.charge(Counter::MbaCalls, 1), Err(Exhausted::FactWork));
        assert_eq!(m.spent.mba_calls, 0);
    }

    #[test]
    fn every_charge_reads_the_deadline_when_due_and_the_stop_latches() {
        let clock = Ticks(core::cell::Cell::new(0));
        let d = Deadline {
            clock: &clock,
            at: 3,
            check_every: 2,
        };
        let mut m = Meter::new(Budget::UNLIMITED, Some(d));
        // Reads at charges 1, 3, 5, …: ticks 0, 1, 2, then 3 stops.
        for _ in 0..6 {
            assert_eq!(m.charge(Counter::EqsatWork, 1), Ok(()));
        }
        assert_eq!(m.charge(Counter::EqsatWork, 1), Err(Exhausted::Deadline));
        assert_eq!(m.check(), Err(Exhausted::Deadline));
        assert_eq!(m.visit(), Err(Exhausted::Deadline));
        assert_eq!(clock.0.get(), 4);
    }
}
