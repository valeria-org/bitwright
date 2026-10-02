//! A conflict-driven clause-learning SAT solver: two watched literals with blockers, VSIDS
//! decisions with phase saving, first-UIP learning with recursive minimization, Luby restarts,
//! and a learned-clause database reduced by literal block distance. Every learned clause is a
//! reverse-unit-propagation (RUP) consequence of the clauses before it, so the solver can log
//! a DRUP proof (additions and deletions) that [`super::drup`] checks independently.
//!
//! Written from the published descriptions of these techniques (Marques-Silva and Sakallah's
//! GRASP learning, Moskewicz et al.'s watched literals and VSIDS, Eén and Sörensson's MiniSat
//! paper, Audemard and Simon's LBD, Wetzler, Heule and Hunt's DRAT format), not from any
//! solver's code.

/// A variable, from 0.
pub type Var = u32;

/// A literal: `2·var` for the positive one, `2·var + 1` for the negative.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(pub u32);

impl Lit {
    /// The positive literal of `v`.
    pub fn pos(v: Var) -> Lit {
        Lit(v << 1)
    }
    /// The negative literal of `v`.
    pub fn neg(v: Var) -> Lit {
        Lit((v << 1) | 1)
    }
    /// `v` if `positive`, else `¬v`.
    pub fn new(v: Var, positive: bool) -> Lit {
        Lit((v << 1) | u32::from(!positive))
    }
    /// The variable.
    pub fn var(self) -> Var {
        self.0 >> 1
    }
    /// Whether the literal is negative.
    pub fn is_neg(self) -> bool {
        self.0 & 1 == 1
    }
    /// DIMACS form: `var + 1`, negated if negative.
    pub fn dimacs(self) -> i64 {
        let v = i64::from(self.var()) + 1;
        if self.is_neg() { -v } else { v }
    }
}

impl core::ops::Not for Lit {
    type Output = Lit;
    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

/// A step of a DRUP proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// A clause added (implied by reverse unit propagation).
    Add(Vec<Lit>),
    /// A clause deleted.
    Delete(Vec<Lit>),
}

/// The answer of [`Solver::solve`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer {
    /// Satisfiable: the value of every variable.
    Sat(Vec<bool>),
    /// Unsatisfiable (with a proof, when logging was on).
    Unsat,
    /// A limit was reached: another call goes on from here.
    Unknown,
}

/// The most work one call of [`Solver::solve_within`] may do, counted from the call's start.
/// Both counters are deterministic: the same clauses and limits give the same answer.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Conflicts.
    pub conflicts: u64,
    /// Propagations (literals propagated), which track the time a call takes more closely than
    /// conflicts do: each conflict costs more propagation on a larger formula.
    pub propagations: u64,
}

impl Limits {
    /// At most `conflicts` conflicts, and any number of propagations.
    pub fn conflicts(conflicts: u64) -> Limits {
        Limits {
            conflicts,
            propagations: u64::MAX,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Value {
    True,
    False,
    Unset,
}

/// A clause: its literals are `arena[start..start + len]`, the two watched ones first.
#[derive(Copy, Clone)]
struct Clause {
    start: u32,
    len: u32,
    lbd: u32,
    activity: f32,
    learnt: bool,
    deleted: bool,
}

#[derive(Copy, Clone)]
struct Watch {
    clause: u32,
    /// A literal of the clause: when it is true, the clause is (for a binary clause, the other
    /// literal, which the watched one's falsity implies).
    blocker: Lit,
}

/// A CDCL solver. Clauses are added, then [`solve`](Self::solve) is called; a call that ends
/// on its limits keeps the search where it stopped, so the next call goes on from there, and
/// calls of `a` then `b` conflicts do exactly what one call of `a + b` would. Adding a clause
/// after a call starts the search again from the top level, keeping what was learned.
pub struct Solver {
    clauses: Vec<Clause>,
    /// Every clause's literals, one after another.
    arena: Vec<Lit>,
    /// Reused while normalizing incoming clauses; never retained as a clause's storage.
    clause_buffer: Vec<Lit>,
    /// Literals of deleted clauses still in the arena.
    wasted: usize,
    /// Clauses of three or more literals, under the negation of each watched literal.
    watches: Vec<Vec<Watch>>,
    /// Binary clauses, likewise (the other literal as the blocker).
    bins: Vec<Vec<Watch>>,
    values: Vec<Value>,
    level: Vec<u32>,
    reason: Vec<Option<u32>>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,
    activity: Vec<f64>,
    var_inc: f64,
    cla_inc: f32,
    heap: Heap,
    phase: Vec<bool>,
    seen: Vec<u8>,
    /// The formula is already contradictory (an empty clause, or a top-level conflict).
    unsat: bool,
    proof: Option<Vec<Step>>,
    /// Restarts so far (the index into the Luby sequence).
    restarts: u32,
    /// Conflicts since the last restart.
    here: u64,
    /// When to reduce the learned clauses next (in conflicts).
    next_reduce: u64,
    /// Learned clauses not deleted.
    learnts: usize,
    /// Conflicts so far.
    pub conflicts: u64,
    /// Decisions so far.
    pub decisions: u64,
    /// Propagations so far.
    pub propagations: u64,
}

impl core::fmt::Debug for Solver {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Solver")
            .field("vars", &self.values.len())
            .field("clauses", &self.clauses.len())
            .field("conflicts", &self.conflicts)
            .field("decisions", &self.decisions)
            .finish()
    }
}

impl Default for Solver {
    fn default() -> Self {
        Solver::new()
    }
}

impl Solver {
    /// An empty solver.
    pub fn new() -> Solver {
        Solver {
            clauses: Vec::new(),
            arena: Vec::new(),
            clause_buffer: Vec::new(),
            wasted: 0,
            watches: Vec::new(),
            bins: Vec::new(),
            values: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            activity: Vec::new(),
            var_inc: 1.0,
            cla_inc: 1.0,
            heap: Heap::default(),
            phase: Vec::new(),
            seen: Vec::new(),
            unsat: false,
            proof: None,
            restarts: 0,
            here: 0,
            next_reduce: 2000,
            learnts: 0,
            conflicts: 0,
            decisions: 0,
            propagations: 0,
        }
    }

    /// Records a DRUP proof of every learned and deleted clause.
    pub fn log_proof(&mut self) {
        self.proof = Some(Vec::new());
    }

    /// The proof logged so far (see [`log_proof`](Self::log_proof)).
    pub fn take_proof(&mut self) -> Option<Vec<Step>> {
        self.proof.take()
    }

    /// The number of variables.
    pub fn num_vars(&self) -> u32 {
        self.values.len() as u32
    }

    /// The number of clauses kept, learned ones included (units are assignments, not
    /// clauses).
    pub fn num_clauses(&self) -> usize {
        self.clauses.iter().filter(|c| !c.deleted).count()
    }

    /// The number of learned clauses kept.
    pub fn num_learnts(&self) -> usize {
        self.learnts
    }

    /// A new variable.
    pub fn new_var(&mut self) -> Var {
        let v = self.values.len() as u32;
        self.values.push(Value::Unset);
        self.level.push(0);
        self.reason.push(None);
        self.activity.push(0.0);
        self.phase.push(false);
        self.seen.push(0);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        self.bins.push(Vec::new());
        self.bins.push(Vec::new());
        self.heap.insert(v, &self.activity);
        v
    }

    fn value(&self, l: Lit) -> Value {
        match self.values[l.var() as usize] {
            Value::Unset => Value::Unset,
            v => {
                if (v == Value::True) != l.is_neg() {
                    Value::True
                } else {
                    Value::False
                }
            }
        }
    }

    pub(super) fn prefer_selector(&mut self, l: Lit) {
        self.activity[l.var() as usize] = 0.5;
        self.phase[l.var() as usize] = l.is_neg();
        self.heap.decrease(l.var(), &self.activity);
    }

    fn lits(&self, c: u32) -> &[Lit] {
        let c = self.clauses[c as usize];
        &self.arena[c.start as usize..(c.start + c.len) as usize]
    }

    /// Adds a clause (the search goes back to the top level first). Returns `false` when the
    /// formula is now known unsatisfiable.
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        self.add_incoming_clause(lits, false, None)
    }

    /// Initial watches for an encoding clause may follow its gate's roles instead of the
    /// numeric variable order. Normalization and proof premises remain unchanged.
    pub(super) fn add_clause_watching(&mut self, lits: &[Lit], watches: [Lit; 2]) -> bool {
        self.add_incoming_clause(lits, false, Some(watches))
    }

    /// A RUP consequence established by native preprocessing, logged as a proof step rather
    /// than admitted as an additional premise. Binary consequences are retained glue clauses.
    pub(super) fn add_rup_clause(&mut self, lits: &[Lit]) -> bool {
        if self.unsat {
            return false;
        }
        if let Some(proof) = &mut self.proof {
            proof.push(Step::Add(lits.to_vec()));
        }
        self.add_incoming_clause(lits, true, None)
    }

    #[cfg(test)]
    pub(super) fn proof_steps(&self) -> Option<&[Step]> {
        self.proof.as_deref()
    }

    fn add_incoming_clause(
        &mut self,
        lits: &[Lit],
        learnt: bool,
        watches: Option<[Lit; 2]>,
    ) -> bool {
        if self.unsat {
            return false;
        }
        let mut buffer = core::mem::take(&mut self.clause_buffer);
        buffer.clear();
        buffer.extend_from_slice(lits);
        let result = self.add_buffered_clause(&mut buffer, learnt, watches);
        self.clause_buffer = buffer;
        result
    }

    fn add_buffered_clause(
        &mut self,
        c: &mut Vec<Lit>,
        learnt: bool,
        watches: Option<[Lit; 2]>,
    ) -> bool {
        self.cancel_until(0);
        c.sort_unstable();
        c.dedup();
        // A tautology is always true.
        if c.windows(2).any(|w| w[0].var() == w[1].var()) {
            return true;
        }
        for &l in c.iter() {
            while l.var() >= self.num_vars() {
                self.new_var();
            }
        }
        // Literals false at level 0 are dropped (the propagation that made them false is a
        // RUP step, so the shorter clause is too); a true one satisfies the clause.
        if c.iter().any(|&l| self.value(l) == Value::True) {
            return true;
        }
        let original_len = c.len();
        c.retain(|&l| self.value(l) != Value::False);
        if c.len() != original_len
            && let Some(p) = &mut self.proof
        {
            p.push(Step::Add(c.clone()));
        }
        match c.len() {
            0 => {
                self.unsat = true;
                false
            }
            1 => {
                self.assign(c[0], None);
                if self.propagate().is_some() {
                    self.unsat = true;
                    if let Some(p) = &mut self.proof {
                        p.push(Step::Add(Vec::new()));
                    }
                    return false;
                }
                true
            }
            _ => {
                if let Some(watches) = watches {
                    let mut selected = 0;
                    for wanted in watches {
                        if let Some(i) = c[selected..].iter().position(|&l| l == wanted) {
                            c.swap(selected, selected + i);
                            selected += 1;
                        }
                    }
                }
                self.attach(c, learnt, if learnt { 2 } else { 0 });
                true
            }
        }
    }

    fn attach(&mut self, lits: &[Lit], learnt: bool, lbd: u32) -> u32 {
        let idx = self.clauses.len() as u32;
        let list = if lits.len() == 2 {
            &mut self.bins
        } else {
            &mut self.watches
        };
        list[(!lits[0]).0 as usize].push(Watch {
            clause: idx,
            blocker: lits[1],
        });
        list[(!lits[1]).0 as usize].push(Watch {
            clause: idx,
            blocker: lits[0],
        });
        self.clauses.push(Clause {
            start: self.arena.len() as u32,
            len: lits.len() as u32,
            lbd,
            activity: 0.0,
            learnt,
            deleted: false,
        });
        self.arena.extend_from_slice(lits);
        self.learnts += usize::from(learnt);
        idx
    }

    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    fn assign(&mut self, l: Lit, reason: Option<u32>) {
        let v = l.var() as usize;
        self.values[v] = if l.is_neg() {
            Value::False
        } else {
            Value::True
        };
        self.level[v] = self.decision_level();
        self.reason[v] = reason;
        self.trail.push(l);
    }

    /// Unit propagation from `qhead`: the conflicting clause, if any.
    fn propagate(&mut self) -> Option<u32> {
        self.propagate_until(u64::MAX)
    }

    /// Complete each literal's watch list before pausing, leaving the remaining trail queued.
    fn propagate_until(&mut self, stop: u64) -> Option<u32> {
        while self.qhead < self.trail.len() && self.propagations < stop {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            self.propagations += 1;
            // Binary clauses with ¬p: the other literal holds.
            let pi = p.0 as usize;
            for k in 0..self.bins[pi].len() {
                let w = self.bins[pi][k];
                match self.value(w.blocker) {
                    Value::True => {}
                    Value::Unset => self.assign(w.blocker, Some(w.clause)),
                    Value::False => {
                        self.qhead = self.trail.len();
                        return Some(w.clause);
                    }
                }
            }
            // Longer clauses watching ¬p (watched under the literal that became false).
            let mut ws = core::mem::take(&mut self.watches[pi]);
            let false_lit = !p;
            let mut i = 0;
            let mut j = 0;
            let mut conflict = None;
            while i < ws.len() {
                let w = ws[i];
                i += 1;
                if self.value(w.blocker) == Value::True {
                    ws[j] = w;
                    j += 1;
                    continue;
                }
                let c = self.clauses[w.clause as usize];
                if c.deleted {
                    continue;
                }
                let (s, e) = (c.start as usize, (c.start + c.len) as usize);
                // Make the second literal the false one.
                if self.arena[s] == false_lit {
                    self.arena.swap(s, s + 1);
                }
                let first = self.arena[s];
                let kept = Watch {
                    clause: w.clause,
                    blocker: first,
                };
                if first != w.blocker && self.value(first) == Value::True {
                    ws[j] = kept;
                    j += 1;
                    continue;
                }
                // Look for a new literal to watch.
                let mut found = false;
                for k in s + 2..e {
                    let l = self.arena[k];
                    if self.value(l) != Value::False {
                        self.arena.swap(s + 1, k);
                        self.watches[(!l).0 as usize].push(kept);
                        found = true;
                        break;
                    }
                }
                if found {
                    continue;
                }
                ws[j] = kept;
                j += 1;
                if self.value(first) == Value::False {
                    conflict = Some(w.clause);
                    self.qhead = self.trail.len();
                    while i < ws.len() {
                        ws[j] = ws[i];
                        i += 1;
                        j += 1;
                    }
                } else {
                    self.assign(first, Some(w.clause));
                }
            }
            ws.truncate(j);
            self.watches[pi] = ws;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    fn bump_var(&mut self, v: Var) {
        let a = &mut self.activity[v as usize];
        *a += self.var_inc;
        if *a > 1e100 {
            for x in &mut self.activity {
                *x *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        self.heap.decrease(v, &self.activity);
    }

    fn bump_clause(&mut self, c: u32) {
        let cl = &mut self.clauses[c as usize];
        cl.activity += self.cla_inc;
        if cl.activity > 1e20 {
            for x in &mut self.clauses {
                x.activity *= 1e-20;
            }
            self.cla_inc *= 1e-20;
        }
    }

    /// Makes `l` the first literal of clause `c` (a reason clause, whose implied literal is
    /// `l`).
    fn implied_first(&mut self, c: u32, l: Lit) {
        let cl = self.clauses[c as usize];
        let s = cl.start as usize;
        if self.arena[s] != l {
            let k = self.arena[s..s + cl.len as usize]
                .iter()
                .position(|&x| x == l)
                .unwrap_or(0);
            self.arena.swap(s, s + k);
        }
    }

    /// First-UIP conflict analysis: the learned clause (asserting literal first), the level to
    /// go back to, and its literal block distance.
    fn analyze(&mut self, confl: u32) -> (Vec<Lit>, u32, u32) {
        let mut learnt: Vec<Lit> = vec![Lit(0)];
        let mut path = 0;
        let mut p: Option<Lit> = None;
        let mut idx = self.trail.len();
        let mut confl = Some(confl);
        loop {
            let c = confl.expect("a reason for every implied literal");
            let cl = self.clauses[c as usize];
            if cl.learnt {
                self.bump_clause(c);
            }
            // A reason's first literal is the implied one (`p`), skipped.
            let s = cl.start as usize + usize::from(p.is_some());
            for k in s..(cl.start + cl.len) as usize {
                let q = self.arena[k];
                let v = q.var() as usize;
                if self.seen[v] == 0 && self.level[v] > 0 {
                    self.bump_var(q.var());
                    self.seen[v] = 1;
                    if self.level[v] >= self.decision_level() {
                        path += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            // The next literal of the trail marked seen.
            loop {
                idx -= 1;
                if self.seen[self.trail[idx].var() as usize] != 0 {
                    break;
                }
            }
            let l = self.trail[idx];
            p = Some(l);
            confl = self.reason[l.var() as usize];
            self.seen[l.var() as usize] = 0;
            path -= 1;
            if path == 0 {
                break;
            }
            if let Some(c) = confl {
                self.implied_first(c, l);
            }
        }
        learnt[0] = !p.expect("a UIP");
        // Recursive minimization: drop literals implied by the others.
        let abstract_levels = learnt[1..].iter().fold(0u32, |acc, l| {
            acc | (1 << (self.level[l.var() as usize] & 31))
        });
        let mut kept = vec![learnt[0]];
        let mut to_clear: Vec<Lit> = learnt.clone();
        for &l in &learnt[1..] {
            if self.reason[l.var() as usize].is_none()
                || !self.redundant(l, abstract_levels, &mut to_clear)
            {
                kept.push(l);
            }
        }
        for l in to_clear {
            self.seen[l.var() as usize] = 0;
        }
        // The backtrack level: the highest level among the rest, that literal second.
        let mut bt = 0;
        if kept.len() > 1 {
            let mut max_i = 1;
            for i in 2..kept.len() {
                if self.level[kept[i].var() as usize] > self.level[kept[max_i].var() as usize] {
                    max_i = i;
                }
            }
            kept.swap(1, max_i);
            bt = self.level[kept[1].var() as usize];
        }
        let lbd = {
            let mut levels: Vec<u32> = kept.iter().map(|l| self.level[l.var() as usize]).collect();
            levels.sort_unstable();
            levels.dedup();
            levels.len() as u32
        };
        (kept, bt, lbd)
    }

    /// Whether `l` (in the learned clause) is implied by the clause's other literals, through
    /// the reasons of the literals it depends on.
    fn redundant(&mut self, l: Lit, abstract_levels: u32, to_clear: &mut Vec<Lit>) -> bool {
        let mut stack = vec![l];
        let top = to_clear.len();
        while let Some(p) = stack.pop() {
            let Some(c) = self.reason[p.var() as usize] else {
                return false;
            };
            let cl = self.clauses[c as usize];
            for k in cl.start as usize..(cl.start + cl.len) as usize {
                let q = self.arena[k];
                let v = q.var() as usize;
                if q.var() == p.var() || self.seen[v] != 0 || self.level[v] == 0 {
                    continue;
                }
                if self.reason[v].is_some() && (abstract_levels >> (self.level[v] & 31)) & 1 == 1 {
                    self.seen[v] = 1;
                    stack.push(q);
                    to_clear.push(q);
                } else {
                    for x in to_clear.drain(top..) {
                        self.seen[x.var() as usize] = 0;
                    }
                    return false;
                }
            }
        }
        true
    }

    fn cancel_until(&mut self, level: u32) {
        if self.decision_level() <= level {
            return;
        }
        let lim = self.trail_lim[level as usize];
        for i in (lim..self.trail.len()).rev() {
            let l = self.trail[i];
            let v = l.var() as usize;
            self.phase[v] = !l.is_neg();
            self.values[v] = Value::Unset;
            self.reason[v] = None;
            if !self.heap.contains(l.var()) {
                self.heap.insert(l.var(), &self.activity);
            }
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(level as usize);
        self.qhead = lim;
    }

    /// The decision levels a restart can keep (van der Tak, Ramos and Heule, "Reusing the
    /// Assignment Trail in CDCL Solvers", 2011): a prefix whose decisions have no lower
    /// priority than variables a restart would free. Root assignments remain fixed;
    /// implications in a discarded suffix become candidates too. Keeping an eligible
    /// prefix avoids rebuilding its propagated literals, which on a large circuit is most
    /// of a restart's cost.
    fn reusable_levels(&mut self) -> u32 {
        // The next decision: the most active unassigned variable (assigned ones leave the
        // heap, and come back when unassigned).
        let next = loop {
            match self.heap.top() {
                // Propagation has completed and every variable is assigned: keep the
                // completed model instead of undoing and rebuilding it at a restart.
                None => return self.decision_level(),
                Some(v) if self.values[v as usize] == Value::Unset => break v,
                Some(_) => {
                    self.heap.pop(&self.activity);
                }
            }
        };
        let mut competing = self.activity[next as usize];
        let mut keep = self.decision_level();
        let mut end = self.trail.len();
        // A fresh restart can also choose variables that are currently implied. Build
        // the maximum priority of the suffix that would become unassigned, excluding
        // the root assignments and the implications of already retained decisions.
        for level in (0..self.trail_lim.len()).rev() {
            let start = self.trail_lim[level];
            for literal in &self.trail[start..end] {
                competing = competing.max(self.activity[literal.var() as usize]);
            }
            let decision = self.trail[start].var();
            if self.activity[decision as usize] < competing {
                keep = level as u32;
            }
            end = start;
        }
        keep
    }

    fn pick(&mut self) -> Option<Lit> {
        while let Some(v) = self.heap.pop(&self.activity) {
            if self.values[v as usize] == Value::Unset {
                return Some(Lit::new(v, self.phase[v as usize]));
            }
        }
        None
    }

    /// Halves the learned clauses, keeping the glue clauses (LBD ≤ 2) and reasons.
    fn reduce(&mut self) {
        let mut idx: Vec<u32> = (0..self.clauses.len() as u32)
            .filter(|&i| {
                let c = &self.clauses[i as usize];
                c.learnt && !c.deleted && c.lbd > 2 && c.len > 2
            })
            .collect();
        idx.sort_by(|&a, &b| {
            let (ca, cb) = (&self.clauses[a as usize], &self.clauses[b as usize]);
            cb.lbd.cmp(&ca.lbd).then(
                ca.activity
                    .partial_cmp(&cb.activity)
                    .unwrap_or(core::cmp::Ordering::Equal),
            )
        });
        let locked = |s: &Solver, c: u32| {
            let l = s.arena[s.clauses[c as usize].start as usize];
            s.value(l) == Value::True && s.reason[l.var() as usize] == Some(c)
        };
        for &c in idx.iter().take(idx.len() / 2) {
            if locked(self, c) {
                continue;
            }
            self.clauses[c as usize].deleted = true;
            self.learnts -= 1;
            self.wasted += self.clauses[c as usize].len as usize;
            if self.proof.is_some() {
                let lits = self.lits(c).to_vec();
                if let Some(p) = &mut self.proof {
                    p.push(Step::Delete(lits));
                }
            }
        }
        if self.wasted * 4 > self.arena.len() {
            self.collect();
        }
    }

    /// Drops the deleted clauses: the arena is compacted, the clauses renumbered, and every
    /// watch and reason follows.
    fn collect(&mut self) {
        let mut map = vec![u32::MAX; self.clauses.len()];
        let mut arena = Vec::with_capacity(self.arena.len() - self.wasted);
        let mut kept = 0usize;
        for (i, m) in map.iter_mut().enumerate() {
            let c = self.clauses[i];
            if c.deleted {
                continue;
            }
            *m = kept as u32;
            let start = arena.len() as u32;
            arena.extend_from_slice(&self.arena[c.start as usize..(c.start + c.len) as usize]);
            self.clauses[kept] = Clause { start, ..c };
            kept += 1;
        }
        self.clauses.truncate(kept);
        self.arena = arena;
        self.wasted = 0;
        for ws in self.watches.iter_mut().chain(self.bins.iter_mut()) {
            ws.retain_mut(|w| {
                w.clause = map[w.clause as usize];
                w.clause != u32::MAX
            });
        }
        for r in self.reason.iter_mut().flatten() {
            *r = map[*r as usize];
        }
    }

    /// Solves within `max_conflicts` conflicts (see [`solve_within`](Self::solve_within)).
    pub fn solve(&mut self, max_conflicts: u64) -> Answer {
        self.solve_within(Limits::conflicts(max_conflicts))
    }

    /// Solves within `limits`, counted from this call. On [`Answer::Unknown`] the search stays
    /// where it stopped: the next call goes on from there. A zero allowance pauses an
    /// undecided search without work; a contradiction already established is still returned.
    pub fn solve_within(&mut self, limits: Limits) -> Answer {
        if self.unsat {
            return Answer::Unsat;
        }
        if limits.conflicts == 0 || limits.propagations == 0 {
            return Answer::Unknown;
        }
        let (c0, p0) = (self.conflicts, self.propagations);
        let propagation_stop = p0.saturating_add(limits.propagations);
        loop {
            if let Some(confl) = self.propagate_until(propagation_stop) {
                self.conflicts += 1;
                self.here += 1;
                if self.decision_level() == 0 {
                    self.unsat = true;
                    if let Some(p) = &mut self.proof {
                        p.push(Step::Add(Vec::new()));
                    }
                    return Answer::Unsat;
                }
                let (learnt, bt, lbd) = self.analyze(confl);
                self.cancel_until(bt);
                if let Some(p) = &mut self.proof {
                    p.push(Step::Add(learnt.clone()));
                }
                if learnt.len() == 1 {
                    self.assign(learnt[0], None);
                } else {
                    let c = self.attach(&learnt, true, lbd);
                    self.bump_clause(c);
                    self.assign(learnt[0], Some(c));
                }
                self.var_inc /= 0.95;
                self.cla_inc /= 0.999;
                if self.conflicts >= self.next_reduce {
                    self.next_reduce = self.conflicts + 2000 + 300 * (self.conflicts / 2000);
                    self.reduce();
                }
                if self.conflicts - c0 >= limits.conflicts
                    || self.propagations - p0 >= limits.propagations
                {
                    return Answer::Unknown;
                }
            } else {
                if self.propagations - p0 >= limits.propagations {
                    return Answer::Unknown;
                }
                if self.here >= luby(self.restarts) * 100 {
                    self.restarts += 1;
                    self.here = 0;
                    let keep = self.reusable_levels();
                    self.cancel_until(keep);
                    continue;
                }
                let Some(d) = self.pick() else {
                    let model = self.values.iter().map(|&v| v == Value::True).collect();
                    self.cancel_until(0);
                    return Answer::Sat(model);
                };
                self.decisions += 1;
                self.trail_lim.push(self.trail.len());
                self.assign(d, None);
            }
        }
    }
}

/// The Luby sequence 1, 1, 2, 1, 1, 2, 4, ... (restart `i`'s length in units).
fn luby(i: u32) -> u64 {
    let mut size = 1u64;
    let mut seq = 0u32;
    let x = u64::from(i);
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    let mut x = x;
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    1 << seq
}

/// A binary max-heap of variables by activity.
#[derive(Default)]
struct Heap {
    heap: Vec<Var>,
    index: Vec<i64>,
}

impl Heap {
    fn contains(&self, v: Var) -> bool {
        self.index.get(v as usize).is_some_and(|&i| i >= 0)
    }

    fn insert(&mut self, v: Var, act: &[f64]) {
        while self.index.len() <= v as usize {
            self.index.push(-1);
        }
        if self.contains(v) {
            return;
        }
        self.index[v as usize] = self.heap.len() as i64;
        self.heap.push(v);
        self.up(self.heap.len() - 1, act);
    }

    fn decrease(&mut self, v: Var, act: &[f64]) {
        if let Some(&i) = self.index.get(v as usize)
            && i >= 0
        {
            self.up(i as usize, act);
        }
    }

    fn top(&self) -> Option<Var> {
        self.heap.first().copied()
    }

    fn pop(&mut self, act: &[f64]) -> Option<Var> {
        let top = *self.heap.first()?;
        let last = self.heap.pop()?;
        self.index[top as usize] = -1;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.index[last as usize] = 0;
            self.down(0, act);
        }
        Some(top)
    }

    fn up(&mut self, mut i: usize, act: &[f64]) {
        let v = self.heap[i];
        while i > 0 {
            let parent = (i - 1) / 2;
            if act[self.heap[parent] as usize] >= act[v as usize] {
                break;
            }
            self.heap[i] = self.heap[parent];
            self.index[self.heap[i] as usize] = i as i64;
            i = parent;
        }
        self.heap[i] = v;
        self.index[v as usize] = i as i64;
    }

    fn down(&mut self, mut i: usize, act: &[f64]) {
        let v = self.heap[i];
        loop {
            let l = 2 * i + 1;
            if l >= self.heap.len() {
                break;
            }
            let r = l + 1;
            let c =
                if r < self.heap.len() && act[self.heap[r] as usize] > act[self.heap[l] as usize] {
                    r
                } else {
                    l
                };
            if act[self.heap[c] as usize] <= act[v as usize] {
                break;
            }
            self.heap[i] = self.heap[c];
            self.index[self.heap[i] as usize] = i as i64;
            i = c;
        }
        self.heap[i] = v;
        self.index[v as usize] = i as i64;
    }
}

#[cfg(test)]
mod restart_tests {
    use super::*;

    fn priority(s: &mut Solver, v: Var, value: f64) {
        s.activity[v as usize] = value;
        s.heap.decrease(v, &s.activity);
    }

    fn decide(s: &mut Solver, v: Var) {
        s.trail_lim.push(s.trail.len());
        s.assign(Lit::pos(v), None);
        assert!(s.propagate_until(u64::MAX).is_none());
    }

    #[test]
    fn a_higher_priority_implication_prevents_retaining_its_decision() {
        let mut s = Solver::new();
        let root = s.new_var();
        let decision = s.new_var();
        let implied = s.new_var();
        let unset = s.new_var();
        assert!(s.add_clause(&[Lit::pos(root)]));
        assert!(s.add_clause(&[Lit::neg(decision), Lit::pos(implied)]));
        for (v, p) in [
            (root, 1000.0),
            (decision, 10.0),
            (implied, 20.0),
            (unset, 1.0),
        ] {
            priority(&mut s, v, p);
        }
        decide(&mut s, decision);
        assert_eq!(s.values[implied as usize], Value::True);
        let keep = s.reusable_levels();
        assert_eq!(keep, 0);
        s.cancel_until(keep);
        assert_eq!(s.pick().unwrap().var(), implied);
        assert_eq!(s.values[root as usize], Value::True);
    }

    #[test]
    fn the_restart_keeps_earlier_levels_but_reconsiders_later_implications() {
        let mut s = Solver::new();
        let first = s.new_var();
        let second = s.new_var();
        let implied = s.new_var();
        let unset = s.new_var();
        assert!(s.add_clause(&[Lit::neg(second), Lit::pos(implied)]));
        for (v, p) in [(first, 30.0), (second, 20.0), (implied, 25.0), (unset, 1.0)] {
            priority(&mut s, v, p);
        }
        decide(&mut s, first);
        decide(&mut s, second);
        let keep = s.reusable_levels();
        assert_eq!(keep, 1);
        s.cancel_until(keep);
        assert_eq!(s.values[first as usize], Value::True);
        assert_eq!(s.values[second as usize], Value::Unset);
        assert_eq!(s.pick().unwrap().var(), implied);
    }

    #[test]
    fn root_priorities_do_not_force_a_restart_of_reusable_levels() {
        let mut s = Solver::new();
        let root = s.new_var();
        let decision = s.new_var();
        let implied = s.new_var();
        let unset = s.new_var();
        assert!(s.add_clause(&[Lit::pos(root)]));
        assert!(s.add_clause(&[Lit::neg(decision), Lit::pos(implied)]));
        for (v, p) in [
            (root, 1000.0),
            (decision, 20.0),
            (implied, 10.0),
            (unset, 1.0),
        ] {
            priority(&mut s, v, p);
        }
        decide(&mut s, decision);
        assert_eq!(s.reusable_levels(), 1);
    }

    #[test]
    fn a_completed_model_is_returned_without_rebuilding_its_trail() {
        let mut s = Solver::new();
        let decision = s.new_var();
        let implied = s.new_var();
        assert!(s.add_clause(&[Lit::neg(decision), Lit::pos(implied)]));
        decide(&mut s, decision);
        s.here = 100;
        assert_eq!(s.reusable_levels(), 1);
        let before = s.decisions;
        assert_eq!(s.solve(1), Answer::Sat(vec![true, true]));
        assert_eq!(s.decisions, before);
    }
}
