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
    /// The conflict budget ran out.
    Unknown,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Value {
    True,
    False,
    Unset,
}

struct Clause {
    lits: Vec<Lit>,
    learnt: bool,
    lbd: u32,
    activity: f32,
    deleted: bool,
}

#[derive(Copy, Clone)]
struct Watch {
    clause: u32,
    blocker: Lit,
}

/// A CDCL solver. Clauses are added once, then [`solve`](Self::solve) is called.
pub struct Solver {
    clauses: Vec<Clause>,
    watches: Vec<Vec<Watch>>,
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
            watches: Vec::new(),
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

    /// Adds a clause (at decision level 0, before solving). Returns `false` when the formula is
    /// now known unsatisfiable.
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        if self.unsat {
            return false;
        }
        let mut c: Vec<Lit> = lits.to_vec();
        c.sort_unstable();
        c.dedup();
        // A tautology is always true.
        if c.windows(2).any(|w| w[0].var() == w[1].var()) {
            return true;
        }
        for &l in &c {
            while l.var() >= self.num_vars() {
                self.new_var();
            }
        }
        // Literals false at level 0 are dropped (the propagation that made them false is a
        // RUP step, so the shorter clause is too); a true one satisfies the clause.
        if c.iter().any(|&l| self.value(l) == Value::True) {
            return true;
        }
        let reduced: Vec<Lit> = c
            .iter()
            .copied()
            .filter(|&l| self.value(l) != Value::False)
            .collect();
        if reduced.len() != c.len()
            && let Some(p) = &mut self.proof
        {
            p.push(Step::Add(reduced.clone()));
        }
        match reduced.len() {
            0 => {
                self.unsat = true;
                false
            }
            1 => {
                self.assign(reduced[0], None);
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
                self.attach(reduced, false, 0);
                true
            }
        }
    }

    fn attach(&mut self, lits: Vec<Lit>, learnt: bool, lbd: u32) -> u32 {
        let idx = self.clauses.len() as u32;
        self.watches[(!lits[0]).0 as usize].push(Watch {
            clause: idx,
            blocker: lits[1],
        });
        self.watches[(!lits[1]).0 as usize].push(Watch {
            clause: idx,
            blocker: lits[0],
        });
        self.clauses.push(Clause {
            lits,
            learnt,
            lbd,
            activity: 0.0,
            deleted: false,
        });
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
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            self.propagations += 1;
            // Clauses watching ¬p (watched under the literal that became false).
            let mut ws = core::mem::take(&mut self.watches[p.0 as usize]);
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
                let ci = w.clause as usize;
                if self.clauses[ci].deleted {
                    continue;
                }
                // Make lits[1] the false literal.
                {
                    let c = &mut self.clauses[ci].lits;
                    if c[0] == false_lit {
                        c.swap(0, 1);
                    }
                }
                let first = self.clauses[ci].lits[0];
                if first != w.blocker && self.value(first) == Value::True {
                    ws[j] = Watch {
                        clause: w.clause,
                        blocker: first,
                    };
                    j += 1;
                    continue;
                }
                // Look for a new literal to watch.
                let len = self.clauses[ci].lits.len();
                let mut found = false;
                for k in 2..len {
                    let l = self.clauses[ci].lits[k];
                    if self.value(l) != Value::False {
                        self.clauses[ci].lits.swap(1, k);
                        self.watches[(!l).0 as usize].push(Watch {
                            clause: w.clause,
                            blocker: first,
                        });
                        found = true;
                        break;
                    }
                }
                if found {
                    continue;
                }
                ws[j] = Watch {
                    clause: w.clause,
                    blocker: first,
                };
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
            self.watches[p.0 as usize] = ws;
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
            if self.clauses[c as usize].learnt {
                self.bump_clause(c);
            }
            let lits = self.clauses[c as usize].lits.clone();
            for &q in lits.iter().skip(usize::from(p.is_some())) {
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
            // The reason's first literal is the implied one (`l`), skipped above.
            if let Some(c) = confl {
                let lits = &mut self.clauses[c as usize].lits;
                if lits[0] != l {
                    let k = lits.iter().position(|&x| x == l).unwrap_or(0);
                    lits.swap(0, k);
                }
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
            let lits = self.clauses[c as usize].lits.clone();
            for &q in &lits {
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
                c.learnt && !c.deleted && c.lbd > 2 && c.lits.len() > 2
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
            let l = s.clauses[c as usize].lits[0];
            s.value(l) == Value::True && s.reason[l.var() as usize] == Some(c)
        };
        for &c in idx.iter().take(idx.len() / 2) {
            if locked(self, c) {
                continue;
            }
            self.clauses[c as usize].deleted = true;
            if let Some(p) = &mut self.proof {
                p.push(Step::Delete(self.clauses[c as usize].lits.clone()));
            }
        }
    }

    /// Solves within `max_conflicts` conflicts.
    pub fn solve(&mut self, max_conflicts: u64) -> Answer {
        if self.unsat {
            return Answer::Unsat;
        }
        if self.propagate().is_some() {
            self.unsat = true;
            if let Some(p) = &mut self.proof {
                p.push(Step::Add(Vec::new()));
            }
            return Answer::Unsat;
        }
        let start = self.conflicts;
        let mut restart = 0u32;
        let mut next_reduce = 2000u64;
        loop {
            let budget = luby(restart) * 100;
            restart += 1;
            let mut here = 0u64;
            loop {
                if let Some(confl) = self.propagate() {
                    self.conflicts += 1;
                    here += 1;
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
                        let first = learnt[0];
                        let c = self.attach(learnt, true, lbd);
                        self.bump_clause(c);
                        self.assign(first, Some(c));
                    }
                    self.var_inc /= 0.95;
                    self.cla_inc /= 0.999;
                    if self.conflicts - start >= max_conflicts {
                        self.cancel_until(0);
                        return Answer::Unknown;
                    }
                    if self.conflicts >= next_reduce {
                        next_reduce = self.conflicts + 2000 + 300 * (self.conflicts / 2000);
                        self.reduce();
                    }
                } else {
                    if here >= budget {
                        self.cancel_until(0);
                        break;
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
