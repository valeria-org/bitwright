//! A forward checker for DRUP proofs: every added clause must follow from the clauses present
//! before it by reverse unit propagation (assigning its literals false and propagating gives a
//! conflict), deleted clauses leave the database, and the proof must add the empty clause. It
//! shares no code with the solver: its own watched-literal propagation over its own database,
//! so a solver bug cannot vouch for itself.

use std::collections::HashMap;

use super::sat::{Lit, Step};

#[derive(Copy, Clone, PartialEq, Eq)]
enum V {
    T,
    F,
    U,
}

struct Db {
    clauses: Vec<Vec<Lit>>,
    alive: Vec<bool>,
    /// Clause indices by sorted literals (for deletions).
    index: HashMap<Vec<Lit>, Vec<usize>>,
    watches: Vec<Vec<usize>>,
    vals: Vec<V>,
    reason: Vec<Option<usize>>,
    trail: Vec<Lit>,
    qhead: usize,
    /// Level-0 units (clauses of one literal), kept apart from the watches.
    units: Vec<usize>,
    /// The database is contradictory at level 0.
    top_conflict: bool,
}

impl Db {
    fn val(&self, l: Lit) -> V {
        match self.vals.get(l.var() as usize).copied().unwrap_or(V::U) {
            V::U => V::U,
            v => {
                if (v == V::T) != l.is_neg() {
                    V::T
                } else {
                    V::F
                }
            }
        }
    }

    fn grow(&mut self, v: u32) {
        while self.vals.len() <= v as usize {
            self.vals.push(V::U);
            self.reason.push(None);
            self.watches.push(Vec::new());
            self.watches.push(Vec::new());
        }
    }

    fn set(&mut self, l: Lit, r: Option<usize>) {
        self.grow(l.var());
        self.vals[l.var() as usize] = if l.is_neg() { V::F } else { V::T };
        self.reason[l.var() as usize] = r;
        self.trail.push(l);
    }

    fn add(&mut self, mut c: Vec<Lit>) -> usize {
        c.sort_unstable();
        c.dedup();
        for &l in &c {
            self.grow(l.var());
        }
        let i = self.clauses.len();
        self.index.entry(c.clone()).or_default().push(i);
        if c.len() >= 2 {
            self.watches[(!c[0]).0 as usize].push(i);
            self.watches[(!c[1]).0 as usize].push(i);
        } else {
            self.units.push(i);
        }
        self.clauses.push(c);
        self.alive.push(true);
        i
    }

    /// Propagates from `qhead`: `true` on a conflict.
    fn propagate(&mut self) -> bool {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let ws = core::mem::take(&mut self.watches[p.0 as usize]);
            let mut keep = Vec::with_capacity(ws.len());
            let mut conflict = false;
            for (n, &ci) in ws.iter().enumerate() {
                if conflict {
                    keep.extend_from_slice(&ws[n..]);
                    break;
                }
                if !self.alive[ci] {
                    continue;
                }
                let false_lit = !p;
                let c = &mut self.clauses[ci];
                if c[0] == false_lit {
                    c.swap(0, 1);
                }
                if c[1] != false_lit {
                    // A stale watch (the clause moved its watch): drop it.
                    continue;
                }
                let first = c[0];
                if self.val(first) == V::T {
                    keep.push(ci);
                    continue;
                }
                let mut moved = false;
                for k in 2..self.clauses[ci].len() {
                    let l = self.clauses[ci][k];
                    if self.val(l) != V::F {
                        self.clauses[ci].swap(1, k);
                        self.watches[(!l).0 as usize].push(ci);
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                keep.push(ci);
                match self.val(first) {
                    V::F => conflict = true,
                    V::U => self.set(first, Some(ci)),
                    V::T => {}
                }
            }
            self.watches[p.0 as usize].extend(keep);
            if conflict {
                return true;
            }
        }
        false
    }

    /// Level 0 afresh: every live unit, then propagation.
    fn reset_top(&mut self) {
        for l in self.trail.drain(..) {
            self.vals[l.var() as usize] = V::U;
            self.reason[l.var() as usize] = None;
        }
        self.qhead = 0;
        self.top_conflict = false;
        let units: Vec<usize> = self
            .units
            .iter()
            .copied()
            .filter(|&i| self.alive[i])
            .collect();
        for i in units {
            let l = self.clauses[i][0];
            match self.val(l) {
                V::F => {
                    self.top_conflict = true;
                    return;
                }
                V::U => self.set(l, Some(i)),
                V::T => {}
            }
        }
        if self.propagate() {
            self.top_conflict = true;
        }
    }

    /// Whether `c` follows by reverse unit propagation.
    fn rup(&mut self, c: &[Lit]) -> bool {
        if self.top_conflict {
            return true;
        }
        let mark = self.trail.len();
        let mut conflict = false;
        for &l in c {
            match self.val(l) {
                V::T => {
                    conflict = true;
                    break;
                }
                V::U => self.set(!l, None),
                V::F => {}
            }
        }
        if !conflict {
            conflict = self.propagate();
        }
        // Back to level 0.
        for l in self.trail.drain(mark..) {
            self.vals[l.var() as usize] = V::U;
            self.reason[l.var() as usize] = None;
        }
        self.qhead = mark;
        conflict
    }
}

/// Checks a DRUP proof of the unsatisfiability of `cnf`: `Ok` when every added clause follows
/// by reverse unit propagation and the empty clause is added; else the first failing step.
pub fn check(cnf: &[Vec<Lit>], proof: &[Step]) -> Result<(), String> {
    let mut db = Db {
        clauses: Vec::new(),
        alive: Vec::new(),
        index: HashMap::new(),
        watches: Vec::new(),
        vals: Vec::new(),
        reason: Vec::new(),
        trail: Vec::new(),
        qhead: 0,
        units: Vec::new(),
        top_conflict: false,
    };
    for c in cnf {
        if c.is_empty() {
            return Ok(());
        }
        db.add(c.clone());
    }
    db.reset_top();
    for (n, step) in proof.iter().enumerate() {
        match step {
            Step::Add(c) => {
                if !db.rup(c) {
                    return Err(format!(
                        "step {n}: {c:?} does not follow by unit propagation"
                    ));
                }
                if c.is_empty() {
                    return Ok(());
                }
                let i = db.add(c.clone());
                if c.len() == 1 || db.clauses[i].len() == 1 {
                    db.reset_top();
                } else if !db.top_conflict {
                    // The new clause may propagate at level 0.
                    let (a, b) = (db.clauses[i][0], db.clauses[i][1]);
                    if db.val(a) == V::F || db.val(b) == V::F {
                        db.reset_top();
                    }
                }
            }
            Step::Delete(c) => {
                let mut key = c.clone();
                key.sort_unstable();
                key.dedup();
                if let Some(list) = db.index.get_mut(&key)
                    && let Some(i) = list.pop()
                {
                    db.alive[i] = false;
                    // A deleted reason changes level 0: recompute it.
                    if db.reason.contains(&Some(i)) {
                        db.reset_top();
                    }
                }
            }
        }
    }
    Err("the proof does not add the empty clause".into())
}
