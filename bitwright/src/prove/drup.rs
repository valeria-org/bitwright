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
    /// The database is contradictory at level 0: the clause that is false there.
    top_conflict: Option<usize>,
    /// Marks for [`Db::explain`], by variable: marked when equal to `stamp`.
    seen: Vec<u32>,
    stamp: u32,
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
            self.seen.push(0);
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

    /// Propagates from `qhead`: the clause that became false, on a conflict.
    fn propagate(&mut self) -> Option<usize> {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            let ws = core::mem::take(&mut self.watches[p.0 as usize]);
            let mut keep = Vec::with_capacity(ws.len());
            let mut conflict = None;
            for (n, &ci) in ws.iter().enumerate() {
                if conflict.is_some() {
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
                    V::F => conflict = Some(ci),
                    V::U => self.set(first, Some(ci)),
                    V::T => {}
                }
            }
            self.watches[p.0 as usize].extend(keep);
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    /// The clauses that make `from` false (a clause, when `conflict`) or true (the literals
    /// of `from`, otherwise) by unit propagation from what is assumed, in an order in which
    /// each is unit when its turn comes; the false clause last. The literals of `assumed`
    /// (the clause being checked) that are false need no clause: the check assumes them so.
    fn explain(&mut self, from: &[Lit], conflict: Option<usize>, assumed: &[Lit]) -> Vec<usize> {
        let mut given: Vec<u32> = (assumed.iter())
            .filter(|&&l| self.val(l) == V::F)
            .map(|l| l.var())
            .collect();
        given.sort_unstable();
        self.stamp += 1;
        for l in from {
            self.seen[l.var() as usize] = self.stamp;
        }
        let mut used = Vec::new();
        for k in (0..self.trail.len()).rev() {
            let v = self.trail[k].var() as usize;
            if self.seen[v] != self.stamp || given.binary_search(&(v as u32)).is_ok() {
                continue;
            }
            if let Some(r) = self.reason[v] {
                used.push(r);
                for i in 0..self.clauses[r].len() {
                    let u = self.clauses[r][i].var() as usize;
                    self.seen[u] = self.stamp;
                }
            }
        }
        used.reverse();
        used.extend(conflict);
        used
    }

    /// Level 0 afresh: every live unit, then propagation.
    fn reset_top(&mut self) {
        for l in self.trail.drain(..) {
            self.vals[l.var() as usize] = V::U;
            self.reason[l.var() as usize] = None;
        }
        self.qhead = 0;
        self.top_conflict = None;
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
                    self.top_conflict = Some(i);
                    return;
                }
                V::U => self.set(l, Some(i)),
                V::T => {}
            }
        }
        self.top_conflict = self.propagate();
    }

    /// Whether `c` follows by reverse unit propagation: the clauses that show it
    /// ([`explain`](Self::explain)), or `None`.
    fn rup(&mut self, c: &[Lit]) -> Option<Vec<usize>> {
        if let Some(ci) = self.top_conflict {
            let lits = self.clauses[ci].clone();
            return Some(self.explain(&lits, Some(ci), c));
        }
        let mark = self.trail.len();
        let mut hints = None;
        for &l in c {
            match self.val(l) {
                V::T => {
                    // True already: by the clauses that made it so (or, for a clause with
                    // a literal and its complement, by nothing).
                    hints = Some(self.explain(&[l], None, c));
                    break;
                }
                V::U => self.set(!l, None),
                V::F => {}
            }
        }
        if hints.is_none()
            && let Some(ci) = self.propagate()
        {
            let lits = self.clauses[ci].clone();
            hints = Some(self.explain(&lits, Some(ci), c));
        }
        // Back to level 0.
        for l in self.trail.drain(mark..) {
            self.vals[l.var() as usize] = V::U;
            self.reason[l.var() as usize] = None;
        }
        self.qhead = mark;
        hints
    }
}

/// Checks a DRUP proof of the unsatisfiability of `cnf`: `Ok` when every added clause follows
/// by reverse unit propagation and the empty clause is added; else the first failing step.
pub fn check(cnf: &[Vec<Lit>], proof: &[Step]) -> Result<(), String> {
    check_steps(cnf, proof, true, None)
}

/// [`check`], writing down for every added clause the clauses it follows from: the proof as
/// LRAT steps ([`super::lrat`]), which a checker verifies without searching for them.
pub(super) fn check_to_lrat(
    cnf: &[Vec<Lit>],
    proof: &[Step],
) -> Result<Vec<super::lrat::Step>, String> {
    let mut out = Vec::new();
    check_steps(cnf, proof, true, Some(&mut out))?;
    Ok(out)
}

/// Test preprocessing and interrupted search transcripts without claiming UNSAT.
#[cfg(test)]
pub(super) fn check_prefix(cnf: &[Vec<Lit>], proof: &[Step]) -> Result<(), String> {
    check_steps(cnf, proof, false, None)
}

fn check_steps(
    cnf: &[Vec<Lit>],
    proof: &[Step],
    complete: bool,
    mut lrat: Option<&mut Vec<super::lrat::Step>>,
) -> Result<(), String> {
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
        top_conflict: None,
        seen: Vec::new(),
        stamp: 0,
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
                let Some(hints) = db.rup(c) else {
                    return Err(format!(
                        "step {n}: {c:?} does not follow by unit propagation"
                    ));
                };
                // A clause's number is its place among the clauses, from one.
                if let Some(out) = lrat.as_deref_mut() {
                    out.push(super::lrat::Step::Add {
                        id: db.clauses.len() as u64 + 1,
                        clause: c.clone(),
                        hints: hints.iter().map(|&h| h as u64 + 1).collect(),
                    });
                }
                if c.is_empty() {
                    return Ok(());
                }
                let i = db.add(c.clone());
                if c.len() == 1 || db.clauses[i].len() == 1 {
                    db.reset_top();
                } else if db.top_conflict.is_none() {
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
                    if let Some(out) = lrat.as_deref_mut() {
                        out.push(super::lrat::Step::Delete { id: i as u64 + 1 });
                    }
                    // A deleted reason changes level 0: recompute it.
                    if db.reason.contains(&Some(i)) {
                        db.reset_top();
                    }
                }
            }
        }
    }
    if complete {
        Err("the proof does not add the empty clause".into())
    } else {
        Ok(())
    }
}
