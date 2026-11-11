//! LRAT: a proof of unsatisfiability in which every added clause names the clauses it follows
//! from, in the order unit propagation uses them, so that a checker does no search at all.
//!
//! The solver logs DRUP ([`super::drup`]): the clauses it learned, without saying from what.
//! The DRUP checker finds that out as it checks each one, and [`from_drup`] writes it down.
//! [`check`] is the other side: a checker for LRAT steps that shares nothing with the solver
//! or with the DRUP checker, and [`to_text`] is the format other checkers read (clause
//! numbers from one, the given clauses first).

use std::collections::HashMap;

use super::sat::Lit;

/// A step of an LRAT proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// Clause `id`, which follows from the clauses `hints` by unit propagation in that
    /// order: with its literals false, each hint but the last has one literal left, which
    /// becomes true, and the last has none.
    Add {
        /// The clause's number: above every number before it.
        id: u64,
        /// The clause.
        clause: Vec<Lit>,
        /// The clauses it follows from.
        hints: Vec<u64>,
    },
    /// Clause `id` is not used again.
    Delete {
        /// The clause's number.
        id: u64,
    },
}

/// The LRAT proof that the DRUP `proof` of the unsatisfiability of `cnf` amounts to, or the
/// first step of `proof` that does not follow.
pub fn from_drup(cnf: &[Vec<Lit>], proof: &[super::sat::Step]) -> Result<Vec<Step>, String> {
    super::drup::check_to_lrat(cnf, proof)
}

/// Checks an LRAT proof of the unsatisfiability of `cnf` (numbered from one, in order): every
/// added clause must follow from its hints as [`Step::Add`] says, and the empty clause must
/// be added.
pub fn check(cnf: &[Vec<Lit>], proof: &[Step]) -> Result<(), String> {
    let mut clauses: HashMap<u64, &[Lit]> = HashMap::with_capacity(cnf.len() + proof.len());
    for (k, c) in cnf.iter().enumerate() {
        if c.is_empty() {
            return Ok(());
        }
        clauses.insert(k as u64 + 1, c);
    }
    let mut last = cnf.len() as u64;
    // The literals false in the step being checked.
    let mut falsified: HashMap<Lit, ()> = HashMap::new();
    for (n, step) in proof.iter().enumerate() {
        match step {
            Step::Delete { id } => {
                clauses.remove(id);
            }
            Step::Add { id, clause, hints } => {
                if *id <= last {
                    return Err(format!(
                        "step {n}: clause {id} is not numbered above {last}"
                    ));
                }
                last = *id;
                falsified.clear();
                // A clause with a literal and its complement holds by itself.
                let mut conflict = false;
                for &l in clause {
                    conflict |= falsified.contains_key(&!l);
                    falsified.insert(l, ());
                }
                for h in hints {
                    if conflict {
                        break;
                    }
                    let Some(c) = clauses.get(h) else {
                        return Err(format!("step {n}: clause {h} is not there"));
                    };
                    let mut open = None;
                    let mut more = false;
                    for &l in c.iter() {
                        if falsified.contains_key(&l) {
                            continue;
                        }
                        // (A literal made true is one whose complement is false.)
                        if falsified.contains_key(&!l) || open.is_some_and(|o| o != l) {
                            more = true;
                            break;
                        }
                        open = Some(l);
                    }
                    if more {
                        return Err(format!("step {n}: clause {h} is not unit"));
                    }
                    match open {
                        None => conflict = true,
                        Some(l) => {
                            falsified.insert(!l, ());
                        }
                    }
                }
                if !conflict {
                    return Err(format!(
                        "step {n}: the hints of clause {id} end without a conflict"
                    ));
                }
                if clause.is_empty() {
                    return Ok(());
                }
                clauses.insert(*id, clause);
            }
        }
    }
    Err("the proof does not add the empty clause".into())
}

/// The proof in LRAT's text format: `id literals 0 hints 0` for a clause added and
/// `id d ids 0` for clauses deleted, literals as in DIMACS.
pub fn to_text(proof: &[Step]) -> String {
    use core::fmt::Write;
    let mut s = String::new();
    let mut last = 0;
    for step in proof {
        match step {
            Step::Add { id, clause, hints } => {
                last = *id;
                let _ = write!(s, "{id} ");
                for l in clause {
                    let _ = write!(s, "{} ", l.dimacs());
                }
                s.push_str("0 ");
                for h in hints {
                    let _ = write!(s, "{h} ");
                }
                s.push_str("0\n");
            }
            Step::Delete { id } => {
                let _ = writeln!(s, "{last} d {id} 0");
            }
        }
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prove::sat::Step as Drup;

    fn lit(d: i32) -> Lit {
        let l = Lit::pos(d.unsigned_abs() - 1);
        if d < 0 { !l } else { l }
    }

    fn clause(ds: &[i32]) -> Vec<Lit> {
        ds.iter().map(|&d| lit(d)).collect()
    }

    #[test]
    fn a_drup_proof_becomes_lrat_and_a_wrong_hint_is_refused() {
        let cnf = [
            clause(&[1, 2]),
            clause(&[-1, 2]),
            clause(&[1, -2]),
            clause(&[-1, -2]),
        ];
        let drup = [
            Drup::Add(clause(&[2])),
            Drup::Delete(clause(&[1, 2])),
            Drup::Add(vec![]),
        ];
        let steps = from_drup(&cnf, &drup).unwrap();
        check(&cnf, &steps).unwrap();
        assert_eq!(to_text(&steps), "5 2 0 1 2 0\n5 d 1 0\n6 0 5 3 4 0\n");
        // A hint that is not unit, a missing conflict, a clause that is gone, a number that
        // does not grow, and a proof that stops short.
        let with = |f: &dyn Fn(&mut Vec<Step>)| {
            let mut s = steps.clone();
            f(&mut s);
            check(&cnf, &s)
        };
        let hints = |s: &mut Vec<Step>, k: usize, h: &[u64]| {
            if let Step::Add { hints, .. } = &mut s[k] {
                *hints = h.to_vec();
            }
        };
        assert!(
            with(&|s| hints(s, 0, &[3, 1]))
                .unwrap_err()
                .contains("not unit")
        );
        assert!(
            with(&|s| hints(s, 0, &[1]))
                .unwrap_err()
                .contains("without a conflict")
        );
        assert!(
            with(&|s| hints(s, 2, &[5, 1, 4]))
                .unwrap_err()
                .contains("not there")
        );
        assert!(with(&|s| s.swap(0, 2)).is_err());
        assert!(
            with(&|s| s.truncate(2))
                .unwrap_err()
                .contains("empty clause")
        );
        // What does not follow is not given hints.
        assert!(from_drup(&cnf[..3], &[Drup::Add(clause(&[-1]))]).is_err());
    }
}
