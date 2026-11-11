//! [CaDiCaL](https://github.com/arminbiere/cadical) as the SAT search of bitwright's solver.
//!
//! bitwright's own search is small and has no dependency; on the long searches (a circuit of
//! multipliers that no word-level procedure decided) a solver with inprocessing is far
//! ahead. This crate puts CaDiCaL behind [`bitwright::prove::Backend`]:
//!
//! ```
//! use bitwright::solve::{Config, Solver, Status};
//! use bitwright::{Context, ParseOptions, Width};
//!
//! let mut cx = Context::new();
//! let mut s = Solver::new(Config::default().with_backend(Some(bitwright_cadical::backend())));
//! let o = ParseOptions::width(Width::W32);
//! let e = cx.parse("(x * y == 0x3b9aca07) & (x >u 1) & (y >u 1) & (x <u 0x10000)", &o)?;
//! s.assert(&cx, e)?;
//! // 0x3b9aca07 = 1000000007 is prime.
//! assert_eq!(s.check(&mut cx)?, Status::Sat); // (modulo 2^32 it has factorizations)
//! # Ok::<(), bitwright::Error>(())
//! ```
//!
//! With it, [`Solver`](bitwright::solve::Solver) searches its kept circuit with CaDiCaL, and
//! hands CaDiCaL what the prover's simplifier left of a question that the prover's own short
//! search did not decide.

use bitwright::prove::sat::{Answer, Lit, Var};
use bitwright::prove::{Backend, Limits};

/// CaDiCaL, as a [`Backend`].
pub struct Cadical {
    solver: cadical::Solver,
    vars: u32,
    failed: Vec<Lit>,
    /// The limits given so far, as an upper bound of the conflicts spent (CaDiCaL's own
    /// count is not exposed).
    conflicts: u64,
}

impl core::fmt::Debug for Cadical {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Cadical")
            .field("vars", &self.vars)
            .field("clauses", &self.solver.num_clauses())
            .finish_non_exhaustive()
    }
}

impl Default for Cadical {
    fn default() -> Self {
        Cadical::new()
    }
}

impl Cadical {
    /// An empty search.
    pub fn new() -> Self {
        Cadical {
            solver: cadical::Solver::new(),
            vars: 0,
            failed: Vec::new(),
            conflicts: 0,
        }
    }
}

/// CaDiCaL's literal: variables from 1, negative when negated.
fn lit(l: Lit) -> i32 {
    let v = l.var() as i32 + 1;
    if l.is_neg() { -v } else { v }
}

impl Backend for Cadical {
    fn new_var(&mut self) -> Var {
        self.vars += 1;
        self.vars - 1
    }

    fn add_clause(&mut self, lits: &[Lit]) {
        self.solver.add_clause(lits.iter().map(|&l| lit(l)));
    }

    fn solve_assuming(&mut self, assumptions: &[Lit], limits: Limits) -> Answer {
        self.failed.clear();
        // CaDiCaL counts conflicts only; a propagation limit has no counterpart.
        let cap = i32::try_from(limits.conflicts).unwrap_or(i32::MAX);
        if self.solver.set_limit("conflicts", cap).is_err() {
            return Answer::Unknown;
        }
        self.conflicts = self
            .conflicts
            .saturating_add(limits.conflicts.min(cap as u64));
        match self.solver.solve_with(assumptions.iter().map(|&l| lit(l))) {
            Some(true) => Answer::Sat(
                (1..=self.vars as i32)
                    .map(|v| self.solver.value(v) == Some(true))
                    .collect(),
            ),
            Some(false) => {
                self.failed = (assumptions.iter().copied())
                    .filter(|&l| self.solver.failed(lit(l)))
                    .collect();
                Answer::Unsat
            }
            None => Answer::Unknown,
        }
    }

    fn failed_assumptions(&self) -> Vec<Lit> {
        self.failed.clone()
    }

    fn conflicts(&self) -> u64 {
        self.conflicts
    }

    fn propagations(&self) -> u64 {
        0
    }
}

/// CaDiCaL for [`solve::Config::backend`](bitwright::solve::Config::backend).
pub fn backend() -> bitwright::solve::Backend {
    bitwright::solve::Backend::new(|| Box::new(Cadical::new()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitwright::prove::{Incremental, IncrementalAnswer};
    use bitwright::solve::{Config, DecidedBy, Solver, Status};
    use bitwright::{Context, ParseOptions, Width};

    #[test]
    fn the_kept_circuit_answers_and_names_what_conflicts() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W16);
        let mut p = |s: &str| cx.parse(s, &o).unwrap();
        let (a, b, c, d) = (p("x * 3 == y"), p("y <u 10"), p("x >u 0x8000"), p("y == 0"));
        let mut inc = Incremental::on(Cadical::new(), 1 << 20);
        let limits = Limits::conflicts(100_000);
        assert!(matches!(
            inc.solve(&mut cx, &[a, b, c], limits).unwrap(),
            IncrementalAnswer::Sat(_)
        ));
        let IncrementalAnswer::Unsat(core) = inc.solve(&mut cx, &[a, b, c, d], limits).unwrap()
        else {
            panic!("x * 3 == 0 only at x == 0");
        };
        assert!([0, 2, 3].iter().all(|k| core.contains(k)), "{core:?}");
        let IncrementalAnswer::Sat(m) = inc.solve(&mut cx, &[a, d], limits).unwrap() else {
            panic!("x == 0 is a model");
        };
        assert!(m.iter().all(|(_, v)| v.is_zero()), "{m:?}");
    }

    /// A multiplier miter the native search leaves at its budget (and at a hundred times it),
    /// and CaDiCaL decides in a few seconds.
    #[test]
    fn a_long_search_goes_to_cadical() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(7).unwrap());
        // Distributivity, with the simplifier off so that only a search can decide it.
        let e = cx.parse("x * (y + z) != x * y + x * z", &o).unwrap();
        let prove = bitwright::prove::Config::default()
            .with_simplify(false)
            .with_max_conflicts(2_000_000);
        let cfg = Config::default().with_prove(prove);
        let mut native = Solver::new(cfg.clone().with_prove(prove.with_max_conflicts(3_000)));
        native.assert(&cx, e).unwrap();
        assert!(matches!(native.check(&mut cx).unwrap(), Status::Unknown(_)));
        let mut s = Solver::new(cfg.with_backend(Some(backend())));
        s.assert(&cx, e).unwrap();
        assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
        assert_eq!(s.decided_by(), Some(DecidedBy::Backend));
    }
}
