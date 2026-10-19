//! PROTOTYPE, not for release: the investigation of how symbolic certificate work is charged.
//!
//! The charge per unit of symbolic work (a monomial operation of the certifier's
//! `symbolic_equal`) comes from the environment, read once: `BW_SYMBOLIC_CHARGE` (units per
//! unit of work, default 1, today's rate), `BW_SYMBOLIC_SCOPE` (`all`, `gate` for the engine's
//! evidence gate only, or `solver` for the solver's own certificates only; default `all`) and
//! `BW_SYMBOLIC_MODE` (`clamp`: a comparison outside a test runs in full and is charged at most
//! what is left, as today; `bound`: it runs within what is left and declines past it; default
//! `clamp`) and `BW_SYMBOLIC_RESERVE` (`0`: the comparison a test runs first is tried within
//! what is left, not within what leaves the test affordable; default today's reserve). This
//! breaks the determinism contract (no environment variables) and exists only to measure the
//! options.
//!
//! With feature `cost-probe`, tallies of certificate work by kind: calls, symbolic work, units
//! charged, user-space instructions (through a clock the host installs) and nanoseconds.

use std::sync::OnceLock;

/// Which meter charges.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Scope {
    /// The engine's evidence gate (pass work).
    Gate,
    /// The solver's own certificates (its steps) and every other caller.
    Solver,
}

struct Switch {
    k: u64,
    gate: bool,
    solver: bool,
    bound: bool,
    reserve: bool,
}

fn switch() -> &'static Switch {
    static S: OnceLock<Switch> = OnceLock::new();
    S.get_or_init(|| {
        let k = std::env::var("BW_SYMBOLIC_CHARGE")
            .ok()
            .and_then(|s| s.parse().ok())
            .filter(|&k: &u64| k >= 1)
            .unwrap_or(1);
        let scope = std::env::var("BW_SYMBOLIC_SCOPE").unwrap_or_default();
        let bound = std::env::var("BW_SYMBOLIC_MODE").is_ok_and(|m| m == "bound");
        let reserve = std::env::var("BW_SYMBOLIC_RESERVE").map_or(true, |r| r != "0");
        Switch {
            k,
            gate: scope != "solver",
            solver: scope != "gate",
            bound,
            reserve,
        }
    })
}

fn applies(scope: Scope) -> bool {
    let s = switch();
    match scope {
        Scope::Gate => s.gate,
        Scope::Solver => s.solver,
    }
}

/// Units a meter of `scope` charges per unit of symbolic work.
pub(crate) fn rate(scope: Scope) -> u64 {
    if applies(scope) { switch().k } else { 1 }
}

/// Whether a symbolic comparison outside a test runs within what is left of a meter of `scope`.
pub(crate) fn bound(scope: Scope) -> bool {
    switch().bound && applies(scope)
}

/// Whether the symbolic comparison a test runs first leaves the test affordable (today's rule;
/// `BW_SYMBOLIC_RESERVE=0` tries it within what is left alone, and a test it then leaves
/// unaffordable is over budget).
pub(crate) fn reserve(scope: Scope) -> bool {
    switch().reserve || !applies(scope)
}

#[cfg(feature = "cost-probe")]
pub use tally::*;
#[cfg(not(feature = "cost-probe"))]
pub(crate) use tally::*;

#[cfg(feature = "cost-probe")]
mod tally {
    use std::cell::{Cell, RefCell};
    use std::sync::OnceLock;
    use std::time::Instant;

    /// Kinds of work.
    #[derive(Copy, Clone, Debug, PartialEq, Eq)]
    pub enum Kind {
        /// The symbolic comparison a polynomial test runs first.
        SymFirst = 0,
        /// The symbolic comparison where no test fits or one is not affordable.
        SymFallback = 1,
        /// Evaluation tests (signature, single bit, sparse, grid, exhaustive).
        Eval = 2,
        /// The refutation sample.
        Sample = 3,
        /// A whole certificate (`certify::prove` at the gate, `certify::check` elsewhere).
        Cert = 4,
        /// A solver call (from the engine).
        Solve = 5,
    }

    /// The number of kinds.
    pub const KINDS: usize = 6;

    /// What one kind of work took.
    #[derive(Copy, Clone, Debug, Default)]
    pub struct Tally {
        pub calls: u64,
        /// Symbolic work (monomial operations), for the symbolic kinds.
        pub work: u64,
        /// Units charged to the meter.
        pub units: u64,
        /// User-space instructions (0 without a clock).
        pub instr: u64,
        pub nanos: u64,
        pub proved: u64,
    }

    /// By meter (0: the solver's and other callers', 1: the engine's evidence gate), by kind.
    pub type Tallies = [[Tally; KINDS]; 2];

    thread_local! {
        static TALLIES: RefCell<Tallies> = RefCell::new(Tallies::default());
        static GATE: Cell<bool> = const { Cell::new(false) };
    }

    static CLOCK: OnceLock<fn() -> u64> = OnceLock::new();

    /// Installs the instruction clock: a function reading a free-running counter.
    pub fn set_clock(f: fn() -> u64) {
        let _ = CLOCK.set(f);
    }

    fn now() -> u64 {
        CLOCK.get().map_or(0, |f| f())
    }

    /// Work in progress.
    pub(crate) struct Span {
        kind: Kind,
        i0: u64,
        t0: Instant,
    }

    pub(crate) fn begin(kind: Kind) -> Span {
        let t0 = Instant::now();
        Span {
            kind,
            i0: now(),
            t0,
        }
    }

    pub(crate) fn end(s: Span, work: u64, units: u64, proved: bool) {
        let i1 = now();
        let nanos = u64::try_from(s.t0.elapsed().as_nanos()).unwrap_or(u64::MAX);
        let g = usize::from(GATE.with(Cell::get));
        TALLIES.with(|t| {
            let e = &mut t.borrow_mut()[g][s.kind as usize];
            e.calls += 1;
            e.work += work;
            e.units += units;
            e.instr += i1.saturating_sub(s.i0);
            e.nanos += nanos;
            e.proved += u64::from(proved);
        });
    }

    /// Runs `f` as the engine's evidence gate.
    pub(crate) fn gate<T>(f: impl FnOnce() -> T) -> T {
        let old = GATE.with(|g| g.replace(true));
        let r = f();
        GATE.with(|g| g.set(old));
        r
    }

    /// The tallies so far (this thread), cleared.
    pub fn take() -> Tallies {
        TALLIES.with(|t| std::mem::take(&mut *t.borrow_mut()))
    }

    /// What `n` empty spans take (the cost of measuring), outside the tallies.
    pub fn overhead(n: u64) -> Tally {
        let saved = take();
        for _ in 0..n {
            let s = begin(Kind::Cert);
            end(s, 0, 0, false);
        }
        let t = take()[0][Kind::Cert as usize];
        TALLIES.with(|x| *x.borrow_mut() = saved);
        t
    }
}

#[cfg(not(feature = "cost-probe"))]
mod tally {
    #[derive(Copy, Clone)]
    pub(crate) enum Kind {
        SymFirst,
        SymFallback,
        Eval,
        Sample,
        Cert,
        Solve,
    }

    pub(crate) struct Span;

    #[inline(always)]
    pub(crate) fn begin(_: Kind) -> Span {
        Span
    }

    #[inline(always)]
    pub(crate) fn end(_: Span, _: u64, _: u64, _: bool) {}

    #[inline(always)]
    pub(crate) fn gate<T>(f: impl FnOnce() -> T) -> T {
        f()
    }
}
