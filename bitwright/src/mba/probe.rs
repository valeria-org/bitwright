//! PROTOTYPE, not for release: the investigations of how symbolic certificate work is charged
//! (`docs/proposals/symbolic-charge.md`) and of how the MBA solver's steps are tied to the
//! engine's budget (`docs/proposals/solver-budget.md`, the `BW_SOLVER_*` switches below).
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
//! charged, user-space instructions (through a clock the host installs) and nanoseconds; and a
//! record of every solver call the engine makes (steps, instructions, CPU time), with the
//! questions of long ones written out on request (`BW_DUMP_OVER`, `BW_DUMP_FILE`).

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

// ---------------------------------------------------------------------------------------------
// PROTOTYPE (solver-budget investigation): how the engine ties the MBA solver's own work (its
// `MbaBudget::steps`) to the run's budget. Read once from the environment:
//
// - `BW_SOLVER_MODE`: `off` (default, today: the solver runs under the configured steps and a
//   call is charged one `mba_calls` unit); `charge` (the configured steps; afterwards the steps
//   it spent are charged as pass work at the rate, at most what is left); `bound` (the call runs
//   within `min(steps, left pass work / rate)` and what it spent is charged at the rate);
//   `derive` (within `min(steps, left / rate)`, nothing charged); `scale` (within
//   `min(steps, the call's pass-work limit / rate)`: a per-call cap scaled by the fuel, not by
//   what is left; nothing charged); `account` (an account of its own, `BW_SOLVER_ACCOUNT` steps
//   per unit of the node-visit limit, the fuel: the call runs within `min(steps, what is left of
//   it)` and what it spent is charged to it).
// - `BW_SOLVER_RATE`: pass-work units per solver step (default 64).
// - `BW_SOLVER_ACCOUNT`: steps per unit of fuel for `account` (default 256).
// - `BW_SOLVER_ROUND`: `pow2` rounds a limit that the budget lowered down to a power of two
//   (so that the solver's memo, keyed by the budget, still hits); default `exact`.
// - `BW_SOLVER_FLOOR`: a call whose limit would be below this many steps is not made (over
//   budget); default 1.
// ---------------------------------------------------------------------------------------------

/// How solver steps are tied to the run's budget.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum SolverMode {
    Off,
    Charge,
    Bound,
    Derive,
    Scale,
    Account,
}

/// The solver switches.
#[derive(Copy, Clone, Debug)]
pub(crate) struct SolverSwitch {
    pub(crate) mode: SolverMode,
    pub(crate) rate: u64,
    pub(crate) account: u64,
    pub(crate) pow2: bool,
    pub(crate) floor: u64,
}

pub(crate) fn solver_switch() -> &'static SolverSwitch {
    static S: OnceLock<SolverSwitch> = OnceLock::new();
    S.get_or_init(|| {
        let num = |v: &str, d: u64| {
            std::env::var(v)
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(d)
        };
        let mode = match std::env::var("BW_SOLVER_MODE").as_deref() {
            Ok("charge") => SolverMode::Charge,
            Ok("bound") => SolverMode::Bound,
            Ok("derive") => SolverMode::Derive,
            Ok("scale") => SolverMode::Scale,
            Ok("account") => SolverMode::Account,
            _ => SolverMode::Off,
        };
        SolverSwitch {
            mode,
            rate: num("BW_SOLVER_RATE", 64).max(1),
            account: num("BW_SOLVER_ACCOUNT", 256),
            pow2: std::env::var("BW_SOLVER_ROUND").is_ok_and(|r| r == "pow2"),
            floor: num("BW_SOLVER_FLOOR", 1).max(1),
        }
    })
}

/// A step limit the budget lowered to `limit` (below the configured `steps`), rounded as the
/// switches say.
pub(crate) fn lowered(steps: u64, limit: u64) -> u64 {
    if limit >= steps {
        return steps;
    }
    if solver_switch().pow2 && limit > 0 {
        1 << (63 - limit.leading_zeros())
    } else {
        limit
    }
}

thread_local! {
    /// Steps the solver's meters have consumed on this thread (see `certify::Steps::solver`).
    static SOLVER_STEPS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Whether the last question was answered from the solver's memo.
    static MEMO_HIT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Adds steps a solver meter consumed.
#[inline]
pub(crate) fn solver_steps(n: u64) {
    SOLVER_STEPS.with(|c| c.set(c.get().saturating_add(n)));
}

/// Steps the solver's meters consumed since the last call, cleared.
pub(crate) fn take_solver_steps() -> u64 {
    SOLVER_STEPS.with(|c| c.replace(0))
}

/// Steps the solver's meters consumed since the last call (not cleared).
pub(crate) fn peek_solver_steps() -> u64 {
    SOLVER_STEPS.with(std::cell::Cell::get)
}

/// Notes a memo hit.
pub(crate) fn memo_hit() {
    MEMO_HIT.with(|c| c.set(true));
}

/// Whether the last question was a memo hit, cleared.
pub(crate) fn take_memo_hit() -> bool {
    MEMO_HIT.with(|c| c.replace(false))
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
    static CPU: OnceLock<fn() -> u64> = OnceLock::new();

    /// Installs the instruction clock: a function reading a free-running counter.
    pub fn set_clock(f: fn() -> u64) {
        let _ = CLOCK.set(f);
    }

    /// Installs a thread CPU-time clock (nanoseconds), read around solver calls only.
    pub fn set_cpu_clock(f: fn() -> u64) {
        let _ = CPU.set(f);
    }

    fn now() -> u64 {
        CLOCK.get().map_or(0, |f| f())
    }

    fn cpu_now() -> u64 {
        CPU.get().map_or(0, |f| f())
    }

    /// Work in progress.
    pub(crate) struct Span {
        kind: Kind,
        i0: u64,
        t0: Instant,
        c0: u64,
    }

    pub(crate) fn begin(kind: Kind) -> Span {
        let c0 = if matches!(kind, Kind::Solve) {
            cpu_now()
        } else {
            0
        };
        let t0 = Instant::now();
        Span {
            kind,
            i0: now(),
            t0,
            c0,
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

    /// One solver call from the engine.
    #[derive(Copy, Clone, Debug, Default)]
    pub struct Call {
        /// User-space instructions (0 without a clock), the probe's own cost included.
        pub instr: u64,
        pub nanos: u64,
        /// Thread CPU time (0 without a CPU clock).
        pub cpu_nanos: u64,
        /// Steps the solver's meters consumed.
        pub steps: u64,
        /// The step limit it ran under.
        pub limit: u64,
        /// The question's nodes and variables.
        pub nodes: u32,
        pub vars: u32,
        /// 0 simplified, 1 no simpler, 2 unsupported, 3 exhausted.
        pub answer: u8,
        /// Answered from the solver's memo.
        pub memo: bool,
        /// Pass work left when it was asked, and the run's pass-work limit.
        pub left: u64,
        pub cap: u64,
    }

    thread_local! {
        static CALLS: RefCell<Vec<Call>> = const { RefCell::new(Vec::new()) };
    }

    /// A question as text, for `--solver-worst` to read back: the variables' widths, then one
    /// node per token (`v3`, `c0x1f:8`, `+ - * n & | ^ ~`, `<<k`, `>>k`, `zx:8`, `sx:8`,
    /// `tr:8`, each with its operands as `@a,b`).
    pub fn question_text(m: &crate::mba::MbaExpr) -> String {
        use crate::mba::MOp;
        let vars: Vec<String> = m.vars().iter().map(|w| w.bits().to_string()).collect();
        let mut out = format!("{};", vars.join(","));
        for n in m.nodes() {
            let w = n.width.bits();
            let t = match &n.op {
                MOp::Const(v) => format!("c{v:x}:{w}"),
                MOp::Var(i) => format!("v{i}"),
                MOp::Add => "+".into(),
                MOp::Sub => "-".into(),
                MOp::Mul => "*".into(),
                MOp::Neg => "n".into(),
                MOp::And => "&".into(),
                MOp::Or => "|".into(),
                MOp::Xor => "^".into(),
                MOp::Not => "~".into(),
                MOp::Shl(k) => format!("<<{k}"),
                MOp::LShr(k) => format!(">>{k}"),
                MOp::Zext => format!("zx:{w}"),
                MOp::Sext => format!("sx:{w}"),
                MOp::Trunc => format!("tr:{w}"),
            };
            let args = &n.args[..n.op.arity()];
            out.push(' ');
            out.push_str(&t);
            if !args.is_empty() {
                let a: Vec<String> = args.iter().map(|a| a.to_string()).collect();
                out.push('@');
                out.push_str(&a.join(","));
            }
        }
        out
    }

    /// With `BW_DUMP_OVER=N` and `BW_DUMP_FILE=PATH`, appends every question whose call took at
    /// least N instructions to PATH (instructions, steps, answer, question).
    pub(crate) fn dump(c: &Call, m: &crate::mba::MbaExpr) {
        static OVER: OnceLock<Option<(u64, String)>> = OnceLock::new();
        let Some((over, path)) = OVER.get_or_init(|| {
            let n = std::env::var("BW_DUMP_OVER").ok()?.parse().ok()?;
            Some((n, std::env::var("BW_DUMP_FILE").ok()?))
        }) else {
            return;
        };
        if c.instr < *over {
            return;
        }
        use std::io::Write;
        if let Ok(mut f) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        {
            let _ = writeln!(
                f,
                "{}\t{}\t{}\t{}\t{}",
                c.instr,
                c.steps,
                c.answer,
                u8::from(c.memo),
                question_text(m)
            );
        }
    }

    /// Ends a solver call's span and records it (tally and call list).
    pub(crate) fn end_call(s: Span, mut c: Call) -> Call {
        let i1 = now();
        let nanos = u64::try_from(s.t0.elapsed().as_nanos()).unwrap_or(u64::MAX);
        c.cpu_nanos = cpu_now().saturating_sub(s.c0);
        c.instr = i1.saturating_sub(s.i0);
        c.nanos = nanos;
        let g = usize::from(GATE.with(Cell::get));
        TALLIES.with(|t| {
            let e = &mut t.borrow_mut()[g][s.kind as usize];
            e.calls += 1;
            e.work += c.steps;
            e.instr += c.instr;
            e.nanos += nanos;
            e.proved += u64::from(c.answer == 0);
        });
        CALLS.with(|v| v.borrow_mut().push(c));
        c
    }

    /// Steps the solver's meters consumed since the last call, cleared (for callers outside
    /// the library).
    pub fn take_solver_steps_pub() -> u64 {
        super::take_solver_steps()
    }

    /// The solver calls so far (this thread), cleared.
    pub fn take_calls() -> Vec<Call> {
        CALLS.with(|v| std::mem::take(&mut *v.borrow_mut()))
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

    #[derive(Copy, Clone, Default)]
    #[allow(dead_code)] // read only with the feature
    pub(crate) struct Call {
        pub(crate) instr: u64,
        pub(crate) nanos: u64,
        pub(crate) cpu_nanos: u64,
        pub(crate) steps: u64,
        pub(crate) limit: u64,
        pub(crate) nodes: u32,
        pub(crate) vars: u32,
        pub(crate) answer: u8,
        pub(crate) memo: bool,
        pub(crate) left: u64,
        pub(crate) cap: u64,
    }

    #[inline(always)]
    pub(crate) fn end_call(_: Span, c: Call) -> Call {
        c
    }

    #[inline(always)]
    pub(crate) fn dump(_: &Call, _: &crate::mba::MbaExpr) {}

    #[inline(always)]
    pub(crate) fn gate<T>(f: impl FnOnce() -> T) -> T {
        f()
    }
}
