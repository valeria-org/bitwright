//! The solver: an assertion stack, checks with models and cores (bitwright.h, "solving").

use core::ffi::c_int;

use bw::solve::{CoreItem, Solver, Status};

use super::{BwContext, BwValue, Out, expr, exprs, get_mut, invalid, run, run_new, slice, value};

/// `bw_solver`.
#[derive(Debug, Default)]
pub struct BwSolver {
    solver: Solver,
}

/// A check's answers, as `bitwright.h` numbers them.
const BW_UNSAT: c_int = 0;
const BW_SAT: c_int = 1;
const BW_UNKNOWN: c_int = 2;

/// In a core: an assumption's position, marked apart from an assertion's.
const BW_CORE_ASSUMPTION: u32 = 1 << 31;

#[unsafe(no_mangle)]
pub extern "C" fn bw_solver_new() -> *mut BwSolver {
    run_new(|| Ok(BwSolver::default()))
}

/// # Safety
/// `s` is NULL or a solver from `bw_solver_new`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_solver_free(s: *mut BwSolver) {
    if !s.is_null() {
        drop(unsafe { Box::from_raw(s) });
    }
}

/// # Safety
/// `s` and `cx` are live; `index` is NULL or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_solver_assert(
    s: *mut BwSolver,
    cx: *mut BwContext,
    p: u64,
    index: *mut u32,
) -> c_int {
    run(|| {
        let s = &mut unsafe { get_mut(s, "s") }?.solver;
        let cx = &unsafe { get_mut(cx, "cx") }?.cx;
        let at = s.assert(cx, expr(p)?)?;
        if let Some(index) = unsafe { index.as_mut() } {
            *index = at as u32;
        }
        Ok(())
    })
}

/// # Safety
/// `s` is live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_solver_push(s: *mut BwSolver) -> c_int {
    run(|| {
        unsafe { get_mut(s, "s") }?.solver.push();
        Ok(())
    })
}

/// # Safety
/// `s` is live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_solver_pop(s: *mut BwSolver, scopes: u32) -> c_int {
    run(|| Ok(unsafe { get_mut(s, "s") }?.solver.pop(scopes as usize)?))
}

/// # Safety
/// `s` and `cx` are live, `assumptions` holds `n` handles, `answer` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_solver_check(
    s: *mut BwSolver,
    cx: *mut BwContext,
    assumptions: *const u64,
    n: usize,
    answer: *mut c_int,
) -> c_int {
    run(|| {
        let s = &mut unsafe { get_mut(s, "s") }?.solver;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let assumptions = exprs(unsafe { slice(assumptions, n, "assumptions") }?)?;
        let answer = Out::new(answer, "answer")?;
        let status = match s.check_assuming(cx, &assumptions)? {
            Status::Sat => BW_SAT,
            Status::Unsat => BW_UNSAT,
            _ => BW_UNKNOWN,
        };
        unsafe { answer.set(status) };
        Ok(())
    })
}

/// # Safety
/// `s` and `cx` are live, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_solver_value(
    s: *mut BwSolver,
    cx: *mut BwContext,
    e: u64,
    out: *mut BwValue,
) -> c_int {
    run(|| {
        let s = &unsafe { get_mut(s, "s") }?.solver;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let v = (s.value(cx, expr(e)?)?)
            .ok_or_else(|| invalid("no model: the last check did not answer BW_SAT"))?;
        unsafe { out.set(value(&v)) };
        Ok(())
    })
}

/// # Safety
/// `s` and `cx` are live, `core` is valid for `capacity` writes (or NULL when it is 0), `len`
/// is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_solver_core(
    s: *mut BwSolver,
    cx: *mut BwContext,
    core: *mut u32,
    capacity: usize,
    len: *mut usize,
) -> c_int {
    run(|| {
        let s = &mut unsafe { get_mut(s, "s") }?.solver;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let len = Out::new(len, "len")?;
        let items = (s.unsat_core(cx)?)
            .ok_or_else(|| invalid("no core: the last check did not answer BW_UNSAT"))?;
        if capacity > 0 && core.is_null() {
            return Err(invalid("`core` is NULL"));
        }
        for (k, item) in items.iter().take(capacity).enumerate() {
            let code = match *item {
                CoreItem::Assertion(i) => i as u32,
                CoreItem::Assumption(i) => i as u32 | BW_CORE_ASSUMPTION,
                _ => u32::MAX,
            };
            unsafe { core.add(k).write(code) };
        }
        unsafe { len.set(items.len()) };
        Ok(())
    })
}
