//! The solver: an assertion stack, checks with models and cores.

use std::sync::Mutex;

use bitwright::solve::{CoreItem, Solver, Status};
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

use super::{OrRaise, PyContext, PyExpr, lock, to_int};

/// 1-bit predicates asserted on a stack, and whether they hold together: `check()` answers
/// True (with `value()` reading the model), False (with `core()` naming what conflicts) or
/// None (not decided). A solver holds expressions of one context.
#[pyclass(frozen, name = "Solver", module = "bitwright")]
#[derive(Debug, Default)]
pub(super) struct PySolver {
    s: Mutex<Solver>,
    /// The context of what was asserted or assumed first.
    cx: Mutex<Option<Py<PyContext>>>,
}

impl PySolver {
    /// The solver's context, which `e` (if given) must be of; `None` before any expression.
    fn context(&self, py: Python<'_>, e: Option<&PyExpr>) -> PyResult<Option<Py<PyContext>>> {
        let mut own = lock(py, &self.cx)?;
        match (own.as_ref(), e) {
            (Some(cx), Some(e)) if !cx.is(&e.cx) => {
                Err(PyValueError::new_err("an expression of another context"))
            }
            (None, Some(e)) => {
                *own = Some(e.cx.clone_ref(py));
                Ok(Some(e.cx.clone_ref(py)))
            }
            (cx, _) => Ok(cx.map(|c| c.clone_ref(py))),
        }
    }
}

#[pymethods]
impl PySolver {
    /// An empty solver; with predicates, each is asserted.
    #[new]
    #[pyo3(signature = (*predicates))]
    fn new(py: Python<'_>, predicates: Vec<PyRef<'_, PyExpr>>) -> PyResult<Self> {
        let s = PySolver::default();
        for p in predicates {
            s.add(py, p)?;
        }
        Ok(s)
    }

    /// Asserts the 1-bit predicate: its position among the assertions (how a core names it).
    fn add(&self, py: Python<'_>, predicate: PyRef<'_, PyExpr>) -> PyResult<usize> {
        self.context(py, Some(&predicate))?;
        let c = predicate.cx.bind(py).get().lock(py)?;
        lock(py, &self.s)?.assert(&c, predicate.e).or_raise()
    }

    /// Opens a scope: `pop()` drops the assertions made since.
    fn push(&self, py: Python<'_>) -> PyResult<()> {
        lock(py, &self.s)?.push();
        Ok(())
    }

    /// Closes the `scopes` innermost scopes.
    #[pyo3(signature = (scopes = 1))]
    fn pop(&self, py: Python<'_>, scopes: usize) -> PyResult<()> {
        lock(py, &self.s)?.pop(scopes).or_raise()
    }

    /// Whether the assertions and the `assumptions` (of this check only) hold together:
    /// True, False, or None when not decided.
    #[pyo3(signature = (*assumptions))]
    fn check(&self, py: Python<'_>, assumptions: Vec<PyRef<'_, PyExpr>>) -> PyResult<Option<bool>> {
        let mut cx = self.context(py, None)?;
        for a in &assumptions {
            cx = self.context(py, Some(a))?;
        }
        // Nothing asserted or assumed: nothing to contradict.
        let Some(cx) = cx else { return Ok(Some(true)) };
        let mut c = cx.bind(py).get().lock(py)?;
        let es: Vec<_> = assumptions.iter().map(|a| a.e).collect();
        Ok(
            match (lock(py, &self.s)?.check_assuming(&mut c, &es)).or_raise()? {
                Status::Sat => Some(true),
                Status::Unsat => Some(false),
                _ => None,
            },
        )
    }

    /// After a check answered True: the value of `e` in the model, as an int.
    fn value<'py>(&self, py: Python<'py>, e: PyRef<'_, PyExpr>) -> PyResult<Bound<'py, PyAny>> {
        self.context(py, Some(&e))?;
        let s = lock(py, &self.s)?;
        let mut c = e.cx.bind(py).get().lock(py)?;
        match s.value(&mut c, e.e).or_raise()? {
            Some(v) => to_int(py, &v),
            None => Err(PyValueError::new_err(
                "no model: the last check was not True",
            )),
        }
    }

    /// After a check answered False: what conflicts, as `("assertion", i)` and
    /// `("assumption", i)` pairs. Sound, not minimal.
    fn core(&self, py: Python<'_>) -> PyResult<Vec<(&'static str, usize)>> {
        let none = || PyValueError::new_err("no core: the last check was not False");
        let cx = self.context(py, None)?.ok_or_else(none)?;
        let mut c = cx.bind(py).get().lock(py)?;
        let core = (lock(py, &self.s)?.unsat_core(&mut c))
            .or_raise()?
            .ok_or_else(none)?;
        Ok((core.into_iter())
            .map(|item| match item {
                CoreItem::Assertion(i) => ("assertion", i),
                CoreItem::Assumption(i) => ("assumption", i),
                _ => ("other", 0),
            })
            .collect())
    }

    fn __len__(&self, py: Python<'_>) -> PyResult<usize> {
        Ok(lock(py, &self.s)?.assertions().len())
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let s = lock(py, &self.s)?;
        Ok(format!(
            "<bitwright.Solver: {} assertions, {} scopes>",
            s.assertions().len(),
            s.depth()
        ))
    }
}
