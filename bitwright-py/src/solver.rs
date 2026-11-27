//! The solver: an assertion stack, checks with models and cores.

use std::sync::Mutex;

use bitwright::solve::{CoreItem, Optimum, Solver, Status, Values};
use bitwright::{Reliance, Truth};
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

use super::{Facts, OrRaise, PyContext, PyExpr, lock, py_facts, to_int, to_signed_int, wrap};

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

    /// Enumerates up to `limit` distinct values `e` can take under the assertions, in ascending
    /// unsigned order: `(values, exact)` where `exact` is True when no further values exist, or
    /// None when a search stopped undecided.
    #[pyo3(signature = (e, limit = 16))]
    fn enumerate<'py>(
        &self,
        py: Python<'py>,
        e: PyRef<'_, PyExpr>,
        limit: usize,
    ) -> PyResult<Option<(Vec<Bound<'py, PyAny>>, bool)>> {
        self.context(py, Some(&e))?;
        let mut s = lock(py, &self.s)?;
        let mut c = e.cx.bind(py).get().lock(py)?;
        match s.enumerate_values(&mut c, e.e, limit).or_raise()? {
            Values::Exact(vs) => {
                let ints = vs
                    .iter()
                    .map(|v| to_int(py, v))
                    .collect::<PyResult<Vec<_>>>()?;
                Ok(Some((ints, true)))
            }
            Values::AtLeast(vs) => {
                let ints = vs
                    .iter()
                    .map(|v| to_int(py, v))
                    .collect::<PyResult<Vec<_>>>()?;
                Ok(Some((ints, false)))
            }
            _ => Ok(None),
        }
    }

    /// Finds the exact minimum value `e` can take under the assertions (unsigned, or signed with
    /// `signed=True`), setting the solver's model to an optimal witness; None when unsatisfiable
    /// or undecided.
    #[pyo3(signature = (e, *, signed = false))]
    fn minimize<'py>(
        &self,
        py: Python<'py>,
        e: PyRef<'_, PyExpr>,
        signed: bool,
    ) -> PyResult<Option<Bound<'py, PyAny>>> {
        self.context(py, Some(&e))?;
        let mut s = lock(py, &self.s)?;
        let mut c = e.cx.bind(py).get().lock(py)?;
        let opt = if signed {
            s.minimize_signed(&mut c, e.e).or_raise()?
        } else {
            s.minimize(&mut c, e.e).or_raise()?
        };
        match opt {
            Optimum::Found(v) => Ok(Some(if signed {
                to_signed_int(py, &v)?
            } else {
                to_int(py, &v)?
            })),
            _ => Ok(None),
        }
    }

    /// Finds the exact maximum value `e` can take under the assertions (unsigned, or signed with
    /// `signed=True`), setting the solver's model to an optimal witness; None when unsatisfiable
    /// or undecided.
    #[pyo3(signature = (e, *, signed = false))]
    fn maximize<'py>(
        &self,
        py: Python<'py>,
        e: PyRef<'_, PyExpr>,
        signed: bool,
    ) -> PyResult<Option<Bound<'py, PyAny>>> {
        self.context(py, Some(&e))?;
        let mut s = lock(py, &self.s)?;
        let mut c = e.cx.bind(py).get().lock(py)?;
        let opt = if signed {
            s.maximize_signed(&mut c, e.e).or_raise()?
        } else {
            s.maximize(&mut c, e.e).or_raise()?
        };
        match opt {
            Optimum::Found(v) => Ok(Some(if signed {
                to_signed_int(py, &v)?
            } else {
                to_int(py, &v)?
            })),
            _ => Ok(None),
        }
    }

    /// Solver-tightened facts of `e` under the assertions, or None when unsatisfiable.
    fn tighten_facts(&self, py: Python<'_>, e: PyRef<'_, PyExpr>) -> PyResult<Option<Facts>> {
        self.context(py, Some(&e))?;
        let mut s = lock(py, &self.s)?;
        let f = {
            let mut c = e.cx.bind(py).get().lock(py)?;
            s.tighten_facts(&mut c, e.e).or_raise()?
        };
        f.map(|f| py_facts(py, &f, e.width, Reliance::NONE))
            .transpose()
    }

    /// Whether `target` is uniquely determined by `inputs` under the assertions: True, False, or
    /// None when undecided.
    fn is_determined_by(
        &self,
        py: Python<'_>,
        target: PyRef<'_, PyExpr>,
        inputs: Vec<PyRef<'_, PyExpr>>,
    ) -> PyResult<Option<bool>> {
        self.context(py, Some(&target))?;
        for inp in &inputs {
            self.context(py, Some(inp))?;
        }
        let ins: Vec<_> = inputs.iter().map(|x| x.e).collect();
        let mut s = lock(py, &self.s)?;
        let mut c = target.cx.bind(py).get().lock(py)?;
        Ok(
            match s.is_determined_by(&mut c, target.e, &ins).or_raise()? {
                Truth::True => Some(true),
                Truth::False => Some(false),
                Truth::Unknown => None,
            },
        )
    }

    /// Closed-form expression over `inputs` proved equal to `target` under the assertions, or
    /// None.
    fn functional_def(
        &self,
        py: Python<'_>,
        target: PyRef<'_, PyExpr>,
        inputs: Vec<PyRef<'_, PyExpr>>,
    ) -> PyResult<Option<PyExpr>> {
        self.context(py, Some(&target))?;
        for inp in &inputs {
            self.context(py, Some(inp))?;
        }
        let ins: Vec<_> = inputs.iter().map(|x| x.e).collect();
        let cxb = target.cx.bind(py);
        let def = {
            let mut s = lock(py, &self.s)?;
            let mut c = cxb.get().lock(py)?;
            s.functional_def(&mut c, target.e, &ins).or_raise()?
        };
        let c = cxb.get().lock(py)?;
        def.map(|d| wrap(cxb, &c, d)).transpose()
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
