//! What a compiler needs beyond simplifying: host rewrites written in Python with their
//! checker, semantics templates, lowering a function into expressions and raising results back,
//! and the counters of a run.
//!
//! A host rewrite runs inside the engine, with the context locked: it sees nodes through a
//! `Site` as integer handles, never as `Expr`s (whose methods would lock the context again). A
//! rewrite that uses the context it is simplifying anyway gets an error instead of a deadlock.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::ffi::c_void;
use std::sync::atomic::{AtomicPtr, Ordering};
use std::sync::{Arc, Mutex};

use bitwright::check::{RewriteCheckConfig, RewriteFailure};
use bitwright::engine::{PassCounts, Rewrite, Site, Stats};
use bitwright::translate::{Lowered, Lowering, Template};
use bitwright::{BinOp, CmpOpExt, Expr, KnownBits, PrintOptions, UnOp, View, Width};
use pyo3::exceptions::{PyRuntimeError, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyDict;

use super::{
    BitwrightError, Facts, OrRaise, PyContext, PyExpr, py_facts, to_bitvec, to_int, width, wrap,
};

// ----- the deadlock guard ---------------------------------------------------------------------

thread_local! {
    /// Host rewrite calls running on this thread (each inside an engine run that holds a
    /// context's lock).
    static IN_REWRITE: Cell<u32> = const { Cell::new(0) };
}

/// Whether this thread is running a host rewrite: a lock it cannot take at once is then likely
/// the one the engine holds, which it would wait for forever.
pub(super) fn in_rewrite() -> bool {
    IN_REWRITE.with(Cell::get) > 0
}

struct RewriteScope;

impl RewriteScope {
    fn enter() -> RewriteScope {
        IN_REWRITE.with(|n| n.set(n.get() + 1));
        RewriteScope
    }
}

impl Drop for RewriteScope {
    fn drop(&mut self) {
        IN_REWRITE.with(|n| n.set(n.get() - 1));
    }
}

// ----- host rewrites --------------------------------------------------------------------------

/// A Python callable as a [`Rewrite`].
#[derive(Debug)]
pub(super) struct PyHostRewrite {
    name: String,
    group: String,
    revision: u32,
    function: Py<PyAny>,
}

impl PyHostRewrite {
    fn call(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
        Python::attach(|py| {
            let _scope = RewriteScope::enter();
            let p: *mut Site<'_> = site;
            let handle = PySite {
                site: AtomicPtr::new(p.cast()),
            };
            let obj = match Py::new(py, handle) {
                Ok(o) => o,
                Err(err) => {
                    err.write_unraisable(py, Some(self.function.bind(py)));
                    return None;
                }
            };
            let r = self.function.call1(py, (obj.clone_ref(py), e.to_bits()));
            // The site is lent for the call only.
            obj.get()
                .site
                .store(core::ptr::null_mut(), Ordering::SeqCst);
            let r = r.and_then(|v| v.extract::<Option<u64>>(py));
            match r {
                Ok(v) => v.and_then(Expr::from_bits),
                Err(err) => {
                    // Reported as an exception that cannot propagate; the node is left.
                    err.write_unraisable(py, Some(self.function.bind(py)));
                    None
                }
            }
        })
    }
}

impl Rewrite for PyHostRewrite {
    fn name(&self) -> &str {
        &self.name
    }

    fn group(&self) -> &str {
        &self.group
    }

    fn revision(&self) -> u32 {
        self.revision
    }

    fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
        self.call(site, e)
    }
}

/// A rewrite written in Python, for `Engine(rewrites=...)` and `check_rewrite`: `function(site,
/// node)` returns the replacement of `node` (a handle of the site's context, built through the
/// site), or None to leave it. It is called with the interpreter lock held, once per node the
/// rule phases visit: best for prototyping. It must be deterministic (bump `revision` when its
/// results change). An exception it raises is reported through `sys.unraisablehook` and leaves
/// the node.
#[pyclass(frozen, name = "Rewrite", module = "bitwright")]
#[derive(Debug)]
pub(super) struct PyRewrite {
    pub(super) r: Arc<PyHostRewrite>,
}

#[pymethods]
impl PyRewrite {
    #[new]
    #[pyo3(signature = (name, function, *, group = String::from("host"), revision = 1))]
    fn new(name: String, function: Py<PyAny>, group: String, revision: u32) -> PyResult<Self> {
        Python::attach(|py| {
            if !function.bind(py).is_callable() {
                return Err(PyTypeError::new_err(
                    "a rewrite's function must be callable",
                ));
            }
            Ok(())
        })?;
        Ok(PyRewrite {
            r: Arc::new(PyHostRewrite {
                name,
                group,
                revision,
                function,
            }),
        })
    }

    #[getter]
    fn name(&self) -> &str {
        &self.r.name
    }

    #[getter]
    fn group(&self) -> &str {
        &self.r.group
    }

    #[getter]
    fn revision(&self) -> u32 {
        self.r.revision
    }

    fn __repr__(&self) -> String {
        format!("<bitwright.Rewrite {} in {}>", self.r.name, self.r.group)
    }
}

/// What a host rewrite may do at a node: inspect nodes, ask for their facts, build nodes. Nodes
/// are integer handles of the context being simplified. Valid during the rewrite's call only.
/// When the call's budget runs out, every request answers None.
#[pyclass(frozen, name = "Site", module = "bitwright")]
#[derive(Debug)]
pub(super) struct PySite {
    site: AtomicPtr<c_void>,
}

impl PySite {
    /// Runs `f` on the site, if it is still lent.
    fn with<T>(&self, f: impl FnOnce(&mut Site<'_>) -> T) -> PyResult<T> {
        let p = self.site.load(Ordering::SeqCst);
        if p.is_null() {
            return Err(PyRuntimeError::new_err(
                "a Site is valid only during the rewrite call it was given to",
            ));
        }
        // SAFETY: the pointer is the `&mut Site` of a rewrite call running on this thread (the
        // site is cleared before that call returns); the interpreter lock, held by every method
        // here, keeps two methods from using it at once.
        let site = unsafe { &mut *p.cast::<Site<'_>>() };
        Ok(f(site))
    }

    fn view(&self, e: u64) -> PyResult<Option<View>> {
        self.with(|s| Expr::from_bits(e).and_then(|e| s.view(e)))
    }

    /// Runs a construction on handles.
    fn make(&self, f: impl FnOnce(&mut Site<'_>) -> Option<Expr>) -> PyResult<Option<u64>> {
        self.with(|s| f(s).map(Expr::to_bits))
    }
}

fn handle(e: u64) -> Option<Expr> {
    Expr::from_bits(e)
}

fn unop(name: &str) -> PyResult<UnOp> {
    UnOp::ALL
        .into_iter()
        .find(|o| o.name() == name)
        .ok_or_else(|| PyValueError::new_err(format!("unknown unary operator {name:?}")))
}

fn binop(name: &str) -> PyResult<BinOp> {
    BinOp::ALL
        .into_iter()
        .find(|o| o.name() == name)
        .ok_or_else(|| PyValueError::new_err(format!("unknown binary operator {name:?}")))
}

fn cmpop(name: &str) -> PyResult<CmpOpExt> {
    CmpOpExt::ALL
        .into_iter()
        .find(|o| format!("{o:?}").to_lowercase() == name)
        .ok_or_else(|| PyValueError::new_err(format!("unknown comparison {name:?}")))
}

#[pymethods]
impl PySite {
    /// The node's kind, as `Expr.kind` names it; None if `e` is not a handle of the site's
    /// context.
    fn kind(&self, e: u64) -> PyResult<Option<&'static str>> {
        Ok(self.view(e)?.map(|v| super::kind_name(&v)))
    }

    /// The node's operator, as `Expr.op` names it, else None.
    fn op(&self, e: u64) -> PyResult<Option<String>> {
        Ok(self.view(e)?.and_then(|v| super::op_name(&v)))
    }

    /// The node's operands, as `Expr.children` orders them.
    fn children(&self, e: u64) -> PyResult<Vec<u64>> {
        self.with(|s| {
            let Some(e) = handle(e) else {
                return Vec::new();
            };
            s.context()
                .children(e)
                .map(|c| c.map(Expr::to_bits).collect())
                .unwrap_or_default()
        })
    }

    /// The first bit of an extract (the output of an extension call), else None.
    fn lo(&self, e: u64) -> PyResult<Option<u16>> {
        Ok(match self.view(e)? {
            Some(View::Extract { lo, .. }) => Some(lo),
            Some(View::Ext { output, .. }) => Some(u16::from(output)),
            _ => None,
        })
    }

    /// The width of `e`, None if it is not a handle of the site's context.
    fn width(&self, e: u64) -> PyResult<Option<u16>> {
        self.with(|s| handle(e).and_then(|e| s.width(e)).map(Width::bits))
    }

    /// The value of `e` (unsigned) if it is a constant.
    fn value<'py>(&self, py: Python<'py>, e: u64) -> PyResult<Option<Bound<'py, PyAny>>> {
        let v = self.with(|s| handle(e).and_then(|e| s.as_const(e)))?;
        v.map(|v| to_int(py, &v)).transpose()
    }

    /// The facts of `e` under the run's assumptions and the declared known bits; None when the
    /// fact budget declined the query (the node's result is then not final). `relies_on` is
    /// empty: the engine keeps track of what the result relies on.
    fn facts(&self, py: Python<'_>, e: u64) -> PyResult<Option<Facts>> {
        let f = self.with(|s| handle(e).and_then(|e| Some((s.facts(e)?, s.width(e)?))))?;
        f.map(|(f, w)| py_facts(py, &f, w.bits(), bitwright::Reliance::NONE))
            .transpose()
    }

    /// `e` in the text syntax, None if it is not a handle of the site's context.
    #[pyo3(signature = (e, *, lets = true))]
    fn to_string(&self, e: u64, lets: bool) -> PyResult<Option<String>> {
        self.with(|s| {
            let e = handle(e)?;
            s.width(e)?;
            let opts = PrintOptions::default().with_lets(lets);
            Some(s.context().display_with(e, opts).to_string())
        })
    }

    /// The constant `value` of `width` bits (an int; negative in two's complement).
    fn constant(&self, value: &Bound<'_, PyAny>, width: u16) -> PyResult<Option<u64>> {
        let v = to_bitvec(value, super::width(width)?)?;
        self.make(|s| s.constant(&v))
    }

    /// The unary operator named `op` (`"neg"`, `"popcnt"`, ...).
    fn un(&self, op: &str, a: u64) -> PyResult<Option<u64>> {
        let op = unop(op)?;
        self.make(|s| s.un(op, handle(a)?))
    }

    /// The binary operator named `op` (`"add"`, `"shl"`, `"urem"`, ...).
    fn bin(&self, op: &str, a: u64, b: u64) -> PyResult<Option<u64>> {
        let op = binop(op)?;
        self.make(|s| s.bin(op, handle(a)?, handle(b)?))
    }

    /// The comparison named `op` (`"eq"`, `"ult"`, `"sge"`, ...), 1 bit.
    fn cmp(&self, op: &str, a: u64, b: u64) -> PyResult<Option<u64>> {
        let op = cmpop(op)?;
        self.make(|s| s.cmp(op, handle(a)?, handle(b)?))
    }

    fn zext(&self, a: u64, width: u16) -> PyResult<Option<u64>> {
        let w = super::width(width)?;
        self.make(|s| s.zext(handle(a)?, w))
    }

    fn sext(&self, a: u64, width: u16) -> PyResult<Option<u64>> {
        let w = super::width(width)?;
        self.make(|s| s.sext(handle(a)?, w))
    }

    fn trunc(&self, a: u64, width: u16) -> PyResult<Option<u64>> {
        let w = super::width(width)?;
        self.make(|s| s.trunc(handle(a)?, w))
    }

    /// Bits `[lo, lo + length)` of `a`.
    fn extract(&self, a: u64, lo: u16, length: u16) -> PyResult<Option<u64>> {
        let w = super::width(length)?;
        self.make(|s| s.extract(handle(a)?, lo, w))
    }

    /// `hi` in the high bits, `lo` in the low bits.
    fn concat(&self, hi: u64, lo: u64) -> PyResult<Option<u64>> {
        self.make(|s| s.concat(handle(hi)?, handle(lo)?))
    }

    /// `cond ? then : els`, with a 1-bit condition.
    fn select(&self, cond: u64, then: u64, els: u64) -> PyResult<Option<u64>> {
        self.make(|s| s.select(handle(cond)?, handle(then)?, handle(els)?))
    }

    fn __repr__(&self) -> &'static str {
        if self.site.load(Ordering::SeqCst).is_null() {
            "<bitwright.Site (expired)>"
        } else {
            "<bitwright.Site>"
        }
    }
}

// ----- checking a rewrite ---------------------------------------------------------------------

/// Why a check failed. Expressions are in the text syntax.
#[pyclass(frozen, name = "RewriteFailure", module = "bitwright")]
#[derive(Debug)]
pub(super) struct RewriteFailureInfo {
    /// `"unparsable"`, `"never_applied"`, `"differs"`, `"width"`, `"not_smaller"`,
    /// `"nondeterministic"` or `"foreign_expr"`.
    #[pyo3(get)]
    kind: &'static str,
    /// The whole failure, as a sentence.
    #[pyo3(get)]
    message: String,
    /// The node (the input, for `"unparsable"`), if there is one.
    #[pyo3(get)]
    node: Option<String>,
    /// The rewrite's result (the first, for `"nondeterministic"`), if there is one.
    #[pyo3(get)]
    result: Option<String>,
    /// The second result, for `"nondeterministic"`.
    #[pyo3(get)]
    second: Option<String>,
    /// For `"differs"`: the symbols' values where the result and the node differ.
    #[pyo3(get)]
    assignment: Py<PyDict>,
}

#[pymethods]
impl RewriteFailureInfo {
    fn __repr__(&self) -> String {
        format!("<bitwright.RewriteFailure {}: {}>", self.kind, self.message)
    }
}

/// What `check_rewrite` covered, or why it failed: true when it passed.
#[pyclass(frozen, module = "bitwright")]
#[derive(Debug)]
pub(super) struct RewriteReport {
    /// Nodes where the rewrite returned a result other than the node.
    #[pyo3(get)]
    applications: u64,
    /// Points at which a result was compared with its node.
    #[pyo3(get)]
    points: u64,
    /// Applications compared at every assignment of their symbols.
    #[pyo3(get)]
    exhaustive: u64,
    /// Why the check failed, or None.
    #[pyo3(get)]
    failure: Option<Py<RewriteFailureInfo>>,
}

#[pymethods]
impl RewriteReport {
    fn __bool__(&self) -> bool {
        self.failure.is_none()
    }

    fn __repr__(&self) -> String {
        match &self.failure {
            None => format!(
                "<bitwright.RewriteReport passed: {} applications, {} points>",
                self.applications, self.points
            ),
            Some(f) => format!("<bitwright.RewriteReport failed: {}>", f.get().message),
        }
    }
}

fn failure_info(py: Python<'_>, f: &RewriteFailure) -> PyResult<RewriteFailureInfo> {
    let assignment = PyDict::new(py);
    let (kind, node, result, second) = match f {
        RewriteFailure::Unparsable { input } => ("unparsable", Some(input), None, None),
        RewriteFailure::NeverApplied => ("never_applied", None, None, None),
        RewriteFailure::Differs {
            node,
            result,
            assignment: a,
        } => {
            for (name, v) in a {
                assignment.set_item(name, to_int(py, v)?)?;
            }
            ("differs", Some(node), Some(result), None)
        }
        RewriteFailure::Width { node, result } => ("width", Some(node), Some(result), None),
        RewriteFailure::NotSmaller { node, result } => {
            ("not_smaller", Some(node), Some(result), None)
        }
        RewriteFailure::Nondeterministic {
            node,
            first,
            second,
        } => ("nondeterministic", Some(node), Some(first), Some(second)),
        RewriteFailure::ForeignExpr { node } => ("foreign_expr", Some(node), None, None),
        _ => ("other", None, None, None),
    };
    Ok(RewriteFailureInfo {
        kind,
        message: f.to_string(),
        node: node.cloned(),
        result: result.cloned(),
        second: second.cloned(),
        assignment: assignment.unbind(),
    })
}

/// Tests `rewrite` offline on `inputs` (expression text): at every node of every input, at
/// every width it parses at (`widths`, default 1 to 8, 16, 32 and 64) and on `variants`
/// variations with other constants, each result compared with its node (at every assignment
/// up to `max_exhaustive_bits` bits of symbols, at `samples` boundary-biased points
/// otherwise), and what the engine relies on (width, determinism, the termination order). A
/// report, true when the check passed. Testing, not proof: give inputs where the rewrite
/// applies and where it nearly does.
#[pyfunction]
#[pyo3(signature = (rewrite, inputs, *, widths = None, variants = None, max_exhaustive_bits = None, samples = None, seed = None))]
#[allow(clippy::too_many_arguments)]
pub(super) fn check_rewrite(
    py: Python<'_>,
    rewrite: PyRef<'_, PyRewrite>,
    inputs: Vec<String>,
    widths: Option<Vec<u16>>,
    variants: Option<u32>,
    max_exhaustive_bits: Option<u32>,
    samples: Option<u32>,
    seed: Option<u64>,
) -> PyResult<RewriteReport> {
    let mut cfg = RewriteCheckConfig::default();
    if let Some(w) = widths {
        cfg = cfg.with_widths(w);
    }
    if let Some(v) = variants {
        cfg = cfg.with_variants(v);
    }
    if let Some(b) = max_exhaustive_bits {
        cfg = cfg.with_max_exhaustive_bits(b);
    }
    if let Some(s) = samples {
        cfg = cfg.with_samples(s);
    }
    if let Some(s) = seed {
        cfg = cfg.with_seed(s);
    }
    let r = rewrite.r.clone();
    let texts: Vec<&str> = inputs.iter().map(String::as_str).collect();
    // The checker calls the rewrite, which takes the interpreter lock for each call.
    let out = py.detach(|| bitwright::check::rewrite(&*r, &texts, &cfg));
    match out {
        Ok(rep) => Ok(RewriteReport {
            applications: rep.applications,
            points: rep.points,
            exhaustive: rep.exhaustive,
            failure: None,
        }),
        Err(f) => Ok(RewriteReport {
            applications: 0,
            points: 0,
            exhaustive: 0,
            failure: Some(Py::new(py, failure_info(py, &f)?)?),
        }),
    }
}

// ----- counters -------------------------------------------------------------------------------

/// Counters of one pass, or of the host rewrites together.
#[pyclass(frozen, skip_from_py_object, module = "bitwright")]
#[derive(Debug, Clone, Copy)]
pub(super) struct PassStats {
    /// Nodes considered.
    #[pyo3(get)]
    calls: u64,
    /// Results equal to the node.
    #[pyo3(get)]
    noop: u64,
    /// Nodes replaced.
    #[pyo3(get)]
    changed: u64,
    /// Results that would not make the DAG smaller (host rewrites: not smaller in the
    /// termination order).
    #[pyo3(get)]
    rejected_cost: u64,
    /// Results rejected by a postcondition or vetoed.
    #[pyo3(get)]
    rejected: u64,
    /// Regions over the size cap, treated as atoms.
    #[pyo3(get)]
    atomized: u64,
}

impl From<&PassCounts> for PassStats {
    fn from(c: &PassCounts) -> Self {
        PassStats {
            calls: c.calls,
            noop: c.noop,
            changed: c.changed,
            rejected_cost: c.rejected_cost,
            rejected: c.rejected,
            atomized: c.atomized,
        }
    }
}

#[pymethods]
impl PassStats {
    fn __repr__(&self) -> String {
        format!(
            "<bitwright.PassStats calls {}, changed {}, noop {}, rejected {} (cost {})>",
            self.calls, self.changed, self.noop, self.rejected, self.rejected_cost
        )
    }
}

/// Counters of one simplification call (`Engine.run(..., stats=True)`). Always collected;
/// no-op work is counted like useful work.
#[pyclass(frozen, name = "Stats", module = "bitwright")]
#[derive(Debug)]
pub(super) struct RunStats {
    #[pyo3(get)]
    node_visits: u64,
    /// Nodes answered from the context's memo.
    #[pyo3(get)]
    memo_hits: u64,
    /// Rules tried after the dispatch prefilter.
    #[pyo3(get)]
    candidates: u64,
    #[pyo3(get)]
    match_steps: u64,
    #[pyo3(get)]
    no_match: u64,
    #[pyo3(get)]
    guard_false: u64,
    /// Candidates and pass steps declined for lack of work or facts.
    #[pyo3(get)]
    degraded: u64,
    #[pyo3(get)]
    no_change: u64,
    /// Rewrites committed.
    #[pyo3(get)]
    rewrites: u64,
    /// Rewrites refused (`Engine(refuse=...)`).
    #[pyo3(get)]
    hook_vetoes: u64,
    /// Rewrites rejected by a postcondition.
    #[pyo3(get)]
    rejected: u64,
    #[pyo3(get)]
    cycles_cut: u64,
    /// Rules and host rewrites quarantined for the rest of the call.
    #[pyo3(get)]
    quarantined: u64,
    #[pyo3(get)]
    new_nodes: u64,
    #[pyo3(get)]
    fact_work: u64,
    #[pyo3(get)]
    pass_work: u64,
    #[pyo3(get)]
    rounds: u32,
    /// Per normal-form pass, by name.
    #[pyo3(get)]
    passes: BTreeMap<&'static str, PassStats>,
    /// The host rewrites (`Engine(rewrites=...)`), together.
    #[pyo3(get)]
    host: PassStats,
}

impl From<&Stats> for RunStats {
    fn from(s: &Stats) -> Self {
        RunStats {
            node_visits: s.node_visits,
            memo_hits: s.memo_hits,
            candidates: s.candidates,
            match_steps: s.match_steps,
            no_match: s.no_match,
            guard_false: s.guard_false,
            degraded: s.degraded,
            no_change: s.no_change,
            rewrites: s.rewrites,
            hook_vetoes: s.hook_vetoes,
            rejected: s.rejected,
            cycles_cut: s.cycles_cut,
            quarantined: s.quarantined,
            new_nodes: s.new_nodes,
            fact_work: s.fact_work,
            pass_work: s.pass_work,
            rounds: s.rounds,
            passes: s.passes.iter().map(|(k, v)| (*k, v.into())).collect(),
            host: (&s.host).into(),
        }
    }
}

#[pymethods]
impl RunStats {
    fn __repr__(&self) -> String {
        format!(
            "<bitwright.Stats {} visits, {} rewrites, {} rounds>",
            self.node_visits, self.rewrites, self.rounds
        )
    }
}

// ----- templates ------------------------------------------------------------------------------

/// An instruction's semantics as an expression over named parameters, read at run time:
/// `Template("select(a <s b, a, b)", ["a", "b"])`. The parameters take the widths of the
/// operands it is instantiated with, and a literal whose width the text does not fix takes the
/// widest operand's. Compiled once per combination of widths, then instantiated by copying.
/// Shared freely between threads.
#[pyclass(frozen, name = "Template", module = "bitwright")]
#[derive(Debug)]
pub(super) struct PyTemplate {
    t: Template,
    params: Vec<String>,
}

#[pymethods]
impl PyTemplate {
    #[new]
    fn new(text: &str, params: Vec<String>) -> PyResult<Self> {
        let p: Vec<&str> = params.iter().map(String::as_str).collect();
        Ok(PyTemplate {
            t: Template::new(text, &p).or_raise()?,
            params,
        })
    }

    /// The parameter names, in order.
    #[getter]
    fn params(&self) -> Vec<String> {
        self.params.clone()
    }

    /// Reads the text with parameters of these widths: a syntax or width error now, not at the
    /// first instantiation.
    fn check(&self, py: Python<'_>, widths: Vec<u16>) -> PyResult<()> {
        let widths = widths
            .into_iter()
            .map(width)
            .collect::<PyResult<Vec<Width>>>()?;
        py.detach(|| self.t.check(&widths)).or_raise()
    }

    /// The template's expression with its parameters bound to `args` (expressions of one
    /// context; `context` gives it for a template without parameters).
    #[pyo3(signature = (args, context = None))]
    fn instantiate(
        &self,
        py: Python<'_>,
        args: Vec<PyRef<'_, PyExpr>>,
        context: Option<Py<PyContext>>,
    ) -> PyResult<PyExpr> {
        let cx = match (args.first(), context) {
            (Some(a), _) => a.cx.clone_ref(py),
            (None, Some(c)) => c,
            (None, None) => {
                return Err(PyValueError::new_err(
                    "a template without parameters needs a context",
                ));
            }
        };
        if args.iter().any(|a| !a.cx.is(&cx)) {
            return Err(PyValueError::new_err("expressions of two contexts"));
        }
        let handles: Vec<Expr> = args.iter().map(|a| a.e).collect();
        let cx = cx.bind(py);
        let mut c = cx.get().lock(py)?;
        let e = self.t.instantiate(&mut c, &handles).or_raise()?;
        wrap(cx, &c, e)
    }

    fn __repr__(&self) -> String {
        format!("<bitwright.Template ({})>", self.params.join(", "))
    }
}

// ----- lowering and raising -------------------------------------------------------------------

/// One function (or block) of the host's IR translated into expressions of a context: the
/// expression of every host value (a non-negative int of the host's choosing: an SSA number,
/// say), and a symbol for every value defined outside it.
#[pyclass(frozen, name = "Lowering", module = "bitwright")]
#[derive(Debug)]
pub(super) struct PyLowering {
    cx: Py<PyContext>,
    lw: Mutex<Option<Lowered<u64>>>,
}

impl PyLowering {
    /// Runs `f` on the lowering attached to its locked context (the context first, then the
    /// lowering: every lock of the bindings is taken in that order).
    fn with<T>(
        &self,
        py: Python<'_>,
        f: impl FnOnce(&Bound<'_, PyContext>, &mut Lowering<'_, u64>) -> PyResult<T>,
    ) -> PyResult<T> {
        let cx = self.cx.bind(py);
        let mut c = cx.get().lock(py)?;
        let mut slot = super::lock(py, &self.lw)?;
        let mut lw = slot.take().unwrap_or_default().attach(&mut c);
        let r = f(cx, &mut lw);
        *slot = Some(lw.detach());
        r
    }

    fn own(&self, e: &PyExpr) -> PyResult<Expr> {
        if !e.cx.is(&self.cx) {
            return Err(PyValueError::new_err(
                "an expression of another context than the lowering's",
            ));
        }
        Ok(e.e)
    }

    fn read<T>(&self, py: Python<'_>, f: impl FnOnce(Option<&Lowered<u64>>) -> T) -> PyResult<T> {
        Ok(f(super::lock(py, &self.lw)?.as_ref()))
    }
}

/// Known bits from a `(zero, one)` pair of masks of `w` bits.
fn known_bits(known: &Bound<'_, PyAny>, w: Width) -> PyResult<KnownBits> {
    let (zero, one): (Bound<'_, PyAny>, Bound<'_, PyAny>) = known.extract()?;
    let (zero, one) = (to_bitvec(&zero, w)?, to_bitvec(&one, w)?);
    KnownBits::new(zero, one).ok_or_else(|| {
        PyValueError::new_err("a bit is declared both 0 and 1 (`zero & one` is not 0)")
    })
}

pub(super) fn declared_pair(
    py: Python<'_>,
    k: Option<KnownBits>,
) -> PyResult<Option<(Py<PyAny>, Py<PyAny>)>> {
    k.map(|k| {
        Ok((
            to_int(py, &k.known_zero())?.unbind(),
            to_int(py, &k.known_one())?.unbind(),
        ))
    })
    .transpose()
}

/// Declares `known` (a `(zero, one)` pair of masks) for symbol `sym` of `cx`.
pub(super) fn declare_known(
    py: Python<'_>,
    cx: &PyContext,
    sym: &PyExpr,
    known: &Bound<'_, PyAny>,
) -> PyResult<()> {
    let k = known_bits(known, width(sym.width)?)?;
    let mut c = cx.lock(py)?;
    if c.symbol_id(sym.e).or_raise()?.is_none() {
        return Err(PyTypeError::new_err(
            "known bits are declared for symbols only",
        ));
    }
    c.declare_known(sym.e, k).or_raise()
}

#[pymethods]
impl PyLowering {
    #[new]
    fn new(context: Py<PyContext>) -> Self {
        PyLowering {
            cx: context,
            lw: Mutex::new(None),
        }
    }

    /// The context the lowering builds in.
    #[getter]
    fn context(&self, py: Python<'_>) -> Py<PyContext> {
        self.cx.clone_ref(py)
    }

    /// The expression of host value `v` of `width` bits: its definition, or for a value not
    /// defined here, a fresh symbol that stands for it (`input`).
    fn value(&self, py: Python<'_>, v: u64, width: u16) -> PyResult<PyExpr> {
        let w = super::width(width)?;
        self.with(py, |cx, lw| {
            let e = lw.value(v, w).or_raise()?;
            wrap(cx, lw.context(), e)
        })
    }

    /// A value defined outside (a parameter, a load, a call result): a symbol of `width` bits
    /// that stands for it, named `name` (default: a fresh symbol), with `known`, a `(zero, one)`
    /// pair of masks of the bits the host knows are 0 and 1 (`Context.declare_known`). Its
    /// expression if it has one already.
    #[pyo3(signature = (v, width, *, name = None, known = None))]
    fn input(
        &self,
        py: Python<'_>,
        v: u64,
        width: u16,
        name: Option<String>,
        known: Option<&Bound<'_, PyAny>>,
    ) -> PyResult<PyExpr> {
        let w = super::width(width)?;
        let known = known.map(|k| known_bits(k, w)).transpose()?;
        self.with(py, |cx, lw| {
            let e = match name {
                Some(n) => lw.input_named(v, n.as_str(), w, known),
                None => lw.input(v, w, known),
            }
            .or_raise()?;
            wrap(cx, lw.context(), e)
        })
    }

    /// Records that host value `v` is `e`.
    fn define(&self, py: Python<'_>, v: u64, e: PyRef<'_, PyExpr>) -> PyResult<()> {
        let e = self.own(&e)?;
        self.with(py, |_, lw| lw.define(v, e).or_raise())
    }

    /// The expression of host value `v`, if it has one.
    fn get(&self, py: Python<'_>, v: u64) -> PyResult<Option<PyExpr>> {
        let Some(e) = self.read(py, |lw| lw.and_then(|lw| lw.get(v)))? else {
            return Ok(None);
        };
        let cx = self.cx.bind(py);
        let c = cx.get().lock(py)?;
        wrap(cx, &c, e).map(Some)
    }

    /// A host value that computes `e` already (the first defined), if one does.
    fn owner(&self, py: Python<'_>, e: PyRef<'_, PyExpr>) -> PyResult<Option<u64>> {
        let e = self.own(&e)?;
        self.read(py, |lw| lw.and_then(|lw| lw.owner(e)))
    }

    /// The values defined outside that were read, in order, with their symbols.
    #[getter]
    fn inputs(&self, py: Python<'_>) -> PyResult<Vec<(u64, PyExpr)>> {
        let ins: Vec<(u64, Expr)> = self.read(py, |lw| {
            lw.map(|lw| lw.inputs().to_vec()).unwrap_or_default()
        })?;
        let cx = self.cx.bind(py);
        let c = cx.get().lock(py)?;
        ins.into_iter()
            .map(|(v, e)| Ok((v, wrap(cx, &c, e)?)))
            .collect()
    }

    /// Turns `e` into host instructions: the value computing it. A node some host value computes
    /// is that value; every other node is emitted by `emit(node, operands)`, operands first,
    /// with `node` an `Expr` and `operands` the host values of its children in order, and
    /// then owned by the value `emit` returns (so later raises reuse it). The context is free
    /// while `emit` runs. (`raise` is a keyword: hence the underscore.)
    fn raise_(
        &self,
        py: Python<'_>,
        e: PyRef<'_, PyExpr>,
        emit: &Bound<'_, PyAny>,
    ) -> PyResult<u64> {
        let e = self.own(&e)?;
        let todo = self.with(py, |_, lw| {
            let nodes = lw.unraised(e).or_raise()?;
            nodes
                .into_iter()
                .map(|n| {
                    let kids: Vec<Expr> = lw.context().children(n).or_raise()?.collect();
                    Ok((n, kids))
                })
                .collect::<PyResult<Vec<_>>>()
        })?;
        let cx = self.cx.bind(py);
        for (n, kids) in todo {
            let owners: Vec<u64> = self.read(py, |lw| {
                let lw = lw.expect("a lowering with pending nodes has values");
                kids.iter()
                    .map(|&k| lw.owner(k).expect("operands are emitted first"))
                    .collect()
            })?;
            let node = {
                let c = cx.get().lock(py)?;
                wrap(cx, &c, n)?
            };
            let v: u64 = emit.call1((node, owners))?.extract()?;
            self.with(py, |_, lw| lw.emitted(n, v).or_raise())?;
        }
        self.read(py, |lw| lw.and_then(|lw| lw.owner(e)))?
            .ok_or_else(|| BitwrightError::new_err("the raised expression has no host value"))
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        let inputs = self.read(py, |lw| lw.map_or(0, |lw| lw.inputs().len()))?;
        Ok(format!("<bitwright.Lowering {inputs} inputs>"))
    }
}
