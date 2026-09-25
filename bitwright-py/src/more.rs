//! Proofs, synthesis, equality saturation, memory, lifted code and compiler transformations.

use std::sync::Mutex;

use bitwright::memory::{Endian, Memory, Version};
use bitwright::prove::{self, Outcome as ProofOutcome};
use bitwright::{Context, Expr, SymbolKey, Width};
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyDict;

use super::{OrRaise, PyContext, PyExpr, key_name, lock, to_int, width, wrap};

// ----- proofs, synthesis, saturation --------------------------------------------------------

/// Whether `a` and `b` are equal for every value of their symbols, by bitwright's own
/// bit-blaster and SAT solver: True (proved), a dict of symbol values where they differ
/// (checked by evaluation), or None (not decided within `conflicts`).
#[pyfunction]
#[pyo3(signature = (a, b, *, conflicts = 1_000_000))]
pub(super) fn equivalent<'py>(
    py: Python<'py>,
    a: PyRef<'_, PyExpr>,
    b: PyRef<'_, PyExpr>,
    conflicts: u64,
) -> PyResult<Bound<'py, PyAny>> {
    if !a.cx.is(&b.cx) {
        return Err(PyValueError::new_err("expressions of two contexts"));
    }
    let cx = a.cx.bind(py).get();
    let (ea, eb) = (a.e, b.e);
    let cfg = prove::Config::default().with_max_conflicts(conflicts);
    let out = py
        .detach(|| {
            let mut c = cx.cx.lock().unwrap_or_else(|p| p.into_inner());
            prove::equal(&mut c, ea, eb, &cfg)
        })
        .or_raise()?;
    match out {
        ProofOutcome::Proved(_) => Ok(true.into_pyobject(py)?.to_owned().into_any()),
        ProofOutcome::Refuted(model) => {
            let d = PyDict::new(py);
            for (k, v) in &model {
                let key: Bound<'py, PyAny> = match k {
                    SymbolKey::Str(s) => s.as_ref().into_pyobject(py)?.into_any(),
                    other => key_name(other).into_pyobject(py)?.into_any(),
                };
                d.set_item(key, to_int(py, v)?)?;
            }
            Ok(d.into_any())
        }
        _ => Ok(py.None().into_bound(py)),
    }
}

/// The smallest expression equal to `e` that synthesis finds over its variables and constants
/// (proved equal), or None.
#[pyfunction]
#[pyo3(signature = (e, *, max_size = 7))]
pub(super) fn synthesize(
    py: Python<'_>,
    e: PyRef<'_, PyExpr>,
    max_size: u8,
) -> PyResult<Option<PyExpr>> {
    let cxb = e.cx.bind(py);
    let cx = cxb.get();
    let x = e.e;
    let cfg = bitwright::synth::Config::default().with_max_size(max_size);
    let out = py
        .detach(|| {
            let mut c = cx.cx.lock().unwrap_or_else(|p| p.into_inner());
            bitwright::synth::synthesize(&mut c, x, &cfg)
        })
        .or_raise()?;
    let c = cx.lock(py);
    out.map(|s| wrap(cxb, &c, s)).transpose()
}

/// The equality-saturation search's candidate for `e` over the built-in equations (every
/// group of `eqsat.bwr`, or the ones named), or None when it finds nothing smaller.
#[pyfunction]
#[pyo3(signature = (e, *, groups = None))]
pub(super) fn saturate(
    py: Python<'_>,
    e: PyRef<'_, PyExpr>,
    groups: Option<Vec<String>>,
) -> PyResult<Option<PyExpr>> {
    use bitwright::eqsat::{SaturateConfig, Saturator, SearchRun};
    let names: Vec<String> = groups.unwrap_or_else(|| {
        [
            "eqsat.assoc",
            "eqsat.distrib",
            "eqsat.distrib_and",
            "eqsat.distrib_or",
            "eqsat.negation",
            "eqsat.cancel",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect()
    });
    let refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let (sat, _) = Saturator::builtin_groups(&refs, SaturateConfig::default());
    let cxb = e.cx.bind(py);
    let cx = cxb.get();
    let x = e.e;
    let out = py
        .detach(|| {
            let mut c = cx.cx.lock().unwrap_or_else(|p| p.into_inner());
            sat.search(&mut c, &[x], SearchRun::default())
        })
        .or_raise()?;
    let c = cx.lock(py);
    out.roots[0].candidate.map(|s| wrap(cxb, &c, s)).transpose()
}

// ----- memory -------------------------------------------------------------------------------

/// A memory of a context: loads and stores as expressions (see the book's Memory chapter).
/// `store` moves it to a new version; `load` reads the current one.
#[pyclass(frozen, name = "Memory", module = "bitwright")]
#[derive(Debug)]
pub(super) struct PyMemory {
    cx: Py<PyContext>,
    m: Mutex<(Memory, Version)>,
}

#[pymethods]
impl PyMemory {
    /// A memory of `ctx` from `addr_width`-bit addresses to `cell_width`-bit cells, all unknown
    /// (the symbols `name.0`, `name.1`, …), or zero with `zeroed`.
    #[new]
    #[pyo3(signature = (ctx, name = "mem", addr_width = 64, cell_width = 8, *, big_endian = false, zeroed = false))]
    fn new(
        ctx: Py<PyContext>,
        name: &str,
        addr_width: u16,
        cell_width: u16,
        big_endian: bool,
        zeroed: bool,
    ) -> PyResult<Self> {
        let endian = if big_endian {
            Endian::Big
        } else {
            Endian::Little
        };
        let mut m = Memory::new(name, width(addr_width)?, width(cell_width)?, endian);
        if zeroed {
            m = m.zeroed();
        }
        let v = m.initial();
        Ok(PyMemory {
            cx: ctx,
            m: Mutex::new((m, v)),
        })
    }

    /// Known contents: `data` (bytes, for 8-bit cells) from address `start` on. Before any
    /// load or store.
    fn set_bytes(&self, py: Python<'_>, start: u128, data: Vec<u8>) -> PyResult<()> {
        let mut g = lock(py, &self.m);
        let (m, v) = &mut *g;
        let taken = std::mem::replace(m, Memory::new("tmp", Width::W8, Width::W8, Endian::Little));
        *m = taken.with_bytes(start, &data).or_raise()?;
        *v = m.initial();
        Ok(())
    }

    /// Stores `value` (a whole number of cells) at `addr`.
    fn store(
        &self,
        py: Python<'_>,
        addr: PyRef<'_, PyExpr>,
        value: PyRef<'_, PyExpr>,
    ) -> PyResult<()> {
        let (a, x) = (addr.e, value.e);
        let cx = self.cx.bind(py).get();
        let mut c = cx.lock(py);
        let mut g = lock(py, &self.m);
        let (m, v) = &mut *g;
        *v = m.store(&mut c, *v, a, x).or_raise()?;
        Ok(())
    }

    /// Loads `cells` cells at `addr`, as one value.
    #[pyo3(signature = (addr, cells = 1))]
    fn load(&self, py: Python<'_>, addr: PyRef<'_, PyExpr>, cells: u16) -> PyResult<PyExpr> {
        let a = addr.e;
        let cxb = self.cx.bind(py);
        let e = {
            let mut c = cxb.get().lock(py);
            let mut g = lock(py, &self.m);
            let (m, v) = &mut *g;
            m.load(&mut c, *v, a, cells).or_raise()?
        };
        let c = cxb.get().lock(py);
        wrap(cxb, &c, e)
    }

    /// The reads of unknown cells so far: (address, symbol) pairs.
    fn reads(&self, py: Python<'_>) -> PyResult<Vec<(PyExpr, PyExpr)>> {
        let list: Vec<(Expr, Expr)> = lock(py, &self.m).0.reads().to_vec();
        let cxb = self.cx.bind(py);
        let c = cxb.get().lock(py);
        list.into_iter()
            .map(|(a, s)| Ok((wrap(cxb, &c, a)?, wrap(cxb, &c, s)?)))
            .collect()
    }
}

// ----- lifted code --------------------------------------------------------------------------

/// A block of lifted code, read into expressions.
#[pyclass(frozen, name = "LiftedBlock", module = "bitwright")]
#[derive(Debug)]
pub(super) struct LiftedBlock {
    /// Registers read before written: name → the symbol of the value it had.
    #[pyo3(get)]
    inputs: Vec<(String, PyExpr)>,
    /// Registers written: name → final value, in the order first written.
    #[pyo3(get)]
    outputs: Vec<(String, PyExpr)>,
    /// Stores to memory: (address, value).
    #[pyo3(get)]
    stores: Vec<(PyExpr, PyExpr)>,
    /// Conditional exits: (condition, target).
    #[pyo3(get)]
    exits: Vec<(PyExpr, PyExpr)>,
    /// Where the block continues, when it says.
    #[pyo3(get)]
    next: Option<PyExpr>,
}

#[pymethods]
impl LiftedBlock {
    /// The final value of a register (any case), or None.
    fn register(&self, py: Python<'_>, name: &str) -> Option<PyExpr> {
        let find = |list: &[(String, PyExpr)]| {
            list.iter()
                .find(|(n, _)| n.eq_ignore_ascii_case(name))
                .map(|(_, e)| e.clone_ref(py))
        };
        find(&self.outputs).or_else(|| find(&self.inputs))
    }
}

impl PyExpr {
    fn clone_ref(&self, py: Python<'_>) -> PyExpr {
        PyExpr {
            cx: self.cx.clone_ref(py),
            e: self.e,
            width: self.width,
        }
    }
}

fn lifted(
    py: Python<'_>,
    ctx: &Bound<'_, PyContext>,
    read: impl FnOnce(&mut Context) -> Result<bitwright::lift::Block, bitwright::Error> + Send,
) -> PyResult<LiftedBlock> {
    let cx = ctx.get();
    let b = py
        .detach(|| {
            let mut c = cx.cx.lock().unwrap_or_else(|p| p.into_inner());
            read(&mut c)
        })
        .or_raise()?;
    let c = cx.lock(py);
    let w = |e: Expr| wrap(ctx, &c, e);
    Ok(LiftedBlock {
        inputs: b
            .inputs
            .iter()
            .map(|(n, e)| Ok((n.clone(), w(*e)?)))
            .collect::<PyResult<_>>()?,
        outputs: b
            .outputs
            .iter()
            .map(|(n, e)| Ok((n.clone(), w(*e)?)))
            .collect::<PyResult<_>>()?,
        stores: b
            .stores
            .iter()
            .map(|(a, v)| Ok((w(*a)?, w(*v)?)))
            .collect::<PyResult<_>>()?,
        exits: b
            .exits
            .iter()
            .map(|(a, v)| Ok((w(*a)?, w(*v)?)))
            .collect::<PyResult<_>>()?,
        next: b.next.map(w).transpose()?,
    })
}

/// Ghidra p-code, one operation per line (see the book's chapter on lifted code).
#[pyfunction]
pub(super) fn lift_pcode(
    py: Python<'_>,
    ctx: &Bound<'_, PyContext>,
    text: &str,
) -> PyResult<LiftedBlock> {
    let t = text.to_string();
    lifted(py, ctx, move |c| bitwright::lift::pcode(c, &t))
}

/// VEX IR as pyvex prints an IRSB.
#[pyfunction]
pub(super) fn lift_vex(
    py: Python<'_>,
    ctx: &Bound<'_, PyContext>,
    text: &str,
) -> PyResult<LiftedBlock> {
    let t = text.to_string();
    lifted(py, ctx, move |c| bitwright::lift::vex(c, &t))
}

/// A function of an LLVM IR module (the first, without `function`): its return value is the
/// output `ret`.
#[pyfunction]
#[pyo3(signature = (ctx, text, function = None))]
pub(super) fn lift_llvm(
    py: Python<'_>,
    ctx: &Bound<'_, PyContext>,
    text: &str,
    function: Option<String>,
) -> PyResult<LiftedBlock> {
    let t = text.to_string();
    lifted(py, ctx, move |c| {
        bitwright::lift::llvm(c, &t, function.as_deref())
    })
}

// ----- compiler transformations -------------------------------------------------------------

/// The verdict on one transformation or function pair.
#[pyclass(frozen, name = "TransformReport", module = "bitwright")]
#[derive(Debug)]
pub(super) struct TransformReport {
    /// Its name.
    #[pyo3(get)]
    name: String,
    /// `"valid"`, `"invalid"`, `"unknown"` or `"unsupported"`.
    #[pyo3(get)]
    verdict: &'static str,
    /// The report as the command line prints it (a counterexample for an invalid one).
    #[pyo3(get)]
    text: String,
}

#[pymethods]
impl TransformReport {
    fn __repr__(&self) -> String {
        format!("<bitwright.TransformReport {} {}>", self.verdict, self.name)
    }
}

fn report(r: &bitwright::transform::Report) -> TransformReport {
    use bitwright::transform::Verdict;
    TransformReport {
        name: r.name.clone(),
        verdict: match r.verdict() {
            Verdict::Valid => "valid",
            Verdict::Invalid(_) => "invalid",
            Verdict::Unknown(_) => "unknown",
            _ => "unsupported",
        },
        text: r.to_string(),
    }
}

fn transform_config(
    widths: Option<Vec<u16>>,
    conflicts: Option<u64>,
) -> bitwright::transform::Config {
    let mut cfg = bitwright::transform::Config::default();
    if let Some(w) = widths {
        cfg = cfg.with_widths(w);
    }
    if let Some(c) = conflicts {
        cfg = cfg.with_conflicts(c);
    }
    cfg
}

fn syntax(e: bitwright::transform::SyntaxError) -> PyErr {
    super::ParseError::new_err(e.to_string())
}

/// Verifies transformations in the syntax of the Alive paper (`Pre:`, source, `=>`, target):
/// a report each.
#[pyfunction]
#[pyo3(signature = (text, *, widths = None, conflicts = None))]
pub(super) fn verify_transforms(
    py: Python<'_>,
    text: &str,
    widths: Option<Vec<u16>>,
    conflicts: Option<u64>,
) -> PyResult<Vec<TransformReport>> {
    let ts = bitwright::transform::parse_transforms(text).map_err(syntax)?;
    let cfg = transform_config(widths, conflicts);
    Ok(py.detach(|| {
        ts.iter()
            .map(|t| report(&bitwright::transform::verify(t, &cfg)))
            .collect()
    }))
}

/// Translation validation: each function of `tgt` against the one of the same name in `src`
/// (or `@tgt` against `@src` of one module).
#[pyfunction]
#[pyo3(signature = (src, tgt = None, *, conflicts = None))]
pub(super) fn validate_functions(
    py: Python<'_>,
    src: &str,
    tgt: Option<&str>,
    conflicts: Option<u64>,
) -> PyResult<Vec<TransformReport>> {
    let pairs = bitwright::transform::pairs(src, tgt).map_err(syntax)?;
    let cfg = transform_config(None, conflicts);
    Ok(py.detach(|| {
        pairs
            .iter()
            .map(|t| report(&bitwright::transform::verify(t, &cfg)))
            .collect()
    }))
}

/// A precondition inferred for a transformation.
#[pyclass(frozen, name = "InferredPrecondition", module = "bitwright")]
#[derive(Debug)]
pub(super) struct InferredPrecondition {
    /// The transformation's name.
    #[pyo3(get)]
    name: String,
    /// The precondition, or None (none needed, none found, or no symbolic constants).
    #[pyo3(get)]
    pre: Option<String>,
    /// Whether it admits every valid example seen.
    #[pyo3(get)]
    weakest: bool,
    /// The verdict of the transformation with it (None when there was nothing to verify).
    #[pyo3(get)]
    verdict: Option<&'static str>,
}

/// Infers the precondition of each transformation over its symbolic constants.
#[pyfunction]
pub(super) fn infer_preconditions(
    py: Python<'_>,
    text: &str,
) -> PyResult<Vec<InferredPrecondition>> {
    let ts = bitwright::transform::parse_transforms(text).map_err(syntax)?;
    let cfg = bitwright::transform::Config::default();
    py.detach(|| {
        ts.iter()
            .map(|t| {
                let i = bitwright::transform::infer(t, &cfg).map_err(PyValueError::new_err)?;
                Ok(InferredPrecondition {
                    name: t.name.clone(),
                    pre: i.pre,
                    weakest: i.weakest,
                    verdict: i.report.map(|r| report(&r).verdict),
                })
            })
            .collect()
    })
}
