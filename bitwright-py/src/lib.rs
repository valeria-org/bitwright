//! Python bindings for bitwright: the `bitwright._bitwright` extension module, re-exported by the
//! `bitwright` package (`python/bitwright/__init__.py`, typed in `_bitwright.pyi`).
//!
//! A `Context` owns its arena behind a mutex, so it may be shared between Python threads; an
//! `Expr` holds its context and a handle. Every operation locks one context (and then, if
//! given, one assumption set: always in that order). Simplification runs with the interpreter
//! released and the context locked.
//!
//! No Python code runs while a lock is held: arguments are converted before locking and results
//! after unlocking (Python code, such as an `__index__` or a finalizer run by an allocation,
//! could use the same context again and deadlock). A thread waits for a busy lock with the
//! interpreter released, so a long simplification in one thread does not stall the others.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, MutexGuard, OnceLock, TryLockError};

use bitwright::check::{CheckConfig, Verdict, check_program};
use bitwright::engine::{Budget, Each, End, Engine, Run, Strategy};
use bitwright::fp::{FpCmpOp, FpFormat, FpOp, FpTest, RoundingMode};
use bitwright::mba::{MbaConfig, MbaTrust, NormalFormSolver};
use bitwright::rules::{Ledger, RuleProgram};
use bitwright::{
    Assumptions, BinOp, BitVec, Bounded, CmpOpExt, Context, ContextConfig, Error, Expr,
    ParseOptions, PrintOptions, Query, Reliance, SymbolKey, Truth, UnOp, View, Width,
};
use pyo3::create_exception;
use pyo3::exceptions::{PyException, PyTypeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict, PyInt, PyString, PyTuple};

mod more;

create_exception!(
    bitwright,
    BitwrightError,
    PyException,
    "An error reported by bitwright."
);
create_exception!(
    bitwright,
    WidthError,
    BitwrightError,
    "A width rule was violated: operands of different widths, a bad cast, a symbol used at two widths."
);
create_exception!(
    bitwright,
    ParseError,
    BitwrightError,
    "A syntax or typing error in expression text or an SMT-LIB script."
);
create_exception!(
    bitwright,
    RuleError,
    BitwrightError,
    "A rule file that does not compile or check, or an engine that does not link."
);

fn err(e: Error) -> PyErr {
    let msg = e.to_string();
    match e {
        Error::Width(_) | Error::SymbolWidthConflict { .. } | Error::EnvWidth { .. } => {
            WidthError::new_err(msg)
        }
        Error::Value(_) => PyValueError::new_err(msg),
        Error::Syntax(_) => ParseError::new_err(msg),
        _ => BitwrightError::new_err(msg),
    }
}

trait OrRaise<T> {
    fn or_raise(self) -> PyResult<T>;
}

impl<T, E: Into<Error>> OrRaise<T> for Result<T, E> {
    fn or_raise(self) -> PyResult<T> {
        self.map_err(|e| err(e.into()))
    }
}

fn width(bits: u16) -> PyResult<Width> {
    Width::new(bits).map_err(|e| WidthError::new_err(e.to_string()))
}

// ----- integers ------------------------------------------------------------------------------

/// A Python int as a `w`-bit value: `0 <= v < 2^w`, or `-2^(w-1) <= v < 0` in two's complement.
fn to_bitvec(v: &Bound<'_, PyAny>, w: Width) -> PyResult<BitVec> {
    let does_not_fit = || {
        PyValueError::new_err(format!(
            "{} does not fit in {} bits",
            v.repr().map_or_else(|_| "value".into(), |r| r.to_string()),
            w.bits()
        ))
    };
    if !v.is_instance_of::<PyInt>() {
        return Err(PyTypeError::new_err(format!(
            "expected an int, got {}",
            v.get_type().name()?
        )));
    }
    if let Ok(i) = v.extract::<i128>() {
        let r = if i >= 0 {
            BitVec::from_u128(w, i as u128)
        } else {
            BitVec::from_i128(w, i)
        };
        return r.map_err(|_| does_not_fit());
    }
    if let Ok(u) = v.extract::<u128>() {
        return BitVec::from_u128(w, u).map_err(|_| does_not_fit());
    }
    // Wider than 128 bits: through the bytes of v (or of v + 2^w when negative).
    let py = v.py();
    let bits = u32::from(w.bits());
    let negative = v.lt(0)?;
    let v = if negative {
        v.add(PyInt::new(py, 1).lshift(bits)?)?
    } else {
        v.clone()
    };
    let bytes: Vec<u8> = v
        .call_method1("to_bytes", ((bits as usize).div_ceil(8), "little"))
        .map_err(|_| does_not_fit())?
        .extract()?;
    let limbs: Vec<u64> = bytes
        .chunks(8)
        .map(|c| {
            let mut b = [0; 8];
            b[..c.len()].copy_from_slice(c);
            u64::from_le_bytes(b)
        })
        .collect();
    let r = BitVec::from_limbs(w, &limbs).map_err(|_| does_not_fit())?;
    if negative && !r.msb() {
        return Err(does_not_fit());
    }
    Ok(r)
}

/// A value as a Python int, unsigned.
fn to_int<'py>(py: Python<'py>, v: &BitVec) -> PyResult<Bound<'py, PyAny>> {
    if let Some(u) = v.to_u128() {
        return Ok(u.into_pyobject(py)?.into_any());
    }
    let bytes: Vec<u8> = v.limbs().iter().flat_map(|l| l.to_le_bytes()).collect();
    py.get_type::<PyInt>()
        .call_method1("from_bytes", (PyBytes::new(py, &bytes), "little"))
}

/// A value as a Python int, signed (two's complement).
fn to_signed_int<'py>(py: Python<'py>, v: &BitVec) -> PyResult<Bound<'py, PyAny>> {
    if let Some(i) = v.to_i128() {
        return Ok(i.into_pyobject(py)?.into_any());
    }
    let u = to_int(py, v)?;
    if v.msb() {
        u.sub(PyInt::new(py, 1).lshift(u32::from(v.width().bits()))?)
    } else {
        Ok(u)
    }
}

/// The constraints a result relies on: their numbers, with 63 standing for every constraint
/// from 63 on.
fn reliance<'py>(py: Python<'py>, r: Reliance) -> PyResult<Bound<'py, PyTuple>> {
    let (ids, rest) = r.indices();
    let mut v: Vec<u32> = ids.collect();
    if rest {
        v.push(63);
    }
    PyTuple::new(py, v)
}

fn truth(t: Truth) -> Option<bool> {
    match t {
        Truth::True => Some(true),
        Truth::False => Some(false),
        Truth::Unknown => None,
    }
}

// ----- floating point ------------------------------------------------------------------------

/// A binary floating-point format: `eb` exponent bits and `sb` significand bits, the hidden bit
/// included, so an encoding is `eb + sb` bits wide. `2 <= eb <= 31`, `sb >= 2`, `eb + sb <= 512`.
#[pyclass(
    frozen,
    eq,
    hash,
    from_py_object,
    name = "FpFormat",
    module = "bitwright"
)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PyFpFormat {
    f: FpFormat,
}

#[pymethods]
impl PyFpFormat {
    /// The format `(eb, sb)`; raises `WidthError` unless `2 <= eb <= 31`, `sb >= 2` and
    /// `eb + sb <= 512`.
    #[new]
    fn new(eb: u32, sb: u32) -> PyResult<Self> {
        FpFormat::new(eb, sb)
            .map(|f| PyFpFormat { f })
            .map_err(|e| WidthError::new_err(e.to_string()))
    }

    /// Exponent bits.
    #[getter]
    fn eb(&self) -> u32 {
        self.f.eb()
    }

    /// Significand bits, the hidden bit included (the precision).
    #[getter]
    fn sb(&self) -> u32 {
        self.f.sb()
    }

    /// The width of an encoding: `eb + sb`.
    #[getter]
    fn width(&self) -> u16 {
        self.f.width().bits()
    }

    /// The name of a standard format in the text syntax (`"f32"`, ...), else None.
    #[getter]
    fn name(&self) -> Option<&'static str> {
        self.f.name()
    }

    fn __repr__(&self) -> String {
        format!("FpFormat({}, {})", self.f.eb(), self.f.sb())
    }
}

/// A rounding mode by its name in the text syntax.
fn rounding(rm: &str) -> PyResult<RoundingMode> {
    RoundingMode::from_name(rm).ok_or_else(|| {
        PyValueError::new_err(format!(
            "unknown rounding mode {rm:?} (\"rne\", \"rna\", \"rtp\", \"rtn\" or \"rtz\")"
        ))
    })
}

/// The name of a floating-point operation in the text syntax (`fp.add`, ...).
fn fp_name(op: FpOp) -> Option<&'static str> {
    Some(match op {
        FpOp::Add(_) => "add",
        FpOp::Mul(_) => "mul",
        FpOp::Div(_) => "div",
        FpOp::Fma(_) => "fma",
        FpOp::Sqrt(_) => "sqrt",
        FpOp::Rem => "rem",
        FpOp::RoundToIntegral(_) => "round",
        FpOp::Min => "min",
        FpOp::Max => "max",
        FpOp::Eq => "eq",
        FpOp::Lt => "lt",
        FpOp::Le => "le",
        FpOp::Convert { .. } => "convert",
        FpOp::FromSInt(_) => "from_sbv",
        FpOp::FromUInt(_) => "from_ubv",
        FpOp::ToSInt(..) => "to_sbv",
        FpOp::ToUInt(..) => "to_ubv",
        _ => return None,
    })
}

// ----- contexts ------------------------------------------------------------------------------

/// A hash-consed expression arena. Every expression belongs to one context; structurally equal
/// expressions of a context are one node (the same `Expr`).
#[pyclass(frozen, name = "Context", module = "bitwright")]
#[derive(Debug)]
struct PyContext {
    cx: Mutex<Context>,
}

/// Locks `m`, waiting with the interpreter released if another thread holds it.
fn lock<'a, T: Send>(py: Python<'_>, m: &'a Mutex<T>) -> MutexGuard<'a, T> {
    loop {
        match m.try_lock() {
            Ok(g) => return g,
            Err(TryLockError::Poisoned(p)) => return p.into_inner(),
            Err(TryLockError::WouldBlock) => py.detach(|| drop(m.lock())),
        }
    }
}

impl PyContext {
    fn lock(&self, py: Python<'_>) -> MutexGuard<'_, Context> {
        lock(py, &self.cx)
    }
}

/// A new expression of `cx`.
fn wrap(cx: &Bound<'_, PyContext>, c: &Context, e: Expr) -> PyResult<PyExpr> {
    Ok(PyExpr {
        cx: cx.clone().unbind(),
        e,
        width: c.width(e).or_raise()?.bits(),
    })
}

/// A symbol key from a Python `str` or `int`.
fn symbol_key(key: &Bound<'_, PyAny>) -> PyResult<SymbolKey> {
    if let Ok(s) = key.cast::<PyString>() {
        Ok(SymbolKey::from(s.to_str()?))
    } else if let Ok(k) = key.extract::<u64>() {
        Ok(SymbolKey::from(k))
    } else {
        Err(PyTypeError::new_err(
            "a symbol name is a str or a non-negative int",
        ))
    }
}

/// The name of a symbol key: the string itself, `#k` for an integer, `$k` for a fresh symbol.
fn key_name(key: &SymbolKey) -> String {
    match key {
        SymbolKey::Str(s) => s.to_string(),
        other => other.to_string(),
    }
}

#[pymethods]
impl PyContext {
    /// A new, empty context: at most `max_nodes` nodes (default 2^24) and at most `fact_work`
    /// transfer functions per fact query (default 2^20).
    #[new]
    #[pyo3(signature = (*, max_nodes = None, fact_work = None))]
    fn new(max_nodes: Option<u32>, fact_work: Option<u32>) -> Self {
        let mut config = ContextConfig::default();
        if let Some(n) = max_nodes {
            config = config.with_max_nodes(n);
        }
        if let Some(n) = fact_work {
            config = config.with_fact_work(n);
        }
        PyContext {
            cx: Mutex::new(Context::with_config(config)),
        }
    }

    /// The number of nodes.
    fn __len__(&self, py: Python<'_>) -> usize {
        self.lock(py).len()
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        format!("<bitwright.Context with {} nodes>", self.lock(py).len())
    }

    /// Drops every node and symbol: every expression of the context becomes stale.
    fn clear(&self, py: Python<'_>) {
        self.lock(py).clear();
    }

    /// The symbol `name` (a `str`, or an `int` key printed `#k`) of `width` bits; the same
    /// expression on every call.
    fn symbol(slf: &Bound<'_, Self>, name: &Bound<'_, PyAny>, width: u16) -> PyResult<PyExpr> {
        let key = symbol_key(name)?;
        let w = self::width(width)?;
        let mut c = slf.get().lock(slf.py());
        let e = c.symbol(key, w).or_raise()?;
        wrap(slf, &c, e)
    }

    /// Symbols named by the words of `names` (e.g. `"x y z"`), all of `width` bits.
    fn symbols(slf: &Bound<'_, Self>, names: &str, width: u16) -> PyResult<Vec<PyExpr>> {
        let w = self::width(width)?;
        let mut c = slf.get().lock(slf.py());
        names
            .split_whitespace()
            .map(|n| {
                let e = c.symbol(n, w).or_raise()?;
                wrap(slf, &c, e)
            })
            .collect()
    }

    /// A symbol distinct from every other (printed `$k`).
    fn fresh_symbol(slf: &Bound<'_, Self>, width: u16) -> PyResult<PyExpr> {
        let w = self::width(width)?;
        let mut c = slf.get().lock(slf.py());
        let e = c.fresh_symbol(w).or_raise()?;
        wrap(slf, &c, e)
    }

    /// The constant `value` of `width` bits: `0 <= value < 2**width`, or a negative value in
    /// two's complement down to `-2**(width - 1)`.
    #[pyo3(name = "const")]
    fn constant(slf: &Bound<'_, Self>, value: &Bound<'_, PyAny>, width: u16) -> PyResult<PyExpr> {
        let v = to_bitvec(value, self::width(width)?)?;
        let mut c = slf.get().lock(slf.py());
        let e = c.constant(&v).or_raise()?;
        wrap(slf, &c, e)
    }

    /// Parses expression text, e.g. `"(x & y) + (x | y)"` or `"let m = x * 3; m ^ (m >>u 7)"`.
    /// `width` types the symbols and literals whose width cannot be inferred.
    #[pyo3(signature = (text, width = None))]
    fn parse(slf: &Bound<'_, Self>, text: &str, width: Option<u16>) -> PyResult<PyExpr> {
        let opts = match width {
            Some(w) => ParseOptions::width(self::width(w)?),
            None => ParseOptions::default(),
        };
        let mut c = slf.get().lock(slf.py());
        let e = c.parse(text, &opts).or_raise()?;
        wrap(slf, &c, e)
    }

    /// The expressions as an SMT-LIB 2.6 QF_BV script (QF_BVFP with floating point): the
    /// symbols declared and the `K`-th expression defined as `rootK`.
    #[pyo3(signature = (*exprs))]
    fn to_smtlib(&self, py: Python<'_>, exprs: Vec<PyRef<'_, PyExpr>>) -> PyResult<String> {
        let roots: Vec<Expr> = exprs.iter().map(|e| e.e).collect();
        bitwright::smtlib::export(&mut self.lock(py), &roots).or_raise()
    }

    /// Reads an SMT-LIB QF_BV script, floating-point (QF_BVFP) terms included, into this
    /// context.
    fn from_smtlib(slf: &Bound<'_, Self>, script: &str) -> PyResult<SmtScript> {
        let py = slf.py();
        let (symbols, definitions, assertions) = {
            let mut c = slf.get().lock(py);
            let imp = bitwright::smtlib::import(&mut c, script).or_raise()?;
            let named = |v: Vec<(String, Expr)>| -> PyResult<Vec<(String, PyExpr)>> {
                v.into_iter()
                    .map(|(n, e)| Ok((n, wrap(slf, &c, e)?)))
                    .collect()
            };
            let assertions: Vec<PyExpr> = imp
                .assertions
                .iter()
                .map(|&e| wrap(slf, &c, e))
                .collect::<PyResult<_>>()?;
            (named(imp.symbols)?, named(imp.definitions)?, assertions)
        };
        let dict = |v: Vec<(String, PyExpr)>| -> PyResult<Py<PyDict>> {
            let d = PyDict::new(py);
            for (n, e) in v {
                d.set_item(n, e)?;
            }
            Ok(d.unbind())
        };
        Ok(SmtScript {
            symbols: dict(symbols)?,
            definitions: dict(definitions)?,
            assertions,
        })
    }
}

/// A script read by `Context.from_smtlib`.
#[pyclass(frozen, module = "bitwright")]
#[derive(Debug)]
struct SmtScript {
    /// Declared constants, by name.
    #[pyo3(get)]
    symbols: Py<PyDict>,
    /// Definitions without parameters, by name.
    #[pyo3(get)]
    definitions: Py<PyDict>,
    /// Asserted formulas, as 1-bit expressions.
    #[pyo3(get)]
    assertions: Vec<PyExpr>,
}

// ----- expressions ---------------------------------------------------------------------------

/// An expression: a node of a context. Immutable and hashable; `==` is identity (hash-consing
/// makes structurally equal expressions one node). Comparisons that build a 1-bit expression
/// are methods (`eq`, `ult`, `slt`, ...), since `<` could be signed or unsigned.
#[pyclass(frozen, skip_from_py_object, name = "Expr", module = "bitwright")]
#[derive(Debug)]
struct PyExpr {
    cx: Py<PyContext>,
    e: Expr,
    width: u16,
}

impl Clone for PyExpr {
    fn clone(&self) -> Self {
        Python::attach(|py| PyExpr {
            cx: self.cx.clone_ref(py),
            e: self.e,
            width: self.width,
        })
    }
}

/// An operand: an expression, or an int taken as a constant of the other operand's width.
#[derive(FromPyObject)]
enum Operand<'py> {
    Expr(PyRef<'py, PyExpr>),
    Int(Bound<'py, PyInt>),
}

impl PyExpr {
    /// Runs `f` on the locked context, and wraps the expression it builds.
    fn build(
        &self,
        py: Python<'_>,
        f: impl FnOnce(&mut Context) -> Result<Expr, Error>,
    ) -> PyResult<PyExpr> {
        let cx = self.cx.bind(py);
        let mut c = cx.get().lock(py);
        let e = f(&mut c).or_raise()?;
        wrap(cx, &c, e)
    }

    /// The operand's handle; an int becomes a constant of this expression's width.
    fn operand(&self, py: Python<'_>, o: &Operand<'_>) -> PyResult<Expr> {
        match o {
            Operand::Expr(e) => Ok(e.e),
            Operand::Int(i) => {
                let v = to_bitvec(i.as_any(), width(self.width)?)?;
                self.cx.bind(py).get().lock(py).constant(&v).or_raise()
            }
        }
    }

    fn bin(&self, py: Python<'_>, op: BinOp, o: &Operand<'_>, reflected: bool) -> PyResult<PyExpr> {
        let b = self.operand(py, o)?;
        let (x, y) = if reflected { (b, self.e) } else { (self.e, b) };
        self.build(py, |c| c.bin(op, x, y))
    }

    fn cmp(&self, py: Python<'_>, op: CmpOpExt, o: &Operand<'_>) -> PyResult<PyExpr> {
        let b = self.operand(py, o)?;
        self.build(py, |c| c.cmp(op, self.e, b))
    }

    fn un(&self, py: Python<'_>, op: UnOp) -> PyResult<PyExpr> {
        self.build(py, |c| c.un(op, self.e))
    }

    /// The floating-point operation `op` of `fmt` on this expression and `others`.
    fn fp(
        &self,
        py: Python<'_>,
        op: FpOp,
        fmt: PyFpFormat,
        others: &[&Operand<'_>],
    ) -> PyResult<PyExpr> {
        let mut args = vec![self.e];
        for o in others {
            args.push(self.operand(py, o)?);
        }
        self.build(py, |c| c.fp(op, fmt.f, &args))
    }

    fn fcmp(
        &self,
        py: Python<'_>,
        op: FpCmpOp,
        o: &Operand<'_>,
        fmt: PyFpFormat,
    ) -> PyResult<PyExpr> {
        let b = self.operand(py, o)?;
        self.build(py, |c| c.fp_cmp(fmt.f, op, self.e, b))
    }

    fn ftest(&self, py: Python<'_>, t: FpTest, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.build(py, |c| c.fp_test(fmt.f, t, self.e))
    }

    /// Symbol values for `eval` from `env` and `kwargs`, whose keys are names or symbol
    /// expressions: the keys are read, then their widths (locked), then the values.
    fn env(
        &self,
        py: Python<'_>,
        env: Option<&Bound<'_, PyDict>>,
        kwargs: Option<&Bound<'_, PyDict>>,
    ) -> PyResult<HashMap<SymbolKey, BitVec>> {
        enum Key {
            Expr(Expr),
            Name(SymbolKey),
        }
        let mut pending = Vec::new();
        for d in [env, kwargs].into_iter().flatten() {
            for (k, v) in d.iter() {
                let key = match k.cast::<PyExpr>() {
                    Ok(e) => Key::Expr(e.get().e),
                    Err(_) => Key::Name(symbol_key(&k)?),
                };
                pending.push((key, v));
            }
        }
        let resolved = {
            let c = self.cx.bind(py).get().lock(py);
            let mut resolved = Vec::with_capacity(pending.len());
            for (key, v) in pending {
                let symbol = match key {
                    Key::Expr(e) => {
                        let id = c.symbol_id(e).or_raise()?.ok_or_else(|| {
                            PyTypeError::new_err("an environment key is not a symbol")
                        })?;
                        c.symbol_key(id).cloned().zip(c.symbol_width(id))
                    }
                    Key::Name(key) => {
                        let w = c.find_symbol(&key).and_then(|e| c.width(e).ok());
                        w.map(|w| (key, w))
                    }
                };
                resolved.push((symbol, v));
            }
            resolved
        };
        let mut out = HashMap::with_capacity(resolved.len());
        for (symbol, v) in resolved {
            // A symbol the context does not have cannot occur in the expression.
            if let Some((key, w)) = symbol {
                out.insert(key, to_bitvec(&v, w)?);
            }
        }
        Ok(out)
    }
}

#[pymethods]
impl PyExpr {
    /// The width in bits.
    #[getter]
    fn width(&self) -> u16 {
        self.width
    }

    /// The context the expression belongs to.
    #[getter]
    fn context(&self, py: Python<'_>) -> Py<PyContext> {
        self.cx.clone_ref(py)
    }

    /// The handle as an integer, unique within the context.
    #[getter]
    fn handle(&self) -> u64 {
        self.e.to_bits()
    }

    /// The node's kind: `"const"`, `"symbol"`, `"unary"`, `"binary"`, `"compare"`, `"zext"`,
    /// `"sext"`, `"extract"`, `"concat"`, `"select"`, `"ext"` or `"fp"`.
    #[getter]
    fn kind(&self, py: Python<'_>) -> PyResult<&'static str> {
        let c = self.cx.bind(py).get().lock(py);
        Ok(match c.view(self.e).or_raise()? {
            View::Const(_) => "const",
            View::Sym(_) => "symbol",
            View::Un(..) => "unary",
            View::Bin(..) => "binary",
            View::Cmp(..) => "compare",
            View::Zext(_) => "zext",
            View::Sext(_) => "sext",
            View::Extract { .. } => "extract",
            View::Concat { .. } => "concat",
            View::Select { .. } => "select",
            View::Ext { .. } => "ext",
            View::Fp { .. } => "fp",
            _ => "other",
        })
    }

    /// The operator of a unary, binary, comparison or floating-point node (`"add"`, `"ult"`,
    /// `"sqrt"`, ...: a floating-point operation as the text syntax names it), else None.
    #[getter]
    fn op(&self, py: Python<'_>) -> PyResult<Option<String>> {
        let c = self.cx.bind(py).get().lock(py);
        Ok(match c.view(self.e).or_raise()? {
            View::Un(op, _) => Some(op.name().to_string()),
            View::Bin(op, ..) => Some(op.name().to_string()),
            View::Cmp(op, ..) => Some(format!("{op:?}").to_lowercase()),
            View::Fp { op, .. } => fp_name(op).map(str::to_string),
            _ => None,
        })
    }

    /// The format of a floating-point node's operands (for `"from_sbv"` and `"from_ubv"`, of its
    /// result), else None.
    #[getter]
    fn format(&self, py: Python<'_>) -> PyResult<Option<PyFpFormat>> {
        let c = self.cx.bind(py).get().lock(py);
        Ok(match c.view(self.e).or_raise()? {
            View::Fp { format, .. } => Some(PyFpFormat { f: format }),
            _ => None,
        })
    }

    /// The result's format of a conversion between formats (`"convert"`), else None.
    #[getter]
    fn to_format(&self, py: Python<'_>) -> PyResult<Option<PyFpFormat>> {
        let c = self.cx.bind(py).get().lock(py);
        Ok(match c.view(self.e).or_raise()? {
            View::Fp {
                op: FpOp::Convert { to, .. },
                ..
            } => Some(PyFpFormat { f: to }),
            _ => None,
        })
    }

    /// The rounding mode of a floating-point node (`"rne"`, `"rna"`, `"rtp"`, `"rtn"` or
    /// `"rtz"`), else None (also for the operations without one: `"rem"`, `"min"`, `"max"` and
    /// the comparisons).
    #[getter]
    fn rounding(&self, py: Python<'_>) -> PyResult<Option<&'static str>> {
        let c = self.cx.bind(py).get().lock(py);
        Ok(match c.view(self.e).or_raise()? {
            View::Fp { op, .. } => op.rounding_mode().map(RoundingMode::name),
            _ => None,
        })
    }

    /// The operands, in order (for `concat`: high, low; for `select`: condition, then, else).
    #[getter]
    fn children(&self, py: Python<'_>) -> PyResult<Vec<PyExpr>> {
        let cx = self.cx.bind(py);
        let c = cx.get().lock(py);
        let kids: Vec<Expr> = c.children(self.e).or_raise()?.collect();
        kids.into_iter().map(|e| wrap(cx, &c, e)).collect()
    }

    /// The value of a constant (unsigned), else None.
    #[getter]
    fn value<'py>(&self, py: Python<'py>) -> PyResult<Option<Bound<'py, PyAny>>> {
        let v = self
            .cx
            .bind(py)
            .get()
            .lock(py)
            .as_const(self.e)
            .or_raise()?;
        v.map(|v| to_int(py, &v)).transpose()
    }

    /// The value of a constant as a signed integer, else None.
    #[getter]
    fn signed_value<'py>(&self, py: Python<'py>) -> PyResult<Option<Bound<'py, PyAny>>> {
        let v = self
            .cx
            .bind(py)
            .get()
            .lock(py)
            .as_const(self.e)
            .or_raise()?;
        v.map(|v| to_signed_int(py, &v)).transpose()
    }

    /// The name of a symbol (`#k` for an integer key, `$k` for a fresh symbol), else None.
    #[getter]
    fn name(&self, py: Python<'_>) -> PyResult<Option<String>> {
        let c = self.cx.bind(py).get().lock(py);
        let id = c.symbol_id(self.e).or_raise()?;
        Ok(id.and_then(|id| c.symbol_key(id)).map(key_name))
    }

    /// The first bit of an extract (the output of an extension call), else None.
    #[getter]
    fn lo(&self, py: Python<'_>) -> PyResult<Option<u16>> {
        let c = self.cx.bind(py).get().lock(py);
        Ok(match c.view(self.e).or_raise()? {
            View::Extract { lo, .. } => Some(lo),
            View::Ext { output, .. } => Some(u16::from(output)),
            _ => None,
        })
    }

    /// The number of distinct nodes under this one, itself included.
    fn dag_size(&self, py: Python<'_>) -> PyResult<u32> {
        let mut c = self.cx.bind(py).get().lock(py);
        Ok(match c.dag_size(&[self.e], u32::MAX - 1).or_raise()? {
            Bounded::Exact(n) | Bounded::AtLeast(n) => n,
            _ => u32::MAX,
        })
    }

    /// The expression in the text syntax. `lets` binds shared subterms with `let`;
    /// `symbol_widths` annotates symbols with their widths (`x:64`).
    #[pyo3(signature = (*, lets = true, symbol_widths = false))]
    fn to_string(&self, py: Python<'_>, lets: bool, symbol_widths: bool) -> PyResult<String> {
        let c = self.cx.bind(py).get().lock(py);
        c.width(self.e).or_raise()?;
        let opts = PrintOptions::default()
            .with_lets(lets)
            .with_symbol_widths(symbol_widths);
        Ok(c.display_with(self.e, opts).to_string())
    }

    fn __str__(&self, py: Python<'_>) -> PyResult<String> {
        self.to_string(py, true, false)
    }

    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "<bitwright.Expr {}: {}>",
            self.width,
            self.to_string(py, true, false)?
        ))
    }

    fn __hash__(&self) -> u64 {
        self.e.to_bits()
    }

    fn __eq__(&self, other: &Bound<'_, PyAny>) -> bool {
        other
            .cast::<PyExpr>()
            .is_ok_and(|o| o.get().e == self.e && o.get().cx.is(&self.cx))
    }

    fn __ne__(&self, other: &Bound<'_, PyAny>) -> bool {
        !self.__eq__(other)
    }

    fn __bool__(&self) -> PyResult<bool> {
        Err(PyTypeError::new_err(
            "an Expr has no truth value; use prove() to ask whether it holds",
        ))
    }

    // Arithmetic and bitwise operators; an int operand is a constant of this width.

    fn __add__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Add, &o, false)
    }
    fn __radd__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Add, &o, true)
    }
    fn __sub__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Sub, &o, false)
    }
    fn __rsub__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Sub, &o, true)
    }
    fn __mul__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Mul, &o, false)
    }
    fn __rmul__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Mul, &o, true)
    }
    /// Unsigned division (`udiv`; division by zero gives all ones).
    fn __floordiv__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::UDiv, &o, false)
    }
    fn __rfloordiv__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::UDiv, &o, true)
    }
    /// Unsigned remainder (`urem`; `x % 0` is `x`).
    fn __mod__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::URem, &o, false)
    }
    fn __rmod__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::URem, &o, true)
    }
    fn __and__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::And, &o, false)
    }
    fn __rand__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::And, &o, true)
    }
    fn __or__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Or, &o, false)
    }
    fn __ror__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Or, &o, true)
    }
    fn __xor__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Xor, &o, false)
    }
    fn __rxor__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Xor, &o, true)
    }
    fn __lshift__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Shl, &o, false)
    }
    fn __rlshift__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Shl, &o, true)
    }
    /// Logical (unsigned) right shift; `ashr` is the arithmetic one.
    fn __rshift__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::LShr, &o, false)
    }
    fn __rrshift__(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::LShr, &o, true)
    }
    fn __invert__(&self, py: Python<'_>) -> PyResult<PyExpr> {
        self.un(py, UnOp::Not)
    }
    fn __neg__(&self, py: Python<'_>) -> PyResult<PyExpr> {
        self.un(py, UnOp::Neg)
    }

    // Operators without a Python symbol.

    fn udiv(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::UDiv, &o, false)
    }
    fn urem(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::URem, &o, false)
    }
    /// Signed division, truncating (`bvsdiv`).
    fn sdiv(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::SDiv, &o, false)
    }
    /// Signed remainder, with the sign of the dividend (`bvsrem`).
    fn srem(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::SRem, &o, false)
    }
    /// The high half of the unsigned double-width product.
    fn umulhi(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::UMulHi, &o, false)
    }
    /// The high half of the signed double-width product.
    fn smulhi(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::SMulHi, &o, false)
    }
    fn shl(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Shl, &o, false)
    }
    fn lshr(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::LShr, &o, false)
    }
    fn ashr(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::AShr, &o, false)
    }
    fn rotl(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::RotL, &o, false)
    }
    fn rotr(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::RotR, &o, false)
    }
    /// Parallel bit deposit under the mask `o`.
    fn pdep(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Pdep, &o, false)
    }
    /// Parallel bit extract under the mask `o`.
    fn pext(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.bin(py, BinOp::Pext, &o, false)
    }
    fn popcnt(&self, py: Python<'_>) -> PyResult<PyExpr> {
        self.un(py, UnOp::Popcnt)
    }
    fn clz(&self, py: Python<'_>) -> PyResult<PyExpr> {
        self.un(py, UnOp::Clz)
    }
    fn ctz(&self, py: Python<'_>) -> PyResult<PyExpr> {
        self.un(py, UnOp::Ctz)
    }
    fn bswap(&self, py: Python<'_>) -> PyResult<PyExpr> {
        self.un(py, UnOp::Bswap)
    }
    fn bitrev(&self, py: Python<'_>) -> PyResult<PyExpr> {
        self.un(py, UnOp::BitRev)
    }

    // Comparisons, as 1-bit expressions.

    fn eq(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Eq, &o)
    }
    fn ne(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Ne, &o)
    }
    fn ult(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Ult, &o)
    }
    fn ule(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Ule, &o)
    }
    fn ugt(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Ugt, &o)
    }
    fn uge(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Uge, &o)
    }
    fn slt(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Slt, &o)
    }
    fn sle(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Sle, &o)
    }
    fn sgt(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Sgt, &o)
    }
    fn sge(&self, py: Python<'_>, o: Operand<'_>) -> PyResult<PyExpr> {
        self.cmp(py, CmpOpExt::Sge, &o)
    }

    // Casts.

    fn zext(&self, py: Python<'_>, width: u16) -> PyResult<PyExpr> {
        let w = self::width(width)?;
        self.build(py, |c| c.zext(self.e, w))
    }
    fn sext(&self, py: Python<'_>, width: u16) -> PyResult<PyExpr> {
        let w = self::width(width)?;
        self.build(py, |c| c.sext(self.e, w))
    }
    fn trunc(&self, py: Python<'_>, width: u16) -> PyResult<PyExpr> {
        let w = self::width(width)?;
        self.build(py, |c| c.trunc(self.e, w))
    }
    /// Bits `[lo, lo + length)`.
    fn extract(&self, py: Python<'_>, lo: u16, length: u16) -> PyResult<PyExpr> {
        let w = width(length)?;
        self.build(py, |c| c.extract(self.e, lo, w))
    }
    /// Bit `i`, as a 1-bit expression.
    fn bit(&self, py: Python<'_>, i: u16) -> PyResult<PyExpr> {
        self.build(py, |c| c.bit(self.e, i))
    }
    /// This expression in the high bits, then each of `lows`.
    #[pyo3(signature = (*lows))]
    fn concat(&self, py: Python<'_>, lows: Vec<PyRef<'_, PyExpr>>) -> PyResult<PyExpr> {
        self.build(py, |c| {
            lows.iter().try_fold(self.e, |hi, lo| c.concat(hi, lo.e))
        })
    }
    /// `then` where this 1-bit condition holds, else `els`.
    fn select(&self, py: Python<'_>, then: Operand<'_>, els: Operand<'_>) -> PyResult<PyExpr> {
        // Int branches take the other branch's width (or, with two ints, fail below).
        let width_of = |o: &Operand<'_>| match o {
            Operand::Expr(e) => Some(e.width),
            Operand::Int(_) => None,
        };
        let w = width_of(&then)
            .or(width_of(&els))
            .ok_or_else(|| PyTypeError::new_err("select needs at least one expression branch"))?;
        let as_width = |o: &Operand<'_>| -> PyResult<Expr> {
            match o {
                Operand::Expr(e) => Ok(e.e),
                Operand::Int(i) => {
                    let v = to_bitvec(i.as_any(), width(w)?)?;
                    self.cx.bind(py).get().lock(py).constant(&v).or_raise()
                }
            }
        };
        let (t, f) = (as_width(&then)?, as_width(&els)?);
        self.build(py, |c| c.select(self.e, t, f))
    }

    // Floating point (the book's chapter specifies it): this expression and the other operands
    // hold encodings of the format `fmt` (an int operand is one, a constant of this width), and
    // a result is rounded by `rm`: "rne" (to nearest, ties to even), "rna" (to nearest, ties
    // away from zero), "rtp" (toward +inf), "rtn" (toward -inf) or "rtz" (toward zero).

    /// `self + o`.
    #[pyo3(signature = (o, fmt, rm = "rne"))]
    fn fadd(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat, rm: &str) -> PyResult<PyExpr> {
        self.fp(py, FpOp::Add(rounding(rm)?), fmt, &[&o])
    }
    /// `self - o`, built as `self + fneg(o)`.
    #[pyo3(signature = (o, fmt, rm = "rne"))]
    fn fsub(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat, rm: &str) -> PyResult<PyExpr> {
        let rm = rounding(rm)?;
        let b = self.operand(py, &o)?;
        self.build(py, |c| c.fp_sub(fmt.f, rm, self.e, b))
    }
    /// `self * o`.
    #[pyo3(signature = (o, fmt, rm = "rne"))]
    fn fmul(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat, rm: &str) -> PyResult<PyExpr> {
        self.fp(py, FpOp::Mul(rounding(rm)?), fmt, &[&o])
    }
    /// `self / o`.
    #[pyo3(signature = (o, fmt, rm = "rne"))]
    fn fdiv(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat, rm: &str) -> PyResult<PyExpr> {
        self.fp(py, FpOp::Div(rounding(rm)?), fmt, &[&o])
    }
    /// `self * b + c`, rounded once.
    #[pyo3(signature = (b, c, fmt, rm = "rne"))]
    fn ffma(
        &self,
        py: Python<'_>,
        b: Operand<'_>,
        c: Operand<'_>,
        fmt: PyFpFormat,
        rm: &str,
    ) -> PyResult<PyExpr> {
        self.fp(py, FpOp::Fma(rounding(rm)?), fmt, &[&b, &c])
    }
    /// The square root.
    #[pyo3(signature = (fmt, rm = "rne"))]
    fn fsqrt(&self, py: Python<'_>, fmt: PyFpFormat, rm: &str) -> PyResult<PyExpr> {
        self.fp(py, FpOp::Sqrt(rounding(rm)?), fmt, &[])
    }
    /// The IEEE remainder `self - n * o`, `n` the integer nearest `self / o` (exact).
    fn frem(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.fp(py, FpOp::Rem, fmt, &[&o])
    }
    /// Rounded to an integral value.
    #[pyo3(signature = (fmt, rm = "rne"))]
    fn fround(&self, py: Python<'_>, fmt: PyFpFormat, rm: &str) -> PyResult<PyExpr> {
        self.fp(py, FpOp::RoundToIntegral(rounding(rm)?), fmt, &[])
    }
    /// minimumNumber: the smaller operand, a NaN operand ignored, `-0 < +0`.
    fn fmin(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.fp(py, FpOp::Min, fmt, &[&o])
    }
    /// maximumNumber: the larger operand, a NaN operand ignored, `-0 < +0`.
    fn fmax(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.fp(py, FpOp::Max, fmt, &[&o])
    }

    // Floating-point comparisons, 1 bit: false when an operand is a NaN; +0 equals -0.

    fn feq(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.fcmp(py, FpCmpOp::Eq, &o, fmt)
    }
    fn flt(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.fcmp(py, FpCmpOp::Lt, &o, fmt)
    }
    fn fle(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.fcmp(py, FpCmpOp::Le, &o, fmt)
    }
    fn fgt(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.fcmp(py, FpCmpOp::Gt, &o, fmt)
    }
    fn fge(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.fcmp(py, FpCmpOp::Ge, &o, fmt)
    }

    // Sign operations, bit-vector operators that change the sign bit only (a NaN's too).

    /// The sign bit flipped: `self ^ sign`.
    fn fneg(&self, py: Python<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.build(py, |c| c.fp_neg(fmt.f, self.e))
    }
    /// The sign bit cleared: `self & ~sign`.
    fn fabs(&self, py: Python<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.build(py, |c| c.fp_abs(fmt.f, self.e))
    }
    /// With the sign bit of `o`.
    fn fcopysign(&self, py: Python<'_>, o: Operand<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        let b = self.operand(py, &o)?;
        self.build(py, |c| c.fp_copysign(fmt.f, self.e, b))
    }

    // Classification tests, 1 bit: each one unsigned comparison of the encoding.

    /// Any NaN.
    fn fisnan(&self, py: Python<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.ftest(py, FpTest::Nan, fmt)
    }
    /// An infinity.
    fn fisinf(&self, py: Python<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.ftest(py, FpTest::Infinite, fmt)
    }
    /// A zero.
    fn fiszero(&self, py: Python<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.ftest(py, FpTest::Zero, fmt)
    }
    /// Nonzero, with the minimum exponent field.
    fn fissubnormal(&self, py: Python<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.ftest(py, FpTest::Subnormal, fmt)
    }
    /// Finite, nonzero and not subnormal.
    fn fisnormal(&self, py: Python<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.ftest(py, FpTest::Normal, fmt)
    }
    /// The sign bit set, and not a NaN.
    fn fisneg(&self, py: Python<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.ftest(py, FpTest::Negative, fmt)
    }
    /// The sign bit clear, and not a NaN.
    fn fispos(&self, py: Python<'_>, fmt: PyFpFormat) -> PyResult<PyExpr> {
        self.ftest(py, FpTest::Positive, fmt)
    }

    // Conversions.

    /// This value of format `fmt` converted to the format `to`.
    #[pyo3(signature = (to, fmt, rm = "rne"))]
    fn fconvert(
        &self,
        py: Python<'_>,
        to: PyFpFormat,
        fmt: PyFpFormat,
        rm: &str,
    ) -> PyResult<PyExpr> {
        let rm = rounding(rm)?;
        self.fp(py, FpOp::Convert { to: to.f, rm }, fmt, &[])
    }
    /// This integer, signed (or unsigned, with `signed=False`), rounded to the format `fmt`.
    #[pyo3(signature = (fmt, rm = "rne", *, signed = true))]
    fn to_float(
        &self,
        py: Python<'_>,
        fmt: PyFpFormat,
        rm: &str,
        signed: bool,
    ) -> PyResult<PyExpr> {
        let rm = rounding(rm)?;
        let op = if signed {
            FpOp::FromSInt(rm)
        } else {
            FpOp::FromUInt(rm)
        };
        self.fp(py, op, fmt, &[])
    }
    /// This value of format `fmt` rounded to an integer of `width` bits, signed (or unsigned,
    /// with `signed=False`), and saturated to its range; a NaN gives 0.
    #[pyo3(signature = (width, fmt, rm = "rne", *, signed = true))]
    fn to_int(
        &self,
        py: Python<'_>,
        width: u16,
        fmt: PyFpFormat,
        rm: &str,
        signed: bool,
    ) -> PyResult<PyExpr> {
        let (rm, w) = (rounding(rm)?, self::width(width)?);
        let op = if signed {
            FpOp::ToSInt(rm, w)
        } else {
            FpOp::ToUInt(rm, w)
        };
        self.fp(py, op, fmt, &[])
    }
    /// x87's 80-bit extended-precision encoding as a value of `X87` (79 bits): a
    /// pseudo-denormal is the value it stands for; an unnormal, a pseudo-infinity or a
    /// pseudo-NaN loads as the NaN.
    fn x87_load(&self, py: Python<'_>) -> PyResult<PyExpr> {
        self.build(py, |c| c.x87_load(self.e))
    }
    /// A value of `X87` (79 bits) as x87's 80-bit encoding.
    fn x87_store(&self, py: Python<'_>) -> PyResult<PyExpr> {
        self.build(py, |c| c.x87_store(self.e))
    }

    // Evaluating, substituting, reasoning.

    /// The value (unsigned) with symbols bound by `env` and keyword arguments: keys are names
    /// or symbol expressions, values ints.
    #[pyo3(signature = (env = None, /, **kwargs))]
    fn eval<'py>(
        &self,
        py: Python<'py>,
        env: Option<&Bound<'py, PyDict>>,
        kwargs: Option<&Bound<'py, PyDict>>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let env = self.env(py, env, kwargs)?;
        let v = self
            .cx
            .bind(py)
            .get()
            .lock(py)
            .eval(&[self.e], &env)
            .or_raise()?;
        to_int(py, &v[0])
    }

    /// This expression with every key of `mapping` (an expression) replaced by its value (an
    /// expression, or an int of the key's width), all at once.
    fn substitute(&self, py: Python<'_>, mapping: &Bound<'_, PyDict>) -> PyResult<PyExpr> {
        let mut map = Vec::with_capacity(mapping.len());
        for (k, v) in mapping.iter() {
            let k = k
                .cast::<PyExpr>()
                .map_err(|_| PyTypeError::new_err("a substitution key is an Expr"))?
                .get();
            let v = v
                .extract::<Operand<'_>>()
                .map_err(|_| PyTypeError::new_err("a substitution value is an Expr or an int"))?;
            map.push((k.e, k.operand(py, &v)?));
        }
        self.build(py, |c| Ok(c.substitute(&[self.e], &map)?[0]))
    }

    /// What is known about every value: known bits and unsigned and signed bounds, under the
    /// assumptions if given.
    #[pyo3(signature = (assumptions = None))]
    fn facts(&self, py: Python<'_>, assumptions: Option<&PyAssumptions>) -> PyResult<Facts> {
        let (f, r) = {
            let mut c = self.cx.bind(py).get().lock(py);
            match assumptions {
                None => (c.facts(self.e).or_raise()?, Reliance::NONE),
                Some(a) => c
                    .facts_under(self.e, &a.lock(py))
                    .or_raise()?
                    .ok_or_else(|| {
                        BitwrightError::new_err("the assumptions contradict each other")
                    })?,
            }
        };
        let (k, u, s) = (f.known(), f.urange(), f.srange());
        Ok(Facts {
            width: self.width,
            known_zero: to_int(py, &k.known_zero())?.unbind(),
            known_one: to_int(py, &k.known_one())?.unbind(),
            umin: to_int(py, &u.lo())?.unbind(),
            umax: to_int(py, &u.hi())?.unbind(),
            ustride: u.stride(),
            smin: to_signed_int(py, &s.lo())?.unbind(),
            smax: to_signed_int(py, &s.hi())?.unbind(),
            constant: f
                .as_constant()
                .map(|v| to_int(py, &v))
                .transpose()?
                .map(Bound::unbind),
            relies_on: reliance(py, r)?.unbind(),
        })
    }

    /// Whether the expression is nonzero (for a 1-bit predicate: whether it holds): True, False,
    /// or None when not decided. Under the assumptions if given.
    #[pyo3(signature = (assumptions = None))]
    fn prove(&self, py: Python<'_>, assumptions: Option<&PyAssumptions>) -> PyResult<Option<bool>> {
        prove(py, &self.cx, Query::IsNonZero(self.e), assumptions)
    }

    /// Whether the expression is an injective (with `bijective`, also same-width) function of
    /// its subexpression `of`, with every value that does not depend on `of` held fixed.
    #[pyo3(signature = (of, *, bijective = false, assumptions = None))]
    fn prove_injective(
        &self,
        py: Python<'_>,
        of: PyRef<'_, PyExpr>,
        bijective: bool,
        assumptions: Option<&PyAssumptions>,
    ) -> PyResult<Option<bool>> {
        let (e, of) = (self.e, of.e);
        let q = if bijective {
            Query::Bijective { e, of }
        } else {
            Query::Injective { e, of }
        };
        prove(py, &self.cx, q, assumptions)
    }

    /// The expression simplified by `engine` (default: the standard engine).
    #[pyo3(signature = (engine = None))]
    fn simplify(&self, py: Python<'_>, engine: Option<&PyEngine>) -> PyResult<PyExpr> {
        let standard;
        let engine = match engine {
            Some(e) => e,
            None => {
                standard = PyEngine {
                    engine: Engine::standard(),
                    refuse: Vec::new(),
                };
                &standard
            }
        };
        Ok(
            run(py, engine, &[self], Budget::default(), None, None, None)?
                .remove(0)
                .expr,
        )
    }

    /// Whether this equals `other` for every value of the symbols: True (proved), a dict of
    /// symbol values where they differ, or None (not decided). See `bitwright.equivalent`.
    #[pyo3(signature = (other, *, conflicts = 1_000_000))]
    fn equivalent<'py>(
        slf: PyRef<'py, Self>,
        other: PyRef<'py, PyExpr>,
        conflicts: u64,
    ) -> PyResult<Bound<'py, PyAny>> {
        let py = slf.py();
        more::equivalent(py, slf, other, conflicts)
    }

    /// The smallest equal expression synthesis finds (proved), or None.
    #[pyo3(signature = (*, max_size = 7))]
    fn synthesize(slf: PyRef<'_, Self>, max_size: u8) -> PyResult<Option<PyExpr>> {
        let py = slf.py();
        more::synthesize(py, slf, max_size)
    }

    /// The equality-saturation search's smaller candidate, or None.
    #[pyo3(signature = (*, groups = None))]
    fn saturate(slf: PyRef<'_, Self>, groups: Option<Vec<String>>) -> PyResult<Option<PyExpr>> {
        let py = slf.py();
        more::saturate(py, slf, groups)
    }
}

fn prove(
    py: Python<'_>,
    cx: &Py<PyContext>,
    q: Query<'_>,
    assumptions: Option<&PyAssumptions>,
) -> PyResult<Option<bool>> {
    let mut c = cx.bind(py).get().lock(py);
    let t = match assumptions {
        None => c.prove(q),
        Some(a) => c.prove_with(q, &a.lock(py)),
    };
    Ok(truth(t.or_raise()?))
}

// ----- facts and assumptions -----------------------------------------------------------------

/// What is known about every value of an expression.
#[pyclass(frozen, module = "bitwright")]
#[derive(Debug)]
struct Facts {
    /// The width in bits.
    #[pyo3(get)]
    width: u16,
    /// The mask of the bits known to be 0.
    #[pyo3(get)]
    known_zero: Py<PyAny>,
    /// The mask of the bits known to be 1.
    #[pyo3(get)]
    known_one: Py<PyAny>,
    /// The unsigned lower bound.
    #[pyo3(get)]
    umin: Py<PyAny>,
    /// The unsigned upper bound.
    #[pyo3(get)]
    umax: Py<PyAny>,
    /// The unsigned values are among `umin`, `umin + ustride`, ..., `umax` (0 when
    /// `umin == umax`, 1 for every value between).
    #[pyo3(get)]
    ustride: u64,
    /// The signed lower bound.
    #[pyo3(get)]
    smin: Py<PyAny>,
    /// The signed upper bound.
    #[pyo3(get)]
    smax: Py<PyAny>,
    /// The one possible value, if the facts pin it.
    #[pyo3(get)]
    constant: Option<Py<PyAny>>,
    /// The assumptions used, by number (63 stands for every one from 63 on).
    #[pyo3(get)]
    relies_on: Py<PyTuple>,
}

#[pymethods]
impl Facts {
    fn __repr__(&self, py: Python<'_>) -> String {
        let s = |v: &Py<PyAny>| v.bind(py).to_string();
        let hex = |v: &Py<PyAny>| {
            v.bind(py)
                .call_method1("__format__", ("#x",))
                .map_or_else(|_| s(v), |h| h.to_string())
        };
        format!(
            "<bitwright.Facts {} bits: known zero {}, known one {}, unsigned [{}, {}] by {}, signed [{}, {}]>",
            self.width,
            hex(&self.known_zero),
            hex(&self.known_one),
            s(&self.umin),
            s(&self.umax),
            self.ustride,
            s(&self.smin),
            s(&self.smax)
        )
    }
}

/// Constraints known to hold (a path condition, an invariant), numbered from 0 in the order
/// they are added. They belong to the context of their first predicate.
#[pyclass(frozen, name = "Assumptions", module = "bitwright")]
#[derive(Debug, Default)]
struct PyAssumptions {
    a: Mutex<Assumptions>,
}

impl PyAssumptions {
    fn lock(&self, py: Python<'_>) -> MutexGuard<'_, Assumptions> {
        lock(py, &self.a)
    }
}

#[pymethods]
impl PyAssumptions {
    /// An empty set; with predicates, each is assumed to hold.
    #[new]
    #[pyo3(signature = (*predicates))]
    fn new(py: Python<'_>, predicates: Vec<PyRef<'_, PyExpr>>) -> PyResult<Self> {
        let a = PyAssumptions::default();
        for p in predicates {
            a.assume(py, p, true)?;
        }
        Ok(a)
    }

    /// Assumes that the 1-bit predicate holds (or, with `holds=False`, does not); its number.
    /// A contradiction is not an error: it makes the set infeasible.
    #[pyo3(signature = (predicate, holds = true))]
    fn assume(&self, py: Python<'_>, predicate: PyRef<'_, PyExpr>, holds: bool) -> PyResult<u32> {
        let mut c = predicate.cx.bind(py).get().lock(py);
        let mut a = self.lock(py);
        let id = if holds {
            a.assume_true(&mut c, predicate.e)
        } else {
            a.assume_false(&mut c, predicate.e)
        };
        Ok(id.or_raise()?.index())
    }

    /// Whether the constraints contradict each other.
    #[getter]
    fn infeasible(&self, py: Python<'_>) -> bool {
        self.lock(py).is_infeasible()
    }

    fn __len__(&self, py: Python<'_>) -> usize {
        self.lock(py).len()
    }

    fn __repr__(&self, py: Python<'_>) -> String {
        let a = self.lock(py);
        format!(
            "<bitwright.Assumptions: {} constraints{}>",
            a.len(),
            if a.is_infeasible() {
                ", infeasible"
            } else {
                ""
            }
        )
    }
}

// ----- engines -------------------------------------------------------------------------------

/// Caps on the work of one simplification call, in the units of the engine's charging
/// schedule. Unset fields keep the default; `None` is unlimited.
#[pyclass(frozen, skip_from_py_object, name = "Budget", module = "bitwright")]
#[derive(Debug, Clone, Copy)]
struct PyBudget {
    b: Budget,
}

fn uncap(v: u64) -> Option<u64> {
    (v != u64::MAX).then_some(v)
}

#[pymethods]
impl PyBudget {
    /// `Budget(node_visits=10_000, mba_calls=None)`: each limit an int, or None for unlimited.
    /// The limits are `node_visits`, `candidates`, `match_steps`, `rewrites`, `new_nodes`,
    /// `fact_work`, `pass_work`, `mba_calls`, `eqsat_nodes` and `eqsat_work`.
    #[new]
    #[pyo3(signature = (**limits))]
    fn new(limits: Option<&Bound<'_, PyDict>>) -> PyResult<Self> {
        let mut b = Budget::default();
        for (k, v) in limits.into_iter().flat_map(|d| d.iter()) {
            let name: String = k.extract()?;
            let v = v.extract::<Option<u64>>()?.unwrap_or(u64::MAX);
            b = match name.as_str() {
                "node_visits" => b.with_node_visits(v),
                "candidates" => b.with_candidates(v),
                "match_steps" => b.with_match_steps(v),
                "rewrites" => b.with_rewrites(v),
                "new_nodes" => b.with_new_nodes(v),
                "fact_work" => b.with_fact_work(v),
                "pass_work" => b.with_pass_work(v),
                "mba_calls" => b.with_mba_calls(v),
                "eqsat_nodes" => b.with_eqsat_nodes(v),
                "eqsat_work" => b.with_eqsat_work(v),
                other => {
                    return Err(PyTypeError::new_err(format!(
                        "Budget() got an unexpected keyword argument {other:?}"
                    )));
                }
            };
        }
        Ok(PyBudget { b })
    }

    /// No limits.
    #[staticmethod]
    fn unlimited() -> Self {
        PyBudget {
            b: Budget::UNLIMITED,
        }
    }

    #[getter]
    fn node_visits(&self) -> Option<u64> {
        uncap(self.b.node_visits)
    }
    #[getter]
    fn candidates(&self) -> Option<u64> {
        uncap(self.b.candidates)
    }
    #[getter]
    fn match_steps(&self) -> Option<u64> {
        uncap(self.b.match_steps)
    }
    #[getter]
    fn rewrites(&self) -> Option<u64> {
        uncap(self.b.rewrites)
    }
    #[getter]
    fn new_nodes(&self) -> Option<u64> {
        uncap(self.b.new_nodes)
    }
    #[getter]
    fn fact_work(&self) -> Option<u64> {
        uncap(self.b.fact_work)
    }
    #[getter]
    fn pass_work(&self) -> Option<u64> {
        uncap(self.b.pass_work)
    }
    #[getter]
    fn mba_calls(&self) -> Option<u64> {
        uncap(self.b.mba_calls)
    }
    #[getter]
    fn eqsat_nodes(&self) -> Option<u64> {
        uncap(self.b.eqsat_nodes)
    }
    #[getter]
    fn eqsat_work(&self) -> Option<u64> {
        uncap(self.b.eqsat_work)
    }

    fn __repr__(&self) -> String {
        format!("<bitwright.Budget {:?}>", self.b)
    }
}

/// The result for one expression of `Engine.run`.
#[pyclass(frozen, module = "bitwright")]
#[derive(Debug)]
struct Outcome {
    /// The result: equal to the input wherever the assumptions in `relies_on` hold.
    #[pyo3(get)]
    expr: PyExpr,
    /// Whether it differs from the input.
    #[pyo3(get)]
    changed: bool,
    /// `"completed"`, `"budget"` (a limit stopped it; the result is valid but not final) or
    /// `"declined"` (not processed).
    #[pyo3(get)]
    end: &'static str,
    /// The limit that stopped it (e.g. `"node visits"`), for `end == "budget"`.
    #[pyo3(get)]
    limit: Option<String>,
    /// The assumptions the result relies on, by number (63 stands for every one from 63 on).
    #[pyo3(get)]
    relies_on: Py<PyTuple>,
}

#[pymethods]
impl Outcome {
    fn __repr__(&self, py: Python<'_>) -> PyResult<String> {
        Ok(format!(
            "<bitwright.Outcome {}: {}{}>",
            self.end,
            self.expr.__str__(py)?,
            if self.changed { "" } else { " (unchanged)" }
        ))
    }
}

/// Simplifies `exprs` (of one context) with the interpreter released: in one call, or with
/// `threads` each on its own (`Engine::run_each`).
fn run(
    py: Python<'_>,
    engine: &PyEngine,
    exprs: &[&PyExpr],
    budget: Budget,
    assumptions: Option<&PyAssumptions>,
    trace: Option<&mut Trace>,
    threads: Option<usize>,
) -> PyResult<Vec<Outcome>> {
    let refuse = Refuse(&engine.refuse);
    let engine = &engine.engine;
    let Some(first) = exprs.first() else {
        return Ok(Vec::new());
    };
    let cx = first.cx.bind(py);
    let roots: Vec<Expr> = exprs.iter().map(|e| e.e).collect();
    let pycx = cx.get();
    let out = py
        .detach(|| {
            let mut c = pycx.cx.lock().unwrap_or_else(|p| p.into_inner());
            let a = assumptions.map(|a| a.a.lock().unwrap_or_else(|p| p.into_inner()));
            if let Some(threads) = threads {
                let mut each = Each::default().with_threads(threads).with_per_root(budget);
                if let Some(a) = &a {
                    each = each.with_assumptions(a);
                }
                if !refuse.0.is_empty() {
                    each = each.with_hooks(&refuse);
                }
                return engine.run_each(&mut c, &roots, each);
            }
            let mut options = Run::default().with_per_call(budget);
            if let Some(a) = &a {
                options = options.with_assumptions(a);
            }
            if !refuse.0.is_empty() {
                options = options.with_hooks(&refuse);
            }
            if let Some(t) = trace {
                options = options.with_observer(t);
            }
            engine.run(&mut c, &roots, options)
        })
        .or_raise()?;
    let exprs = {
        let c = pycx.lock(py);
        out.roots
            .iter()
            .map(|r| wrap(cx, &c, r.expr))
            .collect::<PyResult<Vec<_>>>()?
    };
    out.roots
        .iter()
        .zip(exprs)
        .map(|(r, expr)| {
            let (end, limit) = match r.end {
                End::Completed => ("completed", None),
                End::BudgetTerminated(x) => ("budget", Some(x.to_string())),
                _ => ("declined", None),
            };
            Ok(Outcome {
                expr,
                changed: r.changed,
                end,
                limit,
                relies_on: reliance(py, r.relies_on)?.unbind(),
            })
        })
        .collect()
}

/// A rule file's source, and the proof ledger vouching for its rules (None: check them now).
#[derive(FromPyObject)]
enum Rules {
    Source(String),
    WithLedger(String, Option<String>),
}

/// Checks every rule of `program`; the ledger vouching for them all.
fn check(program: &RuleProgram) -> PyResult<Ledger> {
    let checks = check_program(program, &CheckConfig::default());
    for c in &checks {
        let why = match &c.verdict {
            Verdict::Sound => continue,
            Verdict::Unsound(cx) => format!("is unsound: {cx}"),
            Verdict::Inconclusive(why) => format!("is not proven sound: {why}"),
            other => format!("is not proven sound: {other:?}"),
        };
        return Err(RuleError::new_err(format!("rule `{}` {why}", c.name)));
    }
    Ok(Ledger::from_checks(&checks))
}

fn compile(source: &str) -> PyResult<RuleProgram> {
    RuleProgram::compile(source).map_err(|e| RuleError::new_err(e.to_string()))
}

/// The engine of a preset without rules of its own, built once per process.
fn preset(name: &str) -> PyResult<Engine> {
    static DEOBFUSCATE: OnceLock<Engine> = OnceLock::new();
    match name {
        "standard" => Ok(Engine::standard()),
        "deobfuscate" => Ok(DEOBFUSCATE
            .get_or_init(|| {
                build(false, Vec::new(), None, false).expect("the deobfuscation engine links")
            })
            .clone()),
        other => Err(PyValueError::new_err(format!(
            "unknown preset {other:?} (\"standard\" or \"deobfuscate\")"
        ))),
    }
}

/// An engine: the standard or deobfuscation strategy, with the rules of `programs`.
fn build(
    standard: bool,
    programs: Vec<(RuleProgram, Ledger)>,
    max_rounds: Option<u8>,
    float_values: bool,
) -> PyResult<Engine> {
    let mut b = Engine::builder().builtin();
    let mut strategy = if standard {
        Strategy::standard()
    } else {
        // The command line's `simplify`: the MBA service with the native solver, on
        // bitwright's own evidence only.
        b = b.mba_solver(Arc::new(NormalFormSolver::default()));
        let trust = MbaTrust::default().with_backend_certificates(false);
        Strategy::deobfuscate().with_mba(MbaConfig::default().with_trust(trust))
    };
    let mut groups = Vec::new();
    for (program, ledger) in programs {
        groups.extend(program.groups().iter().map(|g| g.name.clone()));
        b = b.program(program, &ledger);
    }
    if !groups.is_empty() {
        let groups: Vec<&str> = groups.iter().map(String::as_str).collect();
        strategy = strategy.with_rule_groups(&groups);
    }
    if let Some(n) = max_rounds {
        strategy = strategy.with_max_rounds(n);
    }
    strategy = strategy.with_float_values(float_values);
    b.strategy(strategy)
        .build()
        .map_err(|e| RuleError::new_err(e.to_string()))
}

/// A simplifier: `"standard"` (fact folding, the built-in rules, the normal-form passes) or
/// `"deobfuscate"` (also linear MBA, bit shuffles, and the MBA service with the native solver:
/// the command line's `simplify`), with rule files of your own. Immutable; shared freely.
#[pyclass(frozen, name = "Engine", module = "bitwright")]
#[derive(Debug)]
struct PyEngine {
    engine: Engine,
    /// Rules and passes whose rewrites are refused, by name.
    refuse: Vec<String>,
}

/// Refuses the rewrites of the named rules and passes.
struct Refuse<'a>(&'a [String]);

impl bitwright::engine::Hooks for Refuse<'_> {
    fn admit(&self, _: &Context, _: Expr, _: Expr, by: bitwright::engine::By<'_>) -> bool {
        !self.0.iter().any(|n| n == by.name())
    }

    fn revision(&self) -> u64 {
        // One per refusal list.
        self.0.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, n| {
            n.bytes()
                .fold(h, |h, b| (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3))
        })
    }
}

/// One rewrite of a trace: the rule or pass, the node before, its replacement.
type Step = (String, PyExpr, PyExpr);

/// Records the rewrites of a run: what rewrote which node to which.
#[derive(Default)]
struct Trace(Vec<(String, Expr, Expr)>);

impl bitwright::engine::Observer for Trace {
    fn event(&mut self, event: bitwright::engine::Event<'_>) {
        if let bitwright::engine::Event::Applied { by, before, after } = event {
            self.0.push((by.name().to_string(), before, after));
        }
    }
}

#[pymethods]
impl PyEngine {
    /// `rules` is a sequence of `.bwr` sources, each a string (checked now, which can take a
    /// while) or a `(source, ledger)` pair with the proof ledger from `check_rules`.
    ///
    /// `float_values` also applies the rules that hold for floats as values (every NaN one
    /// value); `refuse` names rules (`group::rule`) and passes (`linear`, …) whose rewrites are
    /// refused.
    #[new]
    #[pyo3(signature = (preset = "standard", *, rules = Vec::new(), max_rounds = None, float_values = false, refuse = Vec::new()))]
    fn new(
        preset: &str,
        rules: Vec<Rules>,
        max_rounds: Option<u8>,
        float_values: bool,
        refuse: Vec<String>,
    ) -> PyResult<Self> {
        let standard = match preset {
            "standard" => true,
            "deobfuscate" => false,
            other => {
                return Err(PyValueError::new_err(format!(
                    "unknown preset {other:?} (\"standard\" or \"deobfuscate\")"
                )));
            }
        };
        if rules.is_empty() && max_rounds.is_none() && !float_values {
            return Ok(PyEngine {
                engine: self::preset(preset)?,
                refuse,
            });
        }
        let mut programs = Vec::new();
        for r in rules {
            let (source, ledger) = match r {
                Rules::Source(s) => (s, None),
                Rules::WithLedger(s, l) => (s, l),
            };
            let program = compile(&source)?;
            let ledger = match ledger {
                Some(l) => {
                    Ledger::parse(&l).map_err(|e| RuleError::new_err(format!("ledger: {e}")))?
                }
                None => check(&program)?,
            };
            programs.push((program, ledger));
        }
        Ok(PyEngine {
            engine: build(standard, programs, max_rounds, float_values)?,
            refuse,
        })
    }

    /// The standard engine.
    #[staticmethod]
    fn standard() -> PyResult<Self> {
        Ok(PyEngine {
            engine: preset("standard")?,
            refuse: Vec::new(),
        })
    }

    /// The deobfuscation engine.
    #[staticmethod]
    fn deobfuscate() -> PyResult<Self> {
        Ok(PyEngine {
            engine: preset("deobfuscate")?,
            refuse: Vec::new(),
        })
    }

    /// The expression simplified: equal to it everywhere, or wherever `assumptions` hold.
    #[pyo3(signature = (expr, *, budget = None, assumptions = None))]
    fn simplify(
        &self,
        py: Python<'_>,
        expr: PyRef<'_, PyExpr>,
        budget: Option<&PyBudget>,
        assumptions: Option<&PyAssumptions>,
    ) -> PyResult<PyExpr> {
        let budget = budget.map_or_else(Budget::default, |b| b.b);
        Ok(run(py, self, &[&expr], budget, assumptions, None, None)?
            .remove(0)
            .expr)
    }

    /// The expression simplified, and each rewrite on the way: (rule or pass, before, after).
    #[pyo3(signature = (expr, *, budget = None, assumptions = None))]
    fn trace(
        &self,
        py: Python<'_>,
        expr: PyRef<'_, PyExpr>,
        budget: Option<&PyBudget>,
        assumptions: Option<&PyAssumptions>,
    ) -> PyResult<(PyExpr, Vec<Step>)> {
        let budget = budget.map_or_else(Budget::default, |b| b.b);
        let mut trace = Trace::default();
        let out = run(
            py,
            self,
            &[&expr],
            budget,
            assumptions,
            Some(&mut trace),
            None,
        )?
        .remove(0)
        .expr;
        let cx = expr.cx.bind(py);
        let c = cx.get().lock(py);
        let steps = trace
            .0
            .iter()
            .map(|(by, b, a)| Ok((by.clone(), wrap(cx, &c, *b)?, wrap(cx, &c, *a)?)))
            .collect::<PyResult<Vec<_>>>()?;
        Ok((out, steps))
    }

    /// Simplifies expressions of one context in one call (they share work); an `Outcome` each.
    #[pyo3(signature = (exprs, *, budget = None, assumptions = None))]
    fn run(
        &self,
        py: Python<'_>,
        exprs: Vec<PyRef<'_, PyExpr>>,
        budget: Option<&PyBudget>,
        assumptions: Option<&PyAssumptions>,
    ) -> PyResult<Vec<Outcome>> {
        let budget = budget.map_or_else(Budget::default, |b| b.b);
        let refs: Vec<&PyExpr> = exprs.iter().map(|e| &**e).collect();
        run(py, self, &refs, budget, assumptions, None, None)
    }

    /// Simplifies expressions of one context each on its own, as `run` would with that one
    /// alone, on up to `threads` threads (0: as many as the machine runs at once), with the
    /// interpreter released; an `Outcome` each. `budget` caps each expression.
    #[pyo3(signature = (exprs, *, threads = 0, budget = None, assumptions = None))]
    fn run_each(
        &self,
        py: Python<'_>,
        exprs: Vec<PyRef<'_, PyExpr>>,
        threads: usize,
        budget: Option<&PyBudget>,
        assumptions: Option<&PyAssumptions>,
    ) -> PyResult<Vec<Outcome>> {
        let budget = budget.map_or_else(Budget::default, |b| b.b);
        let refs: Vec<&PyExpr> = exprs.iter().map(|e| &**e).collect();
        run(py, self, &refs, budget, assumptions, None, Some(threads))
    }

    fn __repr__(&self) -> String {
        format!("<bitwright.Engine {}>", self.engine.strategy().name)
    }
}

// ----- module --------------------------------------------------------------------------------

/// Checks every rule of a `.bwr` source; the proof ledger vouching for them (raises `RuleError`
/// with a counterexample when a rule is unsound).
#[pyfunction]
fn check_rules(py: Python<'_>, source: &str) -> PyResult<String> {
    let program = compile(source)?;
    py.detach(|| check(&program).map(|l| l.render()))
}

/// Simplifies expression text, like the command line's `simplify`: `width` types what cannot
/// be inferred, `deobfuscate` picks the engine, and `assume` lists predicates known to hold.
#[pyfunction]
#[pyo3(signature = (text, width = 64, *, deobfuscate = true, assume = Vec::new()))]
fn simplify(
    py: Python<'_>,
    text: &str,
    width: u16,
    deobfuscate: bool,
    assume: Vec<String>,
) -> PyResult<String> {
    let engine = preset(if deobfuscate {
        "deobfuscate"
    } else {
        "standard"
    })?;
    let opts = ParseOptions::width(self::width(width)?);
    let mut cx = Context::new();
    let e = cx.parse(text, &opts).or_raise()?;
    let mut assumptions = Assumptions::new();
    for p in &assume {
        let p = cx.parse(p, &opts).or_raise()?;
        assumptions.assume_true(&mut cx, p).or_raise()?;
    }
    let out = py
        .detach(|| engine.run(&mut cx, &[e], Run::default().with_assumptions(&assumptions)))
        .or_raise()?;
    Ok(cx.display(out.roots[0].expr).to_string())
}

#[pymodule]
fn _bitwright(m: &Bound<'_, PyModule>) -> PyResult<()> {
    let py = m.py();
    m.add("__version__", env!("CARGO_PKG_VERSION"))?;
    m.add_class::<PyContext>()?;
    m.add_class::<PyExpr>()?;
    m.add_class::<PyEngine>()?;
    m.add_class::<PyAssumptions>()?;
    m.add_class::<PyBudget>()?;
    m.add_class::<Facts>()?;
    m.add_class::<Outcome>()?;
    m.add_class::<SmtScript>()?;
    m.add_class::<PyFpFormat>()?;
    let named = FpFormat::NAMED.into_iter().chain([(FpFormat::X87, "x87")]);
    for (f, name) in named {
        m.add(name.to_uppercase(), PyFpFormat { f })?;
    }
    m.add("BitwrightError", py.get_type::<BitwrightError>())?;
    m.add("WidthError", py.get_type::<WidthError>())?;
    m.add("ParseError", py.get_type::<ParseError>())?;
    m.add("RuleError", py.get_type::<RuleError>())?;
    m.add_function(wrap_pyfunction!(check_rules, m)?)?;
    m.add_function(wrap_pyfunction!(simplify, m)?)?;
    m.add_class::<more::PyMemory>()?;
    m.add_class::<more::LiftedBlock>()?;
    m.add_class::<more::TransformReport>()?;
    m.add_class::<more::InferredPrecondition>()?;
    m.add_function(wrap_pyfunction!(more::equivalent, m)?)?;
    m.add_function(wrap_pyfunction!(more::synthesize, m)?)?;
    m.add_function(wrap_pyfunction!(more::saturate, m)?)?;
    m.add_function(wrap_pyfunction!(more::lift_pcode, m)?)?;
    m.add_function(wrap_pyfunction!(more::lift_vex, m)?)?;
    m.add_function(wrap_pyfunction!(more::lift_llvm, m)?)?;
    m.add_function(wrap_pyfunction!(more::verify_transforms, m)?)?;
    m.add_function(wrap_pyfunction!(more::validate_functions, m)?)?;
    m.add_function(wrap_pyfunction!(more::infer_preconditions, m)?)?;
    Ok(())
}
