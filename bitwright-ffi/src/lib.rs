//! The C API of bitwright: `include/bitwright.h` declares every function here, and
//! `include/bitwright.hpp` wraps them for C++.
//!
//! Each entry point checks its pointers, converts its arguments, runs the library under
//! `catch_unwind` (a panic must not unwind into C), and reports an error as a status code with
//! a message in a thread-local buffer (`bw_last_error`). Output parameters are written only on
//! success. Enumerations cross the boundary as `int` and are read through fixed tables, so an
//! unknown value is an error, never undefined behavior, and the C numbering does not depend on
//! the order of the Rust enums.

use core::ffi::{c_char, c_int, c_uint};
use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::{Arc, OnceLock};

use bw::check::{CheckConfig, Verdict, check_program};
use bw::engine::{Budget, End, Engine, Exhausted, Run, Strategy};
use bw::fp::{FpCmpOp, FpFormat, FpOp, FpTest, RoundingMode};
use bw::mba::{MbaConfig, MbaTrust, NormalFormSolver};
use bw::rules::{Ledger, RuleProgram};
use bw::{
    Assumptions, BinOp, BitVec, Bounded, CmpOp, CmpOpExt, Context, ContextConfig, Error, Expr,
    ParseOptions, PrintOptions, Query, Reliance, SymbolKey, Truth, UnOp, View, Width,
};

#[cfg(test)]
mod tests;

// ----- status codes (bitwright.h) -------------------------------------------------------------

const BW_OK: c_int = 0;
const BW_ERR_WIDTH: c_int = 1;
const BW_ERR_VALUE: c_int = 2;
const BW_ERR_STALE_EXPR: c_int = 3;
const BW_ERR_FOREIGN_EXPR: c_int = 4;
const BW_ERR_SYMBOL_WIDTH: c_int = 5;
const BW_ERR_ARENA_FULL: c_int = 6;
const BW_ERR_UNBOUND_SYMBOL: c_int = 7;
const BW_ERR_ENV_WIDTH: c_int = 8;
const BW_ERR_SYNTAX: c_int = 9;
const BW_ERR_DUPLICATE_SUBSTITUTION: c_int = 10;
const BW_ERR_UNSUPPORTED: c_int = 11;
const BW_ERR_CONTRACT: c_int = 12;
const BW_ERR_INVALID_ARGUMENT: c_int = 13;
const BW_ERR_RULES: c_int = 14;
const BW_ERR_INFEASIBLE: c_int = 15;
const BW_ERR_PANIC: c_int = 16;

/// `BW_ABI_VERSION` in `bitwright.h`: bumped on any change to a declared signature or struct.
const ABI_VERSION: u32 = 1;

// ----- enumeration tables (bitwright.h) -------------------------------------------------------

const UNOPS: [UnOp; 7] = [
    UnOp::Not,
    UnOp::Neg,
    UnOp::Popcnt,
    UnOp::Clz,
    UnOp::Ctz,
    UnOp::Bswap,
    UnOp::BitRev,
];

const BINOPS: [BinOp; 19] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::UMulHi,
    BinOp::SMulHi,
    BinOp::UDiv,
    BinOp::URem,
    BinOp::SDiv,
    BinOp::SRem,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::LShr,
    BinOp::AShr,
    BinOp::RotL,
    BinOp::RotR,
    BinOp::Pdep,
    BinOp::Pext,
];

const CMPOPS: [CmpOpExt; 10] = [
    CmpOpExt::Eq,
    CmpOpExt::Ne,
    CmpOpExt::Ult,
    CmpOpExt::Ule,
    CmpOpExt::Ugt,
    CmpOpExt::Uge,
    CmpOpExt::Slt,
    CmpOpExt::Sle,
    CmpOpExt::Sgt,
    CmpOpExt::Sge,
];

const LIMITS: [Exhausted; 12] = [
    Exhausted::NodeVisits,
    Exhausted::Candidates,
    Exhausted::MatchSteps,
    Exhausted::Rewrites,
    Exhausted::NewNodes,
    Exhausted::FactWork,
    Exhausted::PassWork,
    Exhausted::MbaCalls,
    Exhausted::EqsatNodes,
    Exhausted::EqsatWork,
    Exhausted::Deadline,
    Exhausted::ArenaCapacity,
];

const KIND_CONST: c_int = 0;
const KIND_SYMBOL: c_int = 1;
const KIND_UNARY: c_int = 2;
const KIND_BINARY: c_int = 3;
const KIND_COMPARE: c_int = 4;
const KIND_ZEXT: c_int = 5;
const KIND_SEXT: c_int = 6;
const KIND_EXTRACT: c_int = 7;
const KIND_CONCAT: c_int = 8;
const KIND_SELECT: c_int = 9;
const KIND_EXT: c_int = 10;
const KIND_FP: c_int = 11;

const ROUNDINGS: [RoundingMode; 5] = [
    RoundingMode::Rne,
    RoundingMode::Rna,
    RoundingMode::Rtp,
    RoundingMode::Rtn,
    RoundingMode::Rtz,
];

/// `bw_fpop`: the operations, by their names in the text syntax (`fp.add`, ...).
const FPOPS: [&str; 17] = [
    "add", "mul", "div", "fma", "sqrt", "rem", "round", "min", "max", "eq", "lt", "le", "convert",
    "from_sbv", "from_ubv", "to_sbv", "to_ubv",
];

const FPCMPS: [FpCmpOp; 5] = [
    FpCmpOp::Eq,
    FpCmpOp::Lt,
    FpCmpOp::Le,
    FpCmpOp::Gt,
    FpCmpOp::Ge,
];

const FPTESTS: [FpTest; 7] = [
    FpTest::Nan,
    FpTest::Infinite,
    FpTest::Zero,
    FpTest::Subnormal,
    FpTest::Normal,
    FpTest::Negative,
    FpTest::Positive,
];

const PRESET_STANDARD: c_int = 0;
const PRESET_DEOBFUSCATE: c_int = 1;

const PRINT_NO_LETS: c_uint = 1;
const PRINT_SYMBOL_WIDTHS: c_uint = 2;

const SMT_SYMBOLS: c_int = 0;
const SMT_DEFINITIONS: c_int = 1;
const SMT_ASSERTIONS: c_int = 2;

fn table<T: Copy>(t: &[T], code: c_int, what: &str) -> Res<T> {
    usize::try_from(code)
        .ok()
        .and_then(|i| t.get(i).copied())
        .ok_or_else(|| invalid(format!("unknown {what} {code}")))
}

fn code_of<T: PartialEq>(t: &[T], v: &T) -> c_int {
    t.iter().position(|x| x == v).map_or(-1, |i| i as c_int)
}

/// The code of `v` in `t`; a value without one (added to the library after this table) is
/// `BW_ERR_UNSUPPORTED`.
fn known_code<T: PartialEq + core::fmt::Debug>(t: &[T], v: &T) -> Res<c_int> {
    match code_of(t, v) {
        -1 => Err(Fail(
            BW_ERR_UNSUPPORTED,
            format!("{v:?} has no code in bitwright.h"),
        )),
        c => Ok(c),
    }
}

// ----- errors ---------------------------------------------------------------------------------

/// A failed call: the status code and the message for `bw_last_error`.
struct Fail(c_int, String);

type Res<T> = Result<T, Fail>;

fn invalid(msg: impl Into<String>) -> Fail {
    Fail(BW_ERR_INVALID_ARGUMENT, msg.into())
}

impl From<Error> for Fail {
    fn from(e: Error) -> Fail {
        let code = match &e {
            Error::Width(_) => BW_ERR_WIDTH,
            Error::Value(_) => BW_ERR_VALUE,
            Error::StaleExpr => BW_ERR_STALE_EXPR,
            Error::ForeignExpr => BW_ERR_FOREIGN_EXPR,
            Error::SymbolWidthConflict { .. } => BW_ERR_SYMBOL_WIDTH,
            Error::ArenaFull { .. } => BW_ERR_ARENA_FULL,
            Error::UnboundSymbol { .. } => BW_ERR_UNBOUND_SYMBOL,
            Error::EnvWidth { .. } => BW_ERR_ENV_WIDTH,
            Error::Syntax(_) => BW_ERR_SYNTAX,
            Error::DuplicateSubstitution => BW_ERR_DUPLICATE_SUBSTITUTION,
            Error::Unsupported(_) => BW_ERR_UNSUPPORTED,
            _ => BW_ERR_CONTRACT,
        };
        Fail(code, e.to_string())
    }
}

impl From<bw::WidthError> for Fail {
    fn from(e: bw::WidthError) -> Fail {
        Fail(BW_ERR_WIDTH, e.to_string())
    }
}

impl From<bw::ValueError> for Fail {
    fn from(e: bw::ValueError) -> Fail {
        Fail(BW_ERR_VALUE, e.to_string())
    }
}

thread_local! {
    static LAST_ERROR: RefCell<CString> = RefCell::new(CString::default());
}

/// A C string of `s`, with any NUL byte replaced (C strings cannot hold one).
fn c_string(s: impl Into<String>) -> CString {
    let s = s.into();
    CString::new(s.replace('\0', "\u{fffd}")).unwrap_or_default()
}

/// Runs one entry point: the status code, with the message stored on failure.
fn run(f: impl FnOnce() -> Res<()>) -> c_int {
    let fail = match catch_unwind(AssertUnwindSafe(f)) {
        Ok(Ok(())) => return BW_OK,
        Ok(Err(fail)) => fail,
        Err(panic) => {
            let what = panic
                .downcast_ref::<&str>()
                .map(|s| s.to_string())
                .or_else(|| panic.downcast_ref::<String>().cloned())
                .unwrap_or_default();
            Fail(BW_ERR_PANIC, format!("bitwright panicked: {what}"))
        }
    };
    LAST_ERROR.with(|l| *l.borrow_mut() = c_string(fail.1));
    fail.0
}

/// Runs a constructor: the object, or NULL with the message stored.
fn run_new<T>(f: impl FnOnce() -> Res<T>) -> *mut T {
    let mut out = None;
    run(|| {
        out = Some(f()?);
        Ok(())
    });
    out.map_or(core::ptr::null_mut(), |v| Box::into_raw(Box::new(v)))
}

// ----- pointers -------------------------------------------------------------------------------

/// `p` as a shared reference.
///
/// # Safety
/// `p` is NULL or valid for reads as a `T` for `'a`.
unsafe fn get<'a, T>(p: *const T, what: &str) -> Res<&'a T> {
    unsafe { p.as_ref() }.ok_or_else(|| invalid(format!("`{what}` is NULL")))
}

/// `p` as an exclusive reference.
///
/// # Safety
/// `p` is NULL or valid for reads and writes as a `T` for `'a`, and not otherwise referenced.
unsafe fn get_mut<'a, T>(p: *mut T, what: &str) -> Res<&'a mut T> {
    unsafe { p.as_mut() }.ok_or_else(|| invalid(format!("`{what}` is NULL")))
}

/// An output parameter, checked before any work so that a NULL one fails without effects.
struct Out<T>(*mut T);

impl<T> Out<T> {
    fn new(p: *mut T, what: &str) -> Res<Out<T>> {
        if p.is_null() {
            Err(invalid(format!("`{what}` is NULL")))
        } else {
            Ok(Out(p))
        }
    }

    /// # Safety
    /// The pointer is valid for writes as a `T` (it may be uninitialized).
    unsafe fn set(self, v: T) {
        unsafe { self.0.write(v) }
    }
}

/// `n` elements at `p`, which may be NULL when `n` is 0.
///
/// # Safety
/// `p` is NULL or valid for reads of `n` elements for `'a`.
unsafe fn slice<'a, T>(p: *const T, n: usize, what: &str) -> Res<&'a [T]> {
    if n == 0 {
        Ok(&[])
    } else if p.is_null() {
        Err(invalid(format!("`{what}` is NULL")))
    } else {
        Ok(unsafe { core::slice::from_raw_parts(p, n) })
    }
}

/// A NUL-terminated UTF-8 string.
///
/// # Safety
/// `p` is NULL or a NUL-terminated string valid for `'a`.
unsafe fn text<'a>(p: *const c_char, what: &str) -> Res<&'a str> {
    if p.is_null() {
        return Err(invalid(format!("`{what}` is NULL")));
    }
    unsafe { CStr::from_ptr(p) }
        .to_str()
        .map_err(|e| invalid(format!("`{what}` is not UTF-8: {e}")))
}

/// Hands a string to C (released with `bw_string_free`).
fn give(s: impl Into<String>) -> *mut c_char {
    c_string(s).into_raw()
}

// ----- values and handles ---------------------------------------------------------------------

const LIMBS: usize = 8;

/// `bw_value`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BwValue {
    width: u16,
    limbs: [u64; LIMBS],
}

fn width(bits: u16) -> Res<Width> {
    Ok(Width::new(bits)?)
}

fn bitvec(v: &BwValue) -> Res<BitVec> {
    let w = width(v.width)?;
    Ok(BitVec::from_limbs(w, &v.limbs)?)
}

fn value(v: &BitVec) -> BwValue {
    let mut limbs = [0; LIMBS];
    limbs[..v.limbs().len()].copy_from_slice(v.limbs());
    BwValue {
        width: v.width().bits(),
        limbs,
    }
}

fn expr(bits: u64) -> Res<Expr> {
    Expr::from_bits(bits).ok_or_else(|| Fail(BW_ERR_FOREIGN_EXPR, "the null handle".into()))
}

fn exprs(bits: &[u64]) -> Res<Vec<Expr>> {
    bits.iter().map(|&b| expr(b)).collect()
}

/// A reliance as the mask of `bitwright.h`: bit `i` for constraint `i < 63`, bit 63 for the
/// rest.
fn mask(r: Reliance) -> u64 {
    let (ids, rest) = r.indices();
    ids.fold(u64::from(rest) << 63, |m, i| m | 1 << i)
}

// ----- objects --------------------------------------------------------------------------------

/// `bw_context`.
#[derive(Debug, Default)]
pub struct BwContext {
    cx: Context,
}

/// `bw_assumptions`.
#[derive(Debug, Default)]
pub struct BwAssumptions {
    a: Assumptions,
}

/// `bw_engine`.
#[derive(Debug)]
pub struct BwEngine {
    engine: Engine,
}

/// `bw_engine_builder`.
#[derive(Debug)]
pub struct BwEngineBuilder {
    preset: c_int,
    programs: Vec<(RuleProgram, Ledger)>,
    max_rounds: Option<u8>,
}

/// `bw_smt_import`.
#[derive(Debug, Default)]
pub struct BwSmtImport {
    symbols: Vec<(CString, u64)>,
    definitions: Vec<(CString, u64)>,
    assertions: Vec<u64>,
}

// ----- general --------------------------------------------------------------------------------

#[unsafe(no_mangle)]
pub extern "C" fn bw_last_error() -> *const c_char {
    LAST_ERROR.with(|l| l.borrow().as_ptr())
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_abi_version() -> u32 {
    ABI_VERSION
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_version() -> *const c_char {
    concat!(env!("CARGO_PKG_VERSION"), "\0").as_ptr().cast()
}

/// # Safety
/// `s` is NULL or a string returned by this library, not yet released.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_string_free(s: *mut c_char) {
    if !s.is_null() {
        drop(unsafe { CString::from_raw(s) });
    }
}

// ----- contexts -------------------------------------------------------------------------------

#[unsafe(no_mangle)]
pub extern "C" fn bw_context_new() -> *mut BwContext {
    run_new(|| Ok(BwContext::default()))
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_context_new_with(max_nodes: u32, fact_work: u32) -> *mut BwContext {
    run_new(|| {
        let mut config = ContextConfig::default();
        if max_nodes != 0 {
            config = config.with_max_nodes(max_nodes);
        }
        if fact_work != 0 {
            config = config.with_fact_work(fact_work);
        }
        Ok(BwContext {
            cx: Context::with_config(config),
        })
    })
}

/// # Safety
/// `cx` is NULL or a context from `bw_context_new*`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_context_free(cx: *mut BwContext) {
    if !cx.is_null() {
        drop(unsafe { Box::from_raw(cx) });
    }
}

/// # Safety
/// `cx` is NULL or a live context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_context_clear(cx: *mut BwContext) {
    if let Some(cx) = unsafe { cx.as_mut() } {
        run(|| {
            cx.cx.clear();
            Ok(())
        });
    }
}

/// # Safety
/// `cx` is NULL or a live context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_context_len(cx: *const BwContext) -> usize {
    unsafe { cx.as_ref() }.map_or(0, |cx| cx.cx.len())
}

// ----- building -------------------------------------------------------------------------------

/// The shape of every constructor: a context, an output handle, and the construction.
///
/// # Safety
/// `cx` is NULL or a live context; `out` is NULL or valid for writes.
unsafe fn build(
    cx: *mut BwContext,
    out: *mut u64,
    f: impl FnOnce(&mut Context) -> Res<Expr>,
) -> c_int {
    run(|| {
        let cx = unsafe { get_mut(cx, "cx") }?;
        let out = Out::new(out, "out")?;
        let e = f(&mut cx.cx)?;
        unsafe { out.set(e.to_bits()) };
        Ok(())
    })
}

/// # Safety
/// `cx` is a live context, `name` a string, `out` valid for writes (NULL is reported).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_symbol(
    cx: *mut BwContext,
    name: *const c_char,
    w: u16,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let name = text(name, "name")?;
            Ok(cx.symbol(name, width(w)?)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_symbol_u64(
    cx: *mut BwContext,
    key: u64,
    w: u16,
    out: *mut u64,
) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.symbol(key, width(w)?)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_fresh_symbol(cx: *mut BwContext, w: u16, out: *mut u64) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.fresh_symbol(width(w)?)?)) }
}

/// # Safety
/// As `bw_symbol`; `v` is a readable `bw_value`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_const(cx: *mut BwContext, v: *const BwValue, out: *mut u64) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let v = bitvec(get(v, "v")?)?;
            Ok(cx.constant(&v)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_const_u64(cx: *mut BwContext, w: u16, v: u64, out: *mut u64) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.constant_u64(width(w)?, v)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_const_i64(cx: *mut BwContext, w: u16, v: i64, out: *mut u64) -> c_int {
    unsafe {
        build(
            cx,
            out,
            |cx| Ok(cx.constant_i128(width(w)?, i128::from(v))?),
        )
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_un(cx: *mut BwContext, op: c_int, a: u64, out: *mut u64) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let op = table(&UNOPS, op, "unary operator")?;
            Ok(cx.un(op, expr(a)?)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_bin(
    cx: *mut BwContext,
    op: c_int,
    a: u64,
    b: u64,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let op = table(&BINOPS, op, "binary operator")?;
            Ok(cx.bin(op, expr(a)?, expr(b)?)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_cmp(
    cx: *mut BwContext,
    op: c_int,
    a: u64,
    b: u64,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let op = table(&CMPOPS, op, "comparison")?;
            Ok(cx.cmp(op, expr(a)?, expr(b)?)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_zext(cx: *mut BwContext, a: u64, w: u16, out: *mut u64) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.zext(expr(a)?, width(w)?)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_sext(cx: *mut BwContext, a: u64, w: u16, out: *mut u64) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.sext(expr(a)?, width(w)?)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_trunc(cx: *mut BwContext, a: u64, w: u16, out: *mut u64) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.trunc(expr(a)?, width(w)?)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_extract(
    cx: *mut BwContext,
    a: u64,
    lo: u16,
    len: u16,
    out: *mut u64,
) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.extract(expr(a)?, lo, width(len)?)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_concat(cx: *mut BwContext, hi: u64, lo: u64, out: *mut u64) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.concat(expr(hi)?, expr(lo)?)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_select(
    cx: *mut BwContext,
    cond: u64,
    then: u64,
    els: u64,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            Ok(cx.select(expr(cond)?, expr(then)?, expr(els)?)?)
        })
    }
}

// ----- text -----------------------------------------------------------------------------------

/// # Safety
/// As `bw_symbol`; `src` is a string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_parse(
    cx: *mut BwContext,
    src: *const c_char,
    default_width: u16,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let src = text(src, "text")?;
            let opts = if default_width == 0 {
                ParseOptions::default()
            } else {
                ParseOptions::width(width(default_width)?)
            };
            Ok(cx.parse(src, &opts)?)
        })
    }
}

/// # Safety
/// `cx` is a live context and `out` valid for writes (NULL is reported).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_print(
    cx: *const BwContext,
    e: u64,
    flags: c_uint,
    out: *mut *mut c_char,
) -> c_int {
    run(|| {
        let cx = &unsafe { get(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let e = expr(e)?;
        cx.width(e)?;
        let opts = PrintOptions::default()
            .with_lets(flags & PRINT_NO_LETS == 0)
            .with_symbol_widths(flags & PRINT_SYMBOL_WIDTHS != 0);
        let s = cx.display_with(e, opts).to_string();
        unsafe { out.set(give(s)) };
        Ok(())
    })
}

// ----- inspecting -----------------------------------------------------------------------------

/// `bw_node`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BwNode {
    kind: c_int,
    op: c_int,
    width: u16,
    lo: u16,
    n_children: u32,
    children: [u64; 3],
}

fn node(cx: &Context, e: Expr) -> Res<BwNode> {
    let mut n = BwNode {
        kind: 0,
        op: -1,
        width: cx.width(e)?.bits(),
        lo: 0,
        n_children: 0,
        children: [0; 3],
    };
    let kids = |n: &mut BwNode, kind: c_int, es: &[Expr]| {
        n.kind = kind;
        n.n_children = es.len() as u32;
        for (d, s) in n.children.iter_mut().zip(es) {
            *d = s.to_bits();
        }
    };
    match cx.view(e)? {
        View::Const(_) => kids(&mut n, KIND_CONST, &[]),
        View::Sym(_) => kids(&mut n, KIND_SYMBOL, &[]),
        View::Un(op, a) => {
            kids(&mut n, KIND_UNARY, &[a]);
            n.op = code_of(&UNOPS, &op);
        }
        View::Bin(op, a, b) => {
            kids(&mut n, KIND_BINARY, &[a, b]);
            n.op = code_of(&BINOPS, &op);
        }
        View::Cmp(op, a, b) => {
            kids(&mut n, KIND_COMPARE, &[a, b]);
            let ext = match op {
                CmpOp::Eq => CmpOpExt::Eq,
                CmpOp::Ne => CmpOpExt::Ne,
                CmpOp::Ult => CmpOpExt::Ult,
                CmpOp::Ule => CmpOpExt::Ule,
                CmpOp::Slt => CmpOpExt::Slt,
                CmpOp::Sle => CmpOpExt::Sle,
                _ => return Err(Fail(BW_ERR_UNSUPPORTED, format!("comparison {op:?}"))),
            };
            n.op = code_of(&CMPOPS, &ext);
        }
        View::Zext(a) => kids(&mut n, KIND_ZEXT, &[a]),
        View::Sext(a) => kids(&mut n, KIND_SEXT, &[a]),
        View::Extract { lo, src } => {
            kids(&mut n, KIND_EXTRACT, &[src]);
            n.lo = lo;
        }
        View::Concat { hi, lo } => kids(&mut n, KIND_CONCAT, &[hi, lo]),
        View::Select { cond, then, els } => kids(&mut n, KIND_SELECT, &[cond, then, els]),
        View::Ext { output, args, .. } => {
            kids(&mut n, KIND_EXT, args.as_slice());
            n.lo = u16::from(output);
        }
        View::Fp { op, args, .. } => {
            kids(&mut n, KIND_FP, args.as_slice());
            n.op = fp_code(op)?;
        }
        other => return Err(Fail(BW_ERR_UNSUPPORTED, format!("node {other:?}"))),
    }
    Ok(n)
}

/// # Safety
/// `cx` is a live context and `out` valid for writes (NULL is reported).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_node_of(cx: *const BwContext, e: u64, out: *mut BwNode) -> c_int {
    run(|| {
        let cx = &unsafe { get(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let n = node(cx, expr(e)?)?;
        unsafe { out.set(n) };
        Ok(())
    })
}

/// # Safety
/// As `bw_node_of`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_width(cx: *const BwContext, e: u64, out: *mut u16) -> c_int {
    run(|| {
        let cx = &unsafe { get(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let w = cx.width(expr(e)?)?;
        unsafe { out.set(w.bits()) };
        Ok(())
    })
}

/// # Safety
/// As `bw_node_of`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_const_value(cx: *const BwContext, e: u64, out: *mut BwValue) -> c_int {
    run(|| {
        let cx = &unsafe { get(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let v = cx
            .as_const(expr(e)?)?
            .ok_or_else(|| invalid("not a constant"))?;
        unsafe { out.set(value(&v)) };
        Ok(())
    })
}

/// The name of a symbol key: the string itself, or its printed form for the other keys.
fn key_name(key: &SymbolKey) -> String {
    match key {
        SymbolKey::Str(s) => s.to_string(),
        other => other.to_string(),
    }
}

/// # Safety
/// As `bw_node_of`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_symbol_name(
    cx: *const BwContext,
    e: u64,
    out: *mut *mut c_char,
) -> c_int {
    run(|| {
        let cx = &unsafe { get(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let key = cx
            .symbol_id(expr(e)?)?
            .and_then(|id| cx.symbol_key(id))
            .ok_or_else(|| invalid("not a symbol"))?;
        unsafe { out.set(give(key_name(key))) };
        Ok(())
    })
}

/// # Safety
/// As `bw_node_of`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_dag_size(cx: *mut BwContext, e: u64, out: *mut u32) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let n = match cx.dag_size(&[expr(e)?], u32::MAX - 1)? {
            Bounded::Exact(n) | Bounded::AtLeast(n) => n,
            _ => u32::MAX,
        };
        unsafe { out.set(n) };
        Ok(())
    })
}

// ----- floating point -------------------------------------------------------------------------

/// `bw_fp_format`.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BwFpFormat {
    eb: u32,
    sb: u32,
}

/// The format `f` describes, if it is valid (`BW_ERR_WIDTH` otherwise).
fn fp_format(f: BwFpFormat) -> Res<FpFormat> {
    Ok(FpFormat::new(f.eb, f.sb)?)
}

fn c_format(f: FpFormat) -> BwFpFormat {
    BwFpFormat {
        eb: f.eb(),
        sb: f.sb(),
    }
}

const NO_FORMAT: BwFpFormat = BwFpFormat { eb: 0, sb: 0 };

/// The operation named `name` (of `FPOPS`) with its attributes; each attribute is read only by
/// the operations that have it.
fn fp_op(name: &str, rm: c_int, to: BwFpFormat, int_width: u16) -> Res<FpOp> {
    let rm = || table(&ROUNDINGS, rm, "rounding mode");
    Ok(match name {
        "add" => FpOp::Add(rm()?),
        "mul" => FpOp::Mul(rm()?),
        "div" => FpOp::Div(rm()?),
        "fma" => FpOp::Fma(rm()?),
        "sqrt" => FpOp::Sqrt(rm()?),
        "rem" => FpOp::Rem,
        "round" => FpOp::RoundToIntegral(rm()?),
        "min" => FpOp::Min,
        "max" => FpOp::Max,
        "eq" => FpOp::Eq,
        "lt" => FpOp::Lt,
        "le" => FpOp::Le,
        "convert" => FpOp::Convert {
            to: fp_format(to)?,
            rm: rm()?,
        },
        "from_sbv" => FpOp::FromSInt(rm()?),
        "from_ubv" => FpOp::FromUInt(rm()?),
        "to_sbv" => FpOp::ToSInt(rm()?, width(int_width)?),
        "to_ubv" => FpOp::ToUInt(rm()?, width(int_width)?),
        other => unreachable!("`{other}` is not in FPOPS"),
    })
}

/// The `bw_fpop` of an operation.
fn fp_code(op: FpOp) -> Res<c_int> {
    let name = match op {
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
        other => {
            return Err(Fail(
                BW_ERR_UNSUPPORTED,
                format!("floating-point operation {other:?}"),
            ));
        }
    };
    known_code(&FPOPS, &name)
}

/// # Safety
/// As `bw_symbol`; `args` holds `n` handles.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)] // bitwright.h's signature
pub unsafe extern "C" fn bw_fp(
    cx: *mut BwContext,
    op: c_int,
    rm: c_int,
    format: BwFpFormat,
    args: *const u64,
    n: usize,
    to: BwFpFormat,
    int_width: u16,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let name = table(&FPOPS, op, "floating-point operation")?;
            let op = fp_op(name, rm, to, int_width)?;
            let format = fp_format(format)?;
            let args = exprs(slice(args, n, "args")?)?;
            if args.len() != op.arity() {
                return Err(invalid(format!(
                    "`fp.{name}` takes {} operands, not {n}",
                    op.arity()
                )));
            }
            Ok(cx.fp(op, format, &args)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_fp_sub(
    cx: *mut BwContext,
    rm: c_int,
    format: BwFpFormat,
    a: u64,
    b: u64,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let rm = table(&ROUNDINGS, rm, "rounding mode")?;
            Ok(cx.fp_sub(fp_format(format)?, rm, expr(a)?, expr(b)?)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_fp_neg(
    cx: *mut BwContext,
    format: BwFpFormat,
    a: u64,
    out: *mut u64,
) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.fp_neg(fp_format(format)?, expr(a)?)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_fp_abs(
    cx: *mut BwContext,
    format: BwFpFormat,
    a: u64,
    out: *mut u64,
) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.fp_abs(fp_format(format)?, expr(a)?)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_fp_copysign(
    cx: *mut BwContext,
    format: BwFpFormat,
    a: u64,
    b: u64,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            Ok(cx.fp_copysign(fp_format(format)?, expr(a)?, expr(b)?)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_fp_cmp(
    cx: *mut BwContext,
    op: c_int,
    format: BwFpFormat,
    a: u64,
    b: u64,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let op = table(&FPCMPS, op, "floating-point comparison")?;
            Ok(cx.fp_cmp(fp_format(format)?, op, expr(a)?, expr(b)?)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_fp_test(
    cx: *mut BwContext,
    test: c_int,
    format: BwFpFormat,
    a: u64,
    out: *mut u64,
) -> c_int {
    unsafe {
        build(cx, out, |cx| {
            let t = table(&FPTESTS, test, "floating-point test")?;
            Ok(cx.fp_test(fp_format(format)?, t, expr(a)?)?)
        })
    }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_x87_load(cx: *mut BwContext, a: u64, out: *mut u64) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.x87_load(expr(a)?)?)) }
}

/// # Safety
/// As `bw_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_x87_store(cx: *mut BwContext, a: u64, out: *mut u64) -> c_int {
    unsafe { build(cx, out, |cx| Ok(cx.x87_store(expr(a)?)?)) }
}

/// `bw_fp_node`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BwFpNode {
    op: c_int,
    rm: c_int,
    format: BwFpFormat,
    to: BwFpFormat,
    int_width: u16,
}

/// # Safety
/// As `bw_node_of`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_fp_node_of(cx: *const BwContext, e: u64, out: *mut BwFpNode) -> c_int {
    run(|| {
        let cx = &unsafe { get(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let View::Fp { op, format, .. } = cx.view(expr(e)?)? else {
            return Err(invalid("not a floating-point node"));
        };
        let (to, int_width) = match op {
            FpOp::Convert { to, .. } => (c_format(to), 0),
            FpOp::ToSInt(_, w) | FpOp::ToUInt(_, w) => (NO_FORMAT, w.bits()),
            _ => (NO_FORMAT, 0),
        };
        let rm = match op.rounding_mode() {
            Some(rm) => known_code(&ROUNDINGS, &rm)?,
            None => -1,
        };
        let n = BwFpNode {
            op: fp_code(op)?,
            rm,
            format: c_format(format),
            to,
            int_width,
        };
        unsafe { out.set(n) };
        Ok(())
    })
}

// ----- evaluating and substituting ------------------------------------------------------------

/// # Safety
/// `cx` is a live context, `symbols` and `values` hold `n` elements, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_eval(
    cx: *mut BwContext,
    e: u64,
    symbols: *const u64,
    values: *const BwValue,
    n: usize,
    out: *mut BwValue,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let symbols = unsafe { slice(symbols, n, "symbols") }?;
        let values = unsafe { slice(values, n, "values") }?;
        let out = Out::new(out, "out")?;
        let mut env = HashMap::with_capacity(n);
        for (i, (&s, v)) in symbols.iter().zip(values).enumerate() {
            let key = cx
                .symbol_id(expr(s)?)?
                .and_then(|id| cx.symbol_key(id))
                .ok_or_else(|| invalid(format!("`symbols[{i}]` is not a symbol")))?;
            env.insert(key.clone(), bitvec(v)?);
        }
        let v = cx.eval(&[expr(e)?], &env)?;
        unsafe { out.set(value(&v[0])) };
        Ok(())
    })
}

/// # Safety
/// `cx` is a live context, `from` and `to` hold `n` elements, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_substitute(
    cx: *mut BwContext,
    e: u64,
    from: *const u64,
    to: *const u64,
    n: usize,
    out: *mut u64,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let from = exprs(unsafe { slice(from, n, "from") }?)?;
        let to = exprs(unsafe { slice(to, n, "to") }?)?;
        let out = Out::new(out, "out")?;
        let map: Vec<(Expr, Expr)> = from.into_iter().zip(to).collect();
        let r = cx.substitute(&[expr(e)?], &map)?;
        unsafe { out.set(r[0].to_bits()) };
        Ok(())
    })
}

// ----- assumptions ----------------------------------------------------------------------------

#[unsafe(no_mangle)]
pub extern "C" fn bw_assumptions_new() -> *mut BwAssumptions {
    run_new(|| Ok(BwAssumptions::default()))
}

/// # Safety
/// `a` is NULL or an assumption set from `bw_assumptions_new`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_assumptions_free(a: *mut BwAssumptions) {
    if !a.is_null() {
        drop(unsafe { Box::from_raw(a) });
    }
}

/// # Safety
/// `a` and `cx` are live; `id` is NULL or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_assume(
    a: *mut BwAssumptions,
    cx: *mut BwContext,
    p: u64,
    holds: bool,
    id: *mut u32,
) -> c_int {
    run(|| {
        let a = &mut unsafe { get_mut(a, "a") }?.a;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let p = expr(p)?;
        let c = if holds {
            a.assume_true(cx, p)?
        } else {
            a.assume_false(cx, p)?
        };
        if !id.is_null() {
            unsafe { id.write(c.index()) };
        }
        Ok(())
    })
}

/// # Safety
/// `a` is NULL or live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_assumptions_infeasible(a: *const BwAssumptions) -> bool {
    unsafe { a.as_ref() }.is_some_and(|a| a.a.is_infeasible())
}

/// # Safety
/// `a` is NULL or live.
unsafe fn assumptions<'a>(a: *const BwAssumptions) -> Option<&'a Assumptions> {
    unsafe { a.as_ref() }.map(|a| &a.a)
}

// ----- facts and proofs -----------------------------------------------------------------------

/// `bw_facts`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BwFacts {
    known_zero: BwValue,
    known_one: BwValue,
    umin: BwValue,
    umax: BwValue,
    ustride: u64,
    smin: BwValue,
    smax: BwValue,
    relies_on: u64,
}

/// # Safety
/// `cx` is live, `a` is NULL or live, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_facts_of(
    cx: *mut BwContext,
    e: u64,
    a: *const BwAssumptions,
    out: *mut BwFacts,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let a = unsafe { assumptions(a) };
        let out = Out::new(out, "out")?;
        let e = expr(e)?;
        let (f, r) = match a {
            None => (cx.facts(e)?, Reliance::NONE),
            Some(a) => cx.facts_under(e, a)?.ok_or_else(infeasible)?,
        };
        let (k, u, s) = (f.known(), f.urange(), f.srange());
        unsafe {
            out.set(BwFacts {
                known_zero: value(&k.known_zero()),
                known_one: value(&k.known_one()),
                umin: value(&u.lo()),
                umax: value(&u.hi()),
                ustride: u.stride(),
                smin: value(&s.lo()),
                smax: value(&s.hi()),
                relies_on: mask(r),
            })
        };
        Ok(())
    })
}

fn infeasible() -> Fail {
    Fail(
        BW_ERR_INFEASIBLE,
        "the assumptions contradict each other".into(),
    )
}

/// `bw_proof`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BwProof {
    truth: c_int,
    relies_on: u64,
}

/// Answers `q`, under `a` when given.
///
/// # Safety
/// `cx` is live, `a` is NULL or live, `out` is valid for writes.
unsafe fn prove(
    cx: *mut BwContext,
    a: *const BwAssumptions,
    out: *mut BwProof,
    q: impl FnOnce() -> Res<Query<'static>>,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let a = unsafe { assumptions(a) };
        let out = Out::new(out, "out")?;
        let q = q()?;
        let (truth, r) = match a {
            None => (cx.prove(q)?, Reliance::NONE),
            Some(a) => {
                let p = cx.prove_under(q, a)?;
                (p.truth, p.relies_on)
            }
        };
        let truth = match truth {
            Truth::False => 0,
            Truth::True => 1,
            Truth::Unknown => 2,
        };
        unsafe {
            out.set(BwProof {
                truth,
                relies_on: mask(r),
            })
        };
        Ok(())
    })
}

/// # Safety
/// `cx` is live, `a` is NULL or live, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_prove(
    cx: *mut BwContext,
    e: u64,
    a: *const BwAssumptions,
    out: *mut BwProof,
) -> c_int {
    unsafe { prove(cx, a, out, || Ok(Query::IsNonZero(expr(e)?))) }
}

/// # Safety
/// As `bw_prove`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_prove_cmp(
    cx: *mut BwContext,
    op: c_int,
    x: u64,
    y: u64,
    a: *const BwAssumptions,
    out: *mut BwProof,
) -> c_int {
    unsafe {
        prove(cx, a, out, || {
            let op = table(&CMPOPS, op, "comparison")?;
            Ok(Query::Cmp(op, expr(x)?, expr(y)?))
        })
    }
}

/// # Safety
/// As `bw_prove`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_prove_injective(
    cx: *mut BwContext,
    e: u64,
    of: u64,
    bijective: bool,
    a: *const BwAssumptions,
    out: *mut BwProof,
) -> c_int {
    unsafe {
        prove(cx, a, out, || {
            let (e, of) = (expr(e)?, expr(of)?);
            Ok(if bijective {
                Query::Bijective { e, of }
            } else {
                Query::Injective { e, of }
            })
        })
    }
}

// ----- engines --------------------------------------------------------------------------------

/// The deobfuscation strategy of the command line's `simplify`: the MBA service, on bitwright's
/// own evidence only (with the native solver; see `BwEngineBuilder::build`).
fn deobfuscate_strategy() -> Strategy {
    let trust = MbaTrust::default().with_backend_certificates(false);
    Strategy::deobfuscate().with_mba(MbaConfig::default().with_trust(trust))
}

impl BwEngineBuilder {
    fn new(preset: c_int) -> Res<BwEngineBuilder> {
        if !matches!(preset, PRESET_STANDARD | PRESET_DEOBFUSCATE) {
            return Err(invalid(format!("unknown preset {preset}")));
        }
        Ok(BwEngineBuilder {
            preset,
            programs: Vec::new(),
            max_rounds: None,
        })
    }

    fn build(&self) -> Res<Engine> {
        let mut b = Engine::builder().builtin();
        let mut strategy = if self.preset == PRESET_DEOBFUSCATE {
            b = b.mba_solver(Arc::new(NormalFormSolver::default()));
            deobfuscate_strategy()
        } else {
            Strategy::standard()
        };
        let mut groups = Vec::new();
        for (program, ledger) in &self.programs {
            groups.extend(program.groups().iter().map(|g| g.name.clone()));
            b = b.program(program.clone(), ledger);
        }
        let groups: Vec<&str> = groups.iter().map(String::as_str).collect();
        if !groups.is_empty() {
            strategy = strategy.with_rule_groups(&groups);
        }
        if let Some(n) = self.max_rounds {
            strategy = strategy.with_max_rounds(n);
        }
        b.strategy(strategy)
            .build()
            .map_err(|e| Fail(BW_ERR_RULES, e.to_string()))
    }
}

/// The engine of a preset without rules of its own, built once per process.
fn preset_engine(preset: c_int) -> Res<Engine> {
    static DEOBFUSCATE: OnceLock<Engine> = OnceLock::new();
    match preset {
        PRESET_STANDARD => Ok(Engine::standard()),
        PRESET_DEOBFUSCATE => {
            if let Some(e) = DEOBFUSCATE.get() {
                return Ok(e.clone());
            }
            let e = BwEngineBuilder::new(preset)?.build()?;
            Ok(DEOBFUSCATE.get_or_init(|| e).clone())
        }
        _ => Err(invalid(format!("unknown preset {preset}"))),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_engine_new(preset: c_int) -> *mut BwEngine {
    run_new(|| {
        Ok(BwEngine {
            engine: preset_engine(preset)?,
        })
    })
}

/// # Safety
/// `e` is NULL or an engine from this library, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_free(e: *mut BwEngine) {
    if !e.is_null() {
        drop(unsafe { Box::from_raw(e) });
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_engine_builder_new(preset: c_int) -> *mut BwEngineBuilder {
    run_new(|| BwEngineBuilder::new(preset))
}

/// # Safety
/// `b` is NULL or a builder from `bw_engine_builder_new`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_builder_free(b: *mut BwEngineBuilder) {
    if !b.is_null() {
        drop(unsafe { Box::from_raw(b) });
    }
}

/// Compiles a `.bwr` source.
fn compile(source: &str) -> Res<RuleProgram> {
    RuleProgram::compile(source).map_err(|e| Fail(BW_ERR_RULES, e.to_string()))
}

/// Checks every rule of `program` and gives the ledger vouching for them all, or the first
/// rule that is not proven sound.
fn check(program: &RuleProgram) -> Res<Ledger> {
    let checks = check_program(program, &CheckConfig::default());
    for c in &checks {
        match &c.verdict {
            Verdict::Sound => {}
            Verdict::Unsound(cx) => {
                return Err(Fail(
                    BW_ERR_RULES,
                    format!("rule `{}` is unsound: {cx}", c.name),
                ));
            }
            Verdict::Inconclusive(why) => {
                return Err(Fail(
                    BW_ERR_RULES,
                    format!("rule `{}` is not proven sound: {why}", c.name),
                ));
            }
            other => {
                return Err(Fail(
                    BW_ERR_RULES,
                    format!("rule `{}` is not proven sound: {other:?}", c.name),
                ));
            }
        }
    }
    Ok(Ledger::from_checks(&checks))
}

/// # Safety
/// `b` is live, `source` is a string, `ledger` is NULL or a string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_builder_add_rules(
    b: *mut BwEngineBuilder,
    source: *const c_char,
    ledger: *const c_char,
) -> c_int {
    run(|| {
        let b = unsafe { get_mut(b, "b") }?;
        let program = compile(unsafe { text(source, "source") }?)?;
        let ledger = if ledger.is_null() {
            check(&program)?
        } else {
            Ledger::parse(unsafe { text(ledger, "ledger") }?)
                .map_err(|e| Fail(BW_ERR_RULES, format!("ledger: {e}")))?
        };
        b.programs.push((program, ledger));
        Ok(())
    })
}

/// # Safety
/// `b` is NULL or live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_builder_set_max_rounds(b: *mut BwEngineBuilder, rounds: u8) {
    if let Some(b) = unsafe { b.as_mut() } {
        b.max_rounds = Some(rounds);
    }
}

/// # Safety
/// `b` is live and `out` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_builder_build(
    b: *const BwEngineBuilder,
    out: *mut *mut BwEngine,
) -> c_int {
    run(|| {
        let b = unsafe { get(b, "b") }?;
        let out = Out::new(out, "out")?;
        let engine = if b.programs.is_empty() && b.max_rounds.is_none() {
            preset_engine(b.preset)?
        } else {
            b.build()?
        };
        unsafe { out.set(Box::into_raw(Box::new(BwEngine { engine }))) };
        Ok(())
    })
}

/// # Safety
/// `source` is a string and `out` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_check_rules(source: *const c_char, out: *mut *mut c_char) -> c_int {
    run(|| {
        let program = compile(unsafe { text(source, "source") }?)?;
        let out = Out::new(out, "ledger")?;
        let ledger = check(&program)?;
        unsafe { out.set(give(ledger.render())) };
        Ok(())
    })
}

// ----- simplifying ----------------------------------------------------------------------------

/// `bw_budget`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BwBudget {
    node_visits: u64,
    candidates: u64,
    match_steps: u64,
    rewrites: u64,
    new_nodes: u64,
    fact_work: u64,
    pass_work: u64,
    mba_calls: u64,
    eqsat_nodes: u64,
    eqsat_work: u64,
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_budget_default() -> BwBudget {
    let b = Budget::default();
    BwBudget {
        node_visits: b.node_visits,
        candidates: b.candidates,
        match_steps: b.match_steps,
        rewrites: b.rewrites,
        new_nodes: b.new_nodes,
        fact_work: b.fact_work,
        pass_work: b.pass_work,
        mba_calls: b.mba_calls,
        eqsat_nodes: b.eqsat_nodes,
        eqsat_work: b.eqsat_work,
    }
}

fn budget(b: &BwBudget) -> Budget {
    Budget::default()
        .with_node_visits(b.node_visits)
        .with_candidates(b.candidates)
        .with_match_steps(b.match_steps)
        .with_rewrites(b.rewrites)
        .with_new_nodes(b.new_nodes)
        .with_fact_work(b.fact_work)
        .with_pass_work(b.pass_work)
        .with_mba_calls(b.mba_calls)
        .with_eqsat_nodes(b.eqsat_nodes)
        .with_eqsat_work(b.eqsat_work)
}

/// `bw_outcome`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BwOutcome {
    expr: u64,
    changed: bool,
    end: c_int,
    limit: c_int,
    relies_on: u64,
}

/// # Safety
/// `engine` and `cx` are live and `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_simplify(
    engine: *const BwEngine,
    cx: *mut BwContext,
    e: u64,
    out: *mut u64,
) -> c_int {
    run(|| {
        let engine = &unsafe { get(engine, "engine") }?.engine;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let r = engine.simplify(cx, expr(e)?)?;
        unsafe { out.set(r.expr.to_bits()) };
        Ok(())
    })
}

/// # Safety
/// `engine` and `cx` are live, `roots` holds and `outcomes` has room for `n` elements, `budget`
/// and `a` are NULL or valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_run(
    engine: *const BwEngine,
    cx: *mut BwContext,
    roots: *const u64,
    n: usize,
    b: *const BwBudget,
    a: *const BwAssumptions,
    outcomes: *mut BwOutcome,
) -> c_int {
    run(|| {
        let engine = &unsafe { get(engine, "engine") }?.engine;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let roots = exprs(unsafe { slice(roots, n, "roots") }?)?;
        let per_call = match unsafe { b.as_ref() } {
            Some(b) => budget(b),
            None => Budget::default(),
        };
        let a = unsafe { assumptions(a) };
        if n > 0 && outcomes.is_null() {
            return Err(invalid("`outcomes` is NULL"));
        }
        let mut options = Run::default().with_per_call(per_call);
        if let Some(a) = a {
            options = options.with_assumptions(a);
        }
        let out = engine.run(cx, &roots, options)?;
        for (i, r) in out.roots.iter().enumerate() {
            let (end, limit) = match r.end {
                End::Completed => (0, -1),
                End::BudgetTerminated(x) => (1, code_of(&LIMITS, &x)),
                _ => (2, -1),
            };
            let o = BwOutcome {
                expr: r.expr.to_bits(),
                changed: r.changed,
                end,
                limit,
                relies_on: mask(r.relies_on),
            };
            unsafe { outcomes.add(i).write(o) };
        }
        Ok(())
    })
}

// ----- SMT-LIB --------------------------------------------------------------------------------

/// # Safety
/// `cx` is live, `roots` holds `n` elements, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_smtlib_export(
    cx: *mut BwContext,
    roots: *const u64,
    n: usize,
    out: *mut *mut c_char,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let roots = exprs(unsafe { slice(roots, n, "roots") }?)?;
        let out = Out::new(out, "out")?;
        let s = bw::smtlib::export(cx, &roots)?;
        unsafe { out.set(give(s)) };
        Ok(())
    })
}

/// # Safety
/// `cx` is live, `script` is a string, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_smtlib_import(
    cx: *mut BwContext,
    script: *const c_char,
    out: *mut *mut BwSmtImport,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let script = unsafe { text(script, "script") }?;
        let out = Out::new(out, "out")?;
        let imp = bw::smtlib::import(cx, script)?;
        let named = |v: Vec<(String, Expr)>| {
            v.into_iter()
                .map(|(n, e)| (c_string(n), e.to_bits()))
                .collect()
        };
        let imp = BwSmtImport {
            symbols: named(imp.symbols),
            definitions: named(imp.definitions),
            assertions: imp.assertions.iter().map(|e| e.to_bits()).collect(),
        };
        unsafe { out.set(Box::into_raw(Box::new(imp))) };
        Ok(())
    })
}

/// # Safety
/// `imp` is NULL or an import from `bw_smtlib_import`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_smt_import_free(imp: *mut BwSmtImport) {
    if !imp.is_null() {
        drop(unsafe { Box::from_raw(imp) });
    }
}

/// # Safety
/// `imp` is NULL or live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_smt_import_count(imp: *const BwSmtImport, part: c_int) -> usize {
    let Some(imp) = (unsafe { imp.as_ref() }) else {
        return 0;
    };
    match part {
        SMT_SYMBOLS => imp.symbols.len(),
        SMT_DEFINITIONS => imp.definitions.len(),
        SMT_ASSERTIONS => imp.assertions.len(),
        _ => 0,
    }
}

/// # Safety
/// `imp` is live; `e` and `name` are NULL or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_smt_import_get(
    imp: *const BwSmtImport,
    part: c_int,
    i: usize,
    e: *mut u64,
    name: *mut *const c_char,
) -> c_int {
    run(|| {
        let imp = unsafe { get(imp, "imp") }?;
        let (bits, n) = match part {
            SMT_SYMBOLS | SMT_DEFINITIONS => {
                let v = if part == SMT_SYMBOLS {
                    &imp.symbols
                } else {
                    &imp.definitions
                };
                let (n, bits) = v
                    .get(i)
                    .ok_or_else(|| invalid(format!("index {i} is out of range")))?;
                (*bits, n.as_ptr())
            }
            SMT_ASSERTIONS => {
                let bits = imp
                    .assertions
                    .get(i)
                    .ok_or_else(|| invalid(format!("index {i} is out of range")))?;
                (*bits, core::ptr::null())
            }
            _ => return Err(invalid(format!("unknown part {part}"))),
        };
        if !e.is_null() {
            unsafe { e.write(bits) };
        }
        if !name.is_null() {
            unsafe { name.write(n) };
        }
        Ok(())
    })
}
