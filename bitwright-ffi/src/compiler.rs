//! What a compiler needs beyond simplifying text (bitwright.h, "in a compiler"): declared known
//! bits, the compile strategy's options, host rewrites as C callbacks with their checker,
//! semantics templates, and lowering a host's values into expressions and raising results back.

use core::ffi::{c_char, c_int, c_void};
use std::ffi::CString;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use bw::check::{RewriteCheckConfig, RewriteFailure};
use bw::engine::{Rewrite, Site};
use bw::translate::{Lowered, Raise, Template};
use bw::{BitVec, Context, Error, Expr, KnownBits, View, Width};

use super::{
    BINOPS, BW_ERR_VALUE, BW_ERR_WIDTH, BwContext, BwEngineBuilder, BwFacts, BwNode, BwValue,
    CMPOPS, Fail, LAST_ERROR, Out, Res, SHARINGS, UNOPS, bitvec, c_facts, c_string, expr, exprs,
    get, get_mut, give, invalid, node, run, run_new, slice, table, text, value, width,
};

// ----- contexts -------------------------------------------------------------------------------

/// # Safety
/// `cx` is NULL or live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_context_reserve(cx: *mut BwContext, additional: usize) {
    if let Some(cx) = unsafe { cx.as_mut() } {
        run(|| {
            cx.cx.reserve(additional);
            Ok(())
        });
    }
}

/// Known bits from the masks of the bits known to be 0 and to be 1.
fn known_bits(zero: BitVec, one: BitVec) -> Res<KnownBits> {
    KnownBits::new(zero, one).ok_or_else(|| {
        Fail(
            BW_ERR_VALUE,
            "a bit is declared both 0 and 1 (`zero & one` is not 0)".into(),
        )
    })
}

/// Declares `known` for symbol `sym` of `cx`.
fn declare(cx: &mut Context, sym: Expr, known: impl FnOnce(Width) -> Res<KnownBits>) -> Res<()> {
    if cx.symbol_id(sym)?.is_none() {
        return Err(invalid("known bits are declared for symbols only"));
    }
    let k = known(cx.width(sym)?)?;
    Ok(cx.declare_known(sym, k)?)
}

/// # Safety
/// `cx` is live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_declare_known(
    cx: *mut BwContext,
    sym: u64,
    zero: u64,
    one: u64,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        declare(cx, expr(sym)?, |w| {
            if w.bits() > 64 {
                return Err(Fail(
                    BW_ERR_WIDTH,
                    format!(
                        "the symbol has {} bits: declare with bw_declare_known_value",
                        w.bits()
                    ),
                ));
            }
            known_bits(BitVec::from_u64(w, zero)?, BitVec::from_u64(w, one)?)
        })
    })
}

/// # Safety
/// `cx` is live; `zero` and `one` are valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_declare_known_value(
    cx: *mut BwContext,
    sym: u64,
    zero: *const BwValue,
    one: *const BwValue,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let zero = bitvec(unsafe { get(zero, "zero") }?)?;
        let one = bitvec(unsafe { get(one, "one") }?)?;
        declare(cx, expr(sym)?, |w| {
            if zero.width() != w || one.width() != w {
                return Err(Fail(
                    BW_ERR_WIDTH,
                    format!(
                        "masks of {} and {} bits for a symbol of {} bits",
                        zero.width().bits(),
                        one.width().bits(),
                        w.bits()
                    ),
                ));
            }
            known_bits(zero, one)
        })
    })
}

/// # Safety
/// `cx` is live; `zero`, `one` and `has` are valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_declared_known(
    cx: *const BwContext,
    sym: u64,
    zero: *mut BwValue,
    one: *mut BwValue,
    has: *mut bool,
) -> c_int {
    run(|| {
        let cx = &unsafe { get(cx, "cx") }?.cx;
        let (zero, one) = (Out::new(zero, "zero")?, Out::new(one, "one")?);
        let has = Out::new(has, "has")?;
        let sym = expr(sym)?;
        if cx.symbol_id(sym)?.is_none() {
            return Err(invalid("not a symbol"));
        }
        let k = cx
            .declared_known(sym)?
            .unwrap_or_else(|| KnownBits::unknown(cx.width(sym).expect("checked")));
        let declared = !k.known().is_zero();
        unsafe {
            zero.set(value(&k.known_zero()));
            one.set(value(&k.known_one()));
            has.set(declared);
        }
        Ok(())
    })
}

// ----- the compile strategy's options ---------------------------------------------------------

/// # Safety
/// `b` is live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_builder_set_sharing(
    b: *mut BwEngineBuilder,
    sharing: c_int,
) -> c_int {
    run(|| {
        let b = unsafe { get_mut(b, "b") }?;
        b.sharing = Some(table(&SHARINGS, sharing, "sharing")?);
        Ok(())
    })
}

/// # Safety
/// `b` is NULL or live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_builder_set_max_region(b: *mut BwEngineBuilder, n: u32) {
    if let Some(b) = unsafe { b.as_mut() } {
        b.max_region = Some(n.max(1));
    }
}

// ----- host rewrites --------------------------------------------------------------------------

/// `bw_site`: a [`Site`] lent to a rewrite callback for the length of the call.
#[derive(Debug)]
pub struct BwSite {
    _private: [u8; 0],
}

type RewriteFn = unsafe extern "C" fn(*mut c_void, *mut BwSite, u64) -> u64;
type ReleaseFn = unsafe extern "C" fn(*mut c_void);

/// `bw_rewrite`.
#[repr(C)]
#[derive(Debug)]
pub struct BwRewrite {
    pub(crate) name: *const c_char,
    pub(crate) group: *const c_char,
    pub(crate) revision: u32,
    pub(crate) user: *mut c_void,
    pub(crate) rewrite: Option<RewriteFn>,
    pub(crate) release: Option<ReleaseFn>,
}

/// A C rewrite callback as a [`Rewrite`]. The strings are copied; `user` is released when the
/// last engine or builder holding it goes, if the rewrite was linked (not merely checked).
#[derive(Debug)]
pub(crate) struct HostRewrite {
    name: String,
    group: String,
    revision: u32,
    user: *mut c_void,
    f: RewriteFn,
    release: Option<ReleaseFn>,
}

// SAFETY: `bw_rewrite` requires the callback to be safe to call from any thread, concurrently,
// with its `user` pointer (bitwright.h says so), and `release` to be safe to call from any
// thread once.
unsafe impl Send for HostRewrite {}
unsafe impl Sync for HostRewrite {}

impl HostRewrite {
    /// Reads `bw_rewrite` `r`; `owned` when the library takes `user` over.
    ///
    /// # Safety
    /// `r` is NULL or valid, its strings NULL or NUL-terminated.
    unsafe fn new(r: *const BwRewrite, owned: bool) -> Res<HostRewrite> {
        let r = unsafe { get(r, "rewrite") }?;
        let name = unsafe { text(r.name, "rewrite->name") }?.to_string();
        let group = if r.group.is_null() {
            "host".to_string()
        } else {
            unsafe { text(r.group, "rewrite->group") }?.to_string()
        };
        let f = r
            .rewrite
            .ok_or_else(|| invalid("`rewrite->rewrite` is NULL"))?;
        Ok(HostRewrite {
            name,
            group,
            revision: r.revision,
            user: r.user,
            f,
            release: if owned { r.release } else { None },
        })
    }
}

impl Drop for HostRewrite {
    fn drop(&mut self) {
        if let Some(release) = self.release {
            unsafe { release(self.user) };
        }
    }
}

impl Rewrite for HostRewrite {
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
        let p: *mut Site<'_> = site;
        let r = unsafe { (self.f)(self.user, p.cast(), e.to_bits()) };
        Expr::from_bits(r)
    }
}

/// # Safety
/// `b` is live and `r` valid (see `bw_rewrite` in bitwright.h for what its fields promise).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_builder_add_rewrite(
    b: *mut BwEngineBuilder,
    r: *const BwRewrite,
    trusted: bool,
) -> c_int {
    run(|| {
        let b = unsafe { get_mut(b, "b") }?;
        let r = unsafe { HostRewrite::new(r, true) }?;
        b.rewrites.push((Arc::new(r), trusted));
        Ok(())
    })
}

/// The site behind `s`, for the length of a callback.
///
/// # Safety
/// `s` is NULL or the site a rewrite callback was given, during that call.
unsafe fn site<'a>(s: *mut BwSite) -> Option<&'a mut Site<'a>> {
    unsafe { s.cast::<Site<'a>>().as_mut() }
}

/// Runs a site accessor: its answer, or `None` for a NULL site or a panic (which must not
/// unwind into the callback). Nothing is written to `bw_last_error`.
fn quiet<T>(f: impl FnOnce() -> Option<T>) -> Option<T> {
    catch_unwind(AssertUnwindSafe(f)).ok().flatten()
}

/// Writes `v` to `out` when there is one: whether there was.
///
/// # Safety
/// `out` is NULL or valid for writes.
unsafe fn answer<T>(v: Option<T>, out: *mut T) -> bool {
    match v {
        Some(v) if !out.is_null() => {
            unsafe { out.write(v) };
            true
        }
        _ => false,
    }
}

/// # Safety
/// `s` is a callback's site; `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_node(s: *mut BwSite, e: u64, out: *mut BwNode) -> bool {
    let v = quiet(|| {
        let site = unsafe { site(s) }?;
        node(site.context(), Expr::from_bits(e)?).ok()
    });
    unsafe { answer(v, out) }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_width(s: *mut BwSite, e: u64) -> u16 {
    quiet(|| Some(unsafe { site(s) }?.width(Expr::from_bits(e)?)?.bits())).unwrap_or(0)
}

/// # Safety
/// `s` is a callback's site; `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_const_value(s: *mut BwSite, e: u64, out: *mut BwValue) -> bool {
    let v = quiet(|| Some(value(&unsafe { site(s) }?.as_const(Expr::from_bits(e)?)?)));
    unsafe { answer(v, out) }
}

/// # Safety
/// `s` is a callback's site; `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_as_u64(s: *mut BwSite, e: u64, out: *mut u64) -> bool {
    let v = quiet(|| unsafe { site(s) }?.as_u64(Expr::from_bits(e)?));
    unsafe { answer(v, out) }
}

/// # Safety
/// `s` is a callback's site; `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_facts(s: *mut BwSite, e: u64, out: *mut BwFacts) -> bool {
    let v = quiet(|| Some(c_facts(&unsafe { site(s) }?.facts(Expr::from_bits(e)?)?, 0)));
    unsafe { answer(v, out) }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_print(s: *mut BwSite, e: u64, flags: u32) -> *mut c_char {
    quiet(|| {
        let site = unsafe { site(s) }?;
        let e = Expr::from_bits(e)?;
        site.width(e)?;
        Some(super::print(site.context(), e, flags))
    })
    .map_or(core::ptr::null_mut(), give)
}

/// Runs a site construction: the new node's handle, or 0.
///
/// # Safety
/// `s` is NULL or a callback's site.
unsafe fn make(s: *mut BwSite, f: impl FnOnce(&mut Site<'_>) -> Option<Expr>) -> u64 {
    quiet(|| f(unsafe { site(s) }?)).map_or(0, Expr::to_bits)
}

/// # Safety
/// `s` is a callback's site; `v` is NULL or valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_const(s: *mut BwSite, v: *const BwValue) -> u64 {
    unsafe {
        make(s, |site| {
            let v = bitvec(v.as_ref()?).ok()?;
            site.constant(&v)
        })
    }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_const_u64(s: *mut BwSite, w: u16, v: u64) -> u64 {
    unsafe { make(s, |site| site.constant_u64(width(w).ok()?, v)) }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_un(s: *mut BwSite, op: c_int, a: u64) -> u64 {
    unsafe {
        make(s, |site| {
            let op = table(&UNOPS, op, "").ok()?;
            site.un(op, Expr::from_bits(a)?)
        })
    }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_bin(s: *mut BwSite, op: c_int, a: u64, b: u64) -> u64 {
    unsafe {
        make(s, |site| {
            let op = table(&BINOPS, op, "").ok()?;
            site.bin(op, Expr::from_bits(a)?, Expr::from_bits(b)?)
        })
    }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_cmp(s: *mut BwSite, op: c_int, a: u64, b: u64) -> u64 {
    unsafe {
        make(s, |site| {
            let op = table(&CMPOPS, op, "").ok()?;
            site.cmp(op, Expr::from_bits(a)?, Expr::from_bits(b)?)
        })
    }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_zext(s: *mut BwSite, a: u64, w: u16) -> u64 {
    unsafe { make(s, |site| site.zext(Expr::from_bits(a)?, width(w).ok()?)) }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_sext(s: *mut BwSite, a: u64, w: u16) -> u64 {
    unsafe { make(s, |site| site.sext(Expr::from_bits(a)?, width(w).ok()?)) }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_trunc(s: *mut BwSite, a: u64, w: u16) -> u64 {
    unsafe { make(s, |site| site.trunc(Expr::from_bits(a)?, width(w).ok()?)) }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_extract(s: *mut BwSite, a: u64, lo: u16, len: u16) -> u64 {
    unsafe {
        make(s, |site| {
            site.extract(Expr::from_bits(a)?, lo, width(len).ok()?)
        })
    }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_concat(s: *mut BwSite, hi: u64, lo: u64) -> u64 {
    unsafe {
        make(s, |site| {
            site.concat(Expr::from_bits(hi)?, Expr::from_bits(lo)?)
        })
    }
}

/// # Safety
/// `s` is a callback's site.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_select(s: *mut BwSite, c: u64, t: u64, f: u64) -> u64 {
    unsafe {
        make(s, |site| {
            site.select(
                Expr::from_bits(c)?,
                Expr::from_bits(t)?,
                Expr::from_bits(f)?,
            )
        })
    }
}

// ----- checking a rewrite ---------------------------------------------------------------------

/// `bw_rewrite_check`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BwRewriteCheck {
    pub(crate) widths: *const u16,
    pub(crate) n_widths: usize,
    pub(crate) variants: u32,
    pub(crate) max_exhaustive_bits: u32,
    pub(crate) samples: u32,
    pub(crate) seed: u64,
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_rewrite_check_default() -> BwRewriteCheck {
    let d = RewriteCheckConfig::default();
    BwRewriteCheck {
        widths: core::ptr::null(),
        n_widths: 0,
        variants: d.variants,
        max_exhaustive_bits: d.max_exhaustive_bits,
        samples: d.samples,
        seed: d.seed,
    }
}

/// `bw_rewrite_report`.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct BwRewriteReport {
    pub(crate) applications: u64,
    pub(crate) points: u64,
    pub(crate) exhaustive: u64,
}

pub(crate) const FAILURE_UNPARSABLE: c_int = 0;
pub(crate) const FAILURE_NEVER_APPLIED: c_int = 1;
pub(crate) const FAILURE_DIFFERS: c_int = 2;
pub(crate) const FAILURE_WIDTH: c_int = 3;
pub(crate) const FAILURE_NOT_SMALLER: c_int = 4;
pub(crate) const FAILURE_NONDETERMINISTIC: c_int = 5;
pub(crate) const FAILURE_FOREIGN_EXPR: c_int = 6;

/// `bw_rewrite_failure`: the part C sees.
#[repr(C)]
#[derive(Debug)]
pub struct BwRewriteFailure {
    pub(crate) kind: c_int,
    pub(crate) message: *const c_char,
    pub(crate) node: *const c_char,
    pub(crate) result: *const c_char,
    pub(crate) second: *const c_char,
    pub(crate) n_assignment: usize,
    pub(crate) names: *const *const c_char,
    pub(crate) values: *const BwValue,
}

/// A failure with the storage its pointers point into. `failure` comes first, so a pointer to
/// it is a pointer to the whole.
#[repr(C)]
#[derive(Debug)]
struct OwnedFailure {
    failure: BwRewriteFailure,
    strings: Vec<CString>,
    names: Vec<*const c_char>,
    values: Vec<BwValue>,
}

fn owned_failure(f: &RewriteFailure) -> Box<OwnedFailure> {
    let mut strings = vec![c_string(f.to_string())];
    let mut text = |s: &String| -> Option<usize> {
        strings.push(c_string(s.as_str()));
        Some(strings.len() - 1)
    };
    let none = || (None, None, None);
    let (kind, (node, result, second), assignment) = match f {
        RewriteFailure::Unparsable { input } => {
            (FAILURE_UNPARSABLE, (text(input), None, None), &[][..])
        }
        RewriteFailure::NeverApplied => (FAILURE_NEVER_APPLIED, none(), &[][..]),
        RewriteFailure::Differs {
            node,
            result,
            assignment,
        } => (
            FAILURE_DIFFERS,
            (text(node), text(result), None),
            assignment.as_slice(),
        ),
        RewriteFailure::Width { node, result } => {
            (FAILURE_WIDTH, (text(node), text(result), None), &[][..])
        }
        RewriteFailure::NotSmaller { node, result } => (
            FAILURE_NOT_SMALLER,
            (text(node), text(result), None),
            &[][..],
        ),
        RewriteFailure::Nondeterministic {
            node,
            first,
            second,
        } => (
            FAILURE_NONDETERMINISTIC,
            (text(node), text(first), text(second)),
            &[][..],
        ),
        RewriteFailure::ForeignExpr { node } => {
            (FAILURE_FOREIGN_EXPR, (text(node), None, None), &[][..])
        }
        // A kind added after this table: its message only.
        _ => (-1, none(), &[][..]),
    };
    let first_name = strings.len();
    strings.extend(assignment.iter().map(|(n, _)| c_string(n.as_str())));
    let values: Vec<BwValue> = assignment.iter().map(|(_, v)| value(v)).collect();
    // The strings do not move when the vector does: their pointers are taken after it is full.
    let names: Vec<*const c_char> = strings[first_name..].iter().map(|s| s.as_ptr()).collect();
    let ptr = |k: Option<usize>| k.map_or(core::ptr::null(), |k| strings[k].as_ptr());
    let failure = BwRewriteFailure {
        kind,
        message: strings[0].as_ptr(),
        node: ptr(node),
        result: ptr(result),
        second: ptr(second),
        n_assignment: values.len(),
        names: names.as_ptr(),
        values: values.as_ptr(),
    };
    Box::new(OwnedFailure {
        failure,
        strings,
        names,
        values,
    })
}

/// # Safety
/// `r` is valid; `inputs` holds `n` strings; `config` is NULL or valid (its `widths` holding
/// `n_widths`); `report` is NULL or valid for writes; `failure` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_check_rewrite(
    r: *const BwRewrite,
    inputs: *const *const c_char,
    n: usize,
    config: *const BwRewriteCheck,
    report: *mut BwRewriteReport,
    failure: *mut *mut BwRewriteFailure,
) -> c_int {
    run(|| {
        let r = unsafe { HostRewrite::new(r, false) }?;
        let failure = Out::new(failure, "failure")?;
        let inputs = unsafe { slice(inputs, n, "inputs") }?
            .iter()
            .map(|&p| unsafe { text(p, "inputs[i]") })
            .collect::<Res<Vec<&str>>>()?;
        let mut cfg = RewriteCheckConfig::default();
        if let Some(c) = unsafe { config.as_ref() } {
            if c.n_widths > 0 {
                cfg = cfg.with_widths(
                    unsafe { slice(c.widths, c.n_widths, "config->widths") }?.to_vec(),
                );
            }
            cfg = cfg
                .with_variants(c.variants)
                .with_max_exhaustive_bits(c.max_exhaustive_bits)
                .with_samples(c.samples)
                .with_seed(c.seed);
        }
        match bw::check::rewrite(&r, &inputs, &cfg) {
            Ok(rep) => {
                if !report.is_null() {
                    unsafe {
                        report.write(BwRewriteReport {
                            applications: rep.applications,
                            points: rep.points,
                            exhaustive: rep.exhaustive,
                        })
                    };
                }
                unsafe { failure.set(core::ptr::null_mut()) };
            }
            Err(f) => {
                let owned = Box::into_raw(owned_failure(&f));
                unsafe { failure.set(owned.cast()) };
            }
        }
        Ok(())
    })
}

/// # Safety
/// `f` is NULL or a failure from `bw_check_rewrite`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_rewrite_failure_free(f: *mut BwRewriteFailure) {
    if !f.is_null() {
        drop(unsafe { Box::from_raw(f.cast::<OwnedFailure>()) });
    }
}

// ----- templates ------------------------------------------------------------------------------

/// `bw_template`.
#[derive(Debug)]
pub struct BwTemplate {
    t: Template,
}

/// # Safety
/// `text` is a string, `params` holds `n` strings, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_template_new(
    text_: *const c_char,
    params: *const *const c_char,
    n: usize,
    out: *mut *mut BwTemplate,
) -> c_int {
    run(|| {
        let t = unsafe { text(text_, "text") }?;
        let out = Out::new(out, "out")?;
        let params = unsafe { slice(params, n, "params") }?
            .iter()
            .map(|&p| unsafe { text(p, "params[i]") })
            .collect::<Res<Vec<&str>>>()?;
        let t = Template::new(t, &params)?;
        unsafe { out.set(Box::into_raw(Box::new(BwTemplate { t }))) };
        Ok(())
    })
}

/// # Safety
/// `t` is NULL or a template from `bw_template_new`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_template_free(t: *mut BwTemplate) {
    if !t.is_null() {
        drop(unsafe { Box::from_raw(t) });
    }
}

/// # Safety
/// `t` is live and `widths` holds `n` elements.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_template_check(
    t: *const BwTemplate,
    widths: *const u16,
    n: usize,
) -> c_int {
    run(|| {
        let t = unsafe { get(t, "t") }?;
        let widths = unsafe { slice(widths, n, "widths") }?
            .iter()
            .map(|&w| width(w))
            .collect::<Res<Vec<Width>>>()?;
        Ok(t.t.check(&widths)?)
    })
}

/// # Safety
/// `t` and `cx` are live, `args` holds `n` elements, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_template_instantiate(
    t: *const BwTemplate,
    cx: *mut BwContext,
    args: *const u64,
    n: usize,
    out: *mut u64,
) -> c_int {
    run(|| {
        let t = unsafe { get(t, "t") }?;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let args = exprs(unsafe { slice(args, n, "args") }?)?;
        let e = t.t.instantiate(cx, &args)?;
        unsafe { out.set(e.to_bits()) };
        Ok(())
    })
}

// ----- lowering and raising -------------------------------------------------------------------

/// `bw_lowering`: a lowering's values between calls.
#[derive(Debug, Default)]
pub struct BwLowering {
    lw: Option<Lowered<u64>>,
}

impl BwLowering {
    /// Runs `f` on the lowering attached to `cx`.
    fn with<T>(
        &mut self,
        cx: &mut Context,
        f: impl FnOnce(&mut bw::translate::Lowering<'_, u64>) -> Res<T>,
    ) -> Res<T> {
        let mut lw = self.lw.take().unwrap_or_default().attach(cx);
        let r = f(&mut lw);
        self.lw = Some(lw.detach());
        r
    }

    /// The lowering's values, to read.
    fn read(&self) -> &Lowered<u64> {
        static EMPTY: std::sync::OnceLock<Lowered<u64>> = std::sync::OnceLock::new();
        self.lw
            .as_ref()
            .unwrap_or_else(|| EMPTY.get_or_init(Lowered::default))
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_lowering_new() -> *mut BwLowering {
    run_new(|| Ok(BwLowering::default()))
}

/// # Safety
/// `lw` is NULL or a lowering from `bw_lowering_new`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lowering_free(lw: *mut BwLowering) {
    if !lw.is_null() {
        drop(unsafe { Box::from_raw(lw) });
    }
}

/// # Safety
/// `lw` and `cx` are live, `out` is valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lowering_value(
    lw: *mut BwLowering,
    cx: *mut BwContext,
    v: u64,
    w: u16,
    out: *mut u64,
) -> c_int {
    run(|| {
        let lw = unsafe { get_mut(lw, "lw") }?;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let w = width(w)?;
        let e = lw.with(cx, |lw| Ok(lw.value(v, w)?))?;
        unsafe { out.set(e.to_bits()) };
        Ok(())
    })
}

/// # Safety
/// `lw` and `cx` are live, `name` is NULL or a string, `known_zero` and `known_one` are NULL or
/// valid, `out` is valid for writes.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn bw_lowering_input(
    lw: *mut BwLowering,
    cx: *mut BwContext,
    v: u64,
    w: u16,
    name: *const c_char,
    known_zero: *const BwValue,
    known_one: *const BwValue,
    out: *mut u64,
) -> c_int {
    run(|| {
        let lw = unsafe { get_mut(lw, "lw") }?;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let w = width(w)?;
        let name = if name.is_null() {
            None
        } else {
            Some(unsafe { text(name, "name") }?)
        };
        let mask = |p: *const BwValue| -> Res<BitVec> {
            match unsafe { p.as_ref() } {
                None => Ok(BitVec::zero(w)),
                Some(v) => {
                    let b = bitvec(v)?;
                    if b.width() != w {
                        return Err(Fail(
                            BW_ERR_WIDTH,
                            format!(
                                "a mask of {} bits for a value of {} bits",
                                b.width().bits(),
                                w.bits()
                            ),
                        ));
                    }
                    Ok(b)
                }
            }
        };
        let known = if known_zero.is_null() && known_one.is_null() {
            None
        } else {
            Some(known_bits(mask(known_zero)?, mask(known_one)?)?)
        };
        let e = lw.with(cx, |lw| {
            Ok(match name {
                Some(n) => lw.input_named(v, n, w, known)?,
                None => lw.input(v, w, known)?,
            })
        })?;
        unsafe { out.set(e.to_bits()) };
        Ok(())
    })
}

/// # Safety
/// `lw` and `cx` are live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lowering_define(
    lw: *mut BwLowering,
    cx: *mut BwContext,
    v: u64,
    e: u64,
) -> c_int {
    run(|| {
        let lw = unsafe { get_mut(lw, "lw") }?;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let e = expr(e)?;
        lw.with(cx, |lw| Ok(lw.define(v, e)?))
    })
}

/// # Safety
/// `lw` is NULL or live; `out` is NULL or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lowering_get(lw: *const BwLowering, v: u64, out: *mut u64) -> bool {
    let r = quiet(|| unsafe { lw.as_ref() }?.read().get(v));
    unsafe { answer(r.map(Expr::to_bits), out) }
}

/// # Safety
/// `lw` is NULL or live; `out` is NULL or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lowering_owner(lw: *const BwLowering, e: u64, out: *mut u64) -> bool {
    let r = quiet(|| unsafe { lw.as_ref() }?.read().owner(Expr::from_bits(e)?));
    unsafe { answer(r, out) }
}

/// # Safety
/// `lw` is NULL or live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lowering_input_count(lw: *const BwLowering) -> usize {
    quiet(|| Some(unsafe { lw.as_ref() }?.read().inputs().len())).unwrap_or(0)
}

/// # Safety
/// `lw` is live; `v` and `sym` are NULL or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lowering_input_at(
    lw: *const BwLowering,
    i: usize,
    v: *mut u64,
    sym: *mut u64,
) -> c_int {
    run(|| {
        let lw = unsafe { get(lw, "lw") }?;
        let (value, s) = lw
            .read()
            .inputs()
            .get(i)
            .copied()
            .ok_or_else(|| invalid(format!("no input {i}")))?;
        unsafe {
            if !v.is_null() {
                v.write(value);
            }
            if !sym.is_null() {
                sym.write(s.to_bits());
            }
        }
        Ok(())
    })
}

type EmitFn = unsafe extern "C" fn(
    *mut c_void,
    *const BwContext,
    u64,
    *const BwNode,
    *const u64,
    usize,
    *mut u64,
) -> c_int;

/// A C emit callback as a [`Raise`]; `failed` keeps the status and message of a failed call.
struct CRaise {
    emit: EmitFn,
    user: *mut c_void,
    failed: Option<Fail>,
}

impl Raise for CRaise {
    type Value = u64;

    fn emit(&mut self, cx: &Context, e: Expr, _: &View, ops: &[u64]) -> Result<u64, Error> {
        let n = match node(cx, e) {
            Ok(n) => n,
            Err(Fail(code, msg)) => {
                self.failed = Some(Fail(code, msg.clone()));
                return Err(Error::Unsupported(msg));
            }
        };
        let cxp: *const Context = cx;
        let mut out = 0u64;
        let st = unsafe {
            (self.emit)(
                self.user,
                cxp.cast::<BwContext>(),
                e.to_bits(),
                &n,
                ops.as_ptr(),
                ops.len(),
                &mut out,
            )
        };
        if st == super::BW_OK {
            return Ok(out);
        }
        let why = LAST_ERROR.with(|l| l.borrow().to_string_lossy().into_owned());
        let msg = if why.is_empty() {
            format!("the emit callback failed with status {st}")
        } else {
            format!("the emit callback failed with status {st}: {why}")
        };
        self.failed = Some(Fail(st, msg.clone()));
        Err(Error::Unsupported(msg))
    }
}

/// # Safety
/// `lw` and `cx` are live, `emit` a valid callback (see `bw_emit_fn`), `out` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lowering_raise(
    lw: *mut BwLowering,
    cx: *mut BwContext,
    e: u64,
    emit: Option<EmitFn>,
    user: *mut c_void,
    out: *mut u64,
) -> c_int {
    run(|| {
        let lw = unsafe { get_mut(lw, "lw") }?;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let emit = emit.ok_or_else(|| invalid("`emit` is NULL"))?;
        let e = expr(e)?;
        let mut r = CRaise {
            emit,
            user,
            failed: None,
        };
        let v = lw.with(cx, |lw| match lw.raise(e, &mut r) {
            Ok(v) => Ok(v),
            Err(err) => Err(r.failed.take().unwrap_or_else(|| err.into())),
        })?;
        unsafe { out.set(v) };
        Ok(())
    })
}
