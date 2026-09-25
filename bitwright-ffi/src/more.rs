//! Proofs, synthesis, memory, lifted code and compiler transformations (bitwright.h, their
//! sections).

use core::ffi::{c_char, c_int};
use std::ffi::CString;

use bw::memory::{Endian, Memory, Version};
use bw::prove::{self, Outcome as ProofOutcome};

use super::{
    BW_ERR_SYNTAX, BwContext, BwEngineBuilder, Fail, Out, expr, get, get_mut, give, invalid, run,
    run_new, slice, text, width,
};

// ----- engine options -----------------------------------------------------------------------

/// # Safety
/// `b` is NULL or live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_builder_set_float_values(b: *mut BwEngineBuilder, yes: bool) {
    if let Some(b) = unsafe { b.as_mut() } {
        b.float_values = yes;
    }
}

/// # Safety
/// `b` is live and `name` a string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_engine_builder_refuse(
    b: *mut BwEngineBuilder,
    name: *const c_char,
) -> c_int {
    run(|| {
        let b = unsafe { get_mut(b, "b") }?;
        b.refuse.push(unsafe { text(name, "name") }?.to_string());
        Ok(())
    })
}

// ----- proofs and synthesis -----------------------------------------------------------------

const EQUIVALENT: c_int = 1;
const DIFFERENT: c_int = 0;
const UNDECIDED: c_int = -1;

/// # Safety
/// `cx` is live and `verdict` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_equivalent(
    cx: *mut BwContext,
    a: u64,
    b: u64,
    conflicts: u64,
    verdict: *mut c_int,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let out = Out::new(verdict, "verdict")?;
        let cfg = prove::Config::default().with_max_conflicts(conflicts);
        let v = match prove::equal(cx, expr(a)?, expr(b)?, &cfg)? {
            ProofOutcome::Proved(_) => EQUIVALENT,
            ProofOutcome::Refuted(_) => DIFFERENT,
            _ => UNDECIDED,
        };
        unsafe { out.set(v) };
        Ok(())
    })
}

/// # Safety
/// `cx` is live; `out` and `found` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_synthesize(
    cx: *mut BwContext,
    e: u64,
    max_size: u8,
    out: *mut u64,
    found: *mut bool,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let (out, found) = (Out::new(out, "out")?, Out::new(found, "found")?);
        let cfg = bw::synth::Config::default().with_max_size(max_size);
        let x = expr(e)?;
        let s = bw::synth::synthesize(cx, x, &cfg)?;
        unsafe {
            out.set(s.unwrap_or(x).to_bits());
            found.set(s.is_some());
        }
        Ok(())
    })
}

// ----- memory -------------------------------------------------------------------------------

/// `bw_memory`.
#[derive(Debug)]
pub struct BwMemory {
    m: Memory,
    v: Version,
}

/// # Safety
/// `name` is a string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_memory_new(
    name: *const c_char,
    addr_width: u16,
    cell_width: u16,
    big_endian: bool,
) -> *mut BwMemory {
    run_new(|| {
        let name = unsafe { text(name, "name") }?;
        let endian = if big_endian {
            Endian::Big
        } else {
            Endian::Little
        };
        let m = Memory::new(name, width(addr_width)?, width(cell_width)?, endian);
        let v = m.initial();
        Ok(BwMemory { m, v })
    })
}

/// # Safety
/// `m` is NULL or a memory from `bw_memory_new`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_memory_free(m: *mut BwMemory) {
    if !m.is_null() {
        drop(unsafe { Box::from_raw(m) });
    }
}

/// # Safety
/// `m` is live and `data` holds `n` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_memory_set_bytes(
    m: *mut BwMemory,
    start: u64,
    data: *const u8,
    n: usize,
) -> c_int {
    run(|| {
        let m = unsafe { get_mut(m, "m") }?;
        let data = unsafe { slice(data, n, "data") }?;
        let old = core::mem::replace(
            &mut m.m,
            Memory::new("tmp", bw::Width::W8, bw::Width::W8, Endian::Little),
        );
        m.m = old.with_bytes(u128::from(start), data)?;
        m.v = m.m.initial();
        Ok(())
    })
}

/// # Safety
/// `m` and `cx` are live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_memory_store(
    m: *mut BwMemory,
    cx: *mut BwContext,
    addr: u64,
    value: u64,
) -> c_int {
    run(|| {
        let m = unsafe { get_mut(m, "m") }?;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        m.v = m.m.store(cx, m.v, expr(addr)?, expr(value)?)?;
        Ok(())
    })
}

/// # Safety
/// `m` and `cx` are live and `out` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_memory_load(
    m: *mut BwMemory,
    cx: *mut BwContext,
    addr: u64,
    cells: u16,
    out: *mut u64,
) -> c_int {
    run(|| {
        let m = unsafe { get_mut(m, "m") }?;
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let out = Out::new(out, "out")?;
        let e = m.m.load(cx, m.v, expr(addr)?, cells)?;
        unsafe { out.set(e.to_bits()) };
        Ok(())
    })
}

// ----- lifted code --------------------------------------------------------------------------

const LIFT_PCODE: c_int = 0;
const LIFT_VEX: c_int = 1;
const LIFT_LLVM: c_int = 2;

const PART_INPUTS: c_int = 0;
const PART_OUTPUTS: c_int = 1;
const PART_STORES: c_int = 2;
const PART_EXITS: c_int = 3;

/// `bw_lifted`.
#[derive(Debug)]
pub struct BwLifted {
    inputs: Vec<(CString, u64)>,
    outputs: Vec<(CString, u64)>,
    stores: Vec<(u64, u64)>,
    exits: Vec<(u64, u64)>,
    next: Option<u64>,
}

/// # Safety
/// `cx` is live, `code` a string, `function` NULL or a string, `out` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lift(
    cx: *mut BwContext,
    from: c_int,
    code: *const c_char,
    function: *const c_char,
    out: *mut *mut BwLifted,
) -> c_int {
    run(|| {
        let cx = &mut unsafe { get_mut(cx, "cx") }?.cx;
        let code = unsafe { text(code, "code") }?;
        let function = if function.is_null() {
            None
        } else {
            Some(unsafe { text(function, "function") }?)
        };
        let out = Out::new(out, "out")?;
        let b = match from {
            LIFT_PCODE => bw::lift::pcode(cx, code)?,
            LIFT_VEX => bw::lift::vex(cx, code)?,
            LIFT_LLVM => bw::lift::llvm(cx, code, function)?,
            _ => return Err(invalid(format!("unknown front end {from}"))),
        };
        let names = |v: &[(String, bw::Expr)]| {
            v.iter()
                .map(|(n, e)| (super::c_string(n.as_str()), e.to_bits()))
                .collect()
        };
        let pairs = |v: &[(bw::Expr, bw::Expr)]| {
            v.iter().map(|(a, b)| (a.to_bits(), b.to_bits())).collect()
        };
        let l = BwLifted {
            inputs: names(&b.inputs),
            outputs: names(&b.outputs),
            stores: pairs(&b.stores),
            exits: pairs(&b.exits),
            next: b.next.map(|e| e.to_bits()),
        };
        unsafe { out.set(Box::into_raw(Box::new(l))) };
        Ok(())
    })
}

/// # Safety
/// `l` is NULL or from `bw_lift`, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lifted_free(l: *mut BwLifted) {
    if !l.is_null() {
        drop(unsafe { Box::from_raw(l) });
    }
}

/// # Safety
/// `l` is NULL or live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lifted_count(l: *const BwLifted, part: c_int) -> usize {
    let Some(l) = (unsafe { l.as_ref() }) else {
        return 0;
    };
    match part {
        PART_INPUTS => l.inputs.len(),
        PART_OUTPUTS => l.outputs.len(),
        PART_STORES => l.stores.len(),
        PART_EXITS => l.exits.len(),
        _ => 0,
    }
}

/// # Safety
/// `l` is live; `name`, `a` and `b` are NULL or valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lifted_get(
    l: *const BwLifted,
    part: c_int,
    i: usize,
    name: *mut *const c_char,
    a: *mut u64,
    b: *mut u64,
) -> c_int {
    run(|| {
        let l = unsafe { get(l, "l") }?;
        let oob = || invalid(format!("no entry {i}"));
        let (n, x, y): (Option<&CString>, u64, u64) = match part {
            PART_INPUTS => {
                let (n, e) = l.inputs.get(i).ok_or_else(oob)?;
                (Some(n), *e, 0)
            }
            PART_OUTPUTS => {
                let (n, e) = l.outputs.get(i).ok_or_else(oob)?;
                (Some(n), *e, 0)
            }
            PART_STORES => {
                let (p, v) = l.stores.get(i).ok_or_else(oob)?;
                (None, *p, *v)
            }
            PART_EXITS => {
                let (c, t) = l.exits.get(i).ok_or_else(oob)?;
                (None, *c, *t)
            }
            _ => return Err(invalid(format!("unknown part {part}"))),
        };
        unsafe {
            if !name.is_null() {
                name.write(n.map_or(core::ptr::null(), |s| s.as_ptr()));
            }
            if !a.is_null() {
                a.write(x);
            }
            if !b.is_null() {
                b.write(y);
            }
        }
        Ok(())
    })
}

/// # Safety
/// `l` is live; `out` and `has` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_lifted_next(
    l: *const BwLifted,
    out: *mut u64,
    has: *mut bool,
) -> c_int {
    run(|| {
        let l = unsafe { get(l, "l") }?;
        let (out, has) = (Out::new(out, "out")?, Out::new(has, "has")?);
        unsafe {
            out.set(l.next.unwrap_or(0));
            has.set(l.next.is_some());
        }
        Ok(())
    })
}

// ----- compiler transformations -------------------------------------------------------------

/// `bw_transform_counts`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct BwTransformCounts {
    pub(crate) valid: u32,
    pub(crate) invalid: u32,
    pub(crate) undecided: u32,
}

fn tally(reports: &[bw::transform::Report]) -> (String, BwTransformCounts) {
    use bw::transform::Verdict;
    let mut text = String::new();
    let mut c = BwTransformCounts::default();
    for r in reports {
        text.push_str(&r.to_string());
        match r.verdict() {
            Verdict::Valid => c.valid += 1,
            Verdict::Invalid(_) => c.invalid += 1,
            _ => c.undecided += 1,
        }
    }
    (text, c)
}

fn syntax(e: bw::transform::SyntaxError) -> Fail {
    Fail(BW_ERR_SYNTAX, e.to_string())
}

fn config(conflicts: u64) -> bw::transform::Config {
    let cfg = bw::transform::Config::default();
    if conflicts == 0 {
        cfg
    } else {
        cfg.with_conflicts(conflicts)
    }
}

/// # Safety
/// `text` is a string; `report` and `counts` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_transform_verify(
    code: *const c_char,
    conflicts: u64,
    report: *mut *mut c_char,
    counts: *mut BwTransformCounts,
) -> c_int {
    run(|| {
        let code = unsafe { text(code, "text") }?;
        let (report, counts) = (Out::new(report, "report")?, Out::new(counts, "counts")?);
        let ts = bw::transform::parse_transforms(code).map_err(syntax)?;
        let cfg = config(conflicts);
        let reports: Vec<_> = ts.iter().map(|t| bw::transform::verify(t, &cfg)).collect();
        let (s, c) = tally(&reports);
        unsafe {
            report.set(give(s));
            counts.set(c);
        }
        Ok(())
    })
}

/// # Safety
/// `src` is a string, `tgt` NULL or a string; `report` and `counts` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_transform_validate(
    src: *const c_char,
    tgt: *const c_char,
    conflicts: u64,
    report: *mut *mut c_char,
    counts: *mut BwTransformCounts,
) -> c_int {
    run(|| {
        let src = unsafe { text(src, "src") }?;
        let tgt = if tgt.is_null() {
            None
        } else {
            Some(unsafe { text(tgt, "tgt") }?)
        };
        let (report, counts) = (Out::new(report, "report")?, Out::new(counts, "counts")?);
        let pairs = bw::transform::pairs(src, tgt).map_err(syntax)?;
        let cfg = config(conflicts);
        let reports: Vec<_> = pairs
            .iter()
            .map(|t| bw::transform::verify(t, &cfg))
            .collect();
        let (s, c) = tally(&reports);
        unsafe {
            report.set(give(s));
            counts.set(c);
        }
        Ok(())
    })
}

/// # Safety
/// `text` is a string and `report` valid for writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_transform_infer(
    code: *const c_char,
    report: *mut *mut c_char,
) -> c_int {
    run(|| {
        let code = unsafe { text(code, "text") }?;
        let report = Out::new(report, "report")?;
        let ts = bw::transform::parse_transforms(code).map_err(syntax)?;
        let cfg = bw::transform::Config::default();
        let mut s = String::new();
        for t in &ts {
            let i =
                bw::transform::infer(t, &cfg).map_err(|e| Fail(super::BW_ERR_UNSUPPORTED, e))?;
            let verdict = i.report.as_ref().map(|r| match r.verdict() {
                bw::transform::Verdict::Valid => "valid",
                bw::transform::Verdict::Invalid(_) => "invalid",
                _ => "undecided",
            });
            s.push_str(&format!(
                "{}\t{}\t{}\n",
                t.name,
                i.pre.as_deref().unwrap_or("(none)"),
                verdict.unwrap_or("-")
            ));
        }
        unsafe { report.set(give(s)) };
        Ok(())
    })
}
