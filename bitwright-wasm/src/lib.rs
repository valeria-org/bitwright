//! bitwright as a WebAssembly module for JavaScript (`js/bitwright.mjs` wraps it): text in,
//! text out, through buffers of the module's memory.
//!
//! `bw_alloc` gives JavaScript a buffer for an argument's UTF-8 bytes; `bw_call` runs one
//! operation on up to two strings and a number, and returns a buffer holding a status byte (0
//! for success, 1 for an error), the result's length (4 bytes, little-endian) and its UTF-8
//! bytes; `bw_dealloc` frees each buffer. Every operation runs under `catch_unwind`.
//!
//! Host rewrites are JavaScript functions, called through the one import, `bitwright.rewrite`
//! (see `compiler`).

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::{Arc, OnceLock};

use bw::engine::{Engine, Strategy};
use bw::mba::{MbaConfig, MbaTrust, NormalFormSolver};
use bw::{Context, ParseOptions, Width};

mod compiler;

/// A buffer of `len` bytes, for JavaScript to fill (freed with `bw_dealloc(ptr, len)`).
#[unsafe(no_mangle)]
pub extern "C" fn bw_alloc(len: usize) -> *mut u8 {
    let mut v = Vec::<u8>::with_capacity(len.max(1));
    let p = v.as_mut_ptr();
    core::mem::forget(v);
    p
}

/// Frees a buffer from `bw_alloc` or `bw_call`.
///
/// # Safety
/// `ptr` and `len` are those of a buffer this module gave out, not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_dealloc(ptr: *mut u8, len: usize) {
    if !ptr.is_null() {
        drop(unsafe { Vec::from_raw_parts(ptr, 0, len.max(1)) });
    }
}

/// The operations of `bw_call`.
const SIMPLIFY: u32 = 0;
const SIMPLIFY_STANDARD: u32 = 1;
const SYNTHESIZE: u32 = 2;
const PROVE: u32 = 3;
const VALIDATE: u32 = 4;
const INFER: u32 = 5;
const LIFT: u32 = 6;
const EQUIVALENT: u32 = 7;
const TO_SMTLIB: u32 = 8;
const VERSION: u32 = 9;
const SIMPLIFY_WITH: u32 = 10;
const CHECK_REWRITE: u32 = 11;
const INSTANTIATE: u32 = 12;
const CHECK_TEMPLATE: u32 = 13;
const NAMES: u32 = 14;

/// The command line's deobfuscation strategy: the MBA service, on bitwright's own evidence.
fn deobfuscate_strategy() -> Strategy {
    let trust = MbaTrust::default().with_backend_certificates(false);
    Strategy::deobfuscate().with_mba(MbaConfig::default().with_trust(trust))
}

fn deobfuscator() -> &'static Engine {
    static E: OnceLock<Engine> = OnceLock::new();
    E.get_or_init(|| {
        Engine::builder()
            .builtin()
            .mba_solver(Arc::new(NormalFormSolver::default()))
            .strategy(deobfuscate_strategy())
            .build()
            .expect("the deobfuscation engine links")
    })
}

fn width(n: u32) -> Result<Width, String> {
    u16::try_from(n)
        .ok()
        .and_then(|w| Width::new(w).ok())
        .ok_or_else(|| format!("{n} is not a width (1..=512)"))
}

fn text<E: ToString>(r: Result<String, E>) -> Result<String, String> {
    r.map_err(|e| e.to_string())
}

/// One operation.
fn call(op: u32, a: &str, b: &str, n: u32) -> Result<String, String> {
    match op {
        SIMPLIFY | SIMPLIFY_STANDARD | SYNTHESIZE => {
            let mut cx = Context::new();
            let e = cx
                .parse(a, &ParseOptions::width(width(n)?))
                .map_err(|e| e.to_string())?;
            let engine = if op == SIMPLIFY_STANDARD {
                &Engine::standard()
            } else {
                deobfuscator()
            };
            let mut r = engine.simplify(&mut cx, e).map_err(|e| e.to_string())?.expr;
            if op == SYNTHESIZE
                && let Some(s) = bw::synth::synthesize(&mut cx, r, &Default::default())
                    .map_err(|e| e.to_string())?
            {
                r = s;
            }
            Ok(cx.display(r).to_string())
        }
        PROVE => {
            let ts = bw::transform::parse_transforms(a).map_err(|e| e.to_string())?;
            let cfg = bw::transform::Config::default();
            Ok(ts
                .iter()
                .map(|t| bw::transform::verify(t, &cfg).to_string())
                .collect())
        }
        VALIDATE => {
            let tgt = (!b.is_empty()).then_some(b);
            let pairs = bw::transform::pairs(a, tgt).map_err(|e| e.to_string())?;
            let cfg = bw::transform::Config::default();
            Ok(pairs
                .iter()
                .map(|t| bw::transform::verify(t, &cfg).to_string())
                .collect())
        }
        INFER => {
            let ts = bw::transform::parse_transforms(a).map_err(|e| e.to_string())?;
            let cfg = bw::transform::Config::default();
            let mut out = String::new();
            for t in &ts {
                let i = bw::transform::infer(t, &cfg)?;
                out.push_str(&format!(
                    "{}\t{}\n",
                    t.name,
                    i.pre.as_deref().unwrap_or("(none)")
                ));
            }
            Ok(out)
        }
        LIFT => {
            let mut cx = Context::new();
            let block = match n {
                0 => bw::lift::pcode(&mut cx, a),
                1 => bw::lift::vex(&mut cx, a),
                2 => bw::lift::llvm(&mut cx, a, (!b.is_empty()).then_some(b)),
                _ => {
                    return Err(format!(
                        "unknown front end {n} (0 p-code, 1 VEX, 2 LLVM IR)"
                    ));
                }
            }
            .map_err(|e| e.to_string())?;
            let mut out = String::new();
            let show = |cx: &mut Context, e| -> Result<String, String> {
                let r = deobfuscator().simplify(cx, e).map_err(|e| e.to_string())?;
                Ok(cx.display(r.expr).to_string())
            };
            for (name, e) in &block.outputs {
                let s = show(&mut cx, *e)?;
                out.push_str(&format!("{name} = {s}\n"));
            }
            for (p, v) in &block.stores {
                let (sp, sv) = (show(&mut cx, *p)?, show(&mut cx, *v)?);
                out.push_str(&format!("store [{sp}] = {sv}\n"));
            }
            for (c, t) in &block.exits {
                let (sc, st) = (show(&mut cx, *c)?, show(&mut cx, *t)?);
                out.push_str(&format!("exit to {st} if {sc}\n"));
            }
            if let Some(nx) = block.next {
                let s = show(&mut cx, nx)?;
                out.push_str(&format!("next = {s}\n"));
            }
            Ok(out)
        }
        EQUIVALENT => {
            let mut cx = Context::new();
            let o = ParseOptions::width(width(n)?);
            let x = cx.parse(a, &o).map_err(|e| e.to_string())?;
            let y = cx.parse(b, &o).map_err(|e| e.to_string())?;
            Ok(
                match bw::prove::equal(&mut cx, x, y, &bw::prove::Config::default())
                    .map_err(|e| e.to_string())?
                {
                    bw::prove::Outcome::Proved(_) => "equivalent".into(),
                    bw::prove::Outcome::Refuted(m) => {
                        let at: Vec<String> = m.iter().map(|(k, v)| format!("{k} = {v}")).collect();
                        format!("different at {}", at.join(", "))
                    }
                    _ => "undecided".into(),
                },
            )
        }
        TO_SMTLIB => {
            let mut cx = Context::new();
            let e = cx
                .parse(a, &ParseOptions::width(width(n)?))
                .map_err(|e| e.to_string())?;
            text(bw::smtlib::export(&mut cx, &[e]))
        }
        VERSION => Ok(env!("CARGO_PKG_VERSION").to_string()),
        SIMPLIFY_WITH => compiler::simplify_with(a, b, n),
        CHECK_REWRITE => compiler::check_rewrite(a, b),
        INSTANTIATE => compiler::instantiate(a, b, n),
        CHECK_TEMPLATE => compiler::check_template(a, b),
        NAMES => Ok(compiler::names()),
        _ => Err(format!("unknown operation {op}")),
    }
}

/// # Safety
/// `ptr` holds `len` bytes (or `len` is 0).
unsafe fn arg<'a>(ptr: *const u8, len: usize) -> Result<&'a str, String> {
    if len == 0 {
        return Ok("");
    }
    let bytes = unsafe { core::slice::from_raw_parts(ptr, len) };
    core::str::from_utf8(bytes).map_err(|e| format!("an argument is not UTF-8: {e}"))
}

/// Runs operation `op` on the strings at `a` and `b` and the number `n`: a buffer holding the
/// status, the result's length and its bytes (freed with `bw_dealloc(ptr, len + 5)`).
///
/// # Safety
/// `a` and `b` hold `a_len` and `b_len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_call(
    op: u32,
    a: *const u8,
    a_len: usize,
    b: *const u8,
    b_len: usize,
    n: u32,
) -> *mut u8 {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let a = unsafe { arg(a, a_len) }?;
        let b = unsafe { arg(b, b_len) }?;
        call(op, a, b, n)
    }))
    .unwrap_or_else(|_| Err("bitwright panicked".into()));
    match result {
        Ok(s) => buffer(0, &s),
        Err(e) => buffer(1, &e),
    }
}

/// A buffer holding `status`, the length of `s` and its bytes (freed with `bw_dealloc(ptr,
/// len + 5)`).
fn buffer(status: u8, s: &str) -> *mut u8 {
    let bytes = s.as_bytes();
    let total = bytes.len() + 5;
    let p = bw_alloc(total);
    let out = unsafe { core::slice::from_raw_parts_mut(p, total) };
    out[0] = status;
    out[1..5].copy_from_slice(&(bytes.len() as u32).to_le_bytes());
    out[5..].copy_from_slice(bytes);
    p
}
