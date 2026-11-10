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

use bw::engine::{Engine, Phase, Run, Strategy, Trace};
use bw::mba::{MbaConfig, MbaTrust, NormalFormSolver};
use bw::rules::{Ledger, RuleProgram};
use bw::{Context, ParseOptions, Width};

mod compiler;
mod lean;
mod lean_in;

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
const TRACE: u32 = 15;
const EVALUATE: u32 = 16;
const RULES: u32 = 17;
const FROM_SMTLIB: u32 = 18;
const TO_LEAN: u32 = 19;
const EQUIVALENCE_QUERY: u32 = 20;
const CHECK_RULES: u32 = 21;
const LEAN_TO_RULES: u32 = 22;

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
            let cfg = bw::transform::Config::default();
            let reports = bw::transform::validate(a, tgt, &cfg).map_err(|e| e.to_string())?;
            Ok(reports.iter().map(ToString::to_string).collect())
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
        TRACE => {
            // Options, a line each: `standard` (the standard engine), `assume <predicate>`,
            // `phases <name>,<name>,…` (a strategy of just those phases, in that order).
            let mut cx = Context::new();
            let o = ParseOptions::width(width(n)?);
            let e = cx.parse(a, &o).map_err(|e| e.to_string())?;
            let mut standard = false;
            let mut trusted = false;
            let mut phases: Option<Vec<String>> = None;
            let mut assumptions = bw::Assumptions::new();
            // `rules` on a line of its own: the rest of `b` is a `.bwr` program to link.
            let (opts, rules_src) = match b.find("\nrules\n") {
                Some(i) => (&b[..i], Some(&b[i + 7..])),
                None => match b.strip_prefix("rules\n") {
                    Some(rest) => ("", Some(rest)),
                    None => (b, None),
                },
            };
            for line in opts.lines().map(str::trim).filter(|l| !l.is_empty()) {
                if line == "standard" {
                    standard = true;
                } else if line == "trusted" {
                    trusted = true;
                } else if let Some(list) = line.strip_prefix("phases ") {
                    phases = Some(list.split(',').map(|p| p.trim().to_string()).collect());
                } else if let Some(p) = line.strip_prefix("assume ") {
                    let p = cx.parse(p, &o).map_err(|e| format!("assume {p}: {e}"))?;
                    assumptions
                        .assume_true(&mut cx, p)
                        .map_err(|e| format!("assume: {e} (a predicate is 1 bit wide)"))?;
                } else {
                    return Err(format!("unknown option `{line}`"));
                }
            }
            let own_engine;
            let mut linked: Option<(String, Option<Ledger>)> = None;
            let engine = if let Some(src) = rules_src {
                let (program, ledger) = own_rules(src, trusted)?;
                let groups: Vec<String> = program.groups().iter().map(|g| g.name.clone()).collect();
                let group_refs: Vec<&str> = groups.iter().map(String::as_str).collect();
                let mut strategy = if let Some(names) = &phases {
                    custom_strategy(names)?
                } else if standard {
                    Strategy::standard()
                } else {
                    deobfuscate_strategy()
                };
                strategy = strategy.with_rule_groups(&group_refs);
                let mut builder = Engine::builder()
                    .builtin()
                    .mba_solver(Arc::new(NormalFormSolver::default()))
                    .strategy(strategy);
                builder = match &ledger {
                    Some(l) => builder.program(program, l),
                    None => builder.unproven_program(program).allow_unproven(true),
                };
                own_engine = builder.build().map_err(|e| e.to_string())?;
                linked = Some((src.to_string(), ledger));
                &own_engine
            } else if let Some(names) = phases {
                own_engine = custom_engine(&names)?;
                &own_engine
            } else if standard {
                own_engine = Engine::standard();
                &own_engine
            } else {
                deobfuscator()
            };
            let mut t = Trace::new(engine).with_explanations(true).with_facts(true);
            if let Some((src, ledger)) = &linked {
                t = t.with_source(src, ledger.as_ref());
            }
            t.with_assumptions(&mut cx, &assumptions)
                .map_err(|e| e.to_string())?;
            let out = engine
                .run(
                    &mut cx,
                    &[e],
                    Run::default()
                        .with_assumptions(&assumptions)
                        .with_observer(&mut t),
                )
                .map_err(|e| e.to_string())?;
            t.to_jsonl(&mut cx, &[e], &out).map_err(|e| e.to_string())
        }
        EVALUATE => {
            // `b`: a line per symbol, `name = value` (decimal, or hex with `0x`).
            let mut cx = Context::new();
            let w = width(n)?;
            let e = cx
                .parse(a, &ParseOptions::width(w))
                .map_err(|e| e.to_string())?;
            let mut env: std::collections::HashMap<bw::SymbolKey, bw::BitVec> = Default::default();
            for line in b.lines().map(str::trim).filter(|l| !l.is_empty()) {
                let (name, value) = line
                    .split_once('=')
                    .ok_or_else(|| format!("`{line}`: expected `name = value`"))?;
                let name = name.trim();
                let sym = cx
                    .symbols_in(&[e])
                    .map_err(|e| e.to_string())?
                    .into_iter()
                    .find(|&s| cx.symbol_key(s).is_some_and(|k| k.to_string() == name));
                let Some(sym) = sym else {
                    continue; // a symbol the expression does not have
                };
                let sw = cx.symbol_width(sym).unwrap_or(w);
                let v = parse_value(value.trim(), sw)?;
                if let Some(k) = cx.symbol_key(sym) {
                    env.insert(k.clone(), v);
                }
            }
            let v = cx.eval(&[e], &env).map_err(|e| e.to_string())?;
            Ok(format!("{:#x}", v[0]))
        }
        RULES => Ok(rule_catalog()),
        CHECK_RULES => check_rules(a),
        LEAN_TO_RULES => Ok(lean_in::to_bwr(a)),
        FROM_SMTLIB => {
            // The script's definitions, or its assertions conjoined, as expression text with
            // the symbols' widths; `b` names one definition.
            let mut cx = Context::new();
            let import = bw::smtlib::import(&mut cx, a).map_err(|e| e.to_string())?;
            let e = if !b.is_empty() {
                import
                    .definition(b)
                    .ok_or_else(|| format!("no definition `{b}`"))?
            } else if let Some(&(_, e)) = import.definitions.last() {
                e
            } else if let Some((&first, rest)) = import.assertions.split_first() {
                let mut acc = first;
                for &p in rest {
                    acc = cx.bin(bw::BinOp::And, acc, p).map_err(|e| e.to_string())?;
                }
                acc
            } else {
                return Err("the script defines and asserts nothing".to_string());
            };
            let opts = bw::PrintOptions::default().with_symbol_widths(true);
            Ok(cx.display_with(e, opts).to_string())
        }
        TO_LEAN => {
            // `a = b` as a Lean example over their symbols (`b` empty: the term of `a` alone).
            let mut cx = Context::new();
            let o = ParseOptions::width(width(n)?);
            let l = cx.parse(a, &o).map_err(|e| e.to_string())?;
            if b.is_empty() {
                return lean::term(&cx, l);
            }
            let r = cx.parse(b, &o).map_err(|e| e.to_string())?;
            lean::equation(&mut cx, l, r)
        }
        EQUIVALENCE_QUERY => {
            let mut cx = Context::new();
            let o = ParseOptions::width(width(n)?);
            let l = cx.parse(a, &o).map_err(|e| e.to_string())?;
            let r = cx.parse(b, &o).map_err(|e| e.to_string())?;
            text(bw::smtlib::equivalence_query(&mut cx, l, r))
        }
        _ => Err(format!("unknown operation {op}")),
    }
}

/// A value for a symbol of `w` bits: decimal, or hex with `0x`; negative with a leading `-`.
fn parse_value(text: &str, w: bw::Width) -> Result<bw::BitVec, String> {
    let (neg, body) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let magnitude =
        bw::BitVec::parse(&format!("{body}:{}", w.bits())).map_err(|e| format!("`{text}`: {e}"))?;
    Ok(if neg {
        bw::BitVec::apply_un(bw::UnOp::Neg, &magnitude).map_err(|e| e.to_string())?
    } else {
        magnitude
    })
}

/// An engine of the named phases (`fact_fold`, `local`, `linear`, …, `mba`), in that order.
fn custom_engine(names: &[String]) -> Result<Engine, String> {
    Engine::builder()
        .builtin()
        .mba_solver(Arc::new(NormalFormSolver::default()))
        .strategy(custom_strategy(names)?)
        .build()
        .map_err(|e| e.to_string())
}

/// A strategy of the named phases, in that order.
fn custom_strategy(names: &[String]) -> Result<Strategy, String> {
    let groups = Strategy::standard()
        .phases
        .iter()
        .find_map(|p| match p {
            Phase::Local { groups } => Some(groups.clone()),
            _ => None,
        })
        .unwrap_or_default();
    let mut phases = Vec::new();
    for name in names {
        phases.push(match name.as_str() {
            "fact_fold" => Phase::FactFold,
            "local" => Phase::Local {
                groups: groups.clone(),
            },
            "linear" => Phase::Linear,
            "bitwise" => Phase::Bitwise,
            "xor" => Phase::Xor,
            "compares" => Phase::Compares,
            "casts" => Phase::Casts,
            "demanded" => Phase::Demanded,
            "linear_mba" => Phase::LinearMba,
            "shuffle" => Phase::Shuffle,
            "invert" => Phase::Invert,
            "division" => Phase::Division,
            "carries" => Phase::Carries,
            "words" => Phase::Words,
            "mba" => Phase::Mba(
                MbaConfig::default()
                    .with_trust(MbaTrust::default().with_backend_certificates(false)),
            ),
            other => return Err(format!("unknown phase `{other}`")),
        });
    }
    if phases.is_empty() {
        return Err("no phases".to_string());
    }
    Ok(Strategy::new("custom", phases))
}

/// A `.bwr` program of the user's, compiled; checked by the soundness checker (its ledger)
/// unless `trusted`, when it links unproven and every application is sampled.
fn own_rules(src: &str, trusted: bool) -> Result<(RuleProgram, Option<Ledger>), String> {
    let program = RuleProgram::compile(src).map_err(|e| e.to_string())?;
    if trusted {
        return Ok((program, None));
    }
    let checks = bw::check::check_program(&program, &bw::check::CheckConfig::default());
    let bad: Vec<String> = checks
        .iter()
        .filter_map(|c| match &c.verdict {
            bw::check::Verdict::Sound => None,
            bw::check::Verdict::Unsound(cx) => Some(format!("{} is unsound: {cx}", c.name)),
            bw::check::Verdict::Inconclusive(why) => {
                Some(format!("{} could not be checked ({why})", c.name))
            }
            _ => Some(format!("{} could not be checked", c.name)),
        })
        .collect();
    if !bad.is_empty() {
        return Err(format!(
            "the rules did not pass the checker (link them trusted to run them anyway):\n{}",
            bad.join("\n")
        ));
    }
    Ok((program, Some(Ledger::from_checks(&checks))))
}

/// A `.bwr` program compiled and checked: a JSON object per line. Diagnostics first
/// (`{"diag":"BW0302","level":"error","message":…,"start":…,"end":…}`), then, when the program
/// compiles, each rule's verdict (`{"rule":…,"kind":…,"verdict":"sound"|"unsound"|
/// "inconclusive","detail":…,"evidence":…}`).
fn check_rules(src: &str) -> Result<String, String> {
    let j = |s: &str| format!("{:?}", s);
    let mut out = String::new();
    let program = match RuleProgram::compile(src) {
        Ok(p) => p,
        Err(e) => {
            // The compile error carries the diagnostics; report them.
            for d in &e.diagnostics {
                out.push_str(&format!(
                    "{{\"diag\":{},\"level\":{},\"message\":{},\"start\":{},\"end\":{}}}\n",
                    j(d.code),
                    j(&format!("{:?}", d.level).to_lowercase()),
                    j(&d.message),
                    d.span.0,
                    d.span.1
                ));
            }
            if e.diagnostics.is_empty() {
                out.push_str(&format!(
                    "{{\"diag\":\"\",\"level\":\"error\",\"message\":{},\"start\":0,\"end\":0}}\n",
                    j(&e.to_string())
                ));
            }
            return Ok(out);
        }
    };
    for d in program.diagnostics() {
        out.push_str(&format!(
            "{{\"diag\":{},\"level\":{},\"message\":{},\"start\":{},\"end\":{}}}\n",
            j(d.code),
            j(&format!("{:?}", d.level).to_lowercase()),
            j(&d.message),
            d.span.0,
            d.span.1
        ));
    }
    for c in bw::check::check_program(&program, &bw::check::CheckConfig::default()) {
        let (verdict, detail) = match &c.verdict {
            bw::check::Verdict::Sound => ("sound", String::new()),
            bw::check::Verdict::Unsound(cx) => ("unsound", cx.to_string()),
            bw::check::Verdict::Inconclusive(why) => ("inconclusive", why.to_string()),
            _ => ("inconclusive", String::new()),
        };
        let examples: Vec<String> = c.examples.iter().map(|e| format!("{e:?}")).collect();
        out.push_str(&format!(
            "{{\"rule\":{},\"kind\":{},\"verdict\":{},\"detail\":{},\"evidence\":{},\"failed_examples\":{}}}\n",
            j(&c.name),
            j(if c.kind == bw::rules::RuleKind::Identity { "identity" } else { "rule" }),
            j(verdict),
            j(&detail),
            j(&c.evidence.to_string()),
            examples.len()
        ));
    }
    Ok(out)
}

/// The built-in rules, a JSON object per line: name, kind, doc, examples, source, ledger.
fn rule_catalog() -> String {
    let mut out = String::new();
    for (_, src, ledger_text) in bw::rules::builtin_sources() {
        let Ok(program) = bw::rules::RuleProgram::compile(src) else {
            continue;
        };
        let ledger: std::collections::HashMap<&str, &str> = ledger_text
            .lines()
            .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
            .filter_map(|l| {
                let mut p = l.splitn(3, ' ');
                Some((p.next()?, p.nth(1)?))
            })
            .collect();
        for r in program.rules() {
            let j = |s: &str| format!("{:?}", s);
            out.push_str(&format!(
                "{{\"name\":{},\"kind\":{},\"doc\":{},\"examples\":[{}],\"source\":{},\"ledger\":{}}}\n",
                j(&r.name),
                j(if r.kind == bw::rules::RuleKind::Identity { "identity" } else { "rule" }),
                j(&r.doc),
                r.examples
                    .iter()
                    .map(|(a, b)| format!("[{},{}]", j(a), j(b)))
                    .collect::<Vec<_>>()
                    .join(","),
                j(src.get(r.span.0..r.span.1).unwrap_or("")),
                j(ledger.get(r.name.as_str()).copied().unwrap_or("")),
            ));
        }
    }
    out
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
