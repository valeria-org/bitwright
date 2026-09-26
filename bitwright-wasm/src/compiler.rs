//! What a compiler needs, for JavaScript: the compile engine, declared known bits, host
//! rewrites as JavaScript callbacks with their checker, templates, and a run's counters.
//!
//! A JavaScript rewrite is called through the module's one import, `bitwright.rewrite(index,
//! node)`, while the engine holds the site it runs at; the `bw_site_*` exports work on that
//! site. Handles are `u64`s (`BigInt`s in JavaScript), valid during the call that made them.
//! Values cross as hexadecimal text. Records in text results are separated by NUL characters,
//! which no expression contains.

use core::cell::Cell;
use core::ffi::c_void;
use std::sync::Arc;

use bw::check::{RewriteCheckConfig, RewriteFailure};
use bw::engine::{Engine, Rewrite, Run, Sharing, Site, Stats, Strategy};
use bw::translate::Template;
use bw::{
    BinOp, BitVec, CmpOpExt, Context, Expr, KnownBits, ParseOptions, PrintOptions, SymbolKey, UnOp,
    View, Width,
};

use super::{deobfuscator, width};

// ----- host rewrites --------------------------------------------------------------------------

#[cfg(target_arch = "wasm32")]
#[link(wasm_import_module = "bitwright")]
unsafe extern "C" {
    /// JavaScript's rewrite number `index` at node `e` of the current site: the replacement's
    /// handle, or 0 to leave the node.
    #[link_name = "rewrite"]
    fn js_rewrite(index: u32, e: u64) -> u64;
}

/// Outside WebAssembly (the workspace's native builds and lints) there is no JavaScript.
#[cfg(not(target_arch = "wasm32"))]
unsafe fn js_rewrite(_: u32, _: u64) -> u64 {
    0
}

thread_local! {
    /// The site of the JavaScript rewrite running now, if one is.
    static SITE: Cell<*mut c_void> = const { Cell::new(core::ptr::null_mut()) };
}

/// A JavaScript rewrite, by its index in the call's list.
#[derive(Debug)]
struct JsRewrite {
    index: u32,
    name: String,
    group: String,
    revision: u32,
}

impl Rewrite for JsRewrite {
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
        let outer = SITE.with(|s| s.replace(p.cast()));
        let r = unsafe { js_rewrite(self.index, e.to_bits()) };
        SITE.with(|s| s.set(outer));
        Expr::from_bits(r)
    }
}

/// Runs `f` on the current site, if a JavaScript rewrite is running.
fn with_site<T>(f: impl FnOnce(&mut Site<'_>) -> Option<T>) -> Option<T> {
    let p = SITE.with(Cell::get);
    if p.is_null() {
        return None;
    }
    // SAFETY: the pointer is the `&mut Site` of the rewrite call running now (this module is
    // single-threaded); it is cleared when the call returns.
    let site = unsafe { &mut *p.cast::<Site<'_>>() };
    f(site)
}

/// A buffer holding `s` as `bw_call` returns one (status 0), or status 1 for none.
fn text_out(s: Option<String>) -> *mut u8 {
    let (status, s) = match s {
        Some(s) => (0u8, s),
        None => (1u8, String::new()),
    };
    super::buffer(status, &s)
}

fn kind_code(v: &View) -> i32 {
    match v {
        View::Const(_) => 0,
        View::Sym(_) => 1,
        View::Un(..) => 2,
        View::Bin(..) => 3,
        View::Cmp(..) => 4,
        View::Zext(_) => 5,
        View::Sext(_) => 6,
        View::Extract { .. } => 7,
        View::Concat { .. } => 8,
        View::Select { .. } => 9,
        View::Ext { .. } => 10,
        View::Fp { .. } => 11,
        _ => 12,
    }
}

/// The kinds, by `bw_site_kind`'s codes.
const KINDS: &str =
    "const symbol unary binary compare zext sext extract concat select ext fp other";

/// The node's kind (see `KINDS`), or -1.
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_kind(e: u64) -> i32 {
    with_site(|s| s.view(Expr::from_bits(e)?)).map_or(-1, |v| kind_code(&v))
}

/// The node's operator, as the text syntax names it (status 1: none).
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_op(e: u64) -> *mut u8 {
    text_out(with_site(|s| {
        Some(match s.view(Expr::from_bits(e)?)? {
            View::Un(op, _) => op.name().to_string(),
            View::Bin(op, ..) => op.name().to_string(),
            View::Cmp(op, ..) => format!("{op:?}").to_lowercase(),
            _ => return None,
        })
    }))
}

/// The node's operands, as decimal handles separated by spaces.
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_children(e: u64) -> *mut u8 {
    text_out(with_site(|s| {
        let kids = s.context().children(Expr::from_bits(e)?).ok()?;
        Some(
            kids.map(|k| k.to_bits().to_string())
                .collect::<Vec<_>>()
                .join(" "),
        )
    }))
}

/// The node's width, or 0.
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_width(e: u64) -> u32 {
    with_site(|s| s.width(Expr::from_bits(e)?)).map_or(0, |w| u32::from(w.bits()))
}

/// The first bit of an extract, or -1.
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_lo(e: u64) -> i32 {
    with_site(|s| match s.view(Expr::from_bits(e)?)? {
        View::Extract { lo, .. } => Some(i32::from(lo)),
        _ => None,
    })
    .unwrap_or(-1)
}

/// A constant's value in hexadecimal (status 1: not a constant).
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_value(e: u64) -> *mut u8 {
    text_out(with_site(|s| {
        Some(format!("{:x}", s.as_const(Expr::from_bits(e)?)?))
    }))
}

/// The node's facts: known zero, known one, umin, umax, ustride, smin and smax (bit patterns),
/// in hexadecimal separated by spaces (status 1: declined).
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_facts(e: u64) -> *mut u8 {
    text_out(with_site(|s| {
        let f = s.facts(Expr::from_bits(e)?)?;
        let (k, u, r) = (f.known(), f.urange(), f.srange());
        Some(format!(
            "{:x} {:x} {:x} {:x} {:x} {:x} {:x}",
            k.known_zero(),
            k.known_one(),
            u.lo(),
            u.hi(),
            u.stride(),
            r.lo(),
            r.hi()
        ))
    }))
}

/// The node in the text syntax, without `let`s (status 1: not a handle).
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_print(e: u64) -> *mut u8 {
    text_out(with_site(|s| {
        let e = Expr::from_bits(e)?;
        s.width(e)?;
        let opts = PrintOptions::default().with_lets(false);
        Some(s.context().display_with(e, opts).to_string())
    }))
}

/// The constant `0x<hex>:<width>` at `ptr` (from `bw_alloc`, freed by the caller), or 0.
///
/// # Safety
/// `ptr` holds `len` bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn bw_site_const(ptr: *const u8, len: usize) -> u64 {
    let Ok(text) = (unsafe { super::arg(ptr, len) }) else {
        return 0;
    };
    let Ok(v) = BitVec::parse(text) else {
        return 0;
    };
    with_site(|s| s.constant(&v)).map_or(0, Expr::to_bits)
}

fn build(f: impl FnOnce(&mut Site<'_>) -> Option<Expr>) -> u64 {
    with_site(f).map_or(0, Expr::to_bits)
}

fn nth<T: Copy>(all: &[T], i: u32) -> Option<T> {
    all.get(i as usize).copied()
}

/// Unary operator number `op` of `UnOp::ALL`, or 0.
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_un(op: u32, a: u64) -> u64 {
    build(|s| s.un(nth(&UnOp::ALL, op)?, Expr::from_bits(a)?))
}

/// Binary operator number `op` of `BinOp::ALL`, or 0.
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_bin(op: u32, a: u64, b: u64) -> u64 {
    build(|s| {
        s.bin(
            nth(&BinOp::ALL, op)?,
            Expr::from_bits(a)?,
            Expr::from_bits(b)?,
        )
    })
}

/// Comparison number `op` of `CmpOpExt::ALL`, or 0.
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_cmp(op: u32, a: u64, b: u64) -> u64 {
    build(|s| {
        s.cmp(
            nth(&CmpOpExt::ALL, op)?,
            Expr::from_bits(a)?,
            Expr::from_bits(b)?,
        )
    })
}

fn site_width(w: u32) -> Option<Width> {
    Width::new(u16::try_from(w).ok()?).ok()
}

/// `kind` 0: zext, 1: sext, 2: trunc, to `w` bits; or 0.
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_cast(kind: u32, a: u64, w: u32) -> u64 {
    build(|s| {
        let (a, w) = (Expr::from_bits(a)?, site_width(w)?);
        match kind {
            0 => s.zext(a, w),
            1 => s.sext(a, w),
            2 => s.trunc(a, w),
            _ => None,
        }
    })
}

/// Bits `[lo, lo + len)` of `a`, or 0.
#[unsafe(no_mangle)]
pub extern "C" fn bw_site_extract(a: u64, lo: u32, len: u32) -> u64 {
    build(|s| {
        s.extract(
            Expr::from_bits(a)?,
            u16::try_from(lo).ok()?,
            site_width(len)?,
        )
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_site_concat(hi: u64, lo: u64) -> u64 {
    build(|s| s.concat(Expr::from_bits(hi)?, Expr::from_bits(lo)?))
}

#[unsafe(no_mangle)]
pub extern "C" fn bw_site_select(c: u64, t: u64, f: u64) -> u64 {
    build(|s| {
        s.select(
            Expr::from_bits(c)?,
            Expr::from_bits(t)?,
            Expr::from_bits(f)?,
        )
    })
}

/// The names `bw_site_kind`, `bw_site_un`, `bw_site_bin` and `bw_site_cmp` number, one line
/// each: kinds, unary operators, binary operators, comparisons.
pub(super) fn names() -> String {
    let join = |v: Vec<String>| v.join(" ");
    format!(
        "{KINDS}\n{}\n{}\n{}",
        join(UnOp::ALL.iter().map(|o| o.name().to_string()).collect()),
        join(BinOp::ALL.iter().map(|o| o.name().to_string()).collect()),
        join(
            CmpOpExt::ALL
                .iter()
                .map(|o| format!("{o:?}").to_lowercase())
                .collect()
        ),
    )
}

// ----- simplifying with options ---------------------------------------------------------------

/// A rewrite line's fields: `rewrite <index> <trusted 0|1> <revision> <name> <group>`.
fn rewrite_line(fields: &[&str]) -> Result<(JsRewrite, bool), String> {
    let [index, trusted, revision, name, group] = fields else {
        return Err(format!("a rewrite line has five fields: {fields:?}"));
    };
    let num = |s: &str| s.parse::<u32>().map_err(|e| format!("{s:?}: {e}"));
    Ok((
        JsRewrite {
            index: num(index)?,
            name: (*name).to_string(),
            group: (*group).to_string(),
            revision: num(revision)?,
        },
        *trusted == "1",
    ))
}

fn hex(s: &str, w: Width) -> Result<BitVec, String> {
    BitVec::parse(&format!("{s}:{}", w.bits())).map_err(|e| format!("{s:?}: {e}"))
}

fn stats_line(s: &Stats) -> String {
    let h = &s.host;
    format!(
        "node_visits={} memo_hits={} candidates={} rewrites={} rejected={} quarantined={} \
         hook_vetoes={} new_nodes={} fact_work={} pass_work={} rounds={} host.calls={} \
         host.noop={} host.changed={} host.rejected_cost={} host.rejected={}",
        s.node_visits,
        s.memo_hits,
        s.candidates,
        s.rewrites,
        s.rejected,
        s.quarantined,
        s.hook_vetoes,
        s.new_nodes,
        s.fact_work,
        s.pass_work,
        s.rounds,
        h.calls,
        h.noop,
        h.changed,
        h.rejected_cost,
        h.rejected
    )
}

/// `text` simplified with the options of `opts`, one per line:
/// - `engine standard|deobfuscate|compile` (default deobfuscate);
/// - `sharing roots|ignored`, `max_region <n>`, `max_rounds <n>`;
/// - `known <symbol> <zero hex> <one hex>`: declared known bits of a symbol of the text;
/// - `rewrite <index> <trusted 0|1> <revision> <name> <group>`: a JavaScript rewrite;
/// - `stats`: a second line with the call's counters, `name=value` separated by spaces.
pub(super) fn simplify_with(text: &str, opts: &str, w: u32) -> Result<String, String> {
    let mut cx = Context::new();
    let e = cx
        .parse(text, &ParseOptions::width(width(w)?))
        .map_err(|e| e.to_string())?;
    let mut preset = "deobfuscate";
    let mut strategy_opts: Vec<Box<dyn Fn(Strategy) -> Strategy>> = Vec::new();
    let mut rewrites = Vec::new();
    let mut stats = false;
    for line in opts.lines().filter(|l| !l.trim().is_empty()) {
        let fields: Vec<&str> = line.split_whitespace().collect();
        match fields.as_slice() {
            ["engine", p @ ("standard" | "deobfuscate" | "compile")] => preset = p,
            ["sharing", "roots"] => {
                strategy_opts.push(Box::new(|s| s.with_sharing(Sharing::Roots)))
            }
            ["sharing", "ignored"] => {
                strategy_opts.push(Box::new(|s| s.with_sharing(Sharing::Ignored)))
            }
            ["max_region", n] => {
                let n: u32 = n.parse().map_err(|e| format!("max_region: {e}"))?;
                strategy_opts.push(Box::new(move |s| s.with_max_region(n)));
            }
            ["max_rounds", n] => {
                let n: u8 = n.parse().map_err(|e| format!("max_rounds: {e}"))?;
                strategy_opts.push(Box::new(move |s| s.with_max_rounds(n)));
            }
            ["known", name, zero, one] => {
                let s = cx
                    .find_symbol(&SymbolKey::from(*name))
                    .ok_or_else(|| format!("the expression has no symbol {name}"))?;
                let sw = cx.width(s).map_err(|e| e.to_string())?;
                let k = KnownBits::new(hex(zero, sw)?, hex(one, sw)?)
                    .ok_or_else(|| format!("a bit of {name} is declared both 0 and 1"))?;
                cx.declare_known(s, k).map_err(|e| e.to_string())?;
            }
            ["rewrite", rest @ ..] => rewrites.push(rewrite_line(rest)?),
            ["stats"] => stats = true,
            _ => return Err(format!("unknown option {line:?}")),
        }
    }
    let plain = strategy_opts.is_empty() && rewrites.is_empty();
    let built;
    let engine: &Engine = match preset {
        "standard" if plain => &Engine::standard(),
        "deobfuscate" if plain => deobfuscator(),
        _ => {
            let mut b = Engine::builder().builtin();
            let mut strategy = match preset {
                "standard" => Strategy::standard(),
                "compile" => Strategy::compile(),
                _ => {
                    b = b.mba_solver(Arc::new(bw::mba::NormalFormSolver::default()));
                    super::deobfuscate_strategy()
                }
            };
            let mut groups: Vec<String> = Vec::new();
            for (r, trusted) in rewrites {
                if !groups.contains(&r.group) {
                    groups.push(r.group.clone());
                }
                let r: Arc<dyn Rewrite> = Arc::new(r);
                b = if trusted {
                    b.trusted_rewrite(r)
                } else {
                    b.rewrite(r).allow_unproven(true)
                };
            }
            if !groups.is_empty() {
                let g: Vec<&str> = groups.iter().map(String::as_str).collect();
                strategy = strategy.with_rule_groups(&g);
            }
            for f in &strategy_opts {
                strategy = f(strategy);
            }
            built = b.strategy(strategy).build().map_err(|e| e.to_string())?;
            &built
        }
    };
    let out = engine
        .run(&mut cx, &[e], Run::default())
        .map_err(|e| e.to_string())?;
    let mut s = cx.display(out.roots[0].expr).to_string();
    if stats {
        s.push('\n');
        s.push_str(&stats_line(&out.stats));
    }
    Ok(s)
}

// ----- checking a rewrite ---------------------------------------------------------------------

/// Checks the JavaScript rewrite of `opts` on `inputs` (NUL-separated expression text). `opts`
/// has one option per line: `rewrite <index> 0 <revision> <name> <group>`, `widths <w>...`,
/// `variants <n>`, `max_exhaustive_bits <n>`, `samples <n>`, `seed <n>`. The result is
/// `passed <applications> <points> <exhaustive>`, or NUL-separated records: `failed <kind>`,
/// the message, the node, the result, the second result (each empty when there is none), and
/// `<name> <hex>` for each symbol of the assignment.
pub(super) fn check_rewrite(inputs: &str, opts: &str) -> Result<String, String> {
    let mut cfg = RewriteCheckConfig::default();
    let mut rewrite = None;
    for line in opts.lines().filter(|l| !l.trim().is_empty()) {
        let fields: Vec<&str> = line.split_whitespace().collect();
        let num = |s: &str| s.parse::<u64>().map_err(|e| format!("{line:?}: {e}"));
        match fields.as_slice() {
            ["rewrite", rest @ ..] => rewrite = Some(rewrite_line(rest)?.0),
            ["widths", ws @ ..] => {
                let ws = ws
                    .iter()
                    .map(|w| w.parse::<u16>().map_err(|e| format!("{w:?}: {e}")))
                    .collect::<Result<Vec<_>, _>>()?;
                cfg = cfg.with_widths(ws);
            }
            ["variants", n] => cfg = cfg.with_variants(num(n)? as u32),
            ["max_exhaustive_bits", n] => cfg = cfg.with_max_exhaustive_bits(num(n)? as u32),
            ["samples", n] => cfg = cfg.with_samples(num(n)? as u32),
            ["seed", n] => cfg = cfg.with_seed(num(n)?),
            _ => return Err(format!("unknown option {line:?}")),
        }
    }
    let rewrite = rewrite.ok_or("no rewrite to check")?;
    let inputs: Vec<&str> = inputs.split('\0').filter(|s| !s.is_empty()).collect();
    match bw::check::rewrite(&rewrite, &inputs, &cfg) {
        Ok(r) => Ok(format!(
            "passed {} {} {}",
            r.applications, r.points, r.exhaustive
        )),
        Err(f) => {
            let none = String::new();
            let (kind, node, result, second, assignment) = match &f {
                RewriteFailure::Unparsable { input } => {
                    ("unparsable", input, &none, &none, &[][..])
                }
                RewriteFailure::NeverApplied => ("never_applied", &none, &none, &none, &[][..]),
                RewriteFailure::Differs {
                    node,
                    result,
                    assignment,
                } => ("differs", node, result, &none, assignment.as_slice()),
                RewriteFailure::Width { node, result } => ("width", node, result, &none, &[][..]),
                RewriteFailure::NotSmaller { node, result } => {
                    ("not_smaller", node, result, &none, &[][..])
                }
                RewriteFailure::Nondeterministic {
                    node,
                    first,
                    second,
                } => ("nondeterministic", node, first, second, &[][..]),
                RewriteFailure::ForeignExpr { node } => {
                    ("foreign_expr", node, &none, &none, &[][..])
                }
                _ => ("other", &none, &none, &none, &[][..]),
            };
            let mut records = vec![
                format!("failed {kind}"),
                f.to_string(),
                node.clone(),
                result.clone(),
                second.clone(),
            ];
            records.extend(assignment.iter().map(|(n, v)| format!("{n} {v:x}")));
            Ok(records.join("\0"))
        }
    }
}

// ----- templates ------------------------------------------------------------------------------

/// Splits `params\0arg\0arg...`: the parameter names (separated by spaces) and the rest.
fn params_and(b: &str) -> (Vec<&str>, Vec<&str>) {
    let mut parts = b.split('\0');
    let params = parts
        .next()
        .unwrap_or("")
        .split_whitespace()
        .collect::<Vec<_>>();
    (params, parts.collect())
}

/// Template `text` over the parameters of `b` (`params\0arg\0arg...`) instantiated with the
/// arguments, parsed at `w` bits: the expression, printed.
pub(super) fn instantiate(text: &str, b: &str, w: u32) -> Result<String, String> {
    let (params, args) = params_and(b);
    let t = Template::new(text, &params).map_err(|e| e.to_string())?;
    let mut cx = Context::new();
    let opts = ParseOptions::width(width(w)?);
    let args = args
        .iter()
        .map(|a| cx.parse(a, &opts))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| e.to_string())?;
    let e = t.instantiate(&mut cx, &args).map_err(|e| e.to_string())?;
    Ok(cx.display(e).to_string())
}

/// Template `text` over the parameters of `b` (`params\0widths`, both separated by spaces)
/// read at those widths: an error now, not at first use.
pub(super) fn check_template(text: &str, b: &str) -> Result<String, String> {
    let (params, rest) = params_and(b);
    let t = Template::new(text, &params).map_err(|e| e.to_string())?;
    let widths = rest
        .first()
        .copied()
        .unwrap_or("")
        .split_whitespace()
        .map(|w| width(w.parse::<u32>().map_err(|e| format!("{w:?}: {e}"))?))
        .collect::<Result<Vec<_>, _>>()?;
    t.check(&widths).map_err(|e| e.to_string())?;
    Ok(String::new())
}
