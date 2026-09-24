//! `versus-smt`: bitwright's simplifier against the term simplifiers of z3 and Bitwuzla, on
//! random bit-vector DAGs built from operators SMT-LIB's QF_BV has natively (no tool reads a
//! lowered form of an operator another tool has as one node).
//!
//! Every tool starts from the same SMT-LIB script, bitwright's export of the DAG, and is timed
//! from that text to its answer, parsing included, in a context created before the clock
//! starts: bitwright imports the script and simplifies with `Engine::standard()`; z3 parses it
//! and calls `Z3_simplify` with its default parameters; Bitwuzla parses it and calls
//! `bitwuzla_simplify_term` with its default options. A case's time is the fastest of
//! [`RUNS`] runs. Each answer is read into a bitwright context and measured there, in DAG nodes
//! of the canonical form (as `bitwright-compare` measures), and checked against the input at
//! [`POINTS`] points: all zeros, all ones, one, the sign bit, then random values.
//!
//! Needs the feature `native-smt`, with `Z3_DIR` and `BITWUZLA_DIR` set (see the README).
//! `versus-smt [CASES]` runs CASES inputs per corpus (200 by default).

// Calls into z3's and Bitwuzla's C APIs.
#![allow(unsafe_code)]

use std::collections::BTreeMap;
use std::ffi::{CStr, CString, c_char, c_uint, c_void};
use std::ptr::{null, null_mut};
use std::time::{Duration, Instant};

use bitwright::engine::Engine;
use bitwright::smtlib::import;
use bitwright::{BinOp, BitVec, Bounded, CmpOp, Context, Expr, SymbolKey, UnOp, Width};

/// Runs per case and tool; the fastest counts.
const RUNS: usize = 5;
/// Points each answer is checked at.
const POINTS: usize = 64;

// ----- z3 ----------------------------------------------------------------------------------------

type Z3Context = *mut c_void;
type Z3Ast = *mut c_void;

#[link(name = "z3")]
unsafe extern "C" {
    fn Z3_mk_config() -> *mut c_void;
    fn Z3_del_config(c: *mut c_void);
    fn Z3_mk_context(c: *mut c_void) -> Z3Context;
    fn Z3_del_context(c: Z3Context);
    fn Z3_set_error_handler(c: Z3Context, h: *const c_void);
    fn Z3_get_error_code(c: Z3Context) -> c_uint;
    fn Z3_set_ast_print_mode(c: Z3Context, mode: c_uint);
    fn Z3_parse_smtlib2_string(
        c: Z3Context,
        s: *const c_char,
        num_sorts: c_uint,
        sort_names: *const c_void,
        sorts: *const c_void,
        num_decls: c_uint,
        decl_names: *const c_void,
        decls: *const c_void,
    ) -> *mut c_void;
    fn Z3_ast_vector_inc_ref(c: Z3Context, v: *mut c_void);
    fn Z3_ast_vector_dec_ref(c: Z3Context, v: *mut c_void);
    fn Z3_ast_vector_size(c: Z3Context, v: *mut c_void) -> c_uint;
    fn Z3_ast_vector_get(c: Z3Context, v: *mut c_void, i: c_uint) -> Z3Ast;
    fn Z3_to_app(c: Z3Context, a: Z3Ast) -> *mut c_void;
    fn Z3_get_app_arg(c: Z3Context, a: *mut c_void, i: c_uint) -> Z3Ast;
    fn Z3_simplify(c: Z3Context, a: Z3Ast) -> Z3Ast;
    fn Z3_ast_to_string(c: Z3Context, a: Z3Ast) -> *const c_char;
}

const Z3_OK: c_uint = 0;
const Z3_PRINT_SMTLIB2_COMPLIANT: c_uint = 2;

/// z3's answer for `root0` of `script` and the time from the text to it.
fn z3(script: &str) -> Result<(String, Duration), String> {
    // A definition is expanded while parsing; an uninterpreted predicate keeps the term.
    let text = format!(
        "{script}(declare-fun bw_keep ((_ BitVec {})) Bool)\n(assert (bw_keep root0))\n",
        root_width(script)?
    );
    let text = CString::new(text).map_err(|e| e.to_string())?;
    // SAFETY: a fresh context used on this thread only and deleted at the end; every pointer
    // passed to z3 comes from z3 or from `text`, which outlives the calls.
    unsafe {
        let config = Z3_mk_config();
        let cx = Z3_mk_context(config);
        Z3_del_config(config);
        Z3_set_error_handler(cx, null());
        Z3_set_ast_print_mode(cx, Z3_PRINT_SMTLIB2_COMPLIANT);
        let start = Instant::now();
        let v = Z3_parse_smtlib2_string(cx, text.as_ptr(), 0, null(), null(), 0, null(), null());
        let result = if v.is_null() || Z3_get_error_code(cx) != Z3_OK {
            Err("z3 did not parse the script".to_string())
        } else {
            Z3_ast_vector_inc_ref(cx, v);
            let keep = Z3_ast_vector_get(cx, v, Z3_ast_vector_size(cx, v) - 1);
            let term = Z3_get_app_arg(cx, Z3_to_app(cx, keep), 0);
            let answer = Z3_simplify(cx, term);
            let time = start.elapsed();
            let text = CStr::from_ptr(Z3_ast_to_string(cx, answer));
            // z3's division by a divisor it has shown (or guarded) to be nonzero; the same
            // operation there, and the check at the points (zero included) would catch it
            // otherwise.
            let mut text = text.to_string_lossy().into_owned();
            for op in ["bvudiv", "bvsdiv", "bvurem", "bvsrem", "bvsmod"] {
                text = text.replace(&format!("({op}_i "), &format!("({op} "));
            }
            Z3_ast_vector_dec_ref(cx, v);
            Ok((text, time))
        };
        Z3_del_context(cx);
        result
    }
}

// ----- Bitwuzla ----------------------------------------------------------------------------------

type BzlaTerm = *mut c_void;

// The libraries in link order: each needs the ones after it.
#[allow(clippy::duplicated_attributes)]
#[link(name = "bitwuzla", kind = "static")]
#[link(name = "bitwuzlals", kind = "static")]
#[link(name = "bitwuzlabv", kind = "static")]
#[link(name = "bitwuzlabb", kind = "static")]
#[link(name = "libgmp.so.10", kind = "dylib", modifiers = "+verbatim")]
#[link(name = "libmpfr.so.6", kind = "dylib", modifiers = "+verbatim")]
#[link(name = "stdc++")]
unsafe extern "C" {
    fn bitwuzla_term_manager_new() -> *mut c_void;
    fn bitwuzla_term_manager_delete(tm: *mut c_void);
    fn bitwuzla_options_new() -> *mut c_void;
    fn bitwuzla_options_delete(options: *mut c_void);
    fn bitwuzla_parser_new(
        tm: *mut c_void,
        options: *mut c_void,
        language: *const c_char,
        base: u8,
        outfile_name: *const c_char,
    ) -> *mut c_void;
    fn bitwuzla_parser_delete(parser: *mut c_void);
    fn bitwuzla_parser_parse(
        parser: *mut c_void,
        input: *const c_char,
        parse_only: bool,
        parse_file: bool,
        error_msg: *mut *const c_char,
    );
    fn bitwuzla_parser_parse_term(
        parser: *mut c_void,
        input: *const c_char,
        error_msg: *mut *const c_char,
    ) -> BzlaTerm;
    fn bitwuzla_parser_get_bitwuzla(parser: *mut c_void) -> *mut c_void;
    fn bitwuzla_simplify_term(bitwuzla: *mut c_void, term: BzlaTerm) -> BzlaTerm;
    fn bitwuzla_term_to_string(term: BzlaTerm) -> *const c_char;
}

/// Bitwuzla's answer for `root0` of `script` and the time from the text to it.
fn bitwuzla(script: &str) -> Result<(String, Duration), String> {
    let text = CString::new(script).map_err(|e| e.to_string())?;
    // SAFETY: a fresh term manager, options and parser, used on this thread only and deleted
    // at the end; the strings passed outlive the calls, and a returned string is copied before
    // the next call.
    unsafe {
        let tm = bitwuzla_term_manager_new();
        let options = bitwuzla_options_new();
        let parser = bitwuzla_parser_new(tm, options, c"smt2".as_ptr(), 2, c"<stdout>".as_ptr());
        let mut error: *const c_char = null();
        let start = Instant::now();
        bitwuzla_parser_parse(parser, text.as_ptr(), true, false, &mut error);
        let term = if error.is_null() {
            bitwuzla_parser_parse_term(parser, c"root0".as_ptr(), &mut error)
        } else {
            null_mut()
        };
        let bitwuzla = bitwuzla_parser_get_bitwuzla(parser);
        let result = if !error.is_null() {
            Err(CStr::from_ptr(error).to_string_lossy().into_owned())
        } else if bitwuzla.is_null() {
            Err("Bitwuzla made no solver instance".to_string())
        } else {
            let answer = bitwuzla_simplify_term(bitwuzla, term);
            let time = start.elapsed();
            let text = CStr::from_ptr(bitwuzla_term_to_string(answer));
            Ok((text.to_string_lossy().into_owned(), time))
        };
        bitwuzla_parser_delete(parser);
        bitwuzla_options_delete(options);
        bitwuzla_term_manager_delete(tm);
        result
    }
}

// ----- bitwright ---------------------------------------------------------------------------------

/// bitwright's answer for `root0` of `script` (in a context that also holds the input) and
/// the time from the text to it.
fn bitwright(engine: &Engine, script: &str) -> Result<(Measured, Duration), String> {
    let mut cx = Context::new();
    let start = Instant::now();
    let input = import(&mut cx, script)
        .map_err(|e| e.to_string())?
        .definition("root0")
        .ok_or("no root0")?;
    let answer = engine
        .simplify(&mut cx, input)
        .map_err(|e| e.to_string())?
        .expr;
    let time = start.elapsed();
    Ok((Measured { cx, input, answer }, time))
}

// ----- measuring ---------------------------------------------------------------------------------

/// An input and an answer in one bitwright context.
struct Measured {
    cx: Context,
    input: Expr,
    answer: Expr,
}

impl Measured {
    /// A solver's answer (an SMT-LIB term over the script's symbols), read back.
    fn read(script: &str, answer: &str) -> Result<Measured, String> {
        let mut cx = Context::new();
        let w = root_width(script)?;
        let text = format!("{script}(define-fun bw_answer () (_ BitVec {w}) {answer})\n");
        let read = import(&mut cx, &text).map_err(|e| format!("answer not read back: {e}"))?;
        let (input, answer) = (read.definition("root0"), read.definition("bw_answer"));
        Ok(Measured {
            cx,
            input: input.ok_or("no root0")?,
            answer: answer.ok_or("no answer")?,
        })
    }

    fn size(&mut self, e: Expr) -> u32 {
        match self.cx.dag_size(&[e], u32::MAX) {
            Ok(Bounded::Exact(n)) => n,
            _ => u32::MAX,
        }
    }

    /// Whether the answer equals the input at every point.
    fn agrees(&mut self, seed: u64) -> bool {
        let Ok(ids) = self.cx.symbols_in(&[self.input, self.answer]) else {
            return false;
        };
        let symbols: Vec<(SymbolKey, Width)> = ids
            .into_iter()
            .filter_map(|id| Some((self.cx.symbol_key(id)?.clone(), self.cx.symbol_width(id)?)))
            .collect();
        let mut rng = Rng(seed);
        (0..POINTS).all(|p| {
            let env: BTreeMap<SymbolKey, BitVec> = symbols
                .iter()
                .map(|(k, w)| {
                    let v = match p {
                        0 => BitVec::zero(*w),
                        1 => BitVec::ones(*w),
                        2 => BitVec::one(*w),
                        3 => BitVec::smin(*w),
                        _ => value(&mut rng, *w),
                    };
                    (k.clone(), v)
                })
                .collect();
            let v = self.cx.eval(&[self.input, self.answer], &env);
            v.is_ok_and(|v| v[0] == v[1])
        })
    }
}

/// The width of `root0` in an exported script.
fn root_width(script: &str) -> Result<u16, String> {
    let line = script
        .lines()
        .find(|l| l.starts_with("(define-fun root0 () (_ BitVec "))
        .ok_or("no root0 definition")?;
    let digits = &line["(define-fun root0 () (_ BitVec ".len()..];
    let end = digits.find(')').ok_or("bad root0 sort")?;
    digits[..end]
        .parse()
        .map_err(|_| "bad root0 width".to_string())
}

// ----- inputs ------------------------------------------------------------------------------------

/// SplitMix64.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize]
    }
}

/// A value of `w` bits: mostly random, a quarter of them 0, 1, all ones or the sign bit.
fn value(rng: &mut Rng, w: Width) -> BitVec {
    match rng.below(16) {
        0 => BitVec::zero(w),
        1 => BitVec::one(w),
        2 => BitVec::ones(w),
        3 => BitVec::smin(w),
        _ => BitVec::wrapping_from_limbs(w, &[rng.next(), rng.next(), rng.next(), rng.next()]),
    }
}

/// A random DAG shaped like `bitwright-bench`'s (operands mostly from the last few nodes,
/// sometimes from anywhere; the last 16 nodes xored into the root), over operators SMT-LIB has
/// natively: arithmetic, bitwise, shifts, comparisons under `ite`, and truncations extended
/// back. `heavy` adds division, remainder and shifts by variable amounts.
fn dag(cx: &mut Context, seed: u64, w: Width, nodes: usize, heavy: bool) -> Result<Expr, String> {
    let e = |r: Result<Expr, bitwright::Error>| r.map_err(|e| e.to_string());
    let mut rng = Rng(seed);
    let mut pool: Vec<Expr> = Vec::new();
    for i in 0..4 {
        pool.push(e(cx.symbol(SymbolKey::U64(i), w))?);
    }
    let light = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
    ];
    let slow = [
        BinOp::UDiv,
        BinOp::URem,
        BinOp::SDiv,
        BinOp::SRem,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
    ];
    let operand = |rng: &mut Rng, pool: &[Expr]| {
        let n = pool.len() as u64;
        if rng.below(4) == 0 {
            pool[rng.below(n) as usize]
        } else {
            pool[(n - 1 - rng.below(n.min(8))) as usize]
        }
    };
    for _ in 0..nodes {
        let a = operand(&mut rng, &pool);
        let b = operand(&mut rng, &pool);
        let node = match rng.below(16) {
            0..=8 => cx.bin(rng.pick(&light), a, b),
            9 if heavy => cx.bin(rng.pick(&slow), a, b),
            9 | 10 => {
                let k = value(&mut rng, w);
                let k = e(cx.constant(&k))?;
                cx.bin(rng.pick(&light), a, k)
            }
            11 => {
                let k = e(cx.constant_u64(w, rng.below(u64::from(w.bits()))))?;
                cx.bin(rng.pick(&[BinOp::Shl, BinOp::LShr, BinOp::AShr]), a, k)
            }
            12 => cx.un(rng.pick(&[UnOp::Not, UnOp::Neg]), a),
            13 => {
                let c = e(cx.cmp(rng.pick(&[CmpOp::Eq, CmpOp::Ult, CmpOp::Slt]), a, b))?;
                let d = operand(&mut rng, &pool);
                cx.select(c, b, d)
            }
            14 => {
                let half = Width::new(w.bits() / 2).map_err(|e| e.to_string())?;
                let t = e(cx.trunc(a, half))?;
                if rng.below(2) == 0 {
                    cx.zext(t, w)
                } else {
                    cx.sext(t, w)
                }
            }
            _ => cx.bin(BinOp::Xor, a, b),
        };
        pool.push(e(node)?);
    }
    let tail = pool.len().saturating_sub(16);
    let mut root = pool[tail];
    for &x in &pool[tail + 1..] {
        root = e(cx.bin(BinOp::Xor, root, x))?;
    }
    Ok(root)
}

/// The script every tool starts from: `root0` is the DAG.
fn script(seed: u64, w: Width, nodes: usize, heavy: bool) -> Result<String, String> {
    let mut cx = Context::new();
    let root = dag(&mut cx, seed, w, nodes, heavy)?;
    let text = bitwright::smtlib::export(&mut cx, &[root]).map_err(|e| e.to_string())?;
    Ok(format!("(set-logic QF_BV)\n{text}"))
}

// ----- the report --------------------------------------------------------------------------------

const TOOLS: [&str; 3] = ["bitwright", "z3", "Bitwuzla"];

/// One tool's result on one case.
#[derive(Clone, Copy)]
enum Outcome {
    Answer { size: u32, micros: f64 },
    Wrong,
    Failed,
}

/// The fastest of [`RUNS`] runs of one tool on one case, its answer measured and checked.
/// With `VERSUS_SMT_DUMP=DIR`, the script, each solver's answer as it printed it, and each
/// answer as bitwright reads it go to `DIR/CASE-TOOL.txt`.
fn run(engine: &Engine, tool: usize, script: &str, case: &str, seed: u64) -> Outcome {
    let mut best = Duration::MAX;
    let mut last = None;
    for _ in 0..RUNS {
        let got = match tool {
            0 => bitwright(engine, script).map(|(m, t)| (m, t, String::new())),
            1 => z3(script).and_then(|(a, t)| Ok((Measured::read(script, &a)?, t, a))),
            _ => bitwuzla(script).and_then(|(a, t)| Ok((Measured::read(script, &a)?, t, a))),
        };
        match got {
            Ok((m, t, printed)) => {
                best = best.min(t);
                last = Some((m, printed));
            }
            Err(e) => {
                eprintln!("{} on {case}: {e}", TOOLS[tool]);
                return Outcome::Failed;
            }
        }
    }
    let Some((mut m, printed)) = last else {
        return Outcome::Failed;
    };
    if let Some(dir) = std::env::var_os("VERSUS_SMT_DUMP") {
        let path = std::path::Path::new(&dir).join(format!("{case}-{}.txt", TOOLS[tool]));
        let read = m.cx.display(m.answer);
        let text = format!("{script}\n; printed\n{printed}\n\n; read\n{read}\n");
        std::fs::write(path, text).expect("VERSUS_SMT_DUMP is a writable directory");
    }
    if !m.agrees(seed ^ 0xc0ffee) {
        eprintln!("{} on {case}: wrong answer", TOOLS[tool]);
        return Outcome::Wrong;
    }
    let size = m.size(m.answer);
    Outcome::Answer {
        size,
        micros: best.as_secs_f64() * 1e6,
    }
}

fn percentile(sorted: &[f64], p: usize) -> f64 {
    sorted[(sorted.len() * p / 100).min(sorted.len() - 1)]
}

fn main() {
    let cases: u64 = std::env::args()
        .nth(1)
        .map_or(200, |a| a.parse().expect("CASES is a number"));
    let engine = Engine::standard();
    let corpora = [
        ("40 nodes, 8 bits", 8u16, 40usize, false),
        ("40 nodes, 64 bits", 64, 40, false),
        (
            "40 nodes with division and variable shifts, 64 bits",
            64,
            40,
            true,
        ),
        ("400 nodes, 64 bits", 64, 400, false),
    ];
    println!(
        "| corpus | tool | nodes before | nodes after | smaller | smallest | wrong | failed | median µs | p95 µs |"
    );
    println!("|-|-|-|-|-|-|-|-|-|-|");
    for (name, bits, nodes, heavy) in corpora {
        let w = Width::new(bits).expect("width");
        let mut before = 0u64;
        let mut results: Vec<[Outcome; 3]> = Vec::new();
        let mut sizes_before: Vec<u32> = Vec::new();
        for i in 0..cases {
            let seed = 0x5eed + i;
            let script = script(seed, w, nodes, heavy).expect("the corpus exports");
            let mut m = Measured::read(&script, "root0").expect("the input reads back");
            let n = m.size(m.input);
            before += u64::from(n);
            sizes_before.push(n);
            let case = format!("{bits}-{nodes}{}-{seed:x}", if heavy { "h" } else { "" });
            results.push([0, 1, 2].map(|t| run(&engine, t, &script, &case, seed)));
        }
        for (t, tool) in TOOLS.iter().enumerate() {
            let (mut after, mut smaller, mut smallest, mut wrong, mut failed) = (0u64, 0, 0, 0, 0);
            let mut micros = Vec::new();
            for (case, outcomes) in results.iter().enumerate() {
                let best = outcomes
                    .iter()
                    .filter_map(|o| match o {
                        Outcome::Answer { size, .. } => Some(*size),
                        _ => None,
                    })
                    .min();
                match outcomes[t] {
                    Outcome::Answer { size, micros: us } => {
                        after += u64::from(size);
                        smaller += usize::from(size < sizes_before[case]);
                        smallest += usize::from(Some(size) == best);
                        micros.push(us);
                    }
                    Outcome::Wrong => wrong += 1,
                    Outcome::Failed => failed += 1,
                }
            }
            micros.sort_by(f64::total_cmp);
            let (median, p95) = if micros.is_empty() {
                (f64::NAN, f64::NAN)
            } else {
                (percentile(&micros, 50), percentile(&micros, 95))
            };
            println!(
                "| {name} | {tool} | {before} | {after} | {smaller} | {smallest} | {wrong} | {failed} | {median:.1} | {p95:.1} |"
            );
        }
    }
}
