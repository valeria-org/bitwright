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
//! `versus-smt [CASES]` runs CASES inputs per corpus (200 by default). With `--deobfuscate`,
//! bitwright runs as `bitwright simplify` does: the deobfuscation strategy with the MBA service
//! and the normal-form solver, on its own evidence. `versus-smt --facts` runs
//! the identities of `facts/bitvector.txt` instead, at 8 and 64 bits, over atoms and over
//! compound terms; a case is solved when the answer is no larger than the identity's simpler
//! side. With `--proofs DIR`, no tool is timed: each input's claim that bitwright's answer
//! equals it (and, for `--facts`, the identity itself) is written as an SMT-LIB script for any
//! solver to prove (`unsat`).

// Calls into z3's and Bitwuzla's C APIs.
#![allow(unsafe_code)]

use std::collections::BTreeMap;
use std::ffi::{CStr, CString, c_char, c_uint, c_void};
use std::ptr::{null, null_mut};
use std::time::{Duration, Instant};

use bitwright::engine::{Engine, Strategy};
use bitwright::mba::{MbaConfig, MbaTrust, NormalFormSolver};
use bitwright::smtlib::import;
use bitwright::fp::{FpFormat, FpTest};
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
        "{script}(declare-fun bw_keep ({}) Bool)\n(assert (bw_keep root0))\n",
        root_sort(script)?
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
    let float = root_float(script);
    Ok((
        Measured {
            cx,
            input,
            answer,
            float,
        },
        time,
    ))
}

// ----- measuring ---------------------------------------------------------------------------------

/// An input and an answer in one bitwright context.
struct Measured {
    cx: Context,
    input: Expr,
    answer: Expr,
    /// The root's format when it is a float: then values are compared as SMT-LIB's (every NaN
    /// one value).
    float: Option<FpFormat>,
}

impl Measured {
    /// A solver's answer (an SMT-LIB term over the script's symbols), read back.
    fn read(script: &str, answer: &str) -> Result<Measured, String> {
        let mut cx = Context::new();
        let sort = root_sort(script)?;
        let text = format!("{script}(define-fun bw_answer () {sort} {answer})\n");
        let read = import(&mut cx, &text).map_err(|e| format!("answer not read back: {e}"))?;
        let (input, answer) = (read.definition("root0"), read.definition("bw_answer"));
        Ok(Measured {
            cx,
            input: input.ok_or("no root0")?,
            answer: answer.ok_or("no answer")?,
            float: root_float(script),
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
        self.equal_at(self.input, self.answer, seed)
    }

    /// A fact's simpler side, read into this context over the script's symbols.
    fn truth(&mut self, script: &str, truth: &Truth) -> Result<Expr, String> {
        let text = format!(
            "{script}(define-fun bw_truth () {} {})\n",
            truth.sort, truth.rhs
        );
        let read = import(&mut self.cx, &text).map_err(|e| format!("truth not read: {e}"))?;
        read.definition("bw_truth")
            .ok_or_else(|| "no truth".to_string())
    }

    /// Whether `a` and `b` are equal at every point.
    fn equal_at(&mut self, a: Expr, b: Expr, seed: u64) -> bool {
        let Ok(ids) = self.cx.symbols_in(&[a, b]) else {
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
            let v = self.cx.eval(&[a, b], &env);
            let nan = |f: FpFormat, x: &BitVec| f.test(FpTest::Nan, x).unwrap_or(false);
            v.is_ok_and(|v| {
                v[0] == v[1] || self.float.is_some_and(|f| nan(f, &v[0]) && nan(f, &v[1]))
            })
        })
    }
}

/// The sort of `root0` in a script, as written.
fn root_sort(script: &str) -> Result<String, String> {
    let line = script
        .lines()
        .find(|l| l.starts_with("(define-fun root0 () "))
        .ok_or("no root0 definition")?;
    let rest = &line["(define-fun root0 () ".len()..];
    // One balanced form: `(_ BitVec w)` or `(_ FloatingPoint eb sb)`.
    let mut depth = 0;
    for (i, c) in rest.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(rest[..=i].to_string());
                }
            }
            ' ' if depth == 0 => return Ok(rest[..i].to_string()),
            _ => {}
        }
    }
    Err("bad root0 sort".to_string())
}

/// The format of `root0` when it is a float.
fn root_float(script: &str) -> Option<FpFormat> {
    let sort = root_sort(script).ok()?;
    let inner = sort.strip_prefix("(_ FloatingPoint ")?.strip_suffix(')')?;
    let (eb, sb) = inner.split_once(' ')?;
    FpFormat::new(eb.parse().ok()?, sb.parse().ok()?).ok()
}

/// The claim that bitwright's answer equals `root0` of `script`, for any SMT solver: the script
/// as it is (so the solver reads the input itself), the answer beside it under names of its
/// own, and their difference asserted. `unsat` proves the answer.
fn obligation(script: &str, m: &mut Measured) -> Result<String, String> {
    let answer = bitwright::smtlib::export(&mut m.cx, &[m.answer]).map_err(|e| e.to_string())?;
    let mut text = script.to_string();
    for line in answer.lines() {
        // The script declares every symbol the answer can use.
        if !line.starts_with("(declare-const") && !line.starts_with("(set-logic") {
            text.push_str(&prefixed(line, "bw_"));
            text.push('\n');
        }
    }
    text.push_str("(assert (not (= root0 bw_root0)))\n(check-sat)\n");
    Ok(text)
}

/// `line` with the exporter's own names (`n…`, `root…` and the helpers named after them)
/// prefixed; quoted symbols, literals and operators as they are.
fn prefixed(line: &str, prefix: &str) -> String {
    let mut out = String::new();
    let mut rest = line;
    while let Some(c) = rest.chars().next() {
        let len = if c == '|' {
            rest[1..].find('|').map_or(rest.len(), |j| j + 2)
        } else if c.is_ascii_alphabetic() {
            let word = rest.find([' ', '(', ')', '|']).unwrap_or(rest.len());
            let own = rest.strip_prefix("root").or_else(|| rest.strip_prefix('n'));
            if own.is_some_and(|r| r.starts_with(|d: char| d.is_ascii_digit())) {
                out.push_str(prefix);
            }
            word
        } else {
            c.len_utf8()
        };
        out.push_str(&rest[..len]);
        rest = &rest[len..];
    }
    out
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
    Answer { size: u32, micros: f64, exact: bool },
    Wrong,
    Failed,
}

/// The fastest of [`RUNS`] runs of one tool on one case, its answer measured and checked (and
/// compared with `truth`, if given). With `VERSUS_SMT_DUMP=DIR`, the script, each solver's
/// answer as it printed it, and each answer as bitwright reads it go to `DIR/CASE-TOOL.txt`.
fn run(
    engine: &Engine,
    tool: usize,
    script: &str,
    case: &str,
    seed: u64,
    truth: Option<&Truth>,
) -> Outcome {
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
    let exact = truth.is_some_and(|t| m.truth(script, t).is_ok_and(|e| e == m.answer));
    Outcome::Answer {
        size,
        micros: best.as_secs_f64() * 1e6,
        exact,
    }
}

// ----- the fact sets -----------------------------------------------------------------------------

/// The fact sets, `facts/NAME.txt`: bit-vector algebra first, then one set per area.
const FACT_SETS: [(&str, &str); 7] = [
    ("bitvector", include_str!("../../facts/bitvector.txt")),
    (
        "number-theory",
        include_str!("../../facts/number-theory.txt"),
    ),
    ("order", include_str!("../../facts/order.txt")),
    ("slices", include_str!("../../facts/slices.txt")),
    ("bit-tricks", include_str!("../../facts/bit-tricks.txt")),
    ("canonical", include_str!("../../facts/canonical.txt")),
    ("float", include_str!("../../facts/float.txt")),
];

/// One identity of a fact set: `lhs` equals the simpler `rhs`.
struct Fact {
    set: &'static str,
    category: String,
    name: String,
    /// The root's sort when it is not the base width: `bool`, `2w`, or a width expression
    /// (`h`, `w-3`, a number of bits).
    sort: Option<String>,
    lhs: String,
    rhs: String,
}

/// A fact's simpler side, the ground truth: `rhs`, of sort `sort`, over the script's variables.
struct Truth {
    sort: String,
    rhs: String,
}

fn facts() -> Result<Vec<Fact>, String> {
    let mut out = Vec::new();
    for (set, text) in FACT_SETS {
        let mut category = String::new();
        for (i, line) in text.lines().enumerate() {
            if let Some(c) = line.strip_prefix("## ") {
                category = c.to_string();
                continue;
            }
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let bad = || format!("facts/{set}.txt:{}: {line}", i + 1);
            let (head, body) = line.split_once(": ").ok_or_else(bad)?;
            let (lhs, rhs) = body.split_once(" ==> ").ok_or_else(bad)?;
            let (name, sort) = match head.split_once(" [") {
                Some((n, s)) => (n, Some(s.strip_suffix(']').ok_or_else(bad)?.to_string())),
                None => (head, None),
            };
            out.push(Fact {
                set,
                category: category.clone(),
                name: name.to_string(),
                sort,
                lhs: lhs.trim().to_string(),
                rhs: rhs.trim().to_string(),
            });
        }
    }
    Ok(out)
}

/// `text` with the fact set's placeholders filled in for base width `w`: `{E}` becomes the
/// integer E, `[E]` (or `[E@S]`, S one of `w`, `2w`, `h`, `1`) a constant of that width.
fn instantiate(text: &str, w: u32) -> Result<String, String> {
    let mut out = String::new();
    let mut rest = text;
    while let Some(i) = rest.find(['{', '[']) {
        out.push_str(&rest[..i]);
        let close = if rest[i..].starts_with('{') { '}' } else { ']' };
        let end = i + rest[i..].find(close).ok_or("an unclosed placeholder")?;
        let inner = &rest[i + 1..end];
        if close == '}' {
            out.push_str(&Calc::eval(inner, w, 128)?.to_string());
        } else {
            let (e, n) = match inner.rsplit_once('@') {
                Some((e, s)) => match s.trim() {
                    "w" => (e, w),
                    "2w" => (e, 2 * w),
                    "h" => (e, w / 2),
                    "1" => (e, 1),
                    s => return Err(format!("unknown width `{s}`")),
                },
                None => (inner, w),
            };
            out.push_str(&format!("(_ bv{} {n})", Calc::eval(e, w, n)?));
        }
        rest = &rest[end + 1..];
    }
    out.push_str(rest);
    Ok(out)
}

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Num(u128),
    Id(String),
    Op(&'static str),
    Open,
    Close,
}

/// A placeholder's integer expression, evaluated modulo 2^`n` (every operation is reduced, so
/// `>>` is logical and `~` complements `n` bits).
struct Calc {
    tokens: Vec<Tok>,
    at: usize,
    w: u32,
    n: u32,
}

impl Calc {
    fn eval(text: &str, w: u32, n: u32) -> Result<u128, String> {
        let mut c = Calc {
            tokens: Calc::tokens(text)?,
            at: 0,
            w,
            n,
        };
        let v = c.binary(0)?;
        if c.at != c.tokens.len() {
            return Err(format!("trailing input in `{text}`"));
        }
        Ok(v)
    }

    fn tokens(text: &str) -> Result<Vec<Tok>, String> {
        let mut out = Vec::new();
        let mut rest = text.trim_start();
        while let Some(c) = rest.chars().next() {
            let word = rest
                .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .unwrap_or(rest.len());
            let (tok, len) = match c {
                '0'..='9' => {
                    let lit = &rest[..word];
                    let v = match lit.strip_prefix("0x") {
                        Some(hex) => u128::from_str_radix(hex, 16),
                        None => lit.parse(),
                    };
                    (
                        Tok::Num(v.map_err(|_| format!("bad number `{lit}`"))?),
                        word,
                    )
                }
                'a'..='z' => (Tok::Id(rest[..word].to_string()), word),
                '(' => (Tok::Open, 1),
                ')' => (Tok::Close, 1),
                _ => {
                    let op = ["<<", ">>", "+", "-", "*", "&", "|", "^", "~"]
                        .into_iter()
                        .find(|op| rest.starts_with(op))
                        .ok_or_else(|| format!("unexpected `{c}` in `{text}`"))?;
                    (Tok::Op(op), op.len())
                }
            };
            out.push(tok);
            rest = rest[len..].trim_start();
        }
        Ok(out)
    }

    fn mask(&self, v: u128) -> u128 {
        if self.n >= 128 {
            v
        } else {
            v & ((1 << self.n) - 1)
        }
    }

    fn binary(&mut self, level: usize) -> Result<u128, String> {
        const LEVELS: [&[&str]; 6] = [&["|"], &["^"], &["&"], &["<<", ">>"], &["+", "-"], &["*"]];
        if level == LEVELS.len() {
            return self.unary();
        }
        let mut v = self.binary(level + 1)?;
        while let Some(Tok::Op(op)) = self.tokens.get(self.at) {
            let op = *op;
            if !LEVELS[level].contains(&op) {
                break;
            }
            self.at += 1;
            let r = self.binary(level + 1)?;
            v = self.mask(match op {
                "|" => v | r,
                "^" => v ^ r,
                "&" => v & r,
                "<<" => v.checked_shl(u32::try_from(r).unwrap_or(128)).unwrap_or(0),
                ">>" => v.checked_shr(u32::try_from(r).unwrap_or(128)).unwrap_or(0),
                "+" => v.wrapping_add(r),
                "-" => v.wrapping_sub(r),
                _ => v.wrapping_mul(r),
            });
        }
        Ok(v)
    }

    fn unary(&mut self) -> Result<u128, String> {
        match self.tokens.get(self.at) {
            Some(Tok::Op("-")) => {
                self.at += 1;
                let v = self.unary()?;
                Ok(self.mask(v.wrapping_neg()))
            }
            Some(Tok::Op("~")) => {
                self.at += 1;
                let v = self.unary()?;
                Ok(self.mask(!v))
            }
            _ => self.atom(),
        }
    }

    fn atom(&mut self) -> Result<u128, String> {
        let tok = self
            .tokens
            .get(self.at)
            .cloned()
            .ok_or("an expression ends early")?;
        self.at += 1;
        match tok {
            Tok::Num(v) => Ok(self.mask(v)),
            Tok::Open => {
                let v = self.binary(0)?;
                self.expect(Tok::Close)?;
                Ok(v)
            }
            Tok::Id(name) => match name.as_str() {
                "w" => Ok(u128::from(self.w)),
                "h" => Ok(u128::from(self.w / 2)),
                "ones" => Ok(self.mask(u128::MAX)),
                "smin" => Ok(1 << (self.n - 1)),
                "smax" => Ok((1 << (self.n - 1)) - 1),
                "inv" => {
                    self.expect(Tok::Open)?;
                    let k = self.binary(0)?;
                    self.expect(Tok::Close)?;
                    if k % 2 == 0 {
                        return Err(format!("inv({k}): not odd"));
                    }
                    // Newton's iteration doubles the correct low bits: 3, 6, ..., 192.
                    let mut x = k;
                    for _ in 0..7 {
                        x = x.wrapping_mul(2u128.wrapping_sub(k.wrapping_mul(x)));
                    }
                    Ok(self.mask(x))
                }
                _ => Err(format!("unknown name `{name}`")),
            },
            t => Err(format!("unexpected {t:?}")),
        }
    }

    fn expect(&mut self, t: Tok) -> Result<(), String> {
        if self.tokens.get(self.at) == Some(&t) {
            self.at += 1;
            Ok(())
        } else {
            Err(format!("expected {t:?}"))
        }
    }
}

/// The script for one fact at base width `w`: the variables x, y, z (atoms, or with
/// `compound` terms over fresh atoms), p a comparison, and `root0` the fact's left side; and
/// the fact's right side, the ground truth.
fn fact_script(f: &Fact, w: u32, compound: bool) -> Result<(String, Truth), String> {
    if f.set == "float" {
        let format = if w == 8 { FpFormat::F32 } else { FpFormat::F64 };
        return float_script(f, format, compound);
    }
    let width = match f.sort.as_deref() {
        None => w,
        Some("bool") => 1,
        Some("2w") => 2 * w,
        Some(s) => Calc::eval(s, w, 128)
            .ok()
            .and_then(|n| u32::try_from(n).ok())
            .ok_or_else(|| format!("{}: unknown sort `{s}`", f.name))?,
    };
    let (mut lhs, mut rhs) = (instantiate(&f.lhs, w)?, instantiate(&f.rhs, w)?);
    if f.sort.as_deref() == Some("bool") {
        lhs = format!("(ite {lhs} #b1 #b0)");
        rhs = format!("(ite {rhs} #b1 #b0)");
    }
    let bv = format!("(_ BitVec {w})");
    let mut text = String::from("(set-logic QF_BV)\n");
    let atoms: &[&str] = if compound {
        &["a", "b", "c", "d", "e", "f", "u", "v"]
    } else {
        &["x", "y", "z", "u", "v"]
    };
    for a in atoms {
        text.push_str(&format!("(declare-const {a} {bv})\n"));
    }
    if compound {
        text.push_str(&format!(
            "(define-fun x () {bv} (bvmul a b))\n(define-fun y () {bv} (bvor c d))\n\
             (define-fun z () {bv} (bvsub e f))\n"
        ));
    }
    text.push_str("(define-fun p () Bool (bvult u v))\n");
    let sort = format!("(_ BitVec {width})");
    text.push_str(&format!("(define-fun root0 () {sort} {lhs})\n"));
    Ok((text, Truth { sort, rhs }))
}

/// A float identity's text with `$eb`, `$sb` and the real constants `<r>` filled in.
fn instantiate_float(text: &str, format: FpFormat) -> Result<String, String> {
    let (eb, sb) = (format.eb(), format.sb());
    let text = text.replace("$eb", &eb.to_string()).replace("$sb", &sb.to_string());
    let mut out = String::new();
    let mut rest = text.as_str();
    while let Some(i) = rest.find('<') {
        out.push_str(&rest[..i]);
        let end = i + rest[i..].find('>').ok_or("an unclosed <r>")?;
        // A negative real is the negation of the positive one (rounding to nearest is
        // symmetric), since Bitwuzla's parser has no `(- r)` in a real constant.
        let r = &rest[i + 1..end];
        match r.strip_prefix('-') {
            Some(m) => out.push_str(&format!("(fp.neg ((_ to_fp {eb} {sb}) RNE {m}))")),
            None => out.push_str(&format!("((_ to_fp {eb} {sb}) RNE {r})")),
        }
        rest = &rest[end + 1..];
    }
    out.push_str(rest);
    Ok(out)
}

/// The script for one float identity in `format`: floats x, y, z (atoms, or with `compound`
/// a product, a sum and a root of fresh atoms), integers i (32 bits), j (16), k (8), and `root0`
/// the left side; and the right side, the ground truth.
fn float_script(f: &Fact, format: FpFormat, compound: bool) -> Result<(String, Truth), String> {
    let float = format!("(_ FloatingPoint {} {})", format.eb(), format.sb());
    let sort = match f.sort.as_deref() {
        None => float.clone(),
        Some("bool") => "(_ BitVec 1)".to_string(),
        Some(n) => format!("(_ BitVec {})", n.parse::<u32>().map_err(|e| e.to_string())?),
    };
    let (mut lhs, mut rhs) = (
        instantiate_float(&f.lhs, format)?,
        instantiate_float(&f.rhs, format)?,
    );
    if f.sort.as_deref() == Some("bool") {
        lhs = format!("(ite {lhs} #b1 #b0)");
        rhs = format!("(ite {rhs} #b1 #b0)");
    }
    let mut text = String::from("(set-logic QF_BVFP)\n");
    let atoms: &[&str] = if compound {
        &["a", "b", "c", "d", "e"]
    } else {
        &["x", "y", "z"]
    };
    for a in atoms {
        text.push_str(&format!("(declare-const {a} {float})\n"));
    }
    if compound {
        text.push_str(&format!(
            "(define-fun x () {float} (fp.mul RNE a b))\n(define-fun y () {float} \
             (fp.add RNE c d))\n(define-fun z () {float} (fp.sqrt RNE e))\n"
        ));
    }
    for (name, w) in [("i", 32), ("j", 16), ("k", 8)] {
        text.push_str(&format!("(declare-const {name} (_ BitVec {w}))\n"));
    }
    text.push_str(&format!("(define-fun root0 () {sort} {lhs})\n"));
    Ok((text, Truth { sort, rhs }))
}

/// One group's (or set's) results in `--facts`.
#[derive(Default)]
struct Row {
    set: String,
    category: String,
    facts: usize,
    cases: usize,
    /// Per tool: answers no larger than the simpler side, and the simpler side itself.
    solved: [usize; 3],
    exact: [usize; 3],
}

/// `--facts`: every identity at 8 and 64 bits, over atoms and over compound terms, through the
/// three tools. One markdown row per category: the cases, and per tool how many it solves (its
/// answer no larger than the simpler side) and how many exactly (the simpler side itself).
/// Unsolved cases go to standard error.
fn run_facts(engine: &Engine, proofs: Option<&str>, only: Option<&str>) {
    let mut facts = facts().expect("the fact set parses");
    if let Some(set) = only {
        facts.retain(|f| f.set == set);
    }
    let mut rows: Vec<Row> = Vec::new();
    let mut micros: [Vec<f64>; 3] = Default::default();
    let (mut wrong, mut failed, mut invalid) = ([0usize; 3], [0usize; 3], 0);
    for (k, f) in facts.iter().enumerate() {
        if rows
            .last()
            .is_none_or(|r| r.set != f.set || r.category != f.category)
        {
            rows.push(Row {
                set: f.set.to_string(),
                category: f.category.clone(),
                ..Row::default()
            });
        }
        rows.last_mut().expect("a row").facts += 1;
        for (j, (w, compound)) in [(8u32, false), (8, true), (64, false), (64, true)]
            .into_iter()
            .enumerate()
        {
            let variant = if compound { "-compound" } else { "" };
            let case = format!("{}.{}-{w}{variant}", f.set, f.name);
            let seed = 0xfac7_0000 + 4 * k as u64 + j as u64;
            let read = fact_script(f, w, compound).and_then(|(script, truth)| {
                let mut m = Measured::read(&script, "root0")?;
                let t = m.truth(&script, &truth)?;
                Ok((script, truth, m, t))
            });
            let (script, truth, mut m, t) = match read {
                Ok(read) => read,
                Err(e) => {
                    eprintln!("invalid\t{case}: {e}");
                    invalid += 1;
                    continue;
                }
            };
            if !m.equal_at(m.input, t, seed) {
                eprintln!("invalid\t{case}: the two sides differ");
                invalid += 1;
                continue;
            }
            let truth_size = m.size(t);
            if let Some(dir) = proofs {
                let dir = std::path::Path::new(dir);
                let (mut b, _) = bitwright(engine, &script).expect("bitwright answers");
                let claim = obligation(&script, &mut b).expect("the answer exports");
                std::fs::write(dir.join(format!("{case}.smt2")), claim).expect("a writable DIR");
                let fact = format!(
                    "{script}(define-fun bw_truth () {} {})\n(assert (not (= root0 bw_truth)))\n\
                     (check-sat)\n",
                    truth.sort, truth.rhs
                );
                std::fs::write(dir.join(format!("{case}.fact.smt2")), fact)
                    .expect("a writable DIR");
                continue;
            }
            let row = rows.last_mut().expect("a row");
            row.cases += 1;
            for tool in 0..3 {
                match run(engine, tool, &script, &case, seed, Some(&truth)) {
                    Outcome::Answer {
                        size,
                        micros: us,
                        exact,
                    } => {
                        if size <= truth_size {
                            row.solved[tool] += 1;
                        } else {
                            eprintln!("unsolved\t{}\t{case}", TOOLS[tool]);
                        }
                        row.exact[tool] += usize::from(exact);
                        micros[tool].push(us);
                    }
                    Outcome::Wrong => wrong[tool] += 1,
                    Outcome::Failed => failed[tool] += 1,
                }
            }
        }
    }
    if proofs.is_some() {
        println!("{} facts, {invalid} invalid cases", facts.len());
        return;
    }
    // Per set, then per group within the sets.
    let mut sets: Vec<Row> = Vec::new();
    for row in &rows {
        if sets.last().is_none_or(|s| s.set != row.set) {
            sets.push(Row {
                set: row.set.clone(),
                category: "all".to_string(),
                ..Row::default()
            });
        }
        let set = sets.last_mut().expect("a set");
        set.facts += row.facts;
        set.cases += row.cases;
        for t in 0..3 {
            set.solved[t] += row.solved[t];
            set.exact[t] += row.exact[t];
        }
    }
    let mut total = Row {
        set: "**all**".to_string(),
        ..Row::default()
    };
    for set in &sets {
        total.facts += set.facts;
        total.cases += set.cases;
        for t in 0..3 {
            total.solved[t] += set.solved[t];
            total.exact[t] += set.exact[t];
        }
    }
    let header = "| facts | cases | bitwright | z3 | Bitwuzla | bitwright exact | z3 exact | Bitwuzla exact |";
    let line = |r: &Row| {
        let (s, e) = (r.solved, r.exact);
        format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} |",
            r.facts, r.cases, s[0], s[1], s[2], e[0], e[1], e[2]
        )
    };
    println!("| set {header}\n|-|-:|-:|-:|-:|-:|-:|-:|-:|");
    for r in sets.iter().chain([&total]) {
        println!("| {} {}", r.set, line(r));
    }
    println!("\n| set | group {header}\n|-|-|-:|-:|-:|-:|-:|-:|-:|-:|");
    for r in &rows {
        println!("| {} | {} {}", r.set, r.category, line(r));
    }
    for (t, us) in micros.iter_mut().enumerate() {
        us.sort_by(f64::total_cmp);
        if !us.is_empty() {
            println!(
                "{}: median {:.1} µs, p95 {:.1} µs; wrong {}, failed {}",
                TOOLS[t],
                percentile(us, 50),
                percentile(us, 95),
                wrong[t],
                failed[t]
            );
        }
    }
    if invalid > 0 {
        println!("{invalid} cases whose two sides differ (left out)");
    }
}

fn percentile(sorted: &[f64], p: usize) -> f64 {
    sorted[(sorted.len() * p / 100).min(sorted.len() - 1)]
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let proofs = match args.iter().position(|a| a == "--proofs") {
        Some(i) => {
            let dir = args.get(i + 1).expect("--proofs DIR").clone();
            args.drain(i..i + 2);
            Some(dir)
        }
        None => None,
    };
    let facts = args
        .iter()
        .position(|a| a == "--facts")
        .map(|i| args.remove(i));
    let only = match args.iter().position(|a| a == "--set") {
        Some(i) => {
            let set = args.get(i + 1).expect("--set NAME").clone();
            args.drain(i..i + 2);
            Some(set)
        }
        None => None,
    };
    let deobfuscate = args
        .iter()
        .position(|a| a == "--deobfuscate")
        .map(|i| args.remove(i));
    let cases: u64 = args
        .first()
        .map_or(200, |a| a.parse().expect("CASES is a number"));
    let engine = if deobfuscate.is_some() {
        // As `bitwright simplify` runs: the MBA service with the normal-form solver, on
        // bitwright's own evidence.
        let trust = MbaTrust::default().with_backend_certificates(false);
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default().with_trust(trust)))
            .mba_solver(std::sync::Arc::new(NormalFormSolver::default()))
            .build()
            .expect("the engine builds")
    } else {
        Engine::standard()
    };
    if facts.is_some() {
        run_facts(&engine, proofs.as_deref(), only.as_deref());
        return;
    }
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
    if proofs.is_none() {
        println!(
            "| corpus | tool | nodes before | nodes after | smaller | smallest | wrong | failed | median µs | p95 µs |"
        );
        println!("|-|-|-|-|-|-|-|-|-|-|");
    }
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
            if let Some(dir) = &proofs {
                let (mut m, _) = bitwright(&engine, &script).expect("bitwright answers");
                let text = obligation(&script, &mut m).expect("the answer exports");
                let path = std::path::Path::new(dir).join(format!("{case}.smt2"));
                std::fs::write(path, text).expect("--proofs names a writable directory");
                continue;
            }
            results.push([0, 1, 2].map(|t| run(&engine, t, &script, &case, seed, None)));
        }
        if let Some(dir) = &proofs {
            println!("{name}: {cases} obligations in {dir}");
            continue;
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
                    Outcome::Answer {
                        size, micros: us, ..
                    } => {
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
