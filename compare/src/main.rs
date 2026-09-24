//! Compares bitwright's simplification with other tools on public MBA datasets: bitwright's
//! strategies (with no MBA solver, its native one, or the CoBRA backend), CoBRA itself (the
//! `cobra-mba` crate, in process), and the Z3 and Bitwuzla simplifiers (through their Python
//! bindings, `solvers.py`). Every answer is read into a bitwright context and measured there:
//! checked against the input at sampled points, sized in canonical form, and compared with the
//! dataset's ground truth. See README.md.
//!
//! ```text
//! cargo run --release -- DATASETS [OPTIONS]
//!   DATASETS          a directory of dataset files (searched recursively for *.txt)
//!   --only TEXT       only files whose path contains TEXT (repeatable)
//!   --skip TEXT       not files whose path contains TEXT (repeatable)
//!   --tools LIST      comma-separated tools (default: all; see --list)
//!   --limit N         at most N cases per file
//!   --csv FILE        also write one row per case and tool
//!   --python PATH     the Python for z3 and bitwuzla (default python3)
//!   --cobra-cpp PATH  the cobra-batch driver for C++ CoBRA (see cobra-batch/)
//!   --list            list the tools
//! ```

mod eggs;
mod heap;
mod read;

#[global_allocator]
static HEAP: heap::Counting = heap::Counting;

use std::collections::HashMap;
use std::io::Write as _;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};
use std::sync::Arc;
use std::time::Instant;

use bitwright::engine::{Engine, Run, Strategy};
use bitwright::eqsat::{SaturateConfig, Saturator, SearchRun};
use bitwright::mba::{CobraSolver, MbaConfig, MbaTrust, NormalFormSolver, SignatureSolver};
use bitwright::{BitVec, Bounded, Context, Expr, ParseOptions, SymbolKey, Width};

/// Every dataset is 64-bit.
const W: Width = Width::W64;

/// Points each answer is checked at.
const POINTS: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Tool {
    Standard,
    Deobfuscate,
    Mba,
    Nf,
    BwCobra,
    BwEqsat,
    EggBw,
    EggMba,
    CobraCpp,
    Cobra,
    CobraCert,
    Z3,
    Bitwuzla,
    Cvc5,
    Claripy,
    Miasm,
    TritonLlvm,
    TritonSynth,
}

impl Tool {
    const ALL: [Tool; 18] = [
        Tool::Standard,
        Tool::Deobfuscate,
        Tool::Mba,
        Tool::Nf,
        Tool::BwCobra,
        Tool::BwEqsat,
        Tool::EggBw,
        Tool::EggMba,
        Tool::CobraCpp,
        Tool::Cobra,
        Tool::CobraCert,
        Tool::Z3,
        Tool::Bitwuzla,
        Tool::Cvc5,
        Tool::Claripy,
        Tool::Miasm,
        Tool::TritonLlvm,
        Tool::TritonSynth,
    ];

    fn name(self) -> &'static str {
        match self {
            Tool::Standard => "bw-standard",
            Tool::Deobfuscate => "bw-deobf",
            Tool::Mba => "bw-mba",
            Tool::Nf => "bw-nf",
            Tool::BwCobra => "bw-cobra",
            Tool::BwEqsat => "bw-eqsat",
            Tool::EggBw => "egg-bw",
            Tool::EggMba => "egg-mba",
            Tool::CobraCpp => "cobra-cpp",
            Tool::Cobra => "cobra",
            Tool::CobraCert => "cobra-cert",
            Tool::Z3 => "z3",
            Tool::Bitwuzla => "bitwuzla",
            Tool::Cvc5 => "cvc5",
            Tool::Claripy => "claripy",
            Tool::Miasm => "miasm",
            Tool::TritonLlvm => "triton-llvm",
            Tool::TritonSynth => "triton-synth",
        }
    }

    fn about(self) -> &'static str {
        match self {
            Tool::Standard => "bitwright, Strategy::standard()",
            Tool::Deobfuscate => {
                "bitwright, Strategy::deobfuscate() (linear MBA and shuffle passes)"
            }
            Tool::Mba => {
                "bitwright, deobfuscate with the MBA service and the native SignatureSolver"
            }
            Tool::Nf => {
                "bitwright, deobfuscate with the MBA service, the native NormalFormSolver and \
                 bitwright's own evidence only"
            }
            Tool::BwCobra => "bitwright, deobfuscate with the MBA service and the CoBRA backend",
            Tool::BwEqsat => "bitwright's equality saturation, every built-in equation group",
            Tool::EggBw => "egg with bitwright's equations plus commutativity, default limits",
            Tool::EggMba => "egg with those, MBA identities and constant folding, default limits",
            Tool::CobraCpp => "CoBRA, the upstream C++ tool: cobra-cli's pipeline via cobra-batch",
            Tool::Cobra => "CoBRA's Rust port (cobra-mba 0.4), spot-checked answers like upstream",
            Tool::CobraCert => "CoBRA's Rust port with its defaults: only Lean-certified answers",
            Tool::Z3 => "Z3's simplify (Python bindings, via solvers.py)",
            Tool::Bitwuzla => "Bitwuzla's simplify_term (Python bindings, via solvers.py)",
            Tool::Cvc5 => "cvc5's Solver::simplify (Python bindings, via solvers.py)",
            Tool::Claripy => "angr's claripy.simplify (via solvers.py)",
            Tool::Miasm => "Miasm's expr_simp (via solvers.py)",
            Tool::TritonLlvm => "Triton's simplify through LLVM (via solvers.py)",
            Tool::TritonSynth => "Triton's synthesize (via solvers.py)",
        }
    }
}

/// One line of a dataset: an obfuscated expression and its ground truth.
#[derive(Debug)]
struct Case {
    line: usize,
    input: String,
    truth: String,
}

impl Case {
    /// Some lines give no ground truth (`-`): they are read and checked, but not scored.
    fn has_truth(&self) -> bool {
        !matches!(self.truth.as_str(), "" | "-")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Status {
    /// The answer agrees with the input at every sampled point.
    Ok,
    /// The answer disagrees with the input somewhere: an unsound answer.
    Wrong,
    /// The tool failed, or its answer could not be read back.
    Failed,
    /// bitwright could not read the case (the input or its ground truth).
    Unreadable,
}

/// One case under one tool.
#[derive(Debug)]
struct Row {
    tool: Tool,
    line: usize,
    status: Status,
    /// DAG sizes in bitwright's canonical form.
    input: u32,
    answer: u32,
    truth: u32,
    /// The answer is the ground truth itself (the same canonical node).
    exact: bool,
    /// The dataset's ground truth disagrees with its input at a sampled point.
    bad_truth: bool,
    /// The dataset gives no ground truth for the line.
    no_truth: bool,
    /// The simplification call alone, in microseconds.
    micros: f64,
    /// The heap the call used at its peak, in bytes (in-process tools only).
    heap: Option<usize>,
    note: String,
}

impl Row {
    fn new(tool: Tool, case: &Case) -> Row {
        Row {
            tool,
            line: case.line,
            status: Status::Failed,
            input: 0,
            answer: 0,
            truth: 0,
            exact: false,
            bad_truth: false,
            no_truth: !case.has_truth(),
            micros: 0.0,
            heap: None,
            note: String::new(),
        }
    }

    fn fail(mut self, status: Status, note: impl Into<String>) -> Row {
        self.status = status;
        self.note = note.into();
        self
    }
}

/// The datasets write a logical right shift as `>>` (their values are unsigned).
fn bw_syntax(s: &str) -> String {
    s.replace(">>", ">>u")
}

/// bitwright's parser, or where it declines, the datasets' own syntax (see `read`).
fn parse(cx: &mut Context, s: &str) -> Result<Expr, String> {
    parse_at(cx, s, W)
}

/// [`parse`] at width `w`.
fn parse_at(cx: &mut Context, s: &str, w: Width) -> Result<Expr, String> {
    cx.parse(&bw_syntax(s), &ParseOptions::width(w))
        .map_err(|e| e.to_string())
        .or_else(|e| read::read(cx, s, w).map_err(|_| e))
}

/// The width a case is measured at: 64 bits, unless its ground truth disagrees with its input
/// there and agrees at a narrower one (some OSES lines are 8-bit arithmetic, as `((x + y)·5 +
/// 7)·205 + 101` is `x + y` modulo 2^8 only), then the widest such.
fn case_width(case: &Case) -> Width {
    if !case.has_truth() {
        return W;
    }
    let agrees = |w: Width| -> bool {
        let mut cx = Context::new();
        let (Ok(i), Ok(t)) = (
            parse_at(&mut cx, &case.input, w),
            parse_at(&mut cx, &case.truth, w),
        ) else {
            return false;
        };
        let Ok(syms) = cx.symbols_in(&[i, t]) else {
            return false;
        };
        let keys: Vec<SymbolKey> = syms
            .iter()
            .filter_map(|&s| cx.symbol_key(s).cloned())
            .collect();
        let mut rng = Rng(0x5eed ^ case.line as u64);
        let edges = [0, u64::MAX, 1, 1 << 63];
        let mut env: HashMap<SymbolKey, BitVec> = HashMap::new();
        (0..POINTS).all(|p| {
            for k in &keys {
                let v = edges.get(p).copied().unwrap_or_else(|| rng.next());
                env.insert(k.clone(), BitVec::wrapping_from_u64(w, v));
            }
            matches!(cx.eval(&[i, t], &env), Ok(v) if v[0] == v[1])
        })
    };
    if agrees(W) {
        return W;
    }
    [Width::W32, Width::W16, Width::W8]
        .into_iter()
        .find(|&w| agrees(w))
        .unwrap_or(W)
}

fn dag(cx: &mut Context, e: Expr) -> u32 {
    match cx.dag_size(&[e], u32::MAX) {
        Ok(Bounded::Exact(n) | Bounded::AtLeast(n)) => n,
        _ => 0,
    }
}

/// splitmix64.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

/// Measures `answer` in `cx`, where `input` was read: sizes, whether it is the ground truth,
/// and agreement with the input at [`POINTS`] points (boundary values first, then random). The
/// ground truth is checked the same way, so a dataset error shows as `bad_truth`.
fn measure(cx: &mut Context, input: Expr, answer: Expr, case: &Case, mut row: Row) -> Row {
    // At the input's width (see `case_width`).
    let w = cx.width(input).unwrap_or(W);
    // No ground truth: the input stands in for it (checked, never scored).
    let truth = if case.has_truth() {
        match parse_at(cx, &case.truth, w) {
            Ok(t) => t,
            Err(e) => return row.fail(Status::Unreadable, format!("ground truth: {e}")),
        }
    } else {
        input
    };
    row.input = dag(cx, input);
    row.answer = dag(cx, answer);
    row.truth = dag(cx, truth);
    row.exact = answer == truth;
    let syms = match cx.symbols_in(&[input, answer, truth]) {
        Ok(s) => s,
        Err(e) => return row.fail(Status::Failed, e.to_string()),
    };
    let keys: Vec<SymbolKey> = syms
        .iter()
        .filter_map(|&s| cx.symbol_key(s).cloned())
        .collect();
    let mut rng = Rng(0x5eed ^ case.line as u64);
    let edges = [0, u64::MAX, 1, 1 << 63];
    let mut env: HashMap<SymbolKey, BitVec> = HashMap::new();
    for p in 0..POINTS {
        for k in &keys {
            let v = edges.get(p).copied().unwrap_or_else(|| rng.next());
            env.insert(k.clone(), BitVec::wrapping_from_u64(w, v));
        }
        let vals = match cx.eval(&[input, answer, truth], &env) {
            Ok(v) => v,
            Err(e) => return row.fail(Status::Failed, format!("evaluation: {e}")),
        };
        if vals[1] != vals[0] {
            return row.fail(
                Status::Wrong,
                format!("differs from the input at point {p}"),
            );
        }
        if vals[2] != vals[0] {
            row.bad_truth = true;
        }
    }
    row.status = Status::Ok;
    row
}

fn engine(tool: Tool) -> Result<Engine, String> {
    let mba = |solver: Arc<dyn bitwright::mba::MbaSolver>| {
        Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
            .mba_solver(solver)
            .build()
    };
    let e = match tool {
        Tool::Standard => Ok(Engine::standard()),
        Tool::Deobfuscate => Engine::builder()
            .builtin()
            .strategy(Strategy::deobfuscate())
            .build(),
        Tool::Mba => mba(Arc::new(SignatureSolver)),
        Tool::Nf => Engine::builder()
            .builtin()
            .strategy(
                Strategy::deobfuscate().with_mba(
                    MbaConfig::default()
                        .with_trust(MbaTrust::default().with_backend_certificates(false)),
                ),
            )
            .mba_solver(Arc::new(NormalFormSolver::default()))
            .build(),
        Tool::BwCobra => mba(Arc::new(CobraSolver::default())),
        _ => unreachable!("not a bitwright tool"),
    };
    e.map_err(|e| e.to_string())
}

/// Times and heap cover everything from the text to the answer, parsing included (bitwright's
/// parser builds the canonical, hash-consed form).
fn run_bitwright(tool: Tool, engine: &Engine, case: &Case) -> Row {
    let mut row = Row::new(tool, case);
    let w = case_width(case);
    if w != W {
        row.note = format!("{} bits", w.bits());
    }
    let base = heap::start();
    let t = Instant::now();
    let mut cx = Context::new();
    let input = match parse_at(&mut cx, &case.input, w) {
        Ok(e) => e,
        Err(e) => return row.fail(Status::Unreadable, e),
    };
    let out = engine.run(&mut cx, &[input], Run::default());
    let micros = t.elapsed().as_secs_f64() * 1e6;
    let heap = heap::used_since(base);
    let answer = match out {
        Ok(o) => o.roots[0].expr,
        Err(e) => return row.fail(Status::Failed, e.to_string()),
    };
    let mut row = measure(&mut cx, input, answer, case, row);
    row.micros = micros;
    row.heap = Some(heap);
    if row.status == Status::Ok && !row.no_truth && !row.bad_truth && row.answer > row.truth {
        failure(tool, case, &cx.display(answer).to_string());
    }
    row
}

/// With `BW_FAILURES` set to a file, appends every scored case a bitwright tool leaves larger
/// than the ground truth to it: tool, line, input, ground truth and answer, tab-separated.
fn failure(tool: Tool, case: &Case, answer: &str) {
    let Some(path) = std::env::var_os("BW_FAILURES") else {
        return;
    };
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        let _ = writeln!(
            f,
            "{}\t{}\t{}\t{}\t{}",
            tool.name(),
            case.line,
            case.input,
            case.truth,
            answer.replace('\n', "; ")
        );
    }
}

/// bitwright's equality saturation: the candidate if the search published one (it publishes only
/// a strictly smaller expression from a saturated e-graph), else the input.
fn run_eqsat(sat: &Saturator, case: &Case) -> Row {
    let row = Row::new(Tool::BwEqsat, case);
    let base = heap::start();
    let t = Instant::now();
    let mut cx = Context::new();
    let input = match parse(&mut cx, &case.input) {
        Ok(e) => e,
        Err(e) => return row.fail(Status::Unreadable, e),
    };
    let out = sat.search(&mut cx, &[input], SearchRun::default());
    let micros = t.elapsed().as_secs_f64() * 1e6;
    let heap = heap::used_since(base);
    let (answer, end) = match out {
        Ok(r) => (r.roots[0].candidate.unwrap_or(input), r.roots[0].end),
        Err(e) => return row.fail(Status::Failed, e.to_string()),
    };
    let mut row = measure(&mut cx, input, answer, case, row);
    row.micros = micros;
    row.heap = Some(heap);
    if row.status == Status::Ok {
        row.note = format!("{end:?}");
    }
    row
}

/// egg on the case's own text (see `eggs`); the note says whether the e-graph saturated.
fn run_egg(tool: Tool, rules: &eggs::Rules, case: &Case) -> Row {
    let row = Row::new(tool, case);
    let base = heap::start();
    let t = Instant::now();
    let out = eggs::simplify(rules, &case.input, tool == Tool::EggMba);
    let micros = t.elapsed().as_secs_f64() * 1e6;
    let heap = heap::used_since(base);
    let answer = match out {
        Ok(a) => a,
        Err(e) => return row.fail(Status::Failed, e),
    };
    let mut cx = Context::new();
    let input = match parse(&mut cx, &case.input) {
        Ok(e) => e,
        Err(e) => return row.fail(Status::Unreadable, e),
    };
    let mut row = match parse(&mut cx, &answer.text) {
        Ok(a) => measure(&mut cx, input, a, case, row),
        Err(e) => return row.fail(Status::Failed, format!("reading egg's answer: {e}")),
    };
    row.micros = micros;
    row.heap = Some(heap);
    if row.status == Status::Ok && answer.saturated {
        row.note = "saturated".into();
    }
    row
}

/// CoBRA's Rust port on the case's own text. `cobra-cert` keeps the port's default of answering
/// only with a Lean certificate; `cobra` spot-checks answers, as upstream CoBRA does. The answer
/// is mapped back to the input's variables (CoBRA drops spurious ones), and an outcome of kind
/// `Error` is a failure, as in `cobra-cli`.
fn run_cobra(tool: Tool, case: &Case) -> Row {
    let row = Row::new(tool, case);
    let options = cobra::Options {
        require_lean_certificate: tool == Tool::CobraCert,
        ..cobra::Options::default()
    };
    let mut cx = Context::new();
    let input = match parse(&mut cx, &case.input) {
        Ok(e) => e,
        Err(e) => return row.fail(Status::Unreadable, e),
    };
    let base = heap::start();
    let t = Instant::now();
    let parsed = match cobra::parse_to_ast(&case.input, 64) {
        Ok(p) => p,
        Err(e) => return row.fail(Status::Failed, format!("cobra parse: {e:?}")),
    };
    let out = catch_unwind(AssertUnwindSafe(|| {
        cobra::simplify_expr(&parsed.expr, &parsed.vars, options)
    }));
    let micros = t.elapsed().as_secs_f64() * 1e6;
    let heap = heap::used_since(base);
    let text = match out {
        Ok(Ok(o)) if o.kind == cobra::SimplifyOutcomeKind::Error => {
            return row.fail(Status::Failed, format!("cobra: {}", o.diag.reason));
        }
        Ok(Ok(o)) => {
            let e = cobra::outcome_expr_in_original_space(&o, &parsed.vars)
                .unwrap_or_else(|| parsed.expr.clone());
            cobra::render(&e, &parsed.vars, 64)
        }
        Ok(Err(e)) => return row.fail(Status::Failed, format!("cobra: {e:?}")),
        Err(_) => return row.fail(Status::Failed, "cobra panicked"),
    };
    let answer = match parse(&mut cx, &text) {
        Ok(a) => a,
        Err(e) => return row.fail(Status::Failed, format!("reading {text:?}: {e}")),
    };
    let mut row = measure(&mut cx, input, answer, case, row);
    row.micros = micros;
    row.heap = Some(heap);
    row
}

/// The helper script, next to this crate's manifest.
fn helper() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("solvers.py")
}

/// Whether `python` can import the solver's bindings.
fn available(python: &str, tool: Tool) -> bool {
    Command::new(python)
        .arg(helper())
        .arg(tool.name())
        .arg("--check")
        .output()
        .is_ok_and(|o| o.status.success())
}

/// Every case of a file through one of the Python-driven engines at once (`solvers.py`): each
/// builds the case's own text into its terms, simplifies it, times that call, and answers with an
/// SMT-LIB script defining `answer__`, which is read back here.
fn run_external(tool: Tool, cases: &[&Case], python: &str, scratch: &Path) -> Vec<Row> {
    let request = scratch.join(format!("{}.request.txt", tool.name()));
    let response = scratch.join(format!("{}.response.txt", tool.name()));
    let mut text = String::new();
    for case in cases {
        text.push_str(&case.input);
        text.push('\n');
    }
    let run = std::fs::write(&request, text)
        .map_err(|e| e.to_string())
        .and_then(|()| {
            let o = Command::new(python)
                .arg(helper())
                .arg(tool.name())
                .arg(&request)
                .arg(&response)
                .output()
                .map_err(|e| e.to_string())?;
            if !o.status.success() {
                return Err(String::from_utf8_lossy(&o.stderr).into_owned());
            }
            std::fs::read_to_string(&response).map_err(|e| e.to_string())
        });
    let answers: Vec<String> = match run {
        Ok(r) => r.lines().map(str::to_string).collect(),
        Err(e) => {
            eprintln!("{}: {e}", tool.name());
            Vec::new()
        }
    };
    let mut rows = Vec::with_capacity(cases.len());
    for (k, case) in cases.iter().enumerate() {
        let row = Row::new(tool, case);
        let Some((micros, script)) = answers.get(k).and_then(|l| l.split_once('\t')) else {
            rows.push(row.fail(Status::Failed, "no answer"));
            continue;
        };
        let micros: f64 = micros.parse().unwrap_or(0.0);
        if let Some(e) = script.strip_prefix('!') {
            rows.push(row.fail(Status::Failed, e.to_string()));
            continue;
        }
        let mut cx = Context::new();
        let input = match parse(&mut cx, &case.input) {
            Ok(e) => e,
            Err(e) => {
                rows.push(row.fail(Status::Unreadable, e));
                continue;
            }
        };
        let answer = bitwright::smtlib::import(&mut cx, script)
            .map_err(|e| e.to_string())
            .and_then(|i| i.definition("answer__").ok_or_else(|| "no answer__".into()));
        let mut row = match answer {
            Ok(a) => measure(&mut cx, input, a, case, row),
            Err(e) => row.fail(Status::Failed, format!("reading the answer: {e}")),
        };
        row.micros = micros;
        rows.push(row);
    }
    rows
}

/// Every case of a file through C++ CoBRA at once: `cobra-batch` runs cobra-cli's pipeline on
/// each input line and reports the time, the heap, a status and the answer.
fn run_cobra_cpp(cases: &[&Case], binary: &Path, scratch: &Path) -> Vec<Row> {
    let request = scratch.join("cobra-cpp.request.txt");
    let response = scratch.join("cobra-cpp.response.txt");
    let mut text = String::new();
    for case in cases {
        text.push_str(&case.input);
        text.push('\n');
    }
    let run = std::fs::write(&request, text)
        .map_err(|e| e.to_string())
        .and_then(|()| {
            let o = Command::new(binary)
                .arg(&request)
                .arg(&response)
                .output()
                .map_err(|e| e.to_string())?;
            if !o.status.success() {
                return Err(String::from_utf8_lossy(&o.stderr).into_owned());
            }
            std::fs::read_to_string(&response).map_err(|e| e.to_string())
        });
    let answers: Vec<String> = match run {
        Ok(r) => r.lines().map(str::to_string).collect(),
        Err(e) => {
            eprintln!("cobra-cpp: {e}");
            Vec::new()
        }
    };
    let mut rows = Vec::with_capacity(cases.len());
    for (k, case) in cases.iter().enumerate() {
        let row = Row::new(Tool::CobraCpp, case);
        let fields: Vec<&str> = answers
            .get(k)
            .map_or(Vec::new(), |l| l.splitn(4, '\t').collect());
        let [micros, heap, status, answer] = fields[..] else {
            rows.push(row.fail(Status::Failed, "no answer"));
            continue;
        };
        let micros: f64 = micros.parse().unwrap_or(0.0);
        let heap: Option<usize> = heap.parse().ok();
        if status == "error" {
            let mut row = row.fail(Status::Failed, answer.to_string());
            row.micros = micros;
            rows.push(row);
            continue;
        }
        let mut cx = Context::new();
        let input = match parse(&mut cx, &case.input) {
            Ok(e) => e,
            Err(e) => {
                rows.push(row.fail(Status::Unreadable, e));
                continue;
            }
        };
        let mut row = match parse(&mut cx, answer) {
            Ok(a) => measure(&mut cx, input, a, case, row),
            Err(e) => row.fail(Status::Failed, format!("reading {answer:?}: {e}")),
        };
        if status == "unsupported" && row.status == Status::Ok {
            row.note = "unsupported (answered unchanged)".into();
        }
        row.micros = micros;
        row.heap = heap;
        rows.push(row);
    }
    rows
}

fn load(path: &Path) -> Result<Vec<Case>, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut out = Vec::new();
    for (i, line) in text.lines().enumerate() {
        let l = line.trim();
        if l.is_empty() || l.starts_with('#') {
            continue;
        }
        let mut f = if l.contains('\t') {
            l.split('\t')
        } else {
            l.split(',')
        };
        if let (Some(a), Some(b)) = (f.next(), f.next()) {
            out.push(Case {
                line: i + 1,
                input: a.trim().to_string(),
                truth: b.trim().to_string(),
            });
        }
    }
    Ok(out)
}

fn files(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let p = entry?.path();
        if p.is_dir() {
            files(&p, out)?;
        } else if p.extension().is_some_and(|e| e == "txt") {
            out.push(p);
        }
    }
    Ok(())
}

/// The median and 95th percentile of `xs`.
fn quantiles(mut xs: Vec<f64>) -> (f64, f64) {
    if xs.is_empty() {
        return (f64::NAN, f64::NAN);
    }
    xs.sort_by(f64::total_cmp);
    let at = |q: f64| xs[((xs.len() - 1) as f64 * q).round() as usize];
    (at(0.5), at(0.95))
}

/// One line of the summary for `rows` (one tool).
fn summary(label: &str, tool: Tool, rows: &[&Row]) -> String {
    let n = rows.len();
    let count = |s: Status| rows.iter().filter(|r| r.status == s).count();
    let ok: Vec<&&Row> = rows.iter().filter(|r| r.status == Status::Ok).collect();
    // Lines without a ground truth, or with one that disagrees with the input at every width
    // (a dataset error), are scored apart: whether the answer is smaller.
    let unscored = |r: &Row| r.no_truth || r.bad_truth;
    let untrue = rows.iter().filter(|r| unscored(r)).count();
    let reduced = ok
        .iter()
        .filter(|r| unscored(r) && r.answer < r.input)
        .count();
    let solved = ok
        .iter()
        .filter(|r| !unscored(r) && r.answer <= r.truth)
        .count();
    let exact = ok.iter().filter(|r| !unscored(r) && r.exact).count();
    // Rounded down, so only every scored line solved reads 100.0; `-` without scored lines.
    let scored = n - untrue;
    let pct = |k: usize| {
        (1000 * k)
            .checked_div(scored)
            .map_or("-".to_string(), |t| format!("{:.1}", t as f64 / 10.0))
    };
    let (ratio, _) = quantiles(
        ok.iter()
            .filter(|r| !unscored(r))
            .map(|r| f64::from(r.answer) / f64::from(r.truth.max(1)))
            .collect(),
    );
    let ratio = if ratio.is_nan() {
        "-".to_string()
    } else {
        format!("{ratio:.2}")
    };
    let (t50, t95) = quantiles(ok.iter().map(|r| r.micros).collect());
    let heaps: Vec<f64> = ok
        .iter()
        .filter_map(|r| r.heap)
        .map(|b| b as f64 / 1024.0)
        .collect();
    let heap = if heaps.is_empty() {
        "-".to_string()
    } else {
        format!("{:.0}", quantiles(heaps).0)
    };
    format!(
        "| {label} | {} | {n} | {} | {} | {} | {} | {} | {untrue} | {reduced} | {ratio} | {t50:.0} | {t95:.0} | {heap} |",
        tool.name(),
        pct(solved),
        pct(exact),
        count(Status::Wrong),
        count(Status::Failed),
        count(Status::Unreadable),
    )
}

const HEADER: &str = "| dataset | tool | cases | solved % | exact % | wrong | failed | unread | no truth | reduced | size/truth | µs p50 | µs p95 | heap KB p50 |\n|-|-|-:|-:|-:|-:|-:|-:|-:|-:|-:|-:|-:|-:|";

#[derive(Debug)]
struct Options {
    data: PathBuf,
    only: Vec<String>,
    skip: Vec<String>,
    tools: Vec<Tool>,
    limit: usize,
    csv: Option<PathBuf>,
    python: String,
    cobra_cpp: Option<PathBuf>,
}

fn parse_args() -> Result<Option<Options>, String> {
    let mut data = None;
    let mut o = Options {
        data: PathBuf::new(),
        only: Vec::new(),
        skip: Vec::new(),
        tools: Tool::ALL.to_vec(),
        limit: usize::MAX,
        csv: None,
        python: "python3".into(),
        cobra_cpp: None,
    };
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        let mut value = |name: &str| args.next().ok_or(format!("{name} needs a value"));
        match a.as_str() {
            "--only" => o.only.push(value("--only")?),
            "--skip" => o.skip.push(value("--skip")?),
            "--tools" => {
                o.tools = value("--tools")?
                    .split(',')
                    .map(|t| {
                        Tool::ALL
                            .into_iter()
                            .find(|x| x.name() == t)
                            .ok_or(format!("unknown tool {t} (see --list)"))
                    })
                    .collect::<Result<_, _>>()?;
            }
            "--limit" => {
                o.limit = value("--limit")?
                    .parse()
                    .map_err(|e| format!("--limit: {e}"))?
            }
            "--csv" => o.csv = Some(value("--csv")?.into()),
            "--python" => o.python = value("--python")?,
            "--cobra-cpp" => o.cobra_cpp = Some(value("--cobra-cpp")?.into()),
            "--list" => {
                for t in Tool::ALL {
                    println!("{:<12} {}", t.name(), t.about());
                }
                return Ok(None);
            }
            s if s.starts_with('-') => return Err(format!("unknown option {s}")),
            s => data = Some(PathBuf::from(s)),
        }
    }
    o.data = data.ok_or("which datasets? pass their directory (see README.md)")?;
    Ok(Some(o))
}

fn main() -> ExitCode {
    let o = match parse_args() {
        Ok(Some(o)) => o,
        Ok(None) => return ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            return ExitCode::FAILURE;
        }
    };
    let mut paths = Vec::new();
    if let Err(e) = files(&o.data, &mut paths) {
        eprintln!("error: {}: {e}", o.data.display());
        return ExitCode::FAILURE;
    }
    paths.retain(|p| {
        let s = p.to_string_lossy();
        (o.only.is_empty() || o.only.iter().any(|f| s.contains(f.as_str())))
            && !o.skip.iter().any(|f| s.contains(f.as_str()))
    });
    paths.sort();
    let mut tools = o.tools.clone();
    tools.retain(|&t| {
        let why = match t {
            Tool::CobraCpp if o.cobra_cpp.as_ref().is_none_or(|p| !p.exists()) => {
                Some("no cobra-batch driver (--cobra-cpp PATH)".to_string())
            }
            Tool::Z3
            | Tool::Bitwuzla
            | Tool::Cvc5
            | Tool::Claripy
            | Tool::Miasm
            | Tool::TritonLlvm
            | Tool::TritonSynth
                if !available(&o.python, t) =>
            {
                Some(format!("{} cannot import its bindings", o.python))
            }
            _ => None,
        };
        if let Some(why) = &why {
            eprintln!("skipping {}: {why}", t.name());
        }
        why.is_none()
    });
    let mut engines: HashMap<Tool, Engine> = HashMap::new();
    for &t in &tools {
        if matches!(
            t,
            Tool::Standard | Tool::Deobfuscate | Tool::Mba | Tool::Nf | Tool::BwCobra
        ) {
            match engine(t) {
                Ok(e) => {
                    engines.insert(t, e);
                }
                Err(e) => {
                    eprintln!("error: {}: {e}", t.name());
                    return ExitCode::FAILURE;
                }
            }
        }
    }
    let sat = Saturator::builtin(SaturateConfig::default()).0;
    let egg_rules = eggs::Rules::new();
    let scratch = std::env::temp_dir().join(format!("bitwright-compare-{}", std::process::id()));
    if let Err(e) = std::fs::create_dir_all(&scratch) {
        eprintln!("error: {}: {e}", scratch.display());
        return ExitCode::FAILURE;
    }
    // Each file's results are printed, and its rows written, as soon as the file is done.
    println!("{HEADER}");
    let mut all: Vec<(String, Row)> = Vec::new();
    let mut csv = match &o.csv {
        Some(p) => match std::fs::File::create(p) {
            Ok(f) => Some(std::io::BufWriter::new(f)),
            Err(e) => {
                eprintln!("error: {}: {e}", p.display());
                return ExitCode::FAILURE;
            }
        },
        None => None,
    };
    if let Some(w) = csv.as_mut() {
        let _ = writeln!(
            w,
            "dataset,line,tool,status,input,answer,truth,exact,bad_truth,no_truth,micros,heap,note"
        );
    }
    for path in &paths {
        let label = path
            .strip_prefix(&o.data)
            .unwrap_or(path)
            .to_string_lossy()
            .into_owned();
        let cases = match load(path) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("error: {e}");
                continue;
            }
        };
        let cases: Vec<&Case> = cases.iter().take(o.limit).collect();
        eprintln!("{label}: {} cases", cases.len());
        let mut rows: Vec<Row> = Vec::new();
        for &t in &tools {
            let t0 = Instant::now();
            match t {
                Tool::Cobra | Tool::CobraCert => rows.extend(cases.iter().map(|c| run_cobra(t, c))),
                Tool::BwEqsat => rows.extend(cases.iter().map(|c| run_eqsat(&sat, c))),
                Tool::EggBw | Tool::EggMba => {
                    rows.extend(cases.iter().map(|c| run_egg(t, &egg_rules, c)));
                }
                Tool::Z3
                | Tool::Bitwuzla
                | Tool::Cvc5
                | Tool::Claripy
                | Tool::Miasm
                | Tool::TritonLlvm
                | Tool::TritonSynth => {
                    rows.extend(run_external(t, &cases, &o.python, &scratch));
                }
                Tool::CobraCpp => {
                    let binary = o.cobra_cpp.as_deref().unwrap_or(Path::new(""));
                    rows.extend(run_cobra_cpp(&cases, binary, &scratch));
                }
                _ => {
                    let e = &engines[&t];
                    rows.extend(cases.iter().map(|c| run_bitwright(t, e, c)));
                }
            }
            eprintln!("  {:<12} {:.1}s", t.name(), t0.elapsed().as_secs_f64());
        }
        let bad = rows
            .iter()
            .filter(|r| r.bad_truth)
            .map(|r| r.line)
            .collect::<std::collections::BTreeSet<_>>();
        if !bad.is_empty() {
            eprintln!(
                "  note: {} ground truths disagree with their input",
                bad.len()
            );
        }
        for &t in &tools {
            let mine: Vec<&Row> = rows.iter().filter(|r| r.tool == t).collect();
            println!("{}", summary(&label, t, &mine));
        }
        if let Some(w) = csv.as_mut() {
            for r in &rows {
                let _ = writeln!(
                    w,
                    "{label},{},{},{:?},{},{},{},{},{},{},{:.1},{},{:?}",
                    r.line,
                    r.tool.name(),
                    r.status,
                    r.input,
                    r.answer,
                    r.truth,
                    r.exact,
                    r.bad_truth,
                    r.no_truth,
                    r.micros,
                    r.heap.map_or(String::new(), |h| h.to_string()),
                    r.note,
                );
            }
            let _ = w.flush();
        }
        all.extend(rows.into_iter().map(|r| (label.clone(), r)));
    }
    println!("{}", HEADER.lines().nth(1).unwrap_or(""));
    for &t in &tools {
        let mine: Vec<&Row> = all.iter().map(|(_, r)| r).filter(|r| r.tool == t).collect();
        println!("{}", summary("**all**", t, &mine));
    }
    let _ = std::fs::remove_dir_all(&scratch);
    ExitCode::SUCCESS
}
