//! An SMT-LIB 2 solver session: a script's commands run in order against a
//! [`Solver`](crate::solve::Solver), their responses written as the standard prescribes.

use core::fmt::{self, Write};
use std::collections::BTreeMap;

use super::import::{Arr, Env, EnvMark, Sort, State, Sx, Tok, Val, check};
use crate::engine::{Clock, Deadline};
use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::solve::{Config, CoreItem, Optimum, Solver, Status};
use crate::{BitVec, Width};

/// What a script's run came to.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Summary {
    /// Checks answered `sat`.
    pub sat: u32,
    /// Checks answered `unsat`.
    pub unsat: u32,
    /// Checks answered `unknown`.
    pub unknown: u32,
    /// Commands answered with `(error …)`.
    pub errors: u32,
}

/// Runs an SMT-LIB 2 script as a solver: every command in order, each response written to
/// `out` (one per line, as SMT-LIB prints them), until the end or `(exit)`.
///
/// Commands: everything [`import`](super::import) reads (`set-logic`, `set-info`,
/// `declare-const`, `declare-fun` without parameters, `define-fun`, `assert`), and `push`,
/// `pop`, `minimize`, `maximize`, `get-objectives`, `check-sat`, `check-sat-assuming`,
/// `get-model`, `get-value`, `get-unsat-core`
/// (the `:named` assertions of a core), `get-unsat-assumptions`, `get-info` (`:name`,
/// `:version`, `:reason-unknown`), `set-option` (`:print-success`; any other is accepted and
/// has no effect: models and cores are always available), `echo`, `reset`,
/// `reset-assertions`, `get-assertions`, `get-option`, `get-proof` (after `unsat`: the core as
/// a Lean 4 theorem for `lean` to prove again, in a string) and `exit`. Terms and sorts are the importer's.
///
/// A command that fails (an unsupported one, an ill-sorted term) answers `(error "…")` and the
/// script goes on, as the standard has it; what it had declared before failing stays. The
/// error returned is a syntax error (the whole script must be well formed before any command
/// runs) or `out` failing.
///
/// A name declared in a scope is forgotten when the scope closes, its symbol is not: the
/// context keeps it. `get-model` lists the declared bit-vector, Boolean, floating-point, and
/// array constants along with declared uninterpreted functions (`define-fun`), a floating-point
/// value as its `(fp …)` bits and an array as `((as const …) …)` wrapped in `(store …)`.
///
/// ```
/// let mut cx = bitwright::Context::new();
/// let mut out = String::new();
/// let script = "
///     (declare-const x (_ BitVec 8))
///     (assert (= (bvmul x #x03) #x09))
///     (check-sat)
///     (get-value (x (bvadd x #x01)))
///     (push)
///     (assert (! (bvugt x #x03) :named big))
///     (check-sat)
///     (get-unsat-core)
///     (pop)
///     (check-sat)";
/// let cfg = bitwright::solve::Config::default();
/// let summary = bitwright::smtlib::run(&mut cx, script, &cfg, &mut out)?;
/// assert_eq!(
///     out,
///     "sat\n((x #x03) ((bvadd x #x01) #x04))\nunsat\n(big)\nsat\n"
/// );
/// assert_eq!((summary.sat, summary.unsat), (2, 1));
/// # Ok::<(), bitwright::Error>(())
/// ```
pub fn run(
    cx: &mut Context,
    script: &str,
    cfg: &Config,
    out: &mut dyn Write,
) -> Result<Summary, Error> {
    let mut s = Session::new(cx, cfg);
    s.script(script, out)?;
    Ok(s.summary())
}

/// [`run`] with a time limit for each check: `ticks` of `clock` from the check's start, after
/// which it answers `unknown` (see [`Solver::check_within`] for how closely).
pub fn run_within(
    cx: &mut Context,
    script: &str,
    cfg: &Config,
    clock: &dyn Clock,
    ticks: u64,
    out: &mut dyn Write,
) -> Result<Summary, Error> {
    let mut s = Session::new(cx, cfg).with_time_limit(clock, ticks);
    s.script(script, out)?;
    Ok(s.summary())
}

/// A solver session fed a script in pieces, each command answered as soon as it is complete:
/// what [`run`] does with a whole script, for a script that arrives over time (a pipe from a
/// program that reads each answer before it writes the next command).
///
/// ```
/// let mut cx = bitwright::Context::new();
/// let cfg = bitwright::solve::Config::default();
/// let mut s = bitwright::smtlib::Session::new(&mut cx, &cfg);
/// let mut out = String::new();
/// s.feed("(declare-const x (_ BitVec 8)) (assert (bvult", &mut out)?;
/// s.feed(" x #x02))\n(check-sat)(get-value", &mut out)?;
/// assert_eq!(out, "sat\n");
/// assert!(s.pending());
/// s.feed(" (x))", &mut out)?;
/// assert_eq!(out, "sat\n((x #x00))\n");
/// # Ok::<(), bitwright::Error>(())
/// ```
pub struct Session<'a> {
    cx: &'a mut Context,
    env: Env,
    solver: Solver,
    /// Each assertion's `:named` name and its text as written, by its index in the solver
    /// (a constraint the session added itself has neither).
    names: Vec<Option<String>>,
    texts: Vec<Option<String>>,
    frames: Vec<EnvMark>,
    /// Active bit-vector optimization objectives in declaration (lexicographic) order.
    objectives: Vec<Objective>,
    /// Number of active objectives at each `push`.
    objective_frames: Vec<usize>,
    /// Optimal `(term_text, value)` pairs achieved by the last `sat` check.
    last_objectives: Option<Vec<(String, BitVec)>>,
    /// The assumptions of the last `check-sat-assuming`, as written.
    assumed: Vec<String>,
    /// The same, as predicates.
    assumptions: Vec<Expr>,
    print_success: bool,
    /// Each check's time limit: a clock, and the ticks a check may take.
    limit: Option<(&'a dyn Clock, u64)>,
    summary: Summary,
    /// Text fed and not run yet: the start of a command.
    pending: String,
    /// Of `pending`: how much is scanned, and the scanner's state there.
    scan: Scan,
}

#[derive(Clone)]
struct Objective {
    expr: Expr,
    text: String,
    maximize: bool,
}

/// Where a scan of pending text stands: SMT-LIB's lexical structure, as far as finding the
/// end of a command needs it.
#[derive(Copy, Clone, Default)]
struct Scan {
    at: usize,
    depth: usize,
    /// Inside a string literal, a `|quoted symbol|`, or a comment.
    string: bool,
    quoted: bool,
    comment: bool,
}

impl fmt::Debug for Session<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Session")
            .field("summary", &self.summary)
            .field("depth", &self.frames.len())
            .field("pending", &self.pending.len())
            .finish_non_exhaustive()
    }
}

impl<'a> Session<'a> {
    /// A session on `cx`, its solver configured by `cfg`.
    pub fn new(cx: &'a mut Context, cfg: &Config) -> Self {
        Session {
            cx,
            env: Env::new(true),
            solver: Solver::new(cfg.clone()),
            names: Vec::new(),
            texts: Vec::new(),
            frames: Vec::new(),
            objectives: Vec::new(),
            objective_frames: Vec::new(),
            last_objectives: None,
            assumed: Vec::new(),
            assumptions: Vec::new(),
            print_success: false,
            limit: None,
            summary: Summary::default(),
            pending: String::new(),
            scan: Scan::default(),
        }
    }

    /// A time limit for each check: `ticks` of `clock` from the check's start, after which
    /// it answers `unknown` (see [`Solver::check_within`] for how closely).
    #[must_use]
    pub fn with_time_limit(mut self, clock: &'a dyn Clock, ticks: u64) -> Self {
        self.limit = Some((clock, ticks));
        self
    }

    /// Gives the session's solver answers found elsewhere to answer from and add to
    /// ([`Answers`](crate::solve::Answers)).
    #[must_use]
    pub fn with_answers(mut self, answers: crate::solve::Answers) -> Self {
        self.solver = self.solver.with_answers(answers);
        self
    }

    /// The solver's answers, if it was given any: those and the ones it found since.
    pub fn answers(&self) -> Option<&crate::solve::Answers> {
        self.solver.answers()
    }

    /// The checks answered and the errors so far.
    pub fn summary(&self) -> Summary {
        self.summary
    }

    /// Whether `(exit)` ran: what is fed after it is ignored.
    pub fn exited(&self) -> bool {
        self.env.exited
    }

    /// Whether text was fed that does not end a command yet.
    pub fn pending(&self) -> bool {
        !self.pending.trim().is_empty()
    }

    /// More of the script: every command it completes runs, its response written to `out`.
    /// A command's text may be split anywhere between calls. A command that is not well
    /// formed answers `(error …)` like one that fails; the error returned is `out` failing.
    pub fn feed(&mut self, text: &str, out: &mut dyn Write) -> Result<(), Error> {
        if self.env.exited {
            return Ok(());
        }
        self.pending.push_str(text);
        while let Some(end) = self.complete() {
            let piece: String = self.pending.drain(..end).collect();
            self.scan = Scan::default();
            match check(&piece) {
                Ok(prefixes) => {
                    self.env.reserve(prefixes);
                    // Well formed, so reading it cannot fail.
                    self.forms(&piece, out)?;
                }
                Err(e) => {
                    self.summary.errors += 1;
                    say(out, &error_text(&e))?;
                }
            }
            if self.env.exited {
                self.pending.clear();
                break;
            }
        }
        Ok(())
    }

    /// Where the first command of the pending text ends, once it does: after the `)` that
    /// closes it (or a stray one). The scan goes on from where the last call stopped.
    fn complete(&mut self) -> Option<usize> {
        let bytes = self.pending.as_bytes();
        let s = &mut self.scan;
        while s.at < bytes.len() {
            let c = bytes[s.at];
            s.at += 1;
            if s.comment {
                s.comment = c != b'\n';
            } else if s.string {
                // `""` inside a string closes and reopens it: the same toggling.
                s.string = c != b'"';
            } else if s.quoted {
                s.quoted = c != b'|';
            } else {
                match c {
                    b';' => s.comment = true,
                    b'"' => s.string = true,
                    b'|' => s.quoted = true,
                    b'(' => s.depth += 1,
                    b')' => {
                        s.depth = s.depth.saturating_sub(1);
                        if s.depth == 0 {
                            return Some(s.at);
                        }
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Runs a whole script, as [`run`] does: a syntax error anywhere fails it before any
    /// command runs.
    pub fn script(&mut self, script: &str, out: &mut dyn Write) -> Result<(), Error> {
        let prefixes = check(script)?;
        self.env.reserve(prefixes);
        self.forms(script, out)
    }

    /// Runs the commands of well-formed text in order.
    fn forms(&mut self, text: &str, out: &mut dyn Write) -> Result<(), Error> {
        let mut sx = Sx::default();
        let mut pos = 0;
        while let Some(top) = sx.read(text, &mut pos)? {
            let said = self.command(&sx, top);
            // What reading the command asserted besides what it says (the constraints
            // between the applications of an uninterpreted function): of the current scope.
            self.sides()?;
            let said = match said {
                Ok(Some(text)) => text,
                Ok(None) if self.print_success => "success".to_string(),
                Ok(None) => String::new(),
                Err(e) => {
                    self.summary.errors += 1;
                    error_text(&e)
                }
            };
            if !said.is_empty() {
                say(out, &said)?;
            }
            if self.env.exited {
                break;
            }
        }
        Ok(())
    }

    /// The reader of one command.
    fn state(&mut self) -> State<'_, '_> {
        State::new(self.cx, &mut self.env)
    }

    /// Runs one command: its response, if it prints one.
    fn command(&mut self, sx: &Sx<'_>, id: u32) -> Result<Option<String>, Error> {
        let Some(k) = sx.list(id) else {
            return Err(sx.err(id, "expected a command"));
        };
        let Some((&head, args)) = k.split_first() else {
            return Err(sx.err(id, "empty command"));
        };
        let arity = |ok: bool| {
            if ok {
                Ok(())
            } else {
                Err(sx.err(id, "wrong number of arguments"))
            }
        };
        match sx.sym(head) {
            Some("assert") => {
                arity(args.len() == 1)?;
                let name = named(sx, args[0]).map(str::to_string);
                self.state().command(sx, id)?;
                // The assertion itself is the last the command added.
                if let Some(e) = self.env.out.assertions.pop() {
                    for side in std::mem::take(&mut self.env.out.assertions) {
                        self.solver.assert(self.cx, side)?;
                        self.names.push(None);
                        self.texts.push(None);
                    }
                    self.solver.assert(self.cx, e)?;
                    self.names.push(name);
                    self.texts.push(Some(sx.text(args[0]).to_string()));
                    self.last_objectives = None;
                }
                Ok(None)
            }
            Some("minimize" | "maximize") => {
                arity(args.len() == 1)?;
                let Val::Bv(e) = self.state().term(sx, args[0])? else {
                    return Err(sx.err(args[0], "an objective must be a bit-vector"));
                };
                self.sides()?;
                self.objectives.push(Objective {
                    expr: e,
                    text: sx.text(args[0]).to_string(),
                    maximize: sx.sym(head) == Some("maximize"),
                });
                self.last_objectives = None;
                Ok(None)
            }
            Some("get-objectives") => {
                arity(args.is_empty())?;
                self.need(Status::Sat, "no objectives: the last check was not sat")?;
                let Some(objs) = &self.last_objectives else {
                    return Err(Error::Unsupported(
                        "no objectives: the last check was not sat".into(),
                    ));
                };
                let dummy = self.cx.bool(false)?;
                let mut text = String::from("(objectives\n");
                for (term_text, val) in objs {
                    let _ = writeln!(text, " ({term_text} {})", Value(Val::Bv(dummy), val));
                }
                text.push(')');
                Ok(Some(text))
            }
            Some("push" | "pop") => {
                arity(args.len() <= 1)?;
                let n = match args.first() {
                    Some(&a) => sx.numeral(a)? as usize,
                    None => 1,
                };
                if sx.sym(head) == Some("push") {
                    for _ in 0..n {
                        self.solver.push();
                        self.frames.push(self.env.mark());
                        self.objective_frames.push(self.objectives.len());
                    }
                } else if n > 0 {
                    self.solver.pop(n)?;
                    let keep = self.frames.len() - n;
                    let at = self.frames[keep];
                    let obj_keep = self.objective_frames[keep];
                    self.env.forget(&at);
                    self.frames.truncate(keep);
                    self.objective_frames.truncate(keep);
                    self.objectives.truncate(obj_keep);
                    self.last_objectives = None;
                    self.names.truncate(self.solver.assertions().len());
                    self.texts.truncate(self.solver.assertions().len());
                }
                Ok(None)
            }
            Some("check-sat") => {
                arity(args.is_empty())?;
                self.assumed.clear();
                self.assumptions.clear();
                let status = self.check(&[])?;
                Ok(Some(self.answer(&status)))
            }
            Some("check-sat-assuming") => {
                arity(args.len() == 1)?;
                let Some(lits) = sx.list(args[0]) else {
                    return Err(sx.err(args[0], "expected a list of assumptions"));
                };
                let mut es = Vec::with_capacity(lits.len());
                let mut texts = Vec::with_capacity(lits.len());
                for &l in lits {
                    let Val::Bool(e) = self.state().term(sx, l)? else {
                        return Err(sx.err(l, "an assumption must be Boolean"));
                    };
                    es.push(e);
                    texts.push(sx.text(l).to_string());
                }
                self.assumed = texts;
                self.assumptions.clone_from(&es);
                // What reading the assumptions asserted is part of the question.
                self.sides()?;
                let status = self.check(&es)?;
                Ok(Some(self.answer(&status)))
            }
            Some("get-model") => {
                arity(args.is_empty())?;
                self.need(Status::Sat, "no model: the last check was not sat")?;
                let mut text = String::from("(");
                for (name, e) in self.env.out.symbols.clone() {
                    let Some(&(val, _)) = self.env.globals.get(name.as_str()) else {
                        continue;
                    };
                    let Some(v) = self.solver.value(self.cx, e)? else {
                        continue;
                    };
                    let _ = write!(
                        text,
                        "\n  (define-fun {} () {} {})",
                        Symbol(&name),
                        SortOf(val, v.width()),
                        Value(val, &v)
                    );
                }
                for (name, at) in self.env.wide_symbols.clone() {
                    let wide = self.env.wides[at as usize].clone();
                    if let Some(value) = self.wide_text(&wide)? {
                        let _ = write!(
                            text,
                            "\n  (define-fun {} () (_ BitVec {}) {value})",
                            Symbol(&name),
                            wide.bits
                        );
                    }
                }
                for name in self.env.journal.clone() {
                    let Some(&(val @ Val::Array(idx, _), _)) = self.env.globals.get(name.as_str())
                    else {
                        continue;
                    };
                    let (idx_w, elem_w) = {
                        let mem = &self.env.out.arrays[idx as usize].1;
                        (mem.addr_width(), mem.cell_width())
                    };
                    if let Some(value) = self.array_text(val)? {
                        let _ = write!(
                            text,
                            "\n  (define-fun {} () (Array (_ BitVec {}) (_ BitVec {})) {value})",
                            Symbol(&name),
                            idx_w.bits(),
                            elem_w.bits()
                        );
                    }
                }
                for name in self.env.uf_journal.clone() {
                    if let Some(defn) = self.uf_model_text(&name)? {
                        text.push_str("\n  ");
                        text.push_str(&defn);
                    }
                }
                text.push_str("\n)");
                Ok(Some(text))
            }
            Some("get-value") => {
                arity(args.len() == 1)?;
                let Some(terms) = sx.list(args[0]) else {
                    return Err(sx.err(args[0], "expected a list of terms"));
                };
                self.need(Status::Sat, "no model: the last check was not sat")?;
                let mut vals = Vec::with_capacity(terms.len());
                let mut wides: Vec<(usize, super::import::Wide)> = Vec::new();
                for &t in terms {
                    let val = self.state().term(sx, t)?;
                    if let Val::Wide(at) = val {
                        // Its limbs are read when the others are.
                        wides.push((vals.len(), self.env.wides[at as usize].clone()));
                        let zero = self.cx.bool(false)?;
                        vals.push((t, val, zero));
                        continue;
                    }
                    if matches!(val, Val::Array(..) | Val::Arr(_)) {
                        let zero = self.cx.bool(false)?;
                        vals.push((t, val, zero));
                        continue;
                    }
                    let Some(e) = val.expr() else {
                        return Err(sx.err(t, "a term of this sort has no printed value"));
                    };
                    vals.push((t, val, e));
                }
                // A term read here for the first time (an application of a function, an
                // array read where arrays are compared) is tied to the others by what
                // reading it asserted: the model has to satisfy that too.
                if self.sides()? {
                    let assumptions = self.assumptions.clone();
                    if self.check(&assumptions)? != Status::Sat {
                        return Err(sx.err(args[0], "no model for these terms"));
                    }
                }
                let mut parts = Vec::with_capacity(terms.len());
                for (k, (t, val, e)) in vals.into_iter().enumerate() {
                    if let Some((_, wide)) = wides.iter().find(|(at, _)| *at == k) {
                        let wide = wide.clone();
                        let Some(value) = self.wide_text(&wide)? else {
                            return Err(sx.err(t, "no model"));
                        };
                        parts.push(format!("({} {value})", sx.text(t)));
                        continue;
                    }
                    if matches!(val, Val::Array(..) | Val::Arr(_)) {
                        let Some(value) = self.array_text(val)? else {
                            return Err(sx.err(t, "no model"));
                        };
                        parts.push(format!("({} {value})", sx.text(t)));
                        continue;
                    }
                    let Some(v) = self.solver.value(self.cx, e)? else {
                        return Err(sx.err(t, "no model"));
                    };
                    parts.push(format!("({} {})", sx.text(t), Value(val, &v)));
                }
                Ok(Some(format!("({})", parts.join(" "))))
            }
            Some("get-unsat-core") => {
                arity(args.is_empty())?;
                let core = self.core()?;
                let names: Vec<String> = (core.iter())
                    .filter_map(|c| match *c {
                        CoreItem::Assertion(i) => {
                            self.names[i].as_deref().map(|n| Symbol(n).to_string())
                        }
                        _ => None,
                    })
                    .collect();
                Ok(Some(format!("({})", names.join(" "))))
            }
            Some("get-unsat-assumptions") => {
                arity(args.is_empty())?;
                let core = self.core()?;
                let texts: Vec<&str> = (core.iter())
                    .filter_map(|c| match *c {
                        CoreItem::Assumption(i) => self.assumed.get(i).map(String::as_str),
                        _ => None,
                    })
                    .collect();
                Ok(Some(format!("({})", texts.join(" "))))
            }
            Some("get-proof") => {
                arity(args.is_empty())?;
                self.need(Status::Unsat, "no proof: the last check was not unsat")?;
                // What Lean is to prove again: the core, as a theorem, in a string.
                let name = format!("unsat_{}", self.summary.unsat);
                let theorem = self
                    .solver
                    .lean_theorem(self.cx, &name)?
                    .unwrap_or_default();
                Ok(Some(format!("(lean \"{}\")", theorem.replace('"', "\"\""))))
            }
            Some("get-assertions") => {
                arity(args.is_empty())?;
                let texts: Vec<&str> = self.texts.iter().flatten().map(String::as_str).collect();
                Ok(Some(format!("({})", texts.join("\n "))))
            }
            Some("set-option") => {
                if let [key, value] = *args
                    && sx.sym(key) == Some(":print-success")
                {
                    self.print_success = sx.sym(value) == Some("true");
                }
                Ok(None)
            }
            Some("get-option") => {
                arity(args.len() == 1)?;
                Ok(Some(
                    match sx.sym(args[0]) {
                        Some(":print-success") => {
                            if self.print_success {
                                "true"
                            } else {
                                "false"
                            }
                        }
                        // Always available, whatever a script sets.
                        Some(
                            ":produce-models"
                            | ":produce-unsat-cores"
                            | ":produce-unsat-assumptions"
                            | ":produce-assertions",
                        ) => "true",
                        Some(":produce-proofs" | ":interactive-mode" | ":global-declarations") => {
                            "false"
                        }
                        _ => "unsupported",
                    }
                    .to_string(),
                ))
            }
            Some("get-info") => {
                arity(args.len() == 1)?;
                Ok(Some(match sx.sym(args[0]) {
                    Some(":name") => "(:name \"bitwright\")".to_string(),
                    Some(":version") => {
                        format!("(:version \"{}\")", env!("CARGO_PKG_VERSION"))
                    }
                    Some(":reason-unknown") => match self.solver.status() {
                        Some(Status::Unknown(why)) => format!(
                            "(:reason-unknown \"{}\")",
                            why.to_string().replace('"', "\"\"")
                        ),
                        _ => "(:reason-unknown \"\")".to_string(),
                    },
                    // What the last answer rests on, and the stage that gave it.
                    Some(":tier") => match self.solver.tier() {
                        Some(tier) => format!("(:tier \"{tier}\")"),
                        None => "(:tier \"\")".to_string(),
                    },
                    Some(":decided-by") => match self.solver.decided_by() {
                        Some(by) => format!("(:decided-by \"{by:?}\")"),
                        None => "(:decided-by \"\")".to_string(),
                    },
                    _ => "unsupported".to_string(),
                }))
            }
            Some("echo") => {
                arity(args.len() == 1)?;
                Ok(Some(sx.text(args[0]).to_string()))
            }
            Some("reset" | "reset-assertions") => {
                arity(args.is_empty())?;
                self.solver.reset();
                self.names.clear();
                self.texts.clear();
                self.objectives.clear();
                self.objective_frames.clear();
                self.last_objectives = None;
                self.assumed.clear();
                self.assumptions.clear();
                if sx.sym(head) == Some("reset") {
                    self.frames.clear();
                    self.env.forget(&EnvMark::default());
                    self.print_success = false;
                } else {
                    // The scopes go; what the outermost one declared stays.
                    if let Some(&at) = self.frames.first() {
                        self.env.forget(&at);
                    }
                    self.frames.clear();
                }
                Ok(None)
            }
            _ => {
                // Only `assert` adds assertions; nothing to move.
                self.state().command(sx, id)?;
                Ok(None)
            }
        }
    }

    /// Asserts what reading terms asserted besides what they say (the constraints between
    /// the applications of an uninterpreted function, and of arrays that are compared), in
    /// the current scope. Whether there was any.
    fn sides(&mut self) -> Result<bool, Error> {
        let sides = std::mem::take(&mut self.env.out.assertions);
        for &e in &sides {
            self.solver.assert(self.cx, e)?;
            self.names.push(None);
            self.texts.push(None);
        }
        Ok(!sides.is_empty())
    }

    /// The value of a wide bit-vector in the model, as a literal.
    fn wide_text(&mut self, wide: &super::import::Wide) -> Result<Option<String>, Error> {
        let mut bits = Vec::with_capacity(wide.bits as usize);
        for &limb in &wide.limbs {
            let Some(v) = self.solver.value(self.cx, limb)? else {
                return Ok(None);
            };
            bits.extend((0..v.width().bits()).map(|i| v.bit(i) == Some(true)));
        }
        let mut text = String::with_capacity(bits.len() / 4 + 2);
        if bits.len().is_multiple_of(4) {
            text.push_str("#x");
            for nibble in bits.rchunks(4) {
                let d = nibble
                    .iter()
                    .rev()
                    .fold(0u32, |d, &b| d << 1 | u32::from(b));
                text.push(char::from_digit(d, 16).unwrap_or('0'));
            }
        } else {
            text.push_str("#b");
            text.extend(bits.iter().rev().map(|&b| if b { '1' } else { '0' }));
        }
        Ok(Some(text))
    }

    fn check(&mut self, assumptions: &[Expr]) -> Result<Status, Error> {
        self.last_objectives = None;
        let deadline = self
            .limit
            .map(|(clock, ticks)| Deadline::new(clock, clock.now_ticks().saturating_add(ticks)));
        if self.objectives.is_empty() {
            let status = self.solver.check_within(self.cx, assumptions, deadline)?;
            if status == Status::Sat {
                self.last_objectives = Some(Vec::new());
            }
            return Ok(status);
        }
        let objs = self.objectives.clone();
        let mut pinned: Vec<Expr> = Vec::with_capacity(assumptions.len() + objs.len());
        pinned.extend_from_slice(assumptions);
        let mut solved_objs: Vec<(String, BitVec)> = Vec::with_capacity(objs.len());
        for obj in objs {
            let opt = if obj.maximize {
                self.solver
                    .maximize_within(self.cx, obj.expr, &pinned, deadline)?
            } else {
                self.solver
                    .minimize_within(self.cx, obj.expr, &pinned, deadline)?
            };
            match opt {
                Optimum::Found(val) => {
                    let k = self.cx.constant(&val)?;
                    let eq = self.cx.cmp(crate::CmpOpExt::Eq, obj.expr, k)?;
                    pinned.push(eq);
                    solved_objs.push((obj.text, val));
                }
                Optimum::Unsat => return Ok(Status::Unsat),
                Optimum::Unknown(why) => return Ok(Status::Unknown(why)),
            }
        }
        self.last_objectives = Some(solved_objs);
        Ok(Status::Sat)
    }

    fn answer(&mut self, status: &Status) -> String {
        match status {
            Status::Sat => {
                self.summary.sat += 1;
                "sat"
            }
            Status::Unsat => {
                self.summary.unsat += 1;
                "unsat"
            }
            Status::Unknown(_) => {
                self.summary.unknown += 1;
                "unknown"
            }
        }
        .to_string()
    }

    /// An error unless the last check answered `want`.
    fn need(&self, want: Status, message: &str) -> Result<(), Error> {
        if self.solver.status() == Some(&want) {
            Ok(())
        } else {
            Err(Error::Unsupported(message.into()))
        }
    }

    fn core(&mut self) -> Result<Vec<CoreItem>, Error> {
        self.need(Status::Unsat, "no core: the last check was not unsat")?;
        Ok(self.solver.unsat_core(self.cx)?.unwrap_or_default())
    }

    /// Evaluates an array value in the current model as `(index_width, elem_width, default, map)`.
    #[allow(clippy::type_complexity)]
    fn eval_array_model(
        &mut self,
        val: Val,
        depth: u32,
    ) -> Result<Option<(Width, Width, BitVec, BTreeMap<BitVec, BitVec>)>, Error> {
        if depth > 64 {
            return Ok(None);
        }
        match val {
            Val::Array(m, ver) => {
                let (idx_w, elem_w, init_ver, reads) = {
                    let mem = &self.env.out.arrays[m as usize].1;
                    (
                        mem.addr_width(),
                        mem.cell_width(),
                        mem.initial(),
                        mem.reads().to_vec(),
                    )
                };
                // Infer default cell value if an asserted equality ties this base array to a
                // constant array (or transitively through equal arrays).
                let mut default_cell = BitVec::zero(elem_w);
                let base_val = Val::Array(m, init_ver);
                for &(eq_e, lhs, rhs) in &self.env.array_eqs.clone() {
                    if self
                        .solver
                        .value(self.cx, eq_e)?
                        .is_some_and(|v| !v.is_zero())
                    {
                        let other = if lhs == base_val {
                            Some(rhs)
                        } else if rhs == base_val {
                            Some(lhs)
                        } else {
                            None
                        };
                        if let Some(other_arr) = other
                            && let Some((_, _, d, other_map)) =
                                self.eval_array_model(other_arr, depth + 1)?
                        {
                            default_cell = d;
                            let mut map = other_map;
                            for (ra, rs) in reads.clone() {
                                let (Some(iv), Some(cv)) = (
                                    self.solver.value(self.cx, ra)?,
                                    self.solver.value(self.cx, rs)?,
                                ) else {
                                    return Ok(None);
                                };
                                map.entry(iv).or_insert(cv);
                            }
                            self.apply_array_stores(m, init_ver, ver, &mut map)?;
                            return Ok(Some((idx_w, elem_w, default_cell, map)));
                        }
                    }
                }
                let mut map: BTreeMap<BitVec, BitVec> = BTreeMap::new();
                for (ra, rs) in reads {
                    let (Some(iv), Some(cv)) = (
                        self.solver.value(self.cx, ra)?,
                        self.solver.value(self.cx, rs)?,
                    ) else {
                        return Ok(None);
                    };
                    // Earlier reads first: the first read at an equal address answers.
                    map.entry(iv).or_insert(cv);
                }
                self.apply_array_stores(m, init_ver, ver, &mut map)?;
                Ok(Some((idx_w, elem_w, default_cell, map)))
            }
            Val::Arr(k) => match self.env.arrs[k as usize] {
                Arr::Const(idx_w, elem_e) => {
                    let elem_w = self.cx.width(elem_e)?;
                    let Some(dv) = self.solver.value(self.cx, elem_e)? else {
                        return Ok(None);
                    };
                    Ok(Some((idx_w, elem_w, dv, BTreeMap::new())))
                }
                Arr::Ite(cond, t_arr, e_arr) => {
                    let Some(cv) = self.solver.value(self.cx, cond)? else {
                        return Ok(None);
                    };
                    let chosen = if !cv.is_zero() { t_arr } else { e_arr };
                    self.eval_array_model(chosen, depth + 1)
                }
                Arr::Store(base, i_e, v_e) => {
                    let Some((idx_w, elem_w, dv, mut map)) =
                        self.eval_array_model(base, depth + 1)?
                    else {
                        return Ok(None);
                    };
                    let (Some(iv), Some(vv)) = (
                        self.solver.value(self.cx, i_e)?,
                        self.solver.value(self.cx, v_e)?,
                    ) else {
                        return Ok(None);
                    };
                    map.insert(iv, vv);
                    Ok(Some((idx_w, elem_w, dv, map)))
                }
            },
            _ => Ok(None),
        }
    }

    fn apply_array_stores(
        &mut self,
        m: u32,
        init_ver: crate::memory::Version,
        mut cur: crate::memory::Version,
        map: &mut BTreeMap<BitVec, BitVec>,
    ) -> Result<(), Error> {
        let mut chain: Vec<(Expr, Expr)> = Vec::new();
        while cur != init_ver {
            let Some(&(_, _, parent, i_e, v_e)) = self
                .env
                .array_stores
                .iter()
                .find(|&&(arr, v, ..)| arr == m && v == cur)
            else {
                break;
            };
            chain.push((i_e, v_e));
            cur = parent;
        }
        for (i_e, v_e) in chain.into_iter().rev() {
            if let (Some(iv), Some(vv)) = (
                self.solver.value(self.cx, i_e)?,
                self.solver.value(self.cx, v_e)?,
            ) {
                map.insert(iv, vv);
            }
        }
        Ok(())
    }

    /// Formats an array term's value in the current model as SMT-LIB 2.6 syntax.
    fn array_text(&mut self, val: Val) -> Result<Option<String>, Error> {
        let Some((idx_w, elem_w, default_bv, map)) = self.eval_array_model(val, 0)? else {
            return Ok(None);
        };
        let dummy = self.cx.bool(false)?;
        let mut term = format!(
            "((as const (Array (_ BitVec {}) (_ BitVec {}))) {})",
            idx_w.bits(),
            elem_w.bits(),
            Value(Val::Bv(dummy), &default_bv)
        );
        for (k, v) in map {
            if v != default_bv {
                term = format!(
                    "(store {term} {} {})",
                    Value(Val::Bv(dummy), &k),
                    Value(Val::Bv(dummy), &v)
                );
            }
        }
        Ok(Some(term))
    }

    /// Formats a `define-fun` table for a declared uninterpreted function in the current model.
    fn uf_model_text(&mut self, name: &str) -> Result<Option<String>, Error> {
        let Some(uf) = self.env.ufs.get(name).cloned() else {
            return Ok(None);
        };
        let dummy = self.cx.bool(false)?;
        let sort_text = |s: Sort| -> String {
            match s {
                Sort::Bool => "Bool".into(),
                Sort::Bv(w) => format!("(_ BitVec {})", w.bits()),
                Sort::Fp(f) => format!("(_ FloatingPoint {} {})", f.eb(), f.sb()),
                _ => "Bool".into(),
            }
        };
        let default_val = |s: Sort| -> (Val, BitVec) {
            match s {
                Sort::Bool => (Val::Bool(dummy), BitVec::zero(Width::W1)),
                Sort::Bv(w) => (Val::Bv(dummy), BitVec::zero(w)),
                Sort::Fp(f) => (Val::Fp(dummy, f), f.zero(false)),
                _ => (Val::Bool(dummy), BitVec::zero(Width::W1)),
            }
        };
        let mut params_str = String::new();
        for (i, &ps) in uf.params.iter().enumerate() {
            if i > 0 {
                params_str.push(' ');
            }
            let _ = write!(params_str, "(x!{i} {})", sort_text(ps));
        }
        let ret_str = sort_text(uf.result);

        // Collect distinct evaluated application rows `(arg_conds_key, cond_str, result_str)`.
        let apps: Vec<(Vec<Val>, Val)> = self
            .env
            .apps
            .iter()
            .filter(|a| a.function == name)
            .map(|a| (a.args.clone(), a.result))
            .collect();
        let mut rows: Vec<(Vec<u128>, String, String)> = Vec::new();
        let mut seen_keys: Vec<Vec<(Sort, BitVec)>> = Vec::new();
        for (args, res) in apps {
            let Some(re) = res.expr() else { continue };
            let Some(rv) = self.solver.value(self.cx, re)? else {
                continue;
            };
            let mut key: Vec<(Sort, BitVec)> = Vec::with_capacity(args.len());
            let mut conds: Vec<String> = Vec::with_capacity(args.len());
            let mut ok = true;
            for (i, (&av, &ps)) in args.iter().zip(&uf.params).enumerate() {
                let Some(ae) = av.expr() else {
                    ok = false;
                    break;
                };
                let Some(mut bv) = self.solver.value(self.cx, ae)? else {
                    ok = false;
                    break;
                };
                if let Sort::Fp(f) = ps
                    && f.test(crate::fp::FpTest::Nan, &bv).unwrap_or(false)
                {
                    bv = f.nan();
                    conds.push(format!("(fp.isNaN x!{i})"));
                } else {
                    conds.push(format!("(= x!{i} {})", Value(av, &bv)));
                }
                key.push((ps, bv));
            }
            if !ok || seen_keys.contains(&key) {
                continue;
            }
            seen_keys.push(key);
            let cond = if conds.len() == 1 {
                conds.remove(0)
            } else {
                format!("(and {})", conds.join(" "))
            };
            let res_str = Value(res, &rv).to_string();
            rows.push((Vec::new(), cond, res_str));
        }
        let body = if let Some((_, _, last_res)) = rows.pop() {
            let mut acc = last_res;
            for (_, cond, res_str) in rows.into_iter().rev() {
                if res_str != acc {
                    acc = format!("(ite {cond} {res_str} {acc})");
                }
            }
            acc
        } else {
            let (dv_kind, dv_bv) = default_val(uf.result);
            Value(dv_kind, &dv_bv).to_string()
        };
        Ok(Some(format!(
            "(define-fun {} ({params_str}) {ret_str} {body})",
            Symbol(name)
        )))
    }
}

/// Writes one response and its line end.
fn say(out: &mut dyn Write, text: &str) -> Result<(), Error> {
    writeln!(out, "{text}").map_err(|_| Error::Unsupported("the output failed".into()))
}

/// An error as SMT-LIB's response to the command that failed.
fn error_text(e: &Error) -> String {
    format!("(error \"{}\")", e.to_string().replace('"', "\"\""))
}

/// The name of an assertion written `(! t … :named n …)`.
fn named<'s>(sx: &Sx<'s>, id: u32) -> Option<&'s str> {
    let k = sx.list(id)?;
    if sx.sym(*k.first()?) != Some("!") {
        return None;
    }
    let at = k.iter().position(|&a| sx.sym(a) == Some(":named"))?;
    match sx.tok(*k.get(at + 1)?) {
        Tok::Sym(n) => Some(n),
        _ => None,
    }
}

/// A symbol as SMT-LIB spells it: in bars unless it is a simple symbol.
struct Symbol<'n>(&'n str);

impl fmt::Display for Symbol<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let simple = !self.0.is_empty()
            && !self.0.starts_with(|c: char| c.is_ascii_digit())
            && (self.0.chars())
                .all(|c| c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c));
        if simple {
            f.write_str(self.0)
        } else {
            write!(f, "|{}|", self.0)
        }
    }
}

/// The sort of a value of this kind and width.
struct SortOf(Val, Width);

impl fmt::Display for SortOf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Val::Bool(_) => f.write_str("Bool"),
            Val::Int(_) => f.write_str("Int"),
            Val::RmVar(_) => f.write_str("RoundingMode"),
            Val::Fp(_, format) => write!(f, "(_ FloatingPoint {} {})", format.eb(), format.sb()),
            _ => write!(f, "(_ BitVec {})", self.1.bits()),
        }
    }
}

/// A value as a term of its sort.
struct Value<'v>(Val, &'v BitVec);

impl fmt::Display for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let v = self.1;
        let n = v.width().bits();
        let bits = |f: &mut fmt::Formatter<'_>, hi: u16, lo: u16| {
            f.write_str("#b")?;
            (lo..hi)
                .rev()
                .try_for_each(|i| f.write_str(if v.bit(i) == Some(true) { "1" } else { "0" }))
        };
        match self.0 {
            Val::Bool(_) => f.write_str(if v.is_zero() { "false" } else { "true" }),
            Val::Int(_) => f.write_str(&super::import::decimal(v)),
            Val::RmVar(_) => f.write_str(
                ["RNE", "RNA", "RTP", "RTN", "RTZ"]
                    .get(v.to_u64().unwrap_or(0) as usize)
                    .copied()
                    .unwrap_or("RNE"),
            ),
            Val::Fp(_, format) => {
                let frac = format.sb() as u16 - 1;
                f.write_str("(fp ")?;
                bits(f, n, n - 1)?;
                f.write_str(" ")?;
                bits(f, n - 1, frac)?;
                f.write_str(" ")?;
                bits(f, frac, 0)?;
                f.write_str(")")
            }
            _ if n.is_multiple_of(4) => {
                f.write_str("#x")?;
                (0..n / 4).rev().try_for_each(|d| {
                    let digit = (0..4).fold(0u32, |acc, b| {
                        acc | u32::from(v.bit(d * 4 + b) == Some(true)) << b
                    });
                    write!(f, "{digit:x}")
                })
            }
            _ => bits(f, n, 0),
        }
    }
}
