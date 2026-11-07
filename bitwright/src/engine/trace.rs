//! A recorder of runs: [`Trace`] receives every event of a run and writes the run out as JSON
//! Lines, for a viewer, a diff, or a bug report.

use std::collections::HashMap;
use std::fmt::Write as _;

use super::{
    Budget, By, CertStats, Decline, End, Engine, Event, Exhausted, MbaStats, Observer, Outcome,
    PassCounts, Phase, Reject, Stage, Stats,
};
use crate::error::Error;
use crate::expr::{Context, Expr, View};
use crate::facts::Reliance;
use crate::hash::IdMap;
use crate::ops::CmpOpExt;

/// Records a run's events and writes them out as a trace.
///
/// Give it to [`Run::with_observer`](super::Run::with_observer), then write the run with
/// [`to_jsonl`](Trace::to_jsonl):
///
/// ```
/// use bitwright::engine::{Engine, Run, Trace};
/// use bitwright::{Context, ParseOptions, Width};
///
/// let engine = Engine::standard();
/// let mut cx = Context::new();
/// let e = cx.parse("((x ^ 0x5a) + 3 - 3) ^ 0x5a", &ParseOptions::width(Width::W32))?;
/// let mut trace = Trace::new(&engine);
/// let out = engine.run(&mut cx, &[e], Run::default().with_observer(&mut trace))?;
/// let text = trace.to_jsonl(&cx, &[e], &out)?;
/// assert!(text.lines().any(|l| l.contains(r#""ev":"applied","pass":"linear""#)));
/// # Ok::<(), bitwright::Error>(())
/// ```
///
/// # Format
///
/// One JSON object per line, in this order (format 1):
///
/// - a header: `{"trace":"bitwright","format":1,"version":…,"strategy":…,"max_rounds":…,
///   "phases":[{"name":"fact_fold"},{"name":"local","groups":[…]},…]}`;
/// - each rule and host rewrite the events name, numbered from 0 in order of appearance:
///   `{"rule":0,"name":"core.arith::add_xor_and","id":"…"}`, `{"rewrite":0,"name":…}`;
/// - each node the events and results name, with every node below it, operands first:
///   `{"node":12,"op":"add","w":32,"args":[5,9],"text":"x + y"}`. `op` is `const` (with
///   `value`), `sym` (with `name`), a unary or binary operator's name, `cmp` (with `pred`, its
///   spelling: `<u`), `zext`, `sext`, `extract` (with `lo`), `concat`, `select`, `fp` (with
///   `fp_op` and `format`) or `ext` (with `output`). Node numbers are the context's own, so a
///   node keeps its number across the whole trace: equal numbers are equal expressions. Only
///   the nodes events name carry `text`, the expression as the printer writes it;
/// - the events, in order: `{"ev":"root","index":0,"root":20}` (with `"again":true` for a root
///   worked on again), `{"ev":"stage","stage":"cases","before":…,"after":…}`,
///   `{"ev":"phase_begin","round":0,"phase":1,"root":…}`, `{"ev":"candidate","rule":3,"node":…}`,
///   `{"ev":"no_match","rule":3}` (also `guard_false`, `degraded`, `no_change`),
///   `{"ev":"applied","rule":3,"before":…,"after":…}` (or `"pass":"linear"`, or
///   `"rewrite":0`), `{"ev":"relied","on":[0,2]}` (with `"later":true` when constraints from
///   63 on may be among them), `{"ev":"vetoed",…}`, `{"ev":"rejected",…,"reason":"verify"}`,
///   `{"ev":"phase_end","round":0,"phase":1,"root":…,"spent":{"node_visits":16,…}}` (the
///   nonzero work only; with `"stopped":"node_visits"` when a limit stopped it);
/// - each root's result: `{"result":0,"input":20,"expr":31,"changed":true,"end":"completed",
///   "relies_on":[]}` (`end` is also `budget_terminated`, with `stopped`, or `declined`, with
///   `cap`);
/// - the run's counters: `{"stats":{…}}`, every field of [`Stats`] by name.
///
/// The same run of the same engine on the same input writes the same trace.
#[derive(Clone, Debug)]
pub struct Trace {
    strategy: String,
    max_rounds: u8,
    phases: Vec<(&'static str, Vec<String>)>,
    rules: Vec<(String, String)>,
    rule_index: HashMap<String, u32>,
    rewrites: Vec<String>,
    rewrite_index: HashMap<String, u32>,
    records: Vec<Rec>,
}

/// What made a rewrite, by its number in the trace.
#[derive(Copy, Clone, Debug)]
enum Who {
    Rule(u32),
    Pass(&'static str),
    Rewrite(u32),
}

/// An event, owned.
#[derive(Copy, Clone, Debug)]
enum Rec {
    Candidate(u32, Expr),
    NoMatch(u32),
    GuardFalse(u32),
    Degraded(u32),
    NoChange(u32),
    Applied(Who, Expr, Expr),
    Vetoed(Who),
    Rejected(Who, Reject),
    Relied(Reliance),
    Root(usize, Expr, bool),
    Stage(Stage, Expr, Expr),
    PhaseBegin(u8, usize, Expr),
    PhaseEnd(u8, usize, Expr, Budget, Option<Exhausted>),
}

impl Trace {
    /// The trace format this version writes.
    pub const FORMAT: u32 = 1;

    /// An empty trace of runs of `engine` (its strategy goes in the header).
    pub fn new(engine: &Engine) -> Trace {
        let s = engine.strategy();
        Trace {
            strategy: s.name.to_string(),
            max_rounds: s.max_rounds,
            phases: s
                .phases
                .iter()
                .map(|p| match p {
                    Phase::Local { groups } => (p.name(), groups.clone()),
                    p => (p.name(), Vec::new()),
                })
                .collect(),
            rules: Vec::new(),
            rule_index: HashMap::new(),
            rewrites: Vec::new(),
            rewrite_index: HashMap::new(),
            records: Vec::new(),
        }
    }

    /// The number of events recorded.
    pub fn len(&self) -> usize {
        self.records.len()
    }

    /// Whether no event was recorded.
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    fn rule(&mut self, rule: &crate::rules::Rule) -> u32 {
        if let Some(&k) = self.rule_index.get(rule.name.as_str()) {
            return k;
        }
        let k = self.rules.len() as u32;
        self.rules.push((rule.name.clone(), rule.id.to_string()));
        self.rule_index.insert(rule.name.clone(), k);
        k
    }

    fn who(&mut self, by: By<'_>) -> Who {
        match by {
            By::Rule(r) => Who::Rule(self.rule(r)),
            By::Pass(p) => Who::Pass(p),
            By::Rewrite(name) => Who::Rewrite(match self.rewrite_index.get(name) {
                Some(&k) => k,
                None => {
                    let k = self.rewrites.len() as u32;
                    self.rewrites.push(name.to_string());
                    self.rewrite_index.insert(name.to_string(), k);
                    k
                }
            }),
        }
    }

    /// The run as a trace: the header, the rules and nodes the events name, the events, the
    /// result of each root (`roots[i]` is answered by `outcome.roots[i]`) and the counters. See
    /// [`Trace`] for the format. Fails when an expression is not of `cx`.
    pub fn to_jsonl(
        &self,
        cx: &Context,
        roots: &[Expr],
        outcome: &Outcome,
    ) -> Result<String, Error> {
        // The nodes the trace names directly, in order of first mention.
        let mut named: Vec<u32> = Vec::new();
        let mut seen: IdMap<u32, ()> = IdMap::default();
        let mut name = |e: Expr| -> Result<(), Error> {
            let i = cx.id(e)?;
            if seen.insert(i, ()).is_none() {
                named.push(i);
            }
            Ok(())
        };
        for (&input, r) in roots.iter().zip(&outcome.roots) {
            name(input)?;
            name(r.expr)?;
        }
        for rec in &self.records {
            match *rec {
                Rec::Candidate(_, e) | Rec::Root(_, e, _) | Rec::PhaseBegin(_, _, e) => name(e)?,
                Rec::PhaseEnd(_, _, e, ..) => name(e)?,
                Rec::Applied(_, a, b) | Rec::Stage(_, a, b) => {
                    name(a)?;
                    name(b)?;
                }
                Rec::NoMatch(_)
                | Rec::GuardFalse(_)
                | Rec::Degraded(_)
                | Rec::NoChange(_)
                | Rec::Vetoed(_)
                | Rec::Rejected(..)
                | Rec::Relied(_) => {}
            }
        }
        let direct = seen;

        let mut out = String::new();
        self.header(&mut out);
        for (k, (n, id)) in self.rules.iter().enumerate() {
            out.push_str("{\"rule\":");
            num(&mut out, k as u64);
            out.push_str(",\"name\":");
            jstr(&mut out, n);
            out.push_str(",\"id\":");
            jstr(&mut out, id);
            out.push_str("}\n");
        }
        for (k, n) in self.rewrites.iter().enumerate() {
            out.push_str("{\"rewrite\":");
            num(&mut out, k as u64);
            out.push_str(",\"name\":");
            jstr(&mut out, n);
            out.push_str("}\n");
        }

        // Every node below the named ones, operands first, each once.
        let mut written: IdMap<u32, ()> = IdMap::default();
        let mut stack: Vec<(u32, bool)> = Vec::new();
        for &top in &named {
            stack.push((top, false));
            while let Some((i, expanded)) = stack.pop() {
                if expanded {
                    node_line(&mut out, cx, i, direct.contains_key(&i));
                    continue;
                }
                if written.insert(i, ()).is_some() {
                    continue;
                }
                stack.push((i, true));
                let kids: Vec<u32> = cx.node(i).children().collect();
                for &c in kids.iter().rev() {
                    if !written.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
            }
        }

        let id = |e: Expr| cx.id(e).unwrap_or(0) as u64;
        for rec in &self.records {
            out.push_str("{\"ev\":");
            match *rec {
                Rec::Candidate(r, e) => {
                    out.push_str("\"candidate\",\"rule\":");
                    num(&mut out, u64::from(r));
                    field(&mut out, "node", id(e));
                }
                Rec::NoMatch(r) | Rec::GuardFalse(r) | Rec::Degraded(r) | Rec::NoChange(r) => {
                    jstr(
                        &mut out,
                        match rec {
                            Rec::NoMatch(_) => "no_match",
                            Rec::GuardFalse(_) => "guard_false",
                            Rec::Degraded(_) => "degraded",
                            _ => "no_change",
                        },
                    );
                    field(&mut out, "rule", u64::from(r));
                }
                Rec::Applied(w, a, b) => {
                    out.push_str("\"applied\"");
                    who(&mut out, w);
                    field(&mut out, "before", id(a));
                    field(&mut out, "after", id(b));
                }
                Rec::Vetoed(w) => {
                    out.push_str("\"vetoed\"");
                    who(&mut out, w);
                }
                Rec::Rejected(w, reason) => {
                    out.push_str("\"rejected\"");
                    who(&mut out, w);
                    out.push_str(",\"reason\":");
                    jstr(&mut out, reject_name(reason));
                }
                Rec::Relied(on) => {
                    out.push_str("\"relied\",\"on\":");
                    reliance(&mut out, on, "later");
                }
                Rec::Root(index, e, again) => {
                    out.push_str("\"root\"");
                    field(&mut out, "index", index as u64);
                    field(&mut out, "root", id(e));
                    if again {
                        out.push_str(",\"again\":true");
                    }
                }
                Rec::Stage(stage, a, b) => {
                    out.push_str("\"stage\",\"stage\":");
                    jstr(&mut out, stage.name());
                    field(&mut out, "before", id(a));
                    field(&mut out, "after", id(b));
                }
                Rec::PhaseBegin(round, phase, e) => {
                    out.push_str("\"phase_begin\"");
                    field(&mut out, "round", u64::from(round));
                    field(&mut out, "phase", phase as u64);
                    field(&mut out, "root", id(e));
                }
                Rec::PhaseEnd(round, phase, e, spent, stopped) => {
                    out.push_str("\"phase_end\"");
                    field(&mut out, "round", u64::from(round));
                    field(&mut out, "phase", phase as u64);
                    field(&mut out, "root", id(e));
                    out.push_str(",\"spent\":");
                    budget(&mut out, &spent);
                    if let Some(why) = stopped {
                        out.push_str(",\"stopped\":");
                        jstr(&mut out, exhausted_name(why));
                    }
                }
            }
            out.push_str("}\n");
        }

        for (k, (&input, r)) in roots.iter().zip(&outcome.roots).enumerate() {
            out.push_str("{\"result\":");
            num(&mut out, k as u64);
            field(&mut out, "input", id(input));
            field(&mut out, "expr", id(r.expr));
            out.push_str(if r.changed {
                ",\"changed\":true"
            } else {
                ",\"changed\":false"
            });
            out.push_str(",\"end\":");
            match r.end {
                End::Completed => jstr(&mut out, "completed"),
                End::BudgetTerminated(why) => {
                    jstr(&mut out, "budget_terminated");
                    out.push_str(",\"stopped\":");
                    jstr(&mut out, exhausted_name(why));
                }
                End::Declined(Decline::AdmissionCap(cap)) => {
                    jstr(&mut out, "declined");
                    out.push_str(",\"cap\":");
                    jstr(
                        &mut out,
                        match cap {
                            super::Cap::Height => "height",
                            super::Cap::TreeSize => "tree_size",
                            super::Cap::DagSize => "dag_size",
                        },
                    );
                }
            }
            out.push_str(",\"relies_on\":");
            reliance(&mut out, r.relies_on, "relies_on_later");
            out.push_str("}\n");
        }

        out.push_str("{\"stats\":");
        stats(&mut out, &outcome.stats);
        out.push_str("}\n");
        Ok(out)
    }

    fn header(&self, out: &mut String) {
        out.push_str("{\"trace\":\"bitwright\"");
        field(out, "format", u64::from(Trace::FORMAT));
        out.push_str(",\"version\":");
        jstr(out, env!("CARGO_PKG_VERSION"));
        out.push_str(",\"strategy\":");
        jstr(out, &self.strategy);
        field(out, "max_rounds", u64::from(self.max_rounds));
        out.push_str(",\"phases\":[");
        for (k, (name, groups)) in self.phases.iter().enumerate() {
            if k > 0 {
                out.push(',');
            }
            out.push_str("{\"name\":");
            jstr(out, name);
            if !groups.is_empty() {
                out.push_str(",\"groups\":[");
                for (j, g) in groups.iter().enumerate() {
                    if j > 0 {
                        out.push(',');
                    }
                    jstr(out, g);
                }
                out.push(']');
            }
            out.push('}');
        }
        out.push_str("]}\n");
    }
}

impl Observer for Trace {
    fn event(&mut self, event: Event<'_>) {
        let rec = match event {
            Event::Candidate { rule, node } => Rec::Candidate(self.rule(rule), node),
            Event::NoMatch { rule } => Rec::NoMatch(self.rule(rule)),
            Event::GuardFalse { rule } => Rec::GuardFalse(self.rule(rule)),
            Event::Degraded { rule } => Rec::Degraded(self.rule(rule)),
            Event::NoChange { rule } => Rec::NoChange(self.rule(rule)),
            Event::Applied { by, before, after } => Rec::Applied(self.who(by), before, after),
            Event::Vetoed { by } => Rec::Vetoed(self.who(by)),
            Event::Rejected { by, reason } => Rec::Rejected(self.who(by), reason),
            Event::Relied { on } => Rec::Relied(on),
            Event::Root { index, root, again } => Rec::Root(index, root, again),
            Event::Stage {
                stage,
                before,
                after,
            } => Rec::Stage(stage, before, after),
            Event::PhaseBegin { round, phase, root } => Rec::PhaseBegin(round, phase, root),
            Event::PhaseEnd {
                round,
                phase,
                root,
                spent,
                stopped,
            } => Rec::PhaseEnd(round, phase, root, spent, stopped),
        };
        self.records.push(rec);
    }
}

/// One node's line.
fn node_line(out: &mut String, cx: &Context, i: u32, text: bool) {
    out.push_str("{\"node\":");
    num(out, u64::from(i));
    out.push_str(",\"op\":");
    let e = cx.handle(i);
    match cx.view_of(i) {
        View::Const(v) => {
            jstr(out, "const");
            out.push_str(",\"value\":");
            jstr(out, &format!("{v:#x}"));
        }
        View::Sym(s) => {
            jstr(out, "sym");
            out.push_str(",\"name\":");
            match cx.symbol_key(s) {
                Some(k) => jstr(out, &k.to_string()),
                None => out.push_str("null"),
            }
        }
        View::Un(op, _) => jstr(out, op.name()),
        View::Bin(op, ..) => jstr(out, op.name()),
        View::Cmp(op, ..) => {
            jstr(out, "cmp");
            out.push_str(",\"pred\":");
            jstr(out, CmpOpExt::from(op).symbol());
        }
        View::Zext(_) => jstr(out, "zext"),
        View::Sext(_) => jstr(out, "sext"),
        View::Extract { lo, .. } => {
            jstr(out, "extract");
            field(out, "lo", u64::from(lo));
        }
        View::Concat { .. } => jstr(out, "concat"),
        View::Select { .. } => jstr(out, "select"),
        View::Fp { op, format, .. } => {
            jstr(out, "fp");
            out.push_str(",\"fp_op\":");
            jstr(out, &format!("{op:?}"));
            out.push_str(",\"format\":");
            jstr(out, &format!("{format}"));
        }
        View::Ext { output, .. } => {
            jstr(out, "ext");
            field(out, "output", u64::from(output));
        }
    }
    field(out, "w", u64::from(cx.width_of(i).bits()));
    let mut kids = cx.node(i).children().peekable();
    if kids.peek().is_some() {
        out.push_str(",\"args\":[");
        for (k, c) in kids.enumerate() {
            if k > 0 {
                out.push(',');
            }
            num(out, u64::from(c));
        }
        out.push(']');
    }
    if text {
        out.push_str(",\"text\":");
        jstr(out, &cx.display(e).to_string());
    }
    out.push_str("}\n");
}

fn who(out: &mut String, w: Who) {
    match w {
        Who::Rule(r) => field(out, "rule", u64::from(r)),
        Who::Pass(p) => {
            out.push_str(",\"pass\":");
            jstr(out, p);
        }
        Who::Rewrite(r) => field(out, "rewrite", u64::from(r)),
    }
}

/// The constraint indices as an array; and `"<later>":true` after it when constraints from 63 on
/// may be among them.
fn reliance(out: &mut String, r: Reliance, later: &str) {
    let (ids, rest) = r.indices();
    out.push('[');
    for (k, i) in ids.enumerate() {
        if k > 0 {
            out.push(',');
        }
        num(out, u64::from(i));
    }
    out.push(']');
    if rest {
        out.push_str(",\"");
        out.push_str(later);
        out.push_str("\":true");
    }
}

/// The nonzero fields of a budget, as an object.
fn budget(out: &mut String, b: &Budget) {
    let Budget {
        node_visits,
        candidates,
        match_steps,
        rewrites,
        new_nodes,
        fact_work,
        pass_work,
        mba_calls,
        mba_steps,
        eqsat_nodes,
        eqsat_work,
    } = *b;
    let mut o = Obj::new(out);
    for (k, v) in [
        ("node_visits", node_visits),
        ("candidates", candidates),
        ("match_steps", match_steps),
        ("rewrites", rewrites),
        ("new_nodes", new_nodes),
        ("fact_work", fact_work),
        ("pass_work", pass_work),
        ("mba_calls", mba_calls),
        ("mba_steps", mba_steps),
        ("eqsat_nodes", eqsat_nodes),
        ("eqsat_work", eqsat_work),
    ] {
        if v != 0 {
            o.num(k, v);
        }
    }
    o.end();
}

fn stats(out: &mut String, s: &Stats) {
    // Every field by name, so a new one cannot be forgotten.
    let Stats {
        node_visits,
        memo_hits,
        candidates,
        match_steps,
        no_match,
        guard_false,
        degraded,
        no_change,
        rewrites,
        hook_vetoes,
        rejected,
        cycles_cut,
        quarantined,
        new_nodes,
        fact_work,
        pass_work,
        rounds,
        passes,
        host,
        mba,
        completed,
        budget_terminated,
        declined,
        salvaged,
        not_started,
    } = s;
    let mut o = Obj::new(out);
    for (k, v) in [
        ("node_visits", *node_visits),
        ("memo_hits", *memo_hits),
        ("candidates", *candidates),
        ("match_steps", *match_steps),
        ("no_match", *no_match),
        ("guard_false", *guard_false),
        ("degraded", *degraded),
        ("no_change", *no_change),
        ("rewrites", *rewrites),
        ("hook_vetoes", *hook_vetoes),
        ("rejected", *rejected),
        ("cycles_cut", *cycles_cut),
        ("quarantined", *quarantined),
        ("new_nodes", *new_nodes),
        ("fact_work", *fact_work),
        ("pass_work", *pass_work),
        ("rounds", u64::from(*rounds)),
    ] {
        o.num(k, v);
    }
    o.key("passes");
    let mut p = Obj::new(o.out);
    for (name, c) in passes {
        p.key(name);
        pass_counts(p.out, c);
    }
    p.end();
    o.key("host");
    pass_counts(o.out, host);
    o.key("mba");
    mba_stats(o.out, mba);
    o.key("completed");
    pair(o.out, *completed);
    o.key("budget_terminated");
    pair(o.out, *budget_terminated);
    o.num("declined", *declined);
    o.num("salvaged", *salvaged);
    o.num("not_started", *not_started);
    o.end();
}

fn pair(out: &mut String, [a, b]: [u64; 2]) {
    out.push('[');
    num(out, a);
    out.push(',');
    num(out, b);
    out.push(']');
}

fn pass_counts(out: &mut String, c: &PassCounts) {
    let PassCounts {
        calls,
        noop,
        changed,
        rejected_cost,
        rejected,
        atomized,
        proofs,
        proved,
        refuted,
        unknown,
    } = *c;
    let mut o = Obj::new(out);
    for (k, v) in [
        ("calls", calls),
        ("noop", noop),
        ("changed", changed),
        ("rejected_cost", rejected_cost),
        ("rejected", rejected),
        ("atomized", atomized),
        ("proofs", proofs),
        ("proved", proved),
        ("refuted", refuted),
        ("unknown", unknown),
    ] {
        o.num(k, v);
    }
    o.end();
}

fn mba_stats(out: &mut String, m: &MbaStats) {
    let MbaStats {
        calls,
        steps,
        cache_hits,
        simplified,
        no_simpler,
        unsupported,
        exhausted,
        refuted,
        proof_unknown,
        not_smaller,
        too_many_vars,
        too_large,
        too_wide,
        too_small,
        certificates,
        opaque_asked,
        opaque_proved,
        opaque_known,
        opaque_exhausted,
        opaque_cases,
        piecewise_blocks,
        noise_blocks,
        noise_atoms,
    } = *m;
    let mut o = Obj::new(out);
    for (k, v) in [
        ("calls", calls),
        ("steps", steps),
        ("cache_hits", cache_hits),
        ("simplified", simplified),
        ("no_simpler", no_simpler),
        ("unsupported", unsupported),
        ("exhausted", exhausted),
        ("refuted", refuted),
        ("proof_unknown", proof_unknown),
        ("not_smaller", not_smaller),
        ("too_many_vars", too_many_vars),
        ("too_large", too_large),
        ("too_wide", too_wide),
        ("too_small", too_small),
        ("opaque_asked", opaque_asked),
        ("opaque_proved", opaque_proved),
        ("opaque_known", opaque_known),
        ("opaque_exhausted", opaque_exhausted),
        ("opaque_cases", opaque_cases),
        ("piecewise_blocks", piecewise_blocks),
        ("noise_blocks", noise_blocks),
        ("noise_atoms", noise_atoms),
    ] {
        o.num(k, v);
    }
    o.key("certificates");
    cert_stats(o.out, &certificates);
    o.end();
}

fn cert_stats(out: &mut String, c: &CertStats) {
    let CertStats {
        calls,
        proved,
        refuted,
        unknown,
        signature,
        single_bit,
        sparse,
        grid,
        exhaustive,
        symbolic,
        carries,
        compositional,
        split,
        known_bits,
        points,
        over_budget,
        internal,
    } = *c;
    let mut o = Obj::new(out);
    for (k, v) in [
        ("calls", calls),
        ("proved", proved),
        ("refuted", refuted),
        ("unknown", unknown),
        ("signature", signature),
        ("single_bit", single_bit),
        ("sparse", sparse),
        ("grid", grid),
        ("exhaustive", exhaustive),
        ("symbolic", symbolic),
        ("carries", carries),
        ("compositional", compositional),
        ("split", split),
        ("known_bits", known_bits),
        ("points", points),
        ("over_budget", over_budget),
        ("internal", internal),
    ] {
        o.num(k, v);
    }
    o.end();
}

fn reject_name(r: Reject) -> &'static str {
    match r {
        Reject::Width => "width",
        Reject::Verify => "verify",
        Reject::Tripwire => "tripwire",
        Reject::Termination => "termination",
    }
}

fn exhausted_name(e: Exhausted) -> &'static str {
    match e {
        Exhausted::NodeVisits => "node_visits",
        Exhausted::Candidates => "candidates",
        Exhausted::MatchSteps => "match_steps",
        Exhausted::Rewrites => "rewrites",
        Exhausted::NewNodes => "new_nodes",
        Exhausted::FactWork => "fact_work",
        Exhausted::PassWork => "pass_work",
        Exhausted::MbaCalls => "mba_calls",
        Exhausted::MbaSteps => "mba_steps",
        Exhausted::EqsatNodes => "eqsat_nodes",
        Exhausted::EqsatWork => "eqsat_work",
        Exhausted::Deadline => "deadline",
        Exhausted::ArenaCapacity => "arena_capacity",
    }
}

/// A JSON object being written: keys separated by commas.
struct Obj<'o> {
    out: &'o mut String,
    first: bool,
}

impl<'o> Obj<'o> {
    fn new(out: &'o mut String) -> Obj<'o> {
        out.push('{');
        Obj { out, first: true }
    }

    fn key(&mut self, k: &str) {
        if !self.first {
            self.out.push(',');
        }
        self.first = false;
        jstr(self.out, k);
        self.out.push(':');
    }

    fn num(&mut self, k: &str, v: u64) {
        self.key(k);
        num(self.out, v);
    }

    fn end(self) {
        self.out.push('}');
    }
}

/// `,"<k>":<v>`.
fn field(out: &mut String, k: &str, v: u64) {
    out.push_str(",\"");
    out.push_str(k);
    out.push_str("\":");
    num(out, v);
}

fn num(out: &mut String, v: u64) {
    let _ = write!(out, "{v}");
}

/// `s` as a JSON string.
fn jstr(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}
