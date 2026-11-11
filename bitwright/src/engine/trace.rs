//! A recorder of runs: [`Trace`] receives every event of a run and writes the run out as JSON
//! Lines, for a viewer, a diff, or a bug report.

use std::collections::HashMap;
use std::fmt::Write as _;

use super::{
    Budget, By, CertStats, Decline, Detail, End, Engine, Event, Exhausted, Explanation, MbaStats,
    Observer, Outcome, PassCounts, Phase, Reject, Stage, Stats,
};
use crate::error::Error;
use crate::expr::{Context, Expr, View};
use crate::facts::{Assumptions, Facts, Reliance};
use crate::hash::IdMap;
use crate::ops::CmpOpExt;
use crate::rules::{Ledger, Rule, RuleKind};

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
/// let text = trace.to_jsonl(&mut cx, &[e], &out)?;
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
///   `{"rule":0,"name":"core.arith::add_xor_and","id":"…","kind":"identity","proven":true,
///   "doc":…,"examples":[["…","…"]],"source":…,"ledger":…}` (`source`, the rule as written,
///   and `ledger`, the evidence its proof ledger records, when known: always for the built-in
///   rules, and for others from [`with_source`](Trace::with_source)), `{"rewrite":0,"name":…}`;
/// - each node the events, results and assumptions name, with every node below it, operands
///   first: `{"node":12,"op":"add","w":32,"args":[5,9],"text":"x + y"}`. `op` is `const` (with
///   `value`), `sym` (with `name`), a unary or binary operator's name, `cmp` (with `pred`, its
///   spelling: `<u`), `zext`, `sext`, `extract` (with `lo`), `concat`, `select`, `fp` (with
///   `fp_op` and `format`) or `ext` (with `output`). Node numbers are the context's own, so a
///   node keeps its number across the whole trace: equal numbers are equal expressions. Only
///   the nodes named directly carry `text`, the expression as the printer writes it, and, with
///   [`with_facts`](Trace::with_facts), `facts` (`{"zero":"0x…","one":"0x…","u":["0x…","0x…"],
///   "stride":1,"s":["0x…","0x…"]}`: the known zero and one bits, the unsigned interval and
///   its stride, the signed interval as bit patterns) and, under assumptions where they differ,
///   `assumed` (the same, with `relies`);
/// - each constraint of the run's assumptions ([`with_assumptions`](Trace::with_assumptions)):
///   `{"assume":0,"expr":40}`;
/// - the events, in order: `{"ev":"root","index":0,"root":20}` (with `"again":true` for a root
///   worked on again), `{"ev":"stage","stage":"cases","before":…,"after":…}`,
///   `{"ev":"phase_begin","round":0,"phase":1,"root":…}`, `{"ev":"candidate","rule":3,"node":…}`,
///   `{"ev":"no_match","rule":3,"node":…}` (also `degraded` and `no_change`),
///   `{"ev":"guard_false","rule":3,"node":…,"pred":"disjoint","args":[5,9]}` (`args` null where
///   an operand is no parameter), `{"ev":"applied","rule":3,"before":…,"after":…}` (or
///   `"pass":"linear"`, or `"rewrite":0`), `{"ev":"relied","on":[0,2]}` (with `"later":true`
///   when constraints from 63 on may be among them), `{"ev":"explain","pass":"invert",
///   "node":…,"why":{"kind":"invert",…}}`, `{"ev":"not_smaller","pass":"linear","node":…,
///   "candidate":…,"added":4,"freed":3,"shared":false}` (`candidate` null when it was not
///   built), `{"ev":"folded","node":…,"after":…}`, `{"ev":"vetoed",…}`,
///   `{"ev":"rejected",…,"reason":"verify"}`, `{"ev":"phase_end","round":0,"phase":1,
///   "root":…,"spent":{"node_visits":16,…}}` (the nonzero work only; with
///   `"stopped":"node_visits"` when a limit stopped it);
/// - each root's result: `{"result":0,"input":20,"expr":31,"changed":true,"end":"completed",
///   "relies_on":[]}` (`end` is also `budget_terminated`, with `stopped`, or `declined`, with
///   `cap`);
/// - the run's counters: `{"stats":{…}}`, every field of [`Stats`] by name.
///
/// The `why` of an `explain` event is the pass's [`Explanation`] as an object with its `kind`;
/// like the type, its fields may change in any release. A reader should skip events, fields
/// and kinds it does not know. The same run of the same engine on the same input writes the
/// same trace.
#[derive(Clone, Debug)]
pub struct Trace {
    strategy: String,
    max_rounds: u8,
    phases: Vec<(&'static str, Vec<String>)>,
    detail: Detail,
    facts: bool,
    /// Whether each linked rule is vouched for by its program's ledger, by name.
    proven: HashMap<String, bool>,
    /// Rule sources with their ledgers, for the rules' text and evidence.
    sources: Vec<(String, Option<Ledger>)>,
    rules: Vec<RuleInfo>,
    rule_index: HashMap<String, u32>,
    rewrites: Vec<String>,
    rewrite_index: HashMap<String, u32>,
    records: Vec<Rec>,
    explanations: Vec<Explanation>,
    assumptions: Vec<Expr>,
    /// The node of the last candidate, for the outcome of the attempt that follows it.
    last_candidate: Option<Expr>,
}

/// What the trace says about a rule.
#[derive(Clone, Debug)]
struct RuleInfo {
    name: String,
    id: String,
    identity: bool,
    doc: String,
    examples: Vec<(String, String)>,
    span: (usize, usize),
}

/// What made a rewrite, by its number in the trace.
#[derive(Copy, Clone, Debug)]
enum Who {
    Rule(u32),
    Pass(&'static str),
    Rewrite(u32),
}

/// An event, owned. Explanations are kept apart, by index.
#[derive(Copy, Clone, Debug)]
enum Rec {
    Candidate(u32, Expr),
    /// `no_match`, `degraded` or `no_change`, by name, with the candidate's node.
    Attempt(&'static str, u32, Option<Expr>),
    GuardFalse(u32, Option<Expr>, Option<(&'static str, [Option<Expr>; 2])>),
    Applied(Who, Expr, Expr),
    Vetoed(Who),
    Rejected(Who, Reject),
    Relied(Reliance),
    Explain(Who, Expr, usize),
    NotSmaller(Who, Expr, Option<Expr>, u32, u32, bool),
    Folded(Expr, Expr),
    Root(usize, Expr, bool),
    Stage(Stage, Expr, Expr),
    PhaseBegin(u8, usize, Expr),
    PhaseEnd(u8, usize, Expr, Budget, Option<Exhausted>),
}

impl Trace {
    /// The trace format this version writes.
    pub const FORMAT: u32 = 1;

    /// An empty trace of runs of `engine` (its strategy goes in the header), which knows the
    /// built-in rules' text and proof ledger.
    pub fn new(engine: &Engine) -> Trace {
        let s = engine.strategy();
        let inner = &engine.inner;
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
            detail: Detail::Events,
            facts: false,
            proven: inner
                .rules
                .iter()
                .zip(inner.proven.iter())
                .map(|(r, &p)| (r.name.clone(), p))
                .collect(),
            sources: vec![(
                crate::rules::corpus::CORE.to_string(),
                Ledger::parse(crate::rules::corpus::CORE_LEDGER).ok(),
            )],
            rules: Vec::new(),
            rule_index: HashMap::new(),
            rewrites: Vec::new(),
            rewrite_index: HashMap::new(),
            records: Vec::new(),
            explanations: Vec::new(),
            assumptions: Vec::new(),
            last_candidate: None,
        }
    }

    /// Asks the engine for the passes' reasoning too ([`Detail::Explain`]), recorded as
    /// `explain` events.
    pub fn with_explanations(mut self, yes: bool) -> Trace {
        self.detail = if yes { Detail::Explain } else { Detail::Events };
        self
    }

    /// Writes the facts of every node named directly: known bits and intervals, and under the
    /// assumptions given to [`with_assumptions`](Trace::with_assumptions) where they differ.
    pub fn with_facts(mut self, yes: bool) -> Trace {
        self.facts = yes;
        self
    }

    /// The source of a rule program the engine links, with the ledger that vouches for it:
    /// the trace gives the text and evidence of its rules (those of the groups it declares).
    pub fn with_source(mut self, source: &str, ledger: Option<&Ledger>) -> Trace {
        self.sources.push((source.to_string(), ledger.cloned()));
        self
    }

    /// Records the run's assumptions, written as `assume` lines (and used for the facts under
    /// them). Call it with the assumptions the run is given.
    pub fn with_assumptions(&mut self, cx: &mut Context, a: &Assumptions) -> Result<(), Error> {
        self.assumptions = a.predicates(cx)?;
        Ok(())
    }

    /// The number of events recorded.
    pub fn len(&self) -> usize {
        self.records.len()
    }

    /// Whether no event was recorded.
    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }

    fn rule(&mut self, rule: &Rule) -> u32 {
        if let Some(&k) = self.rule_index.get(rule.name.as_str()) {
            return k;
        }
        let k = self.rules.len() as u32;
        self.rules.push(RuleInfo {
            name: rule.name.clone(),
            id: rule.id.to_string(),
            identity: rule.kind == RuleKind::Identity,
            doc: rule.doc.clone(),
            examples: rule.examples.clone(),
            span: rule.span,
        });
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

    /// The rule's text and ledger evidence, from the source declaring its group.
    fn source_of(&self, r: &RuleInfo) -> (Option<&str>, Option<String>) {
        let group = r.name.split("::").next().unwrap_or("");
        let decl = format!("group {group} {{");
        for (src, ledger) in &self.sources {
            if !src.contains(&decl) {
                continue;
            }
            let text = src.get(r.span.0..r.span.1);
            let ev = ledger.as_ref().and_then(|l| {
                l.entries
                    .get(&r.name)
                    .filter(|(id, _, _)| *id == r.id)
                    .map(|(_, kind, ev)| format!("{kind} {ev}"))
            });
            return (text, ev);
        }
        (None, None)
    }

    /// The run as a trace: the header, the rules and nodes the events name, the assumptions,
    /// the events, the result of each root (`roots[i]` is answered by `outcome.roots[i]`) and
    /// the counters. See [`Trace`] for the format. Fails when an expression is not of `cx`.
    pub fn to_jsonl(
        &self,
        cx: &mut Context,
        roots: &[Expr],
        outcome: &Outcome,
    ) -> Result<String, Error> {
        // The nodes the trace names directly, in order of first mention.
        let mut named: Vec<Expr> = Vec::new();
        {
            let mut seen: IdMap<u32, ()> = IdMap::default();
            let cxr: &Context = cx;
            let mut name = |e: Expr| -> Result<(), Error> {
                if seen.insert(cxr.id(e)?, ()).is_none() {
                    named.push(e);
                }
                Ok(())
            };
            for (&input, r) in roots.iter().zip(&outcome.roots) {
                name(input)?;
                name(r.expr)?;
            }
            for &a in &self.assumptions {
                name(a)?;
            }
            for rec in &self.records {
                match *rec {
                    Rec::Candidate(_, e)
                    | Rec::Root(_, e, _)
                    | Rec::PhaseBegin(_, _, e)
                    | Rec::Explain(_, e, _) => name(e)?,
                    Rec::PhaseEnd(_, _, e, ..) => name(e)?,
                    Rec::Applied(_, a, b) | Rec::Stage(_, a, b) | Rec::Folded(a, b) => {
                        name(a)?;
                        name(b)?;
                    }
                    Rec::NotSmaller(_, a, b, ..) => {
                        name(a)?;
                        if let Some(b) = b {
                            name(b)?;
                        }
                    }
                    Rec::Attempt(_, _, e) => {
                        if let Some(e) = e {
                            name(e)?;
                        }
                    }
                    Rec::GuardFalse(_, e, d) => {
                        for e in e
                            .into_iter()
                            .chain(d.into_iter().flat_map(|(_, a)| a).flatten())
                        {
                            name(e)?;
                        }
                    }
                    Rec::Vetoed(_) | Rec::Rejected(..) | Rec::Relied(_) => {}
                }
            }
            for why in &self.explanations {
                let mut res = Ok(());
                super::explain::exprs(why, &mut |e| {
                    if res.is_ok() {
                        res = name(e);
                    }
                });
                res?;
            }
        }
        // Their facts, before anything is written (they need the context mutably).
        let mut facts: IdMap<u32, (Facts, Option<(Facts, Reliance)>)> = IdMap::default();
        if self.facts {
            let under = if self.assumptions.is_empty() {
                None
            } else {
                let mut a = Assumptions::new();
                for &p in &self.assumptions {
                    a.assume_true(cx, p)?;
                }
                Some(a)
            };
            for &e in &named {
                let Some(base) = cx.try_facts(e)? else {
                    continue;
                };
                let assumed = match &under {
                    Some(a) => cx.facts_under(e, a)?.filter(|(f, _)| *f != base),
                    None => None,
                };
                facts.insert(cx.id(e)?, (base, assumed));
            }
        }
        let cx: &Context = cx;
        let direct: IdMap<u32, ()> = named
            .iter()
            .filter_map(|&e| cx.id(e).ok().map(|i| (i, ())))
            .collect();

        let mut out = String::new();
        self.header(&mut out);
        for (k, r) in self.rules.iter().enumerate() {
            let mut o = Obj::new(&mut out);
            o.num("rule", k as u64);
            o.str("name", &r.name);
            o.str("id", &r.id);
            o.str("kind", if r.identity { "identity" } else { "rule" });
            if let Some(&p) = self.proven.get(&r.name) {
                o.bool("proven", p);
            }
            if !r.doc.is_empty() {
                o.str("doc", &r.doc);
            }
            if !r.examples.is_empty() {
                o.key("examples");
                o.out.push('[');
                for (j, (a, b)) in r.examples.iter().enumerate() {
                    if j > 0 {
                        o.out.push(',');
                    }
                    o.out.push('[');
                    jstr(o.out, a);
                    o.out.push(',');
                    jstr(o.out, b);
                    o.out.push(']');
                }
                o.out.push(']');
            }
            let (text, ev) = self.source_of(r);
            if let Some(t) = text {
                o.str("source", t);
            }
            if let Some(ev) = ev {
                o.str("ledger", &ev);
            }
            o.end();
            out.push('\n');
        }
        for (k, n) in self.rewrites.iter().enumerate() {
            let mut o = Obj::new(&mut out);
            o.num("rewrite", k as u64);
            o.str("name", n);
            o.end();
            out.push('\n');
        }

        // Every node below the named ones, operands first, each once.
        let mut written: IdMap<u32, ()> = IdMap::default();
        let mut stack: Vec<(u32, bool)> = Vec::new();
        for &top in &named {
            stack.push((cx.id(top)?, false));
            while let Some((i, expanded)) = stack.pop() {
                if expanded {
                    node_line(&mut out, cx, i, direct.contains_key(&i));
                    if let Some((base, assumed)) = facts.get(&i) {
                        out.push_str(",\"facts\":");
                        facts_obj(&mut out, base, None);
                        if let Some((f, rel)) = assumed {
                            out.push_str(",\"assumed\":");
                            facts_obj(&mut out, f, Some(*rel));
                        }
                    }
                    out.push_str("}\n");
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

        let id = |e: Expr| u64::from(cx.id(e).unwrap_or(0));
        let opt = |out: &mut String, k: &str, e: Option<Expr>| {
            out.push_str(",\"");
            out.push_str(k);
            out.push_str("\":");
            match e {
                Some(e) => num(out, id(e)),
                None => out.push_str("null"),
            }
        };
        for (k, &a) in self.assumptions.iter().enumerate() {
            out.push_str("{\"assume\":");
            num(&mut out, k as u64);
            field(&mut out, "expr", id(a));
            out.push_str("}\n");
        }
        for rec in &self.records {
            out.push_str("{\"ev\":");
            match *rec {
                Rec::Candidate(r, e) => {
                    out.push_str("\"candidate\",\"rule\":");
                    num(&mut out, u64::from(r));
                    field(&mut out, "node", id(e));
                }
                Rec::Attempt(what, r, e) => {
                    jstr(&mut out, what);
                    field(&mut out, "rule", u64::from(r));
                    opt(&mut out, "node", e);
                }
                Rec::GuardFalse(r, e, detail) => {
                    out.push_str("\"guard_false\"");
                    field(&mut out, "rule", u64::from(r));
                    opt(&mut out, "node", e);
                    if let Some((pred, [a, b])) = detail {
                        out.push_str(",\"pred\":");
                        jstr(&mut out, pred);
                        out.push_str(",\"args\":[");
                        for (j, x) in [a, b].into_iter().enumerate() {
                            if j > 0 {
                                out.push(',');
                            }
                            match x {
                                Some(x) => num(&mut out, id(x)),
                                None => out.push_str("null"),
                            }
                        }
                        out.push(']');
                    }
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
                Rec::Explain(w, e, k) => {
                    out.push_str("\"explain\"");
                    who(&mut out, w);
                    field(&mut out, "node", id(e));
                    out.push_str(",\"why\":");
                    super::explain::write(&mut out, &self.explanations[k], &id);
                }
                Rec::NotSmaller(w, e, c, added, freed, shared) => {
                    out.push_str("\"not_smaller\"");
                    who(&mut out, w);
                    field(&mut out, "node", id(e));
                    opt(&mut out, "candidate", c);
                    field(&mut out, "added", u64::from(added));
                    field(&mut out, "freed", u64::from(freed));
                    out.push_str(if shared {
                        ",\"shared\":true"
                    } else {
                        ",\"shared\":false"
                    });
                }
                Rec::Folded(a, b) => {
                    out.push_str("\"folded\"");
                    field(&mut out, "node", id(a));
                    field(&mut out, "after", id(b));
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
            Event::Candidate { rule, node } => {
                self.last_candidate = Some(node);
                Rec::Candidate(self.rule(rule), node)
            }
            Event::NoMatch { rule } => {
                Rec::Attempt("no_match", self.rule(rule), self.last_candidate)
            }
            Event::Degraded { rule } => {
                Rec::Attempt("degraded", self.rule(rule), self.last_candidate)
            }
            Event::NoChange { rule } => {
                Rec::Attempt("no_change", self.rule(rule), self.last_candidate)
            }
            Event::GuardFalse { rule } => {
                Rec::GuardFalse(self.rule(rule), self.last_candidate, None)
            }
            Event::GuardFailed { rule, pred, args } => {
                let k = self.rule(rule);
                if let Some(Rec::GuardFalse(r, _, d)) = self.records.last_mut()
                    && *r == k
                {
                    *d = Some((pred, args));
                }
                return;
            }
            Event::Applied { by, before, after } => Rec::Applied(self.who(by), before, after),
            Event::Vetoed { by } => Rec::Vetoed(self.who(by)),
            Event::Rejected { by, reason } => Rec::Rejected(self.who(by), reason),
            Event::Relied { on } => Rec::Relied(on),
            Event::Explain { by, node, why } => {
                self.explanations.push(why.clone());
                Rec::Explain(self.who(by), node, self.explanations.len() - 1)
            }
            Event::NotSmaller {
                by,
                node,
                candidate,
                added,
                freed,
                shared,
            } => Rec::NotSmaller(self.who(by), node, candidate, added, freed, shared),
            Event::Folded { node, after } => Rec::Folded(node, after),
            Event::Root { index, root, again } => Rec::Root(index, root, again),
            // (A stage's parts are for a derivation; the trace has the stage.)
            Event::Part { .. } => return,
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

    fn detail(&self) -> Detail {
        self.detail
    }
}

/// Facts as an object (see the format), with what they rely on.
fn facts_obj(out: &mut String, f: &Facts, rel: Option<Reliance>) {
    let hex = |v: crate::BitVec| format!("{v:#x}");
    let mut o = Obj::new(out);
    o.str("zero", &hex(f.known().known_zero()));
    o.str("one", &hex(f.known().known_one()));
    o.key("u");
    o.out.push('[');
    jstr(o.out, &hex(f.urange().lo()));
    o.out.push(',');
    jstr(o.out, &hex(f.urange().hi()));
    o.out.push(']');
    o.num("stride", f.urange().stride());
    o.key("s");
    o.out.push('[');
    jstr(o.out, &hex(f.srange().lo()));
    o.out.push(',');
    jstr(o.out, &hex(f.srange().hi()));
    o.out.push(']');
    if let Some(r) = rel {
        o.key("relies");
        reliance(o.out, r, "relies_later");
    }
    o.end();
}

/// One node's line, left open for its facts.
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
        rounds_capped,
        reruns_capped,
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
    o.num("rounds_capped", *rounds_capped);
    o.num("reruns_capped", *reruns_capped);
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
        // (Not part of a trace: a run records what it did, and a store's advice is not it.)
        opaque_skipped: _,
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
pub(super) struct Obj<'o> {
    pub(super) out: &'o mut String,
    first: bool,
}

impl<'o> Obj<'o> {
    pub(super) fn new(out: &'o mut String) -> Obj<'o> {
        out.push('{');
        Obj { out, first: true }
    }

    pub(super) fn key(&mut self, k: &str) {
        if !self.first {
            self.out.push(',');
        }
        self.first = false;
        jstr(self.out, k);
        self.out.push(':');
    }

    pub(super) fn num(&mut self, k: &str, v: u64) {
        self.key(k);
        num(self.out, v);
    }

    pub(super) fn str(&mut self, k: &str, v: &str) {
        self.key(k);
        jstr(self.out, v);
    }

    pub(super) fn bool(&mut self, k: &str, v: bool) {
        self.key(k);
        self.out.push_str(if v { "true" } else { "false" });
    }

    pub(super) fn end(self) {
        self.out.push('}');
    }
}

/// `,"<k>":<v>`.
pub(super) fn field(out: &mut String, k: &str, v: u64) {
    out.push_str(",\"");
    out.push_str(k);
    out.push_str("\":");
    num(out, v);
}

pub(super) fn num(out: &mut String, v: u64) {
    let _ = write!(out, "{v}");
}

/// `s` as a JSON string.
pub(super) fn jstr(out: &mut String, s: &str) {
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
