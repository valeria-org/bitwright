//! Many questions at once (feature `prove`): simplifications, constants and validity proofs,
//! answered in the order asked, on as many threads as the caller gives, with the work that
//! questions share done once. See `docs/proposals/parallel-proofs.md`.
//!
//! A [`Session`] owns what outlives a call: its engines, its solver and a store of answers.
//! [`Session::run`] takes questions about expressions of one context ([`Ask`]) and returns a
//! [`Reply`] for each. A question is copied into a context of its own and decided there, so
//! what it costs and what it answers depend on the question and the session's [`Config`]
//! alone: not on the other questions, their order, the number of threads, what the store
//! already holds, or what was cancelled.
//!
//! With [`Split`], a question is cut where its noise cancels. Every node is evaluated at a
//! few assignments of the symbols; a node with one value at all of them, over something that
//! varies, is a *hub*, and is asked on its own: "is this the constant it looks like?". Hubs
//! proved are replaced by their constants, in the hubs above them first and in the question
//! last. Sampling only chooses where to cut: a constant is substituted when the engine folded
//! the hub to it or the search proved the equality, never because the samples agreed. A hub
//! is one task however many questions contain it, and its answer is kept in the store.
//!
//! ```
//! use bitwright::batch::{Answer, Ask, Config, Session};
//! use bitwright::{BitVec, Context, ParseOptions, Width};
//!
//! let mut cx = Context::new();
//! let o = ParseOptions::width(Width::W64);
//! // An address with a block of noise that cancels, and an identity.
//! let address = cx.parse("0x1000 + ((x ^ y) + 2 * (x & y) - x - y) * z", &o)?;
//! let identity = cx.parse("(x | y) + (x & y) == x + y", &o)?;
//! let session = Session::new(Config::default().with_threads(2));
//! let replies = session.run(&mut cx, &[Ask::constant(address), Ask::valid(identity)])?;
//! assert_eq!(replies[0].answer, Answer::Constant(BitVec::from_u64(Width::W64, 0x1000).unwrap()));
//! assert_eq!(replies[1].answer, Answer::Proved);
//! // Asked again, both are answered from the store, at the cost they had.
//! let again = session.run(&mut cx, &[Ask::valid(identity)])?;
//! assert_eq!(again[0].cost, replies[1].cost);
//! # Ok::<(), bitwright::Error>(())
//! ```

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex, MutexGuard};

use crate::engine::{Allowance, Budget, Clock, Deadline, End, Exhausted, Run};
use crate::error::Error;
use crate::expr::{Context, ContextConfig, Expr, OpCode};
use crate::facts::{Assumptions, Facts};
use crate::hash::IdMap;
use crate::prove::{self, Env, Limits, Model, Outcome, Question, Simplifiers, Unknown};
use crate::{BinOp, BitVec, CmpOp, SymbolKey, UnOp, Width};

/// Where questions are cut ([`Config::split`]).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct Split {
    /// Ask each hub (a node with one value at every sample, over something that varies) as a
    /// question of its own, and replace those proved constant.
    pub hubs: bool,
    /// When a hub is not proved as written, ask the hubs below it and then the hub with
    /// those proved replaced, and so on down. Without it only the topmost hubs of a
    /// question are asked, each as written.
    pub nested: bool,
    /// Regroup a chain of `+` or of `^` by the symbols its terms read, where that brings
    /// terms together whose sum is constant at the samples: the group is then a hub.
    pub terms: bool,
    /// How many times a validity question that stays undecided is split in two on a
    /// condition its selects test (`c → p[c:=1]` and `¬c → p[c:=0]`): each half is a
    /// question of its own, so 2 means up to four cases. 0: never.
    pub cases: u8,
    /// Ask a question whole first, and cut it only when that does not decide it (a
    /// simplification is its own answer, so an [`Ask::simplify`] is then never cut). A
    /// question the engine settles by itself costs what it costs today, and its hubs are
    /// neither asked nor stored: right for questions that share little, or that the
    /// engine folds whole. [`Split::eager`] asks the hubs first. On by default.
    pub whole_first: bool,
    /// Assignments of the symbols every node is evaluated at to find hubs (at least 2; the
    /// first two are all zeros and all ones).
    pub points: u32,
    /// A hub of fewer nodes than this (as a tree) is left to the question it is in.
    pub min_nodes: u32,
}

impl Default for Split {
    /// Proofs asked whole first; then hubs, nested, with terms regrouped and one case
    /// split, from 64 points.
    fn default() -> Self {
        Split {
            hubs: true,
            nested: true,
            terms: true,
            cases: 1,
            whole_first: true,
            points: 64,
            min_nodes: 4,
        }
    }
}

impl Split {
    /// The default, with every question's hubs asked before the question
    /// ([`whole_first`](Self::whole_first) off): for questions over shared structure that
    /// are not decided whole, where a hub proved once serves every question that contains
    /// it and no question pays for a first attempt that fails. Where the engine folds a
    /// question whole it costs more than asking whole: a hub the engine cannot fold on its
    /// own is asked, fails, and is asked again below.
    pub fn eager() -> Split {
        Split::default().with_whole_first(false)
    }

    /// No cut: every question is asked whole, as [`prove::valid_under`] or
    /// [`Engine::run`](crate::engine::Engine::run) would be in a context of its own.
    pub fn none() -> Split {
        Split {
            hubs: false,
            nested: false,
            terms: false,
            cases: 0,
            whole_first: false,
            points: 64,
            min_nodes: 4,
        }
    }
}

setters!(Split {
    with_hubs: hubs: bool,
    with_nested: nested: bool,
    with_terms: terms: bool,
    with_cases: cases: u8,
    with_whole_first: whole_first: bool,
    with_points: points: u32,
    with_min_nodes: min_nodes: u32,
});

/// A session's configuration, fixed when it is made: every answer and cost is a function of
/// the question and of this.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Config {
    /// Threads a call may use, the calling thread among them (0: as many as the machine
    /// runs at once). The others live for the call only; a session keeps no pool. It
    /// changes how long a call takes and nothing else.
    pub threads: usize,
    /// How every task is decided: the search's limits, the simplifier's budget
    /// ([`prove::Config::simplify_budget`], also the budget of a [`Ask::simplify`]), and
    /// the rest. Certificates are not kept: a split question's proof is of its parts.
    pub prove: prove::Config,
    /// The MBA phase of the session's engines, when not the prover's own (the default with
    /// the opaque-constant sweep).
    #[cfg(feature = "mba")]
    pub mba: Option<crate::mba::MbaConfig>,
    /// How a hub is proved constant, when not as [`prove`](Self::prove) says: a hub is
    /// one of many, and a search that a question deserves is long for each of them.
    pub hub: Option<prove::Config>,
    /// Where questions are cut.
    pub split: Split,
    /// The most nodes the store's context may hold when a call begins; past it the store
    /// is emptied first (its context and every answer). It bounds memory between calls, and
    /// changes how long a call takes and nothing else.
    pub store_nodes: usize,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            threads: 0,
            prove: prove::Config::default(),
            #[cfg(feature = "mba")]
            mba: None,
            hub: None,
            split: Split::default(),
            store_nodes: 1 << 20,
        }
    }
}

setters!(Config {
    with_threads: threads: usize,
    with_prove: prove: prove::Config,
    with_hub: hub ? prove::Config,
    with_split: split: Split,
    with_store_nodes: store_nodes: usize,
});

#[cfg(feature = "mba")]
impl Config {
    /// Sets [`mba`](Self::mba).
    #[must_use]
    pub fn with_mba(mut self, mba: crate::mba::MbaConfig) -> Self {
        self.mba = Some(mba);
        self
    }
}

/// Stops the questions it was given to ([`Ask::cancellable`]) once [`cancel`](Self::cancel)
/// is called, from any thread. Clones are one flag.
#[derive(Clone, Debug, Default)]
pub struct Cancel(Arc<AtomicBool>);

impl Cancel {
    /// A flag not yet set.
    pub fn new() -> Cancel {
        Cancel::default()
    }

    /// Sets it: for good.
    pub fn cancel(&self) {
        self.0.store(true, Ordering::Release);
    }

    /// Whether it is set.
    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::Acquire)
    }
}

#[derive(Copy, Clone, Debug)]
enum Kind {
    Simplify(Expr),
    Constant(Expr),
    Valid(Expr),
    Equal(Expr, Expr),
}

/// A question about expressions of the context given to [`Session::run`].
#[derive(Clone, Debug)]
pub struct Ask<'a> {
    kind: Kind,
    assumptions: Option<&'a Assumptions>,
    cancel: Option<Cancel>,
}

impl<'a> Ask<'a> {
    fn of(kind: Kind) -> Self {
        Ask {
            kind,
            assumptions: None,
            cancel: None,
        }
    }

    /// `e` simplified ([`Answer::Simplified`]).
    pub fn simplify(e: Expr) -> Self {
        Ask::of(Kind::Simplify(e))
    }

    /// Whether `e` has one value for every value of its symbols, and which
    /// ([`Answer::Constant`], [`Answer::Varies`]).
    pub fn constant(e: Expr) -> Self {
        Ask::of(Kind::Constant(e))
    }

    /// Whether the 1-bit `p` is true for every value of its symbols ([`Answer::Proved`],
    /// [`Answer::Refuted`]).
    pub fn valid(p: Expr) -> Self {
        Ask::of(Kind::Valid(p))
    }

    /// Whether `a` and `b`, of one width, are equal for every value of their symbols.
    pub fn equal(a: Expr, b: Expr) -> Self {
        Ask::of(Kind::Equal(a, b))
    }

    /// The question wherever these constraints hold, and not everywhere.
    #[must_use]
    pub fn under(mut self, assumptions: &'a Assumptions) -> Self {
        self.assumptions = Some(assumptions);
        self
    }

    /// Stopped by `cancel`. A task several questions share stops when all of them are
    /// cancelled.
    #[must_use]
    pub fn cancellable(mut self, cancel: &Cancel) -> Self {
        self.cancel = Some(cancel.clone());
        self
    }
}

/// What a question was answered.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Answer {
    /// Of [`Ask::simplify`]: an expression of the caller's context equal to the one asked
    /// about (wherever the assumptions hold), and how the engine ended.
    Simplified {
        /// The result.
        expr: Expr,
        /// Whether it is final.
        end: End,
    },
    /// Of [`Ask::constant`]: this value, at every value of the symbols (that the
    /// assumptions allow). Proved, not sampled.
    Constant(BitVec),
    /// Of [`Ask::constant`]: not a constant. At these two assignments, at which the
    /// assumptions hold, the expression has two values (checked by evaluation).
    Varies(Box<(Model, Model)>),
    /// Of [`Ask::valid`] and [`Ask::equal`]: it holds.
    Proved,
    /// Of [`Ask::valid`] and [`Ask::equal`]: it fails at these values of the symbols
    /// (checked by evaluation of the question as asked).
    Refuted(Model),
    /// Not decided: why.
    Unknown(Unknown),
    /// Stopped by its [`Cancel`] before it was decided.
    Cancelled,
}

/// The work a question took, in counts and never in time: the same for a question whenever
/// and however it is asked of a session with the same [`Config`]. With [`Split`] it is the
/// work of the question's own tasks and of every hub below it, each counted once.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Cost {
    /// What the engine spent, in the units of its budget.
    pub simplify: Budget,
    /// The search's conflicts.
    pub conflicts: u64,
    /// The search's propagations.
    pub propagations: u64,
    /// The search's decisions.
    pub decisions: u64,
    /// AIG nodes of the circuits built.
    pub circuit_nodes: u64,
    /// Assignments the prover evaluated before searching.
    pub samples: u64,
    /// Tasks solved for it: engine runs and proofs.
    pub tasks: u64,
}

impl Default for Cost {
    /// No work.
    fn default() -> Self {
        Cost {
            simplify: Budget::ZERO,
            conflicts: 0,
            propagations: 0,
            decisions: 0,
            circuit_nodes: 0,
            samples: 0,
            tasks: 0,
        }
    }
}

impl Cost {
    fn add(&mut self, o: &Cost) {
        let (a, b) = (&mut self.simplify, &o.simplify);
        a.node_visits = a.node_visits.saturating_add(b.node_visits);
        a.candidates = a.candidates.saturating_add(b.candidates);
        a.match_steps = a.match_steps.saturating_add(b.match_steps);
        a.rewrites = a.rewrites.saturating_add(b.rewrites);
        a.new_nodes = a.new_nodes.saturating_add(b.new_nodes);
        a.fact_work = a.fact_work.saturating_add(b.fact_work);
        a.pass_work = a.pass_work.saturating_add(b.pass_work);
        a.mba_calls = a.mba_calls.saturating_add(b.mba_calls);
        a.mba_steps = a.mba_steps.saturating_add(b.mba_steps);
        a.eqsat_nodes = a.eqsat_nodes.saturating_add(b.eqsat_nodes);
        a.eqsat_work = a.eqsat_work.saturating_add(b.eqsat_work);
        self.conflicts = self.conflicts.saturating_add(o.conflicts);
        self.propagations = self.propagations.saturating_add(o.propagations);
        self.decisions = self.decisions.saturating_add(o.decisions);
        self.circuit_nodes = self.circuit_nodes.saturating_add(o.circuit_nodes);
        self.samples = self.samples.saturating_add(o.samples);
        self.tasks = self.tasks.saturating_add(o.tasks);
    }
}

/// Where a reply came from. It says how the time was spent, not what the answer is.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Source {
    /// Decided in this call.
    Solved,
    /// The store had the question's answer.
    Stored,
}

/// The reply to an [`Ask`].
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Reply {
    /// The answer.
    pub answer: Answer,
    /// What it took. Of an [`Answer::Cancelled`]: what was spent until it stopped, which
    /// depends on when that was.
    pub cost: Cost,
    /// Where it came from.
    pub source: Source,
}

/// What a session has done, for its caller's accounting (hit rates, memory). Counts of
/// events, which depend on the order of calls: no answer does.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Stats {
    /// Questions asked.
    pub asks: u64,
    /// ...answered whole from the store...
    pub asks_stored: u64,
    /// ...or the same as an earlier question of their call.
    pub asks_repeated: u64,
    /// Nodes of the questions asked, each question's counted alone...
    pub nodes_asked: u64,
    /// ...and those the store's context did not hold yet.
    pub nodes_new: u64,
    /// Engine runs and proofs done.
    pub tasks_solved: u64,
    /// Tasks (hubs, remainders, cases) found in the store while a question was planned.
    pub tasks_stored: u64,
    /// Hubs asked...
    pub hubs: u64,
    /// ...and proved constant.
    pub hubs_proved: u64,
    /// Chains of `+` or `^` regrouped.
    pub regrouped: u64,
    /// Questions split in two on a condition.
    pub case_splits: u64,
    /// Tasks stopped by a [`Cancel`].
    pub cancelled: u64,
    /// Nodes of the store's context now.
    pub store_nodes: u64,
    /// Answers the store holds now.
    pub store_answers: u64,
    /// Times the store was emptied.
    pub flushes: u64,
}

/// What a task is, with its root and assumptions: its identity in the store.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum What {
    /// The engine on the root.
    LeafSimplify,
    /// A proof of the root.
    LeafValid,
    /// A proof of the root, `x == k`, by the engine on `x` first: within a hub's limits
    /// ([`Config::hub`])...
    LeafHub,
    /// ...or a question's.
    LeafConstant,
    /// The root is a hub: is it its constant?
    Hub,
    /// The questions as asked: planned, split.
    AskSimplify,
    AskConstant,
    /// With the case splits already made above it.
    AskValid(u8),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Key {
    what: What,
    /// A node of the store's context.
    root: u32,
    /// The constraints, in the order given: their expressions in the store's context.
    assume: Arc<[(u32, Facts)]>,
    /// Of a proof that the root is a constant: which.
    k: Option<BitVec>,
}

/// A task's answer, as the store keeps it (expressions are nodes of its context).
#[derive(Clone, Debug)]
enum Res {
    Simplified { expr: u32, end: End },
    Constant(BitVec),
    Varies(Box<(Model, Model)>),
    Proved,
    Refuted(Model),
    Unknown(Unknown),
}

#[derive(Debug)]
struct Entry {
    /// Unique in its session: what a cost is counted once by.
    id: u64,
    res: Res,
    /// The task's own work.
    own: Cost,
    /// Of a question: its own work and that of everything below it, each once.
    total: Cost,
    /// The tasks it was made of.
    parts: Vec<Arc<Entry>>,
    /// Of a hub: the proved constants to write for it. Itself, when proved; otherwise
    /// those of the hubs below it.
    subst: Arc<[(u32, BitVec)]>,
}

/// The asks a task works for.
#[derive(Clone, Debug, Default)]
struct Wanted {
    /// By an ask that cannot be cancelled.
    always: bool,
    flags: Vec<Cancel>,
}

impl Wanted {
    fn stopped(&self) -> bool {
        !self.always && self.flags.iter().all(Cancel::is_cancelled)
    }

    /// Whether `o` added something.
    fn join(&mut self, o: &Wanted) -> bool {
        if self.always {
            return false;
        }
        if o.always {
            self.always = true;
            self.flags.clear();
            return true;
        }
        let mut grew = false;
        for f in &o.flags {
            if !self.flags.iter().any(|g| Arc::ptr_eq(&g.0, &f.0)) {
                self.flags.push(f.clone());
                grew = true;
            }
        }
        grew
    }
}

impl Clock for Wanted {
    fn now_ticks(&self) -> u64 {
        u64::from(self.stopped())
    }
}

#[derive(Debug)]
enum State {
    /// Waiting for `waiting` tasks.
    Pending,
    /// In the queue.
    Ready,
    Running,
    Done(Arc<Entry>),
    Cancelled,
}

#[derive(Debug)]
enum Plan {
    Leaf,
    Hub {
        /// Its value at the samples.
        k: BitVec,
        /// The hubs nearest below it, once it was not proved as written.
        below: Vec<usize>,
        /// Its proofs: as written, and with the hubs below it replaced.
        proofs: [Option<usize>; 2],
    },
    Ask {
        /// Of a constant question: the value at the samples and the point it was read at.
        /// `None` with `fallback`: no sample satisfied the assumptions.
        candidate: Option<(BitVec, u32)>,
        fallback: bool,
        /// The root with its chains regrouped.
        root: u32,
        /// The topmost hubs below it.
        hubs: Vec<usize>,
        /// The question asked whole ([`Split::whole_first`]).
        first: Option<usize>,
        /// What the remainder asked ([`advance`](Session::advance) fills them in).
        pred: u32,
        rest: Option<usize>,
        cases: Option<(usize, usize)>,
    },
}

#[derive(Debug)]
struct Job {
    key: Key,
    plan: Plan,
    /// The tasks it needs; the first `base` are those it was planned with.
    deps: Vec<usize>,
    base: usize,
    waiting: usize,
    dependents: Vec<usize>,
    state: State,
    stage: u8,
    wanted: Wanted,
    /// What it had spent when it was cancelled.
    partial: Cost,
}

/// The tasks of one call.
#[derive(Debug, Default)]
struct Graph {
    jobs: Vec<Job>,
    by_key: HashMap<Key, usize>,
    ready: VecDeque<usize>,
    running: usize,
    /// Asks not answered yet (distinct tasks).
    open: usize,
    tops: HashSet<usize>,
    error: Option<Error>,
}

struct Store {
    cx: Context,
    done: HashMap<Key, Arc<Entry>>,
    config: Option<ContextConfig>,
    registry: Option<Arc<crate::ext::Registry>>,
    /// What the samples say of the context's nodes.
    sampled: Sampled,
    next_id: u64,
    stats: Stats,
    graph: Graph,
}

impl Store {
    fn empty(&mut self, src: &Context) {
        let mut cx = Context::with_config(src.config().clone());
        cx.registry = src.registry.clone();
        self.cx = cx;
        self.sampled = Sampled::default();
        self.done.clear();
        self.config = Some(src.config().clone());
        self.registry = src.registry.clone();
    }

    fn entry(&mut self, res: Res, own: Cost, parts: Vec<Arc<Entry>>) -> Entry {
        self.next_id += 1;
        Entry {
            id: self.next_id,
            res,
            own,
            total: own,
            parts,
            subst: Arc::from([]),
        }
    }
}

/// What the samples say of a node: whether it had one value at every point, its value at
/// the first, and whether something below it (or itself) varies. A function of the node.
type Sampled = IdMap<u32, (bool, BitVec, bool)>;

/// The nodes whose value at every point was asked for.
type Watched = IdMap<u32, Vec<BitVec>>;

/// The value of a symbol at sample point `p`: zeros, ones, then seeded by the key, always
/// with the bits its declaration fixes.
fn point_value(key: &SymbolKey, w: Width, known: Option<crate::KnownBits>, p: u32) -> BitVec {
    let v = match p {
        0 => BitVec::zero(w),
        1 => BitVec::ones(w),
        _ => {
            let h = crate::hash::mix64(
                key.structural_hash() ^ u64::from(p).wrapping_mul(0x9e37_79b9_7f4a_7c15),
            );
            let limbs = [
                h,
                h.rotate_left(17) ^ 0x5851_f42d_4c95_7f2d,
                !h.rotate_left(29),
                h.rotate_left(41) ^ 0x1405_7b7e_f767_814f,
                crate::hash::mix64(h),
                crate::hash::mix64(!h),
                crate::hash::mix64(h ^ 0xa5a5),
                crate::hash::mix64(h.rotate_left(7)),
            ];
            BitVec::wrapping_from_limbs(w, &limbs)
        }
    };
    match known {
        Some(k) => {
            let v = BitVec::bin_unchecked(BinOp::Or, &v, &k.known_one());
            let keep = BitVec::un_unchecked(UnOp::Not, &k.known_zero());
            BitVec::bin_unchecked(BinOp::And, &v, &keep)
        }
        None => v,
    }
}

/// The symbols below `roots`: key, width and what is declared of each.
fn symbols_below(
    cx: &mut Context,
    roots: &[u32],
) -> Result<Vec<(SymbolKey, Width, Option<crate::KnownBits>)>, Error> {
    let roots: Vec<Expr> = roots.iter().map(|&i| cx.handle(i)).collect();
    let mut symbols = Vec::new();
    for id in cx.symbols_in(&roots)? {
        if let (Some(key), Some(w)) = (cx.symbol_key(id).cloned(), cx.symbol_width(id)) {
            let known = cx.find_symbol(&key).and_then(|s| cx.declared_at(s.index()));
            symbols.push((key, w, known));
        }
    }
    Ok(symbols)
}

/// The symbols below `roots`, each with its value at point `p`.
fn point_model(cx: &mut Context, roots: &[u32], p: u32) -> Result<Model, Error> {
    Ok(symbols_below(cx, roots)?
        .into_iter()
        .map(|(key, w, known)| {
            let v = point_value(&key, w, known, p);
            (key, v)
        })
        .collect())
}

/// Samples the nodes below `roots` into `known`, where they are not there yet, and returns
/// the values of the nodes `watch` at every point.
fn sample(
    cx: &mut Context,
    known: &mut Sampled,
    roots: &[u32],
    watch: &[u32],
    points: u32,
) -> Result<Watched, Error> {
    let mut watched: Watched = watch.iter().map(|&i| (i, Vec::new())).collect();
    // A node is sampled with everything below it.
    let missing: Vec<u32> = (roots.iter().copied())
        .filter(|i| !known.contains_key(i))
        .chain(watch.iter().copied())
        .collect();
    if missing.is_empty() {
        return Ok(watched);
    }
    let order = cx.post_order_ids(&missing);
    let handles: Vec<Expr> = order.iter().map(|&i| cx.handle(i)).collect();
    let symbols = symbols_below(cx, &missing)?;
    let mut first: Vec<BitVec> = Vec::new();
    let mut konst = vec![true; order.len()];
    let at: IdMap<u32, usize> = order.iter().enumerate().map(|(k, &i)| (i, k)).collect();
    for p in 0..points.max(2) {
        let env: HashMap<SymbolKey, BitVec> = symbols
            .iter()
            .map(|(key, w, known)| (key.clone(), point_value(key, *w, *known, p)))
            .collect();
        let vals = cx.eval(&handles, &env)?;
        for (&w, kept) in &mut watched {
            if let Some(&k) = at.get(&w) {
                kept.push(vals[k]);
            }
        }
        if p == 0 {
            first = vals;
        } else {
            for (k, v) in vals.iter().enumerate() {
                konst[k] &= *v == first[k];
            }
        }
    }
    for (k, &i) in order.iter().enumerate() {
        // (Operands come first in the order.)
        let varies = !konst[k]
            || cx
                .node(i)
                .children()
                .any(|c| known.get(&c).is_some_and(|x| x.2));
        known.insert(i, (konst[k], first[k], varies));
    }
    Ok(watched)
}

/// The hubs nearest below the nodes `from` (those themselves, when they are hubs). A hub
/// is a node with one value at the samples though something below it varies: where noise
/// cancels. Of a chain of such nodes that only add a literal constant to the one below
/// (or negate it, or mask it), the lowest is the hub: what many questions share is the
/// noise, and each has its own constant on top.
fn hubs_below(cx: &Context, s: &Sampled, from: &[u32], split: &Split) -> Vec<u32> {
    let cancels = |i: u32| s.get(&i).is_some_and(|x| x.0 && x.2);
    let mut seen: HashSet<u32> = HashSet::new();
    let mut stack: Vec<u32> = from.to_vec();
    let mut hubs = Vec::new();
    while let Some(i) = stack.pop() {
        if !seen.insert(i) || !s.get(&i).is_some_and(|x| x.2) {
            continue;
        }
        let n = cx.node(i);
        if !cancels(i) {
            stack.extend(n.children());
            continue;
        }
        let mut inner = n.children().filter(|&c| cx.node(c).op != OpCode::Const);
        match (inner.next(), inner.next()) {
            (Some(only), None) if cancels(only) => stack.push(only),
            _ if cx
                .tree_size(cx.handle(i))
                .is_ok_and(|t| t >= split.min_nodes) =>
            {
                hubs.push(i)
            }
            _ => {}
        }
    }
    hubs
}

/// The terms of the chain of `op` at `i`: its operands, and theirs while they are `op` too.
fn chain(cx: &Context, i: u32, op: OpCode, terms: &mut Vec<u32>) {
    let mut stack = vec![i];
    while let Some(j) = stack.pop() {
        let n = cx.node(j);
        if n.op == op && terms.len() + stack.len() < 4096 {
            stack.push(n.b);
            stack.push(n.a);
        } else {
            terms.push(j);
        }
    }
}

/// `roots` with their chains of `+` and of `^` regrouped: the terms that read a symbol in
/// common are summed together where that sum is constant at the samples (then a hub) and
/// the chain as written is not. Associativity and commutativity only, through the
/// constructors: each result equals its root at every value. Returns how many chains changed.
fn regroup(
    cx: &mut Context,
    known: &mut Sampled,
    roots: &mut [u32],
    points: u32,
    min_terms: usize,
) -> Result<u64, Error> {
    // The symbols each node reads, as a small set; a question over more symbols than fit
    // is left as it is.
    let order = cx.post_order_ids(roots);
    let mut slot: HashMap<u32, u32> = HashMap::new();
    let mut reads: IdMap<u32, u128> = IdMap::default();
    for &i in &order {
        let n = cx.node(i);
        let set = match n.op {
            OpCode::Sym => {
                let next = slot.len() as u32;
                let k = *slot.entry(i).or_insert(next);
                if k >= 128 {
                    return Ok(0);
                }
                1u128 << k
            }
            _ => n.children().fold(0, |acc, c| acc | reads[&c]),
        };
        reads.insert(i, set);
    }
    // The chains, from their tops: a node of the operator that no chain above it took.
    let mut inner: HashSet<u32> = HashSet::new();
    let mut candidates: Vec<(u32, OpCode, Vec<Vec<u32>>)> = Vec::new();
    for &i in order.iter().rev() {
        let n = cx.node(i);
        if !matches!(n.op, OpCode::Add | OpCode::Xor) || inner.contains(&i) {
            continue;
        }
        let mut terms = Vec::new();
        chain(cx, i, n.op, &mut terms);
        for &t in &[n.a, n.b] {
            let mut stack = vec![t];
            while let Some(j) = stack.pop() {
                let m = cx.node(j);
                if m.op == n.op && inner.insert(j) {
                    stack.push(m.a);
                    stack.push(m.b);
                }
            }
        }
        if terms.len() < min_terms {
            continue;
        }
        // Groups of terms joined by a symbol in common, in the order of their first term.
        let mut groups: Vec<(u128, Vec<u32>)> = Vec::new();
        for &t in &terms {
            let set = reads[&t];
            let mut joined: (u128, Vec<u32>) = (set, vec![t]);
            let mut k = 0;
            let mut place = None;
            while k < groups.len() {
                if set != 0 && groups[k].0 & joined.0 != 0 {
                    let g = groups.remove(k);
                    joined.0 |= g.0;
                    let mut all = g.1;
                    all.append(&mut joined.1);
                    joined.1 = all;
                    place.get_or_insert(k);
                    // A merged group may now touch earlier ones.
                    k = 0;
                    continue;
                }
                k += 1;
            }
            match place {
                Some(p) => groups.insert(p.min(groups.len()), joined),
                None => groups.push(joined),
            }
        }
        if groups.len() < 2 || groups.iter().all(|g| g.1.len() < 2) {
            continue;
        }
        candidates.push((i, n.op, groups.into_iter().map(|g| g.1).collect()));
    }
    if candidates.is_empty() {
        return Ok(0);
    }
    // Each group of several terms, summed; the samples say which are constant.
    let bin = |op: OpCode| {
        if op == OpCode::Add {
            BinOp::Add
        } else {
            BinOp::Xor
        }
    };
    let mut sums: Vec<Vec<Option<u32>>> = Vec::new();
    let mut probe: Vec<u32> = Vec::new();
    for (_, op, groups) in &candidates {
        let mut row = Vec::new();
        for g in groups {
            if g.len() < 2 {
                row.push(None);
                continue;
            }
            let mut acc = g[0];
            for &t in &g[1..] {
                acc = cx.c_bin(bin(*op), acc, t)?;
            }
            probe.push(acc);
            row.push(Some(acc));
        }
        sums.push(row);
    }
    let mut all: Vec<u32> = roots.to_vec();
    all.extend_from_slice(&probe);
    sample(cx, known, &all, &[], points)?;
    let konst = |i: u32| known.get(&i).is_some_and(|x| x.0);
    let mut map: Vec<(Expr, Expr)> = Vec::new();
    for ((i, op, groups), row) in candidates.iter().zip(&sums) {
        // Worth it when a group is constant though one of its terms is not, and the chain
        // is not constant as a whole (then it is a hub as written).
        let folds = |g: &Vec<u32>, sum: &Option<u32>| {
            sum.is_some_and(konst) && g.iter().any(|&t| !konst(t))
        };
        if konst(*i) || !groups.iter().zip(row).any(|(g, sum)| folds(g, sum)) {
            continue;
        }
        // The constant groups as their sums, the other terms as they were, in order.
        let mut acc: Option<u32> = None;
        for (g, sum) in groups.iter().zip(row) {
            let parts: Vec<u32> = match sum {
                Some(x) if folds(g, sum) => vec![*x],
                _ => g.clone(),
            };
            for t in parts {
                acc = Some(match acc {
                    None => t,
                    Some(a) => cx.c_bin(bin(*op), a, t)?,
                });
            }
        }
        if let Some(a) = acc
            && a != *i
        {
            map.push((cx.handle(*i), cx.handle(a)));
        }
    }
    if map.is_empty() {
        return Ok(0);
    }
    let handles: Vec<Expr> = roots.iter().map(|&i| cx.handle(i)).collect();
    let new = cx.substitute(&handles, &map)?;
    for (r, e) in roots.iter_mut().zip(new) {
        *r = cx.id(e)?;
    }
    Ok(map.len() as u64)
}

/// The condition the selects below `root` test most (ties: by the nodes' own hashes, which
/// no context changes).
fn condition(cx: &mut Context, root: u32) -> Option<u32> {
    let mut count: HashMap<u32, u32> = HashMap::new();
    for i in cx.post_order_ids(&[root]) {
        let n = cx.node(i);
        if n.op == OpCode::Select && cx.const_val(n.a).is_none() {
            *count.entry(n.a).or_default() += 1;
        }
    }
    count
        .into_iter()
        .max_by_key(|&(c, n)| {
            let h = cx.structural_hash(cx.handle(c)).unwrap_or(0);
            (n, h, cx.tree_size(cx.handle(c)).unwrap_or(0))
        })
        .map(|(c, _)| c)
}

/// A task for a worker: a context of its own holding the root and the constraints.
struct Spec {
    job: usize,
    simplify: bool,
    hub: bool,
    /// Whether the root is this constant: the engine on the root first.
    constant: Option<BitVec>,
    cx: Context,
    root: Expr,
    assume: Vec<(Expr, Facts)>,
    wanted: Wanted,
}

/// What a worker made of a task.
struct Solved {
    job: usize,
    cx: Context,
    /// `None`: stopped by its cancel flags.
    res: Option<SolvedRes>,
    cost: Cost,
}

enum SolvedRes {
    Simplified(Expr, End),
    Outcome(Outcome),
}

enum Step {
    Solve(Box<Spec>),
    /// Waiting for tasks, finished, or cancelled.
    Settled,
}

/// The search between two readings of the cancel flags.
const SLICE: Limits = Limits {
    conflicts: 2_000,
    propagations: 2_000_000,
};

/// Questions answered in batches, on the caller's threads, with a store of what was proved.
/// See the [module](self).
pub struct Session {
    config: Config,
    simplifiers: Simplifiers,
    store: Mutex<Store>,
    wake: Condvar,
    /// One call at a time: the store's context is the calls' workspace.
    calls: Mutex<()>,
}

impl core::fmt::Debug for Session {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Session")
            .field("config", &self.config)
            .finish_non_exhaustive()
    }
}

impl Session {
    /// A session with an empty store and engines of its own.
    pub fn new(config: Config) -> Session {
        #[cfg(feature = "mba")]
        let simplifiers = match config.mba {
            Some(m) => Simplifiers::new().with_mba(m),
            None => Simplifiers::new(),
        };
        #[cfg(not(feature = "mba"))]
        let simplifiers = Simplifiers::new();
        Session::with_simplifiers(config, simplifiers)
    }

    /// A session that simplifies with these engines (a solver shared with other sessions,
    /// say: its memo answers as solving again would, so sharing it changes no answer).
    /// [`Config::mba`] is then theirs to have set.
    pub fn with_simplifiers(mut config: Config, simplifiers: Simplifiers) -> Session {
        config.prove.certificate = false;
        if let Some(h) = &mut config.hub {
            h.certificate = false;
        }
        Session {
            config,
            simplifiers,
            store: Mutex::new(Store {
                cx: Context::new(),
                done: HashMap::new(),
                config: None,
                registry: None,
                sampled: Sampled::default(),
                next_id: 0,
                stats: Stats::default(),
                graph: Graph::default(),
            }),
            wake: Condvar::new(),
            calls: Mutex::new(()),
        }
    }

    /// Its configuration.
    pub fn config(&self) -> &Config {
        &self.config
    }

    /// What it has done so far.
    pub fn stats(&self) -> Stats {
        let st = self.lock();
        Stats {
            store_nodes: st.cx.len() as u64,
            store_answers: st.done.len() as u64,
            ..st.stats
        }
    }

    /// Empties the store. The next answers are the same, and take the time they first did.
    pub fn forget(&self) {
        let _call = self.calls.lock().unwrap_or_else(|e| e.into_inner());
        let mut st = self.lock();
        st.cx = Context::new();
        st.sampled = Sampled::default();
        st.done.clear();
        st.config = None;
        st.stats.flushes += 1;
    }

    fn lock(&self) -> MutexGuard<'_, Store> {
        self.store.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Answers `asks`, questions about expressions of `cx`: `replies[i]` answers `asks[i]`.
    /// The calling thread and up to [`Config::threads`]` - 1` others, started here and gone
    /// when this returns, decide them; results that are expressions are built in `cx`.
    ///
    /// An error is of the questions as posed (an expression of another context, widths
    /// that do not fit) or a broken invariant; a question not decided is an
    /// [`Answer::Unknown`], not an error.
    pub fn run(&self, cx: &mut Context, asks: &[Ask<'_>]) -> Result<Vec<Reply>, Error> {
        let _call = self.calls.lock().unwrap_or_else(|e| e.into_inner());
        let (tops, stored) = {
            let mut st = self.lock();
            st.graph = Graph::default();
            let planned = self.plan(&mut st, cx, asks);
            if planned.is_err() {
                st.graph = Graph::default();
            }
            planned?
        };
        let threads = match self.config.threads {
            0 => std::thread::available_parallelism().map_or(1, |n| n.get()),
            n => n,
        };
        let pending = self.lock().graph.open;
        let threads = threads.clamp(1, pending.max(1));
        if pending > 0 {
            let work = || self.work();
            std::thread::scope(|s| {
                for _ in 1..threads {
                    if std::thread::Builder::new().spawn_scoped(s, work).is_err() {
                        break;
                    }
                }
                work();
            });
        }
        let mut st = self.lock();
        let graph = core::mem::take(&mut st.graph);
        if let Some(e) = graph.error {
            return Err(e);
        }
        let mut replies = Vec::with_capacity(asks.len());
        for (&j, &was_stored) in tops.iter().zip(&stored) {
            let job = &graph.jobs[j];
            replies.push(match &job.state {
                State::Done(entry) => {
                    let answer = match &entry.res {
                        Res::Simplified { expr, end } => {
                            let e = st.cx.handle(*expr);
                            Answer::Simplified {
                                expr: cx.import(&st.cx, &[e])?[0],
                                end: *end,
                            }
                        }
                        Res::Constant(v) => Answer::Constant(*v),
                        Res::Varies(m) => Answer::Varies(m.clone()),
                        Res::Proved => Answer::Proved,
                        Res::Refuted(m) => Answer::Refuted(m.clone()),
                        Res::Unknown(why) => Answer::Unknown(why.clone()),
                    };
                    Reply {
                        answer,
                        cost: entry.total,
                        source: match was_stored {
                            true => Source::Stored,
                            false => Source::Solved,
                        },
                    }
                }
                _ => Reply {
                    answer: Answer::Cancelled,
                    cost: spent_below(&graph, j),
                    source: Source::Solved,
                },
            });
        }
        Ok(replies)
    }

    /// Copies the questions into the store's context and plans those it has no answer to:
    /// each ask's task, and whether the store had its answer.
    fn plan(
        &self,
        st: &mut Store,
        src: &Context,
        asks: &[Ask<'_>],
    ) -> Result<(Vec<usize>, Vec<bool>), Error> {
        for a in asks {
            if let Some(a) = a.assumptions {
                a.check_context(src)?;
            }
        }
        // A store too large, or of contexts configured otherwise, starts again.
        let same = st.config.as_ref() == Some(src.config())
            && match (&st.registry, &src.registry) {
                (None, None) => true,
                (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                _ => false,
            };
        if !same || st.cx.len() > self.config.store_nodes {
            if st.config.is_some() {
                st.stats.flushes += 1;
            }
            st.empty(src);
        }
        if !self.declarations_agree(st, src, asks)? {
            // The store holds a symbol declared otherwise: its answers are of other
            // questions.
            st.stats.flushes += 1;
            st.empty(src);
        }
        let keys = self.import(st, src, asks)?;
        st.stats.asks += asks.len() as u64;
        let mut tops = Vec::with_capacity(asks.len());
        let mut stored = Vec::with_capacity(asks.len());
        let mut fresh: Vec<usize> = Vec::new();
        for (key, ask) in keys.into_iter().zip(asks) {
            let wanted = match &ask.cancel {
                Some(c) => Wanted {
                    always: false,
                    flags: vec![c.clone()],
                },
                None => Wanted {
                    always: true,
                    flags: Vec::new(),
                },
            };
            let had = st.done.contains_key(&key);
            stored.push(had);
            if had {
                st.stats.asks_stored += 1;
            } else if st.graph.by_key.contains_key(&key) {
                st.stats.asks_repeated += 1;
            }
            let known = st.graph.by_key.contains_key(&key);
            let j = self.job(st, key, &wanted);
            if !had && !known {
                fresh.push(j);
            }
            if st.graph.tops.insert(j) && !matches!(st.graph.jobs[j].state, State::Done(_)) {
                st.graph.open += 1;
            }
            tops.push(j);
        }
        self.plan_asks(st, &fresh)?;
        Ok((tops, stored))
    }

    /// The asks' keys: their expressions copied into the store's context.
    fn import(&self, st: &mut Store, src: &Context, asks: &[Ask<'_>]) -> Result<Vec<Key>, Error> {
        let mut keys = Vec::with_capacity(asks.len());
        for a in asks {
            let before = st.cx.len();
            let (what, root) = match a.kind {
                Kind::Simplify(e) => (What::AskSimplify, st.cx.import(src, &[e])?[0]),
                Kind::Constant(e) => (What::AskConstant, st.cx.import(src, &[e])?[0]),
                Kind::Valid(p) => {
                    let w = src.wid(src.id(p)?);
                    if w != 1 {
                        return Err(crate::WidthError::Mismatch { left: 1, right: w }.into());
                    }
                    (What::AskValid(0), st.cx.import(src, &[p])?[0])
                }
                Kind::Equal(x, y) => {
                    let both = st.cx.import(src, &[x, y])?;
                    (What::AskValid(0), st.cx.cmp(CmpOp::Eq, both[0], both[1])?)
                }
            };
            let mut assume = Vec::new();
            if let Some(asm) = a.assumptions {
                for (_, e, facts) in asm.constraints() {
                    let e = st.cx.import(src, &[e])?[0];
                    assume.push((st.cx.id(e)?, facts));
                }
            }
            let mut all = vec![root];
            all.extend(assume.iter().map(|x| st.cx.handle(x.0)));
            st.stats.nodes_asked += st.cx.post_order(&all)?.len() as u64;
            st.stats.nodes_new += (st.cx.len() - before) as u64;
            keys.push(Key {
                what,
                root: st.cx.id(root)?,
                assume: assume.into(),
                k: None,
            });
        }
        Ok(keys)
    }

    /// Whether every symbol of the asks that the store's context holds is declared there as
    /// in `src`.
    fn declarations_agree(
        &self,
        st: &mut Store,
        src: &Context,
        asks: &[Ask<'_>],
    ) -> Result<bool, Error> {
        let mut roots: Vec<Expr> = Vec::new();
        for a in asks {
            match a.kind {
                Kind::Simplify(e) | Kind::Constant(e) | Kind::Valid(e) => roots.push(e),
                Kind::Equal(x, y) => roots.extend([x, y]),
            }
            if let Some(asm) = a.assumptions {
                roots.extend(asm.constraints().map(|c| c.1));
            }
        }
        let ids = src.ids(&roots)?;
        let mut seen: HashSet<u32> = HashSet::new();
        let mut stack = ids;
        while let Some(i) = stack.pop() {
            if !seen.insert(i) {
                continue;
            }
            let n = src.node(i);
            if n.op == OpCode::Sym {
                let key = &src.symbols.entries[n.a as usize].key;
                // (A symbol the store has not met is declared as it arrives.)
                if let Some(theirs) = st.cx.find_symbol(key)
                    && st.cx.declared_at(theirs.index()) != src.declared_at(i)
                {
                    return Ok(false);
                }
            }
            stack.extend(n.children());
        }
        Ok(true)
    }

    /// The task of `key`, made if this call has none: done when the store has its answer.
    /// A new one that is not a leaf waits to be planned.
    fn job(&self, st: &mut Store, key: Key, wanted: &Wanted) -> usize {
        if let Some(&j) = st.graph.by_key.get(&key) {
            self.want(st, j, wanted);
            return j;
        }
        let state = match st.done.get(&key) {
            Some(e) => State::Done(e.clone()),
            None => State::Pending,
        };
        let plan = match key.what {
            What::LeafSimplify | What::LeafValid | What::LeafHub | What::LeafConstant => Plan::Leaf,
            What::Hub => Plan::Hub {
                k: BitVec::zero(Width::W1),
                below: Vec::new(),
                proofs: [None, None],
            },
            _ => Plan::Ask {
                candidate: None,
                fallback: false,
                root: key.root,
                hubs: Vec::new(),
                first: None,
                pred: key.root,
                rest: None,
                cases: None,
            },
        };
        let j = st.graph.jobs.len();
        st.graph.by_key.insert(key.clone(), j);
        st.graph.jobs.push(Job {
            key,
            plan,
            deps: Vec::new(),
            base: 0,
            waiting: 0,
            dependents: Vec::new(),
            state,
            stage: 0,
            wanted: wanted.clone(),
            partial: Cost::default(),
        });
        j
    }

    /// `j` and the tasks it needs also work for `wanted`; one that was cancelled starts
    /// again.
    fn want(&self, st: &mut Store, j: usize, wanted: &Wanted) {
        let mut stack = vec![j];
        while let Some(j) = stack.pop() {
            let job = &mut st.graph.jobs[j];
            let grew = job.wanted.join(wanted);
            if matches!(job.state, State::Cancelled) && !job.wanted.stopped() {
                self.revive(st, j);
            } else if !grew {
                continue;
            }
            stack.extend(st.graph.jobs[j].deps.iter().copied());
        }
    }

    /// A cancelled task that is wanted again: from its beginning.
    fn revive(&self, st: &mut Store, j: usize) {
        let job = &mut st.graph.jobs[j];
        job.deps.truncate(job.base);
        job.stage = 0;
        job.partial = Cost::default();
        job.dependents.clear();
        job.waiting = 0;
        job.state = State::Pending;
        let base = job.base;
        if let Plan::Hub { below, proofs, .. } = &mut job.plan {
            below.clear();
            *proofs = [None, None];
        }
        if let Plan::Ask {
            rest,
            cases,
            first,
            hubs,
            ..
        } = &mut job.plan
        {
            (*rest, *cases, *first) = (None, None, None);
            hubs.truncate(base);
        }
        if st.graph.tops.contains(&j) {
            st.graph.open += 1;
        }
        let wanted = job.wanted.clone();
        for d in st.graph.jobs[j].deps.clone() {
            st.graph.jobs[d].wanted.join(&wanted);
            if matches!(st.graph.jobs[d].state, State::Cancelled) {
                self.revive(st, d);
            }
            if !matches!(st.graph.jobs[d].state, State::Done(_)) {
                st.graph.jobs[d].dependents.push(j);
                st.graph.jobs[j].waiting += 1;
            }
        }
        self.ready_if(st, j);
    }

    fn ready_if(&self, st: &mut Store, j: usize) {
        let job = &mut st.graph.jobs[j];
        if job.waiting == 0 && matches!(job.state, State::Pending) {
            job.state = State::Ready;
            st.graph.ready.push_back(j);
        }
    }

    /// `j` needs `d`.
    fn depend(&self, st: &mut Store, j: usize, d: usize) {
        st.graph.jobs[j].deps.push(d);
        if !matches!(st.graph.jobs[d].state, State::Done(_)) {
            st.graph.jobs[d].dependents.push(j);
            st.graph.jobs[j].waiting += 1;
        }
    }

    /// Plans the new questions `asks` (tasks of this call): samples them together,
    /// regroups their chains, and makes the tasks of their hubs.
    fn plan_asks(&self, st: &mut Store, asks: &[usize]) -> Result<(), Error> {
        let split = self.config.split;
        let asks: Vec<usize> = asks
            .iter()
            .copied()
            .filter(|&j| matches!(st.graph.jobs[j].state, State::Pending))
            .collect();
        if asks.is_empty() {
            return Ok(());
        }
        let mut roots: Vec<u32> = asks.iter().map(|&j| st.graph.jobs[j].key.root).collect();
        let constants: Vec<usize> = (0..asks.len())
            .filter(|&k| st.graph.jobs[asks[k]].key.what == What::AskConstant)
            .collect();
        if !split.hubs && constants.is_empty() {
            for &j in &asks {
                st.graph.jobs[j].base = 0;
                self.ready_if(st, j);
            }
            return Ok(());
        }
        if split.hubs && split.terms {
            let store = &mut *st;
            let n = regroup(
                &mut store.cx,
                &mut store.sampled,
                &mut roots,
                split.points,
                3,
            )?;
            st.stats.regrouped += n;
        }
        // A constant question's value is read where its assumptions hold.
        let mut watch: Vec<u32> = Vec::new();
        let mut all = roots.clone();
        for &k in &constants {
            watch.push(roots[k]);
            for (e, _) in st.graph.jobs[asks[k]].key.assume.iter() {
                watch.push(*e);
                all.push(*e);
            }
        }
        let store = &mut *st;
        let watched = sample(
            &mut store.cx,
            &mut store.sampled,
            &all,
            &watch,
            split.points,
        )?;
        for &k in &constants {
            let j = asks[k];
            let assume = st.graph.jobs[j].key.assume.clone();
            let values = &watched[&roots[k]];
            let holds = |p: usize| assume.iter().all(|(e, f)| f.contains(&watched[e][p]));
            let mut at: Option<usize> = None;
            let mut varies: Option<(usize, usize)> = None;
            for p in 0..values.len() {
                if !holds(p) {
                    continue;
                }
                match at {
                    None => at = Some(p),
                    Some(q) if values[q] != values[p] => {
                        varies = Some((q, p));
                        break;
                    }
                    Some(_) => {}
                }
            }
            if let Some((p, q)) = varies {
                // Two values where the assumptions hold: evaluated, so decided.
                let mut near = vec![st.graph.jobs[j].key.root];
                near.extend(assume.iter().map(|x| x.0));
                let a = point_model(&mut st.cx, &near, p as u32)?;
                let b = point_model(&mut st.cx, &near, q as u32)?;
                let entry = st.entry(Res::Varies(Box::new((a, b))), Cost::default(), Vec::new());
                self.finish(st, j, entry);
                continue;
            }
            if let Plan::Ask {
                candidate,
                fallback,
                ..
            } = &mut st.graph.jobs[j].plan
            {
                match at {
                    Some(p) => *candidate = Some((values[p], p as u32)),
                    None => *fallback = true,
                }
            }
        }
        for (k, &j) in asks.iter().enumerate() {
            if let Plan::Ask { root, .. } = &mut st.graph.jobs[j].plan {
                *root = roots[k];
            }
        }
        if split.hubs {
            // A proof asked whole first makes its hubs' tasks only if it must.
            for (&j, &root) in asks.iter().zip(&roots) {
                if !self.whole_first(st, j) {
                    self.plan_hubs(st, j, &[root]);
                    st.graph.jobs[j].base = st.graph.jobs[j].deps.len();
                }
            }
        }
        let n = st.graph.jobs.len();
        for j in 0..n {
            self.ready_if(st, j);
        }
        Ok(())
    }

    /// Whether the question `j` is asked whole before it is cut.
    fn whole_first(&self, st: &Store, j: usize) -> bool {
        let job = &st.graph.jobs[j];
        let fallback = matches!(job.plan, Plan::Ask { fallback: true, .. });
        self.config.split.whole_first && !fallback
    }

    /// Makes the tasks of the hubs nearest below the nodes `from` and has `parent` (a
    /// question, or a hub that was not proved as written) wait for them, from the samples
    /// `s` of those nodes.
    fn plan_hubs(&self, st: &mut Store, parent: usize, from: &[u32]) {
        if matches!(st.graph.jobs[parent].state, State::Done(_)) {
            return;
        }
        let split = self.config.split;
        let wanted = st.graph.jobs[parent].wanted.clone();
        for h in hubs_below(&st.cx, &st.sampled, from, &split) {
            let key = Key {
                what: What::Hub,
                root: h,
                assume: Arc::from([]),
                k: None,
            };
            let new = !st.graph.by_key.contains_key(&key);
            let stored = st.done.contains_key(&key);
            let j = self.job(st, key, &wanted);
            if new && stored {
                st.stats.tasks_stored += 1;
            } else if new {
                st.stats.hubs += 1;
                if let Plan::Hub { k, .. } = &mut st.graph.jobs[j].plan {
                    *k = st.sampled[&h].1;
                }
            }
            self.depend(st, parent, j);
            match &mut st.graph.jobs[parent].plan {
                Plan::Ask { hubs, .. } => hubs.push(j),
                Plan::Hub { below, .. } => below.push(j),
                Plan::Leaf => {}
            }
            self.ready_if(st, j);
        }
    }

    /// The proved constants to write for the tasks `deps` of a hub or a question.
    fn substitution(&self, st: &Store, deps: &[usize]) -> Vec<(u32, BitVec)> {
        let mut seen: HashSet<u32> = HashSet::new();
        let mut pairs = Vec::new();
        for &d in deps {
            if let State::Done(e) = &st.graph.jobs[d].state {
                for (i, v) in e.subst.iter() {
                    if seen.insert(*i) {
                        pairs.push((*i, *v));
                    }
                }
            }
        }
        pairs
    }

    fn substituted(
        &self,
        st: &mut Store,
        root: u32,
        pairs: &[(u32, BitVec)],
    ) -> Result<u32, Error> {
        if pairs.is_empty() {
            return Ok(root);
        }
        let mut map = Vec::with_capacity(pairs.len());
        for (i, v) in pairs {
            let c = st.cx.mk_const(v)?;
            map.push((st.cx.handle(*i), st.cx.handle(c)));
        }
        let e = st.cx.substitute(&[st.cx.handle(root)], &map)?[0];
        st.cx.id(e)
    }

    fn parts(&self, st: &Store, j: usize) -> Vec<Arc<Entry>> {
        let mut parts = Vec::new();
        for &d in &st.graph.jobs[j].deps {
            if let State::Done(e) = &st.graph.jobs[d].state {
                parts.push(e.clone());
            }
        }
        parts
    }

    /// A leaf task, as a dependency of `j`.
    fn leaf(
        &self,
        st: &mut Store,
        j: usize,
        what: What,
        root: u32,
        assume: Arc<[(u32, Facts)]>,
        k: Option<BitVec>,
    ) -> usize {
        let key = Key {
            what,
            root,
            assume,
            k,
        };
        if !st.graph.by_key.contains_key(&key) && st.done.contains_key(&key) {
            st.stats.tasks_stored += 1;
        }
        let wanted = st.graph.jobs[j].wanted.clone();
        let l = self.job(st, key, &wanted);
        self.depend(st, j, l);
        self.ready_if(st, l);
        l
    }

    /// Takes the ready task `j` as far as it goes without a worker's own work: to a leaf
    /// to solve, to waiting for tasks it has just made, or to its end.
    fn advance(&self, st: &mut Store, j: usize) -> Result<Step, Error> {
        loop {
            let job = &st.graph.jobs[j];
            if job
                .deps
                .iter()
                .any(|&d| matches!(st.graph.jobs[d].state, State::Cancelled))
            {
                // Its tasks work for all it works for, so they were cancelled with it.
                if !job.wanted.stopped() {
                    return Err(Error::Contract("a wanted task's part was cancelled".into()));
                }
                self.cancel(st, j, Cost::default());
                return Ok(Step::Settled);
            }
            if job.waiting > 0 {
                st.graph.jobs[j].state = State::Pending;
                return Ok(Step::Settled);
            }
            let (key, stage) = (job.key.clone(), job.stage);
            match &job.plan {
                Plan::Leaf => {
                    let mut cx = Context::with_config(st.cx.config().clone());
                    cx.registry = st.cx.registry.clone();
                    let root = cx.import(&st.cx, &[st.cx.handle(key.root)])?[0];
                    let mut assume = Vec::with_capacity(key.assume.len());
                    for (e, f) in key.assume.iter() {
                        assume.push((cx.import(&st.cx, &[st.cx.handle(*e)])?[0], *f));
                    }
                    return Ok(Step::Solve(Box::new(Spec {
                        job: j,
                        simplify: key.what == What::LeafSimplify,
                        hub: key.what == What::LeafHub,
                        constant: key.k,
                        cx,
                        root,
                        assume,
                        wanted: st.graph.jobs[j].wanted.clone(),
                    })));
                }
                Plan::Hub { k, below, proofs } => {
                    let (k, below, proofs) = (*k, below.clone(), *proofs);
                    let proved_by = |st: &Store, l: Option<usize>| {
                        l.is_some_and(|l| match &st.graph.jobs[l].state {
                            State::Done(e) => matches!(e.res, Res::Proved),
                            _ => false,
                        })
                    };
                    if stage == 0 {
                        // As written: where the engine folds the noise by itself, one
                        // proof serves for all that is below.
                        let l = self.leaf(st, j, What::LeafHub, key.root, Arc::from([]), Some(k));
                        if let Plan::Hub { proofs, .. } = &mut st.graph.jobs[j].plan {
                            proofs[0] = Some(l);
                        }
                        st.graph.jobs[j].stage = 1;
                        continue;
                    }
                    let mut proved = proved_by(st, proofs[0]);
                    if stage == 1 && !proved && self.config.split.nested {
                        // The hubs below it first, then.
                        let kids: Vec<u32> = st.cx.node(key.root).children().collect();
                        let store = &mut *st;
                        let points = self.config.split.points;
                        sample(&mut store.cx, &mut store.sampled, &kids, &[], points)?;
                        self.plan_hubs(st, j, &kids);
                        st.graph.jobs[j].stage = 2;
                        continue;
                    }
                    let pairs = self.substitution(st, &below);
                    if stage == 2 && !pairs.is_empty() {
                        let hub = self.substituted(st, key.root, &pairs)?;
                        if st.cx.const_val(hub) == Some(k) {
                            // Folded by the constants below it.
                            proved = true;
                        } else {
                            let l = self.leaf(st, j, What::LeafHub, hub, Arc::from([]), Some(k));
                            if let Plan::Hub { proofs, .. } = &mut st.graph.jobs[j].plan {
                                proofs[1] = Some(l);
                            }
                            st.graph.jobs[j].stage = 3;
                            continue;
                        }
                    }
                    proved |= proved_by(st, proofs[1]);
                    let parts = self.parts(st, j);
                    let res = match proved {
                        true => Res::Constant(k),
                        false => Res::Unknown(Unknown::Unsupported("not proved constant".into())),
                    };
                    let mut entry = st.entry(res, Cost::default(), parts);
                    entry.subst = match proved {
                        true => Arc::from([(key.root, k)]),
                        false => pairs.into(),
                    };
                    st.stats.hubs_proved += u64::from(proved);
                    self.finish(st, j, entry);
                    return Ok(Step::Settled);
                }
                Plan::Ask {
                    candidate,
                    fallback,
                    root,
                    hubs,
                    first,
                    pred,
                    rest,
                    cases,
                } => {
                    let (candidate, fallback, root, pred) = (*candidate, *fallback, *root, *pred);
                    let (rest, cases, first) = (*rest, *cases, *first);
                    let hubs = hubs.clone();
                    let done = |st: &Store, d: usize| match &st.graph.jobs[d].state {
                        State::Done(e) => Ok(e.clone()),
                        _ => Err(Error::Contract("a task ready before its parts".into())),
                    };
                    if stage == 0 {
                        if self.whole_first(st, j) {
                            // The question as asked, before any cut.
                            let whole = match candidate {
                                Some((k, _)) if key.what == What::AskConstant => {
                                    let konst = st.cx.mk_const(&k)?;
                                    st.cx.c_cmp(CmpOp::Eq, key.root, konst)?
                                }
                                _ => key.root,
                            };
                            let l = match (key.what, candidate) {
                                (What::AskSimplify, _) => {
                                    let what = What::LeafSimplify;
                                    self.leaf(st, j, what, key.root, key.assume.clone(), None)
                                }
                                (What::AskConstant, Some((k, _))) => {
                                    let what = What::LeafConstant;
                                    self.leaf(st, j, what, key.root, key.assume.clone(), Some(k))
                                }
                                _ => self.leaf(
                                    st,
                                    j,
                                    What::LeafValid,
                                    whole,
                                    key.assume.clone(),
                                    None,
                                ),
                            };
                            if let Plan::Ask { first, pred, .. } = &mut st.graph.jobs[j].plan {
                                (*first, *pred) = (Some(l), whole);
                            }
                            st.graph.jobs[j].stage = 1;
                        } else {
                            st.graph.jobs[j].stage = 2;
                        }
                        continue;
                    }
                    if stage == 1 {
                        let l = first.ok_or_else(|| Error::Contract("no first attempt".into()))?;
                        let whole = done(st, l)?;
                        // (A simplification is an answer as it is.)
                        if matches!(
                            whole.res,
                            Res::Proved | Res::Refuted(_) | Res::Simplified { .. }
                        ) {
                            let res =
                                self.answer(st, &key, candidate, fallback, whole.res.clone())?;
                            let parts = self.parts(st, j);
                            let entry = st.entry(res, Cost::default(), parts);
                            self.finish(st, j, entry);
                            return Ok(Step::Settled);
                        }
                        if self.config.split.hubs {
                            let store = &mut *st;
                            let points = self.config.split.points;
                            sample(&mut store.cx, &mut store.sampled, &[root], &[], points)?;
                            self.plan_hubs(st, j, &[root]);
                            st.graph.jobs[j].stage = 2;
                        } else {
                            if let Plan::Ask { rest, .. } = &mut st.graph.jobs[j].plan {
                                *rest = Some(l);
                            }
                            st.graph.jobs[j].stage = 3;
                        }
                        continue;
                    }
                    if stage == 2 {
                        let pairs = self.substitution(st, &hubs);
                        let left = self.substituted(st, root, &pairs)?;
                        let mut is = None;
                        let (what, asked) = match (key.what, candidate) {
                            (What::AskSimplify, _) => (What::LeafSimplify, left),
                            (What::AskConstant, _) if fallback => (What::LeafSimplify, left),
                            (What::AskConstant, Some((k, _))) => {
                                if let Some(v) = st.cx.const_val(left) {
                                    // What is left is a constant: of every value.
                                    let parts = self.parts(st, j);
                                    let entry = st.entry(Res::Constant(v), Cost::default(), parts);
                                    self.finish(st, j, entry);
                                    return Ok(Step::Settled);
                                }
                                let konst = st.cx.mk_const(&k)?;
                                is = Some(k);
                                (What::LeafConstant, st.cx.c_cmp(CmpOp::Eq, left, konst)?)
                            }
                            _ => (What::LeafValid, left),
                        };
                        // A constant is asked of the expression; the equality is what a
                        // case split would be of.
                        let of = if is.is_some() { left } else { asked };
                        let l = self.leaf(st, j, what, of, key.assume.clone(), is);
                        if let Plan::Ask { pred, rest, .. } = &mut st.graph.jobs[j].plan {
                            (*pred, *rest) = (asked, Some(l));
                        }
                        st.graph.jobs[j].stage = 3;
                        continue;
                    }
                    let rest = rest.ok_or_else(|| Error::Contract("no remainder".into()))?;
                    let answer = done(st, rest)?;
                    let depth = match key.what {
                        What::AskValid(d) => d,
                        _ => 0,
                    };
                    let mut res = answer.res.clone();
                    if stage == 3
                        && matches!(key.what, What::AskValid(_) | What::AskConstant)
                        && !fallback
                        && depth < self.config.split.cases
                        && matches!(
                            res,
                            Res::Unknown(Unknown::Budget { .. } | Unknown::TooLarge { .. })
                        )
                        && let Some(c) = condition(&mut st.cx, pred)
                    {
                        // Two questions: where the condition holds, and where it does not.
                        let mut halves = [0usize; 2];
                        for (h, value) in halves.iter_mut().zip([true, false]) {
                            let b = st.cx.bool(value)?;
                            let fixed = st
                                .cx
                                .substitute(&[st.cx.handle(pred)], &[(st.cx.handle(c), b)])?[0];
                            let guard = match value {
                                true => st.cx.c_un(UnOp::Not, c)?,
                                false => c,
                            };
                            let fixed = st.cx.id(fixed)?;
                            let half = st.cx.c_bin(BinOp::Or, guard, fixed)?;
                            let key = Key {
                                what: What::AskValid(depth + 1),
                                root: half,
                                assume: key.assume.clone(),
                                k: None,
                            };
                            let new = !st.graph.by_key.contains_key(&key);
                            if new && st.done.contains_key(&key) {
                                st.stats.tasks_stored += 1;
                            }
                            let wanted = st.graph.jobs[j].wanted.clone();
                            let child = self.job(st, key, &wanted);
                            if new {
                                self.plan_asks(st, &[child])?;
                            }
                            self.depend(st, j, child);
                            *h = child;
                        }
                        st.stats.case_splits += 1;
                        if let Plan::Ask { cases, .. } = &mut st.graph.jobs[j].plan {
                            *cases = Some((halves[0], halves[1]));
                        }
                        st.graph.jobs[j].stage = 4;
                        continue;
                    }
                    if let Some((a, b)) = cases {
                        let (a, b) = (done(st, a)?, done(st, b)?);
                        res = match (&a.res, &b.res) {
                            (Res::Proved, Res::Proved) => Res::Proved,
                            (Res::Refuted(m), _) | (_, Res::Refuted(m)) => Res::Refuted(m.clone()),
                            _ => res,
                        };
                    }
                    let res = self.answer(st, &key, candidate, fallback, res)?;
                    let parts = self.parts(st, j);
                    let entry = st.entry(res, Cost::default(), parts);
                    self.finish(st, j, entry);
                    return Ok(Step::Settled);
                }
            }
        }
    }

    /// The answer of the question `key` from that of its remainder, a counterexample
    /// replayed on the question as asked.
    fn answer(
        &self,
        st: &mut Store,
        key: &Key,
        candidate: Option<(BitVec, u32)>,
        fallback: bool,
        res: Res,
    ) -> Result<Res, Error> {
        let mut near = vec![key.root];
        near.extend(key.assume.iter().map(|x| x.0));
        // The values of the question and its constraints at a counterexample.
        let replay = |st: &mut Store, model: &mut Model| -> Result<(BitVec, bool), Error> {
            let given: HashSet<SymbolKey> = model.iter().map(|x| x.0.clone()).collect();
            for (k, v) in point_model(&mut st.cx, &near, 0)? {
                if !given.contains(&k) {
                    model.push((k, v));
                }
            }
            let env: HashMap<SymbolKey, BitVec> = model.iter().cloned().collect();
            let handles: Vec<Expr> = near.iter().map(|&i| st.cx.handle(i)).collect();
            let vals = st.cx.eval(&handles, &env)?;
            let holds = (key.assume.iter().zip(&vals[1..])).all(|((_, f), v)| f.contains(v));
            Ok((vals[0], holds))
        };
        let unsound = || Error::Contract("a counterexample does not refute its question".into());
        Ok(match (key.what, res) {
            (What::AskConstant, Res::Simplified { expr, .. }) if fallback => {
                match st.cx.const_val(expr) {
                    Some(v) => Res::Constant(v),
                    None => Res::Unknown(Unknown::Unsupported(
                        "no sample satisfies the assumptions".into(),
                    )),
                }
            }
            (What::AskConstant, Res::Proved) => match candidate {
                Some((k, _)) => Res::Constant(k),
                None => return Err(Error::Contract("a constant without a candidate".into())),
            },
            (What::AskConstant, Res::Refuted(mut m)) => {
                let Some((k, p)) = candidate else {
                    return Err(unsound());
                };
                let (v, holds) = replay(st, &mut m)?;
                if v == k || !holds {
                    return Err(unsound());
                }
                let other = point_model(&mut st.cx, &near, p)?;
                Res::Varies(Box::new((other, m)))
            }
            (What::AskValid(_), Res::Refuted(mut m)) => {
                let (v, holds) = replay(st, &mut m)?;
                if !v.is_zero() || !holds {
                    return Err(unsound());
                }
                Res::Refuted(m)
            }
            (_, res) => res,
        })
    }

    /// `j` is done: kept in the store, and the tasks waiting for it are told.
    fn finish(&self, st: &mut Store, j: usize, mut entry: Entry) {
        if st.graph.tops.contains(&j) || matches!(st.graph.jobs[j].plan, Plan::Ask { .. }) {
            // A question's cost: every task below it, once.
            let mut total = entry.own;
            let mut seen: HashSet<u64> = HashSet::new();
            let mut stack: Vec<&Arc<Entry>> = entry.parts.iter().collect();
            while let Some(e) = stack.pop() {
                if seen.insert(e.id) {
                    total.add(&e.own);
                    stack.extend(e.parts.iter());
                }
            }
            entry.total = total;
        }
        let entry = Arc::new(entry);
        let key = st.graph.jobs[j].key.clone();
        st.done.insert(key, entry.clone());
        st.graph.jobs[j].state = State::Done(entry);
        self.settled(st, j);
    }

    /// `j` stopped for its cancel flags, having spent `partial`.
    fn cancel(&self, st: &mut Store, j: usize, partial: Cost) {
        st.stats.cancelled += 1;
        st.graph.jobs[j].partial = partial;
        st.graph.jobs[j].state = State::Cancelled;
        self.settled(st, j);
    }

    fn settled(&self, st: &mut Store, j: usize) {
        if st.graph.tops.contains(&j) {
            st.graph.open -= 1;
        }
        for d in core::mem::take(&mut st.graph.jobs[j].dependents) {
            let job = &mut st.graph.jobs[d];
            job.waiting = job.waiting.saturating_sub(1);
            self.ready_if(st, d);
        }
        self.wake.notify_all();
    }

    /// A worker: takes ready tasks until every ask is answered.
    fn work(&self) {
        let mut st = self.lock();
        loop {
            if st.graph.error.is_some() || st.graph.open == 0 {
                self.wake.notify_all();
                return;
            }
            let Some(j) = st.graph.ready.pop_front() else {
                if st.graph.running == 0 {
                    st.graph.error = Some(Error::Contract("tasks left with none ready".into()));
                    continue;
                }
                st = self.wake.wait(st).unwrap_or_else(|e| e.into_inner());
                continue;
            };
            if !matches!(st.graph.jobs[j].state, State::Ready) {
                continue;
            }
            if st.graph.jobs[j].wanted.stopped() {
                self.cancel(&mut st, j, Cost::default());
                continue;
            }
            let spec = match self.advance(&mut st, j) {
                Ok(Step::Settled) => continue,
                Ok(Step::Solve(spec)) => spec,
                Err(e) => {
                    st.graph.error = Some(e);
                    continue;
                }
            };
            st.graph.jobs[j].state = State::Running;
            st.graph.running += 1;
            drop(st);
            let solved =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.solve(*spec)));
            st = self.lock();
            st.graph.running -= 1;
            let merged = match solved {
                Ok(Ok(s)) => self.merge(&mut st, s),
                Ok(Err(e)) => Err(e),
                Err(_) => Err(Error::Contract("a task panicked".into())),
            };
            if let Err(e) = merged {
                st.graph.error = Some(e);
            }
        }
    }

    /// A worker's result, into the store.
    fn merge(&self, st: &mut Store, s: Solved) -> Result<(), Error> {
        let j = s.job;
        let Some(res) = s.res else {
            if st.graph.jobs[j].wanted.stopped() {
                self.cancel(st, j, s.cost);
            } else {
                // Wanted again since it started: from its beginning.
                st.graph.jobs[j].state = State::Ready;
                st.graph.ready.push_back(j);
                self.wake.notify_all();
            }
            return Ok(());
        };
        let res = match res {
            SolvedRes::Simplified(e, end) => {
                let e = st.cx.import(&s.cx, &[e])?[0];
                Res::Simplified {
                    expr: st.cx.id(e)?,
                    end,
                }
            }
            SolvedRes::Outcome(Outcome::Proved(_)) => Res::Proved,
            SolvedRes::Outcome(Outcome::Refuted(m)) => Res::Refuted(m),
            SolvedRes::Outcome(Outcome::Unknown(why)) => Res::Unknown(why),
        };
        st.stats.tasks_solved += 1;
        let entry = st.entry(res, s.cost, Vec::new());
        self.finish(st, j, entry);
        Ok(())
    }

    /// Decides a leaf in its own context: the engine on its root, or a proof of it.
    fn solve(&self, spec: Spec) -> Result<Solved, Error> {
        let Spec {
            job,
            simplify,
            hub,
            constant,
            mut cx,
            mut root,
            assume,
            wanted,
        } = spec;
        let cfg = match (hub, &self.config.hub) {
            (true, Some(h)) => h,
            _ => &self.config.prove,
        };
        let mut assumptions = Assumptions::new();
        for (e, facts) in &assume {
            assumptions.assume(&mut cx, *e, *facts)?;
        }
        let assumptions = (!assume.is_empty()).then_some(&assumptions);
        let deadline = (!wanted.always).then(|| Deadline::new(&wanted, 1));
        let mut cost = Cost {
            tasks: 1,
            ..Cost::default()
        };
        if simplify {
            let mut spent = Allowance::new(Budget::UNLIMITED);
            let mut run = Run::default()
                .with_per_call(cfg.simplify_budget)
                .with_allowance(&mut spent);
            if let Some(a) = assumptions {
                run = run.with_assumptions(a);
            }
            if let Some(d) = deadline {
                run = run.with_deadline(d);
            }
            let engine = self.simplifiers.engine(cfg.strict, cfg.proved_words);
            let out = engine.run(&mut cx, &[root], run)?.roots[0];
            cost.simplify = spent.spent();
            let stopped = out.end == End::BudgetTerminated(Exhausted::Deadline);
            return Ok(Solved {
                job,
                res: (!stopped).then_some(SolvedRes::Simplified(out.expr, out.end)),
                cx,
                cost,
            });
        }
        if let Some(k) = constant {
            // The engine on the expression. Asked of the equality with `k` it moves terms
            // across it, and what cancels on one side no longer meets.
            let konst = cx.constant(&k)?;
            if cfg.simplify {
                let mut spent = Allowance::new(Budget::UNLIMITED);
                let mut run = Run::default()
                    .with_per_call(cfg.simplify_budget)
                    .with_allowance(&mut spent);
                if let Some(a) = assumptions {
                    run = run.with_assumptions(a);
                }
                if let Some(d) = deadline {
                    run = run.with_deadline(d);
                }
                let engine = self.simplifiers.engine(cfg.strict, cfg.proved_words);
                let out = engine.run(&mut cx, &[root], run)?.roots[0];
                cost.simplify = spent.spent();
                if out.end == End::BudgetTerminated(Exhausted::Deadline) {
                    return Ok(Solved {
                        job,
                        res: None,
                        cx,
                        cost,
                    });
                }
                if out.expr == konst {
                    return Ok(Solved {
                        job,
                        res: Some(SolvedRes::Outcome(Outcome::Proved(None))),
                        cx,
                        cost,
                    });
                }
                root = out.expr;
            }
            root = cx.cmp(CmpOp::Eq, root, konst)?;
        }
        let env = Env {
            simplifiers: &self.simplifiers,
            deadline,
        };
        let before_build = cost.simplify;
        let mut q = Question::build(&mut cx, root, assumptions, &[], cfg, env)?;
        let total = cfg.limits();
        let before = q.stats();
        let outcome = loop {
            let now = q.stats();
            // What is left of the limits, counted from the first search as one search's are.
            let left = Limits {
                conflicts: total
                    .conflicts
                    .saturating_sub(now.conflicts - before.conflicts),
                propagations: total
                    .propagations
                    .saturating_sub(now.propagations - before.propagations),
            };
            // (A limit used up leaves nothing to slice: the search says so itself.)
            let whole = wanted.always || left.conflicts == 0 || left.propagations == 0;
            let slice = match whole {
                true => left,
                false => Limits {
                    conflicts: left.conflicts.min(SLICE.conflicts),
                    propagations: left.propagations.min(SLICE.propagations),
                },
            };
            match q.solve(&mut cx, slice)? {
                Outcome::Unknown(Unknown::Budget { .. }) if slice != left && !wanted.stopped() => {}
                Outcome::Unknown(Unknown::Budget { .. }) if slice != left => break None,
                Outcome::Unknown(Unknown::Deadline) => break None,
                o => break Some(o),
            }
        };
        let stats = q.stats();
        cost.simplify = stats.simplification.spent;
        cost.add(&Cost {
            simplify: before_build,
            ..Cost::default()
        });
        cost.conflicts = stats.conflicts;
        cost.propagations = stats.propagations;
        cost.decisions = stats.decisions;
        cost.circuit_nodes = stats.nodes as u64;
        cost.samples = stats.samples;
        Ok(Solved {
            job,
            res: outcome.map(SolvedRes::Outcome),
            cx,
            cost,
        })
    }
}

/// What the tasks below `j` spent, finished or stopped, each once.
fn spent_below(graph: &Graph, j: usize) -> Cost {
    let mut total = Cost::default();
    let mut jobs: HashSet<usize> = HashSet::new();
    let mut entries: HashSet<u64> = HashSet::new();
    let mut stack = vec![j];
    while let Some(j) = stack.pop() {
        if !jobs.insert(j) {
            continue;
        }
        let job = &graph.jobs[j];
        match &job.state {
            State::Done(e) => {
                let mut es = vec![e];
                while let Some(e) = es.pop() {
                    if entries.insert(e.id) {
                        total.add(&e.own);
                        es.extend(e.parts.iter());
                    }
                }
            }
            _ => {
                total.add(&job.partial);
                stack.extend(job.deps.iter().copied());
            }
        }
    }
    total
}
