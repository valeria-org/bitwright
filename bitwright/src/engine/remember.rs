//! Simplification results remembered across contexts and runs.

use std::collections::HashMap;

use super::{Engine, Outcome, Run};
use crate::error::Error;
use crate::expr::{Context, Expr};
use crate::hash::IdMap;
use crate::text::{ParseOptions, PrintOptions};
use crate::{BitVec, FnEnv, SymbolKey, Width};

/// What an [`Engine`] found expressions equal to, kept outside any context: the next time
/// one of them is what is simplified, or a part of it that the engine had taken down to a
/// few nodes (in this context or another, in this process or a later one), it is replaced by what it was found equal to before the engine starts, so
/// the work that found it is not done again. In a deobfuscator's questions most
/// subexpressions come back, a few nodes around them changed; this is what makes the second
/// question about a piece of code cost what is new in it.
///
/// An entry is an equality the engine established, for every value of the symbols: it is
/// kept by the expression's [structural hash](Context::structural_hash), which is of the
/// expression alone, and a hit is checked before use (the shape, the width, and the values
/// of both sides at a few points), so a hash that is not the expression's does no harm.
/// Results are of an engine: a store filled by one is not read by another. It keeps nothing
/// from runs under [assumptions](Run::assumptions) or [hooks](Run::hooks).
///
/// The store is a value: the host keeps it, shares it and writes it where it likes
/// ([`to_text`](Self::to_text), [`from_text`](Self::from_text)); bitwright does no IO.
///
/// ```
/// use bitwright::engine::{Engine, Remembered, Run};
/// use bitwright::{Context, ParseOptions, Width};
///
/// let engine = Engine::standard();
/// let o = ParseOptions::width(Width::W64);
/// let mut memory = Remembered::new();
/// let src = "((x & y) + (x | y)) * 3 + ((x ^ 0x5a) + 7 - 7 ^ 0x5a)";
/// let mut cx = Context::new();
/// let e = cx.parse(src, &o)?;
/// let first = engine.run_remembering(&mut cx, &[e], Run::default(), &mut memory)?;
/// assert!(first.stats.rewrites > 0);
///
/// // Later, elsewhere: the store as text, read back, and the expression inside another.
/// let mut memory = Remembered::from_text(&memory.to_text())?;
/// let mut cx = Context::new();
/// let again = cx.parse(&format!("({src}) ^ z"), &o)?;
/// let second = engine.run_remembering(&mut cx, &[again], Run::default(), &mut memory)?;
/// assert_eq!(cx.display(second.roots[0].expr).to_string(), "(x + y) * 3 + x ^ z");
/// assert_eq!((memory.hits(), second.stats.rewrites), (1, 0));
/// # Ok::<(), bitwright::Error>(())
/// ```
#[derive(Clone, Debug)]
pub struct Remembered {
    /// The engine the entries are of, once one is.
    engine: Option<u128>,
    entries: HashMap<u64, Entry>,
    /// When each entry was last learned or found, by a count of those events: the entries
    /// used longest ago make room when the store is full.
    used: HashMap<u64, u64>,
    clock: u64,
    min_tree: u32,
    max_entries: usize,
    per_run: usize,
    settled_tree: u32,
    hits: u64,
    /// By shape: how often a question of the opaque-constant sweep about an expression of
    /// the shape was proved, and how often it was not.
    asked: std::sync::Arc<HashMap<u64, (u32, u32)>>,
    skip_after: u32,
}

/// What a run in progress reads of a store and reports back to it, carried by the context
/// (the engine's passes have it at hand): the shapes whose questions have only failed, and
/// the outcomes of the questions this run asked.
#[derive(Clone, Debug, Default)]
#[cfg_attr(not(feature = "mba"), allow(dead_code))]
pub(crate) struct SweepNotes {
    asked: Option<std::sync::Arc<HashMap<u64, (u32, u32)>>>,
    skip_after: u32,
    log: Vec<(u64, bool)>,
}

#[cfg_attr(not(feature = "mba"), allow(dead_code))]
impl SweepNotes {
    /// Whether a run under a store is in progress (shapes are worth computing).
    pub(crate) fn wanted(&self) -> bool {
        self.asked.is_some()
    }

    /// Whether questions about `shape` have failed often enough, and never succeeded.
    pub(crate) fn fruitless(&self, shape: u64) -> bool {
        (self.asked.as_ref().and_then(|m| m.get(&shape)))
            .is_some_and(|&(proved, failed)| proved == 0 && failed >= self.skip_after)
    }

    /// A question about `shape` was asked: whether it was proved.
    pub(crate) fn note(&mut self, shape: u64, proved: bool) {
        self.log.push((shape, proved));
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Entry {
    shape: u64,
    width: u16,
    /// The result, in the text syntax with symbol widths.
    text: Box<str>,
}

impl Default for Remembered {
    fn default() -> Self {
        Remembered {
            engine: None,
            entries: HashMap::new(),
            used: HashMap::new(),
            clock: 0,
            min_tree: 8,
            max_entries: 1 << 20,
            per_run: 64,
            settled_tree: 3,
            hits: 0,
            asked: Default::default(),
            skip_after: u32::MAX,
        }
    }
}

/// The points both sides of a hit are compared at.
const CHECKS: u64 = 4;

impl Remembered {
    /// An empty store: expressions of at least 8 nodes (as a tree), up to 64 of each run,
    /// a million in all.
    pub fn new() -> Self {
        Self::default()
    }

    /// The smallest expression (in nodes, as a tree) worth remembering.
    #[must_use]
    pub fn with_min_tree(mut self, nodes: u32) -> Self {
        self.min_tree = nodes.max(2);
        self
    }

    /// The most entries the store holds; when full, the eighth of them learned or found
    /// longest ago makes room (an order that starts again when a store is read from text).
    #[must_use]
    pub fn with_max_entries(mut self, entries: usize) -> Self {
        self.max_entries = entries;
        self
    }

    /// The largest result (in nodes, as a tree) a subexpression is remembered with: by
    /// default 3, a constant, a symbol or one operation on them. A root is remembered
    /// whatever it became.
    #[must_use]
    pub fn with_settled_tree(mut self, nodes: u32) -> Self {
        self.settled_tree = nodes;
        self
    }

    /// After how many failures (and no success) the questions of the opaque-constant sweep
    /// about expressions of one shape are not asked again; never, by default. The sweep asks
    /// of every node that looks constant at its samples whether it is, and most of its time
    /// goes to the ones that are not: a shape that failed in `n` questions, whatever its
    /// constants, is likely to fail in the next. Unlike everything else a store does, this
    /// can lose a simplification (a constant that only some values of a shape's constants
    /// make): the price of the time it saves, for the host to weigh.
    #[must_use]
    pub fn with_skip_after(mut self, failures: u32) -> Self {
        self.skip_after = failures.max(1);
        self
    }

    /// The most subexpressions one run adds besides its roots (the largest are taken).
    #[must_use]
    pub fn with_per_run(mut self, entries: usize) -> Self {
        self.per_run = entries;
        self
    }

    /// The number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the store is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Subexpressions replaced from the store so far.
    pub fn hits(&self) -> u64 {
        self.hits
    }

    /// The store as text: a header naming the versions the entries are of, then the entries.
    pub fn to_text(&self) -> String {
        use core::fmt::Write;
        let mut out = format!(
            "bitwright-remembered 1 hash {} crate {} engine {:032x}\n",
            crate::HASH_VERSION,
            env!("CARGO_PKG_VERSION"),
            self.engine.unwrap_or(0),
        );
        // In hash order: the same store is the same text.
        let mut keys: Vec<&u64> = self.entries.keys().collect();
        keys.sort();
        for k in keys {
            let e = &self.entries[k];
            let _ = write!(
                out,
                "{k:016x} {:016x} {}\n{}\n%%\n",
                e.shape, e.width, e.text
            );
        }
        let mut shapes: Vec<(&u64, &(u32, u32))> = self.asked.iter().collect();
        shapes.sort();
        for (shape, (proved, failed)) in shapes {
            let _ = writeln!(out, "asked {shape:016x} {proved} {failed}");
        }
        out
    }

    /// A store from [`to_text`](Self::to_text). One written under another hash or crate
    /// version reads as an empty store (its entries would never be found, or be of another
    /// engine's code); text that is not a store is an error.
    pub fn from_text(text: &str) -> Result<Self, Error> {
        let bad = |what: &str| Error::Unsupported(format!("not a store of results: {what}"));
        let mut lines = text.lines();
        let header: Vec<&str> = lines.next().unwrap_or_default().split(' ').collect();
        let &[
            "bitwright-remembered",
            "1",
            "hash",
            hash,
            "crate",
            version,
            "engine",
            engine,
        ] = header.as_slice()
        else {
            return Err(bad("the header"));
        };
        let mut store = Remembered::new();
        if hash.parse() != Ok(crate::HASH_VERSION) || version != env!("CARGO_PKG_VERSION") {
            return Ok(store);
        }
        let engine = u128::from_str_radix(engine, 16).map_err(|_| bad("the engine"))?;
        store.engine = (engine != 0).then_some(engine);
        let mut asked = HashMap::new();
        while let Some(head) = lines.next() {
            let fields: Vec<&str> = head.split(' ').collect();
            if let &["asked", shape, proved, failed] = fields.as_slice() {
                let n = |s: &str| s.parse::<u32>().map_err(|_| bad("a count"));
                let shape = u64::from_str_radix(shape, 16).map_err(|_| bad("a shape"))?;
                asked.insert(shape, (n(proved)?, n(failed)?));
                continue;
            }
            let &[key, shape, width] = fields.as_slice() else {
                return Err(bad("an entry's first line"));
            };
            let mut body = String::new();
            loop {
                match lines.next() {
                    Some("%%") => break,
                    Some(l) => {
                        if !body.is_empty() {
                            body.push('\n');
                        }
                        body.push_str(l);
                    }
                    None => return Err(bad("an entry without its end")),
                }
            }
            let entry = Entry {
                shape: u64::from_str_radix(shape, 16).map_err(|_| bad("a shape"))?,
                width: width.parse().map_err(|_| bad("a width"))?,
                text: body.into_boxed_str(),
            };
            let key = u64::from_str_radix(key, 16).map_err(|_| bad("a hash"))?;
            store.entries.insert(key, entry);
        }
        store.asked = std::sync::Arc::new(asked);
        Ok(store)
    }
}

impl Engine {
    /// [`run`](Self::run), with a memory: subexpressions `memory` holds results for are
    /// replaced by them first, and what this run finds is added to it. The outcome answers
    /// the roots as given. Under assumptions or hooks, or with a store of another engine,
    /// it is `run` and the store is left alone.
    pub fn run_remembering(
        &self,
        cx: &mut Context,
        roots: &[Expr],
        run: Run<'_>,
        memory: &mut Remembered,
    ) -> Result<Outcome, Error> {
        let id = self.inner.id;
        if run.assumptions.is_some()
            || run.hooks.is_some()
            || memory.engine.is_some_and(|e| e != id)
        {
            return self.run(cx, roots, run);
        }
        memory.engine = Some(id);
        cx.sweep = SweepNotes {
            asked: Some(memory.asked.clone()),
            skip_after: memory.skip_after,
            log: Vec::new(),
        };
        // What is remembered of the roots' subexpressions, outermost first: below a hit
        // nothing is looked up.
        let ids = cx.ids(roots)?;
        let mut replace: Vec<(Expr, Expr)> = Vec::new();
        if !memory.entries.is_empty() {
            let mut seen: IdMap<u32, ()> = IdMap::default();
            let mut stack = ids.clone();
            while let Some(n) = stack.pop() {
                if seen.insert(n, ()).is_some() || cx.meta[n as usize].tree < memory.min_tree {
                    continue;
                }
                if let Some(to) = memory.recall(cx, n)? {
                    replace.push((cx.handle(n), to));
                    continue;
                }
                stack.extend(cx.node(n).children());
            }
        }
        memory.hits += replace.len() as u64;
        let start = if replace.is_empty() {
            roots.to_vec()
        } else {
            cx.substitute(roots, &replace)?
        };
        let ran = self.run(cx, &start, run);
        // The outcomes of the sweep's questions, by shape (the run's notes are dropped
        // first, so that the map is the store's alone again and changes in place).
        let notes = core::mem::take(&mut cx.sweep);
        drop(notes.asked);
        let asked = std::sync::Arc::make_mut(&mut memory.asked);
        for (shape, proved) in notes.log {
            let e = asked.entry(shape).or_default();
            if proved {
                e.0 = e.0.saturating_add(1);
            } else {
                e.1 = e.1.saturating_add(1);
            }
        }
        let mut out = ran?;
        for ((o, &given), &from) in out.roots.iter_mut().zip(roots).zip(&start) {
            o.changed = o.expr != given;
            let _ = from;
        }
        // What to remember: each root as given, and the largest subexpressions the run's
        // phases took somewhere smaller.
        let mut learned: Vec<(u32, u32)> = (ids.iter().zip(&out.roots))
            .map(|(&n, o)| Ok((n, cx.id(o.expr)?)))
            .collect::<Result<_, Error>>()?;
        let mut inner: Vec<(u32, u32)> = Vec::new();
        for n in cx.post_order_ids(&cx.ids(&start)?) {
            if cx.meta[n as usize].tree < memory.min_tree {
                continue;
            }
            // Through the phases in order: each took the node somewhere, or left it.
            let mut r = n;
            for phase in &cx.memo.phases {
                if let Some((to, rel)) = phase.get(r)
                    && rel.is_none()
                {
                    r = to;
                }
            }
            // Only what a phase took all the way down to a few nodes (a constant, a symbol,
            // one operation): replacing a subexpression by a half-simplified one changes
            // what the engine starts from, and where it ends up is then not always as small.
            if r != n && cx.meta[r as usize].tree <= memory.settled_tree {
                inner.push((n, r));
            }
        }
        inner.sort_by_key(|&(n, _)| core::cmp::Reverse(cx.meta[n as usize].tree));
        inner.truncate(memory.per_run);
        learned.extend(inner);
        for (n, r) in learned {
            memory.learn(cx, n, r)?;
        }
        Ok(out)
    }
}

impl Remembered {
    /// What is remembered of node `n`, built in `cx` and checked, if anything.
    fn recall(&mut self, cx: &mut Context, n: u32) -> Result<Option<Expr>, Error> {
        let key = cx.meta[n as usize].shash;
        let Some(entry) = self.entries.get(&key) else {
            return Ok(None);
        };
        let w = cx.width_of(n);
        let from = cx.handle(n);
        if entry.width != w.bits() || cx.shape_hashes(&[from])?[0] != entry.shape {
            return Ok(None);
        }
        // The text names its symbols' widths; a symbol this context has at another width
        // (or anything else that does not read) is no hit.
        let Ok(to) = cx.parse(&entry.text, &ParseOptions::width(w)) else {
            return Ok(None);
        };
        if cx.width(to)? != w {
            return Ok(None);
        }
        for k in 0..CHECKS {
            let env = FnEnv(|key: &SymbolKey, width: Width| {
                let h = key.structural_hash() ^ k.wrapping_mul(0x9e37_79b9_7f4a_7c15);
                let h = crate::hash::mix64(h);
                let pick = [0, !0, h, h.rotate_left(29)];
                Some(BitVec::wrapping_from_limbs(
                    width,
                    &[pick[(k % 4) as usize], h.rotate_left(17), h, !h],
                ))
            });
            // (An expression that cannot be evaluated, an extension without a value, is
            // taken on its hash and shape.)
            if let Ok(v) = cx.eval(&[from, to], &env)
                && v[0] != v[1]
            {
                return Ok(None);
            }
        }
        self.clock += 1;
        self.used.insert(key, self.clock);
        Ok(Some(to))
    }

    /// Remembers that node `n` is `r`, when it is worth it and there is room.
    fn learn(&mut self, cx: &mut Context, n: u32, r: u32) -> Result<(), Error> {
        let key = cx.meta[n as usize].shash;
        if n == r
            || cx.meta[n as usize].tree < self.min_tree
            || self.max_entries == 0
            || self.entries.contains_key(&key)
        {
            return Ok(());
        }
        let opts = PrintOptions::default()
            .with_symbol_widths(true)
            .with_max_nodes(100_000)
            .with_max_chars(1 << 22);
        let text = cx.display_with(cx.handle(r), opts).to_string();
        // A result too large to print whole is not kept.
        if text.ends_with('…') || text.contains("\n%%\n") {
            return Ok(());
        }
        let entry = Entry {
            shape: cx.shape_hashes(&[cx.handle(n)])?[0],
            width: cx.width_of(n).bits(),
            text: text.into_boxed_str(),
        };
        if self.entries.len() >= self.max_entries {
            self.make_room();
        }
        self.entries.insert(key, entry);
        self.clock += 1;
        self.used.insert(key, self.clock);
        Ok(())
    }

    /// Drops the eighth of the entries (one at least) learned or found longest ago.
    fn make_room(&mut self) {
        let mut ages: Vec<(u64, u64)> = (self.entries.keys())
            .map(|k| (self.used.get(k).copied().unwrap_or(0), *k))
            .collect();
        ages.sort_unstable();
        for &(_, k) in ages.iter().take((self.max_entries / 8).max(1)) {
            self.entries.remove(&k);
            self.used.remove(&k);
        }
    }

    /// Adds what `other` holds and this store does not (stores of two runs, or of two
    /// hosts, as one), while there is room; the counts of the sweep's questions add up.
    /// `false`, and nothing is added, when the two are of different engines.
    pub fn merge(&mut self, other: &Remembered) -> bool {
        match (self.engine, other.engine) {
            (Some(a), Some(b)) if a != b => return false,
            (None, b) => self.engine = b,
            _ => {}
        }
        for (k, e) in &other.entries {
            if self.entries.len() >= self.max_entries {
                break;
            }
            self.entries.entry(*k).or_insert_with(|| e.clone());
        }
        let asked = std::sync::Arc::make_mut(&mut self.asked);
        for (shape, (proved, failed)) in other.asked.iter() {
            let e = asked.entry(*shape).or_default();
            e.0 = e.0.saturating_add(*proved);
            e.1 = e.1.saturating_add(*failed);
        }
        true
    }
}
