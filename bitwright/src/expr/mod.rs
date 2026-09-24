//! The hash-consed expression arena.
//!
//! A [`Context`] owns every node it creates. Nodes are immutable and appended in creation
//! order, and every child index is lower than its parent's, so ascending index order is a
//! topological order. Structurally equal expressions are the same node ("equal handle implies
//! equal value"; the converse does not hold). Every node is in canonical form (see
//! `build.rs` and `docs/design.md` §4.3).

mod build;
pub(crate) use build::count_mod;
pub use build::traps;
mod eval;
mod node;
mod symbols;
#[cfg(test)]
mod tests;

use core::cmp::Ordering;
use core::fmt;
use core::num::NonZeroU32;
use std::sync::atomic::{AtomicU32, Ordering as AtomicOrdering};

use hashbrown::HashTable;

use crate::error::Error;
use crate::hash::{IdMap, combine};
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::value::wide::nlimbs;
use crate::{BitVec, Width};

pub use eval::{Env, FnEnv, Substitution};
pub(crate) use node::{AUX_POOLED, Node, OpCode};
pub(crate) use symbols::{SymEntry, SymbolTable};
pub use symbols::{SymbolId, SymbolKey};

/// A handle to an expression node.
///
/// A handle is valid only in the context, and the context generation, that created it. Using it
/// anywhere else is detected (best effort) and reported as [`Error::ForeignExpr`] or
/// [`Error::StaleExpr`]; it never silently refers to another node.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    index: u32,
    tag: NonZeroU32,
}

impl Expr {
    /// The node's index. Indices are dense from 0 in creation order, and children always have
    /// lower indices than their parents. Useful as a key for caller-side dense tables.
    #[inline]
    pub fn index(self) -> u32 {
        self.index
    }

    /// The handle as one integer, never 0, for hosts that keep handles outside Rust (the C and
    /// Python bindings). [`Expr::from_bits`] reads it back.
    #[inline]
    pub fn to_bits(self) -> u64 {
        u64::from(self.tag.get()) << 32 | u64::from(self.index)
    }

    /// The handle [`Expr::to_bits`] gave, or `None` for 0. Any other integer reads as a handle:
    /// a context rejects one it did not create ([`Error::ForeignExpr`] or
    /// [`Error::StaleExpr`]), like any other foreign handle.
    #[inline]
    pub fn from_bits(bits: u64) -> Option<Expr> {
        Some(Expr {
            index: bits as u32,
            tag: NonZeroU32::new((bits >> 32) as u32)?,
        })
    }
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "e{}", self.index)
    }
}

/// Configuration of a [`Context`].
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ContextConfig {
    /// The maximum number of nodes. Building past it fails with [`Error::ArenaFull`].
    pub max_nodes: u32,
    /// Seed for the interning table's layout. It never changes any result.
    pub hash_seed: u64,
    /// The most transfer functions one fact query may run before answering `top`.
    pub fact_work: u32,
}

impl Default for ContextConfig {
    fn default() -> Self {
        ContextConfig {
            max_nodes: 1 << 24,
            hash_seed: 0,
            fact_work: 1 << 20,
        }
    }
}

impl ContextConfig {
    /// Sets [`max_nodes`](Self::max_nodes).
    pub fn with_max_nodes(mut self, n: u32) -> Self {
        self.max_nodes = n;
        self
    }

    /// Sets [`fact_work`](Self::fact_work).
    pub fn with_fact_work(mut self, n: u32) -> Self {
        self.fact_work = n;
        self
    }

    /// Sets [`hash_seed`](Self::hash_seed).
    pub fn with_hash_seed(mut self, seed: u64) -> Self {
        self.hash_seed = seed;
        self
    }
}

/// Nodes created by the caller's own builder calls versus nodes created by bitwright itself
/// (simplification, search). Lets a host retry maintenance only after enough *input* growth.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct ArenaCounters {
    /// New nodes created through the public builder.
    pub caller_nodes: u64,
    /// New nodes created by the library's own transformations.
    pub engine_nodes: u64,
}

/// A position in the caller-growth counter; see [`Context::caller_growth_since`].
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Mark {
    tag: NonZeroU32,
    caller_nodes: u64,
}

/// A size that may have been cut off at a bound.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Bounded {
    /// The exact value.
    Exact(u32),
    /// The walk stopped at the bound; the value is at least this.
    AtLeast(u32),
}

/// A read-only view of one node.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
#[non_exhaustive]
pub enum View {
    /// A constant.
    Const(BitVec),
    /// A symbol.
    Sym(SymbolId),
    /// A unary operator.
    Un(UnOp, Expr),
    /// A binary operator.
    Bin(BinOp, Expr, Expr),
    /// A comparison (1-bit result).
    Cmp(CmpOp, Expr, Expr),
    /// Zero extension to the node's width.
    Zext(Expr),
    /// Sign extension to the node's width.
    Sext(Expr),
    /// Bits `[lo, lo + W)` of `src`, where `W` is the node's width.
    Extract {
        /// First extracted bit.
        lo: u16,
        /// The operand.
        src: Expr,
    },
    /// `hi` in the high bits and `lo` in the low bits.
    Concat {
        /// The high part.
        hi: Expr,
        /// The low part.
        lo: Expr,
    },
    /// `cond ? then : els` with a 1-bit condition.
    Select {
        /// The condition.
        cond: Expr,
        /// The value when the condition is 1.
        then: Expr,
        /// The value when the condition is 0.
        els: Expr,
    },
    /// Output `output` of an extension call (see [`ext`](crate::ext)).
    Ext {
        /// The operation, in the context's registry.
        op: crate::ext::ExtId,
        /// Which output.
        output: u8,
        /// The arguments.
        args: crate::ext::ExtArgs,
    },
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct Meta {
    pub(crate) shash: u64,
    pub(crate) height: u32,
    pub(crate) tree: u32,
}

/// Generation-stamped marks, reused across traversals without clearing.
#[derive(Clone, Debug, Default)]
pub(crate) struct Marks {
    stamp: Vec<u32>,
    cur: u32,
}

impl Marks {
    pub(crate) fn begin(&mut self, len: usize) {
        if self.stamp.len() < len {
            self.stamp.resize(len, 0);
        }
        self.cur = self.cur.wrapping_add(1);
        if self.cur == 0 {
            self.stamp.fill(0);
            self.cur = 1;
        }
    }

    /// Marks `i`; returns whether it was already marked.
    #[inline]
    pub(crate) fn test_and_set(&mut self, i: u32) -> bool {
        let s = &mut self.stamp[i as usize];
        let was = *s == self.cur;
        *s = self.cur;
        was
    }
}

/// The only process-wide state in bitwright: a counter that gives every context generation
/// (each new context, and each `clear()`) a distinct handle tag. Tags repeat only after 2^32
/// generations have been created in the process. It never influences any result or output.
static TAGS: AtomicU32 = AtomicU32::new(0);

fn fresh_tag() -> NonZeroU32 {
    loop {
        let t = TAGS.fetch_add(1, AtomicOrdering::Relaxed).wrapping_add(1);
        if let Some(nz) = NonZeroU32::new(t) {
            return nz;
        }
    }
}

/// How many earlier tags of a context are remembered to report `StaleExpr` (older ones are
/// reported as `ForeignExpr`; both are rejected).
const RETIRED: usize = 8;

/// A hash-consed expression arena.
///
/// A context owns every node it creates. Nodes are immutable and appended in creation order,
/// and every child index is lower than its parent's, so ascending index order is a topological
/// order. Structurally equal expressions are the same node ("equal handle implies equal
/// value"; the converse does not hold). Every node is in canonical form: constants are folded,
/// commutative operands are ordered (constants last) independently of construction order, and
/// a fixed set of O(1) identities and cast collapses is applied (see `docs/design.md` §4.3).
///
/// ```
/// use bitwright::{Context, Width};
/// let mut cx = Context::new();
/// let x = cx.symbol("x", Width::W32)?;
/// let one = cx.one(Width::W32)?;
/// let a = cx.add(one, x)?;
/// let b = cx.add(x, one)?;
/// assert_eq!(a, b);
/// let z = cx.xor(a, b)?;
/// assert_eq!(cx.as_const(z)?.map(|v| v.is_zero()), Some(true));
/// # Ok::<(), bitwright::Error>(())
/// ```
pub struct Context {
    pub(crate) nodes: Vec<Node>,
    pub(crate) meta: Vec<Meta>,
    interner: HashTable<u32>,
    pub(crate) wide_consts: Vec<u64>,
    pub(crate) symbols: SymbolTable,
    config: ContextConfig,
    generation: u32,
    tag: NonZeroU32,
    retired: [u32; RETIRED],
    counters: ArenaCounters,
    engine_mode: bool,
    /// Nodes the engine may still create in engine mode (its call's remaining `new_nodes`
    /// budget), if limited; see [`Context::as_engine_limited`].
    engine_allowance: Option<u64>,
    /// Set when the engine allowance refused a node.
    engine_refused: bool,
    pub(crate) marks: Marks,
    dag_cache: IdMap<u32, u32>,
    pub(crate) facts: crate::facts::FactCache,
    pub(crate) memo: crate::engine::Memo,
    #[cfg(feature = "eqsat")]
    pub(crate) eqsat_memo: crate::eqsat::Memo,
    /// The extension operations this context can build.
    pub(crate) registry: Option<std::sync::Arc<crate::ext::Registry>>,
}

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Context")
            .field("nodes", &self.nodes.len())
            .field("symbols", &self.symbols.entries.len())
            .field("generation", &self.generation)
            .finish_non_exhaustive()
    }
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    /// An empty context with the default configuration. Allocates nothing until the first node.
    pub fn new() -> Self {
        Self::with_config(ContextConfig::default())
    }

    /// An empty context.
    pub fn with_config(config: ContextConfig) -> Self {
        Context {
            nodes: Vec::new(),
            meta: Vec::new(),
            interner: HashTable::new(),
            wide_consts: Vec::new(),
            symbols: SymbolTable::default(),
            config,
            generation: 0,
            tag: fresh_tag(),
            retired: [0; RETIRED],
            counters: ArenaCounters::default(),
            engine_mode: false,
            engine_allowance: None,
            engine_refused: false,
            marks: Marks::default(),
            dag_cache: IdMap::default(),
            facts: crate::facts::FactCache::default(),
            memo: crate::engine::Memo::default(),
            #[cfg(feature = "eqsat")]
            eqsat_memo: crate::eqsat::Memo::default(),
            registry: None,
        }
    }

    /// An empty context that can build the extension operations of `registry`.
    pub fn with_registry(
        config: ContextConfig,
        registry: std::sync::Arc<crate::ext::Registry>,
    ) -> Self {
        let mut cx = Self::with_config(config);
        cx.registry = Some(registry);
        cx
    }

    /// The extension operations this context can build.
    pub fn registry(&self) -> Option<&crate::ext::Registry> {
        self.registry.as_deref()
    }

    /// Replaces the registry by one that extends it: every operation of the current registry is
    /// at the same position in `registry` (same name, revision and traits), so every existing
    /// node keeps its meaning and canonical form. Otherwise an error, and nothing changes.
    pub fn extend_registry(
        &mut self,
        registry: std::sync::Arc<crate::ext::Registry>,
    ) -> Result<(), Error> {
        if let Some(old) = self.registry.as_deref() {
            // Same operation (name, revision) with the same traits: the traits decide canonical
            // forms (argument order) that existing nodes were built in.
            let kept = old.ids().all(|id| {
                registry.op(id).is_some_and(|o| {
                    old.op(id).is_some_and(|p| {
                        p.name() == o.name()
                            && p.revision() == o.revision()
                            && p.traits() == o.traits()
                    })
                })
            });
            if !kept {
                return Err(Error::Unsupported(
                    "the new registry does not extend the current one".into(),
                ));
            }
        }
        self.registry = Some(registry);
        Ok(())
    }

    /// The configuration.
    pub fn config(&self) -> &ContextConfig {
        &self.config
    }

    /// Changes the node limit ([`ContextConfig::max_nodes`]). Existing nodes stay; a limit
    /// below the current size only stops new nodes from being created (lookups of existing
    /// structure still succeed).
    pub fn set_max_nodes(&mut self, n: u32) {
        self.config.max_nodes = n;
    }

    /// The number of nodes.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the context has no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Removes every node and symbol, keeping allocations. Handles created before the call
    /// become stale and are rejected with [`Error::StaleExpr`].
    pub fn clear(&mut self) {
        self.nodes.clear();
        self.meta.clear();
        self.interner.clear();
        self.wide_consts.clear();
        self.symbols.clear();
        self.dag_cache.clear();
        self.facts.clear();
        self.memo.clear();
        #[cfg(feature = "eqsat")]
        self.eqsat_memo.clear();
        self.counters = ArenaCounters::default();
        self.generation = self.generation.wrapping_add(1);
        self.retired.rotate_right(1);
        self.retired[0] = self.tag.get();
        self.tag = fresh_tag();
    }

    /// Node creation counters.
    pub fn counters(&self) -> ArenaCounters {
        self.counters
    }

    /// The current position of the caller-growth counter.
    pub fn mark(&self) -> Mark {
        Mark {
            tag: self.tag,
            caller_nodes: self.counters.caller_nodes,
        }
    }

    /// New nodes created by the caller since `mark` (all of them, if the mark is from another
    /// context or from before a `clear()`). Nodes created by the library itself are not counted.
    pub fn caller_growth_since(&self, mark: Mark) -> u64 {
        if mark.tag != self.tag {
            return self.counters.caller_nodes;
        }
        self.counters.caller_nodes.saturating_sub(mark.caller_nodes)
    }

    // ----- handles --------------------------------------------------------------------------

    /// Validates a handle and returns its node index.
    #[inline]
    pub(crate) fn id(&self, e: Expr) -> Result<u32, Error> {
        if e.tag == self.tag && (e.index as usize) < self.nodes.len() {
            return Ok(e.index);
        }
        if self.retired.contains(&e.tag.get()) {
            Err(Error::StaleExpr)
        } else {
            Err(Error::ForeignExpr)
        }
    }

    #[inline]
    pub(crate) fn handle(&self, index: u32) -> Expr {
        Expr {
            index,
            tag: self.tag,
        }
    }

    pub(crate) fn ids(&self, es: &[Expr]) -> Result<Vec<u32>, Error> {
        es.iter().map(|&e| self.id(e)).collect()
    }

    // ----- raw node access ------------------------------------------------------------------

    #[inline]
    pub(crate) fn node(&self, i: u32) -> Node {
        self.nodes[i as usize]
    }

    #[inline]
    pub(crate) fn wid(&self, i: u32) -> u16 {
        self.nodes[i as usize].width
    }

    #[inline]
    pub(crate) fn width_of(&self, i: u32) -> Width {
        // Every stored width was validated at construction.
        Width::new(self.nodes[i as usize].width).unwrap_or(Width::W1)
    }

    /// The value of a constant node.
    pub(crate) fn const_val(&self, i: u32) -> Option<BitVec> {
        let n = self.nodes[i as usize];
        if n.op != OpCode::Const {
            return None;
        }
        let width = Width::new(n.width).ok()?;
        if n.aux & AUX_POOLED != 0 {
            let len = nlimbs(n.width);
            let off = n.a as usize;
            Some(BitVec::wrapping_from_limbs(
                width,
                &self.wide_consts[off..off + len],
            ))
        } else {
            Some(BitVec::wrapping_from_u64(
                width,
                u64::from(n.a) | (u64::from(n.b) << 32),
            ))
        }
    }

    // ----- interning ------------------------------------------------------------------------

    fn table_hash(&self, shash: u64) -> u64 {
        combine(self.config.hash_seed, shash)
    }

    /// The structural hash of a (non-constant, non-symbol) node from its children's hashes.
    fn structural_hash(&self, n: &Node) -> u64 {
        let mut h = combine(u64::from(n.op as u8), u64::from(n.width));
        if n.op.as_ext().is_some() {
            // The operation by name and revision, not by registry position.
            let op = self.registry.as_deref().map_or(0, |r| r.hash_at(n.aux));
            h = combine(h, op);
        }
        match n.op {
            OpCode::Extract => {
                h = combine(h, u64::from(n.b));
                h = combine(h, self.meta[n.a as usize].shash);
            }
            _ => {
                for c in n.children() {
                    h = combine(h, self.meta[c as usize].shash);
                }
            }
        }
        h
    }

    fn const_hash(v: &BitVec) -> u64 {
        let mut h = combine(u64::from(OpCode::Const as u8), u64::from(v.width().bits()));
        for &l in v.limbs() {
            h = combine(h, l);
        }
        h
    }

    /// Appends a node that the caller has checked is not already interned.
    fn push(&mut self, n: Node, shash: u64) -> Result<u32, Error> {
        self.room()?;
        let idx = self.nodes.len() as u32;
        let (mut height, mut tree) = (0u32, 1u32);
        for c in n.children() {
            let m = self.meta[c as usize];
            height = height.max(m.height);
            tree = tree.saturating_add(m.tree);
        }
        let height = if n.op.arity() == 0 {
            0
        } else {
            height.saturating_add(1)
        };
        self.nodes.push(n);
        self.meta.push(Meta {
            shash,
            height,
            tree,
        });
        let seed = self.config.hash_seed;
        let meta = &self.meta;
        self.interner
            .insert_unique(combine(seed, shash), idx, |&i| {
                combine(seed, meta[i as usize].shash)
            });
        if self.engine_mode {
            self.counters.engine_nodes += 1;
            if let Some(a) = &mut self.engine_allowance {
                *a -= 1;
            }
        } else {
            self.counters.caller_nodes += 1;
        }
        Ok(idx)
    }

    /// Interns a canonical non-constant, non-symbol node.
    pub(crate) fn mk(&mut self, n: Node) -> Result<u32, Error> {
        let shash = self.structural_hash(&n);
        let nodes = &self.nodes;
        if let Some(&i) = self
            .interner
            .find(self.table_hash(shash), |&i| nodes[i as usize] == n)
        {
            return Ok(i);
        }
        self.push(n, shash)
    }

    /// Interns a constant.
    pub(crate) fn mk_const(&mut self, v: &BitVec) -> Result<u32, Error> {
        let w = v.width().bits();
        let shash = Self::const_hash(v);
        let (nodes, wide) = (&self.nodes, &self.wide_consts);
        let limbs = v.limbs();
        let inline = w <= 64;
        let lo = limbs[0];
        let found = self.interner.find(self.table_hash(shash), |&i| {
            let n = &nodes[i as usize];
            n.op == OpCode::Const
                && n.width == w
                && if inline {
                    u64::from(n.a) | (u64::from(n.b) << 32) == lo
                } else {
                    let off = n.a as usize;
                    wide[off..off + limbs.len()] == *limbs
                }
        });
        if let Some(&i) = found {
            return Ok(i);
        }
        self.room()?;
        let node = if inline {
            Node::new(OpCode::Const, w, lo as u32, (lo >> 32) as u32, 0)
        } else {
            let off = self.wide_consts.len() as u32;
            self.wide_consts.extend_from_slice(limbs);
            let mut n = Node::new(OpCode::Const, w, off, 0, 0);
            n.aux = AUX_POOLED;
            n
        };
        self.push(node, shash)
    }

    /// Whether one more node may be created: the arena's `max_nodes`, and in engine mode the
    /// engine's node allowance (refusing marks `engine_refused`).
    fn room(&mut self) -> Result<(), Error> {
        let limit = self.config.max_nodes;
        if self.nodes.len() >= limit as usize {
            return Err(Error::ArenaFull { limit });
        }
        if self.engine_mode && self.engine_allowance == Some(0) {
            self.engine_refused = true;
            return Err(Error::ArenaFull { limit });
        }
        Ok(())
    }

    /// Runs `f` in engine mode, creating at most `allowance` new nodes: a node past it is
    /// refused (as a full arena) before it is created. Returns whether one was refused.
    pub(crate) fn as_engine_limited<T>(
        &mut self,
        allowance: u64,
        f: impl FnOnce(&mut Self) -> T,
    ) -> (T, bool) {
        let prev = (
            self.engine_allowance.replace(allowance),
            core::mem::replace(&mut self.engine_refused, false),
        );
        let r = self.as_engine(f);
        let refused = self.engine_refused;
        (self.engine_allowance, self.engine_refused) = prev;
        (r, refused)
    }

    /// Runs `f` with new nodes counted as engine nodes.
    pub(crate) fn as_engine<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let prev = core::mem::replace(&mut self.engine_mode, true);
        let r = f(self);
        self.engine_mode = prev;
        r
    }

    // ----- canonical operand order ----------------------------------------------------------

    /// The canonical order of two nodes: compound < symbol < constant; compounds by
    /// (operator rank, structural hash); symbols by key; constants by value. Independent of the
    /// context and of construction order (a hash collision falls back to the index).
    pub(crate) fn order(&self, x: u32, y: u32) -> Ordering {
        if x == y {
            return Ordering::Equal;
        }
        let (nx, ny) = (self.node(x), self.node(y));
        let class = |op: OpCode| match op {
            OpCode::Const => 2u8,
            OpCode::Sym => 1,
            _ => 0,
        };
        class(nx.op)
            .cmp(&class(ny.op))
            .then_with(|| match (nx.op, ny.op) {
                (OpCode::Const, OpCode::Const) => {
                    let (a, b) = (self.const_val(x), self.const_val(y));
                    match (a, b) {
                        (Some(a), Some(b)) => {
                            let (la, lb) = (a.limbs(), b.limbs());
                            la.len()
                                .cmp(&lb.len())
                                .then_with(|| la.iter().rev().cmp(lb.iter().rev()))
                        }
                        _ => Ordering::Equal,
                    }
                }
                (OpCode::Sym, OpCode::Sym) => {
                    let ka = &self.symbols.entries[nx.a as usize].key;
                    let kb = &self.symbols.entries[ny.a as usize].key;
                    ka.cmp(kb)
                }
                _ => (nx.op as u8).cmp(&(ny.op as u8)).then(
                    self.meta[x as usize]
                        .shash
                        .cmp(&self.meta[y as usize].shash),
                ),
            })
            .then(nx.width.cmp(&ny.width))
            .then(x.cmp(&y))
    }

    // ----- inspection -----------------------------------------------------------------------

    /// The width of an expression.
    pub fn width(&self, e: Expr) -> Result<Width, Error> {
        Ok(self.width_of(self.id(e)?))
    }

    /// A read-only view of an expression's top node.
    pub fn view(&self, e: Expr) -> Result<View, Error> {
        let i = self.id(e)?;
        Ok(self.view_of(i))
    }

    pub(crate) fn view_of(&self, i: u32) -> View {
        let n = self.node(i);
        let h = |j: u32| self.handle(j);
        match n.op {
            OpCode::Const => View::Const(self.const_val(i).unwrap_or(BitVec::zero(Width::W1))),
            OpCode::Sym => View::Sym(SymbolId(n.a)),
            OpCode::Zext => View::Zext(h(n.a)),
            OpCode::Sext => View::Sext(h(n.a)),
            OpCode::Extract => View::Extract {
                lo: n.b as u16,
                src: h(n.a),
            },
            OpCode::Concat => View::Concat {
                hi: h(n.a),
                lo: h(n.b),
            },
            OpCode::Select => View::Select {
                cond: h(n.a),
                then: h(n.b),
                els: h(n.c),
            },
            op if op.as_ext().is_some() => {
                let (arity, k) = op.as_ext().unwrap_or((1, 0));
                View::Ext {
                    op: self
                        .registry
                        .as_deref()
                        .and_then(|r| r.id_at(n.aux))
                        .unwrap_or_else(crate::ext::ExtId::dangling),
                    output: k as u8,
                    args: crate::ext::ExtArgs::new(&[h(n.a), h(n.b), h(n.c)][..arity]),
                }
            }
            op => {
                if let Some(u) = op.as_un() {
                    View::Un(u, h(n.a))
                } else if let Some(b) = op.as_bin() {
                    View::Bin(b, h(n.a), h(n.b))
                } else if let Some(c) = op.as_cmp() {
                    View::Cmp(c, h(n.a), h(n.b))
                } else {
                    unreachable!("every opcode is covered")
                }
            }
        }
    }

    /// The expression's direct operands, in order.
    pub fn children(&self, e: Expr) -> Result<impl Iterator<Item = Expr> + '_, Error> {
        let i = self.id(e)?;
        Ok(self.node(i).children().map(|c| self.handle(c)))
    }

    /// The value, if the expression is a constant node.
    pub fn as_const(&self, e: Expr) -> Result<Option<BitVec>, Error> {
        Ok(self.const_val(self.id(e)?))
    }

    /// Whether the expression is a constant or a symbol.
    pub fn is_leaf(&self, e: Expr) -> Result<bool, Error> {
        Ok(self.node(self.id(e)?).op.arity() == 0)
    }

    /// Structural depth (leaves are 0), saturating at `u32::MAX`. O(1).
    pub fn height(&self, e: Expr) -> Result<u32, Error> {
        Ok(self.meta[self.id(e)? as usize].height)
    }

    /// The size of the expression unfolded as a tree, saturating at `u32::MAX`. O(1).
    pub fn tree_size(&self, e: Expr) -> Result<u32, Error> {
        Ok(self.meta[self.id(e)? as usize].tree)
    }

    // ----- symbols --------------------------------------------------------------------------

    /// The symbol for `key`, created at width `width` on first use. A key has exactly one
    /// width per context.
    pub fn symbol(&mut self, key: impl Into<SymbolKey>, width: Width) -> Result<Expr, Error> {
        let key = key.into();
        if let Some(&id) = self.symbols.index.get(&key) {
            let e = &self.symbols.entries[id as usize];
            if e.width != width {
                return Err(Error::SymbolWidthConflict {
                    key,
                    have: e.width,
                    want: width,
                });
            }
            return Ok(self.handle(e.node));
        }
        self.new_symbol(key, width).map(|i| self.handle(i))
    }

    fn new_symbol(&mut self, key: SymbolKey, width: Width) -> Result<u32, Error> {
        let id = self.symbols.entries.len() as u32;
        let shash = combine(
            combine(u64::from(OpCode::Sym as u8), u64::from(width.bits())),
            key.structural_hash(),
        );
        let node = self.push(Node::new(OpCode::Sym, width.bits(), id, 0, 0), shash)?;
        self.symbols.index.insert(key.clone(), id);
        self.symbols.entries.push(SymEntry { key, width, node });
        Ok(node)
    }

    /// A new symbol with a key that is not yet used in this context.
    pub fn fresh_symbol(&mut self, width: Width) -> Result<Expr, Error> {
        loop {
            let key = SymbolKey::Fresh(self.symbols.next_fresh);
            self.symbols.next_fresh += 1;
            if !self.symbols.index.contains_key(&key) {
                return self.new_symbol(key, width).map(|i| self.handle(i));
            }
        }
    }

    /// The symbol for `key`, if it exists. Never creates.
    pub fn find_symbol(&self, key: &SymbolKey) -> Option<Expr> {
        let id = *self.symbols.index.get(key)?;
        Some(self.handle(self.symbols.entries[id as usize].node))
    }

    /// The symbol id, if the expression is a symbol node.
    pub fn symbol_id(&self, e: Expr) -> Result<Option<SymbolId>, Error> {
        let n = self.node(self.id(e)?);
        Ok((n.op == OpCode::Sym).then_some(SymbolId(n.a)))
    }

    /// A symbol's key.
    pub fn symbol_key(&self, id: SymbolId) -> Option<&SymbolKey> {
        self.symbols.entries.get(id.0 as usize).map(|e| &e.key)
    }

    /// A symbol's width.
    pub fn symbol_width(&self, id: SymbolId) -> Option<Width> {
        self.symbols.entries.get(id.0 as usize).map(|e| e.width)
    }

    /// The number of symbols.
    pub fn symbol_count(&self) -> usize {
        self.symbols.entries.len()
    }

    // ----- traversal ------------------------------------------------------------------------

    /// Every node reachable from `roots`, each once, children before parents. Iterative.
    pub fn post_order(&mut self, roots: &[Expr]) -> Result<Vec<Expr>, Error> {
        let ids = self.ids(roots)?;
        let order = self.post_order_ids(&ids);
        Ok(order.into_iter().map(|i| self.handle(i)).collect())
    }

    pub(crate) fn post_order_ids(&mut self, roots: &[u32]) -> Vec<u32> {
        self.marks.begin(self.nodes.len());
        let mut out = Vec::new();
        let mut stack: Vec<(u32, u8)> = Vec::new();
        for &r in roots {
            if self.marks.test_and_set(r) {
                continue;
            }
            stack.push((r, 0));
            while let Some(top) = stack.last_mut() {
                let (i, k) = *top;
                let n = self.nodes[i as usize];
                if (k as usize) < n.op.arity() {
                    top.1 += 1;
                    let c = [n.a, n.b, n.c][k as usize];
                    if !self.marks.test_and_set(c) {
                        stack.push((c, 0));
                    }
                } else {
                    stack.pop();
                    out.push(i);
                }
            }
        }
        out
    }

    /// The symbols reachable from `roots`, sorted by key.
    pub fn symbols_in(&mut self, roots: &[Expr]) -> Result<Vec<SymbolId>, Error> {
        let ids = self.ids(roots)?;
        let mut syms: Vec<SymbolId> = self
            .post_order_ids(&ids)
            .into_iter()
            .filter_map(|i| {
                let n = self.node(i);
                (n.op == OpCode::Sym).then_some(SymbolId(n.a))
            })
            .collect();
        syms.sort_by(|a, b| {
            self.symbols.entries[a.0 as usize]
                .key
                .cmp(&self.symbols.entries[b.0 as usize].key)
        });
        Ok(syms)
    }

    /// The number of distinct nodes reachable from `roots`, walking at most `cap + 1` nodes.
    /// Exact single-root results are cached.
    pub fn dag_size(&mut self, roots: &[Expr], cap: u32) -> Result<Bounded, Error> {
        let ids = self.ids(roots)?;
        if let [r] = ids[..]
            && let Some(&n) = self.dag_cache.get(&r)
        {
            return Ok(if n <= cap {
                Bounded::Exact(n)
            } else {
                Bounded::AtLeast(cap.saturating_add(1))
            });
        }
        self.marks.begin(self.nodes.len());
        let mut count: u32 = 0;
        let mut stack: Vec<u32> = Vec::new();
        for &r in &ids {
            if !self.marks.test_and_set(r) {
                stack.push(r);
            }
        }
        while let Some(i) = stack.pop() {
            count += 1;
            if count > cap {
                return Ok(Bounded::AtLeast(cap.saturating_add(1)));
            }
            for c in self.nodes[i as usize].children() {
                if !self.marks.test_and_set(c) {
                    stack.push(c);
                }
            }
        }
        if let [r] = ids[..] {
            self.dag_cache.insert(r, count);
        }
        Ok(Bounded::Exact(count))
    }
}

/// A dense side table keyed by expression index.
#[derive(Clone, Debug)]
pub struct ExprMap<T> {
    data: Vec<Option<T>>,
}

impl<T> Default for ExprMap<T> {
    fn default() -> Self {
        ExprMap { data: Vec::new() }
    }
}

impl<T> ExprMap<T> {
    /// An empty map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Inserts a value, returning the previous one.
    pub fn insert(&mut self, e: Expr, v: T) -> Option<T> {
        let i = e.index() as usize;
        if self.data.len() <= i {
            self.data.resize_with(i + 1, || None);
        }
        self.data[i].replace(v)
    }

    /// The value for `e`.
    pub fn get(&self, e: Expr) -> Option<&T> {
        self.data.get(e.index() as usize)?.as_ref()
    }

    /// Removes and returns the value for `e`.
    pub fn remove(&mut self, e: Expr) -> Option<T> {
        self.data.get_mut(e.index() as usize)?.take()
    }

    /// Whether `e` has a value.
    pub fn contains(&self, e: Expr) -> bool {
        self.get(e).is_some()
    }

    /// Removes every entry, keeping the allocation.
    pub fn clear(&mut self) {
        self.data.clear();
    }
}

/// A dense set of expressions (a bitset keyed by index).
#[derive(Clone, Debug, Default)]
pub struct ExprSet {
    bits: Vec<u64>,
}

impl ExprSet {
    /// An empty set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Inserts `e`; returns whether it was newly inserted.
    pub fn insert(&mut self, e: Expr) -> bool {
        let i = e.index() as usize;
        if self.bits.len() <= i / 64 {
            self.bits.resize(i / 64 + 1, 0);
        }
        let m = 1u64 << (i % 64);
        let fresh = self.bits[i / 64] & m == 0;
        self.bits[i / 64] |= m;
        fresh
    }

    /// Whether `e` is in the set.
    pub fn contains(&self, e: Expr) -> bool {
        let i = e.index() as usize;
        self.bits
            .get(i / 64)
            .is_some_and(|w| w & (1 << (i % 64)) != 0)
    }

    /// Removes every element, keeping the allocation.
    pub fn clear(&mut self) {
        self.bits.clear();
    }
}
