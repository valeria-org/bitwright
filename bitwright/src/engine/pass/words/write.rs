//! Forms written out as nodes, and the search for the smaller DAG (see the module above).
//!
//! Candidates are built in a scratch DAG, hash-consed like the context's, so that a part
//! written anew that is a node of the expression already is that node, and sizes are counted
//! there: only the DAG that is kept is built in the context.

use super::form::{Atom, AtomId, Form, FormId};
use super::lift::Lift;
use crate::engine::budget::Counter;
use crate::engine::{Runner, Stop};
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::{BitVec, Width};

/// No node of the context.
const NONE: u32 = u32::MAX;
/// The widest value written.
const MAX_WIDTH: u32 = 128;
/// How deep a form's parts nest when written.
const MAX_NEST: u32 = 64;
/// The most work (scratch nodes and terms) of one question.
const MAX_WORK: u64 = 1 << 23;
/// How many scratch nodes or terms are a unit of pass work: each is about 15 ns, half of what
/// the passes charge a unit for.
const PER_UNIT: u64 = 2;

/// A candidate was given up: it grew past what it replaces, or left the pass's bounds.
pub(super) enum Halt {
    Budget,
    Stop(Stop),
}

impl From<Stop> for Halt {
    fn from(s: Stop) -> Self {
        Halt::Stop(s)
    }
}

impl From<super::form::Over> for Halt {
    fn from(_: super::form::Over) -> Self {
        Halt::Budget
    }
}

type H<T> = Result<T, Halt>;

/// A node of the scratch DAG: a node of the context taken whole (`leaf`), or an operation
/// over scratch nodes, laid out as the context's nodes are (the operands first, then what is
/// no operand: an `extract`'s low bit).
#[derive(Clone, Copy)]
struct SNode {
    op: OpCode,
    aux: u8,
    width: u16,
    kids: [u32; 3],
    /// The node of the context this one is (a leaf), or is rebuilt like (its operator's
    /// fields), or `NONE`.
    of: u32,
    leaf: bool,
}

type Key = (u8, u8, u16, [u32; 3]);

#[derive(Default)]
pub(super) struct Build {
    nodes: Vec<SNode>,
    index: IdMap<Key, u32>,
    stamp: Vec<u32>,
    epoch: u32,
    stack: Vec<u32>,
    /// The marks of [`without`](Self::without), apart from those of `reach`.
    seen: Vec<u32>,
    tick: u32,
    /// The marks of [`beyond`](Self::beyond).
    extra: Vec<u32>,
    tock: u32,
}

impl Build {
    fn clear(&mut self) {
        self.nodes.clear();
        self.index.clear();
    }

    fn key(n: &SNode) -> Key {
        // (A leaf is the context's node, whatever its operator.)
        let op = if n.leaf { u8::MAX } else { n.op as u8 };
        (op, n.aux, n.width, n.kids)
    }

    fn push(&mut self, n: SNode) -> u32 {
        let key = Self::key(&n);
        if let Some(&i) = self.index.get(&key) {
            return i;
        }
        let i = self.nodes.len() as u32;
        self.nodes.push(n);
        self.index.insert(key, i);
        i
    }

    /// Forgets the nodes made since there were `len`.
    fn truncate(&mut self, len: usize) {
        while self.nodes.len() > len {
            if let Some(n) = self.nodes.pop() {
                self.index.remove(&Self::key(&n));
            }
        }
    }

    fn leaf(&mut self, cx: &Context, n: u32) -> u32 {
        let node = cx.node(n);
        self.push(SNode {
            op: node.op,
            aux: 0,
            width: node.width,
            kids: [n, 0, 0],
            of: n,
            leaf: true,
        })
    }

    /// Node `n` of the context over the scratch operands `kids`.
    fn like(&mut self, cx: &Context, n: u32, kids: [u32; 3]) -> u32 {
        let node = cx.node(n);
        let mut all = [node.a, node.b, node.c];
        let arity = node.op.arity();
        all[..arity].copy_from_slice(&kids[..arity]);
        self.push(SNode {
            op: node.op,
            aux: node.aux,
            width: node.width,
            kids: all,
            of: n,
            leaf: false,
        })
    }

    fn op(&mut self, op: OpCode, width: u32, kids: [u32; 3]) -> u32 {
        self.push(SNode {
            op,
            aux: 0,
            width: width as u16,
            kids,
            of: NONE,
            leaf: false,
        })
    }

    fn width(&self, i: u32) -> u32 {
        u32::from(self.nodes[i as usize].width)
    }

    fn operands(&self, i: u32) -> &[u32] {
        let n = &self.nodes[i as usize];
        if n.leaf { &[] } else { &n.kids[..n.op.arity()] }
    }

    fn extract(&mut self, e: u32, lo: u32, len: u32) -> u32 {
        if lo == 0 && len == self.width(e) {
            return e;
        }
        self.op(OpCode::Extract, len, [e, lo, 0])
    }

    /// `e` at `to` bits: truncated, or zero-extended.
    fn resize(&mut self, e: u32, to: u32) -> u32 {
        let w = self.width(e);
        match w.cmp(&to) {
            core::cmp::Ordering::Equal => e,
            core::cmp::Ordering::Greater => self.extract(e, 0, to),
            core::cmp::Ordering::Less => self.op(OpCode::Zext, to, [e, 0, 0]),
        }
    }

    /// Marks what `root` reaches (under a new epoch) and counts it.
    fn reach(&mut self, root: u32) -> u32 {
        self.stamp.resize(self.nodes.len(), 0);
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.stamp.fill(0);
            self.epoch = 1;
        }
        let mut count = 0;
        let mut stack = core::mem::take(&mut self.stack);
        stack.clear();
        stack.push(root);
        while let Some(i) = stack.pop() {
            if self.stamp[i as usize] == self.epoch {
                continue;
            }
            self.stamp[i as usize] = self.epoch;
            count += 1;
            stack.extend_from_slice(self.operands(i));
        }
        self.stack = stack;
        count
    }

    fn reached(&self, i: u32) -> bool {
        self.stamp.get(i as usize) == Some(&self.epoch)
    }

    /// How many nodes `root` reaches without passing through `avoid`.
    fn without(&mut self, root: u32, avoid: u32) -> u32 {
        self.seen.resize(self.nodes.len(), 0);
        self.tick = self.tick.wrapping_add(1);
        if self.tick == 0 {
            self.seen.fill(0);
            self.tick = 1;
        }
        let mut count = 0;
        let mut stack = core::mem::take(&mut self.stack);
        stack.clear();
        stack.push(root);
        while let Some(i) = stack.pop() {
            if i == avoid || self.seen[i as usize] == self.tick {
                continue;
            }
            self.seen[i as usize] = self.tick;
            count += 1;
            stack.extend_from_slice(self.operands(i));
        }
        self.stack = stack;
        count
    }

    /// How many nodes `e` reaches that the last [`without`](Self::without) did not come to
    /// (through them).
    fn beyond(&mut self, e: u32) -> u32 {
        self.extra.resize(self.nodes.len(), 0);
        self.tock = self.tock.wrapping_add(1);
        if self.tock == 0 {
            self.extra.fill(0);
            self.tock = 1;
        }
        let mut count = 0;
        let mut stack = core::mem::take(&mut self.stack);
        stack.clear();
        stack.push(e);
        while let Some(i) = stack.pop() {
            if self.seen.get(i as usize) == Some(&self.tick) || self.extra[i as usize] == self.tock
            {
                continue;
            }
            self.extra[i as usize] = self.tock;
            count += 1;
            stack.extend_from_slice(self.operands(i));
        }
        self.stack = stack;
        count
    }

    /// How many low bits of each node `root` reaches are read (after [`reach`](Self::reach)
    /// of it): `dem[i]` for node `i`.
    fn demand(&self, cx: &Context, root: u32, dem: &mut Vec<u32>) {
        dem.clear();
        dem.resize(self.nodes.len(), 0);
        dem[root as usize] = self.width(root);
        let konst = |i: u32| -> Option<u64> {
            let n = &self.nodes[i as usize];
            (n.leaf)
                .then(|| cx.const_val(n.of).and_then(|v| v.to_u64()))
                .flatten()
        };
        // (Operands are made before what uses them: every user comes first.)
        for i in (0..=root).rev() {
            if !self.reached(i) {
                continue;
            }
            let n = self.nodes[i as usize];
            if n.leaf {
                continue;
            }
            let d = dem[i as usize];
            let w = u32::from(n.width);
            let [a, b, c] = n.kids;
            let mut need = |k: u32, x: u32| {
                let x = x.min(self.width(k));
                if dem[k as usize] < x {
                    dem[k as usize] = x;
                }
            };
            match n.op {
                OpCode::Add | OpCode::Sub | OpCode::Mul | OpCode::Or | OpCode::Xor => {
                    need(a, d);
                    need(b, d);
                }
                OpCode::And => {
                    for (x, y) in [(a, b), (b, a)] {
                        // (Under a constant, the bits above its highest are not read.)
                        let top = konst(y).map_or(d, |k| d.min(64 - k.leading_zeros()));
                        need(x, top);
                    }
                }
                OpCode::Neg | OpCode::Not | OpCode::Zext => need(a, d),
                OpCode::Sext => need(a, if d <= self.width(a) { d } else { self.width(a) }),
                OpCode::Shl => match konst(b) {
                    Some(k) => {
                        need(a, d.saturating_sub(k.min(u64::from(w)) as u32));
                        need(b, w);
                    }
                    None => {
                        need(a, w);
                        need(b, w);
                    }
                },
                OpCode::LShr => match konst(b) {
                    Some(k) if d > 0 => {
                        need(a, d.saturating_add(k.min(u64::from(w)) as u32).min(w));
                        need(b, w);
                    }
                    Some(_) => need(b, w),
                    None => {
                        need(a, w);
                        need(b, w);
                    }
                },
                // (The second field is the low bit, no operand.)
                OpCode::Extract => need(a, if d > 0 { b + d } else { 0 }),
                OpCode::Concat => {
                    let wl = self.width(b);
                    need(b, d);
                    need(a, d.saturating_sub(wl));
                }
                OpCode::Select => {
                    need(a, 1);
                    need(b, d);
                    need(c, d);
                }
                _ => {
                    for &k in self.operands(i) {
                        need(k, u32::MAX);
                    }
                }
            }
        }
    }

    /// Builds what `root` reaches in the context.
    fn export(&self, cx: &mut Context, root: u32) -> Result<u32, crate::Error> {
        let mut made: IdMap<u32, u32> = IdMap::default();
        let mut stack = vec![(root, false)];
        while let Some((i, expanded)) = stack.pop() {
            if made.contains_key(&i) {
                continue;
            }
            let n = self.nodes[i as usize];
            if n.leaf {
                made.insert(i, n.of);
                continue;
            }
            if !expanded {
                stack.push((i, true));
                for &k in self.operands(i) {
                    if !made.contains_key(&k) {
                        stack.push((k, false));
                    }
                }
                continue;
            }
            let get = |k: u32| made.get(&k).copied().unwrap_or(0);
            let arity = n.op.arity();
            let mut kids = [0u32; 3];
            for (j, kid) in kids.iter_mut().enumerate().take(arity) {
                *kid = get(n.kids[j]);
            }
            let e = if n.of != NONE {
                cx.rebuild(n.of, kids)?
            } else {
                let [a, b, c] = kids;
                match n.op {
                    OpCode::Zext => cx.c_zext(a, n.width)?,
                    OpCode::Sext => cx.c_sext(a, n.width)?,
                    OpCode::Extract => cx.c_extract(a, n.kids[1] as u16, n.width)?,
                    OpCode::Concat => cx.c_concat(a, b)?,
                    OpCode::Select => cx.c_select(a, b, c)?,
                    op => {
                        if let Some(u) = op.as_un() {
                            cx.c_un(u, a)?
                        } else if let Some(bo) = op.as_bin() {
                            cx.c_bin(bo, a, b)?
                        } else {
                            return Err(crate::Error::Contract(
                                "a scratch node of an operator the pass does not write".into(),
                            ));
                        }
                    }
                }
            };
            made.insert(i, e);
        }
        Ok(made.get(&root).copied().unwrap_or(0))
    }
}

/// Which ways of writing a form are used.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Variant {
    /// Floors of one form are read as runs of its bits.
    words: bool,
    /// What of the rest is a multiple of a word's atoms goes into the word.
    absorb: bool,
}

const VARIANTS: [Variant; 3] = [
    Variant {
        words: true,
        absorb: true,
    },
    Variant {
        words: true,
        absorb: false,
    },
    Variant {
        words: false,
        absorb: false,
    },
];

/// The inverse of an odd `a` modulo `2^128`.
fn inverse(a: u128) -> u128 {
    let mut x = a;
    // Each step doubles the correct low bits (3 to start with).
    for _ in 0..6 {
        x = x.wrapping_mul(2u128.wrapping_sub(a.wrapping_mul(x)));
    }
    x
}

fn low(m: u32) -> u128 {
    if m >= 128 {
        u128::MAX
    } else {
        (1u128 << m) - 1
    }
}

/// The nodes under one root, and the search over them.
pub(super) struct Search<'a> {
    pub(super) lift: &'a mut Lift,
    pub(super) b: &'a mut Build,
    /// The nodes under the root, operands before what uses them.
    cone: Vec<u32>,
    /// Each one's place in `cone`.
    place: IdMap<u32, u32>,
    /// Each one's form.
    forms: Vec<Form>,
    /// Each one as it is now, in the scratch DAG.
    cur: Vec<u32>,
    /// What some were replaced by.
    sub: IdMap<u32, u32>,
    /// The place of each node as it was at first, by its scratch node.
    first_of: IdMap<u32, u32>,
    /// The first node of each width whose form modulo its width is the key.
    node_of: IdMap<(FormId, u16), u32>,
    /// The first node that is the atom.
    atom_of: IdMap<AtomId, u32>,
    /// The nodes that are XOR atoms: how many operands, the atom, the node and how many of
    /// the atom's low bits it is (all of them, or as many as its width); the longest first,
    /// then by structure.
    xors: Vec<(u32, AtomId, u32, u32)>,
    /// Per width `m`, the first node wider than `m` whose form modulo `2^m` is the key.
    wide: IdMap<u32, IdMap<FormId, u32>>,
    // What one candidate has written so far.
    below: u32,
    written: IdMap<(FormId, u32), u32>,
    atoms: IdMap<(AtomId, u32), u32>,
    count: u32,
    /// The most scratch nodes a candidate may add (it pays only if it adds fewer than the
    /// node it replaces takes with it), and how many there were when it began.
    cap: u32,
    mark: usize,
    /// Whether the candidate wrote floors as runs of a word, and moved terms into one.
    ran: bool,
    absorbed: bool,
    nest: u32,
    variant: Variant,
    /// Scratch nodes made and terms handled, charged to the meter as they come; and how
    /// many the question may take.
    charged: u64,
    spent: u64,
    total: u64,
    allow: u64,
}

impl<'a> Search<'a> {
    pub(super) fn new(lift: &'a mut Lift, b: &'a mut Build, cone: Vec<u32>) -> Self {
        let place = cone
            .iter()
            .enumerate()
            .map(|(i, &n)| (n, i as u32))
            .collect();
        b.clear();
        Search {
            lift,
            b,
            cone,
            place,
            forms: Vec::new(),
            cur: Vec::new(),
            sub: IdMap::default(),
            first_of: IdMap::default(),
            node_of: IdMap::default(),
            atom_of: IdMap::default(),
            xors: Vec::new(),
            wide: IdMap::default(),
            below: 0,
            written: IdMap::default(),
            atoms: IdMap::default(),
            count: 0,
            cap: 0,
            mark: 0,
            ran: false,
            absorbed: false,
            nest: 0,
            variant: VARIANTS[0],
            charged: 0,
            spent: 0,
            total: 0,
            allow: MAX_WORK,
        }
    }

    /// Charges the work done since the last call; `false` once the question's own allowance
    /// is used up.
    fn pay(&mut self, r: &mut Runner<'_, '_>) -> Result<bool, Stop> {
        // (The scratch DAG shrinks when a candidate is forgotten: only growth is work.)
        let now = self.lift.alg.work + self.b.nodes.len() as u64 + self.spent;
        let due = now.saturating_sub(self.charged);
        self.charged = now;
        self.total += due;
        r.meter.charge(Counter::PassWork, due.div_ceil(PER_UNIT))?;
        Ok(self.total < self.allow)
    }

    /// The work of the question so far.
    pub(super) fn work(&self) -> u64 {
        self.total
    }

    /// The question is given up at `allow` work, where that is less than a question's own.
    pub(super) fn limit(&mut self, allow: u64) {
        self.allow = allow.min(MAX_WORK);
    }

    /// Reads the facts and the form of every node, and what each is.
    fn prepare(&mut self, r: &mut Runner<'_, '_>, cx: &mut Context) -> Result<(), Stop> {
        for i in 0..self.cone.len() {
            let n = self.cone[i];
            self.lift.learn(r, cx, n)?;
        }
        self.lift.alg.work = 0;
        let mut listed: IdMap<(AtomId, u32), ()> = IdMap::default();
        for i in 0..self.cone.len() {
            let n = self.cone[i];
            // (Past the allowance a node is the atom it is.)
            if self.lift.alg.work < self.allow {
                self.lift.read(cx, n);
            }
            let w = cx.node(n).width;
            let f = self.lift.value(cx, n).unwrap_or_default();
            // (What of an atom is below `2^w`, where the node is that.)
            let mut low = None;
            if u32::from(w) <= 64 && self.lift.has(n) {
                let reduced = self.lift.alg.reduce(&f, u32::from(w));
                if let Ok(id) = self.lift.alg.intern(&reduced) {
                    self.node_of.entry((id, w)).or_insert(i as u32);
                }
                low = reduced.single();
            }
            let own = f.single();
            if let Some(a) = own
                && !self.atom_of.contains_key(&a)
            {
                self.atom_of.insert(a, i as u32);
            }
            for (a, bits) in [
                (own, u32::MAX),
                (low.filter(|&a| Some(a) != own), u32::from(w)),
            ] {
                if let Some(a) = a
                    && let Atom::Xor(_, li) = self.lift.alg.atom(a)
                    && listed.insert((a, bits), ()).is_none()
                {
                    let len = self.lift.alg.xor_list(li).0.len() as u32;
                    self.xors.push((len, a, i as u32, bits));
                }
            }
            self.forms.push(f);
        }
        let mut xors = core::mem::take(&mut self.xors);
        xors.sort_by(|x, y| {
            y.0.cmp(&x.0)
                .then(self.lift.alg.order(x.1, y.1))
                .then(y.3.cmp(&x.3))
        });
        self.xors = xors;
        self.pay(r)?;
        Ok(())
    }

    /// Every node as it is now, from place `from` on: itself over its operands as they are
    /// now, or what it was replaced by (`with` for the node at `from`, when given), which
    /// reads the nodes below it as they are now.
    fn rebuild(&mut self, cx: &Context, from: usize, with: Option<u32>) {
        self.cur.truncate(from);
        for i in from..self.cone.len() {
            let n = self.cone[i];
            let s = if i == from && with.is_some() {
                with.unwrap_or(0)
            } else if let Some(&s) = self.sub.get(&(i as u32)) {
                self.follow(s, i as u32)
            } else {
                let node = cx.node(n);
                if matches!(node.op, OpCode::Const | OpCode::Sym) {
                    self.b.leaf(cx, n)
                } else {
                    let mut kids = [0u32; 3];
                    for (j, c) in node.children().enumerate() {
                        kids[j] = self.place.get(&c).map_or(0, |&p| self.cur[p as usize]);
                    }
                    self.b.like(cx, n, kids)
                }
            };
            self.cur.push(s);
        }
        self.spent += (self.cone.len() - from) as u64;
    }

    /// `x`, written for the node at place `k` from the nodes below it as they were at first,
    /// over those nodes as they are now.
    fn follow(&mut self, x: u32, k: u32) -> u32 {
        let mut now: IdMap<u32, u32> = IdMap::default();
        let mut stack = vec![(x, false)];
        while let Some((i, expanded)) = stack.pop() {
            if now.contains_key(&i) {
                continue;
            }
            if let Some(&j) = self.first_of.get(&i)
                && j < k
            {
                now.insert(i, self.cur[j as usize]);
                continue;
            }
            let node = self.b.nodes[i as usize];
            if node.leaf {
                now.insert(i, i);
                continue;
            }
            let arity = node.op.arity();
            if !expanded {
                stack.push((i, true));
                for &c in &node.kids[..arity] {
                    if !now.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
                continue;
            }
            let mut kids = node.kids;
            let mut same = true;
            for c in &mut kids[..arity] {
                let to = now.get(c).copied().unwrap_or(*c);
                same &= to == *c;
                *c = to;
            }
            let to = if same {
                i
            } else {
                self.b.push(SNode { kids, ..node })
            };
            now.insert(i, to);
            self.spent += 1;
        }
        now.get(&x).copied().unwrap_or(x)
    }

    fn konst(&mut self, r: &mut Runner<'_, '_>, cx: &mut Context, v: u128, w: u32) -> H<u32> {
        let width = Width::new(w as u16).map_err(|_| Halt::Budget)?;
        let c = r.build(cx, |cx| {
            cx.mk_const(&BitVec::wrapping_from_u128(width, v & low(w)))
        })?;
        Ok(self.b.leaf(cx, c))
    }

    fn step(&mut self) -> H<()> {
        self.count += 1;
        let added = (self.b.nodes.len() - self.mark.min(self.b.nodes.len())) as u32;
        if added > self.cap || self.count > 8 * (self.cap + 8) {
            return Err(Halt::Budget);
        }
        Ok(())
    }

    /// `f` modulo `2^m`, as a node of `m` bits.
    fn form(&mut self, r: &mut Runner<'_, '_>, cx: &mut Context, f: &Form, m: u32) -> H<u32> {
        if m == 0 || m > MAX_WIDTH {
            return Err(Halt::Budget);
        }
        self.nest += 1;
        let out = if self.nest > MAX_NEST {
            Err(Halt::Budget)
        } else {
            self.form_in(r, cx, f, m)
        };
        self.nest -= 1;
        out
    }

    fn form_in(&mut self, r: &mut Runner<'_, '_>, cx: &mut Context, f: &Form, m: u32) -> H<u32> {
        let mut f = self.lift.alg.reduce(f, m);
        let id = self.lift.alg.intern(&f)?;
        if let Some(&e) = self.written.get(&(id, m)) {
            return Ok(e);
        }
        // A node below that already is this.
        if let Some(&j) = self.node_of.get(&(id, m as u16))
            && j < self.below
        {
            let e = self.cur[j as usize];
            self.written.insert((id, m), e);
            return Ok(e);
        }
        if !f.is_const() {
            if !self.wide.contains_key(&m) {
                let mut by: IdMap<FormId, u32> = IdMap::default();
                for i in 0..self.cone.len() {
                    let w = u32::from(cx.node(self.cone[i]).width);
                    if w > m && w <= 64 && !cx.is_const(self.cone[i]) {
                        let g = self.forms[i].clone();
                        let g = self.lift.alg.reduce(&g, m);
                        if let Ok(k) = self.lift.alg.intern(&g) {
                            by.entry(k).or_insert(i as u32);
                        }
                    }
                }
                self.wide.insert(m, by);
            }
            if let Some(&j) = self.wide.get(&m).and_then(|by| by.get(&id))
                && j < self.below
            {
                let e = self.b.resize(self.cur[j as usize], m);
                self.written.insert((id, m), e);
                return Ok(e);
            }
        }
        self.step()?;
        let mask = low(m);
        let mut parts: Vec<(u32, u128)> = Vec::new();
        self.regroup(r, cx, &mut f, m, &mut parts)?;
        if self.variant.words {
            self.words(r, cx, &mut f, m, &mut parts)?;
        }
        self.choices(r, cx, &mut f, m, &mut parts)?;
        for &(a, c) in &f.t {
            let c = c as u128 & mask;
            if c == 0 {
                continue;
            }
            let p = m - c.trailing_zeros();
            let e = self.atom(r, cx, a, p)?;
            parts.push((self.b.resize(e, m), c));
        }
        let mut acc: Option<u32> = None;
        let mut neg: Vec<u32> = Vec::new();
        for &(e, c) in &parts {
            let t = if c == 1 {
                e
            } else if c == mask {
                neg.push(e);
                continue;
            } else if c.is_power_of_two() {
                let k = self.konst(r, cx, u128::from(c.trailing_zeros()), m)?;
                self.b.op(OpCode::Shl, m, [e, k, 0])
            } else {
                let k = self.konst(r, cx, c, m)?;
                self.b.op(OpCode::Mul, m, [e, k, 0])
            };
            acc = Some(match acc {
                None => t,
                Some(a) => self.b.op(OpCode::Add, m, [a, t, 0]),
            });
        }
        let c = f.c as u128 & mask;
        if c != 0 {
            let k = self.konst(r, cx, c, m)?;
            acc = Some(match acc {
                None => k,
                Some(a) => self.b.op(OpCode::Add, m, [a, k, 0]),
            });
        }
        for e in neg {
            acc = Some(match acc {
                None => self.b.op(OpCode::Neg, m, [e, 0, 0]),
                Some(a) => self.b.op(OpCode::Sub, m, [a, e, 0]),
            });
        }
        let e = match acc {
            Some(e) => e,
            None => self.konst(r, cx, 0, m)?,
        };
        self.written.insert((id, m), e);
        Ok(e)
    }

    /// Terms `λ·G + λ·H − 2λ·(G & H)` of `f` taken out as `λ·(G ^ H)`, and `λ·G + λ·H −
    /// λ·(G & H)` as `λ·(G | H)`, where that leaves fewer terms.
    fn regroup(
        &mut self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
        f: &mut Form,
        m: u32,
        parts: &mut Vec<(u32, u128)>,
    ) -> H<()> {
        let mask = low(m);
        loop {
            let mut found = None;
            // (The ANDs of the largest forms first.)
            for &(a, c) in f.t.iter().rev() {
                let Atom::And(p, gi, hi) = self.lift.alg.atom(a) else {
                    continue;
                };
                // `λ·(G ^ H) + λ·(G & H)` is `λ·(G | H)`, of the values the AND was asked of.
                if let Some(x) = self.lift.alg.xor_of(a)
                    && f.coeff(x) == c
                    && let Some((g, h)) = self.lift.alg.whole(a).cloned()
                {
                    found = Some((OpCode::Or, c, f.without(a).without(x), g, h));
                    break;
                }
                // (An AND of `p` bits is of the operands modulo `2^p`.)
                if u32::from(p) < m {
                    continue;
                }
                let (g, h) = (
                    self.lift.alg.form(gi).clone(),
                    self.lift.alg.form(hi).clone(),
                );
                let n0 = f.t.len();
                let mut best: Option<(OpCode, i128, Form)> = None;
                let mut cands = vec![(OpCode::Or, -c)];
                if c % 2 == 0 {
                    cands.insert(0, (OpCode::Xor, -(c / 2)));
                    // (`−2λ` is the coefficient modulo `2^m` for a second λ.)
                    if m < 100 {
                        cands.insert(1, (OpCode::Xor, -(c / 2) + (1i128 << (m - 1))));
                    }
                }
                for (kind, lam) in cands {
                    let Ok(rest) = self
                        .lift
                        .alg
                        .sum(f, &g, -lam)
                        .and_then(|x| self.lift.alg.sum(&x, &h, -lam))
                    else {
                        continue;
                    };
                    let rest = self.lift.alg.reduce(&rest.without(a), m);
                    let fewer = rest.t.len() + 1 < n0
                        || (rest.t.len() + 1 == n0 && (g.is_const() || h.is_const()));
                    if fewer && best.as_ref().is_none_or(|b| rest.t.len() < b.2.t.len()) {
                        best = Some((kind, lam, rest));
                    }
                }
                if let Some((kind, lam, rest)) = best {
                    found = Some((kind, lam, rest, g, h));
                    break;
                }
            }
            let Some((kind, lam, rest, g, h)) = found else {
                return Ok(());
            };
            let (ge, he) = (self.form(r, cx, &g, m)?, self.form(r, cx, &h, m)?);
            parts.push((self.b.op(kind, m, [ge, he, 0]), lam as u128 & mask));
            *f = rest;
        }
    }

    /// Terms `λ·(c ? 0 : B)` or `λ·(c ? A : 0)` of `f` with `λ·P·C` beside them (`C` the
    /// form of `c`, all its terms) taken out as the choice with the constant arm it was read
    /// from: `λ·(c ? P : B)`, or `λ·(c ? A : −P)` and `λ·P` more in the constant.
    fn choices(
        &mut self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
        f: &mut Form,
        m: u32,
        parts: &mut Vec<(u32, u128)>,
    ) -> H<()> {
        let mask = low(m);
        loop {
            let mut found = None;
            for &(s, lam) in &f.t {
                let Atom::Sel(ci, ai, bi) = self.lift.alg.atom(s) else {
                    continue;
                };
                let (c, a, b) = (
                    self.lift.alg.form(ci).clone(),
                    self.lift.alg.form(ai).clone(),
                    self.lift.alg.form(bi).clone(),
                );
                let none = |x: &Form| x.is_const() && x.c == 0;
                if none(&a) == none(&b) {
                    continue;
                }
                let Some(&(a0, c0)) = c.t.first() else {
                    continue;
                };
                let have = f.coeff(a0);
                let Some(unit) = lam.checked_mul(c0) else {
                    continue;
                };
                if have == 0 || have % unit != 0 {
                    continue;
                }
                let p = have / unit;
                let Some(lp) = lam.checked_mul(p) else {
                    continue;
                };
                let Ok(rest) = self.lift.alg.sum(f, &c, -lp) else {
                    continue;
                };
                let rest = rest.without(s);
                if rest.t.len() + c.t.len() + 1 != f.t.len() {
                    continue;
                }
                found = Some((lam, p, lp, rest, c, a, b));
                break;
            }
            let Some((lam, p, lp, mut rest, c, a, b)) = found else {
                return Ok(());
            };
            let (x, y) = if a.is_const() {
                (Form::konst(p), b)
            } else {
                rest.c = rest.c.wrapping_add(lp);
                (a, Form::konst(-p))
            };
            let ce = self.form(r, cx, &c, 1)?;
            let (xe, ye) = (self.form(r, cx, &x, m)?, self.form(r, cx, &y, m)?);
            parts.push((
                self.b.op(OpCode::Select, m, [ce, xe, ye]),
                lam as u128 & mask,
            ));
            *f = self.lift.alg.reduce(&rest, m);
        }
    }

    /// The floors in `f` that are floors of one form `E` (each `floor(R / 2^k)` with `R ≡ E`
    /// modulo `2^k`) taken out as runs of the bits of `E`.
    fn words(
        &mut self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
        f: &mut Form,
        m: u32,
        parts: &mut Vec<(u32, u128)>,
    ) -> H<()> {
        let mask = low(m);
        // The floors that are no node below, the widest shift first.
        let mut floors: Vec<(AtomId, FormId, u32)> = Vec::new();
        for &(a, _) in &f.t {
            if let Atom::Floor(ri, k) = self.lift.alg.atom(a)
                && self.atom_of.get(&a).is_none_or(|&j| j >= self.below)
            {
                floors.push((a, ri, u32::from(k)));
            }
        }
        if floors.is_empty() {
            return Ok(());
        }
        floors.sort_by(|x, y| y.2.cmp(&x.2).then(self.lift.alg.order(x.0, y.0)));
        // Families: each floor with the first earlier one it is congruent to (the floor, its
        // shift, and what the family's form has more than its own).
        type Family = (Form, Vec<(AtomId, u32, Form)>);
        let mut fams: Vec<Family> = Vec::new();
        for &(a, ri, k) in &floors {
            let rf = self.lift.alg.form(ri).clone();
            let mut joined = false;
            for fam in &mut fams {
                let Ok(d) = self.lift.alg.sum(&fam.0, &rf, -1) else {
                    continue;
                };
                let step = 1i128 << k;
                if d.c % step == 0 && d.t.iter().all(|x| x.1 % step == 0) {
                    fam.1.push((a, k, d));
                    joined = true;
                    break;
                }
            }
            if !joined {
                fams.push((rf, vec![(a, k, Form::default())]));
            }
        }
        // The words that are sums first: one may take with it the high part of an atom (see
        // below) that a word of that atom alone would be slices of.
        fams.sort_by_key(|fam| fam.0.single().is_some());
        for (e0, members) in fams {
            // (An earlier family may have taken a floor away, or changed how often it is there.)
            let mem: Vec<(AtomId, i128, u32, &Form)> = members
                .iter()
                .filter_map(|(a, k, d)| {
                    let c = f.coeff(*a);
                    (c as u128 & mask != 0).then_some((*a, c, *k, d))
                })
                .collect();
            if mem.is_empty() {
                continue;
            }
            let mut e = e0;
            let mut g = f.clone();
            let mut ok = true;
            for &(a, c, k, d) in &mem {
                // c·floor(R / 2^k) = c·floor(E / 2^k) − c·(E − R) / 2^k. The member's term is
                // taken off as it was: `E` may hold members of its own family (a floor of a
                // form with floors of it inside), which this puts back.
                let q = Form {
                    c: d.c >> k,
                    t: d.t.iter().map(|x| (x.0, x.1 >> k)).collect(),
                };
                let own = Form {
                    c: 0,
                    t: vec![(a, 1)],
                };
                let next = self
                    .lift
                    .alg
                    .sum(&g, &own, -c)
                    .and_then(|x| self.lift.alg.sum(&x, &q, -c));
                match next {
                    Ok(x) => g = x,
                    Err(_) => ok = false,
                }
            }
            if !ok {
                continue;
            }
            g = self.lift.alg.reduce(&g, m);
            let kmax = mem.iter().map(|x| x.2).max().unwrap_or(0);
            // What of the rest is a multiple of the atoms of E goes into the word: floor((E +
            // 2^k·Q) / 2^k) = floor(E / 2^k) + Q.
            if self.variant.absorb {
                let total = mem.iter().fold(0u128, |s, x| {
                    s.wrapping_add((x.1 as u128).wrapping_shl(kmax - x.2))
                }) & mask;
                let tz = total.trailing_zeros();
                if total != 0 && tz < m {
                    let bits = m - tz;
                    let inv = inverse(total >> tz) & low(bits);
                    // (The constant goes with them: a constant added limb by limb.)
                    let part = |gb: u128| -> i128 {
                        if gb == 0 || gb.trailing_zeros() < tz {
                            return 0;
                        }
                        let mut x = ((gb >> tz).wrapping_mul(inv) & low(bits)) as i128;
                        if bits < 127 && x >= 1i128 << (bits - 1) {
                            x -= 1i128 << bits;
                        }
                        x
                    };
                    let mut q: Vec<(AtomId, i128)> = Vec::new();
                    for &(b, _) in &e.t {
                        let x = part(g.coeff(b) as u128 & mask);
                        if x != 0 {
                            q.push((b, x));
                        }
                    }
                    let qc = part(g.c as u128 & mask);
                    // And what takes the high part of an atom of E away: with `−2^j·floor(t /
                    // 2^j)` in it, the word has the low `j` bits of `t` where it had `t` (the
                    // half of a register that is the operand).
                    let mut cut: Vec<(AtomId, i128)> = Vec::new();
                    for &(b, gb) in &g.t {
                        if let Atom::Floor(ri, j) = self.lift.alg.atom(b)
                            && let Some(t) = self.lift.alg.form(ri).single()
                            && u32::from(j) >= kmax
                            && u32::from(j) - kmax < 100
                        {
                            let x = part(gb as u128 & mask);
                            let whole = e.coeff(t).checked_mul(1i128 << (u32::from(j) - kmax));
                            if x != 0 && whole.is_some_and(|w| w != 0 && x == -w) {
                                cut.push((b, x));
                            }
                        }
                    }
                    if (!q.is_empty() || qc != 0 || !cut.is_empty()) && bits < 100 && kmax < 100 {
                        let mut qf = Form { c: qc, t: q };
                        for (b, x) in cut {
                            let one = Form {
                                c: 0,
                                t: vec![(b, 1)],
                            };
                            if let Ok(with) = self.lift.alg.sum(&qf, &one, x) {
                                qf = with;
                            }
                        }
                        let moved =
                            self.lift.alg.add(&e, &qf, 1i128 << kmax).and_then(|e2| {
                                Ok((e2, self.lift.alg.sum(&g, &qf, -(total as i128))?))
                            });
                        if let Ok((e2, g2)) = moved {
                            e = e2;
                            g = self.lift.alg.reduce(&g2, m);
                            self.absorbed = true;
                        }
                    }
                }
            }
            // E itself, where the rest holds a multiple of it.
            let mut lam = 0i128;
            if let Some(&(a0, e0c)) = e.t.first() {
                let g0 = g.coeff(a0);
                if g0 != 0
                    && g0 % e0c == 0
                    && let Ok(cand) = self.lift.alg.sum(&g, &e, -(g0 / e0c))
                {
                    let cand = self.lift.alg.reduce(&cand, m);
                    if cand.t.len() < g.t.len() {
                        lam = g0 / e0c;
                        g = cand;
                    }
                }
            }
            // A word `t + 2^j·R` read from bit `j` up is `floor(t / 2^j) + R` read from bit 0
            // (floor((t + 2^j·R) / 2^(j + k)) = floor((floor(t / 2^j) + R) / 2^k)): the word
            // as it was before the slice of `t` in it went into the floors around it.
            let mut drop = 0u32;
            let kmin = mem.iter().map(|x| x.2).min().unwrap_or(0);
            let odd = e.t.iter().filter(|x| x.1 & 1 != 0).count();
            if lam == 0
                && kmin > 0
                && odd == 1
                && let Some(&(t, 1)) = e.t.iter().find(|x| x.1 & 1 != 0)
            {
                let others = e.t.iter().filter(|x| x.0 != t);
                let j = others
                    .clone()
                    .map(|x| x.1.trailing_zeros())
                    .min()
                    .unwrap_or(0)
                    .min(kmin);
                if j > 0 {
                    let below = e.c.rem_euclid(1i128 << j);
                    let inner = Form {
                        c: below,
                        t: vec![(t, 1)],
                    };
                    let rest = Form {
                        c: (e.c - below) >> j,
                        t: others.map(|x| (x.0, x.1 >> j)).collect(),
                    };
                    let up = self.lift.alg.floor(&inner, j, None);
                    if let Ok(e2) = up.and_then(|fl| self.lift.alg.add(&fl, &rest, 1)) {
                        e = e2;
                        drop = j;
                    }
                }
            }
            let ie = self.lift.alg.interval(&e);
            let reach = |c: i128, k: u32| k + m - (c as u128 & mask).trailing_zeros().min(m);
            let mut top = mem
                .iter()
                .map(|x| reach(x.1, x.2 - drop))
                .max()
                .unwrap_or(0);
            if lam as u128 & mask != 0 {
                top = top.max(reach(lam, 0));
            }
            if let Some(b) = ie.bits() {
                top = top.min(b);
            }
            if top == 0 || top > MAX_WIDTH {
                continue;
            }
            // The weight of each bit of E.
            let wts: Vec<u128> = (0..top)
                .map(|b| {
                    let mut w = (lam as u128).wrapping_shl(b);
                    for x in &mem {
                        let k = x.2 - drop;
                        if k <= b {
                            w = w.wrapping_add((x.1 as u128).wrapping_shl(b - k));
                        }
                    }
                    w & mask
                })
                .collect();
            let mut runs: Vec<(u32, u32, u128)> = Vec::new();
            let mut b = 0u32;
            while b < top {
                if wts[b as usize] == 0 {
                    b += 1;
                    continue;
                }
                let (lo, c0) = (b, wts[b as usize]);
                let at = |x: u32| {
                    if x - lo >= 128 {
                        0
                    } else {
                        c0.wrapping_shl(x - lo) & mask
                    }
                };
                b += 1;
                while b < top && wts[b as usize] != 0 && wts[b as usize] == at(b) {
                    b += 1;
                }
                // (Bits whose weight is 0 modulo 2^m may be read too.)
                if b < top && at(b) == 0 && wts[b as usize..].iter().all(|&w| w == 0) {
                    b = top;
                }
                runs.push((lo, b - lo, c0));
            }
            if runs.len() > mem.len() + 1 && lam == 0 {
                continue;
            }
            self.ran = true;
            let word = self.form(r, cx, &e, top)?;
            *f = g;
            for (lo, len, c0) in runs {
                let mut piece = self.b.extract(word, lo, len);
                let p = m - c0.trailing_zeros();
                if len > p {
                    piece = self.b.resize(piece, p);
                }
                parts.push((self.b.resize(piece, m), c0));
            }
        }
        Ok(())
    }

    /// Atom `a` modulo `2^p`, as a node of `p` bits.
    fn atom(&mut self, r: &mut Runner<'_, '_>, cx: &mut Context, a: AtomId, p: u32) -> H<u32> {
        if p == 0 || p > MAX_WIDTH {
            return Err(Halt::Budget);
        }
        if let Some(&e) = self.atoms.get(&(a, p)) {
            return Ok(e);
        }
        let kind = self.lift.alg.atom(a);
        // The node that is the atom: a node of the context is itself (and the node being
        // written is not written from itself).
        let node = match kind {
            Atom::Leaf(n) => self.place.get(&n).copied(),
            _ => self.atom_of.get(&a).copied(),
        }
        .filter(|&j| j < self.below);
        if let Some(j) = node {
            let e = self.b.resize(self.cur[j as usize], p);
            self.atoms.insert((a, p), e);
            return Ok(e);
        }
        self.step()?;
        let iv = self.lift.alg.bounds(a);
        let e = match kind {
            Atom::Leaf(_) => return Err(Halt::Budget),
            Atom::Floor(ri, k) => {
                let (rf, k) = (self.lift.alg.form(ri).clone(), u32::from(k));
                if let Some(bits) = iv.bits() {
                    // Not negative: its bits, and zeros above them.
                    let b = bits.min(p);
                    let inner = self.form(r, cx, &rf, k + b)?;
                    let e = self.b.extract(inner, k, b);
                    self.b.resize(e, p)
                } else if iv.within(-1, 0) {
                    // A borrow: one bit, as its sign.
                    let inner = self.form(r, cx, &rf, k + 1)?;
                    let e = self.b.extract(inner, k, 1);
                    if p == 1 {
                        e
                    } else {
                        self.b.op(OpCode::Sext, p, [e, 0, 0])
                    }
                } else {
                    let inner = self.form(r, cx, &rf, k + p)?;
                    self.b.extract(inner, k, p)
                }
            }
            Atom::And(q0, xi, yi) => {
                let q = u32::from(q0).min(p);
                let (x, y) = (
                    self.lift.alg.form(xi).clone(),
                    self.lift.alg.form(yi).clone(),
                );
                let (xe, ye) = (self.form(r, cx, &x, q)?, self.form(r, cx, &y, q)?);
                let e = self.b.op(OpCode::And, q, [xe, ye, 0]);
                self.b.resize(e, p)
            }
            Atom::Xor(q0, li) => {
                let q = u32::from(q0).min(p);
                let (ops, mut k) = {
                    let (ops, k) = self.lift.alg.xor_list(li);
                    (ops.to_vec(), k)
                };
                // The operands not written yet.
                let mut left: IdMap<FormId, ()> = ops.iter().map(|&i| (i, ())).collect();
                let mut pieces: Vec<u32> = Vec::new();
                // The XORs of some of the operands that nodes below are, the longest first
                // (they are in that order).
                let mut from = 0;
                while !left.is_empty() {
                    let mut part = None;
                    let mut seen = 0u64;
                    for idx in from..self.xors.len() {
                        let (len, b, j, bits) = self.xors[idx];
                        seen += 1;
                        if b == a || j >= self.below || len as usize > left.len() || q > bits {
                            continue;
                        }
                        let Atom::Xor(_, l2) = self.lift.alg.atom(b) else {
                            continue;
                        };
                        let (o2, k2) = self.lift.alg.xor_list(l2);
                        seen += o2.len() as u64;
                        if o2.iter().all(|i| left.contains_key(i)) {
                            part = Some((idx, j, o2.to_vec(), k2));
                            break;
                        }
                    }
                    self.spent += seen;
                    let Some((idx, j, o2, k2)) = part else {
                        break;
                    };
                    for i in &o2 {
                        left.remove(i);
                    }
                    k ^= k2;
                    pieces.push(self.b.resize(self.cur[j as usize], q));
                    from = idx + 1;
                }
                for i in ops {
                    if left.contains_key(&i) {
                        let f = self.lift.alg.form(i).clone();
                        pieces.push(self.form(r, cx, &f, q)?);
                    }
                }
                let k = k as u128 & low(q);
                if k != 0 {
                    pieces.push(self.konst(r, cx, k, q)?);
                }
                let mut acc = pieces[0];
                for &e in &pieces[1..] {
                    acc = self.b.op(OpCode::Xor, q, [acc, e, 0]);
                }
                self.b.resize(acc, p)
            }
            Atom::Sel(ci, ai, bi) => {
                let c = self.lift.alg.form(ci).clone();
                let (x, y) = (
                    self.lift.alg.form(ai).clone(),
                    self.lift.alg.form(bi).clone(),
                );
                let ce = self.form(r, cx, &c, 1)?;
                let (xe, ye) = (self.form(r, cx, &x, p)?, self.form(r, cx, &y, p)?);
                self.b.op(OpCode::Select, p, [ce, xe, ye])
            }
        };
        self.atoms.insert((a, p), e);
        Ok(e)
    }

    /// Node `i` written anew from its form modulo `2^d`, as a node of `at` bits (`d`, or the
    /// node's width: any value with those low `d` bits), in `variant`, with at most `cap`
    /// parts: `None` when that is given up.
    #[allow(clippy::too_many_arguments)]
    fn candidate(
        &mut self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
        i: usize,
        d: u32,
        at: u32,
        variant: Variant,
        cap: u32,
    ) -> Result<Option<u32>, Stop> {
        self.below = i as u32;
        self.written.clear();
        self.atoms.clear();
        self.count = 0;
        self.cap = cap;
        self.mark = self.b.nodes.len();
        self.nest = 0;
        self.variant = variant;
        if variant == VARIANTS[0] {
            self.ran = false;
            self.absorbed = false;
        }
        let f = self.forms[i].clone();
        let w = u32::from(cx.node(self.cone[i]).width);
        let f = if at == d {
            f
        } else {
            // Any value with those low bits: the constant is the one nearest 0 (`−1 − x`, not
            // `2^d − 1 − x`).
            let mut f = self.lift.alg.reduce(&f, d);
            if f.c >> (d - 1) != 0 {
                f.c -= 1i128 << d;
            }
            f
        };
        match self.form(r, cx, &f, at) {
            Ok(e) => Ok(Some(self.b.resize(e, w))),
            Err(Halt::Budget) => Ok(None),
            Err(Halt::Stop(s)) => Err(s),
        }
    }

    /// The search: from the root down, each node is written anew from its form, at its width
    /// and at the bits of it that are read, and replaced where that leaves the root's DAG
    /// smaller. The root as it is in the end, in the scratch DAG, with the size of its DAG,
    /// when anything changed.
    pub(super) fn run(
        &mut self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
    ) -> Result<Option<(u32, u32)>, Stop> {
        self.prepare(r, cx)?;
        self.rebuild(cx, 0, None);
        for (j, &s) in self.cur.iter().enumerate() {
            self.first_of.entry(s).or_insert(j as u32);
        }
        let last = self.cone.len() - 1;
        let first = self.cur[last];
        let mut size = self.b.reach(first);
        let mut dem: Vec<u32> = Vec::new();
        self.b.demand(cx, first, &mut dem);
        for i in (0..=last).rev() {
            let n = self.cone[i];
            let node = cx.node(n);
            let w = u32::from(node.width);
            if matches!(node.op, OpCode::Const | OpCode::Sym) || w > 64 {
                continue;
            }
            // (The marks and the demand are of the root as it is now.)
            let here = self.cur[i];
            if !self.b.reached(here) {
                continue;
            }
            if !self.pay(r)? {
                break;
            }
            let d = dem[here as usize].min(w);
            // At its width; and where only `d` low bits of it are read, those bits alone,
            // extended, or any value of its width that has them.
            let part = 0 < d && d < w;
            let widths = [Some((w, w)), part.then_some((d, d)), part.then_some((d, w))];
            // What goes with the node when it is replaced, at most: what the root reaches only
            // through it. A candidate pays only if it adds fewer nodes than that.
            let kept = self.b.without(self.cur[last], here);
            let own = size - kept;
            self.spent += u64::from(size);
            let cap = own.saturating_sub(1);
            let mut best: Option<(u32, u32, u32, Variant)> = None;
            let mut moved = false;
            let mark = self.b.nodes.len();
            for (width, at) in widths.into_iter().flatten() {
                for variant in VARIANTS {
                    // (Without what the first way did not do, the others are the first.)
                    if (variant == VARIANTS[1] && !self.absorbed)
                        || (variant == VARIANTS[2] && !self.ran)
                    {
                        continue;
                    }
                    let cand = self.candidate(r, cx, i, width, at, variant, cap)?;
                    if let Some(e) = cand
                        && e != here
                    {
                        // The root with the candidate in the node's place: what it reaches
                        // without the node, and what the candidate reaches besides. Where
                        // the candidate is a node there was, nodes above it may become nodes
                        // there are, and the root is built to count.
                        let s = if (e as usize) < mark {
                            moved = true;
                            self.rebuild(cx, i, Some(e));
                            self.b.reach(self.cur[last])
                        } else {
                            let more = self.b.beyond(e);
                            self.spent += u64::from(more);
                            kept + more
                        };
                        if s < size && best.is_none_or(|b| s < b.0) {
                            best = Some((s, width, at, variant));
                        }
                    }
                    self.b.truncate(mark);
                }
            }
            // (Written again: the scratch nodes of what was tried were forgotten.)
            let taken = match best {
                Some((_, width, at, variant)) => {
                    self.candidate(r, cx, i, width, at, variant, cap)?
                }
                None => None,
            };
            if let Some(e) = taken {
                self.sub.insert(i as u32, e);
                self.rebuild(cx, i, None);
                let s = self.b.reach(self.cur[last]);
                if s < size {
                    size = s;
                    self.b.demand(cx, self.cur[last], &mut dem);
                    continue;
                }
                // (Counted too small: as it was.)
                self.sub.remove(&(i as u32));
                moved = true;
            }
            if moved {
                self.rebuild(cx, i, None);
                self.b.truncate(mark);
                self.b.reach(self.cur[last]);
            } else {
                self.b.truncate(mark);
            }
        }
        self.pay(r)?;
        let now = self.cur[last];
        Ok((now != first).then_some((now, size)))
    }

    /// Builds the scratch node `e` in the context.
    pub(super) fn export(
        &mut self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
        e: u32,
    ) -> Result<u32, Stop> {
        let b = &*self.b;
        r.build(cx, |cx| b.export(cx, e))
    }
}
