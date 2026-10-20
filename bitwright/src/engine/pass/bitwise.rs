//! The bitwise pass: a pure bitwise function (`& | ^ ~`, with `0` and all-ones) of at most
//! three atoms is determined by its 8-entry truth table, and is replaced by a minimum-size
//! expression for that table when that is smaller.
//!
//! Bitwise functions act on each bit position independently, so the truth table over single
//! bits (W = 1) determines the function at every width: the table is exact, not an
//! approximation. The minimum forms are found once by a breadth-first search over expression
//! sizes (an immutable cache, computed on first use) and verified exhaustively by the tests.
//!
//! *Constants.* A function of at most three atoms and some constants (masks, `(y & C) ^ C`) is,
//! on each class of bit positions where every constant is 0 or all-ones, a function of the
//! atoms alone: one truth table per class. Bit positions are independent, so the tables
//! determine the function exactly. When the classes take at most two tables, `t` on the bits of
//! a mask `M` and `u` elsewhere, it is written as the cheapest of `f_t & M` (`u` zero),
//! `f_t | ~M` (`u` all-ones), `f_u ^ M` (`t` the complement of `u`) and `f_u ^ (f_{t^u} & M)`,
//! with `f` the minimum forms (and the same with the roles swapped). The compares pass decides
//! `a == b` by the same tables: equal tables in every class, or complementary ones in some.
//!
//! *Wider regions.* Above three atoms a region is an atom of the regions over it, which can
//! hide that a function depends on few of the atoms below: a node one of whose atoms is such a
//! region is read again over up to six atoms (a 64-entry table, one `u64`), through every
//! region of at most six, and when its table depends on three atoms or fewer it is written as
//! their minimum form. So masking that cancels over more atoms comes apart:
//! `((a ^ m) & (b ^ n)) ^ ((a ^ m) & n) ^ (m & (b ^ n)) ^ (m & n)` is `a & b`. Constants are
//! atoms there, so a node of more than three atoms is read by classes first.

use std::sync::OnceLock;

use super::{Fin, PassKind, Runner, Step, Stop, finish, worth_building};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::ops::{BinOp, UnOp};

/// The truth tables of the three atoms: bit `i` is the atom's value in combination `i`, where
/// atom `k` is 1 exactly when bit `k` of `i` is.
const VARS: [u8; 3] = [0xAA, 0xCC, 0xF0];

/// The most atoms of a wide description: its table has 2^6 entries, one `u64`.
const WIDE: usize = 6;

/// The truth tables of six atoms, as [`VARS`] for three.
const WIDE_VARS: [u64; WIDE] = [
    0xAAAA_AAAA_AAAA_AAAA,
    0xCCCC_CCCC_CCCC_CCCC,
    0xF0F0_F0F0_F0F0_F0F0,
    0xFF00_FF00_FF00_FF00,
    0xFFFF_0000_FFFF_0000,
    0xFFFF_FFFF_0000_0000,
];

/// A node of a minimum-form template.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum T {
    Var(u8),
    Zero,
    Ones,
    Not(u16),
    Bin(BinOp, u16, u16),
}

/// For every truth table: a template (nodes in post-order; the last is the root) and its size
/// in operators.
pub(crate) struct MinForms {
    pub(crate) forms: Vec<(Vec<T>, u8)>,
    /// Per truth table, more templates of the same size, for renderings that share subterms
    /// with others: the first [`ALTERNATIVES`] found, then as many again each with a subterm
    /// (by table) the ones before lack.
    #[cfg_attr(not(feature = "mba"), allow(dead_code))]
    pub(crate) alts: Vec<Vec<Vec<T>>>,
}

/// The most other templates of minimum size kept per truth table in order found (and again as
/// many for new subterms).
pub(crate) const ALTERNATIVES: usize = 8;

/// The minimum forms, computed on first use.
pub(crate) fn min_forms() -> &'static MinForms {
    static FORMS: OnceLock<MinForms> = OnceLock::new();
    FORMS.get_or_init(search)
}

/// Breadth-first search over expression sizes: every function of size `c` is `~f` with
/// `size(f) = c - 1`, or `f op g` with `size(f) + size(g) = c - 1`. Ties keep the first found
/// (a fixed enumeration order), so the table is deterministic.
fn search() -> MinForms {
    // best[tt] = (template, size)
    let mut best: Vec<Option<(Vec<T>, u8)>> = vec![None; 256];
    let mut alts: Vec<Vec<Vec<T>>> = vec![Vec::new(); 256];
    // Per table, the subterm tables of its form and alternatives.
    let mut covered: Vec<Vec<u8>> = vec![Vec::new(); 256];
    best[0x00] = Some((vec![T::Zero], 0));
    best[0xFF] = Some((vec![T::Ones], 0));
    for (k, &v) in VARS.iter().enumerate() {
        best[v as usize] = Some((vec![T::Var(k as u8)], 0));
    }
    let concat = |a: &[T], b: &[T], op: BinOp| -> Vec<T> {
        let off = a.len() as u16;
        let mut out = a.to_vec();
        out.extend(b.iter().map(|t| match *t {
            T::Not(x) => T::Not(x + off),
            T::Bin(o, x, y) => T::Bin(o, x + off, y + off),
            other => other,
        }));
        out.push(T::Bin(op, off - 1, out.len() as u16 - 1));
        out
    };
    let mut size = 1u8;
    while best.iter().any(Option::is_none) {
        let mut found: Vec<(usize, Vec<T>)> = Vec::new();
        for f in 0..256usize {
            let Some((tf, sf)) = &best[f] else { continue };
            if *sf + 1 == size {
                let mut t = tf.clone();
                t.push(T::Not(t.len() as u16 - 1));
                found.push((!(f as u8) as usize, t));
            }
            for (g, bg) in best.iter().enumerate().skip(f) {
                let Some((tg, sg)) = bg else { continue };
                if sf + sg + 1 != size {
                    continue;
                }
                for (op, v) in [(BinOp::And, f & g), (BinOp::Or, f | g), (BinOp::Xor, f ^ g)] {
                    found.push((v, concat(tf, tg, op)));
                }
            }
        }
        // For the tables first reached at this size, also the combinations of the operands'
        // other forms (after the forms' own, which decide the form): `(x & y) | ~(y ^ z)` from
        // `~(y ^ z)`, the other form of `~z ^ y`.
        let fresh: Vec<bool> = best.iter().map(Option::is_none).collect();
        let all = |f: usize| -> Vec<&Vec<T>> {
            best[f]
                .iter()
                .map(|(t, _)| t)
                .chain(alts[f].iter())
                .collect()
        };
        let mut more: Vec<(usize, Vec<T>)> = Vec::new();
        for f in 0..256usize {
            let Some((_, sf)) = &best[f] else { continue };
            if *sf + 1 == size && fresh[usize::from(!(f as u8))] {
                for tf in all(f).into_iter().skip(1) {
                    let mut t = tf.clone();
                    t.push(T::Not(t.len() as u16 - 1));
                    more.push((usize::from(!(f as u8)), t));
                }
            }
            for (g, bg) in best.iter().enumerate().skip(f) {
                let Some((_, sg)) = bg else { continue };
                if sf + sg + 1 != size {
                    continue;
                }
                for (op, v) in [(BinOp::And, f & g), (BinOp::Or, f | g), (BinOp::Xor, f ^ g)] {
                    if !fresh[v] {
                        continue;
                    }
                    for (i, tf) in all(f).into_iter().enumerate() {
                        for (j, tg) in all(g).into_iter().enumerate() {
                            if i > 0 || j > 0 {
                                more.push((v, concat(tf, tg, op)));
                            }
                        }
                    }
                }
            }
        }
        found.extend(more);
        // The first template found at a table's size is its form; others of that size are
        // kept as alternatives, the first few found and then those with a subterm (by table) the
        // ones kept so far lack (the forms of the level before stay as they are).
        for (v, t) in found {
            if best[v].is_none() {
                covered[v] = subtables(&t);
                best[v] = Some((t, size));
            } else if fresh[v] && alts[v].len() < 2 * ALTERNATIVES && !alts[v].contains(&t) {
                let subs = subtables(&t);
                let new = subs.iter().any(|s| !covered[v].contains(s));
                if alts[v].len() < ALTERNATIVES && best[v].as_ref().is_some_and(|(b, _)| *b != t)
                    || new
                {
                    covered[v].extend(subs);
                    alts[v].push(t);
                }
            }
        }
        size += 1;
    }
    MinForms {
        forms: best
            .into_iter()
            .map(|b| b.unwrap_or((vec![T::Zero], 0)))
            .collect(),
        alts,
    }
}

/// The truth tables of a template's operators but its root.
pub(crate) fn subtables(t: &[T]) -> Vec<u8> {
    let mut vals: Vec<u8> = Vec::with_capacity(t.len());
    for n in t {
        vals.push(match *n {
            T::Var(k) => VARS[usize::from(k)],
            T::Zero => 0,
            T::Ones => 0xFF,
            T::Not(a) => !vals[usize::from(a)],
            T::Bin(op, a, b) => {
                let (x, y) = (vals[usize::from(a)], vals[usize::from(b)]);
                match op {
                    BinOp::And => x & y,
                    BinOp::Or => x | y,
                    _ => x ^ y,
                }
            }
        });
    }
    let mut out: Vec<u8> = t
        .iter()
        .zip(&vals)
        .take(t.len().saturating_sub(1))
        .filter(|(n, _)| matches!(n, T::Not(_) | T::Bin(..)))
        .map(|(_, &v)| v)
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// A node's bitwise description: its atoms (sorted by index, at most three) and its truth
/// table over them; `None` for a node with more than three atoms.
pub(crate) type Info = Option<(Vec<u32>, u8)>;

/// A node's description over at most [`WIDE`] atoms, read through every bitwise region of at
/// most that many: its atoms (sorted by index) and its table over them, entries past the atoms
/// repeating (over three atoms or fewer, its first eight entries are a table as [`Info`] has).
#[derive(Clone, Copy, Debug)]
pub(crate) struct Wide {
    atoms: [u32; WIDE],
    len: u8,
    tt: u64,
}

impl Wide {
    fn atoms(&self) -> &[u32] {
        &self.atoms[..usize::from(self.len)]
    }
}

/// Drops the atoms `tt` does not depend on.
fn prune(atoms: Vec<u32>, tt: u8) -> (Vec<u32>, u8) {
    let mut keep: Vec<u32> = Vec::new();
    for (k, &a) in atoms.iter().enumerate() {
        let flip = |i: usize| (tt >> (i ^ (1 << k))) & 1 != (tt >> i) & 1;
        if (0..8).any(flip) {
            keep.push(a);
        }
    }
    let tt = remap_down(tt, &atoms, &keep);
    (keep, tt)
}

/// Re-expresses `tt` over `from` as a table over `to`, a subset the function depends on only.
fn remap_down(tt: u8, from: &[u32], to: &[u32]) -> u8 {
    let mut out = 0u8;
    for i in 0..8usize {
        // Place combination `i` of `to` into `from`, with the dropped atoms at 0.
        let mut j = 0usize;
        for (k, a) in to.iter().enumerate() {
            let p = from.iter().position(|b| b == a).unwrap_or(0);
            j |= ((i >> k) & 1) << p;
        }
        out |= ((tt >> j) & 1) << i;
    }
    // Entries for combinations beyond the atoms repeat the pattern (the table is over three
    // variables, unused ones included).
    out
}

/// Re-expresses truth table `tt` over atoms `from` as a table over `to` (a superset).
fn remap(tt: u8, from: &[u32], to: &[u32]) -> u8 {
    let pos: Vec<usize> = from
        .iter()
        .map(|a| to.iter().position(|b| b == a).unwrap_or(0))
        .collect();
    let mut out = 0u8;
    for i in 0..8usize {
        let mut j = 0usize;
        for (k, &p) in pos.iter().enumerate() {
            j |= ((i >> p) & 1) << k;
        }
        out |= ((tt >> j) & 1) << i;
    }
    out
}

fn bitwise_op(op: OpCode) -> bool {
    matches!(op, OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not)
}

/// The description of `root`, computing (iteratively) and caching those below it.
fn info_of(r: &mut Runner<'_, '_>, cx: &Context, root: u32) -> Result<Info, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.bitwise.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        let leaf = |i: u32| -> Info {
            match cx.const_val(i) {
                Some(v) if v.is_zero() => Some((Vec::new(), 0x00)),
                Some(v) if v.is_ones() => Some((Vec::new(), 0xFF)),
                _ => Some((vec![i], VARS[0])),
            }
        };
        if !bitwise_op(node.op) {
            r.bitwise.insert(i, leaf(i));
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if !r.bitwise.contains_key(&c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        let kids: Vec<Info> = node.children().map(|c| r.bitwise[&c].clone()).collect();
        let info = if kids.iter().any(Option::is_none) {
            None
        } else {
            let mut atoms: Vec<u32> = kids
                .iter()
                .flat_map(|k| k.as_ref().map_or(Vec::new(), |k| k.0.clone()))
                .collect();
            atoms.sort_unstable();
            atoms.dedup();
            if atoms.len() > 3 {
                None
            } else {
                let t: Vec<u8> = kids
                    .iter()
                    .map(|k| {
                        let (a, tt) = k.as_ref().map_or((&[][..], 0), |k| (&k.0[..], k.1));
                        remap(tt, a, &atoms)
                    })
                    .collect();
                let tt = match node.op {
                    OpCode::Not => !t[0],
                    OpCode::And => t[0] & t[1],
                    OpCode::Or => t[0] | t[1],
                    _ => t[0] ^ t[1],
                };
                Some(prune(atoms, tt))
            }
        };
        let info = if info.is_none() {
            r.stats.passes.entry("bitwise").or_default().atomized += 1;
            leaf(i)
        } else {
            info
        };
        r.bitwise.insert(i, info);
    }
    Ok(r.bitwise[&root].clone())
}

/// Table `tt` with its variables `a < b` exchanged (a delta swap of the entries that differ).
fn swap_vars(tt: u64, a: usize, b: usize) -> u64 {
    let d = (1u32 << b) - (1u32 << a);
    // Each entry with `a` set and `b` clear, and its partner `d` above.
    let t = ((tt >> d) ^ tt) & WIDE_VARS[a] & !WIDE_VARS[b];
    tt ^ t ^ (t << d)
}

/// Re-expresses wide table `tt` over atoms `from` as a table over `to` (a superset; both sorted
/// by index): each atom's variable moves up to its place in `to`, the highest first, onto a
/// variable the table does not read.
fn remap_wide(tt: u64, from: &[u32], to: &[u32]) -> u64 {
    let mut tt = tt;
    let mut p = to.len();
    for (k, a) in from.iter().enumerate().rev() {
        while to[p - 1] != *a {
            p -= 1;
        }
        p -= 1;
        if p > k {
            tt = swap_vars(tt, k, p);
        }
    }
    tt
}

/// Drops the atoms of `atoms` (sorted by index) that table `tt` does not depend on: each kept
/// atom's variable moves down to its place among them, the lowest first.
fn prune_wide(atoms: &[u32], tt: u64) -> Wide {
    let mut out = Wide {
        atoms: [0; WIDE],
        len: 0,
        tt,
    };
    for (k, &a) in atoms.iter().enumerate() {
        // The table with atom `k` flipped.
        let (v, s) = (WIDE_VARS[k], 1u32 << k);
        if (tt & v) >> s | (tt & !v) << s == tt {
            continue;
        }
        let m = usize::from(out.len);
        if m < k {
            out.tt = swap_vars(out.tt, m, k);
        }
        out.atoms[m] = a;
        out.len += 1;
    }
    out
}

/// The wide description of node `i` as an atom (or a constant).
fn wide_leaf(cx: &Context, i: u32) -> Wide {
    let mut w = Wide {
        atoms: [0; WIDE],
        len: 0,
        tt: 0,
    };
    match cx.const_val(i) {
        Some(v) if v.is_zero() => {}
        Some(v) if v.is_ones() => w.tt = u64::MAX,
        _ => (w.atoms[0], w.len, w.tt) = (i, 1, WIDE_VARS[0]),
    }
    w
}

/// The wide description of bitwise node `i` from its operands' (`b` is `a` for `~`); over more
/// than [`WIDE`] atoms, `i` is an atom.
fn wide_op(cx: &Context, i: u32, a: Wide, b: Wide) -> Wide {
    // The operands' atoms merged, in index order.
    let mut atoms = [0u32; 2 * WIDE];
    let (mut n, mut x, mut y) = (0, a.atoms().iter().peekable(), b.atoms().iter().peekable());
    while let Some(&next) = match (x.peek(), y.peek()) {
        (Some(&&p), Some(&&q)) if p == q => {
            y.next();
            x.next()
        }
        (Some(&&p), Some(&&q)) if q < p => y.next(),
        (Some(_), _) => x.next(),
        (None, _) => y.next(),
    } {
        atoms[n] = next;
        n += 1;
    }
    if n > WIDE {
        return wide_leaf(cx, i);
    }
    let atoms = &atoms[..n];
    let (ta, tb) = (
        remap_wide(a.tt, a.atoms(), atoms),
        remap_wide(b.tt, b.atoms(), atoms),
    );
    let tt = match cx.node(i).op {
        OpCode::Not => !ta,
        OpCode::And => ta & tb,
        OpCode::Or => ta | tb,
        _ => ta ^ tb,
    };
    prune_wide(atoms, tt)
}

/// The wide description of `i` if it needs no computing: cached, an atom, or the three-atom
/// reading's where that reads no region of more than three atoms (the same atoms and function,
/// its table repeated).
fn known_wide(r: &Runner<'_, '_>, cx: &Context, i: u32) -> Option<Wide> {
    if !bitwise_op(cx.node(i).op) {
        return Some(wide_leaf(cx, i));
    }
    if let Some(&w) = r.bitwise_wide.get(&i) {
        return Some(w);
    }
    match r.bitwise.get(&i) {
        Some(Some((atoms, tt)))
            if atoms[..] != [i] && atoms.iter().all(|&a| !bitwise_op(cx.node(a).op)) =>
        {
            let mut w = Wide {
                atoms: [0; WIDE],
                len: atoms.len() as u8,
                tt: u64::from(*tt) * 0x0101_0101_0101_0101,
            };
            w.atoms[..atoms.len()].copy_from_slice(atoms);
            Some(w)
        }
        _ => None,
    }
}

/// The wide description of `root`, computing (iteratively) and caching those below it that
/// [`known_wide`] does not give.
fn wide_of(r: &mut Runner<'_, '_>, cx: &Context, root: u32) -> Result<Wide, Stop> {
    if let Some(w) = known_wide(r, cx, root) {
        return Ok(w);
    }
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.bitwise_wide.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if known_wide(r, cx, c).is_none() {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        let known = |c: u32| known_wide(r, cx, c).expect("operands come first");
        let a = known(node.a);
        let b = if node.op == OpCode::Not {
            a
        } else {
            known(node.b)
        };
        r.bitwise_wide.insert(i, wide_op(cx, i, a, b));
    }
    Ok(r.bitwise_wide[&root])
}

/// Builds the minimum form of `tt` over `atoms` (in the order the table's variables use).
pub(super) fn emit(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    tt: u8,
    atoms: &[u32],
) -> Result<u32, Stop> {
    let (tmpl, _) = &min_forms().forms[tt as usize];
    let w = cx.width_of(atoms.first().copied().unwrap_or(0));
    let mut built: Vec<u32> = Vec::with_capacity(tmpl.len());
    for t in tmpl {
        r.meter.charge(Counter::PassWork, 1)?;
        let id = match *t {
            T::Var(k) => atoms[k as usize],
            T::Zero => r.build(cx, |cx| cx.mk_const(&crate::BitVec::zero(w)))?,
            T::Ones => r.build(cx, |cx| cx.mk_const(&crate::BitVec::ones(w)))?,
            T::Not(a) => {
                let a = built[a as usize];
                r.build(cx, |cx| cx.c_un(UnOp::Not, a))?
            }
            T::Bin(op, a, b) => {
                let (a, b) = (built[a as usize], built[b as usize]);
                r.build(cx, |cx| cx.c_bin(op, a, b))?
            }
        };
        built.push(id);
    }
    r.meter.check()?;
    Ok(*built.last().unwrap_or(&atoms[0]))
}

/// The most distinct constants (other than 0 and all-ones) a masked description splits on.
const MAX_MASKS: usize = 3;

/// The most nodes a masked description walks.
const MAX_MASKED_REGION: usize = 32;

/// Bitwise functions of at most three atoms and some constants (see the module notes): the atoms
/// (sorted by index), and per class of bit positions with one table for each root, the class's
/// positions (classes with equal tables merged) and the tables.
pub(crate) struct Masked {
    atoms: Vec<u32>,
    consts: Vec<u32>,
    classes: Vec<(BitVec, Vec<u8>)>,
    /// The region's operators.
    ops: u32,
}

/// The masked description of `roots` (of one width), if their bitwise region below has at most
/// three atoms and [`MAX_MASKS`] constants.
fn masked(r: &mut Runner<'_, '_>, cx: &Context, roots: &[u32]) -> Result<Option<Masked>, Stop> {
    /// A region node: an atom (its index), a constant (its index), or an operator over slots.
    #[derive(Clone, Copy)]
    enum Slot {
        Atom(usize),
        Const(usize),
        Op(OpCode, usize, usize),
    }
    // The region in post-order (a node's slot after its operands'), at most
    // `MAX_MASKED_REGION` nodes: small enough to search.
    // Fixed buffers: a region visits at most `MAX_MASKED_REGION` nodes, each pushing itself
    // and at most two operands.
    let mut ids = [0u32; MAX_MASKED_REGION];
    let mut slots = [Slot::Atom(0); MAX_MASKED_REGION];
    let mut len = 0usize;
    let (mut atoms, mut consts) = (Vec::with_capacity(3), Vec::with_capacity(2));
    let slot_of = |ids: &[u32], i: u32| ids.iter().position(|&j| j == i);
    let mut stack = [(0u32, false); 3 * MAX_MASKED_REGION + 2];
    let mut top = 0usize;
    for &n in roots.iter().rev() {
        stack[top] = (n, false);
        top += 1;
    }
    let mut visits = 0usize;
    let beyond = loop {
        if top == 0 {
            break false;
        }
        top -= 1;
        let (i, expanded) = stack[top];
        if slot_of(&ids[..len], i).is_some() {
            continue;
        }
        let node = cx.node(i);
        if expanded {
            let a = slot_of(&ids[..len], node.a).unwrap_or(0);
            let b = if node.op == OpCode::Not {
                a
            } else {
                slot_of(&ids[..len], node.b).unwrap_or(0)
            };
            ids[len] = i;
            slots[len] = Slot::Op(node.op, a, b);
            len += 1;
            continue;
        }
        visits += 1;
        if visits > MAX_MASKED_REGION || r.bitwise_beyond.contains_key(&i) {
            break true;
        }
        if !bitwise_op(node.op) {
            let slot = if cx.const_val(i).is_some() {
                consts.push(i);
                Slot::Const(consts.len() - 1)
            } else {
                atoms.push(i);
                Slot::Atom(atoms.len() - 1)
            };
            if atoms.len() > 3 || consts.len() > MAX_MASKS + 2 {
                break true;
            }
            ids[len] = i;
            slots[len] = slot;
            len += 1;
            continue;
        }
        stack[top] = (i, true);
        top += 1;
        for c in node.children() {
            if slot_of(&ids[..len], c).is_none() {
                stack[top] = (c, false);
                top += 1;
            }
        }
    };
    let (ids, slots) = (&ids[..len], &slots[..len]);
    if beyond {
        // So are the regions above a lone root (they contain its region).
        if let [n] = roots {
            r.bitwise_beyond.insert(*n, ());
        }
        r.meter.charge(Counter::PassWork, visits as u64)?;
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, visits as u64)?;
    // Atoms in index order: the tables' variables.
    let mut by_index: Vec<usize> = (0..atoms.len()).collect();
    by_index.sort_unstable_by_key(|&k| atoms[k]);
    let mut var = [0u8; 3];
    for (v, &k) in by_index.iter().enumerate() {
        var[k] = VARS[v];
    }
    atoms.sort_unstable();
    let w = cx.width_of(roots[0]);
    let values: Vec<BitVec> = consts
        .iter()
        .map(|&c| cx.const_val(c).unwrap_or(BitVec::zero(w)))
        .collect();
    // The constants that split: neither 0 nor all-ones.
    let mut splits: Vec<BitVec> = Vec::new();
    for v in &values {
        if !v.is_zero() && !v.is_ones() && !splits.contains(v) {
            splits.push(*v);
        }
    }
    if splits.len() > MAX_MASKS {
        if let [n] = roots {
            r.bitwise_beyond.insert(*n, ());
        }
        return Ok(None);
    }
    let mut classes: Vec<(BitVec, Vec<u8>)> = Vec::new();
    let mut vals: Vec<u8> = vec![0; slots.len()];
    for pattern in 0..1usize << splits.len() {
        // The class's positions: each splitting constant set (or clear) as the pattern says.
        let mut mask = BitVec::ones(w);
        for (k, v) in splits.iter().enumerate() {
            let v = if pattern >> k & 1 == 1 {
                *v
            } else {
                BitVec::un_unchecked(UnOp::Not, v)
            };
            mask = BitVec::bin_unchecked(BinOp::And, &mask, &v);
        }
        if mask.is_zero() {
            continue;
        }
        r.meter
            .charge(Counter::PassWork, slots.len() as u64 / 4 + 1)?;
        // Every slot's table in this class (a constant is all-ones on a class exactly when its
        // bits there are set: the class lies within it or outside it).
        for (k, slot) in slots.iter().enumerate() {
            vals[k] = match *slot {
                Slot::Atom(a) => var[a],
                Slot::Const(c) => {
                    if BitVec::bin_unchecked(BinOp::And, &values[c], &mask) == mask {
                        0xFF
                    } else {
                        0x00
                    }
                }
                Slot::Op(OpCode::Not, a, _) => !vals[a],
                Slot::Op(OpCode::And, a, b) => vals[a] & vals[b],
                Slot::Op(OpCode::Or, a, b) => vals[a] | vals[b],
                Slot::Op(_, a, b) => vals[a] ^ vals[b],
            };
        }
        let tables: Vec<u8> = roots
            .iter()
            .map(|&n| vals[slot_of(ids, n).unwrap_or(0)])
            .collect();
        match classes.iter_mut().find(|(_, t)| *t == tables) {
            Some((m, _)) => *m = BitVec::bin_unchecked(BinOp::Or, m, &mask),
            None => classes.push((mask, tables)),
        }
    }
    let ops = slots.iter().filter(|s| matches!(s, Slot::Op(..))).count() as u32;
    Ok(Some(Masked {
        atoms,
        consts,
        classes,
        ops,
    }))
}

/// Whether `a == b` (of one width) always (`Some(true)`) or never (`Some(false)`) holds, by
/// their masked descriptions: equal tables in every class, or complementary ones in a class.
pub(super) fn equal(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    a: u32,
    b: u32,
) -> Result<Option<bool>, Stop> {
    if !bitwise_op(cx.node(a).op) && !bitwise_op(cx.node(b).op) {
        return Ok(None);
    }
    let Some(m) = masked(r, cx, &[a, b])? else {
        return Ok(None);
    };
    if m.classes.iter().all(|(_, t)| t[0] == t[1]) {
        return Ok(Some(true));
    }
    if m.classes.iter().any(|(_, t)| t[0] == !t[1]) {
        return Ok(Some(false));
    }
    Ok(None)
}

/// The operators and constants a template adds.
fn cost(tt: u8) -> u32 {
    min_forms().forms[tt as usize]
        .0
        .iter()
        .filter(|t| !matches!(t, T::Var(_)))
        .count() as u32
}

/// How a function of two classes is written (see the module notes): `t` on the mask's bits,
/// `u` elsewhere.
#[derive(Clone, Copy)]
enum Split {
    /// `f_t & mask`.
    And(u8),
    /// `f_t | mask` (the mask's bits all-ones).
    Or(u8),
    /// `f_u ^ mask`.
    Xor(u8),
    /// `f_u ^ (f_g & mask)`.
    Blend(u8, u8),
}

/// The bitwise pass at `n` for a function with constants: its masked description written
/// as the module notes say, when that is smaller.
fn masked_step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let Some(m) = masked(r, cx, &[n])? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    if m.consts.is_empty() || m.classes.len() > 2 {
        return Ok(Step::Normal(Fin::FINAL));
    }
    // A rewrite frees at most the region's operators: a form needing as many is not smaller.
    let cheapest = |t: u8| cost(t) + 1;
    let floor = match &m.classes[..] {
        [(_, t)] => cost(t[0]),
        [(_, t), (_, u)] => cheapest(t[0]).min(cheapest(u[0])),
        _ => u32::MAX,
    };
    if floor >= m.ops {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let mut canon = m.atoms.clone();
    canon.sort_by(|a, b| cx.order(*a, *b));
    let tt = |t: u8| remap(t, &m.atoms, &canon);
    let w = cx.width_of(n);
    // Each candidate: the function, its mask, and the nodes it adds (a mask that is not one of
    // the constants already there is one more).
    let is_old = |v: &BitVec| {
        m.consts
            .iter()
            .any(|&c| cx.const_val(c).as_ref() == Some(v))
    };
    let mut best: Option<(u32, Option<(Split, BitVec)>)> = None;
    let mut offer = |c: u32, s: Option<(Split, BitVec)>| {
        if best.as_ref().is_none_or(|(b, _)| c < *b) {
            best = Some((c, s));
        }
    };
    if let [(_, t)] = &m.classes[..] {
        offer(cost(tt(t[0])), None);
    } else {
        for (x, y) in [(0, 1), (1, 0)] {
            let (mask, t) = (m.classes[x].0, tt(m.classes[x].1[0]));
            let u = tt(m.classes[y].1[0]);
            let extra = 1 + u32::from(!is_old(&mask));
            if u == 0x00 {
                offer(cost(t) + extra, Some((Split::And(t), mask)));
            }
            if t == 0xFF {
                offer(cost(u) + extra, Some((Split::Or(u), mask)));
            }
            if t == !u {
                offer(cost(u) + extra, Some((Split::Xor(u), mask)));
            }
            offer(
                cost(u) + cost(t ^ u) + extra + 1,
                Some((Split::Blend(u, t ^ u), mask)),
            );
        }
    }
    let Some((estimate, split)) = best else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    if estimate >= m.ops {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let mut bounds = m.atoms.clone();
    bounds.extend(&m.consts);
    if let Some(f) = worth_building(r, cx, n, &bounds, estimate)? {
        r.stats.passes.entry("bitwise").or_default().rejected_cost += 1;
        return Ok(Step::Normal(Fin::FINAL.and(f)));
    }
    let before = cx.len() as u32;
    let form = |r: &mut Runner<'_, '_>, cx: &mut Context, t: u8| -> Result<u32, Stop> {
        if canon.is_empty() || t == 0x00 || t == 0xFF {
            let v = if t == 0xFF {
                BitVec::ones(w)
            } else {
                BitVec::zero(w)
            };
            r.build(cx, |cx| cx.mk_const(&v))
        } else {
            emit(r, cx, t, &canon)
        }
    };
    let e = match split {
        None => form(r, cx, tt(m.classes[0].1[0]))?,
        Some((split, mask)) => {
            let k = r.build(cx, |cx| cx.mk_const(&mask))?;
            match split {
                Split::And(t) => {
                    let f = form(r, cx, t)?;
                    r.build(cx, |cx| cx.c_bin(BinOp::And, f, k))?
                }
                Split::Or(u) => {
                    let f = form(r, cx, u)?;
                    r.build(cx, |cx| cx.c_bin(BinOp::Or, f, k))?
                }
                Split::Xor(u) => {
                    let f = form(r, cx, u)?;
                    r.build(cx, |cx| cx.c_bin(BinOp::Xor, f, k))?
                }
                Split::Blend(u, g) => {
                    let (f, g) = (form(r, cx, u)?, form(r, cx, g)?);
                    let gm = r.build(cx, |cx| cx.c_bin(BinOp::And, g, k))?;
                    r.build(cx, |cx| cx.c_bin(BinOp::Xor, f, gm))?
                }
            }
        }
    };
    finish(r, cx, PassKind::Bitwise, n, e, before, &bounds, Fin::FINAL)
}

/// Writes the function `tt` of `atoms` (at most three, sorted by index) at `n` as its minimum
/// form, when that is smaller; `fin` is what the node's candidates declined so far contribute.
fn write(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    atoms: &[u32],
    tt: u8,
    fin: Fin,
) -> Result<Step, Stop> {
    // Canonical variable order: the context's order of the atoms, independent of indices.
    let mut canon = atoms.to_vec();
    canon.sort_by(|a, b| cx.order(*a, *b));
    let tt_c = remap(tt, atoms, &canon);
    // Upper bound on new nodes: the template's operators and constants.
    if let Some(f) = worth_building(r, cx, n, atoms, cost(tt_c))? {
        r.stats.passes.entry("bitwise").or_default().rejected_cost += 1;
        return Ok(Step::Normal(fin.and(f)));
    }
    let before = cx.len() as u32;
    // A constant needs a width: when the function ignores every atom, use the node's.
    let e = if canon.is_empty() {
        let w = cx.width_of(n);
        let v = if tt == 0 {
            BitVec::zero(w)
        } else {
            BitVec::ones(w)
        };
        r.build(cx, |cx| cx.mk_const(&v))?
    } else {
        emit(r, cx, tt_c, &canon)?
    };
    finish(r, cx, PassKind::Bitwise, n, e, before, atoms, fin)
}

/// The bitwise pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    if !bitwise_op(cx.node(n).op) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let Some((atoms, tt)) = info_of(r, cx, n)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    // More than three atoms (constants included): `n` is an atom itself, read first by classes
    // of bit positions, where the constants are not atoms.
    let first = if atoms == [n] {
        masked_step(r, cx, n)?
    } else {
        write(r, cx, n, &atoms, tt, Fin::FINAL)?
    };
    let mut fin = match first {
        Step::Normal(f) => f,
        done => return Ok(done),
    };
    // An atom that is a bitwise region of its own may hide that `n` reads three atoms or fewer
    // below it (see the module notes); read over more than six, `n` is an atom again.
    if atoms.iter().any(|&a| bitwise_op(cx.node(a).op)) {
        let wide = wide_of(r, cx, n)?;
        if wide.atoms().len() <= 3 && wide.atoms() != atoms && wide.atoms() != [n] {
            match write(r, cx, n, wide.atoms(), wide.tt as u8, fin)? {
                Step::Normal(f) => fin = f,
                done => return Ok(done),
            }
        }
    }
    Ok(Step::Normal(fin))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `tt` over `from` as a table over `to`, entry by entry.
    fn reference(tt: u64, from: &[u32], to: &[u32]) -> u64 {
        (0..64).fold(0, |out, i| {
            let j = from.iter().enumerate().fold(0, |j, (k, a)| {
                let p = to.iter().position(|b| b == a).unwrap();
                j | ((i >> p) & 1) << k
            });
            out | ((tt >> j) & 1) << i
        })
    }

    /// A random table over `m` variables (its entries repeating past them).
    fn table(state: &mut u64, m: usize) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        (0..64).fold(0, |out, i| out | ((*state >> (i % (1 << m))) & 1) << i)
    }

    /// The atoms of subset `s` of `ids`.
    fn subset(ids: &[u32], s: usize) -> Vec<u32> {
        (0..ids.len())
            .filter(|k| s >> k & 1 == 1)
            .map(|k| ids[k])
            .collect()
    }

    #[test]
    fn wide_tables_move_between_atom_sets() {
        let ids = [3, 5, 8, 9, 12, 20];
        let mut state = 0x7769_6465;
        for big in 0..64usize {
            let to = subset(&ids, big);
            // Every subset of `to`, with tables over it.
            for small in (0..64usize).filter(|s| s & !big == 0) {
                let from = subset(&ids, small);
                for _ in 0..4 {
                    let tt = table(&mut state, from.len());
                    assert_eq!(
                        remap_wide(tt, &from, &to),
                        reference(tt, &from, &to),
                        "{from:?} -> {to:?}, {tt:#x}"
                    );
                }
            }
            // A table over all six that reads exactly `to`: pruning finds `to`, and its table.
            let mut tt = table(&mut state, to.len());
            while (0..to.len()).any(|k| {
                let (v, s) = (WIDE_VARS[k], 1u32 << k);
                (tt & v) >> s | (tt & !v) << s == tt
            }) {
                tt = table(&mut state, to.len());
            }
            let p = prune_wide(&ids, reference(tt, &to, &ids));
            assert_eq!(p.atoms(), &to[..]);
            assert_eq!(p.tt, tt, "{to:?}");
        }
    }
}
