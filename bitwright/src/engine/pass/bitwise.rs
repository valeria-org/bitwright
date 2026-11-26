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
//!
//! *Chains.* A chain of `&` or of `|` over three operands or more is written with its operands
//! in the context's order, each once ([`sort_chain`](super::sort_chain)): one node however it
//! was parenthesized and ordered, also over more atoms than a table reads, so
//! `(a & b & … & g) ^ (g & … & b & a)` is 0. An operand beside its complement decides the chain.

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
        if r.bitwise.info.contains_key(&i) {
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
            r.bitwise.info.insert(i, leaf(i));
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if !r.bitwise.info.contains_key(&c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        let kids: Vec<Info> = node
            .children()
            .map(|c| r.bitwise.info[&c].clone())
            .collect();
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
        r.bitwise.info.insert(i, info);
    }
    Ok(r.bitwise.info[&root].clone())
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

fn wide_select(cx: &Context, i: u32, c: Wide, t: Wide, f: Wide) -> Wide {
    let mut atoms = [0u32; 3 * WIDE];
    let mut vec_atoms = Vec::with_capacity(c.atoms().len() + t.atoms().len() + f.atoms().len());
    vec_atoms.extend_from_slice(c.atoms());
    vec_atoms.extend_from_slice(t.atoms());
    vec_atoms.extend_from_slice(f.atoms());
    vec_atoms.sort_unstable();
    vec_atoms.dedup();
    if vec_atoms.len() > WIDE {
        return wide_leaf(cx, i);
    }
    atoms[..vec_atoms.len()].copy_from_slice(&vec_atoms);
    let atoms = &atoms[..vec_atoms.len()];
    let tc = remap_wide(c.tt, c.atoms(), atoms);
    let tt = remap_wide(t.tt, t.atoms(), atoms);
    let tf = remap_wide(f.tt, f.atoms(), atoms);
    prune_wide(atoms, (tc & tt) | (!tc & tf))
}

fn wide_region_op(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    bitwise_op(n.op) || (n.op == OpCode::Select && n.width == 1)
}

/// The wide description of `i` if it needs no computing: cached, an atom, or the three-atom
/// reading's where that reads no region of more than three atoms (the same atoms and function,
/// its table repeated).
fn known_wide(r: &Runner<'_, '_>, cx: &Context, i: u32) -> Option<Wide> {
    if !wide_region_op(cx, i) {
        return Some(wide_leaf(cx, i));
    }
    if let Some(&w) = r.bitwise.wide.get(&i) {
        return Some(w);
    }
    match r.bitwise.info.get(&i) {
        Some(Some((atoms, tt)))
            if atoms[..] != [i] && atoms.iter().all(|&a| !wide_region_op(cx, a)) =>
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
        if r.bitwise.wide.contains_key(&i) {
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
        let w = if node.op == OpCode::Select {
            wide_select(cx, i, known(node.a), known(node.b), known(node.c))
        } else {
            let a = known(node.a);
            let b = if node.op == OpCode::Not {
                a
            } else {
                known(node.b)
            };
            wide_op(cx, i, a, b)
        };
        r.bitwise.wide.insert(i, w);
    }
    Ok(r.bitwise.wide[&root])
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
    /// Finality of any known-bit facts read on the atoms.
    fin: Fin,
    /// Whether any atom's known bits folded a class.
    used_known: bool,
    /// Known bits of each atom in `atoms` order (populated when `use_known` is set).
    atom_known: [Option<(crate::facts::KnownBits, Fin)>; 3],
}

impl Masked {
    /// The atoms, and each class of bit positions with the first root's table there.
    pub(crate) fn atoms_classes(&self) -> (&[u32], impl Iterator<Item = (&BitVec, u8)>) {
        (&self.atoms, self.classes.iter().map(|(m, t)| (m, t[0])))
    }
}

/// The masked description of `roots` (of one width), if their bitwise region below has at most
/// three atoms and [`MAX_MASKS`] constants.
pub(in crate::engine) fn masked(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    roots: &[u32],
) -> Result<Option<Masked>, Stop> {
    masked_with(r, cx, roots, false)
}

fn masked_with(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    roots: &[u32],
    use_known: bool,
) -> Result<Option<Masked>, Stop> {
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
        if visits > MAX_MASKED_REGION || r.bitwise.beyond.contains_key(&i) {
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
            r.bitwise.beyond.insert(*n, ());
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
            r.bitwise.beyond.insert(*n, ());
        }
        return Ok(None);
    }
    let mut atom_known: [Option<(crate::facts::KnownBits, Fin)>; 3] = [None, None, None];
    if use_known {
        for (k, &a) in atoms.iter().enumerate() {
            if r.assumptions.is_none() && cx.node(a).op == OpCode::Sym {
                continue;
            }
            let (kb, f) = super::known(r, cx, a)?;
            if let Some(kb) = kb
                && !kb.known().is_zero()
            {
                atom_known[k] = Some((kb, f));
            }
        }
    }
    let mut sorted_known: [Option<(crate::facts::KnownBits, Fin)>; 3] = [None, None, None];
    for (v, &k) in by_index.iter().enumerate() {
        sorted_known[v] = atom_known[k];
    }
    atoms.sort_unstable();
    // Without constant masks, split on partial known-bit masks of up to two atoms so
    // disjoint-bit combinations (e.g. `(x >>u 5) | (y << 3)`) can still collapse.
    if use_known && splits.is_empty() {
        for (kb, _) in atom_known.iter().flatten() {
            let m = kb.known();
            if !m.is_zero() && !m.is_ones() && !splits.contains(&m) {
                splits.push(m);
                if splits.len() == 2 {
                    break;
                }
            }
        }
    }
    let mut fin = Fin::FINAL;
    let mut used_known = false;
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
        // bits there are set: the class lies within it or outside it). An atom whose known
        // bits fix every position of this class folds to 0x00 or 0xFF here.
        for (k, slot) in slots.iter().enumerate() {
            vals[k] = match *slot {
                Slot::Atom(a) => match &atom_known[a] {
                    Some((kb, f))
                        if BitVec::bin_unchecked(BinOp::And, &kb.known_zero(), &mask) == mask =>
                    {
                        fin = fin.and(*f);
                        used_known = true;
                        0x00
                    }
                    Some((kb, f))
                        if BitVec::bin_unchecked(BinOp::And, &kb.known_one(), &mask) == mask =>
                    {
                        fin = fin.and(*f);
                        used_known = true;
                        0xFF
                    }
                    _ => var[a],
                },
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
        fin,
        used_known,
        atom_known: sorted_known,
    }))
}

/// Whether `a == b` (of one width) always (`Some(true)`) or never (`Some(false)`) holds, by
/// their masked descriptions: equal tables in every class, or complementary ones in a class.
pub(super) fn equal(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
) -> Result<(Option<bool>, Fin), Stop> {
    if !bitwise_op(cx.node(a).op) && !bitwise_op(cx.node(b).op) {
        return Ok((None, Fin::FINAL));
    }
    let Some(m) = masked_with(r, cx, &[a, b], true)? else {
        return Ok((None, Fin::FINAL));
    };
    if m.classes.iter().all(|(_, t)| t[0] == t[1]) {
        return Ok((Some(true), m.fin));
    }
    if m.classes.iter().any(|(_, t)| t[0] == !t[1]) {
        return Ok((Some(false), m.fin));
    }
    Ok((None, m.fin.unchanged()))
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
    /// A single form valid on every bit position (no mask needed).
    Direct(u8),
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
fn masked_step(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    require_known: bool,
) -> Result<Step, Stop> {
    let Some(m) = masked_with(r, cx, &[n], true)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    if (require_known && !m.used_known) || m.classes.len() > 2 {
        return Ok(Step::Normal(m.fin.unchanged()));
    }
    // A rewrite frees at most the region's operators: a form needing as many is not smaller.
    let floor = match &m.classes[..] {
        [(_, t)] => cost(t[0]),
        [(_, t), (_, u)] => cost(t[0]).min(cost(u[0])),
        _ => u32::MAX,
    };
    if floor >= m.ops {
        return Ok(Step::Normal(m.fin.unchanged()));
    }
    let mut canon = m.atoms.clone();
    canon.sort_by(|a, b| cx.order(*a, *b));
    let tt = |t: u8| remap(t, &m.atoms, &canon);
    let w = cx.width_of(n);
    let mut canon_known: [Option<(crate::facts::KnownBits, Fin)>; 3] = [None, None, None];
    if m.classes.len() == 2 {
        for (k, &a) in canon.iter().enumerate() {
            if let Some(p) = m.atoms.iter().position(|&b| b == a) {
                canon_known[k] = m.atom_known[p];
            }
        }
    }
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
    let mut fin = m.fin;
    if let [(_, t)] = &m.classes[..] {
        offer(cost(tt(t[0])), None);
    } else {
        for (x, y) in [(0, 1), (1, 0)] {
            let (mask, t) = (m.classes[x].0, tt(m.classes[x].1[0]));
            let (other, u) = (m.classes[y].0, tt(m.classes[y].1[0]));
            // If an atom is already known zero on `other` (or known one on `mask`), it agrees
            // with the constant class without needing an explicit `& mask` / `| mask`.
            if u == 0x00
                && let Some(v) = VARS[..canon.len()].iter().position(|&b| b == t)
                && let Some((kb, f)) = &canon_known[v]
                && BitVec::bin_unchecked(BinOp::And, &kb.known_zero(), &other) == other
            {
                fin = fin.and(*f);
                offer(0, Some((Split::Direct(t), mask)));
            }
            if t == 0xFF
                && let Some(v) = VARS[..canon.len()].iter().position(|&b| b == u)
                && let Some((kb, f)) = &canon_known[v]
                && BitVec::bin_unchecked(BinOp::And, &kb.known_one(), &mask) == mask
            {
                fin = fin.and(*f);
                offer(0, Some((Split::Direct(u), mask)));
            }
            if m.consts.is_empty() {
                continue;
            }
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
        return Ok(Step::Normal(fin.unchanged()));
    };
    if estimate >= m.ops {
        return Ok(Step::Normal(fin.unchanged()));
    }
    let mut bounds = m.atoms.clone();
    bounds.extend(&m.consts);
    if let Some(f) = worth_building(r, cx, n, &bounds, estimate)? {
        r.stats.passes.entry("bitwise").or_default().rejected_cost += 1;
        return Ok(Step::Normal(fin.unchanged().and(f)));
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
        Some((Split::Direct(t), _)) => form(r, cx, t)?,
        Some((split, mask)) => {
            let k = r.build(cx, |cx| cx.mk_const(&mask))?;
            match split {
                Split::Direct(_) => unreachable!(),
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
    finish(r, cx, PassKind::Bitwise, n, e, before, &bounds, fin)
}

/// The most nodes a one-atom region walks.
const ONE_ATOM_REGION: usize = 64;

/// The bitwise pass at `n` for a function of one atom and any constants: `(x & a) ^ b`, when
/// that is smaller. Each bit of such a function is 0, 1, the atom's bit or its complement,
/// whatever the constants are, so its value at 0 (`b`) and where that differs from its value
/// at all-ones (`a`) say what it is; the classes of [`masked`] (at most [`MAX_MASKS`]
/// constants, two tables) are not needed.
fn one_atom_step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let w = cx.width_of(n);
    // The region, operands first; its one atom and its constants.
    let mut order: Vec<u32> = Vec::new();
    let mut seen: crate::hash::IdMap<u32, ()> = crate::hash::IdMap::default();
    let mut stack: Vec<(u32, bool)> = vec![(n, false)];
    let (mut atom, mut consts, mut ops) = (None, Vec::new(), 0u32);
    while let Some((i, expanded)) = stack.pop() {
        if expanded {
            order.push(i);
            continue;
        }
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if seen.len() > ONE_ATOM_REGION {
            r.meter.charge(Counter::PassWork, seen.len() as u64)?;
            return Ok(Step::Normal(Fin::FINAL));
        }
        let node = cx.node(i);
        if bitwise_op(node.op) {
            ops += 1;
            stack.push((i, true));
            stack.extend(node.children().map(|c| (c, false)));
        } else if cx.const_val(i).is_some() {
            consts.push(i);
        } else if atom.is_some_and(|a| a != i) {
            r.meter.charge(Counter::PassWork, seen.len() as u64)?;
            return Ok(Step::Normal(Fin::FINAL));
        } else {
            atom = Some(i);
        }
    }
    r.meter.charge(Counter::PassWork, 2 * seen.len() as u64)?;
    let Some(x) = atom else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    // The function at `x = v`.
    let at = |v: BitVec| -> BitVec {
        let mut vals: crate::hash::IdMap<u32, BitVec> = crate::hash::IdMap::default();
        vals.insert(x, v);
        for &c in &consts {
            vals.insert(c, cx.const_val(c).unwrap_or(BitVec::zero(w)));
        }
        for &i in &order {
            let node = cx.node(i);
            let v = match node.op {
                OpCode::Not => BitVec::un_unchecked(UnOp::Not, &vals[&node.a]),
                OpCode::And => BitVec::bin_unchecked(BinOp::And, &vals[&node.a], &vals[&node.b]),
                OpCode::Or => BitVec::bin_unchecked(BinOp::Or, &vals[&node.a], &vals[&node.b]),
                _ => BitVec::bin_unchecked(BinOp::Xor, &vals[&node.a], &vals[&node.b]),
            };
            vals.insert(i, v);
        }
        vals[&n]
    };
    let b = at(BitVec::zero(w));
    let a = BitVec::bin_unchecked(BinOp::Xor, &b, &at(BitVec::ones(w)));
    // The nodes the form adds: a constant alone, else `& a` unless every bit follows the
    // atom, and `^ b` (`~` for all ones) unless no bit is flipped or set.
    let is_old = |v: &BitVec| consts.iter().any(|&c| cx.const_val(c).as_ref() == Some(v));
    let estimate = if a.is_zero() {
        1
    } else {
        let masked = if a.is_ones() {
            0
        } else {
            1 + u32::from(!is_old(&a))
        };
        let flipped = match (b.is_zero(), b.is_ones()) {
            (true, _) => 0,
            (_, true) => 1,
            _ => 1 + u32::from(!is_old(&b)),
        };
        masked + flipped
    };
    if estimate >= ops {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let mut bounds = vec![x];
    bounds.extend(&consts);
    if let Some(f) = worth_building(r, cx, n, &bounds, estimate)? {
        r.stats.passes.entry("bitwise").or_default().rejected_cost += 1;
        return Ok(Step::Normal(Fin::FINAL.and(f)));
    }
    let before = cx.len() as u32;
    let e = r.build(cx, |cx| {
        let ka = cx.mk_const(&a)?;
        let kb = cx.mk_const(&b)?;
        let masked = cx.c_bin(BinOp::And, x, ka)?;
        cx.c_bin(BinOp::Xor, masked, kb)
    })?;
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
    r.explain_with(|| crate::engine::Explanation::Bitwise {
        atoms: atoms.iter().map(|&a| cx.handle(a)).collect(),
        table: u64::from(tt),
    });
    finish(r, cx, PassKind::Bitwise, n, e, before, atoms, fin)
}

/// The most nodes of a bitwise tree [`hoist_cast`] reads.
const HOIST_NODES: usize = 64;

/// The low bits of values as a sum of multiples of the low bits of atoms, modulo a power of
/// two (see [`low_form`]).
#[derive(Default)]
struct Low {
    konst: u64,
    terms: Vec<(u32, u64)>,
}

/// The most nodes [`low_form`] reads for one sum.
const LOW_NODES: usize = 64;

/// Adds `k` times the low `bits` bits of node `i` to `out`, modulo `2^bits` (at most 63):
/// through sums, products and left shifts by constants, and through truncations, extensions
/// and masks that keep those bits; anything else is an atom. `false` past [`LOW_NODES`].
fn low_form(cx: &Context, i: u32, k: u64, bits: u16, out: &mut Low) -> bool {
    let m = (1u64 << bits) - 1;
    let mut todo = vec![(i, k & m)];
    let mut seen = 0usize;
    while let Some((i, k)) = todo.pop() {
        seen += 1;
        if seen > LOW_NODES {
            return false;
        }
        if k == 0 {
            continue;
        }
        let n = cx.node(i);
        let low = |c: u32| {
            cx.const_val(c)
                .map(|v| v.limbs().first().copied().unwrap_or(0) & m)
        };
        let keeps = |x: u32| cx.wid(x) >= bits;
        match n.op {
            OpCode::Const => {
                out.konst = out.konst.wrapping_add(k.wrapping_mul(low(i).unwrap_or(0))) & m
            }
            OpCode::Add => todo.extend([(n.a, k), (n.b, k)]),
            OpCode::Sub => todo.extend([(n.a, k), (n.b, k.wrapping_neg() & m)]),
            OpCode::Neg => todo.push((n.a, k.wrapping_neg() & m)),
            OpCode::Mul if low(n.b).is_some() => {
                todo.push((n.a, k.wrapping_mul(low(n.b).unwrap_or(0)) & m))
            }
            OpCode::Mul if low(n.a).is_some() => {
                todo.push((n.b, k.wrapping_mul(low(n.a).unwrap_or(0)) & m))
            }
            OpCode::Shl
                if cx
                    .const_val(n.b)
                    .and_then(|v| v.to_u64())
                    .is_some_and(|s| s < 64) =>
            {
                let s = cx.const_val(n.b).and_then(|v| v.to_u64()).unwrap_or(0);
                todo.push((n.a, (k << s) & m));
            }
            OpCode::Extract if n.b == 0 => todo.push((n.a, k)),
            OpCode::Zext | OpCode::Sext if keeps(n.a) => todo.push((n.a, k)),
            OpCode::And if low(n.b) == Some(m) => todo.push((n.a, k)),
            OpCode::And if low(n.a) == Some(m) => todo.push((n.b, k)),
            _ => match out.terms.iter_mut().find(|t| t.0 == i) {
                Some(t) => t.1 = t.1.wrapping_add(k) & m,
                None => out.terms.push((i, k)),
            },
        }
    }
    true
}

/// `x << a | x >>u b` (or joined by `^`: the halves share no bit) with counts below the width
/// whose sum is the width or nothing: `rotl(x, a)`. The counts are compared at the width's
/// logarithm as sums of multiples of what they are made of ([`low_form`]), so two spellings
/// of one count meet (`trunc<6>(u·83)` and `trunc<6>(u·109)`, extended, at 64 bits: `u·192`
/// has no low six bits). Constant counts are a rule's.
fn rotation(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let w = node.width;
    if !matches!(node.op, OpCode::Or | OpCode::Xor) || !w.is_power_of_two() || w < 2 {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let (l, s) = match (cx.node(node.a).op, cx.node(node.b).op) {
        (OpCode::Shl, OpCode::LShr) => (cx.node(node.a), cx.node(node.b)),
        (OpCode::LShr, OpCode::Shl) => (cx.node(node.b), cx.node(node.a)),
        _ => return Ok(Step::Normal(Fin::FINAL)),
    };
    let (x, a, b) = (l.a, l.b, s.b);
    if s.a != x || cx.const_val(a).is_some() || cx.const_val(b).is_some() {
        return Ok(Step::Normal(Fin::FINAL));
    }
    r.meter.charge(Counter::PassWork, 1)?;
    // Both counts below the width.
    let bits = w.trailing_zeros() as u16;
    let mut fin = Fin::FINAL;
    for count in [a, b] {
        let (f, g) = super::facts(r, cx, count)?;
        fin = fin.and(g);
        let below = f.is_some_and(|f| (bits..w).all(|i| f.known.known_zero().bit(i) == Some(true)));
        if !below {
            return Ok(Step::Normal(fin));
        }
    }
    // And their sum nothing at the low bits.
    let mut sum = Low::default();
    if !(low_form(cx, a, 1, bits, &mut sum) && low_form(cx, b, 1, bits, &mut sum))
        || sum.konst != 0
        || sum.terms.iter().any(|&(_, k)| k != 0)
    {
        return Ok(Step::Normal(fin));
    }
    let before = cx.len() as u32;
    let e = r.build(cx, |cx| cx.c_bin(BinOp::RotL, x, a))?;
    finish(r, cx, PassKind::Bitwise, n, e, before, &[x, a], fin)
}

/// A bitwise tree (`& | ^ ~`) whose leaves are extensions of one kind from one width `W`, and
/// constants, is the extension of the tree over the operands: `zext(a) & ~zext(b)` is
/// `zext(a & ~b)`, `~zext(a) & lowmask(W)` is `zext(~a)`, `sext(a) | sext(b)` is `sext(a | b)`.
/// Bitwise operators act by position, and a sign extension replicates one position, so a sign
/// extension of the narrow tree is the tree of the sign extensions when every constant's bits
/// from `W − 1` on agree (the tree's bit there is then the narrow result's sign). Above `W`
/// every zero extension is 0, so the wide tree is a constant bit there: 0 gives `zext(f)`, all
/// ones `~zext(~f)`. Committed when smaller: with two or more extensions, or one and a
/// constant it absorbs.
fn hoist_cast(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let u = cx.width_of(n);
    let node = cx.node(n);
    // A bitwise tree masked by `1` (`tree & 1`) observes only bit 0 of each leaf: hoist
    // `zext`/`sext` of 1-bit conditions and constant right shifts (`x >>u k` -> `extract<k, 1>(x)`)
    // into a 1-bit bitwise tree under a single `zext`, so majority/carry expressions unify.
    let is_one_const = |id: u32| cx.const_val(id).and_then(|v| v.to_u64()) == Some(1);
    if node.op == OpCode::And && u.bits() > 1 && (is_one_const(node.a) || is_one_const(node.b)) {
        let inner = if is_one_const(node.b) { node.a } else { node.b };
        if bitwise_op(cx.node(inner).op) {
            let mut b_order: Vec<u32> = Vec::new();
            let mut b_seen: Vec<u32> = Vec::new();
            let mut b_stack: Vec<(u32, bool)> = vec![(inner, false)];
            let mut b_casts = 0usize;
            let mut b_shifts = 0usize;
            let mut b_stops: Vec<u32> = Vec::new();
            let mut ok = true;
            while let Some((i, expanded)) = b_stack.pop() {
                if expanded {
                    b_order.push(i);
                    continue;
                }
                if b_seen.contains(&i) {
                    continue;
                }
                b_seen.push(i);
                if b_seen.len() > HOIST_NODES {
                    ok = false;
                    break;
                }
                let li = cx.node(i);
                if cx.const_val(i).is_some() {
                    continue;
                }
                match li.op {
                    OpCode::Zext | OpCode::Sext if cx.wid(li.a) == 1 => {
                        b_casts += 1;
                        b_stops.push(li.a);
                    }
                    OpCode::LShr
                        if cx
                            .const_val(li.b)
                            .and_then(|v| v.to_u64())
                            .is_some_and(|s| s < u64::from(cx.wid(li.a))) =>
                    {
                        b_shifts += 1;
                        b_stops.push(li.a);
                    }
                    op if bitwise_op(op) => {
                        b_stack.push((i, true));
                        for c in li.children() {
                            b_stack.push((c, false));
                        }
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok && b_casts >= 1 && b_casts + b_shifts >= 2 {
                r.meter.charge(Counter::PassWork, b_order.len() as u64)?;
                let before = cx.len() as u32;
                let mut bit_map: crate::hash::IdMap<u32, u32> = crate::hash::IdMap::default();
                for &i in &b_seen {
                    let li = cx.node(i);
                    if let Some(c) = cx.const_val(i) {
                        let t = c.trunc(crate::Width::W1).map_err(|e| Stop::Error(e.into()))?;
                        bit_map.insert(i, r.build(cx, |cx| cx.mk_const(&t))?);
                    } else if matches!(li.op, OpCode::Zext | OpCode::Sext) && cx.wid(li.a) == 1 {
                        bit_map.insert(i, li.a);
                    } else if li.op == OpCode::LShr {
                        let s = cx.const_val(li.b).unwrap().to_u64().unwrap() as u16;
                        let ex = r.build(cx, |cx| cx.c_extract(li.a, s, 1))?;
                        bit_map.insert(i, ex);
                    }
                }
                for &i in &b_order {
                    let li = cx.node(i);
                    let a = bit_map[&li.a];
                    let bit = if li.op == OpCode::Not {
                        r.build(cx, |cx| cx.c_un(UnOp::Not, a))?
                    } else {
                        let bin = li.op.as_bin().unwrap_or(BinOp::And);
                        let b = bit_map[&li.b];
                        r.build(cx, |cx| cx.c_bin(bin, a, b))?
                    };
                    bit_map.insert(i, bit);
                }
                let mut f = bit_map[&inner];
                if bitwise_op(cx.node(f).op)
                    && let Some(m) = masked_with(r, cx, &[f], false)?
                    && !m.atoms.is_empty()
                    && let Some((_, tables)) = m.classes.first()
                {
                    for &a in &m.atoms {
                        if a < before {
                            b_stops.push(a);
                        }
                    }
                    f = emit(r, cx, tables[0], &m.atoms)?;
                }
                let e = r.build(cx, |cx| cx.c_zext(f, u.bits()))?;
                b_stops.sort_unstable();
                b_stops.dedup();
                match super::finish_with(
                    r,
                    cx,
                    PassKind::Bitwise,
                    n,
                    e,
                    before,
                    &b_stops,
                    Fin::FINAL,
                    true,
                )? {
                    Step::Normal(_) => {}
                    done => return Ok(done),
                }
            }
        }
    }
    // The tree, operands first; its leaves.
    let mut order: Vec<u32> = Vec::new();
    let mut seen: Vec<u32> = Vec::new();
    let mut stack: Vec<(u32, bool)> = vec![(n, false)];
    let mut kind: Option<(OpCode, crate::Width)> = None;
    let mut casts = 0usize;
    let mut consts = 0usize;
    let mut narrow: Vec<u32> = Vec::new();
    while let Some((i, expanded)) = stack.pop() {
        if expanded {
            order.push(i);
            continue;
        }
        if seen.contains(&i) {
            continue;
        }
        seen.push(i);
        if seen.len() > HOIST_NODES {
            return Ok(Step::Normal(Fin::FINAL));
        }
        let node = cx.node(i);
        if cx.const_val(i).is_some() {
            consts += 1;
            continue;
        }
        match node.op {
            OpCode::Zext | OpCode::Sext => {
                let wa = cx.width_of(node.a);
                match kind {
                    Some(k) if k != (node.op, wa) => return Ok(Step::Normal(Fin::FINAL)),
                    _ => kind = Some((node.op, wa)),
                }
                casts += 1;
                narrow.push(node.a);
            }
            op if bitwise_op(op) => {
                stack.push((i, true));
                for c in node.children() {
                    stack.push((c, false));
                }
            }
            _ => return Ok(Step::Normal(Fin::FINAL)),
        }
    }
    let Some((k, w)) = kind else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    if casts < 2 && consts == 0 {
        return Ok(Step::Normal(Fin::FINAL));
    }
    r.meter.charge(Counter::PassWork, order.len() as u64)?;
    // Every constant must agree with the extension: a sign extension of its low `W` bits, or
    // (for a zero extension) any bits, which decide the wide tree's value above `W`.
    let wide = |cx: &Context, i: u32| -> Option<BitVec> {
        let node = cx.node(i);
        if let Some(c) = cx.const_val(i) {
            return Some(c);
        }
        match node.op {
            OpCode::Zext | OpCode::Sext => Some(BitVec::zero(u)),
            _ => None,
        }
    };
    if k == OpCode::Sext {
        for &i in &seen {
            if let Some(c) = cx.const_val(i)
                && c.trunc(w).ok().and_then(|t| t.sext(u).ok()) != Some(c)
            {
                return Ok(Step::Normal(Fin::FINAL));
            }
        }
    }
    let before = cx.len() as u32;
    // The tree at `W` over the operands, and (for a zero extension) at the full width over
    // zeros for its value above `W`.
    let mut low: crate::hash::IdMap<u32, u32> = crate::hash::IdMap::default();
    let mut above: crate::hash::IdMap<u32, BitVec> = crate::hash::IdMap::default();
    for &i in &seen {
        let node = cx.node(i);
        if let Some(c) = cx.const_val(i) {
            let t = c.trunc(w).map_err(|e| Stop::Error(e.into()))?;
            low.insert(i, r.build(cx, |cx| cx.mk_const(&t))?);
            above.insert(i, c);
        } else if matches!(node.op, OpCode::Zext | OpCode::Sext) {
            low.insert(i, node.a);
            above.insert(i, BitVec::zero(u));
        }
    }
    for &i in &order {
        let node = cx.node(i);
        let (a, b) = (low[&node.a], node.b);
        let (va, vb) = (
            above[&node.a],
            wide(cx, node.b).or_else(|| above.get(&node.b).copied()),
        );
        let (l, v) = match node.op {
            OpCode::Not => (
                r.build(cx, |cx| cx.c_un(UnOp::Not, a))?,
                BitVec::un_unchecked(UnOp::Not, &va),
            ),
            op => {
                let bin = op.as_bin().unwrap_or(BinOp::And);
                let Some(vb) = vb else {
                    return Ok(Step::Normal(Fin::FINAL));
                };
                let lb = low[&b];
                (
                    r.build(cx, |cx| cx.c_bin(bin, a, lb))?,
                    BitVec::bin_unchecked(bin, &va, &vb),
                )
            }
        };
        low.insert(i, l);
        above.insert(i, v);
    }
    let f = low[&n];
    let e = if k == OpCode::Sext {
        r.build(cx, |cx| cx.c_sext(f, u.bits()))?
    } else {
        // The wide tree's bits above `W`.
        let v = above[&n];
        let hi = crate::facts::known::bv_lshr(&v, u32::from(w.bits()));
        let span = crate::facts::known::low_mask(u, u32::from(u.bits() - w.bits()));
        if hi.is_zero() {
            r.build(cx, |cx| cx.c_zext(f, u.bits()))?
        } else if hi == span {
            r.build(cx, |cx| {
                let nf = cx.c_un(UnOp::Not, f)?;
                let z = cx.c_zext(nf, u.bits())?;
                cx.c_un(UnOp::Not, z)
            })?
        } else {
            super::discard(r, cx, before);
            return Ok(Step::Normal(Fin::FINAL));
        }
    };
    narrow.sort_unstable();
    narrow.dedup();
    finish(r, cx, PassKind::Bitwise, n, e, before, &narrow, Fin::FINAL)
}

/// `(x | (y & m)) ^ (x & y)` is `x ^ (y & m)` if `x` has no bit
/// outside `m`: the second arm then cancels exactly the overlapping ones.
/// A truth table treating `x` as a free word cannot drop that arm.
fn masked_overlap(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let (join, meet) = match (cx.node(node.a), cx.node(node.b)) {
        (j, m) if j.op == OpCode::Or && m.op == OpCode::And => (j, m),
        (m, j) if j.op == OpCode::Or && m.op == OpCode::And => (j, m),
        _ => return Ok(Step::Normal(Fin::FINAL)),
    };
    for (x, masked) in [(join.a, join.b), (join.b, join.a)] {
        let y = if meet.a == x {
            meet.b
        } else if meet.b == x {
            meet.a
        } else {
            continue;
        };
        let field = cx.node(masked);
        if field.op != OpCode::And || field.a != y || cx.node(field.b).op != OpCode::Const {
            continue;
        }
        let (fits, fm, fx) = super::within(r, cx, field.b, x)?;
        let fin = fm.and(fx);
        if !fits {
            return Ok(Step::Normal(fin));
        }
        let before = cx.len() as u32;
        let e = r.build(cx, |cx| cx.c_bin(BinOp::Xor, x, masked))?;
        return finish(r, cx, PassKind::Bitwise, n, e, before, &[x, masked, y], fin);
    }
    Ok(Step::Normal(Fin::FINAL))
}

/// Whether 1-bit conditions `x` and `y` are exact logical complements (`~`, `==`/`!=`, `<`/`>=`).
pub(super) fn complementary_conds(cx: &Context, x: u32, y: u32) -> bool {
    let (nx, ny) = (cx.node(x), cx.node(y));
    if (nx.op == OpCode::Not && nx.a == y) || (ny.op == OpCode::Not && ny.a == x) {
        return true;
    }
    match (nx.op, ny.op) {
        (OpCode::Eq, OpCode::Ne) | (OpCode::Ne, OpCode::Eq) => {
            (nx.a == ny.a && nx.b == ny.b) || (nx.a == ny.b && nx.b == ny.a)
        }
        (OpCode::Ult, OpCode::Ule)
        | (OpCode::Ule, OpCode::Ult)
        | (OpCode::Slt, OpCode::Sle)
        | (OpCode::Sle, OpCode::Slt) => nx.a == ny.b && nx.b == ny.a,
        _ => false,
    }
}

/// Extract `(cond, true_is_val, val)` from a branchless gated arm (`select(c, v, 0)`,
/// `select(c, 0, v)`, `v * zext(c)`, or `v & sext(c)`).
fn gated_arm(cx: &Context, id: u32) -> Option<(u32, bool, u32)> {
    let n = cx.node(id);
    let is_zero = |x: u32| cx.const_val(x).is_some_and(|v| v.is_zero());
    match n.op {
        OpCode::Select if is_zero(n.c) => Some((n.a, true, n.b)),
        OpCode::Select if is_zero(n.b) => Some((n.a, false, n.c)),
        OpCode::Mul => {
            let (na, nb) = (cx.node(n.a), cx.node(n.b));
            if nb.op == OpCode::Zext && cx.wid(nb.a) == 1 {
                Some((nb.a, true, n.a))
            } else if na.op == OpCode::Zext && cx.wid(na.a) == 1 {
                Some((na.a, true, n.b))
            } else {
                None
            }
        }
        OpCode::And => {
            let (na, nb) = (cx.node(n.a), cx.node(n.b));
            if nb.op == OpCode::Sext && cx.wid(nb.a) == 1 {
                Some((nb.a, true, n.a))
            } else if na.op == OpCode::Sext && cx.wid(na.a) == 1 {
                Some((na.a, true, n.b))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Merge `a | b`, `a ^ b`, or `a + b` when `a` and `b` are complementary gated arms
/// (`select(c, x, 0) | select(!c, y, 0)` or `x * zext(u == k) | y * zext(u != k)`) into `select(c, x, y)`.
pub(super) fn merge_complementary_arms(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    kind: PassKind,
    n: u32,
    lhs: u32,
    rhs: u32,
) -> Result<Option<Step>, Stop> {
    let (Some((c1, p1, v1)), Some((c2, p2, v2))) = (gated_arm(cx, lhs), gated_arm(cx, rhs)) else {
        return Ok(None);
    };
    let choice = if c1 == c2 && p1 != p2 {
        let (t, f) = if p1 { (v1, v2) } else { (v2, v1) };
        Some((c1, t, f))
    } else if complementary_conds(cx, c1, c2) && p1 == p2 {
        let prefer_second = matches!(cx.node(c1).op, OpCode::Not | OpCode::Ne)
            && !matches!(cx.node(c2).op, OpCode::Not | OpCode::Ne);
        if prefer_second {
            let (t, f) = if p2 { (v2, v1) } else { (v1, v2) };
            Some((c2, t, f))
        } else {
            let (t, f) = if p1 { (v1, v2) } else { (v2, v1) };
            Some((c1, t, f))
        }
    } else {
        None
    };
    let Some((cond, t, f)) = choice else {
        return Ok(None);
    };
    let before = cx.len() as u32;
    let e = r.build(cx, |cx| cx.c_select(cond, t, f))?;
    let mut stops = vec![cond, t, f];
    stops.sort_unstable();
    stops.dedup();
    finish(r, cx, kind, n, e, before, &stops, Fin::FINAL).map(Some)
}

/// The bitwise pass at `n`. What a candidate it declines contributes stays in the result (see
/// the linear pass's `step`).
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let op = cx.node(n).op;
    // Collapse diamond nested selects (`select(a, select(b, x, y), x) -> select(a & ~b, y, x)`
    // and symmetric arm matches) into a single `select` over a combined 1-bit guard.
    if op == OpCode::Select {
        let node = cx.node(n);
        let (a, t, f) = (node.a, node.b, node.c);
        let tn = cx.node(t);
        let fn_ = cx.node(f);
        let diamond = if tn.op == OpCode::Select && tn.b == f {
            Some((0u8, t, tn.a, tn.c, f))
        } else if tn.op == OpCode::Select && tn.c == f {
            Some((1u8, t, tn.a, tn.b, f))
        } else if fn_.op == OpCode::Select && fn_.c == t {
            Some((2u8, f, fn_.a, fn_.b, t))
        } else if fn_.op == OpCode::Select && fn_.b == t {
            Some((3u8, f, fn_.a, t, fn_.c))
        } else {
            None
        };
        if let Some((mode, inner_sel, b, arm1, arm2)) = diamond {
            let inner_once = if super::alone(r) {
                true
            } else {
                super::refresh_uses(r, cx)?;
                !r.life.dead.contains(inner_sel)
                    && r.life.live.uses(inner_sel) == Some(1)
                    && !r.life.live_roots.contains(&inner_sel)
            };
            let before = cx.len() as u32;
            let e = r.build(cx, |cx| {
                let g = match mode {
                    0 => {
                        let nb = cx.c_un(UnOp::Not, b)?;
                        cx.c_bin(BinOp::And, a, nb)?
                    }
                    1 => cx.c_bin(BinOp::And, a, b)?,
                    2 => {
                        let na = cx.c_un(UnOp::Not, a)?;
                        cx.c_bin(BinOp::And, na, b)?
                    }
                    _ => cx.c_bin(BinOp::Or, a, b)?,
                };
                cx.c_select(g, arm1, arm2)
            })?;
            let mut stops = Vec::with_capacity(4);
            for id in [a, b, arm1, arm2] {
                if id < before && !cx.is_const(id) && !stops.contains(&id) {
                    stops.push(id);
                }
            }
            let tie = cx.meta[n as usize].tree != u32::MAX
                && cx.meta[e as usize].tree < cx.meta[n as usize].tree;
            let slack = if tie && inner_once { 2 } else { u32::from(tie) };
            return super::finish_within(r, cx, PassKind::Bitwise, n, e, before, &stops, Fin::FINAL, slack);
        }
    }
    if !bitwise_op(op) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    // Reassociate `(x op c1) op c2 -> x op (c1 op c2)` for `op ∈ {And, Or, Xor}` even when
    // `x op c1` has other users (a 1-for-1 DAG size tie that strictly reduces tree depth and
    // unifies constant masks/flips across shared subexpressions).
    if let Some(bop) = match op {
        OpCode::And => Some(BinOp::And),
        OpCode::Or => Some(BinOp::Or),
        OpCode::Xor => Some(BinOp::Xor),
        _ => None,
    } {
        let node = cx.node(n);
        let outer = match (cx.const_val(node.a), cx.const_val(node.b)) {
            (None, Some(c2)) => Some((node.a, c2)),
            (Some(c2), None) => Some((node.b, c2)),
            _ => None,
        };
        if let Some((y, c2)) = outer {
            let yn = cx.node(y);
            if yn.op == op {
                let inner = match (cx.const_val(yn.a), cx.const_val(yn.b)) {
                    (None, Some(c1)) => Some((yn.a, c1)),
                    (Some(c1), None) => Some((yn.b, c1)),
                    _ => None,
                };
                if let Some((x, c1)) = inner {
                    let c = BitVec::bin_unchecked(bop, &c1, &c2);
                    let before = cx.len() as u32;
                    let kc = r.build(cx, |cx| cx.mk_const(&c))?;
                    let e = r.build(cx, |cx| cx.c_bin(bop, x, kc))?;
                    let mut stops = vec![x, kc];
                    stops.sort_unstable();
                    stops.dedup();
                    match super::finish_with(
                        r,
                        cx,
                        PassKind::Bitwise,
                        n,
                        e,
                        before,
                        &stops,
                        Fin::FINAL,
                        true,
                    )? {
                        Step::Normal(_) => {}
                        done => return Ok(done),
                    }
                }
            }
            // Homomorphic shift/rotate reassociation:
            // `sh(x bop c1, s) bop c2 -> sh(x, s) bop (sh(c1, s) bop c2)` for constant `s` and
            // `sh ∈ {Shl, LShr, RotL, RotR}`, folding the two constants across the shift/rotate.
            if let Some(sh_op) = match yn.op {
                OpCode::Shl => Some(BinOp::Shl),
                OpCode::LShr => Some(BinOp::LShr),
                OpCode::RotL => Some(BinOp::RotL),
                OpCode::RotR => Some(BinOp::RotR),
                _ => None,
            } && let Some(s_bv) = cx.const_val(yn.b)
            {
                let inner_n = cx.node(yn.a);
                if inner_n.op == op {
                    let inner_pair = match (cx.const_val(inner_n.a), cx.const_val(inner_n.b)) {
                        (None, Some(c1)) => Some((inner_n.a, c1)),
                        (Some(c1), None) => Some((inner_n.b, c1)),
                        _ => None,
                    };
                    if let Some((x, c1)) = inner_pair {
                        let sh_c1 = BitVec::bin_unchecked(sh_op, &c1, &s_bv);
                        let c_merged = BitVec::bin_unchecked(bop, &sh_c1, &c2);
                        let before = cx.len() as u32;
                        let e = r.build(cx, |cx| {
                            let sh_x = cx.c_bin(sh_op, x, yn.b)?;
                            let kc = cx.mk_const(&c_merged)?;
                            cx.c_bin(bop, sh_x, kc)
                        })?;
                        let mut stops = vec![x, yn.b];
                        stops.sort_unstable();
                        stops.dedup();
                        match super::finish_with(
                            r,
                            cx,
                            PassKind::Bitwise,
                            n,
                            e,
                            before,
                            &stops,
                            Fin::FINAL,
                            true,
                        )? {
                            Step::Normal(_) => {}
                            done => return Ok(done),
                        }
                    }
                }
            }
        }
    }
    let mut pre_fin = Fin::FINAL;
    // Redundant known-bit field splice: `(x & m) | c -> x` (and `(x & m) ^ c -> x` when `c & m == 0`,
    // including `zext<w>(trunc<k>(x)) | c -> x`) whenever `KnownBits(x)` proves every 1-bit of `c`
    // is already 1 in `x` and every cleared bit `~m & ~c` is already 0 in `x`.
    if matches!(op, OpCode::Or | OpCode::Xor)
        && r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(n)))
    {
        let node = cx.node(n);
        let const_side = match (cx.const_val(node.a), cx.const_val(node.b)) {
            (None, Some(c)) if !c.is_zero() => Some((node.a, c)),
            (Some(c), None) if !c.is_zero() => Some((node.b, c)),
            _ => None,
        };
        if let Some((masked_id, c)) = const_side {
            let mn = cx.node(masked_id);
            let w = cx.width_of(n);
            let xm = if mn.op == OpCode::And {
                match (cx.const_val(mn.a), cx.const_val(mn.b)) {
                    (None, Some(m)) => Some((mn.a, m)),
                    (Some(m), None) => Some((mn.b, m)),
                    _ => None,
                }
            } else if mn.op == OpCode::Zext {
                let en = cx.node(mn.a);
                if en.op == OpCode::Extract && en.b == 0 && cx.wid(en.a) == w.bits() {
                    Some((en.a, crate::facts::known::low_mask(w, u32::from(en.width))))
                } else {
                    None
                }
            } else {
                None
            };
            if let Some((x, m)) = xm
                && (op == OpCode::Or || crate::facts::known::bv_and(&c, &m).is_zero())
            {
                let (kb_opt, kfin) = super::known(r, cx, x)?;
                if let Some(kb) = kb_opt {
                    let ko_ok = crate::facts::known::bv_and(
                        &c,
                        &crate::facts::known::bv_not(&kb.known_one()),
                    )
                    .is_zero();
                    let cleared_zeros = crate::facts::known::bv_and(
                        &crate::facts::known::bv_not(&m),
                        &crate::facts::known::bv_not(&c),
                    );
                    let kz_ok = crate::facts::known::bv_and(
                        &cleared_zeros,
                        &crate::facts::known::bv_not(&kb.known_zero()),
                    )
                    .is_zero();
                    if ko_ok && kz_ok {
                        let before = cx.len() as u32;
                        match finish(r, cx, PassKind::Bitwise, n, x, before, &[x], kfin)? {
                            Step::Normal(f) => pre_fin = pre_fin.and(f),
                            done => return Ok(done),
                        }
                    } else {
                        pre_fin = pre_fin.and(kfin.unchanged());
                    }
                }
            }
        }
    }
    if op == OpCode::And {
        let node = cx.node(n);
        // `(x | c_or) & c_and -> (x & (c_and & ~c_or)) | (c_or & c_and)` when `c_or & c_and != 0`.
        let or_and = match (cx.node(node.a).op, cx.const_val(node.b)) {
            (OpCode::Or, Some(c_and)) => Some((node.a, c_and)),
            _ => match (cx.node(node.b).op, cx.const_val(node.a)) {
                (OpCode::Or, Some(c_and)) => Some((node.b, c_and)),
                _ => None,
            },
        };
        if let Some((or_id, c_and)) = or_and {
            let on = cx.node(or_id);
            let or_pair = match (cx.const_val(on.a), cx.const_val(on.b)) {
                (None, Some(c_or)) => Some((on.a, c_or)),
                (Some(c_or), None) => Some((on.b, c_or)),
                _ => None,
            };
            if let Some((x, c_or)) = or_pair {
                let c_keep = BitVec::bin_unchecked(BinOp::And, &c_or, &c_and);
                let c_rem = BitVec::bin_unchecked(
                    BinOp::And,
                    &c_and,
                    &BitVec::un_unchecked(UnOp::Not, &c_or),
                );
                if !c_keep.is_zero() {
                    let before = cx.len() as u32;
                    let e = r.build(cx, |cx| {
                        let kc = cx.mk_const(&c_keep)?;
                        if c_rem.is_zero() {
                            Ok(kc)
                        } else {
                            let rc = cx.mk_const(&c_rem)?;
                            let xm = cx.c_bin(BinOp::And, x, rc)?;
                            cx.c_bin(BinOp::Or, xm, kc)
                        }
                    })?;
                    let stops = if c_rem.is_zero() { vec![] } else { vec![x] };
                    match super::finish_with(
                        r,
                        cx,
                        PassKind::Bitwise,
                        n,
                        e,
                        before,
                        &stops,
                        Fin::FINAL,
                        true,
                    )? {
                        Step::Normal(f) => pre_fin = pre_fin.and(f),
                        done => return Ok(done),
                    }
                }
            }
        }
        let not_const = match (cx.node(node.a).op, cx.const_val(node.b)) {
            (OpCode::Not, Some(c)) if !c.is_zero() && !c.is_ones() => Some((cx.node(node.a).a, c)),
            _ => match (cx.node(node.b).op, cx.const_val(node.a)) {
                (OpCode::Not, Some(c)) if !c.is_zero() && !c.is_ones() => {
                    Some((cx.node(node.b).a, c))
                }
                _ => None,
            },
        };
        if let Some((x, c)) = not_const {
            let (kb_opt, kfin) = super::known(r, cx, x)?;
            if let Some(kb) = kb_opt
                && BitVec::bin_unchecked(BinOp::Or, &kb.known_zero(), &c).is_ones()
            {
                let before = cx.len() as u32;
                let kc = r.build(cx, |cx| cx.mk_const(&c))?;
                let e = r.build(cx, |cx| cx.c_bin(BinOp::Xor, x, kc))?;
                let mut stops = vec![x];
                if kc < before {
                    stops.push(kc);
                }
                match super::finish_with(r, cx, PassKind::Bitwise, n, e, before, &stops, kfin, true)?
                {
                    Step::Normal(f) => pre_fin = pre_fin.and(f),
                    done => return Ok(done),
                }
            } else {
                pre_fin = pre_fin.and(kfin.unchanged());
            }
        }
    }
    // Canonicalize 1-bit Majority `(u & v) | ((u | v) & w)` (even when `u & v` is flattened
    // across `And` leaves, e.g. `(a & x & y) | (((x & y) | a) & c)`) to the 2-node canonical
    // `select(tri[1] ^ tri[2], tri[0], tri[1])` matching `core.select_idioms::select_by_xor_bit`.
    if op == OpCode::Or && cx.wid(n) == 1 {
        let node = cx.node(n);
        let and_leaves = |root: u32| -> Option<Vec<u32>> {
            let mut out = Vec::with_capacity(4);
            let mut st = vec![root];
            while let Some(cur) = st.pop() {
                if out.len() + st.len() > 8 {
                    return None;
                }
                let cn = cx.node(cur);
                if cn.op == OpCode::And {
                    st.push(cn.b);
                    st.push(cn.a);
                } else {
                    out.push(cur);
                }
            }
            out.sort_unstable();
            out.dedup();
            Some(out)
        };
        let mut maj_triple: Option<[u32; 3]> = None;
        for (conj_side, prod_side) in [(node.a, node.b), (node.b, node.a)] {
            let pn = cx.node(prod_side);
            if cx.node(conj_side).op != OpCode::And || pn.op != OpCode::And {
                continue;
            }
            for (or_child, w_child) in [(pn.a, pn.b), (pn.b, pn.a)] {
                let on = cx.node(or_child);
                if on.op != OpCode::Or {
                    continue;
                }
                let (u, v) = (on.a, on.b);
                if let (Some(cl), Some(mut ul), Some(vl)) =
                    (and_leaves(conj_side), and_leaves(u), and_leaves(v))
                {
                    ul.extend(vl);
                    ul.sort_unstable();
                    ul.dedup();
                    if cl == ul {
                        maj_triple = Some([u, v, w_child]);
                        break;
                    }
                }
            }
            if maj_triple.is_some() {
                break;
            }
        }
        if let Some(mut tri) = maj_triple {
            tri.sort_by(|&a, &b| cx.order(a, b));
            let before = cx.len() as u32;
            let e = if tri[0] == tri[1] {
                tri[0]
            } else if tri[1] == tri[2] {
                tri[1]
            } else {
                r.build(cx, |cx| {
                    let x = cx.c_bin(BinOp::Xor, tri[1], tri[2])?;
                    cx.c_select(x, tri[0], tri[1])
                })?
            };
            let mut stops = tri.to_vec();
            stops.sort_unstable();
            stops.dedup();
            match super::finish_with(r, cx, PassKind::Bitwise, n, e, before, &stops, Fin::FINAL, true)?
            {
                Step::Normal(_) => {}
                done => return Ok(done),
            }
        }
    }
    if matches!(op, OpCode::And | OpCode::Or | OpCode::Xor) {
        let node = cx.node(n);
        let (na, nb) = (cx.node(node.a), cx.node(node.b));
        if na.op == OpCode::Select && nb.op == OpCode::Select && na.a == nb.a {
            let bin_op = op.as_bin().unwrap_or(BinOp::Or);
            let before = cx.len() as u32;
            let e = r.build(cx, |cx| {
                let t = cx.c_bin(bin_op, na.b, nb.b)?;
                let f = cx.c_bin(bin_op, na.c, nb.c)?;
                cx.c_select(na.a, t, f)
            })?;
            let mut stops = Vec::with_capacity(5);
            for id in [na.a, na.b, na.c, nb.b, nb.c] {
                if id < before && !cx.is_const(id) && !stops.contains(&id) {
                    stops.push(id);
                }
            }
            match super::finish_with(r, cx, PassKind::Bitwise, n, e, before, &stops, Fin::FINAL, true)?
            {
                Step::Normal(f) => pre_fin = pre_fin.and(f),
                done => return Ok(done),
            }
        }
    }
    if matches!(op, OpCode::Or | OpCode::Xor) {
        let node = cx.node(n);
        if let Some(step) =
            merge_complementary_arms(r, cx, PassKind::Bitwise, n, node.a, node.b)?
        {
            match step {
                Step::Normal(f) => pre_fin = pre_fin.and(f),
                done => return Ok(done),
            }
        }
    }
    let hoisted = match hoist_cast(r, cx, n)? {
        Step::Normal(f) => pre_fin.and(f),
        done => return Ok(done),
    };
    let hoisted = match rotation(r, cx, n)? {
        Step::Normal(f) => hoisted.and(f),
        done => return Ok(done),
    };
    let hoisted = if cx.node(n).op == OpCode::Xor {
        match masked_overlap(r, cx, n)? {
            Step::Normal(f) => hoisted.and(f),
            done => return Ok(done),
        }
    } else {
        hoisted
    };
    let Some((atoms, tt)) = info_of(r, cx, n)? else {
        return Ok(Step::Normal(hoisted));
    };
    // More than three atoms (constants included): `n` is an atom itself, read first by classes
    // of bit positions, where the constants are not atoms.
    let first = if atoms == [n] {
        match masked_step(r, cx, n, false)? {
            Step::Normal(f) => match one_atom_step(r, cx, n)? {
                Step::Normal(g) => Step::Normal(f.and(g)),
                done => done,
            },
            done => done,
        }
    } else {
        match write(r, cx, n, &atoms, tt, Fin::FINAL)? {
            Step::Normal(f)
                if cx.node(n).children().any(|c| bitwise_op(cx.node(c).op))
                    && (cx.node(n).op == OpCode::Xor
                        || atoms.iter().any(|&a| {
                            cx.const_val(a)
                                .is_some_and(|v| !v.is_zero() && !v.is_ones())
                        })) =>
            {
                match masked_step(r, cx, n, true)? {
                    Step::Normal(g) => {
                        let nonconst = atoms
                            .iter()
                            .filter(|&&a| !bitwise_op(cx.node(a).op) && cx.const_val(a).is_none())
                            .count();
                        if nonconst <= 1 && atoms.len() >= 3 {
                            match one_atom_step(r, cx, n)? {
                                Step::Normal(h) => Step::Normal(f.and(g).and(h)),
                                done => done,
                            }
                        } else {
                            Step::Normal(f.and(g))
                        }
                    }
                    done => done,
                }
            }
            done => done,
        }
    };
    let mut fin = match first {
        Step::Normal(f) => f.and(hoisted),
        done => return Ok(done),
    };
    // An atom that is a bitwise region of its own may hide that `n` reads three atoms or fewer
    // below it (see the module notes); read over more than six, `n` is an atom again.
    if atoms.iter().any(|&a| wide_region_op(cx, a)) {
        let wide = wide_of(r, cx, n)?;
        if wide.atoms().len() <= 3 && wide.atoms() != atoms && wide.atoms() != [n] {
            match write(r, cx, n, wide.atoms(), wide.tt as u8, fin)? {
                Step::Normal(f) => fin = f,
                done => return Ok(done),
            }
        }
    }
    // A chain of `&` or `|` no table reads whole, its operands in order (see `sort_chain`).
    if !matches!(cx.node(n).op, OpCode::And | OpCode::Or) {
        return Ok(Step::Normal(fin));
    }
    Ok(match super::sort_chain(r, cx, PassKind::Bitwise, n)? {
        Step::Normal(f) => Step::Normal(fin.and(f)),
        done => done,
    })
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

/// The pass's state for a call.
#[derive(Default)]
pub(crate) struct State {
    /// The bitwise pass's truth tables, per node.
    pub(crate) info: crate::hash::IdMap<u32, Info>,
    /// The bitwise pass's tables over up to six atoms, per node (read where three hide some).
    pub(crate) wide: crate::hash::IdMap<u32, Wide>,
    /// Nodes whose bitwise region is beyond the bitwise pass's reading with constants (see
    /// `pass::bitwise`): so is every region above them.
    pub(crate) beyond: crate::hash::IdMap<u32, ()>,
}
