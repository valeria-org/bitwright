//! The bitwise pass: a pure bitwise function (`& | ^ ~`, with `0` and all-ones) of at most
//! three atoms is determined by its 8-entry truth table, and is replaced by a minimum-size
//! expression for that table when that is smaller.
//!
//! Bitwise functions act on each bit position independently, so the truth table over single
//! bits (W = 1) determines the function at every width: the table is exact, not an
//! approximation. The minimum forms are found once by a breadth-first search over expression
//! sizes (an immutable cache, computed on first use) and verified exhaustively by the tests.

use std::sync::OnceLock;

use super::{Fin, PassKind, Runner, Step, Stop, finish, worth_building};
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::ops::{BinOp, UnOp};

/// The truth tables of the three atoms: bit `i` is the atom's value in combination `i`, where
/// atom `k` is 1 exactly when bit `k` of `i` is.
const VARS: [u8; 3] = [0xAA, 0xCC, 0xF0];

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
}

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
        for (v, t) in found {
            if best[v].is_none() {
                best[v] = Some((t, size));
            }
        }
        size += 1;
    }
    MinForms {
        forms: best
            .into_iter()
            .map(|b| b.unwrap_or((vec![T::Zero], 0)))
            .collect(),
    }
}

/// A node's bitwise description: its atoms (sorted by index, at most three) and its truth
/// table over them; `None` for a node with more than three atoms.
pub(crate) type Info = Option<(Vec<u32>, u8)>;

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

/// The bitwise pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    if !bitwise_op(cx.node(n).op) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let Some((atoms, tt)) = info_of(r, cx, n)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    if atoms == [n] {
        return Ok(Step::Normal(Fin::FINAL));
    }
    // Canonical variable order: the context's order of the atoms, independent of indices.
    let mut canon = atoms.clone();
    canon.sort_by(|a, b| cx.order(*a, *b));
    let tt_c = remap(tt, &atoms, &canon);
    // Upper bound on new nodes: the template's operators and constants.
    let estimate = min_forms().forms[tt_c as usize]
        .0
        .iter()
        .filter(|t| !matches!(t, T::Var(_)))
        .count() as u32;
    if let Some(f) = worth_building(r, cx, n, &atoms, estimate)? {
        r.stats.passes.entry("bitwise").or_default().rejected_cost += 1;
        return Ok(Step::Normal(Fin::FINAL.and(f)));
    }
    let before = cx.len() as u32;
    // A constant needs a width: when the function ignores every atom, use the node's.
    let e = if canon.is_empty() {
        let w = cx.width_of(n);
        let v = if tt == 0 {
            crate::BitVec::zero(w)
        } else {
            crate::BitVec::ones(w)
        };
        r.build(cx, |cx| cx.mk_const(&v))?
    } else {
        emit(r, cx, tt_c, &canon)?
    };
    finish(r, cx, PassKind::Bitwise, n, e, before, &atoms, Fin::FINAL)
}
