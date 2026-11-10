//! what a condition fixes, put into the operands it guards.
//!
//! Obfuscated case tables can have the form `(x & 52 == c) & C`, where `C` is an MBA over `x`
//! that is 1 whenever `x & 52 == c`. `C` alone does not simplify (72 nodes to 59);
//! with `x`'s bits under 52 written as `c` it folds to 1. The engine never reads one operand
//! of `a & b` under the other, so the table stays. Wherever `a` is 0, `a & b` is 0 whatever `b`
//! is, so `b` may be read where `a` holds: with every node `a` fixes bits of written with
//! those bits. Likewise the arms of `select(c, t, f)` under `c` and under `!c`, and `t` in
//! `zext(c) · t`.
//!
//! [`push`] writes a root so; the engine asks it again and keeps the answer only when it is
//! smaller than the root's own (see `Runner::strategy`).
//!
//! The noise also hides values behind one condition: `rotl(select(c, 0, k) + k2, 51)` masked
//! down is a constant on either side of `c`, often the same one, but no pass evaluates a node
//! at both values of the condition it depends on. [`cut`] finds every piece of a root whose
//! inputs are only conditions (at most [`MAX_CASES`] of them), evaluates it for each value of
//! those conditions, and writes it as the table of those constants: `select(c, v1, v0)`, or
//! `v` where the cases agree.
//!
//! And a root is often far simpler on one side of a condition than it is as a whole: with a
//! flag that picks between two masked values fixed, one of them is a constant and everything
//! computed from it folds. [`sides_on`] is the root on either side, and [`join`] writes the
//! two sides (once the engine has simplified each) as one expression again, the choice as
//! far down as the sides agree (see `Runner::strategy`).

use crate::Error;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, CmpOp, UnOp};

/// Bits of a node a condition fixes: node `x` (at most 64 bits wide) has the bits `mask`
/// equal to `value`.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct Fact {
    x: u32,
    mask: u64,
    value: u64,
}

/// The most conditions [`push`] reads facts from in one root.
const MAX_SITES: usize = 512;

/// All ones at node `i`'s width, when it is at most 64 bits.
fn ones(cx: &Context, i: u32) -> Option<u64> {
    let w = cx.wid(i);
    (w <= 64).then(|| u64::MAX >> (64 - u32::from(w)))
}

/// What 1-bit node `c` being `want` fixes, added to `out`. An unknown shape fixes nothing.
fn fixes(cx: &Context, c: u32, want: bool, out: &mut Vec<Fact>, depth: u32) {
    if depth > 16 || cx.wid(c) != 1 || cx.is_const(c) {
        return;
    }
    let n = cx.node(c);
    match n.op {
        OpCode::Not => fixes(cx, n.a, !want, out, depth + 1),
        OpCode::And if want => {
            fixes(cx, n.a, true, out, depth + 1);
            fixes(cx, n.b, true, out, depth + 1);
        }
        OpCode::Or if !want => {
            fixes(cx, n.a, false, out, depth + 1);
            fixes(cx, n.b, false, out, depth + 1);
        }
        // The comparison itself, and its complement (see [`put`]): `t != 0` in what `t == 0`
        // being false guards.
        OpCode::Eq | OpCode::Ne => {
            out.push(Fact {
                x: c,
                mask: 1,
                value: u64::from(want),
            });
            if (n.op == OpCode::Eq) != want {
                return;
            }
            let (x, k) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => (n.a, k),
                (Some(k), None) => (n.b, k),
                _ => return,
            };
            if let (Some(k), Some(all)) = (k.to_u64(), ones(cx, x)) {
                masked(cx, x, all, k, out, depth + 1);
            }
        }
        _ => out.push(Fact {
            x: c,
            mask: 1,
            value: u64::from(want),
        }),
    }
}

/// `x & mask == value`, read through the shifts, extractions, extensions and masks that pick
/// `x`'s bits from another node's.
fn masked(cx: &Context, x: u32, mask: u64, value: u64, out: &mut Vec<Fact>, depth: u32) {
    if mask == 0 || value & !mask != 0 || cx.is_const(x) {
        return;
    }
    let n = cx.node(x);
    let narrow = |src: u32, by: u16| -> Option<(u64, u64)> {
        // `x`'s bits are `src`'s from `by` up: both moved up by `by`, if none falls off.
        let all = ones(cx, src)?;
        let m = mask.checked_shl(u32::from(by))?;
        (m & all == m && m >> by == mask).then(|| (m, value << by))
    };
    if depth < 16 {
        match n.op {
            OpCode::LShr | OpCode::Extract => {
                let by = match n.op {
                    OpCode::Extract => Some(n.b as u16),
                    _ => cx.const_val(n.b).and_then(|k| k.to_u64()).map(|k| k as u16),
                };
                if let Some((m, v)) = by.and_then(|by| narrow(n.a, by)) {
                    return masked(cx, n.a, m, v, out, depth + 1);
                }
            }
            OpCode::Zext => {
                if let Some(inner) = ones(cx, n.a)
                    && value & !inner == 0
                {
                    return masked(cx, n.a, mask & inner, value, out, depth + 1);
                }
            }
            OpCode::And => {
                let k = cx.const_val(n.b).or_else(|| cx.const_val(n.a));
                let y = if cx.is_const(n.b) { n.a } else { n.b };
                if let Some(k) = k.and_then(|k| k.to_u64()) {
                    return masked(cx, y, mask & k, value & k, out, depth + 1);
                }
            }
            _ => {}
        }
    }
    out.push(Fact { x, mask, value });
}

/// `e` with each node `facts` fix bits of written with those bits: `(x & !mask) | value`,
/// or `value` where every bit is fixed.
fn put(cx: &mut Context, e: u32, facts: &[Fact]) -> Result<u32, Error> {
    if facts.is_empty() {
        return Ok(e);
    }
    let mut merged: Vec<Fact> = Vec::new();
    for f in facts {
        match merged.iter_mut().find(|m| m.x == f.x) {
            // Facts that disagree: the guard never holds, and nothing is put in.
            Some(m) if (m.value ^ f.value) & m.mask & f.mask != 0 => return Ok(e),
            Some(m) => {
                m.value |= f.value;
                m.mask |= f.mask;
            }
            None => merged.push(*f),
        }
    }
    // A comparison fixed fixes its complement: `a != b` is `!(a == b)`.
    let mut more = Vec::new();
    for f in &merged {
        let n = cx.node(f.x);
        if f.mask == 1 && n.width == 1 && matches!(n.op, OpCode::Eq | OpCode::Ne) {
            let other = if n.op == OpCode::Eq {
                CmpOp::Ne
            } else {
                CmpOp::Eq
            };
            let c = cx.c_cmp(other, n.a, n.b)?;
            if c != f.x && !merged.iter().any(|m| m.x == c) && cx.wid(c) == 1 && !cx.is_const(c) {
                more.push(Fact {
                    x: c,
                    mask: 1,
                    value: f.value ^ 1,
                });
            }
        }
    }
    merged.extend(more);
    let mut repl: IdMap<u32, u32> = IdMap::default();
    for f in merged {
        let w = cx.wid(f.x);
        let Some(all) = ones(cx, f.x) else { continue };
        let v = cx.mk_const_u64(w, f.value)?;
        let r = if f.mask == all {
            v
        } else {
            let keep = cx.mk_const_u64(w, all & !f.mask)?;
            let rest = cx.c_bin(BinOp::And, f.x, keep)?;
            cx.c_bin(BinOp::Or, rest, v)?
        };
        repl.insert(f.x, r);
    }
    Ok(cx.substitute_ids(&[e], &repl)?[0])
}

/// `root` with what each condition fixes put into the operands it guards (see the module),
/// or `None` when no condition fixes anything, or the root would grow past `max_new` nodes.
pub(super) fn push(cx: &mut Context, root: u32, max_new: u32) -> Result<Option<u32>, Error> {
    let start = cx.len() as u32;
    let order = cx.post_order_ids(&[root]);
    let mut pushed: IdMap<u32, u32> = IdMap::default();
    let mut sites = 0usize;
    for i in order {
        if cx.len() as u32 - start > max_new {
            return Ok(None);
        }
        let n = cx.node(i);
        let now = |cx: &mut Context, pushed: &IdMap<u32, u32>, e: u32| -> Result<u32, Error> {
            Ok(cx.substitute_ids(&[e], pushed)?[0])
        };
        let new = match n.op {
            OpCode::And if n.width == 1 => {
                let (mut fa, mut fb) = (Vec::new(), Vec::new());
                fixes(cx, n.a, true, &mut fa, 0);
                fixes(cx, n.b, true, &mut fb, 0);
                if fa.is_empty() && fb.is_empty() {
                    continue;
                }
                // One side only: `a & b[a's facts]` is `a & b` (where `a` is 0 both are), but
                // with both sides rewritten, an input where both are 0 can make both 1.
                let (a, b) = (now(cx, &pushed, n.a)?, now(cx, &pushed, n.b)?);
                let b2 = put(cx, b, &fa)?;
                if b2 != b {
                    cx.c_bin(BinOp::And, a, b2)?
                } else {
                    let a2 = put(cx, a, &fb)?;
                    if a2 == a {
                        continue;
                    }
                    cx.c_bin(BinOp::And, a2, b)?
                }
            }
            OpCode::Select => {
                let (mut ft, mut ff) = (Vec::new(), Vec::new());
                fixes(cx, n.a, true, &mut ft, 0);
                fixes(cx, n.a, false, &mut ff, 0);
                if ft.is_empty() && ff.is_empty() {
                    continue;
                }
                let c = now(cx, &pushed, n.a)?;
                let (t, f) = (now(cx, &pushed, n.b)?, now(cx, &pushed, n.c)?);
                let (t2, f2) = (put(cx, t, &ft)?, put(cx, f, &ff)?);
                if (t2, f2) == (t, f) {
                    continue;
                }
                cx.c_select(c, t2, f2)?
            }
            OpCode::Mul => {
                let zext_of = |e: u32| {
                    let m = cx.node(e);
                    (m.op == OpCode::Zext && cx.wid(m.a) == 1).then_some(m.a)
                };
                let (c, t) = match (zext_of(n.a), zext_of(n.b)) {
                    (Some(c), _) => (c, n.b),
                    (None, Some(c)) => (c, n.a),
                    _ => continue,
                };
                let mut fc = Vec::new();
                fixes(cx, c, true, &mut fc, 0);
                if fc.is_empty() {
                    continue;
                }
                let t1 = now(cx, &pushed, t)?;
                let t2 = put(cx, t1, &fc)?;
                if t2 == t1 {
                    continue;
                }
                let z = if t == n.b { n.a } else { n.b };
                let z = now(cx, &pushed, z)?;
                cx.c_bin(BinOp::Mul, z, t2)?
            }
            _ => continue,
        };
        pushed.insert(i, new);
        sites += 1;
        if sites >= MAX_SITES {
            break;
        }
    }
    if pushed.is_empty() {
        return Ok(None);
    }
    let r = cx.substitute_ids(&[root], &pushed)?[0];
    Ok((r != root).then_some(r))
}

/// The condition `root` is split on by [`sides`]: the one most of its selects (and `zext(c)`
/// factors) test, a condition and its complement counted as one, when one is tested twice.
pub(super) fn most_tested(cx: &mut Context, root: u32) -> Result<Option<u32>, Error> {
    let order = cx.post_order_ids(&[root]);
    let mut uses: IdMap<u32, u32> = IdMap::default();
    for &i in &order {
        let n = cx.node(i);
        let c = match n.op {
            OpCode::Select => n.a,
            OpCode::Zext if cx.wid(n.a) == 1 => n.a,
            _ => continue,
        };
        if cx.is_const(c) {
            continue;
        }
        // A comparison and its complement are one condition: the one with the smaller id.
        let c = match cx.node(c).op.as_cmp() {
            Some(_) => c.min(cx.c_un(UnOp::Not, c)?),
            None => c,
        };
        *uses.entry(c).or_default() += 1;
    }
    Ok(uses
        .into_iter()
        .filter(|&(_, k)| k >= 2)
        .max_by_key(|&(c, k)| (k, std::cmp::Reverse(c)))
        .map(|(c, _)| c))
}

/// `root` on either side of the condition [`most_tested`] picks: the condition, `root` with what
/// it fixes put in, and `root` with what its complement fixes put in (see [`put`]);
/// `select(c, t, f)` is `root`. `None` when no condition is tested twice, or neither side
/// changes.
pub(super) fn sides(cx: &mut Context, root: u32) -> Result<Option<(u32, u32, u32)>, Error> {
    let Some(c) = most_tested(cx, root)? else {
        return Ok(None);
    };
    Ok(sides_on(cx, root, c)?.map(|(t, f)| (c, t, f)))
}

/// [`sides`] on the condition `c`: `root` where `c` holds and where it does not, at an input
/// where `c` holds the first is `root`'s value, at any other the second. `None` when neither
/// differs from `root`.
pub(super) fn sides_on(cx: &mut Context, root: u32, c: u32) -> Result<Option<(u32, u32)>, Error> {
    let (mut ft, mut ff) = (Vec::new(), Vec::new());
    fixes(cx, c, true, &mut ft, 0);
    fixes(cx, c, false, &mut ff, 0);
    let (t, f) = (put(cx, root, &ft)?, put(cx, root, &ff)?);
    Ok((t != root || f != root).then_some((t, f)))
}

/// The most conditions a piece [`cut`] reads as a table may depend on.
const MAX_CASES: usize = 2;

/// What a node's value depends on, for [`cut`].
#[derive(Clone, Debug, PartialEq, Eq)]
enum Dep {
    /// An input other than a condition, or more than [`MAX_CASES`] conditions.
    Open,
    /// A condition: a 1-bit node of an open operand, named by its variable (see [`cut`]).
    Cond(u32),
    /// A function of these condition variables (sorted, none for a constant).
    Of(Vec<u32>),
}

impl Dep {
    /// The condition variables a parent reading this node depends on, or `None` when open.
    fn vars(&self) -> Option<&[u32]> {
        match self {
            Dep::Open => None,
            Dep::Cond(v) => Some(std::slice::from_ref(v)),
            Dep::Of(s) => Some(s),
        }
    }
}

/// `root` with every piece that depends on at most [`MAX_CASES`] conditions written as the
/// table of its values (see the module), or `None` when no piece is worth writing so. The
/// pieces' evaluations walk at most `fuel` nodes.
///
/// A condition is a 1-bit node with an operand that is not itself such a function. It and its
/// complement (`a != b` beside `a == b`) are one variable: the spelling met first, with the
/// other's value its negation. A piece is evaluated with the variables written as constants, which
/// the context folds to a constant for each case: the table is exact, at every input.
pub(super) fn cut(cx: &mut Context, root: u32, fuel: u64) -> Result<Option<u32>, Error> {
    let order = cx.post_order_ids(&[root]);
    let mut dep: IdMap<u32, Dep> = IdMap::default();
    // Each variable's complement spelling, and the variable such a spelling negates.
    let mut other: IdMap<u32, u32> = IdMap::default();
    let mut var_of: IdMap<u32, u32> = IdMap::default();
    for &i in &order {
        let n = cx.node(i);
        if cx.is_const(i) {
            dep.insert(i, Dep::Of(Vec::new()));
            continue;
        }
        // Inputs, extension calls and floating point are not folded on constants: open.
        let mut d = if n.op == OpCode::Sym || n.op as u8 > OpCode::Select as u8 {
            None
        } else {
            Some(Vec::new())
        };
        for c in n.children() {
            match (&mut d, dep[&c].vars()) {
                (Some(s), Some(t)) => {
                    for &v in t {
                        if let Err(at) = s.binary_search(&v) {
                            s.insert(at, v);
                        }
                    }
                    if s.len() > MAX_CASES {
                        d = None;
                    }
                }
                _ => d = None,
            }
        }
        let d = match d {
            Some(s) => Dep::Of(s),
            None if n.width == 1 => match var_of.get(&i) {
                Some(&v) => Dep::Cond(v),
                None => {
                    if n.op.as_cmp().is_some() {
                        let not = cx.c_un(UnOp::Not, i)?;
                        if not != i {
                            other.insert(i, not);
                            var_of.insert(not, i);
                        }
                    }
                    Dep::Cond(i)
                }
            },
            None => Dep::Open,
        };
        dep.insert(i, d);
    }
    // The outermost pieces: functions of conditions read by the root or by a node that is not.
    let piece = |dep: &IdMap<u32, Dep>, i: u32| matches!(&dep[&i], Dep::Of(s) if !s.is_empty());
    let mut outer: Vec<u32> = Vec::new();
    for &i in &order {
        if piece(&dep, i) {
            continue;
        }
        for c in cx.node(i).children() {
            if piece(&dep, c) && !outer.contains(&c) {
                outer.push(c);
            }
        }
    }
    if piece(&dep, root) {
        outer.push(root);
    }
    // Pieces by the variables they depend on; each group is evaluated once per case.
    let mut groups: Vec<(Vec<u32>, Vec<u32>)> = Vec::new();
    for &i in &outer {
        let Dep::Of(s) = &dep[&i] else { continue };
        match groups.iter_mut().find(|(g, _)| g == s) {
            Some((_, ps)) => ps.push(i),
            None => groups.push((s.clone(), vec![i])),
        }
    }
    let mut repl: IdMap<u32, u32> = IdMap::default();
    let mut walked = 0u64;
    for (vars, pieces) in groups {
        let cases = 1usize << vars.len();
        // A piece is written as its table only when that is smaller by a margin: a table has
        // at most `cases - 1` selects, and a small piece is the plainer spelling.
        let inner = interior(cx, &dep, &pieces);
        let size: usize = inner.iter().map(|&(n, _)| n).sum();
        walked += (size * cases) as u64;
        if walked > fuel {
            break;
        }
        let (pieces, noisy): (Vec<u32>, Vec<bool>) = pieces
            .into_iter()
            .zip(inner)
            .filter(|&(_, (n, _))| n >= cases + 2)
            .map(|(p, (_, noisy))| (p, noisy))
            .unzip();
        if pieces.is_empty() {
            continue;
        }
        let mut values: Vec<Vec<u32>> = Vec::with_capacity(cases);
        let (zero, one) = (cx.mk_const_u64(1, 0)?, cx.mk_const_u64(1, 1)?);
        for case in 0..cases {
            let mut at: IdMap<u32, u32> = IdMap::default();
            for (j, &v) in vars.iter().enumerate() {
                let set = case >> j & 1 == 1;
                at.insert(v, if set { one } else { zero });
                if let Some(&o) = other.get(&v) {
                    at.insert(o, if set { zero } else { one });
                }
            }
            values.push(cx.substitute_ids(&pieces, &at)?);
        }
        for (k, &p) in pieces.iter().enumerate() {
            if values.iter().any(|vs| !cx.is_const(vs[k])) {
                continue;
            }
            // Bits placed by conditions (`zext(c1) << 2 | zext(c2) << 6`, a flags word) are
            // the form the MBA phase reads best: kept, unless every case is one value.
            if !noisy[k] && values.iter().any(|vs| vs[k] != values[0][k]) {
                continue;
            }
            let t = table(cx, &vars, |case| values[case][k], 0, 0)?;
            if t != p {
                repl.insert(p, t);
            }
        }
    }
    if repl.is_empty() {
        return Ok(None);
    }
    let r = cx.substitute_ids(&[root], &repl)?[0];
    Ok((r != root).then_some(r))
}

/// Per piece, the nodes it is made of above its conditions (constants left out), and whether
/// any of them does more than place bits: arithmetic, a rotate, or a shift by a variable.
fn interior(cx: &Context, dep: &IdMap<u32, Dep>, pieces: &[u32]) -> Vec<(usize, bool)> {
    let mut seen: IdMap<u32, ()> = IdMap::default();
    pieces
        .iter()
        .map(|&p| {
            seen.clear();
            let mut noisy = false;
            let mut stack = vec![p];
            while let Some(i) = stack.pop() {
                if cx.is_const(i)
                    || !matches!(dep.get(&i), Some(Dep::Of(_)))
                    || seen.insert(i, ()).is_some()
                {
                    continue;
                }
                let n = cx.node(i);
                noisy |= match n.op {
                    OpCode::Not
                    | OpCode::And
                    | OpCode::Or
                    | OpCode::Xor
                    | OpCode::Zext
                    | OpCode::Sext
                    | OpCode::Extract
                    | OpCode::Concat
                    | OpCode::Select => false,
                    OpCode::Shl | OpCode::LShr => !cx.is_const(n.b),
                    op => op.as_cmp().is_none(),
                };
                stack.extend(n.children());
            }
            (seen.len(), noisy)
        })
        .collect()
}

/// The table of `value` (by case: variable `j` set is bit `j`) over `vars` from variable
/// `j` on, in the case `case` so far.
fn table(
    cx: &mut Context,
    vars: &[u32],
    value: impl Fn(usize) -> u32 + Copy,
    j: usize,
    case: usize,
) -> Result<u32, Error> {
    if j == vars.len() {
        return Ok(value(case));
    }
    let set = table(cx, vars, value, j + 1, case | 1 << j)?;
    let unset = table(cx, vars, value, j + 1, case)?;
    cx.c_select(vars[j], set, unset)
}

/// The most pairs of nodes [`join`] merges.
const MAX_JOINED: usize = 4096;

/// The deepest [`join`] follows two sides.
const MAX_JOIN_DEPTH: u32 = 512;

/// `select(c, t, f)` with the choice written as far down as the two sides are one operator
/// over operands of the same widths: `select(c, a * k1 + b, a * k2 + b)` is
/// `a * select(c, k1, k2) + b`. Equal to the select at every input: where `c` holds every
/// merged operand is `t`'s, elsewhere `f`'s. A shift or a rotation keeps its amount (two
/// amounts are two operations), and at most [`MAX_JOINED`] pairs of nodes are merged; past
/// that, and where the sides differ in operator, the select is written.
pub(super) fn join(cx: &mut Context, c: u32, t: u32, f: u32) -> Result<u32, Error> {
    fn go(
        cx: &mut Context,
        c: u32,
        (x, y): (u32, u32),
        memo: &mut std::collections::HashMap<(u32, u32), u32>,
        depth: u32,
    ) -> Result<u32, Error> {
        if x == y {
            return Ok(x);
        }
        if let Some(&m) = memo.get(&(x, y)) {
            return Ok(m);
        }
        let (nx, ny) = (cx.node(x), cx.node(y));
        let plain = nx.op.as_un().is_some()
            || nx.op.as_bin().is_some()
            || nx.op.as_cmp().is_some()
            || matches!(
                nx.op,
                OpCode::Zext | OpCode::Sext | OpCode::Extract | OpCode::Concat | OpCode::Select
            );
        let kx: Vec<u32> = nx.children().collect();
        let mut ky: Vec<u32> = ny.children().collect();
        // A commutative operator's operands, paired so that equal ones meet.
        if nx.op.as_bin().is_some_and(BinOp::is_commutative)
            && ky.len() == 2
            && kx[0] != ky[0]
            && kx[1] != ky[1]
            && (kx[0] == ky[1] || kx[1] == ky[0])
        {
            ky.swap(0, 1);
        }
        let amount = matches!(
            nx.op,
            OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR
        );
        let same = plain
            && nx.op == ny.op
            && nx.width == ny.width
            && nx.aux == ny.aux
            && kx.len() == ky.len()
            && (nx.op != OpCode::Extract || nx.b == ny.b)
            && (!amount || kx[1] == ky[1])
            && kx.iter().zip(&ky).all(|(&a, &b)| cx.wid(a) == cx.wid(b))
            && memo.len() < MAX_JOINED
            && depth < MAX_JOIN_DEPTH;
        let out = if same {
            // (An extract keeps its offset in the second field.)
            let mut kids = [nx.a, nx.b, nx.c];
            for (k, (&a, &b)) in kx.iter().zip(&ky).enumerate() {
                kids[k] = go(cx, c, (a, b), memo, depth + 1)?;
            }
            cx.rebuild(x, kids)?
        } else {
            cx.c_select(c, x, y)?
        };
        memo.insert((x, y), out);
        Ok(out)
    }
    let mut memo = std::collections::HashMap::new();
    go(cx, c, (t, f), &mut memo, 0)
}
