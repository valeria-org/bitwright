//! Limbs of one word in a linear form, read back as the word.
//!
//! Arithmetic done limb by limb multiplies each limb of a word by a constant of its own and
//! adds the products: `lo(W)·K + hi(W)·(K << k)` is `W·K`, since `W = lo(W) + 2^k·hi(W)`. A
//! term `c·t` of a form modulo `2^j` whose atom `t` is some bits of a value `B` (`B & (2^k −
//! 1)`, `B >>u k`, `zext(extract<k, n>(B))`, a digit of a digit, the bits a `concat` or an
//! extension passes on) puts the coefficient `c·2^(p − lo)` on each bit `p` of `B` it reads,
//! and only the low `j − ctz(c)` bits of `t` are read at all (a coefficient whose trailing
//! zeros discard the atom's high bits reads a narrower slice: `sext(B) >>s k` under `K << k` is
//! the high limb of `B`). The coefficients of all terms that read one value are added bit by
//! bit, and the bits covered again by the fewest slices: a run of bits whose coefficients
//! double from one to the next is one term, its slice times the run's first coefficient. So
//! any number of limbs join, in any spelling, and so do `W − lo(W)` (`hi(W) << k`) and a
//! product of the word beside a product of one limb.
//!
//! A `concat` is read as the bits of its halves, so limbs put together again from the pieces
//! of a word (`concat(zext(trunc<3>(m)), l)` beside the word `concat(h, concat(m, l))`) are
//! bits of the same values. Runs that follow one another through the pieces of a `concat`
//! (or of a sign extension) some term reads, their coefficients doubling across, are one run
//! of that node: the word, where the limbs were joined by a `concat`.
//!
//! A bitwise function of two slices cut at the same bits is that slice of the function of
//! the words (`hi(a) ^ hi(b)` is `hi(a ^ b)`, bit by bit), so a high limb the casts pass has
//! pushed into the operands of an `^` joins the low limb cut from the word. For a caller
//! that asks ([`joined_over`]), a slice of a sum is a slice of another sum read that is the
//! same linear form modulo `2^o`, `o` the slice's top: one word computed at several widths
//! (in a 32-bit register, narrowed to its low limb, over an extension for a wider reader).
//!
//! Every step is an identity of the integers modulo `2^j` and nothing is proved; the one
//! fact read is where an operand of an `^` or `|` is known 0, so that the other operand's
//! bits there are the node's (the top limb of `x ^ (x >>u s)` written as that of `x`). The
//! terms over values the reading connects are replaced only when they get fewer.

use super::forms::Parts;
use super::linear::{self, Form};
use super::{Fin, PassKind, Runner, Step, Stop, casts, discard, finish};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::ops::BinOp;

/// The most pieces one atom is read as (a `concat` of more is read whole).
const MAX_PIECES: usize = 8;

/// The most nodes that pass bits of several values on (`concat`s, sign extensions) kept as
/// candidates for a run.
const MAX_TOPS: usize = 16;

/// The most `^` and `|` nodes whose operands' pieces are read as their own (where the other
/// operand is known 0).
const MAX_OVER: usize = 4;

/// The most sums read whose low bits are compared (one word computed at several widths).
const MAX_WORDS: usize = 4;

/// Bits `[lo, lo + len)` of `base`, at bit `at` of the value read.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Piece {
    base: u32,
    lo: u16,
    len: u16,
    at: u16,
}

fn low(n: u16) -> u64 {
    if n >= 64 { u64::MAX } else { (1u64 << n) - 1 }
}

/// Whether `y` passes on bits of other values without being all of one ([`pieces`] reads it
/// through, or stops at it): a candidate for a run over several values.
fn top(cx: &Context, y: u32) -> bool {
    matches!(cx.node(y).op, OpCode::Concat | OpCode::Sext)
}

/// Bits `[lo, lo + len)` of `x` (within its width) as pieces of the values below it, read
/// through what only moves bits: zero and sign extensions, slices, shifts by constants, masks
/// of one run of bits and `concat`s. The bits no piece covers are 0. Each `concat` and sign
/// extension met goes into `tops`.
fn pieces(cx: &Context, x: u32, lo: u16, len: u16, out: &mut Vec<Piece>, tops: &mut Vec<u32>) {
    let start = out.len();
    let mut stack = vec![(x, lo, len, 0u16)];
    while let Some((mut x, mut lo, mut len, mut at)) = stack.pop() {
        while len > 0 {
            let n = cx.node(x);
            let w = n.width;
            if top(cx, x) && tops.len() < MAX_TOPS && !tops.contains(&x) {
                tops.push(x);
            }
            match n.op {
                OpCode::Zext => {
                    let wa = cx.wid(n.a);
                    if lo >= wa {
                        len = 0;
                        break;
                    }
                    len = len.min(wa - lo);
                    x = n.a;
                }
                OpCode::Sext if lo + len <= cx.wid(n.a) => x = n.a,
                OpCode::Extract => {
                    lo += n.b as u16;
                    x = n.a;
                }
                OpCode::LShr | OpCode::AShr | OpCode::Shl => {
                    let Some(k) = cx.const_val(n.b).and_then(|k| k.to_u64()) else {
                        break;
                    };
                    if k >= u64::from(w) {
                        if n.op != OpCode::AShr {
                            len = 0;
                        }
                        break;
                    }
                    let k = k as u16;
                    match n.op {
                        OpCode::LShr => {
                            if lo + k >= w {
                                len = 0;
                                break;
                            }
                            len = len.min(w - lo - k);
                            lo += k;
                        }
                        OpCode::AShr => {
                            if lo + k + len > w {
                                break;
                            }
                            lo += k;
                        }
                        _ => {
                            if lo >= k {
                                lo -= k;
                            } else {
                                // The window's low bits are the zeros shifted in.
                                let z = k - lo;
                                if z >= len {
                                    len = 0;
                                    break;
                                }
                                at += z;
                                len -= z;
                                lo = 0;
                            }
                        }
                    }
                    x = n.a;
                }
                OpCode::And if w <= 64 => {
                    let (a, m) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                        (None, Some(m)) => (n.a, m),
                        (Some(m), None) => (n.b, m),
                        _ => break,
                    };
                    let m = (m.limbs()[0] >> lo) & low(len);
                    if m == 0 {
                        len = 0;
                        break;
                    }
                    let z = m.trailing_zeros() as u16;
                    let run = (m >> z).trailing_ones() as u16;
                    if run < 64 && (m >> z) >> run != 0 {
                        break;
                    }
                    at += z;
                    lo += z;
                    len = run;
                    x = a;
                }
                OpCode::Concat => {
                    let wl = cx.wid(n.b);
                    if lo + len <= wl {
                        x = n.b;
                    } else if lo >= wl {
                        lo -= wl;
                        x = n.a;
                    } else if out.len() - start + stack.len() + 2 > MAX_PIECES {
                        break;
                    } else {
                        stack.push((n.a, 0, lo + len - wl, at + (wl - lo)));
                        len = wl - lo;
                        x = n.b;
                    }
                }
                _ => break,
            }
        }
        if len > 0 {
            out.push(Piece {
                base: x,
                lo,
                len,
                at,
            });
        }
    }
    out[start..].sort_unstable_by_key(|p| p.at);
}

/// A run of bits of one value whose coefficients double: `c` on bit `lo`.
#[derive(Clone, Copy, Debug)]
struct Run {
    base: u32,
    lo: u16,
    len: u16,
    c: u64,
    /// Whether no bit above the run is read under `c` (the slice may be any wider).
    open: bool,
    /// The terms it stands for: an index into the components.
    of: usize,
    /// Taken into a run of a node above.
    used: bool,
}

/// The fewest runs that give each bit of `base` the sum of the coefficients put on it by
/// `on`, the pieces of it with each one's coefficient at its low bit, modulo `2^j`.
fn runs(base: u32, on: &[(Piece, u64)], j: u16, out: &mut Vec<Run>) {
    let mask = low(j);
    let mut cuts: Vec<u16> = Vec::with_capacity(2 * on.len());
    for (p, _) in on {
        cuts.push(p.lo);
        cuts.push(p.lo + p.len);
    }
    cuts.sort_unstable();
    cuts.dedup();
    let shl = |c: u64, by: u16| if by >= 64 { 0 } else { (c << by) & mask };
    let first = out.len();
    for s in cuts.windows(2) {
        let (from, to) = (s[0], s[1]);
        let c = on
            .iter()
            .filter(|(p, _)| p.lo <= from && to <= p.lo + p.len)
            .fold(0u64, |c, (p, k)| {
                c.wrapping_add(shl(*k, from - p.lo)) & mask
            });
        if c == 0 {
            continue;
        }
        match out[first..].last_mut() {
            Some(run) if run.lo + run.len == from && shl(run.c, run.len) == c => {
                run.len = to - run.lo;
            }
            _ => out.push(Run {
                base,
                lo: from,
                len: to - from,
                c,
                open: false,
                of: 0,
                used: false,
            }),
        }
    }
    for run in &mut out[first..] {
        clip(run, j);
    }
}

/// Only the low `j − ctz(c)` bits of a slice under `c` are read.
fn clip(run: &mut Run, j: u16) {
    let read = j - run.c.trailing_zeros() as u16;
    if run.len >= read {
        run.len = read;
        run.open = true;
    }
}

/// Bits `[lo, lo + len)` of `base` zero-extended to `w` bits, or any value equal to that on
/// its low `len` bits when `open`: the value itself where that is one.
fn slice(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    base: u32,
    lo: u16,
    len: u16,
    open: bool,
    w: u16,
) -> Result<u32, Stop> {
    let wb = cx.wid(base);
    // Up to the value's top (zeros above), or past the run where nothing reads.
    let whole = open || lo + len == wb;
    let take = if whole { (wb - lo).min(w) } else { len };
    r.build(cx, |cx| {
        if wb == w && whole {
            if lo == 0 {
                return Ok(base);
            }
            let k = cx.mk_const(&BitVec::wrapping_from_u64(cx.width_of(base), u64::from(lo)))?;
            return cx.c_bin(BinOp::LShr, base, k);
        }
        if wb == w && lo == 0 {
            let m = cx.mk_const(&BitVec::wrapping_from_u64(cx.width_of(base), low(len)))?;
            return cx.c_bin(BinOp::And, base, m);
        }
        let e = if lo == 0 && take == wb {
            base
        } else {
            cx.c_extract(base, lo, take)?
        };
        if take < w { cx.c_zext(e, w) } else { Ok(e) }
    })
}

fn find(up: &mut [usize], mut i: usize) -> usize {
    while up[i] != i {
        up[i] = up[up[i]];
        i = up[i];
    }
    i
}

fn union(up: &mut [usize], a: usize, b: usize) {
    let (a, b) = (find(up, a), find(up, b));
    up[a.max(b)] = a.min(b);
}

/// Whether `a` and `b` have the same low `o` bits, by their forms narrowed to them; `fin`
/// takes what that relied on.
pub(super) fn same_low(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
    o: u16,
    fin: &mut Fin,
) -> Result<bool, Stop> {
    if o == 0 || o > cx.wid(a) || o > cx.wid(b) {
        return Ok(false);
    }
    let (Some((x, fx, _)), Some((y, fy, _))) = (
        casts::narrowed_from(r, cx, a, 0, o)?,
        casts::narrowed_from(r, cx, b, 0, o)?,
    ) else {
        return Ok(false);
    };
    let (f, g) = (linear::form_of(r, cx, x)?, linear::form_of(r, cx, y)?);
    if x != y && (f.parts().0 != g.parts().0 || f.parts().1 != g.parts().1) {
        return Ok(false);
    }
    *fin = fin.and(fx).and(fy).and(f.fin).and(g.fin);
    Ok(true)
}

/// `form` modulo `2^j` with the terms that are bits of one value joined (see the module), and
/// the nodes the commit rule's region stops at; `None` when no terms get fewer.
pub(super) fn joined(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    form: &Form,
    j: u16,
) -> Result<Option<(Form, Vec<u32>)>, Stop> {
    joined_over(r, cx, form, j, false)
}

/// [`joined`], with `spellings` also over the sums that are one word computed at several
/// widths.
pub(super) fn joined_over(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    form: &Form,
    j: u16,
    spellings: bool,
) -> Result<Option<(Form, Vec<u32>)>, Stop> {
    let (konst, terms, fin) = form.parts();
    let width = konst.width();
    let w = width.bits();
    if w > 64 || j == 0 || j > w || terms.len() < 2 {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, terms.len() as u64)?;
    // (What the readings below build, the words of bitwise functions and the sums narrowed,
    // is taken back where nothing joins.)
    let before = cx.len() as u32;
    let mask = low(j);
    let shl = |c: u64, by: u16| if by >= 64 { 0 } else { (c << by) & mask };
    // Each term's atom as pieces, on the bits its coefficient reads; the terms in the
    // canonical order (which nodes are kept as candidates then does not depend on indices).
    let mut terms = terms.to_vec();
    terms.sort_by(|a, b| cx.order(a.0, b.0));
    let mut read: Vec<(u32, u64, core::ops::Range<usize>)> = Vec::with_capacity(terms.len());
    let mut all: Vec<Piece> = Vec::with_capacity(terms.len());
    let mut tops: Vec<u32> = Vec::new();
    for &(atom, k) in &terms {
        let c = k.limbs()[0] & mask;
        if c == 0 {
            continue;
        }
        let from = all.len();
        let bits = cx.wid(atom).min(j - c.trailing_zeros() as u16);
        pieces(cx, atom, 0, bits, &mut all, &mut tops);
        read.push((atom, c, from..all.len()));
    }
    // A piece of a value that a node some term reads whole passes on is a piece of that
    // node (the low limb of `B` beside bits of `sext(B)` from above `B`'s top), the widest
    // such node first; a node of nodes once per level, three at most.
    let deep: Vec<u32> = all.iter().map(|p| p.base).collect();
    tops.sort_by(|a, b| cx.wid(*b).cmp(&cx.wid(*a)).then(cx.order(*a, *b)));
    let mut through: Vec<Piece> = Vec::new();
    for _ in 0..3 {
        let mut lifted = false;
        for &y in &tops {
            if !all.iter().any(|p| p.base == y) {
                continue;
            }
            through.clear();
            let wy = match cx.node(y).op {
                OpCode::Sext => cx.wid(cx.node(y).a),
                _ => cx.wid(y),
            };
            pieces(cx, y, 0, wy, &mut through, &mut Vec::new());
            for p in &mut all {
                if let Some(q) = through.iter().find(|q| {
                    q.base == p.base && q.base != y && p.lo >= q.lo && p.lo + p.len <= q.lo + q.len
                }) {
                    p.base = y;
                    p.lo = q.at + (p.lo - q.lo);
                    lifted = true;
                }
            }
        }
        if !lifted {
            break;
        }
    }
    // A piece of a bitwise function of two slices is a piece of the function of the words
    // (`hi(a) ^ hi(b)` is `hi(a ^ b)`: the casts pass pushes a slice into `^`, `|` and `&`,
    // while the low limb beside it is cut from the word itself).
    let mut fns: Vec<u32> = all
        .iter()
        .map(|p| p.base)
        .filter(|&b| {
            matches!(cx.node(b).op, OpCode::Xor | OpCode::Or | OpCode::And) && cx.wid(b) <= 64
        })
        .collect();
    fns.sort_by(|a, b| cx.order(*a, *b));
    fns.dedup();
    fns.truncate(MAX_OVER);
    for &y in &fns {
        let n = cx.node(y);
        let op = match n.op {
            OpCode::Xor => BinOp::Xor,
            OpCode::Or => BinOp::Or,
            _ => BinOp::And,
        };
        let mut one = |v: u32| {
            through.clear();
            pieces(cx, v, 0, n.width, &mut through, &mut Vec::new());
            match through[..] {
                [p] if p.at == 0 && p.len == n.width && p.base != v => Some(p),
                _ => None,
            }
        };
        let (Some(pa), Some(pb)) = (one(n.a), one(n.b)) else {
            continue;
        };
        let w = cx.wid(pa.base).min(cx.wid(pb.base));
        if pa.lo != pb.lo || w > 64 || pa.lo + n.width > w {
            continue;
        }
        r.meter.charge(Counter::PassWork, 4)?;
        let word = r.build(cx, |cx| {
            let a = cx.c_extract(pa.base, 0, w)?;
            let b = cx.c_extract(pb.base, 0, w)?;
            cx.c_bin(op, a, b)
        })?;
        for p in all.iter_mut().filter(|p| p.base == y) {
            p.base = word;
            p.lo += pa.lo;
        }
    }
    // A piece of what an operand of an `^` or `|` some term reads bits of passes on, where
    // the other operand is known 0 on its bits, is a piece of that node: the top limb of `x
    // ^ (x >>u s)` is the top limb of `x`, and is written so.
    let mut relied = Fin::FINAL;
    let mut over: Vec<u32> = all
        .iter()
        .map(|p| p.base)
        .filter(|&b| matches!(cx.node(b).op, OpCode::Xor | OpCode::Or) && cx.wid(b) <= 64)
        .collect();
    over.sort_by(|a, b| cx.order(*a, *b));
    over.dedup();
    over.truncate(MAX_OVER);
    for &y in &over {
        let n = cx.node(y);
        for (v, t) in [(n.a, n.b), (n.b, n.a)] {
            if v == t {
                continue;
            }
            through.clear();
            pieces(cx, v, 0, cx.wid(y), &mut through, &mut Vec::new());
            // Where each piece read sits in the node, if the operand passes it on.
            let place = |p: &Piece| {
                through
                    .iter()
                    .find(|q| {
                        q.base == p.base
                            && p.base != y
                            && p.lo >= q.lo
                            && p.lo + p.len <= q.lo + q.len
                    })
                    .map(|q| q.at + (p.lo - q.lo))
            };
            if !all.iter().any(|p| place(p).is_some()) {
                continue;
            }
            r.meter.charge(Counter::PassWork, 1)?;
            let (Some([zero, _]), f) = super::known_words(r, cx, t)? else {
                continue;
            };
            for p in &mut all {
                let Some(lo) = place(p) else {
                    continue;
                };
                let m = low(p.len) << lo;
                if zero & m == m {
                    p.base = y;
                    p.lo = lo;
                    relied = relied.and(f);
                }
            }
        }
    }
    // With `spellings`, a piece of a sum is a piece of another sum read that has the same
    // bits up to the piece's top (the two the same linear form there): a word computed at
    // several widths (the product in a 32-bit register, `trunc<14>(x) * k` for its low limb,
    // a 64-bit product for the bits a wider register reads) is one value. Onto the sum read
    // highest, then the widest.
    let sum = |b: u32| {
        cx.wid(b) <= 64
            && matches!(
                cx.node(b).op,
                OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Mul
            )
    };
    let mut words: Vec<(u32, u16)> = Vec::new();
    for p in all.iter().filter(|p| spellings && sum(p.base)) {
        match words.iter_mut().find(|v| v.0 == p.base) {
            Some(v) => v.1 = v.1.max(p.lo + p.len),
            None => words.push((p.base, p.lo + p.len)),
        }
    }
    words.sort_by(|a, b| {
        (b.1.cmp(&a.1))
            .then(cx.wid(b.0).cmp(&cx.wid(a.0)))
            .then(cx.order(a.0, b.0))
    });
    words.truncate(MAX_WORDS);
    for i in 1..words.len() {
        let (b, o) = words[i];
        for &(a, _) in &words[..i] {
            // (One that is itself read as another is not read onto.)
            if !all.iter().any(|p| p.base == a) {
                continue;
            }
            r.meter.charge(Counter::PassWork, 16)?;
            let mut f = Fin::FINAL;
            if same_low(r, cx, a, b, o, &mut f)? {
                for p in all.iter_mut().filter(|p| p.base == b) {
                    p.base = a;
                }
                relied = relied.and(f);
                break;
            }
        }
    }
    // The values read, in the canonical order; a term reading none is 0.
    let mut bases: Vec<u32> = all.iter().map(|p| p.base).collect();
    bases.sort_by(|a, b| cx.order(*a, *b));
    bases.dedup();
    let at = |b: u32| bases.iter().position(|&x| x == b).unwrap_or(0);
    let shared = (0..bases.len()).any(|b| {
        read.iter()
            .filter(|t| all[t.2.clone()].iter().any(|p| at(p.base) == b))
            .count()
            > 1
    });
    if !shared && tops.is_empty() && read.iter().all(|t| !t.2.is_empty()) {
        discard(r, cx, before);
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, all.len() as u64)?;
    // Components: the values, joined by the terms that read several and by the runs over
    // several; then one more per term that reads nothing.
    let mut up: Vec<usize> = (0..bases.len()).collect();
    for t in &read {
        let ps = &all[t.2.clone()];
        for p in ps.iter().skip(1) {
            union(&mut up, at(ps[0].base), at(p.base));
        }
    }
    let mut found: Vec<Run> = Vec::new();
    for (b, &base) in bases.iter().enumerate() {
        let on: Vec<(Piece, u64)> = read
            .iter()
            .flat_map(|t| all[t.2.clone()].iter().map(|p| (*p, shl(t.1, p.at))))
            .filter(|(p, _)| p.base == base)
            .collect();
        let first = found.len();
        runs(base, &on, j, &mut found);
        for run in &mut found[first..] {
            run.of = b;
        }
    }
    // Runs that follow one another in a node that passes their values on (or holds one
    // itself), their coefficients doubling across: one run of that node. The widest such
    // node first.
    for &y in &tops {
        through.clear();
        let wy = match cx.node(y).op {
            OpCode::Sext => cx.wid(cx.node(y).a),
            _ => cx.wid(y),
        };
        pieces(cx, y, 0, wy, &mut through, &mut Vec::new());
        // Each run as bits of `y`: its own, and those of a value within one of its pieces.
        let mut cand: Vec<(u16, usize)> = Vec::new();
        for (x, run) in found.iter().enumerate() {
            if run.used {
                continue;
            }
            if run.base == y {
                cand.push((run.lo, x));
            } else if let Some(p) = through
                .iter()
                .find(|p| p.base == run.base && run.lo >= p.lo && run.lo + run.len <= p.lo + p.len)
            {
                cand.push((p.at + (run.lo - p.lo), x));
            }
        }
        cand.sort_unstable();
        for i in 0..cand.len() {
            let (lo, x) = cand[i];
            if found[x].used {
                continue;
            }
            let mut chain = vec![x];
            let mut last = found[x];
            let mut end = lo + last.len;
            while !last.open {
                let c = shl(last.c, last.len);
                let next = cand[i + 1..].iter().find(|&&(l, x2)| {
                    l == end && !found[x2].used && !chain.contains(&x2) && found[x2].c == c
                });
                let Some(&(_, x2)) = next.filter(|_| c != 0) else {
                    break;
                };
                chain.push(x2);
                last = found[x2];
                end += last.len;
            }
            if chain.len() < 2 {
                continue;
            }
            let first = found[x];
            let mut run = Run {
                base: y,
                lo,
                len: end - lo,
                c: first.c,
                open: false,
                of: first.of,
                used: false,
            };
            clip(&mut run, j);
            for &x2 in &chain {
                found[x2].used = true;
                union(&mut up, first.of, found[x2].of);
            }
            found.push(run);
        }
    }
    found.retain(|run| !run.used);
    // Per component: the terms and the runs.
    let part = |up: &mut Vec<usize>, t: &(u32, u64, core::ops::Range<usize>)| {
        all[t.2.clone()].first().map(|p| find(up, at(p.base)))
    };
    let mut out: Vec<(u32, BitVec)> = Vec::with_capacity(read.len());
    let mut leaves: Vec<u32> = Vec::with_capacity(read.len());
    let mut changed = false;
    let mut scratch: Vec<Piece> = Vec::new();
    let mut target: Vec<Piece> = Vec::new();
    for t in &read {
        if t.2.is_empty() {
            // The term is 0 on the bits read.
            changed = true;
            leaves.push(t.0);
        }
    }
    for b in 0..bases.len() {
        if find(&mut up, b) != b {
            continue;
        }
        let members: Vec<&(u32, u64, core::ops::Range<usize>)> = read
            .iter()
            .filter(|t| part(&mut up, t) == Some(b))
            .collect();
        let mine: Vec<Run> = found
            .iter()
            .filter(|run| find(&mut up, run.of) == b)
            .copied()
            .collect();
        if mine.len() >= members.len() {
            for t in &members {
                out.push((t.0, BitVec::wrapping_from_u64(width, t.1)));
                leaves.push(t.0);
            }
            continue;
        }
        changed = true;
        for t in &members {
            leaves.extend(all[t.2.clone()].iter().map(|p| p.base));
            leaves.extend(deep[t.2.clone()].iter().copied());
        }
        for run in mine {
            leaves.push(run.base);
            // A term that is this slice already stays the atom.
            target.clear();
            pieces(cx, run.base, run.lo, run.len, &mut target, &mut Vec::new());
            let bits = j - run.c.trailing_zeros() as u16;
            let mut same: Option<u32> = None;
            for t in &members {
                scratch.clear();
                pieces(
                    cx,
                    t.0,
                    0,
                    cx.wid(t.0).min(bits),
                    &mut scratch,
                    &mut Vec::new(),
                );
                if scratch == target && same.is_none_or(|s| cx.order(t.0, s).is_lt()) {
                    same = Some(t.0);
                }
            }
            let atom = match same {
                Some(a) => a,
                None => slice(r, cx, run.base, run.lo, run.len, run.open, w)?,
            };
            out.push((atom, BitVec::wrapping_from_u64(width, run.c)));
        }
    }
    if !changed {
        discard(r, cx, before);
        return Ok(None);
    }
    leaves.sort_unstable();
    leaves.dedup();
    let mut f = Form::of(*konst, &out);
    f.fin = fin.and(relied);
    let f = if j < w {
        f.reduce(crate::Width::new(j).map_err(|e| Stop::Error(e.into()))?)
    } else {
        f
    };
    Ok(Some((f, leaves)))
}

/// The linear pass's reading of `n` (whose form is `form`) with its limbs joined: `Ok(step)`
/// when it commits, else `Err(fin)` with what the rejection contributes to the node's
/// finality.
pub(super) fn step(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    form: &Form,
) -> Result<Result<Step, Fin>, Stop> {
    // Nothing joins where every term is a value read whole: no term moves bits of another
    // value (an extension, a slice, a shift or a mask, a `concat`, a bitwise function of
    // such), and no coefficient leaves low bits of its term unread. A long sum of plain
    // terms pays a unit for 32 of them here, not one a term at every node.
    let terms = form.parts().1;
    r.meter
        .charge(Counter::PassWork, terms.len() as u64 / 32 + 1)?;
    let moves = |t: u32| {
        matches!(
            cx.node(t).op,
            OpCode::Zext
                | OpCode::Sext
                | OpCode::Extract
                | OpCode::Concat
                | OpCode::Shl
                | OpCode::LShr
                | OpCode::AShr
                | OpCode::And
                | OpCode::Or
                | OpCode::Xor
        )
    };
    if !terms
        .iter()
        .any(|t| moves(t.0) || t.1.bit(0) == Some(false))
    {
        return Ok(Err(Fin::FINAL));
    }
    let before = cx.len() as u32;
    let Some((f, leaves)) = joined(r, cx, form, cx.wid(n))? else {
        return Ok(Err(Fin::FINAL));
    };
    let e = linear::emit(r, cx, &f)?;
    Ok(
        match finish(r, cx, PassKind::Linear, n, e, before, &leaves, f.fin)? {
            Step::To(x, fin) => Ok(Step::To(x, fin)),
            Step::Normal(fin) => Err(fin),
        },
    )
}

/// The linear pass's reading of `n` (whose form is `form`) where it is a slice of a sum from
/// above bit 0 plus a constant: `extract<lo, n>(B) + c` is `extract<lo, n>(B + (c << lo))`
/// (the shifted constant adds nothing below bit `lo`, and above it adds `c`), `B`'s own
/// constant taking the other in. A constant added limb by limb is then the word's constant
/// in every limb's slice, and the limbs are slices of one word. `Ok(step)` when it commits,
/// else `Err(fin)` with what the rejection contributes to the node's finality.
pub(super) fn folded(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
    form: &Form,
) -> Result<Result<Step, Fin>, Stop> {
    let (konst, terms, fin) = form.parts();
    if konst.is_zero() || terms.len() != 1 || terms[0].1 != BitVec::one(konst.width()) {
        return Ok(Err(Fin::FINAL));
    }
    let s = cx.node(terms[0].0);
    if s.op != OpCode::Extract
        || s.b == 0
        || cx.wid(s.a) > 64
        || !matches!(
            cx.node(s.a).op,
            OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Mul | OpCode::Shl
        )
    {
        return Ok(Err(Fin::FINAL));
    }
    let before = cx.len() as u32;
    let wide = cx.width_of(s.a);
    let base = linear::form_of(r, cx, s.a)?;
    let up = BitVec::wrapping_from_u64(wide, konst.limbs()[0] << s.b);
    let word = base.add(&Form::of(up, &[]));
    let leaves: Vec<u32> = word.parts().1.iter().map(|t| t.0).collect();
    let b = linear::emit(r, cx, &word)?;
    let e = r.build(cx, |cx| cx.c_extract(b, s.b as u16, s.width))?;
    let relied = fin.and(base.fin);
    Ok(
        match finish(r, cx, PassKind::Linear, n, e, before, &leaves, relied)? {
            Step::To(x, fin) => Ok(Step::To(x, fin)),
            Step::Normal(fin) => Err(fin),
        },
    )
}
