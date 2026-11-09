//! Carries and borrows written as comparisons of low digits, read back as the high digits they
//! complete.
//!
//! Arithmetic done digit by digit (a value split at bit `k`, the two halves computed apart)
//! writes the carry between them as a comparison: `lo(P) <u lo(Q)`, the borrow of `P − Q` out
//! of the low `k` bits (and, with `P = a + b` and `Q = a`, the carry of `a + b`). For `P` and
//! `Q` of `W` bits and `hi(X) = X >> k`,
//!
//! ```text
//! [lo(P) <u lo(Q)] = hi(P) − hi(Q) − hi(P − Q)   (mod 2^(W − k))
//! ```
//!
//! since `P − Q = D + 2^W·b` splits into `2^k·(hi P − hi Q) + (lo P − lo Q)` on the left and
//! `2^k·hi D + lo D + 2^W·b` on the right, and `lo P − lo Q = lo D − 2^k·[lo P < lo Q]`. A sum
//! read on `j ≤ W − k` low bits has each such term replaced by the three high digits, every
//! term taken at `j` bits (`extract<k, j>` pushed into the operands, so one digit written
//! several ways is one node), and the form collected again: `hi(a) + hi(b) + [lo(a + b) <u
//! lo(a)]` is `hi(a + b)`. The sum is replaced only when it has fewer terms.
//!
//! A side that is no low digit is read as one where it can be: a value its known bits put
//! below `2^k` is its own low digit (and its high digit is 0), and a `k`-bit side is read back
//! at the other side's width, the narrowing a comparison of digits pushes into its sides undone.

use super::forms::Parts;
use super::{Fin, Runner, Stop, casts, discard, linear, linear_mba};
use crate::expr::{Context, OpCode};
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// The most terms of a sum read.
const MAX_TERMS: usize = 24;

/// `x` as the low `k` bits of a wider `P`: `trunc<k>(P)` or `P & (2^k − 1)`.
fn low_digit(cx: &Context, x: u32) -> Option<(u32, u16)> {
    let n = cx.node(x);
    match n.op {
        OpCode::Extract if n.b == 0 && cx.wid(n.a) <= 64 => Some((n.a, n.width)),
        OpCode::And if n.width <= 64 => {
            let (p, c) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                (Some(c), None) => (n.b, c.limbs()[0]),
                (None, Some(c)) => (n.a, c.limbs()[0]),
                _ => return None,
            };
            let k = c.trailing_ones() as u16;
            (c != 0 && c >> k == 0 && k < n.width).then_some((p, k))
        }
        _ => None,
    }
}

/// The comparison's sides when `a` is a carry term: `zext(x <u y)`, or `sext` of it (minus
/// one), which the flag tells.
fn borrow(cx: &Context, a: u32) -> Option<(u32, u32, bool)> {
    let n = cx.node(a);
    if !matches!(n.op, OpCode::Zext | OpCode::Sext) || n.width < 2 {
        return None;
    }
    let c = cx.node(n.a);
    (c.op == OpCode::Ult).then_some((c.a, c.b, n.op == OpCode::Sext))
}

/// The most nodes of a narrowed digit read back at its full width.
const MAX_LIFT: u32 = 24;

/// A `w`-bit value whose low bits are `x`: `x` with its truncations of wider values undone
/// through `+ − * neg & | ^ ~` (the low bits of each depend only on the low bits of its
/// operands), anything else zero-extended; and whether a truncation was undone.
fn lifted(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    w: u16,
    seen: &mut Vec<(u32, u32)>,
    wide: &mut bool,
) -> Result<u32, Stop> {
    if let Some(&(_, v)) = seen.iter().find(|s| s.0 == x) {
        return Ok(v);
    }
    let n = cx.node(x);
    let bin = match n.op {
        OpCode::Add => Some(BinOp::Add),
        OpCode::Sub => Some(BinOp::Sub),
        OpCode::Mul => Some(BinOp::Mul),
        OpCode::And => Some(BinOp::And),
        OpCode::Or => Some(BinOp::Or),
        OpCode::Xor => Some(BinOp::Xor),
        _ => None,
    };
    let un = match n.op {
        OpCode::Neg => Some(UnOp::Neg),
        OpCode::Not => Some(UnOp::Not),
        _ => None,
    };
    let room = (seen.len() as u32) < MAX_LIFT;
    let v = match n.op {
        OpCode::Extract if n.b == 0 && cx.wid(n.a) >= w => {
            *wide = true;
            r.build(cx, |cx| cx.c_extract(n.a, 0, w))?
        }
        _ if room && let Some(op) = bin => {
            let a = lifted(r, cx, n.a, w, seen, wide)?;
            let b = lifted(r, cx, n.b, w, seen, wide)?;
            r.build(cx, |cx| cx.c_bin(op, a, b))?
        }
        _ if room && let Some(op) = un => {
            let a = lifted(r, cx, n.a, w, seen, wide)?;
            r.build(cx, |cx| cx.c_un(op, a))?
        }
        _ => r.build(cx, |cx| cx.c_zext(x, w))?,
    };
    seen.push((x, v));
    Ok(v)
}

/// One side of a carry's comparison as the low `k` bits of a `W`-bit value.
#[derive(Clone, Copy)]
struct Digit {
    /// The value.
    of: u32,
    /// Whether the value is below `2^k` (its high digit is 0).
    small: bool,
}

/// `P`, `Q` and `k` when `x` and `y` are the low `k` bits of `P` and `Q` of one width, and what
/// the facts used relied on. A side that is no low digit is its own where it is below `2^k`
/// (by its known bits), and a `k`-bit side is read back at the other's width (the narrowing a
/// comparison of digits pushes into its sides undone).
fn digits(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    y: u32,
) -> Result<Option<(Digit, Digit, u16, Fin)>, Stop> {
    let whole = |of| Digit { of, small: false };
    let (dx, dy) = (low_digit(cx, x), low_digit(cx, y));
    if let (Some((p, k)), Some((q, k2))) = (dx, dy)
        && k == k2
        && cx.wid(p) == cx.wid(q)
    {
        return Ok(Some((whole(p), whole(q), k, Fin::FINAL)));
    }
    // `c` as a value of the width of `like` with `c` its low `k` bits.
    let other = |r: &mut Runner<'_, '_>, cx: &mut Context, c: u32, like: u32, k: u16| {
        let (cw, w) = (cx.wid(c), cx.wid(like));
        if cw > 64 || cw > w {
            return Ok(None);
        }
        if cw == k {
            let mut wide = false;
            let of = lifted(r, cx, c, w, &mut Vec::new(), &mut wide)?;
            return Ok(Some((Digit { of, small: !wide }, Fin::FINAL)));
        }
        let (known, fin) = super::known_words(r, cx, c)?;
        let Some([zero, _]) = known else {
            return Ok(None);
        };
        let mask = if cw == 64 { !0 } else { (1u64 << cw) - 1 };
        if k < 64 && (zero | ((1u64 << k) - 1)) & mask != mask {
            return Ok(None);
        }
        let of = r.build(cx, |cx| cx.c_zext(c, w))?;
        Ok::<_, Stop>(Some((Digit { of, small: true }, fin)))
    };
    if let Some((p, k)) = dx
        && let Some((q, fin)) = other(r, cx, y, p, k)?
    {
        return Ok(Some((whole(p), q, k, fin)));
    }
    if let Some((q, k)) = dy
        && let Some((p, fin)) = other(r, cx, x, q, k)?
    {
        return Ok(Some((p, whole(q), k, fin)));
    }
    Ok(None)
}

/// Whether a term of `x`'s sum may be a carry, or two of them high digits: cheap, before the
/// form is read.
fn may_expand(cx: &Context, x: u32) -> bool {
    let mut stack = vec![x];
    let (mut seen, mut high) = (0, 0);
    while let Some(i) = stack.pop() {
        seen += 1;
        if seen > 4 * MAX_TERMS {
            return false;
        }
        let n = cx.node(i);
        match n.op {
            OpCode::Add | OpCode::Sub | OpCode::Neg => stack.extend(n.children()),
            _ if borrow(cx, i).is_some() => return true,
            OpCode::Extract if n.b > 0 => {
                high += 1;
                if high == 2 {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// The low `j` bits of the sum `x` (a `j`-bit node) with its carry terms read as high digits,
/// when that leaves fewer terms; with what the facts used relied on and the nodes the
/// narrowing stopped at.
pub(super) fn expanded(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    j: u16,
) -> Result<Option<(u32, Fin, Vec<u32>)>, Stop> {
    let w = cx.wid(x);
    if j == 0 || j > w || !may_expand(cx, x) {
        return Ok(None);
    }
    let form = linear::form_of(r, cx, x)?;
    let (konst, terms, fin) = form.parts();
    let (konst, terms, mut fin) = (*konst, terms.to_vec(), fin);
    if terms.len() > MAX_TERMS {
        return Ok(None);
    }
    let jw = Width::new(j).map_err(|e| Stop::Error(e.into()))?;
    let low = |v: &BitVec| v.trunc(jw).unwrap_or(*v);
    let neg = |v: &BitVec| BitVec::bin_unchecked(BinOp::Sub, &BitVec::zero(jw), v);
    // The carries first: nothing is built for a sum without one.
    let before = cx.len() as u32;
    let mut carries = Vec::with_capacity(terms.len());
    for &(a, _) in &terms {
        let c = match borrow(cx, a) {
            Some((x, y, minus)) => digits(r, cx, x, y)?
                .filter(|&(p, _, k, _)| cx.wid(p.of) > k && j <= cx.wid(p.of) - k)
                .map(|d| (d, minus)),
            None => None,
        };
        carries.push(c);
    }
    // Without one, a sum of high digits: each is pushed into its operand again, where one
    // written two ways (`hi(a | b)` and `hi(a) | hi(b)`) meets itself.
    let high = |&(a, _): &(u32, BitVec)| cx.node(a).op == OpCode::Extract && cx.node(a).b > 0;
    if carries.iter().all(Option::is_none) && terms.iter().filter(|t| high(t)).count() < 2 {
        discard(r, cx, before);
        return Ok(None);
    }
    let mut out: Vec<(u32, BitVec)> = Vec::with_capacity(terms.len() + 4);
    let mut stops = Vec::new();
    for (&(a, k), c) in terms.iter().zip(&carries) {
        let k = low(&k);
        let Some(((p, q, at, relied), minus)) = *c else {
            let n = cx.node(a);
            let (from, lo) = match n.op {
                OpCode::Extract if j == w => (n.a, n.b as u16),
                _ if j == w => {
                    stops.push(a);
                    out.push((a, k));
                    continue;
                }
                _ => (a, 0),
            };
            let Some((h, f, s)) = casts::narrowed_from(r, cx, from, lo, j)? else {
                discard(r, cx, before);
                return Ok(None);
            };
            fin = fin.and(f);
            stops.extend(s);
            out.push((h, k));
            continue;
        };
        fin = fin.and(relied);
        let k = if minus { neg(&k) } else { k };
        // `P − Q`, as the linear-MBA pass writes it, or the linear pass.
        let d = r.build(cx, |cx| cx.c_bin(BinOp::Sub, p.of, q.of))?;
        let d = match linear_mba::normal(r, cx, d)? {
            Some(d) => d,
            None => {
                let df = linear::form_of(r, cx, d)?;
                let d = linear::emit(r, cx, &df)?;
                linear_mba::normal(r, cx, d)?.unwrap_or(d)
            }
        };
        // The high digit of a value below `2^k` is 0.
        let highs = [
            (!p.small).then_some((p.of, k)),
            (!q.small).then_some((q.of, neg(&k))),
            Some((d, neg(&k))),
        ];
        for (v, k) in highs.into_iter().flatten() {
            let Some((h, f, s)) = casts::narrowed_from(r, cx, v, at, j)? else {
                discard(r, cx, before);
                return Ok(None);
            };
            fin = fin.and(f);
            stops.extend(s);
            out.push((h, k));
        }
    }
    let sum = linear::Form::of(low(&konst), &out);
    let mut left = sum.parts().1.len();
    let mut e = linear::emit(r, cx, &sum)?;
    // The digits of one linear MBA (`hi(a | b) + hi(a & b) − hi(a) − hi(b)`) are one again.
    if left > 1
        && let Some(e2) = linear_mba::normal(r, cx, e)?
    {
        let f = linear::form_of(r, cx, e2)?;
        if f.parts().1.len() < left {
            left = f.parts().1.len();
            e = e2;
        }
    }
    if left >= terms.len() {
        discard(r, cx, before);
        return Ok(None);
    }
    Ok(Some((e, fin, stops)))
}
