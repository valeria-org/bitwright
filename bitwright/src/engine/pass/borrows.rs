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
//! lo(a)]` is `hi(a + b)`. Where the known bits say `Q + (P − Q)` cannot wrap, `b` is 0, the
//! identity holds of the integers, and the carry is read at any `j`, the digits zero-extended.
//!
//! The sum's terms are flattened first, and those that are one value written two ways made
//! one term: a shift beside a slice of the same bits, the slices of two spellings of one
//! linear form. The sum is replaced only when it is left fewer terms than its narrowing alone
//! leaves it.
//!
//! A side that is no low digit is read as one where it can be. Each side is read through its
//! truncations, masks of low bits and zero extensions, the two at the widest width both are
//! read at; a value its known bits put below `2^k` is its own low digit (and its high digit is
//! 0); a `k`-bit side is read back at the other side's width, the narrowing a comparison of
//! digits pushes into its sides undone. The high digit of a side read back is 0 only where
//! the known bits say so: a narrowed sum of two digits carries.

use super::forms::Parts;
use super::{Fin, Runner, Stop, casts, discard, linear, linear_mba};
use crate::expr::{Context, OpCode};
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// The most terms of a sum read.
const MAX_TERMS: usize = 24;

/// The readings of `x` as the low `k` bits of a value `P`, zero-extended, as `(P, k)`: `x`
/// itself at its width, then each value under its truncations, masks of the low bits and zero
/// extensions, of at most 64 bits (`trunc<16>(P & 0x3fff)` is the low 16 bits of `P &
/// 0x3fff` and the low 14 bits of `P`).
fn readings(cx: &Context, x: u32) -> Vec<(u32, u16)> {
    let (mut p, mut k) = (x, cx.wid(x));
    let mut out = vec![(p, k)];
    loop {
        let n = cx.node(p);
        let (below, bits) = match n.op {
            OpCode::Extract if n.b == 0 => (n.a, n.width),
            OpCode::Zext => (n.a, cx.wid(n.a)),
            OpCode::And if n.width <= 64 => {
                let (v, c) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (Some(c), None) => (n.b, c.limbs()[0]),
                    (None, Some(c)) => (n.a, c.limbs()[0]),
                    _ => break,
                };
                let m = c.trailing_ones() as u16;
                if m == 0 || m >= n.width || c >> m != 0 {
                    break;
                }
                (v, m)
            }
            _ => break,
        };
        if cx.wid(below) > 64 {
            break;
        }
        p = below;
        k = k.min(bits);
        out.push((p, k));
    }
    out
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
/// operands), anything else zero-extended.
fn lifted(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    w: u16,
    seen: &mut Vec<(u32, u32)>,
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
            r.build(cx, |cx| cx.c_extract(n.a, 0, w))?
        }
        _ => match (bin, un) {
            (Some(op), _) if room => {
                let a = lifted(r, cx, n.a, w, seen)?;
                let b = lifted(r, cx, n.b, w, seen)?;
                r.build(cx, |cx| cx.c_bin(op, a, b))?
            }
            (_, Some(op)) if room => {
                let a = lifted(r, cx, n.a, w, seen)?;
                r.build(cx, |cx| cx.c_un(op, a))?
            }
            _ => r.build(cx, |cx| cx.c_zext(x, w))?,
        },
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

/// The widest value of at most 64 bits a truncation in `x` reads, through the operators
/// [`lifted`] undoes it through; 0 without one.
fn lift_width(cx: &Context, x: u32) -> u16 {
    let mut stack = vec![x];
    let (mut seen, mut w) = (0, 0);
    while let Some(i) = stack.pop() {
        seen += 1;
        if seen > MAX_LIFT {
            break;
        }
        let n = cx.node(i);
        match n.op {
            OpCode::Extract if n.b == 0 => {
                let s = cx.wid(n.a);
                if s <= 64 {
                    w = w.max(s);
                }
            }
            OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Neg
            | OpCode::Not => stack.extend(n.children()),
            _ => {}
        }
    }
    w
}

/// Whether the known bits of `v` (of at most 64 bits) put it below `2^k`, and what they
/// relied on.
fn below(r: &mut Runner<'_, '_>, cx: &mut Context, v: u32, k: u16) -> Result<(bool, Fin), Stop> {
    let w = cx.wid(v);
    if k >= w {
        return Ok((true, Fin::FINAL));
    }
    let (known, fin) = super::known_words(r, cx, v)?;
    let high = (u64::MAX >> (64 - w)) & !((1u64 << k) - 1);
    Ok((known.is_some_and(|[zero, _]| zero & high == high), fin))
}

/// A side `x` of a carry's comparison, the low `kp` bits of `p` (see [`readings`]), as the
/// low `k` bits of a `w`-bit value; `fin` takes what the facts used relied on.
#[allow(clippy::too_many_arguments)]
fn side(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    p: u32,
    kp: u16,
    k: u16,
    w: u16,
    fin: &mut Fin,
) -> Result<Option<Digit>, Stop> {
    let wp = cx.wid(p);
    // The low `k` bits of `p` are `x` where `kp` is `k`, and where it is more with `x` below
    // `2^k`. A whole `p` of fewer bits is below `2^k` itself: its zero extension.
    if kp > k {
        let (fits, f) = below(r, cx, x, k)?;
        if !fits {
            return Ok(None);
        }
        *fin = fin.and(f);
    } else if kp < k {
        if wp != kp || wp > w {
            return Ok(None);
        }
        let of = r.build(cx, |cx| cx.c_zext(p, w))?;
        return Ok(Some(Digit { of, small: true }));
    }
    // Read at `w` bits: a narrower `p` with its truncations undone (the narrowing a comparison
    // of digits pushes into its sides), which keeps its low bits. Its high digit is 0 only
    // where the known bits say so (a sum of two zero-extended digits carries).
    let of = match wp.cmp(&w) {
        core::cmp::Ordering::Less => lifted(r, cx, p, w, &mut Vec::new())?,
        core::cmp::Ordering::Equal => p,
        core::cmp::Ordering::Greater => r.build(cx, |cx| cx.c_extract(p, 0, w))?,
    };
    let (small, f) = below(r, cx, of, k)?;
    if small {
        *fin = fin.and(f);
    }
    Ok(Some(Digit { of, small }))
}

/// `P`, `Q` and `k` when `x` and `y` are the low `k` bits of `P` and `Q` of one width (more
/// than `k`), and what the facts used relied on. Each side is read through its truncations,
/// masks and zero extensions ([`readings`]), at the widest width both are read at, a digit of
/// more than `k` bits standing for its low `k` where its known bits put it below `2^k`.
/// Without such a width, a side is read back at the width of the other, or of the values its
/// truncations read (the narrowing a comparison of digits pushes into its sides undone).
fn digits(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    y: u32,
) -> Result<Option<(Digit, Digit, u16, Fin)>, Stop> {
    if cx.wid(x) > 64 {
        return Ok(None);
    }
    let (rx, ry) = (readings(cx, x), readings(cx, y));
    // The innermost reading of each side at the widest width both have, one of them a digit
    // of a wider value there.
    let at = |rs: &[(u32, u16)], w: u16| rs.iter().rev().find(|v| cx.wid(v.0) == w).copied();
    let common = rx
        .iter()
        .filter_map(|&(p, _)| {
            let w = cx.wid(p);
            let (a, b) = (at(&rx, w)?, at(&ry, w)?);
            (w > a.1.min(b.1)).then_some((w, a, b))
        })
        .max_by_key(|c| c.0);
    let ((p, kp), (q, kq), k, w) = match common {
        Some((w, a, b)) => (a, b, a.1.min(b.1), w),
        None => {
            let (a, b) = (rx[rx.len() - 1], ry[ry.len() - 1]);
            let (wp, wq) = (cx.wid(a.0), cx.wid(b.0));
            let (k, w) = match (wp > a.1, wq > b.1) {
                (true, true) => (a.1.min(b.1), wp.max(wq)),
                (true, false) => (a.1, wp),
                (false, true) => (b.1, wq),
                (false, false) => {
                    let k = a.1.max(b.1);
                    let lift = |v: (u32, u16)| if v.1 == k { lift_width(cx, v.0) } else { 0 };
                    (k, lift(a).max(lift(b)))
                }
            };
            (a, b, k, w)
        }
    };
    if w <= k {
        return Ok(None);
    }
    let mut fin = Fin::FINAL;
    let Some(a) = side(r, cx, x, p, kp, k, w, &mut fin)? else {
        return Ok(None);
    };
    let Some(b) = side(r, cx, y, q, kq, k, w, &mut fin)? else {
        return Ok(None);
    };
    Ok(Some((a, b, k, fin)))
}

/// Whether `i` is a high digit as a sum holds one: a slice from above bit 0, its zero
/// extension, or a shift right by a constant.
fn high_digit(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    match n.op {
        OpCode::Extract => n.b > 0,
        OpCode::Zext => {
            let s = cx.node(n.a);
            s.op == OpCode::Extract && s.b > 0
        }
        OpCode::LShr => cx.const_val(n.b).is_some(),
        _ => false,
    }
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
            _ if high_digit(cx, i) => {
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

/// `p − q` as the linear pass writes it over its terms, each slice pushed into its operand (a
/// value written two ways, `trunc<32>(x >>u 32)` beside `extract<32, 32>(x)` where something
/// else still reads the shift, is one term), or as the linear-MBA pass writes that where it
/// has fewer terms: `(a + b) − (a ^ b)` is `2·(a & b)`, while a difference that cancels to
/// one term as it stands stays that term. `fin` takes what the facts used relied on.
fn difference(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    p: u32,
    q: u32,
    fin: &mut Fin,
) -> Result<u32, Stop> {
    let d = r.build(cx, |cx| cx.c_bin(BinOp::Sub, p, q))?;
    let mut form = linear::form_of(r, cx, d)?;
    let (konst, terms, _) = form.parts();
    let (konst, mut terms) = (*konst, terms.to_vec());
    let mut pushed = false;
    for t in &mut terms {
        let n = cx.node(t.0);
        if n.op == OpCode::Extract
            && let Some((h, f, _)) = casts::narrowed_from(r, cx, n.a, n.b as u16, n.width)?
            && h != t.0
        {
            *fin = fin.and(f);
            t.0 = h;
            pushed = true;
        }
    }
    if pushed {
        let relied = form.fin;
        let e = linear::emit(r, cx, &linear::Form::of(konst, &terms))?;
        form = linear::form_of(r, cx, e)?;
        form.fin = form.fin.and(relied);
    }
    *fin = fin.and(form.fin);
    let d = linear::emit(r, cx, &form)?;
    if form.parts().1.len() > 1
        && let Some(mixed) = linear_mba::normal(r, cx, d)?
        && linear::form_of(r, cx, mixed)?.parts().1.len() < form.parts().1.len()
    {
        return Ok(mixed);
    }
    Ok(d)
}

/// Whether `q + d` cannot wrap, by the known bits of both, and what they relied on: a `p` that
/// is `q + d` modulo `2^W` is then `q + d`, and no less than `q`.
fn no_wrap(r: &mut Runner<'_, '_>, cx: &mut Context, q: u32, d: u32) -> Result<(bool, Fin), Stop> {
    let mask = u64::MAX >> (64 - cx.wid(q));
    let (kq, fq) = super::known_words(r, cx, q)?;
    let (kd, fd) = super::known_words(r, cx, d)?;
    let (Some([zq, _]), Some([zd, _])) = (kq, kd) else {
        return Ok((false, Fin::FINAL));
    };
    let most = u128::from(!zq & mask) + u128::from(!zd & mask);
    Ok((most <= u128::from(mask), fq.and(fd)))
}

/// `t` (of at most 64 bits) as the zero extension of the low bits its known bits leave open,
/// the truncation pushed into it: `x >>u 7` and `zext(extract<7, 7>(x))` of an `x` below
/// `2^14` are one node. `fin` takes what the facts relied on where they are used.
fn trimmed(r: &mut Runner<'_, '_>, cx: &mut Context, t: u32, fin: &mut Fin) -> Result<u32, Stop> {
    let w = cx.wid(t);
    let (Some([zero, _]), f) = super::known_words(r, cx, t)? else {
        return Ok(t);
    };
    let open = !zero & (u64::MAX >> (64 - w));
    let bits = (u64::BITS - open.leading_zeros()) as u16;
    if bits == w {
        return Ok(t);
    }
    let e = if bits == 0 {
        let zero = BitVec::zero(cx.width_of(t));
        r.build(cx, |cx| cx.mk_const(&zero))?
    } else {
        let Some((h, fh, _)) = casts::narrowed_from(r, cx, t, 0, bits)? else {
            return Ok(t);
        };
        *fin = fin.and(fh);
        r.build(cx, |cx| cx.c_zext(h, w))?
    };
    *fin = fin.and(f);
    Ok(e)
}

/// `t`, a slice of a sum (or its zero extension), as that slice of the sum's form written
/// out anew: two spellings of one linear form (`a + b - (m + m)` beside `-(m << 1) + (a +
/// b)`, one of them shared with something else) are then one node, and their slices one term.
/// `fin` takes what the form relied on where it is used.
fn rebased(r: &mut Runner<'_, '_>, cx: &mut Context, t: u32, fin: &mut Fin) -> Result<u32, Stop> {
    let outer = cx.node(t);
    let slice = if outer.op == OpCode::Zext { outer.a } else { t };
    let s = cx.node(slice);
    if s.op != OpCode::Extract
        || !matches!(cx.node(s.a).op, OpCode::Add | OpCode::Sub | OpCode::Neg)
    {
        return Ok(t);
    }
    let form = linear::form_of(r, cx, s.a)?;
    let base = linear::emit(r, cx, &form)?;
    if base == s.a {
        return Ok(t);
    }
    *fin = fin.and(form.fin);
    r.build(cx, |cx| {
        let e = cx.c_extract(base, s.b as u16, s.width)?;
        cx.c_zext(e, outer.width)
    })
}

/// `sum` with its terms that are one value merged: each read as [`trimmed`] and [`rebased`]
/// write it, the coefficients of equal ones added. A term that meets no other stays as it is
/// written.
fn merged(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    sum: &linear::Form,
    fin: &mut Fin,
) -> Result<linear::Form, Stop> {
    let (konst, terms, relied) = sum.parts();
    let mut read = Vec::with_capacity(terms.len());
    for &(t, k) in terms {
        let mut f = Fin::FINAL;
        let e = trimmed(r, cx, t, &mut f)?;
        read.push((rebased(r, cx, e, &mut f)?, t, k, f));
    }
    read.sort_by_key(|v| v.0);
    let mut out: Vec<(u32, BitVec)> = Vec::with_capacity(read.len());
    for group in read.chunk_by(|a, b| a.0 == b.0) {
        if let [(_, t, k, _)] = group {
            out.push((*t, *k));
            continue;
        }
        let k = group.iter().fold(BitVec::zero(konst.width()), |k, v| {
            BitVec::bin_unchecked(BinOp::Add, &k, &v.2)
        });
        for v in group {
            *fin = fin.and(v.3);
        }
        // (A term the known bits make 0 is a constant: no term.)
        if cx.const_val(group[0].0).is_none() {
            out.push((group[0].0, k));
        }
    }
    let mut form = linear::Form::of(*konst, &out);
    form.fin = relied;
    Ok(form)
}

/// A carry term read: the comparison's sides as the low digits of `p` and `q`, their
/// difference `d`, the digits' width and whether the term is minus the carry (a `sext`).
#[derive(Clone, Copy)]
struct Carry {
    p: Digit,
    q: Digit,
    d: u32,
    at: u16,
    minus: bool,
}

/// The low `j` bits of the sum `x` (a node of `j` bits) with its carry terms read as high
/// digits, when that leaves fewer terms; with what the facts used relied on and the nodes the
/// narrowing stopped at.
///
/// A carry of digits of `W`-bit values is read where `j ≤ W − k`, and at any `j` where `Q +
/// (P − Q)` cannot wrap (by the known bits): `P ≥ Q` then, and the identity holds of the
/// integers, each high digit zero-extended. The terms of such a sum are merged as
/// [`merged`] reads them, the high digits written as shifts among them.
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
        let mut c = None;
        if let Some((x, y, minus)) = borrow(cx, a)
            && let Some((p, q, at, relied)) = digits(r, cx, x, y)?
        {
            let mut f = relied;
            let d = difference(r, cx, p.of, q.of, &mut f)?;
            let room = cx.wid(p.of) - at;
            let reads = j <= room || {
                let (exact, fe) = no_wrap(r, cx, q.of, d)?;
                f = f.and(fe);
                exact
            };
            if reads {
                fin = fin.and(f);
                c = Some(Carry { p, q, d, at, minus });
            }
        }
        carries.push(c);
    }
    // Without one, a sum of high digits: each is pushed into its operand again, where one
    // written two ways (`hi(a | b)` and `hi(a) | hi(b)`, `x >>u 7` and `zext(extract<7,
    // 7>(x))`) meets itself.
    let highs = terms.iter().filter(|t| high_digit(cx, t.0)).count();
    if carries.iter().all(Option::is_none) && highs < 2 {
        discard(r, cx, before);
        return Ok(None);
    }
    // The terms at `j` bits: `out` with each carry as its high digits, `rest` without the
    // carries (what the sum is measured against: a term narrowed into a sum is its terms).
    let mut out: Vec<(u32, BitVec)> = Vec::with_capacity(terms.len() + 4);
    let mut rest: Vec<(u32, BitVec)> = Vec::with_capacity(terms.len());
    let mut read = 0;
    let mut stops = Vec::new();
    for (&(a, k), c) in terms.iter().zip(&carries) {
        let k = low(&k);
        let Some(c) = *c else {
            let n = cx.node(a);
            let (from, lo) = match n.op {
                OpCode::Extract if j == w => (n.a, n.b as u16),
                _ if j == w => {
                    stops.push(a);
                    out.push((a, k));
                    rest.push((a, k));
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
            rest.push((h, k));
            continue;
        };
        read += usize::from(!k.is_zero());
        let k = if c.minus { neg(&k) } else { k };
        // The high digit of a value below `2^k` is 0.
        let highs = [
            (!c.p.small).then_some((c.p.of, k)),
            (!c.q.small).then_some((c.q.of, neg(&k))),
            Some((c.d, neg(&k))),
        ];
        for (v, k) in highs.into_iter().flatten() {
            // All of the digit's bits, zero-extended, where it has fewer than `j`.
            let bits = j.min(cx.wid(v) - c.at);
            let Some((h, f, s)) = casts::narrowed_from(r, cx, v, c.at, bits)? else {
                discard(r, cx, before);
                return Ok(None);
            };
            fin = fin.and(f);
            stops.extend(s);
            out.push((r.build(cx, |cx| cx.c_zext(h, j))?, k));
        }
    }
    // The form over the digits' own terms: one pushed into a sum is a sum, and one that is a
    // constant is no term.
    let flat = |r: &mut Runner<'_, '_>, cx: &mut Context, terms: &[(u32, BitVec)]| {
        let e = linear::emit(r, cx, &linear::Form::of(low(&konst), terms))?;
        linear::form_of(r, cx, e)
    };
    // Without a carry, the digits pushed into their operands are measured against the terms
    // as they were.
    let plain = if read == 0 {
        terms.len()
    } else {
        flat(r, cx, &rest)?.parts().1.len() + read
    };
    let sum = flat(r, cx, &out)?;
    let sum = merged(r, cx, &sum, &mut fin)?;
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
    if left >= plain {
        discard(r, cx, before);
        return Ok(None);
    }
    Ok(Some((e, fin, stops)))
}
