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
//! leaves it; a reading that leaves it no fewer (the digits that would cancel are in another
//! sum, or in none) is taken only by the step at the root, last and costed whole (see
//! `demanded::whole`).
//!
//! A side that is no low digit is read as one where it can be. Each side is read through its
//! truncations, masks of low bits and zero extensions, the two at the widest width both are
//! read at; a value its known bits put below `2^k` is its own low digit (and its high digit is
//! 0); a `k`-bit side is read back at the other side's width, the narrowing a comparison of
//! digits pushes into its sides undone. The high digit of a side read back is 0 only where
//! the known bits say so: a narrowed sum of two digits carries.
//!
//! Three readings follow the way a handler writes its digits:
//!
//! - A low digit computed apart from its word, at the digit's own width and with the word's
//!   constants reduced to it, is read as the low bits of that word where the sum holds the
//!   word's high digit (`anchors`): lifting it blindly gives another value with the same low
//!   bits, whose high digit meets nothing.
//! - A comparison of the bits `[o, o + n)` of `P` and `Q`, a constant added to either (the
//!   same slice of the value plus the constant shifted), is the comparison of their low
//!   `o + n` bits unless the digit of `P − Q` is all ones and a carry comes into it; it is
//!   read as that where a bit of that digit is known 0 (`middle`). A constant added limb by
//!   limb writes its carries so.
//! - A narrow value added into the middle of a wide one, `extract<o, n>(A) + t` compared
//!   with `t` or with the slice, is the digit of `A + (zext(t) << o)`: the comparison is the
//!   carry out of bit `o + n` of that word (`shifted`), and the limb and its carry out are
//!   slices of it. Digits held in a wider register are compared at their own width first.
//! - Sides that are truncations of wider values (the low digit of a 64-bit word computed in
//!   a 32-bit register) are read at the width of those where the sum reads more bits than
//!   the register has above the digit and holds a high digit of a value that wide: the high
//!   digits are then the word's own.
//!
//! `y != 0` is the borrow `0 <u y` (of a negation).

use super::forms::Parts;
use super::limbs::same_low;
use super::{Fin, Runner, Stop, casts, discard, linear, linear_mba};
use crate::engine::budget::Counter;
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
/// one), which the flag tells. `y != 0` is `0 <u y` (the borrow of a negation: `hi(−Y)` is
/// `−hi(Y) − [lo(Y) != 0]`), told by no first side.
fn borrow(cx: &Context, a: u32) -> Option<(Option<u32>, u32, bool)> {
    let n = cx.node(a);
    if !matches!(n.op, OpCode::Zext | OpCode::Sext) || n.width < 2 {
        return None;
    }
    let c = cx.node(n.a);
    let minus = n.op == OpCode::Sext;
    match c.op {
        OpCode::Ult => Some((Some(c.a), c.b, minus)),
        OpCode::Ne if cx.const_val(c.b).is_some_and(|k| k.is_zero()) => Some((None, c.a, minus)),
        OpCode::Ne if cx.const_val(c.a).is_some_and(|k| k.is_zero()) => Some((None, c.b, minus)),
        // `x != M` for an `x` that is the low `k` bits of a value and `M = 2^k − 1` is `x <u
        // M` (the borrow of subtracting `M`: of adding 1).
        OpCode::Ne => {
            let (x, k) = match (cx.const_val(c.a), cx.const_val(c.b)) {
                (None, Some(_)) => (c.a, c.b),
                (Some(_), None) => (c.b, c.a),
                _ => return None,
            };
            if cx.wid(x) > 64 {
                return None;
            }
            let bits = readings(cx, x).last()?.1;
            let ones = u64::MAX >> (64 - bits);
            (cx.const_val(k)?.limbs()[0] == ones).then_some((Some(x), k, minus))
        }
        _ => None,
    }
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

/// A word one of the sum's high digits is of, with its low digit as the casts pass writes it
/// (the truncation pushed into the word, its constants reduced to the digit's bits) and what
/// that relied on.
#[derive(Clone, Copy)]
struct Anchor {
    low: u32,
    of: u32,
    k: u16,
    fin: Fin,
}

/// The most words of a sum's high digits looked at.
const MAX_ANCHORS: usize = 4;

/// The words the high digits among `terms` are of (see [`Anchor`]), each with its low digit
/// in the two ways the casts pass writes it: pushed in all the way, and down to the slices
/// something else already reads.
fn anchors(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    terms: &[(u32, BitVec)],
) -> Result<Vec<Anchor>, Stop> {
    let mut out: Vec<Anchor> = Vec::new();
    let mut words: Vec<(u32, u16)> = Vec::new();
    for &(a, _) in terms {
        let n = cx.node(a);
        let s = if n.op == OpCode::Zext {
            cx.node(n.a)
        } else {
            n
        };
        let (of, k) = match s.op {
            OpCode::Extract if s.b > 0 => (s.a, u64::from(s.b)),
            OpCode::LShr => match cx.const_val(s.b).and_then(|k| k.to_u64()) {
                Some(k) => (s.a, k),
                None => continue,
            },
            _ => continue,
        };
        let w = cx.wid(of);
        if w > 64 || k == 0 || k >= u64::from(w) || words.contains(&(of, k as u16)) {
            continue;
        }
        if words.len() == MAX_ANCHORS {
            break;
        }
        let k = k as u16;
        words.push((of, k));
        if let Some((low, fin)) = casts::narrowed(r, cx, of, 0, k)? {
            out.push(Anchor { low, of, k, fin });
        }
        if let Some((low, fin)) = casts::narrowed_live(r, cx, of, 0, k)?
            && out
                .last()
                .is_none_or(|a| a.of != of || a.k != k || a.low != low)
        {
            out.push(Anchor { low, of, k, fin });
        }
    }
    Ok(out)
}

/// Whether one of `lows` is `x` or below it through the operators [`lifted`] undoes
/// truncations through.
fn holds(cx: &Context, x: u32, lows: &[u32]) -> bool {
    let mut stack = vec![x];
    let mut seen = 0;
    while let Some(i) = stack.pop() {
        if lows.contains(&i) {
            return true;
        }
        seen += 1;
        if seen > MAX_LIFT {
            break;
        }
        let n = cx.node(i);
        if matches!(
            n.op,
            OpCode::Add
                | OpCode::Sub
                | OpCode::Mul
                | OpCode::And
                | OpCode::Or
                | OpCode::Xor
                | OpCode::Neg
                | OpCode::Not
        ) {
            stack.extend(n.children());
        }
    }
    false
}

/// [`digits`] where a side is a `k`-bit value that holds the low digit of a word one of the
/// sum's high digits is of, written as the casts pass narrows that word (`anchors`): the
/// side is read back as the word, where lifting it blindly gives another value with the same
/// low bits (its constants were reduced to the digit's bits), whose high digit meets nothing.
/// A side read at the word's width already stays as it is read.
fn anchored(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    y: u32,
    anchors: &[Anchor],
) -> Result<Option<(Digit, Digit, u16, Fin)>, Stop> {
    let (rx, ry) = (readings(cx, x), readings(cx, y));
    for (at, first) in anchors.iter().enumerate() {
        let (k, w) = (first.k, cx.wid(first.of));
        // (Once per digit width and word width.)
        if anchors[..at].iter().any(|a| a.k == k && cx.wid(a.of) == w) {
            continue;
        }
        let same: Vec<&Anchor> = anchors
            .iter()
            .filter(|a| a.k == k && cx.wid(a.of) == w)
            .collect();
        let lows: Vec<u32> = same.iter().map(|a| a.low).collect();
        // Each side: the `k`-bit value to read back (and whether it holds an anchor), or
        // the `w`-bit value it is the low `k` bits of.
        let side = |rs: &[(u32, u16)]| {
            let (p, _) = rs.iter().rev().find(|v| v.1 == k).copied()?;
            let wp = cx.wid(p);
            if wp == k {
                Some((p, true, holds(cx, p, &lows)))
            } else {
                (wp == w).then_some((p, false, false))
            }
        };
        let (Some((px, nx, hx)), Some((py, ny, hy))) = (side(&rx), side(&ry)) else {
            continue;
        };
        if !(hx || hy) {
            continue;
        }
        let seed: Vec<(u32, u32)> = same.iter().map(|a| (a.low, a.of)).collect();
        let mut fin = same.iter().fold(Fin::FINAL, |f, a| f.and(a.fin));
        let p = if nx {
            lifted(r, cx, px, w, &mut seed.clone())?
        } else {
            px
        };
        let q = if ny {
            lifted(r, cx, py, w, &mut seed.clone())?
        } else {
            py
        };
        let mut digit = |r: &mut Runner<'_, '_>, cx: &mut Context, of: u32| {
            let (small, f) = below(r, cx, of, k)?;
            if small {
                fin = fin.and(f);
            }
            Ok::<_, Stop>(Digit { of, small })
        };
        let (a, b) = (digit(r, cx, p)?, digit(r, cx, q)?);
        return Ok(Some((a, b, k, fin)));
    }
    Ok(None)
}

/// The sides of a carry's comparison read as digits: the low `at` bits of `p` and `q`.
#[derive(Clone, Copy)]
struct Sides {
    p: Digit,
    q: Digit,
    at: u16,
    /// What the facts used relied on.
    fin: Fin,
    /// The bits `[o, o + n)` of `p − q` that must not all be 1 for the reading to hold (a
    /// comparison of middle digits, see [`middle`]).
    guard: Option<(u16, u16)>,
}

/// `word` at the width of its terms where it is a sum of zero extensions from one width, at
/// least `top` bits (the sum of two values with its carry out, read below the carry: its low
/// bits are those of the sum at the values' own width, whose digits the other words' meet).
fn narrow_word(r: &mut Runner<'_, '_>, cx: &mut Context, word: u32, top: u16) -> Result<u32, Stop> {
    if !matches!(cx.node(word).op, OpCode::Add | OpCode::Sub) {
        return Ok(word);
    }
    let form = linear::form_of(r, cx, word)?;
    let (konst, terms, _) = form.parts();
    let mut w = 0;
    for &(t, _) in terms {
        let n = cx.node(t);
        if n.op != OpCode::Zext || w != 0 && cx.wid(n.a) != w {
            return Ok(word);
        }
        w = cx.wid(n.a);
    }
    if w < top || w == 0 {
        return Ok(word);
    }
    let ww = Width::new(w).map_err(|e| Stop::Error(e.into()))?;
    let low = |v: &BitVec| v.trunc(ww).unwrap_or(*v);
    let narrow: Vec<(u32, BitVec)> = terms
        .iter()
        .map(|&(t, k)| (cx.node(t).a, low(&k)))
        .collect();
    // (Through the terms' own forms: `(v + 1) + c` is `v` plus one constant.)
    let e = linear::emit(r, cx, &linear::Form::of(low(konst), &narrow))?;
    let form = linear::form_of(r, cx, e)?;
    linear::emit(r, cx, &form)
}

/// `x` as the bits `[o, o + n)` of a value, `o > 0`: `extract<o, n>(A)`, or that plus a
/// constant `c`, which is the same slice of `A + (c << o)` (a constant added to a middle
/// digit carries into nothing below it). The value and `o`.
fn middle_of(r: &mut Runner<'_, '_>, cx: &mut Context, x: u32) -> Result<Option<(u32, u16)>, Stop> {
    let n = cx.node(x);
    let slice = |cx: &Context, i: u32| {
        let s = cx.node(i);
        (s.op == OpCode::Extract && s.b > 0 && cx.wid(s.a) <= 64).then_some((s.a, s.b as u16))
    };
    if let Some((a, o)) = slice(cx, x) {
        return Ok(Some((narrow_word(r, cx, a, o + n.width)?, o)));
    }
    if n.op != OpCode::Add || n.width > 64 {
        return Ok(None);
    }
    let (e, c) = match (cx.const_val(n.a), cx.const_val(n.b)) {
        (None, Some(c)) => (n.a, c),
        (Some(c), None) => (n.b, c),
        _ => return Ok(None),
    };
    let Some((a, o)) = slice(cx, e) else {
        return Ok(None);
    };
    let a = narrow_word(r, cx, a, o + n.width)?;
    let w = cx.width_of(a);
    let k = (c.limbs()[0] << o) & (u64::MAX >> (64 - w.bits()));
    let k = BitVec::from_u64(w, k).map_err(|e| Stop::Error(e.into()))?;
    let of = r.build(cx, |cx| {
        let k = cx.mk_const(&k)?;
        cx.c_bin(BinOp::Add, a, k)
    })?;
    // (As the linear pass writes it: `(v + 1) + (c << o)` is `v` plus one constant.)
    let form = linear::form_of(r, cx, of)?;
    Ok(Some((linear::emit(r, cx, &form)?, o)))
}

/// A comparison of the middle digits `[o, o + n)` of `P` and `Q` (of one width, with bits
/// above them), read as one of their low `o + n` bits. With `D = P − Q`, the digit of `P` is
/// the digit of `Q` plus the digit of `D` plus the carry into bit `o`, so it is below the
/// digit of `Q` exactly when that sum carries out of bit `o + n`, unless the digit of `D` is
/// all ones and the carry comes in (the digits are equal then, and the sum carries): the
/// reading holds where some bit of the digit of `D` is known 0 (the guard).
fn middle(r: &mut Runner<'_, '_>, cx: &mut Context, x: u32, y: u32) -> Result<Option<Sides>, Stop> {
    let n = cx.wid(x);
    if n != cx.wid(y) {
        return Ok(None);
    }
    let (Some((p, o)), Some((q, oq))) = (middle_of(r, cx, x)?, middle_of(r, cx, y)?) else {
        return Ok(None);
    };
    let w = cx.wid(p);
    if o != oq || w != cx.wid(q) || o + n >= w {
        return Ok(None);
    }
    middle_sides(r, cx, p, q, o, n, Fin::FINAL).map(Some)
}

/// The sides of a comparison of digits held in a register wider than they are, at the digits'
/// own width `n`: one side is `zext` of an `n`-bit value (the widest such), the other a `zext`
/// too or below `2^n` by its known bits, and the comparison of the `n`-bit values is the
/// same. A slice from above bit 0 stays that slice, shorter, of the value under a mask that
/// keeps its bits (narrowed into a sum, it would be no slice of the word any more);
/// anything else is narrowed. With what the facts used relied on.
fn unextended(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    y: u32,
) -> Result<Option<(u32, u32, Fin)>, Stop> {
    let m = cx.wid(x);
    if m != cx.wid(y) || m > 64 {
        return Ok(None);
    }
    let inner = |cx: &Context, v: u32| {
        let nd = cx.node(v);
        (nd.op == OpCode::Zext).then(|| cx.wid(nd.a))
    };
    let n = match (inner(cx, x), inner(cx, y)) {
        (None, None) => return Ok(None),
        (a, b) => a.unwrap_or(0).max(b.unwrap_or(0)),
    };
    if n >= m {
        return Ok(None);
    }
    let mut fin = Fin::FINAL;
    let mut out = [0; 2];
    for (i, v) in [x, y].into_iter().enumerate() {
        let nd = cx.node(v);
        out[i] = if nd.op == OpCode::Zext {
            if cx.wid(nd.a) == n {
                nd.a
            } else {
                r.build(cx, |cx| cx.c_zext(nd.a, n))?
            }
        } else {
            let (fits, f) = below(r, cx, v, n)?;
            if !fits {
                return Ok(None);
            }
            fin = fin.and(f);
            if nd.op == OpCode::Extract && nd.b > 0 && cx.wid(nd.a) <= 64 {
                let a = cx.node(nd.a);
                let keep = (u64::MAX >> (64 - n)) << nd.b;
                let under = match (a.op, cx.const_val(a.a), cx.const_val(a.b)) {
                    (OpCode::And, None, Some(c)) if c.limbs()[0] & keep == keep => a.a,
                    (OpCode::And, Some(c), None) if c.limbs()[0] & keep == keep => a.b,
                    _ => nd.a,
                };
                r.build(cx, |cx| cx.c_extract(under, nd.b as u16, n))?
            } else {
                let Some((h, f2, _)) = casts::narrowed_from(r, cx, v, 0, n)? else {
                    return Ok(None);
                };
                fin = fin.and(f2);
                h
            }
        };
    }
    Ok(Some((out[0], out[1], fin)))
}

/// The sides of a comparison of the digits `[o, o + n)` of `p` and `q` (see [`middle`]); `fin`
/// is what reading them relied on.
fn middle_sides(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    p: u32,
    q: u32,
    o: u16,
    n: u16,
    mut fin: Fin,
) -> Result<Sides, Stop> {
    let at = o + n;
    let mut digit = |r: &mut Runner<'_, '_>, cx: &mut Context, of: u32| {
        let (small, f) = below(r, cx, of, at)?;
        if small {
            fin = fin.and(f);
        }
        Ok::<_, Stop>(Digit { of, small })
    };
    let (p, q) = (digit(r, cx, p)?, digit(r, cx, q)?);
    Ok(Sides {
        p,
        q,
        at,
        fin,
        guard: Some((o, n)),
    })
}

/// A comparison of middle digits where a side is no slice: a narrow value added into the
/// middle of a wide one, `extract<o, n>(A) + t` against `t` or against the slice. An `n`-bit
/// `t` is the digit `[o, o + n)` of its own shifted word `zext(t) << o`, and the sum is the
/// digit of `A + (zext(t) << o)`: the shifted word is 0 below bit `o`, so nothing carries
/// into the digit, and above it adds `t`.
///
/// The sides are read by their forms modulo `2^n`, around one slice `extract<o, n>(A)` of
/// coefficient 1 with bits of `A` above it:
///
/// - one both sides have (the first in the canonical order): each side is the digit of `A +
///   (c << o) + (zext(t) << o)`, with `c` its constant and `t` its other terms as one
///   `n`-bit value, and `P − Q` is a shifted word;
/// - one of `x` where `y` has none and is the rest of `x` up to a constant `c` (`x = slice +
///   y + c`): `Q` is `zext(y) << o` and `P` is `A + (c << o) + Q`;
/// - `x` a slice and a constant where `y` has none (the borrow of the digit less `y`): `Q` is
///   `zext(y) << o`, or the constant `y` is, shifted.
///
/// The comparison is then one of middle digits as [`middle`] reads it, under its guard, which
/// holds by construction: `Q` or `P − Q` is 0 below bit `o`. With `words`, only around a
/// slice of a word they hold the high digit of above the digit (see [`Anchor`]).
fn shifted(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    y: u32,
    words: Option<&[Anchor]>,
) -> Result<Option<Sides>, Stop> {
    use crate::facts::known::bv_shl;
    let n = cx.wid(x);
    if n != cx.wid(y) || n > 64 {
        return Ok(None);
    }
    let nw = cx.width_of(x);
    let (zero, one) = (BitVec::zero(nw), BitVec::one(nw));
    let (fx, fy) = (linear::form_of(r, cx, x)?, linear::form_of(r, cx, y)?);
    let ((kx, tx, relx), (ky, ty, rely)) = (fx.parts(), fy.parts());
    r.meter
        .charge(Counter::PassWork, (tx.len() + ty.len()) as u64)?;
    let slice = |cx: &Context, t: &(u32, BitVec)| {
        let s = cx.node(t.0);
        t.1 == one
            && s.op == OpCode::Extract
            && s.b > 0
            && cx.wid(s.a) <= 64
            && s.b as u16 + n < cx.wid(s.a)
            && words.is_none_or(|ws| ws.iter().any(|a| a.of == s.a && a.k == s.b as u16 + n))
    };
    let without = |ts: &[(u32, BitVec)], s: u32| -> Vec<(u32, BitVec)> {
        ts.iter().filter(|t| t.0 != s).copied().collect()
    };
    let mut own: Vec<u32> = tx.iter().filter(|t| slice(cx, t)).map(|t| t.0).collect();
    own.sort_by(|a, b| cx.order(*a, *b));
    let shared = own.iter().copied().find(|s| ty.contains(&(*s, one)));
    // The slice, whether `Q` has its word, and each side's constant and value beside it.
    let (s, both, consts, values) = if let Some(s) = shared {
        let mut values = [None; 2];
        for (v, ts) in values.iter_mut().zip([tx, ty]) {
            let rest = without(ts, s);
            if !rest.is_empty() {
                *v = Some(linear::emit(r, cx, &linear::Form::of(zero, &rest))?);
            }
        }
        (s, true, [*kx, *ky], values)
    } else if ty.iter().any(|t| slice(cx, t)) {
        return Ok(None);
    } else {
        let found = own.iter().copied().find(|s| {
            let rest = without(tx, *s);
            rest.is_empty() || rest == ty
        });
        let Some(s) = found else {
            return Ok(None);
        };
        let t = (!ty.is_empty()).then_some(y);
        if tx.len() == 1 {
            let k = if ty.is_empty() { *ky } else { zero };
            (s, false, [*kx, k], [None, t])
        } else {
            let k = BitVec::bin_unchecked(BinOp::Sub, kx, ky);
            (s, false, [k, zero], [t, t])
        }
    };
    let (a, o) = (cx.node(s).a, cx.node(s).b as u16);
    let wide = cx.width_of(a);
    let w = wide.bits();
    let up = |v: &BitVec| bv_shl(&v.zext(wide).unwrap_or(*v), u32::from(o));
    let mut fin = relx.and(rely);
    let mut words = [0u32; 2];
    for i in 0..2 {
        let mut word = if i == 0 || both {
            linear::form_of(r, cx, a)?
        } else {
            linear::Form::of(BitVec::zero(wide), &[])
        };
        word = word.add(&linear::Form::of(up(&consts[i]), &[]));
        if let Some(t) = values[i] {
            // (A truncation of a value of the word's width as its mask, as in `mid_word`.)
            let v = cx.node(t);
            let z = if v.op == OpCode::Extract && v.b == 0 && cx.wid(v.a) == w {
                let m = BitVec::wrapping_from_u64(wide, u64::MAX >> (64 - n));
                r.build(cx, |cx| {
                    let m = cx.mk_const(&m)?;
                    cx.c_bin(BinOp::And, v.a, m)
                })?
            } else {
                r.build(cx, |cx| cx.c_zext(t, w))?
            };
            word = word.add(&linear::form_of(r, cx, z)?.scale(&up(&one)));
        }
        fin = fin.and(word.fin);
        words[i] = linear::emit(r, cx, &word)?;
    }
    middle_sides(r, cx, words[0], words[1], o, n, fin).map(Some)
}

/// `P`, `Q` and `k` when `x` and `y` are the low `k` bits of `P` and `Q` of one width (more
/// than `k`), and what the facts used relied on. Each side is read through its truncations,
/// masks and zero extensions ([`readings`]), at the widest width both are read at, a digit of
/// more than `k` bits standing for its low `k` where its known bits put it below `2^k`.
/// Without such a width, a side is read back at the width of the other, or of the values its
/// truncations read (the narrowing a comparison of digits pushes into its sides undone). A
/// side that holds the low digit of one of `anchors` is read as that word first, and two
/// sides that are one slice from above bit 0 of two values as their middle digits
/// ([`middle`]), also through the zero extensions of a wider register ([`unextended`]). A
/// narrow value added into the middle of a word is read as that word plus the value shifted
/// ([`shifted`]): before the low readings where the sum holds the high digit of the word
/// above the digit, and where they read nothing.
///
/// The sum reads `need` bits of the carry. Where the width both sides are read at leaves
/// fewer above the digit, the sides are truncations of wider values (the low half of a
/// 64-bit word computed in a 32-bit register) and the sum holds a high digit of a value
/// that wide above the same `k` bits, they are read at that width: the high digits are then
/// the word's own, as many as it has.
fn digits(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    y: u32,
    anchors: &[Anchor],
    need: u16,
) -> Result<Option<Sides>, Stop> {
    if cx.wid(x) > 64 {
        return Ok(None);
    }
    if !anchors.is_empty()
        && let Some((p, q, at, fin)) = anchored(r, cx, x, y, anchors)?
    {
        return Ok(Some(Sides {
            p,
            q,
            at,
            fin,
            guard: None,
        }));
    }
    if let Some(found) = middle(r, cx, x, y)? {
        return Ok(Some(found));
    }
    // The sides at the digits' own width where a wider register holds them, and as the
    // middle digits of a word a narrow value is added into: before the low readings where
    // the sum holds that word's high digit above them, after them otherwise.
    let narrow = unextended(r, cx, x, y)?;
    if let Some((x, y, f)) = narrow
        && let Some(mut found) = middle(r, cx, x, y)?
    {
        found.fin = found.fin.and(f);
        return Ok(Some(found));
    }
    let (mx, my, mf) = narrow.unwrap_or((x, y, Fin::FINAL));
    let other = |r: &mut Runner<'_, '_>, cx: &mut Context, words: Option<&[Anchor]>| {
        Ok::<_, Stop>(shifted(r, cx, mx, my, words)?.map(|mut s| {
            s.fin = s.fin.and(mf);
            s
        }))
    };
    if let Some(found) = other(r, cx, Some(anchors))? {
        return Ok(Some(found));
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
    // (Only to the width of a word the sum holds this digit's high digit of: the bits above
    // a register's own width are otherwise nobody's.)
    let wide = lift_width(cx, p).max(lift_width(cx, q));
    let w = if w > k
        && w - k < need
        && wide > w
        && anchors.iter().any(|a| a.k == k && cx.wid(a.of) == wide)
    {
        wide
    } else {
        w
    };
    if w <= k {
        return other(r, cx, None);
    }
    let mut fin = Fin::FINAL;
    let Some(a) = side(r, cx, x, p, kp, k, w, &mut fin)? else {
        return other(r, cx, None);
    };
    let Some(b) = side(r, cx, y, q, kq, k, w, &mut fin)? else {
        return other(r, cx, None);
    };
    Ok(Some(Sides {
        p: a,
        q: b,
        at: k,
        fin,
        guard: None,
    }))
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
pub(super) fn may_expand(cx: &Context, x: u32) -> bool {
    let mut stack = vec![x];
    let (mut seen, mut high) = (0, 0);
    while let Some(i) = stack.pop() {
        seen += 1;
        if seen > 4 * MAX_TERMS {
            return false;
        }
        let n = cx.node(i);
        match n.op {
            // (`a − ~c` is how `a + c + 1` is written: the form reads `~c` as `−c − 1`.)
            OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Not => stack.extend(n.children()),
            _ if borrow(cx, i).is_some() || detects(cx, i).is_some() => return true,
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
/// else still reads the shift, is one term), or as the linear-MBA pass writes that, or the
/// difference of the sides as they are written, where it has fewer terms: `(a + b) − (a ^
/// b)` is `2·(a & b)`, while a difference that cancels to one term as it stands stays that
/// term. An XOR or an OR with a constant is read through
/// the conjunction where that leaves fewer terms (`(a + c) − (a ^ c)` is `2·(a & c)`: the
/// borrow of an XOR with a constant done in limbs). `fin` takes what the facts used relied
/// on.
fn difference(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    p: u32,
    q: u32,
    fin: &mut Fin,
) -> Result<u32, Stop> {
    let raw = r.build(cx, |cx| cx.c_bin(BinOp::Sub, p, q))?;
    let mut form = linear::form_of(r, cx, raw)?;
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
    // Limbs of one word that the two sides hold apart, joined (`lo26(x)·k − lo13(x)·k` is
    // `(x >> 13 & 8191)·(k << 13)`: the high digit of a partial product).
    if let Some((f, _)) = super::limbs::joined(r, cx, &form, cx.wid(raw))? {
        form = f;
    }
    if form.parts().1.len() > 1
        && let Some(f) = linear::unmasked(r, cx, &form)?
    {
        form = f;
    }
    *fin = fin.and(form.fin);
    let d = linear::emit(r, cx, &form)?;
    let (mut best, mut left) = (d, form.parts().1.len());
    // The linear-MBA reading where it has fewer terms: of the difference as the form writes
    // it, and of the sides as they are written (a slice pushed into its operand is no
    // operand of a bitwise term any more: `(t + s) − (t ^ s)` with `t` a truncation of a
    // product is `2·(t & s)` over `t` as it is written).
    if left > 1 {
        for e in [Some(d), (raw != d).then_some(raw)].into_iter().flatten() {
            if let Some(mixed) = linear_mba::normal(r, cx, e)? {
                let n = linear::form_of(r, cx, mixed)?.parts().1.len();
                if n < left {
                    (best, left) = (mixed, n);
                }
            }
        }
    }
    Ok(best)
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

/// The key `t` is merged under, with the constant `t` is above it: `t`, a slice of a sum (or
/// its zero extension), as that slice of the sum's form written out anew: two spellings of
/// one linear form (`a + b - (m + m)` beside `-(m << 1) + (a + b)`, one of them shared with
/// something else) are then one node, and their slices one term. On the way:
///
/// - A form whose coefficients all end in `z` zeros is `2^z·G + c` with `c` its constant,
///   and the low `z` bits of `c` carry nothing: its bits from `lo ≥ z` are those of
///   `G + (c >> z)` from `lo − z` (`extract<20, 7>(x * (953 << 10))` is
///   `extract<10, 7>(x * 953)`), so a partial product shifted into place meets the product
///   itself.
/// - A constant `c_lo + 2^lo·c_hi` above a slice from `lo` adds `c_hi` to the slice, modulo
///   `2^n`: where the slice is all of the term, `c_hi` is the constant returned, and the
///   slices of `X + c` and of `X + c − 2^lo` are one term.
///
/// `fin` takes what the form relied on where it is used.
fn rebased(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    t: u32,
    fin: &mut Fin,
) -> Result<(u32, BitVec), Stop> {
    use crate::facts::known::{bv_lshr, bv_shl, trailing_zeros};
    let none = (t, BitVec::zero(cx.width_of(t)));
    let outer = cx.node(t);
    let slice = if outer.op == OpCode::Zext { outer.a } else { t };
    let s = cx.node(slice);
    if s.op != OpCode::Extract {
        return Ok(none);
    }
    let of = cx.node(s.a).op;
    if !matches!(
        of,
        OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Mul | OpCode::Shl
    ) {
        return Ok(none);
    }
    let (mut lo, n) = (s.b, s.width);
    let form = linear::form_of(r, cx, s.a)?;
    let mut relied = form.fin;
    let z = form
        .parts()
        .1
        .iter()
        .map(|t| trailing_zeros(&t.1))
        .min()
        .unwrap_or(0)
        .min(lo);
    let down = if z > 0 {
        let (konst, terms, _) = form.parts();
        let down: Vec<(u32, BitVec)> = terms.iter().map(|&(a, k)| (a, bv_lshr(&k, z))).collect();
        linear::Form::of(bv_lshr(konst, z), &down)
    } else {
        form
    };
    lo -= z;
    let mut base = linear::emit(r, cx, &down)?;
    let mut above = BitVec::zero(cx.width_of(t));
    if lo > 0 && outer.width == n {
        let form = linear::form_of(r, cx, base)?;
        let (konst, terms, f) = form.parts();
        let high = bv_lshr(konst, lo);
        if !terms.is_empty() && !high.is_zero() {
            let low = BitVec::bin_unchecked(BinOp::Sub, konst, &bv_shl(&high, lo));
            base = linear::emit(r, cx, &linear::Form::of(low, terms))?;
            relied = relied.and(f);
            above = high.trunc(cx.width_of(t)).unwrap_or(above);
        }
    }
    if base == s.a && lo == s.b {
        return Ok(none);
    }
    *fin = fin.and(relied);
    let key = r.build(cx, |cx| {
        let e = cx.c_extract(base, lo as u16, n)?;
        cx.c_zext(e, outer.width)
    })?;
    Ok((key, above))
}

/// The key `t` is merged under (see [`merged`]), the constant it is above it and what that
/// relied on.
fn key_of(r: &mut Runner<'_, '_>, cx: &mut Context, t: u32) -> Result<(u32, BitVec, Fin), Stop> {
    let mut f = Fin::FINAL;
    let e = trimmed(r, cx, t, &mut f)?;
    let (key, above) = rebased(r, cx, e, &mut f)?;
    // The key with every slice in it pushed into its operand, as a carry's digits are
    // written: `hi(a ^ b) & c` beside `(hi(a) ^ hi(b)) & c`.
    let key = match casts::spelled(r, cx, key, 0, cx.wid(key))? {
        Some((s, fs, _)) => {
            f = f.and(fs);
            s
        }
        None => key,
    };
    Ok((key, above, f))
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
    let w = konst.width();
    let mut read = Vec::with_capacity(terms.len());
    for &(t, k) in terms {
        let (key, above, f) = key_of(r, cx, t)?;
        read.push((key, t, k, f, above));
    }
    read.sort_by_key(|v| v.0);
    let mut konst = *konst;
    let mut out: Vec<(u32, BitVec)> = Vec::with_capacity(read.len());
    for group in read.chunk_by(|a, b| a.0 == b.0) {
        if let [(_, t, k, ..)] = group {
            out.push((*t, *k));
            continue;
        }
        let add = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Add, a, b);
        let mul = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Mul, a, b);
        let k = group.iter().fold(BitVec::zero(w), |k, v| add(&k, &v.2));
        for v in group {
            *fin = fin.and(v.3);
            // Each term is the key and its constant.
            konst = add(&konst, &mul(&v.2, &v.4));
        }
        let key = group[0].0;
        // (A term the known bits make a constant is no term.)
        if let Some(c) = cx.const_val(key) {
            konst = add(&konst, &mul(&k, &c));
            continue;
        }
        out.push((key, k));
    }
    let mut form = linear::Form::of(konst, &out);
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
    /// What reading it relied on.
    fin: Fin,
    /// The term of the sum that is the high digit of `q` (with the flag) or of `p` on the
    /// bits the sum is read on (see [`respelled`]): that side's digit is the term as the
    /// sum has it.
    met: Option<(usize, bool)>,
    /// The term of the sum that is the high digit of `d` on the bits the sum is read on (see
    /// [`over_difference`]): the two go.
    gone: Option<usize>,
}

/// `sum`, the low `j` bits of a sum whose own terms are `terms` (those with a carry read
/// aside), as one slice where it is `A + hi_k(P)` with `P` its only high digit: for `P` of
/// `W ≥ k + j` bits, `A + hi_k(P) = hi_k(P + (A << k))` modulo `2^j` (the shifted `A` adds
/// nothing below bit `k`, and above it adds `A`), with `A` taken at `W` bits as the sum has
/// it (terms that are not high digits themselves, checked to be all that `sum` has beside
/// the digit). The word's form is then joined modulo `2^(k + j)` (see `limbs`): the limb
/// products of a schoolbook high limb are the product of the word. With the form's terms
/// counted and the nodes it stops at; `None` when the terms are no limbs of one word.
fn absorbed(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    terms: &[(u32, BitVec)],
    carries: &[Option<Carry>],
    sum: &linear::Form,
    j: u16,
    fin: &mut Fin,
) -> Result<Option<(u32, usize, Vec<u32>)>, Stop> {
    use crate::facts::known::bv_shl;
    let (konst, left, _) = sum.parts();
    let jw = konst.width();
    let low = |v: &BitVec| v.trunc(jw).unwrap_or(*v);
    let all: Vec<(u32, BitVec)> = terms
        .iter()
        .zip(carries)
        .filter(|(_, c)| c.is_none())
        .map(|(t, _)| (t.0, low(&t.1)))
        .collect();
    let plain = &all;
    // The digit: a slice from where a carry read was taken, with which the sum is the
    // digit and these terms (the same form); the first in the canonical order.
    let one = BitVec::one(jw);
    let mut digits: Vec<u32> = left
        .iter()
        .filter(|t| {
            let n = cx.node(t.0);
            t.1 == one
                && n.op == OpCode::Extract
                && cx.wid(n.a) <= 64
                && carries.iter().flatten().any(|c| u32::from(c.at) == n.b)
        })
        .map(|t| t.0)
        .collect();
    if plain.is_empty() || digits.is_empty() {
        return Ok(None);
    }
    digits.sort_by(|a, b| cx.order(*a, *b));
    digits.truncate(2);
    let mut narrow = Vec::with_capacity(plain.len() + 1);
    for &(a, ka) in plain {
        let e = if cx.wid(a) == j {
            a
        } else {
            let Some((e, f, _)) = casts::narrowed_from(r, cx, a, 0, j)? else {
                return Ok(None);
            };
            *fin = fin.and(f);
            e
        };
        narrow.push((e, ka));
    }
    let zero = BitVec::zero(jw);
    let mut found = None;
    for h in digits {
        // The terms that are left beside the digit: all of the sum's own, less the high
        // digits among them that met a carry's (chosen so that what is over gets fewer
        // terms, then checked: the digit and the chosen terms are the sum's form).
        let mut over = linear::Form::of(zero, left).add(&linear::Form::of(zero, &[(h, one)]).neg());
        for &(e, ka) in &narrow {
            over = over.add(&linear::form_of(r, cx, e)?.scale(&ka).neg());
        }
        // (In the canonical order: the choice does not depend on node indices.)
        let mut by_order: Vec<usize> = (0..narrow.len()).collect();
        by_order.sort_by(|a, b| cx.order(plain[*a].0, plain[*b].0));
        let mut kept: Vec<usize> = Vec::with_capacity(narrow.len());
        for i in by_order {
            let (e, ka) = narrow[i];
            if high_digit(cx, plain[i].0) {
                let with = over.add(&linear::form_of(r, cx, e)?.scale(&ka));
                if with.parts().1.len() < over.parts().1.len() {
                    over = with;
                    continue;
                }
            }
            kept.push(i);
        }
        if kept.is_empty() {
            continue;
        }
        let mut check: Vec<(u32, BitVec)> = kept.iter().map(|&i| narrow[i]).collect();
        check.push((h, one));
        let e = linear::emit(r, cx, &linear::Form::of(*konst, &check))?;
        let same = linear::form_of(r, cx, e)?;
        if same.parts().0 == konst && same.parts().1 == left {
            found = Some((h, same.fin, kept));
            break;
        }
    }
    let Some((h, same, kept)) = found else {
        return Ok(None);
    };
    let plain: Vec<(u32, BitVec)> = kept.iter().map(|&i| all[i]).collect();
    let (p, k) = (cx.node(h).a, cx.node(h).b);
    let w = cx.wid(p);
    let wide = cx.width_of(p);
    // The word: `P + (A << k)`, each term of `A` at the word's width.
    let up = |c: &BitVec| bv_shl(&c.zext(wide).unwrap_or(*c), k);
    let form = linear::form_of(r, cx, p)?;
    let mut relied = same.and(form.fin);
    let mut word = form.parts().1.to_vec();
    let mut konst = BitVec::bin_unchecked(BinOp::Add, form.parts().0, &up(konst));
    for &(a, ka) in &plain {
        let wa = cx.wid(a);
        let at = match wa.cmp(&w) {
            core::cmp::Ordering::Equal => a,
            core::cmp::Ordering::Less => r.build(cx, |cx| cx.c_zext(a, w))?,
            core::cmp::Ordering::Greater => r.build(cx, |cx| cx.c_extract(a, 0, w))?,
        };
        let fa = linear::form_of(r, cx, at)?;
        relied = relied.and(fa.fin);
        let ka = up(&ka);
        let (ca, ta, _) = fa.parts();
        konst = BitVec::bin_unchecked(
            BinOp::Add,
            &konst,
            &BitVec::bin_unchecked(BinOp::Mul, ca, &ka),
        );
        word.extend(
            ta.iter()
                .map(|&(t, c)| (t, BitVec::bin_unchecked(BinOp::Mul, &c, &ka))),
        );
    }
    let total = linear::Form::of(konst, &word);
    // Modulo the bits the slice reads; at the word's whole width where that joins as well
    // (the constants are then the word's, the same for every slice of it).
    let m = (k as u16 + j).min(w);
    let Some(mut found) = super::limbs::joined(r, cx, &total, m)? else {
        return Ok(None);
    };
    if m < w
        && let Some(whole) = super::limbs::joined(r, cx, &total, w)?
        && whole.0.parts().1.len() <= found.0.parts().1.len()
    {
        found = whole;
    }
    let (joined, leaves) = found;
    *fin = fin.and(relied).and(joined.fin);
    let base = linear::emit(r, cx, &joined)?;
    let e = r.build(cx, |cx| cx.c_extract(base, k as u16, j))?;
    Ok(Some((e, joined.parts().1.len(), leaves)))
}

/// The term `a` of a `w`-bit sum at `j` bits, with what the narrowing relied on and the nodes
/// it stopped at.
fn narrow_term(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    j: u16,
    w: u16,
) -> Result<Option<(u32, Fin, Vec<u32>)>, Stop> {
    let n = cx.node(a);
    let (from, lo) = match n.op {
        OpCode::Extract if j == w => (n.a, n.b as u16),
        _ if j == w => return Ok(Some((a, Fin::FINAL, vec![a]))),
        _ => (a, 0),
    };
    casts::narrowed_from(r, cx, from, lo, j)
}

/// A carry read as its high digits at the bits a sum is read on: the digits with their
/// coefficients, what reading them relied on and the nodes the narrowings stopped at.
type Read = (Vec<(u32, BitVec)>, Fin, Vec<u32>);

/// A sum with its carries read (see [`settled`]).
struct Settled {
    /// The sum.
    e: u32,
    /// The terms it has.
    left: usize,
    /// The terms it is measured against: its own narrowed, each carry read one term.
    plain: usize,
    fin: Fin,
    stops: Vec<u32>,
}

/// The low `j` bits of the sum of `terms` and `konst` with the carries in `digs` read as
/// their high digits and the terms in `owns` as they are written: the terms that are one
/// value merged ([`merged`]), those of one linear MBA and the limbs of one word joined.
#[allow(clippy::too_many_arguments)]
fn settled(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    terms: &[(u32, BitVec)],
    konst: BitVec,
    carries: &[Option<Carry>],
    digs: &[Option<Read>],
    owns: &[Option<(u32, Fin, Vec<u32>)>],
    j: u16,
) -> Result<Settled, Stop> {
    let jw = konst.width();
    let low = |v: &BitVec| v.trunc(jw).unwrap_or(*v);
    // The terms at `j` bits: `out` with each carry read as its high digits, `rest` without
    // those carries (what the sum is measured against: a term narrowed into a sum is its
    // terms).
    let mut out: Vec<(u32, BitVec)> = Vec::with_capacity(terms.len() + 4);
    let mut rest: Vec<(u32, BitVec)> = Vec::with_capacity(terms.len());
    let mut read = 0;
    let mut stops = Vec::new();
    let mut fin = Fin::FINAL;
    for (i, &(_, k)) in terms.iter().enumerate() {
        let k = low(&k);
        if let Some((ds, f, s)) = &digs[i] {
            read += usize::from(!k.is_zero());
            fin = fin.and(*f);
            stops.extend(s);
            out.extend(ds);
        } else if let Some((h, f, s)) = &owns[i] {
            fin = fin.and(*f);
            stops.extend(s);
            out.push((*h, k));
            rest.push((*h, k));
        }
    }
    // The form over the digits' own terms: one pushed into a sum is a sum, and one that is a
    // constant is no term.
    let flat = |r: &mut Runner<'_, '_>, cx: &mut Context, terms: &[(u32, BitVec)]| {
        let e = linear::emit(r, cx, &linear::Form::of(konst, terms))?;
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
    // The terms beside one high digit taken into the word it is of, where they are its
    // limbs.
    if left > 1
        && read > 0
        && let Some((e2, count, leaves)) = absorbed(r, cx, terms, carries, &sum, j, &mut fin)?
        && count < left
    {
        left = count;
        e = e2;
        stops.extend(leaves);
    }
    // The digits that are bits of one value, where they cancel (`lo13(hi(T)) + (bit(T) <<
    // 13)` beside the digit of `T << 13` a carry is read with: one slice of `T` twice): the
    // sum with its limbs joined, where every term that leaves is one the sum had (slices
    // cut anew are another sum, which the carries were not read for).
    if left > 1
        && read > 0
        && let Some((f, _)) = super::limbs::joined_over(r, cx, &sum, j, true)?
        && f.parts().1.len() < left
        && f.parts()
            .1
            .iter()
            .all(|t| sum.parts().1.iter().any(|s| s.0 == t.0))
    {
        left = f.parts().1.len();
        fin = fin.and(f.fin);
        e = linear::emit(r, cx, &f)?;
    }
    Ok(Settled {
        e,
        left,
        plain,
        fin,
        stops,
    })
}

/// The condition when `a` is a carry detector with a carry in under an extension: `zext` of
/// `e & c | t` with `t` a comparison (see [`detector`]), or `sext` of it (minus one), which
/// the flag tells.
fn detects(cx: &Context, a: u32) -> Option<(u32, bool)> {
    let n = cx.node(a);
    if !matches!(n.op, OpCode::Zext | OpCode::Sext) || n.width < 2 {
        return None;
    }
    let c = cx.node(n.a);
    if c.op != OpCode::Or || c.width != 1 {
        return None;
    }
    let and = |i: u32| cx.node(i).op == OpCode::And;
    let test = |i: u32| matches!(cx.node(i).op, OpCode::Ult | OpCode::Ule | OpCode::Ne);
    (and(c.a) && test(c.b) || and(c.b) && test(c.a)).then_some((n.a, n.op == OpCode::Sext))
}

/// A limb's digit read as bits of a word: the low `n` bits of the value read are
/// `extract<o, n>(word) + extra` modulo `2^n`.
struct Mid {
    word: u32,
    o: u16,
    /// What the digit has beside the slice: terms of `n` bits, no constant.
    extra: linear::Form,
    /// What the reading relied on.
    fin: Fin,
}

/// The low `n` bits of `s` as a detector reads a limb: a sum with its carries read (whatever
/// terms that leaves it: nothing is committed here), anything else narrowed; with what that
/// relied on.
fn limb_digit(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    s: u32,
    n: u16,
    depth: u32,
) -> Result<Option<(u32, Fin)>, Stop> {
    if matches!(cx.node(s).op, OpCode::Add | OpCode::Sub | OpCode::Neg)
        && let Some((e, f, _, _)) = read_sum(r, cx, s, n, depth, true, false)?
    {
        return Ok(Some((e, f)));
    }
    Ok(casts::narrowed_from(r, cx, s, 0, n)?.map(|(h, f, _)| (h, f)))
}

/// The most slices of a limb's sum tried as the word the limb is a digit of.
const MAX_BASES: usize = 3;

/// `v`, the low `n` bits of a value zero-extended, as the bits `[o, o + n)` of a word: the
/// value narrowed to them, a sum with its carries read first (a middle limb is the digits of
/// its operands and the carry into them: `hi(a) + hi(b) + [lo(a + b) <u lo(a)]` is the digit
/// of `a + b`), whether or not that leaves the sum fewer terms: nothing is committed here.
///
/// A sum that is one slice from above bit 0 and a constant is that slice of the word plus the
/// constant shifted. One that is more is read once for each slice `extract<o, n>(B)` it has
/// with coefficient 1 (at most [`MAX_BASES`], in the canonical order): the digit is that
/// slice plus the other terms `A`, which is the digit of `B + (A << o)` (the shifted `A` adds
/// nothing below bit `o`, and above it adds `A`), so the reading is `B` with `A` beside it.
fn middle_words(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    v: u32,
    n: u16,
    depth: u32,
) -> Result<Vec<Mid>, Stop> {
    if cx.wid(v) > 64 {
        return Ok(Vec::new());
    }
    let Some(&(s, _)) = readings(cx, v).iter().rev().find(|x| x.1 == n) else {
        return Ok(Vec::new());
    };
    let Some((d, fin)) = limb_digit(r, cx, s, n, depth)? else {
        return Ok(Vec::new());
    };
    let nw = Width::new(n).map_err(|e| Stop::Error(e.into()))?;
    let none = linear::Form::of(BitVec::zero(nw), &[]);
    if let Some((word, o)) = middle_of(r, cx, d)? {
        return Ok(vec![Mid {
            word,
            o,
            extra: none,
            fin,
        }]);
    }
    if cx.wid(d) != n {
        return Ok(Vec::new());
    }
    let form = linear::form_of(r, cx, d)?;
    let (konst, terms, relied) = form.parts();
    let fin = fin.and(relied);
    let one = BitVec::one(nw);
    let mut bases: Vec<u32> = terms
        .iter()
        .filter(|t| {
            let s = cx.node(t.0);
            t.1 == one && s.op == OpCode::Extract && s.b > 0 && cx.wid(s.a) <= 64
        })
        .map(|t| t.0)
        .collect();
    bases.sort_by(|a, b| cx.order(*a, *b));
    bases.truncate(MAX_BASES);
    let mut out = Vec::with_capacity(bases.len());
    for h in bases {
        r.meter.charge(Counter::PassWork, terms.len() as u64)?;
        let (a, o) = (cx.node(h).a, cx.node(h).b as u16);
        let w = cx.width_of(a);
        let k = (konst.limbs()[0] << o) & (u64::MAX >> (64 - w.bits()));
        let mut f = fin;
        let word = if k == 0 {
            a
        } else {
            let k = BitVec::from_u64(w, k).map_err(|e| Stop::Error(e.into()))?;
            let of = r.build(cx, |cx| {
                let k = cx.mk_const(&k)?;
                cx.c_bin(BinOp::Add, a, k)
            })?;
            let form = linear::form_of(r, cx, of)?;
            f = f.and(form.fin);
            linear::emit(r, cx, &form)?
        };
        let rest: Vec<(u32, BitVec)> = terms.iter().filter(|t| t.0 != h).copied().collect();
        out.push(Mid {
            word,
            o,
            extra: linear::Form::of(BitVec::zero(nw), &rest),
            fin: f,
        });
    }
    Ok(out)
}

/// The word a limb's digit is the bits `[o, o + n)` of (see [`Mid`]): `word + (extra << o)`,
/// each term of `extra` zero-extended to the word's width; `fin` takes what its form relied
/// on.
fn mid_word(r: &mut Runner<'_, '_>, cx: &mut Context, m: &Mid, fin: &mut Fin) -> Result<u32, Stop> {
    use crate::facts::known::bv_shl;
    let (_, extra, _) = m.extra.parts();
    if extra.is_empty() {
        return Ok(m.word);
    }
    let w = cx.width_of(m.word);
    let form = linear::form_of(r, cx, m.word)?;
    let (konst, terms, relied) = form.parts();
    *fin = fin.and(relied);
    let mut all = terms.to_vec();
    for &(t, c) in extra {
        // (A truncation of a value of the word's width as its mask, which is how a digit
        // held up to the word's width is written.)
        let n = cx.node(t);
        let z = if n.op == OpCode::Extract && n.b == 0 && cx.wid(n.a) == w.bits() && w.bits() <= 64
        {
            let m = BitVec::wrapping_from_u64(w, u64::MAX >> (64 - n.width));
            r.build(cx, |cx| {
                let m = cx.mk_const(&m)?;
                cx.c_bin(BinOp::And, n.a, m)
            })?
        } else {
            r.build(cx, |cx| cx.c_zext(t, w.bits()))?
        };
        let c = c.sext(w).map_err(|e| Stop::Error(e.into()))?;
        all.push((z, bv_shl(&c, u32::from(m.o))));
    }
    linear::emit(r, cx, &linear::Form::of(*konst, &all))
}

/// The sides of the comparison a carry is, when `c` (of one bit) is one: `x <u y`, `y != 0`
/// (`0 <u y`), or a detector with a carry in ([`detector`]).
fn carried(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    c: u32,
    anchors: &[Anchor],
    need: u16,
    depth: u32,
) -> Result<Option<Sides>, Stop> {
    let n = cx.node(c);
    let zero = |cx: &Context, i: u32| cx.const_val(i).is_some_and(|k| k.is_zero());
    let y = match n.op {
        OpCode::Ult => return digits(r, cx, n.a, n.b, anchors, need),
        OpCode::Or if depth > 0 => return detector(r, cx, c, anchors, need, depth - 1),
        OpCode::Ne if zero(cx, n.b) => n.a,
        OpCode::Ne if zero(cx, n.a) => n.b,
        _ => return Ok(None),
    };
    let wy = cx.width_of(y);
    let x = r.build(cx, |cx| cx.mk_const(&BitVec::zero(wy)))?;
    digits(r, cx, x, y, anchors, need)
}

/// A carry detector with a carry in, `e & c | (x <u y)`, read as the comparison of low digits
/// it is. A limb in the middle of a word adds the digits `[o, o + n)` of `Y` and `Z` and the
/// carry `c` out of their low `o` bits; with `P = Y + Z`, its sum (the digit of `P`) is below
/// the digit of `Y` exactly when it carries out of bit `o + n`, unless the digit of `Z` is
/// all ones and the carry comes in (the digits are then equal, and it carries): the handler
/// writes that case beside the comparison. So with
///
/// - `x` the digit of `P` and `y` the digit of `Y` (each read as a slice from bit `o` of a
///   word, a sum of digits with its own carries read first; `y != 0` is `0 <u y`, of the
///   word 0),
/// - `e` a test that is true exactly when the digit of `Z = P − Y` is all ones (`f == k`
///   with `f − k` the digit plus one, or minus that, as linear forms modulo `2^n`),
/// - `c` the carry out of the low `o` bits of `Y + Z` (a comparison read as `lo(P') <u
///   lo(Q')` at `o` bits with `P'` the low bits of `P` and `Q'` those of `Y` or of `Z`, or a
///   detector itself),
///
/// the whole is `lo(P) <u lo(Y)` at `o + n` bits. A constant digit `y` is the digit of the
/// constant `P − Z`, with `Z` the word whose digit `e` tests.
fn detector(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    c: u32,
    anchors: &[Anchor],
    need: u16,
    depth: u32,
) -> Result<Option<Sides>, Stop> {
    r.meter.charge(Counter::PassWork, 16)?;
    let node = cx.node(c);
    let and = |cx: &Context, i: u32| cx.node(i).op == OpCode::And;
    let (both, test) = if and(cx, node.a) {
        (node.a, node.b)
    } else {
        (node.b, node.a)
    };
    if node.op != OpCode::Or || !and(cx, both) {
        return Ok(None);
    }
    // The test of a digit and the carry in; the comparison is read below.
    let b = cx.node(both);
    let (eq, cin) = if cx.node(b.a).op == OpCode::Eq {
        (b.a, b.b)
    } else {
        (b.b, b.a)
    };
    let e = cx.node(eq);
    if e.op != OpCode::Eq {
        return Ok(None);
    }
    // `f − k`, 0 exactly when the test holds, modulo `2^n`: of `f == k` with `f` read through
    // its masks and truncations to `n` bits, or of `f == g` (as the compares pass writes
    // `f + g + 1 & M == 0`: `~g == f`), which is `f − g`.
    let konst = |v: BitVec| linear::Form::of(v, &[]);
    let mut fin = Fin::FINAL;
    let (tested, n) = match (cx.const_val(e.a), cx.const_val(e.b)) {
        (None, None) => {
            let n = cx.wid(e.a);
            if n > 64 {
                return Ok(None);
            }
            let (Some((ha, fa)), Some((hb, fb))) = (
                limb_digit(r, cx, e.a, n, depth)?,
                limb_digit(r, cx, e.b, n, depth)?,
            ) else {
                return Ok(None);
            };
            fin = fin.and(fa).and(fb);
            let tested = linear::form_of(r, cx, ha)?.add(&linear::form_of(r, cx, hb)?.neg());
            (tested, n)
        }
        (None, Some(k)) | (Some(k), None) => {
            let v = if cx.const_val(e.a).is_some() {
                e.b
            } else {
                e.a
            };
            let k = k.limbs()[0];
            if cx.wid(v) > 64 {
                return Ok(None);
            }
            let rs = readings(cx, v);
            let (g, n) = rs[rs.len() - 1];
            if n < 64 && k >> n != 0 {
                return Ok(None);
            }
            // (The digit tested may be a limb's own sum, its carry in among its terms.)
            let Some((h, fh)) = limb_digit(r, cx, g, n, depth)? else {
                return Ok(None);
            };
            fin = fin.and(fh);
            let nw = Width::new(n).map_err(|e| Stop::Error(e.into()))?;
            let tested =
                linear::form_of(r, cx, h)?.add(&konst(BitVec::wrapping_from_u64(nw, k)).neg());
            (tested, n)
        }
        _ => return Ok(None),
    };
    let nw = Width::new(n).map_err(|e| Stop::Error(e.into()))?;
    let one = BitVec::one(nw);
    fin = fin.and(tested.fin);
    let same = |a: &linear::Form, b: &linear::Form| {
        a.parts().0 == b.parts().0 && a.parts().1 == b.parts().1
    };
    let mask = u64::MAX >> (64 - n);
    // The digits compared: `x <u y`; `y != 0` (`0 <u y`); or `c <=u d` with a constant, which
    // for an `n`-bit `d` is `d + k <u k` with `k = 2^n − c` (as the compares pass writes the
    // comparison of a digit plus a constant against the constant).
    let konst_of = |cx: &Context, i: u32| cx.const_val(i).map(|k| k.limbs()[0]);
    let t = cx.node(test);
    if cx.wid(t.a) > 64 {
        return Ok(None);
    }
    let (x, y, kd) = match (t.op, konst_of(cx, t.a), konst_of(cx, t.b)) {
        (OpCode::Ne, None, Some(0)) => (None, Some(t.a), 0),
        (OpCode::Ne | OpCode::Ult, Some(0), None) => (None, Some(t.b), 0),
        (OpCode::Ult, None, None) => (Some(t.a), Some(t.b), 0),
        (OpCode::Ult, None, Some(kd)) if kd <= mask => (Some(t.a), None, kd),
        (OpCode::Ult | OpCode::Ule, Some(c), None) => {
            let c = c.wrapping_add(u64::from(t.op == OpCode::Ult));
            if c == 0 || c > mask {
                return Ok(None);
            }
            let kd = c.wrapping_neg() & mask;
            let Some(&(s, _)) = readings(cx, t.b).iter().rev().find(|x| x.1 == n) else {
                return Ok(None);
            };
            let Some((d, fd, _)) = casts::narrowed_from(r, cx, s, 0, n)? else {
                return Ok(None);
            };
            fin = fin.and(fd);
            let kv = BitVec::wrapping_from_u64(nw, kd);
            let x = r.build(cx, |cx| {
                let k = cx.mk_const(&kv)?;
                cx.c_bin(BinOp::Add, d, k)
            })?;
            (Some(x), None, kd)
        }
        _ => return Ok(None),
    };
    // `P` and `Y`, the limb's offset, and the words whose low `o` bits are those of `P`, `Y`
    // and `Z` (the limb's own terms beside its slice are above them).
    let (p, yw, o, lows) = match (x, y, kd) {
        // A constant digit: `Z` is the word the test reads, `Y` the constant `P − Z`.
        (Some(x), None, kd) => {
            let xs = middle_words(r, cx, x, n, depth)?;
            if xs.is_empty() {
                return Ok(None);
            }
            let mut found = None;
            for pm in &xs {
                r.meter.charge(Counter::PassWork, 16)?;
                let (p, o) = (pm.word, pm.o);
                let w = cx.wid(p);
                if o + n >= w {
                    continue;
                }
                // The digit tested, `f − k − 1` or `−(f − k) − 1`, less what the limb has
                // beside its slice: a slice of `Z`'s word.
                let minus = konst(one).neg().add(&pm.extra.neg());
                let digit = [tested.add(&minus), tested.neg().add(&minus)]
                    .iter()
                    .find_map(|f| {
                        let (k0, ts, _) = f.parts();
                        (k0.is_zero() && ts.len() == 1 && ts[0].1 == one).then(|| ts[0].0)
                    });
                let Some(digit) = digit else {
                    continue;
                };
                let s = cx.node(digit);
                if s.op != OpCode::Extract || s.b != u32::from(o) || s.width != n || cx.wid(s.a) < w
                {
                    continue;
                }
                let z = if cx.wid(s.a) == w {
                    s.a
                } else {
                    r.build(cx, |cx| cx.c_extract(s.a, 0, w))?
                };
                let mut f = pm.fin;
                let yw = difference(r, cx, p, z, &mut f)?;
                let Some(k) = cx.const_val(yw) else {
                    continue;
                };
                if (k.limbs()[0] >> o) & mask != kd {
                    continue;
                }
                let word = mid_word(r, cx, pm, &mut f)?;
                found = Some((word, yw, o, [p, yw, z], f));
                break;
            }
            let Some((p, yw, o, lows, f)) = found else {
                return Ok(None);
            };
            fin = fin.and(f);
            (p, yw, o, lows)
        }
        (None, None, _) => return Ok(None),
        (x, Some(y), _) => {
            let ys = middle_words(r, cx, y, n, depth)?;
            if ys.is_empty() {
                return Ok(None);
            }
            let xs = match x {
                Some(x) => {
                    let xs = middle_words(r, cx, x, n, depth)?;
                    if xs.is_empty() {
                        return Ok(None);
                    }
                    Some(xs)
                }
                None => None,
            };
            let mut found = None;
            'pairs: for ym in &ys {
                let (yb, o) = (ym.word, ym.o);
                let w = cx.wid(yb);
                if o + n >= w {
                    continue;
                }
                // (`y != 0` is `0 <u y`: `P` is the word 0.)
                let nothing;
                let ps: &[Mid] = match &xs {
                    Some(xs) => xs,
                    None => {
                        let zero = BitVec::zero(cx.width_of(yb));
                        nothing = [Mid {
                            word: r.build(cx, |cx| cx.mk_const(&zero))?,
                            o,
                            extra: konst(BitVec::zero(nw)),
                            fin: Fin::FINAL,
                        }];
                        &nothing
                    }
                };
                for pm in ps {
                    if pm.o != o || cx.wid(pm.word) != w {
                        continue;
                    }
                    r.meter.charge(Counter::PassWork, 16)?;
                    let mut f = pm.fin.and(ym.fin);
                    // The digit of `Z = P − Y`: that of the words' difference and what the
                    // limbs have beside their slices.
                    let z = difference(r, cx, pm.word, yb, &mut f)?;
                    let Some((hz, fz, _)) = casts::narrowed_from(r, cx, z, o, n)? else {
                        continue;
                    };
                    let digit = linear::form_of(r, cx, hz)?
                        .add(&pm.extra)
                        .add(&ym.extra.neg())
                        .add(&konst(one));
                    if !(same(&tested, &digit) || same(&tested, &digit.neg())) {
                        continue;
                    }
                    f = f.and(fz).and(digit.fin);
                    let p = mid_word(r, cx, pm, &mut f)?;
                    let yw = mid_word(r, cx, ym, &mut f)?;
                    found = Some((p, yw, o, [pm.word, yb, z], f));
                    break 'pairs;
                }
            }
            let Some((p, yw, o, lows, f)) = found else {
                return Ok(None);
            };
            fin = fin.and(f);
            (p, yw, o, lows)
        }
    };
    // The carry in: of the low `o` bits of `P` against those of `Y` or of `Z`.
    let Some(inner) = carried(r, cx, cin, anchors, need, depth)? else {
        return Ok(None);
    };
    if inner.guard.is_some() || inner.at != o || !same_low(r, cx, inner.p.of, lows[0], o, &mut fin)?
    {
        return Ok(None);
    }
    if !(same_low(r, cx, inner.q.of, lows[1], o, &mut fin)?
        || same_low(r, cx, inner.q.of, lows[2], o, &mut fin)?)
    {
        return Ok(None);
    }
    fin = fin.and(inner.fin);
    let at = o + n;
    let mut digit = |r: &mut Runner<'_, '_>, cx: &mut Context, of: u32| {
        let (small, f) = below(r, cx, of, at)?;
        if small {
            fin = fin.and(f);
        }
        Ok::<_, Stop>(Digit { of, small })
    };
    let (p, q) = (digit(r, cx, p)?, digit(r, cx, yw)?);
    Ok(Some(Sides {
        p,
        q,
        at,
        fin,
        guard: None,
    }))
}

/// The most words of a sum's high digits a carry's sides are compared with.
const MAX_WORDS: usize = 4;

/// A carry's sides read as the low digits of other values with the same low `at` bits: the
/// words the sum holds high digits of above bit `at`. `[lo(P) <u lo(Q)]` depends on the low
/// `at` bits of `P` and `Q` only, so it is `hi(P') − hi(Q') − hi(P' − Q')` for any `P'` and
/// `Q'` that have those bits, at any width. Where a word `A` among `terms` (a high digit
/// `extract<at, _>(A)` or `A >>u at`), wider than `P`, has the low `at` bits of `P`, of `Q`
/// or of `P − Q` (by their forms narrowed to them), it is read in that one's place, the
/// others zero-extended to its width, and the third made of the two: the handler's own digit
/// of the word, in a register wider than the limb, then meets the carry's, on as many bits
/// as the register has. (A word of the sides' own width is another spelling of one of them,
/// and a difference over two spellings is no linear MBA any more: measured, it loses.) The
/// sides, and `P' − Q'`.
#[allow(clippy::too_many_arguments)]
fn reanchored(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    terms: &[(u32, BitVec)],
    p: Digit,
    q: Digit,
    d: u32,
    at: u16,
    fin: &mut Fin,
) -> Result<Option<(Digit, Digit, u32)>, Stop> {
    let w = cx.wid(p.of);
    let mut words: Vec<u32> = Vec::new();
    for &(a, _) in terms {
        let n = cx.node(a);
        let s = if n.op == OpCode::Zext {
            cx.node(n.a)
        } else {
            n
        };
        let (of, k) = match s.op {
            OpCode::Extract if s.b > 0 => (s.a, u64::from(s.b)),
            OpCode::LShr => match cx.const_val(s.b).and_then(|k| k.to_u64()) {
                Some(k) => (s.a, k),
                None => continue,
            },
            _ => continue,
        };
        let wa = cx.wid(of);
        if k != u64::from(at) || wa > 64 || wa <= at || words.contains(&of) {
            continue;
        }
        if wa > w {
            words.push(of);
        }
    }
    if words.is_empty() {
        return Ok(None);
    }
    words.sort_by(|a, b| cx.order(*a, *b));
    words.truncate(MAX_WORDS);
    // The first word that has the low bits of each of `P − Q`, `Q` and `P`, all of one
    // width.
    let olds = [d, q.of, p.of];
    let mut news: [Option<u32>; 3] = [None; 3];
    let mut wide = 0;
    let mut f = Fin::FINAL;
    for &a in &words {
        let wa = cx.wid(a);
        if wide != 0 && wa != wide {
            continue;
        }
        for (old, new) in olds.iter().zip(&mut news) {
            if new.is_some() {
                continue;
            }
            r.meter.charge(Counter::PassWork, 16)?;
            if a == *old || same_low(r, cx, a, *old, at, &mut f)? {
                *new = Some(a);
                wide = wa;
                break;
            }
        }
    }
    if (0..3).all(|i| news[i].is_none_or(|a| a == olds[i])) {
        return Ok(None);
    }
    let resized = |r: &mut Runner<'_, '_>, cx: &mut Context, v: u32| {
        let wv = cx.wid(v);
        match wv.cmp(&wide) {
            core::cmp::Ordering::Equal => Ok(v),
            core::cmp::Ordering::Less => r.build(cx, |cx| cx.c_zext(v, wide)),
            core::cmp::Ordering::Greater => r.build(cx, |cx| cx.c_extract(v, 0, wide)),
        }
    };
    let sum = |r: &mut Runner<'_, '_>, cx: &mut Context, a: u32, b: u32, f: &mut Fin| {
        let (fa, fb) = (linear::form_of(r, cx, a)?, linear::form_of(r, cx, b)?);
        *f = f.and(fa.fin).and(fb.fin);
        linear::emit(r, cx, &fa.add(&fb))
    };
    let (p2, q2, d2) = match news {
        [Some(d2), Some(q2), _] => (sum(r, cx, q2, d2, &mut f)?, q2, d2),
        [Some(d2), None, Some(p2)] => (p2, difference(r, cx, p2, d2, &mut f)?, d2),
        [None, Some(q2), Some(p2)] => (p2, q2, difference(r, cx, p2, q2, &mut f)?),
        [Some(d2), None, None] => {
            let q2 = resized(r, cx, q.of)?;
            (sum(r, cx, q2, d2, &mut f)?, q2, d2)
        }
        [None, Some(q2), None] => {
            let d2 = resized(r, cx, d)?;
            (sum(r, cx, q2, d2, &mut f)?, q2, d2)
        }
        [None, None, Some(p2)] => {
            let q2 = resized(r, cx, q.of)?;
            // (A word that is the sum of two values with its carry out, and an XOR or OR
            // of the two subtracted.)
            let d2 = match summands(r, cx, p2, p.of, &mut f)? {
                Some((a, b)) => conjunction(r, cx, a, b, d, wide, &mut f)?,
                None => None,
            };
            let d2 = match d2 {
                Some(d2) => d2,
                None => difference(r, cx, p2, q2, &mut f)?,
            };
            (p2, q2, d2)
        }
        [None, None, None] => return Ok(None),
    };
    *fin = fin.and(f);
    let mut digit = |r: &mut Runner<'_, '_>, cx: &mut Context, of: u32| {
        let (small, f) = below(r, cx, of, at)?;
        if small {
            *fin = fin.and(f);
        }
        Ok::<_, Stop>(Digit { of, small })
    };
    Ok(Some((digit(r, cx, p2)?, digit(r, cx, q2)?, d2)))
}

/// Whether `a` and `b`, of one width, have the same low `o` bits: the difference of their
/// forms is 0 modulo `2^o`, as it stands (a product with its constant reduced to other
/// bits) or with the limbs of one word joined (`lo26(x)·k + lo13(x)·(c << 13)` is `x·(k +
/// (c << 13))` modulo `2^26`: a product computed limb by limb beside the product of the
/// word); the forms of the two as they are, then of the two narrowed to those bits (what
/// is no sum at their width may be one there). `fin` takes what the forms relied on.
fn congruent(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
    o: u16,
    fin: &mut Fin,
) -> Result<bool, Stop> {
    if o == 0 || o > cx.wid(a) || cx.wid(a) != cx.wid(b) {
        return Ok(false);
    }
    let ow = Width::new(o).map_err(|e| Stop::Error(e.into()))?;
    let nothing = |h: &linear::Form| h.parts().0.is_zero() && h.parts().1.is_empty();
    // Whether `f − g` is 0 modulo `2^o`, and what that relied on.
    let zero = |r: &mut Runner<'_, '_>, cx: &mut Context, x: u32, y: u32| {
        let (f, g) = (linear::form_of(r, cx, x)?, linear::form_of(r, cx, y)?);
        let relied = f.fin.and(g.fin);
        let over = f.add(&g.neg()).reduce(ow);
        if x == y || nothing(&over) {
            return Ok::<_, Stop>(Some(relied));
        }
        Ok(match super::limbs::joined(r, cx, &over, o)? {
            Some((h, _)) if nothing(&h) => Some(relied.and(h.fin)),
            _ => None,
        })
    };
    if let Some(relied) = zero(r, cx, a, b)? {
        *fin = fin.and(relied);
        return Ok(true);
    }
    if o == cx.wid(a) {
        return Ok(false);
    }
    let (Some((x, fx, _)), Some((y, fy, _))) = (
        casts::narrowed_from(r, cx, a, 0, o)?,
        casts::narrowed_from(r, cx, b, 0, o)?,
    ) else {
        return Ok(false);
    };
    let Some(relied) = zero(r, cx, x, y)? else {
        return Ok(false);
    };
    *fin = fin.and(relied).and(fx).and(fy);
    Ok(true)
}

/// The words of `w` bits whose high digit above bit `at` a term among `terms` is, on no
/// fewer bits than the sum is read on (`c·extract<at, n>(A)`, its zero extension, or `c·(A >>u
/// at)`), with a coefficient that is `k` (the flag: the digit goes with a carry's `−k·hi(Q)`)
/// or `−k` (with its `k·hi(P)`), and the term; in the canonical order, a word once (which is
/// found does not depend on node indices).
fn digit_words(
    cx: &Context,
    terms: &[(u32, BitVec)],
    k: &BitVec,
    w: u16,
    at: u16,
) -> Vec<(u32, bool, usize)> {
    let jw = k.width();
    let minus = BitVec::bin_unchecked(BinOp::Sub, &BitVec::zero(jw), k);
    let mut words: Vec<(u32, bool, usize)> = Vec::new();
    for (i, &(a, c)) in terms.iter().enumerate() {
        let n = cx.node(a);
        let s = if n.op == OpCode::Zext {
            cx.node(n.a)
        } else {
            n
        };
        let (of, lo) = match s.op {
            OpCode::Extract if s.b > 0 => (s.a, u64::from(s.b)),
            OpCode::LShr => match cx.const_val(s.b).and_then(|k| k.to_u64()) {
                Some(k) => (s.a, k),
                None => continue,
            },
            _ => continue,
        };
        let c = c.trunc(jw).unwrap_or(c);
        let bits = if s.op == OpCode::Extract {
            s.width
        } else {
            w.saturating_sub(at)
        };
        if lo != u64::from(at) || cx.wid(of) != w || bits < jw.bits() {
            continue;
        }
        if c == *k || c == minus {
            words.push((of, c == *k, i));
        }
    }
    words.sort_by(|a, b| {
        cx.order(a.0, b.0)
            .then_with(|| cx.order(terms[a.2].0, terms[b.2].0))
    });
    words.dedup_by_key(|v| v.0);
    words
}

/// `v` when `x` is `(v & m) << s` with a constant `s < at` and a mask `m` that has the bits
/// below `at − s`: a word shifted left with the bits a digit of `at` bits does not read
/// masked off before the shift. Its low `at` bits are those of `v << s`.
fn masked_shift(cx: &Context, x: u32, at: u16) -> Option<(u32, u16)> {
    let n = cx.node(x);
    if n.op != OpCode::Shl || n.width > 64 {
        return None;
    }
    let s = cx.const_val(n.b)?.to_u64().filter(|s| *s < u64::from(at))? as u16;
    let a = cx.node(n.a);
    if a.op != OpCode::And {
        return None;
    }
    let (v, m) = match (cx.const_val(a.a), cx.const_val(a.b)) {
        (Some(m), None) => (a.b, m.limbs()[0]),
        (None, Some(m)) => (a.a, m.limbs()[0]),
        _ => return None,
    };
    let low = (1u64 << (at - s)) - 1;
    (m & low == low).then_some((v, s))
}

/// A carry's sides read over a shifted word, where one is its low digit written with the
/// shift's operand masked ([`masked_shift`]): the low digit of `T << s` in limbs of `at` bits
/// is `(T & (2^(at − s) − 1)) << s`. `[lo(P) <u lo(Q)]` depends on the low `at` bits of `P`
/// and `Q` only, so it is `hi(P') − hi(Q') − hi(P' − Q')` for any `P'` and `Q'` that have
/// those bits: the side is read as `v << s` where that leaves the difference fewer terms
/// (`(T + (T << s)) − (T << s)` is `T`, while less the masked digit it is two terms that meet
/// nothing). The sides and their difference.
fn unmasked(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    p: Digit,
    q: Digit,
    d: u32,
    at: u16,
    fin: &mut Fin,
) -> Result<Option<(Digit, Digit, u32)>, Stop> {
    let (sp, sq) = (masked_shift(cx, p.of, at), masked_shift(cx, q.of, at));
    if sp.is_none() && sq.is_none() {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, 16)?;
    let w = cx.width_of(p.of);
    let whole = |r: &mut Runner<'_, '_>, cx: &mut Context, old: u32, s: Option<(u32, u16)>| {
        let Some((v, s)) = s else {
            return Ok::<_, Stop>(old);
        };
        r.build(cx, |cx| {
            let k = cx.mk_const(&BitVec::wrapping_from_u64(w, u64::from(s)))?;
            cx.c_bin(BinOp::Shl, v, k)
        })
    };
    let (p2, q2) = (whole(r, cx, p.of, sp)?, whole(r, cx, q.of, sq)?);
    let mut relied = Fin::FINAL;
    let over = difference(r, cx, p2, q2, &mut relied)?;
    let (fo, fd) = (linear::form_of(r, cx, over)?, linear::form_of(r, cx, d)?);
    if fo.parts().1.len() >= fd.parts().1.len() {
        return Ok(None);
    }
    *fin = fin.and(relied).and(fo.fin);
    let mut digit = |r: &mut Runner<'_, '_>, cx: &mut Context, of: u32| {
        let (small, f) = below(r, cx, of, at)?;
        if small {
            *fin = fin.and(f);
        }
        Ok::<_, Stop>(Digit { of, small })
    };
    Ok(Some((digit(r, cx, p2)?, digit(r, cx, q2)?, over)))
}

/// A carry's sides read over a word of their own width that the sum holds the high digit
/// of, where one of them is another spelling of it. `[lo(P) <u lo(Q)]` depends on the low
/// `at` bits of `P` and `Q` only, so it is `hi(P') − hi(Q') − hi(P' − Q')` for any `P'` and
/// `Q'` that have those bits. Where a word `A` among `terms` (`c·extract<at, n>(A)` or
/// `c·(A >>u at)`, on no fewer bits than the sum is read on) has the low `at` bits of `Q`
/// ([`congruent`]: a product with its constant reduced to other bits, or computed limb by
/// limb) and `c` is the carry's coefficient `k`, `Q'` is `A`: the sum's digit of `A` goes
/// with the carry's `−hi(A)`. The other side is the one of `P` (as it is: `P` written over
/// `A`) and `A + D` (`D = P − Q` as it was: `P` written over `Q`) that leaves the
/// difference fewer terms, so that none is taken over two spellings. Where `A` has the low
/// bits of `P` and `c` is `−k`, likewise with `P' = A` and `Q'` one of `Q` and `A − D`. The
/// sides, their difference, and the term met with the side it is the digit of (`Q'`: true).
#[allow(clippy::too_many_arguments, clippy::type_complexity)]
fn respelled(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    terms: &[(u32, BitVec)],
    k: &BitVec,
    p: Digit,
    q: Digit,
    d: u32,
    at: u16,
    fin: &mut Fin,
) -> Result<Option<(Digit, Digit, u32, (usize, bool))>, Stop> {
    let w = cx.wid(p.of);
    // The words that are arithmetic themselves (a mask of a side is the side, less of it).
    let mut words = digit_words(cx, terms, k, w, at);
    words.retain(|v| {
        v.0 != p.of
            && v.0 != q.of
            && matches!(
                cx.node(v.0).op,
                OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Mul | OpCode::Shl
            )
    });
    words.truncate(MAX_WORDS);
    for (a, with_q, term) in words {
        r.meter.charge(Counter::PassWork, 16)?;
        let mut f = Fin::FINAL;
        let old = if with_q { q.of } else { p.of };
        if !congruent(r, cx, a, old, at, &mut f)? {
            continue;
        }
        // The difference as it was, or over the word.
        let (fa, fd) = (linear::form_of(r, cx, a)?, linear::form_of(r, cx, d)?);
        let mut relied = f;
        let over = if with_q {
            difference(r, cx, p.of, a, &mut relied)?
        } else {
            difference(r, cx, a, q.of, &mut relied)?
        };
        let fo = linear::form_of(r, cx, over)?;
        let (p2, q2, d2) = if fo.parts().1.len() < fd.parts().1.len() {
            f = relied.and(fo.fin);
            if with_q {
                (p.of, a, over)
            } else {
                (a, q.of, over)
            }
        } else {
            f = f.and(fa.fin).and(fd.fin);
            let other = if with_q {
                fa.add(&fd)
            } else {
                fa.add(&fd.neg())
            };
            let other = linear::emit(r, cx, &other)?;
            if with_q { (other, a, d) } else { (a, other, d) }
        };
        *fin = fin.and(f);
        let mut digit = |r: &mut Runner<'_, '_>, cx: &mut Context, of: u32| {
            let (small, f) = below(r, cx, of, at)?;
            if small {
                *fin = fin.and(f);
            }
            Ok::<_, Stop>(Digit { of, small })
        };
        return Ok(Some((
            digit(r, cx, p2)?,
            digit(r, cx, q2)?,
            d2,
            (term, with_q),
        )));
    }
    Ok(None)
}

/// Whether the carry `m` may make its word ([`widened`]): one added, whose difference is the
/// window's own (the sides' terms cancel in it, as in `(a + b) − a`, or one of the two is a
/// constant). A difference that had to be built is no operand of the word's sum.
fn makes(r: &mut Runner<'_, '_>, cx: &mut Context, m: &Wide) -> Result<bool, Stop> {
    if m.minus {
        return Ok(false);
    }
    let np = linear::form_of(r, cx, m.p.of)?.parts().1.len();
    let nq = linear::form_of(r, cx, m.q.of)?.parts().1.len();
    let nd = linear::form_of(r, cx, m.d)?.parts().1.len();
    Ok(nd < np + nq || nq == 0 || nd == 0)
}

/// A carry whose sides have fewer bits above the digit than the sum reads: the sides `p` and
/// `q` of `W` bits, their difference `d`, the digits' width `at`, of the term `i` of the sum.
#[derive(Clone, Copy)]
struct Wide {
    i: usize,
    p: Digit,
    q: Digit,
    d: u32,
    at: u16,
    minus: bool,
    fin: Fin,
}

/// The most words of a sum read wider, and the most carries of one of them tried as the one
/// that makes the word.
const MAX_WIDE: usize = 4;

/// `a` and `b` when `word` is `zext(a) + zext(b)`, the sum with its carry out of two values
/// of the width of `p` whose sum at that width is `p` (by their forms); `fin` takes what the
/// forms relied on.
fn summands(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    word: u32,
    p: u32,
    fin: &mut Fin,
) -> Result<Option<(u32, u32)>, Stop> {
    let w = cx.wid(p);
    let form = linear::form_of(r, cx, word)?;
    let (konst, terms, relied) = form.parts();
    let &[(za, ka), (zb, kb)] = terms else {
        return Ok(None);
    };
    let one = BitVec::one(konst.width());
    let (na, nb) = (cx.node(za), cx.node(zb));
    if !konst.is_zero()
        || ka != one
        || kb != one
        || na.op != OpCode::Zext
        || nb.op != OpCode::Zext
        || cx.wid(na.a) != w
        || cx.wid(nb.a) != w
    {
        return Ok(None);
    }
    let (fa, fb) = (linear::form_of(r, cx, na.a)?, linear::form_of(r, cx, nb.a)?);
    let (sum, fp) = (fa.add(&fb), linear::form_of(r, cx, p)?);
    if sum.parts().0 != fp.parts().0 || sum.parts().1 != fp.parts().1 {
        return Ok(None);
    }
    *fin = fin.and(relied).and(sum.fin).and(fp.fin);
    Ok(Some((na.a, nb.a)))
}

/// `S − zext(Q)` at `wide` bits, for `S = zext(a) + zext(b)` the sum of two `W`-bit values
/// with its carry out and a `Q` whose difference from it at `W` bits, `d = (a + b) − Q`, is
/// `2·(a & b)` or `a & b` (one term of its form, the conjunction of two values with the
/// forms of `a` and `b`): `Q` is then `a ^ b` or `a | b`, which at any width is `a + b −
/// 2·(a & b)` or `a + b − (a & b)`, so the difference is `2·zext(a & b)` or `zext(a & b)`
/// whatever way `Q` is written. `fin` takes what the forms relied on.
fn conjunction(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
    d: u32,
    wide: u16,
    fin: &mut Fin,
) -> Result<Option<u32>, Stop> {
    let w = cx.width_of(d);
    let form = linear::form_of(r, cx, d)?;
    let (konst, terms, relied) = form.parts();
    let &[(m, c)] = terms else {
        return Ok(None);
    };
    let node = cx.node(m);
    let twice = c == BitVec::wrapping_from_u64(w, 2);
    if !konst.is_zero() || node.op != OpCode::And || !(twice || c == BitVec::one(w)) {
        return Ok(None);
    }
    let mut f = relied;
    let mut same = |r: &mut Runner<'_, '_>, cx: &mut Context, u: u32, v: u32| {
        if u == v {
            return Ok::<_, Stop>(true);
        }
        let (fu, fv) = (linear::form_of(r, cx, u)?, linear::form_of(r, cx, v)?);
        if fu.parts().0 != fv.parts().0 || fu.parts().1 != fv.parts().1 {
            return Ok(false);
        }
        f = f.and(fu.fin).and(fv.fin);
        Ok(true)
    };
    if !(same(r, cx, node.a, a)? && same(r, cx, node.b, b)?
        || same(r, cx, node.a, b)? && same(r, cx, node.b, a)?)
    {
        return Ok(None);
    }
    *fin = fin.and(f);
    let ww = Width::new(wide).map_err(|e| Stop::Error(e.into()))?;
    let zm = r.build(cx, |cx| cx.c_zext(m, wide))?;
    let k = BitVec::wrapping_from_u64(ww, if twice { 2 } else { 1 });
    let out = linear::form_of(r, cx, zm)?.scale(&k);
    *fin = fin.and(out.fin);
    Ok(Some(linear::emit(r, cx, &out)?))
}

/// The carries of `group`, comparisons of the low `k` bits of one `P` of `W` bits against
/// those of `Q_i`, read for a sum that reads `j > W − k` bits of them, at `W'` bits: twice
/// `W` where that is at least `k + j` and at most 64 (one width for a word whatever reads
/// it), `k + j` otherwise, at most 64.
///
/// The carry `g` makes the word: `S = zext(Q_g) + zext(D_g)` with `D_g = P − Q_g` at `W`
/// bits, the sum of the two with its carry out. `lo(P) <u lo(Q)` is the carry of adding the
/// low digits of `Q` and `D`, and of the integers `Q + D = 2^k·(hi(Q) + hi(D) + carry) +
/// lo(P)`, so the carry is `hi(S) − hi(Q_g) − hi(D_g)` on any number of bits, every digit
/// zero-extended (`hi(a) + hi(b) + [lo(a + b) <u lo(a)]` is the high digit of `zext(a) +
/// zext(b)`).
///
/// The others are read against that word: `[lo(P) <u lo(Q)]` depends on the low `k` bits of
/// its sides only, and `S` is `P` modulo `2^W`, so it is `hi(S) − hi(Q') − hi(S − Q')`
/// modulo `2^(W' − k)` with `Q'` the zero extension of `Q`; `None` for one where `W' − k` is
/// below `j`. The borrow of `a + b − 2·(a & b)` out of `a + b` has the digit of `2·zext(a &
/// b)`, the handler's own and-term ([`conjunction`]).
fn widened(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    group: &[Wide],
    g: usize,
    j: u16,
) -> Result<Vec<Option<Carry>>, Stop> {
    let (w, at) = (cx.wid(group[0].p.of), group[0].at);
    let wide = if at + j <= 2 * w && 2 * w <= 64 {
        2 * w
    } else {
        (at + j).min(64)
    };
    let mut out = vec![None; group.len()];
    if wide <= w {
        return Ok(out);
    }
    let modular = j <= wide - at;
    let maker = &group[g];
    let (zq, zd) = (
        r.build(cx, |cx| cx.c_zext(maker.q.of, wide))?,
        r.build(cx, |cx| cx.c_zext(maker.d, wide))?,
    );
    let (fq, fd) = (linear::form_of(r, cx, zq)?, linear::form_of(r, cx, zd)?);
    let mut relied = fq.fin.and(fd.fin);
    let word = linear::emit(r, cx, &fq.add(&fd))?;
    let (small, fs) = below(r, cx, word, at)?;
    if small {
        relied = relied.and(fs);
    }
    for (n, m) in group.iter().enumerate() {
        let mut fin = m.fin.and(relied);
        let d = if n == g {
            m.d
        } else if !modular {
            continue;
        } else if let Some(d) = conjunction(r, cx, maker.q.of, maker.d, m.d, wide, &mut fin)? {
            d
        } else {
            let zq = r.build(cx, |cx| cx.c_zext(m.q.of, wide))?;
            difference(r, cx, word, zq, &mut fin)?
        };
        out[n] = Some(Carry {
            p: Digit { of: word, small },
            q: m.q,
            d,
            at,
            minus: m.minus,
            fin,
            met: None,
            gone: None,
        });
    }
    Ok(out)
}

/// The carry `c`, of a term with the coefficient `k` at `j` bits of a `w`-bit sum, read as
/// its high digits at `j` bits: all of a digit's bits, zero-extended, where it has fewer. A
/// side whose digit a term of the sum is (`c.met`, an index into `terms`) has it as the sum
/// does: the two go together whatever each is narrowed to. `None` where a digit is not
/// narrowed.
fn carry_digits(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    c: &Carry,
    k: BitVec,
    j: u16,
    terms: &[(u32, BitVec)],
    w: u16,
) -> Result<Option<Read>, Stop> {
    let neg = |v: &BitVec| BitVec::bin_unchecked(BinOp::Sub, &BitVec::zero(v.width()), v);
    let k = if c.minus { neg(&k) } else { k };
    let own = |with_q: bool| c.met.filter(|m| m.1 == with_q).map(|m| terms[m.0].0);
    // The high digit of a value below `2^k` is 0.
    let highs = [
        (!c.p.small).then_some((c.p.of, k, own(false))),
        (!c.q.small).then_some((c.q.of, neg(&k), own(true))),
        Some((c.d, neg(&k), c.gone.map(|t| terms[t].0))),
    ];
    let mut ds = Vec::with_capacity(3);
    let (mut relied, mut stopped) = (c.fin, Vec::new());
    for (v, k, own) in highs.into_iter().flatten() {
        if let Some(t) = own {
            let Some((h, f, s)) = narrow_term(r, cx, t, j, w)? else {
                return Ok(None);
            };
            relied = relied.and(f);
            stopped.extend(s);
            ds.push((h, k));
            continue;
        }
        let bits = j.min(cx.wid(v) - c.at);
        let Some((h, f, s)) = casts::narrowed_from(r, cx, v, c.at, bits)? else {
            return Ok(None);
        };
        relied = relied.and(f);
        stopped.extend(s);
        ds.push((r.build(cx, |cx| cx.c_zext(h, j))?, k));
    }
    Ok(Some((ds, relied, stopped)))
}

/// The carry `i` of a sum read on `j` bits, over the word the sum holds the high digit of
/// its difference of. `[lo(P) <u lo(Q)]` depends on the low `at` bits of `P` and `Q` only,
/// so it is `hi(P') − hi(Q') − hi(D')` for any `D'` that has the low `at` bits of `P − Q`,
/// with `P' = Q + D'` and `Q' = Q`, or `P' = P` and `Q' = P − D'` (modulo `2^(W − at)`, so
/// only where `j` is no more). Where a term `k·extract<o, n>(A)` of the sum (or its zero
/// extension, or `k·(A >>u o)`; `n ≥ j`, `o ≤ at`, `A` of the sides' width `W`) has the
/// carry's coefficient `k`, and `A << (at − o)` has the low `at` bits of `P − Q`
/// ([`congruent`]), `D'` is `A << (at − o)`: its bits `[at, at + j)` are the bits `[o, o +
/// j)` of `A`, the term itself, which goes with the carry's `−k·hi(D')`. (A partial product
/// `a·c` added at bit `s` of a wider sum is so written: the sum holds `a·c >>u (at − s)`,
/// what of it is above the low limb, and the carry's sides are other spellings of the sums
/// with and without it, the product of the word say.)
///
/// Where `D'` is `P − Q` itself in another spelling, the sides stay. Otherwise the side
/// kept is the one whose digit a term of the sum is, then the one another carry of the sum
/// has (in a chain of carries the sum before is the next one's side); with both or neither,
/// the one that leaves the other fewer terms, `Q` on a tie. (A `Q` below `2^at` is no
/// reason to keep it: where it is the low limb of an addend, `P − D'` is the addend, whose
/// high digit the handler has elsewhere. Measured: kept, 90 results of the sample grow.)
fn over_difference(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    terms: &[(u32, BitVec)],
    carries: &[Option<Carry>],
    i: usize,
    j: u16,
) -> Result<Option<Carry>, Stop> {
    let Some(c) = carries[i] else {
        return Ok(None);
    };
    let (w, at) = (cx.wid(c.p.of), c.at);
    if c.gone.is_some() || j > w - at {
        return Ok(None);
    }
    let jw = Width::new(j).map_err(|e| Stop::Error(e.into()))?;
    let low = |v: &BitVec| v.trunc(jw).unwrap_or(*v);
    let k = low(&terms[i].1);
    let k = if c.minus {
        BitVec::bin_unchecked(BinOp::Sub, &BitVec::zero(jw), &k)
    } else {
        k
    };
    // The terms that are high digits with the carry's coefficient: the word and the bit.
    let mut words: Vec<(u32, u16, usize)> = Vec::new();
    for (t, &(a, ka)) in terms.iter().enumerate() {
        if carries[t].is_some()
            || low(&ka) != k
            || carries.iter().flatten().any(|o| o.gone == Some(t))
        {
            continue;
        }
        let n = cx.node(a);
        let s = if n.op == OpCode::Zext {
            cx.node(n.a)
        } else {
            n
        };
        let (of, o) = match s.op {
            OpCode::Extract if s.b > 0 && s.width >= j => (s.a, u64::from(s.b)),
            OpCode::LShr => match cx.const_val(s.b).and_then(|k| k.to_u64()) {
                Some(k) => (s.a, k),
                None => continue,
            },
            _ => continue,
        };
        if o == 0 || o > u64::from(at) || cx.wid(of) != w {
            continue;
        }
        words.push((of, o as u16, t));
    }
    words.sort_by(|a, b| {
        cx.order(a.0, b.0)
            .then(a.1.cmp(&b.1))
            .then_with(|| cx.order(terms[a.2].0, terms[b.2].0))
    });
    words.truncate(MAX_WORDS);
    let wide = cx.width_of(c.p.of);
    for (a, o, term) in words {
        r.meter.charge(Counter::PassWork, 16)?;
        let mut f = c.fin;
        // `A << (at − o)`, as the linear pass writes it.
        let fa = linear::form_of(r, cx, a)?;
        let up = BitVec::from_u64(wide, 1u64 << (at - o)).map_err(|e| Stop::Error(e.into()))?;
        let fd = fa.scale(&up);
        let d = linear::emit(r, cx, &fd)?;
        // The difference as it is, in another spelling: its digit is the term, and the sides
        // stay. (One that is the word but for a constant has its digit merged with the term
        // as it is: see `rebased`.)
        let same = d == c.d || {
            let over = difference(r, cx, d, c.d, &mut f)?;
            match cx.const_val(over) {
                Some(k) if k.is_zero() => true,
                Some(_) => return Ok(None),
                None => false,
            }
        };
        if same {
            return Ok(Some(Carry {
                fin: f.and(fd.fin),
                gone: Some(term),
                ..c
            }));
        }
        if !congruent(r, cx, c.d, d, at, &mut f)? {
            continue;
        }
        f = f.and(fd.fin);
        let shared = |v: u32| {
            carries
                .iter()
                .enumerate()
                .any(|(n, o)| n != i && o.is_some_and(|o| o.p.of == v || o.q.of == v))
        };
        let (fp, fq) = (
            linear::form_of(r, cx, c.p.of)?,
            linear::form_of(r, cx, c.q.of)?,
        );
        let (with_p, with_q) = (fp.add(&fd.neg()), fq.add(&fd));
        // A side whose digit is a term of the sum stays.
        let keep_p = match c.met {
            Some((_, with_q)) => !with_q,
            None => {
                let (hp, hq) = (shared(c.p.of), shared(c.q.of));
                if hp != hq {
                    hp
                } else {
                    with_p.parts().1.len() < with_q.parts().1.len()
                }
            }
        };
        let (p, q) = if keep_p {
            f = f.and(fp.fin);
            (c.p.of, linear::emit(r, cx, &with_p)?)
        } else {
            f = f.and(fq.fin);
            (linear::emit(r, cx, &with_q)?, c.q.of)
        };
        let mut digit = |r: &mut Runner<'_, '_>, cx: &mut Context, of: u32, was: Digit| {
            if of == was.of {
                return Ok::<_, Stop>(was);
            }
            let (small, fs) = below(r, cx, of, at)?;
            if small {
                f = f.and(fs);
            }
            Ok(Digit { of, small })
        };
        let (p, q) = (digit(r, cx, p, c.p)?, digit(r, cx, q, c.q)?);
        return Ok(Some(Carry {
            p,
            q,
            d,
            fin: f,
            gone: Some(term),
            ..c
        }));
    }
    Ok(None)
}

/// The low `j` bits of the sum `x` (a node of `j` bits) with its carry terms read as high
/// digits, when that leaves fewer terms; with what the facts used relied on and the nodes the
/// narrowing stopped at.
///
/// A carry of digits of `W`-bit values is read where `j ≤ W − k`, and at any `j` where `Q +
/// (P − Q)` cannot wrap (by the known bits): `P ≥ Q` then, and the identity holds of the
/// integers, each high digit zero-extended. The terms of such a sum are merged as
/// [`merged`] reads them, the high digits written as shifts among them.
///
/// With `ties`, the reading is also returned where it reads a carry and leaves the sum no
/// fewer terms (the last value tells): the digits that would cancel are then in no term of
/// this sum. They may be in another one, or cost nothing because the words they are of are
/// there already, which only a caller that sees every sum can tell (the step at the root,
/// see `demanded::whole`). The nodes such a reading stops at are no measure of what it
/// needs: a word it built (the difference of a carry's sides) is among them.
#[allow(clippy::type_complexity)]
pub(super) fn expanded(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    j: u16,
    ties: bool,
) -> Result<Option<(u32, Fin, Vec<u32>, bool)>, Stop> {
    read_sum(r, cx, x, j, DETECTORS, false, ties)
}

/// The most detectors with a carry in read one inside another (a limb's carry in is the
/// detector of the limb below; its digit is a sum with that carry).
const DETECTORS: u32 = 3;

/// [`expanded`], with `depth` the detectors that may still be read inside one another, and
/// with `any` also where the sum gets no fewer terms (a limb's sum read for a detector's
/// use: what the word is, not what the sum is replaced by); with `ties`, also where it gets
/// no fewer and a carry is read.
#[allow(clippy::type_complexity)]
fn read_sum(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    j: u16,
    depth: u32,
    any: bool,
    ties: bool,
) -> Result<Option<(u32, Fin, Vec<u32>, bool)>, Stop> {
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
    // The words the sum's high digits are of: a carry's sides may be their low digits,
    // narrowed.
    let anchors = if terms
        .iter()
        .any(|t| borrow(cx, t.0).is_some() || detects(cx, t.0).is_some())
    {
        anchors(r, cx, &terms)?
    } else {
        Vec::new()
    };
    let mut pending: Vec<Wide> = Vec::new();
    let mut carries = Vec::with_capacity(terms.len());
    for &(a, k) in &terms {
        let mut c = None;
        let sides = match borrow(cx, a) {
            Some((Some(x), y, minus)) => Some((x, y, minus)),
            // `y != 0` is `0 <u y`.
            Some((None, y, minus)) => {
                let wy = cx.width_of(y);
                Some((r.build(cx, |cx| cx.mk_const(&BitVec::zero(wy)))?, y, minus))
            }
            None => None,
        };
        let found = match sides {
            Some((x, y, minus)) => digits(r, cx, x, y, &anchors, j)?.map(|s| (s, minus)),
            None => match detects(cx, a) {
                Some((c, minus)) if depth > 0 => {
                    detector(r, cx, c, &anchors, j, depth - 1)?.map(|s| (s, minus))
                }
                _ => None,
            },
        };
        if let Some((
            Sides {
                p,
                q,
                at,
                fin: relied,
                guard,
            },
            minus,
        )) = found
        {
            let mut f = relied;
            let mut d = difference(r, cx, p.of, q.of, &mut f)?;
            let (mut p, mut q) = (p, q);
            if guard.is_none()
                && j <= cx.wid(p.of) - at
                && let Some((p2, q2, d2)) = unmasked(r, cx, p, q, d, at, &mut f)?
            {
                (p, q, d) = (p2, q2, d2);
            }
            let wide = j > cx.wid(p.of) - at && !no_wrap(r, cx, q.of, d)?.0;
            // (Where the sum reads more bits than the sides have above the digit.)
            if guard.is_none()
                && wide
                && let Some((p2, q2, d2)) = reanchored(r, cx, &terms, p, q, d, at, &mut f)?
            {
                (p, q, d) = (p2, q2, d2);
            }
            let room = cx.wid(p.of) - at;
            let mut reads = j <= room || {
                let (exact, fe) = no_wrap(r, cx, q.of, d)?;
                f = f.and(fe);
                exact
            };
            // The sum reads more bits than the sides have above the digit: read with the
            // others of its word, where that leaves the sum fewer terms.
            if !reads && guard.is_none() {
                pending.push(Wide {
                    i: carries.len(),
                    p,
                    q,
                    d,
                    at,
                    minus,
                    fin: f,
                });
            }
            // Middle digits: some bit of the difference's digit is known 0, or nothing
            // carries into the digit (the low bits of `Q` or of `P − Q` are 0).
            if reads && let Some((o, n)) = guard {
                let (known, fk) = super::known_words(r, cx, d)?;
                let digit = (u64::MAX >> (64 - n)) << o;
                let lows = (1u64 << o) - 1;
                reads = known.is_some_and(|[zero, _]| zero & digit != 0 || zero & lows == lows);
                f = f.and(fk);
                if !reads {
                    let (known, fq) = super::known_words(r, cx, q.of)?;
                    reads = known.is_some_and(|[zero, _]| zero & lows == lows);
                    f = f.and(fq);
                }
            }
            // A side whose high digit a term of the sum is, on the bits the sum is read on;
            // or the sides over a word the sum holds such a digit of, where they are
            // another spelling of it (see `respelled`). (Not where the reading is exact by
            // the known bits of the sides as they are, and not for sides lifted above what
            // the comparison reads: a word that wide is the register's, not the limb's.)
            let kc = if minus { neg(&low(&k)) } else { low(&k) };
            let mut met = digit_words(cx, &terms, &kc, cx.wid(p.of), at)
                .into_iter()
                .find(|v| v.0 == if v.1 { q.of } else { p.of })
                .map(|v| (v.2, v.1));
            let natural = guard.is_some()
                || sides.is_none_or(|(x, y, _)| {
                    let widest = |v: u32| readings(cx, v).iter().map(|s| cx.wid(s.0)).max();
                    widest(x).max(widest(y)).is_some_and(|n| cx.wid(p.of) <= n)
                });
            if reads
                && met.is_none()
                && j <= room
                && natural
                && let Some((p2, q2, d2, m)) = respelled(r, cx, &terms, &kc, p, q, d, at, &mut f)?
            {
                (p, q, d, met) = (p2, q2, d2, Some(m));
            }
            // The difference modulo `2^at`, where that is fewer terms and a side's digit is
            // a term of the sum: the carry depends on no more of `P − Q`, and what a side
            // lifted above its digit put there is nobody's. The other side is then made of
            // the one met and the difference (`P' = Q + D'`, or `Q' = P − D'`).
            if reads
                && j <= room
                && let Some((_, with_q)) = met
            {
                let fd = linear::form_of(r, cx, d)?;
                let low = fd.reduce(Width::new(at).map_err(|e| Stop::Error(e.into()))?);
                if low.parts().1.len() < fd.parts().1.len() {
                    let kept = linear::form_of(r, cx, if with_q { q.of } else { p.of })?;
                    let other = if with_q {
                        kept.add(&low)
                    } else {
                        kept.add(&low.neg())
                    };
                    f = f.and(fd.fin).and(kept.fin);
                    let of = linear::emit(r, cx, &other)?;
                    let (small, fs) = below(r, cx, of, at)?;
                    if small {
                        f = f.and(fs);
                    }
                    d = linear::emit(r, cx, &low)?;
                    if with_q {
                        p = Digit { of, small };
                    } else {
                        q = Digit { of, small };
                    }
                }
            }
            if reads {
                c = Some(Carry {
                    p,
                    q,
                    d,
                    at,
                    minus,
                    fin: f,
                    met,
                    gone: None,
                });
            }
        }
        carries.push(c);
    }
    // The carries whose difference the sum holds the high digit of, in another spelling.
    for i in 0..carries.len() {
        if let Some(c) = over_difference(r, cx, &terms, &carries, i, j)? {
            carries[i] = Some(c);
        }
    }
    // Without one, a sum of high digits: each is pushed into its operand again, where one
    // written two ways (`hi(a | b)` and `hi(a) | hi(b)`, `x >>u 7` and `zext(extract<7,
    // 7>(x))`) meets itself.
    let highs = terms.iter().filter(|t| high_digit(cx, t.0)).count();
    if carries.iter().all(Option::is_none) && highs < 2 && pending.is_empty() {
        discard(r, cx, before);
        return Ok(None);
    }
    // Each carry read as its high digits at `j` bits, with what that relied on and the
    // nodes the narrowings stopped at; the other terms as they are written, at `j` bits.
    let mut digs: Vec<Option<Read>> = Vec::with_capacity(terms.len());
    let mut owns: Vec<Option<(u32, Fin, Vec<u32>)>> = Vec::with_capacity(terms.len());
    // (Whether a term is a slice of a sum with its carry out, `zext(a) + zext(b)`, of which
    // the `j` bits read are below the carry: bits of the sum at the operands' width, which
    // the term narrowed is a slice of. The sum is then read so with as many terms.)
    let mut lowered = false;
    for (&(a, k), c) in terms.iter().zip(&carries) {
        let Some(c) = *c else {
            let Some(own) = narrow_term(r, cx, a, j, w)? else {
                discard(r, cx, before);
                return Ok(None);
            };
            let n = cx.node(a);
            if j < w
                && n.op == OpCode::Extract
                && n.b > 0
                && let Some(m) = casts::zext_sum(cx, n.a, 1)
            {
                let lo = n.b as u16;
                lowered |= lo + j <= m && m < lo + n.width;
            }
            owns.push(Some(own));
            digs.push(None);
            continue;
        };
        let Some(read) = carry_digits(r, cx, &c, low(&k), j, &terms, w)? else {
            discard(r, cx, before);
            return Ok(None);
        };
        owns.push(None);
        digs.push(Some(read));
    }
    let konst = low(&konst);
    let base = settled(r, cx, &terms, konst, &carries, &digs, &owns, j)?;
    // The carries of words with too few bits, word by word, each read with the carry that
    // makes its word wider ([`widened`]) where that leaves the sum fewer terms.
    pending.sort_by(|a, b| {
        cx.order(a.p.of, b.p.of)
            .then(a.at.cmp(&b.at))
            .then(cx.order(terms[a.i].0, terms[b.i].0))
    });
    let mut wide: Option<Settled> = None;
    for group in pending
        .chunk_by(|a, b| a.p.of == b.p.of && a.at == b.at)
        .take(MAX_WIDE)
    {
        for g in 0..group.len().min(MAX_WIDE) {
            if !makes(r, cx, &group[g])? {
                continue;
            }
            r.meter.charge(Counter::PassWork, 4 * terms.len() as u64)?;
            let read = widened(r, cx, group, g, j)?;
            let (mut c2, mut d2, mut o2) = (carries.clone(), digs.clone(), owns.clone());
            let mut whole = true;
            for (c, m) in read.iter().zip(group) {
                let Some(c) = c else {
                    continue;
                };
                let Some(ds) = carry_digits(r, cx, c, low(&terms[m.i].1), j, &terms, w)? else {
                    whole = false;
                    break;
                };
                c2[m.i] = Some(*c);
                d2[m.i] = Some(ds);
                o2[m.i] = None;
            }
            if !whole || read.iter().all(Option::is_none) {
                continue;
            }
            let other = settled(r, cx, &terms, konst, &c2, &d2, &o2, j)?;
            if other.left < wide.as_ref().map_or(base.left, |s| s.left) {
                wide = Some(other);
                (carries, digs, owns) = (c2, d2, o2);
            }
        }
    }
    // Taken where every such carry of the sum is read, or the sum gets two terms fewer (a
    // carry and its digits met): one term fewer beside a carry left as it is was measured
    // to keep the rest of the word from being read later.
    let taken = wide
        .as_ref()
        .is_some_and(|s| s.left + 2 <= base.left || pending.iter().all(|m| carries[m.i].is_some()));
    let best = match wide {
        Some(s) if taken => s,
        Some(_) => {
            for m in &pending {
                carries[m.i] = None;
            }
            base
        }
        None => base,
    };
    if carries.iter().all(Option::is_none) && highs < 2 {
        discard(r, cx, before);
        return Ok(None);
    }
    let Settled {
        e,
        left,
        plain,
        fin: relied,
        stops,
    } = best;
    fin = fin.and(relied);
    // (A sum without a carry whose slice of a carry-out sum is read below the carry.)
    let lowered = lowered && carries.iter().all(Option::is_none) && pending.is_empty();
    // A reading that leaves the sum no fewer terms: only for a caller that asks for it, and
    // only where a carry is read.
    let tied = left >= plain && !(lowered && left == plain);
    if tied && !any && !(ties && carries.iter().any(Option::is_some)) {
        discard(r, cx, before);
        return Ok(None);
    }
    Ok(Some((e, fin, stops, tied)))
}
