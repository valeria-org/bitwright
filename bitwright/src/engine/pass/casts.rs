//! The casts pass: an `extract<lo, n>(x)` (a `trunc` when `lo = 0`) is pushed into `x`:
//!
//! - through `+ − * neg` when `lo = 0` (the low bits of a sum, difference or product depend
//!   only on the low bits of its operands), and through `& | ^ ~` and `select` for any `lo`;
//! - through shifts by a constant (an arithmetic shift fills with the sign bit), zero and
//!   sign extensions, and `concat`, by re-indexing (or becoming the constant 0, or the
//!   extension of the part that remains);
//! - above bit `lo` through `a + a` (the bits one lower), and through `+ − *` where an operand's
//!   low `lo` bits are known zero (nothing carries in from below).
//!
//! The narrowing is computed for the whole region below the extract (bounded), and replaces the
//! node only when that region gets strictly smaller: `trunc(zext(x) + zext(y))` becomes
//! `x + y`, while `trunc(a + b)` over opaque operands stays as it is.
//!
//! A `concat` of two values that are neighbouring slices of one bitwise value once the upper
//! one is pushed into it (`concat(hi(a) | hi(b), lo(a | b))`) is the slice that covers both.

use super::{Fin, PassKind, Runner, Step, Stop, finish};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};

/// The most extract pushes per narrowing.
const MAX_PUSHES: u32 = 128;

struct Narrow {
    /// Results per (node, lo, n).
    memo: IdMap<(u32, u16, u16), u32>,
    /// Nodes where narrowing stopped (the region's atoms).
    stops: Vec<u32>,
    pushes: u32,
    /// What the facts a push relied on contribute to the node's finality.
    fin: Fin,
}

/// Whether the low `lo` bits of `i` are known zero (so a sum or product with it carries
/// nothing into the bits above), and what that relied on.
fn low_zero(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    i: u32,
    lo: u16,
) -> Result<(bool, Fin), Stop> {
    let w = cx.wid(i);
    if lo == 0 {
        return Ok((true, Fin::FINAL));
    }
    if w <= 64 {
        let (k, fin) = super::known_words(r, cx, i)?;
        let need = if lo >= 64 { u64::MAX } else { (1u64 << lo) - 1 };
        return Ok((k.is_some_and(|[zero, _]| zero & need == need), fin));
    }
    let (k, fin) = super::known(r, cx, i)?;
    let need = crate::facts::known::low_mask(
        crate::Width::new(w).map_err(|e| Stop::Error(e.into()))?,
        u32::from(lo),
    );
    Ok((
        k.is_some_and(|k| crate::facts::known::bv_and(&k.known_zero(), &need) == need),
        fin,
    ))
}

/// The carry into bit `lo` of `a + b` (of `a − b`, as `a + ~b + 1`, when `sub`), when the
/// operands' known bits below `lo` decide it, and what that relied on. From the carry into bit
/// 0 up, each bit's carry out is the majority of its two operand bits and its carry in, known
/// when two of the three are known and agree: a bit known zero in both stops any carry, one
/// known one in both makes one, and a known carry passes a bit known to differ.
fn carry_in(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    a: u32,
    b: u32,
    lo: u16,
    sub: bool,
) -> Result<(Option<bool>, Fin), Stop> {
    let (ka, fa) = super::known(r, cx, a)?;
    let (kb, fb) = super::known(r, cx, b)?;
    let fin = fa.and(fb);
    let (Some(ka), Some(kb)) = (ka, kb) else {
        return Ok((None, fin));
    };
    let bit = |k: &crate::facts::KnownBits, j: u16, flip: bool| {
        if k.known_one().bit(j) == Some(true) {
            Some(!flip)
        } else if k.known_zero().bit(j) == Some(true) {
            Some(flip)
        } else {
            None
        }
    };
    let mut c = Some(sub);
    for j in 0..lo {
        let (x, y) = (bit(&ka, j, false), bit(&kb, j, sub));
        c = match (x, y, c) {
            (Some(p), Some(q), _) | (Some(p), _, Some(q)) | (_, Some(p), Some(q)) if p == q => {
                Some(p)
            }
            _ => None,
        };
    }
    Ok((c, fin))
}

/// `extract<lo, n>(x)`, narrowed as far as the rules above allow.
fn narrow(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    st: &mut Narrow,
    x: u32,
    lo: u16,
    n: u16,
) -> Result<u32, Stop> {
    if let Some(&v) = st.memo.get(&(x, lo, n)) {
        return Ok(v);
    }
    let w = cx.wid(x);
    if lo == 0 && n == w {
        st.stops.push(x);
        return Ok(x);
    }
    r.meter.charge(Counter::PassWork, 1)?;
    r.meter.check()?;
    let node = cx.node(x);
    let stop = |r: &mut Runner<'_, '_>, cx: &mut Context, st: &mut Narrow| -> Result<u32, Stop> {
        st.stops.push(x);
        r.build(cx, |cx| cx.c_extract(x, lo, n))
    };
    st.pushes += 1;
    let v = if st.pushes > MAX_PUSHES {
        stop(r, cx, st)?
    } else if let Some(c) = cx.const_val(x) {
        let v = c
            .extract(lo, crate::Width::new(n).map_err(|e| Stop::Error(e.into()))?)
            .map_err(|e| Stop::Error(e.into()))?;
        r.build(cx, |cx| cx.mk_const(&v))?
    } else {
        match node.op {
            OpCode::Add | OpCode::Sub | OpCode::Mul if lo == 0 => {
                let a = narrow(r, cx, st, node.a, 0, n)?;
                let b = narrow(r, cx, st, node.b, 0, n)?;
                let op = node.op.as_bin().unwrap_or(BinOp::Add);
                r.build(cx, |cx| cx.c_bin(op, a, b))?
            }
            // `a + a` is `a << 1` (the linear pass writes it so): the bits one lower.
            OpCode::Add if node.a == node.b => narrow(r, cx, st, node.a, lo - 1, n)?,
            // Above bit `lo`, a sum or difference is the sum or difference of its operands' bits
            // there and the carry into bit `lo`, when the operands' known bits below decide it:
            // nothing carries past a bit known zero in both (a guard bit between packed lanes),
            // or from operands whose low bits are known zero (`(a + 2^lo·b') >> lo` is
            // `(a >> lo) + b'`).
            OpCode::Add | OpCode::Sub => {
                let sub = node.op == OpCode::Sub;
                let (carry, f) = carry_in(r, cx, node.a, node.b, lo, sub)?;
                match carry {
                    None => {
                        st.fin = st.fin.and(f.unchanged());
                        stop(r, cx, st)?
                    }
                    Some(c) => {
                        st.fin = st.fin.and(f);
                        let a = narrow(r, cx, st, node.a, lo, n)?;
                        let b = narrow(r, cx, st, node.b, lo, n)?;
                        let op = if sub { BinOp::Sub } else { BinOp::Add };
                        let s = r.build(cx, |cx| cx.c_bin(op, a, b))?;
                        // `a − b` is `a + ~b + 1`: its own carry in is 1.
                        if c == sub {
                            s
                        } else {
                            let one = BitVec::one(
                                crate::Width::new(n).map_err(|e| Stop::Error(e.into()))?,
                            );
                            let fix = if c { BinOp::Add } else { BinOp::Sub };
                            r.build(cx, |cx| {
                                let one = cx.mk_const(&one)?;
                                cx.c_bin(fix, s, one)
                            })?
                        }
                    }
                }
            }
            // A product's bits from `lo` on are `a · b'` there when an operand's low `lo` bits
            // are zero.
            OpCode::Mul => {
                let (za, fa) = low_zero(r, cx, node.a, lo)?;
                let (zb, fb) = low_zero(r, cx, node.b, lo)?;
                if !(za || zb) {
                    st.fin = st.fin.and(fa.unchanged()).and(fb.unchanged());
                    stop(r, cx, st)?
                } else {
                    st.fin = st.fin.and(if za { fa } else { fb });
                    // The operand with zero low bits is read from `lo`, the other below.
                    let (z, o) = if zb {
                        (node.b, node.a)
                    } else {
                        (node.a, node.b)
                    };
                    let zz = narrow(r, cx, st, z, lo, n)?;
                    let oo = narrow(r, cx, st, o, 0, n)?;
                    let (a, b) = if zb { (oo, zz) } else { (zz, oo) };
                    r.build(cx, |cx| cx.c_bin(BinOp::Mul, a, b))?
                }
            }
            OpCode::Neg if lo == 0 => {
                let a = narrow(r, cx, st, node.a, 0, n)?;
                r.build(cx, |cx| cx.c_un(UnOp::Neg, a))?
            }
            OpCode::And | OpCode::Or | OpCode::Xor => {
                let a = narrow(r, cx, st, node.a, lo, n)?;
                let b = narrow(r, cx, st, node.b, lo, n)?;
                let op = node.op.as_bin().unwrap_or(BinOp::And);
                r.build(cx, |cx| cx.c_bin(op, a, b))?
            }
            OpCode::Not => {
                let a = narrow(r, cx, st, node.a, lo, n)?;
                r.build(cx, |cx| cx.c_un(UnOp::Not, a))?
            }
            OpCode::Select => {
                let t = narrow(r, cx, st, node.b, lo, n)?;
                let f = narrow(r, cx, st, node.c, lo, n)?;
                let c = node.a;
                st.stops.push(c);
                r.build(cx, |cx| cx.c_select(c, t, f))?
            }
            OpCode::Shl | OpCode::LShr if cx.const_val(node.b).is_some() => {
                let k = cx
                    .const_val(node.b)
                    .and_then(|k| k.to_u64())
                    .unwrap_or(u64::MAX);
                let (lo64, n64, w64) = (u64::from(lo), u64::from(n), u64::from(w));
                if node.op == OpCode::Shl {
                    if lo64 + n64 <= k {
                        // Every extracted bit is a shifted-in zero.
                        r.build(cx, |cx| cx.mk_const(&BitVec::zero(crate::Width::new(n)?)))?
                    } else if lo64 >= k {
                        narrow(r, cx, st, node.a, (lo64 - k) as u16, n)?
                    } else {
                        // Straddling the shift: the operand's low bits, shifted by what is left
                        // of the shift at the narrow width (not `concat(trunc(x), 0)`, a worse
                        // start for the passes after).
                        let a = narrow(r, cx, st, node.a, 0, n)?;
                        let s = BitVec::wrapping_from_u64(
                            crate::Width::new(n).map_err(|e| Stop::Error(e.into()))?,
                            k - lo64,
                        );
                        r.build(cx, |cx| {
                            let s = cx.mk_const(&s)?;
                            cx.c_bin(BinOp::Shl, a, s)
                        })?
                    }
                } else if lo64 + k >= w64 {
                    r.build(cx, |cx| cx.mk_const(&BitVec::zero(crate::Width::new(n)?)))?
                } else if lo64 + k + n64 <= w64 {
                    narrow(r, cx, st, node.a, (lo64 + k) as u16, n)?
                } else {
                    stop(r, cx, st)?
                }
            }
            // An arithmetic shift: the operand's bits from `lo + k`, the sign bit above them.
            OpCode::AShr if cx.const_val(node.b).is_some() => {
                let k = cx
                    .const_val(node.b)
                    .and_then(|k| k.to_u64())
                    .unwrap_or(u64::MAX);
                let (lo64, n64, w64) = (u64::from(lo), u64::from(n), u64::from(w));
                if lo64 + k + n64 <= w64 {
                    narrow(r, cx, st, node.a, (lo64 + k) as u16, n)?
                } else if lo64 + k >= w64 - 1 {
                    let sign = narrow(r, cx, st, node.a, w - 1, 1)?;
                    r.build(cx, |cx| cx.c_sext(sign, n))?
                } else {
                    let from = (lo64 + k) as u16;
                    let p = narrow(r, cx, st, node.a, from, w - from)?;
                    r.build(cx, |cx| cx.c_sext(p, n))?
                }
            }
            OpCode::Zext | OpCode::Sext => {
                let wa = cx.wid(node.a);
                if lo + n <= wa {
                    narrow(r, cx, st, node.a, lo, n)?
                } else if node.op == OpCode::Zext && lo >= wa {
                    r.build(cx, |cx| cx.mk_const(&BitVec::zero(crate::Width::new(n)?)))?
                } else {
                    // The extracted bits straddle the operand's top: extend the part that
                    // remains (for a sign extension past the operand, its sign bit).
                    let (plo, pn) = if lo >= wa { (wa - 1, 1) } else { (lo, wa - lo) };
                    let p = narrow(r, cx, st, node.a, plo, pn)?;
                    let sext = node.op == OpCode::Sext;
                    r.build(cx, |cx| {
                        if sext {
                            cx.c_sext(p, n)
                        } else {
                            cx.c_zext(p, n)
                        }
                    })?
                }
            }
            OpCode::Concat => {
                let wl = cx.wid(node.b);
                if lo + n <= wl {
                    narrow(r, cx, st, node.b, lo, n)?
                } else if lo >= wl {
                    narrow(r, cx, st, node.a, lo - wl, n)?
                } else {
                    stop(r, cx, st)?
                }
            }
            OpCode::Extract => narrow(r, cx, st, node.a, node.b as u16 + lo, n)?,
            _ => stop(r, cx, st)?,
        }
    };
    st.memo.insert((x, lo, n), v);
    Ok(v)
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry("casts").or_default()
}

/// `extract<lo, n>(x)` pushed into `x` as far as the rules above allow, whatever its size, and
/// what the facts the pushes used relied on: for a caller that commits on its own measure (the
/// invert pass compares truncations at their own width). `None` when the pushes were capped.
pub(super) fn narrowed(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    lo: u16,
    n: u16,
) -> Result<Option<(u32, Fin)>, Stop> {
    Ok(narrowed_from(r, cx, x, lo, n)?.map(|(e, fin, _)| (e, fin)))
}

/// [`narrowed`], with the nodes where the pushes stopped (the region's atoms, for the commit
/// rule's count).
pub(super) fn narrowed_from(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    lo: u16,
    n: u16,
) -> Result<Option<(u32, Fin, Vec<u32>)>, Stop> {
    let mut st = Narrow {
        memo: IdMap::default(),
        stops: Vec::new(),
        pushes: 0,
        fin: Fin::FINAL,
    };
    let e = narrow(r, cx, &mut st, x, lo, n)?;
    Ok((st.pushes <= MAX_PUSHES).then_some((e, st.fin, st.stops)))
}

/// The width `k` and operand `x` when `n` sign-extends the low `k` bits of `x` spelled with
/// shifts or arithmetic: `(x << c) >>s c` (`k = W − c`), or `((x & (2^k − 1)) ^ 2^(k−1)) −
/// 2^(k−1)` (the builder's `+ −2^(k−1)`; the masked value may also be `zext(trunc<k>(x))`).
fn sext_idiom(cx: &Context, n: u32) -> Option<(u16, u32)> {
    let node = cx.node(n);
    let w = node.width;
    let small = |i: u32| cx.const_val(i).and_then(|v| v.to_u64());
    match node.op {
        OpCode::AShr => {
            let c = small(node.b)?;
            let inner = cx.node(node.a);
            (inner.op == OpCode::Shl && small(inner.b) == Some(c) && c >= 1 && c < u64::from(w))
                .then_some((w - c as u16, inner.a))
        }
        OpCode::Add => {
            // (t ^ h) + (−h) with h = 2^(k−1) and t the low k bits of x.
            let (x, k) = (node.a, cx.const_val(node.b)?);
            let neg_h = BitVec::apply_un(UnOp::Neg, &k).ok()?;
            let h = neg_h.to_u64()?;
            if !h.is_power_of_two() {
                return None;
            }
            let kk = h.trailing_zeros() as u16 + 1;
            if kk >= w {
                return None;
            }
            let xor = cx.node(x);
            if xor.op != OpCode::Xor || small(xor.b) != Some(h) {
                return None;
            }
            let t = cx.node(xor.a);
            match t.op {
                OpCode::And if small(t.b) == Some((1u64 << kk) - 1) => Some((kk, t.a)),
                OpCode::Zext => {
                    let e = cx.node(t.a);
                    (e.op == OpCode::Extract && e.b == 0 && e.width == kk).then_some((kk, e.a))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The casts pass at `n`.
/// `concat(h, l)` where one half is a slice of a bitwise `x` and the other is the neighbouring
/// slice of `x` pushed into it (`concat(hi(a) | hi(b), lo(a | b))`): the one slice of `x` that
/// covers both.
fn rejoined(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let (h, l) = (node.a, node.b);
    let (hw, lw) = (cx.wid(h), cx.wid(l));
    // The slice kept whole, and where the other half lies in its operand.
    let sliced = |cx: &Context, i: u32| {
        let s = cx.node(i);
        (s.op == OpCode::Extract).then_some((s.a, s.b as u16))
    };
    let bitwise = |cx: &Context, x: u32, other: u32| {
        let op = cx.node(x).op;
        matches!(
            op,
            OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not | OpCode::Select
        ) && cx.node(other).op == op
    };
    let (x, lo, at, len, other) = match (sliced(cx, l), sliced(cx, h)) {
        (Some((x, lo)), _)
            if bitwise(cx, x, h)
                && u32::from(lo) + u32::from(lw) + u32::from(hw) <= u32::from(cx.wid(x)) =>
        {
            (x, lo, lo + lw, hw, h)
        }
        (_, Some((x, lo))) if bitwise(cx, x, l) && lo >= lw => (x, lo - lw, lo - lw, lw, l),
        _ => return Ok(Step::Normal(Fin::FINAL)),
    };
    let before = cx.len() as u32;
    let Some((e, fin, _)) = narrowed_from(r, cx, x, at, len)? else {
        super::discard(r, cx, before);
        return Ok(Step::Normal(Fin::FINAL));
    };
    if e != other {
        super::discard(r, cx, before);
        return Ok(Step::Normal(fin));
    }
    let e = r.build(cx, |cx| cx.c_extract(x, lo, hw + lw))?;
    finish(r, cx, PassKind::Casts, n, e, before, &[x], fin)
}

pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    if let Some((k, x)) = sext_idiom(cx, n) {
        let before = cx.len() as u32;
        let w = node.width;
        let e = r.build(cx, |cx| {
            let t = cx.c_extract(x, 0, k)?;
            cx.c_sext(t, w)
        })?;
        r.explain_with(|| crate::engine::Explanation::Casts {
            source: cx.handle(x),
            lo: 0,
            bits: k,
            sign_extended: true,
        });
        return finish(r, cx, PassKind::Casts, n, e, before, &[x], Fin::FINAL);
    }
    if node.op == OpCode::Concat {
        return rejoined(r, cx, n);
    }
    if node.op != OpCode::Extract {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let before = cx.len() as u32;
    let mut st = Narrow {
        memo: IdMap::default(),
        stops: Vec::new(),
        pushes: 0,
        fin: Fin::FINAL,
    };
    let e = narrow(r, cx, &mut st, node.a, node.b as u16, node.width)?;
    if st.pushes > MAX_PUSHES {
        count(r).atomized += 1;
    }
    let fin = st.fin;
    r.explain_with(|| crate::engine::Explanation::Casts {
        source: cx.handle(node.a),
        lo: node.b as u16,
        bits: node.width,
        sign_extended: false,
    });
    finish(r, cx, PassKind::Casts, n, e, before, &st.stops, fin)
}
