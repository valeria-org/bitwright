//! The casts pass: an `extract<lo, n>(x)` (a `trunc` when `lo = 0`) is pushed into `x`:
//!
//! - through `+ − * neg` when `lo = 0` (the low bits of a sum, difference or product depend
//!   only on the low bits of its operands), and through `& | ^ ~` and `select` for any `lo`;
//! - through shifts by a constant (an arithmetic shift fills with the sign bit), zero and
//!   sign extensions, and `concat`, by re-indexing (or becoming the constant 0, or the
//!   extension of the part that remains); across the seam of a `concat` only in an arm of a
//!   `select` (the limbs on either side of it; elsewhere the slice of the joined word is
//!   what the limb passes read);
//! - above bit `lo` through `a + a` (the bits one lower), and through `+ − *` where an operand's
//!   low `lo` bits are known zero (nothing carries in from below).
//!
//! The narrowing is computed for the whole region below the extract (bounded), and replaces the
//! node only when that region gets strictly smaller: `trunc(zext(x) + zext(y))` becomes
//! `x + y`, while `trunc(a + b)` over opaque operands stays as it is. Where it reaches a node
//! whose slice something else already reads, it uses that slice: narrowing the node again
//! would build it a second time, which pays for neither reader while the other holds it.
//!
//! A `concat` of two values that are neighbouring slices of one bitwise value once the upper
//! one is pushed into it (`concat(hi(a) | hi(b), lo(a | b))`) is the slice that covers both.
//!
//! The other way, `select(c, F(a), F(b))` is `F(select(c, a, b))` where the two arms are the
//! same operations over operands that differ in a pair or two, and doing them once makes the
//! DAG smaller: a register read limb by limb, each limb through its own `select`, is the limbs
//! of the selected register.

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
    /// The extract the narrowing is of (its own node), where a slice some other node already
    /// reads is used as it is (see [`live_slice`]).
    own: Option<u32>,
    /// Whether a slice met whole is pushed into its operand like one asked for (see
    /// [`spelled`]).
    whole: bool,
    /// How many `select`s the narrowing is in an arm of.
    arms: u32,
}

/// The node `extract<lo, n>(x)` where it exists and something live reads it, other than
/// `own`: a narrowing that reaches `x` uses it, where pushing on would build the slice a
/// second time (the low half of a word two limbs read, each of which alone frees nothing by
/// narrowing it).
fn live_slice(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    own: u32,
    x: u32,
    lo: u16,
    n: u16,
) -> Result<Option<u32>, Stop> {
    if matches!(
        cx.node(x).op,
        OpCode::Extract | OpCode::Zext | OpCode::Sext | OpCode::Concat | OpCode::Const
    ) {
        return Ok(None);
    }
    let Some(e) = cx.find(&crate::expr::Node::new(
        OpCode::Extract,
        n,
        x,
        u32::from(lo),
        0,
    )) else {
        return Ok(None);
    };
    if e == own {
        return Ok(None);
    }
    super::refresh_uses(r, cx)?;
    Ok(r.live.uses(e).is_some_and(|u| u > 0).then_some(e))
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

/// `x` read whole by a caller that compares spellings ([`spelled`]): a slice is pushed into
/// its operand like one asked for, and the operands of the operators a slice passes through
/// at any bit (`& | ^ ~`, extensions) are read the same way. `None` for anything else.
fn respelled(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    st: &mut Narrow,
    x: u32,
) -> Result<Option<u32>, Stop> {
    let node = cx.node(x);
    let w = node.width;
    let bin = match node.op {
        OpCode::And => Some(BinOp::And),
        OpCode::Or => Some(BinOp::Or),
        OpCode::Xor => Some(BinOp::Xor),
        _ => None,
    };
    if bin.is_none()
        && !matches!(
            node.op,
            OpCode::Extract | OpCode::Not | OpCode::Zext | OpCode::Sext
        )
    {
        return Ok(None);
    }
    r.meter.charge(Counter::PassWork, 1)?;
    st.pushes += 1;
    if st.pushes > MAX_PUSHES {
        return Ok(None);
    }
    let v = match (node.op, bin) {
        (OpCode::Extract, _) => narrow(r, cx, st, node.a, node.b as u16, w)?,
        (_, Some(op)) => {
            let a = narrow(r, cx, st, node.a, 0, w)?;
            let b = narrow(r, cx, st, node.b, 0, w)?;
            r.build(cx, |cx| cx.c_bin(op, a, b))?
        }
        (OpCode::Not, _) => {
            let a = narrow(r, cx, st, node.a, 0, w)?;
            r.build(cx, |cx| cx.c_un(UnOp::Not, a))?
        }
        _ => {
            let wa = cx.wid(node.a);
            let a = narrow(r, cx, st, node.a, 0, wa)?;
            let sext = node.op == OpCode::Sext;
            r.build(cx, |cx| {
                if sext {
                    cx.c_sext(a, w)
                } else {
                    cx.c_zext(a, w)
                }
            })?
        }
    };
    Ok(Some(v))
}

/// The width `x` is a sum of zero extensions from (of sums and differences of them, at most
/// `depth` deep): `zext(a) + zext(b)` of two values of one width.
pub(super) fn zext_sum(cx: &Context, x: u32, depth: u32) -> Option<u16> {
    let node = cx.node(x);
    match node.op {
        OpCode::Zext => Some(cx.wid(node.a)),
        OpCode::Add | OpCode::Sub if depth > 0 => {
            let (a, b) = (
                zext_sum(cx, node.a, depth - 1)?,
                zext_sum(cx, node.b, depth - 1)?,
            );
            (a == b).then_some(a)
        }
        _ => None,
    }
}

/// The sum `a + b` at the operands' own width where `x` is `zext(a) + zext(b)`, the sum of
/// the two with its carry out, and that sum is a node something live reads: the word the
/// limbs beside the carry are of.
#[cfg(feature = "prove")]
pub(super) fn live_word(r: &mut Runner<'_, '_>, cx: &Context, x: u32) -> Result<Option<u32>, Stop> {
    let node = cx.node(x);
    let (a, b) = (cx.node(node.a), cx.node(node.b));
    if node.op != OpCode::Add
        || a.op != OpCode::Zext
        || b.op != OpCode::Zext
        || cx.wid(a.a) != cx.wid(b.a)
    {
        return Ok(None);
    }
    let m = cx.wid(a.a);
    let find = |p: u32, q: u32| cx.find(&crate::expr::Node::new(OpCode::Add, m, p, q, 0));
    let Some(e) = find(a.a, b.a).or_else(|| find(b.a, a.a)) else {
        return Ok(None);
    };
    super::refresh_uses(r, cx)?;
    Ok(r.live.uses(e).is_some_and(|u| u > 0).then_some(e))
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
        if st.whole
            && let Some(v) = respelled(r, cx, st, x)?
        {
            st.memo.insert((x, lo, n), v);
            return Ok(v);
        }
        st.stops.push(x);
        return Ok(x);
    }
    if let Some(own) = st.own
        && let Some(e) = live_slice(r, cx, own, x, lo, n)?
    {
        st.stops.push(e);
        st.memo.insert((x, lo, n), e);
        return Ok(e);
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
                    // A sum of values zero-extended from one width (the sum with its carry
                    // out) read below the carry is the sum at that width: its low bits.
                    None if zext_sum(cx, x, 4).is_some_and(|m| lo + n <= m && m < w) => {
                        let m = zext_sum(cx, x, 4).unwrap_or(w);
                        let low = narrow(r, cx, st, x, 0, m)?;
                        r.build(cx, |cx| cx.c_extract(low, lo, n))?
                    }
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
                st.arms += 1;
                let t = narrow(r, cx, st, node.b, lo, n)?;
                let f = narrow(r, cx, st, node.c, lo, n)?;
                st.arms -= 1;
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
                } else if st.arms > 0 {
                    // In an arm of a `select`, across the seam: the low bits of the upper
                    // part over the high bits of the lower, each re-indexed where it is a
                    // join or a slice itself and left as a slice otherwise (the word the
                    // arm joins is not what the `select`'s reader reads).
                    let part = |r: &mut Runner<'_, '_>,
                                cx: &mut Context,
                                st: &mut Narrow,
                                p: u32,
                                plo: u16,
                                pn: u16|
                     -> Result<u32, Stop> {
                        if matches!(
                            cx.node(p).op,
                            OpCode::Concat | OpCode::Extract | OpCode::Zext | OpCode::Sext
                        ) || cx.const_val(p).is_some()
                        {
                            narrow(r, cx, st, p, plo, pn)
                        } else {
                            st.stops.push(p);
                            r.build(cx, |cx| cx.c_extract(p, plo, pn))
                        }
                    };
                    let hi = part(r, cx, st, node.a, 0, lo + n - wl)?;
                    let low = part(r, cx, st, node.b, lo, wl - lo)?;
                    r.build(cx, |cx| cx.c_concat(hi, low))?
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

/// [`narrowed`] as the pass itself writes it where slices are already there: a slice
/// something else reads is used (see [`live_slice`]).
#[cfg(feature = "prove")]
pub(super) fn narrowed_live(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    lo: u16,
    n: u16,
) -> Result<Option<(u32, Fin)>, Stop> {
    let mut st = Narrow {
        memo: IdMap::default(),
        stops: Vec::new(),
        pushes: 0,
        fin: Fin::FINAL,
        own: Some(u32::MAX),
        whole: false,
        arms: 0,
    };
    let e = narrow(r, cx, &mut st, x, lo, n)?;
    Ok((st.pushes <= MAX_PUSHES).then_some((e, st.fin)))
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
    pushed(r, cx, x, lo, n, false)
}

/// [`narrowed_from`] for a caller that compares spellings: a slice met whole on the way (the
/// operand of another operation) is pushed into its operand like one asked for, so that
/// `hi(a ^ b) & c` and `(hi(a) ^ hi(b)) & c` are one node.
#[cfg(feature = "prove")]
pub(super) fn spelled(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    lo: u16,
    n: u16,
) -> Result<Option<(u32, Fin, Vec<u32>)>, Stop> {
    pushed(r, cx, x, lo, n, true)
}

/// [`narrowed_from`] (or [`spelled`], with `whole`), asked once in a call: the pushes read
/// the nodes and their facts and nothing of what is live, so an answer that is final is the
/// answer every time.
fn pushed(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    lo: u16,
    n: u16,
    whole: bool,
) -> Result<Option<(u32, Fin, Vec<u32>)>, Stop> {
    if let Some(known) = r.narrows.get(&(x, lo, n, whole)) {
        return Ok(known.clone());
    }
    let mut st = Narrow {
        memo: IdMap::default(),
        stops: Vec::new(),
        pushes: 0,
        fin: Fin::FINAL,
        own: None,
        whole,
        arms: 0,
    };
    let e = narrow(r, cx, &mut st, x, lo, n)?;
    let out = (st.pushes <= MAX_PUSHES).then_some((e, st.fin, st.stops));
    if out.as_ref().is_none_or(|o| o.1.done) {
        r.narrows.insert((x, lo, n, whole), out.clone());
    }
    Ok(out)
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

/// The most operations of a `select`'s arms read as the same.
const MAX_HOIST: usize = 32;

/// The most `select`s one hoist builds.
const MAX_BASES: usize = 2;

/// How a pair of nodes, one of each arm of a `select`, is read.
#[derive(Clone, Copy)]
enum Paired {
    /// One operation on both sides, over the pairs of its operands.
    Node,
    /// A zero extension of the pair of these: one side masks the low `k` bits of a wider value,
    /// the other zero-extends a `k`-bit value (one value written two ways).
    Zext(u32, u32),
    /// Two values with nothing in common: the `select` is of them.
    Leaf,
    /// The same slice of the two values of a `select` that exists and something live reads:
    /// that `select`, and where the slice starts.
    Slice(u32, u16),
}

/// The two arms of a `select` read side by side (see [`hoisted`]).
struct Hoist {
    /// The `select` and its condition.
    n: u32,
    c: u32,
    /// Whether a pair whose `select` exists and something live reads is taken as it is.
    live: bool,
    seen: IdMap<(u32, u32), Paired>,
    /// The pairs with nothing in common, in the order met.
    leaves: Vec<(u32, u32)>,
    /// The `select`s found that pairs are slices of.
    found: Vec<u32>,
    /// Operations read as the same.
    ops: usize,
}

/// Whether a pair of nodes of `op` may be one operation over their operands' pairs: an integer
/// operation, whose value is a function of its operands alone.
fn pairable(op: OpCode) -> bool {
    op.as_un().is_some()
        || op.as_bin().is_some()
        || op.as_cmp().is_some()
        || matches!(
            op,
            OpCode::Zext | OpCode::Sext | OpCode::Extract | OpCode::Concat | OpCode::Select
        )
}

/// The low `k` bits of `x` when `i` is `x & (2^k − 1)`, `k` below its width.
fn low_mask_of(cx: &Context, i: u32) -> Option<(u32, u16)> {
    let p = cx.node(i);
    if p.op != OpCode::And || p.width > 64 {
        return None;
    }
    let (x, k) = match (cx.const_val(p.a), cx.const_val(p.b)) {
        (None, Some(k)) => (p.a, k.limbs()[0]),
        (Some(k), None) => (p.b, k.limbs()[0]),
        _ => return None,
    };
    let bits = k.trailing_ones() as u16;
    (bits > 0 && bits < p.width && k >> bits == 0).then_some((x, bits))
}

impl Hoist {
    /// Reads `a` and `b` (of one width) side by side.
    fn pair(
        &mut self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
        a: u32,
        b: u32,
    ) -> Result<(), Stop> {
        if a == b || self.seen.contains_key(&(a, b)) {
            return Ok(());
        }
        r.meter.charge(Counter::PassWork, 1)?;
        if let Some((s, o)) = self.wider(r, cx, a, b)? {
            self.seen.insert((a, b), Paired::Slice(s, o));
            self.found.push(s);
            self.ops += 1;
            return Ok(());
        }
        let (na, nb) = (cx.node(a), cx.node(b));
        let (ka, kb) = ([na.a, na.b, na.c], [nb.a, nb.b, nb.c]);
        let arity = na.op.arity();
        // One operation with the same parameters, over operands of the same widths.
        let same = na.op == nb.op
            && pairable(na.op)
            && na.width == nb.width
            && (0..3).all(|s| {
                if s < arity {
                    cx.wid(ka[s]) == cx.wid(kb[s])
                } else {
                    ka[s] == kb[s]
                }
            });
        if self.ops < MAX_HOIST && !(self.live && self.exists(r, cx, a, b)?) {
            if same {
                self.seen.insert((a, b), Paired::Node);
                self.ops += 1;
                for s in 0..arity {
                    self.pair(r, cx, ka[s], kb[s])?;
                }
                return Ok(());
            }
            let mixed = match (na.op, nb.op) {
                (OpCode::And, OpCode::Zext) => low_mask_of(cx, a)
                    .filter(|&(_, k)| k == cx.wid(nb.a))
                    .map(|(x, k)| (Some(x), None, k)),
                (OpCode::Zext, OpCode::And) => low_mask_of(cx, b)
                    .filter(|&(_, k)| k == cx.wid(na.a))
                    .map(|(y, k)| (None, Some(y), k)),
                _ => None,
            };
            if let Some((x, y, k)) = mixed {
                let a2 = match x {
                    Some(x) => r.build(cx, |cx| cx.c_extract(x, 0, k))?,
                    None => na.a,
                };
                let b2 = match y {
                    Some(y) => r.build(cx, |cx| cx.c_extract(y, 0, k))?,
                    None => nb.a,
                };
                self.seen.insert((a, b), Paired::Zext(a2, b2));
                self.ops += 1;
                return self.pair(r, cx, a2, b2);
            }
        }
        self.seen.insert((a, b), Paired::Leaf);
        self.leaves.push((a, b));
        Ok(())
    }

    /// Whether `select(c, a, b)` exists and something live reads it.
    fn exists(&self, r: &mut Runner<'_, '_>, cx: &Context, a: u32, b: u32) -> Result<bool, Stop> {
        let word = crate::expr::Node::new(OpCode::Select, cx.wid(a), self.c, a, b);
        let Some(s) = cx.find(&word).filter(|&s| s != self.n) else {
            return Ok(false);
        };
        super::refresh_uses(r, cx)?;
        Ok(r.live.uses(s).is_some_and(|u| u > 0))
    }

    /// A `select` on the condition that exists, that something live reads, and whose two
    /// values `a` and `b` are the same slice of, with where the slice starts: the values are
    /// looked for at the byte, 16-, 32- and 64-bit boundaries around `a` (a limb read out of
    /// a register whose half is selected whole elsewhere).
    fn wider(
        &self,
        r: &mut Runner<'_, '_>,
        cx: &Context,
        a: u32,
        b: u32,
    ) -> Result<Option<(u32, u16)>, Stop> {
        let (na, nb) = (cx.node(a), cx.node(b));
        if na.op != OpCode::Extract || nb.op != OpCode::Extract {
            return Ok(None);
        }
        let (x, i, len) = (na.a, na.b as u16, na.width);
        let (y, j) = (nb.a, nb.b as u16);
        // The slice `[lo, lo + w)` of `v`, where it is a node.
        let slice = |v: u32, lo: u16, w: u16| {
            if lo == 0 && w == cx.wid(v) {
                Some(v)
            } else {
                cx.find(&crate::expr::Node::new(
                    OpCode::Extract,
                    w,
                    v,
                    u32::from(lo),
                    0,
                ))
            }
        };
        for w in [8u16, 16, 32, 64] {
            let (lp, o) = (i - i % w, i % w);
            if w <= len || o + len > w || j < o {
                continue;
            }
            let lq = j - o;
            if u32::from(lp) + u32::from(w) > u32::from(cx.wid(x))
                || u32::from(lq) + u32::from(w) > u32::from(cx.wid(y))
            {
                continue;
            }
            let (Some(p), Some(q)) = (slice(x, lp, w), slice(y, lq, w)) else {
                continue;
            };
            let word = crate::expr::Node::new(OpCode::Select, w, self.c, p, q);
            if let Some(s) = cx.find(&word).filter(|&s| s != self.n) {
                super::refresh_uses(r, cx)?;
                if r.live.uses(s).is_some_and(|u| u > 0) {
                    return Ok(Some((s, o)));
                }
            }
        }
        Ok(None)
    }

    /// The pair `(a, b)` over the `select`s of the leaves (`of`).
    fn build(
        &self,
        r: &mut Runner<'_, '_>,
        cx: &mut Context,
        of: &IdMap<(u32, u32), u32>,
        memo: &mut IdMap<(u32, u32), u32>,
        a: u32,
        b: u32,
    ) -> Result<u32, Stop> {
        if a == b {
            return Ok(a);
        }
        if let Some(&v) = memo.get(&(a, b)) {
            return Ok(v);
        }
        let v = match self.seen[&(a, b)] {
            Paired::Leaf => of[&(a, b)],
            Paired::Slice(s, o) => {
                let len = cx.wid(a);
                r.build(cx, |cx| cx.c_extract(s, o, len))?
            }
            Paired::Zext(a2, b2) => {
                let w = cx.wid(a);
                let low = self.build(r, cx, of, memo, a2, b2)?;
                r.build(cx, |cx| cx.c_zext(low, w))?
            }
            Paired::Node => {
                let (na, nb) = (cx.node(a), cx.node(b));
                let (mut kids, kb) = ([na.a, na.b, na.c], [nb.a, nb.b, nb.c]);
                for s in 0..na.op.arity() {
                    kids[s] = self.build(r, cx, of, memo, kids[s], kb[s])?;
                }
                r.build(cx, |cx| cx.rebuild(a, kids))?
            }
        };
        memo.insert((a, b), v);
        Ok(v)
    }
}

/// `select(c, F(a), F(b))` as `F(select(c, a, b))`: the two arms are read side by side, and
/// where they are the same operations over operands that differ only in a few pairs (at most
/// [`MAX_BASES`], a pair that is the same slice of both values of another counting with it),
/// the operations are done once, over the `select`s of those pairs. A register read limb by
/// limb, each limb its own chain of `select`s over slices of the registers, is the limbs of
/// the one chain over the registers themselves; a word shifted by a count taken from itself,
/// selected after the shift, is the shift of the selected word.
///
/// The arms are read as far as they agree, where that makes the DAG smaller; otherwise down to
/// pairs whose `select` exists and something live reads.
fn hoisted(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let (c, a, b) = (node.a, node.b, node.c);
    let start = cx.len() as u32;
    let mut fin = Fin::FINAL;
    // What the first reading ended at: the second is tried where it ends elsewhere.
    let mut first: Option<Hoist> = None;
    for live in [false, true] {
        let mut h = Hoist {
            n,
            c,
            live,
            seen: IdMap::default(),
            leaves: Vec::new(),
            found: Vec::new(),
            ops: 0,
        };
        h.pair(r, cx, a, b)?;
        if h.ops == 0
            || first
                .as_ref()
                .is_some_and(|t| t.leaves == h.leaves && t.found == h.found)
        {
            continue;
        }
        // A slice of a value: the value, and where the slice is.
        let view = |cx: &Context, v: u32| {
            let p = cx.node(v);
            if p.op == OpCode::Extract {
                (p.a, p.b as u16, p.width)
            } else {
                (v, 0, p.width)
            }
        };
        // The leaves that are the same slice of both values of a wider leaf (the widest
        // such), and how far into it.
        let slice_of = |cx: &Context, (x, y): (u32, u32)| {
            let ((vx, i, len), (vy, j, _)) = (view(cx, x), view(cx, y));
            h.leaves
                .iter()
                .filter_map(|&(p, q)| {
                    let ((vp, lp, wp), (vq, lq, _)) = (view(cx, p), view(cx, q));
                    (vp == vx
                        && vq == vy
                        && wp > len
                        && i >= lp
                        && j >= lq
                        && i - lp == j - lq
                        && i - lp + len <= wp)
                        .then(|| (wp, (p, q), i - lp))
                })
                .max_by_key(|s| s.0)
        };
        let bases: Vec<(u32, u32)> = h
            .leaves
            .iter()
            .copied()
            .filter(|&l| slice_of(cx, l).is_none())
            .collect();
        if bases.len() > MAX_BASES {
            first = Some(h);
            continue;
        }
        let mut of: IdMap<(u32, u32), u32> = IdMap::default();
        // What the candidate is built over: the condition, the pairs, and a pair's `select`
        // itself where it exists and something live reads it (it is there either way).
        let mut atoms = vec![c];
        for &(x, y) in &bases {
            let there = h.exists(r, cx, x, y)?;
            let s = r.build(cx, |cx| cx.c_select(c, x, y))?;
            of.insert((x, y), s);
            if there {
                atoms.push(s);
            } else {
                atoms.extend([x, y]);
            }
        }
        for &l in &h.leaves {
            if let Some((_, base, o)) = slice_of(cx, l) {
                let (s, len) = (of[&base], cx.wid(l.0));
                of.insert(l, r.build(cx, |cx| cx.c_extract(s, o, len))?);
            }
        }
        atoms.extend(&h.found);
        let e = h.build(r, cx, &of, &mut IdMap::default(), a, b)?;
        match finish(r, cx, PassKind::Casts, n, e, start, &atoms, fin)? {
            Step::Normal(f) => fin = f,
            step => return Ok(step),
        }
        first = Some(h);
    }
    super::discard(r, cx, start);
    Ok(Step::Normal(fin))
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
    if node.op == OpCode::Select {
        return hoisted(r, cx, n);
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
        own: Some(n),
        whole: false,
        arms: 0,
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
