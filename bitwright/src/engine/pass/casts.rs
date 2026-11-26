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
    Ok(is_live(r, e).then_some(e))
}

fn is_live(r: &Runner<'_, '_>, id: u32) -> bool {
    !r.life.dead.contains(id) && r.life.live.uses(id).is_some_and(|u| u > 0)
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
    Ok(is_live(r, e).then_some(e))
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
            // Non-straddling slice of a constant rotation: `rotl(a, r)` places `[w - r, w)` at
            // `[0, r)` and `[0, w - r)` at `[r, w)`.
            OpCode::RotL | OpCode::RotR if cx.const_val(node.b).is_some() && w > 0 => {
                let raw = cx
                    .const_val(node.b)
                    .and_then(|k| k.to_u64())
                    .map(|k| (k % u64::from(w)) as u16);
                if let Some(raw) = raw {
                    let rot_left = if node.op == OpCode::RotL || raw == 0 {
                        raw
                    } else {
                        w - raw
                    };
                    if rot_left == 0 {
                        narrow(r, cx, st, node.a, lo, n)?
                    } else if lo + n <= rot_left {
                        narrow(r, cx, st, node.a, lo + (w - rot_left), n)?
                    } else if lo >= rot_left {
                        narrow(r, cx, st, node.a, lo - rot_left, n)?
                    } else {
                        stop(r, cx, st)?
                    }
                } else {
                    stop(r, cx, st)?
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

/// `zext(x) | select(sign(x), high_mask, 0)` is `sext(x)`: the low bits are
/// exactly `x`, and every bit above them is the same copy of its top bit.
/// Read only these nodes (no search into `x`); `select` can swap its arms
/// when the condition is complemented.
fn selected_sext(cx: &Context, a: u32, b: u32) -> Option<(u16, u32)> {
    let (a, b) = (cx.node(a), cx.node(b));
    let (x, sel) = match (a.op, b.op) {
        (OpCode::Zext, OpCode::Select) => (a.a, b),
        (OpCode::Select, OpCode::Zext) => (b.a, a),
        _ => return None,
    };
    let w = cx.width_of(x);
    let (sign_word, sign_bit) = {
        let xn = cx.node(x);
        if xn.op == OpCode::Extract {
            (xn.a, xn.b as u16 + w.bits() - 1)
        } else {
            (x, w.bits() - 1)
        }
    };
    // Whether the condition means "negative". Shared `bit_literal` recognizes all signed,
    // unsigned-threshold, mask-bit, extract, and negated spellings of the sign bit.
    let (word, bit, negative) = crate::expr::field::bit_literal(cx, sel.a);
    if word != sign_word || bit != sign_bit {
        return None;
    }
    let (set, clear) = if negative {
        (sel.b, sel.c)
    } else {
        (sel.c, sel.b)
    };
    if !cx.const_val(clear)?.is_zero() {
        return None;
    }
    let mask = cx.const_val(set)?;
    (mask == crate::facts::known::high_mask(mask.width(), u32::from(sel.width - w.bits())))
        .then_some((w.bits(), x))
}

/// The width `k` and operand `x` when `n` sign-extends the low `k` bits of `x` spelled with
/// a selected high mask (above), shifts or arithmetic: `(x << c) >>s c` (`k = W − c`), or
/// `((x & (2^k − 1)) ^ 2^(k−1)) − 2^(k−1)` (the builder's `+ −2^(k−1)`;
/// the masked value may also be `zext(trunc<k>(x))`).
fn sext_idiom(cx: &Context, n: u32) -> Option<(u16, u32)> {
    let node = cx.node(n);
    let w = node.width;
    let small = |i: u32| cx.const_val(i).and_then(|v| v.to_u64());
    match node.op {
        OpCode::Or => selected_sext(cx, node.a, node.b),
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
                OpCode::And => {
                    let mask = cx.const_val(t.b)?;
                    (mask == crate::facts::known::low_mask(k.width(), u32::from(kk)))
                        .then_some((kk, t.a))
                }
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
        Ok(r.life.live.uses(s).is_some_and(|u| u > 0))
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
                if r.life.live.uses(s).is_some_and(|u| u > 0) {
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
    // Shallow 1-level hoist: when deep pairing hit `MAX_BASES` because the differing operands
    // themselves share an outer opcode, hoisting just the matching top-level op (`a >>u k` /
    // `b >>u k`, `rotl(a, k)` / `rotl(b, k)`, etc.) over a single `select` can still strictly
    // shrink the DAG.
    {
        let (na, nb) = (cx.node(a), cx.node(b));
        let (ka, kb) = ([na.a, na.b, na.c], [nb.a, nb.b, nb.c]);
        let arity = na.op.arity();
        let same_top = na.op == nb.op
            && pairable(na.op)
            && na.width == nb.width
            && (0..3).all(|s| {
                if s < arity {
                    cx.wid(ka[s]) == cx.wid(kb[s])
                } else {
                    ka[s] == kb[s]
                }
            });
        if same_top {
            let mut diff_slot = None;
            let mut multi_diff = false;
            for s in 0..arity {
                if ka[s] != kb[s] {
                    if diff_slot.is_some() {
                        multi_diff = true;
                        break;
                    }
                    diff_slot = Some(s);
                }
            }
            if !multi_diff && let Some(s) = diff_slot {
                let (x, y) = (ka[s], kb[s]);
                let sel_node = crate::expr::Node::new(OpCode::Select, cx.wid(x), c, x, y);
                let there = cx.find(&sel_node).is_some_and(|sid| {
                    sid != n && {
                        super::refresh_uses(r, cx).is_ok()
                            && r.life.live.uses(sid).is_some_and(|u| u > 0)
                    }
                });
                let sel = r.build(cx, |cx| cx.c_select(c, x, y))?;
                let mut kids = ka;
                kids[s] = sel;
                let e = r.build(cx, |cx| cx.rebuild(a, kids))?;
                let mut atoms = vec![c];
                for (t, &child) in ka.iter().enumerate().take(arity) {
                    if t != s {
                        atoms.push(child);
                    }
                }
                if there {
                    atoms.push(sel);
                } else {
                    atoms.extend([x, y]);
                }
                match finish(r, cx, PassKind::Casts, n, e, start, &atoms, fin)? {
                    Step::Normal(f) => fin = f,
                    step => return Ok(step),
                }
            }
        }
    }
    // Live-select binary decomposition: for `op ∈ {Add, Sub, Or, Xor}` (where `k op 0 == k`),
    // rewrite `select(c, u op v, k)` to `select(c, u, k) op select(c, v, 0)` (and symmetrically
    // when the op is on the false arm) whenever both sub-selects already exist and are live.
    let w = cx.wid(n);
    if w <= 64 {
        let zero_mark = cx.len() as u32;
        let zv = r.build(cx, |cx| cx.mk_const_u64(w, 0))?;
        if zv < zero_mark {
            let find_live_sel = |r: &mut Runner<'_, '_>, cx: &Context, p: u32, q: u32| -> Result<Option<u32>, Stop> {
                let Some(sid) = cx.find(&crate::expr::Node::new(OpCode::Select, w, c, p, q)) else {
                    return Ok(None);
                };
                if sid == n {
                    return Ok(None);
                }
                super::refresh_uses(r, cx)?;
                Ok(r.life.live.uses(sid).is_some_and(|u| u > 0).then_some(sid))
            };
            for (op_arm, k_arm, on_true) in [(a, b, true), (b, a, false)] {
                let on = cx.node(op_arm);
                let bop = match on.op {
                    OpCode::Add => BinOp::Add,
                    OpCode::Sub => BinOp::Sub,
                    OpCode::Or => BinOp::Or,
                    OpCode::Xor => BinOp::Xor,
                    _ => continue,
                };
                let (u, v) = (on.a, on.b);
                let mut candidates = Vec::with_capacity(2);
                if on_true {
                    candidates.push(((u, k_arm), (v, zv)));
                    if bop.is_commutative() {
                        candidates.push(((u, zv), (v, k_arm)));
                    }
                } else {
                    candidates.push(((k_arm, u), (zv, v)));
                    if bop.is_commutative() {
                        candidates.push(((zv, u), (k_arm, v)));
                    }
                }
                for ((p1, q1), (p2, q2)) in candidates {
                    if let Some(s1) = find_live_sel(r, cx, p1, q1)?
                        && let Some(s2) = find_live_sel(r, cx, p2, q2)?
                    {
                        let e = r.build(cx, |cx| cx.c_bin(bop, s1, s2))?;
                        match finish(r, cx, PassKind::Casts, n, e, start, &[s1, s2], fin)? {
                            Step::Normal(f) => fin = f,
                            step => return Ok(step),
                        }
                    }
                }
            }
        }
    }
    super::discard(r, cx, start);
    Ok(Step::Normal(fin))
}

/// Rewrite `trunc<nw>(X) op C` (for `op ∈ {Add, Sub, Mul, And, Or, Xor, Shl}`) to `trunc<nw>(wide)`
/// whenever a live `wide = X op C_w` (with `trunc<nw>(C_w) == C`) already exists in `cx`.
fn narrow_to_live_wide(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let nw = node.width;
    if nw >= 64
        || !matches!(
            node.op,
            OpCode::Add
                | OpCode::Sub
                | OpCode::Mul
                | OpCode::And
                | OpCode::Or
                | OpCode::Xor
                | OpCode::Shl
        )
    {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let comm = node.op.as_bin().is_some_and(BinOp::is_commutative);
    let (tr, cval, tr_is_lhs) = if let Some(cv) = cx.const_val(node.b) {
        (node.a, cv, true)
    } else if node.op != OpCode::Shl && let Some(cv) = cx.const_val(node.a) {
        (node.b, cv, false)
    } else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    if node.op == OpCode::Shl && !cval.to_u64().is_some_and(|s| s < u64::from(nw)) {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let tn = cx.node(tr);
    if tn.op != OpCode::Extract || tn.b != 0 {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let x = tn.a;
    let w = cx.wid(x);
    if w <= nw || w > 64 {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let Ok(wt) = crate::Width::new(w) else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    let Ok(zc) = cval.zext(wt) else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    let Ok(sc) = cval.sext(wt) else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    let before = cx.len() as u32;
    let mut cands = vec![zc];
    if node.op != OpCode::Shl && sc != zc {
        cands.push(sc);
    }
    for cw in cands {
        let mark = cx.len() as u32;
        let k = r.build(cx, |cx| cx.mk_const(&cw))?;
        if k >= mark {
            super::discard(r, cx, mark);
            continue;
        }
        let (a1, b1) = if tr_is_lhs { (x, k) } else { (k, x) };
        let wide = cx
            .find(&crate::expr::Node::new(node.op, w, a1, b1, 0))
            .or_else(|| {
                comm.then(|| cx.find(&crate::expr::Node::new(node.op, w, b1, a1, 0)))
                    .flatten()
            });
        if let Some(wide) = wide {
            super::refresh_uses(r, cx)?;
            if is_live(r, wide) {
                let e = r.build(cx, |cx| cx.c_extract(wide, 0, nw))?;
                let mut stops = vec![wide];
                if e < before {
                    stops.push(e);
                }
                match finish(r, cx, PassKind::Casts, n, e, before, &stops, Fin::FINAL)? {
                    Step::Normal(_) => {}
                    step => return Ok(step),
                }
            }
        }
    }
    if node.op != OpCode::Shl
        && cx.len() <= 4096
        && let Ok(nwt) = crate::Width::new(nw)
    {
        super::refresh_uses(r, cx)?;
        r.meter
            .charge(Counter::PassWork, (cx.len() as u64) / 64 + 1)?;
        let len = cx.len() as u32;
        for wide in 0..len {
            let wn = cx.node(wide);
            if wn.op != node.op || wn.width != w || !is_live(r, wide) {
                continue;
            }
            let k_id = if tr_is_lhs {
                if wn.a == x {
                    Some(wn.b)
                } else if comm && wn.b == x {
                    Some(wn.a)
                } else {
                    None
                }
            } else if wn.b == x {
                Some(wn.a)
            } else if comm && wn.a == x {
                Some(wn.b)
            } else {
                None
            };
            if let Some(k_id) = k_id
                && cx
                    .const_val(k_id)
                    .and_then(|kv| kv.trunc(nwt).ok())
                    .is_some_and(|t| t == cval)
            {
                let e = r.build(cx, |cx| cx.c_extract(wide, 0, nw))?;
                let mut stops = vec![wide];
                if e < before {
                    stops.push(e);
                }
                match finish(r, cx, PassKind::Casts, n, e, before, &stops, Fin::FINAL)? {
                    Step::Normal(_) => {}
                    step => return Ok(step),
                }
            }
        }
    }
    super::discard(r, cx, before);
    Ok(Step::Normal(Fin::FINAL))
}

/// Find existing `w`-bit nodes `id` in `cx` (`cx.find` only, zero allocations) that satisfy
/// `(id & req_mask) == (zext<w>(u) & req_mask)` for every input (`1 <= nw < w <= 64`).
pub(super) fn find_wide_masked(cx: &Context, u: u32, w: u16, req_mask: u64, depth: u8) -> Vec<u32> {
    let mut out = Vec::new();
    let nw = cx.wid(u);
    if nw == 0 || nw >= w || w > 64 || depth == 0 {
        return out;
    }
    let low_nw = (1u64 << nw) - 1;
    let full_w = u64::MAX >> (64 - w);
    let req_mask = req_mask & full_w;
    let Ok(wt) = crate::Width::new(w) else {
        return out;
    };
    let push = |out: &mut Vec<u32>, id: u32| {
        if !out.contains(&id) && out.len() < 4 {
            out.push(id);
        }
    };
    let find_bin = |op: OpCode, a: u32, b: u32| -> Option<u32> {
        cx.find(&crate::expr::Node::new(op, w, a, b, 0)).or_else(|| {
            op.as_bin()
                .is_some_and(BinOp::is_commutative)
                .then(|| cx.find(&crate::expr::Node::new(op, w, b, a, 0)))
                .flatten()
        })
    };
    let find_const = |val: u64| -> Option<u32> { cx.find_const_u64(w, val & full_w) };

    if let Some(cv) = cx.const_val(u).and_then(|v| v.to_u64()) {
        if let Some(cid) = find_const(cv & low_nw) {
            push(&mut out, cid);
        }
        if (req_mask & !low_nw) == 0
            && let Ok(sc) = cx.const_val(u).unwrap().sext(wt)
            && let Some(sc_u) = sc.to_u64()
            && let Some(cid) = find_const(sc_u)
        {
            push(&mut out, cid);
        }
        return out;
    }

    let n = cx.node(u);
    let needs_zero_above = (req_mask & !low_nw) != 0;

    // If caller requires bits `>= nw` to be zero, any `raw` matching `u` on `low_nw` masked by
    // `& low_nw` in `cx` is exact on all `w` bits (except `Extract` at `lo > 0`, where
    // `zext<w>(extract<lo, nw>(x))` is already canonical over `(x >>u lo) & low_nw`).
    if needs_zero_above
        && !(n.op == OpCode::Extract && n.b > 0)
        && let Some(m_id) = find_const(low_nw)
    {
        for raw in find_wide_masked(cx, u, w, req_mask & low_nw, depth) {
            if let Some(masked) = find_bin(OpCode::And, raw, m_id) {
                push(&mut out, masked);
            }
        }
    }

    match n.op {
        OpCode::Zext => {
            out.extend(find_wide_masked(cx, n.a, w, req_mask, depth - 1));
        }
        OpCode::Extract if cx.wid(n.a) == w => {
            let lo = n.b as u16;
            if lo == 0 {
                if !needs_zero_above {
                    push(&mut out, n.a);
                }
                if let Some(m_id) = find_const(low_nw)
                    && let Some(masked) = find_bin(OpCode::And, n.a, m_id)
                {
                    push(&mut out, masked);
                }
            } else if u32::from(lo) + u32::from(nw) <= u32::from(w) {
                if (u32::from(lo) + u32::from(nw) == u32::from(w) || !needs_zero_above)
                    && let Some(sh_c) = find_const(u64::from(lo))
                    && let Some(shifted) =
                        cx.find(&crate::expr::Node::new(OpCode::LShr, w, n.a, sh_c, 0))
                {
                    push(&mut out, shifted);
                }
                if !needs_zero_above {
                    if let Some(rl_c) = find_const(u64::from(w - lo))
                        && let Some(rotated) =
                            cx.find(&crate::expr::Node::new(OpCode::RotL, w, n.a, rl_c, 0))
                    {
                        push(&mut out, rotated);
                    }
                    if let Some(rr_c) = find_const(u64::from(lo))
                        && let Some(rotated) =
                            cx.find(&crate::expr::Node::new(OpCode::RotR, w, n.a, rr_c, 0))
                    {
                        push(&mut out, rotated);
                    }
                }
            }
        }
        OpCode::And => {
            let const_side = if let Some(c) = cx.const_val(n.b).and_then(|v| v.to_u64()) {
                Some((n.a, c & low_nw))
            } else {
                cx.const_val(n.a)
                    .and_then(|v| v.to_u64())
                    .map(|c| (n.b, c & low_nw))
            };
            if let Some((arg, cmask)) = const_side {
                if let Some(cid) = find_const(cmask) {
                    for wa in find_wide_masked(cx, arg, w, req_mask & cmask, depth - 1) {
                        if let Some(id) = find_bin(OpCode::And, wa, cid) {
                            push(&mut out, id);
                        }
                    }
                }
            } else {
                for wa in find_wide_masked(cx, n.a, w, req_mask, depth - 1) {
                    for wb in find_wide_masked(cx, n.b, w, req_mask, depth - 1) {
                        if let Some(id) = find_bin(OpCode::And, wa, wb) {
                            push(&mut out, id);
                        }
                    }
                }
            }
        }
        OpCode::Not if !needs_zero_above => {
            for wa in find_wide_masked(cx, n.a, w, req_mask, depth - 1) {
                if let Some(id) = cx.find(&crate::expr::Node::new(OpCode::Not, w, wa, 0, 0)) {
                    push(&mut out, id);
                }
            }
        }
        OpCode::LShr => {
            if let Some(s) = cx.const_val(n.b).and_then(|v| v.to_u64())
                && s > 0
                && s < u64::from(nw)
                && let Some(sh_c) = find_const(s)
            {
                // Exact `w`-bit operand (bits `>= nw` already zero) shifted right is exact on all `w` bits.
                for wa in find_wide_masked(cx, n.a, w, full_w, depth - 1) {
                    if let Some(id) = cx.find(&crate::expr::Node::new(OpCode::LShr, w, wa, sh_c, 0)) {
                        push(&mut out, id);
                    }
                }
                // Unmasked operand works when `req_mask` only reads bits `< nw - s`.
                let valid_shifted = (1u64 << (u64::from(nw) - s)) - 1;
                if (req_mask & !valid_shifted) == 0 {
                    for wa in find_wide_masked(cx, n.a, w, (req_mask << s) & low_nw, depth - 1) {
                        if let Some(id) =
                            cx.find(&crate::expr::Node::new(OpCode::LShr, w, wa, sh_c, 0))
                        {
                            push(&mut out, id);
                        }
                    }
                }
            }
        }
        OpCode::Add | OpCode::Sub | OpCode::Mul if !needs_zero_above => {
            for wa in find_wide_masked(cx, n.a, w, low_nw, depth - 1) {
                for wb in find_wide_masked(cx, n.b, w, low_nw, depth - 1) {
                    if let Some(id) = find_bin(n.op, wa, wb) {
                        push(&mut out, id);
                    }
                }
            }
            if out.is_empty() && n.op == OpCode::Add {
                let mut leaves = Vec::with_capacity(6);
                let mut st = vec![u];
                let mut ok = true;
                while let Some(cur) = st.pop() {
                    if leaves.len() + st.len() > 8 {
                        ok = false;
                        break;
                    }
                    let cn = cx.node(cur);
                    if cn.op == OpCode::Add {
                        st.push(cn.b);
                        st.push(cn.a);
                    } else {
                        leaves.push(cur);
                    }
                }
                if ok && leaves.len() >= 3 {
                    let mut w_vars = Vec::with_capacity(leaves.len());
                    let mut w_consts = Vec::new();
                    for l in leaves {
                        let Some(&wl) =
                            find_wide_masked(cx, l, w, low_nw, depth - 1).first()
                        else {
                            ok = false;
                            break;
                        };
                        if cx.is_const(wl) {
                            w_consts.push(wl);
                        } else {
                            w_vars.push(wl);
                        }
                    }
                    if ok {
                        w_vars.sort_unstable();
                        let mut seq = w_vars;
                        seq.extend(w_consts);
                        let mut acc = Some(seq[0]);
                        for &item in &seq[1..] {
                            acc = acc.and_then(|a| find_bin(OpCode::Add, a, item));
                        }
                        if let Some(id) = acc {
                            push(&mut out, id);
                        }
                    }
                }
            }
        }
        OpCode::Neg if !needs_zero_above => {
            for wa in find_wide_masked(cx, n.a, w, low_nw, depth - 1) {
                if let Some(id) = cx.find(&crate::expr::Node::new(OpCode::Neg, w, wa, 0, 0)) {
                    push(&mut out, id);
                }
            }
        }
        OpCode::Shl if !needs_zero_above => {
            if let Some(s) = cx.const_val(n.b).and_then(|v| v.to_u64())
                && s < u64::from(nw)
                && let Some(sh_c) = find_const(s)
            {
                for wa in find_wide_masked(cx, n.a, w, low_nw >> s, depth - 1) {
                    if let Some(id) = cx.find(&crate::expr::Node::new(OpCode::Shl, w, wa, sh_c, 0)) {
                        push(&mut out, id);
                    }
                }
            }
        }
        OpCode::Or | OpCode::Xor => {
            let sub_mask = if needs_zero_above { full_w } else { req_mask };
            for wa in find_wide_masked(cx, n.a, w, sub_mask, depth - 1) {
                for wb in find_wide_masked(cx, n.b, w, sub_mask, depth - 1) {
                    if let Some(id) = find_bin(n.op, wa, wb) {
                        push(&mut out, id);
                    }
                }
            }
        }
        _ => {}
    }
    out
}

/// Replace `zext<w>(narrow)` with an already-live `w`-bit equivalent node in `cx` (`added = 0`).
fn zext_to_live_wide(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let w = node.width;
    let nw = cx.wid(node.a);
    if node.op != OpCode::Zext || w > 64 || nw >= w {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let full_w = u64::MAX >> (64 - w);
    let cands = find_wide_masked(cx, node.a, w, full_w, 8);
    let mut fin = Fin::FINAL;
    if !cands.is_empty() {
        super::refresh_uses(r, cx)?;
        let before = cx.len() as u32;
        for wide in cands {
            if wide != n && is_live(r, wide) {
                match finish(r, cx, PassKind::Casts, n, wide, before, &[wide], Fin::FINAL)? {
                    Step::Normal(f) => fin = fin.and(f),
                    step => return Ok(step),
                }
            }
        }
    }
    Ok(Step::Normal(fin))
}

pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let mut declined = Fin::FINAL;
    if matches!(
        node.op,
        OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Shl
    ) {
        match narrow_to_live_wide(r, cx, n)? {
            Step::Normal(f) => declined = declined.and(f),
            step => return Ok(step),
        }
    }
    // Narrow 1-bit masked wide expressions `x & 1` (`width > 1`) via `zext<W>(narrow(x, 0, 1))`
    // whenever pushing `trunc<1>` strictly shrinks the DAG (e.g. compound boolean expressions
    // over shifts/zexts, or `(y >>u k) & 1` when `extract<k, 1>(y)` is already live).
    if node.op == OpCode::And && node.width > 1 {
        let one_mask = match (cx.const_val(node.a), cx.const_val(node.b)) {
            (None, Some(k)) if k.to_u64() == Some(1) => Some(node.a),
            (Some(k), None) if k.to_u64() == Some(1) => Some(node.b),
            _ => None,
        };
        if let Some(other) = one_mask
            && matches!(
                cx.node(other).op,
                OpCode::And
                    | OpCode::Or
                    | OpCode::Xor
                    | OpCode::Not
                    | OpCode::Select
                    | OpCode::Zext
                    | OpCode::Sext
                    | OpCode::Concat
            )
        {
            let before = cx.len() as u32;
            if let Some((mut b1, fin, stops)) = narrowed_from(r, cx, other, 0, 1)? {
                // Fold 1-bit `((u ^ v) & (w ^ u)) ^ u` directly to 2-node Majority `select`
                // so `zext<W>(select(...))` strictly shrinks 6-node `& 1` trees without cycles.
                let bn = cx.node(b1);
                if bn.op == OpCode::Xor {
                    let xor_other = |id: u32, target: u32| -> Option<u32> {
                        let xn = cx.node(id);
                        if xn.op != OpCode::Xor {
                            None
                        } else if xn.a == target {
                            Some(xn.b)
                        } else if xn.b == target {
                            Some(xn.a)
                        } else {
                            None
                        }
                    };
                    let mut maj: Option<[u32; 3]> = None;
                    for (and_side, u) in [(bn.a, bn.b), (bn.b, bn.a)] {
                        let an = cx.node(and_side);
                        if an.op == OpCode::And
                            && let Some(v) = xor_other(an.a, u)
                            && let Some(w_id) = xor_other(an.b, u)
                        {
                            maj = Some([u, v, w_id]);
                            break;
                        }
                    }
                    if let Some(mut tri) = maj {
                        tri.sort_by(|&a, &b| cx.order(a, b));
                        b1 = if tri[0] == tri[1] {
                            tri[0]
                        } else if tri[1] == tri[2] {
                            tri[1]
                        } else {
                            r.build(cx, |cx| {
                                let x = cx.c_bin(BinOp::Xor, tri[1], tri[2])?;
                                cx.c_select(x, tri[0], tri[1])
                            })?
                        };
                    }
                }
                let e = r.build(cx, |cx| cx.c_zext(b1, node.width))?;
                super::discard_but(r, cx, before, e);
                match finish(r, cx, PassKind::Casts, n, e, before, &stops, fin)? {
                    Step::Normal(f) => declined = declined.and(f),
                    done => return Ok(done),
                }
            } else {
                super::discard(r, cx, before);
            }
        } else if one_mask.is_none() {
            let zext_bit = if cx.node(node.b).op == OpCode::Zext && cx.wid(cx.node(node.b).a) == 1 {
                Some((node.a, cx.node(node.b).a))
            } else if cx.node(node.a).op == OpCode::Zext && cx.wid(cx.node(node.a).a) == 1 {
                Some((node.b, cx.node(node.a).a))
            } else {
                None
            };
            if let Some((other, bit)) = zext_bit
                && !(cx.node(other).op == OpCode::Zext && cx.wid(cx.node(other).a) == 1)
                && matches!(
                    cx.node(other).op,
                    OpCode::And
                        | OpCode::Or
                        | OpCode::Xor
                        | OpCode::Not
                        | OpCode::Select
                        | OpCode::Zext
                        | OpCode::Sext
                        | OpCode::Concat
                        | OpCode::LShr
                        | OpCode::RotL
                        | OpCode::RotR
                        | OpCode::Add
                        | OpCode::Sub
                        | OpCode::Mul
                )
            {
                let before = cx.len() as u32;
                if let Some((b1, fin, mut stops)) = narrowed_from(r, cx, other, 0, 1)? {
                    let e = r.build(cx, |cx| {
                        let band = cx.c_bin(BinOp::And, b1, bit)?;
                        cx.c_zext(band, node.width)
                    })?;
                    if bit < before && !stops.contains(&bit) {
                        stops.push(bit);
                    }
                    super::discard_but(r, cx, before, e);
                    match finish(r, cx, PassKind::Casts, n, e, before, &stops, fin)? {
                        Step::Normal(f) => declined = declined.and(f),
                        done => return Ok(done),
                    }
                } else {
                    super::discard(r, cx, before);
                }
            }
        }
    }
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
        let hi = cx.node(node.a);
        if hi.op == OpCode::Zext
            && cx.wid(hi.a) == 1
            && node.width <= 64
            && let Some(lo_bv) = cx.const_val(node.b)
            && let Some(lo_u64) = lo_bv.to_u64()
            && lo_u64 != 0
        {
            let l_bits = cx.wid(node.b);
            if l_bits < node.width {
                let before = cx.len() as u32;
                let bit = hi.a;
                let t_val = (1u64 << l_bits) | lo_u64;
                let e = r.build(cx, |cx| {
                    let kt = cx.mk_const_u64(node.width, t_val)?;
                    let kf = cx.mk_const_u64(node.width, lo_u64)?;
                    cx.c_select(bit, kt, kf)
                })?;
                match super::finish_with(
                    r,
                    cx,
                    PassKind::Casts,
                    n,
                    e,
                    before,
                    &[bit],
                    Fin::FINAL,
                    true,
                )? {
                    Step::Normal(_) => {}
                    done => return Ok(done),
                }
            }
        }
        return rejoined(r, cx, n);
    }
    if node.op == OpCode::Select {
        return hoisted(r, cx, n);
    }
    if node.op == OpCode::Popcnt {
        let arg = cx.node(node.a);
        if arg.op == OpCode::Zext {
            let before = cx.len() as u32;
            let e = r.build(cx, |cx| {
                let p = cx.c_un(UnOp::Popcnt, arg.a)?;
                cx.c_zext(p, node.width)
            })?;
            return super::finish_with(
                r,
                cx,
                PassKind::Casts,
                n,
                e,
                before,
                &[arg.a],
                Fin::FINAL,
                true,
            );
        }
        if node.width <= 64 && arg.op == OpCode::And {
            let pair = match (cx.const_val(arg.a), cx.const_val(arg.b)) {
                (None, Some(k)) => k.to_u64().map(|m| (arg.a, m)),
                (Some(k), None) => k.to_u64().map(|m| (arg.b, m)),
                _ => None,
            };
            if let Some((shifted, mask)) = pair
                && mask != 0
                && cx.node(shifted).op == OpCode::LShr
            {
                let sn = cx.node(shifted);
                if let Some(sh) = cx.const_val(sn.b).and_then(|v| v.to_u64())
                    && sh < 64
                {
                    let tz = mask.trailing_zeros();
                    let lo = sh as u32 + tz;
                    let m_shifted = mask >> tz;
                    let span = 64 - m_shifted.leading_zeros();
                    if lo > 0
                        && span > 0
                        && span < u32::from(node.width)
                        && lo + span <= u32::from(cx.wid(sn.a))
                    {
                        let run = m_shifted == (u64::MAX >> (64 - span));
                        let before = cx.len() as u32;
                        let e = r.build(cx, |cx| {
                            let mut field = cx.c_extract(sn.a, lo as u16, span as u16)?;
                            if !run {
                                let mc = cx.mk_const_u64(span as u16, m_shifted)?;
                                field = cx.c_bin(BinOp::And, field, mc)?;
                            }
                            let p = cx.c_un(UnOp::Popcnt, field)?;
                            cx.c_zext(p, node.width)
                        })?;
                        return super::finish_with(
                            r,
                            cx,
                            PassKind::Casts,
                            n,
                            e,
                            before,
                            &[sn.a],
                            Fin::FINAL,
                            true,
                        );
                    }
                }
            }
        }
        return Ok(Step::Normal(Fin::FINAL));
    }
    if node.op == OpCode::Zext {
        let p = cx.node(node.a);
        if p.op == OpCode::Popcnt {
            let ex = cx.node(p.a);
            if ex.op == OpCode::Extract && ex.b == 0 && cx.wid(ex.a) == node.width {
                let (kb_opt, kfin) = super::known(r, cx, ex.a)?;
                if let Some(kb) = kb_opt {
                    let high = BitVec::un_unchecked(
                        UnOp::Not,
                        &crate::facts::known::low_mask(cx.width_of(n), u32::from(ex.width)),
                    );
                    if BitVec::bin_unchecked(BinOp::And, &kb.known_zero(), &high) == high {
                        let before = cx.len() as u32;
                        let e = r.build(cx, |cx| cx.c_un(UnOp::Popcnt, ex.a))?;
                        match finish(r, cx, PassKind::Casts, n, e, before, &[ex.a], kfin)? {
                            Step::Normal(_) => {}
                            done => return Ok(done),
                        }
                    }
                }
                let mask_bv = crate::facts::known::low_mask(cx.width_of(n), u32::from(ex.width));
                let before = cx.len() as u32;
                let mc = r.build(cx, |cx| cx.mk_const(&mask_bv))?;
                let e = r.build(cx, |cx| {
                    let masked = cx.c_bin(BinOp::And, ex.a, mc)?;
                    cx.c_un(UnOp::Popcnt, masked)
                })?;
                let mut stops = vec![ex.a];
                if mc < before {
                    stops.push(mc);
                }
                match super::finish_with(
                    r,
                    cx,
                    PassKind::Casts,
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
        // `zext<U>(extract<0, N>(~x))` / `zext<U>(~extract<0, N>(x))` (`N < wid(x)`) ->
        // `(x_u & low_mask(N)) ^ low_mask(N)` (collapsing to `x ^ low_mask(N)` when high bits are 0).
        let not_trunc = if p.op == OpCode::Extract
            && p.b == 0
            && cx.node(p.a).op == OpCode::Not
            && p.width < cx.wid(cx.node(p.a).a)
        {
            Some((cx.node(p.a).a, p.width))
        } else if p.op == OpCode::Not
            && cx.node(p.a).op == OpCode::Extract
            && cx.node(p.a).b == 0
            && cx.node(p.a).width < cx.wid(cx.node(p.a).a)
        {
            let ex = cx.node(p.a);
            Some((ex.a, ex.width))
        } else {
            None
        };
        if let Some((src, nbits)) = not_trunc {
            let mask_bv = crate::facts::known::low_mask(cx.width_of(n), u32::from(nbits));
            let before = cx.len() as u32;
            let (mc, masked, e) = r.build(cx, |cx| {
                let src_u = match cx.wid(src).cmp(&node.width) {
                    core::cmp::Ordering::Equal => src,
                    core::cmp::Ordering::Greater => cx.c_extract(src, 0, node.width)?,
                    core::cmp::Ordering::Less => cx.c_zext(src, node.width)?,
                };
                let mc = cx.mk_const(&mask_bv)?;
                let masked = cx.c_bin(BinOp::And, src_u, mc)?;
                let e = cx.c_bin(BinOp::Xor, masked, mc)?;
                Ok((mc, masked, e))
            })?;
            super::refresh_uses(r, cx)?;
            let mut stops = vec![src];
            for id in [mc, masked, e] {
                if id < before && is_live(r, id) && !stops.contains(&id) {
                    stops.push(id);
                }
            }
            match super::finish_with(
                r,
                cx,
                PassKind::Casts,
                n,
                e,
                before,
                &stops,
                Fin::FINAL,
                true,
            )? {
                Step::Normal(f) => declined = declined.and(f),
                done => return Ok(done),
            }
        }
        // `zext<W>(extract<K, N>(x) & M)` / `zext<W>(~extract<K, N>(x) & M)` (`wid(x) == W`, `K > 0`).
        // Single contiguous low-bit runs `M == low_mask(len)` (`!inverted`) fold directly to
        // `zext<W>(extract<K, len>(x))` matching `Shuffle`; non-run or inverted masks become
        // `(x >>u K) & zext<W>(M)` / `~(x >>u K) & zext<W>(M)`.
        if p.op == OpCode::And {
            let (inner, mask_bv) = match (cx.const_val(p.a), cx.const_val(p.b)) {
                (None, Some(m)) => (p.a, Some(m)),
                (Some(m), None) => (p.b, Some(m)),
                _ => (0, None),
            };
            if let Some(mask_bv) = mask_bv {
                let in_node = cx.node(inner);
                let (ex_id, inverted) = if in_node.op == OpCode::Not {
                    (in_node.a, true)
                } else {
                    (inner, false)
                };
                let ex = cx.node(ex_id);
                if ex.op == OpCode::Extract
                    && ex.b > 0
                    && cx.wid(ex.a) == node.width
                    && let Ok(wide_m) = mask_bv.zext(cx.width_of(n))
                {
                    let x = ex.a;
                    let ones = crate::facts::known::count_ones(&mask_bv);
                    let tz = crate::facts::known::trailing_zeros(&mask_bv);
                    let is_single_run = ones > 0
                        && crate::facts::known::bv_lshr(&mask_bv, tz)
                            == crate::facts::known::low_mask(mask_bv.width(), ones);
                    if !inverted && is_single_run && tz == 0 && ones < u32::from(ex.width) {
                        let before = cx.len() as u32;
                        let e = r.build(cx, |cx| {
                            let s = cx.c_extract(x, ex.b as u16, ones as u16)?;
                            cx.c_zext(s, node.width)
                        })?;
                        match finish(r, cx, PassKind::Casts, n, e, before, &[x], Fin::FINAL)? {
                            Step::Normal(f) => declined = declined.and(f),
                            done => return Ok(done),
                        }
                    } else if inverted || !is_single_run {
                        let k_sh = u64::from(ex.b);
                        let w_n = cx.width_of(n);
                        let before = cx.len() as u32;
                        let e = r.build(cx, |cx| {
                            let sh = cx.mk_const(&BitVec::wrapping_from_u64(w_n, k_sh))?;
                            let mut s = cx.c_bin(BinOp::LShr, x, sh)?;
                            if inverted {
                                s = cx.c_un(UnOp::Not, s)?;
                            }
                            let mc = cx.mk_const(&wide_m)?;
                            cx.c_bin(BinOp::And, s, mc)
                        })?;
                        match super::finish_with(
                            r,
                            cx,
                            PassKind::Casts,
                            n,
                            e,
                            before,
                            &[x],
                            Fin::FINAL,
                            true,
                        )? {
                            Step::Normal(f) => declined = declined.and(f),
                            done => return Ok(done),
                        }
                    }
                }
            }
        }
        return match zext_to_live_wide(r, cx, n)? {
            Step::Normal(f) => Ok(Step::Normal(declined.and(f))),
            done => Ok(done),
        };
    }
    if node.op == OpCode::LShr
        && let Some(sh_bv) = cx.const_val(node.b)
        && let Some(sh) = sh_bv.to_u64()
        && sh > 0
        && sh < u64::from(node.width)
    {
        let an = cx.node(node.a);
        if an.op == OpCode::And {
            let pair = match (cx.const_val(an.a), cx.const_val(an.b)) {
                (None, Some(m)) => Some((an.a, m)),
                (Some(m), None) => Some((an.b, m)),
                _ => None,
            };
            if let Some((x, m)) = pair {
                let m_shifted = BitVec::bin_unchecked(BinOp::LShr, &m, &sh_bv);
                let before = cx.len() as u32;
                let e = r.build(cx, |cx| {
                    let s = cx.c_bin(BinOp::LShr, x, node.b)?;
                    let mc = cx.mk_const(&m_shifted)?;
                    cx.c_bin(BinOp::And, s, mc)
                })?;
                let mut stops = vec![x];
                if node.b < before {
                    stops.push(node.b);
                }
                match super::finish_with(
                    r,
                    cx,
                    PassKind::Casts,
                    n,
                    e,
                    before,
                    &stops,
                    Fin::FINAL,
                    true,
                )? {
                    Step::Normal(f) => declined = declined.and(f),
                    done => return Ok(done),
                }
            }
        }
    }
    if node.op != OpCode::Extract {
        return Ok(Step::Normal(declined));
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

#[cfg(test)]
mod extra_tests {
    use crate::{Context, ParseOptions, Width};

    #[test]
    fn casts_hoists_select_and_narrows_live_wide() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Shallow 1-level hoist through shared-op arms
            "let c = k == 0; select(c, (a & b) >>u 10, (d & e) >>u 10) == (select(c, a & b, d & e) >>u 10)",
            // Live-select binary decomposition: select(c, a ^ b, K) == select(c, a, K) ^ select(c, b, 0)
            "let c = k == 0; let s1 = select(c, a, 0x123456789abcdef0:64); let s2 = select(c, b, 0:64); \
             (select(c, a ^ b, 0x123456789abcdef0:64) + s1 + s2) == ((s1 ^ s2) + s1 + s2)",
            // narrow_to_live_wide unifies trunc<32>(x) + C with trunc<32>(x + zext<64>(C))
            "let w = x + 0xba7ea0cf; let n = trunc<32>(x) + 0xba7ea0cf; \
             (extract<16, 1>(n) == extract<16, 1>(w)) & (extract<0, 1>(w) == extract<0, 1>(w))",
            // zext_to_live_wide unifies zext<64>(trunc<32>(x)) and shifted narrow ops with live masked wide terms
            "let m = x & 0xffffffff; (zext<64>(trunc<32>(x)) ^ m) + m == m",
            "let s = (x & 0xffffffff) >>u 5; (zext<64>(trunc<32>(x) >>u 5) ^ s) + s == s",
        ] {
            let e = cx.parse(text, &opt).unwrap();
            let out = crate::prove::valid_under_with(&mut cx, e, None, &cfg, &prover).unwrap();
            assert!(
                matches!(out, crate::prove::Outcome::Proved(_)),
                "expected Proved for {text}, got {out:?}"
            );
        }
    }

    #[test]
    fn casts_rejects_unsound_select_and_trunc_identities() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Non-zero false arm does NOT satisfy K ^ 1 == K
            "let c = k == 0; let s1 = select(c, a, 0x1234:64); let s2 = select(c, b, 1:64); \
             select(c, a ^ b, 0x1234:64) == (s1 ^ s2)",
            // Different low 32-bit constants
            "trunc<32>(x) + 0x1234 == trunc<32>(x + 0x1235)",
            // Unmasked wide right-shift leaks bits >= 32, so zext<64>(trunc<32>(x) >>u 5) != x >>u 5
            "zext<64>(trunc<32>(x) >>u 5) == (x >>u 5)",
        ] {
            let e = cx.parse(text, &opt).unwrap();
            let out = crate::prove::valid_under_with(&mut cx, e, None, &cfg, &prover).unwrap();
            assert!(
                matches!(out, crate::prove::Outcome::Refuted(_)),
                "expected Refuted for {text}, got {out:?}"
            );
        }
    }
}
