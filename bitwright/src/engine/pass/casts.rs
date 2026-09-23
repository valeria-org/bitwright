//! The casts pass: an `extract<lo, n>(x)` (a `trunc` when `lo = 0`) is pushed into `x`:
//!
//! - through `+ − * neg` when `lo = 0` (the low bits of a sum, difference or product depend
//!   only on the low bits of its operands), and through `& | ^ ~` and `select` for any `lo`;
//! - through shifts by a constant, zero and sign extensions, and `concat`, by re-indexing
//!   (or becoming the constant 0, or the extension of the part that remains).
//!
//! The narrowing is computed for the whole region below the extract (bounded), and replaces the
//! node only when that region gets strictly smaller: `trunc(zext(x) + zext(y))` becomes
//! `x + y`, while `trunc(a + b)` over opaque operands stays as it is.

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
                        stop(r, cx, st)?
                    }
                } else if lo64 + k >= w64 {
                    r.build(cx, |cx| cx.mk_const(&BitVec::zero(crate::Width::new(n)?)))?
                } else if lo64 + k + n64 <= w64 {
                    narrow(r, cx, st, node.a, (lo64 + k) as u16, n)?
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

/// The casts pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    if node.op != OpCode::Extract {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let before = cx.len() as u32;
    let mut st = Narrow {
        memo: IdMap::default(),
        stops: Vec::new(),
        pushes: 0,
    };
    let e = narrow(r, cx, &mut st, node.a, node.b as u16, node.width)?;
    if st.pushes > MAX_PUSHES {
        count(r).atomized += 1;
    }
    finish(r, cx, PassKind::Casts, n, e, before, &st.stops, Fin::FINAL)
}
