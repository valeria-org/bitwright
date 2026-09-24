//! The shuffle pass: bit provenance of values assembled from pieces of other values.
//!
//! For a node of at most [`MAX_WIDTH`] bits, every output bit is traced to a constant or to one
//! bit of a *source* (an atom): through `&` with a constant, `|`, `^` and `+` of pieces whose
//! traced bits do not overlap (so no carry and no cancellation can occur), shifts and rotations
//! by constants, zero and sign extension, `extract`, `concat` and `bswap`. When every bit is
//! traced, the node is re-emitted as the source itself, a rotation, a byte swap, one source in
//! place with constant bits (`(s & ~zeros) | ones`), or a `concat` of slices and constant runs,
//! and replaced when that is smaller. Limb recompositions, shifted-and-masked byte shuffles and
//! identity round trips collapse this way.

use super::{Fin, PassKind, Runner, Step, Stop, finish};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::ops::{BinOp, UnOp};

/// The widest value traced.
pub(crate) const MAX_WIDTH: u16 = 128;

/// The most distinct sources and runs in one emission.
const MAX_PIECES: usize = 16;

/// Where one bit comes from.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Prov {
    Zero,
    One,
    /// Bit `j` of source node `s`.
    Bit(u32, u16),
}

/// A node's bits, low first; `None` when some bit cannot be traced (then the node is a source
/// for its users).
pub(crate) type Bits = Option<Vec<Prov>>;

fn traced_op(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Add
            | OpCode::Shl
            | OpCode::LShr
            | OpCode::AShr
            | OpCode::RotL
            | OpCode::RotR
            | OpCode::Zext
            | OpCode::Sext
            | OpCode::Extract
            | OpCode::Concat
            | OpCode::Bswap
            | OpCode::Const
    )
}

fn source(i: u32, w: u16) -> Vec<Prov> {
    (0..w).map(|j| Prov::Bit(i, j)).collect()
}

fn const_bits(v: &BitVec) -> Vec<Prov> {
    let one = BitVec::one(v.width());
    (0..v.width().bits())
        .map(|j| {
            let b = BitVec::bin_unchecked(
                BinOp::LShr,
                v,
                &BitVec::wrapping_from_u64(v.width(), u64::from(j)),
            );
            if crate::facts::known::bv_and(&b, &one).is_zero() {
                Prov::Zero
            } else {
                Prov::One
            }
        })
        .collect()
}

/// Combines two traced values bit by bit where at most one side is non-zero at each bit.
fn disjoint(a: &[Prov], b: &[Prov]) -> Option<Vec<Prov>> {
    a.iter()
        .zip(b)
        .map(|(x, y)| match (x, y) {
            (Prov::Zero, v) | (v, Prov::Zero) => Some(*v),
            _ => None,
        })
        .collect()
}

fn small_const(cx: &Context, i: u32) -> Option<u64> {
    cx.const_val(i).and_then(|v| v.to_u64())
}

/// The bits of `i` from its operands' (already traced) bits.
fn trace(cx: &Context, bits: &crate::hash::IdMap<u32, Bits>, i: u32) -> Bits {
    let n = cx.node(i);
    let w = n.width;
    let get = |j: u32| -> Vec<Prov> {
        match bits.get(&j) {
            Some(Some(b)) => b.clone(),
            _ => source(j, cx.node(j).width),
        }
    };
    Some(match n.op {
        OpCode::Const => const_bits(&cx.const_val(i)?),
        OpCode::And => {
            let (a, b) = (get(n.a), get(n.b));
            let (x, m) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                (Some(_), None) => (b, a),
                (None, Some(_)) => (a, b),
                _ => return None,
            };
            x.iter()
                .zip(&m)
                .map(|(p, k)| if *k == Prov::One { *p } else { Prov::Zero })
                .collect()
        }
        OpCode::Or | OpCode::Xor | OpCode::Add => {
            let (a, b) = (get(n.a), get(n.b));
            if n.op == OpCode::Or {
                // `1 | p` is 1: an or with a constant one bit is traced too.
                a.iter()
                    .zip(&b)
                    .map(|(x, y)| match (x, y) {
                        (Prov::One, _) | (_, Prov::One) => Some(Prov::One),
                        (Prov::Zero, v) | (v, Prov::Zero) => Some(*v),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?
            } else {
                disjoint(&a, &b)?
            }
        }
        OpCode::Shl | OpCode::LShr | OpCode::AShr => {
            let k = small_const(cx, n.b)?.min(u64::from(w)) as usize;
            let a = get(n.a);
            let w = w as usize;
            (0..w)
                .map(|i| match n.op {
                    OpCode::Shl => {
                        if i >= k {
                            a[i - k]
                        } else {
                            Prov::Zero
                        }
                    }
                    OpCode::LShr => {
                        if i + k < w {
                            a[i + k]
                        } else {
                            Prov::Zero
                        }
                    }
                    _ => a[(i + k).min(w - 1)],
                })
                .collect()
        }
        OpCode::RotL | OpCode::RotR => {
            // (The builder turns constant rotations into `rotl` by a count below the width;
            // both directions and any count are handled here anyway.)
            // The count modulo the width, exactly at every width.
            let c = cx.const_val(n.b)?;
            let wv = BitVec::wrapping_from_u64(c.width(), u64::from(w));
            let k = BitVec::bin_unchecked(BinOp::URem, &c, &wv)
                .to_u64()
                .unwrap_or(0) as usize;
            let a = get(n.a);
            let w = w as usize;
            (0..w)
                .map(|i| {
                    if n.op == OpCode::RotL {
                        a[(i + w - k) % w]
                    } else {
                        a[(i + k) % w]
                    }
                })
                .collect()
        }
        OpCode::Zext | OpCode::Sext => {
            let a = get(n.a);
            let top = if n.op == OpCode::Zext {
                Prov::Zero
            } else {
                *a.last()?
            };
            let mut v = a;
            v.resize(w as usize, top);
            v
        }
        OpCode::Extract => {
            let a = get(n.a);
            let lo = n.b as usize;
            a.get(lo..lo + w as usize)?.to_vec()
        }
        OpCode::Concat => {
            let mut v = get(n.b);
            v.extend(get(n.a));
            v
        }
        OpCode::Bswap => {
            let a = get(n.a);
            let bytes = (w / 8) as usize;
            (0..w as usize)
                .map(|i| a[(bytes - 1 - i / 8) * 8 + i % 8])
                .collect()
        }
        _ => return None,
    })
}

fn bits_of(r: &mut Runner<'_, '_>, cx: &Context, root: u32) -> Result<Bits, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.shuffle.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        if node.width > MAX_WIDTH || !traced_op(node.op) {
            r.shuffle.insert(i, None);
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if !r.shuffle.contains_key(&c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, u64::from(node.width))?;
        let b = trace(cx, &r.shuffle, i);
        r.shuffle.insert(i, b);
    }
    Ok(r.shuffle[&root].clone())
}

/// Maximal runs, low bits first: a constant run, or a slice of a source with consecutive bits.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Run {
    Const(bool, u16),
    Slice(u32, u16, u16),
}

fn runs(bits: &[Prov]) -> Vec<Run> {
    let mut out: Vec<Run> = Vec::new();
    for p in bits {
        match (out.last_mut(), p) {
            (Some(Run::Const(v, len)), Prov::Zero) if !*v => *len += 1,
            (Some(Run::Const(v, len)), Prov::One) if *v => *len += 1,
            (Some(Run::Slice(s, lo, len)), Prov::Bit(s2, j)) if s == s2 && *lo + *len == *j => {
                *len += 1
            }
            (_, Prov::Zero) => out.push(Run::Const(false, 1)),
            (_, Prov::One) => out.push(Run::Const(true, 1)),
            (_, Prov::Bit(s, j)) => out.push(Run::Slice(*s, *j, 1)),
        }
    }
    out
}

fn emit(r: &mut Runner<'_, '_>, cx: &mut Context, bits: &[Prov]) -> Result<Option<u32>, Stop> {
    let w = bits.len() as u16;
    let width = crate::Width::new(w).map_err(|e| Stop::Error(e.into()))?;
    let rs = runs(bits);
    if rs.len() > MAX_PIECES {
        return Ok(None);
    }
    // A whole source, possibly rotated or byte-swapped.
    if let Some(Prov::Bit(s, _)) = bits.first()
        && cx.node(*s).width == w
        && bits.iter().all(|p| matches!(p, Prov::Bit(t, _) if t == s))
    {
        let s = *s;
        let j = |i: usize| match bits[i] {
            Prov::Bit(_, j) => j as usize,
            _ => 0,
        };
        let wu = w as usize;
        let k = (wu - j(0)) % wu;
        if (0..wu).all(|i| j(i) == (i + wu - k) % wu) {
            if k == 0 {
                return Ok(Some(s));
            }
            let kv = BitVec::wrapping_from_u64(width, k as u64);
            return r
                .build(cx, |cx| {
                    let kc = cx.mk_const(&kv)?;
                    cx.c_bin(BinOp::RotL, s, kc)
                })
                .map(Some);
        }
        if w.is_multiple_of(8) && (0..wu).all(|i| j(i) == (wu / 8 - 1 - i / 8) * 8 + i % 8) {
            return r.build(cx, |cx| cx.c_un(UnOp::Bswap, s)).map(Some);
        }
    }
    // One source in place with some bits constant: `(s & ~zeros) | ones`, smaller than any
    // concat of its runs.
    if let Some(Prov::Bit(s, _)) = bits.iter().find(|p| matches!(p, Prov::Bit(..)))
        && cx.node(*s).width == w
        && bits
            .iter()
            .enumerate()
            .all(|(i, p)| !matches!(p, Prov::Bit(t, j) if t != s || usize::from(*j) != i))
    {
        let s = *s;
        let mask = |v: Prov| {
            bits.iter().enumerate().filter(|&(_, p)| *p == v).fold(
                BitVec::zero(width),
                |m, (i, _)| {
                    let bit = crate::facts::known::bv_shl(&BitVec::one(width), i as u32);
                    crate::facts::known::bv_or(&m, &bit)
                },
            )
        };
        let (zeros, ones) = (mask(Prov::Zero), mask(Prov::One));
        r.meter.charge(Counter::PassWork, u64::from(w))?;
        return r
            .build(cx, |cx| {
                let mut x = s;
                if !zeros.is_zero() {
                    let c = cx.mk_const(&crate::facts::known::bv_not(&zeros))?;
                    x = cx.c_bin(BinOp::And, x, c)?;
                }
                if !ones.is_zero() {
                    let c = cx.mk_const(&ones)?;
                    x = cx.c_bin(BinOp::Or, x, c)?;
                }
                Ok(x)
            })
            .map(Some);
    }
    // A concat of the runs, high first.
    let mut acc: Option<u32> = None;
    for run in rs.iter().rev() {
        r.meter.charge(Counter::PassWork, 1)?;
        let piece = match *run {
            Run::Const(v, len) => {
                let lw = crate::Width::new(len).map_err(|e| Stop::Error(e.into()))?;
                let c = if v {
                    BitVec::ones(lw)
                } else {
                    BitVec::zero(lw)
                };
                r.build(cx, |cx| cx.mk_const(&c))?
            }
            Run::Slice(s, lo, len) => r.build(cx, |cx| cx.c_extract(s, lo, len))?,
        };
        acc = Some(match acc {
            None => piece,
            Some(h) => r.build(cx, |cx| cx.c_concat(h, piece))?,
        });
    }
    r.meter.check()?;
    Ok(acc)
}

/// The shuffle pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    if node.width > MAX_WIDTH || !traced_op(node.op) || node.op == OpCode::Const {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let Some(bits) = bits_of(r, cx, n)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    let mut atoms: Vec<u32> = bits
        .iter()
        .filter_map(|p| match p {
            Prov::Bit(s, _) => Some(*s),
            _ => None,
        })
        .collect();
    atoms.sort_unstable();
    atoms.dedup();
    if atoms.len() > MAX_PIECES || atoms == [n] {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let before = cx.len() as u32;
    let Some(e) = emit(r, cx, &bits)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    finish(r, cx, PassKind::Shuffle, n, e, before, &atoms, Fin::FINAL)
}
