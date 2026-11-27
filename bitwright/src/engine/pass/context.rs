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

use crate::expr::{Context, OpCode};
use crate::facts::known::{bv_and, bv_lshr, bv_not, bv_or, bv_shl, bv_xor, count_ones, low_mask};
use crate::hash::IdMap;
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::{BitVec, Error, Width};

/// Bits of a node a condition fixes across widths `1..=512`: node `x` has bits `mask` equal to
/// `value`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Fact {
    x: u32,
    mask: BitVec,
    value: BitVec,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RelOp {
    Equal,
    Xor(BitVec),
    Add(BitVec),
    SubFrom(BitVec),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RelFact {
    /// Full-width functional relation `hi == f(lo)` (`lo` is the preferred representative).
    Full { hi: u32, lo: u32, op: RelOp },
    /// Partial-mask congruence `(hi ^ lo) & mask == xor_diff` (`0 < mask < ones`).
    /// Never substitutes unmasked `hi`; only rewrites consumers whose demanded bits on `hi`
    /// lie inside `mask`.
    Slice {
        hi: u32,
        lo: u32,
        mask: BitVec,
        xor_diff: BitVec,
    },
}

#[derive(Clone, Debug, Default)]
struct GuardFacts {
    bits: Vec<Fact>,
    rels: Vec<RelFact>,
    conflict: bool,
}

impl GuardFacts {
    fn is_empty(&self) -> bool {
        !self.conflict && self.bits.is_empty() && self.rels.is_empty()
    }

    fn extend_from(&mut self, other: &GuardFacts) {
        self.conflict |= other.conflict;
        self.bits.extend_from_slice(&other.bits);
        self.rels.extend_from_slice(&other.rels);
    }
}

/// Outcome of inspecting `lhs == rhs` for a two-source bit-slice or full-width congruence.
pub(crate) enum SliceCheck {
    None,
    Conflict,
    FullEq(u32, u32),
    Slice {
        hi: u32,
        lo: u32,
        mask: BitVec,
        xor_diff: BitVec,
    },
}

fn orient_pair(cx: &Context, a: u32, b: u32) -> (u32, u32) {
    let key = |id: u32| (cx.node(id).op != OpCode::Sym, cx.meta[id as usize].tree);
    match key(a).cmp(&key(b)).then_with(|| cx.order(a, b)) {
        core::cmp::Ordering::Greater => (b, a),
        _ => (a, b),
    }
}

fn set_range_limbs(limbs: &mut [u64; 8], off: u16, len: u16) {
    if len == 0 {
        return;
    }
    let start = usize::from(off);
    let end = start + usize::from(len);
    let mut pos = start;
    while pos < end {
        let word = pos / 64;
        let bit = pos % 64;
        let chunk = (end - pos).min(64 - bit);
        let m = if chunk == 64 {
            u64::MAX
        } else {
            ((1u64 << chunk) - 1) << bit
        };
        limbs[word] |= m;
        pos += chunk;
    }
}

/// Extracts a 2-variable bit-slice congruence `(hi ^ lo) & mask == xor_diff` (or full-width
/// equality / conflict) from `lhs == rhs` via canonical bit-provenance runs (`1..=512` bits).
pub(crate) fn extract_slice_congruence(cx: &Context, lhs: u32, rhs: u32) -> SliceCheck {
    use super::shuffle::BitRun;
    if lhs == rhs {
        return SliceCheck::None;
    }
    let (Some(rl), Some(rr)) = (
        super::shuffle::bit_runs_of(cx, lhs, 16),
        super::shuffle::bit_runs_of(cx, rhs, 16),
    ) else {
        return SliceCheck::None;
    };
    let run_len = |r: BitRun| match r {
        BitRun::Const { len, .. } | BitRun::Slice { len, .. } => len,
    };
    let split = |r: BitRun, take: u16| -> (BitRun, BitRun) {
        match r {
            BitRun::Const { val, len } => (
                BitRun::Const { val, len: take },
                BitRun::Const {
                    val,
                    len: len - take,
                },
            ),
            BitRun::Slice { src, lo, len, inv } => (
                BitRun::Slice {
                    src,
                    lo,
                    len: take,
                    inv,
                },
                BitRun::Slice {
                    src,
                    lo: lo + take,
                    len: len - take,
                    inv,
                },
            ),
        }
    };

    let (mut il, mut ir) = (0usize, 0usize);
    let (Some(mut cl), Some(mut cr)) = (rl.first().copied(), rr.first().copied()) else {
        return SliceCheck::None;
    };
    let mut pair: Option<(u32, u32)> = None;
    let mut mask_limbs = [0u64; 8];
    let mut xor_limbs = [0u64; 8];
    let mut any_slice = false;

    loop {
        let step = run_len(cl).min(run_len(cr));
        let (hl, next_cl) = split(cl, step);
        let (hr, next_cr) = split(cr, step);
        match (hl, hr) {
            (BitRun::Const { val: vl, .. }, BitRun::Const { val: vr, .. }) => {
                if vl != vr {
                    return SliceCheck::Conflict;
                }
            }
            (
                BitRun::Slice {
                    src: sx,
                    lo: lx,
                    inv: ix,
                    ..
                },
                BitRun::Slice {
                    src: sy,
                    lo: ly,
                    inv: iy,
                    ..
                },
            ) => {
                if sx == sy && lx == ly {
                    if ix != iy {
                        return SliceCheck::Conflict;
                    }
                } else if lx == ly && cx.wid(sx) == cx.wid(sy) {
                    match pair {
                        None => pair = Some((sx, sy)),
                        Some((px, py)) if px == sx && py == sy => {}
                        _ => return SliceCheck::None,
                    }
                    set_range_limbs(&mut mask_limbs, lx, step);
                    if ix ^ iy {
                        set_range_limbs(&mut xor_limbs, lx, step);
                    }
                    any_slice = true;
                } else {
                    return SliceCheck::None;
                }
            }
            _ => return SliceCheck::None,
        }
        cl = if run_len(next_cl) == 0 {
            il += 1;
            if il == rl.len() {
                ir += usize::from(run_len(next_cr) == 0);
                if ir != rr.len() {
                    return SliceCheck::None;
                }
                break;
            }
            rl[il]
        } else {
            next_cl
        };
        cr = if run_len(next_cr) == 0 {
            ir += 1;
            if ir == rr.len() {
                return SliceCheck::None;
            }
            rr[ir]
        } else {
            next_cr
        };
    }

    if !any_slice {
        return SliceCheck::None;
    }
    let Some((sx, sy)) = pair else {
        return SliceCheck::None;
    };
    let w = cx.width_of(sx);
    let mask = BitVec::wrapping_from_limbs(w, &mask_limbs);
    let xor_diff = BitVec::wrapping_from_limbs(w, &xor_limbs);
    let (lo, hi) = orient_pair(cx, sx, sy);
    if mask.is_ones() && xor_diff.is_zero() {
        return SliceCheck::FullEq(lo, hi);
    }
    SliceCheck::Slice {
        hi,
        lo,
        mask,
        xor_diff,
    }
}

/// Unwrap simple full-width affine/complement wrappers around a single variable:
/// `x == base * (±1) + offset` (`negated = true` means `offset - base`).
fn peel_affine_side(cx: &Context, mut id: u32) -> (u32, bool, BitVec) {
    let w = cx.width_of(id);
    let mut neg = false;
    let mut off = BitVec::zero(w);
    for _ in 0..6 {
        if cx.is_const(id) {
            break;
        }
        let n = cx.node(id);
        match n.op {
            OpCode::Add => match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => {
                    off = if neg {
                        BitVec::bin_unchecked(BinOp::Sub, &off, &k)
                    } else {
                        BitVec::bin_unchecked(BinOp::Add, &off, &k)
                    };
                    id = n.a;
                }
                (Some(k), None) => {
                    off = if neg {
                        BitVec::bin_unchecked(BinOp::Sub, &off, &k)
                    } else {
                        BitVec::bin_unchecked(BinOp::Add, &off, &k)
                    };
                    id = n.b;
                }
                _ => break,
            },
            OpCode::Sub => match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => {
                    off = if neg {
                        BitVec::bin_unchecked(BinOp::Add, &off, &k)
                    } else {
                        BitVec::bin_unchecked(BinOp::Sub, &off, &k)
                    };
                    id = n.a;
                }
                (Some(k), None) => {
                    off = if neg {
                        BitVec::bin_unchecked(BinOp::Sub, &off, &k)
                    } else {
                        BitVec::bin_unchecked(BinOp::Add, &off, &k)
                    };
                    neg = !neg;
                    id = n.b;
                }
                _ => break,
            },
            OpCode::Neg => {
                neg = !neg;
                id = n.a;
            }
            OpCode::Not => {
                // `~u == -1 - u`
                let minus_one = BitVec::ones(w);
                off = if neg {
                    BitVec::bin_unchecked(BinOp::Sub, &off, &minus_one)
                } else {
                    BitVec::bin_unchecked(BinOp::Add, &off, &minus_one)
                };
                neg = !neg;
                id = n.a;
            }
            _ => break,
        }
    }
    (id, neg, off)
}

/// The most conditions [`push`] reads facts from in one root.
const MAX_SITES: usize = 512;

/// What 1-bit node `c` being `want` fixes across widths `1..=512`, added to `out`.
fn fixes(cx: &Context, c: u32, want: bool, out: &mut GuardFacts, depth: u32) {
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
        OpCode::Eq | OpCode::Ne => {
            out.bits.push(Fact {
                x: c,
                mask: BitVec::one(Width::W1),
                value: BitVec::from_bool(want),
            });
            if (n.op == OpCode::Eq) != want {
                return;
            }
            match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => {
                    let w = cx.width_of(n.a);
                    masked(cx, n.a, BitVec::ones(w), k, out, depth + 1);
                }
                (Some(k), None) => {
                    let w = cx.width_of(n.b);
                    masked(cx, n.b, BitVec::ones(w), k, out, depth + 1);
                }
                (None, None) => {
                    extract_relational_eq(cx, n.a, n.b, out);
                }
                (Some(ka), Some(kb)) => {
                    if ka != kb {
                        out.conflict = true;
                    }
                }
            }
        }
        _ => out.bits.push(Fact {
            x: c,
            mask: BitVec::one(Width::W1),
            value: BitVec::from_bool(want),
        }),
    }
}

fn extract_relational_eq(cx: &Context, lhs: u32, rhs: u32, out: &mut GuardFacts) {
    if lhs == rhs {
        return;
    }
    let mut eq_pair = (lhs, rhs);
    // 1. Check bit-slice / masked / XOR congruence (also peels `bswap(a) == bswap(b)`,
    //    `rotl(a, k) == rotl(b, k)`, and `x ^ c1 == y ^ c2`).
    match extract_slice_congruence(cx, lhs, rhs) {
        SliceCheck::Conflict => {
            out.conflict = true;
            return;
        }
        SliceCheck::FullEq(lo, hi) => {
            out.rels.push(RelFact::Full {
                hi,
                lo,
                op: RelOp::Equal,
            });
            // Continue into affine peeling on `(lo, hi)` so `y + 5 == x` (and even
            // `bswap(y + 5) == bswap(x)`) also extracts `y = x - 5`.
            eq_pair = (lo, hi);
        }
        SliceCheck::Slice {
            hi,
            lo,
            mask,
            xor_diff,
        } => {
            if mask.is_ones() {
                out.rels.push(RelFact::Full {
                    hi,
                    lo,
                    op: if xor_diff.is_zero() {
                        RelOp::Equal
                    } else {
                        RelOp::Xor(xor_diff)
                    },
                });
                if xor_diff.is_zero() {
                    eq_pair = (lo, hi);
                } else {
                    return;
                }
            } else {
                out.rels.push(RelFact::Slice {
                    hi,
                    lo,
                    mask,
                    xor_diff,
                });
                return;
            }
        }
        SliceCheck::None => {}
    }

    // 2. Check full-width affine relation (`x + k1 == y + k2`, `x - y == k`, `x + y == k`).
    let (bx, nx, ox) = peel_affine_side(cx, eq_pair.0);
    let (by, ny, oy) = peel_affine_side(cx, eq_pair.1);
    if (bx, by) == eq_pair && !nx && !ny && ox.is_zero() && oy.is_zero() {
        return;
    }
    if cx.is_const(bx) || cx.is_const(by) {
        // E.g. `(x - y) == 0` peeled? No, `lhs` and `rhs` had no top-level const, unless `(x + k) == k2`.
        return;
    }
    if bx == by {
        if nx == ny && ox != oy {
            out.conflict = true;
        }
        return;
    }
    let (lo, hi) = orient_pair(cx, bx, by);
    let (n_lo, o_lo, n_hi, o_hi) = if lo == bx {
        (nx, ox, ny, oy)
    } else {
        (ny, oy, nx, ox)
    };
    // Solve `(-1)^{n_hi} * hi + o_hi == (-1)^{n_lo} * lo + o_lo` for `hi`:
    if n_hi == n_lo {
        // If `n_hi == false`: `hi = lo + (o_lo - o_hi)`.
        // If `n_hi == true`: `-hi + o_hi = -lo + o_lo => hi = lo + (o_hi - o_lo)`.
        let delta = if !n_hi {
            BitVec::bin_unchecked(BinOp::Sub, &o_lo, &o_hi)
        } else {
            BitVec::bin_unchecked(BinOp::Sub, &o_hi, &o_lo)
        };
        out.rels.push(RelFact::Full {
            hi,
            lo,
            op: if delta.is_zero() {
                RelOp::Equal
            } else {
                RelOp::Add(delta)
            },
        });
    } else {
        // Opposite signs:
        // If `n_hi == false, n_lo == true`: `hi + o_hi = -lo + o_lo => hi = (o_lo - o_hi) - lo`.
        // If `n_hi == true, n_lo == false`: `-hi + o_hi = lo + o_lo => hi = (o_hi - o_lo) - lo`.
        let sum_k = if !n_hi {
            BitVec::bin_unchecked(BinOp::Sub, &o_lo, &o_hi)
        } else {
            BitVec::bin_unchecked(BinOp::Sub, &o_hi, &o_lo)
        };
        out.rels.push(RelFact::Full {
            hi,
            lo,
            op: RelOp::SubFrom(sum_k),
        });
    }

    // Also record direct equality of the raw comparison operands `(lhs, rhs)` when distinct from `(bx, by)`.
    if (lhs, rhs) != (bx, by) && (rhs, lhs) != (bx, by) {
        let (r_lo, r_hi) = orient_pair(cx, lhs, rhs);
        out.rels.push(RelFact::Full {
            hi: r_hi,
            lo: r_lo,
            op: RelOp::Equal,
        });
    }
}

/// `x & mask == value`, read through shifts, extractions, extensions, complements, XORs, and
/// full-width constant offsets across widths `1..=512`.
fn masked(cx: &Context, x: u32, mask: BitVec, value: BitVec, out: &mut GuardFacts, depth: u32) {
    if mask.is_zero() || cx.is_const(x) {
        if let Some(cv) = cx.const_val(x)
            && bv_and(&cv, &mask) != bv_and(&value, &mask)
        {
            out.conflict = true;
        }
        return;
    }
    if !bv_and(&value, &bv_not(&mask)).is_zero() {
        out.conflict = true;
        return;
    }
    let n = cx.node(x);
    if depth < 16 {
        match n.op {
            OpCode::LShr | OpCode::Extract => {
                let by = match n.op {
                    OpCode::Extract => Some(n.b),
                    _ => cx
                        .const_val(n.b)
                        .and_then(|k| k.to_u64())
                        .and_then(|k| u32::try_from(k).ok()),
                };
                if let Some(by) = by {
                    let src_w = cx.width_of(n.a);
                    if by < u32::from(src_w.bits()) {
                        let m_wide = resize_bv(&mask, src_w);
                        let v_wide = resize_bv(&value, src_w);
                        let m_up = bv_shl(&m_wide, by);
                        if resize_bv(&bv_lshr(&m_up, by), mask.width()) == mask {
                            return masked(cx, n.a, m_up, bv_shl(&v_wide, by), out, depth + 1);
                        }
                    }
                }
            }
            OpCode::Shl => {
                if let Some(by) = cx
                    .const_val(n.b)
                    .and_then(|k| k.to_u64())
                    .and_then(|k| u32::try_from(k).ok())
                    && by < u32::from(mask.width().bits())
                {
                    let low_zeros = low_mask(mask.width(), by);
                    if !bv_and(&value, &bv_and(&mask, &low_zeros)).is_zero() {
                        out.conflict = true;
                        return;
                    }
                    let m_down = bv_lshr(&mask, by);
                    let v_down = bv_lshr(&value, by);
                    return masked(cx, n.a, m_down, v_down, out, depth + 1);
                }
            }
            OpCode::Zext => {
                let iw = cx.width_of(n.a);
                let hi_bits = bv_not(&low_mask(mask.width(), u32::from(iw.bits())));
                if !bv_and(&value, &bv_and(&mask, &hi_bits)).is_zero() {
                    out.conflict = true;
                    return;
                }
                let m_in = resize_bv(&mask, iw);
                let v_in = resize_bv(&value, iw);
                return masked(cx, n.a, m_in, v_in, out, depth + 1);
            }
            OpCode::And => {
                let pair = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (None, Some(k)) => Some((n.a, k)),
                    (Some(k), None) => Some((n.b, k)),
                    _ => None,
                };
                if let Some((y, k)) = pair {
                    if !bv_and(&value, &bv_and(&mask, &bv_not(&k))).is_zero() {
                        out.conflict = true;
                        return;
                    }
                    return masked(cx, y, bv_and(&mask, &k), bv_and(&value, &k), out, depth + 1);
                }
            }
            OpCode::Or => {
                let pair = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (None, Some(k)) => Some((n.a, k)),
                    (Some(k), None) => Some((n.b, k)),
                    _ => None,
                };
                if let Some((y, k)) = pair {
                    // Where `k` is 1, `(y | k)` is 1, so `value` on `mask & k` must be `mask & k`.
                    let must_one = bv_and(&mask, &k);
                    if bv_and(&value, &must_one) != must_one {
                        out.conflict = true;
                        return;
                    }
                    let rem_m = bv_and(&mask, &bv_not(&k));
                    return masked(cx, y, rem_m, bv_and(&value, &rem_m), out, depth + 1);
                }
            }
            OpCode::Not => {
                return masked(
                    cx,
                    n.a,
                    mask,
                    bv_and(&bv_not(&value), &mask),
                    out,
                    depth + 1,
                );
            }
            OpCode::Xor => {
                let pair = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (None, Some(k)) => Some((n.a, k)),
                    (Some(k), None) => Some((n.b, k)),
                    _ => None,
                };
                if let Some((y, k)) = pair {
                    return masked(
                        cx,
                        y,
                        mask,
                        bv_and(&bv_xor(&value, &k), &mask),
                        out,
                        depth + 1,
                    );
                }
            }
            OpCode::Add if mask.is_ones() => match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => {
                    return masked(
                        cx,
                        n.a,
                        mask,
                        BitVec::bin_unchecked(BinOp::Sub, &value, &k),
                        out,
                        depth + 1,
                    );
                }
                (Some(k), None) => {
                    return masked(
                        cx,
                        n.b,
                        mask,
                        BitVec::bin_unchecked(BinOp::Sub, &value, &k),
                        out,
                        depth + 1,
                    );
                }
                // `(a - b) + k == value` when `value == k` means `a == b`!
                _ => {}
            },
            OpCode::Sub if mask.is_ones() => match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => {
                    return masked(
                        cx,
                        n.a,
                        mask,
                        BitVec::bin_unchecked(BinOp::Add, &value, &k),
                        out,
                        depth + 1,
                    );
                }
                (Some(k), None) => {
                    return masked(
                        cx,
                        n.b,
                        mask,
                        BitVec::bin_unchecked(BinOp::Sub, &k, &value),
                        out,
                        depth + 1,
                    );
                }
                (None, None) if value.is_zero() => {
                    extract_relational_eq(cx, n.a, n.b, out);
                    return;
                }
                _ => {}
            },
            _ => {}
        }
        if mask.is_ones() && n.op == OpCode::Xor && value.is_zero() {
            extract_relational_eq(cx, n.a, n.b, out);
            return;
        }
    }
    out.bits.push(Fact { x, mask, value });
}

fn resize_bv(v: &BitVec, w: Width) -> BitVec {
    match v.width().bits().cmp(&w.bits()) {
        core::cmp::Ordering::Equal => *v,
        core::cmp::Ordering::Less => v.zext(w).unwrap_or_else(|_| BitVec::zero(w)),
        core::cmp::Ordering::Greater => v.trunc(w).unwrap_or_else(|_| BitVec::zero(w)),
    }
}

/// Collapses multi-node affine (`Add`/`Sub`/`Neg`/`Not`) and `Xor` cancellations introduced by
/// relational substitution (e.g. `(x + -5) + 5 -> x`, `x - (x + -5) -> 5`, `(x ^ c1) ^ x -> c1`,
/// `(y + 7) - y != 7 -> false`) in O(1) without waiting for a later linear/xor pass.
fn simplify_rebuilt(cx: &mut Context, id: u32) -> Result<u32, Error> {
    if cx.is_const(id) {
        return Ok(id);
    }
    let nd = cx.node(id);
    match nd.op {
        OpCode::Add | OpCode::Sub => {
            let (bx, nx, ox) = peel_affine_side(cx, nd.a);
            let (by, ny, oy) = peel_affine_side(cx, nd.b);
            let cancels = if nd.op == OpCode::Sub {
                bx == by && nx == ny
            } else {
                bx == by && nx != ny
            };
            if cancels {
                let val = if nd.op == OpCode::Sub {
                    BitVec::bin_unchecked(BinOp::Sub, &ox, &oy)
                } else {
                    BitVec::bin_unchecked(BinOp::Add, &ox, &oy)
                };
                return cx.mk_const(&val);
            }
            let (b, neg, off) = peel_affine_side(cx, id);
            if b != id && !cx.is_const(b) {
                let cand = if !neg {
                    if off.is_zero() {
                        b
                    } else {
                        let kc = cx.mk_const(&off)?;
                        cx.c_bin(BinOp::Add, b, kc)?
                    }
                } else if off.is_zero() {
                    cx.c_un(UnOp::Neg, b)?
                } else {
                    let kc = cx.mk_const(&off)?;
                    cx.c_bin(BinOp::Sub, kc, b)?
                };
                if cx.meta[cand as usize].tree < cx.meta[id as usize].tree {
                    return Ok(cand);
                }
            }
        }
        OpCode::Xor => {
            let peel_xor = |cx: &Context, mut x: u32| -> (u32, BitVec) {
                let w = cx.width_of(x);
                let mut mask = BitVec::zero(w);
                for _ in 0..4 {
                    if cx.is_const(x) {
                        break;
                    }
                    let n = cx.node(x);
                    match n.op {
                        OpCode::Not => {
                            mask = bv_not(&mask);
                            x = n.a;
                        }
                        OpCode::Xor => match (cx.const_val(n.a), cx.const_val(n.b)) {
                            (None, Some(k)) => {
                                mask = bv_xor(&mask, &k);
                                x = n.a;
                            }
                            (Some(k), None) => {
                                mask = bv_xor(&mask, &k);
                                x = n.b;
                            }
                            _ => break,
                        },
                        _ => break,
                    }
                }
                (x, mask)
            };
            let (bx, mx) = peel_xor(cx, nd.a);
            let (by, my) = peel_xor(cx, nd.b);
            if bx == by {
                return cx.mk_const(&bv_xor(&mx, &my));
            }
            let (b, m) = peel_xor(cx, id);
            if b != id && !cx.is_const(b) {
                let cand = if m.is_zero() {
                    b
                } else if m.is_ones() {
                    cx.c_un(UnOp::Not, b)?
                } else {
                    let kc = cx.mk_const(&m)?;
                    cx.c_bin(BinOp::Xor, b, kc)?
                };
                if cx.meta[cand as usize].tree < cx.meta[id as usize].tree {
                    return Ok(cand);
                }
            }
        }
        OpCode::Eq | OpCode::Ne => {
            let (bx, nx, ox) = peel_affine_side(cx, nd.a);
            let (by, ny, oy) = peel_affine_side(cx, nd.b);
            if bx == by && nx == ny {
                let eq = ox == oy;
                let res = if nd.op == OpCode::Eq { eq } else { !eq };
                return cx.mk_const_u64(1, u64::from(res));
            }
        }
        _ => {}
    }
    Ok(id)
}

/// Merge bit-facts and detect contradictions (`true` when contradictory).
fn merge_bit_facts(facts: &[Fact]) -> Result<Vec<Fact>, ()> {
    let mut merged: Vec<Fact> = Vec::new();
    for f in facts {
        match merged.iter_mut().find(|m| m.x == f.x) {
            Some(m) => {
                let shared = bv_and(&m.mask, &f.mask);
                if !bv_and(&bv_xor(&m.value, &f.value), &shared).is_zero() {
                    return Err(());
                }
                m.value = bv_or(&m.value, &f.value);
                m.mask = bv_or(&m.mask, &f.mask);
            }
            None => merged.push(f.clone()),
        }
    }
    Ok(merged)
}

/// `e` with each node `gf` fixes bits or relations of specialized soundly.
fn put(cx: &mut Context, e: u32, gf: &GuardFacts) -> Result<u32, Error> {
    if gf.conflict || gf.is_empty() {
        return Ok(e);
    }
    let Ok(mut merged) = merge_bit_facts(&gf.bits) else {
        // Contradictory guard: unreachable branch, leave `e` unchanged.
        return Ok(e);
    };
    let mut more = Vec::new();
    for f in &merged {
        let n = cx.node(f.x);
        if n.width == 1 && f.mask.is_ones() && matches!(n.op, OpCode::Eq | OpCode::Ne) {
            let other = if n.op == OpCode::Eq {
                CmpOp::Ne
            } else {
                CmpOp::Eq
            };
            let c = cx.c_cmp(other, n.a, n.b)?;
            if c != f.x && !merged.iter().any(|m| m.x == c) && cx.wid(c) == 1 && !cx.is_const(c) {
                more.push(Fact {
                    x: c,
                    mask: BitVec::one(Width::W1),
                    value: BitVec::from_bool(f.value.is_zero()),
                });
            }
        }
    }
    merged.extend(more);

    let cone = cx.post_order_ids(&[e]);
    let in_cone: IdMap<u32, ()> = cone.iter().map(|&id| (id, ())).collect();

    let mut repl: IdMap<u32, u32> = IdMap::default();
    for f in merged {
        if !in_cone.contains_key(&f.x) {
            continue;
        }
        let v = cx.mk_const(&f.value)?;
        let r = if f.mask.is_ones() {
            v
        } else {
            let keep = cx.mk_const(&bv_not(&f.mask))?;
            let rest = cx.c_bin(BinOp::And, f.x, keep)?;
            cx.c_bin(BinOp::Or, rest, v)?
        };
        repl.insert(f.x, r);
    }

    let mut slice_rels: Vec<(u32, u32, BitVec, BitVec)> = Vec::new();
    for rel in &gf.rels {
        match rel {
            RelFact::Full { hi, lo, op } => {
                if !in_cone.contains_key(hi) || repl.contains_key(hi) {
                    continue;
                }
                let r = match op {
                    RelOp::Equal => *lo,
                    RelOp::Xor(c) if c.is_ones() => cx.c_un(UnOp::Not, *lo)?,
                    RelOp::Xor(c) => {
                        if !in_cone.contains_key(lo) {
                            continue;
                        }
                        let kc = cx.mk_const(c)?;
                        cx.c_bin(BinOp::Xor, *lo, kc)?
                    }
                    RelOp::Add(c) => {
                        if !in_cone.contains_key(lo) {
                            continue;
                        }
                        let kc = cx.mk_const(c)?;
                        cx.c_bin(BinOp::Add, *lo, kc)?
                    }
                    RelOp::SubFrom(c) => {
                        if !in_cone.contains_key(lo) {
                            continue;
                        }
                        let kc = cx.mk_const(c)?;
                        cx.c_bin(BinOp::Sub, kc, *lo)?
                    }
                };
                repl.insert(*hi, r);
            }
            RelFact::Slice {
                hi,
                lo,
                mask,
                xor_diff,
            } => {
                if in_cone.contains_key(hi) {
                    slice_rels.push((*hi, *lo, *mask, *xor_diff));
                }
            }
        }
    }

    if repl.is_empty() && slice_rels.is_empty() {
        return Ok(e);
    }

    // Bottom-up cone rebuild that applies full-node `repl`, local ring/xor simplification of
    // substituted terms, AND site-scoped `slice_rels` (only rewriting `hi` inside consumers `u`
    // whose demanded mask on `hi` lies inside `mask`, leaving any unmasked reads of `hi`
    // completely untouched!).
    let mut map: IdMap<u32, u32> = repl;
    for &u in &cone {
        if map.contains_key(&u) {
            continue;
        }
        let nd = cx.node(u);
        let arity = nd.op.arity();
        if arity == 0 {
            continue;
        }
        let mut kids = [nd.a, nd.b, nd.c];
        let mut changed = false;
        for k in kids.iter_mut().take(arity) {
            if let Some(&m) = map.get(k) {
                changed |= m != *k;
                *k = m;
            }
        }
        let u_rebuilt = if changed {
            let r = cx.rebuild(u, kids)?;
            simplify_rebuilt(cx, r)?
        } else {
            u
        };
        let mut final_u = u_rebuilt;
        if !slice_rels.is_empty()
            && let Some((operand, dem_mask)) = super::demanded::observed(cx, u_rebuilt)
        {
            for &(hi, lo, ref mask, ref xor_diff) in &slice_rels {
                if operand == hi && bv_and(&dem_mask, &bv_not(mask)).is_zero() {
                    let lo_cur = map.get(&lo).copied().unwrap_or(lo);
                    let sub_xor = bv_and(xor_diff, &dem_mask);
                    let repl_op = if sub_xor.is_zero() {
                        lo_cur
                    } else if sub_xor == dem_mask {
                        cx.c_un(UnOp::Not, lo_cur)?
                    } else {
                        let kc = cx.mk_const(&sub_xor)?;
                        cx.c_bin(BinOp::Xor, lo_cur, kc)?
                    };
                    let und = cx.node(u_rebuilt);
                    let mut ukids = [und.a, und.b, und.c];
                    for k in ukids.iter_mut().take(und.op.arity()) {
                        if *k == operand {
                            *k = repl_op;
                        }
                    }
                    let r2 = cx.rebuild(u_rebuilt, ukids)?;
                    final_u = simplify_rebuilt(cx, r2)?;
                    break;
                }
            }
        }
        if final_u != u {
            map.insert(u, final_u);
        }
    }
    Ok(map.get(&e).copied().unwrap_or(e))
}

/// Specialize `arm` assuming 1-bit condition `cond == want` (for `Select` arms in `compares`).
pub(super) fn specialize_arm(
    cx: &mut Context,
    arm: u32,
    cond: u32,
    want: bool,
) -> Result<u32, Error> {
    let mut gf = GuardFacts::default();
    fixes(cx, cond, want, &mut gf, 0);
    if gf.conflict || gf.is_empty() {
        return Ok(arm);
    }
    put(cx, arm, &gf)
}

/// Specialize a 1-bit `And` (`want = true`) or `Or` (`want = false`) binary node by propagating
/// each side's bit/relational facts into its sibling (and detecting contradictory conjuncts/tautologous disjuncts).
pub(super) fn specialize_bool_bin(cx: &mut Context, n: u32) -> Result<Option<u32>, Error> {
    let nd = cx.node(n);
    let want = match nd.op {
        OpCode::And if nd.width == 1 => true,
        OpCode::Or if nd.width == 1 => false,
        _ => return Ok(None),
    };
    let (mut fa, mut fb) = (GuardFacts::default(), GuardFacts::default());
    fixes(cx, nd.a, want, &mut fa, 0);
    fixes(cx, nd.b, want, &mut fb, 0);
    if fa.is_empty() && fb.is_empty() {
        return Ok(None);
    }
    if fa.conflict || fb.conflict {
        return cx.mk_const_u64(1, u64::from(!want)).map(Some);
    }
    let mut both = fa.clone();
    both.extend_from(&fb);
    if merge_bit_facts(&both.bits).is_err() {
        return cx.mk_const_u64(1, u64::from(!want)).map(Some);
    }
    let op = if want { BinOp::And } else { BinOp::Or };
    // Try propagating the smaller/simpler guard side into the heavier side first.
    let a_into_b = cx.meta[nd.a as usize].tree <= cx.meta[nd.b as usize].tree;
    let first = if a_into_b {
        let b2 = put(cx, nd.b, &fa)?;
        (b2 != nd.b).then_some((nd.a, b2))
    } else {
        let a2 = put(cx, nd.a, &fb)?;
        (a2 != nd.a).then_some((a2, nd.b))
    };
    let pair = match first {
        Some(p) => Some(p),
        None if a_into_b => {
            let a2 = put(cx, nd.a, &fb)?;
            (a2 != nd.a).then_some((a2, nd.b))
        }
        None => {
            let b2 = put(cx, nd.b, &fa)?;
            (b2 != nd.b).then_some((nd.a, b2))
        }
    };
    let Some((na, nb)) = pair else {
        return Ok(None);
    };
    let out = cx.c_bin(op, na, nb)?;
    Ok((out != n).then_some(out))
}

/// `root` with what each condition fixes put into the operands it guards (see the module),
/// or `None` when no condition fixes anything, or the root would grow past `max_new` nodes.
#[cfg_attr(not(feature = "mba"), allow(dead_code))]
pub(super) fn push(cx: &mut Context, root: u32, max_new: u32) -> Result<Option<u32>, Error> {
    const MAX_SPINE: usize = 128;
    let start = cx.len() as u32;
    let order = cx.post_order_ids(&[root]);
    let mut and_uses: IdMap<u32, u32> = IdMap::default();
    let mut and_child_of_and: IdMap<u32, ()> = IdMap::default();
    if cx.node(root).op == OpCode::And && cx.wid(root) == 1 {
        *and_uses.entry(root).or_default() += 1;
    }
    for &id in &order {
        let nd = cx.node(id);
        let parent_is_and1 = nd.op == OpCode::And && nd.width == 1;
        for c in nd.children() {
            if cx.node(c).op == OpCode::And && cx.wid(c) == 1 {
                *and_uses.entry(c).or_default() += 1;
                if parent_is_and1 {
                    and_child_of_and.insert(c, ());
                }
            }
        }
    }
    let is_interior_and1 = |id: u32| -> bool {
        and_uses.get(&id).copied() == Some(1) && and_child_of_and.contains_key(&id)
    };

    let mut pushed: IdMap<u32, u32> = IdMap::default();
    let mut sites = 0usize;
    for i in order {
        if cx.len() as u32 - start > max_new {
            return Ok(None);
        }
        if is_interior_and1(i) {
            continue;
        }
        let n = cx.node(i);
        let now = |cx: &mut Context, pushed: &IdMap<u32, u32>, e: u32| -> Result<u32, Error> {
            Ok(cx.substitute_ids(&[e], pushed)?[0])
        };
        let new = match n.op {
            OpCode::And if n.width == 1 => {
                // Flatten single-use 1-bit `And` spines so all sibling guards are merged once
                // and applied in a single substitution pass over heavy conjuncts instead of
                // re-substituting the sibling DAG at every binary `&` along the spine.
                let mut raw_leaves = Vec::new();
                let mut st = vec![n.b, n.a];
                while let Some(cur) = st.pop() {
                    if is_interior_and1(cur) && raw_leaves.len() + st.len() + 2 <= MAX_SPINE {
                        let cn = cx.node(cur);
                        st.push(cn.b);
                        st.push(cn.a);
                    } else {
                        raw_leaves.push(cur);
                    }
                }
                let mut leaves = Vec::with_capacity(raw_leaves.len());
                let mut folded_zero = false;
                for raw in raw_leaves {
                    let cur = now(cx, &pushed, raw)?;
                    if let Some(cv) = cx.const_val(cur) {
                        if cv.is_zero() {
                            folded_zero = true;
                            break;
                        }
                        continue;
                    }
                    if !leaves.contains(&cur) {
                        leaves.push(cur);
                    }
                }
                if folded_zero {
                    cx.mk_const_u64(1, 0)?
                } else if leaves.is_empty() {
                    cx.mk_const_u64(1, 1)?
                } else if leaves.len() == 1 {
                    leaves[0]
                } else {
                    let mut leaf_facts: Vec<GuardFacts> = Vec::with_capacity(leaves.len());
                    let mut any_facts = false;
                    let mut conflict = false;
                    for &l in &leaves {
                        let mut lf = GuardFacts::default();
                        fixes(cx, l, true, &mut lf, 0);
                        conflict |= lf.conflict;
                        any_facts |= !lf.is_empty();
                        leaf_facts.push(lf);
                    }
                    if conflict {
                        cx.mk_const_u64(1, 0)?
                    } else if !any_facts {
                        let mut iter = leaves.iter().copied();
                        let mut acc = iter.next().unwrap();
                        for l in iter {
                            acc = cx.c_bin(BinOp::And, acc, l)?;
                        }
                        if acc == i {
                            continue;
                        }
                        acc
                    } else {
                        let mut all_bits: Vec<Fact> = Vec::new();
                        for lf in &leaf_facts {
                            all_bits.extend_from_slice(&lf.bits);
                        }
                        if merge_bit_facts(&all_bits).is_err() {
                            cx.mk_const_u64(1, 0)?
                        } else {
                            let tier = |idx: usize| -> u8 {
                                let l = leaves[idx];
                                let lf = &leaf_facts[idx];
                                let fixes_sym = lf
                                    .bits
                                    .iter()
                                    .any(|f| f.x != l && cx.node(f.x).op == OpCode::Sym)
                                    || lf.rels.iter().any(|r| match r {
                                        RelFact::Full { hi, lo, .. }
                                        | RelFact::Slice { hi, lo, .. } => {
                                            cx.node(*hi).op == OpCode::Sym
                                                || cx.node(*lo).op == OpCode::Sym
                                        }
                                    });
                                if fixes_sym {
                                    0
                                } else if lf.bits.iter().any(|f| f.x != l) || !lf.rels.is_empty() {
                                    1
                                } else {
                                    2
                                }
                            };
                            let mut perm: Vec<usize> = (0..leaves.len()).collect();
                            perm.sort_by_key(|&idx| {
                                let l = leaves[idx] as usize;
                                (tier(idx), cx.meta[l].height, cx.meta[l].tree, idx)
                            });
                            let mut rewritten = leaves.clone();
                            let mut prefix_facts = GuardFacts::default();
                            let mut any_changed = false;
                            for &idx in &perm {
                                if cx.len() as u32 - start > max_new {
                                    return Ok(None);
                                }
                                if !prefix_facts.is_empty() {
                                    let l2 = put(cx, leaves[idx], &prefix_facts)?;
                                    if l2 != leaves[idx] {
                                        rewritten[idx] = l2;
                                        any_changed = true;
                                    }
                                }
                                prefix_facts.extend_from(&leaf_facts[idx]);
                            }
                            if !any_changed && perm.len() >= 2 {
                                let mut suffix_facts = GuardFacts::default();
                                for &idx in &perm[1..] {
                                    suffix_facts.extend_from(&leaf_facts[idx]);
                                }
                                let first = perm[0];
                                let l2 = put(cx, leaves[first], &suffix_facts)?;
                                if l2 != leaves[first] {
                                    rewritten[first] = l2;
                                    any_changed = true;
                                }
                            }
                            if !any_changed
                                && leaves.len() == 2
                                && leaves[0] == n.a
                                && leaves[1] == n.b
                            {
                                continue;
                            }
                            let mut iter = rewritten.into_iter();
                            let mut acc = iter.next().unwrap();
                            for l in iter {
                                acc = cx.c_bin(BinOp::And, acc, l)?;
                            }
                            if acc == i {
                                continue;
                            }
                            acc
                        }
                    }
                }
            }
            OpCode::Select => {
                let (mut ft, mut ff) = (GuardFacts::default(), GuardFacts::default());
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
                let mut fc = GuardFacts::default();
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
#[cfg_attr(not(feature = "mba"), allow(dead_code))]
pub(super) fn most_tested(cx: &mut Context, root: u32) -> Result<Option<u32>, Error> {
    let order = cx.post_order_ids(&[root]);
    let is_bool_root = cx.wid(root) == 1;
    let mut node_uses: IdMap<u32, u32> = IdMap::default();
    if is_bool_root {
        *node_uses.entry(root).or_default() += 1;
        for &id in &order {
            for ch in cx.node(id).children() {
                *node_uses.entry(ch).or_default() += 1;
            }
        }
    }
    let mut uses: IdMap<u32, (u32, u32)> = IdMap::default();
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
        let fan = if is_bool_root {
            node_uses.get(&i).copied().unwrap_or(1).max(1)
        } else {
            1
        };
        let entry = uses.entry(c).or_default();
        entry.0 += 1;
        entry.1 += fan;
    }
    let sym_bits = |cx: &Context, c: u32| -> u32 {
        let mut ft = GuardFacts::default();
        fixes(cx, c, true, &mut ft, 0);
        if ft
            .bits
            .iter()
            .all(|f| cx.node(f.x).op != OpCode::Sym || count_ones(&f.mask) < 2)
        {
            ft = GuardFacts::default();
            fixes(cx, c, false, &mut ft, 0);
        }
        ft.bits
            .into_iter()
            .filter(|f| cx.node(f.x).op == OpCode::Sym && count_ones(&f.mask) >= 2)
            .map(|f| count_ones(&f.mask))
            .max()
            .unwrap_or(0)
    };
    Ok(uses
        .into_iter()
        .filter(|&(c, (sites, fan))| {
            sites >= 2 || (is_bool_root && fan >= 2 && sym_bits(cx, c) >= 2)
        })
        .max_by_key(|&(c, (sites, fan))| (sym_bits(cx, c) >= 2, sites, fan, std::cmp::Reverse(c)))
        .map(|(c, _)| c))
}

/// Whether `root` has at least two `select` sites — or a shared multi-reader `select` (`uses >= 2`)
/// after hoisting — guarded by a condition (or its complement) that fixes at least 2 bits of an
/// input symbol (`OpCode::Sym`).
#[cfg_attr(not(feature = "mba"), allow(dead_code))]
pub(super) fn has_sym_select_guard(cx: &mut Context, root: u32) -> bool {
    let order = cx.post_order_ids(&[root]);
    let mut node_uses: IdMap<u32, u32> = IdMap::default();
    *node_uses.entry(root).or_default() += 1;
    for &id in &order {
        for ch in cx.node(id).children() {
            *node_uses.entry(ch).or_default() += 1;
        }
    }
    let mut conds: Vec<(u32, u32)> = Vec::new();
    for &i in &order {
        let n = cx.node(i);
        if n.op != OpCode::Select || cx.is_const(n.a) {
            continue;
        }
        let c = n.a;
        let key = if cx.node(c).op == OpCode::Not {
            cx.node(c).a
        } else {
            c
        };
        let fan = node_uses.get(&i).copied().unwrap_or(1).max(1);
        if let Some(slot) = conds
            .iter_mut()
            .find(|(k, _)| *k == key || super::bitwise::complementary_conds(cx, *k, key))
        {
            slot.1 += fan;
        } else {
            conds.push((key, fan));
        }
    }
    conds.into_iter().any(|(c, count)| {
        if count < 2 {
            return false;
        }
        let mut f = GuardFacts::default();
        fixes(cx, c, true, &mut f, 0);
        if f.bits
            .iter()
            .any(|fx| cx.node(fx.x).op == OpCode::Sym && count_ones(&fx.mask) >= 2)
        {
            return true;
        }
        f = GuardFacts::default();
        fixes(cx, c, false, &mut f, 0);
        f.bits
            .iter()
            .any(|fx| cx.node(fx.x).op == OpCode::Sym && count_ones(&fx.mask) >= 2)
    })
}

/// `root` on either side of the condition [`most_tested`] picks: the condition, `root` with what
/// it fixes put in, and `root` with what its complement fixes put in (see [`put`]);
/// `select(c, t, f)` is `root`. `None` when no condition is tested twice, or neither side
/// changes.
#[cfg_attr(not(feature = "mba"), allow(dead_code))]
pub(super) fn sides(cx: &mut Context, root: u32) -> Result<Option<(u32, u32, u32)>, Error> {
    let Some(c) = most_tested(cx, root)? else {
        return Ok(None);
    };
    Ok(sides_on(cx, root, c)?.map(|(t, f)| (c, t, f)))
}

/// [`sides`] on the condition `c`: `root` where `c` holds and where it does not, at an input
/// where `c` holds the first is `root`'s value, at any other the second. `None` when neither
/// differs from `root`.
#[cfg_attr(not(feature = "mba"), allow(dead_code))]
pub(super) fn sides_on(cx: &mut Context, root: u32, c: u32) -> Result<Option<(u32, u32)>, Error> {
    let (mut ft, mut ff) = (GuardFacts::default(), GuardFacts::default());
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
#[cfg_attr(not(feature = "mba"), allow(dead_code))]
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
#[cfg_attr(not(feature = "mba"), allow(dead_code))]
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
