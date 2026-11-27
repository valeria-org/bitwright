//! The shuffle pass: bit provenance of values assembled from pieces of other values.
//!
//! For a node of at most [`MAX_WIDTH`] bits, every output bit is traced to a constant or to one
//! bit of a *source* (an atom): through `&` with a constant, `|`, `^` and `+` of pieces whose
//! traced bits do not overlap (so no carry and no cancellation can occur), `a + a` (a shift by
//! one, as the linear pass writes it), shifts and rotations by constants, zero and sign
//! extension, `extract`, `concat` and `bswap`. When every bit is traced, the node is
//! re-emitted as the source itself, a rotation, a byte swap, one source in
//! place with constant bits (`(s & ~zeros) | ones`), or a `concat` of slices and constant runs,
//! and replaced when that is smaller. Limb recompositions, shifted-and-masked byte shuffles and
//! identity round trips collapse this way.

use super::{Fin, PassKind, Runner, Step, Stop};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::ops::{BinOp, CmpOp, UnOp};

/// The widest value traced.
pub(crate) const MAX_WIDTH: u16 = 512;

/// The most distinct sources and runs in one emission.
const MAX_PIECES: usize = 16;

/// Where one bit comes from.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Prov {
    Zero,
    One,
    /// Bit `j` of source node `s`, inverted when the third field is `true`.
    Bit(u32, u16, bool),
}

impl Prov {
    #[inline]
    pub(crate) fn invert(self) -> Prov {
        match self {
            Prov::Zero => Prov::One,
            Prov::One => Prov::Zero,
            Prov::Bit(s, j, inv) => Prov::Bit(s, j, !inv),
        }
    }
}

/// Canonical run-encoded bit provenance of a node, low bits first.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum BitRun {
    Const {
        val: bool,
        len: u16,
    },
    Slice {
        src: u32,
        lo: u16,
        len: u16,
        inv: bool,
    },
}

/// A node's bits, low first; `None` when some bit cannot be traced (then the node is a source
/// for its users).
pub(crate) type Bits = Option<Vec<Prov>>;

enum CowBits<'a> {
    Borrowed(&'a [Prov]),
    Owned(Vec<Prov>),
}

impl core::ops::Deref for CowBits<'_> {
    type Target = [Prov];

    #[inline]
    fn deref(&self) -> &[Prov] {
        match self {
            CowBits::Borrowed(s) => s,
            CowBits::Owned(v) => v,
        }
    }
}

impl CowBits<'_> {
    fn into_vec(self) -> Vec<Prov> {
        match self {
            CowBits::Borrowed(s) => s.to_vec(),
            CowBits::Owned(v) => v,
        }
    }
}

fn traced_op_emit(op: OpCode) -> bool {
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
            | OpCode::BitRev
            | OpCode::Const
    )
}

fn traced_op_full(op: OpCode) -> bool {
    traced_op_emit(op) || matches!(op, OpCode::Not | OpCode::Sub)
}

fn source(i: u32, w: u16) -> Vec<Prov> {
    (0..w).map(|j| Prov::Bit(i, j, false)).collect()
}

fn const_bits(v: &BitVec) -> Vec<Prov> {
    let limbs = v.limbs();
    (0..v.width().bits())
        .map(|j| {
            let word = limbs.get((j / 64) as usize).copied().unwrap_or(0);
            if (word >> (j % 64)) & 1 == 0 {
                Prov::Zero
            } else {
                Prov::One
            }
        })
        .collect()
}

fn and_prov(x: Prov, y: Prov) -> Option<Prov> {
    match (x, y) {
        (Prov::Zero, _) | (_, Prov::Zero) => Some(Prov::Zero),
        (Prov::One, p) | (p, Prov::One) => Some(p),
        (p, q) if p == q => Some(p),
        (Prov::Bit(s1, j1, i1), Prov::Bit(s2, j2, i2)) if s1 == s2 && j1 == j2 && i1 != i2 => {
            Some(Prov::Zero)
        }
        _ => None,
    }
}

fn or_prov(x: Prov, y: Prov) -> Option<Prov> {
    match (x, y) {
        (Prov::One, _) | (_, Prov::One) => Some(Prov::One),
        (Prov::Zero, p) | (p, Prov::Zero) => Some(p),
        (p, q) if p == q => Some(p),
        (Prov::Bit(s1, j1, i1), Prov::Bit(s2, j2, i2)) if s1 == s2 && j1 == j2 && i1 != i2 => {
            Some(Prov::One)
        }
        _ => None,
    }
}

fn xor_prov(x: Prov, y: Prov) -> Option<Prov> {
    match (x, y) {
        (Prov::Zero, p) | (p, Prov::Zero) => Some(p),
        (Prov::One, p) | (p, Prov::One) => Some(p.invert()),
        (p, q) if p == q => Some(Prov::Zero),
        (Prov::Bit(s1, j1, i1), Prov::Bit(s2, j2, i2)) if s1 == s2 && j1 == j2 && i1 != i2 => {
            Some(Prov::One)
        }
        _ => None,
    }
}

fn add_prov(x: Prov, y: Prov) -> Option<Prov> {
    match (x, y) {
        (Prov::Zero, p) | (p, Prov::Zero) => Some(p),
        // `b + ~b == 1` with zero carry out at every input.
        (Prov::Bit(s1, j1, i1), Prov::Bit(s2, j2, i2)) if s1 == s2 && j1 == j2 && i1 != i2 => {
            Some(Prov::One)
        }
        _ => None,
    }
}

fn sub_prov(x: Prov, y: Prov) -> Option<Prov> {
    match (x, y) {
        (p, Prov::Zero) => Some(p),
        // `1 - p == ~p` with zero borrow out at every input.
        (Prov::One, p) => Some(p.invert()),
        (p, q) if p == q => Some(Prov::Zero),
        _ => None,
    }
}

fn small_const(cx: &Context, i: u32) -> Option<u64> {
    cx.const_val(i).and_then(|v| v.to_u64())
}

/// The bits of `i` from its operands' (already traced) bits.
/// When `full` is `false` (`Phase::Shuffle`'s node rewriter), only non-complementing bit movement
/// and constant masks are traced so slice extraction preserves complement boundaries for
/// `Phase::Demanded` / `Phase::Mba`. When `full` is `true` (`bit_runs_of` / `decide_cmp_by_bits`),
/// complements, XOR bit flips, and single-bit borrow-free subtractions are traced as well.
fn trace(cx: &Context, bits: &crate::hash::IdMap<u32, Bits>, i: u32, full: bool) -> Bits {
    let n = cx.node(i);
    let w = n.width;
    let get = |j: u32| -> CowBits<'_> {
        match bits.get(&j) {
            Some(Some(b)) => CowBits::Borrowed(b.as_slice()),
            _ => CowBits::Owned(source(j, cx.node(j).width)),
        }
    };
    Some(match n.op {
        OpCode::Const => const_bits(&cx.const_val(i)?),
        OpCode::Not if full => get(n.a).iter().copied().map(Prov::invert).collect(),
        OpCode::And => {
            let (a, b) = (get(n.a), get(n.b));
            if full {
                a.iter()
                    .copied()
                    .zip(b.iter().copied())
                    .map(|(x, y)| and_prov(x, y))
                    .collect::<Option<Vec<_>>>()?
            } else {
                let (x, m) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                    (Some(_), None) => (b, a),
                    (None, Some(_)) => (a, b),
                    _ => return None,
                };
                x.iter()
                    .zip(m.iter())
                    .map(|(&p, &k)| if k == Prov::One { p } else { Prov::Zero })
                    .collect()
            }
        }
        // `a + a` is `a << 1` (the linear pass writes it so).
        OpCode::Add if n.a == n.b => {
            let a = get(n.a);
            core::iter::once(Prov::Zero)
                .chain(a.iter().copied())
                .take(w as usize)
                .collect()
        }
        OpCode::Sub if full && n.a == n.b => vec![Prov::Zero; w as usize],
        OpCode::Or | OpCode::Xor | OpCode::Add | OpCode::Sub => {
            if n.op == OpCode::Sub && !full {
                return None;
            }
            let (a, b) = (get(n.a), get(n.b));
            if full {
                let f = match n.op {
                    OpCode::Or => or_prov,
                    OpCode::Xor => xor_prov,
                    OpCode::Add => add_prov,
                    _ => sub_prov,
                };
                a.iter()
                    .copied()
                    .zip(b.iter().copied())
                    .map(|(x, y)| f(x, y))
                    .collect::<Option<Vec<_>>>()?
            } else if n.op == OpCode::Or {
                a.iter()
                    .zip(b.iter())
                    .map(|(&x, &y)| match (x, y) {
                        (Prov::One, _) | (_, Prov::One) => Some(Prov::One),
                        (Prov::Zero, v) | (v, Prov::Zero) => Some(v),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?
            } else {
                a.iter()
                    .zip(b.iter())
                    .map(|(&x, &y)| match (x, y) {
                        (Prov::Zero, v) | (v, Prov::Zero) => Some(v),
                        _ => None,
                    })
                    .collect::<Option<Vec<_>>>()?
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
            let mut v = a.into_vec();
            v.resize(w as usize, top);
            v
        }
        OpCode::Extract => {
            let a = get(n.a);
            let lo = n.b as usize;
            a.get(lo..lo + w as usize)?.to_vec()
        }
        OpCode::Concat => {
            let mut v = get(n.b).into_vec();
            v.extend_from_slice(&get(n.a));
            v
        }
        OpCode::Bswap => {
            let a = get(n.a);
            let bytes = (w / 8) as usize;
            (0..w as usize)
                .map(|i| a[(bytes - 1 - i / 8) * 8 + i % 8])
                .collect()
        }
        OpCode::BitRev => {
            let a = get(n.a);
            let wu = w as usize;
            (0..wu).map(|i| a[wu - 1 - i]).collect()
        }
        _ => return None,
    })
}

pub(super) fn bits_of(r: &mut Runner<'_, '_>, cx: &Context, root: u32) -> Result<Bits, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.shuffle.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        if node.width == 0 || node.width > MAX_WIDTH || !traced_op_emit(node.op) {
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
        let b = trace(cx, &r.shuffle, i, false);
        r.shuffle.insert(i, b);
    }
    Ok(r.shuffle[&root].clone())
}

fn full_bits_bounded(cx: &Context, root: u32, max_nodes: usize) -> (Option<Vec<Prov>>, u64) {
    let w = cx.wid(root);
    if w == 0 || w > MAX_WIDTH || !traced_op_full(cx.node(root).op) {
        return (None, 0);
    }
    let mut memo: crate::hash::IdMap<u32, Bits> = crate::hash::IdMap::default();
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    let mut visited = 0usize;
    let mut work = 0u64;
    while let Some((i, expanded)) = stack.pop() {
        if memo.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        if node.width == 0 || node.width > MAX_WIDTH || !traced_op_full(node.op) {
            memo.insert(i, None);
            continue;
        }
        if !expanded {
            if visited >= max_nodes {
                memo.insert(i, None);
                continue;
            }
            visited += 1;
            stack.push((i, true));
            for c in node.children() {
                if !memo.contains_key(&c) && traced_op_full(cx.node(c).op) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        work += u64::from(node.width);
        let b = trace(cx, &memo, i, true);
        memo.insert(i, b);
    }
    (memo.remove(&root).flatten(), work)
}

/// Coalesces per-bit provenance into maximal contiguous runs, low bits first.
pub(crate) fn bit_runs(bits: &[Prov]) -> Vec<BitRun> {
    let mut out: Vec<BitRun> = Vec::new();
    for &p in bits {
        match (out.last_mut(), p) {
            (Some(BitRun::Const { val, len }), Prov::Zero) if !*val => *len += 1,
            (Some(BitRun::Const { val, len }), Prov::One) if *val => *len += 1,
            (
                Some(BitRun::Slice {
                    src,
                    lo,
                    len,
                    inv: r_inv,
                }),
                Prov::Bit(s2, j, inv2),
            ) if *src == s2 && *r_inv == inv2 && *lo + *len == j => *len += 1,
            (_, Prov::Zero) => out.push(BitRun::Const { val: false, len: 1 }),
            (_, Prov::One) => out.push(BitRun::Const { val: true, len: 1 }),
            (_, Prov::Bit(src, lo, inv)) => out.push(BitRun::Slice {
                src,
                lo,
                len: 1,
                inv,
            }),
        }
    }
    out
}

/// Pure `Context`-only bounded bit-provenance run canonicalization (`1..=512` bits).
/// Always returns `Some` for valid widths `1..=512` (untraced nodes become a single whole-word
/// `BitRun::Slice` of themselves).
pub(crate) fn bit_runs_of(cx: &Context, root: u32, max_nodes: usize) -> Option<Vec<BitRun>> {
    let w = cx.wid(root);
    if w == 0 || w > MAX_WIDTH {
        return None;
    }
    match full_bits_bounded(cx, root, max_nodes).0 {
        Some(bits) => Some(bit_runs(&bits)),
        None => Some(vec![BitRun::Slice {
            src: root,
            lo: 0,
            len: w,
            inv: false,
        }]),
    }
}

/// Pure `Context`-only bounded equality / disequality check via canonical bit-provenance runs
/// (`1..=512` bits). Returns `Some(true)` when bit-for-bit identical, `Some(false)` when at least
/// one bit position is provably opposite (`0` vs `1` or `bit_j` vs `~bit_j`), else `None`.
pub(crate) fn decide_eq_by_runs(cx: &Context, a: u32, b: u32, max_nodes: usize) -> Option<bool> {
    let w = cx.wid(a);
    if w == 0 || w > MAX_WIDTH || cx.wid(b) != w {
        return None;
    }
    let ra = bit_runs_of(cx, a, max_nodes)?;
    let rb = bit_runs_of(cx, b, max_nodes)?;
    if ra == rb {
        return Some(true);
    }
    let (mut ia, mut ib) = (0usize, 0usize);
    let mut ca = ra.first().copied()?;
    let mut cb = rb.first().copied()?;
    loop {
        let step = run_len(ca).min(run_len(cb));
        let (ha, next_a) = split_run(ca, step);
        let (hb, next_b) = split_run(cb, step);
        let opposite = match (ha, hb) {
            (BitRun::Const { val: va, .. }, BitRun::Const { val: vb, .. }) => va != vb,
            (
                BitRun::Slice {
                    src: sa,
                    lo: la,
                    inv: inv_a,
                    ..
                },
                BitRun::Slice {
                    src: sb,
                    lo: lb,
                    inv: inv_b,
                    ..
                },
            ) => sa == sb && la == lb && inv_a != inv_b,
            _ => false,
        };
        if opposite {
            return Some(false);
        }
        ca = if run_len(next_a) == 0 {
            ia += 1;
            if ia == ra.len() {
                break;
            }
            ra[ia]
        } else {
            next_a
        };
        cb = if run_len(next_b) == 0 {
            ib += 1;
            if ib == rb.len() {
                break;
            }
            rb[ib]
        } else {
            next_b
        };
    }
    None
}

/// Number of low bit positions `[0..k)` on which `a` and `b` have provably identical bit
/// provenance (`a === b (mod 2^k)` for every input).
pub(crate) fn common_low_bits(cx: &Context, a: u32, b: u32, max_nodes: usize) -> u32 {
    let w = cx.wid(a);
    if w == 0 || w > MAX_WIDTH || cx.wid(b) != w {
        return 0;
    }
    let (Some(ra), Some(rb)) = (bit_runs_of(cx, a, max_nodes), bit_runs_of(cx, b, max_nodes))
    else {
        return 0;
    };
    let (mut ia, mut ib) = (0usize, 0usize);
    let (Some(mut ca), Some(mut cb)) = (ra.first().copied(), rb.first().copied()) else {
        return 0;
    };
    let mut matched = 0u32;
    loop {
        let step = run_len(ca).min(run_len(cb));
        let (ha, next_a) = split_run(ca, step);
        let (hb, next_b) = split_run(cb, step);
        if ha != hb {
            break;
        }
        matched += u32::from(step);
        ca = if run_len(next_a) == 0 {
            ia += 1;
            if ia == ra.len() {
                break;
            }
            ra[ia]
        } else {
            next_a
        };
        cb = if run_len(next_b) == 0 {
            ib += 1;
            if ib == rb.len() {
                break;
            }
            rb[ib]
        } else {
            next_b
        };
    }
    matched
}

/// Bitwise complement of a canonical run list.
pub(crate) fn runs_invert(runs: &[BitRun]) -> Vec<BitRun> {
    runs.iter()
        .map(|&r| match r {
            BitRun::Const { val, len } => BitRun::Const { val: !val, len },
            BitRun::Slice { src, lo, len, inv } => BitRun::Slice {
                src,
                lo,
                len,
                inv: !inv,
            },
        })
        .collect()
}

fn run_len(r: BitRun) -> u16 {
    match r {
        BitRun::Const { len, .. } | BitRun::Slice { len, .. } => len,
    }
}

fn split_run(r: BitRun, take: u16) -> (BitRun, BitRun) {
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
}

#[cfg(feature = "mba")]
fn set_bit_range(limbs: &mut [u64; 8], off: u16, len: u16) {
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
        let mask = if chunk == 64 {
            u64::MAX
        } else {
            ((1u64 << chunk) - 1) << bit
        };
        limbs[word] |= mask;
        pos += chunk;
    }
}

/// When `a ^ b` is identically a constant `c` at every bit (`b == a ^ c`), returns `Some(c)`.
#[cfg(feature = "mba")]
pub(crate) fn runs_xor_diff(a: &[BitRun], b: &[BitRun], w: crate::Width) -> Option<BitVec> {
    let (mut ia, mut ib) = (0usize, 0usize);
    let mut ra = a.first().copied()?;
    let mut rb = b.first().copied()?;
    let mut off = 0u16;
    let mut limbs = [0u64; 8];
    loop {
        let step = run_len(ra).min(run_len(rb));
        let (ha, next_ra) = split_run(ra, step);
        let (hb, next_rb) = split_run(rb, step);
        let diff = match (ha, hb) {
            (BitRun::Const { val: va, .. }, BitRun::Const { val: vb, .. }) => va ^ vb,
            (
                BitRun::Slice {
                    src: sa,
                    lo: la,
                    inv: ia_inv,
                    ..
                },
                BitRun::Slice {
                    src: sb,
                    lo: lb,
                    inv: ib_inv,
                    ..
                },
            ) if sa == sb && la == lb => ia_inv ^ ib_inv,
            _ => return None,
        };
        if diff {
            set_bit_range(&mut limbs, off, step);
        }
        off += step;
        ra = if run_len(next_ra) == 0 {
            ia += 1;
            if ia == a.len() {
                ib += usize::from(run_len(next_rb) == 0);
                if ib != b.len() {
                    return None;
                }
                break;
            }
            a[ia]
        } else {
            next_ra
        };
        rb = if run_len(next_rb) == 0 {
            ib += 1;
            if ib == b.len() {
                return None;
            }
            b[ib]
        } else {
            next_rb
        };
    }
    Some(BitVec::wrapping_from_limbs(w, &limbs))
}

/// Checks whether `sub` is `(sup & mask)` (`inv = false`) or `(~sup & mask)` (`inv = true`) for
/// some non-zero constant `mask`.
#[cfg(feature = "mba")]
pub(crate) fn runs_masked_sub(
    sub: &[BitRun],
    sup: &[BitRun],
    w: crate::Width,
) -> Option<(BitVec, bool)> {
    let (mut ia, mut ib) = (0usize, 0usize);
    let mut ra = sub.first().copied()?;
    let mut rb = sup.first().copied()?;
    let mut off = 0u16;
    let mut limbs = [0u64; 8];
    let mut polarity: Option<bool> = None;
    let mut any_active = false;
    loop {
        let step = run_len(ra).min(run_len(rb));
        let (ha, next_ra) = split_run(ra, step);
        let (hb, next_rb) = split_run(rb, step);
        match (ha, hb) {
            (BitRun::Const { val: false, .. }, _) => {}
            (BitRun::Const { val: true, .. }, BitRun::Const { val: vb, .. }) => {
                let want_inv = !vb;
                if let Some(p) = polarity
                    && p != want_inv
                {
                    return None;
                }
                polarity = Some(want_inv);
                set_bit_range(&mut limbs, off, step);
                any_active = true;
            }
            (
                BitRun::Slice {
                    src: sa,
                    lo: la,
                    inv: ia_inv,
                    ..
                },
                BitRun::Slice {
                    src: sb,
                    lo: lb,
                    inv: ib_inv,
                    ..
                },
            ) if sa == sb && la == lb => {
                let want_inv = ia_inv != ib_inv;
                if let Some(p) = polarity
                    && p != want_inv
                {
                    return None;
                }
                polarity = Some(want_inv);
                set_bit_range(&mut limbs, off, step);
                any_active = true;
            }
            _ => return None,
        }
        off += step;
        ra = if run_len(next_ra) == 0 {
            ia += 1;
            if ia == sub.len() {
                ib += usize::from(run_len(next_rb) == 0);
                if ib != sup.len() {
                    return None;
                }
                break;
            }
            sub[ia]
        } else {
            next_ra
        };
        rb = if run_len(next_rb) == 0 {
            ib += 1;
            if ib == sup.len() {
                return None;
            }
            sup[ib]
        } else {
            next_rb
        };
    }
    if !any_active {
        return None;
    }
    Some((
        BitVec::wrapping_from_limbs(w, &limbs),
        polarity.unwrap_or(false),
    ))
}

/// Checks whether `u == a | b` identically at every bit across `1..=512`.
pub(crate) fn runs_is_or(u: &[BitRun], a: &[BitRun], b: &[BitRun]) -> bool {
    let (mut iu, mut ia, mut ib) = (0usize, 0usize, 0usize);
    let (Some(mut ru), Some(mut ra), Some(mut rb)) =
        (u.first().copied(), a.first().copied(), b.first().copied())
    else {
        return false;
    };
    loop {
        let step = run_len(ru).min(run_len(ra)).min(run_len(rb));
        let (hu, next_ru) = split_run(ru, step);
        let (ha, next_ra) = split_run(ra, step);
        let (hb, next_rb) = split_run(rb, step);
        let ok = match (ha, hb) {
            (BitRun::Const { val: true, .. }, _) | (_, BitRun::Const { val: true, .. }) => {
                matches!(hu, BitRun::Const { val: true, .. })
            }
            (BitRun::Const { val: false, .. }, x) | (x, BitRun::Const { val: false, .. }) => {
                hu == x
            }
            (x, y) if x == y => hu == x,
            (
                BitRun::Slice {
                    src: sa,
                    lo: la,
                    inv: ia_inv,
                    ..
                },
                BitRun::Slice {
                    src: sb,
                    lo: lb,
                    inv: ib_inv,
                    ..
                },
            ) if sa == sb && la == lb && ia_inv != ib_inv => {
                matches!(hu, BitRun::Const { val: true, .. })
            }
            _ => false,
        };
        if !ok {
            return false;
        }
        ru = if run_len(next_ru) == 0 {
            iu += 1;
            if iu == u.len() {
                ia += usize::from(run_len(next_ra) == 0);
                ib += usize::from(run_len(next_rb) == 0);
                return ia == a.len() && ib == b.len();
            }
            u[iu]
        } else {
            next_ru
        };
        ra = if run_len(next_ra) == 0 {
            ia += 1;
            if ia == a.len() {
                return false;
            }
            a[ia]
        } else {
            next_ra
        };
        rb = if run_len(next_rb) == 0 {
            ib += 1;
            if ib == b.len() {
                return false;
            }
            b[ib]
        } else {
            next_rb
        };
    }
}

fn bits_of_full(r: &mut Runner<'_, '_>, cx: &Context, root: u32) -> Result<Bits, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.shuffle_full.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        if node.width == 0 || node.width > MAX_WIDTH || !traced_op_full(node.op) {
            r.shuffle_full.insert(i, None);
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if !r.shuffle_full.contains_key(&c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, u64::from(node.width))?;
        let b = trace(cx, &r.shuffle_full, i, true);
        r.shuffle_full.insert(i, b);
    }
    Ok(r.shuffle_full[&root].clone())
}

/// Decides `a op b` directly when per-bit provenance determines the comparison for every input.
pub(super) fn decide_cmp_by_bits(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    op: CmpOp,
    a: u32,
    b: u32,
) -> Result<Option<bool>, Stop> {
    let w = cx.wid(a);
    if w == 0 || w > MAX_WIDTH || cx.wid(b) != w {
        return Ok(None);
    }
    let (oa, ob) = (cx.node(a).op, cx.node(b).op);
    if (!traced_op_full(oa) && !traced_op_full(ob))
        || (oa == OpCode::Const && !traced_op_full(ob))
        || (ob == OpCode::Const && !traced_op_full(oa))
    {
        return Ok(None);
    }
    let b_a = bits_of_full(r, cx, a)?.unwrap_or_else(|| source(a, w));
    let b_b = bits_of_full(r, cx, b)?.unwrap_or_else(|| source(b, w));
    if b_a == b_b {
        return Ok(Some(matches!(op, CmpOp::Eq | CmpOp::Ule | CmpOp::Sle)));
    }
    match op {
        CmpOp::Eq | CmpOp::Ne => {
            let guaranteed_diff = b_a.iter().zip(&b_b).any(|(&pa, &pb)| {
                matches!((pa, pb), (Prov::Zero, Prov::One) | (Prov::One, Prov::Zero))
                    || matches!(
                        (pa, pb),
                        (Prov::Bit(s1, j1, i1), Prov::Bit(s2, j2, i2))
                            if s1 == s2 && j1 == j2 && i1 != i2
                    )
            });
            if guaranteed_diff {
                return Ok(Some(op == CmpOp::Ne));
            }
            Ok(None)
        }
        CmpOp::Ult | CmpOp::Ule | CmpOp::Slt | CmpOp::Sle => {
            let Some(msb_diff) = (0..b_a.len()).rev().find(|&k| b_a[k] != b_b[k]) else {
                return Ok(None);
            };
            let (pa, pb) = (b_a[msb_diff], b_b[msb_diff]);
            let a_lt_b = match (pa, pb) {
                (Prov::Zero, Prov::One) => true,
                (Prov::One, Prov::Zero) => false,
                _ => return Ok(None),
            };
            let signed_flip = matches!(op, CmpOp::Slt | CmpOp::Sle) && msb_diff + 1 == b_a.len();
            Ok(Some(a_lt_b ^ signed_flip))
        }
    }
}

fn emit(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    owner: u32,
    bits: &[Prov],
) -> Result<(Option<u32>, Fin), Stop> {
    let w = bits.len() as u16;
    let width = crate::Width::new(w).map_err(|e| Stop::Error(e.into()))?;
    if bits.iter().all(|p| matches!(p, Prov::Zero | Prov::One)) {
        let mut limbs = [0u64; 8];
        for (i, &p) in bits.iter().enumerate() {
            if p == Prov::One {
                limbs[i / 64] |= 1u64 << (i % 64);
            }
        }
        let kv = BitVec::wrapping_from_limbs(width, &limbs);
        let c = r.build(cx, |cx| cx.mk_const(&kv))?;
        return Ok((Some(c), Fin::FINAL));
    }
    let rs = bit_runs(bits);
    if rs.len() > MAX_PIECES {
        return Ok((None, Fin::FINAL));
    }
    // A whole source, possibly rotated, byte-swapped, bit-reversed, and/or uniformly complemented.
    if let Some(&Prov::Bit(s, _, inv0)) = bits.first()
        && cx.node(s).width == w
        && bits
            .iter()
            .all(|p| matches!(*p, Prov::Bit(t, _, inv) if t == s && inv == inv0))
    {
        let j = |i: usize| match bits[i] {
            Prov::Bit(_, j, _) => j as usize,
            _ => 0,
        };
        let wu = w as usize;
        let k = (wu - j(0)) % wu;
        let wrap_inv = |r: &mut Runner<'_, '_>, cx: &mut Context, x: u32| -> Result<u32, Stop> {
            if inv0 {
                r.build(cx, |cx| cx.c_un(UnOp::Not, x))
            } else {
                Ok(x)
            }
        };
        if (0..wu).all(|i| j(i) == (i + wu - k) % wu) {
            let base = if k == 0 {
                s
            } else {
                let kv = BitVec::wrapping_from_u64(width, k as u64);
                r.build(cx, |cx| {
                    let kc = cx.mk_const(&kv)?;
                    cx.c_bin(BinOp::RotL, s, kc)
                })?
            };
            return Ok((Some(wrap_inv(r, cx, base)?), Fin::FINAL));
        }
        if w.is_multiple_of(8) && (0..wu).all(|i| j(i) == (wu / 8 - 1 - i / 8) * 8 + i % 8) {
            let bs = r.build(cx, |cx| cx.c_un(UnOp::Bswap, s))?;
            return Ok((Some(wrap_inv(r, cx, bs)?), Fin::FINAL));
        }
        if wu > 1 && (0..wu).all(|i| j(i) == wu - 1 - i) {
            let br = r.build(cx, |cx| cx.c_un(UnOp::BitRev, s))?;
            return Ok((Some(wrap_inv(r, cx, br)?), Fin::FINAL));
        }
    }
    // One source in place with some bits constant or inverted.
    if let Some(&Prov::Bit(s, _, _)) = bits.iter().find(|p| matches!(p, Prov::Bit(..)))
        && cx.node(s).width == w
        && bits
            .iter()
            .enumerate()
            .all(|(i, p)| !matches!(*p, Prov::Bit(t, j, _) if t != s || usize::from(j) != i))
    {
        let mut z_limbs = [0u64; 8];
        let mut o_limbs = [0u64; 8];
        let mut f_limbs = [0u64; 8];
        for (i, &p) in bits.iter().enumerate() {
            match p {
                Prov::Zero => z_limbs[i / 64] |= 1u64 << (i % 64),
                Prov::One => o_limbs[i / 64] |= 1u64 << (i % 64),
                Prov::Bit(_, _, true) => f_limbs[i / 64] |= 1u64 << (i % 64),
                Prov::Bit(_, _, false) => {}
            }
        }
        let mut zeros = BitVec::wrapping_from_limbs(width, &z_limbs);
        let mut ones = BitVec::wrapping_from_limbs(width, &o_limbs);
        let flips = BitVec::wrapping_from_limbs(width, &f_limbs);
        let mut fin = Fin::FINAL;
        if flips.is_zero() {
            if (!zeros.is_zero() || !ones.is_zero())
                && r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(owner)))
                && let (Some(kb), kfin) = super::known(r, cx, s)?
            {
                let next_zeros = crate::facts::known::bv_and(
                    &zeros,
                    &crate::facts::known::bv_not(&kb.known_zero()),
                );
                let next_ones = crate::facts::known::bv_and(
                    &ones,
                    &crate::facts::known::bv_not(&kb.known_one()),
                );
                if next_zeros != zeros || next_ones != ones {
                    zeros = next_zeros;
                    ones = next_ones;
                    fin = fin.and(kfin);
                } else {
                    fin = fin.and(kfin.unchanged());
                }
            }
            r.meter.charge(Counter::PassWork, u64::from(w))?;
            let built = r.build(cx, |cx| {
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
            })?;
            return Ok((Some(built), fin));
        }
        r.meter.charge(Counter::PassWork, u64::from(w))?;
        let all_bits_inverted = !bits.iter().any(|p| matches!(p, Prov::Bit(_, _, false)));
        let built = r.build(cx, |cx| {
            if all_bits_inverted {
                let mut x = cx.c_un(UnOp::Not, s)?;
                if !zeros.is_zero() {
                    let c = cx.mk_const(&crate::facts::known::bv_not(&zeros))?;
                    x = cx.c_bin(BinOp::And, x, c)?;
                }
                if !ones.is_zero() {
                    let c = cx.mk_const(&ones)?;
                    x = cx.c_bin(BinOp::Or, x, c)?;
                }
                Ok(x)
            } else {
                let clear = crate::facts::known::bv_or(&zeros, &ones);
                let mut x = s;
                if !clear.is_zero() {
                    let c = cx.mk_const(&crate::facts::known::bv_not(&clear))?;
                    x = cx.c_bin(BinOp::And, x, c)?;
                }
                let xor_mask = crate::facts::known::bv_or(&flips, &ones);
                if !xor_mask.is_zero() {
                    let c = cx.mk_const(&xor_mask)?;
                    x = cx.c_bin(BinOp::Xor, x, c)?;
                }
                Ok(x)
            }
        })?;
        return Ok((Some(built), fin));
    }
    // A concat of the runs, high first.
    let mut acc: Option<u32> = None;
    for run in rs.iter().rev() {
        r.meter.charge(Counter::PassWork, 1)?;
        let piece = match *run {
            BitRun::Const { val, len } => {
                let lw = crate::Width::new(len).map_err(|e| Stop::Error(e.into()))?;
                let c = if val {
                    BitVec::ones(lw)
                } else {
                    BitVec::zero(lw)
                };
                r.build(cx, |cx| cx.mk_const(&c))?
            }
            BitRun::Slice { src, lo, len, inv } => r.build(cx, |cx| {
                let sl = cx.c_extract(src, lo, len)?;
                if inv { cx.c_un(UnOp::Not, sl) } else { Ok(sl) }
            })?,
        };
        acc = Some(match acc {
            None => piece,
            Some(h) => r.build(cx, |cx| cx.c_concat(h, piece))?,
        });
    }
    r.meter.check()?;
    Ok((acc, Fin::FINAL))
}

/// Strip a redundant `& (w - 1)` mask from a rotation count at a power-of-two width `w`.
fn strip_rot_mask(cx: &Context, s: u32, w: u16) -> u32 {
    let n = cx.node(s);
    if n.op == OpCode::And && w.is_power_of_two() {
        let want = u64::from(w - 1);
        if cx.const_val(n.b).and_then(|v| v.to_u64()) == Some(want) {
            return n.a;
        }
        if cx.const_val(n.a).and_then(|v| v.to_u64()) == Some(want) {
            return n.b;
        }
    }
    s
}

/// Recognize variable-count rotations:
/// - `(x << s1) | (x >>u s2)` (or their shared low truncation) where `0 <= s1, s2 < w` and
///   `(s1 + s2) ≡ 0 (mod w)` at power-of-two width `w <= 64` -> `rotr(x, s2)` or `rotl(x, s1)`;
/// - chained rotations `rot(rot(x, s1), s2)` at power-of-two width `w` -> `rot(x, s1 ± s2)`;
/// - redundant `& (w - 1)` mask on a rotation count at power-of-two width `w`.
fn var_rotate(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Option<Step>, Stop> {
    let node = cx.node(n);
    let w = node.width;
    if matches!(node.op, OpCode::RotL | OpCode::RotR) && w.is_power_of_two() && w >= 8 {
        let s = strip_rot_mask(cx, node.b, w);
        let inner = cx.node(node.a);
        if matches!(inner.op, OpCode::RotL | OpCode::RotR)
            && (cx.const_val(node.b).is_none() || cx.const_val(inner.b).is_none())
        {
            let before = cx.len() as u32;
            let s1 = strip_rot_mask(cx, inner.b, w);
            let same_dir = node.op == inner.op;
            let combined = r.build(cx, |cx| {
                if same_dir {
                    cx.c_bin(BinOp::Add, s1, s)
                } else {
                    cx.c_bin(BinOp::Sub, s, s1)
                }
            })?;
            let rop = if node.op == OpCode::RotL {
                BinOp::RotL
            } else {
                BinOp::RotR
            };
            let e = r.build(cx, |cx| cx.c_bin(rop, inner.a, combined))?;
            // Combining two nested rotates into one with summed count breaks the chain cleanly.
            return super::finish_with(
                r,
                cx,
                PassKind::Shuffle,
                n,
                e,
                before,
                &[inner.a, s1, s],
                Fin::FINAL,
                true,
            )
            .map(Some);
        }
        if s != node.b {
            let before = cx.len() as u32;
            let rop = if node.op == OpCode::RotL {
                BinOp::RotL
            } else {
                BinOp::RotR
            };
            let e = r.build(cx, |cx| cx.c_bin(rop, node.a, s))?;
            return super::finish(
                r,
                cx,
                PassKind::Shuffle,
                n,
                e,
                before,
                &[node.a, s],
                Fin::FINAL,
            )
            .map(Some);
        }
        return Ok(None);
    }
    if node.op != OpCode::Or {
        return Ok(None);
    }
    let unwrap_low = |id: u32| -> (u32, bool) {
        let m = cx.node(id);
        if m.op == OpCode::Extract && m.b == 0 {
            (m.a, true)
        } else {
            (id, false)
        }
    };
    let (la, ta) = unwrap_low(node.a);
    let (lb, tb) = unwrap_low(node.b);
    if ta != tb {
        return Ok(None);
    }
    let (na, nb) = (cx.node(la), cx.node(lb));
    let (x, s1, s2) = match (na.op, nb.op) {
        (OpCode::Shl, OpCode::LShr) if na.a == nb.a => (na.a, na.b, nb.b),
        (OpCode::LShr, OpCode::Shl) if na.a == nb.a => (na.a, nb.b, na.b),
        _ => return Ok(None),
    };
    if cx.const_val(s1).is_some() && cx.const_val(s2).is_some() {
        return Ok(None);
    }
    let wx = cx.wid(x);
    if !wx.is_power_of_two() || wx < 8 {
        return Ok(None);
    }
    let logw = wx.trailing_zeros() as u16;
    let count_w = cx.width_of(s1);
    let hi_mask =
        crate::facts::known::bv_not(&crate::facts::known::low_mask(count_w, u32::from(logw)));
    let (k1, f1) = super::known(r, cx, s1)?;
    let (k2, f2) = super::known(r, cx, s2)?;
    let bounded = |k: Option<crate::facts::KnownBits>| {
        k.is_some_and(|kb| crate::facts::known::bv_and(&kb.known_zero(), &hi_mask) == hi_mask)
    };
    if !(bounded(k1) && bounded(k2)) {
        return Ok(None);
    }
    let fin = f1.and(f2);
    let before = cx.len() as u32;
    let neg_s2 = r.build(cx, |cx| cx.c_un(UnOp::Neg, s2))?;
    #[cfg_attr(not(feature = "mba"), allow(unused_mut))]
    let mut complementary = super::poly::equal_mod(r, cx, s1, neg_s2, logw)?;
    #[cfg(feature = "mba")]
    if !complementary {
        complementary = super::mba::equal_lanes(r, cx, s1, neg_s2, logw)?;
    }
    if !complementary {
        super::discard(r, cx, before);
        return Ok(None);
    }
    let tree = |i: u32| cx.meta[i as usize].tree;
    let (rop, chosen_s) = if tree(s2) <= tree(s1) {
        (BinOp::RotR, strip_rot_mask(cx, s2, wx))
    } else {
        (BinOp::RotL, strip_rot_mask(cx, s1, wx))
    };
    let rot = r.build(cx, |cx| cx.c_bin(rop, x, chosen_s))?;
    let e = if ta {
        r.build(cx, |cx| cx.c_extract(rot, 0, w))?
    } else {
        rot
    };
    super::finish(r, cx, PassKind::Shuffle, n, e, before, &[x, chosen_s], fin).map(Some)
}

/// The shuffle pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    if let Some(step) = var_rotate(r, cx, n)? {
        return Ok(step);
    }
    let node = cx.node(n);
    if node.op == OpCode::Popcnt {
        let mut word = node.a;
        while matches!(
            cx.node(word).op,
            OpCode::RotL | OpCode::RotR | OpCode::BitRev | OpCode::Bswap
        ) {
            r.meter.charge(Counter::PassWork, 1)?;
            word = cx.node(word).a;
        }
        if word != node.a {
            let before = cx.len() as u32;
            let e = r.build(cx, |cx| cx.c_un(UnOp::Popcnt, word))?;
            return super::finish_with(
                r,
                cx,
                PassKind::Shuffle,
                n,
                e,
                before,
                &[word],
                Fin::FINAL,
                true,
            );
        }
    }
    // Reordering the counts preserves saturating shifts and modular rotations even
    // at widths where adding the counts in their own bit width would wrap.
    if matches!(
        node.op,
        OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR
    ) {
        let inner = cx.node(node.a);
        if inner.op == node.op
            && cx.order(inner.b, node.b).is_gt()
            && !cx.is_const(node.b)
            && !cx.is_const(inner.b)
        {
            let before = cx.len() as u32;
            let op = node.op.as_bin().unwrap();
            let first = r.build(cx, |cx| cx.c_bin(op, inner.a, node.b))?;
            let e = r.build(cx, |cx| cx.c_bin(op, first, inner.b))?;
            return super::finish_with(
                r,
                cx,
                PassKind::Shuffle,
                n,
                e,
                before,
                &[inner.a, inner.b, node.b],
                Fin::FINAL,
                true,
            );
        }
    }
    if node.width > MAX_WIDTH || !traced_op_emit(node.op) || node.op == OpCode::Const {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let Some(bits) = bits_of(r, cx, n)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    let mut atoms: Vec<u32> = bits
        .iter()
        .filter_map(|p| match p {
            Prov::Bit(s, _, _) => Some(*s),
            _ => None,
        })
        .collect();
    atoms.sort_unstable();
    atoms.dedup();
    if atoms.len() > MAX_PIECES || atoms == [n] {
        return Ok(Step::Normal(Fin::FINAL));
    }
    let before = cx.len() as u32;
    let (Some(e), emit_fin) = emit(r, cx, n, &bits)? else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    if e == n {
        super::discard(r, cx, before);
        return Ok(Step::Normal(emit_fin.unchanged()));
    }
    r.explain_with(|| crate::engine::Explanation::Shuffle {
        bits: bits
            .iter()
            .map(|b| match *b {
                Prov::Zero => crate::engine::Source::Zero,
                Prov::One => crate::engine::Source::One,
                Prov::Bit(s, j, false) => crate::engine::Source::Bit {
                    of: cx.handle(s),
                    bit: j,
                },
                Prov::Bit(s, j, true) => crate::engine::Source::NotBit {
                    of: cx.handle(s),
                    bit: j,
                },
            })
            .collect(),
    });
    let tie = node.op == OpCode::And && zext_slice(cx, e) && {
        let tree = |i: u32| cx.meta[i as usize].tree;
        tree(e) < tree(n)
    };
    super::finish_with(
        r,
        cx,
        PassKind::Shuffle,
        n,
        e,
        before,
        &atoms,
        emit_fin,
        tie,
    )
}

/// Whether `e` is `zext<N>(extract<lo, k>(x))` with `x` not `N` bits wide: a mask keeping the
/// low bits of a slice, as the narrower slice zero-extended. Nothing rewrites that back (the
/// rule `zext_trunc` reads only a truncation of a value of the extension's own width), so the
/// pass commits it on a tie as well, when it is a smaller tree: masks sharing their constant
/// would otherwise each wait for the other to free it, as in the digit product
/// `(trunc<13>(x) & 127) * (extract<7, 13>(y) & 127)`.
fn zext_slice(cx: &Context, e: u32) -> bool {
    let z = cx.node(e);
    if z.op != OpCode::Zext {
        return false;
    }
    let s = cx.node(z.a);
    s.op == OpCode::Extract && cx.wid(s.a) != z.width
}

#[cfg(all(test, feature = "prove"))]
mod extra_tests {
    use crate::{Context, ParseOptions, Width};

    #[test]
    fn var_rotate_recognizes_complementary_bounded_shifts_and_folds_chains() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Complementary bounded shifts mod 64
            "let s = k & 63; let c = (0 - s) & 63; (x << c) | (x >>u s) == rotr(x, k)",
            // Chained variable rotates cancel
            "rotl(rotr(x, k & 63), k & 63) == x",
            // Redundant low-bit mask on power-of-two rotate count
            "rotr(x, k & 63) == rotr(x, k)",
            // Causal low-6-bit MBA rotate count equivalence (0x14022a990-style)
            "let %36 = a ^ b; let %37 = (b + 2) ^ a; let %38 = %36 & 61; \
             let %39 = (%38 - (%37 & 61)) * 310 + 0xffffb14a & 62; \
             (x << (10 - ((%36 & 2) + %37 - %38) * 10 & 62) | x >>u %39) == rotr(x, %39)",
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
    fn var_rotate_rejects_unbounded_shift_count_above_width() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        // At s == 65, `c = (64 - s) & 127 = 127`: both shifts are >= 64, so LHS == 0 while RHS == rotr(x, 1).
        let text = "let s = k & 127; let c = (64 - s) & 127; ((x << c) | (x >>u s)) == rotr(x, s)";
        let e = cx.parse(text, &opt).unwrap();
        let out = crate::prove::valid_under_with(&mut cx, e, None, &cfg, &prover).unwrap();
        assert!(
            matches!(out, crate::prove::Outcome::Refuted(_)),
            "expected Refuted for {text}, got {out:?}"
        );
    }
}
