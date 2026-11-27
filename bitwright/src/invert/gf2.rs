//! Linear algebra over GF(2) across widths `1..=512`: dependency matrices and affine
//! decompositions through `^`, `~`, constant `&`/`|`, shifts and rotations by constants,
//! byte swaps, bit reversals, slices, extensions, and concatenations, plus rank and linear
//! system solving by Gaussian elimination.

use crate::BitVec;
use crate::expr::{Context, OpCode};
use crate::hash::IdMap;

/// Maximum bit width represented by a single [`Row`] (`8 * 64 = 512` bits).
pub(crate) const MAX_BITS: u16 = 512;

/// One row of a matrix over GF(2): bit `j` (`0 <= j < 512`) is the entry in column `j`.
pub(crate) type Row = [u64; 8];

/// A matrix over GF(2), one [`Row`] per output bit.
pub(crate) type Rows = Vec<Row>;

/// The all-zero row.
pub(crate) const ZERO_ROW: Row = [0; 8];

#[inline]
pub(crate) fn row_is_zero(r: &Row) -> bool {
    (r[0] | r[1] | r[2] | r[3] | r[4] | r[5] | r[6] | r[7]) == 0
}

#[inline]
pub(crate) fn row_bit(r: &Row, j: usize) -> bool {
    (r[j >> 6] >> (j & 63)) & 1 != 0
}

#[inline]
pub(crate) fn row_set(r: &mut Row, j: usize) {
    r[j >> 6] |= 1u64 << (j & 63);
}

#[inline]
pub(crate) fn row_xor(a: &Row, b: &Row) -> Row {
    [
        a[0] ^ b[0],
        a[1] ^ b[1],
        a[2] ^ b[2],
        a[3] ^ b[3],
        a[4] ^ b[4],
        a[5] ^ b[5],
        a[6] ^ b[6],
        a[7] ^ b[7],
    ]
}

#[inline]
pub(crate) fn row_xor_assign(a: &mut Row, b: &Row) {
    for k in 0..8 {
        a[k] ^= b[k];
    }
}

/// Lowest set column index `0..512`, or `None` for [`ZERO_ROW`].
#[inline]
fn row_lead(r: &Row) -> Option<usize> {
    for (w, &limb) in r.iter().enumerate() {
        if limb != 0 {
            return Some(w * 64 + limb.trailing_zeros() as usize);
        }
    }
    None
}

fn identity_rows(w: usize) -> Rows {
    let mut rows = vec![ZERO_ROW; w];
    for (k, r) in rows.iter_mut().enumerate() {
        row_set(r, k);
    }
    rows
}

fn apply_un_rows(op: OpCode, a: &[Row], w: usize) -> Option<Rows> {
    match op {
        OpCode::Not | OpCode::Neg if op == OpCode::Not || w == 1 => Some(a.to_vec()),
        OpCode::Bswap if w >= 16 && w.is_multiple_of(8) => {
            let bytes = w / 8;
            Some(
                (0..w)
                    .map(|k| a[(bytes - 1 - k / 8) * 8 + (k % 8)])
                    .collect(),
            )
        }
        OpCode::BitRev => Some((0..w).map(|k| a[w - 1 - k]).collect()),
        _ => None,
    }
}

fn apply_shift_rows(op: OpCode, a: &[Row], cnt: &BitVec, w: usize) -> Option<Rows> {
    match op {
        OpCode::Shl | OpCode::LShr | OpCode::AShr => {
            let s = cnt.to_u64().map_or(w, |v| (v as usize).min(w));
            Some(match op {
                OpCode::Shl => (0..w)
                    .map(|k| if k >= s { a[k - s] } else { ZERO_ROW })
                    .collect(),
                OpCode::LShr => (0..w)
                    .map(|k| if k + s < w { a[k + s] } else { ZERO_ROW })
                    .collect(),
                _ => (0..w).map(|k| a[(k + s).min(w - 1)]).collect(),
            })
        }
        OpCode::RotL | OpCode::RotR if w > 0 => {
            let s = super::count_mod(cnt, w as u16) as usize;
            Some(
                (0..w)
                    .map(|k| {
                        let j = if op == OpCode::RotL {
                            (k + w - s) % w
                        } else {
                            (k + s) % w
                        };
                        a[j]
                    })
                    .collect(),
            )
        }
        _ => None,
    }
}

fn mask_rows(a: &[Row], mask: &BitVec, clear_on_one: bool) -> Rows {
    (0..a.len())
        .map(|k| {
            let set = mask.bit(k as u16) == Some(true);
            if set == clear_on_one { ZERO_ROW } else { a[k] }
        })
        .collect()
}

/// For each node in `nodes` (between `hole` and some root, in topological order), the matrix of
/// its output bits over the bits of `hole` (`1..=512` bits), or `None` if an operation is not
/// affine over GF(2) in `hole` (given constant masks and shift counts).
pub(crate) fn rows(cx: &Context, hole: u32, nodes: &[u32]) -> Option<IdMap<u32, Rows>> {
    let wv = cx.wid(hole);
    if wv == 0 || wv > MAX_BITS {
        return None;
    }
    let mut out: IdMap<u32, Rows> = IdMap::default();
    out.insert(hole, identity_rows(usize::from(wv)));
    let dep = |r: &Rows| r.iter().any(|row| !row_is_zero(row));
    for &i in nodes {
        if i == hole {
            continue;
        }
        let n = cx.node(i);
        let w = usize::from(n.width);
        if w == 0 || w > usize::from(MAX_BITS) {
            return None;
        }
        for c in n.children() {
            out.entry(c)
                .or_insert_with(|| vec![ZERO_ROW; usize::from(cx.wid(c))]);
        }
        if !n.children().any(|c| dep(&out[&c])) {
            out.insert(i, vec![ZERO_ROW; w]);
            continue;
        }
        let rows = match n.op {
            OpCode::Xor => (0..w)
                .map(|k| row_xor(&out[&n.a][k], &out[&n.b][k]))
                .collect(),
            OpCode::Add | OpCode::Sub if w == 1 => vec![row_xor(&out[&n.a][0], &out[&n.b][0])],
            OpCode::Not | OpCode::Neg | OpCode::Bswap | OpCode::BitRev => {
                apply_un_rows(n.op, &out[&n.a], w)?
            }
            OpCode::And | OpCode::Or => {
                let clear = n.op == OpCode::Or;
                let (v, m) = if !dep(&out[&n.b]) {
                    (&out[&n.a], cx.const_val(n.b)?)
                } else if !dep(&out[&n.a]) {
                    (&out[&n.b], cx.const_val(n.a)?)
                } else {
                    return None;
                };
                mask_rows(v, &m, clear)
            }
            OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR => {
                if dep(&out[&n.b]) {
                    return None;
                }
                let cnt = cx.const_val(n.b)?;
                apply_shift_rows(n.op, &out[&n.a], &cnt, w)?
            }
            OpCode::Extract => {
                let lo = n.b as usize;
                out[&n.a][lo..lo + w].to_vec()
            }
            OpCode::Zext => {
                let mut v = out[&n.a].clone();
                v.resize(w, ZERO_ROW);
                v
            }
            OpCode::Sext => {
                let a = &out[&n.a];
                let sign = *a.last()?;
                let mut v = a.clone();
                v.resize(w, sign);
                v
            }
            OpCode::Concat => {
                let mut v = out[&n.b].clone();
                v.extend_from_slice(&out[&n.a]);
                v
            }
            _ => return None,
        };
        out.insert(i, rows);
    }
    Some(out)
}

/// Multi-atom GF(2)-affine decomposition of a root node `f(x_0, ..., x_{K-1}) = konst ⊕ ⊕_m M_m·x_m`.
pub(crate) struct Affine {
    /// Output value when every atom in `atoms` is zero.
    pub(crate) konst: BitVec,
    /// Per-atom matrix (`W_out` rows over the bits of `atoms[m]`), or `None` when the root is
    /// independent of `atoms[m]`.
    pub(crate) mats: Vec<Option<Rows>>,
}

/// Computes the exact GF(2)-affine decomposition of `nodes.last()` over `atoms` (`1..=512` bits
/// each), where `nodes` is in topological order and every child outside `nodes` is either in
/// `atoms` or a constant.
pub(crate) fn affine(cx: &Context, atoms: &[u32], nodes: &[u32]) -> Option<Affine> {
    let k_atoms = atoms.len();
    if k_atoms == 0 || nodes.is_empty() {
        return None;
    }
    for &a in atoms {
        let wa = cx.wid(a);
        if wa == 0 || wa > MAX_BITS {
            return None;
        }
    }
    let mut vals: IdMap<u32, BitVec> = IdMap::default();
    let mut mats: IdMap<u32, Vec<Option<Rows>>> = IdMap::default();
    for (idx, &a) in atoms.iter().enumerate() {
        vals.insert(a, BitVec::zero(cx.width_of(a)));
        let mut entry = vec![None; k_atoms];
        entry[idx] = Some(identity_rows(usize::from(cx.wid(a))));
        mats.insert(a, entry);
    }
    for &i in nodes {
        if mats.contains_key(&i) {
            continue;
        }
        let n = cx.node(i);
        let w = usize::from(n.width);
        if w == 0 || w > usize::from(MAX_BITS) {
            return None;
        }
        for c in n.children() {
            if mats.contains_key(&c) {
                continue;
            }
            let cv = cx.const_val(c)?;
            vals.insert(c, cv);
            mats.insert(c, vec![None; k_atoms]);
        }
        let kv = cx.eval_node(i, |c| vals[&c], |_, _| None).ok()?;
        let has_dep = |c: u32| mats[&c].iter().any(Option::is_some);
        if !n.children().any(has_dep) {
            vals.insert(i, kv);
            mats.insert(i, vec![None; k_atoms]);
            continue;
        }
        let mut cur: Vec<Option<Rows>> = vec![None; k_atoms];
        match n.op {
            OpCode::Xor => {
                let (ma, mb) = (&mats[&n.a], &mats[&n.b]);
                for m in 0..k_atoms {
                    cur[m] = match (&ma[m], &mb[m]) {
                        (None, None) => None,
                        (Some(ra), None) => Some(ra.clone()),
                        (None, Some(rb)) => Some(rb.clone()),
                        (Some(ra), Some(rb)) => {
                            let xored: Rows = (0..w).map(|b| row_xor(&ra[b], &rb[b])).collect();
                            xored.iter().any(|r| !row_is_zero(r)).then_some(xored)
                        }
                    };
                }
            }
            OpCode::Add | OpCode::Sub if w == 1 => {
                let (ma, mb) = (&mats[&n.a], &mats[&n.b]);
                for m in 0..k_atoms {
                    cur[m] = match (&ma[m], &mb[m]) {
                        (None, None) => None,
                        (Some(ra), None) => Some(ra.clone()),
                        (None, Some(rb)) => Some(rb.clone()),
                        (Some(ra), Some(rb)) => {
                            let r = row_xor(&ra[0], &rb[0]);
                            (!row_is_zero(&r)).then(|| vec![r])
                        }
                    };
                }
            }
            OpCode::Not | OpCode::Neg | OpCode::Bswap | OpCode::BitRev => {
                let ma = &mats[&n.a];
                for m in 0..k_atoms {
                    if let Some(ra) = &ma[m] {
                        cur[m] = Some(apply_un_rows(n.op, ra, w)?);
                    }
                }
            }
            OpCode::And | OpCode::Or => {
                let clear = n.op == OpCode::Or;
                let (mv, mask) = if !has_dep(n.b) {
                    (&mats[&n.a], cx.const_val(n.b)?)
                } else if !has_dep(n.a) {
                    (&mats[&n.b], cx.const_val(n.a)?)
                } else {
                    return None;
                };
                for m in 0..k_atoms {
                    if let Some(ra) = &mv[m] {
                        let masked = mask_rows(ra, &mask, clear);
                        if masked.iter().any(|r| !row_is_zero(r)) {
                            cur[m] = Some(masked);
                        }
                    }
                }
            }
            OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR => {
                if has_dep(n.b) {
                    return None;
                }
                let cnt = cx.const_val(n.b)?;
                let ma = &mats[&n.a];
                for m in 0..k_atoms {
                    if let Some(ra) = &ma[m] {
                        let shifted = apply_shift_rows(n.op, ra, &cnt, w)?;
                        if shifted.iter().any(|r| !row_is_zero(r)) {
                            cur[m] = Some(shifted);
                        }
                    }
                }
            }
            OpCode::Extract => {
                let lo = n.b as usize;
                let ma = &mats[&n.a];
                for m in 0..k_atoms {
                    if let Some(ra) = &ma[m] {
                        let slice = ra[lo..lo + w].to_vec();
                        if slice.iter().any(|r| !row_is_zero(r)) {
                            cur[m] = Some(slice);
                        }
                    }
                }
            }
            OpCode::Zext => {
                let ma = &mats[&n.a];
                for m in 0..k_atoms {
                    if let Some(ra) = &ma[m] {
                        let mut v = ra.clone();
                        v.resize(w, ZERO_ROW);
                        cur[m] = Some(v);
                    }
                }
            }
            OpCode::Sext => {
                let ma = &mats[&n.a];
                for m in 0..k_atoms {
                    if let Some(ra) = &ma[m] {
                        let sign = *ra.last()?;
                        let mut v = ra.clone();
                        v.resize(w, sign);
                        cur[m] = Some(v);
                    }
                }
            }
            OpCode::Concat => {
                let (mhi, mlo) = (&mats[&n.a], &mats[&n.b]);
                let whi = usize::from(cx.wid(n.a));
                let wlo = usize::from(cx.wid(n.b));
                for m in 0..k_atoms {
                    if mhi[m].is_none() && mlo[m].is_none() {
                        continue;
                    }
                    let mut v = mlo[m].clone().unwrap_or_else(|| vec![ZERO_ROW; wlo]);
                    match &mhi[m] {
                        Some(rhi) => v.extend_from_slice(rhi),
                        None => v.resize(wlo + whi, ZERO_ROW),
                    }
                    if v.iter().any(|r| !row_is_zero(r)) {
                        cur[m] = Some(v);
                    }
                }
            }
            _ => return None,
        }
        vals.insert(i, kv);
        mats.insert(i, cur);
    }
    let root = *nodes.last()?;
    Some(Affine {
        konst: vals.remove(&root)?,
        mats: mats.remove(&root)?,
    })
}

/// Whether `rows` has column rank `wv` (`1 <= wv <= 512`).
pub(crate) fn full_rank(rows: &[Row], wv: u32) -> bool {
    let wv = wv as usize;
    if wv == 0 || wv > usize::from(MAX_BITS) || rows.len() < wv {
        return false;
    }
    let mut basis: Vec<Option<Row>> = vec![None; wv];
    let mut rank = 0usize;
    for &(mut r) in rows {
        while let Some(p) = row_lead(&r) {
            if p >= wv {
                return false;
            }
            match &basis[p] {
                Some(b) => row_xor_assign(&mut r, b),
                None => {
                    basis[p] = Some(r);
                    rank += 1;
                    if rank == wv {
                        return true;
                    }
                    break;
                }
            }
        }
    }
    rank == wv
}

/// Solves `rows · x = y` over GF(2) for a `wv`-bit `x` (`1 <= wv <= 512`): `Some(Some(x))` for
/// the unique solution, `Some(None)` if inconsistent, `None` if underdetermined.
pub(crate) fn solve(rows: &[Row], y: &[bool], wv: u32) -> Option<Option<Row>> {
    let wv = wv as usize;
    if wv == 0 || wv > usize::from(MAX_BITS) || rows.len() != y.len() {
        return None;
    }
    let mut basis: Vec<Option<(Row, bool)>> = vec![None; wv];
    let mut rank = 0usize;
    for (&r_in, &rhs_in) in rows.iter().zip(y) {
        let (mut r, mut rhs) = (r_in, rhs_in);
        while let Some(p) = row_lead(&r) {
            if p >= wv {
                return None;
            }
            match &basis[p] {
                Some((b, by)) => {
                    row_xor_assign(&mut r, b);
                    rhs ^= *by;
                }
                None => {
                    basis[p] = Some((r, rhs));
                    rank += 1;
                    rhs = false;
                    break;
                }
            }
        }
        if rhs {
            return Some(None);
        }
    }
    if rank < wv {
        return None;
    }
    let mut x = ZERO_ROW;
    for p in (0..wv).rev() {
        let (b, by) = basis[p].as_ref()?;
        let parity = (0..8).fold(0u32, |acc, w| acc ^ (b[w] & x[w]).count_ones()) & 1 != 0;
        if *by ^ parity {
            row_set(&mut x, p);
        }
    }
    Some(Some(x))
}

#[cfg(test)]
pub(crate) fn rank(rows: &[Row]) -> u32 {
    let mut basis: Vec<Option<Row>> = vec![None; usize::from(MAX_BITS)];
    let mut rnk = 0u32;
    for &(mut r) in rows {
        while let Some(p) = row_lead(&r) {
            match &basis[p] {
                Some(b) => row_xor_assign(&mut r, b),
                None => {
                    basis[p] = Some(r);
                    rnk += 1;
                    break;
                }
            }
        }
    }
    rnk
}
