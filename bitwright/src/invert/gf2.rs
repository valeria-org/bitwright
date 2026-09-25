//! Affine maps over GF(2): a region built from `^`, `~`, `&` and `|` with constants, shifts and
//! rotations by constants, byte swaps and bit reversals, extracts, extensions and `concat` is,
//! bit by bit, the xor of some bits of its hole and a constant: `f(x) = M·x ⊕ f(0)` with `M` a
//! matrix over GF(2). It is injective exactly when `M` has full column rank, whatever the
//! dependencies look like: `x ^ rotl(x, a) ^ rotl(x, b)` reads every bit of `x` three times
//! (no bit has a single pivot), yet it is a bijection at every power-of-two width (the
//! polynomial `1 + t^a + t^b` has an odd number of terms, so it is prime to `t^W + 1 =
//! (t + 1)^W`). A preimage is `M⁻¹·(c ⊕ f(0))`, found by elimination and checked by evaluation.

use crate::expr::{Context, OpCode};
use crate::hash::IdMap;

/// Per bit of a node, the hole bits it is the xor of.
pub(crate) type Rows = Vec<u128>;

/// The rows of every node of `nodes` (ascending, each operand before its users) as an affine
/// function of `hole` (at most 128 bits): `None` when a node is not affine in the hole with its
/// other operands fixed (a product, a sum, a mask that is not a constant, a shift by a count
/// that is not one).
pub(crate) fn rows(cx: &Context, hole: u32, nodes: &[u32]) -> Option<IdMap<u32, Rows>> {
    let wv = cx.wid(hole);
    if wv > 128 {
        return None;
    }
    let mut map: IdMap<u32, Rows> = IdMap::default();
    map.insert(hole, (0..wv).map(|k| 1u128 << k).collect());
    let konst = |i: u32| cx.const_val(i);
    for &i in nodes {
        // The hole, and parameters (constants) listed among the nodes.
        if i == hole || cx.const_val(i).is_some() {
            continue;
        }
        let n = cx.node(i);
        let w = usize::from(n.width);
        let get = |map: &IdMap<u32, Rows>, c: u32| -> Rows {
            map.get(&c)
                .cloned()
                .unwrap_or_else(|| vec![0; usize::from(cx.wid(c))])
        };
        let dep = |c: u32| map.contains_key(&c);
        let count = |c: u32| konst(c).and_then(|v| v.to_u64());
        let r: Rows = match n.op {
            OpCode::Xor => {
                let (a, b) = (get(&map, n.a), get(&map, n.b));
                a.iter().zip(&b).map(|(x, y)| x ^ y).collect()
            }
            OpCode::Not => get(&map, n.a),
            OpCode::And | OpCode::Or => {
                // One operand varies, the other is a constant mask.
                let (v, k) = match (dep(n.a), dep(n.b)) {
                    (true, false) => (n.a, n.b),
                    (false, true) => (n.b, n.a),
                    _ => return None,
                };
                let m = konst(k)?;
                let a = get(&map, v);
                let keep = |bit: bool| if n.op == OpCode::And { bit } else { !bit };
                (0..w)
                    .map(|k| {
                        if keep(m.bit(k as u16) == Some(true)) {
                            a[k]
                        } else {
                            0
                        }
                    })
                    .collect()
            }
            OpCode::Shl | OpCode::LShr | OpCode::AShr | OpCode::RotL | OpCode::RotR => {
                if dep(n.b) {
                    return None;
                }
                let s = count(n.b)?;
                let a = get(&map, n.a);
                (0..w)
                    .map(|k| {
                        let k = k as u64;
                        let w = w as u64;
                        let src = match n.op {
                            OpCode::Shl => k.checked_sub(s),
                            OpCode::LShr => k.checked_add(s).filter(|&j| j < w),
                            OpCode::AShr => Some(k.saturating_add(s).min(w - 1)),
                            OpCode::RotL => Some((k + w - s % w) % w),
                            _ => Some((k + s % w) % w),
                        };
                        src.map_or(0, |j| a[j as usize])
                    })
                    .collect()
            }
            OpCode::Bswap => {
                let a = get(&map, n.a);
                (0..w).map(|k| a[(w / 8 - 1 - k / 8) * 8 + k % 8]).collect()
            }
            OpCode::BitRev => {
                let a = get(&map, n.a);
                (0..w).map(|k| a[w - 1 - k]).collect()
            }
            OpCode::Extract => {
                let a = get(&map, n.a);
                let lo = n.b as usize;
                (0..w).map(|k| a[lo + k]).collect()
            }
            OpCode::Zext => {
                let mut a = get(&map, n.a);
                a.resize(w, 0);
                a
            }
            OpCode::Sext => {
                let mut a = get(&map, n.a);
                let top = *a.last()?;
                a.resize(w, top);
                a
            }
            OpCode::Concat => {
                let (hi, mut lo) = (get(&map, n.a), get(&map, n.b));
                lo.extend(hi);
                lo
            }
            _ => return None,
        };
        map.insert(i, r);
    }
    Some(map)
}

/// The rank of the rows over GF(2).
pub(crate) fn rank(rows: &[u128]) -> u32 {
    let mut basis: Vec<u128> = Vec::new();
    for &r in rows {
        let mut v = r;
        for &b in &basis {
            v = v.min(v ^ b);
        }
        if v != 0 {
            basis.push(v);
            // Keep the basis reduced by leading bit (highest set bit first).
            basis.sort_unstable_by(|a, b| b.cmp(a));
        }
    }
    basis.len() as u32
}

/// A solution `x` of `M·x = y` (rows of `M` with the bits of `y`), when `M` has full column
/// rank `wv`: `Some(Some(x))`; `Some(None)` when no `x` solves it; `None` when `M` is not of
/// full rank.
pub(crate) fn solve(rows: &[u128], y: &[bool], wv: u32) -> Option<Option<u128>> {
    // Gaussian elimination on the augmented rows (bit `wv` is the right-hand side).
    let mut m: Vec<(u128, bool)> = rows.iter().copied().zip(y.iter().copied()).collect();
    let mut pivots: Vec<(u32, usize)> = Vec::new();
    let mut row = 0;
    for col in 0..wv {
        let bit = 1u128 << col;
        let p = (row..m.len()).find(|&i| m[i].0 & bit != 0)?;
        m.swap(row, p);
        let (pr, pv) = m[row];
        for (i, e) in m.iter_mut().enumerate() {
            if i != row && e.0 & bit != 0 {
                e.0 ^= pr;
                e.1 ^= pv;
            }
        }
        pivots.push((col, row));
        row += 1;
    }
    // Rows left over are all zero: consistent only if their right-hand sides are 0.
    if m[row..].iter().any(|&(r, v)| r == 0 && v) {
        return Some(None);
    }
    let mut x = 0u128;
    for (col, r) in pivots {
        if m[r].1 {
            x |= 1u128 << col;
        }
    }
    Some(Some(x))
}
