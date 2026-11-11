//! The compares pass: boolean combinations (`& | ^ ~` on 1-bit values) of comparisons.
//!
//! *Same operand pair.* Two values `x`, `y` stand in exactly one of five relations: equal, or
//! one of {less, greater} unsigned × {less, greater} signed. Every predicate over `(x, y)` (in
//! either operand order) is a set of those relations, and `& | ^ ~` are set operations, so any
//! combination is a set; it is emitted when that set is one predicate, true or false. At
//! W = 1 only three relations can occur (`0 <u 1` but `0 >s -1`), which is accounted for.
//!
//! *One operand against constants.* A comparison of `x` with a constant is a set of values of
//! `x`: a union of unsigned intervals (signed comparisons split at the sign boundary).
//! Combinations are exact interval-set operations, emitted when the set is empty, everything, a
//! single comparison, or one wrapped interval `[lo, hi]` as the range check `x - lo <=u hi - lo`.
//! A comparison of `t + k`, `k - t`, `-t`, `~t`, `t ^ smin`, `t & (2^j - 1)`, `t | smin` or an
//! extension of `t` is one of `t` as well (the values of `t` such a map sends into an interval
//! set are an interval set), so comparisons of two such terms combine on the nearest term both
//! are functions of: a range check `x - 4 <=u 5` with `x == 12`, or the floating-point
//! classification tests, which compare `x & ~sign` or `x ^ sign`, on `x`.
//!
//! *Floats.* A floating-point comparison with a constant is a set of encodings of its other
//! operand (in the order `key` puts encodings in, the values below a constant are an interval),
//! so it combines with the rest; a set that is one comparison of that format with a constant,
//! or its negation, can be emitted as that. Two floats `x`, `y` stand in one of six relations:
//! equal, less, greater, or unordered because `x`, `y` or both are NaN. Every comparison of
//! the two and the NaN test of either is a set of those.
//!
//! All of it is exact at every width; the result replaces the node only when smaller.

use core::cmp::Ordering;

use super::{Fin, PassKind, Runner, Step, Stop, finish};
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::fp::node::{Desc, Kind};
use crate::fp::{FpFormat, FpOp};
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::{BitVec, Width};

/// The most intervals an interval set keeps before its node is treated as opaque.
const MAX_INTERVALS: usize = 8;

/// The longest chain of terms `peel` follows.
const MAX_PEEL: usize = 6;

// ----- relation sets ------------------------------------------------------------------------------

/// Relations of the first operand to the second: bit 0 equal, bit 1 (<u, <s), bit 2 (<u, >s),
/// bit 3 (>u, <s), bit 4 (>u, >s).
const ALL: u8 = 0b11111;

fn pred_set(op: CmpOp) -> u8 {
    match op {
        CmpOp::Eq => 0b00001,
        CmpOp::Ne => 0b11110,
        CmpOp::Ult => 0b00110,
        CmpOp::Ule => 0b00111,
        CmpOp::Slt => 0b01010,
        CmpOp::Sle => 0b01011,
    }
}

/// The same set with the operands exchanged.
fn swap_set(s: u8) -> u8 {
    let bit = |k: u8| (s >> k) & 1;
    bit(0) | (bit(4) << 1) | (bit(3) << 2) | (bit(2) << 3) | (bit(1) << 4)
}

/// The relations that can occur at width `w`.
fn realizable(w: u16) -> u8 {
    if w == 1 { 0b01101 } else { ALL }
}

/// Relations of float `x` to float `y`: bit 0 equal, bit 1 less, bit 2 greater, bit 3 `x` NaN
/// and `y` not, bit 4 `y` NaN and `x` not, bit 5 both NaN. All six occur in every format.
const FLOAT_ALL: u8 = 0b111111;

/// `x` is a NaN.
const X_NAN: u8 = 0b101000;

/// `y` is a NaN.
const Y_NAN: u8 = 0b110000;

fn float_pred_set(k: Kind) -> u8 {
    match k {
        Kind::Eq => 0b001,
        Kind::Lt => 0b010,
        _ => 0b011,
    }
}

/// The same set with the floats exchanged.
fn float_swap(s: u8) -> u8 {
    let bit = |k: u8| (s >> k) & 1;
    bit(0) | (bit(2) << 1) | (bit(1) << 2) | (bit(4) << 3) | (bit(3) << 4) | (bit(5) << 5)
}

// ----- interval sets ------------------------------------------------------------------------------

/// Sorted, disjoint, non-adjacent unsigned intervals.
type Set = Vec<(BitVec, BitVec)>;

fn one(w: Width) -> BitVec {
    BitVec::one(w)
}

fn inc(v: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Add, v, &one(v.width()))
}

fn dec(v: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Sub, v, &one(v.width()))
}

fn add(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Add, a, b)
}

fn sub(a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(BinOp::Sub, a, b)
}

fn ult(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Ult, a, b)
}

fn ule(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Ule, a, b)
}

fn full(w: Width) -> Set {
    vec![(BitVec::zero(w), BitVec::ones(w))]
}

fn complement(s: &Set, w: Width) -> Set {
    let mut out = Vec::new();
    let mut next = Some(BitVec::zero(w));
    for (lo, hi) in s {
        if let Some(n) = next
            && ult(&n, lo)
        {
            out.push((n, dec(lo)));
        }
        next = if hi.is_ones() { None } else { Some(inc(hi)) };
    }
    if let Some(n) = next {
        out.push((n, BitVec::ones(w)));
    }
    out
}

fn intersect(a: &Set, b: &Set) -> Set {
    let mut out = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        let lo = if ult(&a[i].0, &b[j].0) {
            b[j].0
        } else {
            a[i].0
        };
        let hi = if ult(&a[i].1, &b[j].1) {
            a[i].1
        } else {
            b[j].1
        };
        if ule(&lo, &hi) {
            out.push((lo, hi));
        }
        if ult(&a[i].1, &b[j].1) {
            i += 1;
        } else {
            j += 1;
        }
    }
    out
}

fn union(a: &Set, b: &Set, w: Width) -> Set {
    complement(&intersect(&complement(a, w), &complement(b, w)), w)
}

fn sym_diff(a: &Set, b: &Set, w: Width) -> Set {
    union(
        &intersect(a, &complement(b, w)),
        &intersect(&complement(a, w), b),
        w,
    )
}

/// The cyclic interval from `a` up to `b`: one interval, or two touching both ends.
fn push_cyclic(out: &mut Set, a: BitVec, b: BitVec) {
    if ule(&a, &b) {
        out.push((a, b));
    } else {
        let w = a.width();
        out.push((BitVec::zero(w), b));
        out.push((a, BitVec::ones(w)));
    }
}

/// Disjoint intervals in any order as a set: sorted, adjacent ones merged.
fn normalize(mut v: Set) -> Set {
    v.sort_by(|p, q| {
        if ult(&p.0, &q.0) {
            Ordering::Less
        } else if p.0 == q.0 {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    });
    let mut out: Set = Vec::with_capacity(v.len());
    for (lo, hi) in v {
        if let Some(last) = out.last_mut()
            && (last.1.is_ones() || ule(&lo, &inc(&last.1)))
        {
            if ult(&last.1, &hi) {
                last.1 = hi;
            }
            continue;
        }
        out.push((lo, hi));
    }
    out
}

/// The values `x` for which `x op c` holds.
fn interval_of(op: CmpOp, c: &BitVec, x_first: bool) -> Set {
    let w = c.width();
    let zero = BitVec::zero(w);
    let max = BitVec::ones(w);
    let smin = BitVec::smin(w);
    let smax = BitVec::smax(w);
    // A signed interval [a, b] (a <=s b) as unsigned intervals.
    let signed = |a: BitVec, b: BitVec| -> Set {
        if a.msb() == b.msb() {
            vec![(a, b)]
        } else {
            vec![(zero, b), (a, max)]
        }
    };
    match (op, x_first) {
        (CmpOp::Eq, _) => vec![(*c, *c)],
        (CmpOp::Ne, _) => complement(&vec![(*c, *c)], w),
        // x <u c / x <=u c
        (CmpOp::Ult, true) if c.is_zero() => Vec::new(),
        (CmpOp::Ult, true) => vec![(zero, dec(c))],
        (CmpOp::Ule, true) => vec![(zero, *c)],
        // c <u x / c <=u x
        (CmpOp::Ult, false) if c.is_ones() => Vec::new(),
        (CmpOp::Ult, false) => vec![(inc(c), max)],
        (CmpOp::Ule, false) => vec![(*c, max)],
        // x <s c / x <=s c
        (CmpOp::Slt, true) if *c == smin => Vec::new(),
        (CmpOp::Slt, true) => signed(smin, dec(c)),
        (CmpOp::Sle, true) => signed(smin, *c),
        // c <s x / c <=s x
        (CmpOp::Slt, false) if *c == smax => Vec::new(),
        (CmpOp::Slt, false) => signed(inc(c), smax),
        (CmpOp::Sle, false) => signed(*c, smax),
    }
}

// ----- terms that are functions of another -------------------------------------------------------

/// A function of one operand `t` under which the values of `t` sent into an interval set form
/// an interval set.
#[derive(Clone, Copy, Debug)]
enum Map {
    /// `t + k`.
    Shift(BitVec),
    /// `k - t`.
    Reflect(BitVec),
    /// `t & (2^j - 1)`, `0 < j < W`.
    Low(u16),
    /// `t | smin`.
    SetTop,
    /// Zero extension of `t`.
    Zext,
    /// Sign extension of `t`.
    Sext,
    /// The low bits of `t`, as a narrower value.
    Trunc,
}

/// The operand node `e` is a function of, and the function, if it is one of `Map`'s.
fn peel(cx: &Context, e: u32) -> Option<(u32, Map)> {
    let n = cx.node(e);
    let w = cx.width_of(e);
    match n.op {
        OpCode::Neg => return Some((n.a, Map::Reflect(BitVec::zero(w)))),
        OpCode::Not => return Some((n.a, Map::Reflect(BitVec::ones(w)))),
        OpCode::Zext => return Some((n.a, Map::Zext)),
        OpCode::Sext => return Some((n.a, Map::Sext)),
        OpCode::Extract if n.b == 0 => return Some((n.a, Map::Trunc)),
        OpCode::Add | OpCode::Sub | OpCode::Xor | OpCode::And | OpCode::Or => {}
        _ => return None,
    }
    let (t, k, k_first) = match (cx.const_val(n.a), cx.const_val(n.b)) {
        (None, Some(k)) => (n.a, k, false),
        (Some(k), None) => (n.b, k, true),
        _ => return None,
    };
    let smin = BitVec::smin(w);
    let map = match n.op {
        OpCode::Add => Map::Shift(k),
        OpCode::Sub if k_first => Map::Reflect(k),
        OpCode::Sub => Map::Shift(BitVec::un_unchecked(UnOp::Neg, &k)),
        OpCode::Xor if k == smin => Map::Shift(k),
        OpCode::Xor if k.is_ones() => Map::Reflect(k),
        OpCode::And
            if !k.is_zero()
                && !k.is_ones()
                && BitVec::bin_unchecked(BinOp::And, &k, &inc(&k)).is_zero() =>
        {
            let j = BitVec::un_unchecked(UnOp::Popcnt, &k).to_u64()?;
            Map::Low(u16::try_from(j).ok()?)
        }
        OpCode::Or if k == smin => Map::SetTop,
        _ => return None,
    };
    Some((t, map))
}

/// The values of `t` (width `tw`) that `m` sends into `s` (a set at width `w`), unless that
/// takes more than `MAX_INTERVALS` intervals.
fn preimage(m: Map, s: &Set, w: Width, tw: Width) -> Option<Set> {
    let mut out = Set::new();
    match m {
        Map::Shift(k) => {
            for (lo, hi) in s {
                push_cyclic(&mut out, sub(lo, &k), sub(hi, &k));
            }
        }
        Map::Reflect(k) => {
            for (lo, hi) in s {
                push_cyclic(&mut out, sub(&k, hi), sub(&k, lo));
            }
        }
        Map::Low(j) => {
            let step = BitVec::bin_unchecked(
                BinOp::Shl,
                &one(w),
                &BitVec::wrapping_from_u64(w, u64::from(j)),
            );
            let mask = dec(&step);
            let low = intersect(s, &vec![(BitVec::zero(w), mask)]);
            if low.is_empty() {
                return Some(out);
            }
            if low == [(BitVec::zero(w), mask)] {
                return Some(full(w));
            }
            // One copy of `low` for every value of the bits the mask clears.
            let copies = 1u64
                .checked_shl(u32::from(w.bits() - j))
                .filter(|&c| c.saturating_mul(low.len() as u64) <= MAX_INTERVALS as u64)?;
            let mut base = BitVec::zero(w);
            for _ in 0..copies {
                for (lo, hi) in &low {
                    out.push((add(lo, &base), add(hi, &base)));
                }
                base = add(&base, &step);
            }
        }
        Map::SetTop => {
            let smin = BitVec::smin(w);
            for (lo, hi) in intersect(s, &vec![(smin, BitVec::ones(w))]) {
                out.push((sub(&lo, &smin), sub(&hi, &smin)));
                out.push((lo, hi));
            }
        }
        Map::Zext | Map::Sext => {
            // The values an extension takes: every value of `t` below the sign boundary, and
            // for a sign extension the ones above it, as the top of the wide range.
            let pos = if matches!(m, Map::Zext) {
                BitVec::ones(tw)
            } else {
                BitVec::smax(tw)
            };
            let mut parts = vec![(BitVec::zero(w), pos.zext(w).ok()?)];
            if matches!(m, Map::Sext) {
                parts.push((BitVec::smin(tw).sext(w).ok()?, BitVec::ones(w)));
            }
            for (lo, hi) in intersect(s, &parts) {
                out.push((lo.trunc(tw).ok()?, hi.trunc(tw).ok()?));
            }
        }
        Map::Trunc => {
            if s.is_empty() {
                return Some(out);
            }
            if *s == full(w) {
                return Some(full(tw));
            }
            // One copy of `s` for every value of the bits the truncation drops.
            let copies = 1u64
                .checked_shl(u32::from(tw.bits() - w.bits()))
                .filter(|&c| c.saturating_mul(s.len() as u64) <= MAX_INTERVALS as u64)?;
            let step = BitVec::bin_unchecked(
                BinOp::Shl,
                &one(tw),
                &BitVec::wrapping_from_u64(tw, u64::from(w.bits())),
            );
            let mut base = BitVec::zero(tw);
            for _ in 0..copies {
                for (lo, hi) in s {
                    out.push((
                        add(&lo.zext(tw).ok()?, &base),
                        add(&hi.zext(tw).ok()?, &base),
                    ));
                }
                base = add(&base, &step);
            }
        }
    }
    let out = normalize(out);
    (out.len() <= MAX_INTERVALS).then_some(out)
}

/// `e` and the terms `peel` reaches from it, each `maps[i]` of the next.
fn chain(cx: &Context, e: u32) -> (Vec<u32>, Vec<Map>) {
    let (mut nodes, mut maps) = (vec![e], Vec::new());
    let mut cur = e;
    while maps.len() < MAX_PEEL
        && let Some((t, m)) = peel(cx, cur)
    {
        nodes.push(t);
        maps.push(m);
        cur = t;
    }
    (nodes, maps)
}

/// `s`, a set of values of `nodes[0]`, as a set of values of `nodes[k]`.
fn pull(cx: &Context, nodes: &[u32], maps: &[Map], k: usize, s: &Set) -> Option<Set> {
    let mut s = s.clone();
    for i in 0..k {
        s = preimage(
            maps[i],
            &s,
            cx.width_of(nodes[i]),
            cx.width_of(nodes[i + 1]),
        )?;
    }
    Some(s)
}

/// A set of values of `x` and one of `y` as sets of values of the nearest term both are
/// functions of.
fn common(cx: &Context, x: u32, s: &Set, y: u32, t: &Set) -> Option<(u32, Set, Set)> {
    if x == y {
        return Some((x, s.clone(), t.clone()));
    }
    let (xs, xm) = chain(cx, x);
    let (ys, ym) = chain(cx, y);
    let (i, j) = xs
        .iter()
        .enumerate()
        .find_map(|(i, n)| ys.iter().position(|m| m == n).map(|j| (i, j)))?;
    Some((xs[i], pull(cx, &xs, &xm, i, s)?, pull(cx, &ys, &ym, j, t)?))
}

// ----- floating-point encodings -------------------------------------------------------------------

/// The keys of the encodings in `s`. Keys put encodings in the order of the values they stand
/// for: a positive encoding `e` is at `e + smin`, a negative one at `~e`. So `−∞ … −0, +0 … +∞`
/// is one interval of keys, with `−0` and `+0` adjacent, the negative NaNs below it and the
/// positive ones above.
fn key_set(s: &Set, w: Width) -> Set {
    let (smin, smax) = (BitVec::smin(w), BitVec::smax(w));
    let mut out = Set::new();
    for (lo, hi) in intersect(s, &vec![(BitVec::zero(w), smax)]) {
        out.push((add(&lo, &smin), add(&hi, &smin)));
    }
    for (lo, hi) in intersect(s, &vec![(smin, BitVec::ones(w))]) {
        out.push((
            BitVec::un_unchecked(UnOp::Not, &hi),
            BitVec::un_unchecked(UnOp::Not, &lo),
        ));
    }
    normalize(out)
}

/// The encodings at the keys in `k`.
fn unkey_set(k: &Set, w: Width) -> Set {
    let (smin, smax) = (BitVec::smin(w), BitVec::smax(w));
    let mut out = Set::new();
    for (lo, hi) in intersect(k, &vec![(smin, BitVec::ones(w))]) {
        out.push((sub(&lo, &smin), sub(&hi, &smin)));
    }
    for (lo, hi) in intersect(k, &vec![(BitVec::zero(w), smax)]) {
        out.push((
            BitVec::un_unchecked(UnOp::Not, &hi),
            BitVec::un_unchecked(UnOp::Not, &lo),
        ));
    }
    normalize(out)
}

fn key(e: &BitVec) -> BitVec {
    if e.msb() {
        BitVec::un_unchecked(UnOp::Not, e)
    } else {
        add(e, &BitVec::smin(e.width()))
    }
}

fn unkey(k: &BitVec) -> BitVec {
    if k.msb() {
        sub(k, &BitVec::smin(k.width()))
    } else {
        BitVec::un_unchecked(UnOp::Not, k)
    }
}

/// The keys of −∞ and +∞ in `f`, the ends of the non-NaN values.
fn key_ends(f: FpFormat) -> (BitVec, BitVec) {
    (key(&f.inf(true)), key(&f.inf(false)))
}

/// The keys of −0 and +0.
fn key_zeros(w: Width) -> (BitVec, BitVec) {
    (BitVec::smax(w), BitVec::smin(w))
}

/// The encodings of `f` that are not NaNs.
fn non_nan(f: FpFormat) -> Set {
    let (lo, hi) = key_ends(f);
    unkey_set(&vec![(lo, hi)], f.width())
}

/// The encodings `x` of `f` for which `x op c` holds (`c op x` unless `x_first`), `op` one of
/// `Eq`, `Lt`, `Le`.
fn float_interval(f: FpFormat, op: Kind, c: &BitVec, x_first: bool) -> Set {
    let w = f.width();
    let (kninf, kpinf) = key_ends(f);
    let kc = key(c);
    if ult(&kc, &kninf) || ult(&kpinf, &kc) {
        // A NaN compares false.
        return Vec::new();
    }
    // The keys of the values equal to c: both zeros for a zero.
    let (klo, khi) = if BitVec::bin_unchecked(BinOp::And, c, &BitVec::smax(w)).is_zero() {
        key_zeros(w)
    } else {
        (kc, kc)
    };
    let (a, b) = match (op, x_first) {
        (Kind::Eq, _) => (klo, khi),
        (Kind::Lt, true) if klo == kninf => return Vec::new(),
        (Kind::Lt, true) => (kninf, dec(&klo)),
        (Kind::Lt, false) if khi == kpinf => return Vec::new(),
        (Kind::Lt, false) => (inc(&khi), kpinf),
        (_, true) => (kninf, khi),
        (_, false) => (klo, kpinf),
    };
    unkey_set(&vec![(a, b)], w)
}

/// The number of trailing zero bits of the magnitude of the float `e` (a zero has them all):
/// the roundest constant is the one to print.
fn roundness(e: &BitVec) -> u64 {
    let m = BitVec::bin_unchecked(BinOp::And, e, &BitVec::smax(e.width()));
    BitVec::un_unchecked(UnOp::Ctz, &m).to_u64().unwrap_or(0)
}

/// A comparison of floats of `f` that holds exactly for the encodings `x` in `s`: `x op c`, or
/// `c op x` if the flag is false, or `x == x` (no constant) for every non-NaN.
fn float_form(f: FpFormat, s: &Set) -> Option<(Kind, Option<BitVec>, bool)> {
    let w = f.width();
    let keys = key_set(s, w);
    let [(a, b)] = keys.as_slice() else {
        return None;
    };
    let (kninf, kpinf) = key_ends(f);
    let (kmz, kpz) = key_zeros(w);
    if ult(a, &kninf) || ult(&kpinf, b) {
        return None;
    }
    // A zero constant is written +0.
    let value = |k: &BitVec| {
        let e = unkey(k);
        if e == BitVec::smin(w) {
            BitVec::zero(w)
        } else {
            e
        }
    };
    // Of `x <= u` and `x < v` (or `u <= x`, `v < x`), the one with the rounder constant.
    let pick = |u: BitVec, v: BitVec, x_first: bool| {
        Some(if roundness(&v) > roundness(&u) {
            (Kind::Lt, Some(v), x_first)
        } else {
            (Kind::Le, Some(u), x_first)
        })
    };
    match (*a == kninf, *b == kpinf) {
        (true, true) => Some((Kind::Eq, None, true)),
        // Holding at one zero and not the other is no comparison.
        (true, false) if *b == kmz => None,
        (true, false) => pick(value(b), value(&inc(b)), true),
        (false, true) if *a == kpz => None,
        (false, true) => pick(value(a), value(&dec(a)), false),
        (false, false) if *a == kmz && *b == kpz => Some((Kind::Eq, Some(BitVec::zero(w)), true)),
        (false, false) => None,
    }
}

// ----- per-node descriptions ------------------------------------------------------------------------

/// What a 1-bit node says, if it is in a fragment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Info {
    /// A constant truth value.
    Const(bool),
    /// A set of relations of `x` to `y` (`x < y` by index).
    Pair(u32, u32, u8),
    /// A set of relations of the floats `x` and `y` of a format (`x < y` by index).
    Floats(u32, u32, FpFormat, u8),
    /// A set of values of `x`, and a float format of `x`'s width some of the comparisons were
    /// in (the set may be one comparison in it).
    Values(u32, Set, Option<FpFormat>),
    /// Neither (or over a cap).
    Opaque,
}

fn boolean_op(op: OpCode) -> bool {
    matches!(op, OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not)
}

fn float_cmp(op: OpCode) -> bool {
    matches!(op, OpCode::FEq | OpCode::FLt | OpCode::FLe)
}

fn leaf(cx: &Context, i: u32) -> Info {
    let n = cx.node(i);
    if let Some(v) = cx.const_val(i) {
        return if n.width == 1 {
            Info::Const(!v.is_zero())
        } else {
            Info::Opaque
        };
    }
    if float_cmp(n.op) {
        return float_leaf(cx, i);
    }
    let Some(op) = n.op.as_cmp() else {
        return Info::Opaque;
    };
    match (cx.const_val(n.a), cx.const_val(n.b)) {
        (Some(_), Some(_)) => Info::Opaque,
        (None, Some(c)) => Info::Values(n.a, interval_of(op, &c, true), None),
        (Some(c), None) => Info::Values(n.b, interval_of(op, &c, false), None),
        (None, None) if n.a == n.b => Info::Opaque,
        (None, None) if n.a < n.b => Info::Pair(n.a, n.b, pred_set(op)),
        (None, None) => Info::Pair(n.b, n.a, swap_set(pred_set(op))),
    }
}

fn float_leaf(cx: &Context, i: u32) -> Info {
    let n = cx.node(i);
    let Some(Desc { op, format: f }) = cx.fp_desc(i) else {
        return Info::Opaque;
    };
    let kind = match op {
        FpOp::Eq => Kind::Eq,
        FpOp::Lt => Kind::Lt,
        FpOp::Le => Kind::Le,
        _ => return Info::Opaque,
    };
    match (cx.const_val(n.a), cx.const_val(n.b)) {
        (Some(_), Some(_)) => Info::Opaque,
        (None, Some(c)) => Info::Values(n.a, float_interval(f, kind, &c, true), Some(f)),
        (Some(c), None) => Info::Values(n.b, float_interval(f, kind, &c, false), Some(f)),
        // `x < x` never holds, `x == x` and `x <= x` unless x is a NaN.
        (None, None) if n.a == n.b => {
            let s = if kind == Kind::Lt {
                Vec::new()
            } else {
                non_nan(f)
            };
            Info::Values(n.a, s, Some(f))
        }
        (None, None) if n.a < n.b => Info::Floats(n.a, n.b, f, float_pred_set(kind)),
        (None, None) => Info::Floats(n.b, n.a, f, float_swap(float_pred_set(kind))),
    }
}

/// A set of values of `z` as a set of relations of floats `x`, `y` of `f`, if `z` is one of
/// them (or a function of one) and the set is a NaN test.
fn nan_relations(cx: &Context, x: u32, y: u32, f: FpFormat, z: u32, s: &Set) -> Option<u8> {
    let (zs, zm) = chain(cx, z);
    let (k, nan) = [(x, X_NAN), (y, Y_NAN)]
        .into_iter()
        .find_map(|(v, nan)| zs.iter().position(|&n| n == v).map(|k| (k, nan)))?;
    let s = pull(cx, &zs, &zm, k, s)?;
    let w = f.width();
    let numbers = non_nan(f);
    if s.is_empty() {
        Some(0)
    } else if s == full(w) {
        Some(FLOAT_ALL)
    } else if s == numbers {
        Some(!nan & FLOAT_ALL)
    } else if s == complement(&numbers, w) {
        Some(nan)
    } else {
        None
    }
}

/// The format whose NaN encodings at width `w` are exactly `s`, if there is one.
fn nan_format(s: &Set, w: Width) -> Option<FpFormat> {
    let [(a, _), _] = s.as_slice() else {
        return None;
    };
    // The positive NaNs start just above +∞, whose encoding is all exponent bits.
    let inf = dec(a);
    let eb = u32::try_from(BitVec::un_unchecked(UnOp::Popcnt, &inf).to_u64()?).ok()?;
    let f = FpFormat::new(eb, u32::from(w.bits()).checked_sub(eb)?).ok()?;
    (f.inf(false) == inf && complement(&non_nan(f), w) == *s).then_some(f)
}

/// The float the set `s` of values of `z` tests for being a NaN (`true`) or not (`false`), and
/// its format: `z` itself, or the nearest term `z` is a function of for which the set is one.
fn nan_test(cx: &Context, z: u32, s: &Set) -> Option<(u32, FpFormat, bool)> {
    let (zs, zm) = chain(cx, z);
    for k in 0..zs.len() {
        let t = pull(cx, &zs, &zm, k, s)?;
        let w = cx.width_of(zs[k]);
        if let Some(f) = nan_format(&t, w) {
            return Some((zs[k], f, true));
        }
        if let Some(f) = nan_format(&complement(&t, w), w) {
            return Some((zs[k], f, false));
        }
    }
    None
}

/// NaN tests of two different floats of one format as sets of relations of the two: the floats
/// (by index) and the format, then each test's set.
fn nan_pair(
    cx: &Context,
    x: u32,
    s: &Set,
    y: u32,
    t: &Set,
) -> Option<(u32, u32, FpFormat, u8, u8)> {
    let (a, f, p) = nan_test(cx, x, s)?;
    let (b, g, q) = nan_test(cx, y, t)?;
    if a == b || f != g {
        return None;
    }
    let (lo, hi) = (a.min(b), a.max(b));
    let rel = |v: u32, nan: bool| {
        let bits = if v == lo { X_NAN } else { Y_NAN };
        if nan { bits } else { !bits & FLOAT_ALL }
    };
    Some((lo, hi, f, rel(a, p), rel(b, q)))
}

/// The float format hint of a combination on `base`: one of the operands', if its width is
/// still the base's.
fn hint(cx: &Context, base: u32, a: Option<FpFormat>, b: Option<FpFormat>) -> Option<FpFormat> {
    let w = cx.width_of(base);
    a.into_iter().chain(b).find(|f| f.width() == w)
}

/// Combines operand descriptions under a boolean operator (`None` operand for `Not`).
fn combine(cx: &Context, op: OpCode, a: &Info, b: Option<&Info>) -> Info {
    // A constant becomes the neutral description of the other side's fragment.
    let lift = |c: bool, other: &Info| -> Info {
        match other {
            Info::Pair(x, y, _) => Info::Pair(*x, *y, if c { ALL } else { 0 }),
            Info::Floats(x, y, f, _) => Info::Floats(*x, *y, *f, if c { FLOAT_ALL } else { 0 }),
            Info::Values(x, _, h) => {
                let w = cx.width_of(*x);
                Info::Values(*x, if c { full(w) } else { Vec::new() }, *h)
            }
            _ => Info::Const(c),
        }
    };
    let (a, b) = match (a, b) {
        (Info::Const(c), Some(o)) => (lift(*c, o), Some(o.clone())),
        (o, Some(Info::Const(c))) => (o.clone(), Some(lift(*c, o))),
        (o, b) => (o.clone(), b.cloned()),
    };
    // A NaN test joins the relations of the floats it tests.
    let (a, b) = match (a, b) {
        (Info::Floats(x, y, f, s), Some(Info::Values(z, t, _))) => {
            match nan_relations(cx, x, y, f, z, &t) {
                Some(t) => (Info::Floats(x, y, f, s), Some(Info::Floats(x, y, f, t))),
                None => return Info::Opaque,
            }
        }
        (Info::Values(z, t, _), Some(Info::Floats(x, y, f, s))) => {
            match nan_relations(cx, x, y, f, z, &t) {
                Some(t) => (Info::Floats(x, y, f, t), Some(Info::Floats(x, y, f, s))),
                None => return Info::Opaque,
            }
        }
        (a, b) => (a, b),
    };
    let bool_op = |x: bool, y: bool| match op {
        OpCode::And => x & y,
        OpCode::Or => x | y,
        _ => x ^ y,
    };
    let bits_op = |s: u8, t: u8| match op {
        OpCode::And => s & t,
        OpCode::Or => s | t,
        _ => s ^ t,
    };
    match (op, &a, &b) {
        (OpCode::Not, Info::Const(c), None) => Info::Const(!c),
        (OpCode::Not, Info::Pair(x, y, s), None) => Info::Pair(*x, *y, !s & ALL),
        (OpCode::Not, Info::Floats(x, y, f, s), None) => Info::Floats(*x, *y, *f, !s & FLOAT_ALL),
        (OpCode::Not, Info::Values(x, s, h), None) => {
            Info::Values(*x, complement(s, cx.width_of(*x)), *h)
        }
        (_, Info::Const(p), Some(Info::Const(q))) => Info::Const(bool_op(*p, *q)),
        (_, Info::Pair(x, y, s), Some(Info::Pair(x2, y2, t))) if x == x2 && y == y2 => {
            Info::Pair(*x, *y, bits_op(*s, *t))
        }
        (_, Info::Floats(x, y, f, s), Some(Info::Floats(x2, y2, f2, t)))
            if x == x2 && y == y2 && f == f2 =>
        {
            Info::Floats(*x, *y, *f, bits_op(*s, *t))
        }
        (_, Info::Values(x, s, h), Some(Info::Values(x2, t, h2))) => {
            let Some((base, s, t)) = common(cx, *x, s, *x2, t) else {
                // Unrelated terms: NaN tests of two floats are relations of the two.
                return match nan_pair(cx, *x, s, *x2, t) {
                    Some((x, y, f, s, t)) => Info::Floats(x, y, f, bits_op(s, t)),
                    None => Info::Opaque,
                };
            };
            let w = cx.width_of(base);
            let r = match op {
                OpCode::And => intersect(&s, &t),
                OpCode::Or => union(&s, &t, w),
                _ => sym_diff(&s, &t, w),
            };
            if r.len() > MAX_INTERVALS {
                Info::Opaque
            } else {
                Info::Values(base, r, hint(cx, base, *h, *h2))
            }
        }
        _ => Info::Opaque,
    }
}

pub(in crate::engine) fn info_of(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    root: u32,
) -> Result<Info, Stop> {
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if r.compares.contains_key(&i) {
            continue;
        }
        let node = cx.node(i);
        if node.width != 1 || !boolean_op(node.op) {
            r.compares.insert(i, leaf(cx, i));
            continue;
        }
        if !expanded {
            stack.push((i, true));
            for c in node.children() {
                if !r.compares.contains_key(&c) {
                    stack.push((c, false));
                }
            }
            continue;
        }
        r.meter.charge(Counter::PassWork, 1)?;
        r.meter.check()?;
        let a = r.compares[&node.a].clone();
        let info = if node.op == OpCode::Not {
            combine(cx, OpCode::Not, &a, None)
        } else {
            let b = r.compares[&node.b].clone();
            combine(cx, node.op, &a, Some(&b))
        };
        r.compares.insert(i, info);
    }
    Ok(r.compares[&root].clone())
}

// ----- emission -------------------------------------------------------------------------------------

fn bool_const(r: &mut Runner<'_, '_>, cx: &mut Context, v: bool) -> Result<u32, Stop> {
    r.build(cx, |cx| cx.mk_const(&BitVec::from_bool(v)))
}

/// A comparison `x op c` or `c op x`.
fn cmp_const(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    op: CmpOp,
    x: u32,
    c: &BitVec,
    x_first: bool,
) -> Result<u32, Stop> {
    let c = *c;
    r.build(cx, |cx| {
        let k = cx.mk_const(&c)?;
        if x_first {
            cx.c_cmp(op, x, k)
        } else {
            cx.c_cmp(op, k, x)
        }
    })
}

/// The float comparison `x op y` in `f`, negated if `not`.
fn float_cmp_node(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    f: FpFormat,
    op: Kind,
    x: u32,
    y: u32,
    not: bool,
) -> Result<u32, Stop> {
    let op = match op {
        Kind::Eq => FpOp::Eq,
        Kind::Lt => FpOp::Lt,
        _ => FpOp::Le,
    };
    r.build(cx, |cx| {
        let c = cx.c_fp(Desc { op, format: f }, &[x, y])?;
        if not { cx.c_un(UnOp::Not, c) } else { Ok(c) }
    })
}

fn emit_pair(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    y: u32,
    s: u8,
) -> Result<Option<u32>, Stop> {
    let real = realizable(cx.wid(x));
    let s = s & real;
    if s == 0 {
        return bool_const(r, cx, false).map(Some);
    }
    if s == real {
        return bool_const(r, cx, true).map(Some);
    }
    for op in [
        CmpOp::Eq,
        CmpOp::Ne,
        CmpOp::Ult,
        CmpOp::Ule,
        CmpOp::Slt,
        CmpOp::Sle,
    ] {
        if pred_set(op) & real == s {
            return r.build(cx, |cx| cx.c_cmp(op, x, y)).map(Some);
        }
        if swap_set(pred_set(op)) & real == s {
            return r.build(cx, |cx| cx.c_cmp(op, y, x)).map(Some);
        }
    }
    Ok(None)
}

/// A set of relations of floats: false, true, one comparison, or one negated.
fn emit_floats(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    y: u32,
    f: FpFormat,
    s: u8,
) -> Result<Option<u32>, Stop> {
    if s == 0 {
        return bool_const(r, cx, false).map(Some);
    }
    if s == FLOAT_ALL {
        return bool_const(r, cx, true).map(Some);
    }
    for not in [false, true] {
        for op in [Kind::Eq, Kind::Lt, Kind::Le] {
            let p = float_pred_set(op);
            let p = if not { !p & FLOAT_ALL } else { p };
            if p == s {
                return float_cmp_node(r, cx, f, op, x, y, not).map(Some);
            }
            if float_swap(p) == s {
                return float_cmp_node(r, cx, f, op, y, x, not).map(Some);
            }
        }
    }
    Ok(None)
}

/// Whether [`emit_values`] writes `s` as one comparison with a constant (or a truth value).
fn simple_set(s: &Set, w: Width) -> bool {
    if s.is_empty() || *s == full(w) {
        return true;
    }
    let wrapped = match s.as_slice() {
        [(lo, hi)] => Some((*lo, *hi)),
        [(z, hi), (lo, m)] if z.is_zero() && m.is_ones() => Some((*lo, *hi)),
        _ => None,
    };
    let Some((lo, hi)) = wrapped else {
        return false;
    };
    if lo == hi {
        return true;
    }
    if let [(a, b)] = complement(s, w).as_slice()
        && a == b
    {
        return true;
    }
    lo.is_zero() || hi.is_ones() || lo == BitVec::smin(w) || hi == BitVec::smax(w)
}

fn emit_values(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    x: u32,
    s: &Set,
    hint: Option<FpFormat>,
) -> Result<Option<u32>, Stop> {
    let w = cx.width_of(x);
    let (zero, max, smin, smax) = (
        BitVec::zero(w),
        BitVec::ones(w),
        BitVec::smin(w),
        BitVec::smax(w),
    );
    if s.is_empty() {
        return bool_const(r, cx, false).map(Some);
    }
    if *s == full(w) {
        return bool_const(r, cx, true).map(Some);
    }
    // One wrapped interval [lo, hi]: either one interval, or two touching both ends.
    let wrapped = match s.as_slice() {
        [(lo, hi)] => Some((*lo, *hi)),
        [(z, hi), (lo, m)] if z.is_zero() && m.is_ones() => Some((*lo, *hi)),
        _ => None,
    };
    // One comparison with a constant.
    if let Some((lo, hi)) = wrapped {
        let comp = complement(s, w);
        let simple = if lo == hi {
            Some((CmpOp::Eq, lo, true))
        } else if let [(a, b)] = comp.as_slice()
            && a == b
        {
            Some((CmpOp::Ne, *a, true))
        } else if lo == smin && hi == max {
            // The negative values: a sign test, not `smin <=u x`.
            Some((CmpOp::Sle, max, true))
        } else if lo == zero && hi == smax {
            Some((CmpOp::Sle, zero, false))
        } else if lo == zero {
            Some((CmpOp::Ule, hi, true))
        } else if hi == max {
            Some((CmpOp::Ule, lo, false))
        } else if lo == smin {
            Some((CmpOp::Sle, hi, true))
        } else if hi == smax {
            Some((CmpOp::Sle, lo, false))
        } else {
            None
        };
        if let Some((op, c, x_first)) = simple {
            return cmp_const(r, cx, op, x, &c, x_first).map(Some);
        }
    }
    // One float comparison with a constant, or its negation.
    if let Some(f) = hint {
        for not in [false, true] {
            let t = if not { complement(s, w) } else { s.clone() };
            if let Some((op, c, x_first)) = float_form(f, &t) {
                let e = r.build(cx, |cx| {
                    let k = match c {
                        Some(c) => cx.mk_const(&c)?,
                        None => x,
                    };
                    let op = match op {
                        Kind::Eq => FpOp::Eq,
                        Kind::Lt => FpOp::Lt,
                        _ => FpOp::Le,
                    };
                    let args = if x_first { [x, k] } else { [k, x] };
                    let e = cx.c_fp(Desc { op, format: f }, &args)?;
                    if not { cx.c_un(UnOp::Not, e) } else { Ok(e) }
                })?;
                return Ok(Some(e));
            }
        }
    }
    let Some((lo, hi)) = wrapped else {
        return Ok(None);
    };
    // x - lo <=u hi - lo (wrapping).
    let span = BitVec::bin_unchecked(BinOp::Sub, &hi, &lo);
    r.build(cx, |cx| {
        let l = cx.mk_const(&lo)?;
        let d = cx.c_bin(BinOp::Sub, x, l)?;
        let k = cx.mk_const(&span)?;
        cx.c_cmp(CmpOp::Ule, d, k)
    })
    .map(Some)
}

/// An OR of every value a masked word can take is true; when every test is
/// conjoined with the same condition, it is that condition. VM case tables
/// spell `c` as `(x & m == k0) & c | …` for every submask `k` of `m`.
fn exhaustive_mask_cases(
    r: &mut Runner<'_, '_>,
    cx: &Context,
    root: u32,
) -> Result<Option<Option<u32>>, Stop> {
    const MAX_TERMS: usize = 32;

    let mut terms = Vec::new();
    let mut todo = vec![root];
    while let Some(e) = todo.pop() {
        r.meter.charge(Counter::PassWork, 1)?;
        let n = cx.node(e);
        if n.op == OpCode::Or && n.width == 1 {
            todo.push(n.a);
            todo.push(n.b);
        } else {
            terms.push(e);
            if terms.len() > MAX_TERMS {
                return Ok(None);
            }
        }
    }
    if terms.len() < 2 {
        return Ok(None);
    }

    let first = cx.node(terms[0]);
    let candidates = if first.op == OpCode::And && first.width == 1 {
        [Some(first.a), Some(first.b), None]
    } else {
        [None, None, None]
    };
    for common in candidates.into_iter().flatten().map(Some).chain([None]) {
        let mut expr = None;
        let mut values = Vec::new();
        let mut valid = true;
        for &term in &terms {
            let test = if let Some(c) = common {
                let n = cx.node(term);
                if n.op != OpCode::And || n.width != 1 {
                    valid = false;
                    break;
                }
                if n.a == c {
                    n.b
                } else if n.b == c {
                    n.a
                } else {
                    valid = false;
                    break;
                }
            } else {
                term
            };
            let n = cx.node(test);
            if n.op != OpCode::Eq {
                valid = false;
                break;
            }
            let (e, k) = match (cx.const_val(n.a), cx.const_val(n.b)) {
                (None, Some(k)) => (n.a, k),
                (Some(k), None) => (n.b, k),
                _ => {
                    valid = false;
                    break;
                }
            };
            if expr.replace(e).is_some_and(|old| old != e) {
                valid = false;
                break;
            }
            let Some(k) = k.to_u64() else {
                valid = false;
                break;
            };
            values.push(k);
        }
        let Some(e) = expr.filter(|_| valid) else {
            continue;
        };
        let n = cx.node(e);
        if n.op != OpCode::And {
            continue;
        }
        let mask = match (cx.const_val(n.a), cx.const_val(n.b)) {
            (Some(k), None) | (None, Some(k)) => k,
            _ => continue,
        };
        let Some(mask) = mask.to_u64() else {
            continue;
        };
        let bits = mask.count_ones();
        if bits > 5 || values.iter().any(|v| v & !mask != 0) {
            continue;
        }
        values.sort_unstable();
        values.dedup();
        if values.len() == 1usize << bits {
            return Ok(Some(common));
        }
    }
    Ok(None)
}

/// The compares pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    if node.op == OpCode::Select {
        // What `arms_read` declines contributes to the result (see the linear pass's `step`).
        let declined = match arms_read(r, cx, n)? {
            Some(Step::Normal(f)) => f,
            Some(step) => return Ok(step),
            None => Fin::FINAL,
        };
        return Ok(match order_step(r, cx, n)? {
            Step::Normal(f) => Step::Normal(f.and(declined)),
            step => step,
        });
    }
    if node.width != 1 || !(boolean_op(node.op) || node.op.as_cmp().is_some() || float_cmp(node.op))
    {
        return Ok(Step::Normal(Fin::FINAL));
    }
    if let Some(common) = exhaustive_mask_cases(r, cx, n)? {
        let before = cx.len() as u32;
        let (e, atoms) = match common {
            Some(c) => (c, vec![c]),
            None => (bool_const(r, cx, true)?, Vec::new()),
        };
        return finish(r, cx, PassKind::Compares, n, e, before, &atoms, Fin::FINAL);
    }
    // A test of one bit through a mask: `(x & 2^k) != 0` is bit k of x.
    if let Some((x, k, set)) = bit_test(cx, n) {
        let before = cx.len() as u32;
        let e = r.build(cx, |cx| {
            let b = cx.c_extract(x, k, 1)?;
            if set { Ok(b) } else { cx.c_un(UnOp::Not, b) }
        })?;
        return finish(r, cx, PassKind::Compares, n, e, before, &[x], Fin::FINAL);
    }
    let info = info_of(r, cx, n)?;
    let before = cx.len() as u32;
    let (e, atoms) = match &info {
        Info::Pair(x, y, s) => (emit_pair(r, cx, *x, *y, *s)?, vec![*x, *y]),
        Info::Floats(x, y, f, s) => (emit_floats(r, cx, *x, *y, *f, *s)?, vec![*x, *y]),
        // A set of values of `x`: emitted on the deepest term `x` is a function of where it
        // is one comparison with a constant (`sext(a) <s 5` is `a <s 5`, `zext(a) <u 5` is
        // `a <u 5`), else on `x` (`(x + 3) <u 10` stays: on `x` it is a range check). Decided
        // before anything is built: a candidate built and dropped would count as a use of
        // the nodes it shares with the chosen one.
        Info::Values(x, s, h) => {
            let (nodes, maps) = chain(cx, *x);
            let mut at = 0usize;
            let mut set = s.clone();
            let mut best = u32::MAX;
            for k in 0..nodes.len() {
                let t = if k == 0 {
                    Some(s.clone())
                } else {
                    pull(cx, &nodes, &maps, k, s)
                };
                let Some(t) = t else {
                    continue;
                };
                // The term, and one comparison with a constant (two nodes) or a range check
                // (a subtraction, two constants and the comparison).
                let term = match cx.dag_size(&[cx.handle(nodes[k])], 256) {
                    Ok(crate::expr::Bounded::Exact(n)) => n,
                    _ => continue,
                };
                let cost = term
                    + if simple_set(&t, cx.width_of(nodes[k])) {
                        2
                    } else {
                        4
                    };
                if cost < best {
                    (at, set, best) = (k, t, cost);
                }
            }
            let hint = if at == 0 { *h } else { None };
            (emit_values(r, cx, nodes[at], &set, hint)?, vec![nodes[at]])
        }
        Info::Const(v) if boolean_op(node.op) => (Some(bool_const(r, cx, *v)?), Vec::new()),
        _ => (None, Vec::new()),
    };
    let e = match e {
        Some(e) if e != n => e,
        _ => {
            if matches!(node.op, OpCode::Eq | OpCode::Ne)
                && cx.wid(node.a) > 1
                && super::poly::equal(r, cx, node.a, node.b)?
            {
                let before = cx.len() as u32;
                let c = bool_const(r, cx, node.op == OpCode::Eq)?;
                return finish(r, cx, PassKind::Compares, n, c, before, &[], Fin::FINAL);
            }
            if matches!(node.op, OpCode::Eq | OpCode::Ne)
                && cx.wid(node.a) > 1
                && let Some(same) = super::bitwise::equal(r, cx, node.a, node.b)?
            {
                let before = cx.len() as u32;
                let c = bool_const(r, cx, same == (node.op == OpCode::Eq))?;
                return finish(r, cx, PassKind::Compares, n, c, before, &[], Fin::FINAL);
            }
            if matches!(node.op, OpCode::Eq | OpCode::Ne)
                && cx.wid(node.a) > 1
                && super::linear_mba::equal(r, cx, node.a, node.b)?
            {
                let before = cx.len() as u32;
                let c = bool_const(r, cx, node.op == OpCode::Eq)?;
                return finish(r, cx, PassKind::Compares, n, c, before, &[], Fin::FINAL);
            }
            if let Some(b) = residue_decide(r, cx, n)? {
                let before = cx.len() as u32;
                let c = bool_const(r, cx, b)?;
                return finish(r, cx, PassKind::Compares, n, c, before, &[], Fin::FINAL);
            }
            if let Some(b) = super::predicate::decide(r, cx, n)? {
                let before = cx.len() as u32;
                let c = bool_const(r, cx, b)?;
                return finish(r, cx, PassKind::Compares, n, c, before, &[], Fin::FINAL);
            }
            if let Some((x, j, truth)) = super::predicate::recover(r, cx, n)? {
                let before = cx.len() as u32;
                let t = r.build(cx, |cx| cx.c_extract(x, 0, j))?;
                let e = if j == 1 {
                    // One residue of two is true (the other, or it would be constant, is not).
                    Some(if truth[1] {
                        t
                    } else {
                        r.build(cx, |cx| cx.c_un(UnOp::Not, t))?
                    })
                } else {
                    emit_values(r, cx, t, &residue_set(&truth, cx.width_of(t)), None)?
                };
                if let Some(e) = e {
                    return finish(r, cx, PassKind::Compares, n, e, before, &[x], Fin::FINAL);
                }
                super::discard(r, cx, before);
            }
            return order_step(r, cx, n);
        }
    };
    match &info {
        Info::Pair(x, y, s) => r.explain_with(|| crate::engine::Explanation::Relations {
            x: cx.handle(*x),
            y: cx.handle(*y),
            set: *s,
        }),
        Info::Values(x, s, _) => r.explain_with(|| crate::engine::Explanation::Intervals {
            x: cx.handle(*x),
            set: s.clone(),
        }),
        _ => {}
    }
    let step = finish(r, cx, PassKind::Compares, n, e, before, &atoms, Fin::FINAL)?;
    let Step::Normal(fin) = step else {
        return Ok(step);
    };
    // Not smaller (`0 <=s x·x` as `x·x <=u smax`): residues may still show it constant.
    if let Some(b) = super::predicate::decide(r, cx, n)? {
        let before = cx.len() as u32;
        let c = bool_const(r, cx, b)?;
        return Ok(
            match finish(r, cx, PassKind::Compares, n, c, before, &[], Fin::FINAL)? {
                Step::Normal(f) => Step::Normal(f.and(fin)),
                to => to,
            },
        );
    }
    Ok(Step::Normal(fin))
}

/// `(x & 2^k) != 0` (`Some((x, k, true))`) or `(x & 2^k) == 0` (`false`).
fn bit_test(cx: &Context, n: u32) -> Option<(u32, u16, bool)> {
    let node = cx.node(n);
    let set = match node.op {
        OpCode::Ne => true,
        OpCode::Eq => false,
        _ => return None,
    };
    if !cx.const_val(node.b)?.is_zero() {
        return None;
    }
    let and = cx.node(node.a);
    if and.op != OpCode::And {
        return None;
    }
    let m = cx.const_val(and.b)?;
    let one = BitVec::apply_un(UnOp::Popcnt, &m).ok()?.to_u64()? == 1;
    let k = BitVec::apply_un(UnOp::Ctz, &m).ok()?.to_u64()? as u16;
    one.then_some((and.a, k, set))
}

/// `e == c` or `e != c` decided by the residues of `e`: when `c`'s low bits are none of the
/// values `e` takes there (`x·x == 2`, `(x·x & 7) == 5`).
fn residue_decide(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Option<bool>, Stop> {
    let node = cx.node(n);
    if !matches!(node.op, OpCode::Eq | OpCode::Ne) {
        return Ok(None);
    }
    let (e, c) = match (cx.const_val(node.a), cx.const_val(node.b)) {
        (None, Some(c)) => (node.a, c),
        (Some(c), None) => (node.b, c),
        _ => return Ok(None),
    };
    let k = u32::from(cx.wid(e)).min(4);
    let Some(t) = super::residue::residues(r, cx, e, k)? else {
        return Ok(None);
    };
    let low = c.limbs()[0] & t.mask;
    if t.values.contains(&low) {
        return Ok(None);
    }
    Ok(Some(node.op == OpCode::Ne))
}

/// The values `r` below `2^W` where `truth[r]`, as an interval set.
fn residue_set(truth: &[bool], w: Width) -> Set {
    let mut out = Set::new();
    let mut r = 0;
    while r < truth.len() {
        if !truth[r] {
            r += 1;
            continue;
        }
        let lo = r;
        while r + 1 < truth.len() && truth[r + 1] {
            r += 1;
        }
        out.push((
            BitVec::wrapping_from_u64(w, lo as u64),
            BitVec::wrapping_from_u64(w, r as u64),
        ));
        r += 1;
    }
    out
}

/// The order reading of `n` (see `order`).
/// The most nodes above its condition an arm may have for [`arms_read`].
const MAX_ARM: usize = 64;

/// Whether `e` reads `c` among at most [`MAX_ARM`] nodes made after `c`.
fn reads(cx: &Context, e: u32, c: u32) -> bool {
    let mut seen = crate::hash::IdMap::<u32, ()>::default();
    let mut todo = vec![e];
    while let Some(v) = todo.pop() {
        if v == c {
            return true;
        }
        if v < c || seen.insert(v, ()).is_some() {
            continue;
        }
        if seen.len() > MAX_ARM {
            return false;
        }
        todo.extend(cx.node(v).children());
    }
    false
}

/// `select(c, t, f)` that is one of its values for every input (see
/// [`one_value`]).
fn arms_read(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Option<Step>, Stop> {
    let node = cx.node(n);
    let (c, t, f) = (node.a, node.b, node.c);
    if cx.const_val(c).is_some() {
        return Ok(None);
    }
    let before = cx.len() as u32;
    let Some(e) = one_value(r, cx, c, t, f)? else {
        super::discard(r, cx, before);
        return Ok(None);
    };
    // The nodes from before the rewrite that it reads.
    let mut stops = Vec::new();
    let mut todo = vec![e];
    let mut seen = crate::hash::IdMap::<u32, ()>::default();
    while let Some(i) = todo.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if i < before {
            stops.push(i);
        } else {
            todo.extend(cx.node(i).children());
        }
    }
    finish(r, cx, PassKind::Compares, n, e, before, &stops, Fin::FINAL).map(Some)
}

/// The one value `select(c, t, f)` takes, when it is one:
///
/// - arms that read `c` (a flag a `setcc` and a carry both spell): `t` with `c` true and `f`
///   with `c` false, when they come out alike (`select(c, zext(c), zext(c) + 1)` is 1);
/// - a flag (1 bit) chosen by a test of `p` against a constant `k`: the arm taken when
///   `p != k`, when with `p` at `k` it is the other arm (a shift's flags by its count,
///   `count != 0 ? r == 0 : x == 0`, with `x << 0` being `x`).
///
/// Only one value: a select with its arms rewritten is no smaller, and the commit rule would
/// take it on one run and not another.
fn one_value(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    c: u32,
    t: u32,
    f: u32,
) -> Result<Option<u32>, Stop> {
    let with = |r: &mut Runner<'_, '_>, cx: &mut Context, e: u32, from: u32, to: u32| {
        let mut repl = crate::hash::IdMap::default();
        repl.insert(from, to);
        r.build(cx, |cx| Ok(cx.substitute_ids(&[e], &repl)?[0]))
    };
    if reads(cx, t, c) || reads(cx, f, c) {
        let one = bool_const(r, cx, true)?;
        let zero = bool_const(r, cx, false)?;
        let t2 = with(r, cx, t, c, one)?;
        let f2 = with(r, cx, f, c, zero)?;
        if t2 == f2 {
            return Ok(Some(t2));
        }
    }
    // A flag's value only: on wider values the arm in place of the select shares less with
    // the code around it.
    let cn = cx.node(c);
    if cx.wid(t) != 1 || !matches!(cn.op, OpCode::Eq | OpCode::Ne) {
        return Ok(None);
    }
    let (p, k) = match (cx.const_val(cn.a), cx.const_val(cn.b)) {
        (None, Some(_)) => (cn.a, cn.b),
        (Some(_), None) => (cn.b, cn.a),
        _ => return Ok(None),
    };
    let (held, other) = if cn.op == OpCode::Eq { (t, f) } else { (f, t) };
    if !reads(cx, other, p) {
        return Ok(None);
    }
    Ok((with(r, cx, other, p, k)? == held).then_some(other))
}

fn order_step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let before = cx.len() as u32;
    match super::order::decide(r, cx, n)? {
        Some((e, atoms, fin)) => finish(r, cx, PassKind::Compares, n, e, before, &atoms, fin),
        None => Ok(Step::Normal(Fin::FINAL)),
    }
}
