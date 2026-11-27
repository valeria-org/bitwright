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
const MAX_PEEL: usize = 10;

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
    if n.width == 1 && n.op == OpCode::Extract && n.b == 0 {
        return Info::Values(
            i,
            vec![(BitVec::one(Width::W1), BitVec::one(Width::W1))],
            None,
        );
    }
    let Some(op) = n.op.as_cmp() else {
        return Info::Opaque;
    };
    // `a - (b + k) == -k` is `a == b` (the VM's `x <u y`, written `~((y - x == 0) | (y <u
    // x))`, once a constant both sides added is folded into the equality alone).
    let equal = |t: u32, c: &BitVec| {
        matches!(op, CmpOp::Eq | CmpOp::Ne)
            .then(|| difference(cx, t))
            .flatten()
            .filter(|(_, _, k)| k == c)
            .map(|(a, b, _)| Info::Pair(a.min(b), a.max(b), pred_set(op)))
    };
    match (cx.const_val(n.a), cx.const_val(n.b)) {
        (Some(_), Some(_)) => Info::Opaque,
        (None, Some(c)) => {
            equal(n.a, &c).unwrap_or_else(|| Info::Values(n.a, interval_of(op, &c, true), None))
        }
        (Some(c), None) => {
            equal(n.b, &c).unwrap_or_else(|| Info::Values(n.b, interval_of(op, &c, false), None))
        }
        (None, None) if n.a == n.b => Info::Opaque,
        (None, None) if n.a < n.b => Info::Pair(n.a, n.b, pred_set(op)),
        (None, None) => Info::Pair(n.b, n.a, swap_set(pred_set(op))),
    }
}

/// `(a, b, k)` when `t` is `a - b + k` at any width `1..=512`: a difference of two values, a
/// constant added to it or to either of them (`a - (b + k)`; the constructors keep constants
/// on the right of a sum).
fn difference(cx: &Context, t: u32) -> Option<(u32, u32, BitVec)> {
    let w = cx.width_of(t);
    let bare = |mut x: u32| {
        let mut k = BitVec::zero(w);
        loop {
            let node = cx.node(x);
            let added = (node.op == OpCode::Add)
                .then(|| cx.const_val(node.b))
                .flatten();
            match added {
                Some(c) => {
                    k = BitVec::bin_unchecked(BinOp::Add, &k, &c);
                    x = node.a;
                }
                None => return (x, k),
            }
        }
    };
    let (d, k) = bare(t);
    let node = cx.node(d);
    if node.op != OpCode::Sub {
        return None;
    }
    let ((a, ka), (b, kb)) = (bare(node.a), bare(node.b));
    let k = BitVec::bin_unchecked(BinOp::Sub, &BitVec::bin_unchecked(BinOp::Add, &k, &ka), &kb);
    (a != b && !cx.is_const(a) && !cx.is_const(b)).then_some((a, b, k))
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

/// Flatten a `<= 64`-bit node into `(sorted_terms, bias)` mod `2^w` (`<= 16` terms).
fn affine_terms_64(cx: &Context, root: u32, w: u16) -> Option<(Vec<(u32, u64)>, u64)> {
    if w == 0 || w > 64 {
        return None;
    }
    let mask = u64::MAX >> (64 - w);
    let mut bias = 0u64;
    let mut parts: Vec<(u32, u64)> = Vec::new();
    let mut stack: Vec<(u32, u64, u8)> = vec![(root, 1, 12)];
    let mut steps = 0usize;
    while let Some((i, k, depth)) = stack.pop() {
        steps += 1;
        if steps > 48 || parts.len() > 20 {
            return None;
        }
        if let Some(c) = cx.const_val(i).and_then(|v| v.to_u64()) {
            bias = bias.wrapping_add(k.wrapping_mul(c));
            continue;
        }
        let n = cx.node(i);
        if depth == 0 {
            parts.push((i, k));
            continue;
        }
        match n.op {
            OpCode::Add => {
                stack.push((n.a, k, depth - 1));
                stack.push((n.b, k, depth - 1));
            }
            OpCode::Sub => {
                stack.push((n.a, k, depth - 1));
                stack.push((n.b, k.wrapping_neg(), depth - 1));
            }
            OpCode::Neg => {
                stack.push((n.a, k.wrapping_neg(), depth - 1));
            }
            OpCode::Not => {
                bias = bias.wrapping_sub(k);
                stack.push((n.a, k.wrapping_neg(), depth - 1));
            }
            OpCode::Mul if cx.const_val(n.b).and_then(|v| v.to_u64()).is_some() => {
                let c = cx.const_val(n.b)?.to_u64()?;
                stack.push((n.a, k.wrapping_mul(c), depth - 1));
            }
            OpCode::Mul if cx.const_val(n.a).and_then(|v| v.to_u64()).is_some() => {
                let c = cx.const_val(n.a)?.to_u64()?;
                stack.push((n.b, k.wrapping_mul(c), depth - 1));
            }
            OpCode::Shl
                if cx
                    .const_val(n.b)
                    .and_then(|v| v.to_u64())
                    .is_some_and(|s| s < u64::from(w)) =>
            {
                let s = cx.const_val(n.b)?.to_u64()?;
                stack.push((n.a, k << s, depth - 1));
            }
            _ => parts.push((i, k)),
        }
    }
    parts.sort_unstable_by_key(|&(id, _)| id);
    parts.dedup_by(|next, prev| {
        if next.0 != prev.0 {
            return false;
        }
        prev.1 = prev.1.wrapping_add(next.1);
        true
    });
    parts.retain(|(_, c)| *c & mask != 0);
    for (_, c) in &mut parts {
        *c &= mask;
    }
    Some((parts, bias & mask))
}

/// Whether `z == k` (or `z != k`) has the exact same zero locus as `x == y` (`z - k == ±(x - y) mod 2^w`).
fn singleton_eq_rel_for_pair(cx: &Context, x: u32, y: u32, z: u32, s: &Set) -> Option<u8> {
    let w = cx.wid(x);
    if w == 0 || w > 64 || cx.wid(z) != w {
        return None;
    }
    let wt = cx.width_of(z);
    let (k_bv, rel) = if s.len() == 1 && s[0].0 == s[0].1 {
        (s[0].0, pred_set(CmpOp::Eq))
    } else {
        let comp = complement(s, wt);
        if comp.len() == 1 && comp[0].0 == comp[0].1 {
            (comp[0].0, pred_set(CmpOp::Ne))
        } else {
            return None;
        }
    };
    let k = k_bv.to_u64()?;
    let mask = u64::MAX >> (64 - w);
    let (px, bx) = affine_terms_64(cx, x, w)?;
    let (py, by) = affine_terms_64(cx, y, w)?;
    let (pz, bz) = affine_terms_64(cx, z, w)?;
    let mut dxy = px;
    for (id, c) in py {
        dxy.push((id, c.wrapping_neg()));
    }
    dxy.sort_unstable_by_key(|&(id, _)| id);
    dxy.dedup_by(|next, prev| {
        if next.0 != prev.0 {
            return false;
        }
        prev.1 = prev.1.wrapping_add(next.1);
        true
    });
    dxy.retain(|(_, c)| *c & mask != 0);
    for (_, c) in &mut dxy {
        *c &= mask;
    }
    if dxy.is_empty() || dxy.len() != pz.len() {
        return None;
    }
    let bxy = bx.wrapping_sub(by) & mask;
    let bzk = bz.wrapping_sub(k) & mask;
    let same_pos = bzk == bxy && pz == dxy;
    let same_neg = bzk.wrapping_add(bxy) & mask == 0
        && pz
            .iter()
            .zip(&dxy)
            .all(|(&(a, ca), &(b, cb))| a == b && ca.wrapping_add(cb) & mask == 0);
    (same_pos || same_neg).then_some(rel)
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
        (_, Info::Pair(x, y, s), Some(Info::Values(z, t, _))) => {
            match singleton_eq_rel_for_pair(cx, *x, *y, *z, t) {
                Some(rel) => Info::Pair(*x, *y, bits_op(*s, rel)),
                None => Info::Opaque,
            }
        }
        (_, Info::Values(z, t, _), Some(Info::Pair(x, y, s))) => {
            match singleton_eq_rel_for_pair(cx, *x, *y, *z, t) {
                Some(rel) => Info::Pair(*x, *y, bits_op(rel, *s)),
                None => Info::Opaque,
            }
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
        // Two-point single-bit cube on a 2-bit masked word `x` (`x = y & M` or `x = y | M` with
        // only two unfixed bits `{b0, b1}`): `{c1, c2}` (or its complement) where `c1 ^ c2 == 2^b1`
        // fixes the single remaining bit `b0`, collapsing directly to `extract<b0, 1>(y)` (or `~`).
        if w.bits() <= 64 {
            let full_m = u64::MAX >> (64 - w.bits());
            let xn = cx.node(x);
            let mask_info: Option<(u32, u64, u64)> = match xn.op {
                OpCode::And => cx
                    .const_val(xn.b)
                    .and_then(|v| v.to_u64())
                    .map(|m| (xn.a, m & full_m, 0))
                    .or_else(|| {
                        cx.const_val(xn.a)
                            .and_then(|v| v.to_u64())
                            .map(|m| (xn.b, m & full_m, 0))
                    }),
                OpCode::Or => cx
                    .const_val(xn.b)
                    .and_then(|v| v.to_u64())
                    .map(|m| (xn.a, !m & full_m, m & full_m))
                    .or_else(|| {
                        cx.const_val(xn.a)
                            .and_then(|v| v.to_u64())
                            .map(|m| (xn.b, !m & full_m, m & full_m))
                    }),
                _ => None,
            };
            if let Some((src, varying, fixed_ones)) = mask_info {
                let single_bit_cube = |pts: &Set| -> Option<(u16, bool)> {
                    let [(c1, d1), (c2, d2)] = pts.as_slice() else {
                        return None;
                    };
                    if c1 != d1 || c2 != d2 {
                        return None;
                    }
                    let (v1, v2) = (c1.to_u64()? & full_m, c2.to_u64()? & full_m);
                    let diff = v1 ^ v2;
                    if !diff.is_power_of_two() || (diff & varying) != diff {
                        return None;
                    }
                    let check_mask = !diff & full_m;
                    let target = v1 & check_mask;
                    if (fixed_ones & !varying & check_mask) != (target & !varying & check_mask) {
                        return None;
                    }
                    let rem = varying & check_mask;
                    if !rem.is_power_of_two() {
                        return None;
                    }
                    let bit = rem.trailing_zeros() as u16;
                    let want_one = ((target >> bit) & 1) != 0;
                    Some((bit, want_one))
                };
                if let Some((bit, want_one)) = single_bit_cube(s) {
                    return r
                        .build(cx, |cx| {
                            let b = cx.c_extract(src, bit, 1)?;
                            if want_one {
                                Ok(b)
                            } else {
                                cx.c_un(UnOp::Not, b)
                            }
                        })
                        .map(Some);
                }
                let comp = complement(s, w);
                if let Some((bit, want_one)) = single_bit_cube(&comp) {
                    return r
                        .build(cx, |cx| {
                            let b = cx.c_extract(src, bit, 1)?;
                            if !want_one {
                                Ok(b)
                            } else {
                                cx.c_un(UnOp::Not, b)
                            }
                        })
                        .map(Some);
                }
            }
        }
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

enum MaskCase {
    Const(bool),
    Expr(u32),
    Bit { expr: u32, bit: u16, set: bool },
}

/// An OR of every value a bounded word can take is true (or the common conjunct); an OR of
/// every value with one unknown bit set (or clear) is that single bit test. VM case tables
/// spell `c` as `(x & m == k0) & c | …` or `extract<b, 1>(x)` as `(x == 1) | (x == 3) | …`.
fn exhaustive_mask_cases(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    root: u32,
) -> Result<Option<(MaskCase, Fin)>, Stop> {
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
        let ew = cx.wid(e);
        if ew == 0 || ew > 64 {
            continue;
        }
        let full_mask = u64::MAX >> (64 - ew);
        let (kb, fin) = super::known_words(r, cx, e)?;
        let (kz, ko) = match kb {
            Some([z, o]) => (z & full_mask, o & full_mask),
            None => continue,
        };
        let unk = full_mask & !(kz | ko);
        let bits = unk.count_ones();
        if bits > 5 {
            continue;
        }
        values.retain(|&v| (v & kz) == 0 && (v & ko) == ko);
        values.sort_unstable();
        values.dedup();
        if values.is_empty() {
            return Ok(Some((MaskCase::Const(false), fin)));
        }
        if values.len() == 1usize << bits {
            return Ok(Some((
                common.map_or(MaskCase::Const(true), MaskCase::Expr),
                fin,
            )));
        }
        if common.is_none() && bits >= 1 && values.len() == (1usize << (bits - 1)) {
            let mut rem = unk;
            while rem != 0 {
                let b = rem.trailing_zeros() as u16;
                rem &= rem - 1;
                if values.iter().all(|&v| (v >> b) & 1 == 1) {
                    return Ok(Some((
                        MaskCase::Bit {
                            expr: e,
                            bit: b,
                            set: true,
                        },
                        fin,
                    )));
                }
                if values.iter().all(|&v| (v >> b) & 1 == 0) {
                    return Ok(Some((
                        MaskCase::Bit {
                            expr: e,
                            bit: b,
                            set: false,
                        },
                        fin,
                    )));
                }
            }
        }
    }
    Ok(None)
}

/// Sign test on a sign-extension bit hack `((y ^ 2^(k-1)) - 2^(k-1)) <s 0` (or `0 <=s ...`)
/// where bits `k..w` of `y` are known zero: this is exact `extract<k-1, 1>(y)` (or its negation).
fn sign_extend_sign_test(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<(u32, u16, bool, Fin)>, Stop> {
    let node = cx.node(n);
    let (arg, is_neg) = match node.op {
        OpCode::Slt if cx.const_val(node.b).is_some_and(|v| v.is_zero()) => (node.a, true),
        OpCode::Sle if cx.const_val(node.a).is_some_and(|v| v.is_zero()) => (node.b, false),
        _ => return Ok(None),
    };
    let w = cx.wid(arg);
    if !(2..=64).contains(&w) {
        return Ok(None);
    }
    let mask = u64::MAX >> (64 - w);
    let an = cx.node(arg);
    let (lhs, sub_val) = match an.op {
        OpCode::Sub => match cx.const_val(an.b).and_then(|v| v.to_u64()) {
            Some(c) => (an.a, c & mask),
            None => return Ok(None),
        },
        OpCode::Add => match (
            cx.const_val(an.a).and_then(|v| v.to_u64()),
            cx.const_val(an.b).and_then(|v| v.to_u64()),
        ) {
            (None, Some(c)) => (an.a, c.wrapping_neg() & mask),
            (Some(c), None) => (an.b, c.wrapping_neg() & mask),
            _ => return Ok(None),
        },
        _ => return Ok(None),
    };
    if sub_val == 0 || !sub_val.is_power_of_two() {
        return Ok(None);
    }
    let bit = sub_val.trailing_zeros() as u16;
    let xn = cx.node(lhs);
    if xn.op != OpCode::Xor {
        return Ok(None);
    }
    let y = match (
        cx.const_val(xn.a).and_then(|v| v.to_u64()),
        cx.const_val(xn.b).and_then(|v| v.to_u64()),
    ) {
        (None, Some(c)) if (c & mask) == sub_val => xn.a,
        (Some(c), None) if (c & mask) == sub_val => xn.b,
        _ => return Ok(None),
    };
    let k = u32::from(bit) + 1;
    let hi_mask = if k >= u32::from(w) {
        0
    } else {
        mask & !((1u64 << k) - 1)
    };
    if hi_mask == 0 {
        return Ok(Some((y, bit, is_neg, Fin::FINAL)));
    }
    let (kb, fin) = super::known_words(r, cx, y)?;
    if let Some([kz, _]) = kb
        && (kz & hi_mask) == hi_mask
    {
        return Ok(Some((y, bit, is_neg, fin)));
    }
    Ok(None)
}

/// Decides Hacker's Delight signed addition/subtraction overflow sign-bit idioms when operand
/// signed intervals prove overflow impossible (or unconditional):
/// - `((x ^ y) & ((x - y) ^ x)) <s 0`       (`ssub.overflow(x, y)`)
/// - `((a ^ b) & ((~a + b) ^ b)) <s 0`      (`ssub.overflow(b, a + 1)`)
/// - `((~(x ^ y)) & ((x + y) ^ x)) <s 0`    (`sadd.overflow(x, y)`)
///
/// and their `0 <=s ...` complements.
fn signed_overflow_sign_test(
    r: &mut Runner<'_, '_>,
    cx: &mut Context,
    n: u32,
) -> Result<Option<(bool, Fin)>, Stop> {
    let node = cx.node(n);
    let (arg, want_overflow) = match node.op {
        OpCode::Slt if cx.const_val(node.b).is_some_and(|v| v.is_zero()) => (node.a, true),
        OpCode::Sle if cx.const_val(node.a).is_some_and(|v| v.is_zero()) => (node.b, false),
        _ => return Ok(None),
    };
    let w = cx.wid(arg);
    if !(2..=64).contains(&w) {
        return Ok(None);
    }
    let an = cx.node(arg);
    if an.op != OpCode::And {
        return Ok(None);
    }
    #[derive(Copy, Clone)]
    enum Kind {
        Add(u32, u32),
        Sub(u32, u32),
        SubInc(u32, u32), // b - a - 1  (via ~a + b)
    }
    let match_pair = |p: u32, q: u32| -> Option<Kind> {
        let pn = cx.node(p);
        let qn = cx.node(q);
        if qn.op != OpCode::Xor {
            return None;
        }
        if pn.op == OpCode::Xor {
            let (u, v) = (pn.a, pn.b);
            for (sum_or_diff, partner) in [(qn.a, qn.b), (qn.b, qn.a)] {
                let other = if partner == u {
                    v
                } else if partner == v {
                    u
                } else {
                    continue;
                };
                let sn = cx.node(sum_or_diff);
                if sn.op == OpCode::Sub && sn.a == partner && sn.b == other {
                    return Some(Kind::Sub(partner, other));
                }
                if sn.op == OpCode::Add {
                    for (na, nb) in [(sn.a, sn.b), (sn.b, sn.a)] {
                        if nb == partner && cx.node(na).op == OpCode::Not && cx.node(na).a == other
                        {
                            return Some(Kind::SubInc(partner, other));
                        }
                    }
                }
            }
        } else if pn.op == OpCode::Not && cx.node(pn.a).op == OpCode::Xor {
            let xn = cx.node(pn.a);
            let (u, v) = (xn.a, xn.b);
            for (sum, partner) in [(qn.a, qn.b), (qn.b, qn.a)] {
                if partner != u && partner != v {
                    continue;
                }
                let sn = cx.node(sum);
                if sn.op == OpCode::Add && ((sn.a == u && sn.b == v) || (sn.a == v && sn.b == u)) {
                    return Some(Kind::Add(u, v));
                }
            }
        }
        None
    };
    let Some(kind) = match_pair(an.a, an.b).or_else(|| match_pair(an.b, an.a)) else {
        return Ok(None);
    };
    let (lhs, rhs) = match kind {
        Kind::Add(x, y) | Kind::Sub(x, y) | Kind::SubInc(x, y) => (x, y),
    };
    let (fl, fin_l) = super::facts(r, cx, lhs)?;
    let (fr, fin_r) = super::facts(r, cx, rhs)?;
    let (Some(fl), Some(fr)) = (fl, fr) else {
        return Ok(None);
    };
    let to_i128 = |v: &BitVec| -> Option<i128> {
        let u = v.to_u64()?;
        let sh = 64 - u32::from(w);
        Some(i128::from(((u << sh) as i64) >> sh))
    };
    let (Some(ll), Some(lh), Some(rl), Some(rh)) = (
        to_i128(&fl.srange().lo()),
        to_i128(&fl.srange().hi()),
        to_i128(&fr.srange().lo()),
        to_i128(&fr.srange().hi()),
    ) else {
        return Ok(None);
    };
    let (lo, hi) = match kind {
        Kind::Add(..) => (ll + rl, lh + rh),
        Kind::Sub(..) => (ll - rh, lh - rl),
        Kind::SubInc(..) => (ll - rh - 1, lh - rl - 1),
    };
    let smin_w = -(1i128 << (w - 1));
    let smax_w = (1i128 << (w - 1)) - 1;
    let fin = fin_l.and(fin_r);
    if lo >= smin_w && hi <= smax_w {
        Ok(Some((!want_overflow, fin)))
    } else if lo > smax_w || hi < smin_w {
        Ok(Some((want_overflow, fin)))
    } else {
        Ok(None)
    }
}

/// Peel identical enclosing operations from `a` and `b` while tracking the surviving low
/// bit prefix `bits` such that `pa ≡ pb (mod 2^bits)` implies `a == b`. Forward congruence
/// only: equal arguments under a shared operation imply equal outputs, never the converse.
fn peel_congruence(cx: &Context, mut a: u32, mut b: u32) -> (u32, u32, u16) {
    let mut bits = cx.wid(a);
    for _ in 0..MAX_PEEL {
        if a == b || bits == 0 {
            break;
        }
        let (x, y) = (cx.node(a), cx.node(b));
        if x.width != y.width || x.op != y.op {
            break;
        }
        match x.op {
            OpCode::Add => {
                if x.a == y.a {
                    (a, b) = (x.b, y.b);
                } else if x.b == y.b {
                    (a, b) = (x.a, y.a);
                } else if x.a == y.b {
                    (a, b) = (x.b, y.a);
                } else if x.b == y.a {
                    (a, b) = (x.a, y.b);
                } else {
                    break;
                }
            }
            OpCode::Sub => {
                if x.a == y.a {
                    (a, b) = (x.b, y.b);
                } else if x.b == y.b {
                    (a, b) = (x.a, y.a);
                } else {
                    break;
                }
            }
            OpCode::Not | OpCode::Neg => (a, b) = (x.a, y.a),
            OpCode::Zext | OpCode::Sext => {
                let wa = cx.wid(x.a);
                if wa != cx.wid(y.a) {
                    break;
                }
                bits = bits.min(wa);
                (a, b) = (x.a, y.a);
            }
            OpCode::Extract if x.b == y.b => {
                let wa = cx.wid(x.a);
                let Some(need) = u16::try_from(x.b).ok().and_then(|lo| lo.checked_add(bits)) else {
                    break;
                };
                if wa != cx.wid(y.a) || need > wa {
                    break;
                }
                bits = need;
                (a, b) = (x.a, y.a);
            }
            OpCode::Concat => {
                if cx.wid(x.a) != cx.wid(y.a) || cx.wid(x.b) != cx.wid(y.b) {
                    break;
                }
                let w_lo = cx.wid(x.b);
                if x.a == y.a {
                    bits = bits.min(w_lo);
                    (a, b) = (x.b, y.b);
                } else if x.b == y.b {
                    bits = bits.saturating_sub(w_lo);
                    (a, b) = (x.a, y.a);
                } else {
                    break;
                }
            }
            OpCode::Select => {
                if x.a == y.a && x.b == y.b {
                    (a, b) = (x.c, y.c);
                } else if x.a == y.a && x.c == y.c {
                    (a, b) = (x.b, y.b);
                } else if x.b == y.b && x.c == y.c {
                    bits = 1;
                    (a, b) = (x.a, y.a);
                } else {
                    break;
                }
            }
            _ if x.op.as_cmp().is_some() || x.op.as_bin().is_some() => {
                let swapped = x.op.as_bin().is_some_and(BinOp::is_commutative)
                    || x.op.as_cmp().is_some_and(CmpOp::is_commutative);
                let (next_a, next_b, shared, is_lhs) = if x.a == y.a {
                    (x.b, y.b, x.a, false)
                } else if x.b == y.b {
                    (x.a, y.a, x.b, true)
                } else if swapped && x.a == y.b {
                    (x.b, y.a, x.a, false)
                } else if swapped && x.b == y.a {
                    (x.a, y.b, x.b, true)
                } else {
                    break;
                };
                if cx.wid(next_a) != cx.wid(next_b) {
                    break;
                }
                bits = match x.op {
                    OpCode::Mul => {
                        if let Some(k) = cx.const_val(shared) {
                            let tz = crate::facts::known::trailing_zeros(&k).min(u32::from(bits));
                            bits.saturating_sub(tz as u16)
                        } else {
                            bits
                        }
                    }
                    OpCode::And => {
                        if let Some(m) = cx.const_val(shared) {
                            let keep = crate::facts::known::low_mask(m.width(), u32::from(bits));
                            let active = crate::facts::known::bv_and(&m, &keep);
                            (u32::from(m.width().bits())
                                - crate::facts::known::leading_zeros(&active))
                                as u16
                        } else {
                            bits
                        }
                    }
                    OpCode::Or => {
                        if let Some(m) = cx.const_val(shared) {
                            let keep = crate::facts::known::low_mask(m.width(), u32::from(bits));
                            let active = crate::facts::known::bv_and(
                                &crate::facts::known::bv_not(&m),
                                &keep,
                            );
                            (u32::from(m.width().bits())
                                - crate::facts::known::leading_zeros(&active))
                                as u16
                        } else {
                            bits
                        }
                    }
                    OpCode::Xor => bits,
                    OpCode::Shl if is_lhs => {
                        if let Some(c) = cx.const_val(shared).and_then(|v| v.to_u64()) {
                            bits.saturating_sub(c.min(u64::from(bits)) as u16)
                        } else {
                            bits
                        }
                    }
                    OpCode::LShr if is_lhs => {
                        if let Some(c) = cx.const_val(shared).and_then(|v| v.to_u64()) {
                            bits.saturating_add(c.min(u64::from(u16::MAX)) as u16)
                                .min(cx.wid(next_a))
                        } else {
                            cx.wid(next_a)
                        }
                    }
                    _ => cx.wid(next_a),
                };
                (a, b) = (next_a, next_b);
            }
            _ => break,
        }
    }
    (a, b, bits)
}

/// The compares pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    #[cfg(feature = "prove")]
    if matches!(node.op, OpCode::Eq | OpCode::Ne)
        && let Some(vfin) = super::views::known(r, node.a, node.b)
        && r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(n)))
    {
        let before = cx.len() as u32;
        let c = bool_const(r, cx, node.op == OpCode::Eq)?;
        return finish(r, cx, PassKind::Compares, n, c, before, &[], vfin);
    }
    if node.op == OpCode::Select {
        let (c, t, f) = (node.a, node.b, node.c);
        // Canonicalize `select(a <=s b, 0, K) -> select(b <s a, K, 0)` (and `<=u`, `!=`),
        // placing zero in the `else` arm and `<`/`==` as the condition.
        if cx.const_val(t).is_some_and(|v| v.is_zero())
            && !cx.const_val(f).is_some_and(|v| v.is_zero())
        {
            let cn = cx.node(c);
            let neg_cmp = match cn.op {
                OpCode::Sle => Some((CmpOp::Slt, cn.b, cn.a)),
                OpCode::Ule => Some((CmpOp::Ult, cn.b, cn.a)),
                OpCode::Ne => Some((CmpOp::Eq, cn.a, cn.b)),
                _ => None,
            };
            if let Some((op2, x, y)) = neg_cmp {
                let before = cx.len() as u32;
                let c2 = r.build(cx, |cx| cx.c_cmp(op2, x, y))?;
                let e = r.build(cx, |cx| cx.c_select(c2, f, t))?;
                let mut stops = vec![x, y, f, t];
                stops.retain(|&id| id < before);
                stops.sort_unstable();
                stops.dedup();
                match super::finish_with(
                    r,
                    cx,
                    PassKind::Compares,
                    n,
                    e,
                    before,
                    &stops,
                    Fin::FINAL,
                    true,
                )? {
                    Step::Normal(_) => {}
                    step => return Ok(step),
                }
            }
        }
        // Canonicalize `select(x <=s -1, K, 0) -> select(x <s 0, K, 0)` (after `Info::Values`
        // pulls `sext(x) <s 0` into `x <=s -1`) so both forms unify on `select(x <s 0, K, 0)`.
        if cx.const_val(f).is_some_and(|v| v.is_zero())
            && !cx.const_val(t).is_some_and(|v| v.is_zero())
            && cx.node(c).op == OpCode::Sle
            && cx.const_val(cx.node(c).b).is_some_and(|v| v.is_ones())
        {
            let x = cx.node(c).a;
            let before = cx.len() as u32;
            let z = r.build(cx, |cx| cx.mk_const(&BitVec::zero(cx.width_of(x))))?;
            let c2 = r.build(cx, |cx| cx.c_cmp(CmpOp::Slt, x, z))?;
            let e = r.build(cx, |cx| cx.c_select(c2, t, f))?;
            let mut stops = vec![x, t, f, z];
            stops.retain(|&id| id < before);
            stops.sort_unstable();
            stops.dedup();
            match super::finish_with(
                r,
                cx,
                PassKind::Compares,
                n,
                e,
                before,
                &stops,
                Fin::FINAL,
                true,
            )? {
                Step::Normal(_) => {}
                step => return Ok(step),
            }
        }
        // Canonicalize `select(c, base + K, base) -> base + select(c, K, 0)` for non-leaf `base`
        // and constant `K` so factored and unfactored constant-offset select tables unify.
        if node.width <= 64 && !cx.is_const(f) && cx.meta[f as usize].tree >= 2 {
            let tn = cx.node(t);
            let k_id = if tn.op == OpCode::Add && tn.a == f && cx.is_const(tn.b) {
                Some(tn.b)
            } else if tn.op == OpCode::Add && tn.b == f && cx.is_const(tn.a) {
                Some(tn.a)
            } else {
                None
            };
            if let Some(k) = k_id {
                let before = cx.len() as u32;
                let zero = r.build(cx, |cx| cx.mk_const_u64(node.width, 0))?;
                let sel0 = r.build(cx, |cx| cx.c_select(c, k, zero))?;
                let e = r.build(cx, |cx| cx.c_bin(BinOp::Add, f, sel0))?;
                let mut stops = vec![c, f, k];
                if zero < before {
                    stops.push(zero);
                }
                stops.sort_unstable();
                stops.dedup();
                match super::finish_with(
                    r,
                    cx,
                    PassKind::Compares,
                    n,
                    e,
                    before,
                    &stops,
                    Fin::FINAL,
                    true,
                )? {
                    Step::Normal(_) => {}
                    step => return Ok(step),
                }
            }
        }
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
    if let Some((mc, fin)) = exhaustive_mask_cases(r, cx, n)? {
        let before = cx.len() as u32;
        let (e, atoms) = match mc {
            MaskCase::Expr(c) => (c, vec![c]),
            MaskCase::Const(b) => (bool_const(r, cx, b)?, Vec::new()),
            MaskCase::Bit { expr, bit, set } => {
                let e = r.build(cx, |cx| {
                    let b = cx.c_extract(expr, bit, 1)?;
                    if set { Ok(b) } else { cx.c_un(UnOp::Not, b) }
                })?;
                (e, vec![expr])
            }
        };
        return finish(r, cx, PassKind::Compares, n, e, before, &atoms, fin);
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
    if let Some((x, k, set, fin)) = sign_extend_sign_test(r, cx, n)? {
        let before = cx.len() as u32;
        let e = r.build(cx, |cx| {
            let b = cx.c_extract(x, k, 1)?;
            if set { Ok(b) } else { cx.c_un(UnOp::Not, b) }
        })?;
        return finish(r, cx, PassKind::Compares, n, e, before, &[x], fin);
    }
    if let Some((val, fin)) = signed_overflow_sign_test(r, cx, n)? {
        let before = cx.len() as u32;
        let e = r.build(cx, |cx| cx.mk_const_u64(1, u64::from(val)))?;
        return finish(r, cx, PassKind::Compares, n, e, before, &[], fin);
    }
    // Population-count boundary comparisons (`popcnt(x) == 0 -> x == 0`, `popcnt(x) != 0 ->
    // x != 0`, `popcnt(x) <=u 0 -> x == 0`, `0 <u popcnt(x) -> x != 0`, and all-ones counterparts
    // `popcnt(x) == W -> x == -1`, `popcnt(x) != W -> x != -1` across casts of `popcnt(x)`).
    if let Some(cmp) = node.op.as_cmp() {
        if r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(n)))
            && let Some(decided) = super::shuffle::decide_cmp_by_bits(r, cx, cmp, node.a, node.b)?
        {
            let before = cx.len() as u32;
            let c = bool_const(r, cx, decided)?;
            return finish(r, cx, PassKind::Compares, n, c, before, &[], Fin::FINAL);
        }
        let popcnt_arg = |cx: &Context, id: u32| -> Option<u32> {
            let mut cur = id;
            for _ in 0..3 {
                let pn = cx.node(cur);
                if pn.op == OpCode::Popcnt {
                    return Some(pn.a);
                }
                if pn.op == OpCode::Zext || (pn.op == OpCode::Sext && cx.wid(pn.a) > 1) {
                    cur = pn.a;
                } else {
                    break;
                }
            }
            None
        };
        let pop_cmp = if let (Some(x), Some(c)) = (popcnt_arg(cx, node.a), cx.const_val(node.b)) {
            Some((x, c, false))
        } else if let (Some(c), Some(x)) = (cx.const_val(node.a), popcnt_arg(cx, node.b)) {
            Some((x, c, true))
        } else {
            None
        };
        if let Some((x, c, const_lhs)) = pop_cmp {
            let wx = cx.width_of(x);
            let wc = c.width();
            let is_zero = c.is_zero();
            let is_all_bits = (wc.bits() >= 10 || u32::from(wx.bits()) < (1u32 << wc.bits()))
                && c == BitVec::wrapping_from_u64(wc, u64::from(wx.bits()));
            let target = match (cmp, const_lhs) {
                (CmpOp::Eq, _) if is_zero => Some((CmpOp::Eq, BitVec::zero(wx))),
                (CmpOp::Ne, _) if is_zero => Some((CmpOp::Ne, BitVec::zero(wx))),
                (CmpOp::Ule, false) if is_zero => Some((CmpOp::Eq, BitVec::zero(wx))),
                (CmpOp::Ult, true) if is_zero => Some((CmpOp::Ne, BitVec::zero(wx))),
                (CmpOp::Eq, _) if is_all_bits => Some((CmpOp::Eq, BitVec::ones(wx))),
                (CmpOp::Ne, _) if is_all_bits => Some((CmpOp::Ne, BitVec::ones(wx))),
                (CmpOp::Ule, true) if is_all_bits => Some((CmpOp::Eq, BitVec::ones(wx))),
                (CmpOp::Ult, false) if is_all_bits => Some((CmpOp::Ne, BitVec::ones(wx))),
                _ => None,
            };
            if let Some((eq_op, target_bv)) = target {
                let before = cx.len() as u32;
                let e = r.build(cx, |cx| {
                    let kc = cx.mk_const(&target_bv)?;
                    cx.c_cmp(eq_op, x, kc)
                })?;
                let tie = cx.meta[n as usize].tree != u32::MAX
                    && cx.meta[e as usize].tree < cx.meta[n as usize].tree;
                match super::finish_with(
                    r,
                    cx,
                    PassKind::Compares,
                    n,
                    e,
                    before,
                    &[x],
                    Fin::FINAL,
                    tie,
                )? {
                    Step::Normal(_) => {}
                    done => return Ok(done),
                }
            }
        }
    }
    // Canonicalize complemented unsigned comparisons (`~X <u ~Y -> Y <u X`, `(C - U) <u ~Y ->
    // Y <u U + ~C`, and `<=u` counterparts), strictly shrinking by stripping `Not`.
    if matches!(node.op, OpCode::Ult | OpCode::Ule) && cx.wid(node.a) <= 64 {
        let cmp = if node.op == OpCode::Ult {
            CmpOp::Ult
        } else {
            CmpOp::Ule
        };
        #[derive(Clone, Copy)]
        enum CompSide {
            Plain(u32),
            Xor(u32, u32),
            AddConst(u32, BitVec),
        }
        let comp_of = |cx: &Context, id: u32| -> Option<CompSide> {
            let m = cx.node(id);
            if m.op == OpCode::Not {
                return Some(CompSide::Plain(m.a));
            }
            if m.op == OpCode::Xor {
                if cx.node(m.a).op == OpCode::Not {
                    return Some(CompSide::Xor(cx.node(m.a).a, m.b));
                }
                if cx.node(m.b).op == OpCode::Not {
                    return Some(CompSide::Xor(m.a, cx.node(m.b).a));
                }
            }
            if m.op == OpCode::Sub
                && let Some(c) = cx.const_val(m.a)
            {
                return Some(CompSide::AddConst(m.b, BitVec::un_unchecked(UnOp::Not, &c)));
            }
            if m.op == OpCode::Add
                && cx.node(m.a).op == OpCode::Neg
                && let Some(c) = cx.const_val(m.b)
            {
                return Some(CompSide::AddConst(
                    cx.node(m.a).a,
                    BitVec::un_unchecked(UnOp::Not, &c),
                ));
            }
            None
        };
        if let (Some(la), Some(rb)) = (comp_of(cx, node.a), comp_of(cx, node.b))
            && (!matches!(la, CompSide::AddConst(..)) || !matches!(rb, CompSide::AddConst(..)))
        {
            let before = cx.len() as u32;
            let mut stops = Vec::with_capacity(4);
            let build_side = |r: &mut Runner<'_, '_>,
                              cx: &mut Context,
                              side: CompSide,
                              stops: &mut Vec<u32>|
             -> Result<u32, Stop> {
                match side {
                    CompSide::Plain(x) => {
                        stops.push(x);
                        Ok(x)
                    }
                    CompSide::Xor(a, b) => {
                        stops.push(a);
                        stops.push(b);
                        r.build(cx, |cx| cx.c_bin(BinOp::Xor, a, b))
                    }
                    CompSide::AddConst(u, nc) => {
                        stops.push(u);
                        let kv = r.build(cx, |cx| cx.mk_const(&nc))?;
                        if kv < before {
                            stops.push(kv);
                        }
                        r.build(cx, |cx| cx.c_bin(BinOp::Add, u, kv))
                    }
                }
            };
            let new_lhs = build_side(r, cx, rb, &mut stops)?;
            let new_rhs = build_side(r, cx, la, &mut stops)?;
            let e = r.build(cx, |cx| cx.c_cmp(cmp, new_lhs, new_rhs))?;
            match finish(r, cx, PassKind::Compares, n, e, before, &stops, Fin::FINAL)? {
                Step::Normal(_) => {}
                step => return Ok(step),
            }
        }
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
            // Fallback when `Info::Values` skipped `sext(x)` because `dag_size(x) > 256`:
            // strip `sext` in signed/equality tests against `0`.
            if let Some(cmp) = node.op.as_cmp()
                && matches!(cmp, CmpOp::Slt | CmpOp::Sle | CmpOp::Eq | CmpOp::Ne)
            {
                let sext_zero = if cx.node(node.a).op == OpCode::Sext
                    && cx.const_val(node.b).is_some_and(|v| v.is_zero())
                {
                    Some((cx.node(node.a).a, true))
                } else if cx.node(node.b).op == OpCode::Sext
                    && cx.const_val(node.a).is_some_and(|v| v.is_zero())
                {
                    Some((cx.node(node.b).a, false))
                } else {
                    None
                };
                if let Some((x, x_lhs)) = sext_zero {
                    let before = cx.len() as u32;
                    let nw = cx.width_of(x);
                    let z = r.build(cx, |cx| cx.mk_const(&BitVec::zero(nw)))?;
                    let e2 = r.build(cx, |cx| {
                        if x_lhs {
                            cx.c_cmp(cmp, x, z)
                        } else {
                            cx.c_cmp(cmp, z, x)
                        }
                    })?;
                    let mut stops = vec![x];
                    if z < before {
                        stops.push(z);
                    }
                    match super::finish_with(
                        r,
                        cx,
                        PassKind::Compares,
                        n,
                        e2,
                        before,
                        &stops,
                        Fin::FINAL,
                        true,
                    )? {
                        Step::Normal(_) => {}
                        step => return Ok(step),
                    }
                }
            }
            // Multi-term unsigned carry cancellation:
            // `(B + R) <u B => ~B <u R`, `B <=u (B + R) => R <=u ~B`,
            // `B <u (B + R) => B <u -R`, and `(B + R) <=u B => -R <=u B`
            // when `B`'s additive leaves are a sub-multiset of `B + R`.
            if matches!(node.op, OpCode::Ult | OpCode::Ule) {
                let collect_add = |cx: &Context, root: u32| -> Option<Vec<u32>> {
                    let mut out = Vec::with_capacity(8);
                    let mut st = vec![root];
                    while let Some(cur) = st.pop() {
                        if out.len() + st.len() > 16 {
                            return None;
                        }
                        let cn = cx.node(cur);
                        if cn.op == OpCode::Add {
                            st.push(cn.b);
                            st.push(cn.a);
                        } else {
                            out.push(cur);
                        }
                    }
                    Some(out)
                };
                for (sum_id, sub_id, sum_is_lhs) in
                    [(node.a, node.b, true), (node.b, node.a, false)]
                {
                    if cx.node(sum_id).op != OpCode::Add {
                        continue;
                    }
                    if let (Some(mut s_leaves), Some(b_leaves)) =
                        (collect_add(cx, sum_id), collect_add(cx, sub_id))
                        && b_leaves.len() < s_leaves.len()
                        && (b_leaves.len() >= 2 || s_leaves.len() >= 3)
                    {
                        let mut matched_all = true;
                        for &bl in &b_leaves {
                            if let Some(pos) = s_leaves.iter().position(|&x| x == bl) {
                                s_leaves.remove(pos);
                            } else {
                                matched_all = false;
                                break;
                            }
                        }
                        if matched_all && !s_leaves.is_empty() {
                            s_leaves.sort_by(|&a, &b| cx.order(a, b));
                            let before = cx.len() as u32;
                            let mut rem = s_leaves[0];
                            for &t in &s_leaves[1..] {
                                rem = r.build(cx, |cx| cx.c_bin(BinOp::Add, rem, t))?;
                            }
                            let is_ult = node.op == OpCode::Ult;
                            let e2 = if (is_ult && sum_is_lhs) || (!is_ult && !sum_is_lhs) {
                                // `(B + R) <u B => ~B <u R` and `B <=u (B + R) => R <=u ~B`
                                let not_b = r.build(cx, |cx| cx.c_un(UnOp::Not, sub_id))?;
                                r.build(cx, |cx| {
                                    if is_ult {
                                        cx.c_cmp(CmpOp::Ult, not_b, rem)
                                    } else {
                                        cx.c_cmp(CmpOp::Ule, rem, not_b)
                                    }
                                })?
                            } else {
                                // `B <u (B + R) => B <u -R` and `(B + R) <=u B => -R <=u B`
                                let neg_r = r.build(cx, |cx| cx.c_un(UnOp::Neg, rem))?;
                                r.build(cx, |cx| {
                                    if is_ult {
                                        cx.c_cmp(CmpOp::Ult, sub_id, neg_r)
                                    } else {
                                        cx.c_cmp(CmpOp::Ule, neg_r, sub_id)
                                    }
                                })?
                            };
                            let mut stops = s_leaves;
                            if !stops.contains(&sub_id) {
                                stops.push(sub_id);
                            }
                            match super::finish_with(
                                r,
                                cx,
                                PassKind::Compares,
                                n,
                                e2,
                                before,
                                &stops,
                                Fin::FINAL,
                                true,
                            )? {
                                Step::Normal(_) => {}
                                step => return Ok(step),
                            }
                        }
                    }
                }
            }
            // `(A * select(c, 0, k)) ==/!= (B * select(c, 0, k))` (or `select(c, k, 0)`):
            // hoist the zero-annihilating `select` factor out of `Eq`/`Ne` into `select(c, ...)`
            // so `arms_read` can specialize `c` inside `A` and `B`.
            if matches!(node.op, OpCode::Eq | OpCode::Ne) && cx.wid(node.a) > 1 {
                let (la, lb) = (cx.node(node.a), cx.node(node.b));
                if la.op == OpCode::Mul && lb.op == OpCode::Mul {
                    let shared_sel = [
                        (la.a, la.b, lb.a, lb.b),
                        (la.a, la.b, lb.b, lb.a),
                        (la.b, la.a, lb.a, lb.b),
                        (la.b, la.a, lb.b, lb.a),
                    ]
                    .into_iter()
                    .find_map(|(sa, xa, sb, xb)| {
                        (sa == sb && cx.node(sa).op == OpCode::Select).then_some((sa, xa, xb))
                    });
                    if let Some((sel_id, xa, xb)) = shared_sel {
                        let sn = cx.node(sel_id);
                        let zero_arm = if cx.const_val(sn.b).is_some_and(|v| v.is_zero()) {
                            Some((true, sn.c))
                        } else if cx.const_val(sn.c).is_some_and(|v| v.is_zero()) {
                            Some((false, sn.b))
                        } else {
                            None
                        };
                        if let Some((true_is_zero, k_other)) = zero_arm {
                            let is_eq = node.op == OpCode::Eq;
                            let cmp_op = if is_eq { CmpOp::Eq } else { CmpOp::Ne };
                            let before = cx.len() as u32;
                            let zero_val = bool_const(r, cx, is_eq)?;
                            let e_sel = r.build(cx, |cx| {
                                let ma = cx.c_bin(BinOp::Mul, xa, k_other)?;
                                let mb = cx.c_bin(BinOp::Mul, xb, k_other)?;
                                let cmp = cx.c_cmp(cmp_op, ma, mb)?;
                                if true_is_zero {
                                    cx.c_select(sn.a, zero_val, cmp)
                                } else {
                                    cx.c_select(sn.a, cmp, zero_val)
                                }
                            })?;
                            let mut stops = Vec::with_capacity(4);
                            for id in [sn.a, xa, xb, k_other] {
                                if id < before && !cx.is_const(id) && !stops.contains(&id) {
                                    stops.push(id);
                                }
                            }
                            match super::finish_with(
                                r,
                                cx,
                                PassKind::Compares,
                                n,
                                e_sel,
                                before,
                                &stops,
                                Fin::FINAL,
                                true,
                            )? {
                                Step::Normal(_) => {}
                                step => return Ok(step),
                            }
                        }
                    }
                }
            }
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
                && let (Some(same), fin) = super::bitwise::equal(r, cx, node.a, node.b)?
            {
                let before = cx.len() as u32;
                let c = bool_const(r, cx, same == (node.op == OpCode::Eq))?;
                return finish(r, cx, PassKind::Compares, n, c, before, &[], fin);
            }
            if matches!(node.op, OpCode::Eq | OpCode::Ne)
                && cx.wid(node.a) > 1
                && super::linear_mba::equal(r, cx, node.a, node.b)?
            {
                let before = cx.len() as u32;
                let c = bool_const(r, cx, node.op == OpCode::Eq)?;
                return finish(r, cx, PassKind::Compares, n, c, before, &[], Fin::FINAL);
            }
            if matches!(node.op, OpCode::Eq | OpCode::Ne)
                && cx.wid(node.a) > 1
                && r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(n)))
                && let Some(wfin) =
                    super::words::prove_equal(r, cx, node.a, node.b, cx.wid(node.a))?
            {
                let before = cx.len() as u32;
                let c = bool_const(r, cx, node.op == OpCode::Eq)?;
                return finish(r, cx, PassKind::Compares, n, c, before, &[], wfin);
            }
            if matches!(node.op, OpCode::Eq | OpCode::Ne)
                && cx.wid(node.a) > 1
                && !cx.is_const(node.a)
                && !cx.is_const(node.b)
                && (matches!(
                    cx.node(node.a).op,
                    OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Mul
                ) || matches!(
                    cx.node(node.b).op,
                    OpCode::Add | OpCode::Sub | OpCode::Neg | OpCode::Mul
                ))
            {
                let fa = super::linear::form_of(r, cx, node.a)?;
                let fb = super::linear::form_of(r, cx, node.b)?;
                let (ka, ta, fin_a) = super::forms::Parts::parts(&fa);
                let (kb, tb, fin_b) = super::forms::Parts::parts(&fb);
                let shares_atom = !ta.is_empty()
                    && !tb.is_empty()
                    && ta
                        .iter()
                        .any(|&(a, _)| tb.binary_search_by_key(&a, |t| t.0).is_ok());
                if shares_atom {
                    let mut merged = ta.to_vec();
                    for &(b_id, b_k) in tb {
                        let neg_bk = BitVec::un_unchecked(UnOp::Neg, &b_k);
                        match merged.binary_search_by_key(&b_id, |t| t.0) {
                            Ok(pos) => {
                                merged[pos].1 =
                                    BitVec::bin_unchecked(BinOp::Add, &merged[pos].1, &neg_bk);
                            }
                            Err(pos) => merged.insert(pos, (b_id, neg_bk)),
                        }
                    }
                    merged.retain(|(_, k)| !k.is_zero());
                    let stops: Vec<u32> = merged.iter().map(|&(a, _)| a).collect();
                    let dk = BitVec::bin_unchecked(BinOp::Sub, ka, kb);
                    let df_fin = fin_a.and(fin_b);
                    let df: super::linear::Form =
                        super::forms::Parts::from_parts(dk, merged, df_fin);
                    let before = cx.len() as u32;
                    let d_node = super::linear::emit(r, cx, &df)?;
                    let z_node = r.build(cx, |cx| cx.mk_const(&BitVec::zero(dk.width())))?;
                    let cmp_op = if node.op == OpCode::Eq {
                        CmpOp::Eq
                    } else {
                        CmpOp::Ne
                    };
                    let e_cmp = r.build(cx, |cx| cx.c_cmp(cmp_op, d_node, z_node))?;
                    match finish(r, cx, PassKind::Compares, n, e_cmp, before, &stops, df_fin)? {
                        Step::Normal(_) => {}
                        step => return Ok(step),
                    }
                }
            }
            if matches!(node.op, OpCode::Eq | OpCode::Ne) {
                let (pa, pb, bits) = peel_congruence(cx, node.a, node.b);
                let mut fin = Fin::FINAL;
                let mut proved = pa == pb || bits == 0;
                if !proved && (pa != node.a || pb != node.b) && bits > 1 {
                    proved = super::poly::equal_mod(r, cx, pa, pb, bits)?;
                    if !proved && bits == cx.wid(pa) {
                        if let (Some(true), f) = super::bitwise::equal(r, cx, pa, pb)? {
                            proved = true;
                            fin = f;
                        }
                        if !proved {
                            proved = super::linear_mba::equal(r, cx, pa, pb)?;
                        }
                    }
                    if !proved
                        && r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(n)))
                        && let Some(wfin) = super::words::prove_equal(r, cx, pa, pb, bits)?
                    {
                        proved = true;
                        fin = wfin;
                    }
                }
                #[cfg(feature = "mba")]
                if !proved {
                    if bits == 1 {
                        proved = super::mba::equal_lanes(r, cx, pa, pb, 1)?;
                    } else {
                        proved = super::mba::equal_sums(r, cx, pa, pb, bits)?;
                    }
                }
                // Binary congruence fallback: if `pa` and `pb` share a binary opcode at full width
                // and both operand pairs are independently provably equal (e.g. `(A1 | B1) == (A2 | B2)`
                // where neither half is syntactically identical yet), then `pa == pb`.
                if !proved && bits == cx.wid(pa) {
                    let (nx, ny) = (cx.node(pa), cx.node(pb));
                    if nx.op == ny.op
                        && matches!(
                            nx.op,
                            OpCode::Or
                                | OpCode::And
                                | OpCode::Xor
                                | OpCode::Add
                                | OpCode::Sub
                                | OpCode::Mul
                        )
                        && cx.wid(nx.a) == cx.wid(ny.a)
                    {
                        let pair_eq = |r: &mut Runner<'_, '_>,
                                       cx: &mut Context,
                                       x: u32,
                                       y: u32|
                         -> Result<(bool, Fin), Stop> {
                            if x == y {
                                return Ok((true, Fin::FINAL));
                            }
                            let (qa, qb, qbits) = peel_congruence(cx, x, y);
                            if qa == qb || qbits == 0 {
                                return Ok((true, Fin::FINAL));
                            }
                            if qbits > 1 && super::poly::equal_mod(r, cx, qa, qb, qbits)? {
                                return Ok((true, Fin::FINAL));
                            }
                            if qbits == cx.wid(qa) {
                                if let (Some(true), f) = super::bitwise::equal(r, cx, qa, qb)? {
                                    return Ok((true, f));
                                }
                                if super::linear_mba::equal(r, cx, qa, qb)? {
                                    return Ok((true, Fin::FINAL));
                                }
                            }
                            #[cfg(feature = "mba")]
                            if qbits <= 64 && super::mba::equal_lanes(r, cx, qa, qb, qbits)? {
                                return Ok((true, Fin::FINAL));
                            }
                            Ok((false, Fin::FINAL))
                        };
                        let comm = nx.op.as_bin().is_some_and(BinOp::is_commutative);
                        let (eq_aa, f1) = pair_eq(r, cx, nx.a, ny.a)?;
                        if eq_aa {
                            let (eq_bb, f2) = pair_eq(r, cx, nx.b, ny.b)?;
                            if eq_bb {
                                proved = true;
                                fin = fin.and(f1).and(f2);
                            }
                        } else if comm {
                            let (eq_ab, f1) = pair_eq(r, cx, nx.a, ny.b)?;
                            if eq_ab {
                                let (eq_ba, f2) = pair_eq(r, cx, nx.b, ny.a)?;
                                if eq_ba {
                                    proved = true;
                                    fin = fin.and(f1).and(f2);
                                }
                            }
                        }
                    }
                }
                if proved {
                    let before = cx.len() as u32;
                    let c = bool_const(r, cx, node.op == OpCode::Eq)?;
                    return finish(r, cx, PassKind::Compares, n, c, before, &[], fin);
                }
                // Partial-arm `select` congruence: `select(c, X, A) == select(c, X, B)` is
                // `c | (A == B)` (and `select(c, A, X) == select(c, B, X)` is `!c | (A == B)`),
                // dropping a `select` node and exposing `A == B` directly.
                let (la, rb) = (cx.node(node.a), cx.node(node.b));
                if la.op == OpCode::Select && rb.op == OpCode::Select && la.a == rb.a {
                    let shared_arm = if la.b == rb.b {
                        Some((la.a, false, la.c, rb.c))
                    } else if la.c == rb.c {
                        Some((la.a, true, la.b, rb.b))
                    } else {
                        None
                    };
                    if let Some((cond, neg_cond, arm_a, arm_b)) = shared_arm {
                        let before = cx.len() as u32;
                        let is_eq = node.op == OpCode::Eq;
                        let cmp_op = if is_eq { CmpOp::Eq } else { CmpOp::Ne };
                        let inner_cmp = r.build(cx, |cx| cx.c_cmp(cmp_op, arm_a, arm_b))?;
                        let e = if is_eq {
                            let guard = if neg_cond {
                                r.build(cx, |cx| cx.c_un(UnOp::Not, cond))?
                            } else {
                                cond
                            };
                            r.build(cx, |cx| cx.c_bin(BinOp::Or, guard, inner_cmp))?
                        } else {
                            let guard = if neg_cond {
                                cond
                            } else {
                                r.build(cx, |cx| cx.c_un(UnOp::Not, cond))?
                            };
                            r.build(cx, |cx| cx.c_bin(BinOp::And, guard, inner_cmp))?
                        };
                        let mut stops = vec![cond, arm_a, arm_b];
                        stops.sort_unstable();
                        stops.dedup();
                        match finish(r, cx, PassKind::Compares, n, e, before, &stops, Fin::FINAL)? {
                            Step::Normal(_) => {}
                            step => return Ok(step),
                        }
                    }
                }
                // Single-side `select` equality: `select(c, X, A) == X` is `c | (A == X)` and
                // `select(c, A, X) == X` is `!c | (A == X)` (and `!=` is `!c & (A != X)` /
                // `c & (A != X)`), dropping the wide mux and exposing the active branch condition.
                let one_side = if la.op == OpCode::Select {
                    if la.b == node.b {
                        Some((la.a, false, la.c, node.b))
                    } else if la.c == node.b {
                        Some((la.a, true, la.b, node.b))
                    } else {
                        None
                    }
                } else if rb.op == OpCode::Select {
                    if rb.b == node.a {
                        Some((rb.a, false, rb.c, node.a))
                    } else if rb.c == node.a {
                        Some((rb.a, true, rb.b, node.a))
                    } else {
                        None
                    }
                } else {
                    None
                };
                if let Some((cond, neg_cond, other_arm, target)) = one_side {
                    let before = cx.len() as u32;
                    let is_eq = node.op == OpCode::Eq;
                    let cmp_op = if is_eq { CmpOp::Eq } else { CmpOp::Ne };
                    let inner_cmp = r.build(cx, |cx| cx.c_cmp(cmp_op, other_arm, target))?;
                    let e = if is_eq {
                        let guard = if neg_cond {
                            r.build(cx, |cx| cx.c_un(UnOp::Not, cond))?
                        } else {
                            cond
                        };
                        r.build(cx, |cx| cx.c_bin(BinOp::Or, guard, inner_cmp))?
                    } else {
                        let guard = if neg_cond {
                            cond
                        } else {
                            r.build(cx, |cx| cx.c_un(UnOp::Not, cond))?
                        };
                        r.build(cx, |cx| cx.c_bin(BinOp::And, guard, inner_cmp))?
                    };
                    let mut stops = vec![cond, other_arm, target];
                    stops.sort_unstable();
                    stops.dedup();
                    match super::finish_with(
                        r,
                        cx,
                        PassKind::Compares,
                        n,
                        e,
                        before,
                        &stops,
                        Fin::FINAL,
                        true,
                    )? {
                        Step::Normal(_) => {}
                        step => return Ok(step),
                    }
                }
            }
            let mut spec_fin = Fin::FINAL;
            if matches!(node.op, OpCode::And | OpCode::Or)
                && cx.wid(n) == 1
                && cx.meta[n as usize].tree <= 192
                && r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(n)))
            {
                let before = cx.len() as u32;
                if let Some(e_spec) =
                    r.build(cx, |cx| super::context::specialize_bool_bin(cx, n))?
                    && e_spec != n
                {
                    let stops = stops_below(cx, n, e_spec);
                    let tie = cx.meta[n as usize].tree != u32::MAX
                        && cx.meta[e_spec as usize].tree < cx.meta[n as usize].tree;
                    match super::finish_with(
                        r,
                        cx,
                        PassKind::Compares,
                        n,
                        e_spec,
                        before,
                        &stops,
                        Fin::FINAL,
                        tie,
                    )? {
                        Step::Normal(df) => spec_fin = spec_fin.and(df),
                        step => return Ok(step),
                    }
                } else {
                    super::discard(r, cx, before);
                }
            }
            #[cfg(feature = "mba")]
            if matches!(node.op, OpCode::Eq | OpCode::Ne | OpCode::And | OpCode::Or)
                && cx.wid(n) == 1
            {
                let before = cx.len() as u32;
                if let Some(e) = super::mba::bit_table_reduce(r, cx, n)?
                    && e != n
                {
                    let stops = stops_below(cx, n, e);
                    return finish(r, cx, PassKind::Compares, n, e, before, &stops, spec_fin);
                }
            }
            if let Some(step) = packed_zero_or(r, cx, n)? {
                return Ok(step);
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
                    return finish(r, cx, PassKind::Compares, n, e, before, &[x], spec_fin);
                }
                super::discard(r, cx, before);
            }
            return Ok(match order_step(r, cx, n)? {
                Step::Normal(f) => Step::Normal(f.and(spec_fin)),
                step => step,
            });
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

/// Decompose packed zero-OR equalities `((x1 ^ c1) | (x2 ^ c2) | ...) == 0` into
/// `(x1 == c1) & (x2 == c2) & ...` (and `!= 0` into `!= | !=`) when at least one disjunct peels a
/// constant bijection (`Xor`, `Not`, `Sub`, `Add`).
fn packed_zero_or(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Option<Step>, Stop> {
    let node = cx.node(n);
    if !matches!(node.op, OpCode::Eq | OpCode::Ne) {
        return Ok(None);
    }
    let is_eq = node.op == OpCode::Eq;
    let lhs = if cx.const_val(node.b).is_some_and(|v| v.is_zero()) {
        node.a
    } else if cx.const_val(node.a).is_some_and(|v| v.is_zero()) {
        node.b
    } else {
        return Ok(None);
    };
    let w = cx.wid(lhs);
    if !(2..=64).contains(&w) || cx.node(lhs).op != OpCode::Or {
        return Ok(None);
    }
    let full = u64::MAX >> (64 - w);
    let mut leaves = Vec::with_capacity(4);
    let mut stack = vec![lhs];
    while let Some(cur) = stack.pop() {
        let m = cx.node(cur);
        if m.op == OpCode::Or && leaves.len() + stack.len() < 8 {
            stack.push(m.b);
            stack.push(m.a);
        } else {
            leaves.push(cur);
        }
    }
    if !(2..=8).contains(&leaves.len()) {
        return Ok(None);
    }
    let peel_one = |cx: &Context, id: u32| -> Option<(u32, u64)> {
        let m = cx.node(id);
        match m.op {
            OpCode::Xor => {
                if let Some(c) = cx.const_val(m.b).and_then(|v| v.to_u64()) {
                    Some((m.a, c & full))
                } else {
                    cx.const_val(m.a)
                        .and_then(|v| v.to_u64())
                        .map(|c| (m.b, c & full))
                }
            }
            OpCode::Sub => {
                if let Some(c) = cx.const_val(m.b).and_then(|v| v.to_u64()) {
                    Some((m.a, c & full))
                } else {
                    cx.const_val(m.a)
                        .and_then(|v| v.to_u64())
                        .map(|c| (m.b, c & full))
                }
            }
            OpCode::Add => {
                if let Some(c) = cx.const_val(m.b).and_then(|v| v.to_u64()) {
                    Some((m.a, c.wrapping_neg() & full))
                } else {
                    cx.const_val(m.a)
                        .and_then(|v| v.to_u64())
                        .map(|c| (m.b, c.wrapping_neg() & full))
                }
            }
            _ => None,
        }
    };
    let mut parts = Vec::with_capacity(leaves.len());
    for &l in &leaves {
        let Some((x, c)) = peel_one(cx, l) else {
            return Ok(None);
        };
        parts.push((x, c));
    }
    let before = cx.len() as u32;
    let cmp_op = if is_eq { CmpOp::Eq } else { CmpOp::Ne };
    let join_op = if is_eq { BinOp::And } else { BinOp::Or };
    let mut stops = Vec::with_capacity(parts.len() * 2);
    let mut acc: Option<u32> = None;
    for (x, c) in parts {
        if !stops.contains(&x) {
            stops.push(x);
        }
        let kv = r.build(cx, |cx| cx.mk_const_u64(w, c))?;
        if kv < before && !stops.contains(&kv) {
            stops.push(kv);
        }
        let cmp_id = r.build(cx, |cx| cx.c_cmp(cmp_op, x, kv))?;
        acc = Some(match acc {
            None => cmp_id,
            Some(prev) => r.build(cx, |cx| cx.c_bin(join_op, prev, cmp_id))?,
        });
    }
    let Some(e) = acc else {
        super::discard(r, cx, before);
        return Ok(None);
    };
    match super::finish_with(
        r,
        cx,
        PassKind::Compares,
        n,
        e,
        before,
        &stops,
        Fin::FINAL,
        true,
    )? {
        Step::Normal(_) => Ok(None),
        step => Ok(Some(step)),
    }
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
    // Canonicalize 1-bit Majority `select(a ^ b, t, a)` / `select(a ^ b, t, b)` by sorting its
    // 3 symmetric arguments `[t, a, b]` into `select(tri[1] ^ tri[2], tri[0], tri[1])`.
    let mut maj_fin = Fin::FINAL;
    if cx.wid(n) == 1 && cx.node(c).op == OpCode::Xor {
        let xn = cx.node(c);
        if f == xn.a || f == xn.b {
            let mut tri = [t, xn.a, xn.b];
            tri.sort_by(|&x, &y| cx.order(x, y));
            let before = cx.len() as u32;
            let e = if tri[0] == tri[1] {
                tri[0]
            } else if tri[1] == tri[2] {
                tri[1]
            } else {
                r.build(cx, |cx| {
                    let x = cx.c_bin(BinOp::Xor, tri[1], tri[2])?;
                    cx.c_select(x, tri[0], tri[1])
                })?
            };
            if e != n {
                let mut stops = tri.to_vec();
                stops.sort_unstable();
                stops.dedup();
                match super::finish_with(
                    r,
                    cx,
                    PassKind::Compares,
                    n,
                    e,
                    before,
                    &stops,
                    Fin::FINAL,
                    true,
                )? {
                    Step::Normal(df) => maj_fin = maj_fin.and(df),
                    done => return Ok(Some(done)),
                }
            }
        }
    }
    let before = cx.len() as u32;
    if let Some(e) = one_value(r, cx, c, t, f)? {
        let stops = stops_below(cx, n, e);
        return finish(r, cx, PassKind::Compares, n, e, before, &stops, maj_fin).map(Some);
    }
    super::discard(r, cx, before);
    // Specialize `t` (`c = true`) and `f` (`c = false`) under `c`'s bit-mask and relational
    // guard facts (including `trunc<k>(x) == trunc<k>(y)`, `(x & m) == (y & m)`, `x == y + k`,
    // and `c` / `!c` occurrences) when the resulting `select` strictly shrinks the DAG.
    if r.hooks.is_none_or(|h| h.fold_known(cx, cx.handle(n)))
        && (cx.meta[t as usize].tree <= 128 || cx.meta[f as usize].tree <= 128)
    {
        let before = cx.len() as u32;
        let t2 = if cx.meta[t as usize].tree <= 128 {
            r.build(cx, |cx| super::context::specialize_arm(cx, t, c, true))?
        } else {
            t
        };
        let f2 = if cx.meta[f as usize].tree <= 128 {
            r.build(cx, |cx| super::context::specialize_arm(cx, f, c, false))?
        } else {
            f
        };
        if t2 != t || f2 != f {
            let e = r.build(cx, |cx| cx.c_select(c, t2, f2))?;
            let stops = stops_below(cx, n, e);
            let tie = cx.meta[n as usize].tree != u32::MAX
                && cx.meta[e as usize].tree < cx.meta[n as usize].tree;
            match super::finish_with(
                r,
                cx,
                PassKind::Compares,
                n,
                e,
                before,
                &stops,
                maj_fin,
                tie,
            )? {
                Step::Normal(df) => maj_fin = maj_fin.and(df),
                step => return Ok(Some(step)),
            }
        } else {
            super::discard(r, cx, before);
        }
    }
    Ok((maj_fin != Fin::FINAL).then_some(Step::Normal(maj_fin)))
}

/// The nodes strictly below `n` that `e` reaches first, independent of arena capacity or
/// nodes left behind in `cx` by earlier rejected candidates.
fn stops_below(cx: &Context, n: u32, e: u32) -> Vec<u32> {
    let mut below = crate::hash::IdMap::<u32, ()>::default();
    let mut stack: Vec<u32> = cx.node(n).children().collect();
    while let Some(i) = stack.pop() {
        if below.len() >= 1024 || below.insert(i, ()).is_some() {
            continue;
        }
        stack.extend(cx.node(i).children());
    }
    let mut stops = Vec::new();
    let mut seen = crate::hash::IdMap::<u32, ()>::default();
    let mut todo = vec![e];
    while let Some(i) = todo.pop() {
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if below.contains_key(&i) {
            stops.push(i);
        } else {
            todo.extend(cx.node(i).children());
        }
    }
    stops
}

/// The one value `select(c, t, f)` takes, when it is one:
///
/// - arms that read `c` (a flag a `setcc` and a carry both spell): `t` with `c` true and `f`
///   with `c` false, when they come out alike (`select(c, zext(c), zext(c) + 1)` is 1);
/// - a value chosen by a test of `p` against a constant `k`: the arm taken when `p != k`,
///   when with `p` at `k` it is the other arm (a shift's flags by its count, `count != 0 ?
///   r == 0 : x == 0`, with `x << 0` being `x`; the shift's result itself likewise).
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
    // (Of any width: the arm in place of the select is the select's nodes fewer, and the
    // commit rule weighs what it shares with the code around it. A shift's flags are often
    // met after their select has been taken out of the comparisons, `select(count != 0, x
    // << count, x) == 0`.)
    let cn = cx.node(c);
    if !matches!(cn.op, OpCode::Eq | OpCode::Ne) {
        return Ok(None);
    }
    let (p, k) = match (cx.const_val(cn.a), cx.const_val(cn.b)) {
        (None, Some(_)) => (cn.a, cn.b),
        (Some(_), None) => (cn.b, cn.a),
        _ => return Ok(None),
    };
    let (held, other) = if cn.op == OpCode::Eq { (t, f) } else { (f, t) };
    // The value tested, and the same value as the arm may spell it: a test of the low bits
    // `trunc<n>(y)` is of `y & (2^n − 1)` too (the count of a shift, tested at its own
    // width and used at the word's).
    let mut repl = crate::hash::IdMap::default();
    if reads(cx, other, p) {
        repl.insert(p, k);
    }
    let pn = cx.node(p);
    if pn.op == OpCode::Extract
        && pn.b == 0
        && pn.width < 64
        && let Some(kv) = cx.const_val(k).and_then(|v| v.to_u64())
    {
        let (y, low) = (pn.a, (1u64 << pn.width) - 1);
        let mut seen = crate::hash::IdMap::<u32, ()>::default();
        let mut todo = vec![other];
        let mut masks = Vec::new();
        while let Some(v) = todo.pop() {
            if v < y || seen.insert(v, ()).is_some() || seen.len() > MAX_ARM {
                continue;
            }
            let vn = cx.node(v);
            let masked =
                |a: u32, b: u32| a == y && cx.const_val(b).and_then(|c| c.to_u64()) == Some(low);
            if vn.op == OpCode::And && (masked(vn.a, vn.b) || masked(vn.b, vn.a)) {
                masks.push(v);
                continue;
            }
            todo.extend(vn.children());
        }
        for m in masks {
            let w_m = cx.width_of(m);
            let to = r.build(cx, |cx| cx.mk_const(&BitVec::wrapping_from_u64(w_m, kv)))?;
            repl.insert(m, to);
        }
    }
    if repl.is_empty() {
        return Ok(None);
    }
    let at = r.build(cx, |cx| Ok(cx.substitute_ids(&[other], &repl)?[0]))?;
    Ok((at == held).then_some(other))
}

fn order_step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let before = cx.len() as u32;
    match super::order::decide(r, cx, n)? {
        Some((e, atoms, fin)) => finish(r, cx, PassKind::Compares, n, e, before, &atoms, fin),
        None => Ok(Step::Normal(Fin::FINAL)),
    }
}

#[cfg(all(test, feature = "prove"))]
mod extra_tests {
    use crate::{Context, ParseOptions, Width};

    #[test]
    fn compares_handles_bit_tables_sign_extend_tests_and_binary_congruence() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Exhaustive mask cases -> single-bit extract
            "let y = (x & 255) >>u 5; ((y == 1) | (y == 3) | (y == 5) | (y == 7)) == extract<5, 1>(x)",
            "let y = (x & 255) >>u 5; ((y == 0) | (y == 2) | (y == 4) | (y == 6)) == ~extract<5, 1>(x)",
            // Sign-extend sign test when high bits are known zero
            "let y = x & 255; (((y ^ 128) - 128) <s 0) == extract<7, 1>(x)",
            "let y = x & 255; (0 <=s ((y ^ 128) - 128)) == ~extract<7, 1>(x)",
            // Binary congruence fallback on Or of two independently equal operands
            "let l1 = (a ^ (b ^ a) & c) * 33 + d; let l2 = ((b & c) | (~c & a)) * 33 + d; \
             let r1 = (e ^ (f ^ e) & g) * 65 + h; let r2 = ((f & g) | (~g & e)) * 65 + h; \
             (l1 | r1) == (l2 | r2)",
            // Packed zero-OR equality decomposition
            "(((a ^ 0x123456789abcdef0) | (b ^ 59)) == 0) == ((a == 0x123456789abcdef0) & (b == 59))",
            // Complemented Ult + affine singleton equality -> Ule
            "let s14 = ~(x41 ^ x42); let u = ~(x9 + x10) - 0x526933fb38aafe58; \
             ((x9 + (x10 - s14) == 0) | (x9 + x10 <u s14)) \
             == ((0xad96cc04c75501a7 - u <u (~x41 ^ x42)) \
                 | ((x41 ^ x42) - u == 0x526933fb38aafe58))",
            // 2-bit masked single_bit_cube collapses to single extract
            "let m = x & 5; ((m == 1) | (m == 5)) == extract<0, 1>(x)",
            // sext<64>(x32:32) <s 0 strips sign-extension and canonicalizes in select
            "select(sext<64>(x32:32) <s 0, 7:64, 0) == select(x32 <s 0, 7:64, 0)",
            // Partial-arm select congruence when one arm already matches syntactically
            "let c = k == 0; select(c, (a ^ b) + 2 * (a & b), z) == select(c, a + b, z)",
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
    fn compares_rejects_unsound_sign_extend_when_high_bits_unknown() {
        let mut cx = Context::new();
        let opt = ParseOptions::width(Width::W64);
        let prover = crate::prove::Simplifiers::new();
        let cfg = crate::prove::Config::default().with_simplify_fuel(1 << 14);
        for text in [
            // Without `& 255`, high bits of `x` are unknown: `((x ^ 128) - 128) <s 0` != bit 7 of x
            "(((x ^ 128) - 128) <s 0) == extract<7, 1>(x)",
            "(((x & 511 ^ 128) - 128) <s 0) == extract<7, 1>(x)",
            // Binary congruence must reject unequal operands
            "((a * 33 + d) | (e * 65 + h)) == ((a * 33 + d) | (e * 65 + h + 1))",
            // Non-single-bit 2-bit masked subset (XOR of bits 0 and 2) is NOT extract<0, 1>(x)
            "let m = x & 5; ((m == 1) | (m == 4)) == extract<0, 1>(x)",
            // Partial-arm select congruence must reject unequal arms
            "let c = k == 0; select(c, a + b, z) == select(c, a + b + 1, z)",
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
