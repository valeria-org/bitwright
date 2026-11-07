//! Orderings through strictly monotone maps.
//!
//! A bijection preserves equality, not order: `x * 3 <u y * 3` says nothing about `x <u y`.
//! What an ordering sees through is a *strictly monotone* map from an order of the inner value
//! (unsigned or signed) to an order of the node: for `f` increasing from `O₁` to `O₂`,
//! `f(a) <₂ f(b)` is `a <₁ b`, and for `f` decreasing it is `b <₁ a` (likewise `<=`). Against
//! a constant, `f(a) <₂ c` is `a <₁ t` for a threshold `t`, or a constant.
//!
//! A layer is one node that is strictly monotone in one operand, the others (its *parameters*)
//! fixed:
//!
//! | Layer | From → to | Direction | Condition |
//! |-|-|-|-|
//! | `zext(v)` | U → U, U → S | increasing | none |
//! | `sext(v)` | S → S, U → U | increasing | none |
//! | `concat(v, k)` | U → U, S → S | increasing | none |
//! | `concat(k, v)` | U → U, U → S | increasing | none |
//! | `v + k`, `v - k`, `v ^ smin` | any | increasing | `v`'s range stays on one piece |
//! | `k - v`, `~v`, `-v` | any | decreasing | `v`'s range stays on one piece |
//! | `v * k` | U → U, S → S | by the sign of `k` | no overflow, `k` nonzero |
//! | `v << s` | U → U, S → S | increasing | no bit shifted out |
//!
//! A wrapping sum is monotone on each *piece* of its operand's range where it does not wrap
//! (as integers, `v + k` or `v + k - 2^W`), so the condition is that the range of `v` the facts
//! give lies on one piece; two operands compared through the same layer must lie on the same
//! piece. The facts about the inner value hold wherever the result is used, so the map need
//! only be monotone there. With constant parameters the orders are handled as one: in *key*
//! space, where a signed value `v` is read as `v ^ smin`, every order is the unsigned one, and a
//! map between different orders is the same map shifted by `smin`.
//!
//! Against a constant, the threshold is found by bisection over the inner value's range: the
//! comparison, as a function of the inner value, changes at most once there (the map is
//! strictly monotone, and a comparison with a constant is monotone in the map's order), so it
//! is a constant or one comparison with the value where it changes. Each layer of the chain
//! was classified on its own operand's range, so the image of the inner value's range under the
//! layers below it must stay inside that range: where it does not, the chain starts above.

use super::Oracle;
use crate::expr::{Context, OpCode};
use crate::facts::Facts;
use crate::ops::{BinOp, CmpOp};
use crate::{BitVec, Width};

/// An order on values of one width.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Order {
    /// Unsigned.
    U,
    /// Signed.
    S,
}

impl Order {
    /// The order a comparison decides, and whether it is strict; `None` for `==` and `!=`.
    pub(crate) fn of(op: CmpOp) -> Option<(Order, bool)> {
        Some(match op {
            CmpOp::Ult => (Order::U, true),
            CmpOp::Ule => (Order::U, false),
            CmpOp::Slt => (Order::S, true),
            CmpOp::Sle => (Order::S, false),
            CmpOp::Eq | CmpOp::Ne => return None,
        })
    }

    /// The comparison deciding this order, strict or not.
    pub(crate) fn cmp(self, strict: bool) -> CmpOp {
        match (self, strict) {
            (Order::U, true) => CmpOp::Ult,
            (Order::U, false) => CmpOp::Ule,
            (Order::S, true) => CmpOp::Slt,
            (Order::S, false) => CmpOp::Sle,
        }
    }

    fn other(self) -> Order {
        match self {
            Order::U => Order::S,
            Order::S => Order::U,
        }
    }

    /// The key of `v`: keys compare unsigned in this order. Its own inverse.
    fn key(self, v: &BitVec) -> BitVec {
        match self {
            Order::U => *v,
            Order::S => xor(v, &BitVec::smin(v.width())),
        }
    }

    /// The range of a value with facts `f`, as keys.
    fn dom(self, f: &Facts) -> (BitVec, BitVec) {
        match self {
            Order::U => (f.urange().lo(), f.urange().hi()),
            Order::S => (self.key(&f.srange().lo()), self.key(&f.srange().hi())),
        }
    }
}

/// How a layer is strictly monotone.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) struct Mono {
    /// The order of the inner value.
    pub(crate) input: Order,
    /// Increasing (else decreasing).
    pub(crate) increasing: bool,
    /// The piece of a wrapping operation the inner value's range lies on (a label, the same
    /// for two values compared through one layer exactly when they lie on one piece).
    piece: i8,
}

/// A parameter: a node, or a value the operator implies (`~v` is `ones - v`).
#[derive(Clone, Debug)]
enum Arg {
    Node(u32),
    Val(BitVec),
}

/// How a layer maps its inner value `v`.
#[derive(Clone, Debug)]
enum Map {
    /// `v + k`.
    Add(Arg),
    /// `v - k`.
    Sub(Arg),
    /// `k - v`.
    SubFrom(Arg),
    /// `v * k`.
    Mul(u32),
    /// `v << s`.
    Shl(u32),
    /// `zext(v)`.
    Zext,
    /// `sext(v)`.
    Sext,
    /// `concat(v, k)`.
    ConcatHi(u32),
    /// `concat(k, v)`.
    ConcatLo(u32),
}

fn bin(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::bin_unchecked(op, a, b)
}

fn xor(a: &BitVec, b: &BitVec) -> BitVec {
    bin(BinOp::Xor, a, b)
}

fn ult(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Ult, a, b)
}

fn ule(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Ule, a, b)
}

fn slt(a: &BitVec, b: &BitVec) -> bool {
    BitVec::cmp_unchecked(CmpOp::Slt, a, b)
}

/// The map of node `n` in its operand at position `pos`, if it can be monotone.
fn map_at(cx: &Context, n: u32, pos: usize) -> Option<Map> {
    let node = cx.node(n);
    let other = if pos == 0 { node.b } else { node.a };
    Some(match (node.op, pos) {
        (OpCode::Not, 0) => Map::SubFrom(Arg::Val(BitVec::ones(cx.width_of(n)))),
        (OpCode::Neg, 0) => Map::SubFrom(Arg::Val(BitVec::zero(cx.width_of(n)))),
        (OpCode::Add, 0 | 1) => Map::Add(Arg::Node(other)),
        (OpCode::Sub, 0) => Map::Sub(Arg::Node(node.b)),
        (OpCode::Sub, 1) => Map::SubFrom(Arg::Node(node.a)),
        (OpCode::Xor, 0 | 1) => {
            let k = cx.const_val(other)?;
            if k != BitVec::smin(k.width()) {
                return None;
            }
            Map::Add(Arg::Val(k))
        }
        (OpCode::Mul, 0 | 1) => Map::Mul(other),
        (OpCode::Shl, 0) => Map::Shl(node.b),
        (OpCode::Zext, 0) => Map::Zext,
        (OpCode::Sext, 0) => Map::Sext,
        (OpCode::Concat, 0) => Map::ConcatHi(node.b),
        (OpCode::Concat, 1) => Map::ConcatLo(node.a),
        _ => return None,
    })
}

/// Facts about node `i`: exact for a constant, nothing when unavailable.
fn facts_of<O: Oracle>(cx: &mut Context, o: &mut O, i: u32) -> Result<Facts, O::Err> {
    if let Some(v) = cx.const_val(i) {
        return Ok(Facts::constant(&v));
    }
    Ok(o.facts(cx, i)?
        .unwrap_or_else(|| Facts::top(cx.width_of(i))))
}

fn arg_val(cx: &Context, a: &Arg) -> Option<BitVec> {
    match a {
        Arg::Node(i) => cx.const_val(*i),
        Arg::Val(v) => Some(*v),
    }
}

fn arg_facts<O: Oracle>(cx: &mut Context, o: &mut O, a: &Arg) -> Result<Facts, O::Err> {
    match a {
        Arg::Node(i) => facts_of(cx, o, *i),
        Arg::Val(v) => Ok(Facts::constant(v)),
    }
}

// ----- pieces of wrapping sums ------------------------------------------------------------------
//
// Each takes the range `[dlo, dhi]` of the inner value and `[klo, khi]` of the parameter, and
// gives the piece the whole range lies on, if one.

/// `v + k`, unsigned.
fn add_u(dlo: &BitVec, dhi: &BitVec, klo: &BitVec, khi: &BitVec) -> Option<i8> {
    let wraps = |a: &BitVec, b: &BitVec| ult(&bin(BinOp::Add, a, b), a);
    if !wraps(dhi, khi) {
        Some(0)
    } else if wraps(dlo, klo) {
        Some(1)
    } else {
        None
    }
}

/// `v - k`, unsigned.
fn sub_u(dlo: &BitVec, dhi: &BitVec, klo: &BitVec, khi: &BitVec) -> Option<i8> {
    if ule(khi, dlo) {
        Some(0)
    } else if ult(dhi, klo) {
        Some(-1)
    } else {
        None
    }
}

/// `k - v`, unsigned.
fn subfrom_u(dlo: &BitVec, dhi: &BitVec, klo: &BitVec, khi: &BitVec) -> Option<i8> {
    if ule(dhi, klo) {
        Some(0)
    } else if ult(khi, dlo) {
        Some(-1)
    } else {
        None
    }
}

/// The signed overflow of `a + b` (or `a - b`): 0 none, 1 past `smax`, -1 past `smin`.
fn sover(sub: bool, a: &BitVec, b: &BitVec) -> i8 {
    let s = bin(if sub { BinOp::Sub } else { BinOp::Add }, a, b);
    let same = (a.msb() == b.msb()) != sub;
    if same && s.msb() != a.msb() {
        if a.msb() { -1 } else { 1 }
    } else {
        0
    }
}

/// One piece from the overflow at the low end (`lo`) and the high end (`hi`) of a range of
/// sums: a sum overflows past `smax` at most once, so the ends decide.
fn piece_s(lo: i8, hi: i8) -> Option<i8> {
    match (lo, hi) {
        (0, 0) => Some(0),
        (1, _) => Some(1),
        (_, -1) => Some(-1),
        _ => None,
    }
}

/// `v + k`, signed.
fn add_s(dlo: &BitVec, dhi: &BitVec, klo: &BitVec, khi: &BitVec) -> Option<i8> {
    piece_s(sover(false, dlo, klo), sover(false, dhi, khi))
}

/// `v - k`, signed.
fn sub_s(dlo: &BitVec, dhi: &BitVec, klo: &BitVec, khi: &BitVec) -> Option<i8> {
    piece_s(sover(true, dlo, khi), sover(true, dhi, klo))
}

/// `k - v`, signed.
fn subfrom_s(dlo: &BitVec, dhi: &BitVec, klo: &BitVec, khi: &BitVec) -> Option<i8> {
    piece_s(sover(true, klo, dhi), sover(true, khi, dlo))
}

// ----- classification ---------------------------------------------------------------------------

/// Whether `map`, over inner value `inner`, is strictly monotone from `input` to `out`:
/// its direction and piece.
fn classify<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    map: &Map,
    inner: u32,
    input: Order,
    out: Order,
) -> Result<Option<(bool, i8)>, O::Err> {
    use Order::{S, U};
    let same = input == out;
    let up = (true, 0);
    Ok(match map {
        Map::Zext | Map::ConcatLo(_) => (input == U).then_some(up),
        Map::Sext | Map::ConcatHi(_) => same.then_some(up),
        Map::Add(arg) | Map::Sub(arg) | Map::SubFrom(arg) => {
            let f = facts_of(cx, o, inner)?;
            let increasing = !matches!(map, Map::SubFrom(_));
            let piece = if let Some(k) = arg_val(cx, arg) {
                // In key space: a change of order shifts the constant by `smin`.
                let (dlo, dhi) = input.dom(&f);
                let w = k.width();
                let mut k = if matches!(map, Map::Sub(_)) {
                    bin(BinOp::Sub, &BitVec::zero(w), &k)
                } else {
                    k
                };
                if !same {
                    k = xor(&k, &BitVec::smin(w));
                }
                if increasing {
                    add_u(&dlo, &dhi, &k, &k)
                } else {
                    subfrom_u(&dlo, &dhi, &k, &k)
                }
            } else if !same {
                None
            } else {
                let kf = arg_facts(cx, o, arg)?;
                let (dlo, dhi, klo, khi) = match input {
                    U => (
                        f.urange().lo(),
                        f.urange().hi(),
                        kf.urange().lo(),
                        kf.urange().hi(),
                    ),
                    S => (
                        f.srange().lo(),
                        f.srange().hi(),
                        kf.srange().lo(),
                        kf.srange().hi(),
                    ),
                };
                let fun = match (map, input) {
                    (Map::Add(_), U) => add_u,
                    (Map::Sub(_), U) => sub_u,
                    (Map::SubFrom(_), U) => subfrom_u,
                    (Map::Add(_), S) => add_s,
                    (Map::Sub(_), S) => sub_s,
                    (_, S) => subfrom_s,
                    _ => unreachable!(),
                };
                fun(&dlo, &dhi, &klo, &khi)
            };
            piece.map(|p| (increasing, p))
        }
        Map::Mul(k) => {
            if !same {
                return Ok(None);
            }
            let w = cx.width_of(inner);
            let Ok(w2) = Width::new(w.bits().saturating_mul(2)) else {
                return Ok(None);
            };
            let f = facts_of(cx, o, inner)?;
            let kf = facts_of(cx, o, *k)?;
            match input {
                U => {
                    let wide = |v: &BitVec| v.zext(w2).unwrap_or_else(|_| unreachable!());
                    let p = bin(
                        BinOp::Mul,
                        &wide(&f.urange().hi()),
                        &wide(&kf.urange().hi()),
                    );
                    let fits = p.trunc(w).map(|t| wide(&t)) == Ok(p);
                    (fits && !kf.urange().lo().is_zero()).then_some((true, 0))
                }
                S => {
                    let wide = |v: &BitVec| v.sext(w2).unwrap_or_else(|_| unreachable!());
                    let (klo, khi) = (kf.srange().lo(), kf.srange().hi());
                    let fits = [f.srange().lo(), f.srange().hi()].iter().all(|v| {
                        [klo, khi].iter().all(|k| {
                            let p = bin(BinOp::Mul, &wide(v), &wide(k));
                            p.trunc(w).map(|t| wide(&t)) == Ok(p)
                        })
                    });
                    let zero = BitVec::zero(w);
                    if !fits {
                        None
                    } else if slt(&zero, &klo) {
                        Some((true, 0))
                    } else if slt(&khi, &zero) {
                        Some((false, 0))
                    } else {
                        None
                    }
                }
            }
        }
        Map::Shl(s) => {
            if !same {
                return Ok(None);
            }
            let f = facts_of(cx, o, inner)?;
            let shi = facts_of(cx, o, *s)?.urange().hi();
            // No bit shifted out at the largest count: then at none, and the map is `v * 2^s`.
            let keeps = |v: &BitVec, back: BinOp| bin(back, &bin(BinOp::Shl, v, &shi), &shi) == *v;
            match input {
                U => keeps(&f.urange().hi(), BinOp::LShr).then_some((true, 0)),
                S => (keeps(&f.srange().lo(), BinOp::AShr) && keeps(&f.srange().hi(), BinOp::AShr))
                    .then_some((true, 0)),
            }
        }
    })
}

/// `map` over `inner` as a strictly monotone layer to `out`, from the same order if possible,
/// else from the other.
fn mono<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    map: &Map,
    inner: u32,
    out: Order,
) -> Result<Option<Mono>, O::Err> {
    for input in [out, out.other()] {
        if let Some((increasing, piece)) = classify(cx, o, map, inner, input, out)? {
            return Ok(Some(Mono {
                input,
                increasing,
                piece,
            }));
        }
    }
    Ok(None)
}

/// `map` at node `n` (its parameters constants) applied to `v`.
fn apply(cx: &Context, n: u32, map: &Map, v: &BitVec) -> Option<BitVec> {
    let k = |i: u32| cx.const_val(i);
    Some(match map {
        Map::Add(a) => bin(BinOp::Add, v, &arg_val(cx, a)?),
        Map::Sub(a) => bin(BinOp::Sub, v, &arg_val(cx, a)?),
        Map::SubFrom(a) => bin(BinOp::Sub, &arg_val(cx, a)?, v),
        Map::Mul(i) => bin(BinOp::Mul, v, &k(*i)?),
        Map::Shl(i) => bin(BinOp::Shl, v, &k(*i)?),
        Map::Zext => v.zext(cx.width_of(n)).ok()?,
        Map::Sext => v.sext(cx.width_of(n)).ok()?,
        Map::ConcatHi(i) => BitVec::concat(v, &k(*i)?).ok()?,
        Map::ConcatLo(i) => BitVec::concat(&k(*i)?, v).ok()?,
    })
}

// ----- cancelling on both sides -----------------------------------------------------------------

/// If `n1` and `n2` are one strictly monotone layer to order `out` over different operands,
/// those operands and how: `n1 <out n2` is `x <in y` (`y <in x` for a decreasing layer).
pub(crate) fn cancel<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    n1: u32,
    n2: u32,
    out: Order,
) -> Result<Option<(u32, u32, Mono)>, O::Err> {
    let (a, b) = (cx.node(n1), cx.node(n2));
    if a.op != b.op || a.width != b.width || a.aux != b.aux || n1 == n2 {
        return Ok(None);
    }
    let (ka, kb): (Vec<u32>, Vec<u32>) = (a.children().collect(), b.children().collect());
    if ka.len() != kb.len() || ka.is_empty() {
        return Ok(None);
    }
    let mut pairings = vec![(0..ka.len()).collect::<Vec<usize>>()];
    if a.op.as_bin().is_some_and(BinOp::is_commutative) {
        let mut s: Vec<usize> = (0..ka.len()).collect();
        s.swap(0, 1);
        pairings.push(s);
    }
    for pairing in &pairings {
        let diff: Vec<usize> = (0..ka.len()).filter(|&p| ka[p] != kb[pairing[p]]).collect();
        let [p] = diff[..] else {
            continue;
        };
        let (x, y) = (ka[p], kb[pairing[p]]);
        if cx.wid(x) != cx.wid(y) {
            continue;
        }
        let (Some(m1), Some(m2)) = (map_at(cx, n1, p), map_at(cx, n2, pairing[p])) else {
            continue;
        };
        for input in [out, out.other()] {
            o.charge(1)?;
            let c1 = classify(cx, o, &m1, x, input, out)?;
            let c2 = classify(cx, o, &m2, y, input, out)?;
            if let (Some(c), Some(d)) = (c1, c2)
                && c == d
            {
                return Ok(Some((
                    x,
                    y,
                    Mono {
                        input,
                        increasing: c.0,
                        piece: c.1,
                    },
                )));
            }
        }
    }
    Ok(None)
}

// ----- solving at a constant --------------------------------------------------------------------

/// The result of solving `e ⋈ c` through `e`'s monotone layers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Solved {
    /// `x op t` (`t op x` when `const_left`).
    Cmp {
        op: CmpOp,
        x: u32,
        t: BitVec,
        const_left: bool,
    },
    /// The comparison is this constant.
    Const(bool),
}

/// One layer of a chain: the node, its inner operand, and how it maps it.
struct Link {
    n: u32,
    inner: u32,
    map: Map,
    mono: Mono,
}

/// Solves `lhs op c` (`c op lhs` when `const_left`) through as many strictly monotone layers of
/// `lhs` with constant parameters as possible; `None` if not even one.
pub(crate) fn solve<O: Oracle>(
    cx: &mut Context,
    o: &mut O,
    op: CmpOp,
    lhs: u32,
    c: &BitVec,
    const_left: bool,
) -> Result<Option<Solved>, O::Err> {
    let Some((top, _)) = Order::of(op) else {
        return Ok(None);
    };
    // Top down: each layer classified on its own inner value's range.
    let mut chain: Vec<Link> = Vec::new();
    let (mut cur, mut order) = (lhs, top);
    loop {
        o.charge(1)?;
        let kids: Vec<u32> = cx.node(cur).children().collect();
        let open: Vec<usize> = (0..kids.len())
            .filter(|&p| cx.const_val(kids[p]).is_none())
            .collect();
        let [pos] = open[..] else {
            break;
        };
        let Some(map) = map_at(cx, cur, pos) else {
            break;
        };
        let inner = kids[pos];
        let Some(mono) = mono(cx, o, &map, inner, order)? else {
            break;
        };
        chain.push(Link {
            n: cur,
            inner,
            map,
            mono,
        });
        (cur, order) = (inner, mono.input);
    }
    if chain.is_empty() {
        return Ok(None);
    }
    // Bottom up: the image of the inner value's range must stay in the range each layer was
    // classified on; where it leaves it, the chain starts at that layer.
    let mut doms = Vec::with_capacity(chain.len());
    for l in &chain {
        let f = facts_of(cx, o, l.inner)?;
        doms.push(l.mono.input.dom(&f));
    }
    let mut start = chain.len() - 1;
    let mut hull = doms[start];
    for j in (0..chain.len()).rev() {
        let l = &chain[j];
        let d = doms[j];
        if j != start && !(ule(&d.0, &hull.0) && ule(&hull.1, &d.1)) {
            start = j;
            hull = d;
        }
        let out = if j == 0 { top } else { chain[j - 1].mono.input };
        let image = |k: &BitVec| apply(cx, l.n, &l.map, &l.mono.input.key(k)).map(|v| out.key(&v));
        let (Some(a), Some(b)) = (image(&hull.0), image(&hull.1)) else {
            return Ok(None);
        };
        hull = if l.mono.increasing { (a, b) } else { (b, a) };
    }
    let x = chain[start].inner;
    let order = chain[start].mono.input;
    let (klo, khi) = doms[start];
    let w = cx.width_of(x);
    // The comparison at a key of `x`.
    let eval = |k: &BitVec| -> Option<bool> {
        let mut v = order.key(k);
        for l in chain[..=start].iter().rev() {
            v = apply(cx, l.n, &l.map, &v)?;
        }
        Some(if const_left {
            BitVec::cmp_unchecked(op, c, &v)
        } else {
            BitVec::cmp_unchecked(op, &v, c)
        })
    };
    let (Some(plo), Some(phi)) = (eval(&klo), eval(&khi)) else {
        return Ok(None);
    };
    if plo == phi {
        return Ok(Some(Solved::Const(plo)));
    }
    // Bisection for the first key where the comparison differs from its value at the low end.
    let one = BitVec::one(w);
    let (mut lo, mut hi) = (klo, khi);
    loop {
        let gap = bin(BinOp::Sub, &hi, &lo);
        if ule(&gap, &one) {
            break;
        }
        o.charge(1)?;
        let mid = bin(BinOp::Add, &lo, &bin(BinOp::LShr, &gap, &one));
        let Some(p) = eval(&mid) else {
            return Ok(None);
        };
        if p == plo {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let t = order.key(&hi);
    Ok(Some(if plo {
        // True below `t`: `x < t`.
        Solved::Cmp {
            op: order.cmp(true),
            x,
            t,
            const_left: false,
        }
    } else {
        // True from `t` on: `t <= x`.
        Solved::Cmp {
            op: order.cmp(false),
            x,
            t,
            const_left: true,
        }
    }))
}
