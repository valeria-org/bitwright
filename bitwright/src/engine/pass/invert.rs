//! The invert pass: equalities through invertible maps (see `crate::invert`).
//!
//! At `a == b` and `a != b`:
//!
//! - both sides one injective layer over different operands (`f(x) == f(y)`, `f` fixed by the
//!   operands the sides share): the operands are compared instead, layer after layer;
//! - against a constant (`f(x) == c`): `x` is compared with the preimage `f⁻¹(c)`, through
//!   every layer whose parameters are constants, and the comparison is a constant when `c` has
//!   no preimage;
//! - `a₁ | … | aₙ == 0` (and `a₁ & … & aₙ == ones`): every `aᵢ` is solved against the constant
//!   on its own, and the answers are intersected, so one value compared with two different
//!   constants is false.
//!
//! At `a <u b`, `a <=u b`, `a <s b` and `a <=s b` (see `crate::invert::monotone`):
//!
//! - both sides one strictly monotone layer over different operands (`f(x) <u f(y)`): the
//!   operands are compared instead, in the order the layer is monotone from, swapped for a
//!   decreasing layer, layer after layer (`zext(x) <s zext(y)` is `x <u y`, `~x <u ~y` is
//!   `y <u x`, `x + k <u y + k` is `x <u y` where neither sum wraps);
//! - against a constant on either side (`f(x) <u c`): `x` is compared with the threshold where
//!   the comparison changes, found by bisection over `x`'s range, or the comparison is a
//!   constant (`zext<16>(x) <u 300` at 8 bits is true).
//!
//! A bijection does not preserve order, so the injective layers above are never used for
//! orderings; a strictly monotone layer is injective, but its monotonicity usually rests on
//! facts, so equalities keep to the layers above. A rewrite replaces a comparison by one of proper subterms of its operands and a
//! constant, or by a constant, so like a rule it strictly decreases the termination order, and
//! it is committed whether or not the operands are shared elsewhere; a split is committed only
//! when its result is a smaller tree.

use super::{Accept, By, Fin, PassKind, Reject, Runner, Step, Stop, discard, facts};
use crate::BitVec;
use crate::engine::budget::Counter;
use crate::expr::{Context, OpCode};
use crate::facts::Facts;
use crate::invert::monotone::{self, Order};
use crate::invert::{self, MAX_SPLIT, Oracle, Solved};
use crate::ops::{BinOp, CmpOp};

/// Facts and work for the analysis, from the call: facts under the run's assumptions and fact
/// budget (what they rely on, and whether a cap cut them, collected in `fin`), work charged to
/// `pass_work`.
struct Calls<'x, 'r, 'a> {
    r: &'x mut Runner<'r, 'a>,
    fin: Fin,
}

impl Oracle for Calls<'_, '_, '_> {
    type Err = Stop;

    fn facts(&mut self, cx: &mut Context, i: u32) -> Result<Option<Facts>, Stop> {
        let (f, fin) = facts(self.r, cx, i)?;
        self.fin = self.fin.and(fin);
        Ok(f)
    }

    fn charge(&mut self, units: u64) -> Result<(), Stop> {
        self.r.meter.charge(Counter::PassWork, units)?;
        Ok(())
    }
}

fn count<'x>(r: &'x mut Runner<'_, '_>) -> &'x mut crate::engine::PassCounts {
    r.stats.passes.entry(PassKind::Invert.name()).or_default()
}

/// The invert pass at `n`.
pub(super) fn step(r: &mut Runner<'_, '_>, cx: &mut Context, n: u32) -> Result<Step, Stop> {
    let node = cx.node(n);
    let Some(op) = node.op.as_cmp() else {
        return Ok(Step::Normal(Fin::FINAL));
    };
    if r.quarantined_passes.contains(&PassKind::Invert) {
        return Ok(Step::Normal(Fin::PROVISIONAL));
    }
    let before = cx.len() as u32;
    let mut o = Calls { r, fin: Fin::FINAL };
    let e = if op.is_commutative() {
        // Constants are on the right of a stored equality.
        match cx.const_val(node.b) {
            Some(c) => {
                let join = cx.node(node.a).op;
                if (join == OpCode::Or && c.is_zero()) || (join == OpCode::And && c.is_ones()) {
                    split(cx, &mut o, op, n, node.a, &c, before)?
                } else {
                    solve(cx, &mut o, op, node.a, &c)?
                }
            }
            None => cancel(cx, &mut o, op, node.a, node.b)?,
        }
    } else {
        match (cx.const_val(node.a), cx.const_val(node.b)) {
            (_, Some(c)) => solve_order(cx, &mut o, op, node.a, &c, false)?,
            (Some(c), None) => solve_order(cx, &mut o, op, node.b, &c, true)?,
            (None, None) => cancel_order(cx, &mut o, op, node.a, node.b)?,
        }
    };
    let fin = o.fin;
    let e = match e {
        Some(e) if e != n => e,
        _ => {
            count(r).noop += 1;
            return Ok(Step::Normal(fin));
        }
    };
    match r.accept(cx, By::Pass(PassKind::Invert.name()), true, n, e, fin.rel)? {
        Accept::Yes => {
            count(r).changed += 1;
            Ok(Step::To(e, fin))
        }
        Accept::Vetoed => {
            count(r).rejected += 1;
            discard(r, cx, before);
            Ok(Step::Normal(fin))
        }
        Accept::Rejected(reason) => {
            count(r).rejected += 1;
            discard(r, cx, before);
            if matches!(reason, Reject::Width | Reject::Verify | Reject::Tripwire) {
                r.quarantined_passes.push(PassKind::Invert);
                r.stats.quarantined += 1;
            }
            Ok(Step::Normal(fin))
        }
    }
}

fn truth(o: &mut Calls<'_, '_, '_>, cx: &mut Context, v: bool) -> Result<u32, Stop> {
    o.r.build(cx, |cx| cx.mk_const(&BitVec::from_bool(v)))
}

/// `x op v`.
fn compare(
    o: &mut Calls<'_, '_, '_>,
    cx: &mut Context,
    op: CmpOp,
    x: u32,
    v: &BitVec,
) -> Result<u32, Stop> {
    let v = *v;
    o.r.build(cx, |cx| {
        let k = cx.mk_const(&v)?;
        cx.c_cmp(op, x, k)
    })
}

/// `f(x) op f(y)` as `x op y`, through every common injective layer.
fn cancel(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    a: u32,
    b: u32,
) -> Result<Option<u32>, Stop> {
    let (mut x, mut y) = (a, b);
    let mut peeled = false;
    while let Some((p, q)) = invert::cancel_layer(cx, o, x, y)? {
        o.charge(1)?;
        (x, y) = (p, q);
        peeled = true;
    }
    if !peeled {
        return Ok(None);
    }
    Ok(Some(o.r.build(cx, |cx| cx.c_cmp(op, x, y))?))
}

/// `f(x) op c` as `x op f⁻¹(c)`, or a constant.
fn solve(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    lhs: u32,
    c: &BitVec,
) -> Result<Option<u32>, Stop> {
    Ok(match invert::solve_eq(cx, o, lhs, c)? {
        None => None,
        Some(Solved::Const(eq)) => Some(truth(o, cx, eq == (op == CmpOp::Eq))?),
        Some(Solved::Eq(x, v)) => Some(compare(o, cx, op, x, &v)?),
    })
}

/// `f(x) op f(y)` as `x op' y`, through every common strictly monotone layer.
fn cancel_order(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    a: u32,
    b: u32,
) -> Result<Option<u32>, Stop> {
    let Some((mut order, strict)) = Order::of(op) else {
        return Ok(None);
    };
    let (mut x, mut y) = (a, b);
    let mut peeled = false;
    while let Some((p, q, m)) = monotone::cancel(cx, o, x, y, order)? {
        o.charge(1)?;
        (x, y) = if m.increasing { (p, q) } else { (q, p) };
        order = m.input;
        peeled = true;
    }
    if !peeled {
        return Ok(None);
    }
    Ok(Some(o.r.build(cx, |cx| cx.c_cmp(order.cmp(strict), x, y))?))
}

/// `f(x) op c` (or `c op f(x)`, with `const_left`) as a comparison of `x` with a threshold, or
/// a constant.
fn solve_order(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    lhs: u32,
    c: &BitVec,
    const_left: bool,
) -> Result<Option<u32>, Stop> {
    Ok(match monotone::solve(cx, o, op, lhs, c, const_left)? {
        None => None,
        Some(monotone::Solved::Const(v)) => Some(truth(o, cx, v)?),
        Some(monotone::Solved::Cmp {
            op,
            x,
            t,
            const_left,
        }) => Some(o.r.build(cx, |cx| {
            let t = cx.mk_const(&t)?;
            if const_left {
                cx.c_cmp(op, t, x)
            } else {
                cx.c_cmp(op, x, t)
            }
        })?),
    })
}

/// `a₁ | … | aₙ op 0` (or `a₁ & … & aₙ op ones`): each `aᵢ op c` solved alone, then
/// intersected (for `==`; `!=` is its negation).
fn split(
    cx: &mut Context,
    o: &mut Calls<'_, '_, '_>,
    op: CmpOp,
    n: u32,
    lhs: u32,
    c: &BitVec,
    before: u32,
) -> Result<Option<u32>, Stop> {
    let join = cx.node(lhs).op;
    let mut leaves = Vec::new();
    let mut stack = vec![lhs];
    while let Some(i) = stack.pop() {
        o.charge(1)?;
        let node = cx.node(i);
        if node.op == join {
            stack.push(node.b);
            stack.push(node.a);
        } else if leaves.len() >= MAX_SPLIT {
            return Ok(None);
        } else {
            leaves.push(i);
        }
    }
    let eq = op == CmpOp::Eq;
    // What each leaf being `c` means: `x == v`, in leaf order, without repeats.
    let mut conj: Vec<(u32, BitVec)> = Vec::new();
    let mut solved = false;
    for leaf in leaves {
        let (x, v) = match invert::solve_eq(cx, o, leaf, c)? {
            // One leaf can never be `c`: the conjunction is false.
            Some(Solved::Const(false)) => return Ok(Some(truth(o, cx, !eq)?)),
            Some(Solved::Const(true)) => {
                solved = true;
                continue;
            }
            Some(Solved::Eq(x, v)) => {
                solved = true;
                (x, v)
            }
            None => (leaf, *c),
        };
        match conj.iter().find(|(y, _)| *y == x) {
            // One value equal to two different constants.
            Some((_, w)) if *w != v => return Ok(Some(truth(o, cx, !eq)?)),
            Some(_) => {}
            None => conj.push((x, v)),
        }
    }
    if !solved {
        return Ok(None);
    }
    let mut out: Option<u32> = None;
    for (x, v) in &conj {
        let t = compare(o, cx, op, *x, v)?;
        out = Some(match out {
            None => t,
            Some(acc) => {
                let join = if eq { BinOp::And } else { BinOp::Or };
                o.r.build(cx, |cx| cx.c_bin(join, acc, t))?
            }
        });
    }
    let e = match out {
        Some(e) => e,
        None => truth(o, cx, eq)?,
    };
    // Kept only when smaller as a tree (a saturated size decides nothing).
    let tree = |i: u32| cx.meta[i as usize].tree;
    if tree(n) == u32::MAX || tree(e) >= tree(n) {
        discard(o.r, cx, before);
        return Ok(None);
    }
    Ok(Some(e))
}
