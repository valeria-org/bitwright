//! Concrete evaluation of rule terms, guards and lets, and width well-formedness per
//! instance. Used by the compiler's width validation and by the soundness checker.

use super::ir::{ConstPred, FactPred, Literal, NodeId, RNode, Rule, Sort};
use crate::facts::known::{bv_and, count_ones, low_mask};
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// A value of a rule node.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum Val {
    Bv(BitVec),
    Bool(bool),
}

impl Val {
    pub(crate) fn truthy(self) -> bool {
        match self {
            Val::Bool(b) => b,
            Val::Bv(v) => !v.is_zero(),
        }
    }
    pub(crate) fn bv(self) -> Option<BitVec> {
        match self {
            Val::Bv(v) => Some(v),
            Val::Bool(_) => None,
        }
    }
}

/// The width of a bit-vector node under a width assignment, if valid.
pub(crate) fn width_of(rule: &Rule, n: NodeId, widths: &[u16]) -> Option<Width> {
    match &rule.sorts[n as usize] {
        Sort::Bv(w) => {
            let v = w.eval(widths);
            u16::try_from(v).ok().and_then(|v| Width::new(v).ok())
        }
        Sort::Bool => None,
    }
}

/// The value of a literal at width `w`, if it is representable there.
pub(crate) fn literal(l: &Literal, w: Width, widths: &[u16]) -> Option<BitVec> {
    let wb = i64::from(w.bits());
    match l {
        Literal::Int { limbs, negative } => {
            let m = BitVec::from_limbs(w, limbs).ok()?;
            if !*negative {
                return Some(m);
            }
            // A negative literal must be representable as a signed value.
            if !m.is_zero() && m != BitVec::smin(w) && m.msb() {
                return None;
            }
            Some(BitVec::un_unchecked(UnOp::Neg, &m))
        }
        Literal::Ones => Some(BitVec::ones(w)),
        Literal::SMin => Some(BitVec::smin(w)),
        Literal::SMax => Some(BitVec::smax(w)),
        Literal::LowMask(k) => {
            let k = k.eval(widths);
            (0..=wb).contains(&k).then(|| low_mask(w, k as u32))
        }
        Literal::Bit(k) => {
            let k = k.eval(widths);
            (0..wb).contains(&k).then(|| {
                let one = BitVec::one(w);
                BitVec::bin_unchecked(BinOp::Shl, &one, &BitVec::wrapping_from_u64(w, k as u64))
            })
        }
        Literal::Width(e) => {
            let v = e.eval(widths);
            if v < 0 {
                return None;
            }
            BitVec::from_u64(w, v as u64).ok()
        }
    }
}

/// Whether every node under `root` is well formed at this width assignment. `strict` is for
/// patterns: an extension to the same width never matches (the builder removes it).
pub(crate) fn well_formed(
    rule: &Rule,
    root: NodeId,
    widths: &[u16],
    strict: bool,
) -> Result<(), NodeId> {
    let mut stack = vec![root];
    while let Some(n) = stack.pop() {
        let node = &rule.nodes[n as usize];
        let w = match &rule.sorts[n as usize] {
            Sort::Bool => None,
            Sort::Bv(_) => Some(width_of(rule, n, widths).ok_or(n)?),
        };
        match node {
            RNode::Lit(l) => {
                literal(l, w.ok_or(n)?, widths).ok_or(n)?;
            }
            RNode::Un(UnOp::Bswap, _) if !w.ok_or(n)?.bits().is_multiple_of(8) => return Err(n),
            RNode::Zext(a) | RNode::Sext(a) => {
                let (wa, wn) = (width_of(rule, *a, widths).ok_or(n)?, w.ok_or(n)?);
                if wa > wn || (strict && wa == wn) {
                    return Err(n);
                }
            }
            RNode::Extract(lo, a) => {
                let wa = i64::from(width_of(rule, *a, widths).ok_or(n)?.bits());
                let lo = lo.eval(widths);
                let wn = i64::from(w.ok_or(n)?.bits());
                if lo < 0 || lo + wn > wa || (strict && lo == 0 && wn == wa) {
                    return Err(n);
                }
            }
            _ => {}
        }
        stack.extend(super::compile::children(node));
    }
    Ok(())
}

/// Whether the rule applies at this width assignment at all: the constraints hold, the
/// pattern can match (strictly well formed) and the template, guard and lets are well formed.
/// The matcher, the checker and compile-time validation all use this one definition, so a
/// rule is only ever applied at assignments of the kind the checker checks.
pub(crate) fn admitted(rule: &Rule, widths: &[u16]) -> bool {
    if widths.len() != rule.width_vars.len()
        || widths.iter().any(|&w| w == 0 || w > Width::MAX_BITS)
        || !rule.constraints.iter().all(|c| c.holds(widths))
        || well_formed(rule, rule.lhs, widths, true).is_err()
    {
        return false;
    }
    let mut parts = vec![rule.rhs];
    parts.extend(rule.guard);
    parts.extend(rule.lets.iter().map(|l| l.value));
    parts
        .into_iter()
        .all(|p| well_formed(rule, p, widths, false).is_ok())
}

/// Evaluates node `n`. Parameters and lets are given; fact predicates are evaluated on the
/// concrete values (the strongest sound answer). `None` means the node is not representable
/// at this instance (the caller has checked well-formedness, so this does not happen there).
pub(crate) fn eval(
    rule: &Rule,
    n: NodeId,
    widths: &[u16],
    params: &[BitVec],
    lets: &[Option<BitVec>],
) -> Option<Val> {
    let ev = |m: NodeId| eval(rule, m, widths, params, lets);
    let bv = |m: NodeId| ev(m).and_then(Val::bv);
    let w = || width_of(rule, n, widths);
    Some(match &rule.nodes[n as usize] {
        RNode::Param(i) => Val::Bv(params[*i as usize]),
        RNode::Let(i) => Val::Bv(lets.get(*i as usize).copied().flatten()?),
        RNode::Lit(l) => Val::Bv(literal(l, w()?, widths)?),
        RNode::Un(op, a) => Val::Bv(BitVec::apply_un(*op, &bv(*a)?).ok()?),
        RNode::Bin(op, a, b) => Val::Bv(BitVec::apply_bin(*op, &bv(*a)?, &bv(*b)?).ok()?),
        RNode::Cmp(op, a, b) => Val::Bv(BitVec::from_bool(
            BitVec::apply_cmp(*op, &bv(*a)?, &bv(*b)?).ok()?,
        )),
        RNode::Zext(a) => Val::Bv(bv(*a)?.zext(w()?).ok()?),
        RNode::Sext(a) => Val::Bv(bv(*a)?.sext(w()?).ok()?),
        RNode::Extract(lo, a) => {
            let lo = u16::try_from(lo.eval(widths)).ok()?;
            Val::Bv(bv(*a)?.extract(lo, w()?).ok()?)
        }
        RNode::Concat(h, l) => Val::Bv(BitVec::concat(&bv(*h)?, &bv(*l)?).ok()?),
        RNode::Select(c, t, f) => Val::Bv(BitVec::select(&bv(*c)?, &bv(*t)?, &bv(*f)?).ok()?),
        RNode::And(a, b) => Val::Bool(ev(*a)?.truthy() && ev(*b)?.truthy()),
        RNode::Or(a, b) => Val::Bool(ev(*a)?.truthy() || ev(*b)?.truthy()),
        RNode::Not(a) => Val::Bool(!ev(*a)?.truthy()),
        RNode::Fact(p, x, m) => {
            let xv = bv(*x);
            Val::Bool(match p {
                FactPred::Proves => ev(*x)?.truthy(),
                FactPred::NonZero => !xv?.is_zero(),
                FactPred::Disjoint => bv_and(&xv?, &bv((*m)?)?).is_zero(),
                FactPred::ZeroBits => bv_and(&xv?, &bv((*m)?)?).is_zero(),
                FactPred::OneBits => {
                    let mv = bv((*m)?)?;
                    bv_and(&xv?, &mv) == mv
                }
            })
        }
        RNode::ConstP(p, a) => {
            let c = bv(*a)?;
            let one = BitVec::one(c.width());
            Val::Bool(match p {
                ConstPred::IsPow2 => count_ones(&c) == 1,
                ConstPred::IsLowMask => {
                    !c.is_zero()
                        && bv_and(&c, &BitVec::bin_unchecked(BinOp::Add, &c, &one)).is_zero()
                }
                ConstPred::IsShiftedMask => {
                    // Fill the trailing zeros, then check for a low mask.
                    let filled = crate::facts::known::bv_or(
                        &c,
                        &BitVec::bin_unchecked(BinOp::Sub, &c, &one),
                    );
                    !c.is_zero()
                        && bv_and(&filled, &BitVec::bin_unchecked(BinOp::Add, &filled, &one))
                            .is_zero()
                }
            })
        }
    })
}

/// Evaluates the lets in order.
#[cfg_attr(not(feature = "check"), allow(dead_code))] // also the engine's, from M4
pub(crate) fn eval_lets(rule: &Rule, widths: &[u16], params: &[BitVec]) -> Vec<Option<BitVec>> {
    let mut out: Vec<Option<BitVec>> = Vec::with_capacity(rule.lets.len());
    for l in &rule.lets {
        let v = eval(rule, l.value, widths, params, &out).and_then(Val::bv);
        out.push(v);
    }
    out
}
