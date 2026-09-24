//! Concrete evaluation of rule terms, guards and lets, and width well-formedness per
//! instance. Used by the compiler's width validation and by the soundness checker.

use super::ir::{
    ConstPred, FactPred, FloatLit, FpNode, Literal, NodeId, RNode, Rounding, Rule, Sort,
};
use crate::facts::known::{bv_and, count_ones, low_mask};
use crate::fp::node::Desc;
use crate::fp::{FpFormat, FpKind, FpOp, RoundingMode};
use crate::ops::{BinOp, CmpOp, UnOp};
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
        Literal::Float { value, eb } => {
            let eb = u32::try_from(eb.eval(widths)).ok()?;
            let f = FpFormat::new(eb, u32::from(w.bits()).checked_sub(eb)?).ok()?;
            Some(float_value(*value, f))
        }
    }
}

/// Whether [`literal`] has a value at width `w` (the same answer, without building it).
fn literal_fits(l: &Literal, w: Width, widths: &[u16]) -> bool {
    let wb = i64::from(w.bits());
    match l {
        Literal::Int { limbs, negative } => {
            // The magnitude's bit length, and whether it is a power of two.
            let top = limbs.iter().rposition(|&x| x != 0);
            let Some(t) = top else {
                return true;
            };
            let len = 64 * t as i64 + 64 - i64::from(limbs[t].leading_zeros());
            if !*negative {
                return len <= wb;
            }
            // Down to the signed minimum: below 2^(w-1), or exactly it.
            let pow2 = limbs[t].is_power_of_two() && limbs[..t].iter().all(|&x| x == 0);
            len < wb || (len == wb && pow2)
        }
        Literal::Ones | Literal::SMin | Literal::SMax => true,
        Literal::LowMask(k) => (0..=wb).contains(&k.eval(widths)),
        Literal::Bit(k) => (0..wb).contains(&k.eval(widths)),
        Literal::Width(e) => {
            let v = e.eval(widths);
            v >= 0 && (wb >= 63 || v < 1i64 << wb)
        }
        Literal::Float { eb, .. } => {
            let eb = eb.eval(widths);
            u32::try_from(eb).is_ok_and(|eb| {
                u32::from(w.bits())
                    .checked_sub(eb)
                    .is_some_and(|sb| FpFormat::new(eb, sb).is_ok())
            })
        }
    }
}

/// The encoding of a floating-point constant in format `f`.
pub(crate) fn float_value(v: FloatLit, f: FpFormat) -> BitVec {
    let w = f.width();
    let rne = RoundingMode::Rne;
    let small = |k: u64| f.from_uint(rne, &BitVec::wrapping_from_u64(Width::W8, k));
    let flip = |x: &BitVec| BitVec::bin_unchecked(BinOp::Xor, x, &BitVec::smin(w));
    match v {
        FloatLit::Zero => f.zero(false),
        FloatLit::NegZero => f.zero(true),
        FloatLit::Inf => f.inf(false),
        FloatLit::NegInf => f.inf(true),
        FloatLit::Nan => f.nan(),
        FloatLit::One => small(1),
        FloatLit::NegOne => flip(&small(1)),
        FloatLit::Two => small(2),
        FloatLit::Half => f.div(rne, &small(1), &small(2)).unwrap_or_else(|_| f.nan()),
        FloatLit::MinNormal => BitVec::bin_unchecked(
            BinOp::Shl,
            &BitVec::one(w),
            &BitVec::wrapping_from_u64(w, u64::from(f.sb() - 1)),
        ),
        FloatLit::MinSubnormal => BitVec::one(w),
        FloatLit::MaxFinite => BitVec::bin_unchecked(BinOp::Sub, &f.inf(false), &BitVec::one(w)),
    }
}

/// The node a rule's floating-point node stands for at this assignment (`n` is the node, for
/// its width): its format valid, its rounding-mode variable assigned.
pub(crate) fn fp_desc(rule: &Rule, n: NodeId, f: &FpNode, widths: &[u16]) -> Option<Desc> {
    let format = |eb: &super::ir::WExpr, sb: &super::ir::WExpr| {
        let (eb, sb) = (eb.eval(widths), sb.eval(widths));
        FpFormat::new(u32::try_from(eb).ok()?, u32::try_from(sb).ok()?).ok()
    };
    let rm = match f.rounding {
        None => RoundingMode::Rne,
        Some(Rounding::Mode(m)) => m,
        Some(Rounding::Var(i)) => {
            let k = *widths.get(rule.width_vars.len() + usize::from(i))?;
            *RoundingMode::ALL.get(usize::from(k))?
        }
    };
    let op = match f.kind {
        FpKind::Add => FpOp::Add(rm),
        FpKind::Mul => FpOp::Mul(rm),
        FpKind::Div => FpOp::Div(rm),
        FpKind::Fma => FpOp::Fma(rm),
        FpKind::Sqrt => FpOp::Sqrt(rm),
        FpKind::Rem => FpOp::Rem,
        FpKind::RoundToIntegral => FpOp::RoundToIntegral(rm),
        FpKind::Min => FpOp::Min,
        FpKind::Max => FpOp::Max,
        FpKind::Eq => FpOp::Eq,
        FpKind::Lt => FpOp::Lt,
        FpKind::Le => FpOp::Le,
        FpKind::Convert => {
            let (e, s) = f.to.as_ref()?;
            FpOp::Convert {
                to: format(e, s)?,
                rm,
            }
        }
        FpKind::FromSInt => FpOp::FromSInt(rm),
        FpKind::FromUInt => FpOp::FromUInt(rm),
        FpKind::ToSInt => FpOp::ToSInt(rm, width_of(rule, n, widths)?),
        FpKind::ToUInt => FpOp::ToUInt(rm, width_of(rule, n, widths)?),
    };
    Some(Desc {
        op,
        format: format(&f.eb, &f.sb)?,
    })
}

/// Whether every node under `root` is well formed at this width assignment. `strict` is for
/// patterns: an extension to the same width never matches (the builder removes it).
pub(crate) fn well_formed(
    rule: &Rule,
    root: NodeId,
    widths: &[u16],
    strict: bool,
) -> Result<(), NodeId> {
    well_formed_with(rule, root, widths, strict, &mut Vec::new())
}

/// [`well_formed`] with a stack to reuse (the compiler asks it at every width).
pub(crate) fn well_formed_with(
    rule: &Rule,
    root: NodeId,
    widths: &[u16],
    strict: bool,
    stack: &mut Vec<NodeId>,
) -> Result<(), NodeId> {
    stack.clear();
    stack.push(root);
    while let Some(n) = stack.pop() {
        let node = &rule.nodes[n as usize];
        let w = match &rule.sorts[n as usize] {
            Sort::Bool => None,
            Sort::Bv(_) => Some(width_of(rule, n, widths).ok_or(n)?),
        };
        match node {
            RNode::Lit(l) => {
                if !literal_fits(l, w.ok_or(n)?, widths) {
                    return Err(n);
                }
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
            // A valid format (and assigned rounding mode); the operands' and result's widths
            // follow from it by construction.
            RNode::Fp(f) => {
                fp_desc(rule, n, f, widths).ok_or(n)?;
            }
            _ => {}
        }
        super::compile::push_children(node, stack);
    }
    Ok(())
}

/// Whether the rule applies at this width assignment at all: the constraints hold, the
/// pattern can match (strictly well formed) and the template, guard and lets are well formed.
/// The matcher, the checker and compile-time validation all use this one definition, so a
/// rule is only ever applied at assignments of the kind the checker checks.
pub(crate) fn admitted(rule: &Rule, widths: &[u16]) -> bool {
    if let Some(bits) = &rule.admitted_widths {
        let i = match widths {
            [] if rule.width_vars.is_empty() => 0,
            [w] if rule.width_vars.len() == 1 => usize::from(*w),
            _ => return false,
        };
        return i <= usize::from(Width::MAX_BITS) && (bits[i / 64] >> (i % 64)) & 1 == 1;
    }
    let n = rule.width_vars.len();
    if widths.len() != n + rule.modes.len()
        || widths[..n].iter().any(|&w| w == 0 || w > Width::MAX_BITS)
        || widths[n..]
            .iter()
            .any(|&m| usize::from(m) >= RoundingMode::ALL.len())
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
                FactPred::FpNotNan | FactPred::FpFinite | FactPred::FpNonZero => {
                    let (x, inf) = (xv?, bv((*m)?)?);
                    let mag = bv_and(&x, &BitVec::smax(x.width()));
                    match p {
                        FactPred::FpNotNan => BitVec::cmp_unchecked(CmpOp::Ule, &mag, &inf),
                        FactPred::FpFinite => BitVec::cmp_unchecked(CmpOp::Ult, &mag, &inf),
                        _ => !mag.is_zero(),
                    }
                }
            })
        }
        RNode::Fp(f) => {
            let d = fp_desc(rule, n, f, widths)?;
            let args: Vec<BitVec> = f.args.iter().map(|&a| bv(a)).collect::<Option<_>>()?;
            Val::Bv(crate::fp::eval(&d, &args))
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::ir::WExpr;

    #[test]
    fn literal_fits_agrees_with_literal() {
        let mut lits = vec![
            Literal::Ones,
            Literal::SMin,
            Literal::SMax,
            Literal::Float {
                value: FloatLit::One,
                eb: WExpr::var(0),
            },
        ];
        for k in [-1, 0, 1, 2, 7, 8, 9, 63, 64, 65, 511, 512, 513] {
            lits.push(Literal::LowMask(WExpr::konst(k)));
            lits.push(Literal::Bit(WExpr::konst(k)));
            lits.push(Literal::Width(WExpr::konst(k)));
        }
        lits.push(Literal::Width(WExpr::konst(1 << 40)));
        // Magnitudes around every power of two up to 512 bits, both signs.
        for bits in 0..=513u32 {
            for delta in [-1i64, 0, 1] {
                let mut limbs = vec![0u64; 9];
                if bits < 576 {
                    limbs[(bits / 64) as usize] |= 1 << (bits % 64);
                }
                // limbs + delta, as a multi-limb number (wrapping at 0).
                let mut v = limbs.clone();
                if delta == 1 {
                    for x in v.iter_mut() {
                        *x = x.wrapping_add(1);
                        if *x != 0 {
                            break;
                        }
                    }
                } else if delta == -1 {
                    for x in v.iter_mut() {
                        let (r, borrow) = x.overflowing_sub(1);
                        *x = r;
                        if !borrow {
                            break;
                        }
                    }
                }
                v.truncate(8);
                if limbs[8] != 0 && delta >= 0 {
                    continue;
                }
                for negative in [false, true] {
                    lits.push(Literal::Int {
                        limbs: v.clone(),
                        negative,
                    });
                }
            }
        }
        for l in &lits {
            for w in (1..=130).chain([192, 255, 256, 257, 511, 512]) {
                let width = Width::new(w).unwrap();
                for eb in [0u16, 2, 5, 8, 11, 31, 32] {
                    let widths = [eb];
                    assert_eq!(
                        literal_fits(l, width, &widths),
                        literal(l, width, &widths).is_some(),
                        "{l:?} at {w} (eb {eb})"
                    );
                }
            }
        }
    }
}
