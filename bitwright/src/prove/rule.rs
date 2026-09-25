//! A rule's soundness at one assignment of its width and rounding-mode variables, proved by the
//! native prover from the rule itself (its IR, not expressions built through the canonicalizing
//! builder, which would put the builder between the rule and the proof): every parameter is a
//! free input; the guard's fact predicates read as what they state about values (`zero_bits(x,
//! m)` is `x & m = 0`, `proves(c)` is `c`), exactly what makes a guard sound to act on; and the
//! claim is that the guard implies the two sides are equal (as floats, every NaN one value, for
//! a `#[float_values]` rule).

use super::aig::{Aig, Cnf, FALSE, L, TRUE};
use super::blast::{self, Bits};
use super::sat::{Answer, Solver};
use super::{Certificate, Config};
use crate::BitVec;
use crate::error::Error;
use crate::ops::{CmpOpExt, UnOp};
use crate::rules::eval::{fp_desc, literal, width_of};
use crate::rules::ir::{ConstPred, FactPred, NodeId, RNode, Rule};

/// The answer for a rule at one assignment.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum RuleOutcome {
    /// Sound there (with a certificate, if asked for).
    Proved(Option<Certificate>),
    /// Unsound there: a value per parameter (in order) where the guard holds and the sides
    /// differ.
    Refuted(Vec<BitVec>),
    /// Not decided: why.
    Unknown(String),
}

#[derive(Clone)]
enum SVal {
    Bv(Bits),
    Bool(L),
}

impl SVal {
    fn bits(&self) -> Option<&Bits> {
        match self {
            SVal::Bv(b) => Some(b),
            SVal::Bool(_) => None,
        }
    }
    fn truthy(&self, g: &mut Aig) -> L {
        match self {
            SVal::Bool(b) => *b,
            SVal::Bv(b) => g.or_all(b),
        }
    }
}

struct Sym<'r> {
    rule: &'r Rule,
    widths: &'r [u16],
    g: Aig,
    params: Vec<Bits>,
    lets: Vec<Option<Bits>>,
    memo: Vec<Option<SVal>>,
}

impl Sym<'_> {
    fn eval(&mut self, n: NodeId) -> Result<SVal, Error> {
        if let Some(v) = &self.memo[n as usize] {
            return Ok(v.clone());
        }
        let v = self.compute(n)?;
        self.memo[n as usize] = Some(v.clone());
        Ok(v)
    }

    fn bits(&mut self, n: NodeId) -> Result<Bits, Error> {
        match self.eval(n)? {
            SVal::Bv(b) => Ok(b),
            SVal::Bool(_) => Err(Error::Contract("a condition where a value belongs".into())),
        }
    }

    fn compute(&mut self, n: NodeId) -> Result<SVal, Error> {
        let rule = self.rule;
        let bad = || Error::Unsupported("the rule is not well formed at this assignment".into());
        let w = width_of(rule, n, self.widths);
        Ok(match &rule.nodes[n as usize] {
            RNode::Param(i) => SVal::Bv(self.params[*i as usize].clone()),
            RNode::Let(i) => SVal::Bv(
                self.lets
                    .get(*i as usize)
                    .cloned()
                    .flatten()
                    .ok_or_else(bad)?,
            ),
            RNode::Lit(l) => SVal::Bv(blast::konst(
                &literal(l, w.ok_or_else(bad)?, self.widths).ok_or_else(bad)?,
            )),
            RNode::Un(op, a) => {
                let a = self.bits(*a)?;
                let g = &mut self.g;
                SVal::Bv(match op {
                    UnOp::Not => blast::not(g, &a),
                    UnOp::Neg => blast::neg(g, &a),
                    UnOp::Popcnt => blast::popcnt(g, &a),
                    UnOp::Clz => blast::clz(g, &a),
                    UnOp::Ctz => blast::ctz(g, &a),
                    UnOp::Bswap => blast::bswap(&a),
                    UnOp::BitRev => blast::bitrev(&a),
                })
            }
            RNode::Bin(op, a, b) => {
                let (a, b) = (self.bits(*a)?, self.bits(*b)?);
                SVal::Bv(bin(&mut self.g, *op, &a, &b))
            }
            RNode::Cmp(op, a, b) => {
                let (a, b) = (self.bits(*a)?, self.bits(*b)?);
                let g = &mut self.g;
                let r = match op {
                    CmpOpExt::Eq => blast::eq(g, &a, &b),
                    CmpOpExt::Ne => blast::eq(g, &a, &b) ^ 1,
                    CmpOpExt::Ult => blast::ult(g, &a, &b),
                    CmpOpExt::Ule => blast::ule(g, &a, &b),
                    CmpOpExt::Ugt => blast::ult(g, &b, &a),
                    CmpOpExt::Uge => blast::ule(g, &b, &a),
                    CmpOpExt::Slt => blast::slt(g, &a, &b),
                    CmpOpExt::Sle => blast::sle(g, &a, &b),
                    CmpOpExt::Sgt => blast::slt(g, &b, &a),
                    CmpOpExt::Sge => blast::sle(g, &b, &a),
                };
                SVal::Bv(vec![r])
            }
            RNode::Zext(a) => {
                let mut v = self.bits(*a)?;
                v.resize(usize::from(w.ok_or_else(bad)?.bits()), FALSE);
                SVal::Bv(v)
            }
            RNode::Sext(a) => {
                let mut v = self.bits(*a)?;
                let s = *v.last().unwrap_or(&FALSE);
                v.resize(usize::from(w.ok_or_else(bad)?.bits()), s);
                SVal::Bv(v)
            }
            RNode::Extract(lo, a) => {
                let v = self.bits(*a)?;
                let lo = usize::try_from(lo.eval(self.widths)).map_err(|_| bad())?;
                let len = usize::from(w.ok_or_else(bad)?.bits());
                SVal::Bv(v.get(lo..lo + len).ok_or_else(bad)?.to_vec())
            }
            RNode::Concat(h, l) => {
                let (h, mut l) = (self.bits(*h)?, self.bits(*l)?);
                l.extend(h);
                SVal::Bv(l)
            }
            RNode::Select(c, t, f) => {
                let c = self.eval(*c)?;
                let c = c.truthy(&mut self.g);
                let (t, f) = (self.bits(*t)?, self.bits(*f)?);
                SVal::Bv(blast::mux(&mut self.g, c, &t, &f))
            }
            RNode::And(a, b) => {
                let (a, b) = (self.eval(*a)?, self.eval(*b)?);
                let (a, b) = (a.truthy(&mut self.g), b.truthy(&mut self.g));
                SVal::Bool(self.g.and(a, b))
            }
            RNode::Or(a, b) => {
                let (a, b) = (self.eval(*a)?, self.eval(*b)?);
                let (a, b) = (a.truthy(&mut self.g), b.truthy(&mut self.g));
                SVal::Bool(self.g.or(a, b))
            }
            RNode::Not(a) => {
                let a = self.eval(*a)?;
                SVal::Bool(a.truthy(&mut self.g) ^ 1)
            }
            RNode::Fact(p, x, m) => {
                if *p == FactPred::Proves {
                    let v = self.eval(*x)?;
                    return Ok(SVal::Bool(v.truthy(&mut self.g)));
                }
                let xv = self.bits(*x)?;
                let mv = match m {
                    Some(m) => Some(self.bits(*m)?),
                    None => None,
                };
                let g = &mut self.g;
                SVal::Bool(match p {
                    FactPred::NonZero => g.or_all(&xv),
                    FactPred::Disjoint | FactPred::ZeroBits => {
                        let a = blast::and(g, &xv, mv.as_ref().ok_or_else(bad)?);
                        g.or_all(&a) ^ 1
                    }
                    FactPred::OneBits => {
                        let m = mv.ok_or_else(bad)?;
                        let a = blast::and(g, &xv, &m);
                        blast::eq(g, &a, &m)
                    }
                    FactPred::FpNotNan | FactPred::FpFinite | FactPred::FpNonZero => {
                        let inf = mv.ok_or_else(bad)?;
                        let mut mag = xv.clone();
                        if let Some(top) = mag.last_mut() {
                            *top = FALSE;
                        }
                        match p {
                            FactPred::FpNotNan => blast::ule(g, &mag, &inf),
                            FactPred::FpFinite => blast::ult(g, &mag, &inf),
                            _ => g.or_all(&mag),
                        }
                    }
                    _ => return Err(Error::Unsupported("an unknown fact predicate".into())),
                })
            }
            RNode::ConstP(p, a) => {
                let c = self.bits(*a)?;
                let g = &mut self.g;
                let one = blast::small(c.len(), 1);
                SVal::Bool(match p {
                    ConstPred::IsPow2 => {
                        let cnt = blast::popcnt(g, &c);
                        blast::eq(g, &cnt, &one)
                    }
                    ConstPred::IsLowMask => {
                        let c1 = blast::add(g, &c, &one);
                        let a = blast::and(g, &c, &c1);
                        let nz = g.or_all(&c);
                        let z = g.or_all(&a) ^ 1;
                        g.and(nz, z)
                    }
                    ConstPred::IsShiftedMask => {
                        let cm1 = blast::sub(g, &c, &one);
                        let filled = blast::or(g, &c, &cm1);
                        let f1 = blast::add(g, &filled, &one);
                        let a = blast::and(g, &filled, &f1);
                        let nz = g.or_all(&c);
                        let z = g.or_all(&a) ^ 1;
                        g.and(nz, z)
                    }
                })
            }
            RNode::Fp(f) => {
                let d = fp_desc(rule, n, f, self.widths).ok_or_else(bad)?;
                let mut kids = Vec::with_capacity(f.args.len());
                for &a in &f.args {
                    kids.push(self.bits(a)?);
                }
                SVal::Bv(super::fp::circuit(&mut self.g, d, &kids)?)
            }
        })
    }
}

fn bin(g: &mut Aig, op: crate::BinOp, a: &[L], b: &[L]) -> Bits {
    use crate::BinOp;
    match op {
        BinOp::Add => blast::add(g, a, b),
        BinOp::Sub => blast::sub(g, a, b),
        BinOp::Mul => blast::mul(g, a, b),
        BinOp::UMulHi => blast::mulhi(g, a, b, false),
        BinOp::SMulHi => blast::mulhi(g, a, b, true),
        BinOp::UDiv => blast::udivrem(g, a, b).0,
        BinOp::URem => blast::udivrem(g, a, b).1,
        BinOp::SDiv => blast::sdiv(g, a, b),
        BinOp::SRem => blast::srem(g, a, b),
        BinOp::And => blast::and(g, a, b),
        BinOp::Or => blast::or(g, a, b),
        BinOp::Xor => blast::xor(g, a, b),
        BinOp::Shl => blast::shift(g, a, b, true, FALSE),
        BinOp::LShr => blast::shift(g, a, b, false, FALSE),
        BinOp::AShr => {
            let s = *a.last().unwrap_or(&FALSE);
            blast::shift(g, a, b, false, s)
        }
        BinOp::RotL => blast::rotate(g, a, b, true),
        BinOp::RotR => blast::rotate(g, a, b, false),
        BinOp::Pdep => blast::pdep(g, a, b),
        BinOp::Pext => blast::pext(g, a, b),
    }
}

/// Proves `rule` at `widths` (the width variables' values, then each mode variable's index in
/// [`RoundingMode::ALL`](crate::fp::RoundingMode::ALL)). When the solver runs out of conflicts
/// and the rule has `const` parameters, the proof is split into the values of those the guard
/// admits (found by the solver, each blocked once proved), each proved with the parameters
/// fixed, which folds their circuits (a division by a constant), up to 8,192 of them.
pub fn rule(rule: &Rule, widths: &[u16], cfg: &Config) -> Result<RuleOutcome, Error> {
    if !rule.admits(widths) {
        return Err(Error::Unsupported(format!(
            "{} does not apply at these widths",
            rule.name
        )));
    }
    let first = attempt(rule, widths, cfg, &[])?;
    let consts: Vec<usize> = rule
        .params
        .iter()
        .enumerate()
        .filter(|(_, p)| p.kind == crate::rules::ir::ParamKind::Const)
        .map(|(k, _)| k)
        .collect();
    if !matches!(first, RuleOutcome::Unknown(_)) || consts.is_empty() || cfg.certificate {
        return Ok(first);
    }
    // The guard over symbolic parameters, and the constants' bits.
    let mut s = Sym {
        rule,
        widths,
        g: Aig::new(),
        params: Vec::new(),
        lets: Vec::new(),
        memo: vec![None; rule.nodes.len()],
    };
    for p in &rule.params {
        let w = usize::try_from(p.width.eval(widths))
            .map_err(|_| Error::Contract("a parameter width".into()))?;
        let bits: Bits = (0..w).map(|_| s.g.input()).collect();
        s.params.push(bits);
    }
    for l in &rule.lets {
        let v = match s.eval(l.value) {
            Ok(v) => v.bits().cloned(),
            Err(_) => return Ok(first),
        };
        s.lets.push(v);
        s.memo = vec![None; rule.nodes.len()];
    }
    let guard = match rule.guard {
        Some(gd) => match s.eval(gd) {
            Ok(v) => v.truthy(&mut s.g),
            Err(_) => return Ok(first),
        },
        None => TRUE,
    };
    let const_bits: Vec<L> = consts.iter().flat_map(|&k| s.params[k].clone()).collect();
    let mut roots = vec![guard];
    roots.extend(&const_bits);
    let mut solver = Solver::new();
    let mut cnf = Cnf::encode(&s.g, &roots, &mut solver);
    cnf.assert(guard, &mut solver);
    for _ in 0..MAX_CASES {
        let model = match solver.solve(cfg.max_conflicts) {
            Answer::Sat(m) => m,
            Answer::Unsat => return Ok(RuleOutcome::Proved(None)),
            Answer::Unknown => return Ok(first),
        };
        let mut fixed: Vec<Option<BitVec>> = vec![None; rule.params.len()];
        let mut block = Vec::new();
        for &k in &consts {
            let bits = &s.params[k];
            let mut limbs = [0u64; 8];
            for (j, &b) in bits.iter().enumerate() {
                let v = cnf.value(b, &model);
                if v {
                    limbs[j / 64] |= 1 << (j % 64);
                }
                let lit = cnf.lit(b);
                block.push(if v { !lit } else { lit });
            }
            let w = crate::Width::new(bits.len() as u16).unwrap_or(crate::Width::W1);
            fixed[k] = Some(BitVec::wrapping_from_limbs(w, &limbs));
        }
        match attempt(rule, widths, cfg, &fixed)? {
            RuleOutcome::Proved(_) => {}
            other => return Ok(other),
        }
        solver.add_clause(&block);
    }
    Ok(first)
}

/// The most values of `const` parameters a split proves.
pub const MAX_CASES: usize = 8192;

/// One attempt at `rule` at `widths`, the parameters in `fixed` held at their values.
fn attempt(
    rule: &Rule,
    widths: &[u16],
    cfg: &Config,
    fixed: &[Option<BitVec>],
) -> Result<RuleOutcome, Error> {
    if !rule.admits(widths) {
        return Err(Error::Unsupported(format!(
            "{} does not apply at these widths",
            rule.name
        )));
    }
    let mut s = Sym {
        rule,
        widths,
        g: Aig::new(),
        params: Vec::new(),
        lets: Vec::new(),
        memo: vec![None; rule.nodes.len()],
    };
    for (k, p) in rule.params.iter().enumerate() {
        let w = usize::try_from(p.width.eval(widths))
            .map_err(|_| Error::Contract("a parameter width".into()))?;
        let bits: Bits = match fixed.get(k).copied().flatten() {
            Some(v) => blast::konst(&v),
            None => (0..w).map(|_| s.g.input()).collect(),
        };
        s.params.push(bits);
    }
    let run = |s: &mut Sym<'_>| -> Result<(L, Bits, Bits), Error> {
        for l in &rule.lets {
            let v = s.eval(l.value)?.bits().cloned();
            s.lets.push(v);
            // Lets may refer to earlier lets: evaluated values are memoized by node, and a
            // `Let(i)` node reads `lets[i]`.
            s.memo = vec![None; rule.nodes.len()];
        }
        let guard = match rule.guard {
            Some(gd) => {
                let v = s.eval(gd)?;
                v.truthy(&mut s.g)
            }
            None => TRUE,
        };
        let (l, r) = (s.bits(rule.lhs)?, s.bits(rule.rhs)?);
        Ok((guard, l, r))
    };
    let (guard, l, r) = match run(&mut s) {
        Ok(x) => x,
        Err(Error::Unsupported(why)) => return Ok(RuleOutcome::Unknown(why)),
        Err(e) => return Err(e),
    };
    if s.g.len() > cfg.max_nodes {
        return Ok(RuleOutcome::Unknown("the circuit is too large".into()));
    }
    let g = &mut s.g;
    let mut equal = blast::eq(g, &l, &r);
    if rule.float_values
        && let Some(f) = rule.values_format(widths)
    {
        let inf = blast::konst(&f.inf(false));
        let nan = |g: &mut Aig, x: &Bits| {
            let mut mag = x.clone();
            if let Some(t) = mag.last_mut() {
                *t = FALSE;
            }
            blast::ult(g, &inf, &mag)
        };
        let (nl, nr) = (nan(g, &l), nan(g, &r));
        let both = g.and(nl, nr);
        equal = g.or(equal, both);
    }
    // The obligation: guard ∧ ¬equal is unsatisfiable.
    let bad = g.and(guard, equal ^ 1);
    let mut solver = Solver::new();
    if cfg.certificate {
        solver.log_proof();
    }
    let mut cnf = Cnf::encode(g, &[bad], &mut solver);
    cnf.assert(bad, &mut solver);
    Ok(match solver.solve(cfg.max_conflicts) {
        Answer::Unsat => RuleOutcome::Proved(cfg.certificate.then(|| Certificate {
            vars: solver.num_vars(),
            clauses: cnf.clauses.clone(),
            proof: solver.take_proof().unwrap_or_default(),
        })),
        Answer::Sat(model) => {
            let params: Vec<BitVec> = s
                .params
                .iter()
                .map(|bits| {
                    let mut limbs = [0u64; 8];
                    for (k, &b) in bits.iter().enumerate() {
                        if cnf.value(b, &model) {
                            limbs[k / 64] |= 1 << (k % 64);
                        }
                    }
                    let w = crate::Width::new(bits.len() as u16).unwrap_or(crate::Width::W1);
                    BitVec::wrapping_from_limbs(w, &limbs)
                })
                .collect();
            // Checked by the rule's own concrete evaluator: a prover bug cannot refute a sound
            // rule unnoticed.
            let lets = crate::rules::eval::eval_lets(rule, widths, &params);
            let holds = rule.guard.is_none_or(|gd| {
                crate::rules::eval::eval(rule, gd, widths, &params, &lets)
                    .is_some_and(|v| v.truthy())
            });
            let lv = crate::rules::eval::eval(rule, rule.lhs, widths, &params, &lets)
                .and_then(|v| v.bv());
            let rv = crate::rules::eval::eval(rule, rule.rhs, widths, &params, &lets)
                .and_then(|v| v.bv());
            let differs = match (lv, rv) {
                (Some(a), Some(b)) => {
                    a != b
                        && !(rule.float_values
                            && rule.values_format(widths).is_some_and(|f| {
                                f.test(crate::fp::FpTest::Nan, &a) == Ok(true)
                                    && f.test(crate::fp::FpTest::Nan, &b) == Ok(true)
                            }))
                }
                _ => false,
            };
            if !(holds && differs) {
                return Err(Error::Contract(format!(
                    "the prover's counterexample to {} does not check",
                    rule.name
                )));
            }
            RuleOutcome::Refuted(params)
        }
        Answer::Unknown => {
            RuleOutcome::Unknown(format!("no answer within {} conflicts", cfg.max_conflicts))
        }
    })
}

/// A rule at every width up to a bound (see [`rule_all_widths`]).
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct WidthReport {
    /// Whether the rule holds at every width by an argument independent of the width: a
    /// rule of bitwise operations on its parameters and constants 0 and all ones, which treat
    /// every bit position alike and alone, holds at every width once it holds at width 1.
    pub every_width: bool,
    /// Assignments proved (widths, then modes).
    pub proved: Vec<Vec<u16>>,
    /// An assignment where the rule fails, with a value per parameter.
    pub refuted: Option<(Vec<u16>, Vec<BitVec>)>,
    /// Assignments not decided within the budget.
    pub open: Vec<Vec<u16>>,
}

/// Whether every node of `rule` is a bitwise operation on parameters and the constants 0 and
/// all ones, with no guard: then bit `i` of each side depends only on bit `i` of the
/// parameters, by one Boolean function for every `i` and every width.
fn bitwise_uniform(rule: &Rule) -> bool {
    use crate::rules::ir::Literal;
    if rule.guard.is_some() || !rule.lets.is_empty() || !rule.modes.is_empty() {
        return false;
    }
    let mut stack = vec![rule.lhs, rule.rhs];
    while let Some(n) = stack.pop() {
        match &rule.nodes[n as usize] {
            RNode::Param(_) => {}
            RNode::Lit(Literal::Ones) => {}
            RNode::Lit(Literal::Int { limbs, negative }) => {
                let zero = limbs.iter().all(|&l| l == 0);
                let minus_one =
                    *negative && limbs.first() == Some(&1) && limbs[1..].iter().all(|&l| l == 0);
                if !zero && !minus_one {
                    return false;
                }
            }
            RNode::Un(UnOp::Not, a) => stack.push(*a),
            RNode::Bin(crate::BinOp::And | crate::BinOp::Or | crate::BinOp::Xor, a, b) => {
                stack.push(*a);
                stack.push(*b);
            }
            _ => return false,
        }
    }
    // Every parameter of one width variable: the rule's single width.
    rule.width_vars.len() == 1
}

/// Proves `rule` at every admitted assignment whose widths are at most `max_width` (every
/// width variable), smallest first, stopping at the first refutation; and, for a rule whose
/// shape makes width irrelevant, at every width at once.
pub fn rule_all_widths(rule: &Rule, max_width: u16, cfg: &Config) -> Result<WidthReport, Error> {
    let mut report = WidthReport::default();
    let nw = rule.width_vars.len();
    let mut assignments: Vec<Vec<u16>> = crate::rules::width_assignments(rule)
        .into_iter()
        .filter(|ws| ws[..nw].iter().all(|&w| w <= max_width) && rule.admits(ws))
        .collect();
    assignments.sort_by_key(|ws| ws[..nw].iter().copied().max().unwrap_or(0));
    if bitwise_uniform(rule) {
        // Width 1 decides every width.
        let one: Vec<u16> = vec![1; nw];
        if rule.admits(&one) {
            match self::rule(rule, &one, cfg)? {
                RuleOutcome::Proved(_) => {
                    report.every_width = true;
                    report.proved.push(one);
                    return Ok(report);
                }
                RuleOutcome::Refuted(p) => {
                    report.refuted = Some((one, p));
                    return Ok(report);
                }
                RuleOutcome::Unknown(_) => {}
            }
        }
    }
    for ws in assignments {
        match self::rule(rule, &ws, cfg)? {
            RuleOutcome::Proved(_) => report.proved.push(ws),
            RuleOutcome::Refuted(p) => {
                report.refuted = Some((ws, p));
                break;
            }
            RuleOutcome::Unknown(_) => report.open.push(ws),
        }
    }
    Ok(report)
}
