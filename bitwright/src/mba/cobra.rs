//! The cobra 0.4 backend (feature `cobra`).

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use cobra::{Expr as CExpr, Kind, Options, ProofLevel, SimplifyOutcomeKind};

/// cobra-mba's options, for [`CobraSolver::new`]. This is cobra-mba 0.4's type: a major version
/// change of that crate is a breaking change of this one.
pub use cobra::Options as CobraOptions;

use super::expr::{MOp, MbaExpr};
use super::solve::{Claim, MbaAnswer, MbaBudget, MbaSolver};
use crate::{BitVec, Width};

/// An [`MbaSolver`] backed by cobra 0.4 (`cobra-mba`, Apache-2.0).
///
/// It takes expressions whose variables and nodes all have one width of at most 64 bits and at
/// most `max_vars` variables, set by [`CobraSolver::new`]; casts are unsupported. `Sub` is lowered to
/// `a + (−b)` and `Shl(k)` to `a · 2^k`; cobra's result is mapped back with
/// `outcome_expr_in_original_space`, and its proof level becomes the [`Claim`]
/// (`LeanCertified` → `Certified`, `SmtProved` → `Proved`, `SpotChecked` → `Sampled`). A panic
/// inside cobra is caught and answered as unsupported. cobra has no caller-visible budget;
/// wrap it in a [`ThreadedSolver`](super::ThreadedSolver) for a hard deadline.
#[derive(Clone, Debug)]
pub struct CobraSolver {
    options: Options,
    max_vars: u32,
    id: String,
}

impl Default for CobraSolver {
    fn default() -> Self {
        CobraSolver::new(Options::default(), 8)
    }
}

impl CobraSolver {
    /// A solver with cobra's `options` (the bit width is set per call) that asks about at most
    /// `max_vars` variables. Its id records both, since they change answers.
    pub fn new(options: Options, max_vars: u32) -> CobraSolver {
        let id = format!("cobra-mba.0.4/{options:?}/{max_vars}");
        CobraSolver {
            options,
            max_vars,
            id,
        }
    }
}

fn to_cobra(p: &MbaExpr, w: u32) -> Option<Arc<CExpr>> {
    let mut v: Vec<Arc<CExpr>> = Vec::with_capacity(p.nodes().len());
    for n in p.nodes() {
        if u32::from(n.width.bits()) != w {
            return None;
        }
        let a = |k: usize| v[n.args[k] as usize].clone();
        let r = match n.op {
            MOp::Const(c) => CExpr::constant(c.to_u64()?),
            MOp::Var(i) => CExpr::variable(i),
            MOp::Add => CExpr::add(a(0), a(1)),
            MOp::Sub => CExpr::add(a(0), CExpr::neg(a(1))),
            MOp::Mul => CExpr::mul(a(0), a(1)),
            MOp::Neg => CExpr::neg(a(0)),
            MOp::And => CExpr::and(a(0), a(1)),
            MOp::Or => CExpr::or(a(0), a(1)),
            MOp::Xor => CExpr::xor(a(0), a(1)),
            MOp::Not => CExpr::not(a(0)),
            MOp::Shl(k) => CExpr::mul(a(0), CExpr::constant(1u64.checked_shl(u32::from(k))?)),
            MOp::LShr(k) => CExpr::shr(a(0), u64::from(k)),
            _ => return None,
        };
        v.push(r);
    }
    v.pop()
}

/// Converts cobra's result back (sharing preserved by pointer identity).
fn from_cobra(e: &Arc<CExpr>, vars: &[Width], w: Width) -> Option<MbaExpr> {
    let mut m = MbaExpr::new(vars.to_vec());
    let mut done: Vec<(*const CExpr, u32)> = Vec::new();
    let mut stack: Vec<(Arc<CExpr>, bool)> = vec![(e.clone(), false)];
    while let Some((x, expanded)) = stack.pop() {
        let ptr = Arc::as_ptr(&x);
        if done.iter().any(|(p, _)| *p == ptr) {
            continue;
        }
        if !expanded {
            stack.push((x.clone(), true));
            for c in x.children.iter() {
                stack.push((c.clone(), false));
            }
            continue;
        }
        let kid = |k: usize| -> Option<u32> {
            let p = Arc::as_ptr(x.children.get(k)?);
            done.iter().find(|(q, _)| *q == p).map(|(_, i)| *i)
        };
        let id = match x.kind {
            Kind::Constant(c) => m.push(MOp::Const(BitVec::wrapping_from_u64(w, c)), &[]),
            Kind::Variable(i) => m.push(MOp::Var(i), &[]),
            Kind::Add => m.push(MOp::Add, &[kid(0)?, kid(1)?]),
            Kind::Mul => m.push(MOp::Mul, &[kid(0)?, kid(1)?]),
            Kind::And => m.push(MOp::And, &[kid(0)?, kid(1)?]),
            Kind::Or => m.push(MOp::Or, &[kid(0)?, kid(1)?]),
            Kind::Xor => m.push(MOp::Xor, &[kid(0)?, kid(1)?]),
            Kind::Not => m.push(MOp::Not, &[kid(0)?]),
            Kind::Neg => m.push(MOp::Neg, &[kid(0)?]),
            Kind::Shr(k) if k < u32::from(w.bits()) => m.push(MOp::LShr(k as u16), &[kid(0)?]),
            Kind::Shr(_) => m.push(MOp::Const(BitVec::zero(w)), &[]),
            _ => return None,
        }
        .ok()?;
        done.push((ptr, id));
    }
    // The root must be the last node.
    let root = done.iter().find(|(p, _)| *p == Arc::as_ptr(e))?.1;
    (m.root() == Some(root)).then_some(m)
}

impl MbaSolver for CobraSolver {
    fn id(&self) -> &str {
        &self.id
    }

    fn solve(&self, p: &MbaExpr, _: &MbaBudget) -> MbaAnswer {
        let Some(w) = p.width() else {
            return MbaAnswer::Unsupported("empty".into());
        };
        if w.bits() > 64 || p.vars().iter().any(|&v| v != w) {
            return MbaAnswer::Unsupported("cobra takes one width of at most 64 bits".into());
        }
        if p.vars().len() as u32 > self.max_vars || p.vars().len() > cobra::MAX_INPUT_VARS {
            return MbaAnswer::Unsupported("too many variables for cobra".into());
        }
        let bits = u32::from(w.bits());
        let Some(expr) = to_cobra(p, bits) else {
            return MbaAnswer::Unsupported("not expressible in cobra".into());
        };
        let names: Vec<String> = (0..p.vars().len()).map(|i| format!("v{i}")).collect();
        let opts = Options {
            bitwidth: bits,
            max_vars: self.max_vars.min(cobra::MAX_INPUT_VARS as u32),
            ..self.options.clone()
        };
        let out = match catch_unwind(AssertUnwindSafe(|| {
            cobra::simplify_expr(&expr, &names, opts)
        })) {
            Ok(Ok(o)) => o,
            Ok(Err(e)) => return MbaAnswer::Unsupported(format!("cobra: {e:?}")),
            Err(_) => return MbaAnswer::Unsupported("cobra panicked".into()),
        };
        match out.kind {
            SimplifyOutcomeKind::Simplified => {
                let Some(r) = cobra::outcome_expr_in_original_space(&out, &names) else {
                    return MbaAnswer::Unsupported(
                        "cobra's answer has no original-space form".into(),
                    );
                };
                let Some(m) = from_cobra(&r, p.vars(), w) else {
                    return MbaAnswer::Unsupported("cobra's answer is outside the fragment".into());
                };
                let claim = match out.proof_level {
                    ProofLevel::LeanCertified => Claim::Certified,
                    ProofLevel::SmtProved => Claim::Proved,
                    ProofLevel::SpotChecked => Claim::Sampled,
                    _ => Claim::Unverified,
                };
                MbaAnswer::Simplified { expr: m, claim }
            }
            // cobra is deterministic for given options (no clock, no budget), and the id records
            // the options, so its "unchanged" is a durable answer under that id.
            SimplifyOutcomeKind::UnchangedUnsupported => MbaAnswer::NoSimpler,
            _ => MbaAnswer::Unsupported("cobra reported an error".into()),
        }
    }
}
