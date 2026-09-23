//! Lowering from the arena into an [`MbaExpr`], and lifting back.

use super::expr::{MOp, MbaExpr};
use crate::error::Error;
use crate::expr::{Context, Expr, OpCode};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// Caps on what is lowered and asked of a solver.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct MbaLimits {
    /// The most variables.
    pub max_vars: u32,
    /// The most nodes.
    pub max_nodes: u32,
    /// The widest node.
    pub max_width: u16,
    /// Fewer nodes than this are not worth a solver call.
    pub min_nodes: u32,
}

impl Default for MbaLimits {
    fn default() -> Self {
        MbaLimits {
            max_vars: 8,
            max_nodes: 256,
            max_width: 512,
            min_nodes: 5,
        }
    }
}

setters!(MbaLimits {
    with_max_vars: max_vars: u32,
    with_max_nodes: max_nodes: u32,
    with_max_width: max_width: u16,
    with_min_nodes: min_nodes: u32,
});

/// Why an expression was not lowered or not solved.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum Refusal {
    /// More variables than the limit.
    TooManyVars,
    /// More nodes than the limit.
    TooLarge,
    /// A node wider than the limit.
    TooWide,
    /// Fewer nodes than worth asking about.
    TooSmall,
    /// Not a mix of arithmetic and bitwise operators.
    NotMixed,
    /// The solver does not handle this input (its reason).
    Unsupported(String),
}

/// The expressions the variables of a lowered [`MbaExpr`] stand for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bindings {
    pub(crate) atoms: Vec<u32>,
}

impl Bindings {
    /// The number of variables.
    pub fn len(&self) -> usize {
        self.atoms.len()
    }

    /// Whether there are none.
    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }
}

/// Whether node `i` belongs to the fragment (otherwise it is an atom).
fn in_fragment(cx: &Context, i: u32) -> bool {
    let n = cx.node(i);
    match n.op {
        OpCode::Const
        | OpCode::Add
        | OpCode::Sub
        | OpCode::Mul
        | OpCode::Neg
        | OpCode::And
        | OpCode::Or
        | OpCode::Xor
        | OpCode::Not
        | OpCode::Zext
        | OpCode::Sext => true,
        OpCode::Extract => n.b == 0,
        OpCode::Shl | OpCode::LShr => cx
            .const_val(n.b)
            .and_then(|k| k.to_u64())
            .is_some_and(|k| k < u64::from(n.width)),
        _ => false,
    }
}

/// Lowers the fragment rooted at `root` (arena index); non-fragment subterms become variables.
pub(crate) fn lower_id(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
) -> Result<(MbaExpr, Bindings), Refusal> {
    let mut atoms: Vec<u32> = Vec::new();
    let mut order: Vec<u32> = Vec::new();
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, expanded)) = stack.pop() {
        if expanded {
            order.push(i);
            continue;
        }
        if seen.insert(i, ()).is_some() {
            continue;
        }
        if cx.node(i).width > lim.max_width {
            return Err(Refusal::TooWide);
        }
        if seen.len() as u32 > lim.max_nodes {
            return Err(Refusal::TooLarge);
        }
        if i != root && !in_fragment(cx, i) {
            atoms.push(i);
            if atoms.len() as u32 > lim.max_vars {
                return Err(Refusal::TooManyVars);
            }
            continue;
        }
        if !in_fragment(cx, i) {
            return Err(Refusal::Unsupported("not an MBA operator".into()));
        }
        stack.push((i, true));
        for c in cx.node(i).children() {
            stack.push((c, false));
        }
    }
    let mut m = MbaExpr::new(atoms.iter().map(|&a| cx.width_of(a)).collect());
    let mut at: IdMap<u32, u32> = IdMap::default();
    for (&a, k) in atoms.iter().zip(0u32..) {
        let v = m
            .push(MOp::Var(k), &[])
            .map_err(|e| Refusal::Unsupported(e.to_string()))?;
        at.insert(a, v);
    }
    for i in order {
        let n = cx.node(i);
        let arg = |k: u32| at[&k];
        let bad = |e: super::expr::MbaError| Refusal::Unsupported(e.to_string());
        let v = match n.op {
            OpCode::Const => m.push(
                MOp::Const(cx.const_val(i).unwrap_or(BitVec::zero(Width::W1))),
                &[],
            ),
            OpCode::Add => m.push(MOp::Add, &[arg(n.a), arg(n.b)]),
            OpCode::Sub => m.push(MOp::Sub, &[arg(n.a), arg(n.b)]),
            OpCode::Mul => m.push(MOp::Mul, &[arg(n.a), arg(n.b)]),
            OpCode::And => m.push(MOp::And, &[arg(n.a), arg(n.b)]),
            OpCode::Or => m.push(MOp::Or, &[arg(n.a), arg(n.b)]),
            OpCode::Xor => m.push(MOp::Xor, &[arg(n.a), arg(n.b)]),
            OpCode::Neg => m.push(MOp::Neg, &[arg(n.a)]),
            OpCode::Not => m.push(MOp::Not, &[arg(n.a)]),
            OpCode::Shl | OpCode::LShr => {
                let k = cx.const_val(n.b).and_then(|k| k.to_u64()).unwrap_or(0) as u16;
                let op = if n.op == OpCode::Shl {
                    MOp::Shl(k)
                } else {
                    MOp::LShr(k)
                };
                m.push(op, &[arg(n.a)])
            }
            OpCode::Zext => m.push_cast(MOp::Zext, arg(n.a), cx.width_of(i)),
            OpCode::Sext => m.push_cast(MOp::Sext, arg(n.a), cx.width_of(i)),
            OpCode::Extract => m.push_cast(MOp::Trunc, arg(n.a), cx.width_of(i)),
            _ => return Err(Refusal::Unsupported("not an MBA operator".into())),
        }
        .map_err(bad)?;
        at.insert(i, v);
    }
    Ok((m, Bindings { atoms }))
}

/// Lowers the fragment rooted at `e` into an [`MbaExpr`]: `+ − * neg & | ^ ~`, shifts by
/// constants below the width, extensions and truncation; every other subterm becomes a variable,
/// bound in the returned [`Bindings`]. Fails with [`Error::Unsupported`] (the refusal) when `e` is
/// not in the fragment or is over a limit.
pub fn lower(cx: &Context, e: Expr, lim: &MbaLimits) -> Result<(MbaExpr, Bindings), Error> {
    let i = cx.id(e)?;
    lower_id(cx, i, lim).map_err(|r| Error::Unsupported(format!("{r:?}")))
}

/// Builds `m` in the arena through the canonicalizing constructors, with each variable bound to
/// its atom.
pub(crate) fn lift_id(cx: &mut Context, m: &MbaExpr, b: &Bindings) -> Result<u32, Error> {
    let mut v: Vec<u32> = Vec::with_capacity(m.nodes().len());
    for n in m.nodes() {
        let a = |k: usize| v[n.args[k] as usize];
        let r = match n.op {
            MOp::Const(c) => cx.mk_const(&c)?,
            MOp::Var(i) => *b
                .atoms
                .get(i as usize)
                .ok_or(Error::Unsupported("unbound MBA variable".into()))?,
            MOp::Add => cx.c_bin(BinOp::Add, a(0), a(1))?,
            MOp::Sub => cx.c_bin(BinOp::Sub, a(0), a(1))?,
            MOp::Mul => cx.c_bin(BinOp::Mul, a(0), a(1))?,
            MOp::And => cx.c_bin(BinOp::And, a(0), a(1))?,
            MOp::Or => cx.c_bin(BinOp::Or, a(0), a(1))?,
            MOp::Xor => cx.c_bin(BinOp::Xor, a(0), a(1))?,
            MOp::Neg => cx.c_un(UnOp::Neg, a(0))?,
            MOp::Not => cx.c_un(UnOp::Not, a(0))?,
            MOp::Shl(k) | MOp::LShr(k) => {
                let kc = cx.mk_const(&BitVec::wrapping_from_u64(n.width, u64::from(k)))?;
                let op = if matches!(n.op, MOp::Shl(_)) {
                    BinOp::Shl
                } else {
                    BinOp::LShr
                };
                cx.c_bin(op, a(0), kc)?
            }
            MOp::Zext => cx.c_zext(a(0), n.width.bits())?,
            MOp::Sext => cx.c_sext(a(0), n.width.bits())?,
            MOp::Trunc => cx.c_extract(a(0), 0, n.width.bits())?,
        };
        v.push(r);
    }
    v.last()
        .copied()
        .ok_or(Error::Unsupported("empty MBA expression".into()))
}

/// Builds `m` in the arena through the canonicalizing constructors, each variable bound to the
/// subterm it stands for.
pub fn lift(cx: &mut Context, m: &MbaExpr, b: &Bindings) -> Result<Expr, Error> {
    let i = lift_id(cx, m, b)?;
    Ok(cx.handle(i))
}
