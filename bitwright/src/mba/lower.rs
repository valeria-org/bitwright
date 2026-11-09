//! Lowering from the arena into an [`MbaExpr`], and lifting back.

use super::expr::{MNode, MOp, MbaExpr};
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
            max_nodes: 2048,
            max_width: 512,
            min_nodes: 4,
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
        | OpCode::Sext
        | OpCode::Concat => true,
        // any slice, as a right shift then a truncation (`extract<8, 8>(x)` is
        // `trunc<8>(x >> 8)`), so a byte of a value stays related to the value.
        OpCode::Extract => n.b + u32::from(n.width) <= u32::from(cx.width_of(n.a).bits()),
        OpCode::Shl | OpCode::LShr => cx
            .const_val(n.b)
            .and_then(|k| k.to_u64())
            .is_some_and(|k| k < u64::from(n.width)),
        _ => false,
    }
}

/// Whether the fragment rooted at `root` is one [`lower_id`] takes (rooted at a fragment
/// operator, within `lim`): its interior nodes, operands first, when it is.
pub(crate) fn fits_nodes(cx: &Context, root: u32, lim: &MbaLimits) -> Result<Vec<u32>, Refusal> {
    let (_, order) = scan(cx, root, lim)?;
    Ok(order)
}

/// the narrower fragments [`lower_id_reading`] lowers.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub(crate) enum Reading {
    /// `+ − neg`, products and left shifts by a constant, and `& | ^ ~` with any constants, at
    /// one width: a semi-linear MBA.
    SemiLinear,
    /// The same, with the operands of `& | ^ ~` bitwise functions of atoms: arithmetic under a
    /// bitwise operator is an atom, as obfuscators build a semi-linear MBA (`Σ cᵢ·fᵢ(x)` over
    /// whatever values they take for `x`).
    Shallow,
    /// The same with `& | ^ ~` only over 0 and all-ones: a linear MBA, decided at the corners.
    Linear,
    /// Semi-linear, with this node (shared by several terms) an atom: `Σ cᵢ·fᵢ(a)` over a
    /// value every term reads.
    Cut(u32),
    /// The whole fragment, casts included, with this node an atom: a block over a rotated value
    /// and over bytes and halves of it (`trunc<32>(t)`, `zext<64>(trunc<8>(n))`), which stay
    /// related to `t` and `n`.
    CutWhole(u32),
}

/// whether node `i` is interior to `reading`'s fragment.
fn in_reading(cx: &Context, i: u32, reading: Reading) -> bool {
    let n = cx.node(i);
    let uniform = |k: u32| cx.const_val(k).is_none_or(|v| v.is_zero() || v.is_ones());
    match n.op {
        OpCode::Const | OpCode::Add | OpCode::Sub | OpCode::Neg => true,
        OpCode::Mul => cx.const_val(n.a).is_some() || cx.const_val(n.b).is_some(),
        OpCode::Shl => reading == Reading::SemiLinear && in_fragment(cx, i),
        OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not => {
            reading == Reading::SemiLinear || n.children().all(uniform)
        }
        _ => false,
    }
}

/// The fragment rooted at `root`: its atoms (in order of discovery) and its other nodes,
/// operands first.
fn scan(cx: &Context, root: u32, lim: &MbaLimits) -> Result<(Vec<u32>, Vec<u32>), Refusal> {
    scan_in(cx, root, lim, &in_fragment)
}

/// [`scan`] over the fragment `in_fragment` defines.
fn scan_in(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
    in_fragment: &dyn Fn(&Context, u32) -> bool,
) -> Result<(Vec<u32>, Vec<u32>), Refusal> {
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
    Ok((atoms, order))
}

/// Lowers the fragment rooted at `root` (arena index); non-fragment subterms become variables.
pub(crate) fn lower_id(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
) -> Result<(MbaExpr, Bindings), Refusal> {
    let (atoms, order) = scan(cx, root, lim)?;
    build(cx, atoms, order, &[])
}

/// [`lower_id`] over `reading`'s narrower fragment: every other subterm (a cast,
/// a right shift, a product of two non-constants, for [`Reading::Linear`] a bitwise operation
/// with another constant) is a variable. An identity of the result holds for independent
/// values of those, so for theirs.
pub(crate) fn lower_id_reading(
    cx: &Context,
    root: u32,
    lim: &MbaLimits,
    reading: Reading,
) -> Result<(MbaExpr, Bindings), Refusal> {
    let inside = |cx: &Context, i: u32, under: Option<&IdMap<u32, ()>>| match reading {
        Reading::Shallow => {
            in_reading(cx, i, Reading::SemiLinear)
                && (bitwise_or_const(cx, i) || under.is_none_or(|u| !u.contains_key(&i)))
        }
        Reading::Cut(cut) => i != cut && in_reading(cx, i, Reading::SemiLinear),
        Reading::CutWhole(cut) => i != cut && in_fragment(cx, i),
        _ => in_reading(cx, i, reading),
    };
    let under = match reading {
        Reading::Shallow => Some(under_bitwise(cx, root, lim)?),
        _ => None,
    };
    let (atoms, order) = scan_in(cx, root, lim, &|cx, i| inside(cx, i, under.as_ref()))?;
    // An atom that is its operand and a constant added (`a = t + k`, `a = k − t`), where the
    // fragment reads `t` too: `t` is `a − k` (`k − a`), a sum over the atom, and nothing below
    // `t` is read. The terms linear in `t` are then terms of `a`, which the bitwise operators
    // read: one variable, where `t`'s own atoms beside `a` were two values no test relates.
    let candidates: &[u32] = match reading {
        Reading::Shallow => &atoms,
        Reading::Cut(cut) | Reading::CutWhole(cut) if atoms.contains(&cut) => &[cut],
        _ => &[],
    };
    let mut solved: Vec<Solved> = Vec::new();
    for &a in candidates {
        let Some((t, k, negated)) = offset(cx, a) else {
            continue;
        };
        if t != root
            && (order.contains(&t) || atoms.contains(&t))
            && solved
                .iter()
                .all(|s| s.operand != t && s.atom != t && s.operand != a)
        {
            solved.push(Solved {
                operand: t,
                atom: a,
                constant: k,
                negated,
            });
        }
    }
    if solved.is_empty() {
        return build(cx, atoms, order, &[]);
    }
    let (mut atoms, order) = scan_in(cx, root, lim, &|cx, i| {
        solved.iter().all(|s| s.operand != i) && inside(cx, i, under.as_ref())
    })?;
    // An operand read only below what another one cut off is not read; an atom it left
    // unread is no variable.
    solved.retain(|s| atoms.contains(&s.operand) && atoms.contains(&s.atom));
    atoms.retain(|a| solved.iter().all(|s| s.operand != *a));
    build(cx, atoms, order, &solved)
}

/// Node `a` as `t + k` or (`true`) `k − t`, `k` a constant: `t`, `k`, and which. The negated
/// operand may be written `−t` or `t · −1`.
fn offset(cx: &Context, a: u32) -> Option<(u32, BitVec, bool)> {
    // Operands are read only once the operator says they are nodes.
    let n = cx.node(a);
    if !matches!(n.op, OpCode::Add | OpCode::Sub) {
        return None;
    }
    let (t, k) = match (n.op, cx.const_val(n.a), cx.const_val(n.b)) {
        (OpCode::Add, None, Some(k)) => (n.a, k),
        (OpCode::Add, Some(k), None) => (n.b, k),
        (OpCode::Sub, Some(k), None) => return Some((n.b, k, true)),
        _ => return None,
    };
    let m = cx.node(t);
    match m.op {
        OpCode::Neg => Some((m.a, k, true)),
        OpCode::Mul => match (cx.const_val(m.a), cx.const_val(m.b)) {
            (None, Some(c)) if c.is_ones() => Some((m.a, k, true)),
            (Some(c), None) if c.is_ones() => Some((m.b, k, true)),
            _ => Some((t, k, false)),
        },
        _ => Some((t, k, false)),
    }
}

/// An atom's operand written over the atom: `atom − constant`, or `constant − atom` (`negated`).
struct Solved {
    operand: u32,
    atom: u32,
    constant: BitVec,
    negated: bool,
}

/// the non-constant interior nodes of the semi-linear fragment below `root` that
/// two or more of its nodes read, most read first (at most `n`): where a [`Reading::Cut`] may
/// cut.
pub(crate) fn shared_nodes(cx: &Context, root: u32, lim: &MbaLimits, n: usize) -> Vec<u32> {
    let mut users: IdMap<u32, u32> = IdMap::default();
    let mut seen: IdMap<u32, ()> = IdMap::default();
    let mut stack = vec![root];
    while let Some(i) = stack.pop() {
        if seen.insert(i, ()).is_some() || seen.len() as u32 > lim.max_nodes {
            continue;
        }
        if !in_reading(cx, i, Reading::SemiLinear) {
            continue;
        }
        for c in cx.node(i).children() {
            *users.entry(c).or_default() += 1;
            stack.push(c);
        }
    }
    let mut v: Vec<(u32, u32)> = users
        .into_iter()
        .filter(|&(i, k)| {
            k >= 2 && cx.const_val(i).is_none() && in_reading(cx, i, Reading::SemiLinear)
        })
        .filter(|&(i, _)| cx.node(i).op != OpCode::Not)
        .map(|(i, k)| (k, i))
        .collect();
    v.sort_by(|a, b| b.cmp(a));
    v.into_iter().take(n).map(|(_, i)| i).collect()
}

/// Whether node `i` is a constant or `& | ^ ~`.
fn bitwise_or_const(cx: &Context, i: u32) -> bool {
    matches!(
        cx.node(i).op,
        OpCode::Const | OpCode::And | OpCode::Or | OpCode::Xor | OpCode::Not
    )
}

/// The nodes of the semi-linear fragment below `root` that a bitwise operator of it reads
/// (directly, or through other bitwise operators).
fn under_bitwise(cx: &Context, root: u32, lim: &MbaLimits) -> Result<IdMap<u32, ()>, Refusal> {
    let mut under: IdMap<u32, ()> = IdMap::default();
    let mut seen: IdMap<(u32, bool), ()> = IdMap::default();
    let mut stack: Vec<(u32, bool)> = vec![(root, false)];
    while let Some((i, bw)) = stack.pop() {
        if seen.insert((i, bw), ()).is_some() {
            continue;
        }
        if seen.len() as u32 > lim.max_nodes.saturating_mul(2) {
            return Err(Refusal::TooLarge);
        }
        if bw {
            under.insert(i, ());
        }
        let bitwise = bitwise_or_const(cx, i);
        // Arithmetic read by a bitwise operator is an atom: nothing below it is read here.
        if (bw && !bitwise) || !in_reading(cx, i, Reading::SemiLinear) {
            continue;
        }
        for c in cx.node(i).children() {
            stack.push((c, bitwise));
        }
    }
    Ok(under)
}

/// The expression over `atoms` that the fragment's nodes `order` (operands first) compute,
/// each operand in `solved` written over its atom.
fn build(
    cx: &Context,
    atoms: Vec<u32>,
    order: Vec<u32>,
    solved: &[Solved],
) -> Result<(MbaExpr, Bindings), Refusal> {
    let mut m = MbaExpr::new(atoms.iter().map(|&a| cx.width_of(a)).collect());
    let mut at: IdMap<u32, u32> = IdMap::default();
    for (&a, k) in atoms.iter().zip(0u32..) {
        let v = m
            .push(MOp::Var(k), &[])
            .map_err(|e| Refusal::Unsupported(e.to_string()))?;
        at.insert(a, v);
    }
    for s in solved {
        let bad = |e: super::expr::MbaError| Refusal::Unsupported(e.to_string());
        let a = at[&s.atom];
        let k = m.push(MOp::Const(s.constant), &[]).map_err(bad)?;
        let args = if s.negated { [k, a] } else { [a, k] };
        let v = m.push(MOp::Sub, &args).map_err(bad)?;
        at.insert(s.operand, v);
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
            OpCode::Extract if n.b == 0 => m.push_cast(MOp::Trunc, arg(n.a), cx.width_of(i)),
            OpCode::Extract => (|| {
                let s = m.push(MOp::LShr(n.b as u16), &[arg(n.a)])?;
                if cx.width_of(i) == cx.width_of(n.a) {
                    return Ok(s);
                }
                m.push_cast(MOp::Trunc, s, cx.width_of(i))
            })(),
            // `concat(hi, lo)` is `(hi << |lo|) + lo`, both extended (their bits are disjoint);
            // a high part that is the low bits of a value of the full width is that value, the
            // rest shifting out (`concat(trunc<62>(y), 3)` is `(y << 2) + 3`).
            OpCode::Concat => (|| {
                let w = cx.width_of(i);
                let lw = cx.width_of(n.b);
                let hn = cx.node(n.a);
                let hi = if hn.op == OpCode::Extract && hn.b == 0 && cx.width_of(hn.a) == w {
                    arg(hn.a)
                } else {
                    m.push_cast(MOp::Zext, arg(n.a), w)?
                };
                let hi = m.push(MOp::Shl(lw.bits()), &[hi])?;
                let lo = match cx.const_val(n.b) {
                    Some(c) => m.push(MOp::Const(c.zext(w).unwrap_or(BitVec::zero(w))), &[])?,
                    None => m.push_cast(MOp::Zext, arg(n.b), w)?,
                };
                m.push(MOp::Add, &[hi, lo])
            })(),
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
            // a truncated right shift is the slice it was lowered from.
            MOp::Trunc => match m.nodes()[n.args[0] as usize] {
                MNode {
                    op: MOp::LShr(k),
                    width,
                    args,
                } if k + n.width.bits() <= width.bits() => {
                    cx.c_extract(v[args[0] as usize], k, n.width.bits())?
                }
                _ => cx.c_extract(a(0), 0, n.width.bits())?,
            },
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
