//! Types: unification over the arena (every operation says which of its operands and result
//! share a type), then an enumeration of the widths and formats left open.

use super::ir::{CFun, Intrinsic, Lit, Node, NodeId, Op, PFun, Term, Transform, Ty};
use crate::fp::FpFormat;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Kind {
    Any,
    Int,
    Float,
}

struct Uf {
    parent: Vec<u32>,
    kind: Vec<Kind>,
    fixed: Vec<Option<Ty>>,
}

impl Uf {
    fn find(&mut self, a: u32) -> u32 {
        let mut r = a;
        while self.parent[r as usize] != r {
            r = self.parent[r as usize];
        }
        let mut x = a;
        while self.parent[x as usize] != r {
            let next = self.parent[x as usize];
            self.parent[x as usize] = r;
            x = next;
        }
        r
    }

    fn set_kind(&mut self, a: u32, k: Kind) -> Result<(), String> {
        let r = self.find(a) as usize;
        self.kind[r] = merge_kind(self.kind[r], k)?;
        if let Some(t) = self.fixed[r] {
            check_kind(t, self.kind[r])?;
        }
        Ok(())
    }

    fn fix(&mut self, a: u32, t: Ty) -> Result<(), String> {
        let r = self.find(a) as usize;
        match self.fixed[r] {
            Some(old) if old != t => return Err(format!("{old} and {t} are one type here")),
            _ => self.fixed[r] = Some(t),
        }
        check_kind(t, self.kind[r])
    }

    fn union(&mut self, a: u32, b: u32) -> Result<(), String> {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return Ok(());
        }
        let k = merge_kind(self.kind[ra as usize], self.kind[rb as usize])?;
        let f = match (self.fixed[ra as usize], self.fixed[rb as usize]) {
            (Some(x), Some(y)) if x != y => return Err(format!("{x} and {y} are one type here")),
            (x, y) => x.or(y),
        };
        self.parent[rb as usize] = ra;
        self.kind[ra as usize] = k;
        self.fixed[ra as usize] = f;
        if let Some(t) = f {
            check_kind(t, k)?;
        }
        Ok(())
    }
}

fn merge_kind(a: Kind, b: Kind) -> Result<Kind, String> {
    match (a, b) {
        (Kind::Any, k) | (k, Kind::Any) => Ok(k),
        (x, y) if x == y => Ok(x),
        _ => Err("an integer and a floating-point value are one type here".into()),
    }
}

fn check_kind(t: Ty, k: Kind) -> Result<(), String> {
    match (t, k) {
        (Ty::Int(_), Kind::Float) => Err(format!("{t} where a floating-point type belongs")),
        (Ty::Float(_), Kind::Int) => Err(format!("{t} where an integer type belongs")),
        _ => Ok(()),
    }
}

/// The typing problem of a transformation.
pub(crate) struct Typing {
    /// The class (a representative node) of each node.
    class: Vec<u32>,
    /// The classes left open, each with its kind and a node to name it by.
    open: Vec<(u32, Kind, NodeId)>,
    /// Fixed types by class representative.
    fixed: Vec<Option<Ty>>,
    /// `(narrower, wider)` class pairs.
    narrower: Vec<(u32, u32)>,
    /// Classes of one width.
    same_width: Vec<(u32, u32)>,
}

/// Solves the equalities of `t`.
pub(crate) fn typing(t: &Transform) -> Result<Typing, String> {
    let n = t.nodes.len();
    let mut uf = Uf {
        parent: (0..n as u32).collect(),
        kind: vec![Kind::Any; n],
        fixed: vec![None; n],
    };
    let mut narrower: Vec<(u32, u32)> = Vec::new();
    let mut same_width: Vec<(u32, u32)> = Vec::new();
    for (i, ann) in t.types.iter().enumerate() {
        if let Some(ty) = ann {
            uf.fix(i as u32, *ty)
                .map_err(|e| format!("{}: {e}", t.label(i as NodeId)))?;
        }
    }
    let bool_ty = Ty::Int(1);
    for (i, node) in t.nodes.iter().enumerate() {
        let i = i as u32;
        let at = |e: String| format!("{}: {e}", t.label(i));
        let r: Result<(), String> = (|| {
            match node {
                Node::Input { .. } => {}
                Node::Sym(_) => uf.set_kind(i, Kind::Int)?,
                Node::Lit(l) => match l {
                    Lit::Bool(_) => uf.fix(i, bool_ty)?,
                    Lit::Inf(_) | Lit::Nan => uf.set_kind(i, Kind::Float)?,
                    _ => {}
                },
                Node::CExpr(f, args) => match f {
                    CFun::Width => uf.set_kind(i, Kind::Int)?,
                    CFun::Trunc => {
                        uf.set_kind(i, Kind::Int)?;
                        uf.set_kind(args[0], Kind::Int)?;
                        narrower.push((i, args[0]));
                    }
                    CFun::ZExt | CFun::SExt => {
                        uf.set_kind(i, Kind::Int)?;
                        uf.set_kind(args[0], Kind::Int)?;
                        narrower.push((args[0], i));
                    }
                    _ => {
                        uf.set_kind(i, Kind::Int)?;
                        for &a in args {
                            uf.union(i, a)?;
                        }
                    }
                },
                Node::Pred(p, args) => {
                    uf.fix(i, bool_ty)?;
                    match p {
                        PFun::And | PFun::Or | PFun::Not => {}
                        PFun::True => {}
                        PFun::Cmp(_)
                        | PFun::MaskedValueIsZero
                        | PFun::WillNotOverflowSignedAdd
                        | PFun::WillNotOverflowUnsignedAdd
                        | PFun::WillNotOverflowSignedSub
                        | PFun::WillNotOverflowUnsignedSub
                        | PFun::WillNotOverflowSignedMul
                        | PFun::WillNotOverflowUnsignedMul
                        | PFun::WillNotOverflowUnsignedShl
                        | PFun::WillNotOverflowSignedShl => {
                            uf.set_kind(args[0], Kind::Int)?;
                            uf.union(args[0], args[1])?;
                        }
                        _ => uf.set_kind(args[0], Kind::Int)?,
                    }
                }
                Node::Inst(inst) => {
                    let a = &inst.args;
                    match inst.op {
                        Op::Add
                        | Op::Sub
                        | Op::Mul
                        | Op::UDiv
                        | Op::SDiv
                        | Op::URem
                        | Op::SRem
                        | Op::Shl
                        | Op::LShr
                        | Op::AShr
                        | Op::And
                        | Op::Or
                        | Op::Xor => {
                            uf.set_kind(i, Kind::Int)?;
                            uf.union(i, a[0])?;
                            uf.union(i, a[1])?;
                        }
                        Op::FAdd | Op::FSub | Op::FMul | Op::FDiv | Op::FRem => {
                            uf.set_kind(i, Kind::Float)?;
                            uf.union(i, a[0])?;
                            uf.union(i, a[1])?;
                        }
                        Op::FNeg => {
                            uf.set_kind(i, Kind::Float)?;
                            uf.union(i, a[0])?;
                        }
                        Op::ICmp(_) => {
                            uf.fix(i, bool_ty)?;
                            uf.set_kind(a[0], Kind::Int)?;
                            uf.union(a[0], a[1])?;
                        }
                        Op::FCmp(_) => {
                            uf.fix(i, bool_ty)?;
                            uf.set_kind(a[0], Kind::Float)?;
                            uf.union(a[0], a[1])?;
                        }
                        Op::Select => {
                            uf.fix(a[0], bool_ty)?;
                            uf.union(i, a[1])?;
                            uf.union(i, a[2])?;
                        }
                        Op::Freeze | Op::Copy => uf.union(i, a[0])?,
                        Op::Load => {
                            uf.fix(a[0], Ty::Int(64))?;
                        }
                        Op::Store => {
                            uf.fix(i, bool_ty)?;
                            uf.fix(a[1], Ty::Int(64))?;
                        }
                        Op::Gep(_) => {
                            uf.fix(i, Ty::Int(64))?;
                            uf.fix(a[0], Ty::Int(64))?;
                            uf.set_kind(a[1], Kind::Int)?;
                        }
                        Op::Alloca => uf.fix(i, Ty::Int(64))?,
                        Op::Resize => {
                            uf.set_kind(i, Kind::Int)?;
                            uf.set_kind(a[0], Kind::Int)?;
                        }
                        Op::Trunc => {
                            uf.set_kind(i, Kind::Int)?;
                            uf.set_kind(a[0], Kind::Int)?;
                            narrower.push((i, a[0]));
                        }
                        Op::ZExt | Op::SExt => {
                            uf.set_kind(i, Kind::Int)?;
                            uf.set_kind(a[0], Kind::Int)?;
                            narrower.push((a[0], i));
                        }
                        Op::FPTrunc => {
                            uf.set_kind(i, Kind::Float)?;
                            uf.set_kind(a[0], Kind::Float)?;
                            narrower.push((i, a[0]));
                        }
                        Op::FPExt => {
                            uf.set_kind(i, Kind::Float)?;
                            uf.set_kind(a[0], Kind::Float)?;
                            narrower.push((a[0], i));
                        }
                        Op::FPToUI | Op::FPToSI => {
                            uf.set_kind(i, Kind::Int)?;
                            uf.set_kind(a[0], Kind::Float)?;
                        }
                        Op::UIToFP | Op::SIToFP => {
                            uf.set_kind(i, Kind::Float)?;
                            uf.set_kind(a[0], Kind::Int)?;
                        }
                        Op::BitCast => same_width.push((i, a[0])),
                        Op::Phi => {
                            for &x in a {
                                uf.union(i, x)?;
                            }
                        }
                        Op::Call(f) => match f {
                            Intrinsic::Assume => {
                                uf.fix(i, bool_ty)?;
                                uf.fix(a[0], bool_ty)?;
                            }
                            Intrinsic::Abs | Intrinsic::Ctlz | Intrinsic::Cttz => {
                                uf.set_kind(i, Kind::Int)?;
                                uf.union(i, a[0])?;
                                uf.fix(a[1], bool_ty)?;
                            }
                            _ => {
                                uf.set_kind(i, if f.is_float() { Kind::Float } else { Kind::Int })?;
                                for &x in a {
                                    uf.union(i, x)?;
                                }
                            }
                        },
                    }
                }
            }
            Ok(())
        })();
        r.map_err(at)?;
    }
    // Terminators and roots.
    for body in [&t.src, &t.tgt] {
        for b in &body.blocks {
            match &b.term {
                Term::Br(c, ..) => uf.fix(*c, bool_ty)?,
                Term::Switch(c, _, cases) => {
                    uf.set_kind(*c, Kind::Int)?;
                    for (l, _) in cases {
                        uf.union(*c, *l)?;
                    }
                }
                _ => {}
            }
        }
    }
    // The results of the two sides share a type.
    if let (Some(a), Some(b)) = (t.src.root, t.tgt.root) {
        uf.union(a, b)
            .map_err(|e| format!("the source's and the target's results: {e}"))?;
    }
    let rets = |body: &super::ir::Body| {
        body.blocks
            .iter()
            .filter_map(|b| match b.term {
                Term::Ret(Some(v)) => Some(v),
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    let all: Vec<NodeId> = rets(&t.src).into_iter().chain(rets(&t.tgt)).collect();
    for w in all.windows(2) {
        uf.union(w[0], w[1])?;
    }
    let class: Vec<u32> = (0..n as u32).map(|i| uf.find(i)).collect();
    let mut open = Vec::new();
    for i in 0..n as u32 {
        let r = class[i as usize];
        if r == i && uf.fixed[r as usize].is_none() {
            // Name the class by its first named member.
            let rep = (0..n as u32)
                .find(|&j| {
                    class[j as usize] == r
                        && matches!(t.node(j), Node::Input { .. } | Node::Sym(_) | Node::Inst(_))
                })
                .unwrap_or(r);
            open.push((r, uf.kind[r as usize], rep));
        }
    }
    Ok(Typing {
        narrower: narrower
            .into_iter()
            .map(|(a, b)| (class[a as usize], class[b as usize]))
            .collect(),
        same_width: same_width
            .into_iter()
            .map(|(a, b)| (class[a as usize], class[b as usize]))
            .collect(),
        fixed: (0..n).map(|i| uf.fixed[class[i] as usize]).collect(),
        class,
        open,
    })
}

/// One assignment of types to every node.
#[derive(Clone, Debug)]
pub struct Assignment {
    /// The type of each node.
    pub types: Vec<Ty>,
    /// What was chosen, for reports: `i8`, or `%x: i16, %r: i8`.
    pub label: String,
}

/// The candidate formats of an open floating-point type.
pub(crate) const FORMATS: [FpFormat; 3] = [FpFormat::F16, FpFormat::F32, FpFormat::F64];

impl Typing {
    /// Every assignment of the open classes (integers from `widths`, floating point from
    /// half, float and double) that meets the ordering constraints and lets every literal fit,
    /// smallest first, at most `max`.
    pub(crate) fn assignments(
        &self,
        t: &Transform,
        widths: &[u16],
        max: usize,
    ) -> Result<Vec<Assignment>, String> {
        let options: Vec<Vec<Ty>> = self
            .open
            .iter()
            .map(|&(_, k, _)| match k {
                Kind::Float => FORMATS.iter().map(|&f| Ty::Float(f)).collect(),
                _ => widths.iter().map(|&w| Ty::Int(w)).collect(),
            })
            .collect();
        let total: usize = options
            .iter()
            .try_fold(1usize, |acc, o| acc.checked_mul(o.len()))
            .unwrap_or(usize::MAX);
        if total > 1_000_000 {
            return Err(format!(
                "{} types are left open; annotate some (`i8 %x`)",
                self.open.len()
            ));
        }
        let mut combos: Vec<Vec<Ty>> = Vec::new();
        let mut idx = vec![0usize; options.len()];
        loop {
            let pick: Vec<Ty> = idx.iter().zip(&options).map(|(&k, o)| o[k]).collect();
            let ty_of = |class: u32| -> Ty {
                self.fixed[class as usize].unwrap_or_else(|| {
                    let k = self
                        .open
                        .iter()
                        .position(|&(r, ..)| r == class)
                        .expect("an open class");
                    pick[k]
                })
            };
            let ok = self
                .narrower
                .iter()
                .all(|&(a, b)| match (ty_of(a), ty_of(b)) {
                    (Ty::Int(x), Ty::Int(y)) => x < y,
                    (Ty::Float(x), Ty::Float(y)) => x.sb() < y.sb() && x.eb() <= y.eb(),
                    _ => false,
                })
                && self
                    .same_width
                    .iter()
                    .all(|&(a, b)| ty_of(a).bits() == ty_of(b).bits());
            if ok {
                combos.push(pick);
            }
            // Next combination.
            let mut k = 0;
            loop {
                if k == idx.len() {
                    break;
                }
                idx[k] += 1;
                if idx[k] < options[k].len() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
            if k == idx.len() {
                break;
            }
        }
        combos.sort_by_key(|p| {
            let bits: Vec<u16> = p.iter().map(|t| t.bits()).collect();
            (
                bits.iter().copied().max().unwrap_or(0),
                bits.iter().map(|&b| u32::from(b)).sum::<u32>(),
                bits,
            )
        });
        let mut out = Vec::new();
        let mut misfit = None;
        for pick in combos {
            let types: Vec<Ty> = (0..t.nodes.len())
                .map(|i| {
                    let c = self.class[i];
                    self.fixed[i].unwrap_or_else(|| {
                        let k = self
                            .open
                            .iter()
                            .position(|&(r, ..)| r == c)
                            .expect("an open class");
                        pick[k]
                    })
                })
                .collect();
            if let Some(why) = misfit_literal(t, &types) {
                misfit.get_or_insert(why);
                continue;
            }
            let label = match self.open.len() {
                0 => String::new(),
                1 => pick[0].to_string(),
                _ => self
                    .open
                    .iter()
                    .zip(&pick)
                    .map(|(&(_, _, rep), ty)| format!("{}: {ty}", t.label(rep)))
                    .collect::<Vec<_>>()
                    .join(", "),
            };
            out.push(Assignment { types, label });
            if out.len() == max {
                break;
            }
        }
        match (out.is_empty(), misfit) {
            (true, Some(why)) => Err(why),
            _ => Ok(out),
        }
    }
}

/// A literal that does not fit its type (an integer as an unsigned or a signed number, a
/// floating-point number exactly), if there is one.
fn misfit_literal(t: &Transform, types: &[Ty]) -> Option<String> {
    t.nodes.iter().enumerate().find_map(|(i, n)| {
        let ty = types[i];
        let fits = match (n, ty) {
            (Node::Lit(Lit::Num(s)), Ty::Int(w)) => super::value::int_literal(s, w).is_some(),
            (Node::Lit(Lit::Num(s)), Ty::Float(f)) => super::value::float_literal(s, f).is_some(),
            (Node::Lit(Lit::Inf(_) | Lit::Nan), Ty::Int(_)) => false,
            _ => true,
        };
        match n {
            Node::Lit(Lit::Num(s)) if !fits => Some(format!("{s} does not fit {ty}")),
            Node::Lit(_) if !fits => Some(format!("a floating-point literal where {ty} belongs")),
            _ => None,
        }
    })
}
