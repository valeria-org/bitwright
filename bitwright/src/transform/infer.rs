//! Precondition inference, after the data-driven method of Alive-Infer (Menendez and
//! Nagarakatte, PLDI 2017): the prover sorts values of the symbolic constants into those where
//! the transformation is valid and those where it is not (every value at small widths, else a
//! sample), a formula over a vocabulary of predicates is learned that excludes every invalid
//! value and admits as many valid ones as it can (a disjunction of conjunctions of at most two
//! predicates, chosen greedily), and the transformation with that precondition is verified at
//! every width. A failure at another width adds that width's examples and learns again.

use super::ir::{CFun, IPred, Lit, Node, NodeId, PFun, Transform, Ty};
use super::types::{Assignment, typing};
use super::verify::{Config, Probe, Report, Verdict, verify};
use crate::{BinOp, BitVec, CmpOpExt, Width};

/// The outcome of inference.
#[derive(Clone, Debug)]
pub struct Inference {
    /// The precondition found, in the transformation syntax. `None` when none is needed
    /// (then the report is valid), when none separates the examples, or when there are no
    /// symbolic constants (then there is no report).
    pub pre: Option<String>,
    /// Whether it admits every valid example (so it is the weakest the vocabulary can say at
    /// the widths sampled).
    pub weakest: bool,
    /// Valid and invalid examples seen.
    pub examples: (usize, usize),
    /// The verification of the transformation with the precondition.
    pub report: Option<Report>,
}

/// A predicate of the vocabulary.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Atom {
    Unary(U, usize),
    Binary(B, usize, usize),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum U {
    Zero,
    NonZero,
    One,
    AllOnes,
    NotAllOnes,
    Positive,
    NonNegative,
    Negative,
    Pow2,
    Pow2OrZero,
    SignBit,
    Mask,
    ShiftedMask,
    ShiftAmount,
    TooFar,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum B {
    Eq,
    Ne,
    Ult,
    Ule,
    Slt,
    Sle,
    Disjoint,
    Subset,
    Cover,
    Negated,
    Complement,
    ShiftSum,
}

const UNARY: [U; 15] = [
    U::Zero,
    U::NonZero,
    U::One,
    U::AllOnes,
    U::NotAllOnes,
    U::Positive,
    U::NonNegative,
    U::Negative,
    U::Pow2,
    U::Pow2OrZero,
    U::SignBit,
    U::Mask,
    U::ShiftedMask,
    U::ShiftAmount,
    U::TooFar,
];

const BINARY: [B; 12] = [
    B::Eq,
    B::Ne,
    B::Ult,
    B::Ule,
    B::Slt,
    B::Sle,
    B::Disjoint,
    B::Subset,
    B::Cover,
    B::Negated,
    B::Complement,
    B::ShiftSum,
];

fn bin(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::apply_bin(op, a, b).expect("one width")
}

fn cmp(op: CmpOpExt, a: &BitVec, b: &BitVec) -> bool {
    BitVec::apply_cmp(op, a, b).expect("one width")
}

impl Atom {
    fn eval(self, c: &[BitVec]) -> bool {
        match self {
            Atom::Unary(u, i) => {
                let x = &c[i];
                let w = x.width();
                let one = BitVec::one(w);
                let m1 = bin(BinOp::Sub, x, &one);
                let single = bin(BinOp::And, x, &m1).is_zero();
                match u {
                    U::Zero => x.is_zero(),
                    U::NonZero => !x.is_zero(),
                    U::One => *x == one,
                    U::AllOnes => x.is_ones(),
                    U::NotAllOnes => !x.is_ones(),
                    U::Positive => !x.is_zero() && !x.msb(),
                    U::NonNegative => !x.msb(),
                    U::Negative => x.msb(),
                    U::Pow2 => single && !x.is_zero(),
                    U::Pow2OrZero => single,
                    U::SignBit => *x == BitVec::smin(w),
                    U::Mask => {
                        let p1 = bin(BinOp::Add, x, &one);
                        !x.is_zero() && bin(BinOp::And, x, &p1).is_zero()
                    }
                    U::ShiftedMask => {
                        let fill = bin(BinOp::Or, x, &m1);
                        let p1 = bin(BinOp::Add, &fill, &one);
                        !x.is_zero() && bin(BinOp::And, &fill, &p1).is_zero()
                    }
                    U::ShiftAmount => x.to_u64().is_some_and(|v| v < u64::from(w.bits())),
                    U::TooFar => !x.to_u64().is_some_and(|v| v < u64::from(w.bits())),
                }
            }
            Atom::Binary(b, i, j) => {
                let (x, y) = (&c[i], &c[j]);
                let w = x.width();
                match b {
                    B::Eq => x == y,
                    B::Ne => x != y,
                    B::Ult => cmp(CmpOpExt::Ult, x, y),
                    B::Ule => cmp(CmpOpExt::Ule, x, y),
                    B::Slt => cmp(CmpOpExt::Slt, x, y),
                    B::Sle => cmp(CmpOpExt::Sle, x, y),
                    B::Disjoint => bin(BinOp::And, x, y).is_zero(),
                    B::Subset => bin(BinOp::And, x, y) == *x,
                    B::Cover => bin(BinOp::Or, x, y).is_ones(),
                    B::Negated => bin(BinOp::Add, x, y).is_zero(),
                    B::Complement => bin(BinOp::Xor, x, y).is_ones(),
                    B::ShiftSum => {
                        // Both shift amounts, and their sum, below the width.
                        let wb = u64::from(w.bits());
                        match (x.to_u64(), y.to_u64()) {
                            (Some(a), Some(b)) => a < wb && b < wb && a + b < wb,
                            _ => false,
                        }
                    }
                }
            }
        }
    }

    /// The predicate in the transformation syntax.
    fn text(self, names: &[String]) -> String {
        match self {
            Atom::Unary(u, i) => {
                let c = &names[i];
                match u {
                    U::Zero => format!("{c} == 0"),
                    U::NonZero => format!("{c} != 0"),
                    U::One => format!("{c} == 1"),
                    U::AllOnes => format!("{c} == -1"),
                    U::NotAllOnes => format!("{c} != -1"),
                    U::Positive => format!("{c} > 0"),
                    U::NonNegative => format!("{c} >= 0"),
                    U::Negative => format!("{c} < 0"),
                    U::Pow2 => format!("isPowerOf2({c})"),
                    U::Pow2OrZero => format!("isPowerOf2OrZero({c})"),
                    U::SignBit => format!("isSignBit({c})"),
                    U::Mask => format!("isMask({c})"),
                    U::ShiftedMask => format!("isShiftedMask({c})"),
                    U::ShiftAmount => format!("{c} u< width({c})"),
                    U::TooFar => format!("{c} u>= width({c})"),
                }
            }
            Atom::Binary(b, i, j) => {
                let (x, y) = (&names[i], &names[j]);
                match b {
                    B::Eq => format!("{x} == {y}"),
                    B::Ne => format!("{x} != {y}"),
                    B::Ult => format!("{x} u< {y}"),
                    B::Ule => format!("{x} u<= {y}"),
                    B::Slt => format!("{x} < {y}"),
                    B::Sle => format!("{x} <= {y}"),
                    B::Disjoint => format!("({x} & {y}) == 0"),
                    B::Subset => format!("({x} & {y}) == {x}"),
                    B::Cover => format!("({x} | {y}) == -1"),
                    B::Negated => format!("{x} + {y} == 0"),
                    B::Complement => format!("({x} ^ {y}) == -1"),
                    B::ShiftSum => {
                        format!("{x} u< width({x}) && {y} u< width({x}) && {x} + {y} u< width({x})")
                    }
                }
            }
        }
    }

    /// Adds the predicate's nodes to `t` (its constants are `cs`).
    fn build(self, t: &mut Transform, cs: &[NodeId]) -> NodeId {
        let lit = |t: &mut Transform, s: &str| t.push(Node::Lit(Lit::Num(s.into())), None);
        let pred = |t: &mut Transform, p: PFun, a: Vec<NodeId>| t.push(Node::Pred(p, a), None);
        let cex = |t: &mut Transform, f: CFun, a: Vec<NodeId>| t.push(Node::CExpr(f, a), None);
        let cmpn = |t: &mut Transform, p: IPred, a: NodeId, b: NodeId| {
            t.push(Node::Pred(PFun::Cmp(p), vec![a, b]), None)
        };
        match self {
            Atom::Unary(u, i) => {
                let c = cs[i];
                match u {
                    U::Zero
                    | U::NonZero
                    | U::One
                    | U::AllOnes
                    | U::NotAllOnes
                    | U::Positive
                    | U::NonNegative
                    | U::Negative => {
                        let (p, k) = match u {
                            U::Zero => (IPred::Eq, "0"),
                            U::NonZero => (IPred::Ne, "0"),
                            U::One => (IPred::Eq, "1"),
                            U::AllOnes => (IPred::Eq, "-1"),
                            U::NotAllOnes => (IPred::Ne, "-1"),
                            U::Positive => (IPred::Sgt, "0"),
                            U::NonNegative => (IPred::Sge, "0"),
                            _ => (IPred::Slt, "0"),
                        };
                        let k = lit(t, k);
                        cmpn(t, p, c, k)
                    }
                    U::Pow2 => pred(t, PFun::IsPowerOf2, vec![c]),
                    U::Pow2OrZero => pred(t, PFun::IsPowerOf2OrZero, vec![c]),
                    U::SignBit => pred(t, PFun::IsSignBit, vec![c]),
                    U::Mask => pred(t, PFun::IsMask, vec![c]),
                    U::ShiftedMask => pred(t, PFun::IsShiftedMask, vec![c]),
                    U::ShiftAmount | U::TooFar => {
                        let wd = cex(t, CFun::Width, vec![c]);
                        let p = if u == U::ShiftAmount {
                            IPred::Ult
                        } else {
                            IPred::Uge
                        };
                        cmpn(t, p, c, wd)
                    }
                }
            }
            Atom::Binary(b, i, j) => {
                let (x, y) = (cs[i], cs[j]);
                match b {
                    B::Eq => cmpn(t, IPred::Eq, x, y),
                    B::Ne => cmpn(t, IPred::Ne, x, y),
                    B::Ult => cmpn(t, IPred::Ult, x, y),
                    B::Ule => cmpn(t, IPred::Ule, x, y),
                    B::Slt => cmpn(t, IPred::Slt, x, y),
                    B::Sle => cmpn(t, IPred::Sle, x, y),
                    B::Disjoint => {
                        let a = cex(t, CFun::And, vec![x, y]);
                        let z = lit(t, "0");
                        cmpn(t, IPred::Eq, a, z)
                    }
                    B::Subset => {
                        let a = cex(t, CFun::And, vec![x, y]);
                        cmpn(t, IPred::Eq, a, x)
                    }
                    B::Cover => {
                        let a = cex(t, CFun::Or, vec![x, y]);
                        let m = lit(t, "-1");
                        cmpn(t, IPred::Eq, a, m)
                    }
                    B::Negated => {
                        let a = cex(t, CFun::Add, vec![x, y]);
                        let z = lit(t, "0");
                        cmpn(t, IPred::Eq, a, z)
                    }
                    B::Complement => {
                        let a = cex(t, CFun::Xor, vec![x, y]);
                        let m = lit(t, "-1");
                        cmpn(t, IPred::Eq, a, m)
                    }
                    B::ShiftSum => {
                        let w1 = cex(t, CFun::Width, vec![x]);
                        let a = cmpn(t, IPred::Ult, x, w1);
                        let w2 = cex(t, CFun::Width, vec![x]);
                        let b2 = cmpn(t, IPred::Ult, y, w2);
                        let s = cex(t, CFun::Add, vec![x, y]);
                        let w3 = cex(t, CFun::Width, vec![x]);
                        let c = cmpn(t, IPred::Ult, s, w3);
                        let ab = pred(t, PFun::And, vec![a, b2]);
                        pred(t, PFun::And, vec![ab, c])
                    }
                }
            }
        }
    }
}

/// An atom or its negation.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct Pred {
    atom: Atom,
    neg: bool,
}

impl Pred {
    fn eval(self, c: &[BitVec]) -> bool {
        self.atom.eval(c) != self.neg
    }

    fn text(self, names: &[String]) -> String {
        let t = self.atom.text(names);
        if !self.neg {
            return t;
        }
        match self.atom {
            // A comparison negates to the opposite comparison.
            Atom::Unary(U::One, _)
            | Atom::Binary(B::Disjoint | B::Subset | B::Cover | B::Negated | B::Complement, ..) => {
                t.replacen(" == ", " != ", 1)
            }
            Atom::Unary(U::Positive, _) => t.replacen(" > 0", " <= 0", 1),
            Atom::Binary(B::ShiftSum, ..) => format!("!({t})"),
            // A function call.
            _ => format!("!{t}"),
        }
    }

    fn build(self, t: &mut Transform, cs: &[NodeId]) -> NodeId {
        let p = self.atom.build(t, cs);
        if self.neg {
            t.push(Node::Pred(PFun::Not, vec![p]), None)
        } else {
            p
        }
    }
}

/// The atoms over constants with these types, and the negations that are not atoms already.
fn vocabulary(types: &[Ty]) -> Vec<Pred> {
    let mut out: Vec<Pred> = Vec::new();
    for a in atoms(types) {
        out.push(Pred {
            atom: a,
            neg: false,
        });
        let negatable = match a {
            Atom::Unary(u, _) => matches!(
                u,
                U::One
                    | U::Positive
                    | U::Pow2
                    | U::Pow2OrZero
                    | U::SignBit
                    | U::Mask
                    | U::ShiftedMask
            ),
            Atom::Binary(b, ..) => matches!(
                b,
                B::Disjoint | B::Subset | B::Cover | B::Negated | B::Complement | B::ShiftSum
            ),
        };
        if negatable {
            out.push(Pred { atom: a, neg: true });
        }
    }
    out
}

/// The atoms over constants with these types.
fn atoms(types: &[Ty]) -> Vec<Atom> {
    let mut out = Vec::new();
    for (i, ty) in types.iter().enumerate() {
        if matches!(ty, Ty::Int(_)) {
            out.extend(UNARY.iter().map(|&u| Atom::Unary(u, i)));
        }
    }
    for i in 0..types.len() {
        for j in 0..types.len() {
            if i == j || types[i] != types[j] || !matches!(types[i], Ty::Int(_)) {
                continue;
            }
            for &b in &BINARY {
                // Symmetric predicates once.
                let symmetric = matches!(
                    b,
                    B::Eq
                        | B::Ne
                        | B::Disjoint
                        | B::Cover
                        | B::Negated
                        | B::Complement
                        | B::ShiftSum
                );
                if symmetric && j < i {
                    continue;
                }
                out.push(Atom::Binary(b, i, j));
            }
        }
    }
    out
}

/// Examples at one type assignment: every value of the constants when there are few, else
/// boundary values and a deterministic sample.
fn example_values(widths: &[Width], budget: usize) -> Vec<Vec<BitVec>> {
    let total: u128 = widths
        .iter()
        .try_fold(1u128, |acc, w| acc.checked_mul(1u128 << w.bits().min(64)))
        .unwrap_or(u128::MAX);
    if total <= budget as u128 {
        let mut out = Vec::new();
        let mut idx = vec![0u64; widths.len()];
        loop {
            out.push(
                widths
                    .iter()
                    .zip(&idx)
                    .map(|(&w, &v)| BitVec::wrapping_from_u64(w, v))
                    .collect(),
            );
            let mut k = 0;
            while k < idx.len() {
                idx[k] += 1;
                if u128::from(idx[k]) < 1u128 << widths[k].bits() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
            if k == idx.len() {
                return out;
            }
        }
    }
    let special = |w: Width| -> Vec<BitVec> {
        let b = w.bits();
        let mut v = vec![
            BitVec::zero(w),
            BitVec::one(w),
            BitVec::ones(w),
            BitVec::smin(w),
            BitVec::smax(w),
        ];
        for k in [1u64, 2, 3, 4, 7, 8, u64::from(b) - 1, u64::from(b)] {
            v.push(BitVec::wrapping_from_u64(w, k));
            v.push(BitVec::wrapping_from_u64(w, 1u64.wrapping_shl(k as u32)));
        }
        v
    };
    let mut out = Vec::new();
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    while out.len() < budget {
        let v: Vec<BitVec> = widths
            .iter()
            .map(|&w| {
                let s = special(w);
                if next() % 2 == 0 {
                    s[(next() % s.len() as u64) as usize]
                } else {
                    BitVec::wrapping_from_u64(w, next())
                }
            })
            .collect();
        out.push(v);
    }
    out
}

/// A learned formula: clauses (conjunctions of atoms) in disjunction.
fn learn(atoms: &[Pred], examples: &[(Vec<BitVec>, bool)]) -> (Vec<Vec<Pred>>, bool) {
    let n = examples.len();
    let words = n.div_ceil(64);
    let truth: Vec<Vec<u64>> = atoms
        .iter()
        .map(|a| {
            let mut bits = vec![0u64; words];
            for (k, (c, _)) in examples.iter().enumerate() {
                if a.eval(c) {
                    bits[k / 64] |= 1 << (k % 64);
                }
            }
            bits
        })
        .collect();
    let mut pos = vec![0u64; words];
    let mut neg = vec![0u64; words];
    for (k, (_, v)) in examples.iter().enumerate() {
        if *v {
            pos[k / 64] |= 1 << (k % 64);
        } else {
            neg[k / 64] |= 1 << (k % 64);
        }
    }
    let and = |a: &[u64], b: &[u64]| a.iter().zip(b).map(|(x, y)| x & y).collect::<Vec<u64>>();
    let count = |a: &[u64]| a.iter().map(|x| x.count_ones() as usize).sum::<usize>();
    // Clauses that exclude every invalid example: single atoms, then pairs.
    let mut clauses: Vec<(Vec<Pred>, Vec<u64>)> = Vec::new();
    for (i, t) in truth.iter().enumerate() {
        if count(&and(t, &neg)) == 0 && count(&and(t, &pos)) > 0 {
            clauses.push((vec![atoms[i]], t.clone()));
        }
    }
    for i in 0..atoms.len() {
        for j in i + 1..atoms.len() {
            let t = and(&truth[i], &truth[j]);
            if count(&and(&t, &neg)) == 0 && count(&and(&t, &pos)) > 0 {
                clauses.push((vec![atoms[i], atoms[j]], t));
            }
        }
    }
    // Greedy cover of the valid examples, fewest atoms first on ties.
    let mut uncovered = pos.clone();
    let mut chosen: Vec<Vec<Pred>> = Vec::new();
    while count(&uncovered) > 0 {
        let best = clauses
            .iter()
            .map(|(c, t)| (count(&and(t, &uncovered)), c.len(), c, t))
            .filter(|&(k, ..)| k > 0)
            .max_by(|a, b| a.0.cmp(&b.0).then(b.1.cmp(&a.1)));
        let Some((_, _, c, t)) = best else {
            break;
        };
        chosen.push(c.clone());
        let t = t.clone();
        for (u, x) in uncovered.iter_mut().zip(&t) {
            *u &= !x;
        }
        if chosen.len() == 4 {
            break;
        }
    }
    let complete = count(&uncovered) == 0;
    (chosen, complete)
}

fn formula_text(f: &[Vec<Pred>], names: &[String]) -> String {
    let clause = |c: &Vec<Pred>| {
        let parts: Vec<String> = c
            .iter()
            .map(|a| {
                let t = a.text(names);
                if t.contains("&&") && (c.len() > 1 || f.len() > 1) {
                    format!("({t})")
                } else {
                    t
                }
            })
            .collect();
        if f.len() > 1 && c.len() > 1 {
            format!("({})", parts.join(" && "))
        } else {
            parts.join(" && ")
        }
    };
    f.iter().map(clause).collect::<Vec<_>>().join(" || ")
}

/// Infers a precondition over the symbolic constants of `t` (its own precondition, if any, is
/// ignored) and verifies the transformation with it.
pub fn infer(t: &Transform, cfg: &Config) -> Result<Inference, String> {
    let mut base = t.clone();
    base.pre = None;
    if base.consts.is_empty() {
        return Ok(Inference {
            pre: None,
            weakest: false,
            examples: (0, 0),
            report: None,
        });
    }
    let names: Vec<String> = base.consts.iter().map(|&c| base.label(c)).collect();
    let all = typing(&base)?.assignments(&base, &cfg.widths, cfg.max_types)?;
    // Sample at the smallest assignment with every constant at least 4 bits wide, and at 8.
    let wide_enough = |a: &Assignment, min: u16| {
        base.consts
            .iter()
            .all(|&c| a.types[c as usize].bits() >= min)
    };
    let mut sample: Vec<&Assignment> = Vec::new();
    for min in [4u16, 8] {
        if let Some(a) = all.iter().find(|a| wide_enough(a, min))
            && !sample.iter().any(|s| s.label == a.label)
        {
            sample.push(a);
        }
    }
    if sample.is_empty() {
        sample.extend(all.first());
    }
    let mut examples: Vec<(Vec<BitVec>, bool)> = Vec::new();
    let add_examples =
        |a: &Assignment, examples: &mut Vec<(Vec<BitVec>, bool)>| -> Result<(), String> {
            let widths: Vec<Width> = base
                .consts
                .iter()
                .map(|&c| Width::new(a.types[c as usize].bits()).expect("a width"))
                .collect();
            let mut probe = Probe::new(&base, a, cfg).map_err(|e| e.to_string())?;
            for v in example_values(&widths, 1024) {
                if let Some(ok) = probe.valid_at(&v).map_err(|e| e.to_string())? {
                    examples.push((v, ok));
                }
            }
            Ok(())
        };
    for a in &sample {
        add_examples(a, &mut examples)?;
    }
    let const_types: Vec<Ty> = base
        .consts
        .iter()
        .map(|&c| sample[0].types[c as usize])
        .collect();
    let atoms = vocabulary(&const_types);
    let mut last: Option<Inference> = None;
    for _round in 0..4 {
        let (npos, nneg) = (
            examples.iter().filter(|e| e.1).count(),
            examples.len() - examples.iter().filter(|e| e.1).count(),
        );
        if npos == 0 {
            return Ok(Inference {
                pre: None,
                weakest: false,
                examples: (npos, nneg),
                report: None,
            });
        }
        let (formula, complete) = if nneg == 0 {
            (Vec::new(), true)
        } else {
            learn(&atoms, &examples)
        };
        if nneg > 0 && formula.is_empty() {
            return Ok(Inference {
                pre: None,
                weakest: false,
                examples: (npos, nneg),
                report: None,
            });
        }
        let mut with = base.clone();
        let text = if formula.is_empty() {
            None
        } else {
            let consts = with.consts.clone();
            let mut disj: Option<NodeId> = None;
            for clause in &formula {
                let mut conj: Option<NodeId> = None;
                for a in clause {
                    let n = a.build(&mut with, &consts);
                    conj = Some(match conj {
                        None => n,
                        Some(c) => with.push(Node::Pred(PFun::And, vec![c, n]), None),
                    });
                }
                let c = conj.expect("a clause has an atom");
                disj = Some(match disj {
                    None => c,
                    Some(d) => with.push(Node::Pred(PFun::Or, vec![d, c]), None),
                });
            }
            with.pre = disj;
            Some(formula_text(&formula, &names))
        };
        let report = verify(&with, cfg);
        let failed = match report.verdict() {
            Verdict::Invalid(cx) => Some(cx.types.clone()),
            _ => None,
        };
        let done = Inference {
            pre: text,
            weakest: complete,
            examples: (npos, nneg),
            report: Some(report),
        };
        match failed {
            // More examples at the width where it failed, and learn again.
            Some(types) => match all.iter().find(|a| a.label == types) {
                Some(a) if !sample.iter().any(|s| s.label == a.label) => {
                    sample.push(a);
                    let before = examples.len();
                    add_examples(a, &mut examples)?;
                    if examples.len() == before {
                        return Ok(done);
                    }
                    last = Some(done);
                }
                _ => return Ok(done),
            },
            None => return Ok(done),
        }
    }
    Ok(last.expect("a round ran"))
}
