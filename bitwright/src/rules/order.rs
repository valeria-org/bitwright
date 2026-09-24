//! The termination order: a Knuth–Bendix order over rule terms, and its ground counterpart
//! over the nodes of a context.
//!
//! Rule terms are compared as the builder will store them: a subterm with no parameters other
//! than `const` ones (`W - 1`, `lowmask(N)`, `c + c`) is folded to a constant, so it is one
//! constant symbol (a `const` parameter is itself one constant); a
//! comparison is in its stored form (`a >u b` is `b <u a`); and a commutative operator's
//! operands are compared as a multiset, since the builder orders them itself. Every node
//! weighs 1, all constants and `let` values are one minimal constant symbol, and ties in weight
//! are broken by a fixed operator precedence, then by the operands. Operator parameters (a
//! cast's width, an extract's offset) must be identical to break a tie: they are width
//! expressions, and a symbolic comparison that held at one width assignment could fail at
//! another. A rule whose left side is greater than its right side strictly decreases every
//! term it rewrites, so rewriting terminates.
//!
//! The precedence orients the cost-neutral canonicalizations toward the forms the rest of the
//! library prefers: `Mul > Shl` (multiply by a power of two becomes a shift), `Add > Or`
//! (a carry-free add becomes an or), `Neg > Not > Sub > Add` (so `~(-x)` becomes `x - 1`),
//! and casts above arithmetic (`zext(trunc(x))` becomes `x & lowmask`).

use core::cmp::Ordering;

use super::ir::ParamKind;
use super::ir::{NodeId, RNode, Rule, Sort, WExpr};
use crate::expr::{Context, OpCode};

/// Precedence rank of an operator; higher is "bigger". Leaves are 0.
pub(crate) fn op_rank(op: OpCode) -> u8 {
    match op {
        OpCode::Const | OpCode::Sym => 0,
        OpCode::Eq => 10,
        OpCode::Ne => 11,
        OpCode::Ult => 12,
        OpCode::Ule => 13,
        OpCode::Slt => 14,
        OpCode::Sle => 15,
        OpCode::Select => 34,
        OpCode::And => 40,
        OpCode::Or => 41,
        OpCode::Xor => 42,
        OpCode::Add => 43,
        OpCode::Sub => 44,
        OpCode::Not => 45,
        OpCode::Neg => 46,
        OpCode::Shl => 47,
        OpCode::LShr => 48,
        OpCode::AShr => 49,
        OpCode::RotL => 50,
        OpCode::RotR => 51,
        OpCode::BitRev => 52,
        OpCode::Bswap => 53,
        OpCode::Ctz => 54,
        OpCode::Clz => 55,
        OpCode::Popcnt => 56,
        OpCode::Pext => 57,
        OpCode::Pdep => 58,
        OpCode::Mul => 59,
        OpCode::SMulHi => 60,
        OpCode::UMulHi => 61,
        OpCode::SRem => 62,
        OpCode::SDiv => 63,
        OpCode::URem => 64,
        OpCode::UDiv => 65,
        // Casts rank above arithmetic: `zext(trunc(x))` becomes `x & mask`, as in LLVM.
        OpCode::Zext => 66,
        OpCode::Sext => 67,
        OpCode::Extract => 68,
        OpCode::Concat => 69,
        // Floating point: above the bit-vector operators, `Mul > Add` as for integers.
        OpCode::FAdd => 70,
        OpCode::FMul => 71,
        OpCode::FFma => 72,
        OpCode::FDiv => 73,
        OpCode::FSqrt => 74,
        OpCode::FRem => 75,
        OpCode::FRound => 76,
        OpCode::FMin => 77,
        OpCode::FMax => 78,
        OpCode::FEq => 79,
        OpCode::FLt => 80,
        OpCode::FLe => 81,
        OpCode::FConvert => 82,
        OpCode::FFromS => 83,
        OpCode::FFromU => 84,
        OpCode::FToS => 85,
        OpCode::FToU => 86,
        // Extension outputs: opaque to rules, ranked above everything built in. Listed one by
        // one, so a new built-in opcode must be given its own rank.
        OpCode::Ext1o0
        | OpCode::Ext1o1
        | OpCode::Ext1o2
        | OpCode::Ext1o3
        | OpCode::Ext1o4
        | OpCode::Ext1o5
        | OpCode::Ext1o6
        | OpCode::Ext1o7
        | OpCode::Ext2o0
        | OpCode::Ext2o1
        | OpCode::Ext2o2
        | OpCode::Ext2o3
        | OpCode::Ext2o4
        | OpCode::Ext2o5
        | OpCode::Ext2o6
        | OpCode::Ext2o7
        | OpCode::Ext3o0
        | OpCode::Ext3o1
        | OpCode::Ext3o2
        | OpCode::Ext3o3
        | OpCode::Ext3o4
        | OpCode::Ext3o5
        | OpCode::Ext3o6
        | OpCode::Ext3o7 => 100,
    }
}

/// Whether the builder may store the operands in either order.
fn op_commutative(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::Add
            | OpCode::Mul
            | OpCode::UMulHi
            | OpCode::SMulHi
            | OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Eq
            | OpCode::Ne
            | OpCode::FAdd
            | OpCode::FMul
            | OpCode::FMin
            | OpCode::FMax
            | OpCode::FEq
    )
}

// ----- rule terms ------------------------------------------------------------------------------

/// A rule term as the builder stores it.
#[derive(Clone, Debug)]
enum T {
    Const,
    Var(u16),
    App {
        op: OpCode,
        /// The result width of a cast or extract, and an extract's offset.
        params: (Option<WExpr>, Option<WExpr>),
        kids: Vec<T>,
    },
}

/// Whether the subterm's value is a constant once matched: it mentions only `const`
/// parameters, literals and `let`s.
fn constant(rule: &Rule, n: NodeId) -> bool {
    let mut stack = vec![n];
    while let Some(k) = stack.pop() {
        match &rule.nodes[k as usize] {
            RNode::Param(i) if rule.params[usize::from(*i)].kind != ParamKind::Const => {
                return false;
            }
            other => stack.extend(super::compile::children(other)),
        }
    }
    true
}

fn term(rule: &Rule, n: NodeId) -> T {
    if constant(rule, n) {
        return T::Const;
    }
    let rec = |m: NodeId| term(rule, m);
    let width = || match &rule.sorts[n as usize] {
        Sort::Bv(w) => Some(w.clone()),
        Sort::Bool => None,
    };
    let app = |op, params, kids| T::App { op, params, kids };
    match &rule.nodes[n as usize] {
        RNode::Param(i) => T::Var(*i),
        RNode::Lit(_) | RNode::Let(_) => T::Const,
        RNode::Un(op, a) => app(OpCode::from_un(*op), (None, None), vec![rec(*a)]),
        RNode::Bin(op, a, b) => app(OpCode::from_bin(*op), (None, None), vec![rec(*a), rec(*b)]),
        RNode::Cmp(op, a, b) => {
            let (stored, swap) = op.canonical();
            let (a, b) = if swap { (*b, *a) } else { (*a, *b) };
            app(OpCode::from_cmp(stored), (None, None), vec![rec(a), rec(b)])
        }
        RNode::Zext(a) => app(OpCode::Zext, (width(), None), vec![rec(*a)]),
        RNode::Sext(a) => app(OpCode::Sext, (width(), None), vec![rec(*a)]),
        RNode::Extract(lo, a) => app(OpCode::Extract, (width(), Some(lo.clone())), vec![rec(*a)]),
        RNode::Concat(h, l) => app(OpCode::Concat, (None, None), vec![rec(*h), rec(*l)]),
        RNode::Select(c, t, f) => app(
            OpCode::Select,
            (None, None),
            vec![rec(*c), rec(*t), rec(*f)],
        ),
        // Guard-only nodes never occur in patterns or templates (checked by the compiler).
        _ => T::Const,
    }
}

fn weight(t: &T) -> u64 {
    match t {
        T::Const | T::Var(_) => 1,
        T::App { kids, .. } => 1 + kids.iter().map(weight).sum::<u64>(),
    }
}

fn count_vars(t: &T, out: &mut Vec<u64>) {
    match t {
        T::Const => {}
        T::Var(i) => {
            let i = usize::from(*i);
            if out.len() <= i {
                out.resize(i + 1, 0);
            }
            out[i] += 1;
        }
        T::App { kids, .. } => kids.iter().for_each(|k| count_vars(k, out)),
    }
}

/// Equality as stored terms (commutative operands in either order).
fn same(a: &T, b: &T) -> bool {
    match (a, b) {
        (T::Const, T::Const) => true,
        (T::Var(x), T::Var(y)) => x == y,
        (
            T::App {
                op: oa,
                params: pa,
                kids: ka,
            },
            T::App {
                op: ob,
                params: pb,
                kids: kb,
            },
        ) => {
            oa == ob
                && pa == pb
                && ka.len() == kb.len()
                && (ka.iter().zip(kb).all(|(x, y)| same(x, y))
                    || (op_commutative(*oa)
                        && ka.len() == 2
                        && same(&ka[0], &kb[1])
                        && same(&ka[1], &kb[0])))
        }
        _ => false,
    }
}

/// `s >_kbo t`, with the variable condition at every step.
fn greater(s: &T, t: &T) -> bool {
    let (mut cs, mut ct) = (Vec::new(), Vec::new());
    count_vars(s, &mut cs);
    count_vars(t, &mut ct);
    if ct
        .iter()
        .enumerate()
        .any(|(i, &n)| n > cs.get(i).copied().unwrap_or(0))
    {
        return false;
    }
    match weight(s).cmp(&weight(t)) {
        Ordering::Greater => return true,
        Ordering::Less => return false,
        Ordering::Equal => {}
    }
    // Equal weights: only two applications of equal rank and parameters can still compare.
    let (
        T::App {
            op: os,
            params: ps,
            kids: ks,
        },
        T::App {
            op: ot,
            params: pt,
            kids: kt,
        },
    ) = (s, t)
    else {
        return false;
    };
    match op_rank(*os).cmp(&op_rank(*ot)) {
        Ordering::Greater => return true,
        Ordering::Less => return false,
        Ordering::Equal => {}
    }
    if os != ot || ps != pt {
        return false;
    }
    if op_commutative(*os) {
        multiset_greater(ks, kt, &same, &greater)
    } else {
        for (a, b) in ks.iter().zip(kt) {
            if !same(a, b) {
                return greater(a, b);
            }
        }
        false
    }
}

/// The multiset extension of `gt`: after removing common elements, `s` is non-empty and every
/// remaining element of `t` is below some remaining element of `s`.
fn multiset_greater<X>(
    s: &[X],
    t: &[X],
    eq: &dyn Fn(&X, &X) -> bool,
    gt: &dyn Fn(&X, &X) -> bool,
) -> bool {
    let mut rs: Vec<&X> = s.iter().collect();
    let mut rt: Vec<&X> = Vec::new();
    for x in t {
        match rs.iter().position(|y| eq(y, x)) {
            Some(i) => {
                rs.remove(i);
            }
            None => rt.push(x),
        }
    }
    !rs.is_empty() && rt.iter().all(|x| rs.iter().any(|y| gt(y, x)))
}

/// `s >_kbo t` for two subterms of a rule.
pub(crate) fn kbo_greater(rule: &Rule, s: NodeId, t: NodeId) -> bool {
    greater(&term(rule, s), &term(rule, t))
}

// ----- ground terms ----------------------------------------------------------------------------

/// Comparisons a ground order check may make before giving up.
#[cfg_attr(not(all(test, feature = "check")), allow(dead_code))]
const GROUND_STEPS: u32 = 4096;

/// `s > t` in the ground Knuth–Bendix order on context nodes (weight = tree size, the same
/// precedence, a cast's width and an extract's offset as numeric parameters, commutative
/// operands as a multiset): `Some(answer)`, or `None` when undecided (both tree sizes saturate
/// where the comparison needs them, or the comparison is over budget). Every application of a
/// directed rule should decrease this order; the engine can check it as a postcondition.
#[cfg_attr(not(all(test, feature = "check")), allow(dead_code))]
pub(crate) fn ground_greater(cx: &Context, s: u32, t: u32) -> Option<bool> {
    let mut steps = GROUND_STEPS;
    ground(cx, s, t, &mut steps)
}

fn ground(cx: &Context, mut s: u32, mut t: u32, steps: &mut u32) -> Option<bool> {
    loop {
        if s == t {
            return Some(false);
        }
        if *steps == 0 {
            return None;
        }
        *steps -= 1;
        let (ws, wt) = (cx.meta[s as usize].tree, cx.meta[t as usize].tree);
        if ws == u32::MAX && wt == u32::MAX {
            return None;
        }
        match ws.cmp(&wt) {
            Ordering::Greater => return Some(true),
            Ordering::Less => return Some(false),
            Ordering::Equal => {}
        }
        let (ns, nt) = (cx.node(s), cx.node(t));
        if ns.op.arity() == 0 || nt.op.arity() == 0 {
            return Some(false);
        }
        match op_rank(ns.op).cmp(&op_rank(nt.op)) {
            Ordering::Greater => return Some(true),
            Ordering::Less => return Some(false),
            Ordering::Equal => {}
        }
        let param = |op: OpCode, width: u16, b: u32| match op {
            OpCode::Zext | OpCode::Sext => (width, 0),
            OpCode::Extract => (width, b),
            _ => (0, 0),
        };
        match param(ns.op, ns.width, ns.b).cmp(&param(nt.op, nt.width, nt.b)) {
            Ordering::Greater => return Some(true),
            Ordering::Less => return Some(false),
            Ordering::Equal => {}
        }
        let (ks, kt) = (
            [ns.a, ns.b, ns.c][..ns.op.arity()].to_vec(),
            [nt.a, nt.b, nt.c][..nt.op.arity()].to_vec(),
        );
        if op_commutative(ns.op) {
            let budget = core::cell::Cell::new(*steps);
            let undecided = core::cell::Cell::new(false);
            let gt = |a: &u32, b: &u32| {
                let mut st = budget.get();
                let r = ground(cx, *a, *b, &mut st);
                budget.set(st);
                if r.is_none() {
                    undecided.set(true);
                }
                r == Some(true)
            };
            let r = multiset_greater(&ks, &kt, &|a, b| a == b, &gt);
            *steps = budget.get();
            return if r {
                Some(true)
            } else if undecided.get() {
                None
            } else {
                Some(false)
            };
        }
        // Lexicographic: continue with the first differing operands.
        match ks.iter().zip(&kt).find(|(a, b)| a != b) {
            Some((&a, &b)) => {
                s = a;
                t = b;
            }
            None => return Some(false),
        }
    }
}
