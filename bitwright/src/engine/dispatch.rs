//! The dispatch net: candidate rules for a node by its operator, prefiltered by the operators
//! of its operands. A pure prefilter: every rule it drops could not have matched.

use crate::expr::{Context, OpCode};
use crate::ops::CmpOp;
use crate::rules::matcher::is_closed;
use crate::rules::{NodeId, ParamKind, RNode, Rule};

/// Operators as a bit set.
type Mask = u128;

const ALL: Mask = !0;

const fn bit(op: OpCode) -> Mask {
    1 << (op as u8)
}

// Every opcode (the floating-point ones last) must fit the mask.
const _: () = assert!((OpCode::FToU as u8) < Mask::BITS as u8);

struct Entry {
    rule: u32,
    /// Allowed operators of each operand of the pattern's root, in stored order.
    masks: [Mask; 3],
    arity: u8,
    /// The operands may appear in either order (commutative root).
    either: bool,
}

/// Candidate lists per operator, in priority order.
pub(crate) struct DispatchNet {
    by_op: Vec<Vec<Entry>>,
}

/// The operators a pattern node can match.
fn mask(rule: &Rule, pat: NodeId) -> Mask {
    if matches!(rule.nodes[pat as usize], RNode::Lit(_)) || is_closed(rule, pat) {
        return bit(OpCode::Const);
    }
    match &rule.nodes[pat as usize] {
        RNode::Param(i) => match rule.params[usize::from(*i)].kind {
            ParamKind::Any => ALL,
            ParamKind::Const => bit(OpCode::Const),
            ParamKind::Sym => bit(OpCode::Sym),
            ParamKind::NonConst => ALL & !bit(OpCode::Const),
        },
        RNode::Un(op, _) => bit(OpCode::from_un(*op)),
        RNode::Bin(op, ..) => bit(OpCode::from_bin(*op)),
        RNode::Cmp(op, ..) => bit(OpCode::from_cmp(op.canonical().0)),
        RNode::Zext(_) => bit(OpCode::Zext),
        RNode::Sext(_) => bit(OpCode::Sext),
        RNode::Extract(..) => bit(OpCode::Extract),
        RNode::Concat(..) => bit(OpCode::Concat),
        RNode::Select(..) => bit(OpCode::Select),
        RNode::Fp(f) => bit(f.kind.opcode()),
        // Nothing else occurs in a pattern.
        _ => 0,
    }
}

impl DispatchNet {
    /// A net over `rules[i]` for the given indices, in that (priority) order.
    pub(crate) fn new(rules: &[Rule], order: &[u32]) -> DispatchNet {
        let mut by_op: Vec<Vec<Entry>> = (0..OpCode::ALL.len()).map(|_| Vec::new()).collect();
        for &ri in order {
            let rule = &rules[ri as usize];
            let root = rule.lhs;
            let (op, kids, either): (OpCode, Vec<NodeId>, bool) = match &rule.nodes[root as usize] {
                RNode::Un(op, a) => (OpCode::from_un(*op), vec![*a], false),
                RNode::Bin(op, a, b) => (OpCode::from_bin(*op), vec![*a, *b], op.is_commutative()),
                RNode::Cmp(op, a, b) => {
                    let (stored, swap) = op.canonical();
                    let kids = if swap { vec![*b, *a] } else { vec![*a, *b] };
                    let either = matches!(stored, CmpOp::Eq | CmpOp::Ne);
                    (OpCode::from_cmp(stored), kids, either)
                }
                RNode::Zext(a) => (OpCode::Zext, vec![*a], false),
                RNode::Sext(a) => (OpCode::Sext, vec![*a], false),
                RNode::Extract(_, a) => (OpCode::Extract, vec![*a], false),
                RNode::Concat(h, l) => (OpCode::Concat, vec![*h, *l], false),
                RNode::Select(c, t, f) => (OpCode::Select, vec![*c, *t, *f], false),
                RNode::Fp(f) => (f.kind.opcode(), f.args.clone(), f.kind.commutative()),
                // A pattern rooted at a parameter or constant never decreases the order, so the
                // compiler rejects it; nothing to index.
                _ => continue,
            };
            if is_closed(rule, root) {
                continue;
            }
            let mut masks = [ALL; 3];
            for (k, &c) in kids.iter().enumerate() {
                masks[k] = mask(rule, c);
            }
            by_op[op as usize].push(Entry {
                rule: ri,
                masks,
                arity: kids.len() as u8,
                either,
            });
        }
        DispatchNet { by_op }
    }

    /// The candidate rules for node `n`, in priority order.
    pub(crate) fn candidates<'a>(
        &'a self,
        cx: &'a Context,
        n: u32,
    ) -> impl Iterator<Item = u32> + 'a {
        let node = cx.node(n);
        let kid_ops: [Mask; 3] = {
            let mut k = [0; 3];
            for (i, c) in node.children().enumerate() {
                k[i] = bit(cx.node(c).op);
            }
            k
        };
        // Extension nodes have no rules.
        let entries = self.by_op.get(node.op as usize).map_or(&[][..], |v| &v[..]);
        entries.iter().filter_map(move |e| {
            let fits = |order: [usize; 3]| {
                (0..e.arity as usize).all(|k| e.masks[k] & kid_ops[order[k]] != 0)
            };
            (fits([0, 1, 2]) || (e.either && fits([1, 0, 2]))).then_some(e.rule)
        })
    }
}
