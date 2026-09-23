//! Extraction: positive tree-size costs by iterative fixpoint (cyclic classes are fine; the
//! selection is acyclic), ties to the original imported e-node, then the lowest index.

use super::egraph::{ClassId, EGraph, EOp};
use crate::engine::budget::{Counter, Meter};
use crate::error::Error;
use crate::expr::Context;
use crate::hash::IdMap;

/// The chosen e-node per canonical class, and its tree cost; `None` when the budget ran out.
pub(crate) fn costs(
    eg: &mut EGraph,
    m: &mut Meter<'_>,
) -> Result<IdMap<ClassId, (u64, u32)>, crate::engine::Exhausted> {
    let mut best: IdMap<ClassId, (u64, u32)> = IdMap::default();
    loop {
        let mut changed = false;
        for idx in 0..eg.nodes.len() as u32 {
            m.charge(Counter::EqsatWork, 1)?;
            let n = eg.nodes[idx as usize];
            let c = {
                let c = eg.node_class[idx as usize];
                eg.find(c)
            };
            let mut cost: u64 = 1;
            let mut known = true;
            for &k in &n.kids[..n.op.arity()] {
                let k = eg.find(k);
                match best.get(&k) {
                    Some(&(ck, _)) => cost = cost.saturating_add(ck),
                    None => known = false,
                }
            }
            if !known {
                continue;
            }
            let better = match best.get(&c) {
                None => true,
                Some(&(bc, bi)) => {
                    cost < bc
                        || (cost == bc
                            && (eg.imported[idx as usize], std::cmp::Reverse(idx))
                                > (eg.imported[bi as usize], std::cmp::Reverse(bi)))
                }
            };
            if better && best.get(&c).map(|b| b.1) != Some(idx) {
                best.insert(c, (cost, idx));
                changed = true;
            }
        }
        if !changed {
            return Ok(best);
        }
    }
}

/// Builds the selection rooted at class `root` in the arena.
pub(crate) fn build(
    eg: &mut EGraph,
    best: &IdMap<ClassId, (u64, u32)>,
    root: ClassId,
    cx: &mut Context,
    w: crate::Width,
) -> Result<Option<u32>, Error> {
    let mut built: IdMap<ClassId, u32> = IdMap::default();
    let mut stack: Vec<(ClassId, bool)> = vec![(eg.find(root), false)];
    while let Some((c, expanded)) = stack.pop() {
        if built.contains_key(&c) {
            continue;
        }
        let Some(&(_, idx)) = best.get(&c) else {
            return Ok(None);
        };
        let n = eg.nodes[idx as usize];
        let kids: Vec<ClassId> = n.kids[..n.op.arity()].iter().map(|&k| eg.find(k)).collect();
        if !expanded {
            stack.push((c, true));
            for &k in &kids {
                if !built.contains_key(&k) {
                    stack.push((k, false));
                }
            }
            continue;
        }
        let at = |k: ClassId| built[&k];
        let id = match n.op {
            EOp::Const(v) => cx.mk_const(&v)?,
            EOp::Leaf(a) => a,
            EOp::Un(op) => cx.c_un(op, at(kids[0]))?,
            EOp::Bin(op) => cx.c_bin(op, at(kids[0]), at(kids[1]))?,
        };
        let _ = w;
        built.insert(c, id);
    }
    Ok(built.get(&eg.find(root)).copied())
}
