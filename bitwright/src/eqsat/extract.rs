//! Extraction: positive operator costs by iterative fixpoint (cyclic classes are fine; the
//! selection is acyclic), with optional shared-DAG coordinate-descent refinement
//! ([`ExtractionMode::Dag`]). Ties go to the original imported e-node, then the lowest index.

use super::egraph::{ClassId, EGraph, EOp};
use super::{CostModel, ExtractionMode};
use crate::engine::Exhausted;
use crate::engine::budget::{Counter, Meter};
use crate::error::Error;
use crate::expr::Context;
use crate::hash::IdMap;

/// The chosen e-node per canonical class, and its unit tree cost; `Err` when the budget ran out.
#[cfg(test)]
pub(crate) fn costs(
    eg: &mut EGraph,
    m: &mut Meter<'_>,
) -> Result<IdMap<ClassId, (u64, u32)>, Exhausted> {
    costs_unit_tree(eg, m)
}

fn costs_unit_tree(
    eg: &mut EGraph,
    m: &mut Meter<'_>,
) -> Result<IdMap<ClassId, (u64, u32)>, Exhausted> {
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
            // A cheaper child lowers this node's cost even when the selected node is
            // unchanged. Propagate that improvement to its parents on the next pass.
            if better {
                best.insert(c, (cost, idx));
                changed = true;
            }
        }
        if !changed {
            return Ok(best);
        }
    }
}

fn costs_weighted_tree(
    eg: &mut EGraph,
    node_costs: &[u64],
    m: &mut Meter<'_>,
) -> Result<IdMap<ClassId, (u64, u32)>, Exhausted> {
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
            let mut cost: u64 = node_costs[idx as usize].max(1);
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
            if better {
                best.insert(c, (cost, idx));
                changed = true;
            }
        }
        if !changed {
            return Ok(best);
        }
    }
}

/// Checks whether `target` is reachable from `kids` in the current acyclic `best` selection.
fn reaches_class(
    eg: &mut EGraph,
    best: &IdMap<ClassId, (u64, u32)>,
    kids: &[ClassId],
    target: ClassId,
    m: &mut Meter<'_>,
) -> Result<bool, Exhausted> {
    let mut seen: IdMap<ClassId, ()> = IdMap::default();
    let mut stack: Vec<ClassId> = kids.iter().map(|&k| eg.find(k)).collect();
    while let Some(cur) = stack.pop() {
        if cur == target {
            return Ok(true);
        }
        if seen.insert(cur, ()).is_some() {
            continue;
        }
        m.charge(Counter::EqsatWork, 1)?;
        let Some(&(_, bidx)) = best.get(&cur) else {
            continue;
        };
        let bn = eg.nodes[bidx as usize];
        for &k in &bn.kids[..bn.op.arity()] {
            let kf = eg.find(k);
            if !seen.contains_key(&kf) {
                stack.push(kf);
            }
        }
    }
    Ok(false)
}

/// Marginal DAG cost of selecting `idx` for class `c` when classes in `outside` are already paid
/// for elsewhere. Returns `None` if any child has no `best` selection or if selecting `idx` would
/// introduce a cycle through `c`.
fn marginal_dag_cost(
    eg: &mut EGraph,
    best: &IdMap<ClassId, (u64, u32)>,
    node_costs: &[u64],
    idx: u32,
    c: ClassId,
    outside: &IdMap<ClassId, ()>,
    m: &mut Meter<'_>,
) -> Result<Option<u64>, Exhausted> {
    let n = eg.nodes[idx as usize];
    let arity = n.op.arity();
    let mut kids = [0 as ClassId; 3];
    for (slot, &k) in kids.iter_mut().zip(&n.kids[..arity]) {
        let kf = eg.find(k);
        if !best.contains_key(&kf) {
            return Ok(None);
        }
        *slot = kf;
    }
    if reaches_class(eg, best, &kids[..arity], c, m)? {
        return Ok(None);
    }
    let mut total = node_costs[idx as usize].max(1);
    let mut seen: IdMap<ClassId, ()> = IdMap::default();
    let mut stack: Vec<ClassId> = kids[..arity].to_vec();
    while let Some(cur) = stack.pop() {
        if outside.contains_key(&cur) || seen.insert(cur, ()).is_some() {
            continue;
        }
        m.charge(Counter::EqsatWork, 1)?;
        let Some(&(_, bidx)) = best.get(&cur) else {
            return Ok(None);
        };
        total = total.saturating_add(node_costs[bidx as usize].max(1));
        let bn = eg.nodes[bidx as usize];
        for &k in &bn.kids[..bn.op.arity()] {
            let kf = eg.find(k);
            if !outside.contains_key(&kf) && !seen.contains_key(&kf) {
                stack.push(kf);
            }
        }
    }
    Ok(Some(total))
}

/// Computes the per-class selection under `model`, refining for shared subterms when
/// [`ExtractionMode::Dag`] is active.
pub(crate) fn costs_for(
    eg: &mut EGraph,
    root: ClassId,
    model: &CostModel,
    external_shared: &IdMap<ClassId, ()>,
    m: &mut Meter<'_>,
) -> Result<IdMap<ClassId, (u64, u32)>, Exhausted> {
    if model.is_default_ast_tree() {
        return costs_unit_tree(eg, m);
    }
    let mut node_costs = Vec::with_capacity(eg.nodes.len());
    for idx in 0..eg.nodes.len() as u32 {
        let (op, w) = eg.cost_op(idx);
        node_costs.push(model.cost(op, w).max(1));
    }
    let mut best = costs_weighted_tree(eg, &node_costs, m)?;
    if model.mode() == ExtractionMode::Tree {
        return Ok(best);
    }
    // Pass 1: bottom-up cone-DAG pass over all reachable canonical classes (ordered by ascending
    // positive tree cost), discounting shared descendants within each candidate's own cone as well
    // as classes already materialized in other roots of the batch (`external_shared`).
    let mut ordered: Vec<(u64, ClassId)> = best.iter().map(|(&c, &(tc, _))| (tc, c)).collect();
    ordered.sort_unstable();
    for &(_, c) in &ordered {
        let Some(&(_, cur_idx)) = best.get(&c) else {
            continue;
        };
        let nodes = eg.classes[c as usize].nodes.clone();
        if nodes.len() <= 1 {
            continue;
        }
        let Some(mut best_cost) =
            marginal_dag_cost(eg, &best, &node_costs, cur_idx, c, external_shared, m)?
        else {
            continue;
        };
        let mut best_idx = cur_idx;
        for idx in nodes {
            if idx == cur_idx {
                continue;
            }
            let Some(cand_cost) =
                marginal_dag_cost(eg, &best, &node_costs, idx, c, external_shared, m)?
            else {
                continue;
            };
            let better = cand_cost < best_cost
                || (cand_cost == best_cost
                    && (eg.imported[idx as usize], std::cmp::Reverse(idx))
                        > (eg.imported[best_idx as usize], std::cmp::Reverse(best_idx)));
            if better {
                best_cost = cand_cost;
                best_idx = idx;
            }
        }
        best.insert(c, (best_cost, best_idx));
    }

    // Passes 2..=4: exact coordinate-descent DAG refinement from `root`, discounting classes
    // reachable from `root` along paths that do not pass through `c` (`outside`). Every accepted
    // move strictly decreases the total DAG cost of `root` while preserving acyclicity.
    let root_c = eg.find(root);
    for _ in 0..3 {
        let mut active: Vec<ClassId> = Vec::new();
        let mut seen: IdMap<ClassId, ()> = IdMap::default();
        let mut stack = vec![root_c];
        while let Some(cur) = stack.pop() {
            if seen.insert(cur, ()).is_some() {
                continue;
            }
            active.push(cur);
            if let Some(&(_, bidx)) = best.get(&cur) {
                let bn = eg.nodes[bidx as usize];
                for &k in &bn.kids[..bn.op.arity()] {
                    stack.push(eg.find(k));
                }
            }
        }
        let mut refined = false;
        for c in active {
            let nodes = eg.classes[c as usize].nodes.clone();
            if nodes.len() <= 1 {
                continue;
            }
            let Some(&(_, cur_idx)) = best.get(&c) else {
                continue;
            };
            // Classes reachable from `root_c` without passing through `c`.
            let mut outside = external_shared.clone();
            if c != root_c {
                let mut walk = vec![root_c];
                while let Some(u) = walk.pop() {
                    if u == c || outside.insert(u, ()).is_some() {
                        continue;
                    }
                    m.charge(Counter::EqsatWork, 1)?;
                    if let Some(&(_, bidx)) = best.get(&u) {
                        let bn = eg.nodes[bidx as usize];
                        for &k in &bn.kids[..bn.op.arity()] {
                            let kf = eg.find(k);
                            if kf != c && !outside.contains_key(&kf) {
                                walk.push(kf);
                            }
                        }
                    }
                }
            }
            let Some(mut best_cost) =
                marginal_dag_cost(eg, &best, &node_costs, cur_idx, c, &outside, m)?
            else {
                continue;
            };
            let mut best_idx = cur_idx;
            for idx in nodes {
                if idx == best_idx {
                    continue;
                }
                let Some(cand_cost) =
                    marginal_dag_cost(eg, &best, &node_costs, idx, c, &outside, m)?
                else {
                    continue;
                };
                if cand_cost < best_cost {
                    best_cost = cand_cost;
                    best_idx = idx;
                }
            }
            if best_idx != cur_idx {
                best.insert(c, (best_cost, best_idx));
                refined = true;
            }
        }
        if !refined {
            break;
        }
    }
    Ok(best)
}

/// Builds the selection rooted at class `root` in the arena across mixed widths (`1..=512`).
pub(crate) fn build(
    eg: &mut EGraph,
    best: &IdMap<ClassId, (u64, u32)>,
    root: ClassId,
    cx: &mut Context,
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
        let cw = eg.classes[c as usize].width;
        let id = match n.op {
            EOp::ConstSmall { .. } | EOp::ConstWide(_) => {
                let v = eg
                    .const_val(n.op)
                    .unwrap_or_else(|| crate::BitVec::zero(cw));
                cx.mk_const(&v)?
            }
            EOp::Leaf { node, .. } => node,
            EOp::Un(op) => cx.c_un(op, at(kids[0]))?,
            EOp::Bin(op) => cx.c_bin(op, at(kids[0]), at(kids[1]))?,
            EOp::Cmp(op) => cx.c_cmp(op, at(kids[0]), at(kids[1]))?,
            EOp::Zext(to) => cx.c_zext(at(kids[0]), to)?,
            EOp::Sext(to) => cx.c_sext(at(kids[0]), to)?,
            EOp::Extract { lo, width } => cx.c_extract(at(kids[0]), lo, width)?,
            EOp::Concat => cx.c_concat(at(kids[0]), at(kids[1]))?,
            EOp::Select => cx.c_select(at(kids[0]), at(kids[1]), at(kids[2]))?,
        };
        built.insert(c, id);
    }
    Ok(built.get(&eg.find(root)).copied())
}
