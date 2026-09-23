//! The e-graph: width-typed classes in insertion order, union by lower id with path
//! compression, a hash-cons of canonical e-nodes (commutative operands sorted), deferred
//! rebuilding through a worklist, and constant folding.

use crate::BitVec;
use crate::engine::Exhausted;
use crate::engine::budget::{Counter, Meter};
use crate::hash::IdMap;
use crate::ops::{BinOp, UnOp};

pub(crate) type ClassId = u32;

/// An e-node operator.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum EOp {
    Const(BitVec),
    /// A leaf: a node of the arena (a symbol, or an opaque atom).
    Leaf(u32),
    Un(UnOp),
    Bin(BinOp),
}

impl EOp {
    pub(crate) fn arity(&self) -> usize {
        match self {
            EOp::Const(_) | EOp::Leaf(_) => 0,
            EOp::Un(_) => 1,
            EOp::Bin(_) => 2,
        }
    }
}

/// An e-node: an operator over classes.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ENode {
    pub(crate) op: EOp,
    pub(crate) kids: [ClassId; 2],
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Class {
    pub(crate) nodes: Vec<u32>,
    pub(crate) parents: Vec<u32>,
    pub(crate) konst: Option<BitVec>,
}

/// Why a search step stopped.
#[derive(Debug)]
pub(crate) enum Halt {
    Budget(Exhausted),
    /// Two different constants were united: only an unsound identity can cause this.
    Contract,
}

impl From<Exhausted> for Halt {
    fn from(e: Exhausted) -> Self {
        Halt::Budget(e)
    }
}

#[derive(Clone)]
pub(crate) struct EGraph {
    pub(crate) nodes: Vec<ENode>,
    pub(crate) node_class: Vec<ClassId>,
    /// Whether each e-node came from the original expression.
    pub(crate) imported: Vec<bool>,
    uf: Vec<ClassId>,
    pub(crate) classes: Vec<Class>,
    memo: IdMap<ENode, u32>,
    pending: Vec<ClassId>,
    pub(crate) unions: u64,
}

fn commutative(op: EOp) -> bool {
    matches!(
        op,
        EOp::Bin(BinOp::Add | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor)
    )
}

fn fold(op: EOp, k: [Option<BitVec>; 2]) -> Option<BitVec> {
    match op {
        EOp::Const(v) => Some(v),
        EOp::Leaf(_) => None,
        EOp::Un(u) => Some(BitVec::un_unchecked(u, &k[0]?)),
        EOp::Bin(b) => Some(BitVec::bin_unchecked(b, &k[0]?, &k[1]?)),
    }
}

impl EGraph {
    pub(crate) fn new() -> Self {
        EGraph {
            nodes: Vec::new(),
            node_class: Vec::new(),
            imported: Vec::new(),
            uf: Vec::new(),
            classes: Vec::new(),
            memo: IdMap::default(),
            pending: Vec::new(),
            unions: 0,
        }
    }

    /// The canonical class of `c` (with path compression).
    pub(crate) fn find(&mut self, mut c: ClassId) -> ClassId {
        let mut root = c;
        while self.uf[root as usize] != root {
            root = self.uf[root as usize];
        }
        while self.uf[c as usize] != root {
            let next = self.uf[c as usize];
            self.uf[c as usize] = root;
            c = next;
        }
        root
    }

    fn canon(&mut self, n: ENode) -> ENode {
        let mut k = n.kids;
        for kid in k.iter_mut().take(n.op.arity()) {
            *kid = self.find(*kid);
        }
        if commutative(n.op) && k[1] < k[0] {
            k.swap(0, 1);
        }
        ENode { op: n.op, kids: k }
    }

    fn konst_of(&mut self, n: &ENode) -> [Option<BitVec>; 2] {
        let mut k = [None, None];
        for (i, slot) in k.iter_mut().enumerate().take(n.op.arity()) {
            let c = self.find(n.kids[i]);
            *slot = self.classes[c as usize].konst;
        }
        k
    }

    /// Adds an e-node (or finds its class).
    pub(crate) fn add(
        &mut self,
        n: ENode,
        imported: bool,
        m: &mut Meter<'_>,
    ) -> Result<ClassId, Halt> {
        let n = self.canon(n);
        m.charge(Counter::EqsatWork, 1)?;
        if let Some(&i) = self.memo.get(&n) {
            let c = self.node_class[i as usize];
            return Ok(self.find(c));
        }
        m.charge(Counter::EqsatNodes, 1)?;
        let idx = self.nodes.len() as u32;
        let id = self.classes.len() as ClassId;
        let konst = {
            let k = self.konst_of(&n);
            fold(n.op, k)
        };
        self.nodes.push(n);
        self.node_class.push(id);
        self.imported.push(imported);
        self.uf.push(id);
        self.classes.push(Class {
            nodes: vec![idx],
            parents: Vec::new(),
            konst,
        });
        for &kid in &n.kids[..n.op.arity()] {
            self.classes[kid as usize].parents.push(idx);
        }
        self.memo.insert(n, idx);
        Ok(id)
    }

    /// Unites two classes; whether they were different.
    pub(crate) fn union(
        &mut self,
        a: ClassId,
        b: ClassId,
        m: &mut Meter<'_>,
    ) -> Result<bool, Halt> {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return Ok(false);
        }
        m.charge(Counter::EqsatWork, 1)?;
        let (keep, gone) = if ra < rb { (ra, rb) } else { (rb, ra) };
        let moved = std::mem::take(&mut self.classes[gone as usize]);
        let konst = match (self.classes[keep as usize].konst, moved.konst) {
            (Some(x), Some(y)) if x != y => return Err(Halt::Contract),
            (x, y) => x.or(y),
        };
        self.uf[gone as usize] = keep;
        let k = &mut self.classes[keep as usize];
        k.nodes.extend(moved.nodes);
        k.parents.extend(moved.parents);
        k.konst = konst;
        self.pending.push(keep);
        self.unions += 1;
        Ok(true)
    }

    /// Restores the hash-cons and congruence after unions.
    pub(crate) fn rebuild(&mut self, m: &mut Meter<'_>) -> Result<(), Halt> {
        while let Some(c) = self.pending.pop() {
            let c = self.find(c);
            let parents = std::mem::take(&mut self.classes[c as usize].parents);
            let mut kept = Vec::with_capacity(parents.len());
            for p in parents {
                m.charge(Counter::EqsatWork, 1)?;
                let old = self.nodes[p as usize];
                if self.memo.get(&old) == Some(&p) {
                    self.memo.remove(&old);
                }
                let n = self.canon(old);
                self.nodes[p as usize] = n;
                let pc = self.node_class[p as usize];
                match self.memo.get(&n).copied() {
                    Some(q) if q != p => {
                        let qc = self.node_class[q as usize];
                        self.union(pc, qc, m)?;
                    }
                    _ => {
                        self.memo.insert(n, p);
                    }
                }
                // Constant folding through the new operand classes.
                let k = self.konst_of(&n);
                if let Some(v) = fold(n.op, k) {
                    let pcr = self.find(pc);
                    match self.classes[pcr as usize].konst {
                        Some(x) if x != v => return Err(Halt::Contract),
                        Some(_) => {}
                        None => {
                            self.classes[pcr as usize].konst = Some(v);
                            self.pending.push(pcr);
                        }
                    }
                }
                kept.push(p);
            }
            let c = self.find(c);
            self.classes[c as usize].parents.extend(kept);
        }
        Ok(())
    }

    /// The canonical classes, ascending.
    pub(crate) fn canonical_classes(&self) -> Vec<ClassId> {
        (0..self.classes.len() as ClassId)
            .filter(|&c| self.uf[c as usize] == c)
            .collect()
    }
}
