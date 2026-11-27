//! The e-graph: per-class width-typed classes (`1..=512`) in insertion order, union by lower id
//! with path compression, a hash-cons of canonical e-nodes (commutative operands sorted),
//! deferred rebuilding through a worklist, constant folding, and reduced-product [`Facts`]
//! e-class analysis.

use crate::engine::Exhausted;
use crate::engine::budget::{Counter, Meter};
use crate::facts::Facts;
use crate::hash::IdMap;
use crate::ops::{BinOp, CmpOp, UnOp};
use crate::{BitVec, Width};

pub(crate) type ClassId = u32;

/// An e-node operator (compact 12-byte representation: wide constants are pooled on [`EGraph`]).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum EOp {
    ConstSmall {
        width: u16,
        lo: u32,
        hi: u32,
    },
    ConstWide(u32),
    /// A leaf: a node of the arena (a symbol, or an opaque atom) with its width.
    Leaf {
        node: u32,
        width: u16,
    },
    Un(UnOp),
    Bin(BinOp),
    Cmp(CmpOp),
    Zext(u16),
    Sext(u16),
    Extract {
        lo: u16,
        width: u16,
    },
    Concat,
    Select,
}

impl EOp {
    pub(crate) fn arity(&self) -> usize {
        match self {
            EOp::ConstSmall { .. } | EOp::ConstWide(_) | EOp::Leaf { .. } => 0,
            EOp::Un(_) | EOp::Zext(_) | EOp::Sext(_) | EOp::Extract { .. } => 1,
            EOp::Bin(_) | EOp::Cmp(_) | EOp::Concat => 2,
            EOp::Select => 3,
        }
    }

    pub(crate) fn is_const(&self) -> bool {
        matches!(self, EOp::ConstSmall { .. } | EOp::ConstWide(_))
    }
}

/// An e-node: an operator over up to three child classes (24 bytes).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ENode {
    pub(crate) op: EOp,
    pub(crate) kids: [ClassId; 3],
}

const _: () = assert!(core::mem::size_of::<ENode>() <= 24);

#[derive(Clone, Debug)]
pub(crate) struct Class {
    pub(crate) width: Width,
    pub(crate) nodes: Vec<u32>,
    pub(crate) parents: Vec<u32>,
    pub(crate) konst: Option<BitVec>,
    pub(crate) facts: Facts,
    pub(crate) has_const_node: bool,
    pub(crate) fact_refines: u8,
}

impl Default for Class {
    fn default() -> Self {
        Class {
            width: Width::W1,
            nodes: Vec::new(),
            parents: Vec::new(),
            konst: None,
            facts: Facts::top(Width::W1),
            has_const_node: false,
            fact_refines: 0,
        }
    }
}

/// Why a search step stopped.
#[derive(Debug)]
pub(crate) enum Halt {
    Budget(Exhausted),
    /// Two different constants or contradictory facts were united: only an unsound identity can
    /// cause this.
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
    wide_consts: Vec<BitVec>,
    wide_memo: IdMap<BitVec, u32>,
    pending: Vec<ClassId>,
    pub(crate) unions: u64,
}

fn commutative(op: EOp) -> bool {
    matches!(
        op,
        EOp::Bin(BinOp::Add | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor)
            | EOp::Cmp(CmpOp::Eq | CmpOp::Ne)
    )
}

impl EGraph {
    pub(crate) fn new(_root_width: Width) -> Self {
        EGraph {
            nodes: Vec::new(),
            node_class: Vec::new(),
            imported: Vec::new(),
            uf: Vec::new(),
            classes: Vec::new(),
            memo: IdMap::default(),
            wide_consts: Vec::new(),
            wide_memo: IdMap::default(),
            pending: Vec::new(),
            unions: 0,
        }
    }

    pub(crate) fn const_node(&mut self, v: BitVec) -> ENode {
        let w = v.width().bits();
        let op = match v.to_u64() {
            Some(x) => EOp::ConstSmall {
                width: w,
                lo: x as u32,
                hi: (x >> 32) as u32,
            },
            None => {
                let idx = match self.wide_memo.get(&v) {
                    Some(&i) => i,
                    None => {
                        let i = self.wide_consts.len() as u32;
                        self.wide_consts.push(v);
                        self.wide_memo.insert(v, i);
                        i
                    }
                };
                EOp::ConstWide(idx)
            }
        };
        ENode {
            op,
            kids: [0, 0, 0],
        }
    }

    pub(crate) fn const_val(&self, op: EOp) -> Option<BitVec> {
        match op {
            EOp::ConstSmall { width, lo, hi } => {
                let w = Width::new(width).ok()?;
                let x = u64::from(lo) | (u64::from(hi) << 32);
                Some(BitVec::wrapping_from_u64(w, x))
            }
            EOp::ConstWide(i) => self.wide_consts.get(i as usize).copied(),
            _ => None,
        }
    }

    pub(crate) fn lookup_const_node(&self, v: &BitVec) -> Option<ENode> {
        let w = v.width().bits();
        let op = match v.to_u64() {
            Some(x) => EOp::ConstSmall {
                width: w,
                lo: x as u32,
                hi: (x >> 32) as u32,
            },
            None => EOp::ConstWide(*self.wide_memo.get(v)?),
        };
        Some(ENode {
            op,
            kids: [0, 0, 0],
        })
    }

    pub(crate) fn find_enode(&mut self, n: ENode) -> Option<ClassId> {
        let n = self.canon(n);
        let &idx = self.memo.get(&n)?;
        let c = self.node_class[idx as usize];
        Some(self.find(c))
    }

    pub(crate) fn cost_op(&mut self, idx: u32) -> (super::CostOp, Width) {
        let n = self.nodes[idx as usize];
        let c = self.node_class[idx as usize];
        let cf = self.find(c);
        let cw = self.classes[cf as usize].width;
        let op = match n.op {
            EOp::ConstSmall { .. } | EOp::ConstWide(_) => super::CostOp::Const,
            EOp::Leaf { .. } => super::CostOp::Symbol,
            EOp::Un(u) => super::CostOp::Un(u),
            EOp::Bin(b) => super::CostOp::Bin(b),
            EOp::Cmp(cmp) => super::CostOp::Cmp(cmp),
            EOp::Zext(_) => {
                let k0 = self.find(n.kids[0]);
                super::CostOp::Zext {
                    from: self.classes[k0 as usize].width,
                    to: cw,
                }
            }
            EOp::Sext(_) => {
                let k0 = self.find(n.kids[0]);
                super::CostOp::Sext {
                    from: self.classes[k0 as usize].width,
                    to: cw,
                }
            }
            EOp::Extract { lo, .. } => {
                let k0 = self.find(n.kids[0]);
                super::CostOp::Extract {
                    from: self.classes[k0 as usize].width,
                    lo,
                    width: cw,
                }
            }
            EOp::Concat => {
                let k0 = self.find(n.kids[0]);
                let k1 = self.find(n.kids[1]);
                super::CostOp::Concat {
                    hi: self.classes[k0 as usize].width,
                    lo: self.classes[k1 as usize].width,
                }
            }
            EOp::Select => super::CostOp::Select(cw),
        };
        (op, cw)
    }

    fn node_width(&mut self, n: &ENode) -> Option<Width> {
        match n.op {
            EOp::ConstSmall { width, .. }
            | EOp::Leaf { width, .. }
            | EOp::Zext(width)
            | EOp::Sext(width)
            | EOp::Extract { width, .. } => Width::new(width).ok(),
            EOp::ConstWide(i) => self.wide_consts.get(i as usize).map(BitVec::width),
            EOp::Un(_) | EOp::Bin(_) => {
                let c0 = self.find(n.kids[0]);
                Some(self.classes[c0 as usize].width)
            }
            EOp::Cmp(_) => Some(Width::W1),
            EOp::Concat => {
                let c0 = self.find(n.kids[0]);
                let c1 = self.find(n.kids[1]);
                let sum = u32::from(self.classes[c0 as usize].width.bits())
                    + u32::from(self.classes[c1 as usize].width.bits());
                u16::try_from(sum).ok().and_then(|b| Width::new(b).ok())
            }
            EOp::Select => {
                let c1 = self.find(n.kids[1]);
                Some(self.classes[c1 as usize].width)
            }
        }
    }

    fn fold(&self, op: EOp, w: Width, k: [Option<BitVec>; 3]) -> Option<BitVec> {
        match op {
            EOp::ConstSmall { .. } | EOp::ConstWide(_) => self.const_val(op),
            EOp::Leaf { .. } => None,
            EOp::Un(u) => BitVec::apply_un(u, &k[0]?).ok(),
            EOp::Bin(b) => BitVec::apply_bin(b, &k[0]?, &k[1]?).ok(),
            EOp::Cmp(c) => BitVec::apply_cmp(c, &k[0]?, &k[1]?)
                .ok()
                .map(BitVec::from_bool),
            EOp::Zext(_) => k[0]?.zext(w).ok(),
            EOp::Sext(_) => k[0]?.sext(w).ok(),
            EOp::Extract { lo, .. } => k[0]?.extract(lo, w).ok(),
            EOp::Concat => BitVec::concat(&k[0]?, &k[1]?).ok(),
            EOp::Select => match k[0] {
                Some(c) => {
                    if c.is_zero() {
                        k[2]
                    } else {
                        k[1]
                    }
                }
                None if k[1].is_some() && k[1] == k[2] => k[1],
                None => None,
            },
        }
    }

    fn eval_facts(&mut self, n: &ENode, w: Width, leaf_facts: Option<Facts>) -> Facts {
        let mut kf = [Facts::top(Width::W1); 3];
        for (i, slot) in kf.iter_mut().enumerate().take(n.op.arity()) {
            let c = self.find(n.kids[i]);
            *slot = self.classes[c as usize].facts;
        }
        match n.op {
            EOp::ConstSmall { .. } | EOp::ConstWide(_) => self
                .const_val(n.op)
                .map_or_else(|| Facts::top(w), |v| Facts::constant(&v)),
            EOp::Leaf { .. } => leaf_facts
                .filter(|f| f.width() == w)
                .unwrap_or_else(|| Facts::top(w)),
            EOp::Un(u) => Facts::apply_un(u, &kf[0]).unwrap_or_else(|_| Facts::top(w)),
            EOp::Bin(b) => Facts::apply_bin(b, &kf[0], &kf[1]).unwrap_or_else(|_| Facts::top(w)),
            EOp::Cmp(c) => {
                Facts::apply_cmp(c, &kf[0], &kf[1]).unwrap_or_else(|_| Facts::top(Width::W1))
            }
            EOp::Zext(_) => kf[0].zext(w).unwrap_or_else(|_| Facts::top(w)),
            EOp::Sext(_) => kf[0].sext(w).unwrap_or_else(|_| Facts::top(w)),
            EOp::Extract { lo, .. } => kf[0].extract(lo, w).unwrap_or_else(|_| Facts::top(w)),
            EOp::Concat => Facts::concat(&kf[0], &kf[1]).unwrap_or_else(|_| Facts::top(w)),
            EOp::Select => Facts::select(&kf[0], &kf[1], &kf[2]).unwrap_or_else(|_| Facts::top(w)),
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
        let mut k = [0; 3];
        for (i, slot) in k.iter_mut().enumerate().take(n.op.arity()) {
            *slot = self.find(n.kids[i]);
        }
        if commutative(n.op) && k[1] < k[0] {
            k.swap(0, 1);
        }
        ENode { op: n.op, kids: k }
    }

    fn konst_of(&mut self, n: &ENode) -> [Option<BitVec>; 3] {
        let mut k = [None, None, None];
        for (i, slot) in k.iter_mut().enumerate().take(n.op.arity()) {
            let c = self.find(n.kids[i]);
            *slot = self.classes[c as usize].konst;
        }
        k
    }

    /// Adds an e-node (or finds its class), optionally refining with `leaf_facts`.
    pub(crate) fn add_with_facts(
        &mut self,
        n: ENode,
        imported: bool,
        leaf_facts: Option<Facts>,
        m: &mut Meter<'_>,
    ) -> Result<ClassId, Halt> {
        let n = self.canon(n);
        m.charge(Counter::EqsatWork, 1)?;
        if let Some(&i) = self.memo.get(&n) {
            let c = self.node_class[i as usize];
            return Ok(self.find(c));
        }
        let w = self.node_width(&n).ok_or(Halt::Contract)?;
        m.charge(Counter::EqsatNodes, 1)?;
        let idx = self.nodes.len() as u32;
        let id = self.classes.len() as ClassId;
        let mut facts = self.eval_facts(&n, w, leaf_facts);
        let k = self.konst_of(&n);
        let konst = match (self.fold(n.op, w, k), facts.as_constant()) {
            (Some(x), Some(y)) if x != y => return Err(Halt::Contract),
            (Some(x), _) => {
                facts = Facts::constant(&x);
                Some(x)
            }
            (None, Some(y)) => Some(y),
            (None, None) => None,
        };
        self.nodes.push(n);
        self.node_class.push(id);
        self.imported.push(imported);
        self.uf.push(id);
        self.classes.push(Class {
            width: w,
            nodes: vec![idx],
            parents: Vec::new(),
            konst,
            facts,
            has_const_node: n.op.is_const(),
            fact_refines: 0,
        });
        for &kid in &n.kids[..n.op.arity()] {
            self.classes[kid as usize].parents.push(idx);
        }
        self.memo.insert(n, idx);
        Ok(id)
    }

    /// Adds an e-node (or finds its class).
    pub(crate) fn add(
        &mut self,
        n: ENode,
        imported: bool,
        m: &mut Meter<'_>,
    ) -> Result<ClassId, Halt> {
        self.add_with_facts(n, imported, None, m)
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
        if self.classes[keep as usize].width != self.classes[gone as usize].width {
            return Err(Halt::Contract);
        }
        let moved = std::mem::take(&mut self.classes[gone as usize]);
        let Some(mut facts) = self.classes[keep as usize].facts.meet(&moved.facts) else {
            return Err(Halt::Contract);
        };
        let mut konst = match (self.classes[keep as usize].konst, moved.konst) {
            (Some(x), Some(y)) if x != y => return Err(Halt::Contract),
            (x, y) => x.or(y),
        };
        if let Some(fc) = facts.as_constant() {
            match konst {
                Some(x) if x != fc => return Err(Halt::Contract),
                Some(_) => {}
                None => konst = Some(fc),
            }
        }
        if let Some(kv) = konst {
            facts = Facts::constant(&kv);
        }
        self.uf[gone as usize] = keep;
        let k = &mut self.classes[keep as usize];
        k.nodes.extend(moved.nodes);
        k.parents.extend(moved.parents);
        k.konst = konst;
        k.facts = facts;
        k.has_const_node |= moved.has_const_node;
        k.fact_refines = k.fact_refines.max(moved.fact_refines);
        self.pending.push(keep);
        self.unions += 1;
        Ok(true)
    }

    /// Restores the hash-cons, congruence, constant folding, and `Facts` refinements after unions.
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
                let pcr = self.find(pc);
                let pw = self.classes[pcr as usize].width;
                // Constant folding through the new operand classes.
                let k = self.konst_of(&n);
                if let Some(v) = self.fold(n.op, pw, k) {
                    match self.classes[pcr as usize].konst {
                        Some(x) if x != v => return Err(Halt::Contract),
                        Some(_) => {}
                        None => {
                            self.classes[pcr as usize].konst = Some(v);
                            self.classes[pcr as usize].facts = Facts::constant(&v);
                            self.pending.push(pcr);
                        }
                    }
                } else if self.classes[pcr as usize].fact_refines < 8 {
                    let nf = self.eval_facts(&n, pw, None);
                    let cur = self.classes[pcr as usize].facts;
                    let Some(merged) = cur.meet(&nf) else {
                        return Err(Halt::Contract);
                    };
                    if merged != cur {
                        self.classes[pcr as usize].facts = merged;
                        self.classes[pcr as usize].fact_refines =
                            self.classes[pcr as usize].fact_refines.saturating_add(1);
                        if let Some(v) = merged.as_constant() {
                            match self.classes[pcr as usize].konst {
                                Some(x) if x != v => return Err(Halt::Contract),
                                Some(_) => {}
                                None => self.classes[pcr as usize].konst = Some(v),
                            }
                        }
                        self.pending.push(pcr);
                    }
                }
                kept.push(p);
            }
            let c = self.find(c);
            self.classes[c as usize].parents.extend(kept);
        }
        Ok(())
    }

    /// Ensures every class whose `konst` was pinned by constant folding or `Facts` contains an
    /// explicit constant `ENode` so cost-based extraction can emit the constant directly.
    pub(crate) fn materialize_constants(&mut self, m: &mut Meter<'_>) -> Result<(), Halt> {
        let mut to_add: Vec<(ClassId, BitVec)> = Vec::new();
        for c in 0..self.classes.len() as ClassId {
            if self.uf[c as usize] == c
                && !self.classes[c as usize].has_const_node
                && let Some(v) = self.classes[c as usize].konst
            {
                to_add.push((c, v));
            }
        }
        if to_add.is_empty() {
            return Ok(());
        }
        for (c, v) in to_add {
            let cn = self.const_node(v);
            let kc = self.add(cn, false, m)?;
            self.union(c, kc, m)?;
        }
        self.rebuild(m)
    }

    /// The canonical classes, ascending.
    pub(crate) fn canonical_classes(&self) -> Vec<ClassId> {
        (0..self.classes.len() as ClassId)
            .filter(|&c| self.uf[c as usize] == c)
            .collect()
    }
}
