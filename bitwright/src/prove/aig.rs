//! An and-inverter graph: every gate a conjunction of two literals, negation free on the
//! edges, with constant folding, trivial simplifications (`a ∧ a`, `a ∧ ¬a`) and structural
//! hashing, so equal subcircuits are one gate. Clauses are generated (Tseitin) only for the
//! gates a goal reaches.

use std::collections::HashMap;

use super::sat::{Lit, Solver};

/// An AIG literal: `2·node` (the node's value) or `2·node + 1` (its negation). Node 0 is the
/// constant false.
pub type L = u32;

/// Constant false.
pub const FALSE: L = 0;
/// Constant true.
pub const TRUE: L = 1;

#[derive(Copy, Clone, Debug)]
enum Node {
    Const,
    Input,
    And(L, L),
}

/// The graph.
#[derive(Debug)]
pub struct Aig {
    nodes: Vec<Node>,
    hash: HashMap<(L, L), L>,
}

impl Default for Aig {
    fn default() -> Self {
        Aig::new()
    }
}

impl Aig {
    /// An empty graph (the constant only).
    pub fn new() -> Aig {
        Aig {
            nodes: vec![Node::Const],
            hash: HashMap::new(),
        }
    }

    /// The number of nodes (gates, inputs and the constant).
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the graph has only its constant.
    pub fn is_empty(&self) -> bool {
        self.nodes.len() == 1
    }

    /// A new input.
    pub fn input(&mut self) -> L {
        self.nodes.push(Node::Input);
        ((self.nodes.len() - 1) as u32) << 1
    }

    /// `a ∧ b`.
    pub fn and(&mut self, a: L, b: L) -> L {
        let (a, b) = if a <= b { (a, b) } else { (b, a) };
        if a == FALSE || a == b ^ 1 {
            return FALSE;
        }
        if a == TRUE || a == b {
            return b;
        }
        if let Some(&g) = self.hash.get(&(a, b)) {
            return g;
        }
        self.nodes.push(Node::And(a, b));
        let g = ((self.nodes.len() - 1) as u32) << 1;
        self.hash.insert((a, b), g);
        g
    }

    /// `a ∨ b`.
    pub fn or(&mut self, a: L, b: L) -> L {
        self.and(a ^ 1, b ^ 1) ^ 1
    }

    /// `a ⊕ b`.
    pub fn xor(&mut self, a: L, b: L) -> L {
        if a == FALSE {
            return b;
        }
        if b == FALSE {
            return a;
        }
        if a == TRUE {
            return b ^ 1;
        }
        if b == TRUE {
            return a ^ 1;
        }
        if a == b {
            return FALSE;
        }
        if a == b ^ 1 {
            return TRUE;
        }
        let p = self.and(a, b ^ 1);
        let q = self.and(a ^ 1, b);
        self.or(p, q)
    }

    /// `a ↔ b`.
    pub fn xnor(&mut self, a: L, b: L) -> L {
        self.xor(a, b) ^ 1
    }

    /// `c ? t : e`.
    pub fn mux(&mut self, c: L, t: L, e: L) -> L {
        if c == TRUE || t == e {
            return t;
        }
        if c == FALSE {
            return e;
        }
        let p = self.and(c, t);
        let q = self.and(c ^ 1, e);
        self.or(p, q)
    }

    /// The majority of three (a full adder's carry).
    pub fn maj(&mut self, a: L, b: L, c: L) -> L {
        let ab = self.and(a, b);
        let ac = self.and(a, c);
        let bc = self.and(b, c);
        let t = self.or(ab, ac);
        self.or(t, bc)
    }

    /// The value of every node, the `k`-th input (in creation order) taking `input(k)`: nodes
    /// are created after their operands, so one pass in order evaluates them all.
    pub fn eval_all(&self, input: impl Fn(u32) -> bool) -> Vec<bool> {
        let mut vals = Vec::with_capacity(self.nodes.len());
        let mut k = 0;
        for n in &self.nodes {
            let v = match *n {
                Node::Const => false,
                Node::Input => {
                    k += 1;
                    input(k - 1)
                }
                Node::And(a, b) => {
                    let get = |l: L| vals[(l >> 1) as usize] != (l & 1 == 1);
                    get(a) && get(b)
                }
            };
            vals.push(v);
        }
        vals
    }

    /// A literal's value in `eval_all`'s result.
    pub fn value(vals: &[bool], l: L) -> bool {
        vals[(l >> 1) as usize] != (l & 1 == 1)
    }

    /// The conjunction of many.
    pub fn and_all(&mut self, ls: &[L]) -> L {
        ls.iter().fold(TRUE, |acc, &l| self.and(acc, l))
    }

    /// The disjunction of many.
    pub fn or_all(&mut self, ls: &[L]) -> L {
        ls.iter().fold(FALSE, |acc, &l| self.or(acc, l))
    }
}

/// The clauses of an AIG's goals for a SAT solver: a variable per reached node (inputs keep
/// theirs for reading models back).
#[derive(Debug)]
pub struct Cnf {
    /// AIG node → solver variable.
    var: HashMap<u32, u32>,
    /// The clauses, as given to the solver (kept for the proof checker).
    pub clauses: Vec<Vec<Lit>>,
}

impl Cnf {
    /// Tseitin clauses for every gate `roots` reach, added to `solver` (and kept).
    pub fn encode(aig: &Aig, roots: &[L], solver: &mut Solver) -> Cnf {
        let mut cnf = Cnf {
            var: HashMap::new(),
            clauses: Vec::new(),
        };
        let mut stack: Vec<u32> = roots.iter().map(|&l| l >> 1).collect();
        let mut order: Vec<u32> = Vec::new();
        let mut state: HashMap<u32, bool> = HashMap::new();
        while let Some(n) = stack.pop() {
            match state.get(&n) {
                Some(true) => continue,
                Some(false) => {
                    state.insert(n, true);
                    order.push(n);
                    continue;
                }
                None => {}
            }
            state.insert(n, false);
            stack.push(n);
            if let Node::And(a, b) = aig.nodes[n as usize] {
                for c in [a >> 1, b >> 1] {
                    if !state.contains_key(&c) {
                        stack.push(c);
                    }
                }
            }
        }
        for n in order {
            let v = solver.new_var();
            cnf.var.insert(n, v);
            match aig.nodes[n as usize] {
                Node::Const => cnf.push(solver, &[Lit::neg(v)]),
                Node::Input => {}
                Node::And(a, b) => {
                    let (la, lb) = (cnf.lit(a), cnf.lit(b));
                    let g = Lit::pos(v);
                    cnf.push(solver, &[!g, la]);
                    cnf.push(solver, &[!g, lb]);
                    cnf.push(solver, &[g, !la, !lb]);
                }
            }
        }
        cnf
    }

    fn push(&mut self, solver: &mut Solver, c: &[Lit]) {
        self.clauses.push(c.to_vec());
        solver.add_clause(c);
    }

    /// The solver literal of an AIG literal (its node must have been encoded).
    pub fn lit(&self, l: L) -> Lit {
        let v = self.var[&(l >> 1)];
        Lit::new(v, l & 1 == 0)
    }

    /// Asserts an AIG literal.
    pub fn assert(&mut self, l: L, solver: &mut Solver) {
        let x = self.lit(l);
        self.push(solver, &[x]);
    }

    /// The value of an AIG literal in a model (inputs not reached are false).
    pub fn value(&self, l: L, model: &[bool]) -> bool {
        let v = match self.var.get(&(l >> 1)) {
            Some(&v) => model.get(v as usize).copied().unwrap_or(false),
            None => false,
        };
        v != (l & 1 == 1)
    }
}
