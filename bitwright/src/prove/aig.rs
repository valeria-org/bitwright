//! An and-inverter graph: every gate a conjunction of two literals, negation free on the
//! edges, with constant folding, trivial simplifications (`a ∧ a`, `a ∧ ¬a`) and structural
//! hashing, so equal subcircuits are one gate. Clauses are generated (Tseitin) only for the
//! gates a goal reaches.

use crate::hash::IdMap;

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
    hash: IdMap<(L, L), L>,
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
            hash: IdMap::default(),
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
        self.xor_raw(a, b)
    }

    /// Share complemented parity at a modular boundary.
    pub(super) fn xor_phase(&mut self, a: L, b: L) -> L {
        self.xor_raw(a & !1, b & !1) ^ ((a ^ b) & 1)
    }

    /// An exclusive or at a bitwise expression boundary, cancelling shared parity terms
    /// without changing the carry/sum structure inside arithmetic operators.
    pub(super) fn xor_simplified(&mut self, a: L, b: L) -> L {
        if a > TRUE
            && b > TRUE
            && a >> 1 != b >> 1
            && let Some(reduced) = self.cancel_xor(a, b)
        {
            return reduced;
        }
        if a <= TRUE || b <= TRUE {
            return self.xor_raw(a, b);
        }
        self.xor_raw(a & !1, b & !1) ^ ((a ^ b) & 1)
    }

    pub(super) fn xor_cancel_input(&mut self, a: L, b: L) -> L {
        // A common input can be exposed through two odd products without flattening the
        // surrounding carry networks. Inspect at most five XOR levels per operand.
        if a <= TRUE || b <= TRUE || a >> 1 == b >> 1 {
            return self.xor_raw(a, b);
        }
        let mut inputs = [[FALSE; 32]; 2];
        let mut lengths = [0; 2];
        for (side, root) in [a, b].into_iter().enumerate() {
            let mut stack = [(FALSE, 0u8); 32];
            stack[0] = (root, 0);
            let mut pending = 1;
            while pending != 0 {
                pending -= 1;
                let (l, depth) = stack[pending];
                if depth < 5
                    && let Some((x, y)) = self.xor_children(l)
                {
                    stack[pending] = (x, depth + 1);
                    stack[pending + 1] = (y, depth + 1);
                    pending += 2;
                } else if matches!(self.nodes[(l >> 1) as usize], Node::Input) {
                    inputs[side][lengths[side]] = l & !1;
                    lengths[side] += 1;
                }
            }
        }
        let target = inputs[0][..lengths[0]]
            .iter()
            .copied()
            .filter(|l| inputs[1][..lengths[1]].contains(l))
            .max();
        let Some(target) = target else {
            return self.xor_raw(a, b);
        };
        let a = self
            .xor_without_input(a, target, 0)
            .expect("bounded input occurrence");
        let b = self
            .xor_without_input(b, target, 0)
            .expect("bounded input occurrence");
        self.xor_raw(a, b)
    }

    // Remove one parity occurrence, rebuilding just its path. Other XOR branches stay
    // intact, including arithmetic sums and shared carry cones.
    fn xor_without_input(&mut self, l: L, target: L, depth: u8) -> Option<L> {
        if l & !1 == target {
            return Some(l & 1);
        }
        if depth == 5 {
            return None;
        }
        let (a, b) = self.xor_children(l)?;
        if let Some(a) = self.xor_without_input(a, target, depth + 1) {
            Some(self.xor_raw(a & !1, b & !1) ^ ((a ^ b) & 1))
        } else {
            let b = self.xor_without_input(b, target, depth + 1)?;
            Some(self.xor_raw(a & !1, b & !1) ^ ((a ^ b) & 1))
        }
    }

    /// The operands of a literal which is structurally an exclusive or. Sharing its inner
    /// gates does not change this identity; encoding still decides which gates may be hidden.
    fn xor_children(&self, l: L) -> Option<(L, L)> {
        let Node::And(a, b) = self.nodes[(l >> 1) as usize] else {
            return None;
        };
        if a & 1 == 0 || b & 1 == 0 {
            return None;
        }
        let (Node::And(p, q), Node::And(r, s)) =
            (self.nodes[(a >> 1) as usize], self.nodes[(b >> 1) as usize])
        else {
            return None;
        };
        if (r == p ^ 1 && s == q ^ 1) || (r == q ^ 1 && s == p ^ 1) {
            Some((p, q ^ (l & 1)))
        } else {
            None
        }
    }

    fn mux_children(&self, l: L) -> Option<(L, L, L)> {
        let Node::And(a, b) = self.nodes[(l >> 1) as usize] else {
            return None;
        };
        if a & 1 == 0 || b & 1 == 0 {
            return None;
        }
        let (Node::And(p, q), Node::And(r, s)) =
            (self.nodes[(a >> 1) as usize], self.nodes[(b >> 1) as usize])
        else {
            return None;
        };
        for (c, t) in [(p, q), (q, p)] {
            for (d, e) in [(r, s), (s, r)] {
                if c == d ^ 1 {
                    let invert = (l & 1) ^ 1;
                    let (t, e) = (t ^ invert, e ^ invert);
                    return Some(if c & 1 == 0 { (c, t, e) } else { (c ^ 1, e, t) });
                }
            }
        }
        None
    }

    // (a XOR b) OR (a XOR c) = mux(a, NOT(b AND c), b OR c). Extend a
    // previously factored mux along the same selector, without touching other gates.
    fn factor_xor_or(&mut self, a: L, b: L) -> Option<L> {
        if let (Some((x, y)), Some((u, v))) = (self.xor_children(a), self.xor_children(b)) {
            for (control, other) in [(x, y), (y, x)] {
                for (second, other2) in [(u, v), (v, u)] {
                    if control & !1 == second & !1 {
                        let (p, q) = (other ^ (control & 1), other2 ^ (second & 1));
                        let t = self.and(p, q) ^ 1;
                        let e = self.or(p, q);
                        return Some(self.mux(control & !1, t, e));
                    }
                }
            }
        }
        for (first, second) in [(a, b), (b, a)] {
            let Some((c, t, e)) = self.mux_children(first) else {
                continue;
            };
            if let Some((x, y)) = self.xor_children(second) {
                for (control, other) in [(x, y), (y, x)] {
                    if control & !1 == c {
                        let other = other ^ (control & 1);
                        let t = self.or(t, other ^ 1);
                        let e = self.or(e, other);
                        return Some(self.mux(c, t, e));
                    }
                }
            }
            if let Some((d, u, v)) = self.mux_children(second)
                && c == d
            {
                let t = self.or(t, u);
                let e = self.or(e, v);
                return Some(self.mux(c, t, e));
            }
        }
        None
    }

    /// Factor a small OR tree when its output must be true. Keep zero-target OR bits in
    /// their conjunction-of-fixed-XOR form, which exposes aliases directly during encoding.
    pub(super) fn factor_positive_or(&mut self, l: L, depth: u8) -> L {
        if depth == 0
            || l & 1 == 0
            || self.xor_children(l).is_some()
            || self.mux_children(l).is_some()
        {
            return l;
        }
        let Node::And(a, b) = self.nodes[(l >> 1) as usize] else {
            return l;
        };
        let a = self.factor_positive_or(a ^ 1, depth - 1);
        let b = self.factor_positive_or(b ^ 1, depth - 1);
        self.factor_xor_or(a, b).unwrap_or_else(|| self.or(a, b))
    }

    // Flatten only a bounded small parity cone, cancelling terms and normalizing phase. No
    // gate is deleted: previously observed literals and shared subcircuits retain their value.
    fn cancel_xor(&mut self, a: L, b: L) -> Option<L> {
        if self.xor_children(a).is_none() && self.xor_children(b).is_none() {
            return None;
        }
        let mut stack = [FALSE; 32];
        stack[0] = a;
        stack[1] = b;
        let mut pending = 2;
        let mut leaves = [FALSE; 16];
        let mut len = 0;
        let mut polarity = FALSE;
        let mut visits = 0;
        while pending != 0 {
            pending -= 1;
            let l = stack[pending];
            visits += 1;
            if visits > 64 {
                return None;
            }
            if let Some((x, y)) = self.xor_children(l) {
                if pending + 2 > stack.len() {
                    return None;
                }
                stack[pending] = x;
                stack[pending + 1] = y;
                pending += 2;
            } else {
                if len == leaves.len() {
                    return None;
                }
                polarity ^= l & 1;
                leaves[len] = l & !1;
                len += 1;
            }
        }
        leaves[..len].sort_unstable();
        let mut kept = 0;
        let mut i = 0;
        while i < len {
            let start = i;
            let l = leaves[i];
            while i < len && leaves[i] == l {
                i += 1;
            }
            if (i - start) & 1 == 1 && l != FALSE {
                leaves[kept] = l;
                kept += 1;
            }
        }
        if kept == len && polarity == FALSE {
            return None;
        }
        let mut out = FALSE;
        for &l in &leaves[..kept] {
            out = self.xor_raw(out, l);
        }
        Some(out ^ polarity)
    }

    fn xor_raw(&mut self, a: L, b: L) -> L {
        // Complemented inputs use the same parity node. Shared AND internals are
        // handled independently when selecting the CNF gate representations.
        let phase = (a ^ b) & 1;
        let (a, b) = (a & !1, b & !1);
        if a == FALSE {
            return b ^ phase;
        }
        if b == FALSE {
            return a ^ phase;
        }
        if a == b {
            return phase;
        }
        let p = self.and(a, b ^ 1);
        let q = self.and(a ^ 1, b);
        self.or(p, q) ^ phase
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
        // A constant makes it a conjunction or a disjunction of the others, and two operands
        // equal or opposite decide it (comparisons with a constant and additions of one meet
        // these at every bit).
        for (k, x, y) in [(a, b, c), (b, a, c), (c, a, b)] {
            if k == FALSE {
                return self.and(x, y);
            }
            if k == TRUE {
                return self.or(x, y);
            }
            if x == y {
                return x;
            }
            if x == y ^ 1 {
                return k;
            }
        }
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

    /// Maps input creation ordinals to dense ordinals in the support of `roots`.
    /// Unused inputs left by an abandoned word probe do not enlarge enumeration.
    pub(super) fn input_support(&self, roots: &[L]) -> (Vec<Option<usize>>, usize) {
        let mut live = vec![false; self.nodes.len()];
        let mut pending = roots.iter().map(|&l| (l >> 1) as usize).collect::<Vec<_>>();
        while let Some(i) = pending.pop() {
            if live[i] {
                continue;
            }
            live[i] = true;
            if let Node::And(a, b) = self.nodes[i] {
                pending.push((a >> 1) as usize);
                pending.push((b >> 1) as usize);
            }
        }
        let mut count = 0;
        let support = self
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(i, node)| {
                if !matches!(node, Node::Input) {
                    return None;
                }
                Some(if live[i] {
                    let ordinal = count;
                    count += 1;
                    Some(ordinal)
                } else {
                    None
                })
            })
            .collect();
        (support, count)
    }

    /// Enumerate a 64-aligned batch over dense live input ordinals. Higher unused lanes
    /// in a short first batch must be masked by the caller.
    pub(super) fn eval_assignment_batch(&self, support: &[Option<usize>], base: usize) -> Vec<u64> {
        self.eval_words(|ordinal| {
            let Some(bit) = support[ordinal as usize] else {
                return 0;
            };
            const LOW_BITS: [u64; 6] = [
                0xaaaa_aaaa_aaaa_aaaa,
                0xcccc_cccc_cccc_cccc,
                0xf0f0_f0f0_f0f0_f0f0,
                0xff00_ff00_ff00_ff00,
                0xffff_0000_ffff_0000,
                0xffff_ffff_0000_0000,
            ];
            if bit < LOW_BITS.len() {
                LOW_BITS[bit]
            } else if (base >> bit) & 1 == 1 {
                u64::MAX
            } else {
                0
            }
        })
    }

    /// The value of every node for 64 input assignments at once: bit `j` of input `k`'s word
    /// is its value in assignment `j`.
    pub fn eval_words(&self, input: impl Fn(u32) -> u64) -> Vec<u64> {
        let mut vals: Vec<u64> = Vec::with_capacity(self.nodes.len());
        let mut k = 0;
        for n in &self.nodes {
            let v = match *n {
                Node::Const => 0,
                Node::Input => {
                    k += 1;
                    input(k - 1)
                }
                Node::And(a, b) => {
                    let get = |l: L| {
                        let x = vals[(l >> 1) as usize];
                        if l & 1 == 1 { !x } else { x }
                    };
                    get(a) & get(b)
                }
            };
            vals.push(v);
        }
        vals
    }

    /// A literal's word in `eval_words`'s result.
    pub fn word(vals: &[u64], l: L) -> u64 {
        let x = vals[(l >> 1) as usize];
        if l & 1 == 1 { !x } else { x }
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

    /// Necessary equalities exposed by asserting literals: true conjunctions are expanded,
    /// including the zero bits of an OR target; a fixed XOR relates its two operands.
    pub(super) fn asserted_aliases(&self, asserted: &[L]) -> Vec<(L, L)> {
        let mut stack = asserted.to_vec();
        let mut seen = IdMap::default();
        let mut aliases = Vec::new();
        while let Some(l) = stack.pop() {
            if seen.len() >= 4096 {
                break;
            }
            if l <= TRUE || seen.insert(l, ()).is_some() {
                continue;
            }
            if let Some((a, b)) = self.xor_children(l) {
                aliases.push((a, b ^ 1));
            } else if l & 1 == 0
                && let Node::And(a, b) = self.nodes[(l >> 1) as usize]
            {
                stack.extend([b, a]);
            }
        }
        aliases
    }
}

/// The clauses of an AIG's goals for a SAT solver: a variable per node the clauses need
/// (inputs keep theirs for reading models back).
///
/// Gates are recognized before encoding (Tseitin's, with gate detection; see Eén, Mishchenko
/// and Sörensson, "Applying Logic Synthesis for Speeding Up SAT", 2007): an exclusive or or a
/// multiplexer (three and-gates, the inner two used nowhere else) is one variable and four
/// clauses, not three variables and nine; a majority's four private inner gates become one
/// variable and six clauses; and a tree of and-gates, the inner ones used nowhere else, is
/// one variable and a clause per input plus one. Optional three-input parity encoding inlines
/// a private intermediate XOR into one variable and eight four-literal clauses. Encoding
/// size and propagation behavior are measured separately: fewer variables alone need not
/// make a search cheaper.
#[derive(Debug)]
pub struct Cnf {
    /// AIG node → solver variable (`NONE` for a node without one).
    var: Vec<u32>,
    /// The clauses, as given to the solver, when kept (for a certificate).
    pub clauses: Vec<Vec<Lit>>,
    keep: bool,
    emitted: usize,
}

const NONE: u32 = u32::MAX;

/// How a node that has a variable is encoded.
enum Gate {
    /// `x ⊕ y`.
    Xor(L, L),
    /// Three-input parity, with a private intermediate XOR inlined.
    Xor3(L, L, L),
    /// `¬(c ? t : e)`.
    NotMux(L, L, L),
    /// The complement of a majority: `¬((x ∧ y) ∨ (x ∧ z) ∨ (y ∧ z))`.
    NotMaj(L, L, L),
    /// The conjunction of `leaves[start..end]`.
    And(usize, usize),
}

impl Cnf {
    /// Clauses for every gate `roots` reach, added to `solver` (and kept in
    /// [`clauses`](Self::clauses) when `keep`).
    pub fn encode(aig: &Aig, roots: &[L], solver: &mut Solver, keep: bool) -> Cnf {
        Self::encode_with_xor3(aig, roots, solver, keep, false)
    }

    pub(super) fn encode_with_xor3(
        aig: &Aig,
        roots: &[L],
        solver: &mut Solver,
        keep: bool,
        xor3: bool,
    ) -> Cnf {
        let n = aig.nodes.len();
        // Uses of each node within the cone (a root counts as a use, so it keeps its
        // variable): nodes come after their operands, so one pass down from the top counts them.
        let mut uses = vec![0u32; n];
        for &r in roots {
            uses[(r >> 1) as usize] += 2;
        }
        for i in (1..n).rev() {
            if uses[i] > 0
                && let Node::And(a, b) = aig.nodes[i]
            {
                uses[(a >> 1) as usize] += 1;
                uses[(b >> 1) as usize] += 1;
            }
        }
        let private_inner = |l: L| -> Option<(L, L)> {
            match aig.nodes[(l >> 1) as usize] {
                Node::And(a, b) if uses[(l >> 1) as usize] == 1 => Some((a, b)),
                _ => None,
            }
        };
        // A logical XOR, mux or majority can bypass its AND internals even when
        // another logical gate shares them. Explicit roots and operands of other
        // selected gates still set `need`, so genuinely observed internals retain
        // their own variables and definitions.
        let inner = |l: L| -> Option<(L, L)> {
            match aig.nodes[(l >> 1) as usize] {
                Node::And(a, b) => Some((a, b)),
                _ => None,
            }
        };
        // `¬P ∧ ¬Q` with P and Q inner gates: an exclusive or or a multiplexer.
        let gate2 = |a: L, b: L| -> Option<Gate> {
            if a & 1 == 0 || b & 1 == 0 {
                return None;
            }
            let ((p0, p1), (q0, q1)) = (inner(a)?, inner(b)?);
            if (q0 == p0 ^ 1 && q1 == p1 ^ 1) || (q0 == p1 ^ 1 && q1 == p0 ^ 1) {
                // P ∨ Q = (p0 ↔ p1).
                return Some(Gate::Xor(p0, p1));
            }
            for (c, t) in [(p0, p1), (p1, p0)] {
                for (d, e) in [(q0, q1), (q1, q0)] {
                    if d == c ^ 1 {
                        return Some(Gate::NotMux(c, t, e));
                    }
                }
            }
            None
        };
        let majority = |a: L, b: L| -> Option<Gate> {
            // A majority's positive AIG node is the complement of three pairwise
            // products. Any independently observed inner gate is encoded too.
            for (tree, pair) in [(a, b), (b, a)] {
                if tree & 1 != 0 || pair & 1 == 0 {
                    continue;
                }
                let Some((p, q)) = inner(tree) else { continue };
                if p & 1 == 0 || q & 1 == 0 {
                    continue;
                }
                let (Some((p0, p1)), Some((q0, q1)), Some((r0, r1))) =
                    (inner(p), inner(q), inner(pair))
                else {
                    continue;
                };
                for (x, y) in [(p0, p1), (p1, p0)] {
                    let z = if q0 == x {
                        q1
                    } else if q1 == x {
                        q0
                    } else {
                        continue;
                    };
                    if (r0 == y && r1 == z) || (r0 == z && r1 == y) {
                        return Some(Gate::NotMaj(x, y, z));
                    }
                }
            }
            None
        };
        let special = |a, b| gate2(a, b).or_else(|| majority(a, b));
        // Which nodes get a variable, and how each is encoded: from the top down, a node's
        // users are decided before it.
        let mut need = vec![false; n];
        for &r in roots {
            need[(r >> 1) as usize] = true;
        }
        let mut gates: Vec<(u32, Gate)> = Vec::new();
        let mut leaves: Vec<L> = Vec::new();
        let mut stack = Vec::new();
        for i in (1..n).rev() {
            if !need[i] {
                continue;
            }
            let Node::And(a, b) = aig.nodes[i] else {
                continue;
            };
            let detected = special(a, b);
            let detected = match detected {
                Some(Gate::Xor(x, y)) if xor3 && uses[i] > 1 => {
                    let mut triple = None;
                    for (operand, other) in [(x, y), (y, x)] {
                        // The parent XOR's two private products account for both uses of
                        // this intermediate. An observed root or another user prevents it
                        // from being hidden. Single-use outputs keep their binary operands
                        // visible for root-conditioned alias extraction.
                        if uses[(operand >> 1) as usize] == 2
                            && let Node::And(p, q) = aig.nodes[(operand >> 1) as usize]
                            && let Some(Gate::Xor(u, v)) = gate2(p, q)
                        {
                            triple = Some(Gate::Xor3(u, v ^ (operand & 1), other));
                            break;
                        }
                    }
                    triple.or(Some(Gate::Xor(x, y)))
                }
                other => other,
            };
            let gate = detected.unwrap_or_else(|| {
                // The inputs of the tree of and-gates under `i`.
                let start = leaves.len();
                stack.extend([b, a]);
                while let Some(l) = stack.pop() {
                    match private_inner(l) {
                        Some((x, y)) if l & 1 == 0 && special(x, y).is_none() => {
                            stack.extend([y, x]);
                        }
                        _ => leaves.push(l),
                    }
                }
                Gate::And(start, leaves.len())
            });
            let operands: &[L] = match &gate {
                Gate::Xor(x, y) => &[*x, *y],
                Gate::Xor3(x, y, z) => &[*x, *y, *z],
                Gate::NotMux(c, t, e) => &[*c, *t, *e],
                Gate::NotMaj(x, y, z) => &[*x, *y, *z],
                Gate::And(s, e) => &leaves[*s..*e],
            };
            for &l in operands {
                need[(l >> 1) as usize] = true;
            }
            gates.push((i as u32, gate));
        }
        let mut cnf = Cnf {
            var: vec![NONE; n],
            clauses: Vec::new(),
            keep,
            emitted: 0,
        };
        for (i, _) in need.iter().enumerate().filter(|(_, n)| **n) {
            cnf.var[i] = solver.new_var();
        }
        if need[0] {
            let f = cnf.lit(FALSE);
            cnf.push(solver, &[!f]);
        }
        let mut long = Vec::new();
        for (i, gate) in gates.into_iter().rev() {
            let g = Lit::pos(cnf.var[i as usize]);
            match gate {
                Gate::Xor(x, y) => {
                    let (x, y) = (cnf.lit(x), cnf.lit(y));
                    cnf.push(solver, &[!g, x, y]);
                    cnf.push(solver, &[!g, !x, !y]);
                    cnf.push(solver, &[g, !x, y]);
                    cnf.push(solver, &[g, x, !y]);
                }
                Gate::Xor3(x, y, z) => {
                    let (x, y, z) = (cnf.lit(x), cnf.lit(y), cnf.lit(z));
                    for assignment in 0..8u32 {
                        let clause = [
                            if assignment.count_ones() & 1 == 1 {
                                g
                            } else {
                                !g
                            },
                            if assignment & 1 == 0 { x } else { !x },
                            if assignment & 2 == 0 { y } else { !y },
                            if assignment & 4 == 0 { z } else { !z },
                        ];
                        cnf.emitted += 1;
                        if cnf.keep {
                            cnf.clauses.push(clause.to_vec());
                        }
                        // Initially watch the output and the outer input (an adder's
                        // incoming carry), rather than the two lowest numbered inputs.
                        solver.add_clause_watching(&clause, [clause[0], clause[3]]);
                    }
                }
                Gate::NotMux(c, t, e) => {
                    let (c, t, e) = (cnf.lit(c), cnf.lit(t), cnf.lit(e));
                    // g = ¬(c ? t : e).
                    cnf.push(solver, &[!c, !t, !g]);
                    cnf.push(solver, &[!c, t, g]);
                    cnf.push(solver, &[c, !e, !g]);
                    cnf.push(solver, &[c, e, g]);
                }
                Gate::NotMaj(x, y, z) => {
                    let (x, y, z) = (cnf.lit(x), cnf.lit(y), cnf.lit(z));
                    for (a, b) in [(x, y), (x, z), (y, z)] {
                        cnf.push(solver, &[!a, !b, !g]);
                        cnf.push(solver, &[a, b, g]);
                    }
                }
                Gate::And(s, e) => {
                    long.clear();
                    long.push(g);
                    for &l in &leaves[s..e] {
                        let x = cnf.lit(l);
                        cnf.push(solver, &[!g, x]);
                        long.push(!x);
                    }
                    cnf.push(solver, &long);
                }
            }
        }
        cnf
    }

    /// The number of clauses given to the solver.
    pub fn emitted(&self) -> usize {
        self.emitted
    }

    fn push(&mut self, solver: &mut Solver, c: &[Lit]) {
        self.emitted += 1;
        if self.keep {
            self.clauses.push(c.to_vec());
        }
        solver.add_clause(c);
    }

    /// The solver literal of an AIG literal (its node must have a variable: a root's does).
    pub fn lit(&self, l: L) -> Lit {
        let v = self.var[(l >> 1) as usize];
        debug_assert_ne!(v, NONE, "a node without a variable");
        Lit::new(v, l & 1 == 0)
    }

    pub(super) fn mapped_lit(&self, l: L) -> Option<Lit> {
        let &v = self.var.get((l >> 1) as usize)?;
        (v != NONE).then(|| Lit::new(v, l & 1 == 0))
    }

    /// Asserts an AIG literal (a root's).
    pub fn assert(&mut self, l: L, solver: &mut Solver) {
        let x = self.lit(l);
        self.push(solver, &[x]);
    }

    /// The value of an AIG literal in a model: an input's, or a root's (inputs not reached
    /// are false).
    pub fn value(&self, l: L, model: &[bool]) -> bool {
        let v = match self.var.get((l >> 1) as usize) {
            Some(&v) if v != NONE => model.get(v as usize).copied().unwrap_or(false),
            _ => false,
        };
        v != (l & 1 == 1)
    }
}
