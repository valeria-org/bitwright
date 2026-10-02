//! Certificates of proofs by complete enumeration.
//!
//! A question with a small enough input domain can be decided by evaluating it at every
//! assignment ([`Config::exhaustive_inputs`](super::Config::exhaustive_inputs)). That decision
//! is made on bitwright's word-level evaluator; its certificate is instead the question's
//! bit-blasted circuit, the same circuit a DRUP certificate's clauses encode, and
//! [`Exhaustion::check`] simulates that circuit at every assignment of its inputs. The check
//! shares no code with the decision.
//!
//! The simulation is scheduled so that it can stop early without weakening the check. A goal
//! that is a negated conjunction holds at an assignment as soon as one conjunct is false
//! there; conjuncts are simulated one cone at a time, and a block of assignments stops once
//! each of them has a false conjunct. Node values live in a register file reused by liveness,
//! so the working set is the circuit's width rather than its size.

use super::aig::L;
use super::sample_words::stripes;
use std::sync::atomic::{AtomicU64, Ordering};

/// Assignments simulated together: sixteen 64-bit words per register.
const WORDS: usize = 16;
/// Input bits that vary within one block: `64 * WORDS` lanes.
const LOW_INPUTS: u32 = 10;
/// Blocks claimed by a worker at a time.
const STRIPE: u64 = 1 << 8;

/// A circuit and the claim that its goal holds wherever its constraints do, at every
/// assignment of its inputs.
///
/// Fields are private: an exhaustion certificate comes from the prover
/// ([`Certificate::exhaustion`](super::Certificate::exhaustion)), and checking it costs up to
/// `2^inputs` circuit evaluations, 1024 at a time and in parallel across threads.
#[derive(Clone, Debug)]
pub struct Exhaustion {
    inputs: u32,
    gates: Vec<(L, L)>,
    goal: L,
    constraints: Vec<L>,
}

/// One register-machine instruction: `dst = (a ^ flip_a) & (b ^ flip_b)`, with the operand
/// registers in the high bits and the flips in the low bit.
#[derive(Clone, Copy)]
struct Gate {
    dst: u32,
    a: u32,
    b: u32,
}

/// The schedule: segments of gates, each ending in a conjunct whose falsity decides the goal.
struct Schedule {
    registers: usize,
    /// Each segment's gates, and the literal (as a register operand) it ends with.
    segments: Vec<(Vec<Gate>, u32)>,
    /// Gates of the constraints' cones not already scheduled, and their literals.
    constraints: (Vec<Gate>, Vec<u32>),
    /// The goal itself when it is not a negated conjunction.
    goal: Option<u32>,
}

impl Exhaustion {
    /// The cone of `goal` and `constraints` in `g`.
    pub(super) fn of(g: &super::aig::Aig, goal: L, constraints: &[L]) -> Exhaustion {
        let mut roots = vec![goal];
        roots.extend_from_slice(constraints);
        let (inputs, gates, roots) = g.cone(&roots);
        Exhaustion {
            inputs,
            gates,
            goal: roots[0],
            constraints: roots[1..].to_vec(),
        }
    }

    /// The circuit's inputs: checking evaluates it at up to `2^inputs` assignments.
    pub fn inputs(&self) -> u32 {
        self.inputs
    }

    /// The circuit's and-gates.
    pub fn gates(&self) -> usize {
        self.gates.len()
    }

    fn gate(&self, node: u32) -> Option<(L, L)> {
        node.checked_sub(self.inputs + 1)
            .map(|i| self.gates[i as usize])
    }

    /// The conjuncts of the goal when it is a negated conjunction: the leaves of the and-tree
    /// below it through uncomplemented edges.
    fn conjuncts(&self) -> Option<Vec<L>> {
        if self.goal & 1 == 0 || self.gate(self.goal >> 1).is_none() {
            return None;
        }
        let mut leaves = Vec::new();
        let mut stack = vec![self.goal ^ 1];
        let mut seen = std::collections::HashSet::new();
        while let Some(l) = stack.pop() {
            if !seen.insert(l) {
                continue;
            }
            match self.gate(l >> 1) {
                Some((a, b)) if l & 1 == 0 => {
                    stack.push(a);
                    stack.push(b);
                }
                _ => leaves.push(l),
            }
        }
        Some(leaves)
    }

    fn schedule(&self) -> Schedule {
        let nodes = (1 + self.inputs as usize) + self.gates.len();
        let mut scheduled = vec![false; nodes];
        // Inputs and the constant are always present.
        for s in scheduled.iter_mut().take(1 + self.inputs as usize) {
            *s = true;
        }
        // The nodes a literal needs that are not scheduled yet, in topological order.
        let missing = |scheduled: &[bool], roots: &[L]| -> Vec<u32> {
            let mut mark = vec![false; nodes];
            let mut stack: Vec<u32> = roots.iter().map(|&l| l >> 1).collect();
            while let Some(n) = stack.pop() {
                if scheduled[n as usize] || core::mem::replace(&mut mark[n as usize], true) {
                    continue;
                }
                if let Some((a, b)) = self.gate(n) {
                    stack.push(a >> 1);
                    stack.push(b >> 1);
                }
            }
            (0..nodes as u32).filter(|&n| mark[n as usize]).collect()
        };
        let mut order: Vec<(Vec<u32>, L)> = Vec::new();
        let goal = match self.conjuncts() {
            Some(mut pending) => {
                // Greedily the conjunct that needs the fewest new gates.
                while !pending.is_empty() {
                    let (best, nodes) = pending
                        .iter()
                        .enumerate()
                        .map(|(i, &l)| (i, missing(&scheduled, &[l])))
                        .min_by_key(|(_, n)| n.len())
                        .unwrap();
                    let l = pending.swap_remove(best);
                    for &n in &nodes {
                        scheduled[n as usize] = true;
                    }
                    order.push((nodes, l));
                }
                None
            }
            None => {
                let nodes = missing(&scheduled, &[self.goal]);
                for &n in &nodes {
                    scheduled[n as usize] = true;
                }
                order.push((nodes, self.goal));
                Some(())
            }
        };
        let constraint_nodes = missing(&scheduled, &self.constraints);

        // Liveness: the last position at which each node is read. Segment ends read their
        // literal; constraints are read after everything.
        let mut position = 0usize;
        let mut last = vec![0usize; nodes];
        let reads = |n: u32, at: usize, last: &mut [usize]| {
            last[n as usize] = last[n as usize].max(at);
        };
        for (gates, l) in &order {
            for &n in gates {
                let (a, b) = self.gate(n).unwrap();
                reads(a >> 1, position, &mut last);
                reads(b >> 1, position, &mut last);
                position += 1;
            }
            reads(l >> 1, position, &mut last);
            position += 1;
        }
        for &n in &constraint_nodes {
            let (a, b) = self.gate(n).unwrap();
            reads(a >> 1, position, &mut last);
            reads(b >> 1, position, &mut last);
            position += 1;
        }
        let end = position;
        for &c in &self.constraints {
            reads(c >> 1, end, &mut last);
        }
        if goal.is_some() {
            reads(self.goal >> 1, end, &mut last);
        }

        // Registers: the constant and inputs are fixed; gates take the lowest free register.
        let mut register = vec![u32::MAX; nodes];
        for (n, r) in register
            .iter_mut()
            .enumerate()
            .take(1 + self.inputs as usize)
        {
            *r = n as u32;
        }
        let mut free: std::collections::BinaryHeap<core::cmp::Reverse<u32>> = Default::default();
        let mut registers = 1 + self.inputs;
        let mut dying: Vec<Vec<u32>> = vec![Vec::new(); end + 1];
        let operand = |register: &[u32], l: L| (register[(l >> 1) as usize] << 1) | (l & 1);
        let mut position = 0usize;
        let mut assign = |n: u32,
                          position: usize,
                          register: &mut Vec<u32>,
                          free: &mut std::collections::BinaryHeap<core::cmp::Reverse<u32>>,
                          dying: &mut Vec<Vec<u32>>|
         -> Gate {
            let (a, b) = self.gate(n).unwrap();
            let (a, b) = (operand(register, a), operand(register, b));
            // Operands dying here free their registers before the result takes one.
            for r in core::mem::take(&mut dying[position]) {
                free.push(core::cmp::Reverse(r));
            }
            let dst = free
                .pop()
                .map(|core::cmp::Reverse(r)| r)
                .unwrap_or_else(|| {
                    registers += 1;
                    registers - 1
                });
            register[n as usize] = dst;
            // A result read later dies after its last read; one never read dies at once.
            let at = last[n as usize].max(position + 1);
            dying[at.min(end)].push(dst);
            Gate { dst, a, b }
        };
        let mut segments = Vec::new();
        for (gates, l) in &order {
            let mut code = Vec::with_capacity(gates.len());
            for &n in gates {
                code.push(assign(n, position, &mut register, &mut free, &mut dying));
                position += 1;
            }
            let lit = operand(&register, *l);
            for r in core::mem::take(&mut dying[position]) {
                free.push(core::cmp::Reverse(r));
            }
            position += 1;
            segments.push((code, lit));
        }
        let mut code = Vec::with_capacity(constraint_nodes.len());
        for &n in &constraint_nodes {
            code.push(assign(n, position, &mut register, &mut free, &mut dying));
            position += 1;
        }
        let constraints = self
            .constraints
            .iter()
            .map(|&c| operand(&register, c))
            .collect();
        let goal = goal.map(|()| operand(&register, self.goal));
        // Inputs and the constant are never freed: they are not gates.
        let registers = registers as usize;
        if goal.is_some() {
            Schedule {
                registers,
                segments: Vec::new(),
                constraints: (
                    segments
                        .into_iter()
                        .flat_map(|(code, _)| code)
                        .chain(code)
                        .collect(),
                    constraints,
                ),
                goal,
            }
        } else {
            Schedule {
                registers,
                segments,
                constraints: (code, constraints),
                goal,
            }
        }
    }

    /// Simulates the circuit at every assignment of its inputs. Fails, naming an assignment,
    /// if the constraints hold and the goal does not at any of them.
    pub fn check(&self) -> Result<(), String> {
        if self.inputs > 63 {
            return Err(format!(
                "an exhaustion certificate over {} inputs cannot be enumerated",
                self.inputs
            ));
        }
        for &(a, b) in &self.gates {
            let limit = (1 + self.inputs as usize + self.gates.len()) as u32;
            if a >> 1 >= limit || b >> 1 >= limit {
                return Err("an exhaustion certificate gate reads a missing node".into());
            }
        }
        for (i, &(a, b)) in self.gates.iter().enumerate() {
            let node = self.inputs + 1 + i as u32;
            if a >> 1 >= node || b >> 1 >= node {
                return Err("an exhaustion certificate is not in topological order".into());
            }
        }
        let schedule = self.schedule();
        let low = self.inputs.min(LOW_INPUTS);
        let blocks = 1u64 << (self.inputs - low);
        // Lane j of a block is the assignment whose low input bits are j.
        let valid = lanes_mask(1usize << low);
        let failure = AtomicU64::new(u64::MAX);
        stripes(blocks, STRIPE, |start, end| {
            if failure.load(Ordering::Relaxed) != u64::MAX {
                return;
            }
            let mut regs = vec![[0u64; WORDS]; schedule.registers];
            for k in 0..low {
                regs[1 + k as usize] = low_pattern(k);
            }
            for block in start..end {
                for k in low..self.inputs {
                    let bit = (block >> (k - low)) & 1;
                    regs[1 + k as usize] = [0u64.wrapping_sub(bit); WORDS];
                }
                if let Some(bad) = schedule.evaluate(&mut regs, valid) {
                    let lane = first_lane(&bad) as u64;
                    failure.fetch_min((block << low) | lane, Ordering::Relaxed);
                    return;
                }
            }
        });
        match failure.into_inner() {
            u64::MAX => Ok(()),
            index => Err(format!(
                "the goal fails at input assignment {index:#x} of the exhaustion certificate"
            )),
        }
    }
}

impl Schedule {
    /// Simulates one block whose inputs are in `regs`: the lanes, if any, where the
    /// constraints hold and the goal does not.
    fn evaluate(&self, regs: &mut [[u64; WORDS]], valid: [u64; WORDS]) -> Option<[u64; WORDS]> {
        // Lanes at which the goal is already known to hold.
        let mut decided = [0u64; WORDS];
        for (code, conjunct) in &self.segments {
            run(regs, code);
            let c = read(regs, *conjunct);
            let mut every = true;
            for w in 0..WORDS {
                decided[w] |= !c[w];
                every &= decided[w] & valid[w] == valid[w];
            }
            if every {
                return None;
            }
        }
        run(regs, &self.constraints.0);
        if let Some(goal) = self.goal {
            let g = read(regs, goal);
            for w in 0..WORDS {
                decided[w] |= g[w];
            }
        }
        let mut bad: [u64; WORDS] = core::array::from_fn(|w| valid[w] & !decided[w]);
        for &c in &self.constraints.1 {
            let c = read(regs, c);
            for w in 0..WORDS {
                bad[w] &= c[w];
            }
        }
        bad.iter().any(|&w| w != 0).then_some(bad)
    }
}

/// The first `lanes` lanes of a block.
fn lanes_mask(lanes: usize) -> [u64; WORDS] {
    core::array::from_fn(|w| match lanes.saturating_sub(64 * w) {
        0 => 0,
        n if n >= 64 => u64::MAX,
        n => (1u64 << n) - 1,
    })
}

fn first_lane(mask: &[u64; WORDS]) -> usize {
    let w = mask.iter().position(|&w| w != 0).unwrap();
    64 * w + mask[w].trailing_zeros() as usize
}

#[inline(always)]
fn run(regs: &mut [[u64; WORDS]], code: &[Gate]) {
    for g in code {
        let (x, y) = (&regs[(g.a >> 1) as usize], &regs[(g.b >> 1) as usize]);
        // One operation per word for every operand polarity, instead of flipping each.
        let r: [u64; WORDS] = match (g.a & 1, g.b & 1) {
            (0, 0) => core::array::from_fn(|w| x[w] & y[w]),
            (1, 0) => core::array::from_fn(|w| !x[w] & y[w]),
            (0, _) => core::array::from_fn(|w| x[w] & !y[w]),
            _ => core::array::from_fn(|w| !(x[w] | y[w])),
        };
        regs[g.dst as usize] = r;
    }
}

/// Input `k`'s words when lane `j` (of `64 * WORDS`) takes the value `j` on the low input bits.
fn low_pattern(k: u32) -> [u64; WORDS] {
    const LOW: [u64; 6] = [
        0xaaaa_aaaa_aaaa_aaaa,
        0xcccc_cccc_cccc_cccc,
        0xf0f0_f0f0_f0f0_f0f0,
        0xff00_ff00_ff00_ff00,
        0xffff_0000_ffff_0000,
        0xffff_ffff_0000_0000,
    ];
    core::array::from_fn(|w| match k {
        0..6 => LOW[k as usize],
        _ => 0u64.wrapping_sub(((w as u64) >> (k - 6)) & 1),
    })
}

#[inline(always)]
fn read(regs: &[[u64; WORDS]], operand: u32) -> [u64; WORDS] {
    let x = regs[(operand >> 1) as usize];
    let flip = 0u64.wrapping_sub(u64::from(operand & 1));
    core::array::from_fn(|w| x[w] ^ flip)
}

#[cfg(test)]
mod tests;
