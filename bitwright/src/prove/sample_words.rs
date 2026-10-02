//! Search on bounded, machine-word integer DAGs. Complete ordered input enumeration can
//! prove a predicate; unsupported graphs and partial samples retain the bit-blast/SAT path.

use super::{Config, Model, SampleMode, sample, small_sample};
use crate::{
    Assumptions, BinOp, BitVec, CmpOp, Context, SymbolKey, UnOp, Width, expr::OpCode, hash::IdMap,
};

const MAX_NODES: usize = 4096;

mod exhaust;
pub(super) use exhaust::stripes;

pub(super) struct Trial {
    pub samples: u64,
    pub model: Option<Model>,
    pub complete: bool,
}

enum Op {
    Constant(u64),
    Symbol(usize),
    Unary(UnOp, usize),
    Binary(BinOp, usize, usize),
    Compare(CmpOp, usize, usize, u16),
    Zext(usize),
    Sext(usize, u16),
    Extract(usize, u16),
    Concat(usize, usize, u16),
    Select(usize, usize, usize),
}

struct Instruction {
    op: Op,
    width: u16,
    mask: u64,
}

struct Symbol {
    key: SymbolKey,
    width: Width,
    ones: u64,
    unknown: Vec<(u16, u32)>,
}

struct Program {
    ops: Vec<Instruction>,
    symbols: Vec<Symbol>,
    inputs: u32,
    goal: usize,
    constraints: Vec<usize>,
    word_groups: Vec<Vec<u32>>,
}

fn mask(width: u16) -> u64 {
    u64::MAX >> (64 - width)
}

fn signed(value: u64, width: u16) -> i64 {
    if value >> (width - 1) & 1 != 0 {
        (value | !mask(width)) as i64
    } else {
        value as i64
    }
}

impl Program {
    fn compile(
        cx: &mut Context,
        goal: u32,
        constraints: &[u32],
        assumptions: Option<&Assumptions>,
    ) -> Option<Self> {
        let mut roots = vec![goal];
        roots.extend_from_slice(constraints);
        let remaining = std::cell::Cell::new(MAX_NODES);
        let truncated = std::cell::Cell::new(false);
        let order = cx.post_order_ids_pruned(&roots, |_| {
            if remaining.get() == 0 {
                truncated.set(true);
                true
            } else {
                remaining.set(remaining.get() - 1);
                false
            }
        });
        if truncated.get() {
            return None;
        }
        let mut slots = IdMap::default();
        let mut ops = Vec::with_capacity(order.len());
        let mut symbols = Vec::new();
        let mut inputs = 0;
        for id in order {
            let node = cx.node(id);
            let width = node.width;
            if width > 64 {
                return None;
            }
            let op = match node.op {
                OpCode::Const => Op::Constant(cx.const_val(id)?.to_u64()?),
                OpCode::Sym => {
                    let symbol_id = cx.symbol_id(cx.handle(id)).ok()??;
                    let key = cx.symbol_key(symbol_id)?.clone();
                    let (ones, zeros) = cx.declared_at(id).map_or((0, 0), |k| {
                        (
                            k.known_one().to_u64().unwrap(),
                            k.known_zero().to_u64().unwrap(),
                        )
                    });
                    let mut unknown = Vec::new();
                    for bit in 0..width {
                        if (ones | zeros) >> bit & 1 == 0 {
                            unknown.push((bit, inputs));
                            inputs += 1;
                        }
                    }
                    let slot = symbols.len();
                    symbols.push(Symbol {
                        key,
                        width: cx.width_of(id),
                        ones,
                        unknown,
                    });
                    Op::Symbol(slot)
                }
                OpCode::Zext => Op::Zext(slots[&node.a]),
                OpCode::Sext => Op::Sext(slots[&node.a], cx.wid(node.a)),
                OpCode::Extract => Op::Extract(slots[&node.a], node.b as u16),
                OpCode::Concat => Op::Concat(slots[&node.a], slots[&node.b], cx.wid(node.b)),
                OpCode::Select => Op::Select(slots[&node.a], slots[&node.b], slots[&node.c]),
                other => {
                    if let Some(op) = other.as_un() {
                        Op::Unary(op, slots[&node.a])
                    } else if let Some(op) = other.as_bin() {
                        Op::Binary(op, slots[&node.a], slots[&node.b])
                    } else {
                        Op::Compare(
                            other.as_cmp()?,
                            slots[&node.a],
                            slots[&node.b],
                            cx.wid(node.a),
                        )
                    }
                }
            };
            slots.insert(id, ops.len());
            ops.push(Instruction {
                op,
                width,
                mask: mask(width),
            });
        }
        let mut program = Self {
            ops,
            symbols,
            inputs,
            goal: slots[&goal],
            constraints: constraints.iter().map(|id| slots[id]).collect(),
            word_groups: Vec::new(),
        };
        if let Some(assumptions) = assumptions {
            program.fix_scoped_bits(assumptions, &slots)?;
        }
        Some(program)
    }

    // Use only exact original seed masks through pure wiring. In particular, do not read
    // an assumption overlay cached under older declarations or spend additional fact work.
    // All original constraints still filter assignments and participate in model replay.
    fn fix_scoped_bits(
        &mut self,
        assumptions: &Assumptions,
        slots: &IdMap<u32, usize>,
    ) -> Option<()> {
        if assumptions.len() > MAX_NODES {
            return None;
        }
        let mut pending = Vec::new();
        for (_, expression, facts) in assumptions.constraints() {
            let known = facts.known();
            if known.width().bits() <= 64
                && !known.known().is_zero()
                && let Some(&slot) = slots.get(&expression.index())
            {
                pending.push((slot, known.known().to_u64()?, known.known_one().to_u64()?));
            }
        }
        let mut fixed = vec![(0u64, 0u64); self.symbols.len()];
        let mut seen = IdMap::<usize, (u64, u64)>::default();
        let mut remaining = MAX_NODES;
        while let Some((slot, mut known, mut ones)) = pending.pop() {
            if remaining == 0 {
                return None;
            }
            remaining -= 1;
            known &= self.ops[slot].mask;
            ones &= known;
            if known == 0 {
                continue;
            }
            let entry = seen.entry(slot).or_default();
            if (entry.0 & known & (entry.1 ^ ones)) != 0 {
                return None;
            }
            let added = known & !entry.0;
            entry.0 |= known;
            entry.1 |= ones;
            known = added;
            ones &= added;
            if known == 0 {
                continue;
            }
            match self.ops[slot].op {
                Op::Constant(value) => {
                    if value & known != ones {
                        return None;
                    }
                }
                Op::Symbol(symbol) => {
                    fixed[symbol].0 |= known;
                    fixed[symbol].1 |= ones;
                }
                Op::Zext(child) => {
                    if ones & !self.ops[child].mask != 0 {
                        return None;
                    }
                    pending.push((child, known, ones));
                }
                Op::Sext(child, width) => {
                    let upper = known & !self.ops[child].mask;
                    let mut low_known = known & self.ops[child].mask;
                    let mut low_ones = ones & low_known;
                    if upper != 0 {
                        let sign = 1u64 << (width - 1);
                        let sign_one = if ones & upper == 0 {
                            false
                        } else if ones & upper == upper {
                            true
                        } else {
                            return None;
                        };
                        if low_known & sign != 0 && (low_ones & sign != 0) != sign_one {
                            return None;
                        }
                        low_known |= sign;
                        if sign_one {
                            low_ones |= sign;
                        }
                    }
                    pending.push((child, low_known, low_ones));
                }
                Op::Extract(child, lo) => pending.push((child, known << lo, ones << lo)),
                Op::Concat(high, low, bits) => {
                    pending.push((low, known & self.ops[low].mask, ones & self.ops[low].mask));
                    pending.push((high, known >> bits, ones >> bits));
                }
                Op::Unary(UnOp::Not, child) => pending.push((child, known, known ^ ones)),
                // Other operations can lose the source-bit relationship. Ignoring their
                // known bits overapproximates legal inputs, never omits one.
                _ => {}
            }
        }
        let mut inputs = 0;
        for (symbol, &(known, ones)) in self.symbols.iter_mut().zip(&fixed) {
            let unknown = symbol
                .unknown
                .iter()
                .fold(0u64, |m, &(bit, _)| m | (1u64 << bit));
            let global = mask(symbol.width.bits()) & !unknown;
            if global & known & (symbol.ones ^ ones) != 0 {
                return None;
            }
            symbol.ones |= ones;
            symbol.unknown.retain(|&(bit, _)| known >> bit & 1 == 0);
            for (_, coordinate) in &mut symbol.unknown {
                *coordinate = inputs;
                inputs += 1;
            }
        }
        self.inputs = inputs;
        Some(())
    }

    fn symbol_value(symbol: &Symbol, inputs: &[u64], lane: u32) -> u64 {
        symbol
            .unknown
            .iter()
            .fold(symbol.ones, |value, &(bit, input)| {
                value | (((inputs[input as usize] >> lane) & 1) << bit)
            })
    }

    // Reorder sampling coordinates, never symbols or expression values. A wire identifies
    // one original unknown bit. Repeated/overlapping words share that same coordinate.
    fn prioritize_words(&mut self) {
        let mut wires: Vec<Option<Vec<Option<u32>>>> = Vec::with_capacity(self.ops.len());
        let mut groups = Vec::new();
        for (slot, instruction) in self.ops.iter().enumerate() {
            let word = match instruction.op {
                Op::Constant(_) => Some(vec![None; usize::from(instruction.width)]),
                Op::Symbol(symbol) => {
                    let mut bits = vec![None; usize::from(instruction.width)];
                    for &(bit, input) in &self.symbols[symbol].unknown {
                        bits[usize::from(bit)] = Some(input);
                    }
                    let inputs: Vec<_> = bits.iter().flatten().copied().collect();
                    if !inputs.is_empty() {
                        groups.push((instruction.width, 1, slot, inputs));
                    }
                    Some(bits)
                }
                Op::Zext(a) | Op::Sext(a, _) => wires[a].as_ref().map(|bits| {
                    let mut word = bits.clone();
                    let fill = if matches!(instruction.op, Op::Sext(..)) {
                        bits.last().copied().flatten()
                    } else {
                        None
                    };
                    word.resize(usize::from(instruction.width), fill);
                    word
                }),
                Op::Extract(a, lo) => wires[a].as_ref().map(|bits| {
                    bits[usize::from(lo)..usize::from(lo + instruction.width)].to_vec()
                }),
                Op::Concat(a, b, _) => match (&wires[a], &wires[b]) {
                    (Some(high), Some(low)) => {
                        let mut bits = low.clone();
                        bits.extend_from_slice(high);
                        let inputs: Vec<_> = bits.iter().flatten().copied().collect();
                        if !inputs.is_empty() {
                            groups.push((instruction.width, 0, slot, inputs));
                        }
                        Some(bits)
                    }
                    _ => None,
                },
                _ => None,
            };
            wires.push(word);
        }
        // Prefer maximal words, including standalone symbols. At equal width a reconstructed
        // word precedes its backing symbol; traversal order breaks remaining ties. Smaller
        // overlapping words add only coordinates that the larger word did not contain.
        groups.sort_unstable_by_key(|(width, kind, slot, _)| {
            (core::cmp::Reverse(*width), *kind, *slot)
        });
        let mut seen = vec![false; self.inputs as usize];
        let mut order = Vec::with_capacity(self.inputs as usize);
        for (_, _, _, group) in groups {
            let adds_inputs = group.iter().any(|&input| !seen[input as usize]);
            if adds_inputs {
                let mut unique = Vec::new();
                for &input in &group {
                    if !unique.contains(&input) {
                        unique.push(input);
                    }
                }
                self.word_groups.push(unique);
            }
            for input in group {
                if !seen[input as usize] {
                    seen[input as usize] = true;
                    order.push(input);
                }
            }
        }
        for (input, found) in seen.iter().enumerate() {
            if !found {
                order.push(input as u32);
            }
        }
        let mut rank = vec![0; self.inputs as usize];
        for (index, input) in order.into_iter().enumerate() {
            rank[input as usize] = index as u32;
        }
        for symbol in &mut self.symbols {
            for (_, input) in &mut symbol.unknown {
                *input = rank[*input as usize];
            }
        }
        for group in &mut self.word_groups {
            for input in group {
                *input = rank[*input as usize];
            }
        }
    }

    fn streams(&self) -> Vec<Vec<Option<u32>>> {
        let global: Vec<_> = (0..self.inputs).map(|i| (i < 32).then_some(i)).collect();
        let mut streams = vec![global];
        if self.word_groups.len() < 2 {
            return streams;
        }
        // At most eight word probes plus the original joint stream and a diagonal stream.
        // A fixed overall sample allowance is shared between them, not multiplied by them.
        for group in self.word_groups.iter().take(8) {
            let mut mapping = vec![None; self.inputs as usize];
            for (bit, &input) in group.iter().enumerate() {
                if bit < 32 {
                    mapping[input as usize] = Some(bit as u32);
                }
            }
            if !streams.contains(&mapping) {
                streams.push(mapping);
            }
        }
        let mut diagonal = vec![None; self.inputs as usize];
        let mut assigned = vec![false; self.inputs as usize];
        for group in &self.word_groups {
            for (bit, &input) in group.iter().enumerate() {
                if !assigned[input as usize] {
                    assigned[input as usize] = true;
                    if bit < 32 {
                        diagonal[input as usize] = Some(bit as u32);
                    }
                }
            }
        }
        if !streams.contains(&diagonal) {
            streams.push(diagonal);
        }
        streams
    }

    fn evaluate(&self, inputs: &[u64], lane: u32, values: &mut [u64]) {
        for (i, instruction) in self.ops.iter().enumerate() {
            let width = instruction.width;
            values[i] = match instruction.op {
                Op::Constant(value) => value,
                Op::Symbol(slot) => Self::symbol_value(&self.symbols[slot], inputs, lane),
                Op::Unary(op, a) => {
                    let a = values[a];
                    match op {
                        UnOp::Not => !a,
                        UnOp::Neg => a.wrapping_neg(),
                        UnOp::Popcnt => u64::from(a.count_ones()),
                        UnOp::Clz => u64::from(a.leading_zeros() - (64 - u32::from(width))),
                        UnOp::Ctz => u64::from(a.trailing_zeros().min(u32::from(width))),
                        UnOp::Bswap => a.swap_bytes() >> (64 - width),
                        UnOp::BitRev => a.reverse_bits() >> (64 - width),
                    }
                }
                Op::Binary(op, a, b) => binary(op, values[a], values[b], width),
                Op::Compare(op, a, b, w) => u64::from(match op {
                    CmpOp::Eq => values[a] == values[b],
                    CmpOp::Ne => values[a] != values[b],
                    CmpOp::Ult => values[a] < values[b],
                    CmpOp::Ule => values[a] <= values[b],
                    CmpOp::Slt => signed(values[a], w) < signed(values[b], w),
                    CmpOp::Sle => signed(values[a], w) <= signed(values[b], w),
                }),
                Op::Zext(a) => values[a],
                Op::Sext(a, w) => signed(values[a], w) as u64,
                Op::Extract(a, lo) => values[a] >> lo,
                Op::Concat(a, b, low) => (values[a] << low) | values[b],
                Op::Select(c, t, e) => values[if values[c] != 0 { t } else { e }],
            } & instruction.mask;
        }
    }
}

fn binary(op: BinOp, a: u64, b: u64, w: u16) -> u64 {
    match op {
        BinOp::Add => a.wrapping_add(b),
        BinOp::Sub => a.wrapping_sub(b),
        BinOp::Mul => a.wrapping_mul(b),
        BinOp::UMulHi => ((u128::from(a) * u128::from(b)) >> w) as u64,
        BinOp::SMulHi => ((i128::from(signed(a, w)) * i128::from(signed(b, w))) >> w) as u64,
        BinOp::UDiv => a.checked_div(b).unwrap_or(u64::MAX),
        BinOp::URem => a.checked_rem(b).unwrap_or(a),
        BinOp::SDiv => {
            if b == 0 {
                if signed(a, w) < 0 { 1 } else { u64::MAX }
            } else {
                signed(a, w).wrapping_div(signed(b, w)) as u64
            }
        }
        BinOp::SRem => {
            if b == 0 {
                a
            } else {
                signed(a, w).wrapping_rem(signed(b, w)) as u64
            }
        }
        BinOp::And => a & b,
        BinOp::Or => a | b,
        BinOp::Xor => a ^ b,
        BinOp::Shl => {
            if b >= u64::from(w) {
                0
            } else {
                a << b
            }
        }
        BinOp::LShr => {
            if b >= u64::from(w) {
                0
            } else {
                a >> b
            }
        }
        BinOp::AShr => (signed(a, w) >> b.min(u64::from(w - 1))) as u64,
        BinOp::RotL | BinOp::RotR => {
            let n = b % u64::from(w);
            if n == 0 {
                a
            } else if op == BinOp::RotL {
                (a << n) | (a >> (u64::from(w) - n))
            } else {
                (a >> n) | (a << (u64::from(w) - n))
            }
        }
        BinOp::Pdep | BinOp::Pext => {
            let mut m = b;
            let mut out = 0;
            let mut bit = 0;
            while m != 0 {
                let low = m & m.wrapping_neg();
                if op == BinOp::Pdep {
                    if a >> bit & 1 != 0 {
                        out |= low;
                    }
                } else if a & low != 0 {
                    out |= 1 << bit;
                }
                bit += 1;
                m &= m - 1;
            }
            out
        }
    }
}

pub(super) fn try_sample(
    cx: &mut Context,
    goal: u32,
    constraints: &[u32],
    assumptions: Option<&Assumptions>,
    cfg: &Config,
) -> Option<Trial> {
    let mut program = Program::compile(cx, goal, constraints, assumptions)?;
    if cfg.sample_mode == SampleMode::Words {
        program.prioritize_words();
    }
    let mut values = vec![0; program.ops.len()];
    let mut inputs = vec![0; program.inputs as usize];
    let mut count = 0;
    let streams = if cfg.sample_mode == SampleMode::Words {
        program.streams()
    } else {
        Vec::new()
    };
    for batch in 0..cfg.samples.div_ceil(64) {
        for (k, word) in inputs.iter_mut().enumerate() {
            *word = match cfg.sample_mode {
                SampleMode::Random => sample(batch, k as u32),
                SampleMode::Small => small_sample(batch, k as u32),
                SampleMode::Words => {
                    let round = batch / (streams.len() as u32);
                    let mapping = &streams[batch as usize % streams.len()];
                    mapping[k].map_or(0, |bit| small_sample(round, bit))
                }
            };
        }
        let mut bad = 0u64;
        for lane in 0..64 {
            program.evaluate(&inputs, lane, &mut values);
            if values[program.goal] == 0 && program.constraints.iter().all(|&c| values[c] != 0) {
                bad |= 1 << lane;
            }
        }
        count += 64;
        if bad != 0 {
            let lane = bad.trailing_zeros();
            let model = program
                .symbols
                .iter()
                .map(|s| {
                    (
                        s.key.clone(),
                        BitVec::from_u64(s.width, Program::symbol_value(s, &inputs, lane)).unwrap(),
                    )
                })
                .collect();
            return Some(Trial {
                samples: count,
                model: Some(model),
                complete: false,
            });
        }
        // Only the joint ordered stream visits every assignment. Individual and diagonal
        // word streams cannot certify a Cartesian product, even when each word was exhausted.
        // Joint word mappings fix coordinates >= 32 at zero. Conservatively keep both
        // ordered modes on the circuit path when the domain has 32 or more unknown bits.
        let joint_batches = match cfg.sample_mode {
            SampleMode::Small => u64::from(batch) + 1,
            SampleMode::Words if (batch as usize).is_multiple_of(streams.len()) => {
                u64::from(batch / streams.len() as u32) + 1
            }
            _ => 0,
        };
        if program.inputs < 32 && joint_batches * 64 >= (1u64 << program.inputs) {
            return Some(Trial {
                samples: count,
                model: None,
                complete: true,
            });
        }
    }
    Some(Trial {
        samples: count,
        model: None,
        complete: false,
    })
}

/// Decides the goal under the constraints by evaluating every legal assignment, when the word
/// program has at most `limit` unknown input bits. Returns the first failing assignment's model
/// (`None` when the goal holds everywhere) and the number of assignments evaluated.
pub(super) fn try_exhaust(
    cx: &mut Context,
    goal: u32,
    constraints: &[u32],
    assumptions: Option<&Assumptions>,
    limit: u8,
) -> Option<(Option<Model>, u64)> {
    let program = Program::compile(cx, goal, constraints, assumptions)?;
    let (found, evaluated) = program.exhaust(limit)?;
    let model = match found {
        exhaust::Exhausted::Holds => None,
        exhaust::Exhausted::Fails(values) => Some(
            program
                .symbols
                .iter()
                .zip(values)
                .map(|(s, v)| (s.key.clone(), BitVec::from_u64(s.width, v).unwrap()))
                .collect(),
        ),
    };
    Some((model, evaluated))
}

#[cfg(test)]
mod tests;
