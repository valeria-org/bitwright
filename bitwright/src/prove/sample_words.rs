//! Search on bounded, machine-word integer DAGs. Complete ordered input enumeration can
//! prove a predicate; unsupported graphs and partial samples retain the bit-blast/SAT path.

use super::{Config, Model, SampleMode, sample, small_sample};
use crate::{
    Assumptions, BinOp, BitVec, CmpOp, Context, SymbolKey, UnOp, Width, expr::OpCode, hash::IdMap,
};

const MAX_NODES: usize = 4096;
const POST_SIMP_MAX_NODES: usize = 32_768;

#[derive(Clone, Copy)]
enum SlicePiece {
    Zero(u16),
    Slice(u32, u16, u16),
}

fn collect_wide_slice(
    cx: &Context,
    src: u32,
    lo: u32,
    len: u16,
    depth: u8,
    pieces: &mut Vec<SlicePiece>,
) -> bool {
    if len == 0 {
        return true;
    }
    if depth == 0 || pieces.len() >= 16 {
        return false;
    }
    let sn = cx.node(src);
    match sn.op {
        OpCode::Concat => {
            let w_lo = u32::from(cx.wid(sn.b));
            if lo >= w_lo {
                collect_wide_slice(cx, sn.a, lo - w_lo, len, depth - 1, pieces)
            } else if lo + u32::from(len) <= w_lo {
                collect_wide_slice(cx, sn.b, lo, len, depth - 1, pieces)
            } else {
                let len_lo = (w_lo - lo) as u16;
                let len_hi = len - len_lo;
                collect_wide_slice(cx, sn.b, lo, len_lo, depth - 1, pieces)
                    && collect_wide_slice(cx, sn.a, 0, len_hi, depth - 1, pieces)
            }
        }
        OpCode::Extract => collect_wide_slice(cx, sn.a, sn.b + lo, len, depth - 1, pieces),
        OpCode::Zext => {
            let w_in = u32::from(cx.wid(sn.a));
            if lo >= w_in {
                pieces.push(SlicePiece::Zero(len));
                true
            } else if lo + u32::from(len) <= w_in {
                collect_wide_slice(cx, sn.a, lo, len, depth - 1, pieces)
            } else {
                let len_lo = (w_in - lo) as u16;
                let ok = collect_wide_slice(cx, sn.a, lo, len_lo, depth - 1, pieces);
                pieces.push(SlicePiece::Zero(len - len_lo));
                ok
            }
        }
        _ => {
            if sn.width > 64 || lo + u32::from(len) > u32::from(sn.width) {
                return false;
            }
            pieces.push(SlicePiece::Slice(src, lo as u16, len));
            true
        }
    }
}

mod exhaust;
mod guard;
mod weighted;
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
    MixerRound(usize, u64),
    MixerUnround(usize, u64),
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
    free: u64,
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
        Self::compile_with_limit(cx, goal, constraints, assumptions, MAX_NODES)
    }

    fn compile_with_limit(
        cx: &mut Context,
        goal: u32,
        constraints: &[u32],
        assumptions: Option<&Assumptions>,
        limit: usize,
    ) -> Option<Self> {
        let (mut program, slots) = Self::lower(cx, goal, constraints, limit)?;
        if assumptions.is_some() || !program.constraints.is_empty() {
            program.fix_scoped_bits(assumptions, &slots, limit)?;
        }
        // Coordinate streams are used by ordered and bit-sliced sampling, never by
        // guard sampling, which supplies one complete word per symbol.
        for symbol in &mut program.symbols {
            let mut free = symbol.free;
            symbol.unknown.reserve_exact(free.count_ones() as usize);
            while free != 0 {
                symbol
                    .unknown
                    .push((free.trailing_zeros() as u16, program.inputs));
                program.inputs += 1;
                free &= free - 1;
            }
        }
        Some(program)
    }

    fn lower(
        cx: &mut Context,
        goal: u32,
        constraints: &[u32],
        limit: usize,
    ) -> Option<(Self, IdMap<u32, usize>)> {
        let mut visited = 0usize;
        let mut seen: IdMap<u32, ()> = IdMap::default();
        let mut wide_extracts: IdMap<u32, Vec<SlicePiece>> = IdMap::default();
        let mut order: Vec<u32> = Vec::new();
        let mut stack: Vec<(u32, bool)> = Vec::new();
        for &c in constraints.iter().rev() {
            stack.push((c, false));
        }
        stack.push((goal, false));
        while let Some((id, expanded)) = stack.pop() {
            if expanded {
                order.push(id);
                continue;
            }
            if seen.contains_key(&id) {
                continue;
            }
            if visited >= limit {
                return None;
            }
            visited += 1;
            let node = cx.node(id);
            if node.width > 64 {
                return None;
            }
            seen.insert(id, ());
            stack.push((id, true));
            if node.op == OpCode::Extract && cx.wid(node.a) > 64 {
                let mut pieces = Vec::new();
                if !collect_wide_slice(cx, node.a, node.b, node.width, 16, &mut pieces)
                    || pieces.is_empty()
                {
                    return None;
                }
                for p in pieces.iter().rev() {
                    if let SlicePiece::Slice(leaf, _, _) = *p
                        && !seen.contains_key(&leaf)
                    {
                        stack.push((leaf, false));
                    }
                }
                wide_extracts.insert(id, pieces);
                continue;
            }
            let mut kids = [0u32; 3];
            let mut klen = 0usize;
            for c in node.children() {
                kids[klen] = c;
                klen += 1;
            }
            for &c in kids[..klen].iter().rev() {
                if !seen.contains_key(&c) {
                    stack.push((c, false));
                }
            }
        }
        let mut slots = IdMap::default();
        let mut ops = Vec::with_capacity(order.len());
        let mut symbols = Vec::new();
        for id in order {
            let node = cx.node(id);
            let width = node.width;
            if width > 64 {
                return None;
            }
            if let Some(pieces) = wide_extracts.get(&id) {
                let mut acc: Option<(usize, u16)> = None;
                for &piece in pieces {
                    let (part_slot, part_w) = match piece {
                        SlicePiece::Zero(pw) => {
                            let s = ops.len();
                            ops.push(Instruction {
                                op: Op::Constant(0),
                                width: pw,
                                mask: mask(pw),
                            });
                            (s, pw)
                        }
                        SlicePiece::Slice(leaf, sub_lo, sub_len) => {
                            let leaf_slot = slots[&leaf];
                            if sub_lo == 0 && sub_len == cx.wid(leaf) {
                                (leaf_slot, sub_len)
                            } else {
                                let s = ops.len();
                                ops.push(Instruction {
                                    op: Op::Extract(leaf_slot, sub_lo),
                                    width: sub_len,
                                    mask: mask(sub_len),
                                });
                                (s, sub_len)
                            }
                        }
                    };
                    acc = Some(match acc {
                        None => (part_slot, part_w),
                        Some((lo_slot, lo_w)) => {
                            let cw = lo_w + part_w;
                            let s = ops.len();
                            ops.push(Instruction {
                                op: Op::Concat(part_slot, lo_slot, lo_w),
                                width: cw,
                                mask: mask(cw),
                            });
                            (s, cw)
                        }
                    });
                }
                let (final_slot, _) = acc?;
                slots.insert(id, final_slot);
                continue;
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
                    let slot = symbols.len();
                    symbols.push(Symbol {
                        key,
                        width: cx.width_of(id),
                        ones,
                        free: mask(width) & !(ones | zeros),
                        unknown: Vec::new(),
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
                    } else if let Some((_, 0)) = other.as_ext() {
                        let ext_op = cx.registry.as_deref()?.op_at(node.aux)?;
                        let mut kids = node.children();
                        let arg_x = kids.next()?;
                        let arg_k = kids.next()?;
                        let key = (cx.wid(arg_k) == 64)
                            .then(|| cx.const_val(arg_k)?.to_u64())
                            .flatten()?;
                        match ext_op.name() {
                            super::mixer::ROUND_OP_NAME => Op::MixerRound(slots[&arg_x], key),
                            super::mixer::UNROUND_OP_NAME if key & 1 == 1 => {
                                Op::MixerUnround(slots[&arg_x], key)
                            }
                            _ => return None,
                        }
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
        let program = Self {
            ops,
            symbols,
            inputs: 0,
            goal: slots[&goal],
            constraints: constraints.iter().map(|id| slots[id]).collect(),
            word_groups: Vec::new(),
        };
        Some((program, slots))
    }

    // Use only exact original seed masks through pure wiring. In particular, do not read
    // an assumption overlay cached under older declarations or spend additional fact work.
    // All original constraints still filter assignments and participate in model replay.
    fn fix_scoped_bits(
        &mut self,
        assumptions: Option<&Assumptions>,
        slots: &IdMap<u32, usize>,
        limit: usize,
    ) -> Option<()> {
        if assumptions.is_some_and(|a| a.len() > limit) {
            return None;
        }
        let mut pending: Vec<(usize, u64, u64)> = self
            .constraints
            .iter()
            .map(|&slot| (slot, 1u64, 1u64))
            .collect();
        if let Some(assumptions) = assumptions {
            for (_, expression, facts) in assumptions.constraints() {
                let known = facts.known();
                if known.width().bits() <= 64
                    && !known.known().is_zero()
                    && let Some(&slot) = slots.get(&expression.index())
                {
                    pending.push((slot, known.known().to_u64()?, known.known_one().to_u64()?));
                }
            }
        }
        let mut fixed = vec![(0u64, 0u64); self.symbols.len()];
        let mut seen = IdMap::<usize, (u64, u64)>::default();
        let mut remaining = limit;
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
                Op::Compare(op @ (CmpOp::Eq | CmpOp::Ne), a, b, _)
                    if known == 1 && ((op == CmpOp::Eq) == (ones == 1)) =>
                {
                    if let Op::Constant(val) = self.ops[b].op {
                        let m = self.ops[a].mask;
                        pending.push((a, m, val & m));
                    } else if let Op::Constant(val) = self.ops[a].op {
                        let m = self.ops[b].mask;
                        pending.push((b, m, val & m));
                    }
                }
                Op::Binary(BinOp::And, a, b) => {
                    if ones != 0 {
                        pending.push((a, ones, ones));
                        pending.push((b, ones, ones));
                    }
                    if let Op::Constant(c) = self.ops[b].op {
                        if (known & !c & ones) != 0 {
                            return None;
                        }
                        let m = known & c;
                        if m != 0 {
                            pending.push((a, m, ones & m));
                        }
                    } else if let Op::Constant(c) = self.ops[a].op {
                        if (known & !c & ones) != 0 {
                            return None;
                        }
                        let m = known & c;
                        if m != 0 {
                            pending.push((b, m, ones & m));
                        }
                    }
                }
                Op::Binary(BinOp::Or, a, b) => {
                    let zeros = known & !ones;
                    if zeros != 0 {
                        pending.push((a, zeros, 0));
                        pending.push((b, zeros, 0));
                    }
                    if let Op::Constant(c) = self.ops[b].op {
                        if (known & c & !ones) != 0 {
                            return None;
                        }
                        let m = known & !c;
                        if m != 0 {
                            pending.push((a, m, ones & m));
                        }
                    } else if let Op::Constant(c) = self.ops[a].op {
                        if (known & c & !ones) != 0 {
                            return None;
                        }
                        let m = known & !c;
                        if m != 0 {
                            pending.push((b, m, ones & m));
                        }
                    }
                }
                Op::Binary(BinOp::Xor, a, b) => {
                    if let Op::Constant(c) = self.ops[b].op {
                        pending.push((a, known, (ones ^ c) & known));
                    } else if let Op::Constant(c) = self.ops[a].op {
                        pending.push((b, known, (ones ^ c) & known));
                    }
                }
                // Other operations can lose the source-bit relationship. Ignoring their
                // known bits overapproximates legal inputs, never omits one.
                _ => {}
            }
        }
        for (symbol, &(known, ones)) in self.symbols.iter_mut().zip(&fixed) {
            let global = mask(symbol.width.bits()) & !symbol.free;
            if global & known & (symbol.ones ^ ones) != 0 {
                return None;
            }
            symbol.ones |= ones;
            symbol.free &= !known;
        }
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
        self.evaluate_with(
            |s| Self::symbol_value(&self.symbols[s], inputs, lane),
            values,
        );
    }

    fn evaluate_with(&self, symbol: impl Fn(usize) -> u64, values: &mut [u64]) {
        for (i, instruction) in self.ops.iter().enumerate() {
            let width = instruction.width;
            values[i] = match instruction.op {
                Op::Constant(value) => value,
                Op::Symbol(slot) => symbol(slot),
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
                Op::MixerRound(a, key) => super::mixer::eval_round(values[a], key),
                Op::MixerUnround(a, key) => super::mixer::invert_round(values[a], key).unwrap_or(0),
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
                let low = m.isolate_lowest_one();
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
    try_sample_with_limit(cx, goal, constraints, assumptions, cfg, MAX_NODES, false)
}

pub(super) fn try_sample_post_simplify(
    cx: &mut Context,
    goal: u32,
    constraints: &[u32],
    assumptions: Option<&Assumptions>,
    cfg: &Config,
) -> Option<Trial> {
    let allow_cone_heuristics =
        !cfg.word_sampling && cfg.sample_mode == SampleMode::Random && !cfg.certificate;
    try_sample_with_limit(
        cx,
        goal,
        constraints,
        assumptions,
        cfg,
        POST_SIMP_MAX_NODES,
        allow_cone_heuristics,
    )
}

fn low_prefix_u64(m: u64) -> u64 {
    if m == 0 {
        0
    } else {
        u64::MAX >> m.leading_zeros()
    }
}

enum SmallCone {
    /// Conjunct `(slot, want)` has zero satisfying assignments across its entire exact support.
    Unsat(u64),
    /// Single-symbol exact satisfying bit-patterns `(sym_idx, eff_mask, patterns)`.
    Witnesses(usize, u64, Vec<u64>),
}

type ConePin = (usize, u64, Vec<u64>);

/// Evaluates any required conjunct `(slot, want)` whose demanded support inside `p` depends on at
/// most 10 free bits of a single symbol (`<= 1024` points) and zero free bits of all other symbols.
fn analyze_small_cones(p: &Program, terms: &[(usize, bool)]) -> (Option<u64>, Vec<ConePin>) {
    let mut pins: Vec<ConePin> = Vec::new();
    let mut dem: IdMap<usize, u64> = IdMap::default();
    let mut cone: Vec<usize> = Vec::new();
    let mut vals: Vec<u64> = Vec::new();

    for &(slot, want) in terms.iter().take(24) {
        dem.clear();
        cone.clear();
        let init_m = p.ops[slot].mask;
        if init_m == 0 {
            continue;
        }
        dem.insert(slot, init_m);
        // Walk backwards through `slot`'s cone by Collecting reachable op indices (`child < parent`).
        let mut stack = vec![slot];
        let mut too_big = false;
        while let Some(u) = stack.pop() {
            if cone.contains(&u) {
                continue;
            }
            if cone.len() >= 256 {
                too_big = true;
                break;
            }
            cone.push(u);
            match p.ops[u].op {
                Op::Constant(_) | Op::Symbol(_) => {}
                Op::Unary(_, a)
                | Op::Zext(a)
                | Op::Sext(a, _)
                | Op::Extract(a, _)
                | Op::MixerRound(a, _)
                | Op::MixerUnround(a, _) => stack.push(a),
                Op::Binary(_, a, b) | Op::Compare(_, a, b, _) | Op::Concat(a, b, _) => {
                    stack.extend([a, b]);
                }
                Op::Select(c, t, e) => stack.extend([c, t, e]),
            }
        }
        if too_big {
            continue;
        }
        cone.sort_unstable();
        for &u in cone.iter().rev() {
            let m = dem.get(&u).copied().unwrap_or(0) & p.ops[u].mask;
            if m == 0 {
                continue;
            }
            let mut add_dem = |ch: usize, cm: u64| {
                let masked = cm & p.ops[ch].mask;
                if masked != 0 {
                    *dem.entry(ch).or_default() |= masked;
                }
            };
            match p.ops[u].op {
                Op::Constant(_) | Op::Symbol(_) => {}
                Op::Unary(UnOp::Not, a) => add_dem(a, m),
                Op::Unary(UnOp::Neg, a) => add_dem(a, low_prefix_u64(m)),
                Op::Unary(_, a) | Op::MixerRound(a, _) | Op::MixerUnround(a, _) => {
                    add_dem(a, p.ops[a].mask);
                }
                Op::Zext(a) => add_dem(a, m),
                Op::Sext(a, w) => {
                    let mut ma = m & p.ops[a].mask;
                    if m & !p.ops[a].mask != 0 {
                        ma |= 1u64 << (w - 1);
                    }
                    add_dem(a, ma);
                }
                Op::Extract(a, lo) => {
                    if lo < 64 {
                        add_dem(a, m << lo);
                    } else {
                        add_dem(a, p.ops[a].mask);
                    }
                }
                Op::Concat(hi, lo, lb) => {
                    add_dem(lo, m);
                    if lb < 64 {
                        add_dem(hi, m >> lb);
                    }
                }
                Op::Binary(BinOp::And, a, b) => match (&p.ops[a].op, &p.ops[b].op) {
                    (_, &Op::Constant(c)) => add_dem(a, m & c),
                    (&Op::Constant(c), _) => add_dem(b, m & c),
                    _ => {
                        add_dem(a, m);
                        add_dem(b, m);
                    }
                },
                Op::Binary(BinOp::Or, a, b) => match (&p.ops[a].op, &p.ops[b].op) {
                    (_, &Op::Constant(c)) => add_dem(a, m & !c),
                    (&Op::Constant(c), _) => add_dem(b, m & !c),
                    _ => {
                        add_dem(a, m);
                        add_dem(b, m);
                    }
                },
                Op::Binary(BinOp::Xor, a, b) => {
                    add_dem(a, m);
                    add_dem(b, m);
                }
                Op::Binary(BinOp::Add | BinOp::Sub | BinOp::Mul, a, b) => {
                    let lp = low_prefix_u64(m);
                    add_dem(a, lp);
                    add_dem(b, lp);
                }
                Op::Binary(BinOp::Shl, a, b) => {
                    if let Op::Constant(k) = p.ops[b].op {
                        if k < 64 {
                            add_dem(a, m >> k);
                        }
                    } else {
                        add_dem(a, p.ops[a].mask);
                        add_dem(b, p.ops[b].mask);
                    }
                }
                Op::Binary(BinOp::LShr, a, b) => {
                    if let Op::Constant(k) = p.ops[b].op {
                        if k < 64 {
                            add_dem(a, m << k);
                        }
                    } else {
                        add_dem(a, p.ops[a].mask);
                        add_dem(b, p.ops[b].mask);
                    }
                }
                Op::Binary(_, a, b) | Op::Compare(_, a, b, _) => {
                    add_dem(a, p.ops[a].mask);
                    add_dem(b, p.ops[b].mask);
                }
                Op::Select(c, t, e) => {
                    add_dem(c, 1);
                    add_dem(t, m);
                    add_dem(e, m);
                }
            }
        }

        let mut active_sym: Option<(usize, u64)> = None;
        let mut multi_sym = false;
        for &u in &cone {
            if let Op::Symbol(s) = p.ops[u].op {
                let eff = dem.get(&u).copied().unwrap_or(0) & p.symbols[s].free;
                if eff != 0 {
                    match active_sym {
                        None => active_sym = Some((s, eff)),
                        Some((prev_s, prev_eff)) if prev_s == s => {
                            active_sym = Some((s, prev_eff | eff));
                        }
                        Some(_) => {
                            multi_sym = true;
                            break;
                        }
                    }
                }
            }
        }
        if multi_sym {
            continue;
        }
        let Some((sym_idx, eff_free)) = active_sym else {
            continue;
        };
        let k = eff_free.count_ones();
        if !(1..=10).contains(&k) {
            continue;
        }
        if pins
            .iter()
            .any(|&(s, m, _)| s == sym_idx && (m & eff_free) != 0)
        {
            continue;
        }

        let mut bit_positions = [0u16; 10];
        let mut tmp = eff_free;
        for bp in bit_positions.iter_mut().take(k as usize) {
            *bp = tmp.trailing_zeros() as u16;
            tmp &= tmp - 1;
        }
        if vals.len() < slot + 1 {
            vals.resize(slot + 1, 0);
        }
        let total_pts = 1u64 << k;
        let mut found = Vec::new();
        let base_ones = p.symbols[sym_idx].ones;
        for pt in 0..total_pts {
            let mut patch = 0u64;
            for (b, &pos) in bit_positions.iter().enumerate().take(k as usize) {
                if (pt >> b) & 1 != 0 {
                    patch |= 1u64 << pos;
                }
            }
            let sym_val = base_ones | patch;
            for &u in &cone {
                let ins = &p.ops[u];
                let w = ins.width;
                vals[u] = match ins.op {
                    Op::Constant(v) => v,
                    Op::Symbol(s) => {
                        if s == sym_idx {
                            sym_val
                        } else {
                            p.symbols[s].ones
                        }
                    }
                    Op::Unary(op, a) => match op {
                        UnOp::Not => !vals[a],
                        UnOp::Neg => vals[a].wrapping_neg(),
                        UnOp::Popcnt => u64::from(vals[a].count_ones()),
                        UnOp::Clz => u64::from(vals[a].leading_zeros() - (64 - u32::from(w))),
                        UnOp::Ctz => u64::from(vals[a].trailing_zeros().min(u32::from(w))),
                        UnOp::Bswap => vals[a].swap_bytes() >> (64 - w),
                        UnOp::BitRev => vals[a].reverse_bits() >> (64 - w),
                    },
                    Op::Binary(op, a, b) => binary(op, vals[a], vals[b], w),
                    Op::Compare(op, a, b, cw) => u64::from(match op {
                        CmpOp::Eq => vals[a] == vals[b],
                        CmpOp::Ne => vals[a] != vals[b],
                        CmpOp::Ult => vals[a] < vals[b],
                        CmpOp::Ule => vals[a] <= vals[b],
                        CmpOp::Slt => signed(vals[a], cw) < signed(vals[b], cw),
                        CmpOp::Sle => signed(vals[a], cw) <= signed(vals[b], cw),
                    }),
                    Op::Zext(a) => vals[a],
                    Op::Sext(a, sw) => signed(vals[a], sw) as u64,
                    Op::Extract(a, lo) => vals[a] >> lo,
                    Op::Concat(a, b, low) => (vals[a] << low) | vals[b],
                    Op::Select(c, t, e) => vals[if vals[c] != 0 { t } else { e }],
                    Op::MixerRound(a, key) => super::mixer::eval_round(vals[a], key),
                    Op::MixerUnround(a, key) => {
                        super::mixer::invert_round(vals[a], key).unwrap_or(0)
                    }
                } & ins.mask;
            }
            if (vals[slot] != 0) == want {
                found.push(patch);
            }
        }
        let res = if found.is_empty() {
            SmallCone::Unsat(total_pts)
        } else {
            SmallCone::Witnesses(sym_idx, eff_free, found)
        };
        match res {
            SmallCone::Unsat(pts) => return (Some(pts), pins),
            SmallCone::Witnesses(s, m, pats) => {
                if pats.len() < (total_pts as usize) {
                    pins.push((s, m, pats));
                }
            }
        }
    }
    (None, pins)
}

fn collect_required_program_conjuncts(p: &Program) -> Vec<(usize, bool)> {
    let mut out = Vec::new();
    let mut stack: Vec<(usize, bool)> = Vec::new();
    for &c in &p.constraints {
        stack.push((c, true));
    }
    stack.push((p.goal, false));
    for _ in 0..128 {
        let Some((u, want)) = stack.pop() else { break };
        match p.ops[u].op {
            Op::Unary(UnOp::Not, a) => stack.push((a, !want)),
            Op::Binary(BinOp::And, a, b) if want => stack.extend([(a, true), (b, true)]),
            Op::Binary(BinOp::Or, a, b) if !want => stack.extend([(a, false), (b, false)]),
            _ => {
                if !out.contains(&(u, want)) {
                    out.push((u, want));
                }
            }
        }
    }
    out
}

fn try_sample_with_limit(
    cx: &mut Context,
    goal: u32,
    constraints: &[u32],
    assumptions: Option<&Assumptions>,
    cfg: &Config,
    limit: usize,
    use_small_cones: bool,
) -> Option<Trial> {
    let mut program = Program::compile_with_limit(cx, goal, constraints, assumptions, limit)?;
    let (unsat_pts, cone_pins) = if use_small_cones {
        let req_terms = collect_required_program_conjuncts(&program);
        analyze_small_cones(&program, &req_terms)
    } else {
        (None, Vec::new())
    };
    if let Some(pts) = unsat_pts
        && pts <= u64::from(cfg.samples)
    {
        return Some(Trial {
            samples: 64,
            model: None,
            complete: true,
        });
    }
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
            if !cone_pins.is_empty() && (batch > 0 || lane >= 2) {
                program.evaluate_with(
                    |s| {
                        let mut v = Program::symbol_value(&program.symbols[s], &inputs, lane);
                        for &(ps, pm, ref pats) in &cone_pins {
                            if ps == s {
                                let idx = (batch as usize * 64 + lane as usize) % pats.len();
                                v = (v & !pm) | pats[idx];
                            }
                        }
                        v
                    },
                    &mut values,
                );
            } else {
                program.evaluate(&inputs, lane, &mut values);
            }
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
                .enumerate()
                .map(|(si, s)| {
                    let mut v = Program::symbol_value(s, &inputs, lane);
                    if !cone_pins.is_empty() && (batch > 0 || lane >= 2) {
                        for &(ps, pm, ref pats) in &cone_pins {
                            if ps == si {
                                let idx = (batch as usize * 64 + lane as usize) % pats.len();
                                v = (v & !pm) | pats[idx];
                            }
                        }
                    }
                    (s.key.clone(), BitVec::from_u64(s.width, v).unwrap())
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

/// A uniform random word essentially never equals a specific 64-bit case label.
/// Spend one sample batch on the original DAG, biasing each symbol toward its own
/// comparison literals. This is witness search only: a miss says nothing.
pub(super) fn guard_samples(cx: &mut Context, root: u32) -> Option<(u64, Option<Model>)> {
    // A short select chain can return its fallback on almost every random input,
    // even when a few simultaneous tag equalities reach a different word.
    let n = cx.node(root);
    let mut selected_equality =
        n.op == OpCode::Eq && [n.a, n.b].iter().any(|&i| cx.node(i).op == OpCode::Select);
    let single_word_target =
        matches!(n.op, OpCode::Eq | OpCode::Ne) && n.op == OpCode::Ne && cx.wid(n.a) >= 8;
    let conjunctive = n.op == OpCode::Or || (n.op == OpCode::Not && cx.node(n.a).op == OpCode::And);
    let tall = cx.height(cx.handle(root)).ok()? >= 32;
    if !selected_equality && !single_word_target && !conjunctive && !tall {
        return None;
    }
    // A short implication can contain a full-width equality whose required
    // value is another lane word, not a constant label. Inspect its Boolean
    // spine before deciding whether to compile the word program.
    let mut terms = Vec::new();
    let mut stack = vec![(root, false)];
    let mut word_guard = false;
    for _ in 0..128 {
        let Some((i, want)) = stack.pop() else { break };
        let n = cx.node(i);
        match n.op {
            OpCode::Not => stack.push((n.a, !want)),
            OpCode::And if want => stack.extend([(n.a, true), (n.b, true)]),
            OpCode::Or if !want => stack.extend([(n.a, false), (n.b, false)]),
            _ => {
                selected_equality |= !want
                    && n.op == OpCode::Eq
                    && [n.a, n.b].iter().any(|&k| cx.node(k).op == OpCode::Select);
                word_guard |= matches!(n.op, OpCode::Eq | OpCode::Ne)
                    && (n.op == OpCode::Eq) == want
                    && cx.wid(n.a) >= 8;
                terms.push((i as usize, want));
            }
        }
    }
    let guarded = word_guard && (terms.len() > 1 || single_word_target);
    if !selected_equality && !guarded && !tall {
        return None;
    }
    let limit = if tall || selected_equality {
        32_768
    } else {
        127
    };
    let (p, slots) = Program::lower(cx, root, &[], limit)?;
    let compact_guard = guarded && p.ops.len() < 128 && (terms.len() > 1 || p.ops.len() >= 12);
    if !selected_equality && !compact_guard && p.ops.len() < 128 {
        return None;
    }
    let mut labels = vec![Vec::new(); p.symbols.len()];
    let mut cases = Vec::new();
    for ins in &p.ops {
        let Op::Compare(op, a, b, _) = ins.op else {
            continue;
        };
        let Some(target) = guard::Target::literal(&p, a, b) else {
            continue;
        };
        if let Op::Symbol(s) = p.ops[target.slot].op {
            if labels[s].len() < 8 && !labels[s].contains(&target.value) {
                labels[s].push(target.value);
            }
        } else if matches!(op, CmpOp::Eq | CmpOp::Ne) && cases.len() < 64 {
            cases.push(target);
        }
    }
    let mut mixer_seed: Vec<(usize, u64)> = Vec::new();
    if super::mixer::may_contain_mixer(cx, root) {
        for (sym_key, bv) in super::mixer::candidate_symbol_patches(cx, root) {
            if let Some(val) = bv.to_u64()
                && let Some(slot) = p.symbols.iter().position(|s| s.key == sym_key)
            {
                if labels[slot].len() < 8 && !labels[slot].contains(&val) {
                    labels[slot].push(val);
                }
                if !mixer_seed.iter().any(|&(s, _)| s == slot) {
                    mixer_seed.push((slot, val));
                }
            }
        }
    }
    if selected_equality
        && p.ops.len() < 128
        && labels.iter().all(Vec::is_empty)
        && cases.is_empty()
    {
        return None;
    }
    let mut values = vec![0; p.ops.len()];
    let mut assignment = vec![0; p.symbols.len()];
    // If the original question is an implication, keep assignments close to
    // satisfying its counterexample conjuncts. Ranking never decides the result.
    let mut fields = Vec::new();
    let mut bit_pins: Vec<(usize, u64, u64)> = Vec::new();
    for (i, want) in &mut terms {
        let node = *i as u32;
        *i = slots[&node];
        if *want
            && cx.node(node).op == OpCode::Eq
            && fields.len() < 8
            && let Some(f) = crate::expr::field::field(cx, node)
            && (1..=64).contains(&f.mask.count_ones())
            && let Op::Symbol(s) = p.ops[slots[&f.base]].op
        {
            fields.push((s, f));
        } else if bit_pins.len() < 16 {
            let nd = cx.node(node);
            if nd.op == OpCode::Sym
                && nd.width == 1
                && let Op::Symbol(s) = p.ops[*i].op
            {
                bit_pins.push((s, 1, u64::from(*want)));
            } else if nd.op == OpCode::Extract
                && nd.width == 1
                && nd.b < 64
                && let Some(&base_slot) = slots.get(&nd.a)
                && let Op::Symbol(s) = p.ops[base_slot].op
            {
                let bit = nd.b;
                bit_pins.push((s, 1u64 << bit, u64::from(*want) << bit));
            } else if let Op::Compare(op @ (CmpOp::Eq | CmpOp::Ne), a, b, _) = p.ops[*i].op
                && (op == CmpOp::Eq) == *want
                && let Some(target) = guard::Target::literal(&p, a, b)
                && let Op::Concat(hi, lo, lo_bits) = p.ops[target.slot].op
            {
                let sym_slice = |slot: usize| -> Option<(usize, u16)> {
                    match p.ops[slot].op {
                        Op::Symbol(s) => Some((s, 0)),
                        Op::Extract(base, off) => match p.ops[base].op {
                            Op::Symbol(s) => Some((s, off)),
                            _ => None,
                        },
                        _ => None,
                    }
                };
                if let Some((s_lo, off_lo)) = sym_slice(lo) {
                    let m = p.ops[lo].mask;
                    bit_pins.push((s_lo, m << off_lo, (target.value & m) << off_lo));
                }
                if let Some((s_hi, off_hi)) = sym_slice(hi) {
                    let m = p.ops[hi].mask;
                    bit_pins.push((s_hi, m << off_hi, ((target.value >> lo_bits) & m) << off_hi));
                }
            }
        }
    }
    let required: Vec<_> = terms
        .iter()
        .filter_map(|&(i, want)| match p.ops[i].op {
            Op::Compare(op @ (CmpOp::Eq | CmpOp::Ne), a, b, _) if (op == CmpOp::Eq) == want => {
                Some(
                    guard::Target::literal(&p, a, b)
                        .map_or(guard::Requirement::Equal(a, b), guard::Requirement::Value),
                )
            }
            Op::Compare(..) => None,
            _ if compact_guard => Some(guard::Requirement::Value(guard::Target {
                slot: i,
                value: u64::from(want),
            })),
            _ => None,
        })
        .collect();
    let ranges = guard::intervals(&p, &terms);
    let (_, cone_pins) = analyze_small_cones(&p, &terms);
    let mut best = assignment.clone();
    let mut distance = u32::MAX;
    let mut offset = None;
    let field_constrained = !fields.is_empty() || !bit_pins.is_empty() || !cone_pins.is_empty();
    for lane in 0..64 {
        // A known field has a constructive inverse. Vary its free bits on
        // fresh lanes instead of repairing unrelated internal case labels.
        let field_lane = field_constrained && terms.len() > 1 && (8..48).contains(&lane);
        // Try the structural inverse and weighted terms first. Later lanes
        // can repair one hidden addend, each from the same legal zero seed.
        let coordinate = (lane >= 32)
            .then(|| (lane - 32) as usize)
            .filter(|&s| s < p.symbols.len())
            .zip(offset);
        let patch = if let Some((s, delta)) = coordinate {
            for (v, sym) in assignment.iter_mut().zip(&p.symbols) {
                *v = sym.ones;
            }
            let sym = &p.symbols[s];
            Some((s, sym.ones | (sym.ones.wrapping_add(delta) & sym.free)))
        } else if compact_guard && lane >= 2 && lane % 8 != 0 {
            // Keep a repaired conjunct when repairing the next one; independent
            // wide constraints are unlikely to hold on the same fresh random lane.
            guard::propose(&p, &values, &required, &ranges, &cases, lane as usize)
        } else if !compact_guard
            && !field_lane
            && lane >= 8
            && lane & 3 < 2
            && (!required.is_empty() || !cases.is_empty() || !ranges.is_empty())
        {
            let round = (lane / 4 * 2 + lane % 4) as usize;
            guard::propose(&p, &values, &required, &ranges, &cases, round)
        } else {
            None
        };
        if let Some((s, v)) = patch {
            assignment[s] = v;
        } else if !mixer_seed.is_empty() && (lane == 2 || lane == 3) {
            let fill = if lane == 2 { 0 } else { u64::MAX };
            for (i, val) in assignment.iter_mut().enumerate() {
                *val = p.symbols[i].ones | (fill & p.symbols[i].free);
            }
            for &(s, mv) in &mixer_seed {
                let sym = &p.symbols[s];
                assignment[s] = sym.ones | (mv & sym.free);
            }
        } else {
            for (i, val) in assignment.iter_mut().enumerate() {
                let rand = sample(lane + 1, i as u32);
                if !field_lane && lane >= 32 && lane % 4 == 3 && terms.len() > 1 && rand & 3 != 0 {
                    *val = best[i];
                    continue;
                }
                let v = match lane {
                    0 => 0,
                    1 => u64::MAX,
                    _ if !labels[i].is_empty() && rand & 7 != 0 => {
                        labels[i][(rand >> 32) as usize % labels[i].len()]
                    }
                    _ if field_lane || compact_guard => rand,
                    _ if lane & 3 == 0 => 0,
                    _ if lane & 3 == 1 => u64::MAX,
                    _ => rand,
                };
                *val = p.symbols[i].ones | (v & p.symbols[i].free);
            }
        }
        // Stay inside mandatory masked equalities while varying their free
        // bits. Do not override declarations or overwrite the extremal seeds.
        if lane >= 2 {
            for &(s, field) in &fields {
                let sym = &p.symbols[s];
                let v = field.seed(assignment[s]) & mask(sym.width.bits());
                if v & !sym.free == sym.ones {
                    assignment[s] = v;
                }
            }
            for &(s, m, val) in &bit_pins {
                let sym = &p.symbols[s];
                let v = ((assignment[s] & !m) | val) & mask(sym.width.bits());
                if v & !sym.free == sym.ones {
                    assignment[s] = v;
                }
            }
            for &(s, m, ref pats) in &cone_pins {
                let sym = &p.symbols[s];
                let pat = pats[lane as usize % pats.len()];
                let v = ((assignment[s] & !m) | pat) & mask(sym.width.bits());
                if v & !sym.free == sym.ones {
                    assignment[s] = v;
                }
            }
        }
        p.evaluate_with(|s| assignment[s], &mut values);
        if lane == 0
            && terms.len() == 2
            && let [interval] = ranges.as_slice()
        {
            offset = interval.offset(&values);
        }
        if values[p.goal] == 0 {
            let model = p
                .symbols
                .iter()
                .zip(assignment)
                .map(|(s, v)| (s.key.clone(), BitVec::from_u64(s.width, v).unwrap()))
                .collect();
            return Some((u64::from(lane) + 1, Some(model)));
        }
        if terms.len() > 1 {
            let rank = terms
                .iter()
                .map(|&(i, want)| {
                    if (values[i] != 0) == want {
                        return 0;
                    }
                    64 + match p.ops[i].op {
                        Op::Compare(CmpOp::Eq | CmpOp::Ne, a, b, _) => {
                            (values[a] ^ values[b]).count_ones()
                        }
                        Op::Compare(CmpOp::Ult | CmpOp::Ule, a, b, _) => {
                            1 + values[a].abs_diff(values[b]).checked_ilog2().unwrap_or(0)
                        }
                        Op::Compare(CmpOp::Slt | CmpOp::Sle, a, b, w) => {
                            1 + signed(values[a], w)
                                .abs_diff(signed(values[b], w))
                                .checked_ilog2()
                                .unwrap_or(0)
                        }
                        _ => 1,
                    }
                })
                .sum();
            if rank <= distance {
                distance = rank;
                best.copy_from_slice(&assignment);
            }
        }
    }
    Some((64, None))
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
